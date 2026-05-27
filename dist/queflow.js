/*!
 * QueFlow.js
 * (c) 2024-now Sodiq Tunde (lahan-xyz)
 * Released under the MIT License.
 */
'use-strict';

// Counter for generating unique IDs for elements with reactive data.
var counterQF = -1,
  nuggetCounter = -1,
  routerObj = {},
  currentComponent,
  navigateFunc = (() => {}),
  globalStateDataQF = [];

var stylesheet = {
  el: document.createElement("style"),
  isAppended: false
};

const updateQueue = [];
let microtaskPending = false;

const components = new Map(),
  nuggets = new Map();

// Cached reactive elements
const reactiveCache = new Map();

// LRU Cache class
class LRUCache {
  constructor(maxSize = 500) {
    this.maxSize = maxSize;
    this._map = new Map();
  }
  
  get(key) {
    if (!this._map.has(key)) return undefined;
    // Move to end (most recently used)
    const value = this._map.get(key);
    this._map.delete(key);
    this._map.set(key, value);
    return value;
  }
  
  set(key, value) {
    // If key already exists, delete it first so the new insert goes to the end
    if (this._map.has(key)) {
      this._map.delete(key);
    } else if (this._map.size >= this.maxSize) {
      // Evict the least recently used (first item in the map)
      const oldestKey = this._map.keys().next().value;
      this._map.delete(oldestKey);
    }
    this._map.set(key, value);
  }
  
  has(key) {
    return this._map.has(key);
  }
  
  delete(key) {
    return this._map.delete(key);
  }
  
  clear() {
    this._map.clear();
  }
  
  get size() {
    return this._map.size;
  }
}


// O(1) element lookup
const selectElement = qfid => {
  return reactiveCache.get(qfid) || document.querySelector(`[data-qfid="${qfid}"]`);
};

// O(N) JavaScript-only filter, zero DOM calls
function filterNullElements(input) {
  if (!input || input.length === 0) return input;
  return input.filter(d => reactiveCache.has(d.qfid));
  
}


const strToEl = (component) => {
  const id = component.element;
  if (typeof id === "string") {
    component.element = document.getElementById(id);
  }
}

const globalState = (name, val, shouldStore) => {
  let stored;
  if (shouldStore) {
    stored = localStorage.getItem(name);
    val = stored ? JSON.parse(stored) : val; // only parse if truthy
  }
  
  const obj = typeof val === "object" ? val : { value: val };
  
  // Batching helpers for localStorage writes
  let localStorageDirty = false;
  const persist = () => {
    if (shouldStore && localStorageDirty) {
      localStorage.setItem(name, JSON.stringify(obj));
      localStorageDirty = false;
    }
  };
  
  const reactiveObj = (object) => {
    return new Proxy(object, {
      get(target, key) {
        // Optional: if you want deep reactivity, return a reactive proxy for nested objects here.
        // For now, keep the simple direct return.
        return target[key];
      },
      set(target, key, value) {
        if (target[key] !== value) {
          target[key] = value;
          // Trigger DOM update (already batched via batchedUpdate)
          updateComponent(key, true, value);
          
          // Mark localStorage as dirty; write will happen once per microtask
          if (shouldStore) {
            localStorageDirty = true;
            queueMicrotask(persist);
          }
        }
        return true;
      }
    });
  };
  
  globalThis[name] = reactiveObj(obj);
};

// Creates a reactive signal, a proxy object that automatically updates the DOM when its values change.
function createSignal(data, object) {
  const item = typeof data !== "object" ? { value: data } : data;
  
  // Cache for nested reactive wrappers – one proxy per underlying object
  const cache = new WeakMap();
  
  function createReactiveObject(obj) {
    if (typeof obj !== "object" || obj === null) return obj;
    
    // Return existing proxy if available
    if (cache.has(obj)) return cache.get(obj);
    
    const proxy = new Proxy(obj, {
      get(target, key) {
        // Recursively wrap nested objects, but now cached
        return createReactiveObject(target[key]);
      },
      set(target, key, value) {
        const prev = target[key];
        if (prev !== value) {
          target[key] = value;
          
          // Run the update synchronously – batching is handled by batchedUpdate
          if (!object.isFrozen) {
            const goAhead = object.onUpdate ?
              object.onUpdate({ oldVal: prev, key, newVal: value },
                object.data
              ) :
              true;
            if (goAhead) updateComponent(key, object, value);
          }
        }
        return true;
      }
    });
    
    cache.set(obj, proxy);
    return proxy;
  }
  
  return createReactiveObject(item);
}

const b = str => stringBetween(str, "{{", "}}");


// Extracts the string between two delimiters in a given string.
function stringBetween(str, f, s) {
  const indx1 = str.indexOf(f);
  if (indx1 === -1) return "";
  const indx2 = str.indexOf(s, indx1 + f.length);
  if (indx2 === -1) return "";
  return str.slice(indx1 + f.length, indx2);
}

// Sanitizes a string to prevent potential XSS attacks.
function sanitizeString(str) {
  str = String(str);
  
  // Single‑pass regex: escape HTML special chars & remove "javascript:"
  return str.replace(/[&<>"']|javascript:/gi, match => {
    switch (match) {
      case '&':
        return '&amp;';
      case '<':
        return '&lt;';
      case '>':
        return '&gt;';
      case '"':
        return '&quot;';
      case "'":
        return '&#39;';
      default: // matched "javascript:" (case‑insensitive)
        return '';
    }
  });
}


const EVAL_REGEX = /\{\{[^\{\{]+\}\}/g;
const ENTITY_REGEX = /&(gt|lt);/g;
const FALSY = [undefined, NaN, null];

// Global evaluator cache – keyed by the full expression string
const evaluatorCache = new Map();

function evaluateTemplate(reff, instance) {
  let out = "",
    currentMarkup = "";
  
  try {
    out = reff.replace(EVAL_REGEX, (match) => {
      currentMarkup = match;
      
      // Convert HTML entities back to real characters in one pass
      const processedMatch = match.replace(ENTITY_REGEX, (_, entity) =>
        entity === 'gt' ? '>' : '<'
      );
      
      // Extract the raw expression between {{ and }}
      let ext = b(processedMatch).trim();
      if (!ext) return match; // edge case: empty expression, keep original
      
      const shouldNegate = ext.startsWith('!');
      const isGlobal = ext.startsWith('$');
      
      // Build the cache key and the JavaScript source code
      let source, cacheKey;
      if (isGlobal) {
        // Global expression – evaluated without instance context
        source = `return ${ext}`;
        cacheKey = `g:${ext}`;
      } else {
        // Local expression – prefix with 'this.data.' unless it starts with 'this'
        const prefixed = ext.startsWith('this') ? ext : `this.data.${ext}`;
        source = `return ${prefixed}`;
        cacheKey = `l:${prefixed}`;
      }
      
      // Retrieve or compile the accessor function (cached)
      let evaluator = evaluatorCache.get(cacheKey);
      if (!evaluator) {
        evaluator = new Function(source);
        evaluatorCache.set(cacheKey, evaluator);
      }
      
      // Call the function with the correct context
      let parsed = isGlobal ? evaluator() : evaluator.call(instance);
      
      // Original fallback logic: if the value is falsy (and not "0"), show the raw template
      if (FALSY.includes(parsed) && parsed !== "0") {
        return match;
      }
      
      return parsed;
    });
  } catch (error) {
    console.warn(`QueFlow:\nAn error occured from expression \`${currentMarkup}\`\n${error}`);
  }
  
  return out;
}


// Gets the attributes of a DOM element.
function getAttributes(el) {
  return Array.from(el.attributes).map(({ nodeName, nodeValue }) => ({ attribute: nodeName, value: nodeValue }));
}


// Helper: wraps any text node that contains a reactive expression in a <span>
function wrapBareExpressions(root) {
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
  const nodesToWrap = [];
  
  let node;
  while ((node = walker.nextNode())) {
    const needsWrapping = node.textContent.includes('{{') && node.textContent.includes('}}') && node.parentNode.childElementCount > 0;
    
    if (needsWrapping) {
      nodesToWrap.push(node);
    }
  }
  
  for (const textNode of nodesToWrap) {
    const span = document.createElement('span');
    span.style.cssText = `
      display: inline;
      font: inherit;
      color: inherit;
      text-decoration: inherit;
      text-transform: inherit;
      letter-spacing: inherit;
      word-spacing: inherit;
      white-space: inherit;
      vertical-align: baseline;
      line-height: inherit;
      direction: inherit;
      unicode-bidi: inherit;
    `;
    textNode.parentNode.insertBefore(span, textNode);
    span.appendChild(textNode);
  }
}


function jsxToHTML(jsx, instance, subId) {
  const div = document.createElement("div");
  // innerHTML is substantially faster than DocumentFragment parsing for strings
  div.innerHTML = jsx;
  
  wrapBareExpressions(div);
  
  const data = [];
  
  try {
    // Live NodeList bypassing CSS engine
    const targetElements = div.getElementsByTagName("*");
    
    for (let i = 0, len = targetElements.length; i < len; i++) {
      const element = targetElements[i];
      
      if (subId && !element.hasAttribute("data-sub_id")) {
        // setAttribute is faster than element.dataset.sub_id
        element.setAttribute("data-sub_id", subId);
      }
      
      const childData = generateComponentData(
        element,
        element.childElementCount > 0, // isParent
        instance
      );
      
      // Traditional loop avoids call stack limits from spread operator (...)
      for (let j = 0; j < childData.length; j++) {
        data.push(childData[j]);
      }
      
      element.removeAttribute("innertext");
    }
    
    const html = div.innerHTML;
    div.remove();
    return [html.replaceAll("<br>", "\n"), data];
  } catch (error) {
    console.warn(
      `QueFlow:\nAn error in Component \`${instance.name || ""}\`:\n ${error}\n\nError sourced from: \`${jsx}\``
    );
    div.remove();
    return ["", data];
  }
}


// Compares two objects and checks if their key-value pairs are strictly same
function isSame(obj1, obj2) {
  const keys1 = Object.keys(obj1);
  const keys2 = Object.keys(obj2);
  
  if (keys1.length !== keys2.length) {
    return false;
  }
  
  for (const key of keys1) {
    if (obj1[key] !== obj2[key]) {
      return false;
    }
  }
  
  return true;
}

const qOnceMap = {
  text: "textContent",
  html: "innerHTML",
  class: "className"
}

function convertDirective(attr, value, child) {
  if (!attr.startsWith('q:')) return [attr, value, false];
  
  child.removeAttribute(attr);
  
  // --- q:once:xxx ---
  if (attr.startsWith('q:once:')) {
    let realAttr = attr.slice(7);
    return [qOnceMap[realAttr] || realAttr, value, true];
  }
  
  // --- Standard directives ---
  switch (attr) {
    case 'q:show': {
      if (value.includes('{{') && value.includes('}}')) {
        const expr = b(value).trim();
        return ['display', `{{ ${expr} ? 'block' : 'none' }}`, false];
      }
      return ['display', (value === 'true' || value === true) ? 'block' : 'none', false];
    }
    case 'q:text':
      child.textContent = value;
      return ['textContent', value, false]; // Added 'false' to match expected destructuring
      
    case 'q:html':
      return ['innerHTML', value, false]; // Added 'false'
      
    default:
      if (attr === 'q:once') {
        console.warn(`QueFlow: 'q:once' must be followed by ':attribute' (e.g., q:once:id="...").`);
      } else {
        console.warn(`QueFlow: unknown directive '${attr}'\n'${child.outerHTML}'`);
      }
      return [attr, value, false];
  }
}

// Generates and returns dataQF property
const generateComponentData = (child, isParent, instance) => {
  const arr = [];
  const attributes = getAttributes(child);
  // getAttribute is faster than dataset
  let QFID = child.getAttribute("data-qfid"); 
  const useStrict = instance.useStrict;
  
  // --- Content injection for leaf nodes ---
  if (!isParent) {
    let hasExplicitContentDirective = false;
    
    // Check our JS array instead of querying the DOM multiple times
    for (let i = 0; i < attributes.length; i++) {
      const name = attributes[i].attribute;
      if (name === 'q:text' || name === 'q:html' || name === 'q:once:text' || name === 'q:once:html') {
        hasExplicitContentDirective = true;
        break;
      }
    }
    
    if (!hasExplicitContentDirective) {
      const contentKey = useStrict ? 'textContent' : 'innerHTML';
      attributes.push({ attribute: contentKey, value: child[contentKey] });
    }
  }
  
  for (let i = 0; i < attributes.length; i++) {
    let { attribute, value } = attributes[i];
    value = value || '';
    
    let once = false;
    [attribute, value, once] = convertDirective(attribute, value, child);
    
    const hasTemplate = value.includes('{{') && value.includes('}}');
    const isStyle = (attribute in child.style) && attribute.toLowerCase() !== 'src';
    
    if (!hasTemplate) {
      if (isStyle) {
        child.style[attribute] = value;
        child.removeAttribute(attribute);
      } else {
        child[attribute] = value;
      }
      continue;
    }
    
    const evaluation = evaluateTemplate(value, instance);
    
    if (!QFID) {
      QFID = `qf${counterQF++}`;
      child.setAttribute('data-qfid', QFID); // Faster than dataset
    }
    
    if (isStyle) {
      child.style[attribute] = evaluation;
      child.removeAttribute(attribute);
    } else {
      child[attribute] = evaluation;
    }
    
    const expression = b(value).trim();
    // charCodeAt(0) === 36 is the fastest way to check if a string starts with '$'
    const isGlobal = expression.charCodeAt(0) === 36; 
    
    const entryObj = {
      template: value,
      key: isStyle ? `style.${attribute}` : attribute,
      qfid: QFID,
      isGlobal,
      once
    };
    
    if (isGlobal) {
      globalStateDataQF.push(entryObj);
    } else {
      arr[arr.length] = entryObj; // arr[length] assignment is marginally faster than arr.push()
    }
  }
  
  return arr;
};


// Function to convert an object into a CSS string
function objToStyle(selector = "", obj = {}, alt = "", shouldSwitch) {
  const lines = [];
  
  for (const key in obj) {
    const value = obj[key];
    
    // Guard against non-object/non-string values
    if (typeof value !== "string" && typeof value !== "object") continue;
    
    const isKeyframes = key.includes("@keyframes");
    const isFontFace = key.includes("@font-face");
    const isSpecialAtRule = isKeyframes || isFontFace;
    const isMedia = alt.includes("@media");
    const isRegularRule = !isSpecialAtRule && !isMedia;
    
    if (typeof value === "string") {
      // Build rule: either "selector key { value }" or "key selector { value }"
      const rule = shouldSwitch ?
        `${key}${isRegularRule ? selector : ""} { ${value} }` :
        `${isRegularRule ? selector + " " : ""}${key} { ${value} }`;
      
      lines.push(rule);
    } else {
      // Nested at-rule (e.g., @media, @keyframes with object body)
      // Recursively process, but only once we've opened the block
      lines.push(`${key} {`);
      lines.push(objToStyle(selector, value, key, shouldSwitch));
      lines.push(`}`);
    }
  }
  
  return lines.join("\n");
}

// Function to initiate the stylesheet
function initiateStyleSheet(selector = "", instance = {}, shouldSwitch) {
  // Convert the instance's stylesheet into a CSS string
  let styles = objToStyle(selector, instance.stylesheet, "", shouldSwitch);
  
  // Append the styles to the stylesheet element
  stylesheet.el.textContent += styles;
  
  // Append the stylesheet to the document head if not already appended
  if (!stylesheet.isAppended) {
    document.head.appendChild(stylesheet.el);
    stylesheet.isAppended = true;
  }
}


// Global cache for compiled event handlers
const eventHandlerCache = new LRUCache(500);

function handleEventListener(parent, instance) {
  const children = parent.querySelectorAll("*");
  
  for (const child of children) {
    const subId = child.dataset.sub_id;
    const targetInstance = subId ? components.get(subId) : instance;
    if (!targetInstance) continue;
    
    const attributes = getAttributes(child);
    
    for (const { attribute, value } of attributes) {
      if (!attribute.startsWith("on")) continue;
      
      // Cache key: instance identity + attribute + expression
      const cacheKey = `${targetInstance.constructor.name || ''}_${value}`;
      let handler = eventHandlerCache.get(cacheKey);
      
      if (!handler) {
        try {
          // Compile the function body once per unique expression/instance pair
          handler = Function("e", `const data = this.data; ${value}`).bind(targetInstance);
          eventHandlerCache.set(cacheKey, handler);
        } catch (e) {
          console.warn(`QueFlow:\nFailed to add event listener on ${child.tagName} element:\n\nError from: \`${value}\``);
          continue;
        }
      }
      
      // Assign the handler
      child[attribute] = handler;
      
      // Store the cache key on the element for later cleanup
      if (!child._qfHandlerKeys) child._qfHandlerKeys = [];
      child._qfHandlerKeys.push(cacheKey);
    }
    
    // Cleanup
    child.removeAttribute("data-sub_id");
    
    // Cache reactive elements (skip if already cached)
    const qfid = child.getAttribute('data-qfid');
    if (qfid && !reactiveCache.has(qfid)) {
      reactiveCache.set(qfid, child);
    }
  }
}


function update(child, key, evaluated) {
  switch (key) {
    case 'q:exist':
      if (evaluated === "false") {
        // getElementsByTagName is highly optimized and faster than TreeWalker
        const descendants = child.getElementsByTagName('*');
        
        // Pass as an array using spread syntax
        removeEvents([child, ...descendants]);
        child.remove();
      }
      break;
      
    case 'disabled':
      // Direct property assignment is much faster than setAttribute/removeAttribute
      const isDisabled = evaluated !== "false";
      if (child.disabled !== isDisabled) {
        child.disabled = isDisabled;
      }
      break;
      
    default:
      if (key.startsWith("style.")) { // startsWith is safer than indexOf > -1
        const sliced = key.slice(6);
        if (child.style[sliced] !== evaluated) {
          child.style[sliced] = evaluated;
        }
      } else {
        // 'in' operator checks the prototype chain and is faster than hasAttribute
        if (key in child) {
          if (child[key] != evaluated) {
            child[key] = evaluated;
          }
        } else {
          // Fallback to attribute if no corresponding object property exists
          if (child.getAttribute(key) != evaluated) {
            child.setAttribute(key, evaluated);
          }
        }
      }
  }
}


function scheduleFlush() {
  if (!microtaskPending) {
    microtaskPending = true;
    queueMicrotask(flushUpdates);
  }
}

function batchedUpdate(child, key, evaluated) {
  updateQueue.push({ child, key, evaluated });
  scheduleFlush();
}

function flushUpdates() {
  // Prevent re-entrancy if flush itself triggers more updates
  const batch = [...updateQueue];
  updateQueue.length = 0;
  microtaskPending = false;
  
  for (const { child, key, evaluated } of batch) {
    // Guard: child may have been removed by a previous queued entry
    if (child?.isConnected) {
      update(child, key, evaluated);
    }
  }
}


const NEEDSUPDATE_REGEX = /\{\{(.+?)\}\}/g;

function needsUpdate(template, key) {
  if (!template.includes('{{') || !template.includes('}}')) return false;
  // Reset regex state
  NEEDSUPDATE_REGEX.lastIndex = 0;
  let match;
  while ((match = NEEDSUPDATE_REGEX.exec(template)) !== null) {
    if (match[1].includes(key)) return true;
  }
  return false;
}


// Attribute-to-property mapping for standard DOM elements
const ATTR_TO_PROP = {
  class: 'className',
  for: 'htmlFor',
  tabindex: 'tabIndex',
  readonly: 'readOnly',
  maxlength: 'maxLength',
  accesskey: 'accessKey',
  colspan: 'colSpan',
  rowspan: 'rowSpan'
};

function updateComponent(ckey, instance) {
  const isGlobal = typeof instance === "boolean";
  let dataQF = filterNullElements(isGlobal ? globalStateDataQF : instance.dataQF);
  
  let writeIndex = 0; // Two-pointer technique for O(n) filtering
  
  for (let i = 0; i < dataQF.length; i++) {
    const entry = dataQF[i];
    const { template, key, qfid, once } = entry;
    
    // Default to keeping the entry
    let keep = true;
    
    if (ckey === "_" || needsUpdate(template, ckey)) {
      const node = selectElement(qfid);
      
      if (node) {
        let evaluated = evaluateTemplate(template, instance);
        let domKey = key.startsWith('style.') ? key : (ATTR_TO_PROP[key.toLowerCase()] || key);
        batchedUpdate(node, domKey, evaluated);
        
        if (once) keep = false; // Mark for removal if executed once
      } else {
        keep = false; // Node is missing; clean it up to prevent memory leaks
      }
    }
    
    // If we are keeping it, write it to the current write index and increment
    if (keep) {
      dataQF[writeIndex++] = entry;
    }
  }
  
  // Truncate the array to remove the discarded elements
  dataQF.length = writeIndex;
  
  // Sync back state
  if (isGlobal) {
    globalStateDataQF = dataQF;
  } else {
    instance.dataQF = dataQF;
  }
}

// Module‑level constant
const RENDER_TEMPLATE_REGEX = /\{\{([^\{\}]+)\}\}/g;

function renderTemplate(input, props, shouldSanitize) {
  return input.replace(RENDER_TEMPLATE_REGEX, (_, extracted) => {
    const trimmed = extracted.trim();
    const value = props[trimmed];
    
    if (value === undefined || value === null) {
      return `{{ ${trimmed} }}`; // keep placeholder for debugging
    }
    
    return shouldSanitize ? sanitizeString(value) : value;
  });
}

function initiateNuggets(markup, isNugget) {
  const nuggetRegex = /<([A-Z]\w*)\s*\{([\s\S]*?)\}\s*\/>/g;
  
  // Shared cache for compiled props (across all calls)
  if (!initiateNuggets._propsCache) {
    initiateNuggets._propsCache = new Map();
  }
  
  const replacedMarkup = markup.replace(nuggetRegex, (match, name, propsString) => {
    // propsString = the object literal inside { } (trimmed later)
    const trimmedProps = `{ ${propsString.trim()} }`;
    const cacheKey = `${propsString.trim()}`;
    
    let evaluated;
    try {
      // Retrieve or compile the props function
      let propsFn = initiateNuggets._propsCache.get(cacheKey);
      if (!propsFn) {
        propsFn = new Function(`return ${trimmedProps}`);
        initiateNuggets._propsCache.set(cacheKey, propsFn);
      }
      const d = propsFn();
      const instance = nuggets.get(name);
      
      if (instance) {
        evaluated = renderNugget(instance, d);
      } else {
        console.warn(`QueFlow:\nNugget '${name}' is not defined`);
        evaluated = match; // leave original markup as fallback
      }
    } catch (e) {
      console.warn(`QueFlow:\nAn error occured while rendering Nugget '${name}': ${e}\n\nError sourced from: \`${match}\``);
      evaluated = match; // keep original on error
    }
    return evaluated;
  });
  
  return lintPlaceholders(replacedMarkup, isNugget);
}



// Compute DOM depth
function getDepth(node) {
  let depth = 0;
  while (node.parentNode) {
    depth++;
    node = node.parentNode;
  }
  return depth;
}

function clearAllNuggetCaches() {
  initiateNuggets._propsCache?.clear();
  initiateExtendedNuggets._propsCache?.clear();
}

const initiateExtendedNuggets = (markup) => {
  // Step 1: Convert component tags to custom elements with qf-attrs
  const componentRegex = /<(\/?[A-Z]\w*)(\s*\(\{[\s\S]*?}\))?\s*>/g;
  const convertedMarkup = markup.replace(componentRegex, (match, p1, p2) => {
    const isClosing = match.startsWith('</');
    const tagName = p1
      .replace(/([A-Z])/g, '-$1')
      .toLowerCase()
      .replace(/^-/, '');
    
    if (isClosing) {
      return `</${tagName.slice(2)}>`; // keep original closing logic
    }
    
    const attrs = (p2 || '')
      .replace(/\(\{/g, '{')
      .replace(/\}\)/g, '}')
      .replace(/"/g, '`');
    
    return `<${tagName} qf-attrs="${attrs}">`;
  });
  
  // Step 2: Parse into a DocumentFragment
  const range = document.createRange();
  const fragment = range.createContextualFragment(convertedMarkup);
  
  // Props cache (static, shared across calls)
  if (!initiateExtendedNuggets._propsCache) {
    initiateExtendedNuggets._propsCache = new Map();
  }
  
  // Step 3: Iteratively replace all qf-attrs elements (including new ones)
  let hasComponents = true;
  while (hasComponents) {
    hasComponents = false;
    
    // Collect all elements with qf-attrs, deepest first
    const elements = fragment.querySelectorAll('[qf-attrs]');
    if (elements.length === 0) break;
    
    // Convert NodeList to array, sort by depth (descending)
    const sorted = Array.from(elements).sort((a, b) => {
      const depthA = getDepth(a);
      const depthB = getDepth(b);
      return depthB - depthA; // deepest first
    });
    
    for (const element of sorted) {
      // Only process if still in the DOM (could have been replaced by a parent)
      if (!element.parentNode) continue;
      
      const originalTag = element.tagName.toLowerCase()
        .replace(/-([a-z])/g, (_, c) => c.toUpperCase())
        .replace(/^./, m => m.toUpperCase());
      const attrs = element.getAttribute('qf-attrs');
      const content = element.innerHTML;
      const instance = nuggets.get(originalTag);
      
      if (!instance) {
        console.warn(`QueFlow:\nNugget '${originalTag}' is not defined`);
        element.removeAttribute('qf-attrs');
        continue;
      }
      
      // Compile props (cached)
      let data;
      if (initiateExtendedNuggets._propsCache.has(attrs)) {
        data = initiateExtendedNuggets._propsCache.get(attrs);
      } else {
        try {
          data = new Function(`return ${attrs}`)();
          initiateExtendedNuggets._propsCache.set(attrs, data);
        } catch (e) {
          console.warn(`QueFlow:\nFailed to parse props for ${originalTag}: ${e}`);
          element.removeAttribute('qf-attrs');
          continue;
        }
      }
      
      // Render the nugget
      const replacementHTML = renderNugget(instance, data, true, content);
      const replacementFragment = range.createContextualFragment(replacementHTML);
      
      // Replace the element in‑place
      element.parentNode.replaceChild(replacementFragment, element);
      
      // Since we've inserted new DOM, we need to re‑scan in the next while iteration
      hasComponents = true;
    }
  }
  
  // Step 4: Serialize the final fragment
  const div = document.createElement('div');
  div.appendChild(fragment);
  const finalMarkup = div.innerHTML;
  div.remove();
  
  // Step 5: Let normal nuggets be processed
  return initiateNuggets(finalMarkup);
};


const COMPONENT_SELF_CLOSING_REGEX = /<([A-Z]\w*)\s*\/>/g;

function initiateComponents(markup, isNugget, fromAtom) {
  markup = lintPlaceholders(markup, isNugget);
  
  // If not a nugget, replace self-closing component tags with rendered output
  if (!isNugget) {
    markup = markup.replace(COMPONENT_SELF_CLOSING_REGEX, (match, tagName) => {
      const instance = components.get(tagName);
      if (!instance) {
        console.warn(`QueFlow:\nComponent '${tagName}' is not defined, check whether '${tagName}' is correctly spelt or is defined.`);
        return match; // leave original to avoid further breakage
      }
      if (!fromAtom) {
        try {
          return renderComponent(instance, tagName);
        } catch (e) {
          console.warn(`QueFlow:\nAn error occured while rendering Component '${tagName}' \n ${e}, \n\nError sourced from: \`${match}\``);
          return match;
        }
      }
    });
  }
  
  // After components, process nuggets
  markup = initiateNuggets(markup);
  markup = initiateExtendedNuggets(markup);
  
  return lintPlaceholders(markup, isNugget);
}


function g(str, className) {
  const div = document.createElement("div");
  div.innerHTML = str;
  
  const children = div.getElementsByTagName("*");
  
  // Standard for-loop avoids callback overhead
  for (let i = 0, len = children.length; i < len; i++) {
    children[i].classList.add(className);
  }
  
  return div.innerHTML;
}

const lintPlaceholders = (html, isNugget) => {
  const attributeRegex = /\w+\s*=\s*\{\{[^}]+\}\}/g;
  const eventRegex = /on\w+\s*=\s*\{\{(.*?)\}\}/gs;
  
  if (eventRegex.test(html) && !isNugget) {
    html = html.replace(eventRegex, (match) => {
      return match.replaceAll("'", "`").replace("{{", "'").replace(/}}$/, "'");
    });
  }
  
  if (attributeRegex.test(html)) {
    return html.replace(attributeRegex, (match) => {
      return match.replace("{{", '"{{').replace(/}}$/, '}}"');
    });
  }
  return html;
};

const removeEvents = (nodeList, shouldRemove) => {
  for (const child of nodeList) {
    const attributes = getAttributes(child);
    
    for (var { attribute, value } of attributes) {
      if (attribute.slice(0, 2) === "on") {
        const fn = child[attribute];
        child.removeEventListener(attribute, fn);
      }
    }
    
    if (child._qfHandlerKeys) {
      for (const key of child._qfHandlerKeys) {
        eventHandlerCache.delete(key);
      }
      delete child._qfHandlerKeys; // clean up
    }
    
    const qfid = child.getAttribute('data-qfid');
    // Remove from reactive cache
    if (qfid) reactiveCache.delete(qfid);
    if (shouldRemove) child.remove();
  };
  
  clearAllNuggetCaches();
}

const renderComponent = (instance, name, flag) => {
  if (!instance.isMounted) {
    const id = typeof instance.element === 'string' ? instance.element : instance.element.id;
    
    let template = !flag ? `<div id="${id}"> ${(instance.template instanceof Function ? instance.template(instance.data) : instance.template)} </div>` : (instance.template instanceof Function ? instance.template(instance.data) : instance.template);
    
    template = handleRouter(template);
    template = initiateComponents(template);
    
    initiateStyleSheet(`#${id}`, instance);
    const rendered = jsxToHTML(template, instance, name);
    
    instance.dataQF = rendered[1];
    instance.isMounted = true;
    return rendered[0];
  } else {
    return ""
  }
}

class App {
  constructor(selector = "", options = {}) {
    this.element = typeof selector == "string" ?
      document.querySelector(selector) :
      selector;
    
    if (!this.element) {
      throw new Error("QueFlow:\nElement selector '" + selector + "' is invalid");
    }
    
    // Reactive state
    this.data = createSignal(options.data, this);
    let _data = this.data;
    
    this.options = options;
    this.isFrozen = false;
    this.stylesheet = options.stylesheet;
    this.dataQF = [];
    this.onUpdate = options.onUpdate;
    this.created = options.created;
    this.run = options.run || (() => {});
    this.useStrict = Object.keys(options).includes('useStrict') ? options.useStrict : true;
    
    // Batched rendering queue
    this._renderPending = false;
    this._renderScheduled = false;
    
    initiateStyleSheet("", this);
    
    Object.defineProperties(this, {
      template: { value: this.options.template },
      data: {
        get: () => _data,
        set: (data) => {
          if (!isSame(data, this.data) && !this.isFrozen) {
            _data = createSignal(data, this);
            this.dataQF = filterNullElements(this.dataQF);
            // ✅ Schedule a batched render
            this._scheduleRender();
          }
          return true;
        },
        configurable: true
      }
    });
    
    if (this.created) {
      this.created(this.data);
    }
  }
  
  // Schedule a render using microtask – if multiple changes happen
  // synchronously, only one render occurs.
  _scheduleRender() {
    if (!this._renderPending) {
      this._renderPending = true;
      queueMicrotask(() => {
        this._renderPending = false;
        this._doRender();
      });
    }
  }
  
  // The actual render logic, now private
  _doRender() {
    let template = this.template instanceof Function ?
      this.template(this.data) :
      this.template;
    
    template = handleRouter(template);
    template = initiateComponents(template);
    
    // Convert template to HTML (still returns a string)
    const rendered = jsxToHTML(template, this);
    const htmlString = rendered[0];
    
    const fragment = document.createRange().createContextualFragment(htmlString);
    
    // Clear the element efficiently (no innerHTML = '')
    while (this.element.firstChild) {
      this.element.firstChild.remove();
    }
    
    this.element.appendChild(fragment);
    
    currentComponent?.navigateFunc(currentComponent.data);
    
    this.dataQF = rendered[1];
    handleEventListener(this.element, this);
    
    for (const component of components) {
      const instance = component[1];
      if (instance.element) {
        strToEl(instance);
      }
      instance.run(instance.data);
    }
    
    this.run(this.data);
  }
  
  // Force an immediate render (skip batching) – rarely needed
  render() {
    // Cancel any pending microtask to avoid double render
    this._renderPending = false;
    this._doRender();
  }
  
  freeze() {
    this.isFrozen = true;
  }
  
  unfreeze() {
    this.isFrozen = false;
  }
  
  destroy() {
    // ✅ Optimized descendant collection
    const allNodes = [this.element];
    const walker = document.createTreeWalker(
      this.element,
      NodeFilter.SHOW_ELEMENT
    );
    let node;
    while ((node = walker.nextNode())) {
      allNodes.push(node);
    }
    
    removeEvents(allNodes);
    this.element.remove();
  }
}


class Component {
  constructor(name, options = {}) {
    if (name) {
      globalThis[name] = this;
    }
    
    this.name = name;
    this.template = options?.template;
    this.run = options.run || (() => {});
    this.navigateFunc = options.onNavigate || (() => {});
    if (!this.template) throw new Error("QueFlow:\nTemplate not provided for Component " + name);
    
    this.element = `qfEl${counterQF}`; // string ID – later resolved to DOM node
    counterQF++;
    this.isMounted = false;
    
    // Reactive state
    this.data = createSignal(options.data, this);
    let _data = this.data;
    
    this.options = options;
    this.isFrozen = false;
    this.created = options.created;
    this.stylesheet = options.stylesheet;
    this.dataQF = [];
    this.onUpdate = options.onUpdate;
    this.useStrict = Object.keys(options).includes('useStrict') ? options.useStrict : true;
    
    // Batched rendering queue (microtask‑based)
    this._renderPending = false;
    
    // Define data property with batched setter
    Object.defineProperties(this, {
      data: {
        get: () => _data,
        set: (data) => {
          if (!isSame(data, this.data) && !this.isFrozen) {
            _data = createSignal(data, this);
            this.dataQF = filterNullElements(this.dataQF);
            // ✅ Schedule a batched render (microtask)
            this._scheduleRender();
          }
          return true;
        },
        configurable: true
      }
    });
    
    if (this.created) this.created(this.data);
    components.set(name, this);
  }
  
  // Schedule render via microtask – coalesce multiple data changes
  _scheduleRender() {
    if (!this._renderPending) {
      this._renderPending = true;
      queueMicrotask(() => {
        this._renderPending = false;
        // Guard: don't render if the component has been destroyed or unmounted
        if (this.element && this.element.isConnected) {
          renderComponent(this, this.name);
        }
      });
    }
  }
  
  // Force an immediate render (skip batching) – rarely needed
  renderNow() {
    this._renderPending = false; // cancel any queued microtask
    renderComponent(this, this.name);
  }
  
  freeze() {
    this.isFrozen = true;
  }
  
  unfreeze() {
    this.isFrozen = false;
  }
  
  show() {
    // Guard already present – keep it. If element is a string, skip.
    const el = this._resolveElement();
    if (el && el.style.display !== 'block') {
      el.style.display = 'block';
    }
  }
  
  hide() {
    const el = this._resolveElement();
    if (el && el.style.display !== 'none') {
      el.style.display = 'none';
    }
  }
  
  mount() {
    if (!this.isMounted) {
      const rendered = renderComponent(this, this.name, true);
      
      const fragment = document.createRange().createContextualFragment(rendered);
      const el = this._resolveElement();
      if (el) {
        // Clear any existing content quickly
        while (el.firstChild) el.firstChild.remove();
        el.appendChild(fragment);
      }
      handleEventListener(el || this.element, this);
      this.isMounted = true;
    }
  }
  
  destroy() {
    // Descendant collection with TreeWalker
    const el = this._resolveElement();
    if (!el) return;
    
    const allNodes = [el];
    const walker = document.createTreeWalker(el, NodeFilter.SHOW_ELEMENT);
    let node;
    while ((node = walker.nextNode())) {
      allNodes.push(node);
    }
    removeEvents(allNodes);
    el.remove();
  }
  
  _resolveElement() {
    if (typeof this.element === 'string') {
      return document.querySelector(`[qfid="${this.element}"]`) || null;
    }
    return this.element;
  }
}

function addIndexToTemplate(str, index) {
  const regex = /\{\{[^\{\{]+\}\}/g;
  const output = str.replace(regex, (match) => {
    const inner = b(match).trim();
    return `{{ this.data[${index}].${inner} }}`;
  });
  return lintPlaceholders(output);
}

function stringToDocumentFragment(htmlString = "") {
  /**
   * Converts an HTML string into a DocumentFragment.
   *
   * @param {string} htmlString - The HTML string to convert.
   * @returns {DocumentFragment} - The DocumentFragment containing the parsed HTML.
   */
  if (typeof htmlString !== 'string') {
    throw new TypeError('Input must be a string.');
  }
  
  const template = document.createElement('template');
  template.innerHTML = htmlString;
  return template.content.cloneNode(true); // Clone to avoid template content issues
}

class Atom {
  constructor(name, options, id) {
    globalThis[name] = this;
    this.element = id;
    this.name = name;
    this.template = options.template;
    this.stylesheet = options.stylesheet;
    initiateStyleSheet(`#${id}`, this);
    this.data = [];
    this.index = 0;
    this.dataQF = [];
    this.useStrict = true;
    this.isReactive = options.isReactive;
    this.created = typeof options.created == "function" ? options.created(this) : 0;
  }
  
  // Resolve string ID to DOM element once and cache it
  _getElement() {
    if (typeof this.element === "string") {
      this.element = document.getElementById(this.element);
      if (!this.element) throw new Error(`Mount node of '${this.name}' is invalid or not provided`);
    }
    return this.element;
  }
  
  // Optionally clear the container (if needed externally)
  destroy() {
    const el = this._getElement();
    removeEvents([el.firstChild, ...el.firstChild.querySelectorAll('*')]);
    el.firstChild.remove();
    
    this.data = [];
    this.dataQF = [];
  }
  
  renderWith(data, position = "append") {
    if (typeof data !== "object")
      throw new Error(`First argument passed to '${this.name}.renderWith()' must be an object or an array.`);
    
    const el = this._getElement();
    const dataArray = Array.isArray(data) ? data : [data];
    if (dataArray.length === 0) return;
    
    this.data = dataArray.slice(); // shallow copy
    
    // Build one combined HTML string from all items
    let combinedHTML = '';
    
    for (let i = 0; i < dataArray.length; i++) {
      const item = dataArray[i];
      const rawTemplate = typeof this.template === "function" ?
        this.template(item, i) :
        this.template;
      
      const indexedTemplate = addIndexToTemplate(rawTemplate, i);
      
      if (this.isReactive) {
        // Expand components/nuggets before concatenation
        combinedHTML += initiateComponents(indexedTemplate, false, true);
      } else {
        // Non‑reactive: simple placeholder replacement + linting
        let rendered = renderTemplate(indexedTemplate, item, true);
        rendered = initiateNuggets(rendered);
        rendered = initiateExtendedNuggets(rendered);
        const linted = lintPlaceholders(rendered, true);
        combinedHTML += linted;
      }
    }
    
    // Single parse & reactive processing
    const [htmlContent, compData] = jsxToHTML(combinedHTML, this, null);
    const fragment = stringToDocumentFragment(htmlContent);
    
    // Insert once
    if (position === "append") {
      el.appendChild(fragment);
    } else {
      el.prepend(fragment);
    }
    
    handleEventListener(el, this);
    
    if (this.isReactive) {
      this.dataQF.push(...compData);
    }
  }
  
  set(index, value, allowShallow) {
    if (!this.isReactive) throw new Error(`Cannot call 'set()' on Atom ${this.name}.\n\n${this.name} is not a reactive Atom`);
    
    // ---- Apply data changes synchronously ----
    if (typeof index === "number") {
      if (allowShallow) {
        // Shallow merge: update only the given keys in the existing data object
        const target = this.data[index];
        if (target && typeof target === "object") {
          Object.keys(value).forEach(key => {
            if (target[key] !== value[key]) target[key] = value[key];
          });
        } else {
          this.data[index] = value;
        }
      } else {
        this.data[index] = value;
      }
    } else if (Array.isArray(index)) {
      this.data = index;
    } else {
      console.warn(`First Argument passed to '${this.name}.set()' must either be a number or an array.`);
      return;
    }
    
    updateComponent("_", this);
  }
}

const renderNugget = (instance, data, isExtended, children) => {
  if (instance) {
    const className = instance.className;
    // Create a variable that holds the template 
    let template = instance.template instanceof Function ? instance.template(data) : instance.template;
    
    if (isExtended) {
      template = template.replaceAll("</>", children);
    }
    
    // Parse and initiate Nested Nuggets
    const initiated = initiateNuggets(template, true);
    
    // Render parsed html
    let rendered = renderTemplate(initiated, data);
    
    const html = g(rendered, className);
    
    if (!instance.stylesheetInitiated) {
      // Initiate stylesheet for instance 
      initiateStyleSheet("." + className, instance, true);
      instance.stylesheetInitiated = true;
    }
    
    // Return processed html
    return html;
  }
}

class Nugget {
  /**
   * A class for creating reusable UI components
   * @param {Object} options    An object containing all required options for the component
   */
  
  constructor(name, options = {}) {
    if (name) {
      globalThis[name] = this;
    }
    // Stores instanc's stylesheet 
    this.stylesheet = options.stylesheet ?? {};
    
    // Create a property that generates a unique className for instance's parent element
    this.className = `nugget${nuggetCounter}`;
    // Increment the counterQF variable for later use
    nuggetCounter++;
    // Stores template 
    this.template = options.template;
    this.stylesheetInitiated = false;
    nuggets.set(name, this)
  }
  
  destroy() {
    const all = document.querySelectorAll(`.${this.className}`);
    // Remove elements and their events from the DOM
    removeEvents(all, true);
  }
}

globalThis.toPage = (path) => {
  history.pushState({}, '', path);
  loadComponent(path)
}

const loadComponent = (path) => {
  const len = routerObj.length;
  let comp404 = '';
  
  const changeView = (name, title) => {
    const instance = components.get(name);
    currentComponent?.hide();
    if (instance.isMounted) {
      instance.show();
    } else {
      instance.mount();
      instance.show();
    }
    document.title = title;
    currentComponent = instance;
    currentComponent.navigateFunc(currentComponent.data);
  }
  
  for (let i = 0; i < len; i++) {
    const { component, route, title } = routerObj[i];
    if (route === "*") {
      comp404 = component;
    }
    if (route === path) {
      changeView(component, title);
      break;
    } else {
      if (i === len - 1) {
        changeView(comp404, title)
      }
    }
  }
  navigateFunc(path);
  window.scrollTo(0, 0);
}


const Link = new Nugget('Link', {
  template: (data) => {
    const classN = data.class ? 'class={{ class }}' : '';
    return `
      <a href={{ to }} ${ classN } onclick="
        e.preventDefault()
        toPage('{{ to }}')">${ data.isBtn ? '<button>{{ label }}</button>' : '{{ label }}' }</a>`
  }
})

function handleRouter(input) {
  const routerReg = /<(Router)\s*\{([\s\S]*?)\}\s*\/>/g;
  let out = '',
    computed = '';
  
  if (routerReg.test(input)) {
    const extr = input.match(routerReg)[0],
      whiteSpaceIndex = extr.indexOf(" "),
      d = extr.slice(whiteSpaceIndex, -2).trim(),
      path = window.location.pathname;
    const data = Function(`return ${d}.routes`)(),
      len = data.length;
    
    let comp404 = '',
      isSet = false;
    
    computed = data.map(({ route, component }, i) => {
      data[i].component = stringBetween(component, " <", "/>");
      
      const name = data[i].component;
      const title = data[i].title;
      if (!title) {
        throw new Error(`QueFlow Router Error:\nTitle not set for component '${ name }'`)
      }
      
      let instance = components.get(name);
      
      if (!instance) throw new Error(`\n\nQueFlow Router Error:\nAn error occured while rendering component '${name}'`);
      
      if (route === "*") {
        comp404 = name;
      }
      
      if (route === path) {
        isSet = true;
        currentComponent = instance;
        document.title = title;
        return renderComponent(instance, name);
      } else {
        if (i === len - 1 && !isSet) {
          instance = components.get(comp404);
          currentComponent = instance;
          document.title = title;
          return renderComponent(instance, comp404);
        } else {
          const id = instance.element;
          return `<div id="${id}" display="none"></div>`;
        }
      }
    }).join('');
    routerObj = data;
    out = input.replace(extr, computed);
  } else {
    return input;
  }
  
  window.addEventListener('popstate', () => {
    const path = window.location.pathname;
    loadComponent(path);
  });
  
  return out;
}

const onNavigate = (func, instance) => {
  navigateFunc = func.bind(instance);
}

export {
  App,
  Component,
  Nugget,
  Atom,
  onNavigate,
  globalState
};