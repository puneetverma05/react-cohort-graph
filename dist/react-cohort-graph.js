(function (global, factory) {
  typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory(require('react')) :
  typeof define === 'function' && define.amd ? define(['react'], factory) :
  (global = global || self, global.ReactCohortGraph = factory(global.React));
}(this, (function (React) { 'use strict';

  React = React && Object.prototype.hasOwnProperty.call(React, 'default') ? React['default'] : React;

  function ownKeys(object, enumerableOnly) {
    var keys = Object.keys(object);

    if (Object.getOwnPropertySymbols) {
      var symbols = Object.getOwnPropertySymbols(object);
      enumerableOnly && (symbols = symbols.filter(function (sym) {
        return Object.getOwnPropertyDescriptor(object, sym).enumerable;
      })), keys.push.apply(keys, symbols);
    }

    return keys;
  }

  function _objectSpread2(target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = null != arguments[i] ? arguments[i] : {};
      i % 2 ? ownKeys(Object(source), !0).forEach(function (key) {
        _defineProperty(target, key, source[key]);
      }) : Object.getOwnPropertyDescriptors ? Object.defineProperties(target, Object.getOwnPropertyDescriptors(source)) : ownKeys(Object(source)).forEach(function (key) {
        Object.defineProperty(target, key, Object.getOwnPropertyDescriptor(source, key));
      });
    }

    return target;
  }

  function _typeof(obj) {
    "@babel/helpers - typeof";

    return _typeof = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (obj) {
      return typeof obj;
    } : function (obj) {
      return obj && "function" == typeof Symbol && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
    }, _typeof(obj);
  }

  function _classCallCheck(instance, Constructor) {
    if (!(instance instanceof Constructor)) {
      throw new TypeError("Cannot call a class as a function");
    }
  }

  function _defineProperties(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i];
      descriptor.enumerable = descriptor.enumerable || false;
      descriptor.configurable = true;
      if ("value" in descriptor) descriptor.writable = true;
      Object.defineProperty(target, descriptor.key, descriptor);
    }
  }

  function _createClass(Constructor, protoProps, staticProps) {
    if (protoProps) _defineProperties(Constructor.prototype, protoProps);
    if (staticProps) _defineProperties(Constructor, staticProps);
    Object.defineProperty(Constructor, "prototype", {
      writable: false
    });
    return Constructor;
  }

  function _defineProperty(obj, key, value) {
    if (key in obj) {
      Object.defineProperty(obj, key, {
        value: value,
        enumerable: true,
        configurable: true,
        writable: true
      });
    } else {
      obj[key] = value;
    }

    return obj;
  }

  function _extends() {
    _extends = Object.assign ? Object.assign.bind() : function (target) {
      for (var i = 1; i < arguments.length; i++) {
        var source = arguments[i];

        for (var key in source) {
          if (Object.prototype.hasOwnProperty.call(source, key)) {
            target[key] = source[key];
          }
        }
      }

      return target;
    };
    return _extends.apply(this, arguments);
  }

  function _inherits(subClass, superClass) {
    if (typeof superClass !== "function" && superClass !== null) {
      throw new TypeError("Super expression must either be null or a function");
    }

    subClass.prototype = Object.create(superClass && superClass.prototype, {
      constructor: {
        value: subClass,
        writable: true,
        configurable: true
      }
    });
    Object.defineProperty(subClass, "prototype", {
      writable: false
    });
    if (superClass) _setPrototypeOf(subClass, superClass);
  }

  function _getPrototypeOf(o) {
    _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function _getPrototypeOf(o) {
      return o.__proto__ || Object.getPrototypeOf(o);
    };
    return _getPrototypeOf(o);
  }

  function _setPrototypeOf(o, p) {
    _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function _setPrototypeOf(o, p) {
      o.__proto__ = p;
      return o;
    };
    return _setPrototypeOf(o, p);
  }

  function _isNativeReflectConstruct() {
    if (typeof Reflect === "undefined" || !Reflect.construct) return false;
    if (Reflect.construct.sham) return false;
    if (typeof Proxy === "function") return true;

    try {
      Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {}));
      return true;
    } catch (e) {
      return false;
    }
  }

  function _objectWithoutPropertiesLoose(source, excluded) {
    if (source == null) return {};
    var target = {};
    var sourceKeys = Object.keys(source);
    var key, i;

    for (i = 0; i < sourceKeys.length; i++) {
      key = sourceKeys[i];
      if (excluded.indexOf(key) >= 0) continue;
      target[key] = source[key];
    }

    return target;
  }

  function _objectWithoutProperties(source, excluded) {
    if (source == null) return {};

    var target = _objectWithoutPropertiesLoose(source, excluded);

    var key, i;

    if (Object.getOwnPropertySymbols) {
      var sourceSymbolKeys = Object.getOwnPropertySymbols(source);

      for (i = 0; i < sourceSymbolKeys.length; i++) {
        key = sourceSymbolKeys[i];
        if (excluded.indexOf(key) >= 0) continue;
        if (!Object.prototype.propertyIsEnumerable.call(source, key)) continue;
        target[key] = source[key];
      }
    }

    return target;
  }

  function _assertThisInitialized(self) {
    if (self === void 0) {
      throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
    }

    return self;
  }

  function _possibleConstructorReturn(self, call) {
    if (call && (typeof call === "object" || typeof call === "function")) {
      return call;
    } else if (call !== void 0) {
      throw new TypeError("Derived constructors may only return object or undefined");
    }

    return _assertThisInitialized(self);
  }

  function _createSuper(Derived) {
    var hasNativeReflectConstruct = _isNativeReflectConstruct();

    return function _createSuperInternal() {
      var Super = _getPrototypeOf(Derived),
          result;

      if (hasNativeReflectConstruct) {
        var NewTarget = _getPrototypeOf(this).constructor;

        result = Reflect.construct(Super, arguments, NewTarget);
      } else {
        result = Super.apply(this, arguments);
      }

      return _possibleConstructorReturn(this, result);
    };
  }

  function _toConsumableArray(arr) {
    return _arrayWithoutHoles(arr) || _iterableToArray(arr) || _unsupportedIterableToArray(arr) || _nonIterableSpread();
  }

  function _arrayWithoutHoles(arr) {
    if (Array.isArray(arr)) return _arrayLikeToArray(arr);
  }

  function _iterableToArray(iter) {
    if (typeof Symbol !== "undefined" && iter[Symbol.iterator] != null || iter["@@iterator"] != null) return Array.from(iter);
  }

  function _unsupportedIterableToArray(o, minLen) {
    if (!o) return;
    if (typeof o === "string") return _arrayLikeToArray(o, minLen);
    var n = Object.prototype.toString.call(o).slice(8, -1);
    if (n === "Object" && o.constructor) n = o.constructor.name;
    if (n === "Map" || n === "Set") return Array.from(o);
    if (n === "Arguments" || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)) return _arrayLikeToArray(o, minLen);
  }

  function _arrayLikeToArray(arr, len) {
    if (len == null || len > arr.length) len = arr.length;

    for (var i = 0, arr2 = new Array(len); i < len; i++) arr2[i] = arr[i];

    return arr2;
  }

  function _nonIterableSpread() {
    throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.");
  }

  function createCommonjsModule(fn, module) {
  	return module = { exports: {} }, fn(module, module.exports), module.exports;
  }

  var reactIs_development = createCommonjsModule(function (module, exports) {



  {
    (function() {

  // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
  // nor polyfill, then a plain number is used for performance.
  var hasSymbol = typeof Symbol === 'function' && Symbol.for;
  var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
  var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
  var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
  var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
  var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
  var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
  var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
  // (unstable) APIs that have been removed. Can we remove the symbols?

  var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
  var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
  var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
  var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
  var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
  var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
  var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
  var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
  var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
  var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
  var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

  function isValidElementType(type) {
    return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
    type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
  }

  function typeOf(object) {
    if (typeof object === 'object' && object !== null) {
      var $$typeof = object.$$typeof;

      switch ($$typeof) {
        case REACT_ELEMENT_TYPE:
          var type = object.type;

          switch (type) {
            case REACT_ASYNC_MODE_TYPE:
            case REACT_CONCURRENT_MODE_TYPE:
            case REACT_FRAGMENT_TYPE:
            case REACT_PROFILER_TYPE:
            case REACT_STRICT_MODE_TYPE:
            case REACT_SUSPENSE_TYPE:
              return type;

            default:
              var $$typeofType = type && type.$$typeof;

              switch ($$typeofType) {
                case REACT_CONTEXT_TYPE:
                case REACT_FORWARD_REF_TYPE:
                case REACT_LAZY_TYPE:
                case REACT_MEMO_TYPE:
                case REACT_PROVIDER_TYPE:
                  return $$typeofType;

                default:
                  return $$typeof;
              }

          }

        case REACT_PORTAL_TYPE:
          return $$typeof;
      }
    }

    return undefined;
  } // AsyncMode is deprecated along with isAsyncMode

  var AsyncMode = REACT_ASYNC_MODE_TYPE;
  var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
  var ContextConsumer = REACT_CONTEXT_TYPE;
  var ContextProvider = REACT_PROVIDER_TYPE;
  var Element = REACT_ELEMENT_TYPE;
  var ForwardRef = REACT_FORWARD_REF_TYPE;
  var Fragment = REACT_FRAGMENT_TYPE;
  var Lazy = REACT_LAZY_TYPE;
  var Memo = REACT_MEMO_TYPE;
  var Portal = REACT_PORTAL_TYPE;
  var Profiler = REACT_PROFILER_TYPE;
  var StrictMode = REACT_STRICT_MODE_TYPE;
  var Suspense = REACT_SUSPENSE_TYPE;
  var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

  function isAsyncMode(object) {
    {
      if (!hasWarnedAboutDeprecatedIsAsyncMode) {
        hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

        console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
      }
    }

    return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
  }
  function isConcurrentMode(object) {
    return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
  }
  function isContextConsumer(object) {
    return typeOf(object) === REACT_CONTEXT_TYPE;
  }
  function isContextProvider(object) {
    return typeOf(object) === REACT_PROVIDER_TYPE;
  }
  function isElement(object) {
    return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
  }
  function isForwardRef(object) {
    return typeOf(object) === REACT_FORWARD_REF_TYPE;
  }
  function isFragment(object) {
    return typeOf(object) === REACT_FRAGMENT_TYPE;
  }
  function isLazy(object) {
    return typeOf(object) === REACT_LAZY_TYPE;
  }
  function isMemo(object) {
    return typeOf(object) === REACT_MEMO_TYPE;
  }
  function isPortal(object) {
    return typeOf(object) === REACT_PORTAL_TYPE;
  }
  function isProfiler(object) {
    return typeOf(object) === REACT_PROFILER_TYPE;
  }
  function isStrictMode(object) {
    return typeOf(object) === REACT_STRICT_MODE_TYPE;
  }
  function isSuspense(object) {
    return typeOf(object) === REACT_SUSPENSE_TYPE;
  }

  exports.AsyncMode = AsyncMode;
  exports.ConcurrentMode = ConcurrentMode;
  exports.ContextConsumer = ContextConsumer;
  exports.ContextProvider = ContextProvider;
  exports.Element = Element;
  exports.ForwardRef = ForwardRef;
  exports.Fragment = Fragment;
  exports.Lazy = Lazy;
  exports.Memo = Memo;
  exports.Portal = Portal;
  exports.Profiler = Profiler;
  exports.StrictMode = StrictMode;
  exports.Suspense = Suspense;
  exports.isAsyncMode = isAsyncMode;
  exports.isConcurrentMode = isConcurrentMode;
  exports.isContextConsumer = isContextConsumer;
  exports.isContextProvider = isContextProvider;
  exports.isElement = isElement;
  exports.isForwardRef = isForwardRef;
  exports.isFragment = isFragment;
  exports.isLazy = isLazy;
  exports.isMemo = isMemo;
  exports.isPortal = isPortal;
  exports.isProfiler = isProfiler;
  exports.isStrictMode = isStrictMode;
  exports.isSuspense = isSuspense;
  exports.isValidElementType = isValidElementType;
  exports.typeOf = typeOf;
    })();
  }
  });
  var reactIs_development_1 = reactIs_development.AsyncMode;
  var reactIs_development_2 = reactIs_development.ConcurrentMode;
  var reactIs_development_3 = reactIs_development.ContextConsumer;
  var reactIs_development_4 = reactIs_development.ContextProvider;
  var reactIs_development_5 = reactIs_development.Element;
  var reactIs_development_6 = reactIs_development.ForwardRef;
  var reactIs_development_7 = reactIs_development.Fragment;
  var reactIs_development_8 = reactIs_development.Lazy;
  var reactIs_development_9 = reactIs_development.Memo;
  var reactIs_development_10 = reactIs_development.Portal;
  var reactIs_development_11 = reactIs_development.Profiler;
  var reactIs_development_12 = reactIs_development.StrictMode;
  var reactIs_development_13 = reactIs_development.Suspense;
  var reactIs_development_14 = reactIs_development.isAsyncMode;
  var reactIs_development_15 = reactIs_development.isConcurrentMode;
  var reactIs_development_16 = reactIs_development.isContextConsumer;
  var reactIs_development_17 = reactIs_development.isContextProvider;
  var reactIs_development_18 = reactIs_development.isElement;
  var reactIs_development_19 = reactIs_development.isForwardRef;
  var reactIs_development_20 = reactIs_development.isFragment;
  var reactIs_development_21 = reactIs_development.isLazy;
  var reactIs_development_22 = reactIs_development.isMemo;
  var reactIs_development_23 = reactIs_development.isPortal;
  var reactIs_development_24 = reactIs_development.isProfiler;
  var reactIs_development_25 = reactIs_development.isStrictMode;
  var reactIs_development_26 = reactIs_development.isSuspense;
  var reactIs_development_27 = reactIs_development.isValidElementType;
  var reactIs_development_28 = reactIs_development.typeOf;

  var reactIs = createCommonjsModule(function (module) {

  {
    module.exports = reactIs_development;
  }
  });

  /*
  object-assign
  (c) Sindre Sorhus
  @license MIT
  */
  /* eslint-disable no-unused-vars */
  var getOwnPropertySymbols = Object.getOwnPropertySymbols;
  var hasOwnProperty = Object.prototype.hasOwnProperty;
  var propIsEnumerable = Object.prototype.propertyIsEnumerable;

  function toObject(val) {
  	if (val === null || val === undefined) {
  		throw new TypeError('Object.assign cannot be called with null or undefined');
  	}

  	return Object(val);
  }

  function shouldUseNative() {
  	try {
  		if (!Object.assign) {
  			return false;
  		}

  		// Detect buggy property enumeration order in older V8 versions.

  		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
  		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
  		test1[5] = 'de';
  		if (Object.getOwnPropertyNames(test1)[0] === '5') {
  			return false;
  		}

  		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
  		var test2 = {};
  		for (var i = 0; i < 10; i++) {
  			test2['_' + String.fromCharCode(i)] = i;
  		}
  		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
  			return test2[n];
  		});
  		if (order2.join('') !== '0123456789') {
  			return false;
  		}

  		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
  		var test3 = {};
  		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
  			test3[letter] = letter;
  		});
  		if (Object.keys(Object.assign({}, test3)).join('') !==
  				'abcdefghijklmnopqrst') {
  			return false;
  		}

  		return true;
  	} catch (err) {
  		// We don't expect any of the above to throw, but better to be safe.
  		return false;
  	}
  }

  var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
  	var from;
  	var to = toObject(target);
  	var symbols;

  	for (var s = 1; s < arguments.length; s++) {
  		from = Object(arguments[s]);

  		for (var key in from) {
  			if (hasOwnProperty.call(from, key)) {
  				to[key] = from[key];
  			}
  		}

  		if (getOwnPropertySymbols) {
  			symbols = getOwnPropertySymbols(from);
  			for (var i = 0; i < symbols.length; i++) {
  				if (propIsEnumerable.call(from, symbols[i])) {
  					to[symbols[i]] = from[symbols[i]];
  				}
  			}
  		}
  	}

  	return to;
  };

  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

  var ReactPropTypesSecret_1 = ReactPropTypesSecret;

  var has = Function.call.bind(Object.prototype.hasOwnProperty);

  var printWarning = function() {};

  {
    var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
    var loggedTypeFailures = {};
    var has$1 = has;

    printWarning = function(text) {
      var message = 'Warning: ' + text;
      if (typeof console !== 'undefined') {
        console.error(message);
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message);
      } catch (x) { /**/ }
    };
  }

  /**
   * Assert that the values match with the type specs.
   * Error messages are memorized and will only be shown once.
   *
   * @param {object} typeSpecs Map of name to a ReactPropType
   * @param {object} values Runtime values that need to be type-checked
   * @param {string} location e.g. "prop", "context", "child context"
   * @param {string} componentName Name of the component for error messages.
   * @param {?Function} getStack Returns the component stack.
   * @private
   */
  function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
    {
      for (var typeSpecName in typeSpecs) {
        if (has$1(typeSpecs, typeSpecName)) {
          var error;
          // Prop type validation may throw. In case they do, we don't want to
          // fail the render phase where it didn't fail before. So we log it.
          // After these have been cleaned up, we'll let them throw.
          try {
            // This is intentionally an invariant that gets caught. It's the same
            // behavior as without this statement except with a better message.
            if (typeof typeSpecs[typeSpecName] !== 'function') {
              var err = Error(
                (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
                'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' +
                'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.'
              );
              err.name = 'Invariant Violation';
              throw err;
            }
            error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
          } catch (ex) {
            error = ex;
          }
          if (error && !(error instanceof Error)) {
            printWarning(
              (componentName || 'React class') + ': type specification of ' +
              location + ' `' + typeSpecName + '` is invalid; the type checker ' +
              'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
              'You may have forgotten to pass an argument to the type checker ' +
              'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
              'shape all require an argument).'
            );
          }
          if (error instanceof Error && !(error.message in loggedTypeFailures)) {
            // Only monitor this failure once because there tends to be a lot of the
            // same error.
            loggedTypeFailures[error.message] = true;

            var stack = getStack ? getStack() : '';

            printWarning(
              'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
            );
          }
        }
      }
    }
  }

  /**
   * Resets warning cache when testing.
   *
   * @private
   */
  checkPropTypes.resetWarningCache = function() {
    {
      loggedTypeFailures = {};
    }
  };

  var checkPropTypes_1 = checkPropTypes;

  var printWarning$1 = function() {};

  {
    printWarning$1 = function(text) {
      var message = 'Warning: ' + text;
      if (typeof console !== 'undefined') {
        console.error(message);
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message);
      } catch (x) {}
    };
  }

  function emptyFunctionThatReturnsNull() {
    return null;
  }

  var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
    /* global Symbol */
    var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
    var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

    /**
     * Returns the iterator method function contained on the iterable object.
     *
     * Be sure to invoke the function with the iterable as context:
     *
     *     var iteratorFn = getIteratorFn(myIterable);
     *     if (iteratorFn) {
     *       var iterator = iteratorFn.call(myIterable);
     *       ...
     *     }
     *
     * @param {?object} maybeIterable
     * @return {?function}
     */
    function getIteratorFn(maybeIterable) {
      var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
      if (typeof iteratorFn === 'function') {
        return iteratorFn;
      }
    }

    /**
     * Collection of methods that allow declaration and validation of props that are
     * supplied to React components. Example usage:
     *
     *   var Props = require('ReactPropTypes');
     *   var MyArticle = React.createClass({
     *     propTypes: {
     *       // An optional string prop named "description".
     *       description: Props.string,
     *
     *       // A required enum prop named "category".
     *       category: Props.oneOf(['News','Photos']).isRequired,
     *
     *       // A prop named "dialog" that requires an instance of Dialog.
     *       dialog: Props.instanceOf(Dialog).isRequired
     *     },
     *     render: function() { ... }
     *   });
     *
     * A more formal specification of how these methods are used:
     *
     *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
     *   decl := ReactPropTypes.{type}(.isRequired)?
     *
     * Each and every declaration produces a function with the same signature. This
     * allows the creation of custom validation functions. For example:
     *
     *  var MyLink = React.createClass({
     *    propTypes: {
     *      // An optional string or URI prop named "href".
     *      href: function(props, propName, componentName) {
     *        var propValue = props[propName];
     *        if (propValue != null && typeof propValue !== 'string' &&
     *            !(propValue instanceof URI)) {
     *          return new Error(
     *            'Expected a string or an URI for ' + propName + ' in ' +
     *            componentName
     *          );
     *        }
     *      }
     *    },
     *    render: function() {...}
     *  });
     *
     * @internal
     */

    var ANONYMOUS = '<<anonymous>>';

    // Important!
    // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
    var ReactPropTypes = {
      array: createPrimitiveTypeChecker('array'),
      bigint: createPrimitiveTypeChecker('bigint'),
      bool: createPrimitiveTypeChecker('boolean'),
      func: createPrimitiveTypeChecker('function'),
      number: createPrimitiveTypeChecker('number'),
      object: createPrimitiveTypeChecker('object'),
      string: createPrimitiveTypeChecker('string'),
      symbol: createPrimitiveTypeChecker('symbol'),

      any: createAnyTypeChecker(),
      arrayOf: createArrayOfTypeChecker,
      element: createElementTypeChecker(),
      elementType: createElementTypeTypeChecker(),
      instanceOf: createInstanceTypeChecker,
      node: createNodeChecker(),
      objectOf: createObjectOfTypeChecker,
      oneOf: createEnumTypeChecker,
      oneOfType: createUnionTypeChecker,
      shape: createShapeTypeChecker,
      exact: createStrictShapeTypeChecker,
    };

    /**
     * inlined Object.is polyfill to avoid requiring consumers ship their own
     * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
     */
    /*eslint-disable no-self-compare*/
    function is(x, y) {
      // SameValue algorithm
      if (x === y) {
        // Steps 1-5, 7-10
        // Steps 6.b-6.e: +0 != -0
        return x !== 0 || 1 / x === 1 / y;
      } else {
        // Step 6.a: NaN == NaN
        return x !== x && y !== y;
      }
    }
    /*eslint-enable no-self-compare*/

    /**
     * We use an Error-like object for backward compatibility as people may call
     * PropTypes directly and inspect their output. However, we don't use real
     * Errors anymore. We don't inspect their stack anyway, and creating them
     * is prohibitively expensive if they are created too often, such as what
     * happens in oneOfType() for any type before the one that matched.
     */
    function PropTypeError(message, data) {
      this.message = message;
      this.data = data && typeof data === 'object' ? data: {};
      this.stack = '';
    }
    // Make `instanceof Error` still work for returned errors.
    PropTypeError.prototype = Error.prototype;

    function createChainableTypeChecker(validate) {
      {
        var manualPropTypeCallCache = {};
        var manualPropTypeWarningCount = 0;
      }
      function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
        componentName = componentName || ANONYMOUS;
        propFullName = propFullName || propName;

        if (secret !== ReactPropTypesSecret_1) {
          if (throwOnDirectAccess) {
            // New behavior only for users of `prop-types` package
            var err = new Error(
              'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
              'Use `PropTypes.checkPropTypes()` to call them. ' +
              'Read more at http://fb.me/use-check-prop-types'
            );
            err.name = 'Invariant Violation';
            throw err;
          } else if ( typeof console !== 'undefined') {
            // Old behavior for people using React.PropTypes
            var cacheKey = componentName + ':' + propName;
            if (
              !manualPropTypeCallCache[cacheKey] &&
              // Avoid spamming the console because they are often not actionable except for lib authors
              manualPropTypeWarningCount < 3
            ) {
              printWarning$1(
                'You are manually calling a React.PropTypes validation ' +
                'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' +
                'and will throw in the standalone `prop-types` package. ' +
                'You may be seeing this warning due to a third-party PropTypes ' +
                'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
              );
              manualPropTypeCallCache[cacheKey] = true;
              manualPropTypeWarningCount++;
            }
          }
        }
        if (props[propName] == null) {
          if (isRequired) {
            if (props[propName] === null) {
              return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
            }
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
          }
          return null;
        } else {
          return validate(props, propName, componentName, location, propFullName);
        }
      }

      var chainedCheckType = checkType.bind(null, false);
      chainedCheckType.isRequired = checkType.bind(null, true);

      return chainedCheckType;
    }

    function createPrimitiveTypeChecker(expectedType) {
      function validate(props, propName, componentName, location, propFullName, secret) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== expectedType) {
          // `propValue` being instance of, say, date/regexp, pass the 'object'
          // check, but we can offer a more precise error message here rather than
          // 'of type `object`'.
          var preciseType = getPreciseType(propValue);

          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'),
            {expectedType: expectedType}
          );
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createAnyTypeChecker() {
      return createChainableTypeChecker(emptyFunctionThatReturnsNull);
    }

    function createArrayOfTypeChecker(typeChecker) {
      function validate(props, propName, componentName, location, propFullName) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
        }
        var propValue = props[propName];
        if (!Array.isArray(propValue)) {
          var propType = getPropType(propValue);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
        }
        for (var i = 0; i < propValue.length; i++) {
          var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createElementTypeChecker() {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        if (!isValidElement(propValue)) {
          var propType = getPropType(propValue);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createElementTypeTypeChecker() {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        if (!reactIs.isValidElementType(propValue)) {
          var propType = getPropType(propValue);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createInstanceTypeChecker(expectedClass) {
      function validate(props, propName, componentName, location, propFullName) {
        if (!(props[propName] instanceof expectedClass)) {
          var expectedClassName = expectedClass.name || ANONYMOUS;
          var actualClassName = getClassName(props[propName]);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createEnumTypeChecker(expectedValues) {
      if (!Array.isArray(expectedValues)) {
        {
          if (arguments.length > 1) {
            printWarning$1(
              'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
              'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
            );
          } else {
            printWarning$1('Invalid argument supplied to oneOf, expected an array.');
          }
        }
        return emptyFunctionThatReturnsNull;
      }

      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        for (var i = 0; i < expectedValues.length; i++) {
          if (is(propValue, expectedValues[i])) {
            return null;
          }
        }

        var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
          var type = getPreciseType(value);
          if (type === 'symbol') {
            return String(value);
          }
          return value;
        });
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
      }
      return createChainableTypeChecker(validate);
    }

    function createObjectOfTypeChecker(typeChecker) {
      function validate(props, propName, componentName, location, propFullName) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
        }
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
        }
        for (var key in propValue) {
          if (has(propValue, key)) {
            var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
            if (error instanceof Error) {
              return error;
            }
          }
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createUnionTypeChecker(arrayOfTypeCheckers) {
      if (!Array.isArray(arrayOfTypeCheckers)) {
         printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') ;
        return emptyFunctionThatReturnsNull;
      }

      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (typeof checker !== 'function') {
          printWarning$1(
            'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
            'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
          );
          return emptyFunctionThatReturnsNull;
        }
      }

      function validate(props, propName, componentName, location, propFullName) {
        var expectedTypes = [];
        for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
          var checker = arrayOfTypeCheckers[i];
          var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1);
          if (checkerResult == null) {
            return null;
          }
          if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
            expectedTypes.push(checkerResult.data.expectedType);
          }
        }
        var expectedTypesMessage = (expectedTypes.length > 0) ? ', expected one of type [' + expectedTypes.join(', ') + ']': '';
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
      }
      return createChainableTypeChecker(validate);
    }

    function createNodeChecker() {
      function validate(props, propName, componentName, location, propFullName) {
        if (!isNode(props[propName])) {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function invalidValidatorError(componentName, location, propFullName, key, type) {
      return new PropTypeError(
        (componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' +
        'it must be a function, usually from the `prop-types` package, but received `' + type + '`.'
      );
    }

    function createShapeTypeChecker(shapeTypes) {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
        }
        for (var key in shapeTypes) {
          var checker = shapeTypes[key];
          if (typeof checker !== 'function') {
            return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
          }
          var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error) {
            return error;
          }
        }
        return null;
      }
      return createChainableTypeChecker(validate);
    }

    function createStrictShapeTypeChecker(shapeTypes) {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
        }
        // We need to check all keys in case some are required but missing from props.
        var allKeys = objectAssign({}, props[propName], shapeTypes);
        for (var key in allKeys) {
          var checker = shapeTypes[key];
          if (has(shapeTypes, key) && typeof checker !== 'function') {
            return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
          }
          if (!checker) {
            return new PropTypeError(
              'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
              '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
              '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  ')
            );
          }
          var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error) {
            return error;
          }
        }
        return null;
      }

      return createChainableTypeChecker(validate);
    }

    function isNode(propValue) {
      switch (typeof propValue) {
        case 'number':
        case 'string':
        case 'undefined':
          return true;
        case 'boolean':
          return !propValue;
        case 'object':
          if (Array.isArray(propValue)) {
            return propValue.every(isNode);
          }
          if (propValue === null || isValidElement(propValue)) {
            return true;
          }

          var iteratorFn = getIteratorFn(propValue);
          if (iteratorFn) {
            var iterator = iteratorFn.call(propValue);
            var step;
            if (iteratorFn !== propValue.entries) {
              while (!(step = iterator.next()).done) {
                if (!isNode(step.value)) {
                  return false;
                }
              }
            } else {
              // Iterator will provide entry [k,v] tuples rather than values.
              while (!(step = iterator.next()).done) {
                var entry = step.value;
                if (entry) {
                  if (!isNode(entry[1])) {
                    return false;
                  }
                }
              }
            }
          } else {
            return false;
          }

          return true;
        default:
          return false;
      }
    }

    function isSymbol(propType, propValue) {
      // Native Symbol.
      if (propType === 'symbol') {
        return true;
      }

      // falsy value can't be a Symbol
      if (!propValue) {
        return false;
      }

      // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
      if (propValue['@@toStringTag'] === 'Symbol') {
        return true;
      }

      // Fallback for non-spec compliant Symbols which are polyfilled.
      if (typeof Symbol === 'function' && propValue instanceof Symbol) {
        return true;
      }

      return false;
    }

    // Equivalent of `typeof` but with special handling for array and regexp.
    function getPropType(propValue) {
      var propType = typeof propValue;
      if (Array.isArray(propValue)) {
        return 'array';
      }
      if (propValue instanceof RegExp) {
        // Old webkits (at least until Android 4.0) return 'function' rather than
        // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
        // passes PropTypes.object.
        return 'object';
      }
      if (isSymbol(propType, propValue)) {
        return 'symbol';
      }
      return propType;
    }

    // This handles more types than `getPropType`. Only used for error messages.
    // See `createPrimitiveTypeChecker`.
    function getPreciseType(propValue) {
      if (typeof propValue === 'undefined' || propValue === null) {
        return '' + propValue;
      }
      var propType = getPropType(propValue);
      if (propType === 'object') {
        if (propValue instanceof Date) {
          return 'date';
        } else if (propValue instanceof RegExp) {
          return 'regexp';
        }
      }
      return propType;
    }

    // Returns a string that is postfixed to a warning about an invalid type.
    // For example, "undefined" or "of type array"
    function getPostfixForTypeWarning(value) {
      var type = getPreciseType(value);
      switch (type) {
        case 'array':
        case 'object':
          return 'an ' + type;
        case 'boolean':
        case 'date':
        case 'regexp':
          return 'a ' + type;
        default:
          return type;
      }
    }

    // Returns class name of the object, if any.
    function getClassName(propValue) {
      if (!propValue.constructor || !propValue.constructor.name) {
        return ANONYMOUS;
      }
      return propValue.constructor.name;
    }

    ReactPropTypes.checkPropTypes = checkPropTypes_1;
    ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
    ReactPropTypes.PropTypes = ReactPropTypes;

    return ReactPropTypes;
  };

  var propTypes = createCommonjsModule(function (module) {
  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  {
    var ReactIs = reactIs;

    // By explicitly using `prop-types` you are opting into new development behavior.
    // http://fb.me/prop-types-in-prod
    var throwOnDirectAccess = true;
    module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
  }
  });

  /**
   * Created by jyothi on 5/6/17.
   */
  var DEFAULT_BODY_CELL_COLOR = "#F5F5F5";
  var DEFAULT_KEY_CELL_COLOR = "#F6F6F6";
  var DEFAULT_HEADER_CELL_COLOR = "#F5F5F5";
  var DEFAULT_SHADE_COLOR = "#3f83a3";
  var DEFAULT_BORDER = "1px solid #F1F1F1";
  var wrapper = function wrapper() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      width: "100%",
      padding: 0,
      margin: 0
    }, custom);
  };
  var table = function table() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      display: 'table',
      width: "100%",
      borderCollapse: 'collapse',
      textAlign: 'center',
      borderLeft: DEFAULT_BORDER
    }, custom);
  };
  var tableRow = function tableRow() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      display: 'table-row'
    }, custom);
  };
  var tableHeading = function tableHeading() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      display: 'table-header-group',
      fontWeight: 'bold',
      padding: '15px 30px',
      borderBottom: DEFAULT_BORDER,
      borderTop: DEFAULT_BORDER
    }, custom);
  };
  var tableBody = function tableBody() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      display: 'table-row-group'
    }, custom);
  };
  var tableCell = function tableCell() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      display: 'table-cell',
      padding: '5px 10px',
      borderBottom: '1px solid #DDD',
      borderRight: DEFAULT_BORDER,
      minWidth: '60px',
      whiteSpace: 'nowrap'
    }, custom);
  };
  var headerValue = function headerValue() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      fontSize: '12px'
    }, custom);
  };
  var headerLabel = function headerLabel() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      fontSize: '16px',
      padding: '0',
      margin: '0'
    }, custom);
  };
  var fixedTablePart = function fixedTablePart() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      display: 'table-cell',
      minWidth: '200px'
    }, custom);
  };
  var scrollableTableContent = function scrollableTableContent() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread2({
      position: 'relative',
      display: 'block'
    }, custom);
  };
  var scrollableTablePart = function scrollableTablePart() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return {
      display: 'table-cell',
      overflowX: 'auto',
      whiteSpace: 'nowrap',
      width: "100%",
      minWidth: 60,
      custom: custom
    };
  };

  /**
   * Created by jyothi on 6/6/17.
   */
  var VALUE_KEYS = {
    VALUE: "value",
    PERCENT: "percent"
  };
  var DEFAULT_VALUES = {
    IS_NORMALIZED_SHADE_COLOR: false
  };

  var VALUE = VALUE_KEYS.VALUE,
      PERCENT = VALUE_KEYS.PERCENT;

  var DataStore = /*#__PURE__*/_createClass(
  /**
   *
   * @param data {Object}
   * @param options {Object}
   * options = {
   *  shadeColor: {string} HEX
   *  headerColor
   * }
   */
  function DataStore(_data) {
    var _this = this;

    var options = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : {};

    _classCallCheck(this, DataStore);

    _defineProperty(this, "_checkValidity", function (data) {
      if (_typeof(data) === 'object' && !Array.isArray(data)) {
        for (var key in data) {
          if (data.hasOwnProperty(key) && _typeof(data[key]) === 'object' && !Array.isArray(data[key])) {
            for (var anotherKey in data[key]) {
              if (data[key].hasOwnProperty(anotherKey) && !Array.isArray(data[key][anotherKey])) {
                _this.isValid = false;
                return;
              }
            }
          } else {
            _this.isValid = false;
            return;
          }
        }
      } else {
        _this.isValid = false;
      }
    });

    _defineProperty(this, "_buildStore", function (data) {
      var _loop = function _loop(key) {
        if (data.hasOwnProperty(key)) {
          _this.store[key] = [];

          var _loop2 = function _loop2(anotherKey) {
            if (data[key].hasOwnProperty(anotherKey)) {
              var cellData = {};
              cellData.type = key;
              cellData[VALUE] = anotherKey;
              cellData.valueFor = anotherKey;
              cellData.total = data[key][anotherKey].length > 0 ? data[key][anotherKey][0] : 0;
              cellData.color = _this.options.keyCellColor;
              cellData.isDate = true;
              cellData.index = -1;
              cellData.isHeader = false;

              _this.store[key].push([cellData].concat(_toConsumableArray(data[key][anotherKey].map(function (value, index) {
                var _ref;

                var percent = _this._getPercentage(cellData.total, value);

                return _ref = {
                  isHeader: false,
                  index: index,
                  type: key
                }, _defineProperty(_ref, VALUE, value), _defineProperty(_ref, "valueFor", anotherKey), _defineProperty(_ref, "total", cellData.total), _defineProperty(_ref, "isTotal", index === 0), _defineProperty(_ref, "isCell", index > 0), _defineProperty(_ref, PERCENT, percent), _defineProperty(_ref, "color", index === 0 ? _this.options.bodyCellColor : _this.options.isNormalizedShadeColor ? _this._shadeCellWithColor(_this._normalizedValue(data[key], value), _this.options.shadeColor) : _this._shadeCellWithColor(percent, _this.options.shadeColor)), _ref;
              }))));
            }
          };

          for (var anotherKey in data[key]) {
            _loop2(anotherKey);
          }
        }
      };

      for (var key in data) {
        _loop(key);
      }
    });

    _defineProperty(this, "_buildHeaders", function () {
      var _loop3 = function _loop3(key) {
        if (_this.store.hasOwnProperty(key)) {
          var _this$headers$key$pus;

          var labelPrefix = _this._turnCamelCase(key.slice(0, -1));

          _this.headers[key] = [];

          _this.headers[key].push((_this$headers$key$pus = {}, _defineProperty(_this$headers$key$pus, VALUE, ""), _defineProperty(_this$headers$key$pus, PERCENT, ""), _defineProperty(_this$headers$key$pus, "color", _this.options.headerCellColor), _defineProperty(_this$headers$key$pus, "isLabel", true), _defineProperty(_this$headers$key$pus, "label", _this._turnCamelCase(key)), _defineProperty(_this$headers$key$pus, "index", 0), _this$headers$key$pus));

          var cellData = {};
          cellData.isHeader = true;
          cellData.index = 1;
          cellData.type = key;
          cellData[VALUE] = _this._sumOfColumnWithIndex(_this.store[key], 1);
          cellData.valueFor = key;
          cellData.total = cellData.value;
          cellData[PERCENT] = 100;
          cellData.color = _this.options.headerCellColor;
          cellData.label = labelPrefix + ' ' + 0;

          _this.headers[key].push(cellData); //second cell (Initial Count)


          var totalRows = _this.store[key].length;
          var largeRow = totalRows > 0 ? _this.store[key][0] : [];
          largeRow.forEach(function (el, index) {
            var _this$headers$key$pus2;

            if (index < 2) return;

            var value = _this._sumOfColumnWithIndex(_this.store[key], index);

            var percent = _this._getPercentage(_this._sumOfFirstColumnUpToIndex(_this.store[key], totalRows, index), value);

            _this.headers[key].push((_this$headers$key$pus2 = {
              isHeader: true,
              index: index,
              type: key
            }, _defineProperty(_this$headers$key$pus2, VALUE, value), _defineProperty(_this$headers$key$pus2, "valueFor", largeRow[0]), _defineProperty(_this$headers$key$pus2, "total", cellData.total), _defineProperty(_this$headers$key$pus2, PERCENT, percent), _defineProperty(_this$headers$key$pus2, "color", _this._shadeCellWithColor(percent, _this.options.shadeColor)), _defineProperty(_this$headers$key$pus2, "label", labelPrefix + ' ' + (index - 1)), _this$headers$key$pus2));
          });
        }
      };

      //TODO: can also take custom headers
      for (var key in _this.store) {
        _loop3(key);
      }
    });

    _defineProperty(this, "_sumOfArrayElements", function (arr) {
      return arr.reduce(function (a, b) {
        return a + b;
      });
    });

    _defineProperty(this, "_sumOfColumnWithIndex", function (arr, index) {
      var sum = 0;
      arr.forEach(function (el) {
        try {
          sum += el[index].value;
        } catch (e) {
          sum += 0;
        }
      });
      return sum;
    });

    _defineProperty(this, "_sumOfFirstColumnUpToIndex", function (arr, index, baseIndex) {
      var sum = 0;

      for (var i = 0; i <= index; i++) {
        try {
          if (arr[i][baseIndex]) {
            //If value exists upto this index FIXME: need better understanding than this
            sum += arr[i][1].value;
          } else {
            break;
          }
        } catch (e) {
          //if no further index break the loop
          break;
        }
      }

      return sum;
    });

    _defineProperty(this, "getTypeData", function (type) {
      if (_this.store.hasOwnProperty(type)) {
        return _this.store[type]; //returns [][]
      } else {
        console.error("No Data Found for type => ".concat(type));
      }
    });

    _defineProperty(this, "getHighestRowSize", function (type) {
      if (_this.store.hasOwnProperty(type)) {
        return _this.store[type][0].length; //returns [][]
      } else {
        console.error("No Columns Found for type => ".concat(type));
      }
    });

    _defineProperty(this, "getCellData", function (type, row, col) {
      if (_this.store.hasOwnProperty(type)) {
        try {
          return _this.store[type][row][col];
        } catch (e) {
          console.error("No Data Found for cell with type => ".concat(type, ", row => ").concat(row, ", col => ").concat(col));
        }
      } else {
        console.error("No Data Found for cell with type => ".concat(type, ", row => ").concat(row, ", col => ").concat(col));
      }
    });

    _defineProperty(this, "getHeaderCellData", function (type, col) {
      if (_this.headers.hasOwnProperty(type)) {
        try {
          return _this.headers[type][col];
        } catch (e) {
          console.error("No Data Found for cell with type => ".concat(type, ", col => ").concat(col));
        }
      } else {
        console.error("No Data Found for cell with type => ".concat(type, ", col => ").concat(col));
      }
    });

    _defineProperty(this, "getHeader", function (type) {
      if (_this.headers.hasOwnProperty(type)) {
        return _this.headers[type]; //returns [][]
      } else {
        console.error("No Headers Found for type => ".concat(type));
        return [];
      }
    });

    _defineProperty(this, "getRows", function (type) {
      if (_this.store.hasOwnProperty(type)) {
        return _this.store[type]; //returns [][]
      } else {
        console.error("No Headers Found for type => ".concat(type));
        return [];
      }
    });

    _defineProperty(this, "_shadeCellWithColor", function (percent) {
      var color = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : "#3f83a3";
      var rate = 1.0 - Math.ceil(percent / 10) / 10;
      var f = parseInt(color.slice(1), 16),
          t = rate < 0 ? 0 : 255,
          p = rate < 0 ? rate * -1 : rate,
          R = f >> 16,
          G = f >> 8 & 0x00FF,
          B = f & 0x0000FF;
      return "#".concat((0x1000000 + (Math.round((t - R) * p) + R) * 0x10000 + (Math.round((t - G) * p) + G) * 0x100 + (Math.round((t - B) * p) + B)).toString(16).slice(1));
    });

    _defineProperty(this, "_getPercentage", function (total, value) {
      return total ? Math.round(value / total * 100 * 100) / 100 : total;
    });

    _defineProperty(this, "_isValidHex", function (color) {
      return /(^#[0-9A-F]{6}$)|(^#[0-9A-F]{3}$)/i.test(color);
    });

    _defineProperty(this, "_turnCamelCase", function (text) {

      if (typeof text === 'string') {
        return text.toLowerCase().replace(/\b\w/g, function (replaced) {
          return replaced.toUpperCase();
        });
      }
    });

    _defineProperty(this, "_normalizedValue", function (array, value) {
      var joinedArray = [];
      Object.entries(array).map(function (el) {
        joinedArray = [].concat(_toConsumableArray(joinedArray), _toConsumableArray(el[1].slice(1)));
      });
      var nv = (value - Math.min.apply(Math, _toConsumableArray(joinedArray))) / (Math.max.apply(Math, _toConsumableArray(joinedArray)) - Math.min.apply(Math, _toConsumableArray(joinedArray))) * 100;
      return Math.round(nv);
    });

    this.isValid = true;

    this._checkValidity(_data);

    this.rawStore = _data;
    this.store = {};
    this.headers = {};
    this.options = options;

    if (this.isValid) {
      this._buildStore(_data);

      this._buildHeaders();
    } else {
      console.error("Invalid Data for cohort graph..!");
    }
  }
  /**
   *
   * @param data
   * @private
   */
  );

  var _excluded = ["formatter"],
      _excluded2 = ["formatter"];
  var VALUE$1 = VALUE_KEYS.VALUE,
      PERCENT$1 = VALUE_KEYS.PERCENT;

  var renderValue = function renderValue(props) {
    //label and cell formatters
    var isTotal = props.isTotal,
        isLabel = props.isLabel,
        isDate = props.isDate,
        valueType = props.valueType,
        formatter = props.formatter;

    if (typeof formatter === 'function') {
      var _formatter = props.formatter,
          rest = _objectWithoutProperties(props, _excluded);

      return _formatter(rest);
    }

    return isTotal || isLabel || isDate ? props[VALUE$1] : valueType === PERCENT$1 ? "".concat(props[PERCENT$1], " %") : props[VALUE$1];
  };

  var renderHeader = function renderHeader(props) {
    //header formatter
    var formatter = props.formatter,
        label = props.label;

    if (typeof formatter === 'function') {
      var _formatter2 = props.formatter,
          rest = _objectWithoutProperties(props, _excluded2);

      return _formatter2(rest);
    }

    return label;
  };

  var HeaderCell = function HeaderCell(props) {
    return /*#__PURE__*/React.createElement("div", {
      style: _objectSpread2(_objectSpread2({}, tableCell(props.tableCellStyles)), {}, {
        backgroundColor: props.color
      }, props.style)
    }, /*#__PURE__*/React.createElement("p", {
      style: headerLabel(props.headerLabelStyles)
    }, renderHeader(props)), props.showHeaderValues ? /*#__PURE__*/React.createElement("span", {
      style: headerValue({})
    }, renderValue(_objectSpread2(_objectSpread2({}, props), {}, {
      isHeaderValue: true
    }))) : null);
  };
  var BodyCell = function BodyCell(props) {
    return /*#__PURE__*/React.createElement("div", {
      style: _objectSpread2(_objectSpread2({}, tableCell(props.tableCellStyles)), {}, {
        backgroundColor: props.color
      }, props.style),
      title: "Out of ".concat(props.total, " on ").concat(props.valueFor)
    }, renderValue(props));
  };
  var ScrollableContent = /*#__PURE__*/function (_React$Component) {
    _inherits(ScrollableContent, _React$Component);

    var _super = _createSuper(ScrollableContent);

    function ScrollableContent(props) {
      var _this;

      _classCallCheck(this, ScrollableContent);

      _this = _super.call(this, props);

      _defineProperty(_assertThisInitialized(_this), "setWidth", function () {
        if (_this.ref && _this.ref.parentNode) {
          try {
            _this.setState({
              width: _this.ref.parentNode.clientWidth - 1
            });
          } catch (e) {//console.error(e);
          }
        }
      });

      _this.state = {
        width: 0
      };
      _this.ref = null;
      return _this;
    }

    _createClass(ScrollableContent, [{
      key: "componentDidMount",
      value: function componentDidMount() {
        var _this2 = this;

        this.setWidth();
        window.addEventListener('resize', function () {
          _this2.setWidth();
        });
      }
    }, {
      key: "render",
      value: function render() {
        var _this3 = this;

        var scrollableTableContentStyles = this.props.scrollableTableContentStyles;
        return /*#__PURE__*/React.createElement("div", {
          ref: function ref(x) {
            return _this3.ref = x;
          },
          style: _objectSpread2(_objectSpread2({}, scrollableTableContent(scrollableTableContentStyles)), {}, {
            width: this.state.width
          })
        }, this.props.children);
      }
    }]);

    return ScrollableContent;
  }(React.Component);

  var ReactCohortGraph = /*#__PURE__*/function (_React$Component) {
    _inherits(ReactCohortGraph, _React$Component);

    var _super = _createSuper(ReactCohortGraph);

    function ReactCohortGraph(_props) {
      var _this;

      _classCallCheck(this, ReactCohortGraph);

      _this = _super.call(this, _props);

      _defineProperty(_assertThisInitialized(_this), "_getStore", function (props) {
        var _props$data = props.data,
            data = _props$data === void 0 ? {} : _props$data,
            _props$shadeColor = props.shadeColor,
            shadeColor = _props$shadeColor === void 0 ? DEFAULT_SHADE_COLOR : _props$shadeColor,
            _props$headerCellColo = props.headerCellColor,
            headerCellColor = _props$headerCellColo === void 0 ? DEFAULT_HEADER_CELL_COLOR : _props$headerCellColo,
            _props$bodyCellColor = props.bodyCellColor,
            bodyCellColor = _props$bodyCellColor === void 0 ? DEFAULT_BODY_CELL_COLOR : _props$bodyCellColor,
            _props$keyCellColor = props.keyCellColor,
            keyCellColor = _props$keyCellColor === void 0 ? DEFAULT_KEY_CELL_COLOR : _props$keyCellColor,
            _props$isNormalizedSh = props.isNormalizedShadeColor,
            isNormalizedShadeColor = _props$isNormalizedSh === void 0 ? DEFAULT_VALUES.IS_NORMALIZED_SHADE_COLOR : _props$isNormalizedSh;
        return new DataStore(data, {
          shadeColor: shadeColor,
          headerCellColor: headerCellColor,
          bodyCellColor: bodyCellColor,
          keyCellColor: keyCellColor,
          isNormalizedShadeColor: isNormalizedShadeColor
        });
      });

      _defineProperty(_assertThisInitialized(_this), "isFixed", function (index) {
        return index < 2;
      });

      _defineProperty(_assertThisInitialized(_this), "renderChildren", function (props) {
        return React.Children.map(props.children, function (child) {
          return /*#__PURE__*/React.cloneElement(child, props);
        });
      });

      var _props$data2 = _props.data,
          _props$defaultValueTy = _props.defaultValueType,
          defaultValueType = _props$defaultValueTy === void 0 ? VALUE_KEYS.PERCENT : _props$defaultValueTy,
          _shadeColor = _props.shadeColor;

      _this.state = {
        dataStore: _this._getStore(_props),
        currentType: "",
        valueType: defaultValueType
      };
      return _this;
    }

    _createClass(ReactCohortGraph, [{
      key: "componentWillMount",
      value: function componentWillMount() {
        var _this$props = this.props,
            data = _this$props.data,
            onStoreUpdate = _this$props.onStoreUpdate;
        var keys = Object.keys(data);

        if (keys.length > 0) {
          var store = this._getStore(this.props);

          var currentType = keys[0];

          if (typeof onStoreUpdate === 'function') {
            onStoreUpdate(store, currentType, this.state.valueType);
          }

          this.setState({
            currentType: currentType,
            dataStore: store
          });
        }
      }
    }, {
      key: "componentWillReceiveProps",
      value: function componentWillReceiveProps(nextProps) {
        var data = nextProps.data,
            dataType = nextProps.dataType,
            valueType = nextProps.valueType,
            onStoreUpdate = nextProps.onStoreUpdate;
        var currentType = this.state.currentType;
        var keys = Object.keys(data);

        if (keys.length > 0) {
          var store = this._getStore(this.props);

          var currentDataType = dataType || Object.keys(data)[0];

          if (currentType === "" || valueType === this.state.valueType && dataType === currentType) {
            this.setState({
              dataStore: store
            });
          } else {
            if (valueType) {
              this.setState({
                currentType: currentDataType,
                valueType: valueType
              });
            } else {
              this.setState({
                currentType: currentDataType
              });
            }
          }

          if (typeof onStoreUpdate === 'function') {
            onStoreUpdate(store, currentDataType, valueType);
          }
        }
      }
    }, {
      key: "componentDidMount",
      value: function componentDidMount() {}
    }, {
      key: "render",
      value: function render() {
        var _this2 = this;

        var _this$props2 = this.props,
            _this$props2$showEmpt = _this$props2.showEmptyDataMessage,
            showEmptyDataMessage = _this$props2$showEmpt === void 0 ? true : _this$props2$showEmpt,
            customEmptyDataMessage = _this$props2.customEmptyDataMessage,
            showHeaderValues = _this$props2.showHeaderValues,
            cellFormatter = _this$props2.cellFormatter,
            headerFormatter = _this$props2.headerFormatter,
            _this$props2$bodyCell = _this$props2.bodyCellStyles,
            bodyCellStyles = _this$props2$bodyCell === void 0 ? {} : _this$props2$bodyCell,
            _this$props2$headerCe = _this$props2.headerCellStyles,
            headerCellStyles = _this$props2$headerCe === void 0 ? {} : _this$props2$headerCe,
            tableStyles = _this$props2.tableStyles,
            tableRowStyles = _this$props2.tableRowStyles,
            tableHeadingStyles = _this$props2.tableHeadingStyles,
            tableBodyStyles = _this$props2.tableBodyStyles,
            fixedTablePartStyles = _this$props2.fixedTablePartStyles,
            wrapperStyles = _this$props2.wrapperStyles,
            scrollableTablePartStyles = _this$props2.scrollableTablePartStyles,
            scrollableTableContentStyles = _this$props2.scrollableTableContentStyles,
            headerLabelStyles = _this$props2.headerLabelStyles,
            tableCellStyles = _this$props2.tableCellStyles;
        var _this$state = this.state,
            dataStore = _this$state.dataStore,
            currentType = _this$state.currentType,
            valueType = _this$state.valueType;
        var header = dataStore.getHeader(currentType);
        var rows = dataStore.getRows(currentType);
        var TableStyles = table(tableStyles);
        var TableRowStyles = tableRow(tableRowStyles);
        var TableHeadingStyles = tableHeading(tableHeadingStyles);
        var TableBodyStyles = tableBody(tableBodyStyles);
        var FixedTablePartStyles = fixedTablePart(fixedTablePartStyles);
        var WrapperStyles = wrapper(wrapperStyles);
        var ScrollableTablePartStyles = scrollableTablePart(scrollableTablePartStyles);
        var ScrollableTableContentStyles = scrollableTableContent(scrollableTableContentStyles);

        if (header && header.length > 0) {
          return /*#__PURE__*/React.createElement("div", {
            style: WrapperStyles
          }, this.renderChildren(_objectSpread2(_objectSpread2({}, this.props), this.state)), /*#__PURE__*/React.createElement("div", {
            style: TableStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: TableBodyStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: TableRowStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: FixedTablePartStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: TableStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: TableHeadingStyles
          }, header.map(function (headerCell, i) {
            return _this2.isFixed(i) && /*#__PURE__*/React.createElement(HeaderCell, _extends({
              tableCellStyles: tableCellStyles,
              headerLabelStyles: headerLabelStyles,
              style: headerCellStyles,
              key: "header" + i
            }, headerCell, {
              formatter: typeof headerFormatter === "function" ? headerFormatter : cellFormatter,
              showHeaderValues: showHeaderValues,
              valueType: valueType,
              isFixed: true
            }));
          })), /*#__PURE__*/React.createElement("div", {
            style: TableBodyStyles
          }, rows.map(function (row, j) {
            return /*#__PURE__*/React.createElement("div", {
              style: TableRowStyles,
              key: "row" + j
            }, row.map(function (cell, k) {
              return _this2.isFixed(k) && /*#__PURE__*/React.createElement(BodyCell, _extends({
                tableCellStyles: tableCellStyles,
                style: bodyCellStyles,
                key: "cell" + k
              }, cell, {
                valueType: valueType,
                formatter: cellFormatter,
                isFixed: true
              }));
            }));
          })))), /*#__PURE__*/React.createElement("div", {
            style: ScrollableTablePartStyles
          }, /*#__PURE__*/React.createElement(ScrollableContent, {
            scrollableTableContentStyles: scrollableTableContentStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: TableStyles
          }, /*#__PURE__*/React.createElement("div", {
            style: TableHeadingStyles
          }, header.map(function (headerCell, i) {
            return !_this2.isFixed(i) && /*#__PURE__*/React.createElement(HeaderCell, _extends({
              tableCellStyles: tableCellStyles,
              style: headerCellStyles,
              key: "header" + i
            }, headerCell, {
              formatter: typeof headerFormatter === "function" ? headerFormatter : cellFormatter,
              showHeaderValues: showHeaderValues,
              valueType: valueType,
              isFixed: false
            }));
          })), /*#__PURE__*/React.createElement("div", {
            style: TableBodyStyles
          }, rows.map(function (row, j) {
            return /*#__PURE__*/React.createElement("div", {
              style: TableRowStyles,
              key: "row" + j
            }, row.map(function (cell, k) {
              return !_this2.isFixed(k) && /*#__PURE__*/React.createElement(BodyCell, _extends({
                tableCellStyles: tableCellStyles,
                style: bodyCellStyles,
                key: "cell" + k
              }, cell, {
                valueType: valueType,
                formatter: cellFormatter,
                isFixed: false
              }));
            }));
          })))))))));
        }

        if (showEmptyDataMessage) {
          return customEmptyDataMessage || /*#__PURE__*/React.createElement("h3", null, "No Data..!");
        }
      }
    }]);

    return ReactCohortGraph;
  }(React.Component);

  ReactCohortGraph.propTypes = {
    data: propTypes.object.isRequired,
    dataType: propTypes.string,
    //keys of data
    defaultValueType: propTypes.string,
    //["value", "percent"]
    cellClickEvent: propTypes.func,
    showEmptyDataMessage: propTypes.bool,
    customEmptyDataMessage: propTypes.any,
    columnClickEvent: propTypes.func,
    shadeColor: propTypes.string,
    //#3f83a3
    headerCellColor: propTypes.string,
    bodyCellColor: propTypes.string,
    keyCellColor: propTypes.string,
    headerFormatter: propTypes.func,
    cellFormatter: propTypes.func,

    /*maxDays : PropTypes.number,
    maxWeeks : PropTypes.number, //TODO:
    maxMonths : PropTypes.number,*/
    //enableTooltip : PropTypes.bool, TODO
    showAbsolute: propTypes.bool,
    toggleValues: propTypes.bool,
    showHeaderValues: propTypes.bool,
    onStoreUpdate: propTypes.func,
    //function(store, currentType, valueType)
    //Styles
    headerCellStyles: propTypes.object,
    bodyCellStyles: propTypes.object,
    tableCellStyles: propTypes.object,
    tableStyles: propTypes.object,
    tableRowStyles: propTypes.object,
    tableHeadingStyles: propTypes.object,
    tableBodyStyles: propTypes.object,
    fixedTablePartStyles: propTypes.object,
    wrapperStyles: propTypes.object,
    scrollableTablePartStyles: propTypes.object,
    scrollableTableContentStyles: propTypes.object,
    headerValueStyles: propTypes.object,
    headerLabelStyles: propTypes.object,
    isNormalizedShadeColor: propTypes.bool
  };

  return ReactCohortGraph;

})));
