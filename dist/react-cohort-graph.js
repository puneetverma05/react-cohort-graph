(function (global, factory) {
  typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory(require('react'), require('crypto')) :
  typeof define === 'function' && define.amd ? define(['react', 'crypto'], factory) :
  (global = global || self, global.ReactCohortGraph = factory(global.React, global.crypto));
}(this, function (React, crypto) { 'use strict';

  React = React && React.hasOwnProperty('default') ? React['default'] : React;
  crypto = crypto && crypto.hasOwnProperty('default') ? crypto['default'] : crypto;

  function _typeof(obj) {
    if (typeof Symbol === "function" && typeof Symbol.iterator === "symbol") {
      _typeof = function (obj) {
        return typeof obj;
      };
    } else {
      _typeof = function (obj) {
        return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
      };
    }

    return _typeof(obj);
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
    _extends = Object.assign || function (target) {
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

  function _objectSpread(target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i] != null ? arguments[i] : {};
      var ownKeys = Object.keys(source);

      if (typeof Object.getOwnPropertySymbols === 'function') {
        ownKeys = ownKeys.concat(Object.getOwnPropertySymbols(source).filter(function (sym) {
          return Object.getOwnPropertyDescriptor(source, sym).enumerable;
        }));
      }

      ownKeys.forEach(function (key) {
        _defineProperty(target, key, source[key]);
      });
    }

    return target;
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
    if (superClass) _setPrototypeOf(subClass, superClass);
  }

  function _getPrototypeOf(o) {
    _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf : function _getPrototypeOf(o) {
      return o.__proto__ || Object.getPrototypeOf(o);
    };
    return _getPrototypeOf(o);
  }

  function _setPrototypeOf(o, p) {
    _setPrototypeOf = Object.setPrototypeOf || function _setPrototypeOf(o, p) {
      o.__proto__ = p;
      return o;
    };

    return _setPrototypeOf(o, p);
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
    }

    return _assertThisInitialized(self);
  }

  function _toConsumableArray(arr) {
    return _arrayWithoutHoles(arr) || _iterableToArray(arr) || _nonIterableSpread();
  }

  function _arrayWithoutHoles(arr) {
    if (Array.isArray(arr)) {
      for (var i = 0, arr2 = new Array(arr.length); i < arr.length; i++) arr2[i] = arr[i];

      return arr2;
    }
  }

  function _iterableToArray(iter) {
    if (Symbol.iterator in Object(iter) || Object.prototype.toString.call(iter) === "[object Arguments]") return Array.from(iter);
  }

  function _nonIterableSpread() {
    throw new TypeError("Invalid attempt to spread non-iterable instance");
  }

  function unwrapExports (x) {
  	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x.default : x;
  }

  function createCommonjsModule(fn, module) {
  	return module = { exports: {} }, fn(module, module.exports), module.exports;
  }

  var reactIs_development = createCommonjsModule(function (module, exports) {



  {
    (function() {

  Object.defineProperty(exports, '__esModule', { value: true });

  // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
  // nor polyfill, then a plain number is used for performance.
  var hasSymbol = typeof Symbol === 'function' && Symbol.for;

  var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
  var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
  var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
  var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
  var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
  var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
  var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace;
  var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
  var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
  var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
  var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
  var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
  var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;

  function isValidElementType(type) {
    return typeof type === 'string' || typeof type === 'function' ||
    // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
    type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE);
  }

  /**
   * Forked from fbjs/warning:
   * https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/__forks__/warning.js
   *
   * Only change is we use console.warn instead of console.error,
   * and do nothing when 'console' is not supported.
   * This really simplifies the code.
   * ---
   * Similar to invariant but only logs a warning if the condition is not met.
   * This can be used to log issues in development environments in critical
   * paths. Removing the logging code for production environments will keep the
   * same logic and follow the same code paths.
   */

  var lowPriorityWarning = function () {};

  {
    var printWarning = function (format) {
      for (var _len = arguments.length, args = Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
        args[_key - 1] = arguments[_key];
      }

      var argIndex = 0;
      var message = 'Warning: ' + format.replace(/%s/g, function () {
        return args[argIndex++];
      });
      if (typeof console !== 'undefined') {
        console.warn(message);
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message);
      } catch (x) {}
    };

    lowPriorityWarning = function (condition, format) {
      if (format === undefined) {
        throw new Error('`lowPriorityWarning(condition, format, ...args)` requires a warning ' + 'message argument');
      }
      if (!condition) {
        for (var _len2 = arguments.length, args = Array(_len2 > 2 ? _len2 - 2 : 0), _key2 = 2; _key2 < _len2; _key2++) {
          args[_key2 - 2] = arguments[_key2];
        }

        printWarning.apply(undefined, [format].concat(args));
      }
    };
  }

  var lowPriorityWarning$1 = lowPriorityWarning;

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
                case REACT_PROVIDER_TYPE:
                  return $$typeofType;
                default:
                  return $$typeof;
              }
          }
        case REACT_LAZY_TYPE:
        case REACT_MEMO_TYPE:
        case REACT_PORTAL_TYPE:
          return $$typeof;
      }
    }

    return undefined;
  }

  // AsyncMode is deprecated along with isAsyncMode
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

  var hasWarnedAboutDeprecatedIsAsyncMode = false;

  // AsyncMode should be deprecated
  function isAsyncMode(object) {
    {
      if (!hasWarnedAboutDeprecatedIsAsyncMode) {
        hasWarnedAboutDeprecatedIsAsyncMode = true;
        lowPriorityWarning$1(false, 'The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
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

  exports.typeOf = typeOf;
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
  exports.isValidElementType = isValidElementType;
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
    })();
  }
  });

  unwrapExports(reactIs_development);
  var reactIs_development_1 = reactIs_development.typeOf;
  var reactIs_development_2 = reactIs_development.AsyncMode;
  var reactIs_development_3 = reactIs_development.ConcurrentMode;
  var reactIs_development_4 = reactIs_development.ContextConsumer;
  var reactIs_development_5 = reactIs_development.ContextProvider;
  var reactIs_development_6 = reactIs_development.Element;
  var reactIs_development_7 = reactIs_development.ForwardRef;
  var reactIs_development_8 = reactIs_development.Fragment;
  var reactIs_development_9 = reactIs_development.Lazy;
  var reactIs_development_10 = reactIs_development.Memo;
  var reactIs_development_11 = reactIs_development.Portal;
  var reactIs_development_12 = reactIs_development.Profiler;
  var reactIs_development_13 = reactIs_development.StrictMode;
  var reactIs_development_14 = reactIs_development.Suspense;
  var reactIs_development_15 = reactIs_development.isValidElementType;
  var reactIs_development_16 = reactIs_development.isAsyncMode;
  var reactIs_development_17 = reactIs_development.isConcurrentMode;
  var reactIs_development_18 = reactIs_development.isContextConsumer;
  var reactIs_development_19 = reactIs_development.isContextProvider;
  var reactIs_development_20 = reactIs_development.isElement;
  var reactIs_development_21 = reactIs_development.isForwardRef;
  var reactIs_development_22 = reactIs_development.isFragment;
  var reactIs_development_23 = reactIs_development.isLazy;
  var reactIs_development_24 = reactIs_development.isMemo;
  var reactIs_development_25 = reactIs_development.isPortal;
  var reactIs_development_26 = reactIs_development.isProfiler;
  var reactIs_development_27 = reactIs_development.isStrictMode;
  var reactIs_development_28 = reactIs_development.isSuspense;

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

  var printWarning = function() {};

  {
    var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
    var loggedTypeFailures = {};
    var has = Function.call.bind(Object.prototype.hasOwnProperty);

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
      } catch (x) {}
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
        if (has(typeSpecs, typeSpecName)) {
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
                'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
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

  var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
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
    function PropTypeError(message) {
      this.message = message;
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
          } else if (typeof console !== 'undefined') {
            // Old behavior for people using React.PropTypes
            var cacheKey = componentName + ':' + propName;
            if (
              !manualPropTypeCallCache[cacheKey] &&
              // Avoid spamming the console because they are often not actionable except for lib authors
              manualPropTypeWarningCount < 3
            ) {
              printWarning$1(
                'You are manually calling a React.PropTypes validation ' +
                'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
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

          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
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
          if (has$1(propValue, key)) {
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
        printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.');
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
        for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
          var checker = arrayOfTypeCheckers[i];
          if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
            return null;
          }
        }

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
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

    function createShapeTypeChecker(shapeTypes) {
      function validate(props, propName, componentName, location, propFullName) {
        var propValue = props[propName];
        var propType = getPropType(propValue);
        if (propType !== 'object') {
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
        }
        for (var key in shapeTypes) {
          var checker = shapeTypes[key];
          if (!checker) {
            continue;
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
        // We need to check all keys in case some are required but missing from
        // props.
        var allKeys = objectAssign({}, props[propName], shapeTypes);
        for (var key in allKeys) {
          var checker = shapeTypes[key];
          if (!checker) {
            return new PropTypeError(
              'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
              '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
              '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
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

  function rng() {
    return crypto.randomBytes(16);
  }

  /**
   * Convert array of 16 byte values to UUID string format of the form:
   * XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX
   */
  var byteToHex = [];

  for (var i = 0; i < 256; ++i) {
    byteToHex[i] = (i + 0x100).toString(16).substr(1);
  }

  function bytesToUuid(buf, offset) {
    var i = offset || 0;
    var bth = byteToHex; // join used to fix memory issue caused by concatenation: https://bugs.chromium.org/p/v8/issues/detail?id=3175#c4

    return [bth[buf[i++]], bth[buf[i++]], bth[buf[i++]], bth[buf[i++]], '-', bth[buf[i++]], bth[buf[i++]], '-', bth[buf[i++]], bth[buf[i++]], '-', bth[buf[i++]], bth[buf[i++]], '-', bth[buf[i++]], bth[buf[i++]], bth[buf[i++]], bth[buf[i++]], bth[buf[i++]], bth[buf[i++]]].join('');
  }

  function v4(options, buf, offset) {
    var i = buf && offset || 0;

    if (typeof options == 'string') {
      buf = options === 'binary' ? new Array(16) : null;
      options = null;
    }

    options = options || {};
    var rnds = options.random || (options.rng || rng)(); // Per 4.4, set bits for version and `clock_seq_hi_and_reserved`

    rnds[6] = rnds[6] & 0x0f | 0x40;
    rnds[8] = rnds[8] & 0x3f | 0x80; // Copy bytes to buffer, if provided

    if (buf) {
      for (var ii = 0; ii < 16; ++ii) {
        buf[i + ii] = rnds[ii];
      }
    }

    return buf || bytesToUuid(rnds);
  }

  function _classCallCheck$1(instance, Constructor) {
    if (!(instance instanceof Constructor)) {
      throw new TypeError("Cannot call a class as a function");
    }
  }

  function _defineProperties$1(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i];
      descriptor.enumerable = descriptor.enumerable || false;
      descriptor.configurable = true;
      if ("value" in descriptor) descriptor.writable = true;
      Object.defineProperty(target, descriptor.key, descriptor);
    }
  }

  function _createClass$1(Constructor, protoProps, staticProps) {
    if (protoProps) _defineProperties$1(Constructor.prototype, protoProps);
    if (staticProps) _defineProperties$1(Constructor, staticProps);
    return Constructor;
  }

  function _defineProperty$1(obj, key, value) {
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

  function _extends$1() {
    _extends$1 = Object.assign || function (target) {
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

    return _extends$1.apply(this, arguments);
  }

  function ownKeys(object, enumerableOnly) {
    var keys = Object.keys(object);

    if (Object.getOwnPropertySymbols) {
      var symbols = Object.getOwnPropertySymbols(object);
      if (enumerableOnly) symbols = symbols.filter(function (sym) {
        return Object.getOwnPropertyDescriptor(object, sym).enumerable;
      });
      keys.push.apply(keys, symbols);
    }

    return keys;
  }

  function _objectSpread2(target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i] != null ? arguments[i] : {};

      if (i % 2) {
        ownKeys(Object(source), true).forEach(function (key) {
          _defineProperty$1(target, key, source[key]);
        });
      } else if (Object.getOwnPropertyDescriptors) {
        Object.defineProperties(target, Object.getOwnPropertyDescriptors(source));
      } else {
        ownKeys(Object(source)).forEach(function (key) {
          Object.defineProperty(target, key, Object.getOwnPropertyDescriptor(source, key));
        });
      }
    }

    return target;
  }

  function _inherits$1(subClass, superClass) {
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
    if (superClass) _setPrototypeOf$1(subClass, superClass);
  }

  function _getPrototypeOf$1(o) {
    _getPrototypeOf$1 = Object.setPrototypeOf ? Object.getPrototypeOf : function _getPrototypeOf(o) {
      return o.__proto__ || Object.getPrototypeOf(o);
    };
    return _getPrototypeOf$1(o);
  }

  function _setPrototypeOf$1(o, p) {
    _setPrototypeOf$1 = Object.setPrototypeOf || function _setPrototypeOf(o, p) {
      o.__proto__ = p;
      return o;
    };

    return _setPrototypeOf$1(o, p);
  }

  function _assertThisInitialized$1(self) {
    if (self === void 0) {
      throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
    }

    return self;
  }

  function _possibleConstructorReturn$1(self, call) {
    if (call && (typeof call === "object" || typeof call === "function")) {
      return call;
    }

    return _assertThisInitialized$1(self);
  }

  var CONSTANT = {
    GLOBAL: {
      HIDE: '__react_tooltip_hide_event',
      REBUILD: '__react_tooltip_rebuild_event',
      SHOW: '__react_tooltip_show_event'
    }
  };

  /**
   * Static methods for react-tooltip
   */

  var dispatchGlobalEvent = function dispatchGlobalEvent(eventName, opts) {
    // Compatible with IE
    // @see http://stackoverflow.com/questions/26596123/internet-explorer-9-10-11-event-constructor-doesnt-work
    // @see https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/CustomEvent
    var event;

    if (typeof window.CustomEvent === 'function') {
      event = new window.CustomEvent(eventName, {
        detail: opts
      });
    } else {
      event = document.createEvent('Event');
      event.initEvent(eventName, false, true, opts);
    }

    window.dispatchEvent(event);
  };

  function staticMethods (target) {
    /**
     * Hide all tooltip
     * @trigger ReactTooltip.hide()
     */
    target.hide = function (target) {
      dispatchGlobalEvent(CONSTANT.GLOBAL.HIDE, {
        target: target
      });
    };
    /**
     * Rebuild all tooltip
     * @trigger ReactTooltip.rebuild()
     */


    target.rebuild = function () {
      dispatchGlobalEvent(CONSTANT.GLOBAL.REBUILD);
    };
    /**
     * Show specific tooltip
     * @trigger ReactTooltip.show()
     */


    target.show = function (target) {
      dispatchGlobalEvent(CONSTANT.GLOBAL.SHOW, {
        target: target
      });
    };

    target.prototype.globalRebuild = function () {
      if (this.mount) {
        this.unbindListener();
        this.bindListener();
      }
    };

    target.prototype.globalShow = function (event) {
      if (this.mount) {
        var hasTarget = event && event.detail && event.detail.target && true || false; // Create a fake event, specific show will limit the type to `solid`
        // only `float` type cares e.clientX e.clientY

        this.showTooltip({
          currentTarget: hasTarget && event.detail.target
        }, true);
      }
    };

    target.prototype.globalHide = function (event) {
      if (this.mount) {
        var hasTarget = event && event.detail && event.detail.target && true || false;
        this.hideTooltip({
          currentTarget: hasTarget && event.detail.target
        }, hasTarget);
      }
    };
  }

  /**
   * Events that should be bound to the window
   */
  function windowListener (target) {
    target.prototype.bindWindowEvents = function (resizeHide) {
      // ReactTooltip.hide
      window.removeEventListener(CONSTANT.GLOBAL.HIDE, this.globalHide);
      window.addEventListener(CONSTANT.GLOBAL.HIDE, this.globalHide, false); // ReactTooltip.rebuild

      window.removeEventListener(CONSTANT.GLOBAL.REBUILD, this.globalRebuild);
      window.addEventListener(CONSTANT.GLOBAL.REBUILD, this.globalRebuild, false); // ReactTooltip.show

      window.removeEventListener(CONSTANT.GLOBAL.SHOW, this.globalShow);
      window.addEventListener(CONSTANT.GLOBAL.SHOW, this.globalShow, false); // Resize

      if (resizeHide) {
        window.removeEventListener('resize', this.onWindowResize);
        window.addEventListener('resize', this.onWindowResize, false);
      }
    };

    target.prototype.unbindWindowEvents = function () {
      window.removeEventListener(CONSTANT.GLOBAL.HIDE, this.globalHide);
      window.removeEventListener(CONSTANT.GLOBAL.REBUILD, this.globalRebuild);
      window.removeEventListener(CONSTANT.GLOBAL.SHOW, this.globalShow);
      window.removeEventListener('resize', this.onWindowResize);
    };
    /**
     * invoked by resize event of window
     */


    target.prototype.onWindowResize = function () {
      if (!this.mount) return;
      this.hideTooltip();
    };
  }

  /**
   * Custom events to control showing and hiding of tooltip
   *
   * @attributes
   * - `event` {String}
   * - `eventOff` {String}
   */
  var checkStatus = function checkStatus(dataEventOff, e) {
    var show = this.state.show;
    var id = this.props.id;
    var isCapture = this.isCapture(e.currentTarget);
    var currentItem = e.currentTarget.getAttribute('currentItem');
    if (!isCapture) e.stopPropagation();

    if (show && currentItem === 'true') {
      if (!dataEventOff) this.hideTooltip(e);
    } else {
      e.currentTarget.setAttribute('currentItem', 'true');
      setUntargetItems(e.currentTarget, this.getTargetArray(id));
      this.showTooltip(e);
    }
  };

  var setUntargetItems = function setUntargetItems(currentTarget, targetArray) {
    for (var i = 0; i < targetArray.length; i++) {
      if (currentTarget !== targetArray[i]) {
        targetArray[i].setAttribute('currentItem', 'false');
      } else {
        targetArray[i].setAttribute('currentItem', 'true');
      }
    }
  };

  var customListeners = {
    id: '9b69f92e-d3fe-498b-b1b4-c5e63a51b0cf',
    set: function set(target, event, listener) {
      if (this.id in target) {
        var map = target[this.id];
        map[event] = listener;
      } else {
        // this is workaround for WeakMap, which is not supported in older browsers, such as IE
        Object.defineProperty(target, this.id, {
          configurable: true,
          value: _defineProperty$1({}, event, listener)
        });
      }
    },
    get: function get(target, event) {
      var map = target[this.id];

      if (map !== undefined) {
        return map[event];
      }
    }
  };
  function customEvent (target) {
    target.prototype.isCustomEvent = function (ele) {
      var event = this.state.event;
      return event || !!ele.getAttribute('data-event');
    };
    /* Bind listener for custom event */


    target.prototype.customBindListener = function (ele) {
      var _this = this;

      var _this$state = this.state,
          event = _this$state.event,
          eventOff = _this$state.eventOff;
      var dataEvent = ele.getAttribute('data-event') || event;
      var dataEventOff = ele.getAttribute('data-event-off') || eventOff;
      dataEvent.split(' ').forEach(function (event) {
        ele.removeEventListener(event, customListeners.get(ele, event));
        var customListener = checkStatus.bind(_this, dataEventOff);
        customListeners.set(ele, event, customListener);
        ele.addEventListener(event, customListener, false);
      });

      if (dataEventOff) {
        dataEventOff.split(' ').forEach(function (event) {
          ele.removeEventListener(event, _this.hideTooltip);
          ele.addEventListener(event, _this.hideTooltip, false);
        });
      }
    };
    /* Unbind listener for custom event */


    target.prototype.customUnbindListener = function (ele) {
      var _this$state2 = this.state,
          event = _this$state2.event,
          eventOff = _this$state2.eventOff;
      var dataEvent = event || ele.getAttribute('data-event');
      var dataEventOff = eventOff || ele.getAttribute('data-event-off');
      ele.removeEventListener(dataEvent, customListeners.get(ele, event));
      if (dataEventOff) ele.removeEventListener(dataEventOff, this.hideTooltip);
    };
  }

  /**
   * Util method to judge if it should follow capture model
   */
  function isCapture (target) {
    target.prototype.isCapture = function (currentTarget) {
      return currentTarget && currentTarget.getAttribute('data-iscapture') === 'true' || this.props.isCapture || false;
    };
  }

  /**
   * Util method to get effect
   */
  function getEffect (target) {
    target.prototype.getEffect = function (currentTarget) {
      var dataEffect = currentTarget.getAttribute('data-effect');
      return dataEffect || this.props.effect || 'float';
    };
  }

  /**
   * Util method to get effect
   */

  var makeProxy = function makeProxy(e) {
    var proxy = {};

    for (var key in e) {
      if (typeof e[key] === 'function') {
        proxy[key] = e[key].bind(e);
      } else {
        proxy[key] = e[key];
      }
    }

    return proxy;
  };

  var bodyListener = function bodyListener(callback, options, e) {
    var _options$respectEffec = options.respectEffect,
        respectEffect = _options$respectEffec === void 0 ? false : _options$respectEffec,
        _options$customEvent = options.customEvent,
        customEvent = _options$customEvent === void 0 ? false : _options$customEvent;
    var id = this.props.id;
    var tip = e.target.getAttribute('data-tip') || null;
    var forId = e.target.getAttribute('data-for') || null;
    var target = e.target;

    if (this.isCustomEvent(target) && !customEvent) {
      return;
    }

    var isTargetBelongsToTooltip = id == null && forId == null || forId === id;

    if (tip != null && (!respectEffect || this.getEffect(target) === 'float') && isTargetBelongsToTooltip) {
      var proxy = makeProxy(e);
      proxy.currentTarget = target;
      callback(proxy);
    }
  };

  var findCustomEvents = function findCustomEvents(targetArray, dataAttribute) {
    var events = {};
    targetArray.forEach(function (target) {
      var event = target.getAttribute(dataAttribute);
      if (event) event.split(' ').forEach(function (event) {
        return events[event] = true;
      });
    });
    return events;
  };

  var getBody = function getBody() {
    return document.getElementsByTagName('body')[0];
  };

  function bodyMode (target) {
    target.prototype.isBodyMode = function () {
      return !!this.props.bodyMode;
    };

    target.prototype.bindBodyListener = function (targetArray) {
      var _this = this;

      var _this$state = this.state,
          event = _this$state.event,
          eventOff = _this$state.eventOff,
          possibleCustomEvents = _this$state.possibleCustomEvents,
          possibleCustomEventsOff = _this$state.possibleCustomEventsOff;
      var body = getBody();
      var customEvents = findCustomEvents(targetArray, 'data-event');
      var customEventsOff = findCustomEvents(targetArray, 'data-event-off');
      if (event != null) customEvents[event] = true;
      if (eventOff != null) customEventsOff[eventOff] = true;
      possibleCustomEvents.split(' ').forEach(function (event) {
        return customEvents[event] = true;
      });
      possibleCustomEventsOff.split(' ').forEach(function (event) {
        return customEventsOff[event] = true;
      });
      this.unbindBodyListener(body);
      var listeners = this.bodyModeListeners = {};

      if (event == null) {
        listeners.mouseover = bodyListener.bind(this, this.showTooltip, {});
        listeners.mousemove = bodyListener.bind(this, this.updateTooltip, {
          respectEffect: true
        });
        listeners.mouseout = bodyListener.bind(this, this.hideTooltip, {});
      }

      for (var _event in customEvents) {
        listeners[_event] = bodyListener.bind(this, function (e) {
          var targetEventOff = e.currentTarget.getAttribute('data-event-off') || eventOff;
          checkStatus.call(_this, targetEventOff, e);
        }, {
          customEvent: true
        });
      }

      for (var _event2 in customEventsOff) {
        listeners[_event2] = bodyListener.bind(this, this.hideTooltip, {
          customEvent: true
        });
      }

      for (var _event3 in listeners) {
        body.addEventListener(_event3, listeners[_event3]);
      }
    };

    target.prototype.unbindBodyListener = function (body) {
      body = body || getBody();
      var listeners = this.bodyModeListeners;

      for (var event in listeners) {
        body.removeEventListener(event, listeners[event]);
      }
    };
  }

  /**
   * Tracking target removing from DOM.
   * It's necessary to hide tooltip when it's target disappears.
   * Otherwise, the tooltip would be shown forever until another target
   * is triggered.
   *
   * If MutationObserver is not available, this feature just doesn't work.
   */
  // https://hacks.mozilla.org/2012/05/dom-mutationobserver-reacting-to-dom-changes-without-killing-browser-performance/
  var getMutationObserverClass = function getMutationObserverClass() {
    return window.MutationObserver || window.WebKitMutationObserver || window.MozMutationObserver;
  };

  function trackRemoval (target) {
    target.prototype.bindRemovalTracker = function () {
      var _this = this;

      var MutationObserver = getMutationObserverClass();
      if (MutationObserver == null) return;
      var observer = new MutationObserver(function (mutations) {
        for (var m1 = 0; m1 < mutations.length; m1++) {
          var mutation = mutations[m1];

          for (var m2 = 0; m2 < mutation.removedNodes.length; m2++) {
            var element = mutation.removedNodes[m2];

            if (element === _this.state.currentTarget) {
              _this.hideTooltip();

              return;
            }
          }
        }
      });
      observer.observe(window.document, {
        childList: true,
        subtree: true
      });
      this.removalTracker = observer;
    };

    target.prototype.unbindRemovalTracker = function () {
      if (this.removalTracker) {
        this.removalTracker.disconnect();
        this.removalTracker = null;
      }
    };
  }

  /**
   * Calculate the position of tooltip
   *
   * @params
   * - `e` {Event} the event of current mouse
   * - `target` {Element} the currentTarget of the event
   * - `node` {DOM} the react-tooltip object
   * - `place` {String} top / right / bottom / left
   * - `effect` {String} float / solid
   * - `offset` {Object} the offset to default position
   *
   * @return {Object}
   * - `isNewState` {Bool} required
   * - `newState` {Object}
   * - `position` {Object} {left: {Number}, top: {Number}}
   */
  function getPosition (e, target, node, place, desiredPlace, effect, offset) {
    var _getDimensions = getDimensions(node),
        tipWidth = _getDimensions.width,
        tipHeight = _getDimensions.height;

    var _getDimensions2 = getDimensions(target),
        targetWidth = _getDimensions2.width,
        targetHeight = _getDimensions2.height;

    var _getCurrentOffset = getCurrentOffset(e, target, effect),
        mouseX = _getCurrentOffset.mouseX,
        mouseY = _getCurrentOffset.mouseY;

    var defaultOffset = getDefaultPosition(effect, targetWidth, targetHeight, tipWidth, tipHeight);

    var _calculateOffset = calculateOffset(offset),
        extraOffsetX = _calculateOffset.extraOffsetX,
        extraOffsetY = _calculateOffset.extraOffsetY;

    var windowWidth = window.innerWidth;
    var windowHeight = window.innerHeight;

    var _getParent = getParent(node),
        parentTop = _getParent.parentTop,
        parentLeft = _getParent.parentLeft; // Get the edge offset of the tooltip


    var getTipOffsetLeft = function getTipOffsetLeft(place) {
      var offsetX = defaultOffset[place].l;
      return mouseX + offsetX + extraOffsetX;
    };

    var getTipOffsetRight = function getTipOffsetRight(place) {
      var offsetX = defaultOffset[place].r;
      return mouseX + offsetX + extraOffsetX;
    };

    var getTipOffsetTop = function getTipOffsetTop(place) {
      var offsetY = defaultOffset[place].t;
      return mouseY + offsetY + extraOffsetY;
    };

    var getTipOffsetBottom = function getTipOffsetBottom(place) {
      var offsetY = defaultOffset[place].b;
      return mouseY + offsetY + extraOffsetY;
    }; //
    // Functions to test whether the tooltip's sides are inside
    // the client window for a given orientation p
    //
    //  _____________
    // |             | <-- Right side
    // | p = 'left'  |\
    // |             |/  |\
    // |_____________|   |_\  <-- Mouse
    //      / \           |
    //       |
    //       |
    //  Bottom side
    //


    var outsideLeft = function outsideLeft(p) {
      return getTipOffsetLeft(p) < 0;
    };

    var outsideRight = function outsideRight(p) {
      return getTipOffsetRight(p) > windowWidth;
    };

    var outsideTop = function outsideTop(p) {
      return getTipOffsetTop(p) < 0;
    };

    var outsideBottom = function outsideBottom(p) {
      return getTipOffsetBottom(p) > windowHeight;
    }; // Check whether the tooltip with orientation p is completely inside the client window


    var outside = function outside(p) {
      return outsideLeft(p) || outsideRight(p) || outsideTop(p) || outsideBottom(p);
    };

    var inside = function inside(p) {
      return !outside(p);
    };

    var placesList = ['top', 'bottom', 'left', 'right'];
    var insideList = [];

    for (var i = 0; i < 4; i++) {
      var p = placesList[i];

      if (inside(p)) {
        insideList.push(p);
      }
    }

    var isNewState = false;
    var newPlace;
    var shouldUpdatePlace = desiredPlace !== place;

    if (inside(desiredPlace) && shouldUpdatePlace) {
      isNewState = true;
      newPlace = desiredPlace;
    } else if (insideList.length > 0 && outside(desiredPlace) && outside(place)) {
      isNewState = true;
      newPlace = insideList[0];
    }

    if (isNewState) {
      return {
        isNewState: true,
        newState: {
          place: newPlace
        }
      };
    }

    return {
      isNewState: false,
      position: {
        left: parseInt(getTipOffsetLeft(place) - parentLeft, 10),
        top: parseInt(getTipOffsetTop(place) - parentTop, 10)
      }
    };
  }

  var getDimensions = function getDimensions(node) {
    var _node$getBoundingClie = node.getBoundingClientRect(),
        height = _node$getBoundingClie.height,
        width = _node$getBoundingClie.width;

    return {
      height: parseInt(height, 10),
      width: parseInt(width, 10)
    };
  }; // Get current mouse offset


  var getCurrentOffset = function getCurrentOffset(e, currentTarget, effect) {
    var boundingClientRect = currentTarget.getBoundingClientRect();
    var targetTop = boundingClientRect.top;
    var targetLeft = boundingClientRect.left;

    var _getDimensions3 = getDimensions(currentTarget),
        targetWidth = _getDimensions3.width,
        targetHeight = _getDimensions3.height;

    if (effect === 'float') {
      return {
        mouseX: e.clientX,
        mouseY: e.clientY
      };
    }

    return {
      mouseX: targetLeft + targetWidth / 2,
      mouseY: targetTop + targetHeight / 2
    };
  }; // List all possibility of tooltip final offset
  // This is useful in judging if it is necessary for tooltip to switch position when out of window


  var getDefaultPosition = function getDefaultPosition(effect, targetWidth, targetHeight, tipWidth, tipHeight) {
    var top;
    var right;
    var bottom;
    var left;
    var disToMouse = 3;
    var triangleHeight = 2;
    var cursorHeight = 12; // Optimize for float bottom only, cause the cursor will hide the tooltip

    if (effect === 'float') {
      top = {
        l: -(tipWidth / 2),
        r: tipWidth / 2,
        t: -(tipHeight + disToMouse + triangleHeight),
        b: -disToMouse
      };
      bottom = {
        l: -(tipWidth / 2),
        r: tipWidth / 2,
        t: disToMouse + cursorHeight,
        b: tipHeight + disToMouse + triangleHeight + cursorHeight
      };
      left = {
        l: -(tipWidth + disToMouse + triangleHeight),
        r: -disToMouse,
        t: -(tipHeight / 2),
        b: tipHeight / 2
      };
      right = {
        l: disToMouse,
        r: tipWidth + disToMouse + triangleHeight,
        t: -(tipHeight / 2),
        b: tipHeight / 2
      };
    } else if (effect === 'solid') {
      top = {
        l: -(tipWidth / 2),
        r: tipWidth / 2,
        t: -(targetHeight / 2 + tipHeight + triangleHeight),
        b: -(targetHeight / 2)
      };
      bottom = {
        l: -(tipWidth / 2),
        r: tipWidth / 2,
        t: targetHeight / 2,
        b: targetHeight / 2 + tipHeight + triangleHeight
      };
      left = {
        l: -(tipWidth + targetWidth / 2 + triangleHeight),
        r: -(targetWidth / 2),
        t: -(tipHeight / 2),
        b: tipHeight / 2
      };
      right = {
        l: targetWidth / 2,
        r: tipWidth + targetWidth / 2 + triangleHeight,
        t: -(tipHeight / 2),
        b: tipHeight / 2
      };
    }

    return {
      top: top,
      bottom: bottom,
      left: left,
      right: right
    };
  }; // Consider additional offset into position calculation


  var calculateOffset = function calculateOffset(offset) {
    var extraOffsetX = 0;
    var extraOffsetY = 0;

    if (Object.prototype.toString.apply(offset) === '[object String]') {
      offset = JSON.parse(offset.toString().replace(/'/g, '"'));
    }

    for (var key in offset) {
      if (key === 'top') {
        extraOffsetY -= parseInt(offset[key], 10);
      } else if (key === 'bottom') {
        extraOffsetY += parseInt(offset[key], 10);
      } else if (key === 'left') {
        extraOffsetX -= parseInt(offset[key], 10);
      } else if (key === 'right') {
        extraOffsetX += parseInt(offset[key], 10);
      }
    }

    return {
      extraOffsetX: extraOffsetX,
      extraOffsetY: extraOffsetY
    };
  }; // Get the offset of the parent elements


  var getParent = function getParent(currentTarget) {
    var currentParent = currentTarget;

    while (currentParent) {
      var computedStyle = window.getComputedStyle(currentParent); // transform and will-change: transform change the containing block
      // https://developer.mozilla.org/en-US/docs/Web/CSS/Containing_Block

      if (computedStyle.getPropertyValue('transform') !== 'none' || computedStyle.getPropertyValue('will-change') === 'transform') break;
      currentParent = currentParent.parentElement;
    }

    var parentTop = currentParent && currentParent.getBoundingClientRect().top || 0;
    var parentLeft = currentParent && currentParent.getBoundingClientRect().left || 0;
    return {
      parentTop: parentTop,
      parentLeft: parentLeft
    };
  };

  /**
   * To get the tooltip content
   * it may comes from data-tip or this.props.children
   * it should support multiline
   *
   * @params
   * - `tip` {String} value of data-tip
   * - `children` {ReactElement} this.props.children
   * - `multiline` {Any} could be Bool(true/false) or String('true'/'false')
   *
   * @return
   * - String or react component
   */
  function getTipContent (tip, children, getContent, multiline) {
    if (children) return children;
    if (getContent !== undefined && getContent !== null) return getContent; // getContent can be 0, '', etc.

    if (getContent === null) return null; // Tip not exist and children is null or undefined

    var regexp = /<br\s*\/?>/;

    if (!multiline || multiline === 'false' || !regexp.test(tip)) {
      // No trim(), so that user can keep their input
      return tip;
    } // Multiline tooltip content


    return tip.split(regexp).map(function (d, i) {
      return React.createElement("span", {
        key: i,
        className: "multi-line"
      }, d);
    });
  }

  /**
   * Support aria- and role in ReactTooltip
   *
   * @params props {Object}
   * @return {Object}
   */
  function parseAria(props) {
    var ariaObj = {};
    Object.keys(props).filter(function (prop) {
      // aria-xxx and role is acceptable
      return /(^aria-\w+$|^role$)/.test(prop);
    }).forEach(function (prop) {
      ariaObj[prop] = props[prop];
    });
    return ariaObj;
  }

  /**
   * Convert nodelist to array
   * @see https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/core/createArrayFromMixed.js#L24
   * NodeLists are functions in Safari
   */
  function nodeListToArray (nodeList) {
    var length = nodeList.length;

    if (nodeList.hasOwnProperty) {
      return Array.prototype.slice.call(nodeList);
    }

    return new Array(length).fill().map(function (index) {
      return nodeList[index];
    });
  }

  function generateUUID() {
    return 't' + v4();
  }

  var baseCss = ".__react_component_tooltip {\n  border-radius: 3px;\n  display: inline-block;\n  font-size: 13px;\n  left: -999em;\n  opacity: 0;\n  padding: 8px 21px;\n  position: fixed;\n  pointer-events: none;\n  transition: opacity 0.3s ease-out;\n  top: -999em;\n  visibility: hidden;\n  z-index: 999;\n}\n.__react_component_tooltip.allow_hover, .__react_component_tooltip.allow_click {\n  pointer-events: auto;\n}\n.__react_component_tooltip::before, .__react_component_tooltip::after {\n  content: \"\";\n  width: 0;\n  height: 0;\n  position: absolute;\n}\n.__react_component_tooltip.show {\n  opacity: 0.9;\n  margin-top: 0;\n  margin-left: 0;\n  visibility: visible;\n}\n.__react_component_tooltip.place-top::before {\n  border-left: 10px solid transparent;\n  border-right: 10px solid transparent;\n  bottom: -8px;\n  left: 50%;\n  margin-left: -10px;\n}\n.__react_component_tooltip.place-bottom::before {\n  border-left: 10px solid transparent;\n  border-right: 10px solid transparent;\n  top: -8px;\n  left: 50%;\n  margin-left: -10px;\n}\n.__react_component_tooltip.place-left::before {\n  border-top: 6px solid transparent;\n  border-bottom: 6px solid transparent;\n  right: -8px;\n  top: 50%;\n  margin-top: -5px;\n}\n.__react_component_tooltip.place-right::before {\n  border-top: 6px solid transparent;\n  border-bottom: 6px solid transparent;\n  left: -8px;\n  top: 50%;\n  margin-top: -5px;\n}\n.__react_component_tooltip .multi-line {\n  display: block;\n  padding: 2px 0;\n  text-align: center;\n}";

  /**
   * Default pop-up style values (text color, background color).
   */
  var defaultColors = {
    dark: {
      text: '#fff',
      background: '#222',
      border: 'transparent',
      arrow: '#222'
    },
    success: {
      text: '#fff',
      background: '#8DC572',
      border: 'transparent',
      arrow: '#8DC572'
    },
    warning: {
      text: '#fff',
      background: '#F0AD4E',
      border: 'transparent',
      arrow: '#F0AD4E'
    },
    error: {
      text: '#fff',
      background: '#BE6464',
      border: 'transparent',
      arrow: '#BE6464'
    },
    info: {
      text: '#fff',
      background: '#337AB7',
      border: 'transparent',
      arrow: '#337AB7'
    },
    light: {
      text: '#222',
      background: '#fff',
      border: 'transparent',
      arrow: '#fff'
    }
  };
  function getDefaultPopupColors(type) {
    return defaultColors[type] ? _objectSpread2({}, defaultColors[type]) : undefined;
  }

  /**
   * Generates the specific tooltip style for use on render.
   */

  function generateTooltipStyle(uuid, customColors, type, hasBorder) {
    return generateStyle(uuid, getPopupColors(customColors, type, hasBorder));
  }
  /**
   * Generates the tooltip style rules based on the element-specified "data-type" property.
   */

  function generateStyle(uuid, colors) {
    var textColor = colors.text;
    var backgroundColor = colors.background;
    var borderColor = colors.border;
    var arrowColor = colors.arrow;
    return "\n  \t.".concat(uuid, " {\n\t    color: ").concat(textColor, ";\n\t    background: ").concat(backgroundColor, ";\n\t    border: 1px solid ").concat(borderColor, ";\n  \t}\n\n  \t.").concat(uuid, ".place-top {\n        margin-top: -10px;\n    }\n    .").concat(uuid, ".place-top::before {\n        border-top: 8px solid ").concat(borderColor, ";\n    }\n    .").concat(uuid, ".place-top::after {\n        border-left: 8px solid transparent;\n        border-right: 8px solid transparent;\n        bottom: -6px;\n        left: 50%;\n        margin-left: -8px;\n        border-top-color: ").concat(arrowColor, ";\n        border-top-style: solid;\n        border-top-width: 6px;\n    }\n\n    .").concat(uuid, ".place-bottom {\n        margin-top: 10px;\n    }\n    .").concat(uuid, ".place-bottom::before {\n        border-bottom: 8px solid ").concat(borderColor, ";\n    }\n    .").concat(uuid, ".place-bottom::after {\n        border-left: 8px solid transparent;\n        border-right: 8px solid transparent;\n        top: -6px;\n        left: 50%;\n        margin-left: -8px;\n        border-bottom-color: ").concat(arrowColor, ";\n        border-bottom-style: solid;\n        border-bottom-width: 6px;\n    }\n\n    .").concat(uuid, ".place-left {\n        margin-left: -10px;\n    }\n    .").concat(uuid, ".place-left::before {\n        border-left: 8px solid ").concat(borderColor, ";\n    }\n    .").concat(uuid, ".place-left::after {\n        border-top: 5px solid transparent;\n        border-bottom: 5px solid transparent;\n        right: -6px;\n        top: 50%;\n        margin-top: -4px;\n        border-left-color: ").concat(arrowColor, ";\n        border-left-style: solid;\n        border-left-width: 6px;\n    }\n\n    .").concat(uuid, ".place-right {\n        margin-left: 10px;\n    }\n    .").concat(uuid, ".place-right::before {\n        border-right: 8px solid ").concat(borderColor, ";\n    }\n    .").concat(uuid, ".place-right::after {\n        border-top: 5px solid transparent;\n        border-bottom: 5px solid transparent;\n        left: -6px;\n        top: 50%;\n        margin-top: -4px;\n        border-right-color: ").concat(arrowColor, ";\n        border-right-style: solid;\n        border-right-width: 6px;\n    }\n  ");
  }

  function getPopupColors(customColors, type, hasBorder) {
    var textColor = customColors.text;
    var backgroundColor = customColors.background;
    var borderColor = customColors.border;
    var arrowColor = customColors.arrow ? customColors.arrow : customColors.background;
    var colors = getDefaultPopupColors(type);

    if (textColor) {
      colors.text = textColor;
    }

    if (backgroundColor) {
      colors.background = backgroundColor;
    }

    if (hasBorder) {
      if (borderColor) {
        colors.border = borderColor;
      } else {
        colors.border = type === 'light' ? 'black' : 'white';
      }
    }

    if (arrowColor) {
      colors.arrow = arrowColor;
    }

    return colors;
  }

  var commonjsGlobal = typeof globalThis !== 'undefined' ? globalThis : typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

  function createCommonjsModule$1(fn, module) {
  	return module = { exports: {} }, fn(module, module.exports), module.exports;
  }

  var check = function (it) {
    return it && it.Math == Math && it;
  };

  // https://github.com/zloirock/core-js/issues/86#issuecomment-115759028
  var global_1 =
    // eslint-disable-next-line es/no-global-this -- safe
    check(typeof globalThis == 'object' && globalThis) ||
    check(typeof window == 'object' && window) ||
    // eslint-disable-next-line no-restricted-globals -- safe
    check(typeof self == 'object' && self) ||
    check(typeof commonjsGlobal == 'object' && commonjsGlobal) ||
    // eslint-disable-next-line no-new-func -- fallback
    (function () { return this; })() || Function('return this')();

  var fails = function (exec) {
    try {
      return !!exec();
    } catch (error) {
      return true;
    }
  };

  // Detect IE8's incomplete defineProperty implementation
  var descriptors = !fails(function () {
    // eslint-disable-next-line es/no-object-defineproperty -- required for testing
    return Object.defineProperty({}, 1, { get: function () { return 7; } })[1] != 7;
  });

  var $propertyIsEnumerable = {}.propertyIsEnumerable;
  // eslint-disable-next-line es/no-object-getownpropertydescriptor -- safe
  var getOwnPropertyDescriptor = Object.getOwnPropertyDescriptor;

  // Nashorn ~ JDK8 bug
  var NASHORN_BUG = getOwnPropertyDescriptor && !$propertyIsEnumerable.call({ 1: 2 }, 1);

  // `Object.prototype.propertyIsEnumerable` method implementation
  // https://tc39.es/ecma262/#sec-object.prototype.propertyisenumerable
  var f = NASHORN_BUG ? function propertyIsEnumerable(V) {
    var descriptor = getOwnPropertyDescriptor(this, V);
    return !!descriptor && descriptor.enumerable;
  } : $propertyIsEnumerable;

  var objectPropertyIsEnumerable = {
  	f: f
  };

  var createPropertyDescriptor = function (bitmap, value) {
    return {
      enumerable: !(bitmap & 1),
      configurable: !(bitmap & 2),
      writable: !(bitmap & 4),
      value: value
    };
  };

  var toString = {}.toString;

  var classofRaw = function (it) {
    return toString.call(it).slice(8, -1);
  };

  var split = ''.split;

  // fallback for non-array-like ES3 and non-enumerable old V8 strings
  var indexedObject = fails(function () {
    // throws an error in rhino, see https://github.com/mozilla/rhino/issues/346
    // eslint-disable-next-line no-prototype-builtins -- safe
    return !Object('z').propertyIsEnumerable(0);
  }) ? function (it) {
    return classofRaw(it) == 'String' ? split.call(it, '') : Object(it);
  } : Object;

  // `RequireObjectCoercible` abstract operation
  // https://tc39.es/ecma262/#sec-requireobjectcoercible
  var requireObjectCoercible = function (it) {
    if (it == undefined) throw TypeError("Can't call method on " + it);
    return it;
  };

  // toObject with fallback for non-array-like ES3 strings



  var toIndexedObject = function (it) {
    return indexedObject(requireObjectCoercible(it));
  };

  var isObject = function (it) {
    return typeof it === 'object' ? it !== null : typeof it === 'function';
  };

  // `ToPrimitive` abstract operation
  // https://tc39.es/ecma262/#sec-toprimitive
  // instead of the ES6 spec version, we didn't implement @@toPrimitive case
  // and the second argument - flag - preferred type is a string
  var toPrimitive = function (input, PREFERRED_STRING) {
    if (!isObject(input)) return input;
    var fn, val;
    if (PREFERRED_STRING && typeof (fn = input.toString) == 'function' && !isObject(val = fn.call(input))) return val;
    if (typeof (fn = input.valueOf) == 'function' && !isObject(val = fn.call(input))) return val;
    if (!PREFERRED_STRING && typeof (fn = input.toString) == 'function' && !isObject(val = fn.call(input))) return val;
    throw TypeError("Can't convert object to primitive value");
  };

  // `ToObject` abstract operation
  // https://tc39.es/ecma262/#sec-toobject
  var toObject$1 = function (argument) {
    return Object(requireObjectCoercible(argument));
  };

  var hasOwnProperty$1 = {}.hasOwnProperty;

  var has$2 = function hasOwn(it, key) {
    return hasOwnProperty$1.call(toObject$1(it), key);
  };

  var document$1 = global_1.document;
  // typeof document.createElement is 'object' in old IE
  var EXISTS = isObject(document$1) && isObject(document$1.createElement);

  var documentCreateElement = function (it) {
    return EXISTS ? document$1.createElement(it) : {};
  };

  // Thank's IE8 for his funny defineProperty
  var ie8DomDefine = !descriptors && !fails(function () {
    // eslint-disable-next-line es/no-object-defineproperty -- requied for testing
    return Object.defineProperty(documentCreateElement('div'), 'a', {
      get: function () { return 7; }
    }).a != 7;
  });

  // eslint-disable-next-line es/no-object-getownpropertydescriptor -- safe
  var $getOwnPropertyDescriptor = Object.getOwnPropertyDescriptor;

  // `Object.getOwnPropertyDescriptor` method
  // https://tc39.es/ecma262/#sec-object.getownpropertydescriptor
  var f$1 = descriptors ? $getOwnPropertyDescriptor : function getOwnPropertyDescriptor(O, P) {
    O = toIndexedObject(O);
    P = toPrimitive(P, true);
    if (ie8DomDefine) try {
      return $getOwnPropertyDescriptor(O, P);
    } catch (error) { /* empty */ }
    if (has$2(O, P)) return createPropertyDescriptor(!objectPropertyIsEnumerable.f.call(O, P), O[P]);
  };

  var objectGetOwnPropertyDescriptor = {
  	f: f$1
  };

  var anObject = function (it) {
    if (!isObject(it)) {
      throw TypeError(String(it) + ' is not an object');
    } return it;
  };

  // eslint-disable-next-line es/no-object-defineproperty -- safe
  var $defineProperty = Object.defineProperty;

  // `Object.defineProperty` method
  // https://tc39.es/ecma262/#sec-object.defineproperty
  var f$2 = descriptors ? $defineProperty : function defineProperty(O, P, Attributes) {
    anObject(O);
    P = toPrimitive(P, true);
    anObject(Attributes);
    if (ie8DomDefine) try {
      return $defineProperty(O, P, Attributes);
    } catch (error) { /* empty */ }
    if ('get' in Attributes || 'set' in Attributes) throw TypeError('Accessors not supported');
    if ('value' in Attributes) O[P] = Attributes.value;
    return O;
  };

  var objectDefineProperty = {
  	f: f$2
  };

  var createNonEnumerableProperty = descriptors ? function (object, key, value) {
    return objectDefineProperty.f(object, key, createPropertyDescriptor(1, value));
  } : function (object, key, value) {
    object[key] = value;
    return object;
  };

  var setGlobal = function (key, value) {
    try {
      createNonEnumerableProperty(global_1, key, value);
    } catch (error) {
      global_1[key] = value;
    } return value;
  };

  var SHARED = '__core-js_shared__';
  var store = global_1[SHARED] || setGlobal(SHARED, {});

  var sharedStore = store;

  var functionToString = Function.toString;

  // this helper broken in `3.4.1-3.4.4`, so we can't use `shared` helper
  if (typeof sharedStore.inspectSource != 'function') {
    sharedStore.inspectSource = function (it) {
      return functionToString.call(it);
    };
  }

  var inspectSource = sharedStore.inspectSource;

  var WeakMap = global_1.WeakMap;

  var nativeWeakMap = typeof WeakMap === 'function' && /native code/.test(inspectSource(WeakMap));

  var shared = createCommonjsModule$1(function (module) {
  (module.exports = function (key, value) {
    return sharedStore[key] || (sharedStore[key] = value !== undefined ? value : {});
  })('versions', []).push({
    version: '3.12.1',
    mode:  'global',
    copyright: '© 2021 Denis Pushkarev (zloirock.ru)'
  });
  });

  var id = 0;
  var postfix = Math.random();

  var uid = function (key) {
    return 'Symbol(' + String(key === undefined ? '' : key) + ')_' + (++id + postfix).toString(36);
  };

  var keys = shared('keys');

  var sharedKey = function (key) {
    return keys[key] || (keys[key] = uid(key));
  };

  var hiddenKeys = {};

  var OBJECT_ALREADY_INITIALIZED = 'Object already initialized';
  var WeakMap$1 = global_1.WeakMap;
  var set, get, has$1$1;

  var enforce = function (it) {
    return has$1$1(it) ? get(it) : set(it, {});
  };

  var getterFor = function (TYPE) {
    return function (it) {
      var state;
      if (!isObject(it) || (state = get(it)).type !== TYPE) {
        throw TypeError('Incompatible receiver, ' + TYPE + ' required');
      } return state;
    };
  };

  if (nativeWeakMap || sharedStore.state) {
    var store$1 = sharedStore.state || (sharedStore.state = new WeakMap$1());
    var wmget = store$1.get;
    var wmhas = store$1.has;
    var wmset = store$1.set;
    set = function (it, metadata) {
      if (wmhas.call(store$1, it)) throw new TypeError(OBJECT_ALREADY_INITIALIZED);
      metadata.facade = it;
      wmset.call(store$1, it, metadata);
      return metadata;
    };
    get = function (it) {
      return wmget.call(store$1, it) || {};
    };
    has$1$1 = function (it) {
      return wmhas.call(store$1, it);
    };
  } else {
    var STATE = sharedKey('state');
    hiddenKeys[STATE] = true;
    set = function (it, metadata) {
      if (has$2(it, STATE)) throw new TypeError(OBJECT_ALREADY_INITIALIZED);
      metadata.facade = it;
      createNonEnumerableProperty(it, STATE, metadata);
      return metadata;
    };
    get = function (it) {
      return has$2(it, STATE) ? it[STATE] : {};
    };
    has$1$1 = function (it) {
      return has$2(it, STATE);
    };
  }

  var internalState = {
    set: set,
    get: get,
    has: has$1$1,
    enforce: enforce,
    getterFor: getterFor
  };

  var redefine = createCommonjsModule$1(function (module) {
  var getInternalState = internalState.get;
  var enforceInternalState = internalState.enforce;
  var TEMPLATE = String(String).split('String');

  (module.exports = function (O, key, value, options) {
    var unsafe = options ? !!options.unsafe : false;
    var simple = options ? !!options.enumerable : false;
    var noTargetGet = options ? !!options.noTargetGet : false;
    var state;
    if (typeof value == 'function') {
      if (typeof key == 'string' && !has$2(value, 'name')) {
        createNonEnumerableProperty(value, 'name', key);
      }
      state = enforceInternalState(value);
      if (!state.source) {
        state.source = TEMPLATE.join(typeof key == 'string' ? key : '');
      }
    }
    if (O === global_1) {
      if (simple) O[key] = value;
      else setGlobal(key, value);
      return;
    } else if (!unsafe) {
      delete O[key];
    } else if (!noTargetGet && O[key]) {
      simple = true;
    }
    if (simple) O[key] = value;
    else createNonEnumerableProperty(O, key, value);
  // add fake Function#toString for correct work wrapped methods / constructors with methods like LoDash isNative
  })(Function.prototype, 'toString', function toString() {
    return typeof this == 'function' && getInternalState(this).source || inspectSource(this);
  });
  });

  var path = global_1;

  var aFunction = function (variable) {
    return typeof variable == 'function' ? variable : undefined;
  };

  var getBuiltIn = function (namespace, method) {
    return arguments.length < 2 ? aFunction(path[namespace]) || aFunction(global_1[namespace])
      : path[namespace] && path[namespace][method] || global_1[namespace] && global_1[namespace][method];
  };

  var ceil = Math.ceil;
  var floor = Math.floor;

  // `ToInteger` abstract operation
  // https://tc39.es/ecma262/#sec-tointeger
  var toInteger = function (argument) {
    return isNaN(argument = +argument) ? 0 : (argument > 0 ? floor : ceil)(argument);
  };

  var min = Math.min;

  // `ToLength` abstract operation
  // https://tc39.es/ecma262/#sec-tolength
  var toLength = function (argument) {
    return argument > 0 ? min(toInteger(argument), 0x1FFFFFFFFFFFFF) : 0; // 2 ** 53 - 1 == 9007199254740991
  };

  var max = Math.max;
  var min$1 = Math.min;

  // Helper for a popular repeating case of the spec:
  // Let integer be ? ToInteger(index).
  // If integer < 0, let result be max((length + integer), 0); else let result be min(integer, length).
  var toAbsoluteIndex = function (index, length) {
    var integer = toInteger(index);
    return integer < 0 ? max(integer + length, 0) : min$1(integer, length);
  };

  // `Array.prototype.{ indexOf, includes }` methods implementation
  var createMethod = function (IS_INCLUDES) {
    return function ($this, el, fromIndex) {
      var O = toIndexedObject($this);
      var length = toLength(O.length);
      var index = toAbsoluteIndex(fromIndex, length);
      var value;
      // Array#includes uses SameValueZero equality algorithm
      // eslint-disable-next-line no-self-compare -- NaN check
      if (IS_INCLUDES && el != el) while (length > index) {
        value = O[index++];
        // eslint-disable-next-line no-self-compare -- NaN check
        if (value != value) return true;
      // Array#indexOf ignores holes, Array#includes - not
      } else for (;length > index; index++) {
        if ((IS_INCLUDES || index in O) && O[index] === el) return IS_INCLUDES || index || 0;
      } return !IS_INCLUDES && -1;
    };
  };

  var arrayIncludes = {
    // `Array.prototype.includes` method
    // https://tc39.es/ecma262/#sec-array.prototype.includes
    includes: createMethod(true),
    // `Array.prototype.indexOf` method
    // https://tc39.es/ecma262/#sec-array.prototype.indexof
    indexOf: createMethod(false)
  };

  var indexOf = arrayIncludes.indexOf;


  var objectKeysInternal = function (object, names) {
    var O = toIndexedObject(object);
    var i = 0;
    var result = [];
    var key;
    for (key in O) !has$2(hiddenKeys, key) && has$2(O, key) && result.push(key);
    // Don't enum bug & hidden keys
    while (names.length > i) if (has$2(O, key = names[i++])) {
      ~indexOf(result, key) || result.push(key);
    }
    return result;
  };

  // IE8- don't enum bug keys
  var enumBugKeys = [
    'constructor',
    'hasOwnProperty',
    'isPrototypeOf',
    'propertyIsEnumerable',
    'toLocaleString',
    'toString',
    'valueOf'
  ];

  var hiddenKeys$1 = enumBugKeys.concat('length', 'prototype');

  // `Object.getOwnPropertyNames` method
  // https://tc39.es/ecma262/#sec-object.getownpropertynames
  // eslint-disable-next-line es/no-object-getownpropertynames -- safe
  var f$3 = Object.getOwnPropertyNames || function getOwnPropertyNames(O) {
    return objectKeysInternal(O, hiddenKeys$1);
  };

  var objectGetOwnPropertyNames = {
  	f: f$3
  };

  // eslint-disable-next-line es/no-object-getownpropertysymbols -- safe
  var f$4 = Object.getOwnPropertySymbols;

  var objectGetOwnPropertySymbols = {
  	f: f$4
  };

  // all object keys, includes non-enumerable and symbols
  var ownKeys$1 = getBuiltIn('Reflect', 'ownKeys') || function ownKeys(it) {
    var keys = objectGetOwnPropertyNames.f(anObject(it));
    var getOwnPropertySymbols = objectGetOwnPropertySymbols.f;
    return getOwnPropertySymbols ? keys.concat(getOwnPropertySymbols(it)) : keys;
  };

  var copyConstructorProperties = function (target, source) {
    var keys = ownKeys$1(source);
    var defineProperty = objectDefineProperty.f;
    var getOwnPropertyDescriptor = objectGetOwnPropertyDescriptor.f;
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i];
      if (!has$2(target, key)) defineProperty(target, key, getOwnPropertyDescriptor(source, key));
    }
  };

  var replacement = /#|\.prototype\./;

  var isForced = function (feature, detection) {
    var value = data[normalize(feature)];
    return value == POLYFILL ? true
      : value == NATIVE ? false
      : typeof detection == 'function' ? fails(detection)
      : !!detection;
  };

  var normalize = isForced.normalize = function (string) {
    return String(string).replace(replacement, '.').toLowerCase();
  };

  var data = isForced.data = {};
  var NATIVE = isForced.NATIVE = 'N';
  var POLYFILL = isForced.POLYFILL = 'P';

  var isForced_1 = isForced;

  var getOwnPropertyDescriptor$1 = objectGetOwnPropertyDescriptor.f;






  /*
    options.target      - name of the target object
    options.global      - target is the global object
    options.stat        - export as static methods of target
    options.proto       - export as prototype methods of target
    options.real        - real prototype method for the `pure` version
    options.forced      - export even if the native feature is available
    options.bind        - bind methods to the target, required for the `pure` version
    options.wrap        - wrap constructors to preventing global pollution, required for the `pure` version
    options.unsafe      - use the simple assignment of property instead of delete + defineProperty
    options.sham        - add a flag to not completely full polyfills
    options.enumerable  - export as enumerable property
    options.noTargetGet - prevent calling a getter on target
  */
  var _export = function (options, source) {
    var TARGET = options.target;
    var GLOBAL = options.global;
    var STATIC = options.stat;
    var FORCED, target, key, targetProperty, sourceProperty, descriptor;
    if (GLOBAL) {
      target = global_1;
    } else if (STATIC) {
      target = global_1[TARGET] || setGlobal(TARGET, {});
    } else {
      target = (global_1[TARGET] || {}).prototype;
    }
    if (target) for (key in source) {
      sourceProperty = source[key];
      if (options.noTargetGet) {
        descriptor = getOwnPropertyDescriptor$1(target, key);
        targetProperty = descriptor && descriptor.value;
      } else targetProperty = target[key];
      FORCED = isForced_1(GLOBAL ? key : TARGET + (STATIC ? '.' : '#') + key, options.forced);
      // contained in target
      if (!FORCED && targetProperty !== undefined) {
        if (typeof sourceProperty === typeof targetProperty) continue;
        copyConstructorProperties(sourceProperty, targetProperty);
      }
      // add a flag to not completely full polyfills
      if (options.sham || (targetProperty && targetProperty.sham)) {
        createNonEnumerableProperty(sourceProperty, 'sham', true);
      }
      // extend global
      redefine(target, key, sourceProperty, options);
    }
  };

  var aFunction$1 = function (it) {
    if (typeof it != 'function') {
      throw TypeError(String(it) + ' is not a function');
    } return it;
  };

  // optional / simple context binding
  var functionBindContext = function (fn, that, length) {
    aFunction$1(fn);
    if (that === undefined) return fn;
    switch (length) {
      case 0: return function () {
        return fn.call(that);
      };
      case 1: return function (a) {
        return fn.call(that, a);
      };
      case 2: return function (a, b) {
        return fn.call(that, a, b);
      };
      case 3: return function (a, b, c) {
        return fn.call(that, a, b, c);
      };
    }
    return function (/* ...args */) {
      return fn.apply(that, arguments);
    };
  };

  // `IsArray` abstract operation
  // https://tc39.es/ecma262/#sec-isarray
  // eslint-disable-next-line es/no-array-isarray -- safe
  var isArray = Array.isArray || function isArray(arg) {
    return classofRaw(arg) == 'Array';
  };

  var engineUserAgent = getBuiltIn('navigator', 'userAgent') || '';

  var process = global_1.process;
  var versions = process && process.versions;
  var v8 = versions && versions.v8;
  var match, version;

  if (v8) {
    match = v8.split('.');
    version = match[0] < 4 ? 1 : match[0] + match[1];
  } else if (engineUserAgent) {
    match = engineUserAgent.match(/Edge\/(\d+)/);
    if (!match || match[1] >= 74) {
      match = engineUserAgent.match(/Chrome\/(\d+)/);
      if (match) version = match[1];
    }
  }

  var engineV8Version = version && +version;

  /* eslint-disable es/no-symbol -- required for testing */



  // eslint-disable-next-line es/no-object-getownpropertysymbols -- required for testing
  var nativeSymbol = !!Object.getOwnPropertySymbols && !fails(function () {
    return !String(Symbol()) ||
      // Chrome 38 Symbol has incorrect toString conversion
      // Chrome 38-40 symbols are not inherited from DOM collections prototypes to instances
      !Symbol.sham && engineV8Version && engineV8Version < 41;
  });

  /* eslint-disable es/no-symbol -- required for testing */


  var useSymbolAsUid = nativeSymbol
    && !Symbol.sham
    && typeof Symbol.iterator == 'symbol';

  var WellKnownSymbolsStore = shared('wks');
  var Symbol$1 = global_1.Symbol;
  var createWellKnownSymbol = useSymbolAsUid ? Symbol$1 : Symbol$1 && Symbol$1.withoutSetter || uid;

  var wellKnownSymbol = function (name) {
    if (!has$2(WellKnownSymbolsStore, name) || !(nativeSymbol || typeof WellKnownSymbolsStore[name] == 'string')) {
      if (nativeSymbol && has$2(Symbol$1, name)) {
        WellKnownSymbolsStore[name] = Symbol$1[name];
      } else {
        WellKnownSymbolsStore[name] = createWellKnownSymbol('Symbol.' + name);
      }
    } return WellKnownSymbolsStore[name];
  };

  var SPECIES = wellKnownSymbol('species');

  // `ArraySpeciesCreate` abstract operation
  // https://tc39.es/ecma262/#sec-arrayspeciescreate
  var arraySpeciesCreate = function (originalArray, length) {
    var C;
    if (isArray(originalArray)) {
      C = originalArray.constructor;
      // cross-realm fallback
      if (typeof C == 'function' && (C === Array || isArray(C.prototype))) C = undefined;
      else if (isObject(C)) {
        C = C[SPECIES];
        if (C === null) C = undefined;
      }
    } return new (C === undefined ? Array : C)(length === 0 ? 0 : length);
  };

  var push = [].push;

  // `Array.prototype.{ forEach, map, filter, some, every, find, findIndex, filterOut }` methods implementation
  var createMethod$1 = function (TYPE) {
    var IS_MAP = TYPE == 1;
    var IS_FILTER = TYPE == 2;
    var IS_SOME = TYPE == 3;
    var IS_EVERY = TYPE == 4;
    var IS_FIND_INDEX = TYPE == 6;
    var IS_FILTER_OUT = TYPE == 7;
    var NO_HOLES = TYPE == 5 || IS_FIND_INDEX;
    return function ($this, callbackfn, that, specificCreate) {
      var O = toObject$1($this);
      var self = indexedObject(O);
      var boundFunction = functionBindContext(callbackfn, that, 3);
      var length = toLength(self.length);
      var index = 0;
      var create = specificCreate || arraySpeciesCreate;
      var target = IS_MAP ? create($this, length) : IS_FILTER || IS_FILTER_OUT ? create($this, 0) : undefined;
      var value, result;
      for (;length > index; index++) if (NO_HOLES || index in self) {
        value = self[index];
        result = boundFunction(value, index, O);
        if (TYPE) {
          if (IS_MAP) target[index] = result; // map
          else if (result) switch (TYPE) {
            case 3: return true;              // some
            case 5: return value;             // find
            case 6: return index;             // findIndex
            case 2: push.call(target, value); // filter
          } else switch (TYPE) {
            case 4: return false;             // every
            case 7: push.call(target, value); // filterOut
          }
        }
      }
      return IS_FIND_INDEX ? -1 : IS_SOME || IS_EVERY ? IS_EVERY : target;
    };
  };

  var arrayIteration = {
    // `Array.prototype.forEach` method
    // https://tc39.es/ecma262/#sec-array.prototype.foreach
    forEach: createMethod$1(0),
    // `Array.prototype.map` method
    // https://tc39.es/ecma262/#sec-array.prototype.map
    map: createMethod$1(1),
    // `Array.prototype.filter` method
    // https://tc39.es/ecma262/#sec-array.prototype.filter
    filter: createMethod$1(2),
    // `Array.prototype.some` method
    // https://tc39.es/ecma262/#sec-array.prototype.some
    some: createMethod$1(3),
    // `Array.prototype.every` method
    // https://tc39.es/ecma262/#sec-array.prototype.every
    every: createMethod$1(4),
    // `Array.prototype.find` method
    // https://tc39.es/ecma262/#sec-array.prototype.find
    find: createMethod$1(5),
    // `Array.prototype.findIndex` method
    // https://tc39.es/ecma262/#sec-array.prototype.findIndex
    findIndex: createMethod$1(6),
    // `Array.prototype.filterOut` method
    // https://github.com/tc39/proposal-array-filtering
    filterOut: createMethod$1(7)
  };

  // `Object.keys` method
  // https://tc39.es/ecma262/#sec-object.keys
  // eslint-disable-next-line es/no-object-keys -- safe
  var objectKeys = Object.keys || function keys(O) {
    return objectKeysInternal(O, enumBugKeys);
  };

  // `Object.defineProperties` method
  // https://tc39.es/ecma262/#sec-object.defineproperties
  // eslint-disable-next-line es/no-object-defineproperties -- safe
  var objectDefineProperties = descriptors ? Object.defineProperties : function defineProperties(O, Properties) {
    anObject(O);
    var keys = objectKeys(Properties);
    var length = keys.length;
    var index = 0;
    var key;
    while (length > index) objectDefineProperty.f(O, key = keys[index++], Properties[key]);
    return O;
  };

  var html = getBuiltIn('document', 'documentElement');

  var GT = '>';
  var LT = '<';
  var PROTOTYPE = 'prototype';
  var SCRIPT = 'script';
  var IE_PROTO = sharedKey('IE_PROTO');

  var EmptyConstructor = function () { /* empty */ };

  var scriptTag = function (content) {
    return LT + SCRIPT + GT + content + LT + '/' + SCRIPT + GT;
  };

  // Create object with fake `null` prototype: use ActiveX Object with cleared prototype
  var NullProtoObjectViaActiveX = function (activeXDocument) {
    activeXDocument.write(scriptTag(''));
    activeXDocument.close();
    var temp = activeXDocument.parentWindow.Object;
    activeXDocument = null; // avoid memory leak
    return temp;
  };

  // Create object with fake `null` prototype: use iframe Object with cleared prototype
  var NullProtoObjectViaIFrame = function () {
    // Thrash, waste and sodomy: IE GC bug
    var iframe = documentCreateElement('iframe');
    var JS = 'java' + SCRIPT + ':';
    var iframeDocument;
    iframe.style.display = 'none';
    html.appendChild(iframe);
    // https://github.com/zloirock/core-js/issues/475
    iframe.src = String(JS);
    iframeDocument = iframe.contentWindow.document;
    iframeDocument.open();
    iframeDocument.write(scriptTag('document.F=Object'));
    iframeDocument.close();
    return iframeDocument.F;
  };

  // Check for document.domain and active x support
  // No need to use active x approach when document.domain is not set
  // see https://github.com/es-shims/es5-shim/issues/150
  // variation of https://github.com/kitcambridge/es5-shim/commit/4f738ac066346
  // avoid IE GC bug
  var activeXDocument;
  var NullProtoObject = function () {
    try {
      /* global ActiveXObject -- old IE */
      activeXDocument = document.domain && new ActiveXObject('htmlfile');
    } catch (error) { /* ignore */ }
    NullProtoObject = activeXDocument ? NullProtoObjectViaActiveX(activeXDocument) : NullProtoObjectViaIFrame();
    var length = enumBugKeys.length;
    while (length--) delete NullProtoObject[PROTOTYPE][enumBugKeys[length]];
    return NullProtoObject();
  };

  hiddenKeys[IE_PROTO] = true;

  // `Object.create` method
  // https://tc39.es/ecma262/#sec-object.create
  var objectCreate = Object.create || function create(O, Properties) {
    var result;
    if (O !== null) {
      EmptyConstructor[PROTOTYPE] = anObject(O);
      result = new EmptyConstructor();
      EmptyConstructor[PROTOTYPE] = null;
      // add "__proto__" for Object.getPrototypeOf polyfill
      result[IE_PROTO] = O;
    } else result = NullProtoObject();
    return Properties === undefined ? result : objectDefineProperties(result, Properties);
  };

  var UNSCOPABLES = wellKnownSymbol('unscopables');
  var ArrayPrototype = Array.prototype;

  // Array.prototype[@@unscopables]
  // https://tc39.es/ecma262/#sec-array.prototype-@@unscopables
  if (ArrayPrototype[UNSCOPABLES] == undefined) {
    objectDefineProperty.f(ArrayPrototype, UNSCOPABLES, {
      configurable: true,
      value: objectCreate(null)
    });
  }

  // add a key to Array.prototype[@@unscopables]
  var addToUnscopables = function (key) {
    ArrayPrototype[UNSCOPABLES][key] = true;
  };

  var $find = arrayIteration.find;


  var FIND = 'find';
  var SKIPS_HOLES = true;

  // Shouldn't skip holes
  if (FIND in []) Array(1)[FIND](function () { SKIPS_HOLES = false; });

  // `Array.prototype.find` method
  // https://tc39.es/ecma262/#sec-array.prototype.find
  _export({ target: 'Array', proto: true, forced: SKIPS_HOLES }, {
    find: function find(callbackfn /* , that = undefined */) {
      return $find(this, callbackfn, arguments.length > 1 ? arguments[1] : undefined);
    }
  });

  // https://tc39.es/ecma262/#sec-array.prototype-@@unscopables
  addToUnscopables(FIND);

  var _class, _class2, _temp;

  var ReactTooltip = staticMethods(_class = windowListener(_class = customEvent(_class = isCapture(_class = getEffect(_class = bodyMode(_class = trackRemoval(_class = (_temp = _class2 =
  /*#__PURE__*/
  function (_React$Component) {
    _inherits$1(ReactTooltip, _React$Component);

    _createClass$1(ReactTooltip, null, [{
      key: "propTypes",
      get: function get() {
        return {
          uuid: propTypes.string,
          children: propTypes.any,
          place: propTypes.string,
          type: propTypes.string,
          effect: propTypes.string,
          offset: propTypes.object,
          multiline: propTypes.bool,
          border: propTypes.bool,
          textColor: propTypes.string,
          backgroundColor: propTypes.string,
          borderColor: propTypes.string,
          arrowColor: propTypes.string,
          insecure: propTypes.bool,
          "class": propTypes.string,
          className: propTypes.string,
          id: propTypes.string,
          html: propTypes.bool,
          delayHide: propTypes.number,
          delayUpdate: propTypes.number,
          delayShow: propTypes.number,
          event: propTypes.string,
          eventOff: propTypes.string,
          isCapture: propTypes.bool,
          globalEventOff: propTypes.string,
          getContent: propTypes.any,
          afterShow: propTypes.func,
          afterHide: propTypes.func,
          overridePosition: propTypes.func,
          disable: propTypes.bool,
          scrollHide: propTypes.bool,
          resizeHide: propTypes.bool,
          wrapper: propTypes.string,
          bodyMode: propTypes.bool,
          possibleCustomEvents: propTypes.string,
          possibleCustomEventsOff: propTypes.string,
          clickable: propTypes.bool
        };
      }
    }]);

    function ReactTooltip(props) {
      var _this;

      _classCallCheck$1(this, ReactTooltip);

      _this = _possibleConstructorReturn$1(this, _getPrototypeOf$1(ReactTooltip).call(this, props));
      _this.state = {
        uuid: props.uuid || generateUUID(),
        place: props.place || 'top',
        // Direction of tooltip
        desiredPlace: props.place || 'top',
        type: 'dark',
        // Color theme of tooltip
        effect: 'float',
        // float or fixed
        show: false,
        border: false,
        customColors: {},
        offset: {},
        extraClass: '',
        html: false,
        delayHide: 0,
        delayShow: 0,
        event: props.event || null,
        eventOff: props.eventOff || null,
        currentEvent: null,
        // Current mouse event
        currentTarget: null,
        // Current target of mouse event
        ariaProps: parseAria(props),
        // aria- and role attributes
        isEmptyTip: false,
        disable: false,
        possibleCustomEvents: props.possibleCustomEvents || '',
        possibleCustomEventsOff: props.possibleCustomEventsOff || '',
        originTooltip: null,
        isMultiline: false
      };

      _this.bind(['showTooltip', 'updateTooltip', 'hideTooltip', 'hideTooltipOnScroll', 'getTooltipContent', 'globalRebuild', 'globalShow', 'globalHide', 'onWindowResize', 'mouseOnToolTip']);

      _this.mount = true;
      _this.delayShowLoop = null;
      _this.delayHideLoop = null;
      _this.delayReshow = null;
      _this.intervalUpdateContent = null;
      return _this;
    }
    /**
     * For unify the bind and unbind listener
     */


    _createClass$1(ReactTooltip, [{
      key: "bind",
      value: function bind(methodArray) {
        var _this2 = this;

        methodArray.forEach(function (method) {
          _this2[method] = _this2[method].bind(_this2);
        });
      }
    }, {
      key: "componentDidMount",
      value: function componentDidMount() {
        var _this$props = this.props,
            insecure = _this$props.insecure,
            resizeHide = _this$props.resizeHide;
        this.bindListener(); // Bind listener for tooltip

        this.bindWindowEvents(resizeHide); // Bind global event for static method

        this.injectStyles(); // Inject styles for each DOM root having tooltip.
      }
    }, {
      key: "componentWillUnmount",
      value: function componentWillUnmount() {
        this.mount = false;
        this.clearTimer();
        this.unbindListener();
        this.removeScrollListener(this.state.currentTarget);
        this.unbindWindowEvents();
      }
      /* Look for the closest DOM root having tooltip and inject styles. */

    }, {
      key: "injectStyles",
      value: function injectStyles() {
        var tooltipRef = this.tooltipRef;

        if (!tooltipRef) {
          return;
        }

        var parentNode = tooltipRef.parentNode;

        while (parentNode.parentNode) {
          parentNode = parentNode.parentNode;
        }

        var domRoot;

        switch (parentNode.constructor.name) {
          case 'Document':
          case 'HTMLDocument':
          case undefined:
            domRoot = parentNode.head;
            break;

          case 'ShadowRoot':
          default:
            domRoot = parentNode;
            break;
        } // Prevent styles duplication.


        if (!domRoot.querySelector('style[data-react-tooltip]')) {
          var style = document.createElement('style');
          style.textContent = baseCss;
          style.setAttribute('data-react-tooltip', 'true');
          domRoot.appendChild(style);
        }
      }
      /**
       * Return if the mouse is on the tooltip.
       * @returns {boolean} true - mouse is on the tooltip
       */

    }, {
      key: "mouseOnToolTip",
      value: function mouseOnToolTip() {
        var show = this.state.show;

        if (show && this.tooltipRef) {
          /* old IE or Firefox work around */
          if (!this.tooltipRef.matches) {
            /* old IE work around */
            if (this.tooltipRef.msMatchesSelector) {
              this.tooltipRef.matches = this.tooltipRef.msMatchesSelector;
            } else {
              /* old Firefox work around */
              this.tooltipRef.matches = this.tooltipRef.mozMatchesSelector;
            }
          }

          return this.tooltipRef.matches(':hover');
        }

        return false;
      }
      /**
       * Pick out corresponded target elements
       */

    }, {
      key: "getTargetArray",
      value: function getTargetArray(id) {
        var targetArray = [];
        var selector;

        if (!id) {
          selector = '[data-tip]:not([data-for])';
        } else {
          var escaped = id.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
          selector = "[data-tip][data-for=\"".concat(escaped, "\"]");
        } // Scan document for shadow DOM elements


        nodeListToArray(document.getElementsByTagName('*')).filter(function (element) {
          return element.shadowRoot;
        }).forEach(function (element) {
          targetArray = targetArray.concat(nodeListToArray(element.shadowRoot.querySelectorAll(selector)));
        });
        return targetArray.concat(nodeListToArray(document.querySelectorAll(selector)));
      }
      /**
       * Bind listener to the target elements
       * These listeners used to trigger showing or hiding the tooltip
       */

    }, {
      key: "bindListener",
      value: function bindListener() {
        var _this3 = this;

        var _this$props2 = this.props,
            id = _this$props2.id,
            globalEventOff = _this$props2.globalEventOff,
            isCapture = _this$props2.isCapture;
        var targetArray = this.getTargetArray(id);
        targetArray.forEach(function (target) {
          if (target.getAttribute('currentItem') === null) {
            target.setAttribute('currentItem', 'false');
          }

          _this3.unbindBasicListener(target);

          if (_this3.isCustomEvent(target)) {
            _this3.customUnbindListener(target);
          }
        });

        if (this.isBodyMode()) {
          this.bindBodyListener(targetArray);
        } else {
          targetArray.forEach(function (target) {
            var isCaptureMode = _this3.isCapture(target);

            var effect = _this3.getEffect(target);

            if (_this3.isCustomEvent(target)) {
              _this3.customBindListener(target);

              return;
            }

            target.addEventListener('mouseenter', _this3.showTooltip, isCaptureMode);
            target.addEventListener('focus', _this3.showTooltip, isCaptureMode);

            if (effect === 'float') {
              target.addEventListener('mousemove', _this3.updateTooltip, isCaptureMode);
            }

            target.addEventListener('mouseleave', _this3.hideTooltip, isCaptureMode);
            target.addEventListener('blur', _this3.hideTooltip, isCaptureMode);
          });
        } // Global event to hide tooltip


        if (globalEventOff) {
          window.removeEventListener(globalEventOff, this.hideTooltip);
          window.addEventListener(globalEventOff, this.hideTooltip, isCapture);
        } // Track removal of targetArray elements from DOM


        this.bindRemovalTracker();
      }
      /**
       * Unbind listeners on target elements
       */

    }, {
      key: "unbindListener",
      value: function unbindListener() {
        var _this4 = this;

        var _this$props3 = this.props,
            id = _this$props3.id,
            globalEventOff = _this$props3.globalEventOff;

        if (this.isBodyMode()) {
          this.unbindBodyListener();
        } else {
          var targetArray = this.getTargetArray(id);
          targetArray.forEach(function (target) {
            _this4.unbindBasicListener(target);

            if (_this4.isCustomEvent(target)) _this4.customUnbindListener(target);
          });
        }

        if (globalEventOff) window.removeEventListener(globalEventOff, this.hideTooltip);
        this.unbindRemovalTracker();
      }
      /**
       * Invoke this before bind listener and unmount the component
       * it is necessary to invoke this even when binding custom event
       * so that the tooltip can switch between custom and default listener
       */

    }, {
      key: "unbindBasicListener",
      value: function unbindBasicListener(target) {
        var isCaptureMode = this.isCapture(target);
        target.removeEventListener('mouseenter', this.showTooltip, isCaptureMode);
        target.removeEventListener('mousemove', this.updateTooltip, isCaptureMode);
        target.removeEventListener('mouseleave', this.hideTooltip, isCaptureMode);
      }
    }, {
      key: "getTooltipContent",
      value: function getTooltipContent() {
        var _this$props4 = this.props,
            getContent = _this$props4.getContent,
            children = _this$props4.children; // Generate tooltip content

        var content;

        if (getContent) {
          if (Array.isArray(getContent)) {
            content = getContent[0] && getContent[0](this.state.originTooltip);
          } else {
            content = getContent(this.state.originTooltip);
          }
        }

        return getTipContent(this.state.originTooltip, children, content, this.state.isMultiline);
      }
    }, {
      key: "isEmptyTip",
      value: function isEmptyTip(placeholder) {
        return typeof placeholder === 'string' && placeholder === '' || placeholder === null;
      }
      /**
       * When mouse enter, show the tooltip
       */

    }, {
      key: "showTooltip",
      value: function showTooltip(e, isGlobalCall) {
        if (!this.tooltipRef) {
          return;
        }

        if (isGlobalCall) {
          // Don't trigger other elements belongs to other ReactTooltip
          var targetArray = this.getTargetArray(this.props.id);
          var isMyElement = targetArray.some(function (ele) {
            return ele === e.currentTarget;
          });
          if (!isMyElement) return;
        } // Get the tooltip content
        // calculate in this phrase so that tip width height can be detected


        var _this$props5 = this.props,
            multiline = _this$props5.multiline,
            getContent = _this$props5.getContent;
        var originTooltip = e.currentTarget.getAttribute('data-tip');
        var isMultiline = e.currentTarget.getAttribute('data-multiline') || multiline || false; // If it is focus event or called by ReactTooltip.show, switch to `solid` effect

        var switchToSolid = e instanceof window.FocusEvent || isGlobalCall; // if it needs to skip adding hide listener to scroll

        var scrollHide = true;

        if (e.currentTarget.getAttribute('data-scroll-hide')) {
          scrollHide = e.currentTarget.getAttribute('data-scroll-hide') === 'true';
        } else if (this.props.scrollHide != null) {
          scrollHide = this.props.scrollHide;
        } // adding aria-describedby to target to make tooltips read by screen readers


        if (e && e.currentTarget && e.currentTarget.setAttribute) {
          e.currentTarget.setAttribute('aria-describedby', this.state.uuid);
        } // Make sure the correct place is set


        var desiredPlace = e.currentTarget.getAttribute('data-place') || this.props.place || 'top';
        var effect = switchToSolid && 'solid' || this.getEffect(e.currentTarget);
        var offset = e.currentTarget.getAttribute('data-offset') || this.props.offset || {};
        var result = getPosition(e, e.currentTarget, this.tooltipRef, desiredPlace, desiredPlace, effect, offset);

        if (result.position && this.props.overridePosition) {
          result.position = this.props.overridePosition(result.position, e, e.currentTarget, this.tooltipRef, desiredPlace, desiredPlace, effect, offset);
        }

        var place = result.isNewState ? result.newState.place : desiredPlace; // To prevent previously created timers from triggering

        this.clearTimer();
        var target = e.currentTarget;
        var reshowDelay = this.state.show ? target.getAttribute('data-delay-update') || this.props.delayUpdate : 0;
        var self = this;

        var updateState = function updateState() {
          self.setState({
            originTooltip: originTooltip,
            isMultiline: isMultiline,
            desiredPlace: desiredPlace,
            place: place,
            type: target.getAttribute('data-type') || self.props.type || 'dark',
            customColors: {
              text: target.getAttribute('data-text-color') || self.props.textColor || null,
              background: target.getAttribute('data-background-color') || self.props.backgroundColor || null,
              border: target.getAttribute('data-border-color') || self.props.borderColor || null,
              arrow: target.getAttribute('data-arrow-color') || self.props.arrowColor || null
            },
            effect: effect,
            offset: offset,
            html: (target.getAttribute('data-html') ? target.getAttribute('data-html') === 'true' : self.props.html) || false,
            delayShow: target.getAttribute('data-delay-show') || self.props.delayShow || 0,
            delayHide: target.getAttribute('data-delay-hide') || self.props.delayHide || 0,
            delayUpdate: target.getAttribute('data-delay-update') || self.props.delayUpdate || 0,
            border: (target.getAttribute('data-border') ? target.getAttribute('data-border') === 'true' : self.props.border) || false,
            extraClass: target.getAttribute('data-class') || self.props["class"] || self.props.className || '',
            disable: (target.getAttribute('data-tip-disable') ? target.getAttribute('data-tip-disable') === 'true' : self.props.disable) || false,
            currentTarget: target
          }, function () {
            if (scrollHide) {
              self.addScrollListener(self.state.currentTarget);
            }

            self.updateTooltip(e);

            if (getContent && Array.isArray(getContent)) {
              self.intervalUpdateContent = setInterval(function () {
                if (self.mount) {
                  var _getContent = self.props.getContent;
                  var placeholder = getTipContent(originTooltip, '', _getContent[0](), isMultiline);
                  var isEmptyTip = self.isEmptyTip(placeholder);
                  self.setState({
                    isEmptyTip: isEmptyTip
                  });
                  self.updatePosition();
                }
              }, getContent[1]);
            }
          });
        }; // If there is no delay call immediately, don't allow events to get in first.


        if (reshowDelay) {
          this.delayReshow = setTimeout(updateState, reshowDelay);
        } else {
          updateState();
        }
      }
      /**
       * When mouse hover, update tool tip
       */

    }, {
      key: "updateTooltip",
      value: function updateTooltip(e) {
        var _this5 = this;

        var _this$state = this.state,
            delayShow = _this$state.delayShow,
            disable = _this$state.disable;
        var afterShow = this.props.afterShow;
        var placeholder = this.getTooltipContent();
        var eventTarget = e.currentTarget || e.target; // Check if the mouse is actually over the tooltip, if so don't hide the tooltip

        if (this.mouseOnToolTip()) {
          return;
        } // if the tooltip is empty, disable the tooltip


        if (this.isEmptyTip(placeholder) || disable) {
          return;
        }

        var delayTime = !this.state.show ? parseInt(delayShow, 10) : 0;

        var updateState = function updateState() {
          if (Array.isArray(placeholder) && placeholder.length > 0 || placeholder) {
            var isInvisible = !_this5.state.show;

            _this5.setState({
              currentEvent: e,
              currentTarget: eventTarget,
              show: true
            }, function () {
              _this5.updatePosition();

              if (isInvisible && afterShow) {
                afterShow(e);
              }
            });
          }
        };

        clearTimeout(this.delayShowLoop);

        if (delayTime) {
          this.delayShowLoop = setTimeout(updateState, delayTime);
        } else {
          updateState();
        }
      }
      /*
       * If we're mousing over the tooltip remove it when we leave.
       */

    }, {
      key: "listenForTooltipExit",
      value: function listenForTooltipExit() {
        var show = this.state.show;

        if (show && this.tooltipRef) {
          this.tooltipRef.addEventListener('mouseleave', this.hideTooltip);
        }
      }
    }, {
      key: "removeListenerForTooltipExit",
      value: function removeListenerForTooltipExit() {
        var show = this.state.show;

        if (show && this.tooltipRef) {
          this.tooltipRef.removeEventListener('mouseleave', this.hideTooltip);
        }
      }
      /**
       * When mouse leave, hide tooltip
       */

    }, {
      key: "hideTooltip",
      value: function hideTooltip(e, hasTarget) {
        var _this6 = this;

        var options = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : {
          isScroll: false
        };
        var disable = this.state.disable;
        var isScroll = options.isScroll;
        var delayHide = isScroll ? 0 : this.state.delayHide;
        var afterHide = this.props.afterHide;
        var placeholder = this.getTooltipContent();
        if (!this.mount) return;
        if (this.isEmptyTip(placeholder) || disable) return; // if the tooltip is empty, disable the tooltip

        if (hasTarget) {
          // Don't trigger other elements belongs to other ReactTooltip
          var targetArray = this.getTargetArray(this.props.id);
          var isMyElement = targetArray.some(function (ele) {
            return ele === e.currentTarget;
          });
          if (!isMyElement || !this.state.show) return;
        } // clean up aria-describedby when hiding tooltip


        if (e && e.currentTarget && e.currentTarget.removeAttribute) {
          e.currentTarget.removeAttribute('aria-describedby');
        }

        var resetState = function resetState() {
          var isVisible = _this6.state.show; // Check if the mouse is actually over the tooltip, if so don't hide the tooltip

          if (_this6.mouseOnToolTip()) {
            _this6.listenForTooltipExit();

            return;
          }

          _this6.removeListenerForTooltipExit();

          _this6.setState({
            show: false
          }, function () {
            _this6.removeScrollListener(_this6.state.currentTarget);

            if (isVisible && afterHide) {
              afterHide(e);
            }
          });
        };

        this.clearTimer();

        if (delayHide) {
          this.delayHideLoop = setTimeout(resetState, parseInt(delayHide, 10));
        } else {
          resetState();
        }
      }
      /**
       * When scroll, hide tooltip
       */

    }, {
      key: "hideTooltipOnScroll",
      value: function hideTooltipOnScroll(event, hasTarget) {
        this.hideTooltip(event, hasTarget, {
          isScroll: true
        });
      }
      /**
       * Add scroll event listener when tooltip show
       * automatically hide the tooltip when scrolling
       */

    }, {
      key: "addScrollListener",
      value: function addScrollListener(currentTarget) {
        var isCaptureMode = this.isCapture(currentTarget);
        window.addEventListener('scroll', this.hideTooltipOnScroll, isCaptureMode);
      }
    }, {
      key: "removeScrollListener",
      value: function removeScrollListener(currentTarget) {
        var isCaptureMode = this.isCapture(currentTarget);
        window.removeEventListener('scroll', this.hideTooltipOnScroll, isCaptureMode);
      } // Calculation the position

    }, {
      key: "updatePosition",
      value: function updatePosition() {
        var _this7 = this;

        var _this$state2 = this.state,
            currentEvent = _this$state2.currentEvent,
            currentTarget = _this$state2.currentTarget,
            place = _this$state2.place,
            desiredPlace = _this$state2.desiredPlace,
            effect = _this$state2.effect,
            offset = _this$state2.offset;
        var node = this.tooltipRef;
        var result = getPosition(currentEvent, currentTarget, node, place, desiredPlace, effect, offset);

        if (result.position && this.props.overridePosition) {
          result.position = this.props.overridePosition(result.position, currentEvent, currentTarget, node, place, desiredPlace, effect, offset);
        }

        if (result.isNewState) {
          // Switch to reverse placement
          return this.setState(result.newState, function () {
            _this7.updatePosition();
          });
        } // Set tooltip position


        node.style.left = result.position.left + 'px';
        node.style.top = result.position.top + 'px';
      }
      /**
       * CLear all kinds of timeout of interval
       */

    }, {
      key: "clearTimer",
      value: function clearTimer() {
        clearTimeout(this.delayShowLoop);
        clearTimeout(this.delayHideLoop);
        clearTimeout(this.delayReshow);
        clearInterval(this.intervalUpdateContent);
      }
    }, {
      key: "hasCustomColors",
      value: function hasCustomColors() {
        var _this8 = this;

        return Boolean(Object.keys(this.state.customColors).find(function (color) {
          return color !== 'border' && _this8.state.customColors[color];
        }) || this.state.border && this.state.customColors['border']);
      }
    }, {
      key: "render",
      value: function render() {
        var _this9 = this;

        var _this$state3 = this.state,
            extraClass = _this$state3.extraClass,
            html = _this$state3.html,
            ariaProps = _this$state3.ariaProps,
            disable = _this$state3.disable,
            uuid = _this$state3.uuid;
        var content = this.getTooltipContent();
        var isEmptyTip = this.isEmptyTip(content);
        var style = generateTooltipStyle(this.state.uuid, this.state.customColors, this.state.type, this.state.border);
        var tooltipClass = '__react_component_tooltip' + " ".concat(this.state.uuid) + (this.state.show && !disable && !isEmptyTip ? ' show' : '') + (this.state.border ? ' border' : '') + " place-".concat(this.state.place) + // top, bottom, left, right
        " type-".concat(this.hasCustomColors() ? 'custom' : this.state.type) + ( // dark, success, warning, error, info, light, custom
        this.props.delayUpdate ? ' allow_hover' : '') + (this.props.clickable ? ' allow_click' : '');
        var Wrapper = this.props.wrapper;

        if (ReactTooltip.supportedWrappers.indexOf(Wrapper) < 0) {
          Wrapper = ReactTooltip.defaultProps.wrapper;
        }

        var wrapperClassName = [tooltipClass, extraClass].filter(Boolean).join(' ');

        if (html) {
          var htmlContent = "".concat(content, "\n<style aria-hidden=\"true\">").concat(style, "</style>");
          return React.createElement(Wrapper, _extends$1({
            className: "".concat(wrapperClassName),
            id: this.props.id || uuid,
            ref: function ref(_ref) {
              return _this9.tooltipRef = _ref;
            }
          }, ariaProps, {
            "data-id": "tooltip",
            dangerouslySetInnerHTML: {
              __html: htmlContent
            }
          }));
        } else {
          return React.createElement(Wrapper, _extends$1({
            className: "".concat(wrapperClassName),
            id: this.props.id || uuid
          }, ariaProps, {
            ref: function ref(_ref2) {
              return _this9.tooltipRef = _ref2;
            },
            "data-id": "tooltip"
          }), React.createElement("style", {
            dangerouslySetInnerHTML: {
              __html: style
            },
            "aria-hidden": "true"
          }), content);
        }
      }
    }], [{
      key: "getDerivedStateFromProps",
      value: function getDerivedStateFromProps(nextProps, prevState) {
        var ariaProps = prevState.ariaProps;
        var newAriaProps = parseAria(nextProps);
        var isChanged = Object.keys(newAriaProps).some(function (props) {
          return newAriaProps[props] !== ariaProps[props];
        });

        if (!isChanged) {
          return null;
        }

        return _objectSpread2({}, prevState, {
          ariaProps: newAriaProps
        });
      }
    }]);

    return ReactTooltip;
  }(React.Component), _defineProperty$1(_class2, "defaultProps", {
    insecure: true,
    resizeHide: true,
    wrapper: 'div',
    clickable: false
  }), _defineProperty$1(_class2, "supportedWrappers", ['div', 'span']), _defineProperty$1(_class2, "displayName", 'ReactTooltip'), _temp)) || _class) || _class) || _class) || _class) || _class) || _class) || _class;

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
    return _objectSpread({
      width: "100%",
      padding: 0,
      margin: 0
    }, custom);
  };
  var table = function table() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
      display: 'table',
      width: "100%",
      borderCollapse: 'collapse',
      textAlign: 'center',
      borderLeft: DEFAULT_BORDER
    }, custom);
  };
  var tableRow = function tableRow() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
      display: 'table-row'
    }, custom);
  };
  var tableHeading = function tableHeading() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
      display: 'table-header-group',
      fontWeight: 'bold',
      padding: '15px 30px',
      borderBottom: DEFAULT_BORDER,
      borderTop: DEFAULT_BORDER
    }, custom);
  };
  var tableBody = function tableBody() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
      display: 'table-row-group'
    }, custom);
  };
  var tableCell = function tableCell() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
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
    return _objectSpread({
      fontSize: '12px'
    }, custom);
  };
  var headerLabel = function headerLabel() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
      fontSize: '16px',
      padding: '0',
      margin: '0'
    }, custom);
  };
  var fixedTablePart = function fixedTablePart() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
      display: 'table-cell',
      minWidth: '200px'
    }, custom);
  };
  var scrollableTableContent = function scrollableTableContent() {
    var custom = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    return _objectSpread({
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
    IS_NORMALIZED_SHADE_COLOR: false,
    IS_DARK_MODE: false,
    LAST_CELL_SHADED: false,
    HEADER_RANGE: 'default'
  };

  var VALUE = VALUE_KEYS.VALUE,
      PERCENT = VALUE_KEYS.PERCENT;

  var DataStore =
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
              var nextKeyIndex = Object.keys(data[key]).indexOf(anotherKey);

              _this.store[key].push([cellData].concat(_toConsumableArray(data[key][anotherKey].map(function (value, index) {
                var _ref;

                var nextKey = Object.keys(data[key])[nextKeyIndex++];
                var nextValueFor = nextKey;

                var percent = _this._getPercentage(cellData.total, value);

                return _ref = {
                  isHeader: false,
                  index: index,
                  type: key
                }, _defineProperty(_ref, VALUE, value), _defineProperty(_ref, "valueFor", anotherKey), _defineProperty(_ref, "nextValueFor", nextValueFor || 'Upcoming Period'), _defineProperty(_ref, "total", cellData.total), _defineProperty(_ref, "isTotal", index === 0), _defineProperty(_ref, "isCell", index > 0), _defineProperty(_ref, PERCENT, percent), _defineProperty(_ref, "color", index === 0 ? _this.options.bodyCellColor : _this.options.isNormalizedShadeColor ? _this._shadeCellWithColor(_this._normalizedValue(data[key], value), _this.options.shadeColor, _this.options.isDarkMode) : _this._shadeCellWithColor(percent, _this.options.shadeColor, _this.options.isDarkMode)), _ref;
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
            }, _defineProperty(_this$headers$key$pus2, VALUE, value), _defineProperty(_this$headers$key$pus2, "valueFor", largeRow[0]), _defineProperty(_this$headers$key$pus2, "total", cellData.total), _defineProperty(_this$headers$key$pus2, PERCENT, percent), _defineProperty(_this$headers$key$pus2, "color", _this._shadeCellWithColor(percent, _this.options.shadeColor, _this.options.isDarkMode)), _defineProperty(_this$headers$key$pus2, "label", _this._postfixHeaderLabel(labelPrefix, index - 1, _this.options.headerRange)), _this$headers$key$pus2));
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
      var darkMode = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : false;
      var rate = 1.0 - Math.ceil(percent / 10) / 10;
      var f = parseInt(color.slice(1), 16),
          p = rate < 0 ? rate * -1 : rate,
          R = f >> 16,
          G = f >> 8 & 0x00FF,
          B = f & 0x0000FF;
      var t = darkMode ? rate < 0 ? 255 : 0 : rate < 0 ? 0 : 255;
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

    _defineProperty(this, "_postfixHeaderLabel", function (labelPrefix, index, headerRange) {
      if (headerRange === 'default') {
        return labelPrefix + ' ' + index;
      } else if (headerRange === 'double') {
        return labelPrefix + ' ' + (index * 2 - 1) + '-' + index * 2;
      } else if (headerRange === 'quarter') {
        return '  Q' + index;
      }
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
  ;

  /**
   * Created by jyothi on 30/5/17.
   */
  var nFormatter = function nFormatter(number) {
    var digits = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 2;
    var abbrev = ['', 'K', 'M', 'B', 'T'];
    var unrangifiedOrder = Math.floor(Math.log10(Math.abs(number)) / 3);
    var order = Math.max(0, Math.min(unrangifiedOrder, abbrev.length - 1));
    var suffix = abbrev[order];
    return (number / Math.pow(10, order * 3)).toFixed(digits) + suffix;
  };

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
          rest = _objectWithoutProperties(props, ["formatter"]);

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
          rest = _objectWithoutProperties(props, ["formatter"]);

      return _formatter2(rest);
    }

    return label;
  };

  var HeaderCell = function HeaderCell(props) {
    return React.createElement("div", {
      style: _objectSpread({}, tableCell(props.tableCellStyles), {
        backgroundColor: props.color
      }, props.style)
    }, React.createElement("p", {
      style: headerLabel(props.headerLabelStyles)
    }, renderHeader(props)), props.showHeaderValues ? React.createElement("span", {
      style: headerValue({})
    }, renderValue(_objectSpread({}, props, {
      isHeaderValue: true
    }))) : null);
  };
  var BodyCell = function BodyCell(props) {
    return React.createElement("div", {
      className: props.lastCellShaded && props.isLastItem && 'last-item-forcasted',
      style: _objectSpread({}, tableCell(props.tableCellStyles), {
        backgroundColor: props.color
      }, props.style),
      "data-tip": "".concat(nFormatter(props[VALUE$1]), " on ").concat(props.nextValueFor)
    }, renderValue(props));
  };
  var FixedBodyCell = function FixedBodyCell(props) {
    return React.createElement("div", {
      style: _objectSpread({}, tableCell(props.tableCellStyles), {
        backgroundColor: props.color
      }, props.style)
    }, renderValue(props), React.createElement("br", null), React.createElement("b", null, nFormatter(props.totalCount)));
  };
  var ScrollableContent =
  /*#__PURE__*/
  function (_React$Component) {
    _inherits(ScrollableContent, _React$Component);

    function ScrollableContent(props) {
      var _this;

      _classCallCheck(this, ScrollableContent);

      _this = _possibleConstructorReturn(this, _getPrototypeOf(ScrollableContent).call(this, props));

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
        return React.createElement("div", {
          ref: function ref(x) {
            return _this3.ref = x;
          },
          style: _objectSpread({}, scrollableTableContent(scrollableTableContentStyles), {
            width: this.state.width
          })
        }, this.props.children);
      }
    }]);

    return ScrollableContent;
  }(React.Component);

  var ReactCohortGraph =
  /*#__PURE__*/
  function (_React$Component) {
    _inherits(ReactCohortGraph, _React$Component);

    function ReactCohortGraph(_props) {
      var _this;

      _classCallCheck(this, ReactCohortGraph);

      _this = _possibleConstructorReturn(this, _getPrototypeOf(ReactCohortGraph).call(this, _props));

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
            isNormalizedShadeColor = _props$isNormalizedSh === void 0 ? DEFAULT_VALUES.IS_NORMALIZED_SHADE_COLOR : _props$isNormalizedSh,
            _props$isDarkMode = props.isDarkMode,
            isDarkMode = _props$isDarkMode === void 0 ? DEFAULT_VALUES.IS_DARK_MODE : _props$isDarkMode,
            _props$lastCellShaded = props.lastCellShaded,
            lastCellShaded = _props$lastCellShaded === void 0 ? DEFAULT_VALUES.LAST_CELL_SHADED : _props$lastCellShaded,
            _props$headerRange = props.headerRange,
            headerRange = _props$headerRange === void 0 ? DEFAULT_VALUES.HEADER_RANGE : _props$headerRange;
        return new DataStore(data, {
          shadeColor: shadeColor,
          headerCellColor: headerCellColor,
          bodyCellColor: bodyCellColor,
          keyCellColor: keyCellColor,
          isNormalizedShadeColor: isNormalizedShadeColor,
          isDarkMode: isDarkMode,
          lastCellShaded: lastCellShaded,
          headerRange: headerRange
        });
      });

      _defineProperty(_assertThisInitialized(_this), "isFixed", function (index) {
        return index < 2;
      });

      _defineProperty(_assertThisInitialized(_this), "renderChildren", function (props) {
        return React.Children.map(props.children, function (child) {
          return React.cloneElement(child, props);
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
            tableCellStyles = _this$props2.tableCellStyles,
            lastCellShaded = _this$props2.lastCellShaded;
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
          return React.createElement("div", {
            style: WrapperStyles
          }, this.renderChildren(_objectSpread({}, this.props, this.state)), React.createElement("div", {
            style: TableStyles
          }, React.createElement("div", {
            style: TableBodyStyles
          }, React.createElement("div", {
            style: TableRowStyles
          }, React.createElement("div", {
            style: FixedTablePartStyles
          }, React.createElement("div", {
            style: TableStyles
          }, React.createElement("div", {
            style: TableHeadingStyles
          }, React.createElement(HeaderCell, _extends({
            tableCellStyles: tableCellStyles,
            headerLabelStyles: _objectSpread({}, headerLabelStyles, {
              visibility: 'hidden'
            }),
            style: headerCellStyles,
            key: "header" + 0
          }, header[0], {
            formatter: typeof headerFormatter === "function" ? headerFormatter : cellFormatter,
            showHeaderValues: showHeaderValues,
            valueType: valueType,
            isFixed: true
          }))), React.createElement("div", {
            style: TableBodyStyles
          }, rows.map(function (row, j) {
            return React.createElement("div", {
              style: TableRowStyles,
              key: "row" + j
            }, React.createElement(FixedBodyCell, _extends({
              tableCellStyles: tableCellStyles,
              style: bodyCellStyles,
              key: "cell" + 0,
              totalCount: row[1][VALUE_KEYS.VALUE]
            }, row[0], {
              valueType: valueType,
              formatter: cellFormatter,
              isFixed: true
            })));
          })))), React.createElement("div", {
            style: ScrollableTablePartStyles
          }, React.createElement(ScrollableContent, {
            scrollableTableContentStyles: scrollableTableContentStyles
          }, React.createElement("div", {
            style: TableStyles
          }, React.createElement("div", {
            style: TableHeadingStyles
          }, header.map(function (headerCell, i) {
            return !_this2.isFixed(i) && React.createElement(HeaderCell, _extends({
              tableCellStyles: tableCellStyles,
              style: headerCellStyles,
              key: "header" + i
            }, headerCell, {
              formatter: typeof headerFormatter === "function" ? headerFormatter : cellFormatter,
              showHeaderValues: showHeaderValues,
              valueType: valueType,
              isFixed: false
            }));
          })), React.createElement("div", {
            style: TableBodyStyles
          }, rows.map(function (row, j) {
            return React.createElement("div", {
              style: TableRowStyles,
              key: "row" + j
            }, row.map(function (cell, k, _ref) {
              var length = _ref.length;
              return !_this2.isFixed(k) && React.createElement(BodyCell, _extends({
                tableCellStyles: tableCellStyles,
                style: bodyCellStyles,
                key: "cell" + k
              }, cell, {
                nextCell: row[k + 1],
                valueType: valueType,
                formatter: cellFormatter,
                isFixed: false,
                lastCellShaded: lastCellShaded,
                isLastItem: k + 1 === length
              }));
            }));
          })), React.createElement(ReactTooltip, {
            delayShow: 500
          }))))))));
        }

        if (showEmptyDataMessage) {
          return customEmptyDataMessage || React.createElement("h3", null, "No Data..!");
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
    isNormalizedShadeColor: propTypes.bool,
    isDarkMode: propTypes.bool,
    lastCellShaded: propTypes.bool,
    headerRange: propTypes.string
  };

  return ReactCohortGraph;

}));
