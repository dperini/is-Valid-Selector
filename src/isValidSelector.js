/*
 * Copyright (C) 2018 Diego Perini
 * All rights reserved.
 *
 * isValidSelector.js - Selector syntax checker
 *
 * Author: Diego Perini <diego.perini at gmail com>
 * Version: 0.92
 * Created: 20180815
 * Release: 20180815
 *
 * License:
 *  https://raw.githubusercontent.com/dperini/is-Valid-Selector/master/LICENSE
 * Download:
 *  https://github.com/dperini/is-Valid-Selector/archive/master.zip
 */

(function Export(global, factory) {

  'use strict';

  if (typeof module == 'object' && typeof exports == 'object') {
    module.exports = factory;
  } else if (typeof define == 'function' && define['amd']) {
    define(factory);
  } else {
    global.isValidSelector = factory(global, Export);
  }

})(this, function Factory(global, Export) {

  var version = '0.92',

  WSP = '[\\x20\\t\\r\\n\\f]',

  CFG = {
    operators: '[~*^$|]=|=',
    combinators: '[\\x20\\t\\r\\n\\f>+~](?=[^>+~])'
  },

  STD = {
    whitespace: RegExp('\\s+'),
    pseudoname: RegExp('^[-a-zA-Z]+'),
    combinator: RegExp('\\s?([>+~])\\s?', 'g'),
    apimethods: RegExp('^(?:[a-z]+|\\*)\\|', 'i'),
    namespaces: RegExp('(\\*|[a-z]+)\\|[-a-z]+', 'i'),
    commagroup: RegExp('(\\s*,\\s*)(?![^\\[\\]]*\\])(?![^\\(\\)]*\\))', 'g')
  },

  REX = {
    HasEscapes: RegExp('\\\\'),
    HexNumbers: RegExp('^[0-9a-fA-F]'),
    EscOrQuote: RegExp('^\\\\|[\\x22\\x27]'),
    RegExpChar: RegExp('(?:(?!\\\\)[\\\\^$.*+?()[\\]{}|\\/])' ,'g'),
    TrimSpaces: RegExp('[\\r\\n\\f]|^' + WSP + '+|' + WSP + '+$', 'g'),
    SplitGroup: RegExp('((?:\\([^\\x29]*\\)|\\[[^\\]]*\\]|\\\\.|[^,])+)', 'g'),
    FixEscapes: RegExp('\\\\([0-9a-fA-F]{1,6}' + WSP + '?|.)|([\\x22\\x27])', 'g')
  },

  struct_1 = '(root|empty|(?:(?:first|last|only)(?:-child|-of-type)))\\b',
  struct_2 = '(nth(?:-last)?(?:-child|-of-type))(?:\\(\\s?(even|odd|(?:[-+]?\\d*)(?:n[-+]?\\d*)?)\\s?(?:\\)|$))',

  pseudo_1 = '(dir|lang)\\x28\\s?([-\\w]{2,})\\s?(?:\\x29|$)|(local-link)\\x28\\s?(\\d*)\\s?(?:\\x29|$)\\b',
  pseudo_2 = ':?(after|before|first-letter|first-line|selection|backdrop|placeholder)\\b',

  noparm_1 = '(link|visited|target|scope|hover|active|focus|enabled|disabled|read-only|read-write|placeholder-shown)\\b',
  noparm_2 = '(default|checked|indeterminate|required|optional|valid|invalid|in-range|out-of-range)\\b',

  logicals = '(matches|not)\\x28\\s?([^()]*|[^\\x28]*\\x28[^\\x29]*\\x29)\\s?(?:\\x29|$)',

  Patterns = {
    // pseudo-classes
    struct_n: RegExp('^:(?:' + struct_1 + ')(.*)', 'i'),
    struct_p: RegExp('^:(?:' + struct_2 + ')(.*)', 'i'),
    hpseudos: RegExp('^:(?:' + pseudo_1 + ')(.*)', 'i'),
    epseudos: RegExp('^:(?:' + pseudo_2 + ')(.*)', 'i'),
    lpseudos: RegExp('^:(?:' + logicals + ')(.*)', 'i'),
    fpseudos: RegExp('^:(?:' + noparm_1 + ')(.*)', 'i'),
    ipseudos: RegExp('^:(?:' + noparm_2 + ')(.*)', 'i'),
    // combinators symbols
    children: RegExp('^' + WSP + '?\\>' + WSP + '?(.*)'),
    adjacent: RegExp('^' + WSP + '?\\+' + WSP + '?(.*)'),
    relative: RegExp('^' + WSP + '?\\~' + WSP + '?(.*)'),
    ancestor: RegExp('^' + WSP + '+(.*)'),
   // universal & namespace
   universal: RegExp('^\\*(.*)'),
   namespace: RegExp('^(\\w+|\\*)?\\|(.*)')
  },

  // global regexp placeholder
  reSimpleNot, reValidator,

  // emulate firefox error strings
  qsNotArgs = 'Not enough arguments',
  qsInvalid = ' is not a valid selector',

  // special handling configuration flags
  Config = {

    SIMPLENOT: true,

    LOGERRORS: true,
    VERBOSITY: true

  },

  // configure the engine to use special handling
  configure =
    function(option) {
      if (typeof option == 'string') { return !!Config[option]; }
      if (typeof option != 'object') { return Config; }
      for (var i in option) {
        Config[i] = !!option[i];
        if (i == 'SIMPLENOT') {
          matchResolvers = { };
          selectResolvers = { };
        }
      }
      setIdentifierSyntax();
      return true;
    },

  // centralized error and exceptions handling
  emit =
    function(message, proto) {
      var err;
      if (Config.VERBOSITY) {
        if (proto) {
          err = new proto(message);
        } else {
          err = new global.DOMException(message, 'SyntaxError');
        }
        throw err;
      }
      if (Config.LOGERRORS && console && console.log) {
        console.log(message);
      }
    },

  // build validation regexps used by the engine
  setupSyntaxValidator =
    function() {

      // NOTE: SPECIAL CASES IN CSS SYNTAX PARSING RULES
      //
      // The <EOF-token> https://drafts.csswg.org/css-syntax/#typedef-eof-token
      // allow mangled|unclosed selector syntax at the end of selectors strings
      //
      // These are the non capturing representations of each character: ' " ] )
      //
      // (?:\\"|$) - missing close double quotes
      // (?:\\'|$) - missing close single quote
      // (?:\\]|$) - missing close square bracket
      // (?:\\)|$) - missing close round parens
      //
      // use the above four patterns to find instances throughout the code

      var identifier =
        // doesn't start with a digit
        '(?=[^0-9])' +
        // can start with double dash
        '(?:-{2}' +
          // validate any ascii chars
          '|[a-zA-Z0-9-_]' +
          // validate non-ascii chars
          '|[^\\x00-\\x9f]' +
          // validate escaped chars
          '|\\\\[^\\r\\n\\f0-9a-fA-F]' +
          // validate unicode chars
          '|\\\\[0-9a-fA-F]{1,6}(?:\\r\\n|\\s)?' +
          // accept any escaped chars
          '|\\\\.' +
        ')+',

      pseudoparms = '(?:[-+]?\\d*)(?:n[-+]?\\d*)',
      doublequote = '"[^"\\\\]*(?:\\\\.[^"\\\\]*)*(?:"|$)',
      singlequote = "'[^'\\\\]*(?:\\\\.[^'\\\\]*)*(?:'|$)",

      attrparser = identifier + '|' + doublequote + '|' + singlequote,

      attrvalues = '([\\x22\\x27]?)((?!\\3)*|(?:\\\\?.)*?)(?:\\3|$)',

      attributes =
        '\\[' +
          // attribute presence
          '(?:\\*\\|)?' +
          WSP + '?' +
          '(' + identifier + '(?::' + identifier + ')?)' +
          WSP + '?' +
          '(?:' +
            '(' + CFG.operators + ')' + WSP + '?' +
            '(?:' + attrparser + ')' +
          ')?' +
          // attribute case sensitivity
          WSP + '?' + '(i)?' + WSP + '?' +
        '(?:\\]|$)',

      attrmatcher = attributes.replace(attrparser, attrvalues),

      pseudoclass =
        '(?:\\(' + WSP + '*' +
          '(?:' + pseudoparms + '?)?|' +
          // universal * &
          // namespace *|*
          '(?:\\*|\\|)|' +
          '(?:' +
            '(?::' + identifier +
            '(?:\\(' + pseudoparms + '?(?:\\)|$))?|' +
          ')|' +
          '(?:[.#]?' + identifier + ')|' +
          '(?:' + attributes + ')' +
        ')+' + '(?:' + WSP + '*)(?:\\)|$))*',

      standardValidator =
        '(?=' + WSP + '?[^>+~(){}<>])' +
        '(?:' +
          // universal * &
          // namespace *|*
          '(?:\\*|\\|)|' +
          '(?:[.#]?' + identifier + ')+|' +
          '(?:' + attributes + ')+|' +
          '(?:::?' + identifier + pseudoclass + ')|' +
          '(?:' + WSP + '?' + CFG.combinators + WSP + '?)|' +
          '(?:' + WSP + '?,' + WSP + '?)|' +
          '(?:' + WSP + '*)' +
        ')+',

      extendedValidator = standardValidator.replace(pseudoclass, '.*');

      reSimpleNot = RegExp(
        '^(' +
          // universal negation :not(*) &
          // namespace negation :not(*|*)
          '(?:\\*|\\*\\|\\*)|' +
          '(?!:not)' +
          '(?:' + WSP + '*[.:#]?' +
          '(?:' + identifier + WSP + '*)+|' +
          '(?:\\([^()]*(?:\\)|$))' + ')+|' +
          '(?:' + WSP + '*' + attributes + WSP + '*)+|' +
        ')$');

      reOptimizer = RegExp('(?:([.:#*]?)(' + identifier + ')(?::[-\\w]+|\\[[^\\]]+(?:\\]|$)|\\([^\\)]+(?:\\)|$))*)$');

      Patterns.id = RegExp('^#(' + identifier + ')(.*)');
      Patterns.tagName = RegExp('^(' + identifier + ')(.*)');
      Patterns.className = RegExp('^\\.(' + identifier + ')(.*)');
      Patterns.attribute = RegExp('^(?:' + attrmatcher + ')(.*)');

      reValidator = RegExp(Config.SIMPLENOT ?
        standardValidator : extendedValidator, 'g');
    },

  scanSelectors =
    function(expression, not) {

      // N is the negation pseudo-class flag
      // D is the default inverted negation flag
      var expr, match, nested, result, type, symbol, selector = expression;

      // isolate selector combinators/components and normalize whitespace
      selector = selector.replace(STD.combinator, '$1').replace(STD.whitespace, ' ');

      while (selector) {

        // get namespace prefix if present or get first char of selector
        symbol = STD.apimethods.test(selector) ? '|' : selector[0];

        switch (symbol) {

          // universal resolver
          case '*':
            match = selector.match(Patterns.universal);
            break;

          // id resolver
          case '#':
            match = selector.match(Patterns.id);
            break;
          // class name resolver
          case '.':
            match = selector.match(Patterns.className);
            break;
          // tag name resolver
          case (/[a-z]/i.test(symbol) ? symbol : undefined):
            match = selector.match(Patterns.tagName);
            break;

          // namespace resolver
          case '|':
            match = selector.match(Patterns.namespace);
            break;

          // attributes resolver
          case '[':
            match = selector.match(Patterns.attribute);
            if (match[2] && !(test = Operators[match[2]])) {
              emit('\'' + selector_string + '\'' + qsInvalid);
              return false;
            }
            break;

          // *** General sibling combinator
          // E ~ F (F relative sibling of E)
          case '~':
            match = selector.match(Patterns.relative);
            break;
          // *** Adjacent sibling combinator
          // E + F (F adiacent sibling of E)
          case '+':
            match = selector.match(Patterns.adjacent);
            break;
          // *** Descendant combinator
          // E F (E ancestor of F)
          case ' ':
            match = selector.match(Patterns.ancestor);
            break;
          // *** Child combinator
          // E > F (F children of E)
          case '>':
            match = selector.match(Patterns.children);
            break;

          // *** tree-structural pseudo-classes
          // :root, :empty, :blank
          // :first-child, :last-child, :only-child,
          // :first-of-type, :last-of-type, :only-of-type,
          case ':':
            if ((match = selector.match(Patterns.struct_n))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                case 'root':
                case 'empty':

                // *** child-indexed pseudo-classes
                // :first-child, :last-child, :only-child
                case 'only-child':
                case 'last-child':
                case 'first-child':

                // *** typed child-indexed pseudo-classes
                // :only-of-type, :last-of-type, :first-of-type
                case 'only-of-type':
                case 'last-of-type':
                case 'first-of-type':
                  break;
                default:
                  emit('\'' + selector_string + '\'' + qsInvalid);
                  break;
              }
            }

            // *** child-indexed & typed child-indexed pseudo-classes
            // :nth-child, :nth-of-type, :nth-last-child, :nth-last-of-type
            // 4 cases: 1 (nth) x 4 (child, of-type, last-child, last-of-type)
            else if ((match = selector.match(Patterns.struct_p))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                case 'nth-child':
                case 'nth-of-type':
                case 'nth-last-child':
                case 'nth-last-of-type':
                  if (match[1] && match[2]) {
                    if (match[2] == 'n') {
                      break;
                    } else if (match[2] == '1') {
                      break;
                    }
                  } else {
                    emit('\'' + selector_string + '\'' + qsInvalid);
                  }
                  break;
                default:
                  emit('\'' + selector_string + '\'' + qsInvalid);
                  break;
              }
            }

            // *** logical combination pseudo-classes
            // :matches( s1, [ s2, ... ]), :not( s1, [ s2, ... ])
            else if ((match = selector.match(Patterns.lpseudos))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                case 'matches':
                  if (not === true || nested === true) {
                    emit(':matches() pseudo-class cannot be nested');
                  }
                  nested = true;
                  break;
                case 'not':
                  if (not === true || nested === true) {
                    emit(':not() pseudo-class cannot be nested');
                  }
                  if (Config.SIMPLENOT && !reSimpleNot.test(match[2])) {
                    emit('\'' + selector_string + '\'' + qsInvalid);
                    return false;
                  }
                  expr = match[2].replace(STD.commagroup, ',').replace(REX.TrimSpaces, '');
                  // check nested compound selectors s1, s2
                  expr = match[2].match(REX.SplitGroup);
                  for (var i = 0, l = expr.length; l > i; ++i) {
                    expr[i] = expr[i].replace(REX.TrimSpaces, '');
                    scanSelectors(expr[i], true);
                  }
                  break;
                default:
                  emit('\'' + selector_string + '\'' + qsInvalid);
                  break;
              }
            }

            // *** linguistic pseudo-classes
            // :dir( ltr / rtl ), :lang( en )
            else if ((match = selector.match(Patterns.hpseudos))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                case 'dir':
                case 'lang':
                  break;
                default:
                  emit('\'' + selector_string + '\'' + qsInvalid);
                  break;
              }
            }

            // *** location, user actiond and input pseudo-classes
            else if ((match = selector.match(Patterns.fpseudos))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                // *** location pseudo-classes
                // :link, :visited, :target, :scope
                case 'link':
                case 'visited':
                case 'target':
                case 'scope':

                // *** user actions pseudo-classes
                // :hover, :active, :focus
                case 'hover':
                case 'active':
                case 'focus':

                // *** user interface and form pseudo-classes
                // :enabled, :disabled, :read-only, :read-write, :placeholder-shown
                case 'enabled':
                case 'disabled':
                case 'read-only':
                case 'read-write':
                case 'placeholder-shown':
                  break;
                default:
                  emit('\'' + selector_string + '\'' + qsInvalid);
                  break;
              }
            }

            // *** input pseudo-classes for form validation (was web-forms)
            // :default, :checked, :indeterminate, :valid, :invalid
            // :in-range, :out-of-range, :required, :optional
            else if ((match = selector.match(Patterns.ipseudos))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                case 'default':
                case 'checked':
                case 'indeterminate':
                case 'required':
                case 'optional':
                case 'invalid':
                case 'valid':
                case 'in-range':
                case 'out-of-range':
                  break;
                default:
                  emit('\'' + selector_string + '\'' + qsInvalid);
                  break;
              }
            }

            // allow pseudo-elements as :after/:before (single or double colon)
            else if ((match = selector.match(Patterns.epseudos))) {
              match[1] = match[1].toLowerCase();
              switch (match[1]) {
                case 'after':
                case 'before':
                default:
                  break;
              }
            }

            break;

        default:
          emit('\'' + selector + '\'' + qsInvalid);
          break;

        }
        // end of switch symbol

        if (!match) {
          emit('\'' + selector + '\'' + qsInvalid);
          return false;
        }

        // pop last component
        selector = match.pop();
      }
      // end of while selector

      return true;
    },

  // selector syntax checking helper
  isValidSelector =
    function _validSelector(selectors) {

      var i, l, expressions, result = true;

      // arguments validation
      if (arguments.length === 0) {
        emit('not enough arguments', TypeError);
        return Config.VERBOSITY ? undefined : none;
      } else if (arguments[0] === '') {
        emit('\'\' is not a valid selector');
        return Config.VERBOSITY ? undefined : none;
      }

      // selector NULL or UNDEFINED
      if (typeof selectors != 'string') {
        selectors = '' + selectors;
      }

      // normalize selector
      selectors = selectors.
        replace(/\x00|\\$/g, '\ufffd').
        replace(STD.commagroup, ',').
        replace(REX.TrimSpaces, '');

      expressions = selectors.match(reValidator);

      // parse, validate and split compound selectors
      if (expressions.join('') == selectors) {
        expressions = selectors.match(REX.SplitGroup);
        if (selectors[selectors.length - 1] == ',') {
          emit('invalid or illegal string specified');
          return Config.VERBOSITY ? undefined : false;
        }
      } else {
        emit('\'' + selector + '\' is not a valid selector');
        return Config.VERBOSITY ? undefined : false;
      }

      for (i = 0, l = expressions.length; l > i; ++i) {
        result = result && scanSelectors(expressions[i], false);
      }

      return result;
    };

  setupSyntaxValidator();

  return isValidSelector;

});
