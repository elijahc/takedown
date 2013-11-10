
/** vim: et:ts=4:sw=4:sts=4
 * @license RequireJS 2.1.4 Copyright (c) 2010-2012, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/jrburke/requirejs for details
 */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */

var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.4',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        apsp = ap.splice,
        isBrowser = !!(typeof window !== 'undefined' && navigator && document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value !== 'string') {
                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    //Allow getting a global that expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite and existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                pkgs: {},
                shim: {},
                map: {},
                config: {}
            },
            registry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part;
            for (i = 0; ary[i]; i += 1) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    if (i === 1 && (ary[2] === '..' || ary[0] === '..')) {
                        //End of the line. Keep at least one non-dot
                        //path segment at the front so it can be mapped
                        //correctly to disk. Otherwise, there is likely
                        //no path mapping for a path starting with '..'.
                        //This can still fail, but catches the most reasonable
                        //uses of ..
                        break;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgName, pkgConfig, mapValue, nameParts, i, j, nameSegment,
                foundMap, foundI, foundStarMap, starI,
                baseParts = baseName && baseName.split('/'),
                normalizedBaseParts = baseParts,
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name && name.charAt(0) === '.') {
                //If have a base name, try to normalize against it,
                //otherwise, assume it is a top-level require that will
                //be relative to baseUrl in the end.
                if (baseName) {
                    if (getOwn(config.pkgs, baseName)) {
                        //If the baseName is a package name, then just treat it as one
                        //name to concat the name with.
                        normalizedBaseParts = baseParts = [baseName];
                    } else {
                        //Convert baseName to array, and lop off the last part,
                        //so that . matches that 'directory' and not name of the baseName's
                        //module. For instance, baseName of 'one/two/three', maps to
                        //'one/two/three.js', but we want the directory, 'one/two' for
                        //this normalization.
                        normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    }

                    name = normalizedBaseParts.concat(name.split('/'));
                    trimDots(name);

                    //Some use of packages may use a . path to reference the
                    //'main' module name, so normalize for that.
                    pkgConfig = getOwn(config.pkgs, (pkgName = name[0]));
                    name = name.join('/');
                    if (pkgConfig && name === pkgName + '/' + pkgConfig.main) {
                        name = pkgName;
                    }
                } else if (name.indexOf('./') === 0) {
                    // No baseName, so this is ID is resolved relative
                    // to baseUrl, pull off the leading dot.
                    name = name.substring(2);
                }
            }

            //Apply map config if available.
            if (applyMap && (baseParts || starMap) && map) {
                nameParts = name.split('/');

                for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break;
                                }
                            }
                        }
                    }

                    if (foundMap) {
                        break;
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            return name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                removeScript(id);
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);
                context.require([id]);
                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        normalizedName = normalize(name, parentName, applyMap);
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                getModule(depMap).on(name, fn);
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                //Array splice in the values since the context code has a
                //local var ref to defQueue, so cannot just reassign the one
                //on context.
                apsp.apply(defQueue,
                           [defQueue.length - 1, 0].concat(globalDefQueue));
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return mod.exports;
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            return (config.config && getOwn(config.config, mod.map.id)) || {};
                        },
                        exports: defined[mod.map.id]
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var map, modId, err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(registry, function (mod) {
                map = mod.map;
                modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks is the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    this.fetch();
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            //If there is an error listener, favor passing
                            //to that instead of throwing an error.
                            if (this.events.error) {
                                try {
                                    exports = context.execCb(id, factory, depExports, exports);
                                } catch (e) {
                                    err = e;
                                }
                            } else {
                                exports = context.execCb(id, factory, depExports, exports);
                            }

                            if (this.map.isDefine) {
                                //If setting exports via 'module' is in play,
                                //favor that over return value and exports. After that,
                                //favor a non-undefined return value over exports use.
                                cjsModule = this.module;
                                if (cjsModule &&
                                        cjsModule.exports !== undefined &&
                                        //Make sure it is not already the exports value
                                        cjsModule.exports !== this.exports) {
                                    exports = cjsModule.exports;
                                } else if (exports === undefined && this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                err.requireMap = this.map;
                                err.requireModules = [this.map.id];
                                err.requireType = 'define';
                                return onError((this.error = err));
                            }

                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                req.onResourceLoad(context, this.map, this.depMaps);
                            }
                        }

                        //Clean up
                        delete registry[id];

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', this.errback);
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' + args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths and packages since they require special processing,
                //they are additive.
                var pkgs = config.pkgs,
                    shim = config.shim,
                    objs = {
                        paths: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (prop === 'map') {
                            mixin(config[prop], value, true, true);
                        } else {
                            mixin(config[prop], value, true);
                        }
                    } else {
                        config[prop] = value;
                    }
                });

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location;

                        pkgObj = typeof pkgObj === 'string' ? { name: pkgObj } : pkgObj;
                        location = pkgObj.location;

                        //Create a brand new object on pkgs, since currentPackages can
                        //be passed in again, and config.pkgs is the internal transformed
                        //state for all package configs.
                        pkgs[pkgObj.name] = {
                            name: pkgObj.name,
                            location: location || pkgObj.name,
                            //Remove leading dot in main, so main paths are normalized,
                            //and remove any trailing .js, since different package
                            //envs have different conventions: some use a module name,
                            //some use a file name.
                            main: (pkgObj.main || 'main')
                                  .replace(currDirRegExp, '')
                                  .replace(jsSuffixRegExp, '')
                        };
                    });

                    //Done with modifications, assing packages back to context config
                    config.pkgs = pkgs;
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext, url,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        url = context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext || '.fake');
                        return ext ? url : url.substring(0, url.length - 5);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overriden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext) {
                var paths, pkgs, pkg, pkgPath, syms, i, parentModule, url,
                    parentPath;

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;
                    pkgs = config.pkgs;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');
                        pkg = getOwn(pkgs, parentModule);
                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        } else if (pkg) {
                            //If module name is just the package name, then looking
                            //for the main module.
                            if (moduleName === pkg.name) {
                                pkgPath = pkg.location + '/' + pkg.main;
                            } else {
                                pkgPath = pkg.location;
                            }
                            syms.splice(0, i, pkgPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/\?/.test(url) ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callack function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    return onError(makeError('scripterror', 'Script error', evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = function (err) {
        throw err;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = config.xhtml ?
                    document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                    document.createElement('script');
            node.type = config.scriptType || 'text/javascript';
            node.charset = 'utf-8';
            node.async = true;

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEvenListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            //In a web worker, use importScripts. This is not a very
            //efficient use of importScripts, importScripts will block until
            //its script is downloaded and evaluated. However, if web workers
            //are in play, the expectation that a build has been done so that
            //only one script needs to be loaded anyway. This may need to be
            //reevaluated if other use cases become common.
            importScripts(url);

            //Account for anonymous modules
            context.completeLoad(moduleName);
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = dataMain.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                    dataMain = mainScript;
                }

                //Strip off any trailing .js since dataMain is now
                //like a module name.
                dataMain = dataMain.replace(jsSuffixRegExp, '');

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(dataMain) : [dataMain];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = [];
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps.length && isFunction(callback)) {
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        (context ? context.defQueue : globalDefQueue).push([name, deps, callback]);
    };

    define.amd = {
        jQuery: true
    };


    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));

define("requireLib", function(){});

/* Zepto v1.0 - polyfill zepto detect event ajax form fx - zeptojs.com/license */

;(function(undefined){
  if (String.prototype.trim === undefined) // fix for iOS 3.2
    String.prototype.trim = function(){ return this.replace(/^\s+|\s+$/g, '') }

  // For iOS 3.x
  // from https://developer.mozilla.org/en/JavaScript/Reference/Global_Objects/Array/reduce
  if (Array.prototype.reduce === undefined)
    Array.prototype.reduce = function(fun){
      if(this === void 0 || this === null) throw new TypeError()
      var t = Object(this), len = t.length >>> 0, k = 0, accumulator
      if(typeof fun != 'function') throw new TypeError()
      if(len == 0 && arguments.length == 1) throw new TypeError()

      if(arguments.length >= 2)
       accumulator = arguments[1]
      else
        do{
          if(k in t){
            accumulator = t[k++]
            break
          }
          if(++k >= len) throw new TypeError()
        } while (true)

      while (k < len){
        if(k in t) accumulator = fun.call(undefined, accumulator, t[k], k, t)
        k++
      }
      return accumulator
    }

})()





var Zepto = (function() {
  var undefined, key, $, classList, emptyArray = [], slice = emptyArray.slice, filter = emptyArray.filter,
    document = window.document,
    elementDisplay = {}, classCache = {},
    getComputedStyle = document.defaultView.getComputedStyle,
    cssNumber = { 'column-count': 1, 'columns': 1, 'font-weight': 1, 'line-height': 1,'opacity': 1, 'z-index': 1, 'zoom': 1 },
    fragmentRE = /^\s*<(\w+|!)[^>]*>/,
    tagExpanderRE = /<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/ig,
    rootNodeRE = /^(?:body|html)$/i,

    // special attributes that should be get/set via method calls
    methodAttributes = ['val', 'css', 'html', 'text', 'data', 'width', 'height', 'offset'],

    adjacencyOperators = [ 'after', 'prepend', 'before', 'append' ],
    table = document.createElement('table'),
    tableRow = document.createElement('tr'),
    containers = {
      'tr': document.createElement('tbody'),
      'tbody': table, 'thead': table, 'tfoot': table,
      'td': tableRow, 'th': tableRow,
      '*': document.createElement('div')
    },
    readyRE = /complete|loaded|interactive/,
    classSelectorRE = /^\.([\w-]+)$/,
    idSelectorRE = /^#([\w-]*)$/,
    tagSelectorRE = /^[\w-]+$/,
    class2type = {},
    toString = class2type.toString,
    zepto = {},
    camelize, uniq,
    tempParent = document.createElement('div')

  zepto.matches = function(element, selector) {
    if (!element || element.nodeType !== 1) return false
    var matchesSelector = element.webkitMatchesSelector || element.mozMatchesSelector ||
                          element.oMatchesSelector || element.matchesSelector
    if (matchesSelector) return matchesSelector.call(element, selector)
    // fall back to performing a selector:
    var match, parent = element.parentNode, temp = !parent
    if (temp) (parent = tempParent).appendChild(element)
    match = ~zepto.qsa(parent, selector).indexOf(element)
    temp && tempParent.removeChild(element)
    return match
  }

  function type(obj) {
    return obj == null ? String(obj) :
      class2type[toString.call(obj)] || "object"
  }

  function isFunction(value) { return type(value) == "function" }
  function isWindow(obj)     { return obj != null && obj == obj.window }
  function isDocument(obj)   { return obj != null && obj.nodeType == obj.DOCUMENT_NODE }
  function isObject(obj)     { return type(obj) == "object" }
  function isPlainObject(obj) {
    return isObject(obj) && !isWindow(obj) && obj.__proto__ == Object.prototype
  }
  function isArray(value) { return value instanceof Array }
  function likeArray(obj) { return typeof obj.length == 'number' }

  function compact(array) { return filter.call(array, function(item){ return item != null }) }
  function flatten(array) { return array.length > 0 ? $.fn.concat.apply([], array) : array }
  camelize = function(str){ return str.replace(/-+(.)?/g, function(match, chr){ return chr ? chr.toUpperCase() : '' }) }
  function dasherize(str) {
    return str.replace(/::/g, '/')
           .replace(/([A-Z]+)([A-Z][a-z])/g, '$1_$2')
           .replace(/([a-z\d])([A-Z])/g, '$1_$2')
           .replace(/_/g, '-')
           .toLowerCase()
  }
  uniq = function(array){ return filter.call(array, function(item, idx){ return array.indexOf(item) == idx }) }

  function classRE(name) {
    return name in classCache ?
      classCache[name] : (classCache[name] = new RegExp('(^|\\s)' + name + '(\\s|$)'))
  }

  function maybeAddPx(name, value) {
    return (typeof value == "number" && !cssNumber[dasherize(name)]) ? value + "px" : value
  }

  function defaultDisplay(nodeName) {
    var element, display
    if (!elementDisplay[nodeName]) {
      element = document.createElement(nodeName)
      document.body.appendChild(element)
      display = getComputedStyle(element, '').getPropertyValue("display")
      element.parentNode.removeChild(element)
      display == "none" && (display = "block")
      elementDisplay[nodeName] = display
    }
    return elementDisplay[nodeName]
  }

  function children(element) {
    return 'children' in element ?
      slice.call(element.children) :
      $.map(element.childNodes, function(node){ if (node.nodeType == 1) return node })
  }

  // `$.zepto.fragment` takes a html string and an optional tag name
  // to generate DOM nodes nodes from the given html string.
  // The generated DOM nodes are returned as an array.
  // This function can be overriden in plugins for example to make
  // it compatible with browsers that don't support the DOM fully.
  zepto.fragment = function(html, name, properties) {
    if (html.replace) html = html.replace(tagExpanderRE, "<$1></$2>")
    if (name === undefined) name = fragmentRE.test(html) && RegExp.$1
    if (!(name in containers)) name = '*'

    var nodes, dom, container = containers[name]
    container.innerHTML = '' + html
    dom = $.each(slice.call(container.childNodes), function(){
      container.removeChild(this)
    })
    if (isPlainObject(properties)) {
      nodes = $(dom)
      $.each(properties, function(key, value) {
        if (methodAttributes.indexOf(key) > -1) nodes[key](value)
        else nodes.attr(key, value)
      })
    }
    return dom
  }

  // `$.zepto.Z` swaps out the prototype of the given `dom` array
  // of nodes with `$.fn` and thus supplying all the Zepto functions
  // to the array. Note that `__proto__` is not supported on Internet
  // Explorer. This method can be overriden in plugins.
  zepto.Z = function(dom, selector) {
    dom = dom || []
    dom.__proto__ = $.fn
    dom.selector = selector || ''
    return dom
  }

  // `$.zepto.isZ` should return `true` if the given object is a Zepto
  // collection. This method can be overriden in plugins.
  zepto.isZ = function(object) {
    return object instanceof zepto.Z
  }

  // `$.zepto.init` is Zepto's counterpart to jQuery's `$.fn.init` and
  // takes a CSS selector and an optional context (and handles various
  // special cases).
  // This method can be overriden in plugins.
  zepto.init = function(selector, context) {
    // If nothing given, return an empty Zepto collection
    if (!selector) return zepto.Z()
    // If a function is given, call it when the DOM is ready
    else if (isFunction(selector)) return $(document).ready(selector)
    // If a Zepto collection is given, juts return it
    else if (zepto.isZ(selector)) return selector
    else {
      var dom
      // normalize array if an array of nodes is given
      if (isArray(selector)) dom = compact(selector)
      // Wrap DOM nodes. If a plain object is given, duplicate it.
      else if (isObject(selector))
        dom = [isPlainObject(selector) ? $.extend({}, selector) : selector], selector = null
      // If it's a html fragment, create nodes from it
      else if (fragmentRE.test(selector))
        dom = zepto.fragment(selector.trim(), RegExp.$1, context), selector = null
      // If there's a context, create a collection on that context first, and select
      // nodes from there
      else if (context !== undefined) return $(context).find(selector)
      // And last but no least, if it's a CSS selector, use it to select nodes.
      else dom = zepto.qsa(document, selector)
      // create a new Zepto collection from the nodes found
      return zepto.Z(dom, selector)
    }
  }

  // `$` will be the base `Zepto` object. When calling this
  // function just call `$.zepto.init, which makes the implementation
  // details of selecting nodes and creating Zepto collections
  // patchable in plugins.
  $ = function(selector, context){
    return zepto.init(selector, context)
  }

  function extend(target, source, deep) {
    for (key in source)
      if (deep && (isPlainObject(source[key]) || isArray(source[key]))) {
        if (isPlainObject(source[key]) && !isPlainObject(target[key]))
          target[key] = {}
        if (isArray(source[key]) && !isArray(target[key]))
          target[key] = []
        extend(target[key], source[key], deep)
      }
      else if (source[key] !== undefined) target[key] = source[key]
  }

  // Copy all but undefined properties from one or more
  // objects to the `target` object.
  $.extend = function(target){
    var deep, args = slice.call(arguments, 1)
    if (typeof target == 'boolean') {
      deep = target
      target = args.shift()
    }
    args.forEach(function(arg){ extend(target, arg, deep) })
    return target
  }

  // `$.zepto.qsa` is Zepto's CSS selector implementation which
  // uses `document.querySelectorAll` and optimizes for some special cases, like `#id`.
  // This method can be overriden in plugins.
  zepto.qsa = function(element, selector){
    var found
    return (isDocument(element) && idSelectorRE.test(selector)) ?
      ( (found = element.getElementById(RegExp.$1)) ? [found] : [] ) :
      (element.nodeType !== 1 && element.nodeType !== 9) ? [] :
      slice.call(
        classSelectorRE.test(selector) ? element.getElementsByClassName(RegExp.$1) :
        tagSelectorRE.test(selector) ? element.getElementsByTagName(selector) :
        element.querySelectorAll(selector)
      )
  }

  function filtered(nodes, selector) {
    return selector === undefined ? $(nodes) : $(nodes).filter(selector)
  }

  $.contains = function(parent, node) {
    return parent !== node && parent.contains(node)
  }

  function funcArg(context, arg, idx, payload) {
    return isFunction(arg) ? arg.call(context, idx, payload) : arg
  }

  function setAttribute(node, name, value) {
    value == null ? node.removeAttribute(name) : node.setAttribute(name, value)
  }

  // access className property while respecting SVGAnimatedString
  function className(node, value){
    var klass = node.className,
        svg   = klass && klass.baseVal !== undefined

    if (value === undefined) return svg ? klass.baseVal : klass
    svg ? (klass.baseVal = value) : (node.className = value)
  }

  // "true"  => true
  // "false" => false
  // "null"  => null
  // "42"    => 42
  // "42.5"  => 42.5
  // JSON    => parse if valid
  // String  => self
  function deserializeValue(value) {
    var num
    try {
      return value ?
        value == "true" ||
        ( value == "false" ? false :
          value == "null" ? null :
          !isNaN(num = Number(value)) ? num :
          /^[\[\{]/.test(value) ? $.parseJSON(value) :
          value )
        : value
    } catch(e) {
      return value
    }
  }

  $.type = type
  $.isFunction = isFunction
  $.isWindow = isWindow
  $.isArray = isArray
  $.isPlainObject = isPlainObject

  $.isEmptyObject = function(obj) {
    var name
    for (name in obj) return false
    return true
  }

  $.inArray = function(elem, array, i){
    return emptyArray.indexOf.call(array, elem, i)
  }

  $.camelCase = camelize
  $.trim = function(str) { return str.trim() }

  // plugin compatibility
  $.uuid = 0
  $.support = { }
  $.expr = { }

  $.map = function(elements, callback){
    var value, values = [], i, key
    if (likeArray(elements))
      for (i = 0; i < elements.length; i++) {
        value = callback(elements[i], i)
        if (value != null) values.push(value)
      }
    else
      for (key in elements) {
        value = callback(elements[key], key)
        if (value != null) values.push(value)
      }
    return flatten(values)
  }

  $.each = function(elements, callback){
    var i, key
    if (likeArray(elements)) {
      for (i = 0; i < elements.length; i++)
        if (callback.call(elements[i], i, elements[i]) === false) return elements
    } else {
      for (key in elements)
        if (callback.call(elements[key], key, elements[key]) === false) return elements
    }

    return elements
  }

  $.grep = function(elements, callback){
    return filter.call(elements, callback)
  }

  if (window.JSON) $.parseJSON = JSON.parse

  // Populate the class2type map
  $.each("Boolean Number String Function Array Date RegExp Object Error".split(" "), function(i, name) {
    class2type[ "[object " + name + "]" ] = name.toLowerCase()
  })

  // Define methods that will be available on all
  // Zepto collections
  $.fn = {
    // Because a collection acts like an array
    // copy over these useful array functions.
    forEach: emptyArray.forEach,
    reduce: emptyArray.reduce,
    push: emptyArray.push,
    sort: emptyArray.sort,
    indexOf: emptyArray.indexOf,
    concat: emptyArray.concat,

    // `map` and `slice` in the jQuery API work differently
    // from their array counterparts
    map: function(fn){
      return $($.map(this, function(el, i){ return fn.call(el, i, el) }))
    },
    slice: function(){
      return $(slice.apply(this, arguments))
    },

    ready: function(callback){
      if (readyRE.test(document.readyState)) callback($)
      else document.addEventListener('DOMContentLoaded', function(){ callback($) }, false)
      return this
    },
    get: function(idx){
      return idx === undefined ? slice.call(this) : this[idx >= 0 ? idx : idx + this.length]
    },
    toArray: function(){ return this.get() },
    size: function(){
      return this.length
    },
    remove: function(){
      return this.each(function(){
        if (this.parentNode != null)
          this.parentNode.removeChild(this)
      })
    },
    each: function(callback){
      emptyArray.every.call(this, function(el, idx){
        return callback.call(el, idx, el) !== false
      })
      return this
    },
    filter: function(selector){
      if (isFunction(selector)) return this.not(this.not(selector))
      return $(filter.call(this, function(element){
        return zepto.matches(element, selector)
      }))
    },
    add: function(selector,context){
      return $(uniq(this.concat($(selector,context))))
    },
    is: function(selector){
      return this.length > 0 && zepto.matches(this[0], selector)
    },
    not: function(selector){
      var nodes=[]
      if (isFunction(selector) && selector.call !== undefined)
        this.each(function(idx){
          if (!selector.call(this,idx)) nodes.push(this)
        })
      else {
        var excludes = typeof selector == 'string' ? this.filter(selector) :
          (likeArray(selector) && isFunction(selector.item)) ? slice.call(selector) : $(selector)
        this.forEach(function(el){
          if (excludes.indexOf(el) < 0) nodes.push(el)
        })
      }
      return $(nodes)
    },
    has: function(selector){
      return this.filter(function(){
        return isObject(selector) ?
          $.contains(this, selector) :
          $(this).find(selector).size()
      })
    },
    eq: function(idx){
      return idx === -1 ? this.slice(idx) : this.slice(idx, + idx + 1)
    },
    first: function(){
      var el = this[0]
      return el && !isObject(el) ? el : $(el)
    },
    last: function(){
      var el = this[this.length - 1]
      return el && !isObject(el) ? el : $(el)
    },
    find: function(selector){
      var result, $this = this
      if (typeof selector == 'object')
        result = $(selector).filter(function(){
          var node = this
          return emptyArray.some.call($this, function(parent){
            return $.contains(parent, node)
          })
        })
      else if (this.length == 1) result = $(zepto.qsa(this[0], selector))
      else result = this.map(function(){ return zepto.qsa(this, selector) })
      return result
    },
    closest: function(selector, context){
      var node = this[0], collection = false
      if (typeof selector == 'object') collection = $(selector)
      while (node && !(collection ? collection.indexOf(node) >= 0 : zepto.matches(node, selector)))
        node = node !== context && !isDocument(node) && node.parentNode
      return $(node)
    },
    parents: function(selector){
      var ancestors = [], nodes = this
      while (nodes.length > 0)
        nodes = $.map(nodes, function(node){
          if ((node = node.parentNode) && !isDocument(node) && ancestors.indexOf(node) < 0) {
            ancestors.push(node)
            return node
          }
        })
      return filtered(ancestors, selector)
    },
    parent: function(selector){
      return filtered(uniq(this.pluck('parentNode')), selector)
    },
    children: function(selector){
      return filtered(this.map(function(){ return children(this) }), selector)
    },
    contents: function() {
      return this.map(function() { return slice.call(this.childNodes) })
    },
    siblings: function(selector){
      return filtered(this.map(function(i, el){
        return filter.call(children(el.parentNode), function(child){ return child!==el })
      }), selector)
    },
    empty: function(){
      return this.each(function(){ this.innerHTML = '' })
    },
    // `pluck` is borrowed from Prototype.js
    pluck: function(property){
      return $.map(this, function(el){ return el[property] })
    },
    show: function(){
      return this.each(function(){
        this.style.display == "none" && (this.style.display = null)
        if (getComputedStyle(this, '').getPropertyValue("display") == "none")
          this.style.display = defaultDisplay(this.nodeName)
      })
    },
    replaceWith: function(newContent){
      return this.before(newContent).remove()
    },
    wrap: function(structure){
      var func = isFunction(structure)
      if (this[0] && !func)
        var dom   = $(structure).get(0),
            clone = dom.parentNode || this.length > 1

      return this.each(function(index){
        $(this).wrapAll(
          func ? structure.call(this, index) :
            clone ? dom.cloneNode(true) : dom
        )
      })
    },
    wrapAll: function(structure){
      if (this[0]) {
        $(this[0]).before(structure = $(structure))
        var children
        // drill down to the inmost element
        while ((children = structure.children()).length) structure = children.first()
        $(structure).append(this)
      }
      return this
    },
    wrapInner: function(structure){
      var func = isFunction(structure)
      return this.each(function(index){
        var self = $(this), contents = self.contents(),
            dom  = func ? structure.call(this, index) : structure
        contents.length ? contents.wrapAll(dom) : self.append(dom)
      })
    },
    unwrap: function(){
      this.parent().each(function(){
        $(this).replaceWith($(this).children())
      })
      return this
    },
    clone: function(){
      return this.map(function(){ return this.cloneNode(true) })
    },
    hide: function(){
      return this.css("display", "none")
    },
    toggle: function(setting){
      return this.each(function(){
        var el = $(this)
        ;(setting === undefined ? el.css("display") == "none" : setting) ? el.show() : el.hide()
      })
    },
    prev: function(selector){ return $(this.pluck('previousElementSibling')).filter(selector || '*') },
    next: function(selector){ return $(this.pluck('nextElementSibling')).filter(selector || '*') },
    html: function(html){
      return html === undefined ?
        (this.length > 0 ? this[0].innerHTML : null) :
        this.each(function(idx){
          var originHtml = this.innerHTML
          $(this).empty().append( funcArg(this, html, idx, originHtml) )
        })
    },
    text: function(text){
      return text === undefined ?
        (this.length > 0 ? this[0].textContent : null) :
        this.each(function(){ this.textContent = text })
    },
    attr: function(name, value){
      var result
      return (typeof name == 'string' && value === undefined) ?
        (this.length == 0 || this[0].nodeType !== 1 ? undefined :
          (name == 'value' && this[0].nodeName == 'INPUT') ? this.val() :
          (!(result = this[0].getAttribute(name)) && name in this[0]) ? this[0][name] : result
        ) :
        this.each(function(idx){
          if (this.nodeType !== 1) return
          if (isObject(name)) for (key in name) setAttribute(this, key, name[key])
          else setAttribute(this, name, funcArg(this, value, idx, this.getAttribute(name)))
        })
    },
    removeAttr: function(name){
      return this.each(function(){ this.nodeType === 1 && setAttribute(this, name) })
    },
    prop: function(name, value){
      return (value === undefined) ?
        (this[0] && this[0][name]) :
        this.each(function(idx){
          this[name] = funcArg(this, value, idx, this[name])
        })
    },
    data: function(name, value){
      var data = this.attr('data-' + dasherize(name), value)
      return data !== null ? deserializeValue(data) : undefined
    },
    val: function(value){
      return (value === undefined) ?
        (this[0] && (this[0].multiple ?
           $(this[0]).find('option').filter(function(o){ return this.selected }).pluck('value') :
           this[0].value)
        ) :
        this.each(function(idx){
          this.value = funcArg(this, value, idx, this.value)
        })
    },
    offset: function(coordinates){
      if (coordinates) return this.each(function(index){
        var $this = $(this),
            coords = funcArg(this, coordinates, index, $this.offset()),
            parentOffset = $this.offsetParent().offset(),
            props = {
              top:  coords.top  - parentOffset.top,
              left: coords.left - parentOffset.left
            }

        if ($this.css('position') == 'static') props['position'] = 'relative'
        $this.css(props)
      })
      if (this.length==0) return null
      var obj = this[0].getBoundingClientRect()
      return {
        left: obj.left + window.pageXOffset,
        top: obj.top + window.pageYOffset,
        width: Math.round(obj.width),
        height: Math.round(obj.height)
      }
    },
    css: function(property, value){
      if (arguments.length < 2 && typeof property == 'string')
        return this[0] && (this[0].style[camelize(property)] || getComputedStyle(this[0], '').getPropertyValue(property))

      var css = ''
      if (type(property) == 'string') {
        if (!value && value !== 0)
          this.each(function(){ this.style.removeProperty(dasherize(property)) })
        else
          css = dasherize(property) + ":" + maybeAddPx(property, value)
      } else {
        for (key in property)
          if (!property[key] && property[key] !== 0)
            this.each(function(){ this.style.removeProperty(dasherize(key)) })
          else
            css += dasherize(key) + ':' + maybeAddPx(key, property[key]) + ';'
      }

      return this.each(function(){ this.style.cssText += ';' + css })
    },
    index: function(element){
      return element ? this.indexOf($(element)[0]) : this.parent().children().indexOf(this[0])
    },
    hasClass: function(name){
      return emptyArray.some.call(this, function(el){
        return this.test(className(el))
      }, classRE(name))
    },
    addClass: function(name){
      return this.each(function(idx){
        classList = []
        var cls = className(this), newName = funcArg(this, name, idx, cls)
        newName.split(/\s+/g).forEach(function(klass){
          if (!$(this).hasClass(klass)) classList.push(klass)
        }, this)
        classList.length && className(this, cls + (cls ? " " : "") + classList.join(" "))
      })
    },
    removeClass: function(name){
      return this.each(function(idx){
        if (name === undefined) return className(this, '')
        classList = className(this)
        funcArg(this, name, idx, classList).split(/\s+/g).forEach(function(klass){
          classList = classList.replace(classRE(klass), " ")
        })
        className(this, classList.trim())
      })
    },
    toggleClass: function(name, when){
      return this.each(function(idx){
        var $this = $(this), names = funcArg(this, name, idx, className(this))
        names.split(/\s+/g).forEach(function(klass){
          (when === undefined ? !$this.hasClass(klass) : when) ?
            $this.addClass(klass) : $this.removeClass(klass)
        })
      })
    },
    scrollTop: function(){
      if (!this.length) return
      return ('scrollTop' in this[0]) ? this[0].scrollTop : this[0].scrollY
    },
    position: function() {
      if (!this.length) return

      var elem = this[0],
        // Get *real* offsetParent
        offsetParent = this.offsetParent(),
        // Get correct offsets
        offset       = this.offset(),
        parentOffset = rootNodeRE.test(offsetParent[0].nodeName) ? { top: 0, left: 0 } : offsetParent.offset()

      // Subtract element margins
      // note: when an element has margin: auto the offsetLeft and marginLeft
      // are the same in Safari causing offset.left to incorrectly be 0
      offset.top  -= parseFloat( $(elem).css('margin-top') ) || 0
      offset.left -= parseFloat( $(elem).css('margin-left') ) || 0

      // Add offsetParent borders
      parentOffset.top  += parseFloat( $(offsetParent[0]).css('border-top-width') ) || 0
      parentOffset.left += parseFloat( $(offsetParent[0]).css('border-left-width') ) || 0

      // Subtract the two offsets
      return {
        top:  offset.top  - parentOffset.top,
        left: offset.left - parentOffset.left
      }
    },
    offsetParent: function() {
      return this.map(function(){
        var parent = this.offsetParent || document.body
        while (parent && !rootNodeRE.test(parent.nodeName) && $(parent).css("position") == "static")
          parent = parent.offsetParent
        return parent
      })
    }
  }

  // for now
  $.fn.detach = $.fn.remove

  // Generate the `width` and `height` functions
  ;['width', 'height'].forEach(function(dimension){
    $.fn[dimension] = function(value){
      var offset, el = this[0],
        Dimension = dimension.replace(/./, function(m){ return m[0].toUpperCase() })
      if (value === undefined) return isWindow(el) ? el['inner' + Dimension] :
        isDocument(el) ? el.documentElement['offset' + Dimension] :
        (offset = this.offset()) && offset[dimension]
      else return this.each(function(idx){
        el = $(this)
        el.css(dimension, funcArg(this, value, idx, el[dimension]()))
      })
    }
  })

  function traverseNode(node, fun) {
    fun(node)
    for (var key in node.childNodes) traverseNode(node.childNodes[key], fun)
  }

  // Generate the `after`, `prepend`, `before`, `append`,
  // `insertAfter`, `insertBefore`, `appendTo`, and `prependTo` methods.
  adjacencyOperators.forEach(function(operator, operatorIndex) {
    var inside = operatorIndex % 2 //=> prepend, append

    $.fn[operator] = function(){
      // arguments can be nodes, arrays of nodes, Zepto objects and HTML strings
      var argType, nodes = $.map(arguments, function(arg) {
            argType = type(arg)
            return argType == "object" || argType == "array" || arg == null ?
              arg : zepto.fragment(arg)
          }),
          parent, copyByClone = this.length > 1
      if (nodes.length < 1) return this

      return this.each(function(_, target){
        parent = inside ? target : target.parentNode

        // convert all methods to a "before" operation
        target = operatorIndex == 0 ? target.nextSibling :
                 operatorIndex == 1 ? target.firstChild :
                 operatorIndex == 2 ? target :
                 null

        nodes.forEach(function(node){
          if (copyByClone) node = node.cloneNode(true)
          else if (!parent) return $(node).remove()

          traverseNode(parent.insertBefore(node, target), function(el){
            if (el.nodeName != null && el.nodeName.toUpperCase() === 'SCRIPT' &&
               (!el.type || el.type === 'text/javascript') && !el.src)
              window['eval'].call(window, el.innerHTML)
          })
        })
      })
    }

    // after    => insertAfter
    // prepend  => prependTo
    // before   => insertBefore
    // append   => appendTo
    $.fn[inside ? operator+'To' : 'insert'+(operatorIndex ? 'Before' : 'After')] = function(html){
      $(html)[operator](this)
      return this
    }
  })

  zepto.Z.prototype = $.fn

  // Export internal API functions in the `$.zepto` namespace
  zepto.uniq = uniq
  zepto.deserializeValue = deserializeValue
  $.zepto = zepto

  return $
})()


window.Zepto = Zepto
'$' in window || (window.$ = Zepto)





;(function($){
  function detect(ua){
    var os = this.os = {}, browser = this.browser = {},
      webkit = ua.match(/WebKit\/([\d.]+)/),
      android = ua.match(/(Android)\s+([\d.]+)/),
      ipad = ua.match(/(iPad).*OS\s([\d_]+)/),
      iphone = !ipad && ua.match(/(iPhone\sOS)\s([\d_]+)/),
      webos = ua.match(/(webOS|hpwOS)[\s\/]([\d.]+)/),
      touchpad = webos && ua.match(/TouchPad/),
      kindle = ua.match(/Kindle\/([\d.]+)/),
      silk = ua.match(/Silk\/([\d._]+)/),
      blackberry = ua.match(/(BlackBerry).*Version\/([\d.]+)/),
      bb10 = ua.match(/(BB10).*Version\/([\d.]+)/),
      rimtabletos = ua.match(/(RIM\sTablet\sOS)\s([\d.]+)/),
      playbook = ua.match(/PlayBook/),
      chrome = ua.match(/Chrome\/([\d.]+)/) || ua.match(/CriOS\/([\d.]+)/),
      firefox = ua.match(/Firefox\/([\d.]+)/)

    // Todo: clean this up with a better OS/browser seperation:
    // - discern (more) between multiple browsers on android
    // - decide if kindle fire in silk mode is android or not
    // - Firefox on Android doesn't specify the Android version
    // - possibly devide in os, device and browser hashes

    if (browser.webkit = !!webkit) browser.version = webkit[1]

    if (android) os.android = true, os.version = android[2]
    if (iphone) os.ios = os.iphone = true, os.version = iphone[2].replace(/_/g, '.')
    if (ipad) os.ios = os.ipad = true, os.version = ipad[2].replace(/_/g, '.')
    if (webos) os.webos = true, os.version = webos[2]
    if (touchpad) os.touchpad = true
    if (blackberry) os.blackberry = true, os.version = blackberry[2]
    if (bb10) os.bb10 = true, os.version = bb10[2]
    if (rimtabletos) os.rimtabletos = true, os.version = rimtabletos[2]
    if (playbook) browser.playbook = true
    if (kindle) os.kindle = true, os.version = kindle[1]
    if (silk) browser.silk = true, browser.version = silk[1]
    if (!silk && os.android && ua.match(/Kindle Fire/)) browser.silk = true
    if (chrome) browser.chrome = true, browser.version = chrome[1]
    if (firefox) browser.firefox = true, browser.version = firefox[1]

    os.tablet = !!(ipad || playbook || (android && !ua.match(/Mobile/)) || (firefox && ua.match(/Tablet/)))
    os.phone  = !!(!os.tablet && (android || iphone || webos || blackberry || bb10 ||
      (chrome && ua.match(/Android/)) || (chrome && ua.match(/CriOS\/([\d.]+)/)) || (firefox && ua.match(/Mobile/))))
  }

  detect.call($, navigator.userAgent)
  // make available to unit tests
  $.__detect = detect

})(Zepto)





;(function($){
  var $$ = $.zepto.qsa, handlers = {}, _zid = 1, specialEvents={},
      hover = { mouseenter: 'mouseover', mouseleave: 'mouseout' }

  specialEvents.click = specialEvents.mousedown = specialEvents.mouseup = specialEvents.mousemove = 'MouseEvents'

  function zid(element) {
    return element._zid || (element._zid = _zid++)
  }
  function findHandlers(element, event, fn, selector) {
    event = parse(event)
    if (event.ns) var matcher = matcherFor(event.ns)
    return (handlers[zid(element)] || []).filter(function(handler) {
      return handler
        && (!event.e  || handler.e == event.e)
        && (!event.ns || matcher.test(handler.ns))
        && (!fn       || zid(handler.fn) === zid(fn))
        && (!selector || handler.sel == selector)
    })
  }
  function parse(event) {
    var parts = ('' + event).split('.')
    return {e: parts[0], ns: parts.slice(1).sort().join(' ')}
  }
  function matcherFor(ns) {
    return new RegExp('(?:^| )' + ns.replace(' ', ' .* ?') + '(?: |$)')
  }

  function eachEvent(events, fn, iterator){
    if ($.type(events) != "string") $.each(events, iterator)
    else events.split(/\s/).forEach(function(type){ iterator(type, fn) })
  }

  function eventCapture(handler, captureSetting) {
    return handler.del &&
      (handler.e == 'focus' || handler.e == 'blur') ||
      !!captureSetting
  }

  function realEvent(type) {
    return hover[type] || type
  }

  function add(element, events, fn, selector, getDelegate, capture){
    var id = zid(element), set = (handlers[id] || (handlers[id] = []))
    eachEvent(events, fn, function(event, fn){
      var handler   = parse(event)
      handler.fn    = fn
      handler.sel   = selector
      // emulate mouseenter, mouseleave
      if (handler.e in hover) fn = function(e){
        var related = e.relatedTarget
        if (!related || (related !== this && !$.contains(this, related)))
          return handler.fn.apply(this, arguments)
      }
      handler.del   = getDelegate && getDelegate(fn, event)
      var callback  = handler.del || fn
      handler.proxy = function (e) {
        var result = callback.apply(element, [e].concat(e.data))
        if (result === false) e.preventDefault(), e.stopPropagation()
        return result
      }
      handler.i = set.length
      set.push(handler)
      element.addEventListener(realEvent(handler.e), handler.proxy, eventCapture(handler, capture))
    })
  }
  function remove(element, events, fn, selector, capture){
    var id = zid(element)
    eachEvent(events || '', fn, function(event, fn){
      findHandlers(element, event, fn, selector).forEach(function(handler){
        delete handlers[id][handler.i]
        element.removeEventListener(realEvent(handler.e), handler.proxy, eventCapture(handler, capture))
      })
    })
  }

  $.event = { add: add, remove: remove }

  $.proxy = function(fn, context) {
    if ($.isFunction(fn)) {
      var proxyFn = function(){ return fn.apply(context, arguments) }
      proxyFn._zid = zid(fn)
      return proxyFn
    } else if (typeof context == 'string') {
      return $.proxy(fn[context], fn)
    } else {
      throw new TypeError("expected function")
    }
  }

  $.fn.bind = function(event, callback){
    return this.each(function(){
      add(this, event, callback)
    })
  }
  $.fn.unbind = function(event, callback){
    return this.each(function(){
      remove(this, event, callback)
    })
  }
  $.fn.one = function(event, callback){
    return this.each(function(i, element){
      add(this, event, callback, null, function(fn, type){
        return function(){
          var result = fn.apply(element, arguments)
          remove(element, type, fn)
          return result
        }
      })
    })
  }

  var returnTrue = function(){return true},
      returnFalse = function(){return false},
      ignoreProperties = /^([A-Z]|layer[XY]$)/,
      eventMethods = {
        preventDefault: 'isDefaultPrevented',
        stopImmediatePropagation: 'isImmediatePropagationStopped',
        stopPropagation: 'isPropagationStopped'
      }
  function createProxy(event) {
    var key, proxy = { originalEvent: event }
    for (key in event)
      if (!ignoreProperties.test(key) && event[key] !== undefined) proxy[key] = event[key]

    $.each(eventMethods, function(name, predicate) {
      proxy[name] = function(){
        this[predicate] = returnTrue
        return event[name].apply(event, arguments)
      }
      proxy[predicate] = returnFalse
    })
    return proxy
  }

  // emulates the 'defaultPrevented' property for browsers that have none
  function fix(event) {
    if (!('defaultPrevented' in event)) {
      event.defaultPrevented = false
      var prevent = event.preventDefault
      event.preventDefault = function() {
        this.defaultPrevented = true
        prevent.call(this)
      }
    }
  }

  $.fn.delegate = function(selector, event, callback){
    return this.each(function(i, element){
      add(element, event, callback, selector, function(fn){
        return function(e){
          var evt, match = $(e.target).closest(selector, element).get(0)
          if (match) {
            evt = $.extend(createProxy(e), {currentTarget: match, liveFired: element})
            return fn.apply(match, [evt].concat([].slice.call(arguments, 1)))
          }
        }
      })
    })
  }
  $.fn.undelegate = function(selector, event, callback){
    return this.each(function(){
      remove(this, event, callback, selector)
    })
  }

  $.fn.live = function(event, callback){
    $(document.body).delegate(this.selector, event, callback)
    return this
  }
  $.fn.die = function(event, callback){
    $(document.body).undelegate(this.selector, event, callback)
    return this
  }

  $.fn.on = function(event, selector, callback){
    return !selector || $.isFunction(selector) ?
      this.bind(event, selector || callback) : this.delegate(selector, event, callback)
  }
  $.fn.off = function(event, selector, callback){
    return !selector || $.isFunction(selector) ?
      this.unbind(event, selector || callback) : this.undelegate(selector, event, callback)
  }

  $.fn.trigger = function(event, data){
    if (typeof event == 'string' || $.isPlainObject(event)) event = $.Event(event)
    fix(event)
    event.data = data
    return this.each(function(){
      // items in the collection might not be DOM elements
      // (todo: possibly support events on plain old objects)
      if('dispatchEvent' in this) this.dispatchEvent(event)
    })
  }

  // triggers event handlers on current element just as if an event occurred,
  // doesn't trigger an actual event, doesn't bubble
  $.fn.triggerHandler = function(event, data){
    var e, result
    this.each(function(i, element){
      e = createProxy(typeof event == 'string' ? $.Event(event) : event)
      e.data = data
      e.target = element
      $.each(findHandlers(element, event.type || event), function(i, handler){
        result = handler.proxy(e)
        if (e.isImmediatePropagationStopped()) return false
      })
    })
    return result
  }

  // shortcut methods for `.bind(event, fn)` for each event type
  ;('focusin focusout load resize scroll unload click dblclick '+
  'mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave '+
  'change select keydown keypress keyup error').split(' ').forEach(function(event) {
    $.fn[event] = function(callback) {
      return callback ?
        this.bind(event, callback) :
        this.trigger(event)
    }
  })

  ;['focus', 'blur'].forEach(function(name) {
    $.fn[name] = function(callback) {
      if (callback) this.bind(name, callback)
      else this.each(function(){
        try { this[name]() }
        catch(e) {}
      })
      return this
    }
  })

  $.Event = function(type, props) {
    if (typeof type != 'string') props = type, type = props.type
    var event = document.createEvent(specialEvents[type] || 'Events'), bubbles = true
    if (props) for (var name in props) (name == 'bubbles') ? (bubbles = !!props[name]) : (event[name] = props[name])
    event.initEvent(type, bubbles, true, null, null, null, null, null, null, null, null, null, null, null, null)
    event.isDefaultPrevented = function(){ return this.defaultPrevented }
    return event
  }

})(Zepto)





;(function($){
  var jsonpID = 0,
      document = window.document,
      key,
      name,
      rscript = /<script\b[^<]*(?:(?!<\/script>)<[^<]*)*<\/script>/gi,
      scriptTypeRE = /^(?:text|application)\/javascript/i,
      xmlTypeRE = /^(?:text|application)\/xml/i,
      jsonType = 'application/json',
      htmlType = 'text/html',
      blankRE = /^\s*$/

  // trigger a custom event and return false if it was cancelled
  function triggerAndReturn(context, eventName, data) {
    var event = $.Event(eventName)
    $(context).trigger(event, data)
    return !event.defaultPrevented
  }

  // trigger an Ajax "global" event
  function triggerGlobal(settings, context, eventName, data) {
    if (settings.global) return triggerAndReturn(context || document, eventName, data)
  }

  // Number of active Ajax requests
  $.active = 0

  function ajaxStart(settings) {
    if (settings.global && $.active++ === 0) triggerGlobal(settings, null, 'ajaxStart')
  }
  function ajaxStop(settings) {
    if (settings.global && !(--$.active)) triggerGlobal(settings, null, 'ajaxStop')
  }

  // triggers an extra global event "ajaxBeforeSend" that's like "ajaxSend" but cancelable
  function ajaxBeforeSend(xhr, settings) {
    var context = settings.context
    if (settings.beforeSend.call(context, xhr, settings) === false ||
        triggerGlobal(settings, context, 'ajaxBeforeSend', [xhr, settings]) === false)
      return false

    triggerGlobal(settings, context, 'ajaxSend', [xhr, settings])
  }
  function ajaxSuccess(data, xhr, settings) {
    var context = settings.context, status = 'success'
    settings.success.call(context, data, status, xhr)
    triggerGlobal(settings, context, 'ajaxSuccess', [xhr, settings, data])
    ajaxComplete(status, xhr, settings)
  }
  // type: "timeout", "error", "abort", "parsererror"
  function ajaxError(error, type, xhr, settings) {
    var context = settings.context
    settings.error.call(context, xhr, type, error)
    triggerGlobal(settings, context, 'ajaxError', [xhr, settings, error])
    ajaxComplete(type, xhr, settings)
  }
  // status: "success", "notmodified", "error", "timeout", "abort", "parsererror"
  function ajaxComplete(status, xhr, settings) {
    var context = settings.context
    settings.complete.call(context, xhr, status)
    triggerGlobal(settings, context, 'ajaxComplete', [xhr, settings])
    ajaxStop(settings)
  }

  // Empty function, used as default callback
  function empty() {}

  $.ajaxJSONP = function(options){
    if (!('type' in options)) return $.ajax(options)

    var callbackName = 'jsonp' + (++jsonpID),
      script = document.createElement('script'),
      cleanup = function() {
        clearTimeout(abortTimeout)
        $(script).remove()
        delete window[callbackName]
      },
      abort = function(type){
        cleanup()
        // In case of manual abort or timeout, keep an empty function as callback
        // so that the SCRIPT tag that eventually loads won't result in an error.
        if (!type || type == 'timeout') window[callbackName] = empty
        ajaxError(null, type || 'abort', xhr, options)
      },
      xhr = { abort: abort }, abortTimeout

    if (ajaxBeforeSend(xhr, options) === false) {
      abort('abort')
      return false
    }

    window[callbackName] = function(data){
      cleanup()
      ajaxSuccess(data, xhr, options)
    }

    script.onerror = function() { abort('error') }

    script.src = options.url.replace(/=\?/, '=' + callbackName)
    $('head').append(script)

    if (options.timeout > 0) abortTimeout = setTimeout(function(){
      abort('timeout')
    }, options.timeout)

    return xhr
  }

  $.ajaxSettings = {
    // Default type of request
    type: 'GET',
    // Callback that is executed before request
    beforeSend: empty,
    // Callback that is executed if the request succeeds
    success: empty,
    // Callback that is executed the the server drops error
    error: empty,
    // Callback that is executed on request complete (both: error and success)
    complete: empty,
    // The context for the callbacks
    context: null,
    // Whether to trigger "global" Ajax events
    global: true,
    // Transport
    xhr: function () {
      return new window.XMLHttpRequest()
    },
    // MIME types mapping
    accepts: {
      script: 'text/javascript, application/javascript',
      json:   jsonType,
      xml:    'application/xml, text/xml',
      html:   htmlType,
      text:   'text/plain'
    },
    // Whether the request is to another domain
    crossDomain: false,
    // Default timeout
    timeout: 0,
    // Whether data should be serialized to string
    processData: true,
    // Whether the browser should be allowed to cache GET responses
    cache: true,
  }

  function mimeToDataType(mime) {
    if (mime) mime = mime.split(';', 2)[0]
    return mime && ( mime == htmlType ? 'html' :
      mime == jsonType ? 'json' :
      scriptTypeRE.test(mime) ? 'script' :
      xmlTypeRE.test(mime) && 'xml' ) || 'text'
  }

  function appendQuery(url, query) {
    return (url + '&' + query).replace(/[&?]{1,2}/, '?')
  }

  // serialize payload and append it to the URL for GET requests
  function serializeData(options) {
    if (options.processData && options.data && $.type(options.data) != "string")
      options.data = $.param(options.data, options.traditional)
    if (options.data && (!options.type || options.type.toUpperCase() == 'GET'))
      options.url = appendQuery(options.url, options.data)
  }

  $.ajax = function(options){
    var settings = $.extend({}, options || {})
    for (key in $.ajaxSettings) if (settings[key] === undefined) settings[key] = $.ajaxSettings[key]

    ajaxStart(settings)

    if (!settings.crossDomain) settings.crossDomain = /^([\w-]+:)?\/\/([^\/]+)/.test(settings.url) &&
      RegExp.$2 != window.location.host

    if (!settings.url) settings.url = window.location.toString()
    serializeData(settings)
    if (settings.cache === false) settings.url = appendQuery(settings.url, '_=' + Date.now())

    var dataType = settings.dataType, hasPlaceholder = /=\?/.test(settings.url)
    if (dataType == 'jsonp' || hasPlaceholder) {
      if (!hasPlaceholder) settings.url = appendQuery(settings.url, 'callback=?')
      return $.ajaxJSONP(settings)
    }

    var mime = settings.accepts[dataType],
        baseHeaders = { },
        protocol = /^([\w-]+:)\/\//.test(settings.url) ? RegExp.$1 : window.location.protocol,
        xhr = settings.xhr(), abortTimeout

    if (!settings.crossDomain) baseHeaders['X-Requested-With'] = 'XMLHttpRequest'
    if (mime) {
      baseHeaders['Accept'] = mime
      if (mime.indexOf(',') > -1) mime = mime.split(',', 2)[0]
      xhr.overrideMimeType && xhr.overrideMimeType(mime)
    }
    if (settings.contentType || (settings.contentType !== false && settings.data && settings.type.toUpperCase() != 'GET'))
      baseHeaders['Content-Type'] = (settings.contentType || 'application/x-www-form-urlencoded')
    settings.headers = $.extend(baseHeaders, settings.headers || {})

    xhr.onreadystatechange = function(){
      if (xhr.readyState == 4) {
        xhr.onreadystatechange = empty;
        clearTimeout(abortTimeout)
        var result, error = false
        if ((xhr.status >= 200 && xhr.status < 300) || xhr.status == 304 || (xhr.status == 0 && protocol == 'file:')) {
          dataType = dataType || mimeToDataType(xhr.getResponseHeader('content-type'))
          result = xhr.responseText

          try {
            // http://perfectionkills.com/global-eval-what-are-the-options/
            if (dataType == 'script')    (1,eval)(result)
            else if (dataType == 'xml')  result = xhr.responseXML
            else if (dataType == 'json') result = blankRE.test(result) ? null : $.parseJSON(result)
          } catch (e) { error = e }

          if (error) ajaxError(error, 'parsererror', xhr, settings)
          else ajaxSuccess(result, xhr, settings)
        } else {
          ajaxError(null, xhr.status ? 'error' : 'abort', xhr, settings)
        }
      }
    }

    var async = 'async' in settings ? settings.async : true
    xhr.open(settings.type, settings.url, async)

    for (name in settings.headers) xhr.setRequestHeader(name, settings.headers[name])

    if (ajaxBeforeSend(xhr, settings) === false) {
      xhr.abort()
      return false
    }

    if (settings.timeout > 0) abortTimeout = setTimeout(function(){
        xhr.onreadystatechange = empty
        xhr.abort()
        ajaxError(null, 'timeout', xhr, settings)
      }, settings.timeout)

    // avoid sending empty string (#319)
    xhr.send(settings.data ? settings.data : null)
    return xhr
  }

  // handle optional data/success arguments
  function parseArguments(url, data, success, dataType) {
    var hasData = !$.isFunction(data)
    return {
      url:      url,
      data:     hasData  ? data : undefined,
      success:  !hasData ? data : $.isFunction(success) ? success : undefined,
      dataType: hasData  ? dataType || success : success
    }
  }

  $.get = function(url, data, success, dataType){
    return $.ajax(parseArguments.apply(null, arguments))
  }

  $.post = function(url, data, success, dataType){
    var options = parseArguments.apply(null, arguments)
    options.type = 'POST'
    return $.ajax(options)
  }

  $.getJSON = function(url, data, success){
    var options = parseArguments.apply(null, arguments)
    options.dataType = 'json'
    return $.ajax(options)
  }

  $.fn.load = function(url, data, success){
    if (!this.length) return this
    var self = this, parts = url.split(/\s/), selector,
        options = parseArguments(url, data, success),
        callback = options.success
    if (parts.length > 1) options.url = parts[0], selector = parts[1]
    options.success = function(response){
      self.html(selector ?
        $('<div>').html(response.replace(rscript, "")).find(selector)
        : response)
      callback && callback.apply(self, arguments)
    }
    $.ajax(options)
    return this
  }

  var escape = encodeURIComponent

  function serialize(params, obj, traditional, scope){
    var type, array = $.isArray(obj)
    $.each(obj, function(key, value) {
      type = $.type(value)
      if (scope) key = traditional ? scope : scope + '[' + (array ? '' : key) + ']'
      // handle data in serializeArray() format
      if (!scope && array) params.add(value.name, value.value)
      // recurse into nested objects
      else if (type == "array" || (!traditional && type == "object"))
        serialize(params, value, traditional, key)
      else params.add(key, value)
    })
  }

  $.param = function(obj, traditional){
    var params = []
    params.add = function(k, v){ this.push(escape(k) + '=' + escape(v)) }
    serialize(params, obj, traditional)
    return params.join('&').replace(/%20/g, '+')
  }
})(Zepto)





;(function ($) {
  $.fn.serializeArray = function () {
    var result = [], el
    $( Array.prototype.slice.call(this.get(0).elements) ).each(function () {
      el = $(this)
      var type = el.attr('type')
      if (this.nodeName.toLowerCase() != 'fieldset' &&
        !this.disabled && type != 'submit' && type != 'reset' && type != 'button' &&
        ((type != 'radio' && type != 'checkbox') || this.checked))
        result.push({
          name: el.attr('name'),
          value: el.val()
        })
    })
    return result
  }

  $.fn.serialize = function () {
    var result = []
    this.serializeArray().forEach(function (elm) {
      result.push( encodeURIComponent(elm.name) + '=' + encodeURIComponent(elm.value) )
    })
    return result.join('&')
  }

  $.fn.submit = function (callback) {
    if (callback) this.bind('submit', callback)
    else if (this.length) {
      var event = $.Event('submit')
      this.eq(0).trigger(event)
      if (!event.defaultPrevented) this.get(0).submit()
    }
    return this
  }

})(Zepto)





;(function($, undefined){
  var prefix = '', eventPrefix, endEventName, endAnimationName,
    vendors = { Webkit: 'webkit', Moz: '', O: 'o', ms: 'MS' },
    document = window.document, testEl = document.createElement('div'),
    supportedTransforms = /^((translate|rotate|scale)(X|Y|Z|3d)?|matrix(3d)?|perspective|skew(X|Y)?)$/i,
    transform,
    transitionProperty, transitionDuration, transitionTiming,
    animationName, animationDuration, animationTiming,
    cssReset = {}

  function dasherize(str) { return downcase(str.replace(/([a-z])([A-Z])/, '$1-$2')) }
  function downcase(str) { return str.toLowerCase() }
  function normalizeEvent(name) { return eventPrefix ? eventPrefix + name : downcase(name) }

  $.each(vendors, function(vendor, event){
    if (testEl.style[vendor + 'TransitionProperty'] !== undefined) {
      prefix = '-' + downcase(vendor) + '-'
      eventPrefix = event
      return false
    }
  })

  transform = prefix + 'transform'
  cssReset[transitionProperty = prefix + 'transition-property'] =
  cssReset[transitionDuration = prefix + 'transition-duration'] =
  cssReset[transitionTiming   = prefix + 'transition-timing-function'] =
  cssReset[animationName      = prefix + 'animation-name'] =
  cssReset[animationDuration  = prefix + 'animation-duration'] =
  cssReset[animationTiming    = prefix + 'animation-timing-function'] = ''

  $.fx = {
    off: (eventPrefix === undefined && testEl.style.transitionProperty === undefined),
    speeds: { _default: 400, fast: 200, slow: 600 },
    cssPrefix: prefix,
    transitionEnd: normalizeEvent('TransitionEnd'),
    animationEnd: normalizeEvent('AnimationEnd')
  }

  $.fn.animate = function(properties, duration, ease, callback){
    if ($.isPlainObject(duration))
      ease = duration.easing, callback = duration.complete, duration = duration.duration
    if (duration) duration = (typeof duration == 'number' ? duration :
                    ($.fx.speeds[duration] || $.fx.speeds._default)) / 1000
    return this.anim(properties, duration, ease, callback)
  }

  $.fn.anim = function(properties, duration, ease, callback){
    var key, cssValues = {}, cssProperties, transforms = '',
        that = this, wrappedCallback, endEvent = $.fx.transitionEnd

    if (duration === undefined) duration = 0.4
    if ($.fx.off) duration = 0

    if (typeof properties == 'string') {
      // keyframe animation
      cssValues[animationName] = properties
      cssValues[animationDuration] = duration + 's'
      cssValues[animationTiming] = (ease || 'linear')
      endEvent = $.fx.animationEnd
    } else {
      cssProperties = []
      // CSS transitions
      for (key in properties)
        if (supportedTransforms.test(key)) transforms += key + '(' + properties[key] + ') '
        else cssValues[key] = properties[key], cssProperties.push(dasherize(key))

      if (transforms) cssValues[transform] = transforms, cssProperties.push(transform)
      if (duration > 0 && typeof properties === 'object') {
        cssValues[transitionProperty] = cssProperties.join(', ')
        cssValues[transitionDuration] = duration + 's'
        cssValues[transitionTiming] = (ease || 'linear')
      }
    }

    wrappedCallback = function(event){
      if (typeof event !== 'undefined') {
        if (event.target !== event.currentTarget) return // makes sure the event didn't bubble from "below"
        $(event.target).unbind(endEvent, wrappedCallback)
      }
      $(this).css(cssReset)
      callback && callback.call(this)
    }
    if (duration > 0) this.bind(endEvent, wrappedCallback)

    // trigger page reflow so new elements can animate
    this.size() && this.get(0).clientLeft

    this.css(cssValues)

    if (duration <= 0) setTimeout(function() {
      that.each(function(){ wrappedCallback.call(this) })
    }, 0)

    return this
  }

  testEl = null
})(Zepto)
;
define("lib/zepto/zepto", (function (global) {
    return function () {
        var ret, fn;
        return ret || global.$;
    };
}(this)));

define('zepto',['lib/zepto/zepto'], function(z) {
  return z;
});

// vim:ts=4:sts=4:sw=4:
/*!
 *
 * Copyright 2009-2012 Kris Kowal under the terms of the MIT
 * license found at http://github.com/kriskowal/q/raw/master/LICENSE
 *
 * With parts by Tyler Close
 * Copyright 2007-2009 Tyler Close under the terms of the MIT X license found
 * at http://www.opensource.org/licenses/mit-license.html
 * Forked at ref_send.js version: 2009-05-11
 *
 * With parts by Mark Miller
 * Copyright (C) 2011 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

(function (definition) {
    // Turn off strict mode for this function so we can assign to global.Q
    /* jshint strict: false */

    // This file will function properly as a <script> tag, or a module
    // using CommonJS and NodeJS or RequireJS module formats.  In
    // Common/Node/RequireJS, the module exports the Q API and when
    // executed as a simple <script>, it creates a Q global instead.

    // Montage Require
    if (typeof bootstrap === "function") {
        bootstrap("promise", definition);

    // CommonJS
    } else if (typeof exports === "object") {
        module.exports = definition();

    // RequireJS
    } else if (typeof define === "function" && define.amd) {
        define('lib/q/q',definition);

    // SES (Secure EcmaScript)
    } else if (typeof ses !== "undefined") {
        if (!ses.ok()) {
            return;
        } else {
            ses.makeQ = definition;
        }

    // <script>
    } else {
        Q = definition();
    }

})(function () {


var hasStacks = false;
try {
    throw new Error();
} catch (e) {
    hasStacks = !!e.stack;
}

// All code after this point will be filtered from stack traces reported
// by Q.
var qStartingLine = captureLine();
var qFileName;

// shims

// used for fallback in "allResolved"
var noop = function () {};

// Use the fastest possible means to execute a task in a future turn
// of the event loop.
var nextTick =(function () {
    // linked list of tasks (single, with head node)
    var head = {task: void 0, next: null};
    var tail = head;
    var flushing = false;
    var requestTick = void 0;
    var isNodeJS = false;

    function flush() {
        while (head.next) {
            head = head.next;
            var task = head.task;
            head.task = void 0;
            var domain = head.domain;

            if (domain) {
                head.domain = void 0;
                domain.enter();
            }

            try {
                task();

            } catch (e) {
                if (isNodeJS) {
                    // In node, uncaught exceptions are considered fatal errors.
                    // Re-throw them synchronously to interrupt flushing!

                    // Ensure continuation if the uncaught exception is suppressed
                    // listening "uncaughtException" events (as domains does).
                    // Continue in next event to avoid tick recursion.
                    domain && domain.exit();
                    setTimeout(flush, 0);
                    domain && domain.enter();

                    throw e;

                } else {
                    // In browsers, uncaught exceptions are not fatal.
                    // Re-throw them asynchronously to avoid slow-downs.
                    setTimeout(function() {
                       throw e;
                    }, 0);
                }
            }

            if (domain) {
                domain.exit();
            }
        }

        flushing = false;
    }

    nextTick = function (task) {
        tail = tail.next = {
            task: task,
            domain: isNodeJS && process.domain,
            next: null
        };

        if (!flushing) {
            flushing = true;
            requestTick();
        }
    };

    if (typeof process !== "undefined" && process.nextTick) {
        // Node.js before 0.9. Note that some fake-Node environments, like the
        // Mocha test runner, introduce a `process` global without a `nextTick`.
        isNodeJS = true;

        requestTick = function () {
            process.nextTick(flush);
        };

    } else if (typeof setImmediate === "function") {
        // In IE10, Node.js 0.9+, or https://github.com/NobleJS/setImmediate
        if (typeof window !== "undefined") {
            requestTick = setImmediate.bind(window, flush);
        } else {
            requestTick = function () {
                setImmediate(flush);
            };
        }

    } else if (typeof MessageChannel !== "undefined") {
        // modern browsers
        // http://www.nonblocking.io/2011/06/windownexttick.html
        var channel = new MessageChannel();
        channel.port1.onmessage = flush;
        requestTick = function () {
            channel.port2.postMessage(0);
        };

    } else {
        // old browsers
        requestTick = function () {
            setTimeout(flush, 0);
        };
    }

    return nextTick;
})();

// Attempt to make generics safe in the face of downstream
// modifications.
// There is no situation where this is necessary.
// If you need a security guarantee, these primordials need to be
// deeply frozen anyway, and if you donâ€™t need a security guarantee,
// this is just plain paranoid.
// However, this does have the nice side-effect of reducing the size
// of the code by reducing x.call() to merely x(), eliminating many
// hard-to-minify characters.
// See Mark Millerâ€™s explanation of what this does.
// http://wiki.ecmascript.org/doku.php?id=conventions:safe_meta_programming
function uncurryThis(f) {
    var call = Function.call;
    return function () {
        return call.apply(f, arguments);
    };
}
// This is equivalent, but slower:
// uncurryThis = Function_bind.bind(Function_bind.call);
// http://jsperf.com/uncurrythis

var array_slice = uncurryThis(Array.prototype.slice);

var array_reduce = uncurryThis(
    Array.prototype.reduce || function (callback, basis) {
        var index = 0,
            length = this.length;
        // concerning the initial value, if one is not provided
        if (arguments.length === 1) {
            // seek to the first value in the array, accounting
            // for the possibility that is is a sparse array
            do {
                if (index in this) {
                    basis = this[index++];
                    break;
                }
                if (++index >= length) {
                    throw new TypeError();
                }
            } while (1);
        }
        // reduce
        for (; index < length; index++) {
            // account for the possibility that the array is sparse
            if (index in this) {
                basis = callback(basis, this[index], index);
            }
        }
        return basis;
    }
);

var array_indexOf = uncurryThis(
    Array.prototype.indexOf || function (value) {
        // not a very good shim, but good enough for our one use of it
        for (var i = 0; i < this.length; i++) {
            if (this[i] === value) {
                return i;
            }
        }
        return -1;
    }
);

var array_map = uncurryThis(
    Array.prototype.map || function (callback, thisp) {
        var self = this;
        var collect = [];
        array_reduce(self, function (undefined, value, index) {
            collect.push(callback.call(thisp, value, index, self));
        }, void 0);
        return collect;
    }
);

var object_create = Object.create || function (prototype) {
    function Type() { }
    Type.prototype = prototype;
    return new Type();
};

var object_hasOwnProperty = uncurryThis(Object.prototype.hasOwnProperty);

var object_keys = Object.keys || function (object) {
    var keys = [];
    for (var key in object) {
        if (object_hasOwnProperty(object, key)) {
            keys.push(key);
        }
    }
    return keys;
};

var object_toString = uncurryThis(Object.prototype.toString);

function isObject(value) {
    return value === Object(value);
}

// generator related shims

// FIXME: Remove this function once ES6 generators are in SpiderMonkey.
function isStopIteration(exception) {
    return (
        object_toString(exception) === "[object StopIteration]" ||
        exception instanceof QReturnValue
    );
}

// FIXME: Remove this helper and Q.return once ES6 generators are in
// SpiderMonkey.
var QReturnValue;
if (typeof ReturnValue !== "undefined") {
    QReturnValue = ReturnValue;
} else {
    QReturnValue = function (value) {
        this.value = value;
    };
}

// Until V8 3.19 / Chromium 29 is released, SpiderMonkey is the only
// engine that has a deployed base of browsers that support generators.
// However, SM's generators use the Python-inspired semantics of
// outdated ES6 drafts.  We would like to support ES6, but we'd also
// like to make it possible to use generators in deployed browsers, so
// we also support Python-style generators.  At some point we can remove
// this block.
var hasES6Generators = false;

// long stack traces

var STACK_JUMP_SEPARATOR = "From previous event:";

function makeStackTraceLong(error, promise) {
    // If possible, transform the error stack trace by removing Node and Q
    // cruft, then concatenating with the stack trace of `promise`. See #57.
    if (hasStacks &&
        promise.stack &&
        typeof error === "object" &&
        error !== null &&
        error.stack &&
        error.stack.indexOf(STACK_JUMP_SEPARATOR) === -1
    ) {
        var stacks = [];
        for (var p = promise; !!p; p = p.source) {
            if (p.stack) {
                stacks.unshift(p.stack);
            }
        }
        stacks.unshift(error.stack);

        var concatedStacks = stacks.join("\n" + STACK_JUMP_SEPARATOR + "\n");
        error.stack = filterStackString(concatedStacks);
    }
}

function filterStackString(stackString) {
    var lines = stackString.split("\n");
    var desiredLines = [];
    for (var i = 0; i < lines.length; ++i) {
        var line = lines[i];

        if (!isInternalFrame(line) && !isNodeFrame(line) && line) {
            desiredLines.push(line);
        }
    }
    return desiredLines.join("\n");
}

function isNodeFrame(stackLine) {
    return stackLine.indexOf("(module.js:") !== -1 ||
           stackLine.indexOf("(node.js:") !== -1;
}

function getFileNameAndLineNumber(stackLine) {
    // Named functions: "at functionName (filename:lineNumber:columnNumber)"
    // In IE10 function name can have spaces ("Anonymous function") O_o
    var attempt1 = /at .+ \((.+):(\d+):(?:\d+)\)$/.exec(stackLine);
    if (attempt1) {
        return [attempt1[1], Number(attempt1[2])];
    }

    // Anonymous functions: "at filename:lineNumber:columnNumber"
    var attempt2 = /at ([^ ]+):(\d+):(?:\d+)$/.exec(stackLine);
    if (attempt2) {
        return [attempt2[1], Number(attempt2[2])];
    }

    // Firefox style: "function@filename:lineNumber or @filename:lineNumber"
    var attempt3 = /.*@(.+):(\d+)$/.exec(stackLine);
    if (attempt3) {
        return [attempt3[1], Number(attempt3[2])];
    }
}

function isInternalFrame(stackLine) {
    var fileNameAndLineNumber = getFileNameAndLineNumber(stackLine);

    if (!fileNameAndLineNumber) {
        return false;
    }

    var fileName = fileNameAndLineNumber[0];
    var lineNumber = fileNameAndLineNumber[1];

    return fileName === qFileName &&
        lineNumber >= qStartingLine &&
        lineNumber <= qEndingLine;
}

// discover own file name and line number range for filtering stack
// traces
function captureLine() {
    if (!hasStacks) {
        return;
    }

    try {
        throw new Error();
    } catch (e) {
        var lines = e.stack.split("\n");
        var firstLine = lines[0].indexOf("@") > 0 ? lines[1] : lines[2];
        var fileNameAndLineNumber = getFileNameAndLineNumber(firstLine);
        if (!fileNameAndLineNumber) {
            return;
        }

        qFileName = fileNameAndLineNumber[0];
        return fileNameAndLineNumber[1];
    }
}

function deprecate(callback, name, alternative) {
    return function () {
        if (typeof console !== "undefined" &&
            typeof console.warn === "function") {
            console.warn(name + " is deprecated, use " + alternative +
                         " instead.", new Error("").stack);
        }
        return callback.apply(callback, arguments);
    };
}

// end of shims
// beginning of real work

/**
 * Creates fulfilled promises from non-thenables,
 * Passes Q promises through,
 * Coerces other thenables to Q promises.
 */
function Q(value) {
    return resolve(value);
}

/**
 * Performs a task in a future turn of the event loop.
 * @param {Function} task
 */
Q.nextTick = nextTick;

/**
 * Controls whether or not long stack traces will be on
 */
Q.longStackSupport = false;

/**
 * Constructs a {promise, resolve, reject} object.
 *
 * `resolve` is a callback to invoke with a more resolved value for the
 * promise. To fulfill the promise, invoke `resolve` with any value that is
 * not a thenable. To reject the promise, invoke `resolve` with a rejected
 * thenable, or invoke `reject` with the reason directly. To resolve the
 * promise to another thenable, thus putting it in the same state, invoke
 * `resolve` with that other thenable.
 */
Q.defer = defer;
function defer() {
    // if "messages" is an "Array", that indicates that the promise has not yet
    // been resolved.  If it is "undefined", it has been resolved.  Each
    // element of the messages array is itself an array of complete arguments to
    // forward to the resolved promise.  We coerce the resolution value to a
    // promise using the `resolve` function because it handles both fully
    // non-thenable values and other thenables gracefully.
    var messages = [], progressListeners = [], resolvedPromise;

    var deferred = object_create(defer.prototype);
    var promise = object_create(Promise.prototype);

    promise.promiseDispatch = function (resolve, op, operands) {
        var args = array_slice(arguments);
        if (messages) {
            messages.push(args);
            if (op === "when" && operands[1]) { // progress operand
                progressListeners.push(operands[1]);
            }
        } else {
            nextTick(function () {
                resolvedPromise.promiseDispatch.apply(resolvedPromise, args);
            });
        }
    };

    // XXX deprecated
    promise.valueOf = deprecate(function () {
        if (messages) {
            return promise;
        }
        var nearerValue = nearer(resolvedPromise);
        if (isPromise(nearerValue)) {
            resolvedPromise = nearerValue; // shorten chain
        }
        return nearerValue;
    }, "valueOf", "inspect");

    promise.inspect = function () {
        if (!resolvedPromise) {
            return { state: "pending" };
        }
        return resolvedPromise.inspect();
    };

    if (Q.longStackSupport && hasStacks) {
        try {
            throw new Error();
        } catch (e) {
            // NOTE: don't try to use `Error.captureStackTrace` or transfer the
            // accessor around; that causes memory leaks as per GH-111. Just
            // reify the stack trace as a string ASAP.
            //
            // At the same time, cut off the first line; it's always just
            // "[object Promise]\n", as per the `toString`.
            promise.stack = e.stack.substring(e.stack.indexOf("\n") + 1);
        }
    }

    // NOTE: we do the checks for `resolvedPromise` in each method, instead of
    // consolidating them into `become`, since otherwise we'd create new
    // promises with the lines `become(whatever(value))`. See e.g. GH-252.

    function become(newPromise) {
        resolvedPromise = newPromise;
        promise.source = newPromise;

        array_reduce(messages, function (undefined, message) {
            nextTick(function () {
                newPromise.promiseDispatch.apply(newPromise, message);
            });
        }, void 0);

        messages = void 0;
        progressListeners = void 0;
    }

    deferred.promise = promise;
    deferred.resolve = function (value) {
        if (resolvedPromise) {
            return;
        }

        become(resolve(value));
    };

    deferred.fulfill = function (value) {
        if (resolvedPromise) {
            return;
        }

        become(fulfill(value));
    };
    deferred.reject = function (reason) {
        if (resolvedPromise) {
            return;
        }

        become(reject(reason));
    };
    deferred.notify = function (progress) {
        if (resolvedPromise) {
            return;
        }

        array_reduce(progressListeners, function (undefined, progressListener) {
            nextTick(function () {
                progressListener(progress);
            });
        }, void 0);
    };

    return deferred;
}

/**
 * Creates a Node-style callback that will resolve or reject the deferred
 * promise.
 * @returns a nodeback
 */
defer.prototype.makeNodeResolver = function () {
    var self = this;
    return function (error, value) {
        if (error) {
            self.reject(error);
        } else if (arguments.length > 2) {
            self.resolve(array_slice(arguments, 1));
        } else {
            self.resolve(value);
        }
    };
};

/**
 * @param resolver {Function} a function that returns nothing and accepts
 * the resolve, reject, and notify functions for a deferred.
 * @returns a promise that may be resolved with the given resolve and reject
 * functions, or rejected by a thrown exception in resolver
 */
Q.promise = promise;
function promise(resolver) {
    if (typeof resolver !== "function") {
        throw new TypeError("resolver must be a function.");
    }

    var deferred = defer();
    fcall(
        resolver,
        deferred.resolve,
        deferred.reject,
        deferred.notify
    ).fail(deferred.reject);
    return deferred.promise;
}

/**
 * Constructs a Promise with a promise descriptor object and optional fallback
 * function.  The descriptor contains methods like when(rejected), get(name),
 * set(name, value), post(name, args), and delete(name), which all
 * return either a value, a promise for a value, or a rejection.  The fallback
 * accepts the operation name, a resolver, and any further arguments that would
 * have been forwarded to the appropriate method above had a method been
 * provided with the proper name.  The API makes no guarantees about the nature
 * of the returned object, apart from that it is usable whereever promises are
 * bought and sold.
 */
Q.makePromise = Promise;
function Promise(descriptor, fallback, inspect) {
    if (fallback === void 0) {
        fallback = function (op) {
            return reject(new Error(
                "Promise does not support operation: " + op
            ));
        };
    }
    if (inspect === void 0) {
        inspect = function () {
            return {state: "unknown"};
        };
    }

    var promise = object_create(Promise.prototype);

    promise.promiseDispatch = function (resolve, op, args) {
        var result;
        try {
            if (descriptor[op]) {
                result = descriptor[op].apply(promise, args);
            } else {
                result = fallback.call(promise, op, args);
            }
        } catch (exception) {
            result = reject(exception);
        }
        if (resolve) {
            resolve(result);
        }
    };

    promise.inspect = inspect;

    // XXX deprecated `valueOf` and `exception` support
    if (inspect) {
        var inspected = inspect();
        if (inspected.state === "rejected") {
            promise.exception = inspected.reason;
        }

        promise.valueOf = deprecate(function () {
            var inspected = inspect();
            if (inspected.state === "pending" ||
                inspected.state === "rejected") {
                return promise;
            }
            return inspected.value;
        });
    }

    return promise;
}

Promise.prototype.then = function (fulfilled, rejected, progressed) {
    var self = this;
    var deferred = defer();
    var done = false;   // ensure the untrusted promise makes at most a
                        // single call to one of the callbacks

    function _fulfilled(value) {
        try {
            return typeof fulfilled === "function" ? fulfilled(value) : value;
        } catch (exception) {
            return reject(exception);
        }
    }

    function _rejected(exception) {
        if (typeof rejected === "function") {
            makeStackTraceLong(exception, self);
            try {
                return rejected(exception);
            } catch (newException) {
                return reject(newException);
            }
        }
        return reject(exception);
    }

    function _progressed(value) {
        return typeof progressed === "function" ? progressed(value) : value;
    }

    nextTick(function () {
        self.promiseDispatch(function (value) {
            if (done) {
                return;
            }
            done = true;

            deferred.resolve(_fulfilled(value));
        }, "when", [function (exception) {
            if (done) {
                return;
            }
            done = true;

            deferred.resolve(_rejected(exception));
        }]);
    });

    // Progress propagator need to be attached in the current tick.
    self.promiseDispatch(void 0, "when", [void 0, function (value) {
        var newValue;
        var threw = false;
        try {
            newValue = _progressed(value);
        } catch (e) {
            threw = true;
            if (Q.onerror) {
                Q.onerror(e);
            } else {
                throw e;
            }
        }

        if (!threw) {
            deferred.notify(newValue);
        }
    }]);

    return deferred.promise;
};

Promise.prototype.thenResolve = function (value) {
    return when(this, function () { return value; });
};

Promise.prototype.thenReject = function (reason) {
    return when(this, function () { throw reason; });
};

// Chainable methods
array_reduce(
    [
        "isFulfilled", "isRejected", "isPending",
        "dispatch",
        "when", "spread",
        "get", "set", "del", "delete",
        "post", "send", "mapply", "invoke", "mcall",
        "keys",
        "fapply", "fcall", "fbind",
        "all", "allResolved",
        "timeout", "delay",
        "catch", "finally", "fail", "fin", "progress", "done",
        "nfcall", "nfapply", "nfbind", "denodeify", "nbind",
        "npost", "nsend", "nmapply", "ninvoke", "nmcall",
        "nodeify"
    ],
    function (undefined, name) {
        Promise.prototype[name] = function () {
            return Q[name].apply(
                Q,
                [this].concat(array_slice(arguments))
            );
        };
    },
    void 0
);

Promise.prototype.toSource = function () {
    return this.toString();
};

Promise.prototype.toString = function () {
    return "[object Promise]";
};

/**
 * If an object is not a promise, it is as "near" as possible.
 * If a promise is rejected, it is as "near" as possible too.
 * If itâ€™s a fulfilled promise, the fulfillment value is nearer.
 * If itâ€™s a deferred promise and the deferred has been resolved, the
 * resolution is "nearer".
 * @param object
 * @returns most resolved (nearest) form of the object
 */

// XXX should we re-do this?
Q.nearer = nearer;
function nearer(value) {
    if (isPromise(value)) {
        var inspected = value.inspect();
        if (inspected.state === "fulfilled") {
            return inspected.value;
        }
    }
    return value;
}

/**
 * @returns whether the given object is a promise.
 * Otherwise it is a fulfilled value.
 */
Q.isPromise = isPromise;
function isPromise(object) {
    return isObject(object) &&
        typeof object.promiseDispatch === "function" &&
        typeof object.inspect === "function";
}

Q.isPromiseAlike = isPromiseAlike;
function isPromiseAlike(object) {
    return isObject(object) && typeof object.then === "function";
}

/**
 * @returns whether the given object is a pending promise, meaning not
 * fulfilled or rejected.
 */
Q.isPending = isPending;
function isPending(object) {
    return isPromise(object) && object.inspect().state === "pending";
}

/**
 * @returns whether the given object is a value or fulfilled
 * promise.
 */
Q.isFulfilled = isFulfilled;
function isFulfilled(object) {
    return !isPromise(object) || object.inspect().state === "fulfilled";
}

/**
 * @returns whether the given object is a rejected promise.
 */
Q.isRejected = isRejected;
function isRejected(object) {
    return isPromise(object) && object.inspect().state === "rejected";
}

//// BEGIN UNHANDLED REJECTION TRACKING

// This promise library consumes exceptions thrown in handlers so they can be
// handled by a subsequent promise.  The exceptions get added to this array when
// they are created, and removed when they are handled.  Note that in ES6 or
// shimmed environments, this would naturally be a `Set`.
var unhandledReasons = [];
var unhandledRejections = [];
var unhandledReasonsDisplayed = false;
var trackUnhandledRejections = true;
function displayUnhandledReasons() {
    if (
        !unhandledReasonsDisplayed &&
        typeof window !== "undefined" &&
        !window.Touch &&
        window.console
    ) {
        console.warn("[Q] Unhandled rejection reasons (should be empty):",
                     unhandledReasons);
    }

    unhandledReasonsDisplayed = true;
}

function logUnhandledReasons() {
    for (var i = 0; i < unhandledReasons.length; i++) {
        var reason = unhandledReasons[i];
        if (reason && typeof reason.stack !== "undefined") {
            console.warn("Unhandled rejection reason:", reason.stack);
        } else {
            console.warn("Unhandled rejection reason (no stack):", reason);
        }
    }
}

function resetUnhandledRejections() {
    unhandledReasons.length = 0;
    unhandledRejections.length = 0;
    unhandledReasonsDisplayed = false;

    if (!trackUnhandledRejections) {
        trackUnhandledRejections = true;

        // Show unhandled rejection reasons if Node exits without handling an
        // outstanding rejection.  (Note that Browserify presently produces a
        // `process` global without the `EventEmitter` `on` method.)
        if (typeof process !== "undefined" && process.on) {
            process.on("exit", logUnhandledReasons);
        }
    }
}

function trackRejection(promise, reason) {
    if (!trackUnhandledRejections) {
        return;
    }

    unhandledRejections.push(promise);
    unhandledReasons.push(reason);
    displayUnhandledReasons();
}

function untrackRejection(promise) {
    if (!trackUnhandledRejections) {
        return;
    }

    var at = array_indexOf(unhandledRejections, promise);
    if (at !== -1) {
        unhandledRejections.splice(at, 1);
        unhandledReasons.splice(at, 1);
    }
}

Q.resetUnhandledRejections = resetUnhandledRejections;

Q.getUnhandledReasons = function () {
    // Make a copy so that consumers can't interfere with our internal state.
    return unhandledReasons.slice();
};

Q.stopUnhandledRejectionTracking = function () {
    resetUnhandledRejections();
    if (typeof process !== "undefined" && process.on) {
        process.removeListener("exit", logUnhandledReasons);
    }
    trackUnhandledRejections = false;
};

resetUnhandledRejections();

//// END UNHANDLED REJECTION TRACKING

/**
 * Constructs a rejected promise.
 * @param reason value describing the failure
 */
Q.reject = reject;
function reject(reason) {
    var rejection = Promise({
        "when": function (rejected) {
            // note that the error has been handled
            if (rejected) {
                untrackRejection(this);
            }
            return rejected ? rejected(reason) : this;
        }
    }, function fallback() {
        return this;
    }, function inspect() {
        return { state: "rejected", reason: reason };
    });

    // Note that the reason has not been handled.
    trackRejection(rejection, reason);

    return rejection;
}

/**
 * Constructs a fulfilled promise for an immediate reference.
 * @param value immediate reference
 */
Q.fulfill = fulfill;
function fulfill(value) {
    return Promise({
        "when": function () {
            return value;
        },
        "get": function (name) {
            return value[name];
        },
        "set": function (name, rhs) {
            value[name] = rhs;
        },
        "delete": function (name) {
            delete value[name];
        },
        "post": function (name, args) {
            // Mark Miller proposes that post with no name should apply a
            // promised function.
            if (name === null || name === void 0) {
                return value.apply(void 0, args);
            } else {
                return value[name].apply(value, args);
            }
        },
        "apply": function (thisP, args) {
            return value.apply(thisP, args);
        },
        "keys": function () {
            return object_keys(value);
        }
    }, void 0, function inspect() {
        return { state: "fulfilled", value: value };
    });
}

/**
 * Constructs a promise for an immediate reference, passes promises through, or
 * coerces promises from different systems.
 * @param value immediate reference or promise
 */
Q.resolve = resolve;
function resolve(value) {
    // If the object is already a Promise, return it directly.  This enables
    // the resolve function to both be used to created references from objects,
    // but to tolerably coerce non-promises to promises.
    if (isPromise(value)) {
        return value;
    }

    // assimilate thenables
    if (isPromiseAlike(value)) {
        return coerce(value);
    } else {
        return fulfill(value);
    }
}

/**
 * Converts thenables to Q promises.
 * @param promise thenable promise
 * @returns a Q promise
 */
function coerce(promise) {
    var deferred = defer();
    nextTick(function () {
        try {
            promise.then(deferred.resolve, deferred.reject, deferred.notify);
        } catch (exception) {
            deferred.reject(exception);
        }
    });
    return deferred.promise;
}

/**
 * Annotates an object such that it will never be
 * transferred away from this process over any promise
 * communication channel.
 * @param object
 * @returns promise a wrapping of that object that
 * additionally responds to the "isDef" message
 * without a rejection.
 */
Q.master = master;
function master(object) {
    return Promise({
        "isDef": function () {}
    }, function fallback(op, args) {
        return dispatch(object, op, args);
    }, function () {
        return resolve(object).inspect();
    });
}

/**
 * Registers an observer on a promise.
 *
 * Guarantees:
 *
 * 1. that fulfilled and rejected will be called only once.
 * 2. that either the fulfilled callback or the rejected callback will be
 *    called, but not both.
 * 3. that fulfilled and rejected will not be called in this turn.
 *
 * @param value      promise or immediate reference to observe
 * @param fulfilled  function to be called with the fulfilled value
 * @param rejected   function to be called with the rejection exception
 * @param progressed function to be called on any progress notifications
 * @return promise for the return value from the invoked callback
 */
Q.when = when;
function when(value, fulfilled, rejected, progressed) {
    return Q(value).then(fulfilled, rejected, progressed);
}

/**
 * Spreads the values of a promised array of arguments into the
 * fulfillment callback.
 * @param fulfilled callback that receives variadic arguments from the
 * promised array
 * @param rejected callback that receives the exception if the promise
 * is rejected.
 * @returns a promise for the return value or thrown exception of
 * either callback.
 */
Q.spread = spread;
function spread(promise, fulfilled, rejected) {
    return when(promise, function (valuesOrPromises) {
        return all(valuesOrPromises).then(function (values) {
            return fulfilled.apply(void 0, values);
        }, rejected);
    }, rejected);
}

/**
 * The async function is a decorator for generator functions, turning
 * them into asynchronous generators.  Although generators are only part
 * of the newest ECMAScript 6 drafts, this code does not cause syntax
 * errors in older engines.  This code should continue to work and will
 * in fact improve over time as the language improves.
 *
 * ES6 generators are currently part of V8 version 3.19 with the
 * --harmony-generators runtime flag enabled.  SpiderMonkey has had them
 * for longer, but under an older Python-inspired form.  This function
 * works on both kinds of generators.
 *
 * Decorates a generator function such that:
 *  - it may yield promises
 *  - execution will continue when that promise is fulfilled
 *  - the value of the yield expression will be the fulfilled value
 *  - it returns a promise for the return value (when the generator
 *    stops iterating)
 *  - the decorated function returns a promise for the return value
 *    of the generator or the first rejected promise among those
 *    yielded.
 *  - if an error is thrown in the generator, it propagates through
 *    every following yield until it is caught, or until it escapes
 *    the generator function altogether, and is translated into a
 *    rejection for the promise returned by the decorated generator.
 */
Q.async = async;
function async(makeGenerator) {
    return function () {
        // when verb is "send", arg is a value
        // when verb is "throw", arg is an exception
        function continuer(verb, arg) {
            var result;
            if (hasES6Generators) {
                try {
                    result = generator[verb](arg);
                } catch (exception) {
                    return reject(exception);
                }
                if (result.done) {
                    return result.value;
                } else {
                    return when(result.value, callback, errback);
                }
            } else {
                // FIXME: Remove this case when SM does ES6 generators.
                try {
                    result = generator[verb](arg);
                } catch (exception) {
                    if (isStopIteration(exception)) {
                        return exception.value;
                    } else {
                        return reject(exception);
                    }
                }
                return when(result, callback, errback);
            }
        }
        var generator = makeGenerator.apply(this, arguments);
        var callback = continuer.bind(continuer, "send");
        var errback = continuer.bind(continuer, "throw");
        return callback();
    };
}

/**
 * The spawn function is a small wrapper around async that immediately
 * calls the generator and also ends the promise chain, so that any
 * unhandled errors are thrown instead of forwarded to the error
 * handler. This is useful because it's extremely common to run
 * generators at the top-level to work with libraries.
 */
Q.spawn = spawn;
function spawn(makeGenerator) {
    Q.done(Q.async(makeGenerator)());
}

// FIXME: Remove this interface once ES6 generators are in SpiderMonkey.
/**
 * Throws a ReturnValue exception to stop an asynchronous generator.
 *
 * This interface is a stop-gap measure to support generator return
 * values in older Firefox/SpiderMonkey.  In browsers that support ES6
 * generators like Chromium 29, just use "return" in your generator
 * functions.
 *
 * @param value the return value for the surrounding generator
 * @throws ReturnValue exception with the value.
 * @example
 * // ES6 style
 * Q.async(function* () {
 *      var foo = yield getFooPromise();
 *      var bar = yield getBarPromise();
 *      return foo + bar;
 * })
 * // Older SpiderMonkey style
 * Q.async(function () {
 *      var foo = yield getFooPromise();
 *      var bar = yield getBarPromise();
 *      Q.return(foo + bar);
 * })
 */
Q["return"] = _return;
function _return(value) {
    throw new QReturnValue(value);
}

/**
 * The promised function decorator ensures that any promise arguments
 * are settled and passed as values (`this` is also settled and passed
 * as a value).  It will also ensure that the result of a function is
 * always a promise.
 *
 * @example
 * var add = Q.promised(function (a, b) {
 *     return a + b;
 * });
 * add(Q.resolve(a), Q.resolve(B));
 *
 * @param {function} callback The function to decorate
 * @returns {function} a function that has been decorated.
 */
Q.promised = promised;
function promised(callback) {
    return function () {
        return spread([this, all(arguments)], function (self, args) {
            return callback.apply(self, args);
        });
    };
}

/**
 * sends a message to a value in a future turn
 * @param object* the recipient
 * @param op the name of the message operation, e.g., "when",
 * @param args further arguments to be forwarded to the operation
 * @returns result {Promise} a promise for the result of the operation
 */
Q.dispatch = dispatch;
function dispatch(object, op, args) {
    var deferred = defer();
    nextTick(function () {
        resolve(object).promiseDispatch(deferred.resolve, op, args);
    });
    return deferred.promise;
}

/**
 * Constructs a promise method that can be used to safely observe resolution of
 * a promise for an arbitrarily named method like "propfind" in a future turn.
 *
 * "dispatcher" constructs methods like "get(promise, name)" and "set(promise)".
 */
Q.dispatcher = dispatcher;
function dispatcher(op) {
    return function (object) {
        var args = array_slice(arguments, 1);
        return dispatch(object, op, args);
    };
}

/**
 * Gets the value of a property in a future turn.
 * @param object    promise or immediate reference for target object
 * @param name      name of property to get
 * @return promise for the property value
 */
Q.get = dispatcher("get");

/**
 * Sets the value of a property in a future turn.
 * @param object    promise or immediate reference for object object
 * @param name      name of property to set
 * @param value     new value of property
 * @return promise for the return value
 */
Q.set = dispatcher("set");

/**
 * Deletes a property in a future turn.
 * @param object    promise or immediate reference for target object
 * @param name      name of property to delete
 * @return promise for the return value
 */
Q["delete"] = // XXX experimental
Q.del = dispatcher("delete");

/**
 * Invokes a method in a future turn.
 * @param object    promise or immediate reference for target object
 * @param name      name of method to invoke
 * @param value     a value to post, typically an array of
 *                  invocation arguments for promises that
 *                  are ultimately backed with `resolve` values,
 *                  as opposed to those backed with URLs
 *                  wherein the posted value can be any
 *                  JSON serializable object.
 * @return promise for the return value
 */
// bound locally because it is used by other methods
var post = Q.post = dispatcher("post");
Q.mapply = post; // experimental

/**
 * Invokes a method in a future turn.
 * @param object    promise or immediate reference for target object
 * @param name      name of method to invoke
 * @param ...args   array of invocation arguments
 * @return promise for the return value
 */
Q.send = send;
Q.invoke = send; // synonyms
Q.mcall = send; // experimental
function send(value, name) {
    var args = array_slice(arguments, 2);
    return post(value, name, args);
}

/**
 * Applies the promised function in a future turn.
 * @param object    promise or immediate reference for target function
 * @param args      array of application arguments
 */
Q.fapply = fapply;
function fapply(value, args) {
    return dispatch(value, "apply", [void 0, args]);
}

/**
 * Calls the promised function in a future turn.
 * @param object    promise or immediate reference for target function
 * @param ...args   array of application arguments
 */
Q["try"] = fcall; // XXX experimental
Q.fcall = fcall;
function fcall(value) {
    var args = array_slice(arguments, 1);
    return fapply(value, args);
}

/**
 * Binds the promised function, transforming return values into a fulfilled
 * promise and thrown errors into a rejected one.
 * @param object    promise or immediate reference for target function
 * @param ...args   array of application arguments
 */
Q.fbind = fbind;
function fbind(value) {
    var args = array_slice(arguments, 1);
    return function fbound() {
        var allArgs = args.concat(array_slice(arguments));
        return dispatch(value, "apply", [this, allArgs]);
    };
}

/**
 * Requests the names of the owned properties of a promised
 * object in a future turn.
 * @param object    promise or immediate reference for target object
 * @return promise for the keys of the eventually settled object
 */
Q.keys = dispatcher("keys");

/**
 * Turns an array of promises into a promise for an array.  If any of
 * the promises gets rejected, the whole array is rejected immediately.
 * @param {Array*} an array (or promise for an array) of values (or
 * promises for values)
 * @returns a promise for an array of the corresponding values
 */
// By Mark Miller
// http://wiki.ecmascript.org/doku.php?id=strawman:concurrency&rev=1308776521#allfulfilled
Q.all = all;
function all(promises) {
    return when(promises, function (promises) {
        var countDown = 0;
        var deferred = defer();
        array_reduce(promises, function (undefined, promise, index) {
            var snapshot;
            if (
                isPromise(promise) &&
                (snapshot = promise.inspect()).state === "fulfilled"
            ) {
                promises[index] = snapshot.value;
            } else {
                ++countDown;
                when(promise, function (value) {
                    promises[index] = value;
                    if (--countDown === 0) {
                        deferred.resolve(promises);
                    }
                }, deferred.reject);
            }
        }, void 0);
        if (countDown === 0) {
            deferred.resolve(promises);
        }
        return deferred.promise;
    });
}

/**
 * Waits for all promises to be settled, either fulfilled or
 * rejected.  This is distinct from `all` since that would stop
 * waiting at the first rejection.  The promise returned by
 * `allResolved` will never be rejected.
 * @param promises a promise for an array (or an array) of promises
 * (or values)
 * @return a promise for an array of promises
 */
Q.allResolved = deprecate(allResolved, "allResolved", "allSettled");
function allResolved(promises) {
    return when(promises, function (promises) {
        promises = array_map(promises, resolve);
        return when(all(array_map(promises, function (promise) {
            return when(promise, noop, noop);
        })), function () {
            return promises;
        });
    });
}

Q.allSettled = allSettled;
function allSettled(values) {
    return when(values, function (values) {
        return all(array_map(values, function (value, i) {
            return when(
                value,
                function (fulfillmentValue) {
                    values[i] = { state: "fulfilled", value: fulfillmentValue };
                    return values[i];
                },
                function (reason) {
                    values[i] = { state: "rejected", reason: reason };
                    return values[i];
                }
            );
        })).thenResolve(values);
    });
}

/**
 * Captures the failure of a promise, giving an oportunity to recover
 * with a callback.  If the given promise is fulfilled, the returned
 * promise is fulfilled.
 * @param {Any*} promise for something
 * @param {Function} callback to fulfill the returned promise if the
 * given promise is rejected
 * @returns a promise for the return value of the callback
 */
Q["catch"] = // XXX experimental
Q.fail = fail;
function fail(promise, rejected) {
    return when(promise, void 0, rejected);
}

/**
 * Attaches a listener that can respond to progress notifications from a
 * promise's originating deferred. This listener receives the exact arguments
 * passed to ``deferred.notify``.
 * @param {Any*} promise for something
 * @param {Function} callback to receive any progress notifications
 * @returns the given promise, unchanged
 */
Q.progress = progress;
function progress(promise, progressed) {
    return when(promise, void 0, void 0, progressed);
}

/**
 * Provides an opportunity to observe the settling of a promise,
 * regardless of whether the promise is fulfilled or rejected.  Forwards
 * the resolution to the returned promise when the callback is done.
 * The callback can return a promise to defer completion.
 * @param {Any*} promise
 * @param {Function} callback to observe the resolution of the given
 * promise, takes no arguments.
 * @returns a promise for the resolution of the given promise when
 * ``fin`` is done.
 */
Q["finally"] = // XXX experimental
Q.fin = fin;
function fin(promise, callback) {
    return when(promise, function (value) {
        return when(callback(), function () {
            return value;
        });
    }, function (exception) {
        return when(callback(), function () {
            return reject(exception);
        });
    });
}

/**
 * Terminates a chain of promises, forcing rejections to be
 * thrown as exceptions.
 * @param {Any*} promise at the end of a chain of promises
 * @returns nothing
 */
Q.done = done;
function done(promise, fulfilled, rejected, progress) {
    var onUnhandledError = function (error) {
        // forward to a future turn so that ``when``
        // does not catch it and turn it into a rejection.
        nextTick(function () {
            makeStackTraceLong(error, promise);

            if (Q.onerror) {
                Q.onerror(error);
            } else {
                throw error;
            }
        });
    };

    // Avoid unnecessary `nextTick`ing via an unnecessary `when`.
    var promiseToHandle = fulfilled || rejected || progress ?
        when(promise, fulfilled, rejected, progress) :
        promise;

    if (typeof process === "object" && process && process.domain) {
        onUnhandledError = process.domain.bind(onUnhandledError);
    }
    fail(promiseToHandle, onUnhandledError);
}

/**
 * Causes a promise to be rejected if it does not get fulfilled before
 * some milliseconds time out.
 * @param {Any*} promise
 * @param {Number} milliseconds timeout
 * @param {String} custom error message (optional)
 * @returns a promise for the resolution of the given promise if it is
 * fulfilled before the timeout, otherwise rejected.
 */
Q.timeout = timeout;
function timeout(promise, ms, msg) {
    var deferred = defer();
    var timeoutId = setTimeout(function () {
        deferred.reject(new Error(msg || "Timed out after " + ms + " ms"));
    }, ms);

    when(promise, function (value) {
        clearTimeout(timeoutId);
        deferred.resolve(value);
    }, function (exception) {
        clearTimeout(timeoutId);
        deferred.reject(exception);
    }, deferred.notify);

    return deferred.promise;
}

/**
 * Returns a promise for the given value (or promised value) after some
 * milliseconds.
 * @param {Any*} promise
 * @param {Number} milliseconds
 * @returns a promise for the resolution of the given promise after some
 * time has elapsed.
 */
Q.delay = delay;
function delay(promise, timeout) {
    if (timeout === void 0) {
        timeout = promise;
        promise = void 0;
    }

    var deferred = defer();

    when(promise, undefined, undefined, deferred.notify);
    setTimeout(function () {
        deferred.resolve(promise);
    }, timeout);

    return deferred.promise;
}

/**
 * Passes a continuation to a Node function, which is called with the given
 * arguments provided as an array, and returns a promise.
 *
 *      Q.nfapply(FS.readFile, [__filename])
 *      .then(function (content) {
 *      })
 *
 */
Q.nfapply = nfapply;
function nfapply(callback, args) {
    var nodeArgs = array_slice(args);
    var deferred = defer();
    nodeArgs.push(deferred.makeNodeResolver());

    fapply(callback, nodeArgs).fail(deferred.reject);
    return deferred.promise;
}

/**
 * Passes a continuation to a Node function, which is called with the given
 * arguments provided individually, and returns a promise.
 *
 *      Q.nfcall(FS.readFile, __filename)
 *      .then(function (content) {
 *      })
 *
 */
Q.nfcall = nfcall;
function nfcall(callback/*, ...args */) {
    var nodeArgs = array_slice(arguments, 1);
    var deferred = defer();
    nodeArgs.push(deferred.makeNodeResolver());

    fapply(callback, nodeArgs).fail(deferred.reject);
    return deferred.promise;
}

/**
 * Wraps a NodeJS continuation passing function and returns an equivalent
 * version that returns a promise.
 *
 *      Q.nfbind(FS.readFile, __filename)("utf-8")
 *      .then(console.log)
 *      .done()
 *
 */
Q.nfbind = nfbind;
Q.denodeify = Q.nfbind; // synonyms
function nfbind(callback/*, ...args */) {
    var baseArgs = array_slice(arguments, 1);
    return function () {
        var nodeArgs = baseArgs.concat(array_slice(arguments));
        var deferred = defer();
        nodeArgs.push(deferred.makeNodeResolver());

        fapply(callback, nodeArgs).fail(deferred.reject);
        return deferred.promise;
    };
}

Q.nbind = nbind;
function nbind(callback, thisArg /*, ... args*/) {
    var baseArgs = array_slice(arguments, 2);
    return function () {
        var nodeArgs = baseArgs.concat(array_slice(arguments));
        var deferred = defer();
        nodeArgs.push(deferred.makeNodeResolver());

        function bound() {
            return callback.apply(thisArg, arguments);
        }

        fapply(bound, nodeArgs).fail(deferred.reject);
        return deferred.promise;
    };
}

/**
 * Calls a method of a Node-style object that accepts a Node-style
 * callback with a given array of arguments, plus a provided callback.
 * @param object an object that has the named method
 * @param {String} name name of the method of object
 * @param {Array} args arguments to pass to the method; the callback
 * will be provided by Q and appended to these arguments.
 * @returns a promise for the value or error
 */
Q.npost = npost;
Q.nmapply = npost; // synonyms
function npost(object, name, args) {
    var nodeArgs = array_slice(args || []);
    var deferred = defer();
    nodeArgs.push(deferred.makeNodeResolver());

    post(object, name, nodeArgs).fail(deferred.reject);
    return deferred.promise;
}

/**
 * Calls a method of a Node-style object that accepts a Node-style
 * callback, forwarding the given variadic arguments, plus a provided
 * callback argument.
 * @param object an object that has the named method
 * @param {String} name name of the method of object
 * @param ...args arguments to pass to the method; the callback will
 * be provided by Q and appended to these arguments.
 * @returns a promise for the value or error
 */
Q.nsend = nsend;
Q.ninvoke = Q.nsend; // synonyms
Q.nmcall = Q.nsend; // synonyms
function nsend(object, name /*, ...args*/) {
    var nodeArgs = array_slice(arguments, 2);
    var deferred = defer();
    nodeArgs.push(deferred.makeNodeResolver());
    post(object, name, nodeArgs).fail(deferred.reject);
    return deferred.promise;
}

Q.nodeify = nodeify;
function nodeify(promise, nodeback) {
    if (nodeback) {
        promise.then(function (value) {
            nextTick(function () {
                nodeback(null, value);
            });
        }, function (error) {
            nextTick(function () {
                nodeback(error);
            });
        });
    } else {
        return promise;
    }
}

// All code before this point will be filtered from stack traces.
var qEndingLine = captureLine();

return Q;

});

define('q',['lib/q/q'], function(m) {
  return m;
});

/*

  Javascript State Machine Library - https://github.com/jakesgordon/javascript-state-machine

  Copyright (c) 2012, 2013 Jake Gordon and contributors
  Released under the MIT license - https://github.com/jakesgordon/javascript-state-machine/blob/master/LICENSE

*/

(function (window) {

  var StateMachine = {

    //---------------------------------------------------------------------------

    VERSION: "2.2.0",

    //---------------------------------------------------------------------------

    Result: {
      SUCCEEDED:    1, // the event transitioned successfully from one state to another
      NOTRANSITION: 2, // the event was successfull but no state transition was necessary
      CANCELLED:    3, // the event was cancelled by the caller in a beforeEvent callback
      PENDING:      4  // the event is asynchronous and the caller is in control of when the transition occurs
    },

    Error: {
      INVALID_TRANSITION: 100, // caller tried to fire an event that was innapropriate in the current state
      PENDING_TRANSITION: 200, // caller tried to fire an event while an async transition was still pending
      INVALID_CALLBACK:   300 // caller provided callback function threw an exception
    },

    WILDCARD: '*',
    ASYNC: 'async',

    //---------------------------------------------------------------------------

    create: function(cfg, target) {

      var initial   = (typeof cfg.initial == 'string') ? { state: cfg.initial } : cfg.initial; // allow for a simple string, or an object with { state: 'foo', event: 'setup', defer: true|false }
      var terminal  = cfg.terminal || cfg['final'];
      var fsm       = target || cfg.target  || {};
      var events    = cfg.events || [];
      var callbacks = cfg.callbacks || {};
      var map       = {};

      var add = function(e) {
        var from = (e.from instanceof Array) ? e.from : (e.from ? [e.from] : [StateMachine.WILDCARD]); // allow 'wildcard' transition if 'from' is not specified
        map[e.name] = map[e.name] || {};
        for (var n = 0 ; n < from.length ; n++)
          map[e.name][from[n]] = e.to || from[n]; // allow no-op transition if 'to' is not specified
      };

      if (initial) {
        initial.event = initial.event || 'startup';
        add({ name: initial.event, from: 'none', to: initial.state });
      }

      for(var n = 0 ; n < events.length ; n++)
        add(events[n]);

      for(var name in map) {
        if (map.hasOwnProperty(name))
          fsm[name] = StateMachine.buildEvent(name, map[name]);
      }

      for(var name in callbacks) {
        if (callbacks.hasOwnProperty(name))
          fsm[name] = callbacks[name]
      }

      fsm.current = 'none';
      fsm.is      = function(state) { return (state instanceof Array) ? (state.indexOf(this.current) >= 0) : (this.current === state); };
      fsm.can     = function(event) { return !this.transition && (map[event].hasOwnProperty(this.current) || map[event].hasOwnProperty(StateMachine.WILDCARD)); }
      fsm.cannot  = function(event) { return !this.can(event); };
      fsm.error   = cfg.error || function(name, from, to, args, error, msg, e) { throw e || msg; }; // default behavior when something unexpected happens is to throw an exception, but caller can override this behavior if desired (see github issue #3 and #17)

      fsm.isFinished = function() { return this.is(terminal); };

      if (initial && !initial.defer)
        fsm[initial.event]();

      return fsm;

    },

    //===========================================================================

    doCallback: function(fsm, func, name, from, to, args) {
      if (func) {
        try {
          return func.apply(fsm, [name, from, to].concat(args));
        }
        catch(e) {
          return fsm.error(name, from, to, args, StateMachine.Error.INVALID_CALLBACK, "an exception occurred in a caller-provided callback function", e);
        }
      }
    },

    beforeAnyEvent:  function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onbeforeevent'],                       name, from, to, args); },
    afterAnyEvent:   function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onafterevent'] || fsm['onevent'],      name, from, to, args); },
    leaveAnyState:   function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onleavestate'],                        name, from, to, args); },
    enterAnyState:   function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onenterstate'] || fsm['onstate'],      name, from, to, args); },
    changeState:     function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onchangestate'],                       name, from, to, args); },

    beforeThisEvent: function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onbefore' + name],                     name, from, to, args); },
    afterThisEvent:  function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onafter'  + name] || fsm['on' + name], name, from, to, args); },
    leaveThisState:  function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onleave'  + from],                     name, from, to, args); },
    enterThisState:  function(fsm, name, from, to, args) { return StateMachine.doCallback(fsm, fsm['onenter'  + to]   || fsm['on' + to],   name, from, to, args); },

    beforeEvent: function(fsm, name, from, to, args) {
      if ((false === StateMachine.beforeThisEvent(fsm, name, from, to, args)) ||
          (false === StateMachine.beforeAnyEvent( fsm, name, from, to, args)))
        return false;
    },

    afterEvent: function(fsm, name, from, to, args) {
      StateMachine.afterThisEvent(fsm, name, from, to, args);
      StateMachine.afterAnyEvent( fsm, name, from, to, args);
    },

    leaveState: function(fsm, name, from, to, args) {
      var specific = StateMachine.leaveThisState(fsm, name, from, to, args),
          general  = StateMachine.leaveAnyState( fsm, name, from, to, args);
      if ((false === specific) || (false === general))
        return false;
      else if ((StateMachine.ASYNC === specific) || (StateMachine.ASYNC === general))
        return StateMachine.ASYNC;
    },

    enterState: function(fsm, name, from, to, args) {
      StateMachine.enterThisState(fsm, name, from, to, args);
      StateMachine.enterAnyState( fsm, name, from, to, args);
    },

    //===========================================================================

    buildEvent: function(name, map) {
      return function() {

        var from  = this.current;
        var to    = map[from] || map[StateMachine.WILDCARD] || from;
        var args  = Array.prototype.slice.call(arguments); // turn arguments into pure array

        if (this.transition)
          return this.error(name, from, to, args, StateMachine.Error.PENDING_TRANSITION, "event " + name + " inappropriate because previous transition did not complete");

        if (this.cannot(name))
          return this.error(name, from, to, args, StateMachine.Error.INVALID_TRANSITION, "event " + name + " inappropriate in current state " + this.current);

        if (false === StateMachine.beforeEvent(this, name, from, to, args))
          return StateMachine.Result.CANCELLED;

        if (from === to) {
          StateMachine.afterEvent(this, name, from, to, args);
          return StateMachine.Result.NOTRANSITION;
        }

        // prepare a transition method for use EITHER lower down, or by caller if they want an async transition (indicated by an ASYNC return value from leaveState)
        var fsm = this;
        this.transition = function() {
          fsm.transition = null; // this method should only ever be called once
          fsm.current = to;
          StateMachine.enterState( fsm, name, from, to, args);
          StateMachine.changeState(fsm, name, from, to, args);
          StateMachine.afterEvent( fsm, name, from, to, args);
          return StateMachine.Result.SUCCEEDED;
        };
        this.transition.cancel = function() { // provide a way for caller to cancel async transition if desired (issue #22)
          fsm.transition = null;
          StateMachine.afterEvent(fsm, name, from, to, args);
        }

        var leave = StateMachine.leaveState(this, name, from, to, args);
        if (false === leave) {
          this.transition = null;
          return StateMachine.Result.CANCELLED;
        }
        else if (StateMachine.ASYNC === leave) {
          return StateMachine.Result.PENDING;
        }
        else {
          if (this.transition) // need to check in case user manually called transition() but forgot to return StateMachine.ASYNC
            return this.transition();
        }

      };
    }

  }; // StateMachine

  //===========================================================================

  if ("function" === typeof define) {
    define('lib/javascript-state-machine/state-machine',['require'],function(require) { return StateMachine; });
  }
  else {
    window.StateMachine = StateMachine;
  }

}(this));


define('state-machine',['lib/javascript-state-machine/state-machine'], function(m) {
  return m;
});

define('alias',['zepto'], function($) {
  return {
    w: window,
    h: $('html'),
    b: $('body')
  };
});

define('time',[],function() {
  var defer, delay, wait;

  defer = function(f) {
    return setTimeout(f, 1);
  };
  delay = function(f, t) {
    return setTimeout(f, t);
  };
  wait = function(t, f) {
    return setTimeout(f, t);
  };
  return {
    defer: defer,
    delay: delay,
    wait: wait
  };
});

define('globals',['alias', 'time'], function() {
  var arg, obj, _i, _key, _len;

  obj = {};
  for (_i = 0, _len = arguments.length; _i < _len; _i++) {
    arg = arguments[_i];
    for (_key in arg) {
      obj[_key] = window[_key] = arg[_key];
    }
  }
  return obj;
});

define('array',[],function() {
  Array.prototype.include = function(value) {
    return this.indexOf(value) !== -1;
  };
  Array.prototype.empty = function() {
    return this.length === 0;
  };
  Array.prototype.first = function() {
    return this[0];
  };
  Array.prototype.last = function() {
    return this[this.length - 1];
  };
  Array.prototype.find = function(iterator, context) {
    var index, result, _i, _ref;

    for (index = _i = 0, _ref = this.length; 0 <= _ref ? _i < _ref : _i > _ref; index = 0 <= _ref ? ++_i : --_i) {
      if (iterator.call(context, this[index], index)) {
        result = this[index];
        break;
      }
    }
    return result;
  };
  Array.prototype.findAll = function(iterator, context) {
    return this.filter(iterator, context);
  };
  Array.prototype.uniq = function() {
    var results, value, _i, _len;

    results = [];
    for (_i = 0, _len = this.length; _i < _len; _i++) {
      value = this[_i];
      if (results.indexOf(value) === -1) {
        results.push(value);
      }
    }
    return results;
  };
  Array.prototype.shuffle = function() {
    var copy, i, j, temp;

    copy = this.copy();
    i = this.length;
    while (--i) {
      j = Math.floor(Math.random() * (i + 1));
      temp = copy[i];
      copy[i] = copy[j];
      copy[j] = temp;
    }
    return copy;
  };
  Array.prototype.pluck = function(prop) {
    return this.map(function(o) {
      return o[prop];
    });
  };
  Array.prototype.invoke = function(method) {
    var arg, args, value, _i, _len, _results;

    args = ((function() {
      var _i, _len, _results;

      _results = [];
      for (_i = 0, _len = arguments.length; _i < _len; _i++) {
        arg = arguments[_i];
        _results.push(arg);
      }
      return _results;
    }).apply(this, arguments)).slice(1);
    _results = [];
    for (_i = 0, _len = this.length; _i < _len; _i++) {
      value = this[_i];
      _results.push(value[method].apply(value, args));
    }
    return _results;
  };
  Array.prototype.max = function() {
    return Math.max.apply(null, this);
  };
  Array.prototype.without = function(v) {
    var index;

    index = this.indexOf(v);
    if (index >= 0) {
      this.splice(index, 1);
    }
    return this;
  };
  Array.prototype.sum = function() {
    var sum, value, _i, _len;

    sum = 0;
    for (_i = 0, _len = this.length; _i < _len; _i++) {
      value = this[_i];
      sum += value;
    }
    return sum;
  };
  Array.prototype.copy = function() {
    return this.slice();
  };
  return Array;
});

define('detect',['globals', 'array'], function(g, Array) {
  var android, chrome, featureClassNames, features, firefox, ipad, iphone, key, m, mobile, ua, webkit, windows, xp;

  features = {};
  ua = navigator.userAgent.toLowerCase();
  m = function(p) {
    return !!(ua.match(p));
  };
  xp = m(/xp/i) || m(/windows nt 5.1/i);
  windows = m(/windows/i);
  webkit = m(/webkit/i);
  firefox = m(/firefox/i);
  android = m(/android/i);
  mobile = m(/mobile/i);
  ipad = m(/ipad/i);
  iphone = m(/iphone/i);
  chrome = m(/chrome/i);
  features = {
    transforms_3d_a_grade: (firefox || webkit) && !xp && !android && !(chrome && windows),
    transforms_3d_b_grade: (firefox || webkit) && !mobile && !xp && !android,
    touch: "ontouchstart" in window,
    ipad: ipad,
    iphone: iphone,
    android: android,
    retina: window.devicePixelRatio > 1
  };
  features.handheld = (features.ipad || features.iphone || features.android) && features.touch;
  featureClassNames = (function() {
    var _results;

    _results = [];
    for (key in features) {
      if (features[key]) {
        _results.push(key);
      } else {
        _results.push("no_" + key);
      }
    }
    return _results;
  })();
  h.addClass(featureClassNames.join(' '));
  return features;
});

define('window',['globals', 'lib/zepto/zepto', 'detect'], function(globals, $, features) {
  var appleStatusBar, browserDimensions, device, writeHeight;

  if ((w.orientation != null) && features.iphone) {
    appleStatusBar = 20;
    browserDimensions = {
      iphone: {
        landscape: {
          w: 960,
          h: 640,
          chrome: 32
        },
        portrait: {
          w: 640,
          h: 960,
          chrome: 44
        }
      }
    };
    device = features.ipad ? 'ipad' : 'iphone';
    writeHeight = function() {
      var base, height, orient, subtract;

      orient = w.orientation === 0 || w.orientation === 180 ? "portrait" : "landscape";
      base = browserDimensions[device][orient].h;
      subtract = appleStatusBar;
      if (!w.navigator.standalone) {
        subtract += browserDimensions[device][orient].chrome;
      }
      height = base - (subtract * 2);
      return b.removeClass(['portrait', 'landscape'].without(orient)[0]).addClass(orient).css({
        width: browserDimensions[device][orient]['w'] + "px",
        height: height + 'px'
      });
    };
    $(w).on('orientationchange', function() {
      writeHeight();
      return scrollTo(0, 1);
    });
    writeHeight();
  }
  return w;
});

define('string',['globals'], function() {
  var singleTag, tag,
    _this = this;

  String.prototype.without = function(string) {
    var regexp;

    regexp = new RegExp("" + string, "g");
    return this.replace(regexp, '');
  };
  String.prototype.capitalize = function() {
    return this.charAt(0).toUpperCase() + this.substring(1).toLowerCase();
  };
  String.prototype.include = function(s) {
    return this.indexOf(s) >= 0;
  };
  String.prototype.endsWith = function(s) {
    return this.indexOf(s, this.length - s.length) !== -1;
  };
  String.prototype.lowerCamelCase = function() {
    return this.split(/_|-/).map(function(chunk, i) {
      if (i !== 0) {
        return chunk.capitalize();
      } else {
        return chunk;
      }
    }).join('');
  };
  String.prototype.stripFunkyChars = function() {
    return this.replace(/&#39;/g, '').replace(/&quot;/g, '').replace(/[?!:"',]/g, '').replace(/-+$/g, '');
  };
  String.prototype.convertChars = function() {
    var el;

    el = document.createElement('div');
    el.innerHTML = this;
    return el.innerHTML;
  };
  String.prototype.plural = function() {
    if (this.endsWith('y')) {
      return this.replace(/y$/, 'ies');
    } else {
      return this + "s";
    }
  };
  tag = function(tagName) {
    return function(attrs, guts) {
      var attribute, attributes, attributesString;

      attributesString = '';
      if (arguments.length === 1) {
        guts = attrs;
        attrs = {};
      }
      if (typeof guts === 'function') {
        guts = guts();
      }
      if (arguments.length === 2) {
        attributes = (function() {
          var _results;

          _results = [];
          for (attribute in attrs) {
            _results.push("" + attribute + "='" + attrs[attribute] + "'");
          }
          return _results;
        })();
        attributesString = ' ' + attributes.join(' ');
      }
      return "<" + tagName + attributesString + ">" + guts + "</" + tagName + ">";
    };
  };
  singleTag = function(tagName) {
    return function(attrs) {
      var attribute, attributes;

      attributes = (function() {
        var _results;

        _results = [];
        for (attribute in attrs) {
          _results.push("" + attribute + "='" + attrs[attribute] + "'");
        }
        return _results;
      })();
      return "<" + tagName + " " + (attributes.join(' ')) + " />";
    };
  };
  "td tr div option span".split(" ").forEach(function(tagName) {
    return w[tagName] = tag(tagName);
  });
  "img input".split(" ").forEach(function(tagName) {
    return w[tagName] = singleTag(tagName);
  });
  w.setupSelecterRenderer = function(element, getProperty, max) {
    var renderOptions;

    renderOptions = function() {
      var diff, num, options, template, _i, _num;

      options = "";
      for (num = _i = 0; 0 <= max ? _i <= max : _i >= max; num = 0 <= max ? ++_i : --_i) {
        diff = num - getProperty();
        if (diff > 0) {
          diff = "+" + diff;
        }
        _num = String(num);
        if (_num.length === 1) {
          _num = "&nbsp;" + _num;
        }
        template = diff === 0 ? _num : "" + _num + "&nbsp;&nbsp;&nbsp;&nbsp;:&nbsp;&nbsp;&nbsp;&nbsp;" + diff;
        options += option({
          value: num
        }, template);
      }
      return element.innerHTML = options;
    };
    return renderOptions;
  };
  return String;
});

define('event',['alias', 'zepto', 'detect'], function(alias, $, features) {
  var Event, customEvents;

  customEvents = {};
  Event = {
    customEvents: customEvents,
    down: features.handheld ? "touchstart" : "mousedown",
    up: features.handheld ? "touchend" : "mouseup",
    move: features.handheld ? "touchmove" : "mousemove"
  };
  Event.ondown = "on" + Event.down;
  Event.onup = "on" + Event.up;
  Event.onmove = "on" + Event.move;
  w.fire = function(name, data) {
    var copy, handler, _i, _len;

    if (name in customEvents) {
      copy = customEvents[name].copy();
      for (_i = 0, _len = copy.length; _i < _len; _i++) {
        handler = copy[_i];
        handler({
          data: data
        });
      }
    }
    return w;
  };
  w.after = function(eventNames, handler, data) {
    var name, _i, _len, _results;

    eventNames = eventNames.split(" ");
    _results = [];
    for (_i = 0, _len = eventNames.length; _i < _len; _i++) {
      name = eventNames[_i];
      if (name in customEvents) {
        _results.push(customEvents[name].push(handler));
      } else {
        _results.push(customEvents[name] = [handler]);
      }
    }
    return _results;
  };
  w.forget = function(eventNames, handler) {
    var name, _i, _len, _results;

    if (handler == null) {
      handler = false;
    }
    eventNames = eventNames.split(" ");
    _results = [];
    for (_i = 0, _len = eventNames.length; _i < _len; _i++) {
      name = eventNames[_i];
      if (name in customEvents) {
        if (!handler) {
          _results.push(delete customEvents[name]);
        } else {
          customEvents[name].without(handler);
          if (customEvents[name].empty()) {
            _results.push(delete customEvents[name]);
          } else {
            _results.push(void 0);
          }
        }
      } else {
        _results.push(void 0);
      }
    }
    return _results;
  };
  w.safe = function(f) {
    return function(e) {
      var targ;

      stop(e);
      targ = e.target.nodeType === 3 ? e.target.parentNode : e.target;
      targ.blur();
      return f(e);
    };
  };
  w.stop = function(e) {
    e.preventDefault();
    return e.stopPropagation();
  };
  w.onQuickClick = function(selector, f) {
    return $(selector).on(Event.up, safe(f));
  };
  $.fn.doubleclick = function(handler) {
    var doubleClickHandler, doubleclickTimeout, first, second;

    doubleclickTimeout = false;
    first = second = false;
    doubleClickHandler = function(e) {
      if (first) {
        second = new Date();
      } else {
        first = new Date();
      }
      if (first && second && 300 > second - first) {
        handler(e);
        first = second = false;
        return clearTimeout(doubleclickTimeout);
      } else {
        return doubleclickTimeout = wait(301, function() {
          return first = second = false;
        });
      }
    };
    return this.on('click', doubleClickHandler);
  };
  return Event;
});

define('types',[],function() {
  return ['Creature', 'Artifact', 'Enchantment', 'Land', 'Sorcery', 'Instant', 'Legendary', 'Planeswalker', 'Token'];
});

define('get-active-card',['require'], function(require) {
  return function() {
    return mtg.mousedOverCard || require('popup').card;
  };
});

define('shortcut',['event', 'get-active-card'], function(Event, getActiveCard) {
  var getCard, shortcut;

  getCard = function(f) {
    return function() {
      var card;

      card = getActiveCard();
      if (card) {
        return f.call(card);
      }
    };
  };
  shortcut = function(key, f) {
    return after("" + key + ":pressed", getCard(f));
  };
  return shortcut;
});

define('zone-model',['require', 'event', 'types', 'string', 'shortcut'], function(require, Event, TYPES, String, shortcut) {
  var ZoneModel;

  ZoneModel = (function() {
    function ZoneModel(data) {
      var _this = this;

      $.extend(this, data);
      this.id = this.name.toLowerCase();
      this.cards = [];
      after("onleave" + this.id, function(e) {
        _this.remove(e.data.card);
        return fire("" + _this.id + ":changed", e);
      });
      after("onenter" + this.id, function(e) {
        _this.add(e.data.card);
        return fire("" + _this.id + ":changed", e);
      });
      shortcut(this.key, (function(id) {
        return function() {
          return this[id]();
        };
      })(this.id));
    }

    ZoneModel.prototype.view = function() {
      return require('zone-views')[this.id];
    };

    ZoneModel.prototype.add = function(card, index) {
      var reordered;

      reordered = false;
      if (this.cards.include(card)) {
        this.remove(card);
        reordered = true;
      }
      if (index != null) {
        this.cards.splice(index, 0, card);
        reordered = true;
      } else {
        this.cards.push(card);
      }
      if (reordered) {
        fire("" + this.id + ":reordered");
      }
      return this.cards;
    };

    ZoneModel.prototype.remove = function(card) {
      return this.cards.without(card);
    };

    ZoneModel.prototype.first = function() {
      return this.cards.first();
    };

    ZoneModel.prototype.last = function() {
      return this.cards.last();
    };

    ZoneModel.prototype.size = function() {
      return this.cards.length;
    };

    ZoneModel.prototype.indexOf = function(c) {
      return this.cards.indexOf(c);
    };

    ZoneModel.prototype.include = function(c) {
      return this.cards.include(c);
    };

    ZoneModel.prototype.empty = function() {
      return this.cards.empty();
    };

    ZoneModel.prototype.findByName = function(name) {
      return this.cards.find(function(card) {
        return card.name === name;
      });
    };

    ZoneModel.prototype.findAllByName = function(name) {
      return this.cards.findAll(function(card) {
        return card.name === name;
      });
    };

    ZoneModel.prototype.exportState = function() {
      var state,
        _this = this;

      state = {
        size: this.size()
      };
      state.power = this.creatures().pluck('p').sum();
      state.toughness = this.creatures().pluck('t').sum();
      TYPES.forEach(function(type) {
        var types;

        type = type.toLowerCase();
        types = type.plural();
        return state[types] = _this[types]().length;
      });
      return state;
    };

    return ZoneModel;

  })();
  TYPES.forEach(function(type) {
    return ZoneModel.prototype[type.plural().toLowerCase()] = function() {
      return this.cards.findAll(function(card) {
        return card.type.include(type);
      });
    };
  });
  return ZoneModel;
});

define('library-model',['zone-model'], function(ZoneModel) {
  var library;

  library = new ZoneModel({
    name: 'Library',
    key: 'y'
  });
  library.addToTop = function(card) {
    card.library();
    this.add(card, library.size() - 1);
    return fire("library:addedToTop", {
      id: card.id
    });
  };
  library.addToBottom = function(card) {
    card.library();
    this.add(card, 0);
    return fire("library:addedToBottom", {
      id: card.id
    });
  };
  library.shuffle = function() {
    this.cards = this.cards.shuffle();
    fire("library:shuffled");
    return this;
  };
  return library;
});

define('window-loaded',['zepto', 'q'], function($, Q) {
  var deferred;

  deferred = Q.defer();
  if (window.loaded) {
    deferred.resolve();
  } else {
    $(window).on('load', deferred.resolve);
  }
  return deferred.promise;
});

define('get-focused-field',['zepto', 'q', 'event'], function($, Q, Event) {
  var blurOnEsc, body, fieldSelector, focusedField, getFocusedField, set;

  body = document.body;
  fieldSelector = "input, select";
  focusedField = void 0;
  set = function(e) {
    var deferred, resolve, unset;

    focusedField = e.target;
    deferred = Q.defer();
    resolve = function(e) {
      if (focusedField) {
        if (e.target !== focusedField && $(e.target).parents().indexOf(focusedField) === -1) {
          return deferred.resolve();
        }
      } else {
        return deferred.resolve();
      }
    };
    unset = function() {
      $(body).off(Event.down, resolve).off("blur", fieldSelector, deferred.resolve);
      $(focusedField).blur();
      return focusedField = void 0;
    };
    deferred.promise.then(unset);
    return $(body).on(Event.down, resolve).on("blur", fieldSelector, deferred.resolve);
  };
  blurOnEsc = function(e) {
    if (e.keyCode === 27) {
      $(this).blur().trigger('blur');
    }
    return true;
  };
  $(body).on("focus", fieldSelector, set).on("keyup", "select", blurOnEsc);
  return getFocusedField = function() {
    return focusedField;
  };
});

define('keys',['alias', 'event', 'string', 'shortcut', 'get-focused-field'], function(alias, Event, String, shortcut, getFocusedField) {
  var KEYS, getKey;

  KEYS = {
    13: 'return',
    32: 'spacebar',
    27: 'escape'
  };
  getKey = function(e) {
    return KEYS[e.charCode] || KEYS[e.keyCode];
  };
  $(document.body).on("keypress", function(e) {
    var key;

    if (!getFocusedField() || e.ctrlKey || e.metaKey) {
      key = getKey(e);
      if (!key) {
        key = String.fromCharCode(e.charCode);
      }
      if (key) {
        fire(key + ":pressed", {
          e: e
        });
      }
    }
    return true;
  });
  shortcut("q", function() {
    return this.mod("p", 1);
  });
  shortcut("Q", function() {
    return this.mod("p", -1);
  });
  shortcut("w", function() {
    return this.mod("t", 1);
  });
  shortcut("W", function() {
    return this.mod("t", -1);
  });
  shortcut("e", function() {
    return this.mod("c", 1);
  });
  shortcut("E", function() {
    return this.mod("c", -1);
  });
  shortcut("f", function() {
    if (this.can('transform')) {
      return this.transform();
    } else {
      return this.toggleFace();
    }
  });
  shortcut("F", function() {
    return this.toggleFlipped();
  });
  shortcut("t", function() {
    return this.toggleTapped();
  });
  return {
    KEYS: KEYS,
    shortcut: shortcut,
    getKey: getKey
  };
});

define('draw',['alias', 'zepto', 'event', 'library-model', 'window-loaded', 'keys', 'window'], function(alias, $, Event, library, windowLoaded, keys) {
  var draw;

  draw = function(n, cardName) {
    var card, i, _i;

    if (n == null) {
      n = 1;
    }
    for (i = _i = 0; 0 <= n ? _i < n : _i > n; i = 0 <= n ? ++_i : --_i) {
      if (library.size() === 0) {
        return;
      }
      card = (function() {
        if (cardName != null) {
          return library.findByName(cardName);
        } else {
          return library.last();
        }
      })();
      card.hand();
    }
  };
  $(function() {
    var $selectEl, renderSelectEl;

    $selectEl = $("#draw_card_by_name_field");
    if ($selectEl.length === 0) {
      return;
    }
    renderSelectEl = function() {
      var newOptions;

      newOptions = (function() {
        var name, names;

        if (!library.cards.empty()) {
          names = library.cards.pluck("name").uniq();
          return ((function() {
            var _i, _len, _ref, _results;

            _ref = names.sort();
            _results = [];
            for (_i = 0, _len = _ref.length; _i < _len; _i++) {
              name = _ref[_i];
              _results.push(option({
                value: escape(name)
              }, name));
            }
            return _results;
          })()).join("");
        } else {
          return option({
            value: ""
          }, "There are no cards in the library.");
        }
      })();
      if (newOptions.length !== $selectEl.html().length) {
        return $selectEl.html(newOptions);
      }
    };
    after("onlibrary onleavelibrary", renderSelectEl);
    after("/:pressed", function() {
      return $selectEl.focus().trigger('focus');
    });
    windowLoaded.then(function() {
      $("#draw_card_by_name").show();
      onQuickClick("#draw_card_button", function() {
        return draw(1, unescape($selectEl.val()));
      });
      return $selectEl.on('keypress', function(e) {
        if (keys.getKey(e) === "return" && e.target === $selectEl[0]) {
          return draw(1, unescape($selectEl.val()));
        }
      });
    });
    return after("d:pressed", function() {
      return draw();
    });
  });
  return draw;
});

define('deck-loaded',['event', 'q'], function(Event, Q) {
  var deferred, promise;

  deferred = Q.defer();
  promise = deferred.promise.timeout(15000);
  promise.fail(function() {
    return fire('deck:errored');
  });
  after("deck:loaded", function(e) {
    return deferred.resolve(e.data);
  });
  return promise;
});

define('loaded',['deck-loaded', 'window-loaded'], function(deckLoaded, windowLoaded) {
  return windowLoaded.then(function() {
    return deckLoaded.then(function(deck) {
      return deck;
    });
  });
});

define('card-dimensions',{});

define('preload-images',['globals', 'zepto', 'q', 'card-dimensions'], function(globals, $, Q, cardDimensions) {
  var preloadImageAndCacheSize, _preloadImageAndCacheSize;

  _preloadImageAndCacheSize = function(name, path) {
    var $tempImage, deferred;

    deferred = Q.defer();
    if (cardDimensions[name]) {
      deferred.resolve();
    } else {
      $tempImage = $(document.createElement('img'));
      $tempImage.addClass('temp_image').on('load', deferred.resolve);
      deferred.promise.then(function() {
        var dimensions;

        dimensions = {
          width: $tempImage.width(),
          height: $tempImage.height()
        };
        cardDimensions[name] = dimensions;
        $tempImage.off('load').remove();
        return fire("" + (name.without(' ')) + ":dimensions:loaded", dimensions);
      });
      b.append($tempImage);
      $tempImage.attr('src', path);
    }
    return deferred.promise;
  };
  preloadImageAndCacheSize = function(name, path) {
    var pairs;

    pairs = typeof name === 'object' ? name : [[name, path]];
    return Q.allSettled(pairs.map(function(pair) {
      return _preloadImageAndCacheSize.apply(null, pair);
    }));
  };
  return preloadImageAndCacheSize;
});

define('card-model-string-helpers',['string'], function(String) {
  var formatString, helpers, parsePT;

  helpers = {};
  formatString = function(dirty, delimiter) {
    return dirty.stripFunkyChars().replace(/\s/g, delimiter).replace('//', delimiter).replace('---', delimiter).toLowerCase();
  };
  helpers.buildPath = function(path, edition, name) {
    var built, prefix;

    if (path) {
      return path.replace(/\s/g, '%20').replace(/&#39;/g, "'");
    } else if (mtg.local) {
      prefix = "/decks/images/";
    } else {
      prefix = "http://static.tappedout.net/mtg-cards/";
    }
    edition = formatString(edition, '-');
    name = formatString(name, '-');
    return built = "" + prefix + edition + "/" + name + ".jpg";
  };
  helpers.formatIdString = function(name, n) {
    return formatString(("id_" + name + "_" + n).replace(/\/+/g, '_').replace(/\./g, ''), '_');
  };
  parsePT = function(v) {
    return Number(!!v.match(/\*|x/i) || v);
  };
  helpers.parsePTC = function(string) {
    var obj, pt;

    obj = {
      p: 0,
      t: 0,
      c: 0
    };
    if (string) {
      if (string.include('/')) {
        pt = string.split('/');
        obj.p = parsePT(pt[0]);
        obj.t = parsePT(pt[1]);
      } else if (string.include('Loyalty')) {
        obj.c = Number(string.split(' Loyalty')[0]);
      }
    }
    return obj;
  };
  return helpers;
});

define('sizes',['alias', 'event', 'loaded', 'preload-images', 'detect', 'card-model-string-helpers'], function(alias, Event, loadedPromise, preloadImageAndCacheSize, features, cardModelHelpers) {
  var preload, setSize, sizes, tappedoutSizes;

  tappedoutSizes = {
    small: 'small',
    medium: 'small',
    large: 'medium'
  };
  sizes = {
    cardPadding: 6,
    cardHeight: function() {
      return sizes.targetSizes[sizes.current].height + sizes.cardPadding;
    },
    cardWidth: function() {
      return sizes.targetSizes[sizes.current].width + sizes.cardPadding;
    },
    tappedoutSizes: tappedoutSizes,
    options: ['small', 'medium', 'large'],
    targetSizes: {
      small: {
        width: 80,
        height: 114
      },
      medium: {
        height: 170,
        width: 120
      },
      large: {
        height: 285,
        width: 200
      }
    }
  };
  sizes.current = features.handheld || b.height() < 770 ? 'small' : 'medium';
  sizes.replaceSizeInPath = function(path) {
    var targetSize;

    if (path) {
      targetSize = sizes.tappedoutSizes[features.retina ? 'large' : sizes.current];
      return path.replace('medium.', targetSize + '.');
    } else {
      return '';
    }
  };
  preload = function(deck) {
    var card, cardName, name, pairs, path;

    pairs = (function() {
      var _results;

      _results = [];
      for (cardName in deck.cards) {
        card = deck.cards[cardName];
        path = cardModelHelpers.buildPath(deck.media_root + sizes.replaceSizeInPath(card.image_path), card.edition, cardName);
        name = cardName.stripFunkyChars();
        _results.push([name, path]);
      }
      return _results;
    })();
    return preloadImageAndCacheSize(pairs);
  };
  setSize = function(e) {
    var otherSize, size, _i, _len, _ref;

    size = e.data.value;
    _ref = ['small', 'medium', 'large'].without(size);
    for (_i = 0, _len = _ref.length; _i < _len; _i++) {
      otherSize = _ref[_i];
      h.removeClass("card_size_" + otherSize);
    }
    h.addClass("card_size_" + size);
    return sizes.current = size;
  };
  after("size:changed", setSize);
  loadedPromise.then(function() {
    return after("size:changed", function() {
      return loadedPromise.then(preload);
    });
  });
  return sizes;
});

define('mtg',['window', 'globals', 'array', 'string', 'detect', 'draw', 'loaded', 'sizes'], function(w, globals, array, string, features, draw, loaded, sizes) {
  var mtg;

  mtg = {
    local: location.host.include("local"),
    cardBackPath: function() {
      return "/images/back-" + (features.retina ? 'large' : sizes.current) + ".png";
    },
    transitionDuration: 500,
    mousedOverCard: void 0,
    Z: {
      FLOATING: 201,
      HOVER: 0
    }
  };
  loaded.then(function() {
    scrollTo(0, 1);
    b.removeClass('loading');
    draw(7);
    return defer(function() {
      return fire("hand:drawn");
    });
  });
  return w.mtg = mtg;
});

define('loader-helpers',['array'], function(Array) {
  var getDeckId, getPlaytestURL;

  getPlaytestURL = function(l) {
    var p;

    l = l || location;
    p = false;
    if (l.pathname && l.pathname !== '/' && l.host.match(/playtest.tappedout.net|local|mtgplaytester.herokuapp.com/)) {
      p = "http://tappedout.net/mtg-decks" + l.pathname + "playtest.js";
    } else if (l.hash.length > 0 && l.hash !== '#') {
      p = l.hash.split('#d=')[1];
    }
    return p;
  };
  getDeckId = function(url) {
    if (url.match('playtest.js')) {
      return url.split('/').without('playtest.js').last();
    } else {
      return url.split('/').last().without('.js');
    }
  };
  return {
    getPlaytestURL: getPlaytestURL,
    getDeckId: getDeckId
  };
});

define('deck-url',['loader-helpers'], function(loaderHelpers) {
  return function(deckSrc) {
    return "http://tappedout.net/mtg-decks/" + (loaderHelpers.getDeckId(deckSrc)) + "/";
  };
});

define('card-views',{});

define('zone-names',[],function() {
  return ['battlefield', 'hand', 'library', 'exiled', 'graveyard', 'commander'];
});

define('battlefield-model',['zone-model'], function(ZoneModel) {
  return new ZoneModel({
    name: 'Battlefield',
    key: 'b',
    tapped: function() {
      return this.cards.filter(function(card) {
        return card.tapState.current === 'tapped';
      });
    },
    untap: function() {
      var tapped;

      tapped = this.tapped();
      if (!tapped.empty()) {
        tapped.invoke('untap');
      }
      return this;
    },
    getRecipients: function() {
      return this.cards.filter(function(card) {
        return !card.isPlaneswalker && (card.isCreature || card.hasNotes());
      });
    }
  });
});

define('hand-model',['zone-model'], function(ZoneModel) {
  var hand;

  hand = new ZoneModel({
    name: 'Hand',
    key: 'a'
  });
  hand.hidden = function() {
    var facedown;

    facedown = this.cards.findAll(function(card) {
      return card.faceState.current === 'facedown';
    });
    return facedown.length === this.cards.length && !this.empty();
  };
  return hand;
});

define('graveyard-model',['zone-model'], function(ZoneModel) {
  return new ZoneModel({
    name: 'Graveyard',
    key: 'g'
  });
});

define('exiled-model',['zone-model'], function(ZoneModel) {
  return new ZoneModel({
    name: 'Exiled',
    key: 'x'
  });
});

define('commander-model',['zone-model'], function(ZoneModel) {
  return new ZoneModel({
    name: 'Commander',
    key: 'c'
  });
});

define('zone-models',['zone-model', 'battlefield-model', 'hand-model', 'library-model', 'graveyard-model', 'exiled-model', 'commander-model'], function(ZoneModel, battlefield, hand, library, graveyard, exiled, commander) {
  return {
    hand: hand,
    library: library,
    battlefield: battlefield,
    exiled: exiled,
    graveyard: graveyard,
    commander: commander
  };
});

define('super-select',['lib/zepto/zepto', 'globals'], function($) {
  var SuperSelect;

  SuperSelect = (function() {
    function SuperSelect(options) {
      var _this = this;

      this.$el = $(options.el);
      this.template = options.template || this.template;
      this.render = options.render || this.render;
      this.$button = options.button ? $(options.button) : $(document.createElement('div')).addClass('super_select_button');
      if (!options.button) {
        this.$el.before(this.$button);
      }
      this.$el.on('mouseover', function() {
        return _this.mouseover();
      }).on('mouseout', function() {
        return _this.mouseout();
      }).addClass('super_select').on('change', function() {
        return _this.render();
      });
      defer(function() {
        return _this.render();
      });
    }

    SuperSelect.prototype.render = function() {
      return this.$button.html(this.template(this.$el.val()));
    };

    SuperSelect.prototype.template = function() {
      return this.$el.val();
    };

    SuperSelect.prototype.mouseover = function() {
      return this.$button.addClass('hover');
    };

    SuperSelect.prototype.mouseout = function() {
      return this.$button.removeClass('hover');
    };

    SuperSelect.prototype.toggle = function(enable) {
      return this.$button.toggleClass('disabled', enable);
    };

    return SuperSelect;

  })();
  return SuperSelect;
});

define('modal',['lib/zepto/zepto', 'event'], function($, Event) {
  var $modalOverlay, Modal, hideVisibleModals, modals;

  $modalOverlay = $("#modal_overlay");
  modals = [];
  Modal = (function() {
    function Modal(id, closeId) {
      var _this = this;

      this.id = id;
      this.el = $("#" + id);
      this.closeEl = $("#" + closeId);
      this.visible = false;
      onQuickClick(this.closeEl, function() {
        return _this.hide();
      });
      modals.push(this);
      return this;
    }

    Modal.prototype.show = function() {
      hideVisibleModals();
      this.el.show();
      this.visible = true;
      $modalOverlay.addClass("visible");
      fire("" + this.id + ":shown");
      return this;
    };

    Modal.prototype.hide = function() {
      this.el.hide();
      this.visible = false;
      $modalOverlay.removeClass("visible");
      fire("" + this.id + ":hidden");
      w.modalRecentlyVisible = wait(200, function() {
        return w.modalRecentlyVisible = false;
      });
      return this;
    };

    Modal.prototype.toggle = function() {
      if (this.visible) {
        return this.hide();
      } else {
        return this.show();
      }
    };

    return Modal;

  })();
  hideVisibleModals = function() {
    var modal, _i, _len;

    for (_i = 0, _len = modals.length; _i < _len; _i++) {
      modal = modals[_i];
      if (modal.visible) {
        modal.hide();
      }
    }
    return false;
  };
  $modalOverlay.on(Event.down, hideVisibleModals);
  return {
    Modal: Modal,
    $modalOverlay: $modalOverlay,
    modals: modals
  };
});

define('button',['event', 'zepto'], function(Event, $) {
  var Button;

  Button = function(id, options) {
    var control, handler, type, _ref,
      _this = this;

    this.id = id;
    this.$element = $("#" + id);
    type = (options != null ? options.type : void 0) || Event.up;
    handler = function(e) {
      if (!_this.disabled) {
        fire("button:clicked", {
          id: id
        });
        options.handler(e);
      }
      return stop(e);
    };
    this.$element.on(type, handler);
    this.disable = function() {
      _this.disabled = true;
      return _this.$element.addClass("disabled");
    };
    this.enable = function() {
      _this.disabled = false;
      return _this.$element.removeClass("disabled");
    };
    if (!!options.control) {
      control = function() {
        if (options.control.condition()) {
          return _this.enable();
        } else {
          return _this.disable();
        }
      };
      control();
      after(options.control.events, control);
    } else {
      this.enable();
    }
    if ((_ref = options.init) != null) {
      _ref.call(this);
    }
    return this;
  };
  return Button;
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('popup',['require', 'modal', 'button', 'super-select', 'detect', 'event', 'zone-models', 'deck-loaded'], function(require, modal, Button, SuperSelect, features, Event, zones, deckLoaded) {
  var $modalOverlay, Modal, Popup, addToZone, battlefield, buttonOptionsForZone, exiled, graveyard, hand, inBattlefield, library, manipCounter, mediaRoot, modals, popup, popupButtonWrapper, ptc, _ptc;

  modals = modal.modals;
  Modal = modal.Modal;
  $modalOverlay = modal.$modalOverlay;
  battlefield = zones.battlefield;
  hand = zones.hand;
  graveyard = zones.graveyard;
  exiled = zones.exiled;
  library = zones.library;
  mediaRoot = void 0;
  deckLoaded.then(function(deck) {
    return mediaRoot = deck.media_root;
  });
  _ptc = 'p t c'.split(' ');
  ptc = function(iterator) {
    return _ptc.forEach(iterator);
  };
  Popup = (function(_super) {
    __extends(Popup, _super);

    function Popup(id, closeId) {
      Popup.__super__.constructor.call(this, id, closeId);
    }

    Popup.prototype.card = void 0;

    Popup.prototype.img = $("#zoom_image").get(0);

    Popup.prototype.name = $("#zoomed_name");

    Popup.prototype.edition = $("#zoomed_edition");

    Popup.prototype.cardActionsEl = $("#card_actions");

    Popup.prototype.height = 30;

    Popup.prototype.clickEventFromCard = false;

    Popup.prototype.linkTemplate = function(name) {
      var _char, _name;

      _name = name;
      if (!name.include('zoom')) {
        if (name.include('tap')) {
          _char = 't';
        }
        if (name.match(/flip|face|form/)) {
          _char = 'f';
        }
        name = name.split(_char).join(span({
          'class': 'underline'
        }, _char));
      }
      return "<li><a class='button " + _name + "' data-method='" + _name + "'>" + name + "</a></li>";
    };

    Popup.prototype.visible = false;

    Popup.prototype.show = function(card) {
      var _i, _len, _ref,
        _this = this;

      scrollTo(0, 1);
      this.card = card;
      this.img.src = (((_ref = card.transformState) != null ? _ref.current : void 0) === 'transformed' ? mediaRoot + card.data.transformation.image_path : card.path).replace('small', 'medium');
      this.updateFields();
      this.name.text(card.name);
      this.edition.text(card.edition);
      this.updateLinks();
      this.boundUpdateFields = function() {
        return _this.updateFields();
      };
      after("" + card.id + ":p:changed " + card.id + ":t:changed " + card.id + ":c:changed", this.boundUpdateFields);
      this.boundOnTokenDestroy = function() {
        forget("" + card.id + ":destroyed", _this.boundOnTokenDestroy);
        _this.hide();
        return _this;
      };
      if (card.isToken) {
        after("" + card.id + ":destroyed", this.boundOnTokenDestroy);
      }
      for (_i = 0, _len = modals.length; _i < _len; _i++) {
        modal = modals[_i];
        if (modal.visible && modal !== this) {
          modal.hide();
        }
      }
      this.el.show();
      this.visible = true;
      $modalOverlay.addClass("visible");
      fire("" + this.id + ":shown");
      return this;
    };

    Popup.prototype.hide = function() {
      forget("" + this.card.id + ":p:changed " + this.card.id + ":t:changed " + this.card.id + ":c:changed", this.boundUpdateFields);
      this.card = void 0;
      Popup.__super__.hide.call(this);
      return scrollTo(0, 1);
    };

    Popup.prototype.dismiss = function(e) {
      if (!(e.target.offsetParent === this.card || e.target.offsetParent === this.el.get(0))) {
        b.off(Event.up, Popup.dismiss);
        return this.hide();
      }
    };

    Popup.prototype.tryToSetupFields = function() {
      var _this = this;

      if (!($(this.p).html().length > 0)) {
        this.optionRenderers = {};
        return ptc(function(property) {
          return _this.optionRenderers[property] = setupSelecterRenderer(_this[property], (function() {
            return _this.card[property];
          }), 100);
        });
      }
    };

    Popup.prototype.updateFields = function() {
      var _this = this;

      if (this.card) {
        this.tryToSetupFields();
        ptc(function(property) {
          _this.optionRenderers[property]();
          return _this[property].value = _this.card[property];
        });
        this.pSelector.render();
        this.tSelector.render();
        this.cSelector.render();
        fire("popup:fields:changed");
        return this;
      } else {
        return false;
      }
    };

    Popup.prototype.updateLinks = function() {
      var actions, listEls, zoneName;

      actions = this.card.capabilities();
      for (zoneName in zones) {
        actions.without(zoneName);
      }
      if (popup.card.can('transform')) {
        actions.without('facedown');
      }
      listEls = actions.map(this.linkTemplate).join("");
      return this.cardActionsEl.html("<ul>" + listEls + "</ul>");
    };

    return Popup;

  })(Modal);
  popup = new Popup('popup', 'close_popup');
  popup.p = $("#zoomed_card_p").get(0);
  popup.t = $("#zoomed_card_t").get(0);
  popup.c = $("#zoomed_card_c").get(0);
  popup.pSelector = new SuperSelect({
    el: popup.p
  });
  popup.tSelector = new SuperSelect({
    el: popup.t
  });
  popup.cSelector = new SuperSelect({
    el: popup.c
  });
  after("popup:invoked", function(e) {
    popup.show(e.data.card);
    popup.clickEventFromCard = !!e.data.fromCard;
    if (e.data.fromCard) {
      return b.on(Event.up, popup.unsetClickEventFromCard);
    }
  });
  popup.unsetClickEventFromCard = function() {
    b.off(Event.up, popup.unsetClickEventFromCard);
    return popup.clickEventFromCard = false;
  };
  after("spacebar:pressed", function() {
    if (popup.visible) {
      return popup.hide();
    } else if (mtg.mousedOverCard) {
      return popup.show(mtg.mousedOverCard);
    }
  });
  ptc(function(property) {
    return $(popup[property]).on("change", function(e) {
      var diff;

      diff = Number(popup[property].value - popup.card[property]);
      return popup.card.mod(property, diff);
    });
  });
  popupButtonWrapper = function(f) {
    return function(e) {
      if (popup.clickEventFromCard) {
        return popup.unsetClickEventFromCard();
      } else {
        return f(e);
      }
    };
  };
  popup.eventType = features.iphone ? 'click' : Event.up;
  popup.cardActionsEl.on(popup.eventType, 'a', popupButtonWrapper(function(e) {
    popup.card[$(e.currentTarget).data('method')]();
    popup.hide();
    return false;
  }));
  addToZone = function(zone) {
    return safe(function() {
      var _ref;

      if ((_ref = popup.card) != null ? _ref.can(zone.id) : void 0) {
        popup.card[zone.id]();
        return popup.hide();
      }
    });
  };
  buttonOptionsForZone = function(zone) {
    return {
      handler: popupButtonWrapper(addToZone(zone)),
      type: popup.eventType,
      control: {
        condition: function() {
          var _ref;

          return ((_ref = popup.card) != null ? _ref.zone() : void 0) !== zone;
        },
        events: "popup:shown"
      }
    };
  };
  new Button("move_battlefield", buttonOptionsForZone(battlefield));
  new Button("move_hand", buttonOptionsForZone(hand));
  new Button("move_graveyard", buttonOptionsForZone(graveyard));
  new Button("move_exiled", buttonOptionsForZone(exiled));
  new Button("move_library", {
    handler: popupButtonWrapper(safe(function() {
      library.addToTop(popup.card);
      return popup.hide();
    })),
    type: popup.eventType,
    control: {
      condition: function() {
        return popup.card && library.last() !== popup.card;
      },
      events: "popup:shown"
    }
  });
  new Button("move_bottom_library", {
    handler: popupButtonWrapper(safe(function() {
      library.addToBottom(popup.card);
      return popup.hide();
    })),
    type: popup.eventType,
    control: {
      condition: function() {
        return popup.card && library.first() !== popup.card;
      },
      events: "popup:shown"
    }
  });
  manipCounter = function(v) {
    return safe(function() {
      if (inBattlefield()) {
        if (popup.card.c === 0 && v === -1) {
          return false;
        } else {
          return ptc(function(p) {
            return popup.card.mod(p, v);
          });
        }
      }
    });
  };
  inBattlefield = function() {
    var _ref;

    return ((_ref = popup.card) != null ? _ref.zone() : void 0) === battlefield;
  };
  new Button("add_plus_counter", {
    handler: popupButtonWrapper(manipCounter(1)),
    type: popup.eventType,
    control: {
      condition: inBattlefield,
      events: "popup:shown"
    }
  });
  new Button("remove_plus_counter", {
    handler: popupButtonWrapper(manipCounter(-1)),
    type: popup.eventType,
    control: {
      condition: function() {
        return inBattlefield() && popup.card.c > 0;
      },
      events: "popup:shown popup:fields:changed"
    }
  });
  return popup;
});

define('zone-view',['alias', 'lib/zepto/zepto', 'super-select', 'event', 'window-loaded', 'popup'], function(alias, $, SuperSelect, Event, windowLoaded, popup) {
  var ZoneView, defaultDropdownMessage;

  defaultDropdownMessage = "Select a Card";
  ZoneView = (function() {
    function ZoneView(model) {
      var hideSelector,
        _this = this;

      this.model = model;
      this.$element = $("#" + this.model.id);
      this.counter = $("#" + this.model.id + " strong");
      this.shell = this.$element;
      this.margin = this.length = 0;
      this.id = this.model.id;
      after("onenter" + this.id, function(e) {
        return _this.add(e.data.card);
      });
      after("" + this.id + ":changed", function() {
        return _this.render();
      });
      after("" + this.id + ":reordered", function() {
        return _this.render();
      });
      this.cacheDimensions();
      $(w).on('resize', function() {
        return _this.cacheDimensions();
      });
      after('size:changed', function() {
        return _this.cacheDimensions();
      });
      this.$selectElement = $("#" + this.id + "_card_list");
      this.superSelect = new SuperSelect({
        el: this.$selectElement,
        button: this.$element.find(".super_select_button"),
        template: function() {},
        render: function() {}
      });
      hideSelector = function() {
        _this.$element.removeClass("browsing");
        return _this.$selectElement.get(0).blur();
      };
      if (this.$selectElement.length > 0) {
        this.$selectElement.on("blur", hideSelector).on('change', function() {
          var card;

          hideSelector();
          if (_this.$selectElement.val() !== defaultDropdownMessage) {
            card = _this.model.cards[Number(_this.$selectElement.val().split(" - ").first()) - 1];
            popup.show(card);
            return defer(function() {
              return _this.renderCardList();
            });
          } else {
            return _this.$selectElement.get(0).blur();
          }
        });
      }
      this.render();
    }

    ZoneView.prototype.renderCardList = function() {
      var i, options, value;

      options = [
        option({
          value: defaultDropdownMessage
        }, defaultDropdownMessage)
      ];
      i = this.model.cards.length;
      while (i > 0) {
        value = "" + i + " - " + this.model.cards[i - 1].name;
        options.push(option({
          value: value
        }, value));
        i -= 1;
      }
      return this.$selectElement.html(options.join(''));
    };

    ZoneView.prototype.cacheDimensions = function() {
      var _this = this;

      return windowLoaded.then(function() {
        _this.width = _this.$element.get(0).clientWidth;
        _this.height = _this.$element.get(0).clientHeight;
        _this.left = (function() {
          var parent, parentOffset;

          parent = _this.$element.parent().get(0);
          parentOffset = parent.id === 'side' ? parent.offsetLeft : 0;
          return _this.$element.offset().left + 1 + parentOffset;
        })();
        return _this.top = _this.$element.offset().top + 1;
      });
    };

    ZoneView.prototype.add = function(card, index) {
      var cardView;

      cardView = card.view();
      if ((index != null) < this.model.length - 1) {
        return this.model.cards[index + 1].view().$element.before(cardView.$element);
      } else if (cardView) {
        return this.$element.get(0).appendChild(cardView.$element.get(0));
      }
    };

    ZoneView.prototype.fire = function(eventName, memo) {
      return fire(this.id + ":" + eventName, memo);
    };

    ZoneView.prototype.updateCounter = function() {
      return this.$element.find('.super_select_button strong').text(this.model.size());
    };

    ZoneView.prototype.restingZ = function() {
      return 1;
    };

    ZoneView.prototype.render = function() {
      this.updateCounter();
      this.$element.toggleClass("empty", this.model.empty());
      this.superSelect.toggle(this.model.empty());
      return this.renderCardList();
    };

    return ZoneView;

  })();
  return ZoneView;
});

var __bind = function(fn, me){ return function(){ return fn.apply(me, arguments); }; },
  __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('distributable-zone-view',['time', 'zone-view'], function(time, ZoneView) {
  var DistributableZoneView;

  DistributableZoneView = (function(_super) {
    __extends(DistributableZoneView, _super);

    function DistributableZoneView(model) {
      this.delayedDistributeCards = __bind(this.delayedDistributeCards, this);      DistributableZoneView.__super__.constructor.call(this, model);
      this.margin = 5;
    }

    DistributableZoneView.prototype.render = function() {
      DistributableZoneView.__super__.render.call(this);
      this.renderLastVisibleCards();
      return this.delayedDistributeCards();
    };

    DistributableZoneView.prototype.distributeCards = function() {
      var card, cardIndex, x, y, _i, _ref, _results;

      _results = [];
      for (cardIndex = _i = 0, _ref = this.model.size(); 0 <= _ref ? _i < _ref : _i > _ref; cardIndex = 0 <= _ref ? ++_i : --_i) {
        card = this.model.cards[cardIndex];
        x = y = card.restingY = this.margin;
        _results.push(card.move(x, y, this.restingZ(card)));
      }
      return _results;
    };

    DistributableZoneView.prototype.delayedDistributeCards = function() {
      var _this = this;

      time.defer(function() {
        return _this.distributeCards();
      });
      return false;
    };

    DistributableZoneView.prototype.restingZ = function(card) {
      var i, z;

      i = this.model.cards.indexOf(card);
      z = i + 1;
      return z;
    };

    DistributableZoneView.prototype.renderLastVisibleCards = function() {
      var card, edge, _i, _len, _ref;

      edge = this.model.size() - 2;
      _ref = this.model.cards;
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        card = _ref[_i];
        if (this.model.indexOf(card) < edge) {
          if (card.view()) {
            card.view().$element.removeClass('visible');
          }
        }
      }
      if (this.model.cards[edge] && this.model.cards[edge].view()) {
        this.model.cards[edge].view().$element.addClass('visible');
      }
      if (!this.model.empty()) {
        if (this.model.last().view()) {
          return this.model.last().view().$element.addClass('visible');
        }
      }
    };

    return DistributableZoneView;

  })(ZoneView);
  return DistributableZoneView;
});

define('collection',['array'], function() {
  var Collection;

  return Collection = (function() {
    function Collection(options) {
      this.models = (options != null ? options.models : void 0) || [];
    }

    Collection.prototype.add = function(model) {
      this.models.push(model);
      return this;
    };

    Collection.prototype.remove = function(model) {
      this.models.without(model);
      return this;
    };

    Collection.prototype.indexOf = function(model) {
      return this.models.indexOf(model);
    };

    Collection.prototype.include = function(model) {
      return this.models.include(model);
    };

    Collection.prototype.first = function() {
      return this.models[0];
    };

    Collection.prototype.last = function() {
      return this.models.last();
    };

    Collection.prototype.at = function(i) {
      return this.models[i];
    };

    Collection.prototype.pluck = function(property) {
      return this.models.pluck(property);
    };

    Collection.prototype.empty = function() {
      return this.models.length === 0;
    };

    return Collection;

  })();
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('cell',['collection', 'sizes'], function(Collection, sizes) {
  var Cell, cardXOffset, cardYOffset, gridSizes, size;

  cardYOffset = 30;
  cardXOffset = 10;
  gridSizes = {};
  Cell = (function(_super) {
    __extends(Cell, _super);

    function Cell(options) {
      Cell.__super__.constructor.call(this);
      this.x = options.x;
      this.y = options.y;
      this.collection = options.collection;
      this.destroyHandlers = {};
    }

    Cell.prototype.add = function(card) {
      var coords, id,
        _this = this;

      coords = this.position(this.models.length);
      Cell.__super__.add.call(this, card.move(coords.x, coords.y, this.models.length));
      id = card.id;
      this.destroyHandlers[id] = function() {
        return _this.remove(card);
      };
      after("" + card.id + ":destroyed", this.destroyHandlers[id]);
      return this;
    };

    Cell.prototype.remove = function(card) {
      var _this = this;

      Cell.__super__.remove.call(this, card);
      this.teardownCard(card.id);
      this.models.forEach(function(card, i) {
        var coords;

        coords = _this.position(i);
        return card.move(coords.x, coords.y, i);
      });
      return this;
    };

    Cell.prototype.teardownCard = function(id) {
      forget("" + id + ":destroyed", this.destroyHandlers[id]);
      return delete this.destroyHandlers[id];
    };

    Cell.prototype.teardown = function() {
      var card, _i, _len, _ref;

      _ref = this.models;
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        card = _ref[_i];
        this.teardownCard(card.id);
      }
      return this.models = [];
    };

    Cell.prototype.position = function(i) {
      var currentSize, halfheightdiff, heightdiff, x, y;

      currentSize = sizes.targetSizes[sizes.current];
      heightdiff = currentSize.height - currentSize.width;
      halfheightdiff = heightdiff / 2;
      x = (i * cardXOffset) + halfheightdiff + Cell.padding.left;
      y = (i * cardYOffset) + Cell.padding.top;
      return {
        x: x + this.x,
        y: y + this.y
      };
    };

    Cell.prototype.full = function() {
      return this.models.length >= 3;
    };

    Cell.prototype.next = function() {
      var _ref;

      return (_ref = this.collection) != null ? _ref.at(this.collection.indexOf(this) + 1) : void 0;
    };

    Cell.prototype.previous = function() {
      var _ref;

      return (_ref = this.collection) != null ? _ref.at(this.collection.indexOf(this) - 1) : void 0;
    };

    return Cell;

  })(Collection);
  Cell.width = function() {
    return gridSizes[sizes.current].width;
  };
  Cell.height = function() {
    return gridSizes[sizes.current].height;
  };
  Cell.padding = {
    top: 5,
    left: 5,
    right: 5,
    bottom: 20
  };
  for (size in sizes.targetSizes) {
    gridSizes[size] = {
      height: sizes.targetSizes[size].height + (Cell.padding.bottom + Cell.padding.top) + (2 * cardYOffset)
    };
    gridSizes[size].width = sizes.targetSizes[size].height + Cell.padding.left + Cell.padding.right + (2 * cardXOffset);
  }
  Cell.gridSizes = gridSizes;
  return Cell;
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('cell-collection',['collection', 'cell'], function(Collection, Cell) {
  var CellCollection;

  CellCollection = (function(_super) {
    __extends(CellCollection, _super);

    function CellCollection(options) {
      CellCollection.__super__.constructor.call(this);
      this.width = options.width;
      this.height = options.height;
      this.top = options.top;
      this.left = options.left;
      this.createCells();
      if (options.cards) {
        this.addCards(options.cards);
      }
      this;
    }

    CellCollection.prototype.addCards = function(cards) {
      var card, _i, _len;

      for (_i = 0, _len = cards.length; _i < _len; _i++) {
        card = cards[_i];
        this.addCard(card);
      }
      return this;
    };

    CellCollection.prototype.addCard = function(card) {
      var cell, existingName, fallback, firstEmptyCell, firstNotFullCell, lastEmptyCell, max, section, topCardTypes, _ref;

      topCardTypes = card.type.join('').match(/Creature|Planeswalker|Equipment|Sorcery|Instant/);
      this.removeCard(card);
      section = topCardTypes ? this.models : this.bottomRow();
      firstEmptyCell = section.find(function(cell) {
        return cell.empty();
      });
      lastEmptyCell = (_ref = section.filter(function(cell) {
        return cell.empty();
      })) != null ? _ref.last() : void 0;
      existingName = section.find(function(cell) {
        return !cell.full() && cell.pluck('name').include(card.name);
      });
      firstNotFullCell = section.find(function(cell) {
        return !cell.full();
      });
      max = section.pluck('models').pluck('length').max();
      fallback = section.find(function(cell) {
        return cell.models.length < max;
      }) || section.first();
      cell = false;
      if (topCardTypes) {
        cell = firstEmptyCell || existingName;
      } else {
        cell = existingName || (card.is("land") ? firstEmptyCell : lastEmptyCell);
      }
      (cell || firstNotFullCell || fallback).add(card);
      return this;
    };

    CellCollection.prototype.removeCard = function(card) {
      var cell, match, _i, _len, _ref;

      match = false;
      _ref = this.models;
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        cell = _ref[_i];
        match = cell.include(card) ? cell : false;
        if (match) {
          match.remove(card);
          break;
        }
      }
      return this;
    };

    CellCollection.prototype.createCells = function(options) {
      var coords, slotIndex, _i, _ref;

      if (options) {
        this.height = options.height;
        this.width = options.width;
      }
      this.teardown();
      for (slotIndex = _i = 0, _ref = this.maxCells(); 0 <= _ref ? _i < _ref : _i > _ref; slotIndex = 0 <= _ref ? ++_i : --_i) {
        coords = this.getCoordinates(slotIndex);
        this.add(new Cell({
          x: coords.x,
          y: coords.y,
          collection: this
        }));
      }
      return this;
    };

    CellCollection.prototype.teardown = function() {
      this.models.invoke('teardown');
      this.models = [];
      $(".guide").remove();
      return this;
    };

    CellCollection.prototype.findCellByCoords = function(x, y) {
      var cell, match, _i, _len, _ref;

      match = false;
      _ref = this.models;
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        cell = _ref[_i];
        if ((cell.x <= x && x < cell.x + Cell.width()) && (cell.y <= y && y < cell.y + Cell.height())) {
          match = cell;
          break;
        }
      }
      return match;
    };

    CellCollection.prototype.horizontalLimit = function() {
      return Math.ceil(this.maxCoords().x / Cell.width());
    };

    CellCollection.prototype.verticalLimit = function() {
      return Math.max(Math.ceil(this.maxCoords().y / Cell.height()), 2);
    };

    CellCollection.prototype.maxCells = function() {
      return this.horizontalLimit() * this.verticalLimit();
    };

    CellCollection.prototype.maxCoords = function() {
      return {
        x: this.width - Cell.width(),
        y: this.height - Cell.height()
      };
    };

    CellCollection.prototype.renderGuides = function() {
      var guide, guides, horizontalGuides, makeGuide, verticalGuides, _i, _len, _results,
        _this = this;

      $(".guide").remove();
      makeGuide = function(i, direction) {
        var properties;

        properties = {
          vertical: {
            left: "" + (((i + 1) * Cell.width()) + _this.left) + "px"
          },
          horizontal: {
            top: "" + (((i + 1) * Cell.height()) + _this.top) + "px"
          }
        };
        return $(document.createElement('div')).addClass("guide guide_" + direction).css(properties[direction]);
      };
      guides = [];
      horizontalGuides = 0;
      verticalGuides = 0;
      while (horizontalGuides < this.verticalLimit()) {
        guides.push(makeGuide(horizontalGuides, 'horizontal'));
        horizontalGuides += 1;
      }
      while (verticalGuides < this.horizontalLimit()) {
        guides.push(makeGuide(verticalGuides, 'vertical'));
        verticalGuides += 1;
      }
      _results = [];
      for (_i = 0, _len = guides.length; _i < _len; _i++) {
        guide = guides[_i];
        _results.push($('body').append(guide));
      }
      return _results;
    };

    CellCollection.prototype.getCoordinates = function(i) {
      var coords, horizontalLimit, n;

      coords = {
        x: 0,
        y: 0
      };
      if (i !== 0) {
        horizontalLimit = this.horizontalLimit();
        n = i;
        while (n >= horizontalLimit) {
          n -= horizontalLimit;
        }
        coords.x = Cell.width() * n;
        n = Math.floor(i * (1 / this.horizontalLimit()));
        coords.y = Cell.height() * n;
      }
      return coords;
    };

    CellCollection.prototype.bottomRow = function() {
      var firstCellIndexOfBottomRow;

      firstCellIndexOfBottomRow = this.maxCells() - this.horizontalLimit();
      return this.models.filter(function(cell, i) {
        return i >= firstCellIndexOfBottomRow;
      });
    };

    return CellCollection;

  })(Collection);
  return CellCollection;
});

define('grid',['cell-collection'], function(CellCollection) {
  var disable, enable, pub, render, _grid;

  pub = {};
  _grid = void 0;
  enable = function(options) {
    disable();
    _grid = new CellCollection(options);
    return pub;
  };
  disable = function() {
    if (_grid) {
      _grid.teardown();
      _grid = void 0;
    }
    return pub;
  };
  render = function() {
    if (_grid) {
      _grid.createCells();
    }
    return pub;
  };
  pub.get = function() {
    return _grid;
  };
  pub.render = render;
  pub.enable = enable;
  pub.disable = disable;
  return pub;
});

define('store',[],function() {
  var Store;

  return Store = (function() {
    var createCookie, getCookie, localStorageSupported, safeSet;

    localStorageSupported = (function() {
      var e;

      try {
        return (('localStorage' in window) && window['localStorage'] !== null);
      } catch (_error) {
        e = _error;
        return false;
      }
    })();
    if (localStorageSupported) {
      safeSet = function(key, value) {
        var e, num, _i;

        try {
          localStorage.setItem(key, value);
          return value;
        } catch (_error) {
          e = _error;
          for (num = _i = 0; _i <= 5; num = ++_i) {
            localStorage.removeItem(localStorage.key(localStorage.length - 1));
          }
          return safeSet(key, value);
        }
      };
      return {
        set: safeSet,
        get: function(key) {
          return localStorage[key];
        },
        expire: function(key) {
          var value;

          value = localStorage[key];
          localStorage.removeItem(key);
          return value;
        }
      };
    } else {
      createCookie = function(name, value, days) {
        var date, expires;

        if (days) {
          date = new Date;
          date.setTime(date.getTime() + (days * 24 * 60 * 60 * 1000));
          expires = "; expires=" + date.toGMTString();
        } else {
          expires = "";
        }
        document.cookie = name + "=" + value + expires + "; path=/";
        return value;
      };
      getCookie = function(key) {
        var cookieFragment, _i, _len, _ref;

        key = key + "=";
        _ref = document.cookie.split(';');
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          cookieFragment = _ref[_i];
          if (cookieFragment.indexOf(key) === 0) {
            return cookieFragment.replace(/^\s+/, '').substring(key.length, cookieFragment.length);
          }
        }
        return null;
      };
      return {
        set: function(key, value) {
          return createCookie(key, value, 1);
        },
        get: getCookie,
        expire: function(key) {
          var value;

          value = Store.get(key);
          createCookie(key, "", -1);
          return value;
        }
      };
    }
  })();
});

define('settings',['lib/zepto/zepto', 'event', 'button', 'detect', 'store', 'sizes'], function($, Event, Button, features, Store, sizes) {
  var Setting, SettingGroup, apply3dTransformsClass, restoreDefaults, settings, settingsAreChanged;

  Setting = (function() {
    function Setting(elementId, defaultValue, message) {
      var initialValue,
        _this = this;

      if (defaultValue == null) {
        defaultValue = true;
      }
      if (message == null) {
        message = false;
      }
      this.message = message;
      this.setting = elementId.lowerCamelCase();
      this.element = $("#" + elementId).get(0);
      if (!this.element) {
        return;
      }
      initialValue = Store.get(this.setting) != null ? JSON.parse(Store.get(this.setting)) : defaultValue;
      this.defaultValue = defaultValue;
      this.set(this.value = initialValue);
      if (features.handheld) {
        $(this.element).parent().on(Event.down, function() {
          if (_this.message && !confirm(_this.message)) {
            return false;
          } else {
            _this.set(_this.element.checked = !_this.element.checked);
          }
          return false;
        });
      }
      $(this.element).on('change', function(e) {
        if (_this.message && !confirm(_this.message)) {
          _this.element.checked = !_this.element.checked;
          return false;
        }
        return _this.set(_this.element.checked);
      });
      settings[this.setting] = this;
    }

    Setting.prototype.set = function(value) {
      Store.set(this.setting, this.element.checked = this.value = value);
      fire("setting:changed", {
        setting: this.setting,
        value: value
      });
      fire("" + this.setting + ":changed", {
        value: value
      });
      return this;
    };

    Setting.prototype.get = function() {
      return this.value;
    };

    Setting.prototype.enable = function() {
      return this.set(true);
    };

    Setting.prototype.disable = function() {
      return this.set(false);
    };

    Setting.prototype.revert = function() {
      return this.set(this.defaultValue);
    };

    return Setting;

  })();
  SettingGroup = (function() {
    function SettingGroup(name, defaultValue) {
      var initialValue,
        _this = this;

      this.setting = name;
      this.defaultValue = defaultValue;
      this.elements = $("input[type=radio][name=" + name + "]");
      if (!this.elements.length) {
        return;
      }
      this.set(initialValue = Store.get(this.setting) != null ? Store.get(this.setting) : defaultValue);
      settings[name] = this;
      $(this.elements).parent().on(Event.down, function(e) {
        return _this.set($(e.target).find('input').val());
      });
      $(this.elements).on('change', function(e) {
        if (e.target.checked) {
          return _this.set(e.target.value);
        }
      });
    }

    SettingGroup.prototype.set = function(value) {
      if (value !== null) {
        this.value = value;
        Store.set(this.setting, value);
        $("#" + value + "_" + this.setting).get(0).checked = true;
        fire("setting:changed", {
          setting: this.setting,
          value: value
        });
        fire("" + this.setting + ":changed", {
          value: value
        });
      }
      return this;
    };

    SettingGroup.prototype.get = function() {
      return $("input[type=radio][name=" + this.setting + "]:checked").val();
    };

    SettingGroup.prototype.revert = function() {
      return this.set(this.defaultValue);
    };

    return SettingGroup;

  })();
  settings = {};
  new Setting('auto_untap');
  new Setting('auto_draw');
  new Setting('3d_transforms_2', features.transforms_3d_a_grade, "You must refresh the browser for this change to work.");
  new SettingGroup('size', sizes.current, sizes.options);
  new Setting('auto_layout', true);
  restoreDefaults = function() {
    var setting, _results;

    _results = [];
    for (setting in settings) {
      _results.push(settings[setting].revert());
    }
    return _results;
  };
  after("restore:defaults", restoreDefaults);
  settingsAreChanged = function() {
    var defaultsChanged, setting, _setting;

    defaultsChanged = false;
    for (setting in settings) {
      _setting = settings[setting];
      if (_setting.get() !== _setting.defaultValue) {
        defaultsChanged = true;
        break;
      }
    }
    return defaultsChanged;
  };
  new Button("restore_defaults", {
    handler: restoreDefaults,
    control: {
      condition: settingsAreChanged,
      events: 'settings:shown setting:changed'
    }
  });
  apply3dTransformsClass = function() {
    var _ref;

    return h.toggleClass('enable_3d_transforms', (_ref = settings['3dTransforms2']) != null ? _ref.get() : void 0);
  };
  apply3dTransformsClass();
  after("3dTransforms2:changed", function() {
    return location.reload();
  });
  return settings;
});

define('get-setting',['settings'], function(settings) {
  return function(setting) {
    var _ref;

    return (_ref = settings[setting]) != null ? _ref.get() : void 0;
  };
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('battlefield-zone-view',['distributable-zone-view', 'cell', 'grid', 'get-setting', 'window-loaded'], function(DistributableZoneView, Cell, grid, getSetting, windowLoaded) {
  var BattlefieldZoneView, getGridOptions, wireUpGridToSettings;

  getGridOptions = function(view) {
    return {
      height: view.height,
      width: view.width,
      left: view.left,
      top: view.top,
      cards: view.model.cards
    };
  };
  wireUpGridToSettings = function(view) {
    return windowLoaded.then(function() {
      if (getSetting('autoLayout')) {
        grid.enable(getGridOptions(view));
      }
      after("size:changed", grid.render);
      return after("autoLayout:changed", function() {
        if (getSetting('autoLayout')) {
          return grid.enable(getGridOptions(view));
        } else {
          return grid.disable();
        }
      });
    });
  };
  BattlefieldZoneView = (function(_super) {
    __extends(BattlefieldZoneView, _super);

    function BattlefieldZoneView(model) {
      BattlefieldZoneView.__super__.constructor.call(this, model);
      wireUpGridToSettings(this);
      this;
    }

    BattlefieldZoneView.prototype.cacheDimensions = function() {
      var previous,
        _this = this;

      previous = {
        width: this.width,
        height: this.height
      };
      return BattlefieldZoneView.__super__.cacheDimensions.call(this).then(function() {
        if (getSetting('autoLayout')) {
          return grid.enable(getGridOptions(_this));
        }
      });
    };

    BattlefieldZoneView.prototype.distributeCards = function() {};

    BattlefieldZoneView.prototype.restingZ = function(card) {
      return card.calculateZ();
    };

    return BattlefieldZoneView;

  })(DistributableZoneView);
  return BattlefieldZoneView;
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('hand',['time', 'alias', 'zepto', 'distributable-zone-view', 'detect', 'sizes'], function(time, alias, $, DistributableZoneView, features, sizes) {
  var HandView;

  HandView = (function(_super) {
    __extends(HandView, _super);

    function HandView(model) {
      var boundHandler,
        _this = this;

      HandView.__super__.constructor.call(this, model);
      boundHandler = function() {
        return _this.delayedDistributeCards();
      };
      $(window).on('resize orientationchange', boundHandler);
      after('size:changed', boundHandler);
      if (!features.handheld) {
        this.$element.doubleclick(function(e) {
          var cardElement, _ref;

          cardElement = (_ref = $(e.target).closest('.card')) != null ? _ref[0] : void 0;
          if (cardElement) {
            return _this.model.cards.filter(function(card) {
              return card.view().$element.get(0) === cardElement;
            }).first().battlefield();
          }
        });
      }
    }

    HandView.prototype.distributeCards = function() {
      var card, cardIndex, needsToUseOffset, offset, totalOffset, x, y, z, _i, _ref,
        _this = this;

      offset = 0;
      needsToUseOffset = this.width < sizes.cardWidth() * this.model.size();
      if (needsToUseOffset) {
        totalOffset = this.$element.get(0).clientWidth - (sizes.cardWidth() * this.model.size());
        offset = (totalOffset / (this.model.size() - 1)) * -1;
      }
      for (cardIndex = _i = 0, _ref = this.model.size(); 0 <= _ref ? _i < _ref : _i > _ref; cardIndex = 0 <= _ref ? ++_i : --_i) {
        card = this.model.cards[cardIndex];
        x = (sizes.cardWidth() - offset) * cardIndex;
        card.restingY = y = this.margin;
        card.r = 0;
        z = card.z >= 200 ? card.z : this.restingZ(card);
        card.move(x, y, z);
        if (z >= 200) {
          (function(card) {
            var _card;

            _card = card;
            return time.wait(300, function() {
              return _card.move(null, null, _this.restingZ(_card));
            });
          })(card);
        }
      }
      return false;
    };

    HandView.prototype.restingZ = function(card) {
      var i;

      i = this.model.cards.indexOf(card);
      return i + 1;
    };

    return HandView;

  })(DistributableZoneView);
  return HandView;
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('library',['event', 'distributable-zone-view', 'zepto', 'draw'], function(Event, DistributableZoneView, $, draw) {
  var LibraryView;

  LibraryView = (function(_super) {
    __extends(LibraryView, _super);

    function LibraryView(model) {
      var clickToDraw,
        _this = this;

      LibraryView.__super__.constructor.call(this, model);
      clickToDraw = function(e) {
        if (!popup.visible && e.target.className.match(/card|back/) || e.target.id === _this.model.name) {
          if (!_this.model.last().recentlyDragged) {
            draw();
            return e.preventDefault();
          }
        }
      };
      this.$element.on('click', clickToDraw);
      after('library:shuffled', function() {
        return _this.shuffle();
      });
    }

    LibraryView.prototype.shuffle = function() {
      if (!this.model.cards.empty()) {
        if (this.model.cards.first().view()) {
          this.model.cards.invoke('view').invoke('attach');
          this.render();
          this.renderLastVisibleCards();
        }
      }
      return this;
    };

    return LibraryView;

  })(DistributableZoneView);
  return LibraryView;
});

define('zone-views',['zone-models', 'distributable-zone-view', 'battlefield-zone-view', 'hand', 'library'], function(zones, DistributableZoneView, BattlefieldZoneView, HandView, LibraryView) {
  var zoneViews;

  zoneViews = {
    library: new LibraryView(zones.library),
    hand: new HandView(zones.hand),
    battlefield: new BattlefieldZoneView(zones.battlefield),
    graveyard: new DistributableZoneView(zones.graveyard),
    exiled: new DistributableZoneView(zones.exiled)
  };
  return zoneViews;
});

define('are-you-sure',[],function() {
  var areYouSure;

  areYouSure = function(message, proceed) {
    if (confirm("Are you sure " + message)) {
      return proceed();
    }
  };
  return areYouSure;
});

define('mulligan',['event', 'draw', 'are-you-sure', 'library-model', 'hand-model'], function(Event, draw, areYouSure, library, hand) {
  var mulligan, mulligans;

  mulligans = 0;
  mulligan = function() {
    return areYouSure("you want to mulligan?", function() {
      mulligans = mulligans === 6 ? 6 : mulligans + 1;
      fire("mulligan", {
        mulligans: mulligans
      });
      while (!hand.empty()) {
        hand.first().library();
      }
      library.shuffle();
      return defer(function() {
        return draw(7 - mulligans);
      });
    });
  };
  return mulligan;
});

define('zone-initialize',['lib/zepto/zepto', 'zone-models', 'zone-views', 'get-active-card', 'mulligan', 'are-you-sure'], function($, zones, zoneViews, getActiveCard, mulligan, areYouSure) {
  var battlefield, bindRenderToggleHand, exiled, graveyard, hand, library, renderToggleHandLink, toggleHand, toggleHandLink;

  library = zones.library;
  hand = zones.hand;
  battlefield = zones.battlefield;
  graveyard = zones.graveyard;
  exiled = zones.exiled;
  onQuickClick("#untap_link", function() {
    return battlefield.untap();
  });
  after("u:pressed", function() {
    return battlefield.untap();
  });
  toggleHandLink = $("#toggle_hand_visibility_link");
  toggleHand = function() {
    var flippingCards, method;

    flippingCards = hand.cards.findAll(function(card) {
      return card.flipping;
    });
    if (flippingCards.length > 0) {
      return false;
    }
    method = hand.hidden() ? 'faceup' : 'facedown';
    hand.cards.invoke(method);
    return renderToggleHandLink();
  };
  renderToggleHandLink = function() {
    var text;

    text = hand.hidden() ? "Show Hand" : "Hide Hand";
    if (text !== toggleHandLink.text()) {
      return toggleHandLink.text(text);
    }
  };
  bindRenderToggleHand = function(event, method) {
    return after(event, function(e) {
      var card;

      card = e.data.card;
      renderToggleHandLink();
      return w[method]("" + card.id + ":facedown " + card.id + ":faceup", renderToggleHandLink);
    });
  };
  bindRenderToggleHand("onhand", "after");
  bindRenderToggleHand("onleavehand", "forget");
  after("h:pressed", toggleHand);
  onQuickClick(toggleHandLink, toggleHand);
  onQuickClick("#mulligan", mulligan);
  after("m:pressed", mulligan);
  onQuickClick("#restart", function() {
    return areYouSure("you want to restart?", function() {
      return location.reload();
    });
  });
  onQuickClick("#shuffle_library", function() {
    return library.shuffle();
  });
  after("s:pressed", function() {
    return library.shuffle();
  });
  after("Y:pressed", function() {
    var card;

    card = getActiveCard();
    if (card.can('library')) {
      return library.addToBottom(card);
    }
  });
  return {
    zones: zones,
    zoneViews: zoneViews
  };
});

define('draganddrop',['event', 'zepto', 'zone-initialize', 'detect', 'sizes', 'get-focused-field'], function(Event, $, zoneInstances, features, sizes, getFocusedField) {
  var battlefield, calculateOffset, dnd, drag, getReorderingIndex, hand, releaseElement, setupDrag, updateTargetZone, zoneViews;

  hand = zoneInstances.zones.hand;
  battlefield = zoneInstances.zones.battlefield;
  zoneViews = zoneInstances.zoneViews;
  dnd = {
    dragged: false
  };
  calculateOffset = function(e, card) {
    return {
      x: e.clientX - card.x,
      y: e.clientY - card.y
    };
  };
  dnd.startDrag = function(e, card) {
    var _this = this;

    if (dnd.dragWithCard === void 0) {
      dnd.dragWithCard = function(e) {
        return drag((features.handheld ? e.targetTouches[0] : e), card);
      };
      return $(document).on(Event.move, dnd.dragWithCard).on(Event.up, dnd.tearDown);
    }
  };
  dnd.tearDown = function() {
    $(document).off(Event.move, dnd.dragWithCard).off(Event.up, dnd.tearDown);
    return dnd.dragWithCard = void 0;
  };
  dnd.draggedCard = dnd.targetZone = dnd.dragWithCard = void 0;
  setupDrag = function(e, card) {
    var offset;

    dnd.dragged = true;
    if (getFocusedField()) {
      $(getFocusedField()).blur().trigger('blur');
    }
    card.view().unbindToMouseOver();
    if (dnd.draggedCard) {
      releaseElement();
    }
    card.view().detach();
    dnd.draggedCard = card;
    card.view().$element.addClass('dragging');
    updateTargetZone(e);
    offset = calculateOffset(e, card);
    dnd.initialOffsetX = offset.x;
    dnd.initialOffsetY = offset.y;
    return $(document).on(Event.up, releaseElement);
  };
  releaseElement = function(e) {
    var card, cardView, method, newIndex, newX, newY, zone, zoneView, _ref;

    card = dnd.draggedCard;
    cardView = card.view();
    zone = card.zone();
    zoneView = zone.view();
    if (((_ref = e.changedTouches) != null ? _ref.length : void 0) > 0) {
      e = e.changedTouches[0];
    }
    updateTargetZone(e);
    newX = e.clientX - zoneViews[dnd.targetZone.id].left - dnd.initialOffsetX;
    newY = e.clientY - zoneViews[dnd.targetZone.id].top - dnd.initialOffsetY;
    card.move(newX, newY);
    if (dnd.targetZone === zone) {
      method = zone === battlefield ? 'attach' : 'revert';
      if (zone === hand && method === 'revert') {
        cardView.attach();
        card.move(null, null, mtg.Z.FLOATING);
        newIndex = getReorderingIndex(card, e);
        zone.add(card, newIndex);
      } else {
        cardView[method](e);
      }
    } else {
      card[dnd.targetZone.id]();
      if (dnd.targetZone === hand && hand.include(card)) {
        newIndex = getReorderingIndex(card, e);
        dnd.targetZone.add(card, newIndex);
      }
    }
    cardView.$element.removeClass('dragging');
    $('.zone').removeClass('hover');
    cardView.bindToMouseOver();
    $(document).off(Event.up, releaseElement);
    card.recentlyDragged = true;
    wait(20, (function() {
      var c;

      c = dnd.draggedCard;
      return function() {
        return c.recentlyDragged = false;
      };
    })());
    dnd.draggedCard = void 0;
    return dnd.dragged = false;
  };
  getReorderingIndex = function(card, e) {
    var i, index, l, lefts, tweakedCursorX;

    lefts = hand.cards.pluck('x').without(card.x).map(function(x) {
      return x + (sizes.cardWidth() / 2);
    });
    tweakedCursorX = e.clientX - hand.view().left;
    index = false;
    l = lefts.length - 1;
    if (tweakedCursorX <= lefts[0]) {
      index = 0;
    } else if (tweakedCursorX >= lefts.last()) {
      index = l + 1;
    }
    if (index === false) {
      i = 1;
      while (i <= l && index === false) {
        if ((lefts[i - 1] <= tweakedCursorX && tweakedCursorX <= lefts[i])) {
          index = i;
        }
        i += 1;
      }
    }
    return index;
  };
  updateTargetZone = function(e) {
    var zoneName, zoneView, _ref, _ref1, _results;

    _results = [];
    for (zoneName in zoneViews) {
      zoneView = zoneViews[zoneName];
      if (dnd.targetZone !== zoneView.model) {
        if ((zoneView.left + zoneView.width > (_ref = e.clientX) && _ref > zoneView.left) && (zoneView.top + zoneView.height > (_ref1 = e.clientY) && _ref1 > zoneView.top)) {
          dnd.targetZone = zoneView.model;
          if (!features.handheld) {
            $('.zone').removeClass('hover');
          }
          if (zoneView.model !== battlefield) {
            _results.push(zoneView.$element.addClass('hover'));
          } else {
            _results.push(void 0);
          }
        } else {
          _results.push(void 0);
        }
      } else {
        _results.push(void 0);
      }
    }
    return _results;
  };
  drag = function(e, card) {
    var _x, _y;

    if (!dnd.dragged) {
      setupDrag(e, card);
    }
    updateTargetZone(e);
    _x = e.clientX - dnd.initialOffsetX;
    _y = e.clientY - dnd.initialOffsetY;
    return dnd.draggedCard.move(_x, _y);
  };
  return dnd;
});

define('card-state-helpers',[],function() {
  var rotate, setCard, unrotate;

  rotate = function() {
    return this.card.r += this.deg;
  };
  unrotate = function() {
    return this.card.r -= this.deg;
  };
  setCard = function(card) {
    this.card = card;
    return this;
  };
  return {
    rotate: rotate,
    unrotate: unrotate,
    setCard: setCard
  };
});

define('card-tap-state',['state-machine', 'card-state-helpers'], function(StateMachine, helpers) {
  var TapState, _class, _ref;

  TapState = (function() {
    function TapState() {
      _ref = _class.apply(this, arguments);
      return _ref;
    }

    _class = helpers.setCard;

    TapState.prototype.deg = 90;

    TapState.prototype.ontap = helpers.rotate;

    TapState.prototype.onuntap = helpers.unrotate;

    TapState.prototype.ontapped = function() {
      if (this.card) {
        return fire("" + this.card.id + ":tapped");
      }
    };

    TapState.prototype.onuntapped = function() {
      if (this.card) {
        return fire("" + this.card.id + ":untapped");
      }
    };

    return TapState;

  })();
  StateMachine.create({
    target: TapState.prototype,
    initial: 'untapped',
    events: [
      {
        name: 'tap',
        from: 'untapped',
        to: 'tapped'
      }, {
        name: 'untap',
        from: 'tapped',
        to: 'untapped'
      }
    ]
  });
  return TapState;
});

define('card-flip-state',['state-machine', 'card-state-helpers'], function(StateMachine, helpers) {
  var FlipState, _class, _ref;

  FlipState = (function() {
    function FlipState() {
      _ref = _class.apply(this, arguments);
      return _ref;
    }

    _class = helpers.setCard;

    FlipState.prototype.deg = 180;

    FlipState.prototype.onflip = helpers.rotate;

    FlipState.prototype.onunflip = helpers.unrotate;

    FlipState.prototype.onflipped = function() {
      if (this.card) {
        return fire("" + this.card.id + ":flipped");
      }
    };

    FlipState.prototype.onunflipped = function() {
      if (this.card) {
        return fire("" + this.card.id + ":unflipped");
      }
    };

    return FlipState;

  })();
  StateMachine.create({
    target: FlipState.prototype,
    initial: 'unflipped',
    events: [
      {
        name: 'flip',
        from: 'unflipped',
        to: 'flipped'
      }, {
        name: 'unflip',
        from: 'flipped',
        to: 'unflipped'
      }
    ]
  });
  return FlipState;
});

define('card-face-state',['state-machine'], function(StateMachine) {
  var FaceState;

  FaceState = (function() {
    function FaceState(card) {
      this.card = card;
      this.dofacedown();
    }

    FaceState.prototype.onfacedown = function() {
      return fire("" + this.card.id + ":facedown");
    };

    FaceState.prototype.onfaceup = function() {
      return fire("" + this.card.id + ":faceup");
    };

    return FaceState;

  })();
  StateMachine.create({
    target: FaceState.prototype,
    events: [
      {
        name: 'dofacedown',
        from: ['faceup', 'none'],
        to: 'facedown'
      }, {
        name: 'dofaceup',
        from: 'facedown',
        to: 'faceup'
      }
    ]
  });
  return FaceState;
});

define('card-transform-state',['state-machine', 'card-state-helpers'], function(StateMachine, helpers) {
  var TransformState, _class, _ref;

  TransformState = (function() {
    function TransformState() {
      _ref = _class.apply(this, arguments);
      return _ref;
    }

    _class = helpers.setCard;

    TransformState.prototype.ontransform = function() {
      this.card.copyProperties('transformation').facedown();
      return fire("" + this.card.id + ":transformed");
    };

    TransformState.prototype.onuntransform = function() {
      this.card.copyProperties('data').faceup();
      return fire("" + this.card.id + ":untransformed");
    };

    return TransformState;

  })();
  StateMachine.create({
    target: TransformState.prototype,
    initial: 'default',
    events: [
      {
        name: 'untransform',
        from: 'transformed',
        to: 'default'
      }, {
        name: 'transform',
        from: 'default',
        to: 'transformed'
      }
    ]
  });
  return TransformState;
});

define('card-zone-state',['state-machine', 'card-state-helpers', 'zone-names'], function(StateMachine, helpers, ZONE_NAMES) {
  var PRECOMPILED_ZONE_EVENT_NAMES, ZoneState;

  PRECOMPILED_ZONE_EVENT_NAMES = [];
  ZONE_NAMES.forEach(function(name) {
    return ["onbefore", "onleave", "onenter", "on"].forEach(function(prefix) {
      return PRECOMPILED_ZONE_EVENT_NAMES.push(prefix + name);
    });
  });
  ZoneState = (function() {
    function ZoneState(card) {
      var _this = this;

      this.card = card;
      PRECOMPILED_ZONE_EVENT_NAMES.forEach(function(name) {
        return _this[name] = function(event, from, to) {
          var data;

          data = {
            card: _this.card,
            event: event,
            from: from,
            to: to
          };
          fire(name, data);
          return fire("" + _this.card.id + ":" + name, data);
        };
      });
      if (!w.jasmine) {
        this.onleavenone = function() {
          return StateMachine.ASYNC;
        };
      }
      this[this.card.initialZone]();
      return this;
    }

    return ZoneState;

  })();
  StateMachine.create({
    target: ZoneState.prototype,
    events: (function() {
      var zoneNames;

      zoneNames = ZONE_NAMES.copy();
      zoneNames.push('none');
      return zoneNames.map(function(name) {
        var _zoneName;

        return {
          name: name,
          to: name,
          from: (function() {
            var _i, _len, _results;

            _results = [];
            for (_i = 0, _len = zoneNames.length; _i < _len; _i++) {
              _zoneName = zoneNames[_i];
              if (_zoneName !== name) {
                _results.push(_zoneName);
              } else {
                _results.push(void 0);
              }
            }
            return _results;
          })()
        };
      });
    })()
  });
  return ZoneState;
});

var __slice = [].slice;

define('card-model',['zone-names', 'zone-initialize', 'string', 'draganddrop', 'sizes', 'detect', 'card-model-string-helpers', 'grid', 'card-tap-state', 'card-flip-state', 'card-face-state', 'card-transform-state', 'card-zone-state', 'card-views', 'mtg', 'loaded'], function(ZONE_NAMES, zoneInstances, String, dnd, sizes, features, cardModelHelpers, grid, TapState, FlipState, FaceState, TransformState, ZoneState, cardViews, mtg, loaded) {
  var CardModel, action, battlefield, buildStateAction, hand, zones;

  zones = zoneInstances.zones;
  hand = zones.hand;
  battlefield = zones.battlefield;
  CardModel = (function() {
    function CardModel(data) {
      var segment, type, typeCopy, _i, _j, _len, _len1, _ref, _ref1, _ref2, _ref3, _ref4, _ref5, _ref6, _ref7,
        _this = this;

      this.p = this.t = this.c = 0;
      $.extend(this, data);
      this.data = data;
      if ((_ref = this.id) == null) {
        this.id = cardModelHelpers.formatIdString(this.name, this.n);
      }
      this.transformed = false;
      this.isTransformable = 'transformation' in data;
      this.r = this.x = this.y = this.z = 0;
      this.events = [];
      this.isCreature = !!data.p;
      this.isPlainswalker = !!data.c;
      if ((_ref1 = this.isCommander) == null) {
        this.isCommander = false;
      }
      if (this.type) {
        typeCopy = [];
        _ref2 = this.type;
        for (_i = 0, _len = _ref2.length; _i < _len; _i++) {
          type = _ref2[_i];
          if (type === 'Basic Land') {
            typeCopy.push('Land');
          } else if (type.include(' ')) {
            _ref3 = type.split(' ');
            for (_j = 0, _len1 = _ref3.length; _j < _len1; _j++) {
              segment = _ref3[_j];
              typeCopy.push(segment);
            }
          } else {
            typeCopy.push(type);
          }
        }
        this.type = typeCopy;
      }
      if (!this.type) {
        this.type = [];
        if (this.isCreature) {
          this.type.push('Creature');
        }
        if (this.isPlaneswalker) {
          this.type.push('Planeswalker');
        }
      }
      if ((_ref4 = this.pMod) == null) {
        this.pMod = 0;
      }
      if ((_ref5 = this.tMod) == null) {
        this.tMod = 0;
      }
      if ((_ref6 = this.cMod) == null) {
        this.cMod = 0;
      }
      this.tapState = new TapState(this);
      this.flipState = new FlipState(this);
      this.faceState = new FaceState(this);
      if (this.isTransformable) {
        this.transformState = new TransformState(this);
      }
      if ((_ref7 = this.initialZone) == null) {
        this.initialZone = 'library';
      }
      this.zoneState = new ZoneState(this);
      loaded.then(function() {
        return _this.after("" + _this.id + ":onhand " + _this.id + ":onbattlefield " + _this.id + ":onlibrary " + _this.id + ":onexiled " + _this.id + ":ongraveyard", function() {
          var view, x, y;

          view = _this.zone().view();
          if (view && _this !== dnd.draggedCard) {
            x = _this.x - view.left;
            y = _this.y - view.top;
          }
          return _this.move(x, y, _this.calculateZ());
        });
      });
      this.after("" + this.id + ":onbattlefield", function() {
        var dragged;

        _this.faceup();
        dragged = !!(function() {
          return dnd.draggedCard;
        })();
        if (battlefield.view()) {
          defer(function() {
            if (grid.get()) {
              return grid.get().addCard(_this);
            } else {
              if (!dragged) {
                return _this.move(null, 5);
              }
            }
          });
        }
        return _this;
      });
      this.after("" + this.id + ":onleavebattlefield", function() {
        var _ref8;

        if ((_ref8 = grid.get()) != null) {
          _ref8.removeCard(_this);
        }
        _this.untap().unflip().revertNoteValues();
        if (_this.transformed) {
          _this.transform();
        }
        return _this;
      });
      loaded.then(function() {
        return _this.after("" + _this.id + ":onleavehand " + _this.id + ":onleavebattlefield " + _this.id + ":onleavelibrary " + _this.id + ":onleaveexiled " + _this.id + ":onleavegraveyard", function() {
          var x, y, zone, zoneView, zoneViewHasDimensions;

          zone = _this.zone();
          zoneView = zone != null ? zone.view() : void 0;
          zoneViewHasDimensions = zoneView && (zoneView.left != null) && (zoneView.top != null);
          if (zone && zoneView) {
            if (zoneViewHasDimensions && dnd.draggedCard !== _this) {
              x = _this.x + zoneView.left;
              y = _this.y + zoneView.top;
              _this.move(x, y, mtg.Z.FLOATING);
            }
          }
          return _this;
        });
      });
      this.after("" + this.id + ":onhand", function() {
        if (!hand.hidden() || (hand.size() === 1 && hand.first() === _this)) {
          _this.faceup();
        }
        return _this;
      });
      this.after("" + this.id + ":ongraveyard", function() {
        return _this.faceup();
      });
      this.after("" + this.id + ":onexiled", function() {
        return _this.faceup();
      });
      this.after("" + this.id + ":onlibrary", function() {
        return _this.facedown();
      });
      this.boundRewritePath = function() {
        var sizesRegexp;

        sizesRegexp = /small\.|medium\.|large\./;
        if (_this.path.match(sizesRegexp)) {
          _this.path = _this.path.replace(sizesRegexp, "" + sizes.tappedoutSizes[features.retina ? 'large' : sizes.current] + ".");
          fire("" + _this.id + ":path:changed", _this);
        }
        return _this;
      };
      this.after("size:changed", this.boundRewritePath);
    }

    CardModel.prototype.move = function(x, y, z) {
      if (x != null) {
        this.x = x;
      }
      if (y != null) {
        this.y = y;
      }
      if (z != null) {
        this.z = z;
      }
      fire("" + this.id + ":moved", this);
      return this;
    };

    CardModel.prototype.mod = function(property, value) {
      var M;

      M = property.toUpperCase();
      if (0 > this[property] + value) {
        value = 0;
      }
      this["" + property + "Mod"] += value;
      this[M](this[property] + value);
      return this;
    };

    CardModel.prototype.plus = function(property, value) {
      this.mod(property, value);
      return this;
    };

    CardModel.prototype.minus = function(property, value) {
      this.mod(property, value * -1);
      return this;
    };

    CardModel.prototype.destroy = function() {
      var _this = this;

      this.zoneState.none();
      this.events.forEach(function(e) {
        return _this.forget(e);
      });
      fire("" + this.id + ":destroyed");
      return this;
    };

    CardModel.prototype.after = function(events, callback) {
      if (!this.events.include(events)) {
        this.events.push(events);
      }
      after(events, callback);
      return this;
    };

    CardModel.prototype.forget = function(events, callback) {
      if (callback == null) {
        callback = false;
      }
      this.events.without(events);
      forget(events, callback);
      return this;
    };

    CardModel.prototype.zone = function() {
      return zones[this.zoneState.current];
    };

    CardModel.prototype.view = function() {
      return require('card-views')[this.id];
    };

    CardModel.prototype.revertNoteValues = function() {
      this.P(this.data.p);
      this.T(this.data.t);
      this.C(this.data.c);
      this.pMod = this.tMod = this.cMod = 0;
      return this;
    };

    CardModel.prototype.hasNotes = function() {
      return this.t > 0 || this.c > 0;
    };

    CardModel.prototype.serialize = function() {
      var obj, _ref;

      obj = {
        name: this.name,
        id: this.id,
        p: this.p,
        t: this.t,
        pMod: this.pMod,
        tMod: this.tMod,
        r: this.r,
        x: this.x,
        y: this.y,
        z: this.z,
        states: [this.tapState.current, (_ref = this.transformState) != null ? _ref.current : void 0, this.flipState.current, this.faceState.current, this.zoneState.current]
      };
      return JSON.stringify(obj);
    };

    CardModel.prototype.update = function(json) {
      var method, parsed;

      parsed = JSON.parse(json);
      this.name = parsed.name;
      this.id = parsed.id;
      this.p = parsed.p;
      this.t = parsed.t;
      this.pMod = parsed.pMod;
      this.tMod = parsed.tMod;
      this.r = parsed.r;
      this.x = parsed.x;
      this.y = parsed.y;
      this.z = parsed.z;
      this.zoneState[parsed.states.last()]();
      method = parsed.states[0].without('ped');
      if (this.can(method)) {
        this[method]();
      }
      if (parsed.states[1] && (this.transformState != null)) {
        method = parsed.states[1] === 'transformed' ? 'transform' : 'untransform';
        this.transformState[method]();
      }
      method = parsed.states[2].without('ped');
      if (this.can(method)) {
        this[method]();
      }
      method = parsed.states[3];
      if (this.can(method)) {
        return this[method]();
      }
    };

    CardModel.prototype.transform = function() {
      if (this.can('transform')) {
        if (this.transformState.is('default')) {
          this.transformState.transform();
          this.transformed = true;
        } else {
          this.transformState.untransform();
          this.transformed = false;
        }
      }
      return this;
    };

    CardModel.prototype.copyProperties = function(from) {
      this.P(this[from].p + this.pMod, true);
      this.T(this[from].t + this.tMod, true);
      this.name = this[from].name;
      return this;
    };

    CardModel.prototype.is = function() {
      var type, types;

      type = arguments[0], types = 2 <= arguments.length ? __slice.call(arguments, 1) : [];
      types || (types = [type]);
      if (!types.include(type)) {
        types.push(type);
      }
      types = types.map(function(t) {
        return t.toLowerCase();
      });
      return this.type.filter(function(t) {
        return types.include(t.toLowerCase());
      }).length === types.length;
    };

    return CardModel;

  })();
  "r x y z".split(' ').forEach(function(c) {
    return CardModel.prototype[c.toUpperCase()] = function(v) {
      if (v !== null && typeof v === 'number') {
        this[c] = v;
        fire("" + c + ":changed", this);
        fire("" + this.id + ":" + c + ":changed", this);
      }
      return this[c];
    };
  });
  "p t c".split(' ').forEach(function(c) {
    return CardModel.prototype[c.toUpperCase()] = function(v, dontCalcMod) {
      if (v !== null && typeof v === 'number') {
        this[c] = v;
        fire("" + c + ":changed", this);
        fire("" + this.id + ":" + c + ":changed", this);
      }
      return this[c];
    };
  });
  buildStateAction = function(state, action) {
    return CardModel.prototype[action] = function() {
      if (this.can(action)) {
        this[state][action]();
      }
      return this;
    };
  };
  ['tap', 'flip'].forEach(function(action) {
    var unaction;

    unaction = "un" + action;
    buildStateAction("" + action + "State", action);
    buildStateAction("" + action + "State", unaction);
    return CardModel.prototype["toggle" + (action.capitalize()) + "ped"] = function() {
      var method;

      method = this.can(action) ? action : unaction;
      return this[method]();
    };
  });
  CardModel.prototype.conditions = {
    tap: function() {
      return this.zone() === battlefield && this.tapState.can('tap');
    },
    untap: function() {
      return this.tapState.can('untap');
    },
    flip: function() {
      return this.zone() === battlefield && this.flipState.can('flip');
    },
    unflip: function() {
      return this.flipState.can('unflip');
    },
    faceup: function() {
      return this.faceState.can('dofaceup');
    },
    facedown: function() {
      return this.faceState.can('dofacedown');
    },
    commander: function() {
      return this.isCommander && this.zoneState.can('commander');
    },
    transform: function() {
      return this.isTransformable && this.zone() === battlefield;
    }
  };
  ZONE_NAMES.forEach(function(zoneName) {
    var _base, _ref;

    buildStateAction("zoneState", zoneName);
    return (_ref = (_base = CardModel.prototype.conditions)[zoneName]) != null ? _ref : _base[zoneName] = function() {
      return this.zoneState.can(zoneName);
    };
  });
  CardModel.actions = [];
  for (action in CardModel.prototype.conditions) {
    CardModel.actions.push(action);
  }
  CardModel.prototype.capabilities = function() {
    var _this = this;

    return CardModel.actions.filter(function(action) {
      return _this.can(action);
    });
  };
  CardModel.prototype.can = function(action) {
    return this.conditions[action].call(this);
  };
  CardModel.prototype.cannot = function(action) {
    return !this.can(action);
  };
  CardModel.prototype.facedown = function() {
    if (this.can('facedown')) {
      this.faceState.dofacedown();
    }
    return this;
  };
  CardModel.prototype.faceup = function() {
    if (this.can('faceup')) {
      this.faceState.dofaceup();
    }
    return this;
  };
  CardModel.prototype.toggleFace = function() {
    var method;

    method = this.can('faceup') ? 'faceup' : 'facedown';
    return this[method]();
  };
  CardModel.detectIntersection = function(a, b) {
    var bottom, left, right, top, _ref, _ref1, _ref2, _ref3;

    left = (b.x <= (_ref = a.x) && _ref <= b.x + sizes.cardWidth());
    top = (b.y <= (_ref1 = a.y) && _ref1 <= b.y + sizes.cardHeight());
    right = (b.x <= (_ref2 = a.x + sizes.cardWidth()) && _ref2 <= b.x + sizes.cardWidth());
    bottom = (b.y <= (_ref3 = a.y + sizes.cardHeight()) && _ref3 <= b.y + sizes.cardHeight());
    return left && top || right && top || right && bottom || left && bottom;
  };
  CardModel.prototype.calculateZ = function() {
    var intersecting;

    intersecting = this.intersecting();
    return intersecting.length + 1;
  };
  CardModel.prototype.intersecting = function(recurse) {
    var card, cards, intersection, _i, _len;

    intersection = recurse || [];
    cards = this.zone().cards;
    for (_i = 0, _len = cards.length; _i < _len; _i++) {
      card = cards[_i];
      if (!intersection.include(card)) {
        if (this !== card && CardModel.detectIntersection(this, card)) {
          intersection.push(card);
          card.intersecting(intersection);
        }
      }
    }
    if (!recurse) {
      intersection.splice(intersection.indexOf(this), 1);
    }
    return intersection;
  };
  CardModel.prototype.cleanupZ = function() {
    var z;

    z = this.z;
    this.intersecting().forEach(function(c) {
      if (c.z > z) {
        return c.move(null, null, c.z - 1);
      }
    });
    return this;
  };
  return CardModel;
});

define('element',[],function() {
  return function(tag, attributes) {
    var attribute, el;

    el = document.createElement(tag);
    for (attribute in attributes) {
      el[attribute] = attributes[attribute];
    }
    return el;
  };
});

define('css',['zepto', 'globals', 'get-setting'], function($, globals, getSetting) {
  var css;

  return css = {
    getTransformProperty: (function() {
      var b, p, properties, _i, _len;

      properties = ['transform', 'WebkitTransform', 'MozTransform'];
      b = w.b.get(0);
      for (_i = 0, _len = properties.length; _i < _len; _i++) {
        p = properties[_i];
        if (b.style[p] != null) {
          return p;
        }
      }
    })(),
    transform: function(element, x, y, r, z, scale) {
      var $element, newTransform;

      $element = $(element);
      element = $element.get(0);
      if (getSetting('3dTransforms2')) {
        newTransform = " translate3d(" + x + "px, " + y + "px, " + z + "px)";
        element.style[css.getTransformProperty] = newTransform;
      } else {
        $element.css({
          zIndex: z,
          left: x + "px",
          top: y + "px"
        });
      }
      return element;
    }
  };
});

define('card-view',['require', 'zepto', 'event', 'element', 'zone-models', 'css', 'draganddrop', 'string', 'sizes', 'grid', 'get-setting', 'card-dimensions', 'popup', 'deck-loaded'], function(require, $, Event, element, zones, css, dnd, String, sizes, grid, getSetting, cardDimensions, popup, deckLoaded) {
  var CardView, battlefield, library, mtg;

  library = zones.library;
  battlefield = zones.battlefield;
  mtg = require('mtg');
  CardView = (function() {
    function CardView(model) {
      var boundToggleTapped, downEvent,
        _this = this;

      this.model = model;
      this.invokingAfterAWhile = this.pressed = false;
      this.id = this.model.id;
      this.$element = $(element('div', {
        className: 'card',
        id: this.id
      }));
      this.render();
      if (cardDimensions[this.model.name]) {
        this.setImageDimensions();
      }
      after("" + (this.model.name.without(' ')) + ":dimensions:loaded", function(e) {
        return _this.setImageDimensions(e.data);
      });
      wait(100, function() {
        return after("size:changed", function() {
          _this.setImageDimensions();
          return _this.renderBackImageSrc();
        });
      });
      after("" + this.model.id + ":path:changed", function(e) {
        return _this.renderImageSrc(e.data.path);
      });
      this.bindToMouseOver();
      downEvent = (function() {
        return function(e) {
          if (e.touches || (e.which != null) && e.which === 1) {
            _this.pressed = true;
            if (!dnd.draggedCard) {
              dnd.startDrag(e, _this.model);
            }
            e.preventDefault();
            return _this.invokePopupAfterAWhile(e);
          }
        };
      })();
      this.on(Event.down, downEvent);
      boundToggleTapped = function() {
        _this.pressed = false;
        if (!dnd.dragged && !popup.visible && !w.modalRecentlyVisible) {
          return _this.model.toggleTapped();
        }
      };
      this.$element.on(Event.up, '.face', boundToggleTapped);
      $('.notes', this.$element).on("click", function(e) {
        return popup.show(_this.model);
      });
      $('.face', this.$element).on(Event.down, function() {});
      this.after("tapped", function() {
        return _this.tap();
      }).after("untapped", function() {
        return _this.untap();
      }).after("flipped", function() {
        return _this.flip();
      }).after("unflipped", function() {
        return _this.unflip();
      }).after("facedown", function() {
        return _this.facedown();
      }).after("faceup", function() {
        return _this.faceup();
      }).after("moved", function() {
        return _this.updateTransform();
      }).after("p:changed", function() {
        return _this.renderNotes();
      }).after("t:changed", function() {
        return _this.renderNotes();
      }).after("c:changed", function() {
        return _this.renderNotes();
      });
      this[this.model.faceState.current]();
      this.after("destroyed", function() {
        return _this.destroy();
      });
      if (this.model.isTransformable) {
        this.after('onbattlefield', function() {
          return _this.useTransformImagePath();
        }).after('onleavebattlefield', function() {
          return _this.renderBackImageSrc();
        }).after('transformed', function() {
          return _this.toggleTransformedClass(true);
        }).after('untransformed', function() {
          return _this.toggleTransformedClass(false);
        });
      }
    }

    CardView.prototype.render = function() {
      var html;

      html = "        <div class='card_shape'>          <div class='card_image face' style=\"background-image: url(" + (this.model.path.replace(/'/g, "\\'")) + ")\"></div>          <div class='back_rotate face'>            <div style='background-image: url(" + (mtg.cardBackPath()) + ")' class='card_back'></div>          </div>        </div>        <div id='" + this.model.id + "notes' class='notes'>          <span class='note power_and_toughness' id='" + this.model.id + "power_and_toughness'></span>          <span class='note counters' id='" + this.model.id + "counters'></span>        </div>";
      this.$element.html(html);
      this.setNoteElements();
      return this;
    };

    CardView.prototype.on = function(type, handler) {
      this.$element.on(type, handler);
      return this;
    };

    CardView.prototype.after = function(name, callback) {
      after("" + this.id + ":" + name, callback);
      return this;
    };

    CardView.prototype.forget = function(name, callback) {
      forget("" + this.id + ":" + name, callback);
      return this;
    };

    CardView.prototype.invokePopupAfterAWhile = function(e) {
      var _this = this;

      if (this.invoking) {
        clearTimeout(this.invoking);
      }
      return this.invoking = wait(350, function() {
        if (dnd.draggedCard == null) {
          if (_this.pressed) {
            dnd.tearDown();
            return fire("popup:invoked", {
              card: _this.model,
              fromCard: true
            });
          }
        }
      });
    };

    CardView.prototype.detach = function() {
      var newX, newY;

      this.rememberCardX = this.model.x;
      this.rememberCardY = this.model.y;
      this.rememberCardZ = this.model.z;
      b.append(this.$element);
      this.model.cleanupZ();
      newX = this.model.zone().view().left + this.model.x;
      newY = this.model.zone().view().top + this.model.y;
      return this.model.move(newX, newY, mtg.Z.FLOATING);
    };

    CardView.prototype.attach = function(e) {
      var clientX, clientY,
        _this = this;

      this.model.zone().view().$element.append(this.$element);
      if (e && this.model.zone() === battlefield) {
        clientX = e.clientX;
        clientY = e.clientY;
        return defer(function() {
          var cell, x, y, _grid;

          _grid = grid.get();
          if (_grid) {
            x = clientX - battlefield.view().left;
            y = clientY - battlefield.view().top;
            cell = _grid.findCellByCoords(x, y);
            if (cell) {
              _grid.removeCard(_this.model);
              return cell.add(_this.model);
            } else {
              return _grid.addCard(_this.model);
            }
          }
        });
      }
    };

    CardView.prototype.revert = function() {
      var _this = this;

      this.attach();
      defer((function() {
        _this.model.move(_this.rememberCardX, _this.rememberCardY, _this.rememberCardZ);
        return _this.rememberCardX = _this.rememberCardY = _this.rememberCardZ = void 0;
      }));
      return false;
    };

    CardView.prototype.tap = function() {
      this.$element.addClass('tapped');
      return this.updateTransform();
    };

    CardView.prototype.untap = function() {
      this.$element.removeClass('tapped');
      return this.updateTransform();
    };

    CardView.prototype.flip = function() {
      this.$element.addClass('flipped');
      return this.updateTransform();
    };

    CardView.prototype.unflip = function() {
      this.$element.removeClass('flipped');
      return this.updateTransform();
    };

    CardView.prototype.facedown = function(suppressedFlipDuration) {
      var duration, tempZ,
        _this = this;

      duration = getSetting('3dTransforms2') ? mtg.transitionDuration : 0;
      if ((suppressedFlipDuration != null) && suppressedFlipDuration === true) {
        duration = 0;
      }
      this.flipping = true;
      tempZ = this.model.z;
      this.model.z = mtg.Z.FLOATING;
      if (library.include(this.model)) {
        this.model.z += this.model.zone().size();
      }
      if (duration > 0) {
        wait(duration / 2, function() {
          return _this.$element.addClass('facedown').removeClass('faceup');
        });
        wait((duration / 3) * 2, function() {
          _this.model.z = tempZ;
          _this.updateTransform();
          return _this.flipping = false;
        });
      } else {
        this.$element.addClass('facedown').removeClass('faceup');
        this.model.z = tempZ;
        this.flipping = false;
      }
      this.updateTransform();
      return this.fire("facedown");
    };

    CardView.prototype.faceup = function() {
      var duration, tempZ,
        _this = this;

      duration = getSetting('3dTransforms2') ? mtg.transitionDuration : 0;
      this.flipping = true;
      tempZ = this.z;
      this.model.z = mtg.Z.FLOATING;
      if (library.include(this.model)) {
        this.model.z += zones[this.model.zoneState.current].size();
      }
      if (duration > 0) {
        wait(duration / 2, function() {
          return _this.$element.removeClass('facedown').addClass('faceup');
        });
        wait((duration / 3) * 2, function() {
          _this.model.z = tempZ;
          _this.updateTransform();
          return _this.flipping = false;
        });
      } else {
        this.$element.removeClass('facedown').addClass('faceup');
        this.model.z = tempZ;
        this.updateTransform();
        this.flipping = false;
      }
      this.updateTransform();
      this.fire("faceup");
      return this;
    };

    CardView.prototype.updateTransform = function() {
      css.transform(this.$element, this.model.x, this.model.y, this.model.r, this.model.z);
      return this;
    };

    CardView.prototype.fire = function(action) {
      return fire("card:" + action, {
        action: action,
        card: this
      });
    };

    CardView.prototype.setNoteElements = function() {
      var _ref, _ref1, _ref2;

      if ((_ref = this.$notes) == null) {
        this.$notes = this.$element.find("#" + this.model.id + "notes");
      }
      if ((_ref1 = this.$ptField) == null) {
        this.$ptField = this.$element.find("#" + this.model.id + "power_and_toughness");
      }
      if ((_ref2 = this.$cField) == null) {
        this.$cField = this.$element.find("#" + this.model.id + "counters");
      }
      return this.renderNotes();
    };

    CardView.prototype.renderNotes = function() {
      this.$ptField.text(this.model.t > 0 ? "" + this.model.p + " / " + this.model.t : '');
      this.$cField.text(this.model.c > 0 ? this.model.c + "c" : '');
      return this.$element.toggleClass("has_notes", this.model.hasNotes());
    };

    CardView.prototype.destroy = function() {
      this.$ptField.remove();
      this.$cField.remove();
      this.$notes.remove();
      this.$element.remove();
      return this.forget("tapped").forget("untapped").forget("flipped").forget("unflipped").forget("facedown").forget("faceup").forget("moved").forget("p:changed").forget("t:changed").forget("c:changed").forget("destroyed");
    };

    CardView.prototype.useTransformImagePath = function() {
      var _this = this;

      deckLoaded.then(function(deck) {
        return _this.renderBackImageSrc(deck.media_root + _this.model.data.transformation.image_path);
      });
      return this;
    };

    CardView.prototype.toggleTransformedClass = function(transformed) {
      if (transformed) {
        this.useTransformImagePath();
      } else {
        this.renderBackImageSrc();
      }
      return this.$element.toggleClass('transformed', transformed);
    };

    CardView.prototype.setImageDimensions = function(dimensions) {
      var bogus, targetSize;

      dimensions || (dimensions = cardDimensions[this.model.name]);
      targetSize = sizes.targetSizes[sizes.current];
      bogus = !dimensions || dimensions && (dimensions.width > targetSize.width + 5 || dimensions.height > targetSize.height + 5);
      if (bogus) {
        dimensions = targetSize;
      }
      return $('.face', this.$element).css({
        height: "" + dimensions.height + "px",
        width: "" + dimensions.width + "px",
        backgroundSize: "" + dimensions.width + "px " + dimensions.height + "px"
      });
    };

    CardView.prototype.renderImageSrc = function(path) {
      return $('.card_image.face', this.$element).css('background-image', "url(" + path + ")");
    };

    CardView.prototype.renderBackImageSrc = function(path) {
      return $('.card_back', this.$element).css('background-image', "url(" + (path || mtg.cardBackPath()) + ")");
    };

    CardView.prototype.bindToMouseOver = function() {
      var _this = this;

      return this.on("mouseover", function() {
        return mtg.mousedOverCard = _this.model;
      }).on('mouseout', function() {
        if (mtg.mousedOverCard === _this.model) {
          return mtg.mousedOverCard = void 0;
        }
      });
    };

    CardView.prototype.unbindToMouseOver = function() {
      return this.$element.off("mouseover").off("mouseout");
    };

    return CardView;

  })();
  return CardView;
});

define('process-deck',['q', 'globals', 'zepto', 'card-views', 'card-model', 'card-view', 'detect', 'preload-images', 'sizes', 'get-setting', 'card-model-string-helpers'], function(Q, globals, $, cardViews, CardModel, CardView, features, preloadImageAndCacheSize, sizes, getSetting, cardModelHelpers) {
  var commanderDeferred, commanderPromise, deferred, processDeck, promise;

  deferred = Q.defer();
  promise = deferred.promise;
  commanderDeferred = Q.defer();
  commanderPromise = commanderDeferred.promise;
  processDeck = function(deck) {
    var baseCardObject, card, cardName, cardObjects, edition, firstHand, firstHandPreloaded, getPair, isCommander, model, name, path, ptc, q, theRest, transformation, transformationsPTC, _fn, _i, _j, _len, _ref;

    cardObjects = [];
    for (cardName in deck.cards) {
      card = deck.cards[cardName];
      ptc = cardModelHelpers.parsePTC(card.pt);
      path = cardModelHelpers.buildPath(deck.media_root + sizes.replaceSizeInPath(card.image_path), card.edition, cardName);
      edition = card.edition;
      name = cardName.convertChars();
      transformation = card.transform;
      isCommander = (card.isCommander != null) === true;
      if (transformation) {
        transformationsPTC = cardModelHelpers.parsePTC(card.transform.pt);
        transformation.p = transformationsPTC.p;
        transformation.t = transformationsPTC.t;
        transformation.c = transformationsPTC.c || 0;
      }
      for (q = _i = 1, _ref = Number(card.quantity); 1 <= _ref ? _i <= _ref : _i >= _ref; q = 1 <= _ref ? ++_i : --_i) {
        baseCardObject = {
          name: name,
          edition: edition,
          path: path,
          p: ptc.p,
          t: ptc.t,
          c: ptc.c || 0,
          n: q,
          isCommander: isCommander,
          type: card.type.copy()
        };
        if (transformation) {
          baseCardObject.transformation = card.transform;
        }
        cardObjects.push(baseCardObject);
      }
    }
    cardObjects = cardObjects.shuffle();
    getPair = function(card) {
      return [card.name, card.path];
    };
    firstHand = cardObjects.slice(-7).map(getPair);
    theRest = cardObjects.slice(0, cardObjects.length - 7).map(getPair);
    firstHandPreloaded = preloadImageAndCacheSize(firstHand);
    firstHandPreloaded.then(function() {
      return preloadImageAndCacheSize(theRest).then(function() {});
    });
    if (!w.jasmine) {
      _fn = function(model) {
        return firstHandPreloaded.then(function() {
          var view;

          view = new CardView(model);
          cardViews[model.id] = view;
          return model.zoneState.transition();
        });
      };
      for (_j = 0, _len = cardObjects.length; _j < _len; _j++) {
        card = cardObjects[_j];
        model = new CardModel(card);
        if (model.isCommander) {
          (function(model) {
            return promise.then(function() {
              return commanderDeferred.resolve(model);
            });
          })(model);
        }
        _fn(model);
      }
    }
    if (!('tokens' in deck)) {
      deck.tokens = {
        Thopter: {
          image_url: 'http://static.tappedout.net/mtg-cards/tokens/thopter_1.jpg',
          pt: '1/1'
        }
      };
    }
    return firstHandPreloaded.then(function() {
      if (!w.jasmine) {
        fire("deck:loaded", deck);
      }
      deferred.resolve(deck);
      return promise.then(function() {
        if (!commanderPromise.isFulfilled()) {
          return commanderDeferred.reject("No commander in deck.");
        }
      });
    });
  };
  return {
    processDeck: processDeck,
    promise: promise,
    commander: commanderPromise
  };
});

define('dom',['element'], function(element) {
  return {
    visible: function(element) {
      return element.style.display !== 'none';
    },
    element: element
  };
});

define('requestanimationframe',['alias'], function(alias) {
  var w;

  w = alias.w;
  return {
    requestAnimFrame: (function() {
      return w.requestAnimationFrame || w.webkitRequestAnimationFrame || w.mozRequestAnimationFrame || w.oRequestAnimationFrame || w.msRequestAnimationFrame || function(callback) {
        return w.setTimeout(callback, 1000 / 60);
      };
    })(),
    clearAnimFrame: (function() {
      return w.cancelRequestAnimationFrame || w.webkitCancelRequestAnimationFrame || w.mozCancelRequestAnimationFrame || w.oCancelRequestAnimationFrame || w.msCancelRequestAnimationFrame || w.cancelAnimationFrame || w.webkitCancelAnimationFrame || w.mozCancelAnimationFrame || w.oCancelAnimationFrame || w.msCancelAnimationFrame || function(timeout) {
        return w.clearTimeout(timeout);
      };
    })()
  };
});

define('analytics',['event'], function() {
  var track;

  track = function(category, action) {
    if (w._gaq) {
      return _gaq.push(["_trackEvent", category, action]);
    }
  };
  after("setting:changed", function(e) {
    return track("setting:" + e.data.setting, e.data.value);
  });
  after("submenu:shown", function(e) {
    return track("submenu:shown", e.data.text);
  });
  after("button:clicked", function(e) {
    return track("button:clicked", e.data.id);
  });
  after("library:shuffled", function(e) {
    return track("library", "shuffled");
  });
  after("library:addedToTop", function(e) {
    return track("library", "addedToTop", e.data.id);
  });
  after("library:addedToBottom", function(e) {
    return track("library", "addedToBottom", e.data.id);
  });
  return track;
});

define('progress',['lib/zepto/zepto', 'event', 'globals'], function($) {
  var ProgressBar, eventMap, mapMessageToEvent, progressBar;

  ProgressBar = (function() {
    function ProgressBar($el, events) {
      var className, _fn,
        _this = this;

      this.events = events;
      this.$el = $el;
      _fn = function() {
        var c;

        c = className;
        after(_this.events[c], function() {
          _this.$el.addClass(c);
          return _this[c] = true;
        });
        return _this[c] = false;
      };
      for (className in this.events) {
        _fn();
      }
    }

    return ProgressBar;

  })();
  eventMap = {
    started: "progress:started",
    requested: "deck:requested",
    errored: "deck:errored",
    finished: "hand:drawn",
    hidden: "progressbar:hidden"
  };
  progressBar = new ProgressBar($("#progress"), eventMap);
  mapMessageToEvent = function(event, message) {
    return after(event, function() {
      return $("#progress_label").text(message);
    });
  };
  mapMessageToEvent("deck:errored", "Deck data is loading too slow or errored.");
  mapMessageToEvent("hand:drawn", "Deck data successfully loaded.");
  fire("progress:started");
  after("hand:drawn", function() {
    return wait(800, function() {
      return fire("progressbar:hidden");
    });
  });
  return progressBar;
});

define('turns',['array'], function() {
  return [];
});

define('log-turn-action',['turns'], function(turns) {
  var logTurnAction;

  return logTurnAction = function(attributes) {
    var lastTurn;

    lastTurn = turns.last();
    if (lastTurn) {
      return lastTurn.action(attributes);
    }
  };
});

define('commander',['process-deck', 'button', 'zepto', 'popup'], function(processed, Button, $, popup) {
  processed.commander.then(function(commander) {
    $(function() {
      $('html').addClass('has_commander');
      $("#draw_card_by_name").after("<a id='get_commander' class='button button_spacer'>Commander</a>");
      return new Button("get_commander", {
        handler: function() {
          return popup.show(commander);
        }
      });
    });
    return commander;
  });
  return processed.commander;
});

define('health',['q', 'zepto', 'super-select', 'string', 'log-turn-action', 'commander'], function(Q, $, SuperSelect, String, logTurnAction, commanderPromise) {
  var hasCommander, health, noCommander, setLife, setupHealthViews;

  health = {
    life: 0,
    poison: 0
  };
  setLife = function(life) {
    return function() {
      health.life = life;
      return $(setupHealthViews);
    };
  };
  hasCommander = setLife(40);
  noCommander = setLife(20);
  commanderPromise.then(hasCommander, noCommander);
  setupHealthViews = function() {
    var setupHealthType;

    setupHealthType = function(name, max) {
      var $el, getProperty, mod, renderOptions, setProperty, setValue, superSelect;

      $el = $("#" + name + "_field");
      superSelect = new SuperSelect({
        el: $el,
        button: $("#" + name + " .super_select_button"),
        template: (function() {
          var prefix;

          prefix = ("" + name + ": ").capitalize();
          return function(v) {
            return "" + prefix + " " + v;
          };
        })()
      });
      getProperty = function() {
        return health[name];
      };
      setProperty = function(value) {
        return health[name] = Number(value);
      };
      setValue = function() {
        var value;

        value = getProperty();
        renderOptions();
        (function(value) {
          return wait(400, function() {
            if (value === getProperty()) {
              return logTurnAction({
                name: name.capitalize(),
                value: value
              });
            }
          });
        })(value);
        $el.val(value);
        superSelect.render();
        return value;
      };
      renderOptions = setupSelecterRenderer($el.get(0), getProperty, max);
      mod = function(v) {
        setProperty(getProperty() + v);
        if (getProperty() < 0) {
          setProperty(0);
        } else if (name === 'poison' && getProperty() > 10) {
          setProperty(10);
        }
        return setValue();
      };
      after(name[0] + ":pressed", function() {
        return mod(1);
      });
      after(name[0].toUpperCase() + ":pressed", function() {
        return mod(-1);
      });
      $el.on('change', function() {
        setProperty($el.val());
        return defer(setValue);
      });
      return setValue();
    };
    setupHealthType("poison", 10);
    return setupHealthType("life", 100);
  };
  return health;
});

define('format-token-data',['array', 'card-model-string-helpers'], function(Array, cardModelHelpers) {
  var formatTokenData;

  formatTokenData = function(deck) {
    var formatted, pt, raw, sorted, sorting, source, tokenId, tokenIds, _tokenId;

    raw = deck.tokkens;
    tokenIds = [];
    formatted = [];
    for (tokenId in raw) {
      if (!tokenIds.include(tokenId)) {
        source = raw[tokenId];
        pt = cardModelHelpers.parsePTC(source.pt);
        formatted.push({
          tokenId: tokenId,
          name: source.name,
          p: pt.p,
          t: pt.t,
          type: typeof source.type === 'string' ? [source.type] : source.type.copy(),
          path: source.image_url || deck.token_media_root + source.image_path,
          n: 0
        });
        tokenIds.push(tokenId);
      }
    }
    sorted = formatted.map(function(t) {
      return "" + t.name + t.tokenId;
    }).sort();
    sorting = (function() {
      var _i, _len, _results;

      _results = [];
      for (_i = 0, _len = sorted.length; _i < _len; _i++) {
        _tokenId = sorted[_i];
        _results.push(formatted.find(function(t) {
          return ("" + t.name + t.tokenId) === _tokenId;
        }));
      }
      return _results;
    })();
    formatted = sorting;
    return formatted;
  };
  return formatTokenData;
});

define('formatted-token-data',['q', 'format-token-data', 'deck-loaded'], function(Q, formatTokenData, deckLoaded) {
  var deferred, formattedTokenData;

  deferred = Q.defer();
  formattedTokenData = [];
  deckLoaded.then(function(deck) {
    formattedTokenData = formatTokenData(deck);
    if (formattedTokenData.length) {
      deferred.resolve(formattedTokenData);
    } else {
      deferred.reject();
    }
    return deck;
  });
  return deferred.promise;
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('token-view',['card-view', 'token-views'], function(CardView, tokens) {
  var TokenView;

  TokenView = (function(_super) {
    __extends(TokenView, _super);

    function TokenView(model) {
      TokenView.__super__.constructor.call(this, model);
      this.setImageDimensions();
    }

    TokenView.prototype.destroy = function() {
      TokenView.__super__.destroy.call(this);
      tokens || (tokens = require('token-views'));
      return delete tokens[this.model.id];
    };

    return TokenView;

  })(CardView);
  return TokenView;
});

define('token-views',['lib/zepto/zepto', 'keys', 'token-view', 'formatted-token-data', 'token-model', 'preload-images'], function($, keys, TokenView, formattedTokenDataPromise, TokenModel, preload) {
  var $tokenSelectEl, addToken, preloadTokenImageOnChange, renderTokenOptions, tokens;

  tokens = {};
  $tokenSelectEl = $("#add_token_field");
  addToken = function() {
    return formattedTokenDataPromise.then(function(formattedTokenData) {
      var tokenModel, tokenView;

      TokenModel || (TokenModel = require('token-model'));
      tokenModel = new TokenModel(TokenModel.getTokenDataById(formattedTokenData, $tokenSelectEl.val()));
      tokenView = new TokenView(tokenModel);
      tokens[tokenModel.id] = tokenView;
      return tokenModel.zoneState.transition();
    });
  };
  onQuickClick("#add_token_link", addToken);
  after("k:pressed", function() {
    return $tokenSelectEl.focus().trigger('focus');
  });
  preloadTokenImageOnChange = function(e) {
    return formattedTokenDataPromise.then(function(formattedTokenData) {
      var data;

      TokenModel || (TokenModel = require('token-model'));
      data = TokenModel.getTokenDataById(formattedTokenData, $tokenSelectEl.val());
      return preload("" + data.name + data.tokenId, data.path);
    });
  };
  $tokenSelectEl.on('keypress', function(e) {
    if (keys.getKey(e) === "return" && e.target === $tokenSelectEl[0]) {
      return addToken();
    }
  }).on('change', preloadTokenImageOnChange);
  renderTokenOptions = function(formattedTokenData) {
    var availableToken, newOptions, _i, _len;

    newOptions = '';
    for (_i = 0, _len = formattedTokenData.length; _i < _len; _i++) {
      availableToken = formattedTokenData[_i];
      newOptions += option({
        value: availableToken.tokenId
      }, "" + availableToken.name + " " + availableToken.p + "/" + availableToken.t);
    }
    $tokenSelectEl.html(newOptions);
    return $("#add_token").show();
  };
  formattedTokenDataPromise.then(renderTokenOptions);
  return tokens;
});

var __hasProp = {}.hasOwnProperty,
  __extends = function(child, parent) { for (var key in parent) { if (__hasProp.call(parent, key)) child[key] = parent[key]; } function ctor() { this.constructor = child; } ctor.prototype = parent.prototype; child.prototype = new ctor(); child.__super__ = parent.prototype; return child; };

define('token-model',['require', 'globals', 'card-model', 'card-model-string-helpers', 'token-views'], function(require, globals, CardModel, cardModelHelpers) {
  var TokenModel;

  TokenModel = (function(_super) {
    __extends(TokenModel, _super);

    function TokenModel(data) {
      var _this = this;

      this.initialZone = 'battlefield';
      this.isToken = true;
      this.id = "" + (cardModelHelpers.formatIdString(data.name, data.n)) + "_" + TokenModel.uniqueIndex;
      TokenModel.__super__.constructor.call(this, data);
      if (!this.type.include('Token')) {
        this.type.push('Token');
      }
      if (!this.type.include('Creature')) {
        this.type.push('Creature');
      }
      this.faceup();
      TokenModel.uniqueIndex += 1;
      this.boundDestroy = function(e) {
        if (e.data.card === _this) {
          forget("ongraveyard onlibrary onhand onexiled", _this.boundDestroy);
          return _this.destroy();
        }
      };
      after("ongraveyard onlibrary onhand onexiled", this.boundDestroy);
      this.forget("size:changed", this.boundRewritePath);
    }

    TokenModel.prototype.view = function() {
      return require('token-views')[this.id];
    };

    return TokenModel;

  })(CardModel);
  TokenModel.uniqueIndex = 0;
  TokenModel.getTokenDataById = function(formattedTokenData, tokenId) {
    var data;

    data = formattedTokenData.find(function(t) {
      return t.tokenId === tokenId;
    });
    data.n += 1;
    return data;
  };
  return TokenModel;
});

define('dropdown',['zepto', 'detect', 'event'], function($, features, Event) {
  var Submenu, _ref;

  Submenu = (function() {
    function Submenu(el) {
      var _this = this;

      this.$el = $(el);
      this.$button = this.$el.find('.submenu_button');
      this.$submenu = this.$el.find('.submenu');
      this.visible = false;
      this.disabled = this.$submenu.length === 0 || this.$el.hasClass('no_submenu');
      if (this.disabled) {
        this.$el.addClass('no_submenu');
      } else {
        this.$button.on('click', function(e) {
          if (_this.visible) {
            return _this.hide();
          } else {
            return _this.show();
          }
        });
        if (!features.handheld) {
          this.$button.on('mouseover', function(e) {
            return $(e.target).addClass('hover');
          }).on('mouseout', function(e) {
            return $(e.target).removeClass('hover');
          });
        }
      }
    }

    Submenu.prototype.show = function() {
      var _this = this;

      this.$el.addClass('visible');
      wait(50, function() {
        _this.boundHideFromOutsideList = function(e) {
          return _this.hideFromOutsideList(e);
        };
        return h.on(Event.down, _this.boundHideFromOutsideList);
      });
      fire("submenu:shown", {
        text: this.$el.text()
      });
      return this.visible = true;
    };

    Submenu.prototype.hide = function(e) {
      this.$el.removeClass('visible');
      h.off(Event.down, this.boundHideFromOutsideList);
      return this.visible = false;
    };

    Submenu.prototype.hideFromOutsideList = function(e) {
      if ($(e.target).parents().indexOf(this.$el.get(0)) === -1) {
        return this.hide();
      }
    };

    return Submenu;

  })();
  if ((_ref = w.app) == null) {
    w.app = {};
  }
  app.nav = {
    submenus: [],
    Submenu: Submenu
  };
  $(function() {
    app.nav.submenus.push(new Submenu($('#settings_link').parent()));
    app.nav.submenus.push(new Submenu($('#logger_link').parent()));
    return app.nav.submenus.push(new Submenu($('#stats_link').parent()));
  });
  return app.nav;
});

define('stage',['string', 'zepto', 'deck-loaded', 'mtg', 'sizes', 'q'], function(String, $, deckLoaded, mtg, sizes, Q) {
  var setupStage;

  setupStage = function(deck) {
    return $(function() {
      var _ref;

      $('html').addClass("card_size_" + sizes.current);
      if (mtg.deckUrl) {
        $('#deck_name').attr('href', mtg.deckUrl);
      }
      $('#deck_name').html(deck.name);
      $("#author").text(deck.author).attr('href', "http://tappedout.net/users/" + deck.author + "/");
      document.title = "" + ($('#deck_name').text()) + " by " + deck.author + ": " + document.title;
      if (((_ref = deck.thumb) != null ? _ref.length : void 0) > 0) {
        return $('#pie').html(img({
          src: deck.thumb
        })).show();
      }
    });
  };
  return deckLoaded.then(setupStage);
});

define('turn-model',['event', 'zone-models', 'health'], function(Event, zones, health) {
  var TurnActionModel, TurnModel;

  TurnActionModel = (function() {
    function TurnActionModel(attributes) {
      var key;

      for (key in attributes) {
        this[key] = attributes[key];
      }
    }

    return TurnActionModel;

  })();
  TurnModel = (function() {
    function TurnModel(n) {
      var _this = this;

      this.actions = [];
      this.n = n;
      this.current = true;
      this.recordState();
      this.boundRecordState = function() {
        return _this.recordState();
      };
      after("turn:" + this.n + ":action:added p:changed t:changed", this.boundRecordState);
      this.boundEndTurn = function() {
        _this.current = false;
        forget("turn:" + _this.n + ":action:added", _this.boundRecordState);
        forget("p:changed", _this.boundRecordState);
        forget("t:changed", _this.boundRecordState);
        return forget("end:turn", _this.boundEndTurn);
      };
      after("end:turn", this.boundEndTurn);
    }

    TurnModel.prototype.recordState = function() {
      var zone;

      this.life = health.life;
      this.poison = health.poison;
      for (zone in zones) {
        this[zone] = zones[zone].exportState();
      }
      fire("state:updated");
      return this;
    };

    TurnModel.prototype.action = function(attributes) {
      var _ref;

      if ((_ref = attributes.i) == null) {
        attributes.i = this.actions.length;
      }
      this.actions.push(new TurnActionModel(attributes));
      return fire("turn:action:added");
    };

    return TurnModel;

  })();
  return TurnModel;
});

define('turn',['q', 'event', 'zone-names', 'draw', 'zone-initialize', 'get-setting', 'turn-model', 'turns', 'log-turn-action'], function(Q, Event, ZONE_NAMES, draw, zoneInstances, getSetting, TurnModel, turns, logTurnAction) {
  var battlefield, pub, zones;

  zones = zoneInstances.zones;
  battlefield = zones.battlefield;
  pub = {
    turns: turns,
    turn: 1
  };
  after("turn:action:added", function() {
    return fire("turn:" + pub.turn + ":action:added");
  });
  after("end:turn", function() {
    return fire("next:turn");
  });
  after("next:turn", function() {
    turns.push(new TurnModel(turns.length + 1));
    pub.turn = turns.length;
    $("#turn_el").text(pub.turn);
    if (getSetting('autoUntap')) {
      battlefield.untap();
    }
    if (getSetting('autoDraw')) {
      return draw();
    }
  });
  onQuickClick("#next_turn", function() {
    return fire("end:turn");
  });
  after("n:pressed", function() {
    return fire("end:turn");
  });
  after("hand:drawn", function() {
    var cardEvents;

    turns.push(new TurnModel(1));
    logTurnAction({
      name: "Drawn",
      zoneName: "Hand"
    });
    cardEvents = "";
    ZONE_NAMES.forEach(function(zone) {
      return cardEvents += " on" + zone;
    });
    cardEvents += " battlefield:token:added token:destroyed";
    after(cardEvents, function(e) {
      return logTurnAction({
        cardName: e.data.card.name,
        zoneName: e.data.card.zone().name,
        cardId: e.data.card.id
      });
    });
    after("library:shuffled", function() {
      return logTurnAction({
        name: "Shuffled",
        zoneName: "Library"
      });
    });
    return after("mulligan", function(e) {
      return logTurnAction({
        name: "Mulligan " + e.data.mulligans,
        zoneName: "Hand"
      });
    });
  });
  return pub;
});

define('buffs',['event', 'zepto', 'battlefield-model'], function(Event, $, battlefield) {
  var _mod;

  _mod = function(p, v) {
    return function() {
      return battlefield.getRecipients().forEach(function(card) {
        return card.mod(p, v);
      });
    };
  };
  return ["power", "toughness", "counters"].forEach(function(prop) {
    $("#increase_" + prop).on(Event.down, _mod(prop[0], 1));
    return $("#decrease_" + prop).on(Event.down, _mod(prop[0], -1));
  });
});

define('logger',['alias', 'event', 'zone-names', 'types', 'zone-initialize', 'super-select', 'popup', 'card-views', 'token-views', 'turns'], function(alias, Event, ZONE_NAMES, TYPES, zones, SuperSelect, popup, cardViews, tokenViews, turns) {
  var MetricView, movesInCurrentTurn;

  movesInCurrentTurn = 0;
  after("next:turn:taken", function() {
    return movesInCurrentTurn = 0;
  });
  after("hand:drawn", function() {
    LoggerView.start();
    return StatsView.start();
  });
  w.LoggerView = {
    start: function() {
      var _this = this;

      this.nextTurn();
      this.nav().$button.on('click', function() {
        return _this.render();
      });
      after("next:turn", function() {
        return _this.nextTurn();
      });
      this.$next.on('click', function() {
        return _this.nextTurn();
      });
      this.$previous.on('click', function() {
        return _this.previousTurn();
      });
      return this.$el.on('click', '.linked_card', function(e) {
        var card, id;

        id = $(e.target).data('card-id');
        card = (cardViews[id] || tokenViews[id]).model;
        return popup.show(card);
      });
    },
    $el: $("#logger2"),
    $title: $("#turn_title"),
    $tableBody: $("#action_table tbody"),
    $next: $("#view_next_turn"),
    $previous: $("#view_previous_turn"),
    nav: function() {
      return app.nav.submenus[1];
    },
    setTurn: function(direction) {
      if (!this.turn) {
        this.turn = turns.last();
      } else if (direction) {
        this.turn = turns[turns.indexOf(this.turn) + direction];
      }
      return this;
    },
    visible: function() {
      return this.nav().visible;
    },
    render: function() {
      if (this.visible()) {
        this.$title.text("Turn " + this.turn.n);
        this.$previous.toggleClass('visible', turns.first() !== this.turn);
        this.$next.toggleClass('visible', turns.last() !== this.turn);
        this.renderActions();
      }
      return this;
    },
    renderActions: function() {
      this.$tableBody.get(0).innerHTML = this.actionTableRowTemplate();
      return this;
    },
    actionTableRowTemplate: function() {
      var template;

      if (this.turn.actions.empty()) {
        return '';
      } else {
        template = this.turn.actions.map(function(action, i) {
          var associatedCardView, linkedCard, _ref;

          if (action.cardId) {
            associatedCardView = cardViews[action.cardId] || tokenViews[action.cardId];
            if (associatedCardView) {
              linkedCard = span({
                "class": "linked_card",
                "data-card-id": action.cardId
              }, action.cardName);
            }
          }
          return tr("            " + (td({
            "class": 'action_count'
          }, i + 1)) + "            " + (td(linkedCard || action.cardName || action.name)) + "            " + (td({
            "class": 'zone_name'
          }, action.value != null ? action.value : (_ref = action.zoneName) != null ? _ref.capitalize() : void 0)));
        });
        return template.join('');
      }
    },
    previousTurn: function() {
      this.unbindToTurn().setTurn(-1).render().bindToTurn();
      return this;
    },
    nextTurn: function() {
      this.unbindToTurn().setTurn(1).render().bindToTurn();
      return this;
    },
    bindToTurn: function() {
      var _this = this;

      this.boundRender = function() {
        return _this.render();
      };
      after("turn:" + this.turn.n + ":action:added", this.boundRender);
      return this;
    },
    unbindToTurn: function() {
      if (this.turn) {
        forget("turn:" + this.turn.n + ":action:added", this.boundRender);
      }
      return this;
    }
  };
  w.StatsView = {
    start: function() {
      var metricViewElements,
        _this = this;

      metricViewElements = $('.metric', this.$el);
      this.subviews.push(new MetricView({
        el: metricViewElements[0],
        defaultMetric: 'Lands',
        defaultMetricZone: 'Hand'
      }));
      this.subviews.push(new MetricView({
        el: metricViewElements[1],
        defaultMetric: 'Lands',
        defaultMetricZone: 'Battlefield'
      }));
      this.subviews.push(new MetricView({
        el: metricViewElements[2],
        defaultMetric: 'Creatures',
        defaultMetricZone: 'Battlefield'
      }));
      this.subviews.push(new MetricView({
        el: metricViewElements[3],
        defaultMetric: 'Artifacts',
        defaultMetricZone: 'Battlefield'
      }));
      this.subviews.push(new MetricView({
        el: metricViewElements[4],
        defaultMetric: 'Life'
      }));
      return this.nav().$button.on('click', function() {
        return _this.render();
      });
    },
    subviews: [],
    $el: $("#stats"),
    nav: function() {
      return app.nav.submenus[2];
    },
    visible: function() {
      return this.nav().visible;
    },
    render: function() {
      if (this.visible()) {
        return this.subviews.invoke('render');
      }
    }
  };
  return MetricView = (function() {
    function MetricView(options) {
      var _this = this;

      this.$el = $(options.el);
      this.$selectedMetric = $('.selected_metric', this.$el);
      this.$selectedMetricZone = $('.selected_metric_zone', this.$el);
      this.superSelectMetric = new SuperSelect({
        el: this.$selectedMetric
      });
      this.superSelectMetricZone = new SuperSelect({
        el: this.$selectedMetricZone
      });
      this.superSelectMetricZone.$button.addClass('second_column');
      this.$selectedMetricValue = $('.selected_metric_value', this.$el);
      this.$graphArea = $('.graph_area', this.$el);
      this.$selectedMetric.html(this.metrics.map(function(m) {
        return option(m);
      }).join(''));
      this.$selectedMetricZone.html(this.zoneNames.map(function(m) {
        return option(m);
      }).join(''));
      this.$selectedMetric.on('change', function() {
        return _this.render();
      });
      this.$selectedMetricZone.on('change', function() {
        return _this.render();
      });
      if (options.defaultMetric) {
        this.$selectedMetric.val(options.defaultMetric);
      }
      if (options.defaultMetricZone) {
        this.$selectedMetricZone.val(options.defaultMetricZone);
      }
      this.render();
      after("state:updated", function() {
        return _this.render();
      });
    }

    MetricView.prototype.render = function() {
      var metricName, metricZone,
        _this = this;

      metricName = this.$selectedMetric.val().toLowerCase();
      metricZone = metricName in turns.last() ? false : this.$selectedMetricZone.val().toLowerCase();
      this.$selectedMetricZone.toggleClass('hidden', !metricZone);
      this.superSelectMetricZone.toggle(!metricZone);
      this.$el.find('.in').toggleClass('hidden', !metricZone);
      this.$selectedMetricValue.text(this.getMetricValue(turns.last(), metricName, metricZone));
      return this.$graphArea.get(0).innerHTML = (function() {
        var graphs, maxMetric;

        maxMetric = (metricZone ? turns.pluck(metricZone) : turns).pluck(metricName).max();
        graphs = turns.map(function(turn, i) {
          var height, metricValue;

          metricValue = _this.getMetricValue(turn, metricName, metricZone);
          height = ((metricValue / maxMetric) || 0) * 40;
          return div({
            title: "" + metricValue + " " + metricName + " on turn " + (i + 1),
            "class": 'graph_column'
          }, div({
            "class": "graph_bar" + (height === 0 ? " empty" : ''),
            style: "height: " + height + "px;"
          }, ''));
        });
        return graphs.join('');
      })();
    };

    MetricView.prototype.getMetricValue = function(turn, metricName, metricZone) {
      return (metricZone ? turn[metricZone] : turn)[metricName];
    };

    MetricView.prototype.metrics = (function() {
      var metric, metrics, _i, _len;

      metrics = ['Life', 'Poison'];
      for (_i = 0, _len = TYPES.length; _i < _len; _i++) {
        metric = TYPES[_i];
        metrics.push(metric.plural());
      }
      metrics.push('Power');
      metrics.push('Toughness');
      return metrics;
    })();

    MetricView.prototype.zoneNames = ZONE_NAMES.copy().without('commander').without('none').invoke('capitalize');

    return MetricView;

  })();
});

define('help',['detect', 'event', 'modal'], function(features, Event, modal) {
  var helpModal;

  if (!features.handheld) {
    helpModal = new modal.Modal('help', 'close_help');
    $("#help_link").on(Event.down, function() {
      return helpModal.show();
    });
    return after("?:pressed", function() {
      return helpModal.toggle();
    });
  }
});

define('roll',['lib/zepto/zepto', 'event', 'log-turn-action'], function($, Event, logTurnAction) {
  var dice, roll, rollHandler;

  dice = [2, 4, 6, 8, 10, 12, 20, 100];
  roll = function(max) {
    return Math.ceil(max * Math.random());
  };
  rollHandler = function() {
    var max, rolls;

    rolls = (function() {
      var _i, _len, _results;

      _results = [];
      for (_i = 0, _len = dice.length; _i < _len; _i++) {
        max = dice[_i];
        _results.push("" + (roll(max)) + "/" + max);
      }
      return _results;
    })();
    logTurnAction({
      name: rolls.join(', '),
      value: "Roll"
    });
    return alert("Your Dice Rolled:\n" + (rolls.join(', ')));
  };
  $(function() {
    return $("#roll").on(Event.down, rollHandler);
  });
  after("r:pressed", rollHandler);
  return roll;
});

require.config({
  shim: {
    'lib/zepto/zepto': {
      exports: '$'
    }
  }
});

require(['zepto', 'q', 'state-machine', 'mtg', 'deck-url', 'loader-helpers', 'process-deck', 'dom', 'super-select', 'alias', 'string', 'array', 'requestanimationframe', 'detect', 'event', 'time', 'store', 'window', 'css', 'globals', 'analytics', 'progress', 'keys', 'sizes', 'cell', 'cell-collection', 'grid', 'zone-names', 'zone-view', 'zone-views', 'zone-model', 'battlefield-model', 'hand', 'hand-model', 'library-model', 'library', 'zone-initialize', 'distributable-zone-view', 'battlefield-zone-view', 'card-dimensions', 'card-state-helpers', 'card-tap-state', 'card-flip-state', 'card-face-state', 'card-transform-state', 'card-zone-state', 'card-model', 'health', 'draganddrop', 'card-view', 'card-views', 'format-token-data', 'formatted-token-data', 'get-focused-field', 'token-model', 'token-view', 'token-views', 'draw', 'button', 'modal', 'settings', 'get-setting', 'dropdown', 'popup', 'commander', 'stage', 'log-turn-action', 'turn', 'turns', 'turn-model', 'buffs', 'logger', 'help', 'loaded', 'deck-loaded', 'window-loaded', 'roll', 'get-active-card', 'shortcut'], function() {
  var $, Q, deckSrc, deckUrl, deferred, dom, loaderHelpers, mtg, process;

  $ = require('zepto');
  Q = require('q');
  loaderHelpers = require('loader-helpers');
  deckUrl = require('deck-url');
  mtg = require('mtg');
  process = require('process-deck');
  dom = require('dom');
  deferred = Q.defer();
  if (!window.jasmine) {
    $(window).on('hashchange', function() {
      if (loaderHelpers.getPlaytestURL()) {
        return location.reload();
      }
    });
    deckSrc = loaderHelpers.getPlaytestURL();
    if (deckSrc) {
      mtg.deckUrl = deckUrl(deckSrc);
      fire("deck:requested");
      window.processDeck = process.processDeck;
      $('head').append(dom.element('script', {
        src: deckSrc
      }));
      deferred.resolve();
    } else {
      deferred.reject("No deckSrc. Redirecting.");
      location.href = 'http://www.tappedout.net';
    }
    deferred.reject("Jasmine's on the page. Not starting.");
  }
  return deferred.promise;
});

define("load", function(){});

require(["load"]);

