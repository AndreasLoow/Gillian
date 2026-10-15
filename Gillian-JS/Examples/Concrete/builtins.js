function check(b, m) { if (!b) throw new Error(m); }
var p = { x: 1 };
var q = Object.create(p);
q.y = 2;
check(q.x === 1 && q.hasOwnProperty("y") && !q.hasOwnProperty("x"), "proto");
var cnt = 0; for (var k in q) cnt++;
check(cnt === 2, "forin");
var acc = { _v: 1, get v() { return this._v; }, set v(n) { this._v = n * 2; } };
acc.v = 5;
check(acc.v === 10, "accessor");
function mk() { var n = 0; return function () { return ++n; }; }
var inc = mk(); inc(); check(inc() === 2, "closure");
function args() { return arguments.length; }
check(args(1, 2, 3) === 3, "arguments");
var a = [3, 1, 2];
check(a.length === 3 && a[2] === 2, "array");
a.length = 1; check(a.length === 1 && a[1] === undefined, "array length");
var sealed = Object.seal({ s: 1 });
sealed.t = 2; check(sealed.t === undefined && Object.isSealed(sealed), "seal");
var ne = {}; Object.preventExtensions(ne); check(!Object.isExtensible(ne), "ext");
check(Object.getPrototypeOf(q) === p, "getproto");
check(typeof mk === "function" && typeof p === "object", "typeof");
var names = Object.getOwnPropertyNames({ m: 1, n: 2 });
check(names.length === 2, "names");
var e1 = false; try { undefinedVar; } catch (e) { e1 = e instanceof ReferenceError; }
check(e1, "refErr");
var nf = Object.freeze({ k: 1 }); nf.k = 2; check(nf.k === 1, "frozen write");
check(Boolean(1) && Number("3") === 3 && String(4) === "4", "conv");
var obj2 = new Object(); obj2[1] = "one"; check(obj2["1"] === "one", "numkey");
