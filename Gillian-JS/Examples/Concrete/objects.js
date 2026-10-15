function check(b, m) { if (!b) throw new Error(m); }
var o = { a: 1, b: "x" };
o.c = o.a + 2;
delete o.b;
var ks = Object.keys(o);
function f(x, y) { return x * y + this.c; }
var r = f.call(o, 3, 4);
var arr = [1, 2, 3];
arr.push(4);
var s = 0;
for (var i = 0; i < arr.length; i++) s += arr[i];
var g = Object.getOwnPropertyDescriptor(o, "a");
Object.defineProperty(o, "z", { get: function () { return 42; }, enumerable: false });
var fr = Object.freeze({ q: 1 });
var frozen = Object.isFrozen(fr);
function C(v) { this.v = v; }
C.prototype.get = function () { return this.v; };
var c = new C(7);
var inst = c instanceof C;
var str = JSON === undefined ? "" : "j";
try { null.x; } catch (e) { var caught = e instanceof TypeError; }
check((r === 15) && (s === 10) && (ks.length === 2) && (o.z === 42) && frozen && (c.get() === 7) && inst && caught && g.writable && !("b" in o), "objects");
