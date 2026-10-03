// TC       |  JS
// ---------+-----------
// t        |  []
// t a      |  [a]
// t a b    |  [b, a]
// t a b c  |  [c, b, a]

const apply = (a, b) => {
  const expression = [b, ...a]
  const todo = [expression];
  while (todo.length) {
    const f = todo.pop();
    if (f.length < 3) continue;
    todo.push(f);
    const a = f.pop(), b = f.pop(), c = f.pop();
    if (a.length === 0) f.push(...b);
    else if (a.length === 1) {
      const newPotRedex = [c, ...b];
      f.push(newPotRedex, c, ...a[0]);
      todo.push(newPotRedex);
    }
    else if (a.length === 2)
      if (c.length === 0) f.push(...a[1]);
      else if (c.length === 1) f.push(c[0], ...a[0]);
      else if (c.length === 2) f.push(c[0], c[1], ...b);
  }
  return expression;
};

// Example: Negating booleans
const _false = [];
const _true = [[]];
const _not = [[],[[_false,[]],_true]];
apply(_not, _false); // [[]] = _true
apply(_not, _true);  // []   = _false
