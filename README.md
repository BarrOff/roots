# roots

This is a root finding library for [Nim](https://nim-lang.org). It is highly influenced by [Julia's](https://julialang.org) library [Roots.jl](https://github.com/JuliaMath/Roots.jl). 

-----------------------------------------------------------


## Status

**This library is still subject to development! Breaking API changes are highly likely!**
The basic structure was taken from Roots.jl and reimplemented as close a possible in Nim. All honor goes to them, I merely took their code and converted it to Nim.
As both languages handle things differently, some changes were unavoidable. An example is passing objects to functions: in Julia it is call-by-reference, whereas in Nim it is usually call-by-value. To accomodate for this, most types are ref types. Duplication of state, option and track objects it thereby avoided. To substitute for Julias [multiple dispatch](https://en.wikipedia.org/wiki/Multiple_dispatch) capabilities Generics are used.

Currently implemented methods are:

- bisection.nim:
	- A42
	- AlefeldPotraShi
	- Bisection
	- BisectionExact
	- Brent
	- FalsePosition
- derivativeFree.nim:
	- Order1
	- Secant
	- Order1B
	- King
	- Order2
	- Steffensen
	- Order2B
	- Esser
	- Order5
	- Order8
	- Thukral8
	- Order16
	- Thukral16
- simple.nim:
	- bracketing
	- secantMethod
	- newton
	- dfree





### Usage

Similar to the Roots.jl way specifying the algorithm is optional. If none is given, Bisection is used.
The chosen algorithm can be passed as the third parameter to the `findZero` function call.
Some examples:

```nim
import math, roots

proc f(x: float): float =
  return exp(x) - x^4

echo findZero(f, (8, 9), Bisection())

# Bisection is the preset method so this should give the same result:
echo findZero(f, (8, 9))

# let's see what it does behind the scenes:
echo findZero(f, (8, 9), verbose = true)
```

When using the FalsePosition algorithm, a number has to be passed to the initialisation call.
The number has to be an int from 1 to 12 and correspondts to the respective galdino function.
Options can be passed to the function by giving a UnivariateZeroOptions object as a last parameter:

```nim
import math, roots

proc f(x: float): float =
  return exp(x) - x^4

var
  options: UnivariateZeroOptions[float, float, float, float]

new(options)
options.xabstol = 1e-6
options.xreltol = 1e-6
options.abstol = 4 * 1e-6
options.reltol = 4 * 1e-6
options.maxevals = 50
options.maxfnevals = 50
options.strict = false

echo findZero(f, (8, 9), FalsePosition(g: 12), verbose = true, options)
```

**At this point, the library can not handle arrays as input. The function may not use integers in its' domain or codomain.**

## To-do

- [x] implement basic structure in Nim
- [x] implement basic bisection algorithm and [AlefeldPotraShi](https://dx.doi.org/10.1090/s0025-5718-1993-1192965-2)
- [x] implement all Bracketing algorithms
- [ ] add tests
- [x] implement non-bracketing methods
- [ ] clean up code and possibly restructure
- [ ] add documentation
- [ ] make code more type generic (possibly handling arrays as parameters)
- [ ] don't export everything, use sane encapsulation
