# This is just an example to get you started. You may wish to put all of your
# tests into a single file, or separate them into multiple `test1`, `test2`
# etc. files (better names are recommended, just make sure the name starts with
# the letter 't').
#
# To run these tests, simply execute `nimble test`.

import math, unittest
import roots

suite "float: bracketing Tests":
  setup:
    proc f(x: float): float =
      return exp(x) - x^4
    proc f1(x: float): float =
      return sinh(x - 2.0) + x^2 - 4.5 * x + 4.5

  test "default settings":
    let
      z = findZero(f, (8.0, 9.0))
    check(z == 8.613169456441399)

  test "default settings for A42":
    let
      z = findZero(f, (8.0, 9.0), A42())
      z1 = findZero(f1, (-0.5, 2.0), A42())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125697)

  test "default settings for AlefeldPotraShi":
    let
      z = findZero(f, (8.0, 9.0), AlefeldPotraShi())
      z1 = findZero(f1, (-0.5, 2.0), AlefeldPotraShi())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125698)

  test "default settings for Bisection":
    let
      z1 = findZero(f, (8.0, 9.0))
      z2 = findZero(f, (8.0, 9.0), Bisection())
      z3 = findZero(f1, (-0.5, 2.0), Bisection())
    check(z1 == z2)
    check(z2 == 8.613169456441399)
    check(z3 == 0.8282194527125697)

  test "default settings for BisectionExact":
    let
      z = findZero(f, (8.0, 9.0), BisectionExact())
      z1 = findZero(f1, (-0.5, 2.0), BisectionExact())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125695)

  test "default settings for FalsePosition":
    let
      z = findZero(f, (8.0, 9.0), FalsePosition(g: 12))
      z1 = findZero(f1, (-0.5, 2.0), FalsePosition(g: 12))
    check(z != 8.613169456441399)
    check(z1 == 0.8282194527125698)

suite "int: bracketing Tests":
  setup:
    proc f(x: float): float =
      return exp(x) - x^4

  test "default settings":
    let
      z = findZero(f, (8, 9))
    check(z == 8.613169456441399)

  test "default settings for A42":
    let
      z = findZero(f, (8, 9), A42())
    check(z == 8.613169456441399)

  test "default settings for AlefeldPotraShi":
    let
      z = findZero(f, (8, 9), AlefeldPotraShi())
    check(z == 8.613169456441399)

  test "default settings for Bisection":
    let
      z1 = findZero(f, (8, 9))
      z2 = findZero(f, (8, 9), Bisection())
    check(z1 == z2)
    check(z2 == 8.613169456441399)

  test "default settings for BisectionExact":
    let
      z = findZero(f, (8, 9), BisectionExact())
    check(z == 8.613169456441399)

  test "default settings for FalsePosition":
    let
      z = findZero(f, (8, 9), FalsePosition(g: 12))
    check(z != 8.613169456441399)

suite "kwargs Tests":
  setup:
    proc f(x: float): float =
      return exp(x) - x^4

  test "kwargs without algorithm":
    let
      kw = UnivariateZeroOptions[float, float, float, float]()
    initOptions2(kw, Bisection())
    let
      z = findZero(f, (8.0, 9.0), kwargs = kw)
    check(z == 8.613169456441399)

  test "kwargs with A42":
    let
      kw = UnivariateZeroOptions[float, float, float, float]()
    initOptions2(kw, A42())
    let
      z = findZero(f, (8.0, 9.0), A42(), kwargs = kw)
    check(z == 8.613169456441399)

  test "kwargs with AlefeldPotraShi":
    let
      kw = UnivariateZeroOptions[float, float, float, float]()
    initOptions2(kw, AlefeldPotraShi())
    let
      z = findZero(f, (8.0, 9.0), AlefeldPotraShi(), kwargs = kw)
    check(z == 8.613169456441399)

  test "kwargs with Bisection":
    let
      kw = UnivariateZeroOptions[float, float, float, float]()
    initOptions2(kw, Bisection())
    let
      z1 = findZero(f, (8.0, 9.0), kwargs = kw)
      z2 = findZero(f, (8.0, 9.0), Bisection(), kwargs = kw)
    check(z1 == z2)
    check(z2 == 8.613169456441399)

  test "kwargs with BisectionExact":
    let
      kw = UnivariateZeroOptions[float, float, float, float]()
    initOptions2(kw, BisectionExact())
    let
      z = findZero(f, (8.0, 9.0), BisectionExact(), kwargs = kw)
    check(z == 8.613169456441399)

  test "kwargs with FalsePosition":
    let
      kw = UnivariateZeroOptions[float, float, float, float]()
    initOptions2(kw, FalsePosition(g: 12))
    let
      z = findZero(f, (8.0, 9.0), FalsePosition(g: 12), kwargs = kw)
    check(z != 8.613169456441399)

suite "float: derivativeFree Tests":
  setup:
    proc f(x: float): float =
      return exp(x) - x^4
    proc f1(x: float): float =
      return sinh(x - 2.0) + x^2 - 4.5 * x + 4.5

  test "default settings for Order1":
    let
      z = findZero(f, 8.0, Order1())
      z1 = findZero(f1, 0.0, Order1())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125697)

  test "default settings for Secant":
    let
      z = findZero(f, 8.0, Secant())
      z1 = findZero(f1, 0.0, Secant())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125697)

  test "default settings for Order1B":
    let
      z = findZero(f, 8.0, Order1B())
      z1 = findZero(f1, 0.0, Order1B())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125691)

  test "default settings for King":
    let
      z = findZero(f, 8.0, King())
      z1 = findZero(f1, 0.0, King())
    check(z == 8.0)
    check(z1 == -0.9949612672763375)

  test "default settings for Order2":
    let
      z = findZero(f, 8.0, Order2())
      z1 = findZero(f1, 0.0, Order2())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125698)

  test "default settings for Steffensen":
    let
      z = findZero(f, 8.0, Steffensen())
      z1 = findZero(f1, 0.0, Steffensen())
    check(z == 8.0)
    check(z1 == 0.8282194527125695)

  test "default settings for Order2B":
    let
      z = findZero(f, 8, Order2B())
      # z1 = findZero(f1, 0.0, Order2B())
    check(z == 8.613169456441396)
    # check(z1 == 0.8282194527125696)

  test "default settings for Esser":
    let
      z = findZero(f, 8.0, Esser())
      z1 = findZero(f1, 0.0, Esser())
    check(z == 8.0)
    check(z1 == 0.8282194534204859)

  test "default settings for Order5":
    let
      z = findZero(f, 8.0, Order5())
      z1 = findZero(f1, 0.0, Order5())
    check(z == 1.4296118247255556)
    check(z1 == 0.8282194527125691)

  test "default settings for Order8":
    let
      z = findZero(f, 8.0, Order8())
      z1 = findZero(f1, 0.0, Order8())
    check(z == 8.613169456441399)
    check(z1 == 0.8282194527125698)

  test "default settings for Thukral8":
    let
      z = findZero(f, 8.0, Thukral8())
      z1 = findZero(f1, 0.0, Thukral8())
    check(z == 8.699843063828167)
    check(z1 == 0.8282194527125692)

  test "default settings for Order16":
    let
      z = findZero(f, 8.0, Order16())
      z1 = findZero(f1, 0.0, Order16())
    check(z == 8.613169456441398)
    check(z1 == 0.8282194527125695)

  test "default settings for Thukral16":
    let
      z = findZero(f, 8.0, Thukral16())
      z1 = findZero(f1, 0.0, Thukral16())
    check(z == 8.632072307059465)
    check(z1 == 0.8282194527125695)
