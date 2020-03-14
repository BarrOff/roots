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

  test "default settings":
    let
      z = findZero(f, (8.0, 9.0))
    check(z == 8.613169456441399)

  test "default settings for A42":
    let
      z = findZero(f, (8.0, 9.0), A42())
    check(z == 8.613169456441399)

  test "default settings for AlefeldPotraShi":
    let
      z = findZero(f, (8.0, 9.0), AlefeldPotraShi())
    check(z == 8.613169456441399)

  test "default settings for Bisection":
    let
      z1 = findZero(f, (8.0, 9.0))
      z2 = findZero(f, (8.0, 9.0), Bisection())
    check(z1 == z2)
    check(z2 == 8.613169456441399)

  test "default settings for BisectionExact":
    let
      z = findZero(f, (8.0, 9.0), BisectionExact())
    check(z == 8.613169456441399)

  test "default settings for FalsePosition":
    let
      z = findZero(f, (8.0, 9.0), FalsePosition(g: 12))
    check(z != 8.613169456441399)

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
