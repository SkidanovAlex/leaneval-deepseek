import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Escape dynamics, filled Julia sets and the Green function

This file sets up the vocabulary of the escape/Green-function chapter of the mandelbar project.

The main notion is `MonicGrowth f d A`: a continuous map `f : ℂ → ℂ` whose action on norms is
sandwiched between the monic degree-`d` behaviour `‖z‖^d - A ≤ ‖f z‖ ≤ ‖z‖^d + A`.  Both the
holomorphic family `z ↦ z^d + c` and the antiholomorphic family `z ↦ z̄^d + c` satisfy this with
`A = ‖c‖` (and `d = 2` for the mandelbar/tricorn).

The Green function is defined as the pointwise limit `G_f(z) = lim_n d^{-n} log⁺ ‖f^[n] z‖`
(where `log⁺ x = log (max 1 x)`); it vanishes exactly on the filled Julia set
`K_f = {z | the orbit of z is bounded}`.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-! ## The maps -/

/-- The degree-`d` unicritical **antiholomorphic** polynomial `z ↦ z̄^d + c`. -/
def Td (d : ℕ) (c : ℂ) : ℂ → ℂ := fun z => (starRingEnd ℂ z) ^ d + c

/-- The degree-`d` unicritical **holomorphic** polynomial `z ↦ z^d + c`. -/
def Tpoly (d : ℕ) (c : ℂ) : ℂ → ℂ := fun z => z ^ d + c

/-- `Td 2` is the mandelbar/tricorn iterator `Tantibar` of the challenge file. -/
theorem Td_two_eq : Td 2 = LeanEval.ComplexAnalysis.Tantibar := rfl

/-- `Tpoly 2` is the Mandelbrot family `z ↦ z^2 + c`. -/
theorem Tpoly_two_apply (c z : ℂ) : Tpoly 2 c z = z ^ 2 + c := rfl

/-! ## Monic growth bounds -/

/-- `MonicGrowth f d A` says that `f` is continuous and that its norm behaviour is that of a
monic degree-`d` map up to the additive constant `A`.  This is the only structure needed for the
escape-radius, filled-Julia and Green-function theory. -/
structure MonicGrowth (f : ℂ → ℂ) (d : ℕ) (A : ℝ) : Prop where
  protected continuous : Continuous f
  protected norm_le : ∀ z : ℂ, ‖f z‖ ≤ ‖z‖ ^ d + A
  protected le_norm : ∀ z : ℂ, ‖z‖ ^ d - A ≤ ‖f z‖

/-! ## The escaping region, orbits and the Green function -/

/-- The open **escaping region** `{z | max 2 A < ‖z‖}`.  For a degree-`d` map with `d ≥ 2` and
monic growth constant `A`, every point of this region escapes to infinity (this is the sharp
escape criterion, valid as soon as the orbit exceeds `max 2 A`). -/
def escapeRegion (A : ℝ) : Set ℂ := {z : ℂ | max 2 A < ‖z‖}

/-- `log⁺ x = log (max 1 x)`, the positive part of the logarithm. -/
def logPos (x : ℝ) : ℝ := Real.log (max 1 x)

/-- The `n`-th partial Green function `d^{-n} log⁺ ‖f^[n] z‖`. -/
def greenIter (f : ℂ → ℂ) (d : ℕ) (z : ℂ) (n : ℕ) : ℝ :=
  ((d : ℝ) ^ n)⁻¹ * logPos ‖(f^[n]) z‖

/-- The **Green function** `G_f(z) = lim_{n→∞} d^{-n} log⁺ ‖f^[n] z‖`, as the limit of the
partial Green functions `greenIter f d z`.  Under a `MonicGrowth` hypothesis this limit exists
(see `green_tendsto`): it equals `0` exactly for `z` in the filled Julia set, and is positive on
the escaping region. -/
def green (f : ℂ → ℂ) (d : ℕ) (z : ℂ) : ℝ :=
  limUnder atTop (greenIter f d z)

/-- The **filled Julia set** `K_f` of `f`: the set of points with bounded orbit.  For the
mandelbar family this is the filled tricorn `K_c`. -/
def filledJulia (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | Bornology.IsBounded (range fun n : ℕ => (f^[n]) z)}

/-! ## The tricorn (mandelbar) family -/

/-- The **potential** of the tricorn family at the parameter `c`: the Green function of `Tantibar c`
evaluated at the critical point `0`, i.e. `G_c(0)`.  This is the (exponential of the) parameter
Böttcher coordinate up to the standard normalisation. -/
def greenParam (c : ℂ) : ℝ := green (LeanEval.ComplexAnalysis.Tantibar c) 2 0

/-- The filled tricorn `K_c` of the parameter `c`, as a set in the dynamical plane. -/
def filledTricorn (c : ℂ) : Set ℂ := filledJulia (LeanEval.ComplexAnalysis.Tantibar c)

end Work.Escape
