import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The tricorn family `T_c(z) = z̄² + c`: basic dynamics

This file sets up the antiholomorphic quadratic family of `ChallengeDeps` together with the
dynamical notions that the landing theory for its external rays is phrased with.

Throughout, `Tantibar c` is the map `z ↦ z̄² + c` of `ChallengeDeps`, and

* `Tsq c = Tantibar c ∘ Tantibar c` is its holomorphic second iterate,
  `Tsq c z = (z² + c̄)² + c`.

## Conventions

* `z` is a *periodic point of period `k`* for `T_c` if `(T_c)^[k] z = z` with `k > 0`.  For
  antiholomorphic maps there is no notion of "exact period" in the analytic sense (a point of
  odd period `k` is a fixed point of the holomorphic `2k`-th iterate).
* The *multiplier* of a periodic point of odd period `k` is measured **through the holomorphic
  second return map** `(T_c)^{2k} = (Tsq c)^[k]`: `multiplier2 c k z = deriv ((Tsq c)^[k]) z`.
  This is the quantity that governs the local dynamics in the antiholomorphic setting, and it
  is a nonnegative real number (`deriv_tsq_iterate_odd_real` below); its modulus is the square
  of the modulus of the "antilinear multiplier" of `T_c^[k]` (HS §2).
* Consequently a periodic point is *repelling* when `1 < ‖multiplier2‖` and *parabolic* when
  `multiplier2 = 1`.  For odd `k` these two cases exhaust the possibilities on the Julia set;
  in particular on the boundary of a hyperbolic component of odd period all parabolic points
  have multiplier exactly `+1` (HS §2).
-/

noncomputable section

namespace Work.Landing

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The holomorphic second iterate of the antiholomorphic quadratic `T_c`:
`Tsq c z = T_c(T_c z) = (z² + c̄)² + c`. -/
def Tsq (c : ℂ) : ℂ → ℂ := fun z => (z ^ 2 + star c) ^ 2 + c

@[simp]
theorem Tsq_apply (c z : ℂ) : Tsq c z = (z ^ 2 + star c) ^ 2 + c := rfl

@[simp]
theorem Tantibar_apply (c z : ℂ) : Tantibar c z = star z ^ 2 + c := rfl

/-- `z` is a periodic point of period `n` for `f`: `n > 0` and `f^[n] z = z`. -/
def PeriodicPoint (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Prop := 0 < n ∧ f^[n] z = z

/-- `z` is a periodic point of `f`. -/
def IsPeriodic (f : ℂ → ℂ) (z : ℂ) : Prop := ∃ n : ℕ, PeriodicPoint f n z

/-- The multiplier of the holomorphic second return map `(T_c)^{2k} = (Tsq c)^[k]` at `z`. -/
def multiplier2 (c : ℂ) (k : ℕ) (z : ℂ) : ℂ := deriv ((Tsq c)^[k]) z

/-- A repelling periodic point of odd period `k` of `T_c`, measured through the holomorphic
second return map. -/
def IsRepelling (c : ℂ) (k : ℕ) (z : ℂ) : Prop :=
  PeriodicPoint (Tantibar c) k z ∧ 1 < ‖multiplier2 c k z‖

/-- A parabolic periodic point of odd period `k` of `T_c`: the multiplier of the holomorphic
second return map is exactly `1`. -/
def IsParabolic (c : ℂ) (k : ℕ) (z : ℂ) : Prop :=
  PeriodicPoint (Tantibar c) k z ∧ multiplier2 c k z = 1

/-- The conclusion of the landing theorem for periodic rays (Milnor 18.10). -/
def IsRepellingOrParabolic (c : ℂ) (k : ℕ) (z : ℂ) : Prop :=
  IsRepelling c k z ∨ IsParabolic c k z

/-- An attracting periodic point of odd period `k` of `T_c`, again measured through the
holomorphic second return map. -/
def IsAttracting (c : ℂ) (k : ℕ) (z : ℂ) : Prop :=
  PeriodicPoint (Tantibar c) k z ∧ ‖multiplier2 c k z‖ < 1

/-- `c` belongs to the hyperbolic component of period `n`: the critical orbit is attracted to
an attracting cycle of period `n`.  (This is the definition one wants for the tricorn; for the
non-real period-`5` component of HS Fig. 3/6 one adds `c ∉ ℝ`.) -/
def InHyperbolicComponent (c : ℂ) (n : ℕ) : Prop :=
  ∃ z : ℂ, IsAttracting c n z ∧ ∃ j : ℕ, (Tantibar c)^[j] 0 = z

/-- The geometric input of the landing theorem, isolated as a hypothesis: an attracting
periodic point of `T_c` has a neighbourhood disjoint from the basin of infinity `U`.  (In the
tricorn, `U` is the basin of infinity, whose complement is the filled Julia set, so this says
that attracting cycles lie in the interior of the filled Julia set — the only unbounded Fatou
component is the basin of infinity.) -/
def AttractingAwayFromInfinity (c : ℂ) (U : Set ℂ) : Prop :=
  ∀ z : ℂ, (∃ k : ℕ, IsAttracting c k z) → ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w - z‖ < ε → w ∉ U

end Work.Landing
