/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Mathlib
import Submission.Work.Twist.stdGradingChart

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `chartAwayMapInv ∘ chartAwayMap = id`

`Work.Twist.chartAwayMap 𝕜 n i : A⁰_{X_i} →+* A⁰_{X_0}` and
`Work.Twist.chartAwayMapInv 𝕜 n i : A⁰_{X_0} →+* A⁰_{X_i}` are the maps on the degree-zero
parts of the homogeneous localisations induced by the coordinate transposition `X₀ ↔ X_i`
(`Work.Twist.chartRename`, i.e. `MvPolynomial.rename (Equiv.swap 0 i)`).

Both are instances of `HomogeneousLocalization.map` for the *same* graded ring endomorphism
`chartRename 𝕜 n i`, so their composite is `map` of the composite
`(chartRename).comp (chartRename)`, which is the identity by `chartRename_comp_self`
(the transposition is an involution).  Hence `chartAwayMapInv ∘ chartAwayMap = id` by
`HomogeneousLocalization.map_comp` and `HomogeneousLocalization.map_id`.
-/

set_option autoImplicit false

namespace Work.Twist

open MvPolynomial HomogeneousLocalization

noncomputable section

/-- **`chartAwayMapInv` is a left inverse of `chartAwayMap`.**  Both maps are induced by the same
coordinate transposition, so their composite is induced by the square of the transposition, i.e. by
the identity. -/
theorem chartAwayMapInv_comp_chartAwayMap (𝕜 : Type) [CommRing 𝕜] (n : ℕ)
    (i : Fin (n + 1)) :
    (Work.Twist.chartAwayMapInv 𝕜 n i).comp (Work.Twist.chartAwayMap 𝕜 n i) =
      RingHom.id (HomogeneousLocalization.Away (Work.Twist.stdGrading 𝕜 n)
        (MvPolynomial.X i)) := by
  have h1 : Submonoid.powers (MvPolynomial.X i) ≤
      (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)))).comap (chartRename 𝕜 n i) :=
    fun x hx => by rcases hx with ⟨k, rfl⟩; exact ⟨k, by rw [map_pow, chartRename_X_self]⟩
  have h0 : Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1))) ≤
      (Submonoid.powers (MvPolynomial.X i)).comap (chartRename 𝕜 n i) :=
    fun x hx => by rcases hx with ⟨k, rfl⟩; exact ⟨k, by rw [map_pow, chartRename_X_zero]⟩
  have e1 : chartAwayMap 𝕜 n i = HomogeneousLocalization.map (chartRename 𝕜 n i) h1 := by
    unfold chartAwayMap
    congr 1
  have e2 : chartAwayMapInv 𝕜 n i = HomogeneousLocalization.map (chartRename 𝕜 n i) h0 := by
    unfold chartAwayMapInv
    congr 1
  rw [e1, e2, ← HomogeneousLocalization.map_comp h1 h0]
  rw [← HomogeneousLocalization.map_id (stdGrading 𝕜 n) (Submonoid.powers (MvPolynomial.X i))]
  congr 1
  exact chartRename_comp_self 𝕜 n i

end

end Work.Twist
