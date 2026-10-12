import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG21_bounded` — uniform boundedness of the block II.1 pair fibre

The fibre `pairG21 p Θ A u y` (block II.1 of the `Q₂` pair row, see `pairRowGDefs`) is the
`x`-integral of the integrand

    star (Θ x) * A (x p.1) * A (x p.2) * Θ (update (update x p.1 y) p.2 u) ,

in which the *first* factor `star (Θ x)` sees the state at the un-updated configuration `x` and is
therefore supported in the `n`-particle box `boxPow n ℓ`.  Hence, whenever `Θ` is everywhere
bounded by `C_Θ` and the one-body factor `A` is everywhere bounded by `C_A`, the integrand is
supported in `boxPow n ℓ` (a set of finite volume) and bounded there by `C_Θ² C_A²`, *uniformly in
the two kernel variables* `u` and `y`.  The `L¹`-mass of the fibre is therefore bounded by
`C_Θ² C_A² · vol (boxPow n ℓ)`.

The proof needs no measurability of `Θ` or `A`: the a.e. strongly measurable case is handled by
`MeasureTheory.norm_setIntegral_le_of_norm_le_const`, and the non-a.e.-strongly-measurable case is
handled inside `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae'` (the Bochner integral of
such a function is `0`), which is exactly the form in which Mathlib states the `L¹`-mass bound.
-/

open MeasureTheory

namespace Work.BoseBoxFock

theorem pairG21_bounded {n : ℕ} (p : Fin n × Fin n) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) :
    ∃ C : ℝ, ∀ u y, ‖pairG21 p Θ A u y‖ ≤ C := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hAb
  refine ⟨(max CΘ 0) ^ 2 * (max CA 0) ^ 2
      * (volume : Measure (Work.BoseDict.Xn n)).real (Work.MB.boxPow n ℓ), ?_⟩
  intro u y
  -- the integrand is everywhere bounded by `C_Θ² C_A²`
  have hbd : ∀ x : Work.BoseDict.Xn n,
      ‖star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)‖
        ≤ (max CΘ 0) ^ 2 * (max CA 0) ^ 2 := by
    intro x
    have h1 : ‖Θ x‖ ≤ max CΘ 0 := (hCΘ x).trans (le_max_left _ _)
    have h2 : ‖A (x p.1)‖ ≤ max CA 0 := (hCA _).trans (le_max_left _ _)
    have h3 : ‖A (x p.2)‖ ≤ max CA 0 := (hCA _).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ max CΘ 0 :=
      (hCΘ _).trans (le_max_left _ _)
    calc ‖star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)‖
        = ‖Θ x‖ * ‖A (x p.1)‖ * ‖A (x p.2)‖
            * ‖Θ (Function.update (Function.update x p.1 y) p.2 u)‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_star]
      _ ≤ (max CΘ 0) * (max CA 0) * (max CA 0) * (max CΘ 0) := by gcongr
      _ = (max CΘ 0) ^ 2 * (max CA 0) ^ 2 := by ring
  -- and it vanishes outside the box
  have hsupp : ∀ x : Work.BoseDict.Xn n, x ∉ Work.MB.boxPow n ℓ →
      star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
    intro x hx
    have hz : Θ x = 0 := by
      by_contra h
      exact hx (hΘs (Function.mem_support.mpr h))
    simp [hz]
  have hsfin : (volume : Measure (Work.BoseDict.Xn n)) (Work.MB.boxPow n ℓ) < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact Work.MB.volume_boxPow_lt_top n ℓ
  rw [pairG21]
  calc ‖∫ x : Work.BoseDict.Xn n, star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)‖
      = ‖∫ x in Work.MB.boxPow n ℓ, star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    _ ≤ (max CΘ 0) ^ 2 * (max CA 0) ^ 2
          * (volume : Measure (Work.BoseDict.Xn n)).real (Work.MB.boxPow n ℓ) :=
        norm_setIntegral_le_of_norm_le_const hsfin (fun x _ => hbd x)

end Work.BoseBoxFock
