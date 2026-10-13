/-
Copyright: work module for the Elgindi finite-time singularity project.

# Tonelli slices of an integrand over the open quadrant

If `g` is (Lebesgue-)integrable over the open quadrant `Q0 = (0,∞) × (0,π/2)` then its angular
slices are integrable for almost every `z ∈ Iz = [0,∞)`, and the partial integral
`z ↦ ∫_θ∈Iθ g z θ` is integrable on `Iz`.

Both statements are the Fubini/Tonelli theorems for the product measure
`(volume.restrict (Ioi 0)).prod (volume.restrict (Ioo 0 (π/2)))`, which by
`Measure.prod_restrict` is exactly the restriction of the planar Lebesgue measure to `Q0`.
The only difference between the domains appearing here (`Iz`, `Iθ`) and the open domains of
the product (`Ioi 0`, `Ioo 0 (π/2)`) is the *null* boundary (`{0}` in `z`, and `{0, π/2}` in
`θ`), so the restricted measures agree (`Measure.restrict_congr_set`) and the statements
transfer verbatim.  Note that this is exactly the shape the `ℋ^k`-statements need: the
presumed integrability is *only* known on the open quadrant (the boundary of `Q0` carries no
information), and the conclusion is therefore an a.e. statement in `z`.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.Joint

open MeasureTheory Set
open scoped Real

theorem tonelli_slices_of_integrableOn_Q0 {g : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => g p.1 p.2)
      Work.FTS.EllipticEst.Q0) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ : ℝ => g z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, g z θ)
        Work.Spaces.Iz := by
  -- ### `Iz = [0,∞)` differs from `(0,∞)` by the null set `{0}`
  have hIz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (t := {0}) ?_ (measure_singleton 0)
      intro x hx
      rw [Set.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Set.mem_Ici] at hx1
      rw [Set.mem_Ioi] at hx2
      rw [Set.mem_singleton_iff]
      exact le_antisymm (not_lt.mp hx2) hx1
    · rw [sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]
  -- ### `Iθ = [0,π/2]` differs from `(0,π/2)` by the null set `{0, π/2}`
  have hIθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl, MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
      · intro x hx
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢
        obtain ⟨⟨h0, h1⟩, h2⟩ := hx
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        · right
          by_contra hx2
          exact h2 ⟨lt_of_le_of_ne h0 (Ne.symm hx0), lt_of_le_of_ne h1 hx2⟩
      · rw [Set.insert_eq,
          measure_union_null (measure_singleton (0 : ℝ)) (measure_singleton (π / 2))]
    · rw [sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]
  have hIz' := Measure.restrict_congr_set hIz
  have hIθ' := Measure.restrict_congr_set hIθ
  -- ### the product measure of the open half-strip is the restriction to `Q0`
  have hEq : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      = MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0 := by
    rw [show Work.FTS.EllipticEst.Q0 = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) from rfl]
    exact Measure.prod_restrict _ _
  have hprod : MeasureTheory.Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))) := by
    rw [hEq]
    exact hint
  -- ### Tonelli: a.e. angular slice integrability, and integrability of the partial integral
  constructor
  · rw [hIz']
    refine (hprod.prod_right_ae).mono fun z hz => ?_
    rwa [MeasureTheory.IntegrableOn, hIθ']
  · rw [MeasureTheory.IntegrableOn, hIz', hIθ']
    exact hprod.integral_prod_left

end Work.FTS.PhiStar.Honesty.SlotsLimit.Joint
