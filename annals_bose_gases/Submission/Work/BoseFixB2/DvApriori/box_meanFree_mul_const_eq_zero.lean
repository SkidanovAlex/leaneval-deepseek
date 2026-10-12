import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

open MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Submission.BoseGases

/-- Updating a non-inserted slot of an insertion `kcInsN m k (y, r)` re-inserts with the
updated rest: the slot `k.succAbove j'` of the insertion is exactly the slot `j'` of `r`. -/
lemma update_kcInsN_succAbove {m : ℕ} (k : Fin (m + 1)) (j' : Fin m)
    (y z : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X m) :
    Function.update (Submission.BoseGases.kcInsN m k (y, r)) (k.succAbove j') z
      = Submission.BoseGases.kcInsN m k (y, Function.update r j' z) := by
  funext i
  by_cases hi : i = k
  · rw [hi, Function.update_apply, if_neg (Ne.symm (Fin.succAbove_ne k j')),
      Submission.BoseGases.kc_insN_apply_same, Submission.BoseGases.kc_insN_apply_same]
  · rcases Fin.exists_succAbove_eq hi with ⟨l, rfl⟩
    by_cases hl : l = j'
    · subst hl
      rw [Function.update_apply, if_pos rfl,
        Submission.BoseGases.kc_insN_apply_succ, Function.update_apply, if_pos rfl]
    · rw [Function.update_apply, if_neg (fun h => hl (Fin.succAbove_right_injective h)),
        Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ,
        Function.update_apply, if_neg hl]

/-- If `W` has vanishing box mean in the slot `k` and `V` is independent of the slot-`k`
variable, then for all `z z'` the box integral of `W(x_j ← z)·V(x_j ← z')` vanishes: the `x_j`
and the `x_k` integrations factor, and the `x_k` mean of `W` is zero. -/
theorem box_meanFree_mul_const_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j k : Fin n} (hjk : j ≠ k)
    {W V : Submission.BoseGases.X n → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hfree : ∀ y : Submission.BoseGases.X n,
      (1 / ℓ ^ 3) * ∫ w in Submission.BoseGases.acube ℓ, W (Function.update y k w) = 0)
    (hconst : ∀ (y : Submission.BoseGases.X n) (w : EuclideanSpace ℝ (Fin 3)),
      V (Function.update y k w) = V y) :
    ∀ z z' : EuclideanSpace ℝ (Fin 3),
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (W (Function.update x j z) * V (Function.update x j z'))) = 0 := by
  intro z z'
  cases n with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjk
    have hGcont : Continuous (fun x : Submission.BoseGases.X (m + 1) =>
        W (Function.update x j z) * V (Function.update x j z')) :=
      (hW.comp (continuous_id.update j continuous_const)).mul
        (hV.comp (continuous_id.update j continuous_const))
    have hGint : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X (m + 1) =>
          W (Function.update x j z) * V (Function.update x j z'))
        (Submission.BoseGases.abox (m + 1) ℓ) MeasureTheory.volume :=
      Submission.BoseGases.integrableOn_abox_of_continuous hℓ hGcont
    have hae : (fun x : Submission.BoseGases.X (m + 1) =>
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (W (Function.update x j z) * V (Function.update x j z')))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)]
        (fun x => W (Function.update x j z) * V (Function.update x j z')) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable (m + 1) ℓ)] with x hx
      have hmem : x j ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
        have h1 : x j ∈ Submission.BoseGases.acube ℓ :=
          (Submission.BoseGases.mem_abox_iff (m + 1) ℓ x).mp hx j
        simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
        simpa using h1
      have hind : Work.BoseKinLoc.indU ℓ 0 (x j) = 1 := by
        rw [Work.BoseKinLoc.indU, Set.indicator_of_mem hmem]
      rw [hind, one_mul]
    calc
      (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (W (Function.update x j z) * V (Function.update x j z')))
          = ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              W (Function.update x j z) * V (Function.update x j z') :=
            MeasureTheory.integral_congr_ae hae
      _ = ∫ r in Submission.BoseGases.abox m ℓ, (∫ y in Submission.BoseGases.acube ℓ,
              W (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z)
                * V (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z')) :=
            Submission.BoseGases.abox_integral_peel k _ hGint
      _ = 0 := by
        have hinner : ∀ r : Submission.BoseGases.X m,
            (∫ y in Submission.BoseGases.acube ℓ,
              W (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z)
                * V (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z')) = 0 := by
          intro r
          have hzeroW : (∫ y in Submission.BoseGases.acube ℓ,
              W (Function.update
                (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y)) = 0 := by
            have h := hfree (Submission.BoseGases.kcInsN m k (0, Function.update r j' z))
            have hne : (1 : ℝ) / ℓ ^ 3 ≠ 0 := by positivity
            exact (mul_eq_zero.mp h).resolve_left hne
          have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
              W (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z)
                * V (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z')
              = W (Function.update
                    (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y)
                * V (Function.update
                    (Submission.BoseGases.kcInsN m k (0, Function.update r j' z')) k y) := by
            intro y
            have e1 : Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z
                = Function.update
                    (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y := by
              rw [← hj', update_kcInsN_succAbove, Submission.BoseGases.kcInsN_update_zero]
            have e2 : Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z'
                = Function.update
                    (Submission.BoseGases.kcInsN m k (0, Function.update r j' z')) k y := by
              rw [← hj', update_kcInsN_succAbove, Submission.BoseGases.kcInsN_update_zero]
            rw [e1, e2]
          have hpt2 : ∀ y : EuclideanSpace ℝ (Fin 3),
              W (Function.update
                  (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y)
                * V (Function.update
                    (Submission.BoseGases.kcInsN m k (0, Function.update r j' z')) k y)
              = V (Submission.BoseGases.kcInsN m k (0, Function.update r j' z'))
                * W (Function.update
                    (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y) := by
            intro y
            rw [hconst (Submission.BoseGases.kcInsN m k (0, Function.update r j' z')) y]
            ring
          calc
            (∫ y in Submission.BoseGases.acube ℓ,
              W (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z)
                * V (Function.update (Submission.BoseGases.kcInsN m k (y, r)) j z'))
                = ∫ y in Submission.BoseGases.acube ℓ,
                    W (Function.update
                        (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y)
                      * V (Function.update
                        (Submission.BoseGases.kcInsN m k (0, Function.update r j' z')) k y) :=
                  MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
            _ = ∫ y in Submission.BoseGases.acube ℓ,
                    V (Submission.BoseGases.kcInsN m k (0, Function.update r j' z'))
                      * W (Function.update
                        (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y) :=
                  MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt2)
            _ = V (Submission.BoseGases.kcInsN m k (0, Function.update r j' z'))
                  * (∫ y in Submission.BoseGases.acube ℓ,
                      W (Function.update
                        (Submission.BoseGases.kcInsN m k (0, Function.update r j' z)) k y)) := by
                  rw [MeasureTheory.integral_const_mul]
            _ = V (Submission.BoseGases.kcInsN m k (0, Function.update r j' z')) * 0 := by
                  rw [hzeroW]
            _ = 0 := by ring
        simp only [hinner, MeasureTheory.integral_zero]

end

end Work.BoseFixB2.DvApriori
