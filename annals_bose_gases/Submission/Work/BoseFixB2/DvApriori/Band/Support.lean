import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.Support`

The three measure-theoretic support lemmas of the FS §6 band analysis:

* `slotProd_slotOp_comm` — a slot operator at a slot not occurring in the list commutes
  with the iterated slot product (operators of distinct slots commute);
* `integral_mul_eq_zero_of_meanFree` — a factor that is constant along a slot times a
  factor with vanishing slot mean integrates to `0` (peel the slot);
* `integrableOn_mul_of_continuous_of_integrable` — continuous factors times an integrable
  weight stay integrable on the box.

None of them uses any regularity of the weight `W`, which is essential: the potential
profile `potWordU` of FS is only known to be measurable/integrable.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. Commutation of a slot operator with the iterated slot product -/

/-- A single slot operator at a slot `j` not occurring in the list `L` commutes with the
iterated slot product `slotProd ℓ L R` (slot operators of distinct slots commute). -/
theorem slotProd_slotOp_comm {ℓ : ℝ} (hℓ : 0 < ℓ) {n j : ℕ} (hj : j < n) (L : List ℕ)
    (hdisj : j ∉ L) (b : Bool) (R : Finset ℕ)
    {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    Work.BoseFixB2.Sector.slotOp ℓ ⟨j, hj⟩ b (slotProd ℓ L R Φ)
      = slotProd ℓ L R (Work.BoseFixB2.Sector.slotOp ℓ ⟨j, hj⟩ b Φ) := by
  unfold slotProd
  exact (Work.BoseFixB2.Sector.blockOpL_comm_slotOp hℓ hj
    (L.map (fun k => (k, decide (k ∈ R)))) hΦ (fun p hp => by
      rw [List.mem_map] at hp
      obtain ⟨k, hkL, rfl⟩ := hp
      exact fun h => hdisj (h ▸ hkL))).symm

/-- The `aP`-form of the commutation of a slot operator with the iterated slot product. -/
theorem slotProd_aP_comm {ℓ : ℝ} (hℓ : 0 < ℓ) {n j : ℕ} (hj : j < n) (L : List ℕ)
    (hdisj : j ∉ L) (R : Finset ℕ) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    Submission.BoseGases.aP ℓ ⟨j, hj⟩ (slotProd ℓ L R Φ)
      = slotProd ℓ L R (Submission.BoseGases.aP ℓ ⟨j, hj⟩ Φ) := by
  have h := slotProd_slotOp_comm hℓ hj L hdisj false R hΦ
  simpa using h

/-- The `aQ`-form of the commutation of a slot operator with the iterated slot product. -/
theorem slotProd_aQ_comm {ℓ : ℝ} (hℓ : 0 < ℓ) {n j : ℕ} (hj : j < n) (L : List ℕ)
    (hdisj : j ∉ L) (R : Finset ℕ) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    Submission.BoseGases.aQ ℓ ⟨j, hj⟩ (slotProd ℓ L R Φ)
      = slotProd ℓ L R (Submission.BoseGases.aQ ℓ ⟨j, hj⟩ Φ) := by
  have h := slotProd_slotOp_comm hℓ hj L hdisj true R hΦ
  simpa using h

/-! ## 2. The mean-free-slot vanishing -/

/-- **The mean-free-slot vanishing.**  If `f` is constant along the `i`-th coordinate and
`g` has vanishing slot-`i` mean (`aP ℓ i g = 0`), then the box integral of `f * g`
vanishes: peeling the slot-`i` coordinate, the inner integral is `f · ℓ³ · aP ℓ i g`. -/
theorem integral_mul_eq_zero_of_meanFree {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {f g : Submission.BoseGases.X n → ℝ}
    (hf : ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
      f (Function.update x i z) = f x)
    (hg : Submission.BoseGases.aP ℓ i g = 0)
    (hint : MeasureTheory.IntegrableOn (fun x => f x * g x) (Submission.BoseGases.abox n ℓ)) :
    (∫ x in Submission.BoseGases.abox n ℓ, f x * g x) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    have hinner : ∀ r : Submission.BoseGases.X m,
        (∫ y in Submission.BoseGases.acube ℓ,
          f (Submission.BoseGases.kcInsN m i (y, r))
            * g (Submission.BoseGases.kcInsN m i (y, r))) = 0 := by
      intro r
      have hfun : (fun y => f (Submission.BoseGases.kcInsN m i (y, r))
            * g (Submission.BoseGases.kcInsN m i (y, r)))
          = (fun y => f (Submission.BoseGases.kcInsN m i (0, r))
            * g (Submission.BoseGases.kcInsN m i (y, r))) := by
        funext y
        rw [Submission.BoseGases.kcInsN_update_zero i y r]
        rw [hf (Submission.BoseGases.kcInsN m i (0, r)) y]
      rw [hfun, MeasureTheory.integral_const_mul]
      have hfun2 : (fun y => g (Submission.BoseGases.kcInsN m i (y, r)))
          = (fun y => g (Function.update (Submission.BoseGases.kcInsN m i (0, r)) i y)) := by
        funext y
        rw [Submission.BoseGases.kcInsN_update_zero i y r]
      rw [hfun2]
      have hsmul : (∫ y in Submission.BoseGases.acube ℓ,
            g (Function.update (Submission.BoseGases.kcInsN m i (0, r)) i y))
          = ℓ ^ 3 * Submission.BoseGases.aP ℓ i g (Submission.BoseGases.kcInsN m i (0, r)) := by
        rw [show Submission.BoseGases.aP ℓ i g (Submission.BoseGases.kcInsN m i (0, r))
              = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
                  g (Function.update (Submission.BoseGases.kcInsN m i (0, r)) i y) from rfl,
          one_div]
        rw [← mul_assoc, mul_inv_cancel₀ (by positivity : ℓ ^ 3 ≠ 0), one_mul]
      rw [hsmul, congrFun hg (Submission.BoseGases.kcInsN m i (0, r))]
      simp
    rw [Submission.BoseGases.abox_integral_peel i _ hint]
    simp only [hinner, MeasureTheory.integral_zero]

/-! ## 3. Integrability of continuous factors times an integrable weight -/

/-- Continuous factors times an integrable weight are integrable on the box: the box is
compact, so the continuous factors are bounded. -/
theorem integrableOn_mul_of_continuous_of_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : Submission.BoseGases.X n → ℝ} (hf : Continuous f) (hg : Continuous g)
    {W : Submission.BoseGases.X n → ℝ}
    (hWi : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox n ℓ)) :
    MeasureTheory.IntegrableOn (fun x => f x * W x * g x) (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hf.continuousOn
  obtain ⟨D, hD⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hg.continuousOn
  have hbdd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖f x * W x * g x‖ ≤ (C * D) * ‖W x‖ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    have h1 : ‖f x‖ ≤ C := hC x hx
    have h2 : ‖g x‖ ≤ D := hD x hx
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) h1
    have hD0 : 0 ≤ D := le_trans (norm_nonneg _) h2
    have hW0 : 0 ≤ ‖W x‖ := norm_nonneg _
    calc ‖f x * W x * g x‖ = ‖f x‖ * ‖W x‖ * ‖g x‖ := by rw [norm_mul, norm_mul]
      _ ≤ (C * ‖W x‖) * D :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hW0) h2 (norm_nonneg _)
            (by positivity)
      _ = (C * D) * ‖W x‖ := by ring
  have hmaj : MeasureTheory.Integrable (fun x => (C * D) * ‖W x‖)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    hWi.norm.const_mul (C * D)
  refine hmaj.mono' ?_ hbdd
  exact (hf.aestronglyMeasurable.mul hWi.aestronglyMeasurable).mul hg.aestronglyMeasurable

end

end Work.BoseFixB2.DvApriori
