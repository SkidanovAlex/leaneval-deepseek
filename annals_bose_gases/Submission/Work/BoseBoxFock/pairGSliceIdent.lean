import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGFibre
import Submission.Work.BoseBoxFock.setIntegral_confY13_slice
import Submission.Work.BoseBoxFock.setIntegral_insertCoord2_slice
import Submission.Work.BoseBoxFock.setIntegral_insertCoord_slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock` — the slice identities of the `pairG_dir_leB` estimate

This module collects, in the vocabulary of `pairGCore`, the seven slice identities that
`pairGFibre`'s per-fibre assembly lemmas (`pairEnergy_pairGc13_le`, `pairEnergy_pairGc23_le`,
`pairEnergy_pairGc21_le`) consume:

* `∫_{boxL} memX13 = pinL2`, `∫_{boxL} dirX13 ≤ pinDir`,
* `∫_{boxL} memY13 = ℓ³·pinL2`,
* `∫_{boxL×boxL} memX23 = pinL2`, `∫_{boxL×boxL} dirX23 ≤ pinDir`,
* `∫_{boxL×boxL} memY21(z.2,z.1) = pinL2`, `∫_{boxL×boxL} dirY21(z.2,z.1) ≤ pinDir`.

The measure-theoretic content (the coordinate-insertion slice identities) is in the sibling
modules `setIntegral_insertCoord_slice`, `setIntegral_insertCoord2_slice` and
`setIntegral_confY13_slice`; here we only convert the slice vocabulary into the vocabulary of the
fibres (and swap two integration orders, `integral_integral_swap`).

`sorry`-free.
-/

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. Elementary integrability facts -/

/-- A continuous function is integrable on the `n`-particle box. -/
theorem integrableOn_abox_of_continuous {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Xn n → ℝ}
    (hf : Continuous f) : IntegrableOn f (Submission.BoseGases.abox n ℓ) := by
  have hcomp : IsCompact (Submission.BoseGases.abox n ℓ) := by
    rw [Submission.BoseGases.abox_eq_pi_acube]
    exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hf.continuousOn
  exact IntegrableOn.of_bound (lt_top_iff_ne_top.mpr hcomp.measure_ne_top)
    hf.aestronglyMeasurable C (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict hcomp.measurableSet] with x hx
      exact hC x hx)

/-- `x ↦ fderiv ℝ Θ₀ x v` is continuous for smooth `Θ₀`. -/
theorem continuous_fderiv_apply {n : ℕ} {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (v : Xn n) : Continuous (fun x : Xn n => fderiv ℝ Θ₀ x v) :=
  (hΘ₀.continuous_fderiv (by simp)).clm_apply continuous_const

/-! ## 2. Fubini on the box squared -/

/-- The product-measure integral on the box squared is the iterated integral. -/
theorem setIntegral_boxL_prod_eq_iterated {ℓ : ℝ} {F : E3 × E3 → ℝ}
    (hint : IntegrableOn F (boxL ℓ ×ˢ boxL ℓ)) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, F z) = ∫ w in boxL ℓ, ∫ y in boxL ℓ, F (w, y) := by
  rw [show (∫ z in boxL ℓ ×ˢ boxL ℓ, F z)
      = ∫ z in boxL ℓ ×ˢ boxL ℓ, F z ∂(volume.prod volume) from rfl]
  exact MeasureTheory.setIntegral_prod F hint

/-- **Exchanging the two integration orders on the box squared.** -/
theorem iterated_boxL_swap {ℓ : ℝ} {H : E3 → E3 → ℝ}
    (hH : Integrable (Function.uncurry (fun (a b : E3) => H b a))
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ)))) :
    (∫ w in boxL ℓ, ∫ y in boxL ℓ, H y w) = ∫ a in boxL ℓ, ∫ b in boxL ℓ, H a b :=
  MeasureTheory.integral_integral_swap hH

/-- Integrability of `(a,b) ↦ H b a` against the product of the restricted box measures. -/
theorem integrable_boxL_prod_swap {ℓ : ℝ} {H : E3 → E3 → ℝ}
    (hint : IntegrableOn (fun z : E3 × E3 => H z.2 z.1) (boxL ℓ ×ˢ boxL ℓ)) :
    Integrable (Function.uncurry (fun (a b : E3) => H b a))
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) := by
  rw [MeasureTheory.Measure.prod_restrict]
  exact hint

/-- The Dirichlet content of the full box is the sum of the slice integrals. -/
theorem pinDir_eq_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    pinDir ℓ Θ₀ = ∑ i : Fin n, ∑ j : Fin 3,
      ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2 := by
  unfold pinDir
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finset_sum]
    intro j _
    exact integrableOn_abox_of_continuous hℓ
      (((hΘ₀.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  · intro i _
    exact integrableOn_abox_of_continuous hℓ
      (continuous_finsetSum _ (fun j _ =>
        ((hΘ₀.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2))

/-! ## 3. The `pairG13` slice identities -/

/-- `∫ memX13 = pinL2`. -/
theorem setIntegral_memX13 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ w in boxL ℓ, memX13 ℓ p Θ₀ w) = pinL2 ℓ Θ₀ := by
  show (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
      ‖Θ₀ (insertCoord p.2 w x')‖ ^ 2) = pinL2 ℓ Θ₀
  rw [setIntegral_insertCoord_slice (ℓ := ℓ) hℓ p.2 (f := fun x => ‖Θ₀ x‖ ^ 2)
    (hΘ₀.continuous.norm.pow 2)]
  rfl

/-- `∫ dirX13 ≤ pinDir`. -/
theorem setIntegral_dirX13_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ w in boxL ℓ, dirX13 ℓ p Θ₀ w) ≤ pinDir ℓ Θ₀ := by
  have hslice : ∀ j : Fin 3,
      (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2 :=
    fun j => setIntegral_insertCoord_slice (ℓ := ℓ) hℓ p.2
      (f := fun x => ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2)
      (((hΘ₀.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hswap : (∫ w in boxL ℓ, dirX13 ℓ p Θ₀ w)
      = ∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2 := by
    show (∫ w in boxL ℓ, ∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2) = _
    rw [MeasureTheory.integral_finset_sum]
    intro j _
    have hd : Continuous (fun q : E3 × ({k : Fin n // k ≠ p.2} → E3) =>
        fderiv ℝ Θ₀ (insertCoord p.2 q.1 q.2)) :=
      (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord p.2)
    have hsm : StronglyMeasurable (fun w : E3 =>
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2) :=
      stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
        (g := fun (w : E3) (x : {k : Fin n // k ≠ p.2} → E3) =>
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w x) (slotDirVec p.2 j)‖ ^ 2)
        (((hd.clm_apply continuous_const).norm.pow 2)).stronglyMeasurable
    have hcontj : Continuous (fun x : Xn n => fderiv ℝ Θ₀ x (slotDirVec p.2 j)) :=
      continuous_fderiv_apply hΘ₀ (slotDirVec p.2 j)
    obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox hℓ
      (f := fun x : Xn n => fderiv ℝ Θ₀ x (slotDirVec p.2 j)) hcontj
    refine integrableOn_boxL_of_aeBound (C := M ^ 2
      * (volume (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ)).toReal) hsm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => by positivity)]
    exact setIntegral_boxPiSet_le_const hℓ (fun z _ => by positivity)
      (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
        (hM _ ((insertCoord_mem_abox_iff hℓ hw z).mpr hz)) 2)
  rw [hswap, Finset.sum_congr rfl (fun j _ => hslice j), pinDir_eq_sum hℓ hΘ₀, Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  refine Finset.single_le_sum (f := fun i : Fin n =>
      ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2) ?_
    (Finset.mem_univ p.2)
  intro i _
  exact integral_nonneg fun x => by positivity

/-- `∫ memY13 = ℓ³·pinL2`. -/
theorem setIntegral_memY13 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ y in boxL ℓ, memY13 ℓ p Θ₀ y) = ℓ ^ 3 * pinL2 ℓ Θ₀ := by
  show (∫ y in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxL ℓ,
      ‖Θ₀ (confY13 p y u x')‖ ^ 2) = ℓ ^ 3 * pinL2 ℓ Θ₀
  rw [setIntegral_confY13_slice (ℓ := ℓ) hℓ p hp (f := fun x => ‖Θ₀ x‖ ^ 2)
    (hΘ₀.continuous.norm.pow 2)]
  rfl

/-! ## 4. The `pairG23` slice identities -/

/-- `∫ memX23 = pinL2` (iterated form). -/
theorem setIntegral_memX23_iter {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ w in boxL ℓ, ∫ y in boxL ℓ, memX23 ℓ p Θ₀ w y) = pinL2 ℓ Θ₀ := by
  show (∫ w in boxL ℓ, ∫ y in boxL ℓ,
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖Θ₀ (insertCoord2 p w y x'')‖ ^ 2) = pinL2 ℓ Θ₀
  rw [setIntegral_insertCoord2_slice (ℓ := ℓ) hℓ p hp (f := fun x => ‖Θ₀ x‖ ^ 2)
    (hΘ₀.continuous.norm.pow 2)]
  rfl

/-- `∫ memX23 = pinL2` (product form). -/
theorem setIntegral_memX23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, memX23 ℓ p Θ₀ z.1 z.2) = pinL2 ℓ Θ₀ := by
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  obtain ⟨CM, hCM0, hCM⟩ := memX23_le hℓ p hΘ₀.continuous
  have hint : IntegrableOn (fun z : E3 × E3 => memX23 ℓ p Θ₀ z.1 z.2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound (C := CM) ?_ ?_
    · exact (stronglyMeasurable_memX23 (ℓ := ℓ) p hΘ₀.continuous).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      have h0 : (0 : ℝ) ≤ memX23 ℓ p Θ₀ z.1 z.2 := integral_nonneg fun x => by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hCM z.1 hz.1 z.2 hz.2
  have hconv : (∫ z in boxL ℓ ×ˢ boxL ℓ, memX23 ℓ p Θ₀ z.1 z.2)
      = ∫ w in boxL ℓ, ∫ y in boxL ℓ, memX23 ℓ p Θ₀ w y := by
    change (∫ z in boxL ℓ ×ˢ boxL ℓ, Function.uncurry (memX23 ℓ p Θ₀) z)
      = ∫ w in boxL ℓ, ∫ y in boxL ℓ, memX23 ℓ p Θ₀ w y
    exact setIntegral_boxL_prod_eq_iterated (F := Function.uncurry (memX23 ℓ p Θ₀)) hint
  rw [hconv]
  exact setIntegral_memX23_iter hℓ p hp hΘ₀

/-- `∫ dirX23 ≤ pinDir`. -/
theorem setIntegral_dirX23_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, dirX23 ℓ p Θ₀ z.1 z.2) ≤ pinDir ℓ Θ₀ := by
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hJint : ∀ j : Fin 3, IntegrableOn (fun z : E3 × E3 =>
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    intro j
    obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox hℓ
      (f := fun x : Xn n => fderiv ℝ Θ₀ x (slotDirVec p.1 j))
      (continuous_fderiv_apply hΘ₀ (slotDirVec p.1 j))
    have hsm : StronglyMeasurable (fun z : E3 × E3 =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2) :=
      stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
        (g := fun (z : E3 × E3) (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2)
        ((((hΘ₀.continuous_fderiv (by simp)).comp
          (continuous_insertCoord2_box p)).clm_apply continuous_const).norm.pow 2).stronglyMeasurable
    refine integrableOn_boxL_prod_of_aeBound
      (C := M ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal)
      hsm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    have h0 : (0 : ℝ) ≤ ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2 :=
      integral_nonneg fun x => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact setIntegral_boxPiSet_le_const hℓ (fun x _ => by positivity)
      (fun x hx => pow_le_pow_left₀ (norm_nonneg _)
        (hM _ ((insertCoord2_mem_abox_iff hℓ hz.1 hz.2 x).mpr hx)) 2)
  have hslice_eq : ∀ j : Fin 3,
      (∫ z in boxL ℓ ×ˢ boxL ℓ, ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec p.1 j)‖ ^ 2 := by
    intro j
    change (∫ z in boxL ℓ ×ˢ boxL ℓ, Function.uncurry (fun (w y : E3) =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p w y x'') (slotDirVec p.1 j)‖ ^ 2) z)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec p.1 j)‖ ^ 2
    rw [setIntegral_boxL_prod_eq_iterated
      (F := Function.uncurry (fun (w y : E3) =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p w y x'') (slotDirVec p.1 j)‖ ^ 2)) (hJint j)]
    exact setIntegral_insertCoord2_slice (ℓ := ℓ) hℓ p hp
      (f := fun x => ‖fderiv ℝ Θ₀ x (slotDirVec p.1 j)‖ ^ 2)
      ((continuous_fderiv_apply hΘ₀ (slotDirVec p.1 j)).norm.pow 2)
  have hsum : (∫ z in boxL ℓ ×ˢ boxL ℓ, dirX23 ℓ p Θ₀ z.1 z.2)
      = ∑ j : Fin 3, ∫ z in boxL ℓ ×ˢ boxL ℓ,
          ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2 := by
    show (∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2) = _
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact hJint j
  rw [hsum, Finset.sum_congr rfl (fun j _ => hslice_eq j), pinDir_eq_sum hℓ hΘ₀,
    Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  refine Finset.single_le_sum (f := fun i : Fin n =>
      ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2) ?_
    (Finset.mem_univ p.1)
  intro i _
  exact integral_nonneg fun x => by positivity

/-! ## 5. The `pairG21` slice identities -/

/-- `∫ memY21(z.2,z.1) = pinL2`. -/
theorem setIntegral_memY21 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, memY21 ℓ p Θ₀ z.2 z.1) = pinL2 ℓ Θ₀ := by
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  obtain ⟨CM, hCM0, hCM⟩ := memY21_le hℓ p hΘ₀.continuous
  have hint : IntegrableOn (fun z : E3 × E3 => memY21 ℓ p Θ₀ z.2 z.1) (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound (C := CM) ?_ ?_
    · have hswap : Measurable (fun z : E3 × E3 => (z.2, z.1)) :=
        Measurable.prod measurable_snd measurable_fst
      exact ((stronglyMeasurable_memY21 (ℓ := ℓ) p hΘ₀.continuous).comp_measurable
        hswap).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      have h0 : (0 : ℝ) ≤ memY21 ℓ p Θ₀ z.2 z.1 := integral_nonneg fun x => by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hCM z.2 hz.2 z.1 hz.1
  have hint' : Integrable (Function.uncurry (fun (a b : E3) => memY21 ℓ p Θ₀ b a))
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) :=
    integrable_boxL_prod_swap (ℓ := ℓ) hint
  change (∫ z in boxL ℓ ×ˢ boxL ℓ, Function.uncurry (fun (w y : E3) => memY21 ℓ p Θ₀ y w) z)
      = pinL2 ℓ Θ₀
  rw [setIntegral_boxL_prod_eq_iterated
    (F := Function.uncurry (fun (w y : E3) => memY21 ℓ p Θ₀ y w)) hint]
  show (∫ w in boxL ℓ, ∫ y in boxL ℓ, memY21 ℓ p Θ₀ y w) = pinL2 ℓ Θ₀
  rw [iterated_boxL_swap (ℓ := ℓ) (H := memY21 ℓ p Θ₀) hint']
  show (∫ a in boxL ℓ, ∫ b in boxL ℓ, memY21 ℓ p Θ₀ a b) = pinL2 ℓ Θ₀
  show (∫ a in boxL ℓ, ∫ b in boxL ℓ,
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖Θ₀ (insertCoord2 p a b x'')‖ ^ 2) = pinL2 ℓ Θ₀
  rw [setIntegral_insertCoord2_slice (ℓ := ℓ) hℓ p hp (f := fun x => ‖Θ₀ x‖ ^ 2)
    (hΘ₀.continuous.norm.pow 2)]
  rfl

/-- `∫ dirY21(z.2,z.1) ≤ pinDir`. -/
theorem setIntegral_dirY21_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, dirY21 ℓ p Θ₀ z.2 z.1) ≤ pinDir ℓ Θ₀ := by
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hJint : ∀ j : Fin 3, IntegrableOn (fun z : E3 × E3 =>
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    intro j
    obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox hℓ
      (f := fun x : Xn n => fderiv ℝ Θ₀ x (slotDirVec p.2 j))
      (continuous_fderiv_apply hΘ₀ (slotDirVec p.2 j))
    have hsm : StronglyMeasurable (fun z : E3 × E3 =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2) :=
      stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
        (g := fun (z : E3 × E3) (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2)
        (by
          have hs : Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
              ((q.1.2, q.1.1), q.2)) :=
            ((continuous_snd.comp continuous_fst).prodMk
              (continuous_fst.comp continuous_fst)).prodMk continuous_snd
          have hins : Continuous (fun q : (E3 × E3) ×
              ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) => insertCoord2 p q.1.2 q.1.1 q.2) :=
            (continuous_insertCoord2_box p).comp hs
          exact ((((hΘ₀.continuous_fderiv (by simp)).comp hins).clm_apply
            continuous_const).norm.pow 2).stronglyMeasurable)
    refine integrableOn_boxL_prod_of_aeBound
      (C := M ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal)
      hsm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    have h0 : (0 : ℝ) ≤ ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2 :=
      integral_nonneg fun x => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact setIntegral_boxPiSet_le_const hℓ (fun x _ => by positivity)
      (fun x hx => pow_le_pow_left₀ (norm_nonneg _)
        (hM _ ((insertCoord2_mem_abox_iff hℓ hz.2 hz.1 x).mpr hx)) 2)
  have hslice_eq : ∀ j : Fin 3,
      (∫ z in boxL ℓ ×ˢ boxL ℓ, ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2 := by
    intro j
    have hint' : Integrable
        (Function.uncurry (fun (a b : E3) => ∫ x'' in
          boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p b a x'') (slotDirVec p.2 j)‖ ^ 2))
        (((volume : Measure E3).restrict (boxL ℓ)).prod
          ((volume : Measure E3).restrict (boxL ℓ))) :=
      integrable_boxL_prod_swap (ℓ := ℓ) (H := fun y u => ∫ x'' in
        boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2) (hJint j)
    change (∫ z in boxL ℓ ×ˢ boxL ℓ, Function.uncurry (fun (w y : E3) =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p y w x'') (slotDirVec p.2 j)‖ ^ 2) z) = _
    rw [setIntegral_boxL_prod_eq_iterated (F := Function.uncurry (fun (w y : E3) =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p y w x'') (slotDirVec p.2 j)‖ ^ 2)) (hJint j)]
    show (∫ w in boxL ℓ, ∫ y in boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p y w x'') (slotDirVec p.2 j)‖ ^ 2) = _
    rw [iterated_boxL_swap (ℓ := ℓ) (H := fun y u => ∫ x'' in
        boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ‖fderiv ℝ Θ₀ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2) hint']
    show (∫ a in boxL ℓ, ∫ b in boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p a b x'') (slotDirVec p.2 j)‖ ^ 2) = _
    rw [setIntegral_insertCoord2_slice (ℓ := ℓ) hℓ p hp
      (f := fun x => ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2)
      ((continuous_fderiv_apply hΘ₀ (slotDirVec p.2 j)).norm.pow 2)]
  have hsum : (∫ z in boxL ℓ ×ˢ boxL ℓ, dirY21 ℓ p Θ₀ z.2 z.1)
      = ∑ j : Fin 3, ∫ z in boxL ℓ ×ˢ boxL ℓ,
          ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2 := by
    show (∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2) = _
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact hJint j
  rw [hsum, Finset.sum_congr rfl (fun j _ => hslice_eq j), pinDir_eq_sum hℓ hΘ₀,
    Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  refine Finset.single_le_sum (f := fun i : Fin n =>
      ∫ x in Submission.BoseGases.abox n ℓ, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2) ?_
    (Finset.mem_univ p.2)
  intro i _
  exact integral_nonneg fun x => by positivity

end Work.BoseBoxFock
