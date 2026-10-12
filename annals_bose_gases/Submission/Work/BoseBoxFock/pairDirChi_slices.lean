import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGSliceIdent
import Submission.Work.BoseBoxFock.pairRowDirChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairDirChi_slices` — the χ²-weighted slice bounds of the Dirichlet content

`pairRowDirChi` introduced the **weighted** Dirichlet content

    pinDirChi ℓ Θ = ∫_{x ∈ abox n ℓ} Σ_{i,j} χ_ℓ(x i)² · ‖∂_{i,j} Θ x‖²

(the quantity that the weighted `pairEnergy` of the row's fibres is bounded by: the fibres of the
`Q₂` row are `χ_ℓ`-weighted in their kernel variables, so the state content they need is the
*weighted* content, not the unweighted `pinDir`).  The present file proves the corresponding
**weighted slice bounds**: the χ²-weighted slice Dirichlet contents at a single slot are all
dominated by `pinDirChi`.

The three statements are the exact analogues of
`pairGSliceIdent.setIntegral_dirX13_le`, `…_dirX23_le`, `…_dirY21_le` with the weight
`χ_ℓ(w)²` inserted in the slice variable; the point being that in each of the three slice
vocabularies the weight sits precisely at the slot **where the derivative is taken**:

* `dirX13 ℓ p Θ w` differentiates at slot `p.2` with value `w`,
* `dirX23 ℓ p Θ z.1 z.2` differentiates at slot `p.1` with value `z.1`,
* `dirY21 ℓ p Θ z.2 z.1` differentiates at slot `p.2`, whose value in
  `insertCoord2 p z.2 z.1 x''` is `z.1`.

Hence in each case the coordinate-insertion slice identity rewrites the weighted slice integral as
one summand of the double sum defining `pinDirChi`, and the bound follows by dropping the
remaining nonnegative summands.

Main ingredients:

* the weighted slice identities `setIntegral_insertCoord_slice_weight` /
  `setIntegral_insertCoord2_prod_weight`, which are the unweighted corpus identities applied to the
  *continuous* function `x ↦ W (x i) · g x` (the weight only enters through the value of that
  function at the inserted coordinate);
* `integrableOn_boxL_prod_sliceIntegral`, the integrability of a parametrised slice integral over
  the box squared, needed for the Fubini step of the two-slot product form;
* `weighted_slotDirichlet_le_pinDirChi`, the pointwise (per-configuration) comparison against the
  definition of `pinDirChi`.

The file is complete.
-/

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. Integrability on the slice box -/

/-- A continuous real function on the compact slice box `boxPiSet ι ℓ` is integrable there. -/
lemma integrableOn_boxPiSet_of_continuous {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f : (ι → E3) → ℝ} (hf : Continuous f) :
    IntegrableOn f (boxPiSet ι ℓ) := by
  have hK : IsCompact (boxPiSet ι ℓ) := isCompact_boxPiSet hℓ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact IntegrableOn.of_bound hK.measure_lt_top hf.aestronglyMeasurable C (by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hK.measurableSet] with x hx
    exact hC x hx)

/-! ## 2. The weighted slice identities -/

/-- The value of the one-slot insertion at the inserted coordinate. -/
@[simp] lemma insertCoord_self {n : ℕ} (i : Fin n) (w : E3)
    (x' : {k : Fin n // k ≠ i} → E3) : insertCoord i w x' i = w := by
  simp [insertCoord]

/-- The value of the two-slot insertion at the first inserted coordinate. -/
@[simp] lemma insertCoord2_fst {n : ℕ} (p : Fin n × Fin n) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) : insertCoord2 p w₀ w₁ x' p.1 = w₀ := by
  simp [insertCoord2]

/-- The value of the two-slot insertion at the second inserted coordinate. -/
lemma insertCoord2_snd {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) : insertCoord2 p w₀ w₁ x' p.2 = w₁ := by
  simp [insertCoord2, Ne.symm hp]

/-- **The weighted one-slot slice identity.**  If `W` and `g` are continuous then the slice
integral with the weight `W` at the inserted coordinate is the full box integral of the weighted
function.  This is `setIntegral_insertCoord_slice` applied to the continuous function
`x ↦ W (x i) · g x`, together with the trivial pointwise identity `(insertCoord i w x') i = w`. -/
theorem setIntegral_insertCoord_slice_weight {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {W : E3 → ℝ} (hW : Continuous W) {g : Xn n → ℝ} (hg : Continuous g) :
    (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
        W w * g (insertCoord i w x'))
      = ∫ x in Submission.BoseGases.abox n ℓ, W (x i) * g x := by
  have hf : Continuous (fun x : Xn n => W (x i) * g x) :=
    (hW.comp (continuous_apply i)).mul hg
  rw [← setIntegral_insertCoord_slice hℓ i hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  simp [insertCoord]

/-- **Pulling a constant out of a finite sum of slice integrals.**  For continuous `F j` on the
slice box, `c · Σ_j ∫ F j = ∫ Σ_j c · F j` (`integral_const_mul` for each `j`, then
`integral_finsetSum`). -/
lemma boxPiSet_const_mul_sum_integral {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    (c : ℝ) {F : Fin 3 → (ι → E3) → ℝ} (hF : ∀ j, Continuous (F j)) :
    c * (∑ j : Fin 3, ∫ x in boxPiSet ι ℓ, F j x)
      = ∫ x in boxPiSet ι ℓ, ∑ j : Fin 3, c * F j x := by
  rw [Finset.mul_sum]
  rw [show (∑ j : Fin 3, c * ∫ x in boxPiSet ι ℓ, F j x)
      = ∑ j : Fin 3, ∫ x in boxPiSet ι ℓ, c * F j x from
    Finset.sum_congr rfl (fun j _ => (MeasureTheory.integral_const_mul c (fun x => F j x)).symm)]
  exact (MeasureTheory.integral_finsetSum _ (fun j _ =>
    integrableOn_boxPiSet_of_continuous hℓ (continuous_const.mul (hF j)))).symm

/-! ## 3. Integrability of a parametrised slice integral over the box squared -/

/-- **Integrability of a parametrised slice integral.**  For a continuous integrand
`F : (box × box) × slice-box → ℝ` the parametrised slice integral `z ↦ ∫_{x''} F z x''` is
integrable on the box squared: it is strongly measurable
(`stronglyMeasurable_integral_boxPiSet`) and bounded there (`F` is continuous on the compact
`(boxL ℓ ×ˢ boxL ℓ) ×ˢ boxPiSet ι ℓ`). -/
lemma integrableOn_boxL_prod_sliceIntegral {ℓ : ℝ} {ι : Type*} [Fintype ι]
    (hℓ : 0 < ℓ) {F : (E3 × E3) → (ι → E3) → ℝ} (hF : Continuous (Function.uncurry F)) :
    IntegrableOn (fun z : E3 × E3 => ∫ x'' in boxPiSet ι ℓ, F z x'')
      (boxL ℓ ×ˢ boxL ℓ) := by
  have hK : IsCompact ((boxL ℓ ×ˢ boxL ℓ) ×ˢ boxPiSet ι ℓ) :=
    ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)).prod (isCompact_boxPiSet hℓ)
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hsm : StronglyMeasurable (fun z : E3 × E3 =>
      ∫ x'' in boxPiSet ι ℓ, F z x'') :=
    stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
      (g := fun (z : E3 × E3) (x'' : ι → E3) => F z x'') hF.stronglyMeasurable
  refine integrableOn_boxL_prod_of_aeBound
    (C := Cf * (volume (boxPiSet ι ℓ)).toReal) hsm.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ))] with z hz
  calc ‖∫ x'' in boxPiSet ι ℓ, F z x''‖
      ≤ ∫ x'' in boxPiSet ι ℓ, ‖F z x''‖ := norm_integral_le_integral_norm _
    _ ≤ Cf * (volume (boxPiSet ι ℓ)).toReal :=
        setIntegral_boxPiSet_le_const hℓ (fun w _ => norm_nonneg _)
          (fun w hw => hCf (z, w) ⟨hz, hw⟩)

/-! ## 4. The weighted two-slot slice identity, product form -/

/-- **The weighted two-slot slice identity in product form.**  The weight `W` sits at the inserted
slot `p.1`: Fubini (`setIntegral_boxL_prod_eq_iterated`, whose integrability input is
`integrableOn_boxL_prod_sliceIntegral`) reduces the box-squared integral to the iterated one, and
there `setIntegral_insertCoord2_slice` applied to `x ↦ W (x p.1) · g x` identifies it. -/
theorem setIntegral_insertCoord2_prod_weight {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {W : E3 → ℝ} (hW : Continuous W)
    {g : Xn n → ℝ} (hg : Continuous g) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W z.1 * g (insertCoord2 p z.1 z.2 x''))
      = ∫ x in Submission.BoseGases.abox n ℓ, W (x p.1) * g x := by
  have hFint : IntegrableOn (fun z : E3 × E3 =>
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W z.1 * g (insertCoord2 p z.1 z.2 x'')) (boxL ℓ ×ˢ boxL ℓ) :=
    integrableOn_boxL_prod_sliceIntegral (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ
      (F := fun (z : E3 × E3) (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        W z.1 * g (insertCoord2 p z.1 z.2 x''))
      ((hW.comp (continuous_fst.comp continuous_fst)).mul
        (hg.comp (continuous_insertCoord2_box p)))
  rw [setIntegral_boxL_prod_eq_iterated (ℓ := ℓ) hFint]
  rw [show (∫ y in boxL ℓ, ∫ u in boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W y * g (insertCoord2 p y u x''))
      = ∫ x in Submission.BoseGases.abox n ℓ, W (x p.1) * g x from by
      have hf : Continuous (fun x : Xn n => W (x p.1) * g x) :=
        (hW.comp (continuous_apply p.1)).mul hg
      rw [← setIntegral_insertCoord2_slice hℓ p hp hf]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x'' => ?_)
      simp only [insertCoord2_fst]]

/-- **The weighted two-slot slice identity in product form, swapped orientation.**  The weight `W`
sits at the inserted slot `p.2` (the second argument of `insertCoord2`).  After Fubini
(`setIntegral_boxL_prod_eq_iterated`) the two outer iterated integrals are exchanged by
`iterated_boxL_swap`, which puts the weight at the slot `p.2` carrying the second inserted value,
and `setIntegral_insertCoord2_slice` applied to `x ↦ W (x p.2) · g x` identifies the result. -/
theorem setIntegral_insertCoord2_prod_weight_swap {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {W : E3 → ℝ} (hW : Continuous W)
    {g : Xn n → ℝ} (hg : Continuous g) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W z.1 * g (insertCoord2 p z.2 z.1 x''))
      = ∫ x in Submission.BoseGases.abox n ℓ, W (x p.2) * g x := by
  have hFA : IntegrableOn (fun z : E3 × E3 =>
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W z.1 * g (insertCoord2 p z.2 z.1 x'')) (boxL ℓ ×ˢ boxL ℓ) :=
    integrableOn_boxL_prod_sliceIntegral (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ
      (F := fun (z : E3 × E3) (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        W z.1 * g (insertCoord2 p z.2 z.1 x''))
      ((hW.comp (continuous_fst.comp continuous_fst)).mul
        (hg.comp ((continuous_insertCoord2_box p).comp
          (((continuous_snd.comp continuous_fst).prodMk
            (continuous_fst.comp continuous_fst)).prodMk continuous_snd))))
  have hFB : IntegrableOn (fun z : E3 × E3 =>
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W z.2 * g (insertCoord2 p z.1 z.2 x'')) (boxL ℓ ×ˢ boxL ℓ) :=
    integrableOn_boxL_prod_sliceIntegral (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ
      (F := fun (z : E3 × E3) (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        W z.2 * g (insertCoord2 p z.1 z.2 x''))
      ((hW.comp (continuous_snd.comp continuous_fst)).mul
        (hg.comp (continuous_insertCoord2_box p)))
  have hswap : (∫ w in boxL ℓ, ∫ y in boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          W w * g (insertCoord2 p y w x''))
      = ∫ w in boxL ℓ, ∫ y in boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          W y * g (insertCoord2 p w y x'') :=
    (iterated_boxL_swap (ℓ := ℓ) (H := fun a b =>
      ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        W a * g (insertCoord2 p b a x''))
      (integrable_boxL_prod_swap (ℓ := ℓ) (H := fun a b =>
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          W a * g (insertCoord2 p b a x'')) hFB)).symm
  rw [setIntegral_boxL_prod_eq_iterated (ℓ := ℓ) hFA]
  rw [show (∫ w in boxL ℓ, ∫ y in boxL ℓ,
        ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          W w * g (insertCoord2 p y w x''))
      = ∫ x in Submission.BoseGases.abox n ℓ, W (x p.2) * g x from by
      rw [hswap]
      have hf : Continuous (fun x : Xn n => W (x p.2) * g x) :=
        (hW.comp (continuous_apply p.2)).mul hg
      rw [← setIntegral_insertCoord2_slice hℓ p hp hf]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x'' => ?_)
      simp only [insertCoord2_snd hp]]

/-! ## 5. The core estimate against `pinDirChi` -/

/-- **One weighted slot of the Dirichlet content is dominated by `pinDirChi`.**  Unfolding the
definition of `pinDirChi` as the integral of the double sum `Σ_i Σ_j χ(x_i)²‖∂_{i,j}Θ‖²`, the
single-slot expression `χ(x i)² Σ_j ‖∂_{i,j}Θ x‖²` is the `i`-th summand of the outer sum, hence
dominated by the whole (all summands nonnegative).  Both sides are continuous on the compact box
`abox n ℓ`, hence integrable. -/
theorem weighted_slotDirichlet_le_pinDirChi {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
          * ∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2)
      ≤ pinDirChi ℓ Θ₀ := by
  have hχ : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  rw [pinDirChi]
  refine integral_mono ?_ ?_ ?_
  · rw [show (fun x : Xn n => (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2)
        = (fun x : Xn n => ∑ j : Fin 3, (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2) from by
          funext x; rw [Finset.mul_sum]]
    exact integrableOn_abox_of_continuous hℓ
      (continuous_finsetSum _ (fun j _ =>
        (((hχ.pow 2).comp (continuous_apply i)).mul
          ((continuous_fderiv_apply hΘ₀ _).norm.pow 2))))
  · exact integrableOn_abox_of_continuous hℓ
      (continuous_finsetSum _ (fun i' _ => continuous_finsetSum _ (fun j _ =>
        (((hχ.pow 2).comp (continuous_apply i')).mul
          ((continuous_fderiv_apply hΘ₀ _).norm.pow 2)))))
  · intro x
    change (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
          * ∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec i j)‖ ^ 2
        ≤ ∑ i' : Fin n, ∑ j : Fin 3, (Submission.BoseGases.chiScale ℓ (x i')) ^ 2
          * ‖fderiv ℝ Θ₀ x (slotDirVec i' j)‖ ^ 2
    rw [Finset.mul_sum]
    refine Finset.single_le_sum (f := fun i' : Fin n =>
        ∑ j : Fin 3, (Submission.BoseGases.chiScale ℓ (x i')) ^ 2
          * ‖fderiv ℝ Θ₀ x (slotDirVec i' j)‖ ^ 2) ?_ (Finset.mem_univ i)
    intro i' _
    exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (by positivity)

/-! ## 6. The three weighted slice bounds -/

/-- The `χ²`-weighted `dirX13` slice bound. -/
theorem pairDirChi_dirX13 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ (p : Fin n × Fin n) {Θ₀ : Work.BoseDict.Xn n → ℂ}, ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 * Work.BoseBoxFock.dirX13 ℓ p Θ₀ w)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ := by
  intro p Θ₀ hΘ₀
  have hχ : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  have hg : Continuous (fun x : Xn n =>
      ∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => ((continuous_fderiv_apply hΘ₀ _).norm.pow 2))
  have hx'c : ∀ w : E3, Continuous fun x' : {k : Fin n // k ≠ p.2} → E3 =>
      insertCoord p.2 w x' := fun w =>
    (continuous_insertCoord p.2).comp (continuous_const.prodMk continuous_id)
  -- the pointwise slice identity for `dirX13`
  have hpt : ∀ w : E3, dirX13 ℓ p Θ₀ w
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ∑ j : Fin 3, ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2 := by
    intro w
    rw [dirX13]
    exact (MeasureTheory.integral_finsetSum _
      (fun j _ => integrableOn_boxPiSet_of_continuous hℓ
        (((continuous_fderiv_apply hΘ₀ (slotDirVec p.2 j)).comp (hx'c w)).norm.pow 2))).symm
  have h2 : (∫ w in boxL ℓ,
        (Submission.BoseGases.chiScale ℓ w) ^ 2 * dirX13 ℓ p Θ₀ w)
      = ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, ‖fderiv ℝ Θ₀ (insertCoord p.2 w x')
              (slotDirVec p.2 j)‖ ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [hpt w, MeasureTheory.integral_const_mul]
  calc (∫ w in boxL ℓ,
        (Submission.BoseGases.chiScale ℓ w) ^ 2 * dirX13 ℓ p Θ₀ w)
      = _ := h2
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x p.2)) ^ 2 *
            (∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2) :=
        setIntegral_insertCoord_slice_weight hℓ p.2 (hχ.pow 2) hg
    _ ≤ pinDirChi ℓ Θ₀ := weighted_slotDirichlet_le_pinDirChi hℓ p.2 hΘ₀

/-- The `χ²`-weighted `dirX23` slice bound (product form on the box squared). -/
theorem pairDirChi_dirX23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ (p : Fin n × Fin n), p.1 ≠ p.2 → ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * Work.BoseBoxFock.dirX23 ℓ p Θ₀ z.1 z.2)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ := by
  intro p hp Θ₀ hΘ₀
  have hχ : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  have hg : Continuous (fun x : Xn n =>
      ∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec p.1 j)‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => ((continuous_fderiv_apply hΘ₀ _).norm.pow 2))
  have hx''c : ∀ z : E3 × E3, Continuous fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      insertCoord2 p z.1 z.2 x'' := fun z =>
    (continuous_insertCoord2_box p).comp (continuous_const.prodMk continuous_id)
  have hsum_id : ∀ z : E3 × E3,
      (∑ j : Fin 3, ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2)
        = ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ∑ j : Fin 3,
            ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2 := by
    intro z
    simpa using boxPiSet_const_mul_sum_integral (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2})
      hℓ (1 : ℝ)
      (F := fun j x'' => ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2)
      (fun j => ((continuous_fderiv_apply hΘ₀ (slotDirVec p.1 j)).comp (hx''c z)).norm.pow 2)
  have hpt : ∀ z : E3 × E3,
      (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * dirX23 ℓ p Θ₀ z.1 z.2
        = ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            (Submission.BoseGases.chiScale ℓ z.1) ^ 2 *
              (∑ j : Fin 3,
                ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2) := by
    intro z
    rw [dirX23, hsum_id z]
    exact (MeasureTheory.integral_const_mul _ _).symm
  calc (∫ z in boxL ℓ ×ˢ boxL ℓ,
        (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * dirX23 ℓ p Θ₀ z.1 z.2)
      = ∫ z in boxL ℓ ×ˢ boxL ℓ,
          ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            (Submission.BoseGases.chiScale ℓ z.1) ^ 2 *
              (∑ j : Fin 3,
                ‖fderiv ℝ Θ₀ (insertCoord2 p z.1 z.2 x'') (slotDirVec p.1 j)‖ ^ 2) :=
        MeasureTheory.setIntegral_congr_fun
          ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
            (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ))
          (fun z _ => hpt z)
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2 *
            (∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec p.1 j)‖ ^ 2) :=
        setIntegral_insertCoord2_prod_weight hℓ p hp (hχ.pow 2) hg
    _ ≤ pinDirChi ℓ Θ₀ := weighted_slotDirichlet_le_pinDirChi hℓ p.1 hΘ₀

/-- The `χ²`-weighted `dirY21` slice bound (product form on the box squared, the weight sitting at
the *second* inserted coordinate, which is the slot `p.2` where `dirY21` differentiates). -/
theorem pairDirChi_dirY21 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ (p : Fin n × Fin n), p.1 ≠ p.2 → ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * Work.BoseBoxFock.dirY21 ℓ p Θ₀ z.2 z.1)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ := by
  intro p hp Θ₀ hΘ₀
  have hχ : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  have hg : Continuous (fun x : Xn n =>
      ∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => ((continuous_fderiv_apply hΘ₀ _).norm.pow 2))
  have hx''c : ∀ z : E3 × E3, Continuous fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      insertCoord2 p z.2 z.1 x'' := fun z =>
    (continuous_insertCoord2_box p).comp
      (Continuous.prodMk (continuous_const (y := ((z.2, z.1) : E3 × E3))) continuous_id)
  have hsum_id : ∀ z : E3 × E3,
      (∑ j : Fin 3, ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2)
        = ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ∑ j : Fin 3,
            ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2 := by
    intro z
    simpa using boxPiSet_const_mul_sum_integral
      (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ (1 : ℝ)
      (F := fun j x'' => ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2)
      (fun j => ((continuous_fderiv_apply hΘ₀ (slotDirVec p.2 j)).comp (hx''c z)).norm.pow 2)
  have hpt : ∀ z : E3 × E3,
      (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * dirY21 ℓ p Θ₀ z.2 z.1
        = ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            (Submission.BoseGases.chiScale ℓ z.1) ^ 2 *
              (∑ j : Fin 3,
                ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2) := by
    intro z
    rw [dirY21, hsum_id z]
    exact (MeasureTheory.integral_const_mul _ _).symm
  calc (∫ z in boxL ℓ ×ˢ boxL ℓ,
        (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * dirY21 ℓ p Θ₀ z.2 z.1)
      = ∫ z in boxL ℓ ×ˢ boxL ℓ,
          ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            (Submission.BoseGases.chiScale ℓ z.1) ^ 2 *
              (∑ j : Fin 3,
                ‖fderiv ℝ Θ₀ (insertCoord2 p z.2 z.1 x'') (slotDirVec p.2 j)‖ ^ 2) :=
        MeasureTheory.setIntegral_congr_fun
          ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
            (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ))
          (fun z _ => hpt z)
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x p.2)) ^ 2 *
            (∑ j : Fin 3, ‖fderiv ℝ Θ₀ x (slotDirVec p.2 j)‖ ^ 2) :=
        setIntegral_insertCoord2_prod_weight_swap hℓ p hp (hχ.pow 2) hg
    _ ≤ pinDirChi ℓ Θ₀ := weighted_slotDirichlet_le_pinDirChi hℓ p.2 hΘ₀

/-- **The `χ²`-weighted slice bounds of the Dirichlet content.**  Each of the three slice
Dirichlet contents of the row's fibres (`dirX13`, `dirX23`, `dirY21`), weighted by `χ_ℓ²` in the
kernel variable, is dominated by the weighted Dirichlet content `pinDirChi` of the state. -/
theorem pairDirChi_slices {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ (p : Fin n × Fin n) {Θ₀ : Work.BoseDict.Xn n → ℂ}, ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 * Work.BoseBoxFock.dirX13 ℓ p Θ₀ w)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀) ∧
    (∀ (p : Fin n × Fin n), p.1 ≠ p.2 → ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * Work.BoseBoxFock.dirX23 ℓ p Θ₀ z.1 z.2)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀) ∧
    (∀ (p : Fin n × Fin n), p.1 ≠ p.2 → ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z.1) ^ 2 * Work.BoseBoxFock.dirY21 ℓ p Θ₀ z.2 z.1)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀) :=
  ⟨pairDirChi_dirX13 hℓ, pairDirChi_dirX23 hℓ, pairDirChi_dirY21 hℓ⟩

end Work.BoseBoxFock
