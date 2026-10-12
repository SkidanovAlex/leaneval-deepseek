import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.Pot.aemeasurable_wPairC_prod
import Submission.Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
import Submission.Work.BoseFixB2.Pot.lintegral_pair_abox
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.potWordU_integrable_b2`

Integrability of the localised potential word
`x ↦ potWordU N v (g₀ v h) ℓ μ 0 x` over the centred box `abox N ℓ`.

The word is `-μ Σᵢ ∫_y w_{1,0}(xᵢ,y) dy + Σ_{i<j} w_0(xᵢ,xⱼ)`; with translation
parameter `u = 0` the localisation kernel `wLoc` collapses to the χ-renormalised
two-body kernel `wPairC` (`wLoc_zero_eq_wPairC`).  The proof splits the word into
its one-body (`chemP`) and two-body (`wPairC`) parts and shows each piece
integrable on the box separately:

* one-body piece (`integrableOn_chemP_coord`): bound its `enorm` pointwise by
  `chemQ` (the `enorm`-valued `y`-integral, via `enorm_integral_le_lintegral_enorm`),
  peel the single coordinate over the box (`lintegral_coord_abox`) and bound the
  resulting `ℝ³`-integral by `ofReal (ℓ³ ∫|g|)` (`lintegral_wPairC_le`);
* two-body piece (`integrableOn_wPairC_pair`): peel the *two* coordinates over the
  box (`lintegral_pair_abox`) and bound by `ofReal (ℓ³ ∫|v|)`.

Neither bound uses any diluteness assumption — the χ-factors cancel the
denominator only inside the *joint* integral.  The `n = 0` case is trivial (both
sums are empty) and the `ℓ ≤ 0` case is vacuous (`abox n ℓ` is a null set).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Work.BoseFixB2.Energy

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 0. The kernel at translation parameter `0` -/

/-- With translation parameter `u = 0` the localisation kernel `wLoc` is the
χ-renormalised two-body kernel `wPairC`. -/
lemma wLoc_zero_eq_wPairC (ℓ : ℝ) (h : ℝ³ → ℝ) (a b : ℝ³) :
    Submission.BoseGases.wLoc ℓ h 0 a b = Submission.BoseGases.wPairC ℓ h a b := by
  rw [Submission.BoseGases.wPairC_apply]
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-! ## 1. The one-body (chemical potential) piece -/

/-- The one-body `y`-integral of the χ-renormalised kernel: `a ↦ ∫_y wPairC ℓ g a y`. -/
noncomputable def chemP (ℓ : ℝ) (g : ℝ³ → ℝ) (a : ℝ³) : ℝ :=
  ∫ y : ℝ³, Submission.BoseGases.wPairC ℓ g a y

/-- The `enorm`-valued one-body `y`-integral of the χ-renormalised kernel,
`a ↦ ∫⁻_y ‖wPairC ℓ g a y‖ₑ`, which dominates `‖chemP ℓ g a‖ₑ`. -/
noncomputable def chemQ (ℓ : ℝ) (g : ℝ³ → ℝ) (a : ℝ³) : ENNReal :=
  ∫⁻ y : ℝ³, ‖Submission.BoseGases.wPairC ℓ g a y‖ₑ

/-- `chemP ℓ g` is a.e. strongly measurable for an a.e. strongly measurable `g`. -/
lemma aesm_chemP {ℓ : ℝ} {g : ℝ³ → ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ³)) :
    AEStronglyMeasurable (chemP ℓ g) (volume : Measure ℝ³) :=
  AEStronglyMeasurable.integral_prod_right'
    (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hg)

/-- `chemQ ℓ g` is a.e. strongly measurable for an a.e. strongly measurable `g`. -/
lemma aesm_chemQ {ℓ : ℝ} {g : ℝ³ → ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ³)) :
    AEStronglyMeasurable (chemQ ℓ g) (volume : Measure ℝ³) :=
  (AEMeasurable.lintegral_prod_right'
    (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hg).enorm).aestronglyMeasurable

/-- The `ℝ³`-integral of `chemQ ℓ g` over the (centred) cube is bounded by `ofReal (ℓ³ ∫|g|)`. -/
lemma lintegral_acube_chemQ_le {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ³ → ℝ}
    (hg : MeasureTheory.Integrable g) :
    (∫⁻ a : ℝ³, chemQ ℓ g a
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |g z|) := by
  have h3 : (∫⁻ a : ℝ³, chemQ ℓ g a
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
      ≤ (∫⁻ a : ℝ³, chemQ ℓ g a ∂(volume : Measure ℝ³)) := by
    refine le_trans (lintegral_mono_set (Set.subset_univ (Submission.BoseGases.acube ℓ))) ?_
    simp [Measure.restrict_univ]
  have h4 : (∫⁻ a : ℝ³, chemQ ℓ g a ∂(volume : Measure ℝ³))
      = (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ g p.1 p.2‖ₑ
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
    (MeasureTheory.lintegral_prod
      (f := fun p : ℝ³ × ℝ³ => ‖Submission.BoseGases.wPairC ℓ g p.1 p.2‖ₑ)
      (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hg.aestronglyMeasurable).enorm).symm
  have h5 : (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ g p.1 p.2‖ₑ
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |g z|) :=
    Work.BoseFixB2.Pot.lintegral_wPairC_le hℓ hg
  exact le_trans h3 (le_trans (le_of_eq h4) h5)

/-- **The one-body piece has finite integral over the box.** -/
lemma hasFiniteIntegral_chemP_coord {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ³ → ℝ}
    (hg : MeasureTheory.Integrable g) {n : ℕ} (i : Fin n) :
    MeasureTheory.HasFiniteIntegral (fun x : Submission.BoseGases.X n => chemP ℓ g (x i))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
  have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  have hQ_meas : AEStronglyMeasurable (chemQ ℓ g) (volume : Measure ℝ³) :=
    aesm_chemQ hg.aestronglyMeasurable
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  have hle : ∀ x : Submission.BoseGases.X n,
      ENNReal.ofReal ‖chemP ℓ g (x i)‖ ≤ chemQ ℓ g (x i) := by
    intro x
    have h1 : ‖chemP ℓ g (x i)‖ₑ ≤ chemQ ℓ g (x i) :=
      MeasureTheory.enorm_integral_le_lintegral_enorm
        (f := fun y : ℝ³ => Submission.BoseGases.wPairC ℓ g (x i) y)
    have h2 : ENNReal.ofReal ‖chemP ℓ g (x i)‖ = ‖chemP ℓ g (x i)‖ₑ :=
      (Real.enorm_eq_ofReal_abs _).symm
    rw [h2]
    exact h1
  have h1 : (∫⁻ x : Submission.BoseGases.X n, ENNReal.ofReal ‖chemP ℓ g (x i)‖
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ≤ (∫⁻ x : Submission.BoseGases.X n, chemQ ℓ g (x i)
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) :=
    lintegral_mono hle
  have h2 : (∫⁻ x : Submission.BoseGases.X n, chemQ ℓ g (x i)
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      = ((volume : Measure ℝ³) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
        * (∫⁻ a : ℝ³, chemQ ℓ g a
            ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))) :=
    Work.BoseFixB2.Pot.lintegral_coord_abox hℓ i hQ_meas
  have h6 : ((volume : Measure ℝ³) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
        * ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |g z|) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn))
      ENNReal.ofReal_lt_top
  calc (∫⁻ x : Submission.BoseGases.X n, ENNReal.ofReal ‖chemP ℓ g (x i)‖
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ≤ (∫⁻ x : Submission.BoseGases.X n, chemQ ℓ g (x i)
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) := h1
    _ = ((volume : Measure ℝ³) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
        * (∫⁻ a : ℝ³, chemQ ℓ g a
            ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))) := h2
    _ ≤ ((volume : Measure ℝ³) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
        * ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |g z|) :=
        mul_le_mul_right (lintegral_acube_chemQ_le hℓ hg) _
    _ < ⊤ := h6

/-- **The one-body piece is integrable on the box.**  For `0 < ℓ` and integrable `g`, the
function `x ↦ chemP ℓ g (x i)` is integrable on `abox n ℓ`. -/
lemma integrableOn_chemP_coord {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ³ → ℝ}
    (hg : MeasureTheory.Integrable g) {n : ℕ} (i : Fin n) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => chemP ℓ g (x i))
      (Submission.BoseGases.abox n ℓ) :=
  ⟨((aesm_chemP hg.aestronglyMeasurable).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure ℝ³)) i)).mono_measure
      Measure.restrict_le_self,
    hasFiniteIntegral_chemP_coord hℓ hg i⟩

/-! ## 2. The two-body (pair) piece -/

/-- The pair kernel `x ↦ wPairC ℓ v (x i) (x j)` is a.e. strongly measurable on `X n`. -/
lemma aesm_wPairC_pair {ℓ : ℝ} {v : ℝ³ → ℝ}
    (hv : AEStronglyMeasurable v (volume : Measure ℝ³)) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.wPairC ℓ v (x i) (x j))
      (volume : Measure (Submission.BoseGases.X n)) :=
  (Work.BoseFixB2.Pot.aesm_wLoc_pair_X (ℓ := ℓ) (u := 0) hv i j hij).congr
    (Filter.Eventually.of_forall (fun x => wLoc_zero_eq_wPairC ℓ v (x i) (x j)))

/-- The double `ℝ³`-integral of the pair kernel over the (centred) cube is bounded by
`ofReal (ℓ³ ∫|v|)`. -/
lemma lintegral_acube_pair_le {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv : MeasureTheory.Integrable v) :
    (∫⁻ a : ℝ³, ∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |v z|) := by
  have hvmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wPairC ℓ v p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hv.aestronglyMeasurable
  have hstep : ∀ a : ℝ³,
      (∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
      ≤ (∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ ∂(volume : Measure ℝ³)) := by
    intro a
    refine le_trans (lintegral_mono_set (Set.subset_univ (Submission.BoseGases.acube ℓ))) ?_
    simp [Measure.restrict_univ]
  have h3 : (∫⁻ a : ℝ³, ∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
      ≤ (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ v p.1 p.2‖ₑ
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
    calc (∫⁻ a : ℝ³, ∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
          ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
        ≤ (∫⁻ a : ℝ³, ∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
            ∂(volume : Measure ℝ³)
            ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))) :=
          lintegral_mono hstep
      _ ≤ (∫⁻ a : ℝ³, ∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
            ∂(volume : Measure ℝ³) ∂(volume : Measure ℝ³)) := by
          refine le_trans (lintegral_mono_set (Set.subset_univ (Submission.BoseGases.acube ℓ))) ?_
          simp [Measure.restrict_univ]
      _ = (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ v p.1 p.2‖ₑ
            ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
          (MeasureTheory.lintegral_prod
            (f := fun p : ℝ³ × ℝ³ => ‖Submission.BoseGases.wPairC ℓ v p.1 p.2‖ₑ)
            hvmeas.enorm).symm
  exact le_trans h3 (Work.BoseFixB2.Pot.lintegral_wPairC_le hℓ hv)

/-- **The pair kernel has finite integral over the box.** -/
lemma hasFiniteIntegral_wPairC_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv : MeasureTheory.Integrable v) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasureTheory.HasFiniteIntegral
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.wPairC ℓ v (x i) (x j))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
  have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  have hvmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wPairC ℓ v p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hv.aestronglyMeasurable
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  have h1 : (∫⁻ x : Submission.BoseGases.X n,
        ENNReal.ofReal ‖Submission.BoseGases.wPairC ℓ v (x i) (x j)‖
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      = (∫⁻ x : Submission.BoseGases.X n,
          ‖Submission.BoseGases.wPairC ℓ v (x i) (x j)‖ₑ
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) :=
    lintegral_congr (fun x => by rw [Real.norm_eq_abs, ← Real.enorm_eq_ofReal_abs])
  have h2 : (∫⁻ x : Submission.BoseGases.X n,
        ‖Submission.BoseGases.wPairC ℓ v (x i) (x j)‖ₑ
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      = ((volume : Measure ℝ³) (Submission.BoseGases.acube ℓ)) ^ (n - 2)
        * (∫⁻ a : ℝ³, ∫⁻ b : ℝ³, ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
            ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
            ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))) :=
    Work.BoseFixB2.Pot.lintegral_pair_abox
      (φ := fun a b => ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ) hℓ hij
      hvmeas.enorm.aestronglyMeasurable
  have h5 : ((volume : Measure ℝ³) (Submission.BoseGases.acube ℓ)) ^ (n - 2)
        * ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |v z|) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn))
      ENNReal.ofReal_lt_top
  rw [h1, h2]
  exact lt_of_le_of_lt (mul_le_mul_right (lintegral_acube_pair_le hℓ hv) _) h5

/-- **The pair kernel is integrable on the box.**  For `0 < ℓ`, integrable `v` and distinct
labels `i ≠ j`, the function `x ↦ wPairC ℓ v (x i) (x j)` is integrable on `abox n ℓ`. -/
lemma integrableOn_wPairC_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv : MeasureTheory.Integrable v) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.wPairC ℓ v (x i) (x j)) (Submission.BoseGases.abox n ℓ) :=
  ⟨(aesm_wPairC_pair hv.aestronglyMeasurable hij).mono_measure Measure.restrict_le_self,
    hasFiniteIntegral_wPairC_pair hℓ hv hij⟩

/-! ## 3. The target -/

theorem potWordU_integrable_b2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hv1 : MeasureTheory.MemLp v 1) {μ : ℝ} {n : ℕ} (ℓ : ℝ) : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x) (Submission.BoseGases.abox n ℓ) := by
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hg_int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- ## `n = 0`: the word vanishes identically
    subst hn
    have h0 : ∀ x : Submission.BoseGases.X 0,
        Work.BoseKinLoc.potWordU 0 v (Submission.BoseGases.g0 v h) ℓ μ 0 x = 0 := by
      intro x
      haveI : IsEmpty {ij : Fin 0 × Fin 0 // ij.1 < ij.2} :=
        ⟨fun ij => absurd ij.1.1.isLt (by omega)⟩
      rw [Work.BoseKinLoc.potWordU]
      simp
    exact (MeasureTheory.integrable_zero (Submission.BoseGases.X 0) ℝ
      ((volume : Measure (Submission.BoseGases.X 0)).restrict (Submission.BoseGases.abox 0 ℓ))).congr
      (Filter.Eventually.of_forall (fun x => (h0 x).symm))
  · rcases le_or_gt ℓ 0 with hℓ | hℓ
    · -- ## `ℓ ≤ 0`: the box is null
      have hvol : (volume : Measure (Submission.BoseGases.X n))
          (Submission.BoseGases.abox n ℓ) = 0 := by
        rcases lt_or_eq_of_le hℓ with hlt | heq
        · have hemp : Submission.BoseGases.abox n ℓ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Submission.BoseGases.mem_abox_iff] at hx
            have hmem := hx ⟨0, hn⟩
            rw [Submission.BoseGases.mem_acube_iff] at hmem
            have h2 := hmem 0
            rw [Set.mem_Icc] at h2
            linarith [h2.1, h2.2]
          rw [hemp, measure_empty]
        · subst heq
          have hn' : n ≠ 0 := ne_of_gt hn
          rw [Submission.BoseGases.abox_volume n 0 le_rfl,
            show (((0 : ℝ) ^ 3) ^ n) = 0 by
              rw [zero_pow (by norm_num), zero_pow hn'],
            ENNReal.ofReal_zero]
      change MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X n =>
          Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
      rw [MeasureTheory.Measure.restrict_eq_zero.mpr hvol]
      exact MeasureTheory.integrable_zero_measure
    · -- ## `0 < ℓ`: assemble from the two integrable pieces
      have hpot : ∀ x : Submission.BoseGases.X n,
          Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x
            = (∑ i : Fin n, (-μ) * chemP ℓ (Submission.BoseGases.g0 v h) (x i))
              + ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
                  Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2) := by
        intro x
        have hc : (∑ i : Fin n, ∫ y : ℝ³,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
            = ∑ i : Fin n, chemP ℓ (Submission.BoseGases.g0 v h) (x i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_congr_ae (Filter.Eventually.of_forall
            (fun y => wLoc_zero_eq_wPairC ℓ (Submission.BoseGases.g0 v h) (x i) y))
        have hp : (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
              Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
            = ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
                Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2) := by
          apply Finset.sum_congr rfl
          intro ij _
          exact wLoc_zero_eq_wPairC ℓ v (x ij.1.1) (x ij.1.2)
        rw [Work.BoseKinLoc.potWordU, hc, hp, Finset.mul_sum]
      refine MeasureTheory.Integrable.congr (f := fun x : Submission.BoseGases.X n =>
        (∑ i : Fin n, (-μ) * chemP ℓ (Submission.BoseGases.g0 v h) (x i))
        + ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin n))
          (fun i _ => (integrableOn_chemP_coord hℓ hg_int i).const_mul (-μ))).add
          (MeasureTheory.integrable_finsetSum
            (Finset.univ : Finset {ij : Fin n × Fin n | ij.1 < ij.2})
            (fun ij _ => integrableOn_wPairC_pair hℓ hv_int (ne_of_lt ij.2)))
      · apply Filter.Eventually.of_forall
        intro x
        exact (hpot x).symm

end Work.BoseFixB2.Energy
