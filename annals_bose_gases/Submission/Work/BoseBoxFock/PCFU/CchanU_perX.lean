import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.G_boxFacts
import Submission.Work.BoseBoxFock.PCFU.aPSlotFacts
import Submission.Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.CchanU_perX` — the per-configuration `s`-frame split of the `(C)` channel

The target is the *configuration-wise* form of the `P_i`/`Q_j` slot split of the `s`-frame at an
arbitrary shift, **weighted by the `(C)`-channel kernel** `χ_Λ(w)·KfrU(x i + w)` and integrated in
`w`:

    ∫_{u∈Λ} (∫_w χ_Λ(w)·Ksfr(u+w)·KfrU(x_i+w))·P_iΘ(x[j↦u])
      = ℓ³ ∫_w χ_Λ(w)·KfrU(x_i+w)·∫_{u∈Λ} (Σ'_d Κ(u+w+ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) .

## Proof

`int_Ksfr_aP_eq_imageSum_gen` gives, for **every** shift `b`, the identity

    ∫_{u∈Λ} Ksfr(u−b)·P_iΘ(x[j↦u]) = ℓ³ ∫_{u∈Λ} (Σ'_d Κ(u−b+ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) ,

whose content is the pointwise normalisation `Ksfr = ℓ³Σ'_d Κ(·+ℓ•d) − 1` together with the two
shift-independent integrals `∫Ksfr = 0` and `∫P_iΘ(x[j↦·]) = ℓ³·P_jP_iΘ(x)`.  Applying it at
`b := −w` and multiplying by the (`u`-independent) weight `c w := χ_Λ(w)·KfrU(x_i+w)` gives the
identity **pointwise in `w`**; integrating in `w` and applying Fubini once (`swap_chi`, an abstract
two-variable swap) yields the claim.  The single analytic input is the integrability of the joint
integrand, which holds because `χ_Λ` is continuous with compact support while `Ksfr`, `KfrU` and
`P_iΘ` are bounded.

Everything here is `sorry`-free.
-/

set_option linter.unusedVariables false

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Measurability of the box mean `P_iΞ` (a parametric integral of a measurable function). -/
private lemma measurable_aP_self {N : ℕ} (ℓ : ℝ) (i : Fin N) {Ξ : Submission.BoseGases.X N → ℝ}
    (hΞm : Measurable Ξ) : Measurable (Submission.BoseGases.aP ℓ i Ξ) := by
  unfold Submission.BoseGases.aP
  refine Measurable.const_mul ?_ _
  have huncurry : StronglyMeasurable
      (fun p : Submission.BoseGases.X N × E3 => Ξ (Function.update p.1 i p.2)) :=
    (hΞm.comp (by fun_prop : Measurable
      (fun p : Submission.BoseGases.X N × E3 => Function.update p.1 i p.2))).stronglyMeasurable
  haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
  simpa using (huncurry.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable

/-- Global sup bound of the box mean: the mean over the cube of a function bounded by `B` is again
bounded by `B`. -/
private lemma aP_abs_le_self {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ξ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hΞ : ∀ x, |Ξ x| ≤ B) :
    ∀ x, |Submission.BoseGases.aP ℓ i Ξ x| ≤ B := by
  intro x
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have h1 : ‖∫ y, Ξ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))‖ ≤ B * ℓ ^ 3 := by
    have hb : ∀ᵐ y ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖Ξ (Function.update x i y)‖ ≤ B :=
      Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΞ _
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun y => Ξ (Function.update x i y)) (C := B) hb
    rwa [Measure.real, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)] at h
  unfold Submission.BoseGases.aP
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3) * |∫ y, Ξ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))|
      ≤ (1 / ℓ ^ 3) * (B * ℓ ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.norm_eq_abs]; exact h1
    _ = B := by field_simp

/-- **The `w`-Fubini swap.**  For any `u`-independent test function `χ·Kfr` and the two kernels
`Ks` and `P`,

    ∫_{u∈Λ} (∫_w χ(w)·Ks(u+w)·Kfr(w))·P(u)
      = ∫_w χ(w)·Kfr(w)·(∫_{u∈Λ} Ks(u+w)·P(u)) .

This is the single Fubini step of `CchanU_perX`: the inner `u`-integral and the outer `w`-integral
are exchanged, the `u`-independent factors `χ(w)`, `Kfr(w)` being pulled out of the `u`-integral.
The only input is the joint integrability of the product. -/
private lemma swap_chi {ℓ : ℝ} {chi Ks Kfr P : E3 → ℂ}
    (hF : Integrable (fun p : E3 × E3 => ((chi p.2 * Ks (p.1 + p.2)) * Kfr p.2) * P p.1)
      (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod (volume : Measure E3))) :
    (∫ u in Submission.BoseGases.acube ℓ, (∫ w, chi w * Ks (u + w) * Kfr w) * P u)
      = ∫ w, chi w * Kfr w * (∫ u in Submission.BoseGases.acube ℓ, Ks (u + w) * P u) := by
  have h1 : (∫ u in Submission.BoseGases.acube ℓ, (∫ w, chi w * Ks (u + w) * Kfr w) * P u)
      = ∫ u in Submission.BoseGases.acube ℓ, ∫ w, chi w * Ks (u + w) * Kfr w * P u := by
    refine setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun u _ => ?_)
    exact (MeasureTheory.integral_mul_const (P u) (fun w => chi w * Ks (u + w) * Kfr w)).symm
  rw [h1, MeasureTheory.integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only []
  rw [show (fun u : E3 => chi w * Ks (u + w) * Kfr w * P u)
      = (fun u : E3 => (chi w * Kfr w) * (Ks (u + w) * P u)) from
        funext (fun u => by ring)]
  rw [MeasureTheory.integral_const_mul]

theorem CchanU_perX {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (x : Submission.BoseGases.X n) :
    (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        (∫ w : EuclideanSpace ℝ (Fin 3),
            ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (u + w)
              * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w))
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j u) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u + w + Work.BoseBoxFock.ellH v μ
                            • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ)) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (norm_nonneg (Θ 0)) (hCθ 0)
  have hCθ' : ∀ y, |Θ y| ≤ Cθ := fun y => by
    rw [← Real.norm_eq_abs]; exact hCθ y
  -- the two frame bounds
  have hKsB0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hKUB0 : 0 ≤ ∑ k : Work.BoseBoxFock.Lab N,
      |Work.BoseBoxFock.W1h v h μ fu N k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  -- measurability and boundedness of the slot mean `P_iΘ`
  have hPm : Measurable (fun u : E3 =>
      ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update x j u) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_aP_self (Work.BoseBoxFock.ellH v μ) i hΘm).comp
        (by fun_prop : Measurable (fun u : E3 => Function.update x j u)))
  have hPb : ∀ u : E3, ‖((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update x j u) : ℝ) : ℂ)‖ ≤ Cθ := fun u => by
    rw [show ‖((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
            (Function.update x j u) : ℝ) : ℂ)‖
          = |Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j u)| from by simp]
    exact aP_abs_le_self hℓ i hCθ0 hCθ' (Function.update x j u)
  -- continuity of the pieces
  have hchicont : Continuous (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox (Work.BoseBoxFock.ellH v μ))
  have hchics : HasCompactSupport (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)) :=
    Work.BoseBoxFock.hasCompactSupport_chiLam_complex (Work.BoseBoxFock.ellH v μ) hℓ
  have hKfrcont : Continuous (fun w : E3 =>
      Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)) :=
    (continuous_KfrU v h μ fu N).comp (continuous_const.add continuous_id)
  have hKscont : Continuous fun z : E3 => Work.BoseBoxFock.Ksfr v fc μ N z :=
    (continuous_Ksfr (v := v) (fc := fc) (μ := μ) (N := N))
  -- finiteness of the slot measure
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top _ hℓ.le⟩
  -- integrability of the joint integrand
  have hchiint : Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)) volume :=
    hchicont.integrable_of_hasCompactSupport hchics
  have hchi2 : Integrable (fun p : E3 × E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ))
      (((volume : Measure E3).restrict
          (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))).prod (volume : Measure E3)) :=
    (Integrable.mul_prod (f := fun _ : E3 => (1 : ℂ))
      (g := fun w : E3 =>
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ))
      (integrable_const (1 : ℂ)) hchiint).congr
      (Filter.Eventually.of_forall (fun p => by simp))
  have hbddmeas : AEStronglyMeasurable (fun p : E3 × E3 =>
      Work.BoseBoxFock.Ksfr v fc μ N (p.1 + p.2)
        * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + p.2)
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j p.1) : ℝ) : ℂ)))
      (((volume : Measure E3).restrict
          (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))).prod (volume : Measure E3)) :=
    (((hKscont.comp (continuous_fst.add continuous_snd)).measurable).mul
      (((hKfrcont.comp continuous_snd).measurable).mul
        (hPm.comp measurable_fst))).aestronglyMeasurable
  have hbddle : ∀ᵐ p ∂(((volume : Measure E3).restrict
        (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))).prod (volume : Measure E3)),
      ‖Work.BoseBoxFock.Ksfr v fc μ N (p.1 + p.2)
        * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + p.2)
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j p.1) : ℝ) : ℂ))‖
        ≤ (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
            |Work.BoseBoxFock.fLh v fc μ N s|)
          * ((∑ k : Work.BoseBoxFock.Lab N,
              |Work.BoseBoxFock.W1h v h μ fu N k|) * Cθ) :=
    Filter.Eventually.of_forall (fun p => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (norm_Ksfr_le (p.1 + p.2))
        (mul_le_mul (norm_KfrU_le v h μ fu N (x i + p.2)) (hPb p.1)
          (norm_nonneg _) hKUB0)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hKsB0)
  have hF0 : Integrable (fun p : E3 × E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)
        * (Work.BoseBoxFock.Ksfr v fc μ N (p.1 + p.2)
          * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + p.2)
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update x j p.1) : ℝ) : ℂ))))
      (((volume : Measure E3).restrict
          (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))).prod (volume : Measure E3)) :=
    hchi2.mul_bdd hbddmeas hbddle
  have hF : Integrable (fun p : E3 × E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)
        * Work.BoseBoxFock.Ksfr v fc μ N (p.1 + p.2)
        * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + p.2)
        * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
            (Function.update x j p.1) : ℝ) : ℂ))
      (((volume : Measure E3).restrict
          (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))).prod (volume : Measure E3)) :=
    hF0.congr (Filter.Eventually.of_forall (fun p => by ring))
  -- the per-`w` slot split
  have hgen : ∀ w : E3,
      (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
          Work.BoseBoxFock.Ksfr v fc μ N (u + w)
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update x j u) : ℝ) : ℂ))
        = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
            * ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (u + w + Work.BoseBoxFock.ellH v μ
                        • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                  * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                      (Function.update x j u) : ℝ) : ℂ) := by
    intro w
    have h := int_Ksfr_aP_eq_imageSum_gen (v := v) (fc := fc) (μ := μ) (N := N)
      hℓ hκ hN i j (-w) Θ hΘm ⟨Cθ, hCθ⟩ x
    simpa only [sub_neg_eq_add] using h
  -- the left-hand side, as the abstract swap
  have hL : (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (u + w)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w))
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j u) : ℝ) : ℂ))
      = ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
            * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                Work.BoseBoxFock.Ksfr v fc μ N (u + w)
                  * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                      (Function.update x j u) : ℝ) : ℂ)) := by
    simpa only [] using
      (swap_chi (ℓ := Work.BoseBoxFock.ellH v μ)
        (chi := fun w : E3 =>
          ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ))
        (Ks := fun z : E3 => Work.BoseBoxFock.Ksfr v fc μ N z)
        (Kfr := fun w : E3 => Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w))
        (P := fun u : E3 => ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
            (Function.update x j u) : ℝ) : ℂ)) hF)
  -- the right-hand side, written against the per-`w` identity
  have hR : ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ w : E3,
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u + w + Work.BoseBoxFock.ellH v μ
                            • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ))
      = ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
            * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                Work.BoseBoxFock.Ksfr v fc μ N (u + w)
                  * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                      (Function.update x j u) : ℝ) : ℂ)) := by
    conv_lhs => rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [show ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
            * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (u + w + Work.BoseBoxFock.ellH v μ
                        • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                  * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                      (Function.update x j u) : ℝ) : ℂ)))
        = ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
            * (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
              * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                  (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                        (u + w + Work.BoseBoxFock.ellH v μ
                          • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                    * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                        (Function.update x j u) : ℝ) : ℂ))) from by ring]
    rw [← hgen w]
  exact hL.trans hR.symm

end Work.BoseBoxFock.PCFU
