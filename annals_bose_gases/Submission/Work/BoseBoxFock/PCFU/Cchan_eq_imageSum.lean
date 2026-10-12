import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.CchanU_perX
import Submission.Work.BoseBoxFock.PCFU.chanBCD_canonical
import Submission.Work.BoseBoxFock.PCFU.prod_theta_integral
import Submission.Work.BoseBoxFock.chiRow_aP_abox_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

noncomputable section
open MeasureTheory

/-- **The smeared frame integral** `p ↦ ∫_w χ_Λ(w)·Ksfr(p₂+w)·KfrU(p₁ᵢ+w)`: measurable (the
integrand is jointly continuous, so Fubini measurability applies) and uniformly bounded by
`‖χ_Λ‖₁·(Σ_s|f_L(s)|)·(Σ_k|Ŵ₁(k)|)`.

This is the private copy of the delegated `PCFU.Cchan_smear`; it is reproduced here because that
module declares a `continuous_KfrU` which clashes with the one of `PCFU.G_boxFacts` — the two
modules cannot lie in one import cone. -/
private theorem Cchan_smear_aux {n : ℕ} (i : Fin n) (v : E3 → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun p : Submission.BoseGases.X n × E3 =>
        ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (p.2 + w)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 i + w))
    ∧ ∃ Cf : ℝ, ∀ p : Submission.BoseGases.X n × E3,
        ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (p.2 + w)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 i + w)‖ ≤ Cf := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hKs0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hKw0 : 0 ≤ ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg _)
  constructor
  · have hcont : Continuous fun q : (Submission.BoseGases.X n × E3) × E3 =>
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) q.2 : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (q.1.2 + q.2)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1.1 i + q.2) := by
      refine Continuous.mul (Continuous.mul ?_ ?_) ?_
      · exact (Complex.continuous_ofReal.comp
            (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox
              (Work.BoseBoxFock.ellH v μ))).comp continuous_snd
      · exact (continuous_Ksfr (v := v) (fc := fc) (μ := μ) (N := N)).comp
          (by fun_prop : Continuous fun q : (Submission.BoseGases.X n × E3) × E3 => q.1.2 + q.2)
      · exact (continuous_KfrU v h μ fu N).comp
          (by fun_prop : Continuous fun q : (Submission.BoseGases.X n × E3) × E3 => q.1.1 i + q.2)
    exact (hcont.stronglyMeasurable.integral_prod_right').measurable
  · have hχc : Continuous fun w : E3 =>
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox (Work.BoseBoxFock.ellH v μ))
    have hχint : Integrable fun w : E3 =>
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ) :=
      hχc.integrable_of_hasCompactSupport
        (hasCompactSupport_chiLam_complex (Work.BoseBoxFock.ellH v μ) hℓ)
    have hχnorm : Integrable fun w : E3 =>
        ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖ :=
      hχint.norm
    refine ⟨(∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
          |Work.BoseBoxFock.fLh v fc μ N s|)
        * (∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
        * ∫ w : E3,
            ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖,
      fun p => ?_⟩
    refine le_trans (norm_integral_le_integral_norm _) ?_
    calc ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (p.2 + w)
              * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 i + w)‖
        ≤ ∫ w : E3, (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
              |Work.BoseBoxFock.fLh v fc μ N s|)
            * (∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
            * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
            (hχnorm.const_mul ((∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
              |Work.BoseBoxFock.fLh v fc μ N s|)
              * (∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)))
            (Filter.Eventually.of_forall fun w => ?_)
          beta_reduce
          rw [norm_mul, norm_mul]
          calc ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖
                * ‖Work.BoseBoxFock.Ksfr v fc μ N (p.2 + w)‖
                * ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 i + w)‖
              = ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖
                * (‖Work.BoseBoxFock.Ksfr v fc μ N (p.2 + w)‖
                  * ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 i + w)‖) := by ring
            _ ≤ ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖
                * ((∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                    |Work.BoseBoxFock.fLh v fc μ N s|)
                  * (∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul (norm_Ksfr_le (p.2 + w))
                    (norm_KfrU_le v h μ fu N (p.1 i + w)) (norm_nonneg _) hKs0)
                  (norm_nonneg _)
            _ = (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                    |Work.BoseBoxFock.fLh v fc μ N s|)
                  * (∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
                  * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖ :=
                by ring
      _ = (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
              |Work.BoseBoxFock.fLh v fc μ N s|)
            * (∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
            * ∫ w : E3,
                ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖ := by
          rw [MeasureTheory.integral_const_mul]

/-- **The normalisation of the corpus box localisation** (private copy of
`PCFU.norm_chiLam_le`, which lives in a module that cannot be imported together with
`PCFU.Cchan_smear`): `χ_Λ(z) = χ_base(z/ℓ)/√chiNormSq` with `|χ_base| ≤ 1`, hence
`|χ_Λ(z)| ≤ (√chiNormSq)⁻¹` for every `ℓ`. -/
private lemma Cchan_chiLam_bound (ℓ : ℝ) (z : E3) :
    ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  have hsqrt : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  have hval : Work.BoseK15.corpusBox.chiLam ℓ z
      = Submission.BoseGases.chiBase (ℓ⁻¹ • z) / Real.sqrt Submission.BoseGases.chiNormSq := by
    simp only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi, Submission.BoseGases.chi]
  have hb : |Submission.BoseGases.chiBase (ℓ⁻¹ • z)| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Submission.BoseGases.chiBase_nonneg (ℓ⁻¹ • z)],
      Submission.BoseGases.chiBase_le_one _⟩
  rw [show ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      = |Work.BoseK15.corpusBox.chiLam ℓ z| from by simp]
  rw [hval, abs_div, abs_of_pos hsqrt]
  rw [div_le_iff₀ hsqrt, inv_mul_cancel₀ (ne_of_gt hsqrt)]
  exact hb

/-!
# `Work.BoseBoxFock.PCFU.Cchan_eq_imageSum` — the `(c)`-channel at the image sum

The `(c)`-channel twin of the proved `Work.BoseBoxFock.PCFU.Achan_eq_imageSum`/`Bchan_eq_imageSum`.
Writing `ℓ = ellH v μ`, `κ = ((paramsAt μ (a v)).d²·sideAt μ (a v))⁻¹`, `θ = thetaFun ℓ`,
`χ = chiLam ℓ`, the theorem computes

    Cchan = ∫ Θ(x)·θ(x i)·ChCU(y, x j, u)·Θ'

as `ℓ³` times the `χ`-weighted integral of the fibre deviation `Q_jP_iΘ` against the **image sum** of
the low cut-off kernel, exactly as in `(A)`/`(B)` — the difference being that the `u`-frame of `(C)`
carries the extra `w`-smearing `ℓ⁻³∫_w χ(w)Ksfr(u+w)KfrU(x i+w)`.

The three steps are:

1. `chanC_canonical` puts the channel in the canonical form
   `∫ Θ'Θ θ(y)θ(x j)θ(u) χ(x i) ℓ⁻³ ∫_w χ(w)Ksfr(u+w)KfrU(x i+w)`;
2. `chan_int_y_generic` performs the `∫_y` step against `θ(y)`, producing the slot mean `P_i = aP ℓ i`
   (with `aP_comp_update_eq` turning the parametric mean into `P_iΘ`), and `prod_theta_integral`
   converts the remaining `θ(u)` into the restricted integral `∫_{u∈acube ℓ}`;
3. the per-`x`, per-`w` frame integral `∫_{u∈acube}Ksfr(u+w)·P_iΘ(x[j↦u])` is the image sum
   `ℓ³∫_{u∈acube}(Σ'_d lowKer(u+w+ℓ•latVec d))·Q_jP_iΘ(x[j↦u])` (`int_Ksfr_aP_eq_imageSum_gen` at
   the shift `b = -w`), the `w`-integral being interchanged with the `u`-integral.

The two `ℓ³`-powers (from step 2 and step 3) and the `ℓ⁻³` of the canonical form multiply to the
`ℓ³` of the statement, and the `θ`-factor `θ(x j)` of the canonical form is `1` on the support of
`Θ` (`chiRow_aP_abox_facts`).
-/

theorem Cchan_eq_imageSum {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
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
                                (Function.update x j u) : ℝ) : ℂ))) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  have hCθn : ∀ x, ‖Θ x‖ ≤ Cθ := fun x => by rw [Real.norm_eq_abs]; exact hCθ x
  obtain ⟨hSmear, Cf, hSmearb⟩ := Cchan_smear_aux (n := n) i v h fc fu μ N
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg _) (hSmearb (0, 0))
  -- the two channel weights
  set G : Submission.BoseGases.X n → ℂ := fun x =>
      ((Θ x : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
        * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
    with hGdef
  set F : Submission.BoseGases.X n → E3 → ℂ := fun x u =>
      (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
        * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (u + w)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
    with hFdef
  -- ## the three `G`-facts
  have hGm : Measurable G := by
    rw [hGdef]
    have h1 : Measurable fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hΘm
    have h2 : Measurable fun x : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j) :=
      (measurable_thetaFun hℓ).comp (measurable_pi_apply j)
    have h3 : Measurable fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (((Work.BoseB4.BoxData.chiLam_cont _ _).measurable).comp (measurable_pi_apply i))
    exact (h1.mul h2).mul h3
  have hGb : ∀ x, ‖G x‖ ≤ Cθ * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
    intro x
    have hA : ‖((Θ x : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [show ‖((Θ x : ℝ) : ℂ)‖ = |Θ x| from by simp]
      exact hCθ x
    have hC : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [hGdef]
    rw [show ‖((Θ x : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)‖
        = ‖((Θ x : ℝ) : ℂ)‖
          * ‖Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)‖
          * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)‖
        from by rw [norm_mul, norm_mul]]
    exact mul_le_mul
      (mul_le_mul hA (norm_thetaFun_le_one (Work.BoseBoxFock.ellH v μ) (x j))
        (norm_nonneg _) hCθ0)
      (Cchan_chiLam_bound (Work.BoseBoxFock.ellH v μ) (x i)) (norm_nonneg _)
      (mul_nonneg hCθ0 zero_le_one)
  have hGs : Function.support G ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) := by
    intro x hx
    apply hΘs
    intro h0
    exact hx (by rw [hGdef]; simp [h0])
  -- ## the three `F`-facts
  have hFm : Measurable (fun p : Submission.BoseGases.X n × E3 => F p.1 p.2) := by
    have h := hSmear.const_mul ((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)
    simpa only [hFdef] using h
  have hFb : ∀ p : Submission.BoseGases.X n × E3,
      ‖F p.1 p.2‖ ≤ ‖((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)‖ * Cf := by
    intro p
    rw [hFdef, norm_mul]
    exact mul_le_mul_of_nonneg_left (hSmearb p) (norm_nonneg _)
  -- ## step 1-2: the canonical form, the `∫_y` step, and the slot-mean replacement
  have hcanon := chanC_canonical hij v h fc fu μ N Θ hΘ hΘm ⟨Cθ, hCθn⟩
  have hbridge : (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 i) : ℝ) : ℂ)
          * ((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)
          * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
              * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 i + w))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * F q.1 q.2.2 := by
    apply integral_congr_ae
    filter_upwards with q
    rw [hGdef, hFdef]
    ring
  have hY := chan_int_y_generic (n := n) (i := i) (j := j)
      (ℓ := Work.BoseBoxFock.ellH v μ) hℓ G hGm
      (Cθ * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) hGb hGs Θ hΘm Cθ hCθn
      F hFm (‖((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)‖ * Cf) hFb
  have hP : (∫ p : Submission.BoseGases.X n × E3,
        G p.1 * F p.1 p.2
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
              (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ))
      = ∫ p : Submission.BoseGases.X n × E3,
          G p.1 * F p.1 p.2
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update p.1 j p.2) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with p
    have hcomp := aP_comp_update_eq (ℓ := Work.BoseBoxFock.ellH v μ) hij Θ p.1 p.2
    simp only [hcomp]
  -- ## step 2b: the `θ(u)`-Fubini
  have hHm : Measurable (fun p : Submission.BoseGases.X n × E3 =>
      F p.1 p.2 * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update p.1 j p.2) : ℝ) : ℂ)) := by
    have hAPm' : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
          (fun x' => Θ (Function.update x' j p.2)) p.1) :=
      measurable_aP_param i j hΘm
    have hAPm : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update p.1 j p.2)) := by
      rw [show (fun p : Submission.BoseGases.X n × E3 =>
            Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
              (fun x' => Θ (Function.update x' j p.2)) p.1)
          = (fun p : Submission.BoseGases.X n × E3 =>
            Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update p.1 j p.2)) from by
        funext p
        exact aP_comp_update_eq (ℓ := Work.BoseBoxFock.ellH v μ) hij Θ p.1 p.2] at hAPm'
      exact hAPm'
    exact hFm.mul (Complex.measurable_ofReal.comp hAPm)
  have hHb : ∀ p : Submission.BoseGases.X n × E3,
      ‖F p.1 p.2 * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update p.1 j p.2) : ℝ) : ℂ)‖
        ≤ (‖((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)‖ * Cf) * Cθ := by
    intro p
    have hAPb : |Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update p.1 j p.2)| ≤ Cθ :=
      Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ0 (fun x => hCθ x) (Function.update p.1 j p.2)
    rw [norm_mul]
    refine mul_le_mul (hFb p) ?_ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCf0)
    rw [norm_ofReal_eq_abs]
    exact hAPb
  have hFub := prod_theta_integral (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ
      G hGm hGs (Cθ * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) hGb
      (fun x u => F x u * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update x j u) : ℝ) : ℂ)) hHm
      ((‖((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)‖ * Cf) * Cθ) hHb
  -- ## step 3: the per-`x`, per-`w` frame integral (the image sum)
  set J : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
        * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
            (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                  (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                    * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                  (u + w + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ)) with hJdef
  have hscalar : ((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)
      * (Work.BoseBoxFock.ellH v μ : ℂ) ^ 3 = 1 := by
    have hℓc : (Work.BoseBoxFock.ellH v μ : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hℓ)
    rw [Complex.ofReal_zpow]
    rw [show (-(3 : ℤ)) = -(3 : ℕ) by norm_num, zpow_neg, zpow_natCast]
    field_simp
  have hPerX : ∀ x : Submission.BoseGases.X n,
      (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
          F x u * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j u) : ℝ) : ℂ)) = J x := by
    intro x
    simp only [hJdef, hFdef]
    have hf : (fun u : E3 =>
          ((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)
            * (∫ w : E3,
                ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                  * Work.BoseBoxFock.Ksfr v fc μ N (u + w)
                  * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w))
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update x j u) : ℝ) : ℂ))
        = (fun u : E3 =>
            ((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)
              * ((∫ w : E3,
                  ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                    * Work.BoseBoxFock.Ksfr v fc μ N (u + w)
                    * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w))
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                    (Function.update x j u) : ℝ) : ℂ))) :=
      funext (fun u => mul_assoc _ _ _)
    rw [hf, MeasureTheory.integral_const_mul,
      CchanU_perX (x := x) (v := v) (h := h) (fc := fc) (fu := fu) (μ := μ) (N := N)
        hij hℓ hκ hN Θ hΘm ⟨Cθ, hCθn⟩,
      ← mul_assoc, hscalar, one_mul]
  -- ## step 4: the `θ(x j)`-factor is `1` on the support of `Θ`
  have hGdrop : (∫ x : Submission.BoseGases.X n, G x * J x)
      = ∫ x : Submission.BoseGases.X n,
          (((Θ x : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ))
            * J x := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [hGdef]
    by_cases hx : Θ x = 0
    · simp [hx]
    · have hxmem : x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) :=
        hΘs (Function.mem_support.mpr hx)
      have hθj : Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j) = 1 :=
        (chiRow_aP_abox_facts (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ).2.1 hxmem j
      rw [hθj]
      ring
  -- ## assembly
  calc (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = (∫ q : Submission.BoseGases.X n × (E3 × E3),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 i) : ℝ) : ℂ)
            * ((((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ)) : ℂ)
            * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 i + w)) := hcanon
    _ = (∫ q : Submission.BoseGases.X n × (E3 × E3),
          G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * F q.1 q.2.2) := hbridge
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ p : Submission.BoseGases.X n × E3,
              G p.1 * F p.1 p.2
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                    (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ) := hY
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ p : Submission.BoseGases.X n × E3,
              G p.1 * F p.1 p.2
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                    (Function.update p.1 j p.2) : ℝ) : ℂ) := by rw [hP]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n, G x *
              ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                F x u * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                    (Function.update x j u) : ℝ) : ℂ)) := by
        congr 1
        rw [show (∫ p : Submission.BoseGases.X n × E3,
              G p.1 * F p.1 p.2
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                    (Function.update p.1 j p.2) : ℝ) : ℂ))
            = ∫ p : Submission.BoseGases.X n × E3,
                G p.1 * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                  * (F p.1 p.2 * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                      (Function.update p.1 j p.2) : ℝ) : ℂ)) from by
          apply integral_congr_ae
          filter_upwards with p
          ring]
        exact hFub
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n, G x * J x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        rw [hPerX x]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n,
              (((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ))
                * J x) := by rw [hGdrop]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
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
                                (Function.update x j u) : ℝ) : ℂ))) := by
        rw [hJdef]

end

end Work.BoseBoxFock.PCFU
