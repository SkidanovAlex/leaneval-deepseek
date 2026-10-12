import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.MiddleU_eq_four_integral
import Submission.Work.BoseBoxFock.PCFU.chChannelIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chDintand_integrable` — the `(D)`-channel integrand is integrable

The `(D)`-channel integral `chDint` of the cubic dictionary (`PCFU/ChWordChains`) is the Bochner
integral of the integrand

    `chDintand q = Θ(q.1) · θ_ℓ(q.1 i) · ChDU(q.2.1, q.1 j, q.2.2) · Θ(q.1[i↦q.2.1][j↦q.2.2])`

on `X n × (E3 × E3)`, `ℓ = ellH v μ`.  This module proves it is `Integrable`, by instantiating the
general channel-integrability lemma `PCFU.chChannelIntegrable` at the `(D)`-channel kernel
`K (y, x, u) = ChDU v h fc fu μ N y x u`.

That lemma needs exactly four facts about `ChDU`:

* **measurability** in the triple `(y, x, u)` — `chD_measurable_ChDU`.  `ChDU` is
  `θ_ℓ(y)·θ_ℓ(x)·θ_ℓ(u)·ℓ⁻³` times the `w`-integral `∫_w χ_Λ(w)·Ksfr(x+w)·KχfrU(w)`, whose
  measurability in `x` comes from `StronglyMeasurable.integral_prod_right'` applied to the
  *jointly continuous* integrand `(x, w) ↦ χ_Λ(w)Ksfr(x+w)KχfrU(w)`;
* a **uniform bound** on `E3 × E3 × E3` — `chD_exists_norm_ChDU_le`, obtained from the triangle
  inequality for the `w`-integral (`chD_norm_innerDU_le`) and the frame bounds
  `norm_Ksfr_le` / `norm_KχfrU_le`;
* **vanishing in the first slot** `y ∉ Λ(ℓ)` and in the **third slot** `u ∉ Λ(ℓ)` — both are the
  sharp-box indicator `θ_ℓ` (`ch_thetaFun_eq_zero_of_notMem`); the `(D)`-channel carries no
  `χ_Λ`-factor, its localisation is purely by `θ_ℓ`.

The `θ`-factors also place the *first and third* slots inside the box `Λ(ℓ)`, which is what makes
the product measure of the support finite — the `E3 × E3` factor of the domain is *not* of finite
measure on its own, so this vanishing is essential, not cosmetic.

Everything here is `sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseBoxFock

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the sharp box indicator -/

/-- The sharp box indicator is bounded by one. -/
lemma chD_norm_thetaFun_le (ℓ : ℝ) (z : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]; split_ifs <;> simp

/-! ## Uniform bounds on the `(D)`-channel

The kernel `ChDU` contains the `w`-integral `∫_w χ_Λ(w)·Ksfr(x+w)·KχfrU(w)`, which is bounded
uniformly in `x` because both frames are finite sums of unimodular phases. -/

/-- The inner `w`-integral of the `(D)`-channel is uniformly bounded. -/
lemma chD_norm_innerDU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x : E3) :
    ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w‖
      ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hχnorm : Integrable (fun w : E3 =>
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖) :=
    ((Complex.continuous_ofReal.comp
        (Work.BoseB4.BoxData.chiLam_cont _ _)).integrable_of_hasCompactSupport
      (Work.BoseBoxFock.hasCompactSupport_chiLam_complex (ellH v μ) (ellH_pos v μ))).norm
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  calc ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w‖
      ≤ ∫ w : E3, (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          (hχnorm.const_mul ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
            * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)))
          (Filter.Eventually.of_forall fun w => ?_)
        beta_reduce
        rw [norm_mul, norm_mul]
        have h1 : ‖Ksfr v fc μ N (x + w)‖
            ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| := norm_Ksfr_le (x + w)
        have h2 : ‖KχfrU v h μ fu N w‖
            ≤ ∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k| :=
          norm_KχfrU_le v h μ fu N w
        have hAB : ‖Ksfr v fc μ N (x + w)‖ * ‖KχfrU v h μ fu N w‖
            ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|) :=
          mul_le_mul h1 h2 (norm_nonneg _) hA0
        calc ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ‖Ksfr v fc μ N (x + w)‖ * ‖KχfrU v h μ fu N w‖
            = ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * (‖Ksfr v fc μ N (x + w)‖ * ‖KχfrU v h μ fu N w‖) := by ring
          _ ≤ ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
                * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)) :=
              mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
          _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
              * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by ring
    _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        rw [MeasureTheory.integral_const_mul]

/-- The `(D)`-channel is uniformly bounded on `E3 × E3 × E3`. -/
lemma chD_exists_norm_ChDU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ p : E3 × (E3 × E3), ‖ChDU v h fc fu μ N p.1 p.2.1 p.2.2‖ ≤ C := by
  refine ⟨1 * 1 * 1 * |(ellH v μ) ^ (-(3 : ℤ))|
      * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖),
    fun p => ?_⟩
  obtain ⟨y, x, u⟩ := p
  rw [ChDU, norm_mul, norm_mul, norm_mul, norm_mul]
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hI0 : 0 ≤ ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ :=
    integral_nonneg (fun w => norm_nonneg _)
  gcongr
  · exact chD_norm_thetaFun_le (ellH v μ) y
  · exact chD_norm_thetaFun_le (ellH v μ) x
  · exact chD_norm_thetaFun_le (ellH v μ) u
  · exact le_of_eq (RCLike.norm_ofReal _)
  · exact chD_norm_innerDU_le v h fc fu μ N x

/-! ## Measurability of the `(D)`-channel -/

/-- The `(D)`-channel is measurable as a function of its three slots.  The `w`-integral is
measurable in `x` by `StronglyMeasurable.integral_prod_right'` applied to the jointly continuous
integrand. -/
lemma chD_measurable_ChDU (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun p : E3 × (E3 × E3) => ChDU v h fc fu μ N p.1 p.2.1 p.2.2) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hKs : Continuous (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr
  have hKf : Continuous (fun z : E3 => KχfrU v h μ fu N z) := continuous_KχfrU v h μ fu N
  have hχ : Continuous (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)
  have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    measurable_thetaFun hℓ
  have hF : Continuous (fun z : (E3 × (E3 × E3)) × E3 =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z.2 : ℝ) : ℂ) * Ksfr v fc μ N (z.1.2.1 + z.2)
        * KχfrU v h μ fu N z.2) := by
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul ?_ ?_
      · exact hχ.comp (by fun_prop)
      · exact hKs.comp (by fun_prop)
    · exact hKf.comp (by fun_prop)
  have hint : Measurable (fun p : E3 × (E3 × E3) => ∫ w : E3,
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * Ksfr v fc μ N (p.2.1 + w)
        * KχfrU v h μ fu N w) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))).measurable
  unfold ChDU
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact hθ.comp (by fun_prop)
        · exact hθ.comp (by fun_prop)
      · exact hθ.comp (by fun_prop)
    · exact measurable_const
  · exact hint

/-- **The `(D)`-channel integrand is Bochner integrable**, by the general
`PCFU.chChannelIntegrable` at the kernel `K (y, x, u) = ChDU v h fc fu μ N y x u`. -/
theorem chDintand_integrable {n : ℕ} (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    MeasureTheory.Integrable (Work.BoseBoxFock.PCFU.chDintand v h fc fu μ N i j Θ) := by
  obtain ⟨CK, hCK⟩ := chD_exists_norm_ChDU_le v h fc fu μ N
  have hKm : Measurable (fun p : E3 × (E3 × E3) => ChDU v h fc fu μ N p.1 p.2.1 p.2.2) :=
    chD_measurable_ChDU v h fc fu μ N
  have hKs1 : ∀ y x u : E3, y ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      ChDU v h fc fu μ N y x u = 0 := by
    intro y x u hy
    simp only [ChDU]
    rw [ch_thetaFun_eq_zero_of_notMem hy]
    simp
  have hKs2 : ∀ y x u : E3, u ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      ChDU v h fc fu μ N y x u = 0 := by
    intro y x u hu
    simp only [ChDU]
    rw [ch_thetaFun_eq_zero_of_notMem hu]
    simp
  have hmain := chChannelIntegrable (ellH_pos v μ) Θ hΘm hΘb hΘs i j
    (fun p : E3 × (E3 × E3) => ChDU v h fc fu μ N p.1 p.2.1 p.2.2) hKm CK hCK hKs1 hKs2
  exact hmain

end Work.BoseBoxFock.PCFU
