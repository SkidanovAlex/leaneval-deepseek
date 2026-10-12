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
# `Work.BoseBoxFock.PCFU.chCintand_integrable` — the `(C)`-channel integrand is integrable

The `(C)`-channel integrand of the cubic dictionary (`ChWordChains.lean`) is

    q ↦ Θ(q.1) · θ_ℓ(q.1 i) · ChCU(q.2.1, q.1 j, q.2.2) · Θ(q.1[i↦q.2.1][j↦q.2.2])

on `X n × (E3 × E3)`, where `θ_ℓ = corpusBox.thetaFun ℓ` is the sharp box indicator and
`ChCU = θ_ℓ(y)·θ_ℓ(x)·χ_ℓ(u)·ℓ^{-3}·∫_w χ_ℓ(w)·Ksfr(x+w)·KfrU(u+w)` (`PCFU/UnivFrames.lean`).

The integrand has the shape of the general `chChannelIntegrable` lemma
(`PCFU/chChannelIntegrable.lean`), with `K := ChCU`: it is measurable, uniformly bounded
(the three `θ`/`χ` factors by `1`, `1`, `(√chiNormSq)⁻¹`, the `w`-integral by the triangle
inequality together with the uniform frame bounds `‖Ksfr z‖ ≤ Σ_s |f_L(s)|`,
`‖KfrU z‖ ≤ Σ_k |Ŵ₁(k)|`), and it vanishes *off the box in its first and last slots* —
the `(C)`-channel is one of the two channels whose kernel carries `θ_ℓ` in the first slot
and `χ_ℓ` (not `θ_ℓ`) in the last one, which is exactly why the `A`/`B` pair needs both
slot hypotheses.  The reduction to a *finite*-measure support
(`abox n ℓ × (boxL ℓ × boxL ℓ)`) is then carried by `chChannelIntegrable` itself.

Everything here is `sorry`-free.

**For the sister node `chint_integrable`** (all four channels at once, currently `sorry`): the same
four ingredients close it verbatim — measurability of the channel in its three slots, a uniform
bound on `E³ × E³ × E³`, and vanishing off `boxL ℓ` in the first and in the last slot.  The
first/last-slot facts for the four channels are, from their definitions in `PCFU/UnivFrames.lean`:
`ChAU`: `χ_ℓ(y)` / `χ_ℓ(u)`; `ChBU`: `χ_ℓ(y)` / `θ_ℓ(u)`; `ChCU`: `θ_ℓ(y)` / `χ_ℓ(u)`;
`ChDU`: `θ_ℓ(y)` / `θ_ℓ(u)` — so all four channels satisfy both slot hypotheses
(`ch_thetaFun_eq_zero_of_notMem`, `ch_chiLam_eq_zero_of_notMem`), and `chChannelIntegrable`
then applies to each of them with no further work.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The ingredients of the `(C)`-channel kernel -/

/-- `w ↦ ‖χ_ℓ(w)‖` is integrable (`χ_ℓ` is continuous with compact support). -/
theorem ch_norm_chilam_integrable (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun w : E3 => ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)‖) :=
  ((Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ)).integrable_of_hasCompactSupport
      (Work.BoseBoxFock.hasCompactSupport_chiLam_complex ℓ hℓ)).norm

/-- **The inner `w`-integral of the `(C)`-channel is uniformly bounded.**  The two frame sums
are controlled by the triangle inequality (`norm_Ksfr_le`, `norm_KfrU_le`) and the `χ`-weight
is integrable. -/
theorem ch_norm_innerCU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x u : E3) :
    ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w)‖
      ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hχnorm : Integrable (fun w : E3 =>
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖) :=
    ch_norm_chilam_integrable (ellH v μ) (ellH_pos v μ)
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  calc ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w)‖
      ≤ ∫ w : E3, (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          (hχnorm.const_mul ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
            * (∑ k : Lab N, |W1h v h μ fu N k|)))
          (Filter.Eventually.of_forall fun w => ?_)
        beta_reduce
        rw [norm_mul, norm_mul]
        have h1 : ‖Ksfr v fc μ N (x + w)‖
            ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| := norm_Ksfr_le (x + w)
        have h2 : ‖KfrU v h μ fu N (u + w)‖ ≤ ∑ k : Lab N, |W1h v h μ fu N k| :=
          norm_KfrU_le v h μ fu N (u + w)
        have hAB : ‖Ksfr v fc μ N (x + w)‖ * ‖KfrU v h μ fu N (u + w)‖
            ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k|) :=
          mul_le_mul h1 h2 (norm_nonneg _) hA0
        calc ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ‖Ksfr v fc μ N (x + w)‖ * ‖KfrU v h μ fu N (u + w)‖
            = ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * (‖Ksfr v fc μ N (x + w)‖ * ‖KfrU v h μ fu N (u + w)‖) := by ring
          _ ≤ ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
                * (∑ k : Lab N, |W1h v h μ fu N k|)) :=
              mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
          _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k|)
              * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by ring
    _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        rw [MeasureTheory.integral_const_mul]

/-- **The `(C)`-channel is uniformly bounded on `E³ × E³ × E³`.** -/
theorem ch_exists_norm_ChCU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ y x u : E3, ‖ChCU v h fc fu μ N y x u‖ ≤ C := by
  refine ⟨1 * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * |(ellH v μ) ^ (-(3 : ℤ))|
      * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖),
    fun y x u => ?_⟩
  rw [ChCU, norm_mul, norm_mul, norm_mul, norm_mul]
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hI0 : 0 ≤ ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ :=
    integral_nonneg (fun w => norm_nonneg _)
  gcongr
  · exact ch_thetaFun_norm_le (ellH v μ) y
  · exact ch_thetaFun_norm_le (ellH v μ) x
  · exact norm_chiLam_le (ellH v μ) u
  · exact le_of_eq (RCLike.norm_ofReal _)
  · exact ch_norm_innerCU_le v h fc fu μ N x u

/-- **The `(C)`-channel is measurable as a function of its three slots.** -/
theorem ch_measurable_ChCU (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun p : E3 × (E3 × E3) => ChCU v h fc fu μ N p.1 p.2.1 p.2.2) := by
  have hKs : Continuous (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr
  have hKf : Continuous (fun z : E3 => KfrU v h μ fu N z) := continuous_KfrU v h μ fu N
  have hχ : Continuous (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)
  have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    measurable_thetaFun (ellH_pos v μ)
  have hF : Continuous (fun z : (E3 × (E3 × E3)) × E3 =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z.2 : ℝ) : ℂ) * Ksfr v fc μ N (z.1.2.1 + z.2)
        * KfrU v h μ fu N (z.1.2.2 + z.2)) := by
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul ?_ ?_
      · exact hχ.comp (by fun_prop)
      · exact hKs.comp (by fun_prop)
    · exact hKf.comp (by fun_prop)
  have hint : Measurable (fun p : E3 × (E3 × E3) => ∫ w : E3,
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * Ksfr v fc μ N (p.2.1 + w)
        * KfrU v h μ fu N (p.2.2 + w)) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))).measurable
  have hkey : (fun p : E3 × (E3 × E3) => ChCU v h fc fu μ N p.1 p.2.1 p.2.2)
      = fun p : E3 × (E3 × E3) =>
          Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2.1
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) p.2.2 : ℝ) : ℂ)
            * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Ksfr v fc μ N (p.2.1 + w) * KfrU v h μ fu N (p.2.2 + w) := by
    funext p; rfl
  have h1 : Measurable (fun p : E3 × (E3 × E3) =>
      Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1) := hθ.comp measurable_fst
  have h2 : Measurable (fun p : E3 × (E3 × E3) =>
      Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2.1) :=
    hθ.comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable (fun p : E3 × (E3 × E3) =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) p.2.2 : ℝ) : ℂ)) :=
    hχ.measurable.comp (measurable_snd.comp measurable_snd)
  have h4 : Measurable (fun _ : E3 × (E3 × E3) => (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)) :=
    measurable_const
  rw [hkey]
  exact (((h1.mul h2).mul h3).mul h4).mul hint

/-! ## 2. The two slot-vanishing facts -/

/-- The `(C)`-channel vanishes when its **first** slot leaves the box (the `θ_ℓ(y)` factor). -/
theorem ch_ChCU_eq_zero_of_fst_notMem (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) {y : E3}
    (hy : y ∉ Work.BoseK15.corpusBox.boxL (ellH v μ)) (x u : E3) :
    ChCU v h fc fu μ N y x u = 0 := by
  rw [ChCU, ch_thetaFun_eq_zero_of_notMem (ℓ := ellH v μ) hy]
  simp

/-- The `(C)`-channel vanishes when its **last** slot leaves the box (the `χ_ℓ(u)` factor). -/
theorem ch_ChCU_eq_zero_of_snd_notMem (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) {u : E3}
    (hu : u ∉ Work.BoseK15.corpusBox.boxL (ellH v μ)) (y x : E3) :
    ChCU v h fc fu μ N y x u = 0 := by
  rw [ChCU, ch_chiLam_eq_zero_of_notMem (ellH_pos v μ) hu]
  simp

/-! ## 3. The target -/

theorem chCintand_integrable {n : ℕ} (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    MeasureTheory.Integrable (Work.BoseBoxFock.PCFU.chCintand v h fc fu μ N i j Θ) := by
  obtain ⟨CK, hCK⟩ := ch_exists_norm_ChCU_le v h fc fu μ N
  exact chChannelIntegrable (ellH_pos v μ) Θ hΘm hΘb hΘs i j
    (fun p : E3 × (E3 × E3) => ChCU v h fc fu μ N p.1 p.2.1 p.2.2)
    (ch_measurable_ChCU v h fc fu μ N) CK (fun p => hCK p.1 p.2.1 p.2.2)
    (fun y x u hy => ch_ChCU_eq_zero_of_fst_notMem v h fc fu μ N hy x u)
    (fun y x u hu => ch_ChCU_eq_zero_of_snd_notMem v h fc fu μ N hu y x)

end Work.BoseBoxFock.PCFU
