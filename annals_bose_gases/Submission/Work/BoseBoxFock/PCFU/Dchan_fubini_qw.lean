import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.Bchan_eq_imageSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.Dchan_fubini_qw` — the `q ↔ w` Fubini swap of the `(D)`-channel

The `(D)`-channel of the cubic middle kernel, in canonical form (`chanD_canonical` of
`PCFU/chanBCD_canonical.lean`), is

    `Dchan = ∫_{X n × (E³×E³)} Θ'·Θ·θ(y)θ(x_j)θ(u)θ(x_i)·ℓ⁻³·∫_w χ(w)Ksfr(u+w)KχfrU(w)`

and the downstream dictionary (`Dchan_eq_imageSum`, `Dchan_perW`) needs it with the two
integrations *interchanged*, the `w`-integration outermost and the `q`-integration applied to the
`u`-dependent factor `Ksfr(u+w)` alone:

    `∫_w ℓ⁻³χ(w)KχfrU(w)·∫_q Θ'·Θ·θ(y)θ(x_j)θ(u)θ(x_i)·Ksfr(u+w)`.

This is a pure Bochner–Fubini identity.  The whole analytic content is that the joint integrand

    `dChanG q w = dChanA q · ℓ⁻³ · (χ(w)·KχfrU(w)) · Ksfr(q.2.2 + w)`

is **integrable** on the product measure: `dChanA` is bounded (`|Θ| ≤ C`, `‖θ‖ ≤ 1`) and is
supported in `abox n ℓ × (acube ℓ × acube ℓ)` (the support of `Θ` and the two sharp boxes),
`χ` is bounded by `chiSupAbs` and supported in `acube ℓ`, and `Ksfr`, `KχfrU` are finite sums of
plane waves hence uniformly bounded (`norm_Ksfr_le`, `norm_KχfrU_le`).  The swap is then
`MeasureTheory.integral_integral_swap`, and the two iterated integrals are matched to the two sides
of the statement by `MeasureTheory.integral_const_mul`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- The `q`-weight of the `(D)`-channel: the two `Θ`-factors and the four `θ`-factors. -/
def dChanA {n : ℕ} (i j : Fin n) (ℓ : ℝ) (Θ : Submission.BoseGases.X n → ℝ)
    (q : Submission.BoseGases.X n × (E3 × E3)) : ℂ :=
  ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
    * ((Θ q.1 : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun ℓ q.2.1
    * Work.BoseK15.corpusBox.thetaFun ℓ (q.1 j)
    * Work.BoseK15.corpusBox.thetaFun ℓ q.2.2
    * Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i)

/-- The joint `(q,w)`-integrand of the `(D)`-channel:
`dChanA q · ℓ⁻³ · χ(w)KχfrU(w) · Ksfr(q.2.2+w)` (the product over which the Fubini swap is taken). -/
def dChanG {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (q : Submission.BoseGases.X n × (E3 × E3)) (w : E3) : ℂ :=
  dChanA i j (Work.BoseBoxFock.ellH v μ) Θ q
    * ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
    * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
        * KχfrU v h μ fu N w)
    * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)

lemma dChanA_measurable {n : ℕ} (i j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) : Measurable (dChanA i j ℓ Θ) := by
  unfold dChanA
  have hθ : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := measurable_thetaFun hℓ
  have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) :=
    hΘm.comp (measurable_update_update_pair i j)
  have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => Θ q.1) :=
    hΘm.comp measurable_fst
  have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => q.1 j) :=
    (measurable_fst.eval (a := j))
  have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => q.2.1) :=
    measurable_snd.fst
  have h5 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => q.2.2) :=
    measurable_snd.snd
  have h6 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => q.1 i) :=
    (measurable_fst.eval (a := i))
  exact ((((Complex.measurable_ofReal.comp h1).mul
      (Complex.measurable_ofReal.comp h2)).mul (hθ.comp h4)).mul
      (hθ.comp h3)).mul (hθ.comp h5) |>.mul (hθ.comp h6)

lemma dChanA_eq_zero_of_notMem {n : ℕ} {i j : Fin n} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Submission.BoseGases.X n → ℝ}
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {q : Submission.BoseGases.X n × (E3 × E3)}
    (hq : q ∉ Submission.BoseGases.abox n ℓ
      ×ˢ (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    dChanA i j ℓ Θ q = 0 := by
  rw [Set.mem_prod, not_and_or] at hq
  rcases hq with h1 | h2
  · have h0 : Θ q.1 = 0 := by
      by_contra hne
      exact h1 (hΘs (Function.mem_support.mpr hne))
    unfold dChanA
    rw [h0, Complex.ofReal_zero]
    ring
  · rw [Set.mem_prod, not_and_or] at h2
    rcases h2 with h2 | h2
    · have h0 : Work.BoseK15.corpusBox.thetaFun ℓ q.2.1 = 0 :=
        thetaFun_eq_zero_of_notMem_acube hℓ h2
      unfold dChanA
      rw [h0]
      ring
    · have h0 : Work.BoseK15.corpusBox.thetaFun ℓ q.2.2 = 0 :=
        thetaFun_eq_zero_of_notMem_acube hℓ h2
      unfold dChanA
      rw [h0]
      ring

/-- The norm inequality for a product of six factors in `ℂ`. -/
lemma norm_mul_six_le (a b c d e f : ℂ) :
    ‖a * b * c * d * e * f‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ := by
  calc ‖a * b * c * d * e * f‖ ≤ ‖a * b * c * d * e‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_five_le _ _ _ _ _) (norm_nonneg _)
    _ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ := by ring

lemma norm_dChanA_le {n : ℕ} (i j : Fin n) (ℓ : ℝ) {Θ : Submission.BoseGases.X n → ℝ}
    {C : ℝ} (hC : ∀ x, |Θ x| ≤ C) (q : Submission.BoseGases.X n × (E3 × E3)) :
    ‖dChanA i j ℓ Θ q‖ ≤ C * C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Θ 0)) (hC 0)
  have hb : ‖((Θ q.1 : ℝ) : ℂ)‖ ≤ C := by
    rw [norm_ofReal_eq_abs]; exact hC _
  have hc : ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.1)‖ ≤ 1 := norm_thetaFun_le_one ℓ _
  have hd : ‖(Work.BoseK15.corpusBox.thetaFun ℓ (q.1 j))‖ ≤ 1 := norm_thetaFun_le_one ℓ _
  have he : ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.2)‖ ≤ 1 := norm_thetaFun_le_one ℓ _
  have hf : ‖(Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i))‖ ≤ 1 := norm_thetaFun_le_one ℓ _
  unfold dChanA
  have ha : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖ ≤ C := by
    rw [norm_ofReal_eq_abs]; exact hC _
  refine le_trans (norm_mul_six_le _ _ _ _ _ _) ?_
  have h1 : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
      * ‖((Θ q.1 : ℝ) : ℂ)‖ ≤ C * C := mul_le_mul ha hb (norm_nonneg _) hC0
  have h2 : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
      * ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.1)‖
      ≤ C * C * 1 := mul_le_mul h1 hc (norm_nonneg _) (by positivity)
  have h3 : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
      * ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.1)‖
      * ‖(Work.BoseK15.corpusBox.thetaFun ℓ (q.1 j))‖ ≤ C * C * 1 * 1 :=
    mul_le_mul h2 hd (norm_nonneg _) (by positivity)
  have h4 : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
      * ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.1)‖
      * ‖(Work.BoseK15.corpusBox.thetaFun ℓ (q.1 j))‖
      * ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.2)‖ ≤ C * C * 1 * 1 * 1 :=
    mul_le_mul h3 he (norm_nonneg _) (by positivity)
  have h5 : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
      * ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.1)‖
      * ‖(Work.BoseK15.corpusBox.thetaFun ℓ (q.1 j))‖
      * ‖(Work.BoseK15.corpusBox.thetaFun ℓ q.2.2)‖
      * ‖(Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i))‖ ≤ C * C * 1 * 1 * 1 * 1 :=
    mul_le_mul h4 hf (norm_nonneg _) (by positivity)
  simpa using h5

/-- Measurability of the joint integrand `(q,w) ↦ dChanG q w`. -/
lemma measurable_dChanG {n : ℕ} (i j : Fin n) {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) :
    Measurable (fun p : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      dChanG i j v h fc fu μ N Θ p.1 p.2) := by
  have hA : Measurable (fun p : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      dChanA i j (Work.BoseBoxFock.ellH v μ) Θ p.1) :=
    (dChanA_measurable i j (Work.BoseBoxFock.ellH_pos v μ) hΘm).comp measurable_fst
  have hχ : Measurable (fun p : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((Work.BoseB4.BoxData.chiLam_cont _ _).measurable.comp measurable_snd)
  have hKχ : Measurable (fun p : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      KχfrU v h μ fu N p.2) :=
    (measurable_KχfrU v h μ fu N).comp measurable_snd
  have hKs : Measurable (fun p : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      Work.BoseBoxFock.Ksfr v fc μ N (p.1.2.2 + p.2)) :=
    continuous_Ksfr.measurable.comp
      ((measurable_fst.snd.snd).add measurable_snd)
  unfold dChanG
  exact ((hA.mul measurable_const).mul (hχ.mul hKχ)).mul hKs

/-- The uniform bound on the joint integrand. -/
lemma norm_dChanG_le {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) {Θ : Submission.BoseGases.X n → ℝ}
    {C Kχ Ks : ℝ} (hC : ∀ x, |Θ x| ≤ C)
    (hKχ : ∀ z : E3, ‖KχfrU v h μ fu N z‖ ≤ Kχ)
    (hKs : ∀ z : E3, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ Ks)
    (p : (Submission.BoseGases.X n × (E3 × E3)) × E3) :
    ‖dChanG i j v h fc fu μ N Θ p.1 p.2‖
      ≤ C * C * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
          * (Submission.BoseGases.chiSupAbs * Kχ) * Ks := by
  have hKχ0 : 0 ≤ Kχ := le_trans (norm_nonneg _) (hKχ 0)
  have hKs0 : 0 ≤ Ks := le_trans (norm_nonneg _) (hKs 0)
  have ha : ‖dChanA i j (Work.BoseBoxFock.ellH v μ) Θ p.1‖ ≤ C * C :=
    norm_dChanA_le i j _ hC p.1
  have hχ : ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)‖
      ≤ Submission.BoseGases.chiSupAbs := by
    rw [norm_ofReal_eq_abs]
    rw [show Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2
        = Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) p.2 from rfl]
    exact Submission.BoseGases.chiScale_abs_le_sup _ _
  have hcd : ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)
      * KχfrU v h μ fu N p.2‖ ≤ Submission.BoseGases.chiSupAbs * Kχ := by
    rw [norm_mul]
    exact mul_le_mul hχ (hKχ p.2) (norm_nonneg _) (Submission.BoseGases.chiSupAbs_nonneg)
  have he : ‖Work.BoseBoxFock.Ksfr v fc μ N (p.1.2.2 + p.2)‖ ≤ Ks := hKs _
  have hCD0 : (0:ℝ) ≤ (C * C) * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖ :=
    mul_nonneg (mul_self_nonneg C) (norm_nonneg _)
  have hCD1 : (0:ℝ) ≤ (C * C) * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
      * (Submission.BoseGases.chiSupAbs * Kχ) :=
    mul_nonneg hCD0 (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hKχ0)
  unfold dChanG
  refine le_trans (norm_mul_four_le _ _ _ _) ?_
  have h1 : ‖dChanA i j (Work.BoseBoxFock.ellH v μ) Θ p.1‖
      * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
      ≤ (C * C) * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖ :=
    mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have h2 : ‖dChanA i j (Work.BoseBoxFock.ellH v μ) Θ p.1‖
      * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
      * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)
          * KχfrU v h μ fu N p.2‖
      ≤ (C * C) * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
          * (Submission.BoseGases.chiSupAbs * Kχ) :=
    mul_le_mul h1 hcd (norm_nonneg _) hCD0
  have h3 : ‖dChanA i j (Work.BoseBoxFock.ellH v μ) Θ p.1‖
      * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
      * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 : ℝ) : ℂ)
          * KχfrU v h μ fu N p.2‖
      * ‖Work.BoseBoxFock.Ksfr v fc μ N (p.1.2.2 + p.2)‖
      ≤ (C * C) * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
          * (Submission.BoseGases.chiSupAbs * Kχ) * Ks :=
    mul_le_mul h2 he (norm_nonneg _) hCD1
  simpa using h3

/-- The joint integrand vanishes off `(abox n ℓ × (acube ℓ × acube ℓ)) × acube ℓ`. -/
lemma dChanG_eq_zero_of_notMem {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) {Θ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ))
    {p : (Submission.BoseGases.X n × (E3 × E3)) × E3}
    (hp : p ∉ (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)
        ×ˢ (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)
            ×ˢ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)))
        ×ˢ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) :
    dChanG i j v h fc fu μ N Θ p.1 p.2 = 0 := by
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with hp | hp
  · have h0 : dChanA i j (Work.BoseBoxFock.ellH v μ) Θ p.1 = 0 :=
      dChanA_eq_zero_of_notMem (Work.BoseBoxFock.ellH_pos v μ) hΘs hp
    unfold dChanG
    rw [h0]
    ring
  · have h0 : Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) p.2 = 0 := by
      by_contra hne
      have hmem : p.2 ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) :=
        Work.BoseB4.BoxData.chiLam_supp _ (Work.BoseBoxFock.ellH_pos v μ)
          (Function.mem_support.mpr hne)
      rw [Work.BoseBoxFock.boxL_eq_acube (Work.BoseBoxFock.ellH_pos v μ)] at hmem
      exact hp hmem
    unfold dChanG
    rw [h0, Complex.ofReal_zero]
    ring

theorem Dchan_fubini_qw {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * ∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
      = ∫ w : EuclideanSpace ℝ (Fin 3),
          ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
            * ∫ q : Submission.BoseGases.X n
                  × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
                ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
                  * ((Θ q.1 : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
                  * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w) := by
  -- `volume` on the product type `X n × (E³×E³)` is `volume.prod volume`; the `SFinite` instance
  -- for it is not found by instance search, so it is supplied here explicitly.
  haveI hSF : SFinite (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) :=
    @Measure.instSFiniteProdVolume (Submission.BoseGases.X n) (E3 × E3) _ _ _ _
  obtain ⟨C, hC⟩ := hΘb
  have hKχb : ∀ z : E3, ‖KχfrU v h μ fu N z‖
      ≤ ∑ k : Work.BoseBoxFock.Lab N,
          |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| :=
    fun z => norm_KχfrU_le v h μ fu N z
  have hKsb : ∀ z : E3, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖
      ≤ ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
          |Work.BoseBoxFock.fLh v fc μ N s| := fun z => norm_Ksfr_le z
  have hFb : ∀ p : (Submission.BoseGases.X n × (E3 × E3)) × E3,
      ‖dChanG i j v h fc fu μ N Θ p.1 p.2‖
        ≤ C * C * ‖((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)‖
            * (Submission.BoseGases.chiSupAbs
                * ∑ k : Work.BoseBoxFock.Lab N,
                    |Work.BoseBoxFock.W1h v h μ fu N k
                      * Work.BoseBoxFock.hatChih v μ N k|)
            * ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                |Work.BoseBoxFock.fLh v fc μ N s| :=
    fun p => norm_dChanG_le i j v h fc fu μ N hC hKχb hKsb p
  have hint : Integrable (fun p : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      dChanG i j v h fc fu μ N Θ p.1 p.2)
      ((volume : Measure (Submission.BoseGases.X n × (E3 × E3))).prod (volume : Measure E3)) := by
    refine integrable_of_bounded_support
      (s := (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)
        ×ˢ (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)
            ×ˢ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)))
        ×ˢ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) ?_ ?_ hFb ?_
    · rw [MeasureTheory.Measure.prod_prod]
      exact ENNReal.mul_lt_top (volume_abox_prod_acube_prod_acube_lt_top n hℓ)
        (Submission.BoseGases.acube_lt_top (Work.BoseBoxFock.ellH v μ) hℓ.le)
    · exact measurable_dChanG i j hΘm
    · intro p hp
      exact dChanG_eq_zero_of_notMem i j v h fc fu μ N hℓ hΘs hp
  have hswap : (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ∫ w : E3, dChanG i j v h fc fu μ N Θ q w)
      = ∫ w : E3, ∫ q : Submission.BoseGases.X n × (E3 × E3),
          dChanG i j v h fc fu μ N Θ q w :=
    MeasureTheory.integral_integral_swap
      (μ := (volume : Measure (Submission.BoseGases.X n × (E3 × E3))))
      (ν := (volume : Measure E3)) (f := dChanG i j v h fc fu μ N Θ) hint
  have hA : (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * ∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          ∫ w : E3, dChanG i j v h fc fu μ N Θ q w := by
    apply integral_congr_ae
    filter_upwards with q
    show dChanA i j (Work.BoseBoxFock.ellH v μ) Θ q
        * ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
        * (∫ w : E3,
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
        = ∫ w : E3, dChanG i j v h fc fu μ N Θ q w
    rw [← MeasureTheory.integral_const_mul
      (dChanA i j (Work.BoseBoxFock.ellH v μ) Θ q
        * ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ))
      (fun w => ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
        * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
        * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)]
    apply integral_congr_ae
    filter_upwards with w
    unfold dChanG
    ring
  have hC2 : (∫ w : E3, ∫ q : Submission.BoseGases.X n × (E3 × E3),
        dChanG i j v h fc fu μ N Θ q w)
      = ∫ w : E3, ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
          * ∫ q : Submission.BoseGases.X n × (E3 × E3),
              dChanA i j (Work.BoseBoxFock.ellH v μ) Θ q
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w) := by
    apply integral_congr_ae
    filter_upwards with w
    rw [← MeasureTheory.integral_const_mul
      (((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w))
      (fun q => dChanA i j (Work.BoseBoxFock.ellH v μ) Θ q
        * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w))]
    apply integral_congr_ae
    filter_upwards with q
    unfold dChanG
    ring
  have hD : (∫ w : E3, ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
          * ∫ q : Submission.BoseGases.X n × (E3 × E3),
              dChanA i j (Work.BoseBoxFock.ellH v μ) Θ q
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w))
      = ∫ w : EuclideanSpace ℝ (Fin 3),
          ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w)
            * ∫ q : Submission.BoseGases.X n
                  × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
                ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
                  * ((Θ q.1 : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
                  * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w) := rfl
  exact hA.trans (hswap.trans (hC2.trans hD))

end Work.BoseBoxFock.PCFU
