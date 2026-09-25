/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary estimates for the Bochner–Martinelli divergence computation

This file collects the elementary analytic facts used in
`Submission/Work/CR/Flat/Cauchy/bmKernel_divergence_of_eps.lean`:

* `bmKerEps k ε x → bmKernel k x` as `ε → 0⁺` (pointwise, for every `x`);
* the uniform domination `‖bmKerEps k ε x‖ ≤ ‖bmKernel k x‖`;
* continuity of the regularised kernel `bmKerEps k ε` for `ε ≠ 0`;
* `dbarCoord k g` is continuous with compact support when `g` is `C¹` and vanishes
  outside a ball;
* integrability of `x ↦ bmKernel k x * dbarCoord k g x`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-! ### Continuity of `nrmSq` and of the regularised kernel -/

lemma continuous_nrmSq {n : ℕ} : Continuous (fun x : Fin n → ℂ => nrmSq x) := by
  unfold nrmSq
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).norm.pow 2

lemma continuous_bmKerEps {n : ℕ} (k : Fin n) {ε : ℝ} (hε : ε ≠ 0) :
    Continuous (fun x : Fin n → ℂ => bmKerEps k ε x) := by
  have hpow : ∀ x : Fin n → ℂ, (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n ≠ 0 := by
    intro x
    apply pow_ne_zero
    have hp : 0 < nrmSq x + ε ^ 2 :=
      add_pos_of_nonneg_of_pos (nrmSq_nonneg x) (sq_pos_of_ne_zero hε)
    exact_mod_cast hp.ne'
  have hnum : Continuous (fun x : Fin n → ℂ => starRingEnd ℂ (x k)) := by
    change Continuous (fun x : Fin n → ℂ => star (x k))
    exact continuous_star.comp (continuous_apply k)
  have hden : Continuous (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ))) : ℂ) ^ n) :=
    (Complex.continuous_ofReal.comp (continuous_nrmSq.add continuous_const)).pow n
  exact Continuous.div hnum hden hpow

/-! ### Pointwise convergence of the regularised kernel -/

lemma bmKerEps_tendsto {n : ℕ} (k : Fin n) (x : Fin n → ℂ) :
    Tendsto (fun ε : ℝ => bmKerEps k ε x) (𝓝[>] (0 : ℝ)) (𝓝 (bmKernel k x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : ∀ ε : ℝ, bmKerEps k ε 0 = bmKernel k 0 := by
      intro ε
      simp [bmKerEps, bmKernel, nrmSq]
    simpa only [h] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => bmKernel k 0) (𝓝[>] (0 : ℝ))
        (𝓝 (bmKernel k 0)))
  · have hpos : 0 < nrmSq x := nrmSq_pos hx
    have hden : ((((nrmSq x : ℝ)) : ℂ) ^ n) ≠ 0 := by
      apply pow_ne_zero
      simp only [Complex.ofReal_ne_zero]
      positivity
    have h1 : Tendsto (fun ε : ℝ => (nrmSq x + ε ^ 2 : ℝ)) (𝓝[>] (0 : ℝ))
        (𝓝 (nrmSq x)) := by
      have hc : Continuous (fun ε : ℝ => nrmSq x + ε ^ 2) := by fun_prop
      have h : Tendsto (fun ε : ℝ => nrmSq x + ε ^ 2) (𝓝 (0 : ℝ)) (𝓝 (nrmSq x)) := by
        simpa using hc.tendsto (0 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (((nrmSq x : ℝ)) : ℂ)) := by
      have h : Tendsto (fun ε : ℝ => Complex.ofReal (nrmSq x + ε ^ 2)) (𝓝[>] (0 : ℝ))
          (𝓝 (Complex.ofReal (nrmSq x))) :=
        (Complex.continuous_ofReal.tendsto (nrmSq x)).comp h1
      exact h
    have h3 : Tendsto (fun ε : ℝ => ((((nrmSq x + ε ^ 2 : ℝ))) : ℂ) ^ n) (𝓝[>] (0 : ℝ))
        (𝓝 (((((nrmSq x : ℝ))) : ℂ) ^ n)) := Filter.Tendsto.pow h2 n
    have h4 : Tendsto
        (fun ε : ℝ => starRingEnd ℂ (x k) / ((((nrmSq x + ε ^ 2 : ℝ))) : ℂ) ^ n)
        (𝓝[>] (0 : ℝ)) (𝓝 (starRingEnd ℂ (x k) / ((((nrmSq x : ℝ))) : ℂ) ^ n)) := by
      exact Filter.Tendsto.div
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => starRingEnd ℂ (x k)) (𝓝[>] (0 : ℝ))
          (𝓝 (starRingEnd ℂ (x k)))) h3 hden
    simpa only [bmKerEps_apply, bmKernel_eq] using h4

/-! ### Norm domination -/

lemma norm_bmKerEps_le {n : ℕ} (k : Fin n) (ε : ℝ) (x : Fin n → ℂ) :
    ‖bmKerEps k ε x‖ ≤ ‖bmKernel k x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [bmKerEps, bmKernel, nrmSq]
  · have hpos : 0 < nrmSq x := nrmSq_pos hx
    have hle : nrmSq x ≤ nrmSq x + ε ^ 2 := le_add_of_nonneg_right (sq_nonneg ε)
    have hξ : ‖(((nrmSq x + ε ^ 2 : ℝ)) : ℂ)‖ = nrmSq x + ε ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (le_of_lt hpos) hle)]
    have hη : ‖(((nrmSq x : ℝ)) : ℂ)‖ = nrmSq x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
    simp only [bmKerEps_apply, bmKernel_eq, norm_div, norm_pow, starRingEnd_apply, norm_star,
      hξ, hη]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hpos n)
      (pow_le_pow_left₀ (le_of_lt hpos) hle n)

/-! ### Continuous compactly supported `dbarCoord` -/

lemma continuous_dbarCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) (k : Fin n) :
    Continuous (dbarCoord k g) := by
  have hf : Continuous fun z : Fin n → ℂ => fderiv ℝ g z := hg.continuous_fderiv (by norm_num)
  have h1 : Continuous fun z : Fin n → ℂ => fderiv ℝ g z (Pi.single k (1 : ℂ)) :=
    hf.clm_apply continuous_const
  have h2 : Continuous fun z : Fin n → ℂ => fderiv ℝ g z (Pi.single k (Complex.I)) :=
    hf.clm_apply continuous_const
  exact continuous_const.mul (h1.add (continuous_const.mul h2))

lemma dbarCoord_eq_zero_of_lt_norm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k : Fin n) {x : Fin n → ℂ}
    (hx : R < ‖x‖) : dbarCoord k g x = 0 := by
  have hmem : {y : Fin n → ℂ | R < ‖y‖} ∈ 𝓝 x :=
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) hx
  have heq : g =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hmem] with y hy
    exact hsupp y hy.le
  have hfd : fderiv ℝ g x = 0 := by
    rw [heq.fderiv_eq]
    simp
  unfold dbarCoord
  rw [hfd]
  simp

lemma hasCompactSupport_dbarCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k : Fin n) :
    HasCompactSupport (dbarCoord k g) := by
  rw [HasCompactSupport]
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin n → ℂ) R)
    (isClosed_tsupport (dbarCoord k g)) (closure_minimal ?_ Metric.isClosed_closedBall)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push Not at hlt
  exact hx (dbarCoord_eq_zero_of_lt_norm hsupp k hlt)

/-! ### Integrability of the kernel against a compactly supported `C¹` function -/

lemma integrable_bmKernel_mul_dbarCoord {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k : Fin n) :
    Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord k g x) := by
  have h1 : Integrable (fun x : Fin n → ℂ => dbarCoord k g x • bmKernel k x) :=
    (locallyIntegrable_bmKernel hn k).integrable_smul_left_of_hasCompactSupport
      (continuous_dbarCoord hg k) (hasCompactSupport_dbarCoord hsupp k)
  simpa only [smul_eq_mul, mul_comm] using h1

/-- A `C¹` function vanishing outside a ball is bounded. -/
lemma exists_norm_le_of_supp {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin n → ℂ, ‖g x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ :
      ∃ C : ℝ, ∀ x ∈ Metric.closedBall (0 : Fin n → ℂ) R, ‖g x‖ ≤ C :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).exists_bound_of_continuousOn
      hg.continuous.continuousOn
  refine ⟨max C₀ 0, le_max_right C₀ 0, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · exact (hC₀ x (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx)).trans (le_max_left C₀ 0)
  · rw [hsupp x (le_of_lt (lt_of_not_ge hx)), norm_zero]
    exact le_max_right C₀ 0

end Work.CR.Flat.Cauchy
