/-
# §3 of Cohen's paper: the plurisubharmonic extension `Eω + C|y|`

This module proves `exact_psh_extension_statement` (`prop:Ew_is_psh`).
-/
import Submission.FUP.ExtensionOperator
import Submission.Commons.Analysis.Calculus.contDiffOn_two_Eomega_diag
import Submission.Commons.Analysis.Calculus.laplacian_comp_add_smul
import Submission.Commons.Analysis.Calculus.laplacian_comp_add_smul_general
import Submission.Commons.Analysis.Complex.Harmonic.localSubMeanValue_of_laplacian_nonneg
import Submission.Commons.MeasureTheory.Integral.integral_iteratedFDeriv_two_apply_eq_zero
import Submission.Commons.MeasureTheory.Integral.integral_fderiv_comp_line_eq_zero
import Submission.FUP.EomegaTail
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue
import Submission.Commons.Analysis.Real.abs_poissonExtension_sub_le
import Submission.Commons.Measure.Real.integral_comp_mul_inv_one_add_sq

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Real RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 6400000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-- **Directional local circle sub-mean-value property** on `ℂᵈ`: at every point `z` and for
every direction `v`, the circle sub-mean-value inequality holds for all sufficiently small
radii `ρ`. -/
def DirLocalSubMeanValue (u : ℂᵈ → ℝ) : Prop :=
  ∀ z : ℂᵈ, ∀ v : ℂᵈ, ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ε →
    u z ≤ (∫ θ in (0 : ℝ)..(2 * π), u (z + circlePt θ (ρ • v))) / (2 * π)

lemma circlePt_eq_smul (θ : ℝ) (v : ℂᵈ) :
    circlePt θ v = Complex.exp (θ * Complex.I) • v := rfl

lemma circlePt_smul (θ ρ : ℝ) (v : ℂᵈ) :
    circlePt θ (ρ • v) = (ρ : ℂ) • circlePt θ v := by
  ext i
  simp only [circlePt_apply, Pi.smul_apply, Complex.real_smul]
  ring

lemma circleAverage_eq_interval (g : ℂ → ℝ) (p : ℂ) (r : ℝ) :
    Real.circleAverage g p r
      = (∫ θ in (0 : ℝ)..(2 * π), g (p + (r : ℂ) * Complex.exp (θ * Complex.I)))
        / (2 * π) := by
  simp only [Real.circleAverage_def, circleMap, smul_eq_mul]
  rw [inv_mul_eq_div]

/-- The local circle sub-mean-value property in every direction implies the global one. -/
theorem subMeanValue_of_dirLocalSubMeanValue (u : ℂᵈ → ℝ) (hcont : Continuous u)
    (h : DirLocalSubMeanValue u) : SubMeanValue u := by
  intro z v
  by_cases hv : v = 0
  · subst hv
    have hz : ∀ θ : ℝ, u (z + circlePt θ (0 : ℂᵈ)) = u z := by
      intro θ
      congr 1
      ext i
      simp [circlePt]
    rw [intervalIntegral.integral_congr (fun θ _ => hz θ)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    rw [mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) * π ≠ 0)]
  · set g : ℂ → ℝ := fun ζ => u (z + ζ • v) with hg
    have hgcont : ContinuousOn g (univ : Set ℂ) := hcont.comp (by fun_prop) |>.continuousOn
    have hgloc : ∀ p ∈ (univ : Set ℂ), ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ univ ∧
        ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball p ε →
          g p ≤ Real.circleAverage g p r := by
      intro p _
      obtain ⟨ε, hε, hε'⟩ := h (z + p • v) v
      refine ⟨ε, hε, subset_univ _, fun r hr hsub => ?_⟩
      have hrε : r < ε := by
        by_contra hcon
        rw [not_lt] at hcon
        have hmem : p + (r : ℂ) ∈ Metric.closedBall p r := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          rw [show p + (r : ℂ) - p = (r : ℂ) by ring, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hr]
        have hb := hsub hmem
        rw [Metric.mem_ball, dist_eq_norm] at hb
        rw [show p + (r : ℂ) - p = (r : ℂ) by ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr] at hb
        linarith
      have hkey := hε' r hr hrε
      rw [circleAverage_eq_interval]
      have hcongr : ∀ θ : ℝ,
          g (p + (r : ℂ) * Complex.exp (θ * Complex.I))
            = u (z + p • v + circlePt θ (r • v)) := by
        intro θ
        have h1 : (p + (r : ℂ) * Complex.exp (θ * Complex.I)) • v
            = p • v + circlePt θ (r • v) := by
          rw [add_smul, ← smul_smul, ← circlePt_eq_smul, ← circlePt_smul]
        show u (z + ((p + (r : ℂ) * Complex.exp (θ * Complex.I)) • v)) = _
        rw [h1, add_assoc]
      rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
      show u (z + p • v) ≤ _
      exact hkey
    have hres := Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue
      isOpen_univ hgcont hgloc
      0 (mem_univ 0) 1 one_pos (subset_univ _)
    rw [circleAverage_eq_interval] at hres
    simp only [zero_add, Complex.ofReal_one, one_mul] at hres
    have hg0 : g 0 = u z := by simp [hg]
    rw [hg0] at hres
    exact hres

/-! ## Tools for the line restriction of a weight -/

section LineTools

/-- The restriction of a compactly supported function to a line is compactly supported. -/
lemma hasCompactSupport_comp_line {ω : ℝᵈ → ℝ} (hc : HasCompactSupport ω) (x ŷ : ℝᵈ)
    (hŷ : ‖ŷ‖ = 1) : HasCompactSupport (fun t : ℝ => ω (x + t • ŷ)) := by
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn continuousOn_id
  have hsub : tsupport (fun t : ℝ => ω (x + t • ŷ)) ⊆ Set.Icc (-(M + ‖x‖)) (M + ‖x‖) := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    rw [Function.mem_support] at ht
    have hnorm : ‖t • ŷ‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hŷ, mul_one]
    have hle : |t| ≤ M + ‖x‖ := by
      have h4 : ‖t • ŷ‖ ≤ ‖x + t • ŷ‖ + ‖x‖ := by
        calc ‖t • ŷ‖ = ‖(x + t • ŷ) - x‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖x + t • ŷ‖ + ‖x‖ := norm_sub_le _ _
      rw [hnorm] at h4
      have ht' : x + t • ŷ ∈ Function.support ω := by simpa [Function.mem_support] using ht
      have h5 : ‖x + t • ŷ‖ ≤ M := hM (x + t • ŷ) (subset_tsupport ω ht')
      linarith
    exact abs_le.mp hle
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsub

/-- The Hilbert-transform hypothesis, transported to the line restriction of `ω`. -/
lemma hilbert_line_translate {ω : ℝᵈ → ℝ} (hdiff : Differentiable ℝ ω) {C₁ : ℝ}
    (hH : ∀ x y : ℝᵈ, ‖y‖ = 1 → |hilbertLine ω x y| ≤ C₁) (x ŷ : ℝᵈ) (hŷ : ‖ŷ‖ = 1) :
    ∀ s : ℝ, |(1 / π) * ∫ t in Set.Ioi (0 : ℝ),
      (deriv (fun u : ℝ => ω (x + u • ŷ)) (s + t)
        - deriv (fun u : ℝ => ω (x + u • ŷ)) (s - t)) / t| ≤ C₁ := by
  intro s
  have h1 : ∀ u : ℝ, deriv (fun u : ℝ => ω (x + u • ŷ)) u
      = dirDeriv ω (x + u • ŷ) ŷ := fun u => deriv_comp_line hdiff x ŷ u
  have hE : (∫ t in Set.Ioi (0 : ℝ), (deriv (fun u : ℝ => ω (x + u • ŷ)) (s + t)
          - deriv (fun u : ℝ => ω (x + u • ŷ)) (s - t)) / t)
      = ∫ t in Set.Ioi (0 : ℝ),
          (dirDeriv ω (x + s • ŷ + t • ŷ) ŷ - dirDeriv ω (x + s • ŷ - t • ŷ) ŷ) / t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show (deriv (fun u : ℝ => ω (x + u • ŷ)) (s + t)
        - deriv (fun u : ℝ => ω (x + u • ŷ)) (s - t)) / t
      = (dirDeriv ω (x + s • ŷ + t • ŷ) ŷ - dirDeriv ω (x + s • ŷ - t • ŷ) ŷ) / t
    rw [h1 (s + t), h1 (s - t),
      show x + (s + t) • ŷ = (x + s • ŷ) + t • ŷ by rw [add_smul]; abel,
      show x + (s - t) • ŷ = (x + s • ŷ) - t • ŷ by rw [sub_smul]; abel]
  rw [hE]
  exact hH (x + s • ŷ) ŷ hŷ

end LineTools

/-! ## The two-sided bound for the extension of a weight -/

/-- **Lemma `lem:props_Eomega`(b).**  If the Hilbert transform of the derivative of `ω` along
every line is bounded by `C₁`, then the extension operator does not move `ω` by more than
`C₁‖y‖`. -/
lemma abs_Eomega_sub_le {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 3 ω) (hc : HasCompactSupport ω) {C₁ : ℝ}
    (hH : ∀ x y : ℝᵈ, ‖y‖ = 1 → |hilbertLine ω x y| ≤ C₁) :
    ∀ x y : ℝᵈ, |Eomega ω x y - ω x| ≤ C₁ * ‖y‖ := by
  intro x y
  rcases eq_or_lt_of_le (norm_nonneg y) with hy | hy
  · have hy0 : y = 0 := norm_eq_zero.mp hy.symm
    rw [hy0, Eomega_apply_zero, sub_self, abs_zero]
    simp
  · set σ : ℝ := ‖y‖ with hσdef
    set ŷ : ℝᵈ := σ⁻¹ • y with hŷdef
    have hσ : 0 < σ := hy
    have hŷ1 : ‖ŷ‖ = 1 := by
      rw [hŷdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy), inv_mul_cancel₀ hy.ne']
    have hyσ : y = σ • ŷ := by
      rw [hŷdef, smul_smul, mul_inv_cancel₀ hy.ne', one_smul]
    set φ : ℝ → ℝ := fun t => ω (x + t • ŷ) with hφdef
    have hφcd : ContDiff ℝ 2 φ := by
      rw [hφdef]
      exact (hω.of_le (by norm_num)).comp (by fun_prop)
    have hφcpt : HasCompactSupport φ := hasCompactSupport_comp_line hc x ŷ hŷ1
    have hφH := hilbert_line_translate (hω.differentiable (by norm_num)) hH x ŷ hŷ1
    have h1d := Commons.Analysis.Real.abs_poissonExtension_sub_le hφcd hφcpt hφH σ hσ
    have hφ0 : φ 0 = ω x := by simp [hφdef]
    rw [hφ0] at h1d
    rw [hyσ]
    have hval : Eomega ω x (σ • ŷ) = (1 / π) * ∫ t : ℝ, φ t * (σ / (σ ^ 2 + t ^ 2)) := by
      rw [Eomega]
      congr 1
      have hsubst : (∫ t : ℝ, ω (x + t • (σ • ŷ)) * (1 + t ^ 2)⁻¹)
          = ∫ t : ℝ, φ (t * σ) * (1 + t ^ 2)⁻¹ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hφdef, smul_smul]
      rw [hsubst, Commons.Measure.Real.integral_comp_mul_inv_one_add_sq hσ,
        ← integral_const_mul]
      congr 1
      ext u
      rw [div_eq_mul_inv]
      ring
    rw [hval]
    rw [hσdef] at h1d
    rw [mul_comm ‖y‖ C₁] at h1d
    exact h1d




/-! ## The tilted extension `u = Eω + C‖Im·‖` -/

/-- The function `U(x,y) = Eω(x,y) + C‖y‖` on `ℝᵈ × ℝᵈ`. -/
noncomputable def UWeight (ω : ℝᵈ → ℝ) (C : ℝ) : ℝᵈ × ℝᵈ → ℝ :=
  fun p => Eomega ω p.1 p.2 + C * ‖p.2‖

lemma UWeight_apply (ω : ℝᵈ → ℝ) (C : ℝ) (x y : ℝᵈ) :
    UWeight ω C (x, y) = Eomega ω x y + C * ‖y‖ := rfl

/-- The candidate plurisubharmonic extension `u = Eω + C‖Im·‖` of §3. -/
noncomputable def uWeight (ω : ℝᵈ → ℝ) (C : ℝ) : ℂᵈ → ℝ :=
  fun z => UWeight ω C (reVec z, imVec z)

lemma uWeight_apply (ω : ℝᵈ → ℝ) (C : ℝ) (z : ℂᵈ) :
    uWeight ω C z = EomegaC ω z + C * ‖imVec z‖ := by
  simp [uWeight, UWeight, EomegaC]

lemma uWeight_toCpx (ω : ℝᵈ → ℝ) (C : ℝ) (x : ℝᵈ) : uWeight ω C (toCpx x) = ω x := by
  simp [uWeight, UWeight, Eomega_apply_zero, imVec_toCpx, reVec_toCpx]

lemma uWeight_eq_comp (ω : ℝᵈ → ℝ) (C : ℝ) :
    uWeight ω C = fun w : ℂᵈ => UWeight ω C (reVec w, imVec w) := rfl

lemma reVec_add (z w : ℂᵈ) : reVec (z + w) = reVec z + reVec w := by
  ext i; simp [reVec_apply]

lemma imVec_add (z w : ℂᵈ) : imVec (z + w) = imVec z + imVec w := by
  ext i; simp [imVec_apply]

lemma reVec_add_toCpx (x : ℝᵈ) (z : ℂᵈ) : reVec (toCpx x + z) = x + reVec z := by
  rw [reVec_add, reVec_toCpx]

lemma imVec_add_toCpx (x : ℝᵈ) (z : ℂᵈ) : imVec (toCpx x + z) = imVec z := by
  rw [imVec_add, imVec_toCpx, zero_add]

/-- A global bound on the second derivative of a compactly supported `C²` weight. -/
lemma exists_iteratedFDeriv_two_bound {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ x : ℝᵈ, ‖iteratedFDeriv ℝ 2 ω x‖ ≤ lam := by
  have hcont : Continuous fun x : ℝᵈ => ‖iteratedFDeriv ℝ 2 ω x‖ :=
    (hω.continuous_iteratedFDeriv (by norm_num)).norm
  obtain ⟨M, hM⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) 2).isCompact.exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (iteratedFDeriv ℝ 2 ω)
  · exact le_trans (by simpa using hM x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx]; simp

lemma continuous_circlePt_c (v : ℂᵈ) : Continuous fun θ : ℝ => circlePt θ v := by
  have h : (fun θ : ℝ => circlePt θ v)
      = fun θ : ℝ => fun i : Fin d => Complex.exp (θ * Complex.I) * v i := rfl
  rw [h]
  exact continuous_pi fun i => by
    have h2 : (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * v i)
        = fun θ : ℝ => (Real.cos θ + Real.sin θ * Complex.I) * v i := by
      funext θ; rw [Complex.exp_ofReal_mul_I]
    rw [h2]
    fun_prop

lemma continuous_reVec_circlePt (v : ℂᵈ) : Continuous fun θ : ℝ => reVec (circlePt θ v) := by
  have hcoord : Continuous fun θ : ℝ => (fun i : Fin d => (circlePt θ v i).re) := by
    apply continuous_pi
    intro i
    have hfun : (fun θ : ℝ => (circlePt θ v i).re)
        = fun θ : ℝ => Real.cos θ * (v i).re - Real.sin θ * (v i).im := by
      funext θ; exact reVec_circlePt_apply θ v i
    rw [hfun]
    fun_prop
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp hcoord

lemma continuous_imVec_circlePt (v : ℂᵈ) : Continuous fun θ : ℝ => imVec (circlePt θ v) := by
  have hcoord : Continuous fun θ : ℝ => (fun i : Fin d => (circlePt θ v i).im) := by
    apply continuous_pi
    intro i
    have hfun : (fun θ : ℝ => (circlePt θ v i).im)
        = fun θ : ℝ => Real.sin θ * (v i).re + Real.cos θ * (v i).im := by
      funext θ; exact imVec_circlePt_apply θ v i
    rw [hfun]
    fun_prop
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp hcoord

/-- **The sub-mean-value estimate at points of `ℝᵈ`** (the second half of `prop:Ew_is_psh`). -/
lemma localSubMeanValue_realPoint {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) {C₁ C : ℝ} (hC : C₁ < C)
    (hbound : ∀ x y : ℝᵈ, |Eomega ω x y - ω x| ≤ C₁ * ‖y‖) (x : ℝᵈ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : ℂᵈ, enorm v < ε →
      uWeight ω C (toCpx x)
        ≤ (∫ θ in (0 : ℝ)..(2 * π), uWeight ω C (toCpx x + circlePt θ v)) / (2 * π) := by
  obtain ⟨lam, hlam, hlam2⟩ := exists_iteratedFDeriv_two_bound hω hc
  have hCpos : 0 < C - C₁ := sub_pos.mpr hC
  have hlam1 : 0 < lam + 1 := by linarith
  refine ⟨(C - C₁) / (2 * (lam + 1)), by positivity, fun v hv => ?_⟩
  have hpt : ∀ θ : ℝ, ω (x + reVec (circlePt θ v)) + (C - C₁) * ‖imVec (circlePt θ v)‖
      ≤ uWeight ω C (toCpx x + circlePt θ v) := by
    intro θ
    have hb := hbound (x + reVec (circlePt θ v)) (imVec (circlePt θ v))
    have h1 : ω (x + reVec (circlePt θ v)) - C₁ * ‖imVec (circlePt θ v)‖
        ≤ Eomega ω (x + reVec (circlePt θ v)) (imVec (circlePt θ v)) := by
      have := (abs_le.mp hb).1
      linarith
    rw [uWeight_apply, EomegaC, reVec_add_toCpx, imVec_add_toCpx]
    nlinarith [h1]
  have hcont1 : Continuous fun θ : ℝ => ω (x + reVec (circlePt θ v)) :=
    hω.continuous.comp (continuous_const.add (continuous_reVec_circlePt v))
  have hcont2 : Continuous fun θ : ℝ => (C - C₁) * ‖imVec (circlePt θ v)‖ :=
    continuous_const.mul (continuous_imVec_circlePt v).norm
  have hcont3 : Continuous fun θ : ℝ => uWeight ω C (toCpx x + circlePt θ v) := by
    have h : (fun θ : ℝ => uWeight ω C (toCpx x + circlePt θ v))
        = fun θ : ℝ => EomegaC ω (toCpx x + circlePt θ v) + C * ‖imVec (circlePt θ v)‖ := by
      funext θ; rw [uWeight_apply, imVec_add_toCpx]
    rw [h]
    exact ((continuous_EomegaC hω.continuous hc).comp
      (continuous_const.add (continuous_circlePt_c v))).add
      (continuous_const.mul (continuous_imVec_circlePt v).norm)
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
        (ω (x + reVec (circlePt θ v)) + (C - C₁) * ‖imVec (circlePt θ v)‖))
      ≤ ∫ θ in (0 : ℝ)..(2 * π), uWeight ω C (toCpx x + circlePt θ v) :=
    intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * π)
      ((hcont1.add hcont2).intervalIntegrable _ _) (hcont3.intervalIntegrable _ _) hpt
  have hsplit : (∫ θ in (0 : ℝ)..(2 * π),
        (ω (x + reVec (circlePt θ v)) + (C - C₁) * ‖imVec (circlePt θ v)‖))
      = (∫ θ in (0 : ℝ)..(2 * π), ω (x + reVec (circlePt θ v)))
        + (C - C₁) * (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖) := by
    rw [intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  rw [hsplit] at hint
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hωm := circleMean_omega_ge_of_contDiff hlam hω hlam2 x v
  have him := circleMean_imVec_ge v
  have h1 : (2 * π) * (ω x - lam * enorm v ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(2 * π), ω (x + reVec (circlePt θ v)) := by
    have := (le_div_iff₀ h2π).mp hωm
    linarith [this]
  have h2 : (2 * π) * (enorm v / 2)
      ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖ := by
    have := (le_div_iff₀ h2π).mp him
    linarith [this]
  have hbig : ω x - lam * enorm v ^ 2 + (C - C₁) * enorm v / 2
      ≤ (∫ θ in (0 : ℝ)..(2 * π), uWeight ω C (toCpx x + circlePt θ v)) / (2 * π) := by
    rw [le_div_iff₀ h2π]
    have h3 : (C - C₁) * ((2 * π) * (enorm v / 2))
        ≤ (C - C₁) * (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖) :=
      mul_le_mul_of_nonneg_left h2 hCpos.le
    nlinarith [hint, h1, h3, h2π, Real.pi_pos]
  refine le_trans ?_ hbig
  rw [uWeight_toCpx]
  have hsmall : lam * enorm v ^ 2 ≤ (C - C₁) * enorm v / 2 := by
    rcases eq_or_lt_of_le (enorm_nonneg v) with h0 | hpos
    · rw [← h0]; simp
    · have h1 : (lam + 1) * enorm v < (C - C₁) / 2 := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (lam + 1))] at hv
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hv]
      calc lam * enorm v ^ 2 ≤ (lam + 1) * enorm v ^ 2 := by nlinarith [sq_nonneg (enorm v)]
        _ = ((lam + 1) * enorm v) * enorm v := by ring
        _ ≤ ((C - C₁) / 2) * enorm v := mul_le_mul_of_nonneg_right h1.le hpos.le
        _ = (C - C₁) * enorm v / 2 := by ring
  linarith


/-! ## The Hessian of `u = Eω + C‖Im·‖` in the coordinates `(Re, Im)` -/

lemma continuous_reVec : Continuous (reVec : ℂᵈ → ℝᵈ) := by
  have h : Continuous fun z : ℂᵈ => (fun i : Fin d => (z i).re) :=
    continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)
  change Continuous (fun z : ℂᵈ =>
    (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i : Fin d => (z i).re))
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp h

lemma continuous_imVec : Continuous (imVec : ℂᵈ → ℝᵈ) := by
  have h : Continuous fun z : ℂᵈ => (fun i : Fin d => (z i).im) :=
    continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i)
  change Continuous (fun z : ℂᵈ =>
    (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i : Fin d => (z i).im))
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp h

/-- The linear isometry `ℂᵈ → ℝᵈ × ℝᵈ`, `z ↦ (Re z, Im z)`. -/
noncomputable def reImVec : ℂᵈ →L[ℝ] (ℝᵈ × ℝᵈ) where
  toFun z := (reVec z, imVec z)
  map_add' z w := by ext <;> simp [reVec_add, imVec_add]
  map_smul' c z := by ext <;> simp [reVec, imVec]
  cont := continuous_reVec.prodMk continuous_imVec

lemma reImVec_apply (z : ℂᵈ) : reImVec z = (reVec z, imVec z) := rfl

/-- **The chain rule for the substitution `ℂᵈ → ℝᵈ × ℝᵈ`, `z ↦ (Re z, Im z)`.** -/
theorem iteratedFDeriv_comp_reImVec {U : ℝᵈ × ℝᵈ → ℝ}
    (hU : ContDiffOn ℝ 2 U {p : ℝᵈ × ℝᵈ | p.2 ≠ 0}) {z : ℂᵈ} (hz : imVec z ≠ 0) (a b : ℂᵈ) :
    (iteratedFDeriv ℝ 2 (fun w : ℂᵈ => U (reVec w, imVec w)) z) ![a, b]
      = (iteratedFDeriv ℝ 2 U (reVec z, imVec z))
          ![(reVec a, imVec a), (reVec b, imVec b)] := by
  set s : Set (ℝᵈ × ℝᵈ) := {p | p.2 ≠ 0} with hs
  have hsopen : IsOpen s := isOpen_ne.preimage continuous_snd
  have hgs : reImVec ⁻¹' s = {w : ℂᵈ | imVec w ≠ 0} := by
    ext w; simp [s, reImVec_apply]
  have hgopen : IsOpen (reImVec ⁻¹' s) := by rw [hgs]; exact isOpen_ne.preimage continuous_imVec
  have hx : reImVec z ∈ s := by simp [s, reImVec_apply, hz]
  have hcr := ContinuousLinearMap.iteratedFDerivWithin_comp_right reImVec hU
    hsopen.uniqueDiffOn (by rw [hgs]; exact hgopen.uniqueDiffOn) hx (i := 2) (le_refl 2)
  have h1 : iteratedFDerivWithin ℝ 2 (U ∘ reImVec) (reImVec ⁻¹' s) z
      = iteratedFDeriv ℝ 2 (U ∘ reImVec) z :=
    iteratedFDerivWithin_of_isOpen 2 hgopen (by rw [hgs]; exact hz)
  have h2 : iteratedFDerivWithin ℝ 2 U s (reImVec z) = iteratedFDeriv ℝ 2 U (reImVec z) :=
    iteratedFDerivWithin_of_isOpen 2 hsopen hx
  have hfun : (fun w : ℂᵈ => U (reVec w, imVec w)) = U ∘ reImVec := by
    funext w; rw [Function.comp_apply, reImVec_apply]
  have hmain : iteratedFDeriv ℝ 2 (fun w : ℂᵈ => U (reVec w, imVec w)) z
      = (iteratedFDeriv ℝ 2 U (reImVec z)).compContinuousLinearMap (fun _ => reImVec) := by
    rw [hfun, ← h1, hcr, h2]
  rw [hmain, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [show reImVec z = (reVec z, imVec z) from rfl]
  rw [show (fun i : Fin 2 => reImVec (![a, b] i))
      = ![(reVec a, imVec a), (reVec b, imVec b)] from by
    funext i; fin_cases i <;> simp [reImVec_apply]]


lemma contDiffOn_two_UWeight {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (C : ℝ) : ContDiffOn ℝ 2 (UWeight ω C) {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} := by
  have h1 : ContDiffOn ℝ 2 (fun p : ℝᵈ × ℝᵈ => ∫ u : ℝ, ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹)
      {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} :=
    Commons.Analysis.Calculus.contDiffOn_two_Eomega_diag hω hc
  have h4 : (fun p : ℝᵈ × ℝᵈ => (1 / π) * ∫ u : ℝ, ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹)
      = fun p : ℝᵈ × ℝᵈ => Eomega ω p.1 p.2 := by
    funext p; rw [Eomega]
  have h2 : ContDiffOn ℝ 2 (fun p : ℝᵈ × ℝᵈ => Eomega ω p.1 p.2) {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} := by
    rw [← h4]; exact contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ 2 (fun p : ℝᵈ × ℝᵈ => ‖p.2‖) {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} := by
    refine ContDiffOn.norm ℝ (f := fun p : ℝᵈ × ℝᵈ => p.2) ?_ ?_
    · exact contDiff_snd.contDiffOn
    · intro p hp; exact hp
  exact h2.add ((contDiffOn_const (c := C)).mul h3)


/-! ## The sub-mean-value property off `ℝᵈ` -/

lemma continuous_imVec_add_smul (z v : ℂᵈ) :
    Continuous fun ζ : ℂ => imVec (z + ζ • v) :=
  continuous_imVec.comp (continuous_const.add (continuous_id.smul continuous_const))

/-- Translation invariance of the Laplacian on `ℂ`. -/
lemma laplacian_comp_add_left_C (u : ℂ → ℝ) (a x : ℂ) :
    Laplacian.laplacian (fun z : ℂ => u (a + z)) x = Laplacian.laplacian u (a + x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, Pi.add_apply,
    iteratedFDeriv_comp_add_left]

/-- The Laplacian commutes with translation. -/
lemma laplacian_shift_C (u : ℂ → ℝ) (a : ℂ) :
    Laplacian.laplacian (fun ζ : ℂ => u (a + ζ)) 0 = Laplacian.laplacian u a := by
  rw [laplacian_comp_add_left_C u a 0, add_zero]

/-- The Laplacian of the pullback to a complex line, at an arbitrary point of the line. -/
lemma laplacian_comp_add_smul' {u : ℂᵈ → ℝ} {z v : ℂᵈ} (a : ℂ)
    (hu : ContDiffAt ℝ 2 u (z + a • v)) :
    Laplacian.laplacian (fun ζ : ℂ => u (z + ζ • v)) a
      = (iteratedFDeriv ℝ 2 u (z + a • v)) ![v, v]
        + (iteratedFDeriv ℝ 2 u (z + a • v)) ![Complex.I • v, Complex.I • v] := by
  have hcomp : (fun ζ : ℂ => (fun ψ : ℂ => u (z + ψ • v)) (a + ζ))
      = fun ζ : ℂ => u ((z + a • v) + ζ • v) := by
    funext ζ
    show u (z + (a + ζ) • v) = u ((z + a • v) + ζ • v)
    rw [add_smul]
    congr 1
    abel
  rw [← laplacian_shift_C (fun ζ : ℂ => u (z + ζ • v)) a]
  rw [hcomp]
  exact Commons.Analysis.Calculus.laplacian_comp_add_smul_general hu

lemma contDiffOn_two_uWeight' {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) (C : ℝ) :
    ContDiffOn ℝ 2 (uWeight ω C) {w : ℂᵈ | imVec w ≠ (0 : ℝᵈ)} := by
  have hU := contDiffOn_two_UWeight hω hc C
  have hf : ContDiffOn ℝ 2 (fun w : ℂᵈ => (reVec w, imVec w)) {w : ℂᵈ | imVec w ≠ 0} :=
    reImVec.contDiff.contDiffOn
  have hcomp := hU.comp hf (fun w hw => hw)
  have hfun : (UWeight ω C ∘ fun w : ℂᵈ => (reVec w, imVec w)) = uWeight ω C := by
    funext w; simp [Function.comp_apply, uWeight, UWeight, EomegaC]
  rwa [hfun] at hcomp

lemma contDiffAt_two_uWeight {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (C : ℝ) {z : ℂᵈ} (hz : imVec z ≠ 0) : ContDiffAt ℝ 2 (uWeight ω C) z := by
  have hU := contDiffOn_two_UWeight hω hc C
  have hmem : reImVec z ∈ {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} := hz
  have h1 : ContDiffAt ℝ 2 (UWeight ω C) (reImVec z) :=
    hU.contDiffAt ((isOpen_ne.preimage continuous_snd).mem_nhds hmem)
  exact h1.comp z (reImVec.contDiff.contDiffAt)

/-- **The sub-mean-value property off `ℝᵈ`**, from the nonnegativity of the Hessian of `uWeight`
along complex lines. -/
theorem dirLocalSubMeanValue_off_real {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) (C : ℝ)
    (hhess : ∀ z : ℂᵈ, imVec z ≠ 0 → ∀ vv : ℂᵈ,
      0 ≤ (iteratedFDeriv ℝ 2 (uWeight ω C) z) ![vv, vv]
        + (iteratedFDeriv ℝ 2 (uWeight ω C) z) ![Complex.I • vv, Complex.I • vv])
    {z : ℂᵈ} (hz : imVec z ≠ 0) (v : ℂᵈ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ε →
      uWeight ω C z ≤ (∫ θ in (0 : ℝ)..(2 * π),
        uWeight ω C (z + circlePt θ (ρ • v))) / (2 * π) := by
  set g : ℂ → ℝ := fun ζ => uWeight ω C (z + ζ • v) with hg
  set Ω : Set ℂ := {ζ : ℂ | imVec (z + ζ • v) ≠ 0} with hΩ
  have hΩopen : IsOpen Ω := isOpen_ne.preimage (continuous_imVec_add_smul z v)
  have h0Ω : (0 : ℂ) ∈ Ω := by
    rw [hΩ]; simpa using hz
  have hgc : ContDiffOn ℝ 2 g Ω := by
    have hU := contDiffOn_two_UWeight hω hc C
    have hlin : ContDiff ℝ 2 (fun ζ : ℂ => z + ζ • v) := by fun_prop
    have hf : ContDiffOn ℝ 2 (fun ζ : ℂ => (reVec (z + ζ • v), imVec (z + ζ • v))) Ω := by
      have h2 : (fun ζ : ℂ => (reVec (z + ζ • v), imVec (z + ζ • v)))
          = reImVec ∘ (fun ζ : ℂ => z + ζ • v) := by
        funext ζ; rw [Function.comp_apply, reImVec_apply]
      rw [h2]
      exact (reImVec.contDiff.comp hlin).contDiffOn
    have hcomp := hU.comp hf (fun ζ hζ => by rw [hΩ] at hζ; exact hζ)
    have hfun : (UWeight ω C ∘ fun ζ : ℂ => (reVec (z + ζ • v), imVec (z + ζ • v))) = g := by
      funext ζ; simp [Function.comp_apply, hg, uWeight, UWeight, EomegaC]
    rwa [hfun] at hcomp
  have hglap : ∀ ζ ∈ Ω, 0 ≤ Laplacian.laplacian g ζ := by
    intro ζ hζ
    have hmem : imVec (z + ζ • v) ≠ 0 := by rw [hΩ] at hζ; exact hζ
    rw [hg, laplacian_comp_add_smul' ζ (contDiffAt_two_uWeight hω hc C hmem)]
    exact hhess _ hmem v
  obtain ⟨ε, hε, _hεsub, hεineq⟩ :=
    Commons.Analysis.Complex.Harmonic.localSubMeanValue_of_laplacian_nonneg hΩopen hgc hglap
      0 h0Ω
  refine ⟨min 1 (ε / 2), lt_min one_pos (by linarith), fun ρ hρ hρlt => ?_⟩
  have hcl : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball 0 ε := by
    refine Metric.closedBall_subset_ball ?_
    have := lt_of_lt_of_le hρlt (min_le_right (1 : ℝ) (ε / 2))
    linarith
  have hkey := hεineq ρ hρ hcl
  rw [circleAverage_eq_interval] at hkey
  simp only [zero_add] at hkey
  have hg0 : g 0 = uWeight ω C z := by simp [hg]
  rw [hg0] at hkey
  have hfinal : (∫ θ in (0 : ℝ)..(2 * π), g ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
      = ∫ θ in (0 : ℝ)..(2 * π), uWeight ω C (z + circlePt θ (ρ • v)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    have h1 : g ((ρ : ℂ) * Complex.exp (θ * Complex.I))
        = uWeight ω C (z + ((ρ : ℂ) * Complex.exp (θ * Complex.I)) • v) := rfl
    have h2 : ((ρ : ℂ) * Complex.exp (θ * Complex.I)) • v = circlePt θ (ρ • v) := by
      rw [circlePt_smul, ← smul_smul]
      congr 1
    beta_reduce
    rw [h1, h2]
  rwa [hfinal] at hkey


/-! ## Assembly of `prop:Ew_is_psh` -/

lemma enorm_real_smul (ρ : ℝ) (v : ℂᵈ) : enorm (ρ • v) = |ρ| * enorm v := by
  have h1 : ∑ i : Fin d, ‖(ρ • v) i‖ ^ 2 = |ρ| ^ 2 * ∑ i : Fin d, ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [enorm, h1, enorm, Real.sqrt_mul (sq_nonneg |ρ|), Real.sqrt_sq (abs_nonneg ρ)]

/-- The nonnegativity of the Hessian of `uWeight ω C` along every complex line off `ℝᵈ`. -/
def LineHessianNonneg (ω : ℝᵈ → ℝ) (C : ℝ) : Prop :=
  ∀ z : ℂᵈ, imVec z ≠ 0 → ∀ vv : ℂᵈ,
    0 ≤ (iteratedFDeriv ℝ 2 (uWeight ω C) z) ![vv, vv]
      + (iteratedFDeriv ℝ 2 (uWeight ω C) z) ![Complex.I • vv, Complex.I • vv]

lemma continuous_uWeight {ω : ℝᵈ → ℝ} (hω : Continuous ω) (hc : HasCompactSupport ω)
    (C : ℝ) : Continuous (uWeight ω C) := by
  have h1 : Continuous (fun z : ℂᵈ => EomegaC ω z) := continuous_EomegaC hω hc
  have h2 : Continuous fun z : ℂᵈ => C * ‖imVec z‖ :=
    continuous_const.mul continuous_imVec.norm
  have hfun : (fun z : ℂᵈ => EomegaC ω z + C * ‖imVec z‖) = uWeight ω C := by
    funext z; rw [uWeight_apply]
  rw [← hfun]
  exact h1.add h2

lemma toCpx_reVec_of_imVec_eq_zero {z : ℂᵈ} (hz : imVec z = 0) : toCpx (reVec z) = z := by
  ext i
  have h : (z i).im = 0 := by
    have := congrArg (fun w : ℝᵈ => w i) hz
    simpa [imVec_apply] using this
  simp only [toCpx_apply, reVec_apply]
  exact Complex.ext (by simp) (by simp [h])

/-- `DirLocalSubMeanValue` for `uWeight ω C`, from the line-Hessian condition and the pointwise
bound. -/
theorem dirLocalSubMeanValue_uWeight {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 3 ω)
    (hc : HasCompactSupport ω) {C₁ C₂ C : ℝ} (hC : max C₁ C₂ < C)
    (hC₁ : 0 ≤ C₁) (hbound : ∀ x y : ℝᵈ, |Eomega ω x y - ω x| ≤ C₁ * ‖y‖)
    (hhess : LineHessianNonneg ω C) :
    DirLocalSubMeanValue (uWeight ω C) := by
  intro z v
  by_cases hz : imVec z = 0
  · obtain ⟨ε, hε, hε'⟩ := localSubMeanValue_realPoint (hω.of_le (by norm_num)) hc
      (lt_of_le_of_lt (le_max_left C₁ C₂) hC) hbound (reVec z)
    refine ⟨ε / (enorm v + 1), div_pos hε (by linarith [enorm_nonneg v]),
      fun ρ hρ hρlt => ?_⟩
    have hen : 0 < enorm v + 1 := by linarith [enorm_nonneg v]
    have hρen : ρ * enorm v < ε := by
      have h1 : ρ < ε / (enorm v + 1) := hρlt
      rw [lt_div_iff₀ hen] at h1
      nlinarith [enorm_nonneg v]
    have harg : enorm (ρ • v) < ε := by
      rw [enorm_real_smul, abs_of_pos hρ]
      exact hρen
    have hkey := hε' (ρ • v) harg
    have hzt : toCpx (reVec z) = z := toCpx_reVec_of_imVec_eq_zero hz
    rwa [hzt] at hkey
  · exact dirLocalSubMeanValue_off_real (hω.of_le (by norm_num)) hc C
      (fun z hz vv => hhess z hz vv) hz v


/-- **`prop:Ew_is_psh`** from the line-Hessian nonnegativity. -/
theorem exact_psh_extension_statement_of_hessian
    (hHess : ∀ (ω : ℝᵈ → ℝ) (C₂ C : ℝ), C₂ ≤ C →
      (∀ (x yhat vhat : ℝᵈ), ‖yhat‖ = 1 → ‖vhat‖ = 1 → inner ℝ yhat vhat = 0 →
        -C₂ ≤ (1 / π) * ∫ t : ℝ,
          ((iteratedFDeriv ℝ 2 ω (x + t • yhat)) (fun _ : Fin 2 => vhat))) →
      ContDiff ℝ 2 ω → HasCompactSupport ω → LineHessianNonneg ω C) :
    exact_psh_extension_statement (d := d) := by
  intro C₁ C₂ hC₁ hC₂ ω hω hc hnonpos hHilb hcond
  have hω2 : ContDiff ℝ 2 ω := hω.of_le (by norm_num)
  have hC₁C₀ : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hC₂C₀ : C₂ ≤ max C₁ C₂ := le_max_right _ _
  have hbound : ∀ x y : ℝᵈ, |Eomega ω x y - ω x| ≤ C₁ * ‖y‖ :=
    abs_Eomega_sub_le hω hc hHilb
  -- `u_C` is plurisubharmonic for every `C > max C₁ C₂`
  have hmain : ∀ C : ℝ, max C₁ C₂ < C → IsPSH (uWeight ω C) ∧ Continuous (uWeight ω C) := by
    intro C hC
    have hC1 : C₁ < C := lt_of_le_of_lt hC₁C₀ hC
    have hC2 : C₂ ≤ C := le_of_lt (lt_of_le_of_lt hC₂C₀ hC)
    have hloc := dirLocalSubMeanValue_uWeight hω hc hC hC₁ hbound
      (hHess ω C₂ C hC2 hcond hω2 hc)
    have hcon := continuous_uWeight hω.continuous hc C
    exact ⟨⟨hcon.upperSemicontinuous, subMeanValue_of_dirLocalSubMeanValue _ hcon hloc⟩, hcon⟩
  -- the limiting weight
  have hlim : ∀ K : Set ℂᵈ, IsCompact K →
      TendstoUniformlyOn (fun n : ℕ => uWeight ω (max C₁ C₂ + 1 / ((n : ℝ) + 1)))
        (uWeight ω (max C₁ C₂)) atTop K := by
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuous_imVec.continuousOn
    set R : ℝ := max R₀ 0 with hRdef
    have hR : ∀ z ∈ K, ‖imVec z‖ ≤ R := fun z hz => le_trans (hR₀ z hz) (le_max_left _ _)
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) * R) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul tendsto_const_nhds
    filter_upwards [(tendsto_order.1 h0).2 ε hε] with n hn z hz
    have hdiff : uWeight ω (max C₁ C₂ + 1 / ((n : ℝ) + 1)) z - uWeight ω (max C₁ C₂) z
        = (1 / ((n : ℝ) + 1)) * ‖imVec z‖ := by
      rw [uWeight_apply, uWeight_apply]; ring
    rw [dist_comm, dist_eq_norm, hdiff, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)), abs_of_nonneg (norm_nonneg _)]
    calc (1 / ((n : ℝ) + 1)) * ‖imVec z‖ ≤ (1 / ((n : ℝ) + 1)) * R :=
          mul_le_mul_of_nonneg_left (hR z hz) (by positivity)
      _ < ε := hn
  obtain ⟨-, hpsh_lim⟩ := IsPSH.of_tendstoUniformlyOn_compacts
    (u := fun n : ℕ => uWeight ω (max C₁ C₂ + 1 / ((n : ℝ) + 1)))
    (w := uWeight ω (max C₁ C₂))
    (fun n => (hmain _ (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)).1)
    (fun n => continuous_uWeight hω.continuous hc _) hlim
  refine ⟨max C₁ C₂, rfl, uWeight ω (max C₁ C₂), continuous_uWeight hω.continuous hc _,
    hpsh_lim, fun z => uWeight_apply ω _ z, ?_, ?_⟩
  · -- lower bound
    intro z
    rw [uWeight_toCpx, uWeight_apply, EomegaC]
    have hb := hbound (reVec z) (imVec z)
    have h1 : ω (reVec z) ≤ Eomega ω (reVec z) (imVec z) + C₁ * ‖imVec z‖ := by
      have := (abs_le.mp hb).1
      linarith
    have h2 : C₁ * ‖imVec z‖ ≤ max C₁ C₂ * ‖imVec z‖ :=
      mul_le_mul_of_nonneg_right hC₁C₀ (norm_nonneg _)
    linarith
  · -- upper bound
    intro z
    rw [uWeight_toCpx, uWeight_apply, EomegaC]
    have hb := hbound (reVec z) (imVec z)
    have h1 : Eomega ω (reVec z) (imVec z) ≤ ω (reVec z) + C₁ * ‖imVec z‖ := by
      have := (abs_le.mp hb).2
      linarith
    have h2 : C₁ * ‖imVec z‖ ≤ max C₁ C₂ * ‖imVec z‖ :=
      mul_le_mul_of_nonneg_right hC₁C₀ (norm_nonneg _)
    linarith


/-! ## Transport of the line-Hessian condition to `ℂᵈ` -/

lemma reVec_I_smul (w : ℂᵈ) : reVec (Complex.I • w) = -imVec w := by
  ext i
  simp [reVec_apply, imVec_apply, Complex.mul_I_re]

lemma imVec_I_smul (w : ℂᵈ) : imVec (Complex.I • w) = reVec w := by
  ext i
  simp [reVec_apply, imVec_apply, Complex.mul_I_im]

/-- The line-Hessian condition on `ℂᵈ` follows from its `(Re, Im)`-coordinate form. -/
theorem lineHessian_of_UWeight {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    {C : ℝ}
    (hcoord : ∀ (x y v₁ v₂ : ℝᵈ), y ≠ 0 →
      0 ≤ (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(v₁, v₂), (v₁, v₂)]
        + (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(-v₂, v₁), (-v₂, v₁)]) :
    LineHessianNonneg ω C := by
  intro z hz vv
  have hU : ContDiffOn ℝ 2 (UWeight ω C) {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} :=
    contDiffOn_two_UWeight hω hc C
  have h1 := iteratedFDeriv_comp_reImVec (U := UWeight ω C) hU hz vv vv
  have h2 := iteratedFDeriv_comp_reImVec (U := UWeight ω C) hU hz
    (Complex.I • vv) (Complex.I • vv)
  simp only [uWeight_eq_comp]
  rw [h1, h2, reVec_I_smul, imVec_I_smul]
  exact hcoord (reVec z) (imVec z) (reVec vv) (imVec vv) hz

end Submission.FUP