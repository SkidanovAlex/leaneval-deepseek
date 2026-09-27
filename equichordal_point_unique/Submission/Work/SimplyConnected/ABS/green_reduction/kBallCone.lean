
import Mathlib
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.SimplyConnected.ABS.region_with_sector_boundary
import Submission.Work.SimplyConnected.ABS.green_reduction.crossing

/-!
# A thin cone on which finitely many positive functionals dominate the norm

The finite-family version of exists_cone_of_two_positive: given a finite non-empty family of
real-linear functionals on the complex plane and a direction on which all of them are positive,
there is a thin cone on which all of them dominate a positive multiple of the norm.

The proof is the two-functional proof of green_reduction/crossing.lean, with the two constants
c1, c2, K1, K2 replaced by the finite family c i = N i v, K i = |N i (I * v)| and the parameters
Lambda = max 2 (max_i 4 (K i + 1) / c i), kappa = (min_i c i) / (4 * norm v).
-/

namespace Work.SimplyConnected.ABS.green_reduction

open scoped _root_.Topology Manifold ContDiff ComplexConjugate
open Set Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

set_option maxHeartbeats 4000000 in
/-- **A thin cone on which finitely many positive functionals dominate the norm.**  If 
for every  in a finite non-empty type, then there are non-zero functionals  with a
non-empty common positive sector and a constant  with  for every  and
every  of that sector. -/
theorem exists_cone_of_finite_positive {ι : Type*} [Fintype ι] [Nonempty ι]
    {N : ι → ℂ →L[ℝ] ℝ} {v : ℂ} (h : ∀ i, 0 < N i v) :
    ∃ (L₁ L₂ : ℂ →L[ℝ] ℝ) (κ : ℝ), L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ 0 < κ ∧
      (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ i, ∀ u : ℂ, 0 < L₁ u → 0 < L₂ u → κ * ‖u‖ ≤ N i u := by
  classical
  have hvne : v ≠ 0 := by
    intro hv
    have h0 := h (Classical.arbitrary ι)
    rw [hv, map_zero] at h0
    exact lt_irrefl 0 h0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hWpos : 0 < ‖v‖ ^ 2 := pow_pos hvpos 2
  have hWne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hWpos
  set c : ι → ℝ := fun i => N i v with hcdef
  have hceq : ∀ i, c i = N i v := fun i => rfl
  have hcpos : ∀ i, 0 < c i := fun i => h i
  set K : ι → ℝ := fun i => |N i (Complex.I * v)| with hKdef
  have hKeq : ∀ i, K i = |N i (Complex.I * v)| := fun i => rfl
  have hKnn : ∀ i, 0 ≤ K i := fun i => abs_nonneg _
  set Λ : ℝ := max 2 (Finset.univ.sup' Finset.univ_nonempty (fun i => 4 * (K i + 1) / c i))
    with hΛdef
  have hΛ2 : 2 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by norm_num) hΛ2
  have hΛA : ∀ i, 4 * (K i + 1) / c i ≤ Λ := fun i =>
    le_trans (Finset.le_sup' (fun i => 4 * (K i + 1) / c i) (Finset.mem_univ i))
      (le_max_right _ _)
  have hε : ∀ i, 1 / Λ ≤ c i / (4 * (K i + 1)) := by
    intro i
    rw [div_le_div_iff₀ hΛpos (by positivity)]
    have h3 := mul_le_mul_of_nonneg_right (hΛA i) (le_of_lt (hcpos i))
    rw [div_mul_cancel₀ _ (ne_of_gt (hcpos i))] at h3
    linarith [h3]
  have hKΛ : ∀ i, K i / Λ ≤ c i / 4 := by
    intro i
    have h1 := mul_le_mul_of_nonneg_left (hε i) (hKnn i)
    have h2 : K i * (1 / Λ) = K i / Λ := by ring
    have h3 : K i * (c i / (4 * (K i + 1))) ≤ c i / 4 := by
      rw [show K i * (c i / (4 * (K i + 1))) = c i * K i / (4 * (K i + 1)) by ring]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [(hcpos i).le, hKnn i]
    linarith [h1, h2.le, h2.ge, h3]
  set cinf : ℝ := Finset.univ.inf' Finset.univ_nonempty c with hcinfdef
  have hcinfpos : 0 < cinf :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hcpos i)
  have hcinfle : ∀ i, cinf ≤ c i := fun i => Finset.inf'_le c (Finset.mem_univ i)
  have hL₁v : (reConjCLM v + Λ • reConjCLM (Complex.I * v)) v = ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, reConj_Iv_v,
      mul_zero, add_zero]
    exact reConjCLM_mul_self_re v
  have hL₂v : (reConjCLM v - Λ • reConjCLM (Complex.I * v)) v = ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, reConj_Iv_v,
      mul_zero, sub_zero]
    exact reConjCLM_mul_self_re v
  refine ⟨reConjCLM v + Λ • reConjCLM (Complex.I * v),
    reConjCLM v - Λ • reConjCLM (Complex.I * v), cinf / (4 * ‖v‖), ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at hL₁v
    simp only [ContinuousLinearMap.zero_apply] at hL₁v
    linarith [hWpos, hL₁v]
  · intro h0
    rw [h0] at hL₂v
    simp only [ContinuousLinearMap.zero_apply] at hL₂v
    linarith [hWpos, hL₂v]
  · exact div_pos hcinfpos (by positivity)
  · exact ⟨v, by rw [hL₁v]; exact hWpos, by rw [hL₂v]; exact hWpos⟩
  · intro i u hL₁u hL₂u
    let s : ℝ := reConjCLM v u / ‖v‖ ^ 2
    let t : ℝ := reConjCLM (Complex.I * v) u / ‖v‖ ^ 2
    have hsval : s = reConjCLM v u / ‖v‖ ^ 2 := rfl
    have htval : t = reConjCLM (Complex.I * v) u / ‖v‖ ^ 2 := rfl
    have hsW : s * ‖v‖ ^ 2 = reConjCLM v u := by rw [hsval]; field_simp
    have htW : t * ‖v‖ ^ 2 = reConjCLM (Complex.I * v) u := by rw [htval]; field_simp
    have hL₁eval : (reConjCLM v + Λ • reConjCLM (Complex.I * v)) u
        = reConjCLM v u + Λ * reConjCLM (Complex.I * v) u := by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hL₂eval : (reConjCLM v - Λ • reConjCLM (Complex.I * v)) u
        = reConjCLM v u - Λ * reConjCLM (Complex.I * v) u := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hcone₁ : 0 < s + Λ * t := by
      have hh := hL₁u
      rw [hL₁eval, ← hsW, ← htW] at hh
      nlinarith [hh, hWpos]
    have hcone₂ : 0 < s - Λ * t := by
      have hh := hL₂u
      rw [hL₂eval, ← hsW, ← htW] at hh
      nlinarith [hh, hWpos]
    have hspos : 0 < s := by linarith [hcone₁, hcone₂]
    have hΛne : Λ ≠ 0 := ne_of_gt hΛpos
    have hΛt : Λ * |t| ≤ s := by
      rw [← abs_of_pos hΛpos, ← abs_mul]
      exact abs_le.mpr ⟨by linarith [hcone₁], by linarith [hcone₂]⟩
    have h2t : 2 * |t| ≤ s := by nlinarith [hΛt, hΛ2, abs_nonneg t]
    have hsq : s ^ 2 + t ^ 2 ≤ (2 * s) ^ 2 := by
      nlinarith [h2t, abs_nonneg t, hspos, sq_abs t]
    have htK : |t| * K i ≤ s * (c i / 4) := by
      have h1 : |t| * K i = (Λ * |t|) * (K i / Λ) := by field_simp
      rw [h1]
      exact mul_le_mul hΛt (hKΛ i) (by positivity) (le_of_lt hspos)
    have hdecomp : u = s • v + t • (Complex.I * v) := by
      have key := congrArg (fun z : ℂ => (‖v‖ ^ 2)⁻¹ • z) (smul_decomp v u)
      simp only [smul_smul, inv_mul_cancel₀ hWne, one_smul] at key
      rw [smul_add, smul_smul, smul_smul,
        show (‖v‖ ^ 2)⁻¹ * reConjCLM v u = s from by rw [hsval]; field_simp,
        show (‖v‖ ^ 2)⁻¹ * reConjCLM (Complex.I * v) u = t from by rw [htval]; field_simp]
        at key
      exact key
    have hnorm2 : ‖u‖ ^ 2 = (s ^ 2 + t ^ 2) * ‖v‖ ^ 2 := by
      have hinner1 : inner ℝ (s • v) (t • (Complex.I * v)) = 0 := by
        rw [real_inner_smul_left, real_inner_smul_right, inner_eq_reConj, reConj_v_Iv]
        ring
      have hnorm1 : ‖s • v‖ ^ 2 = s ^ 2 * ‖v‖ ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have hnorm2prime : ‖t • (Complex.I * v)‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_mul, Complex.norm_I,
          one_mul]
      rw [hdecomp, norm_add_sq_real, hnorm1, hnorm2prime, hinner1]
      ring
    have hu_le : ‖u‖ ≤ 2 * s * ‖v‖ := by
      have h4 : ‖u‖ ^ 2 ≤ (2 * s * ‖v‖) ^ 2 := by
        rw [hnorm2]
        nlinarith [hsq, hWpos, sq_nonneg (2 * s * ‖v‖), sq_nonneg s]
      have h5 : 0 ≤ 2 * s * ‖v‖ := by positivity
      nlinarith [h4, h5, norm_nonneg u]
    have hNu : N i u = s * c i + t * N i (Complex.I * v) := by
      rw [hdecomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hceq i]
    have hstep : s * c i / 2 ≤ N i u := by
      have h1 : -(|t| * K i) ≤ t * N i (Complex.I * v) := by
        have h2 : |t * N i (Complex.I * v)| = |t| * K i := by rw [abs_mul, hKeq i]
        linarith [neg_abs_le (t * N i (Complex.I * v)), h2.le, h2.ge]
      have h4 : -(s * (c i / 4)) ≤ t * N i (Complex.I * v) := by linarith [h1, htK]
      have h5 : s * c i - s * (c i / 4) ≤ N i u := by linarith [hNu, h4]
      have h6 : s * c i - s * (c i / 4) = s * c i * (3 / 4) := by ring
      have h7 : 0 < s * c i := mul_pos hspos (hcpos i)
      linarith [h5, h6.le, h6.ge, h7]
    have h7 : c i * ‖u‖ / (4 * ‖v‖) ≤ N i u := by
      have h8 : c i * ‖u‖ / (4 * ‖v‖) ≤ s * c i / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : c i * ‖u‖ ≤ c i * (2 * s * ‖v‖) := mul_le_mul_of_nonneg_left hu_le (hcpos i).le
        have h2 : c i * (2 * s * ‖v‖) = s * c i / 2 * (4 * ‖v‖) := by ring
        linarith [h1, h2.le, h2.ge]
      linarith [h8, hstep]
    have h9 : cinf / (4 * ‖v‖) ≤ c i / (4 * ‖v‖) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hh := mul_le_mul_of_nonneg_right (hcinfle i) (by positivity : (0 : ℝ) ≤ 4 * ‖v‖)
      linarith [hh]
    have h10 : cinf / (4 * ‖v‖) * ‖u‖ ≤ c i / (4 * ‖v‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right h9 (norm_nonneg u)
    have h11 : c i / (4 * ‖v‖) * ‖u‖ = c i * ‖u‖ / (4 * ‖v‖) := by ring
    linarith [h10, h11.le, h11.ge, h7]

end Work.SimplyConnected.ABS.green_reduction
