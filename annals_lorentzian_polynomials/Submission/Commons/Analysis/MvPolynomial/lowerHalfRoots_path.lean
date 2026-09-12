import Mathlib
import Submission.Commons.Analysis.MvPolynomial.realRooted_limit_closed

/-!
# Lower-half-root path lemma

If a continuous family of complex polynomials `P : ℝ → ℂ[X]` has constant degree `d`,
no real roots for `w ∈ [0,1]`, and all roots of `P 0` lie in the open upper half plane,
then all roots of `P 1` lie in the open upper half plane.

Strategy: let `W = {w | P w has a root in the open lower half plane}`.  We show `W ∩ [0,1]`
is closed (a convergent sequence of parameters with lower roots clusters to a lower root of
the limit, using boundedness of roots near a point + Bolzano--Weierstrass) and open in
`[0,1]` (an isolated root of the limit persists to nearby parameters, by the maximum
modulus / `rrl_root_in_closedBall` lemma from `realRooted_limit_closed`).  Then the infimum
of `W ∩ [0,1]` is a minimum, contradicting openness at that point, provided `0 ∉ W` and
`1 ∈ W`.
-/

noncomputable section

open Polynomial Filter Metric Complex
open scoped Topology BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Analysis.MvPolynomial

namespace LHR

-- ============================================================
-- 1. basic polynomial / evaluation facts
-- ============================================================

/-- Evaluation expressed with coefficients up to degree `d` (polynomial has degree `d`). -/
lemma eval_eq_sum_range {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d) (w : ℝ) (z : ℂ) :
    (P w).eval z = ∑ i ∈ Finset.range (d + 1), (P w).coeff i * z ^ i := by
  exact Polynomial.eval_eq_sum_range' (by rw [hdeg]; omega) z

/-- Evaluation expressed with coefficients indexed by `Fin (d + 1)`. -/
lemma eval_eq_sum {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d) (w : ℝ) (z : ℂ) :
    (P w).eval z = ∑ i : Fin (d + 1), (P w).coeff (i : ℕ) * z ^ (i : ℕ) := by
  rw [eval_eq_sum_range hdeg]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < d + 1 := by simpa using (Finset.mem_range.mp hi)
  simp [hi']

/-- A polynomial with positive degree is nonzero. -/
lemma ne_zero_of_natDegree_pos {d : ℕ} (hd : 0 < d) {p : Polynomial ℂ} (hp : p.natDegree = d) :
    p ≠ 0 := by
  intro hp0
  have : (0 : Polynomial ℂ).natDegree = d := by simpa [hp0] using hp
  simp at this
  omega

/-- The leading (degree `d`) coefficient is nonzero at every parameter value. -/
lemma coeff_d_ne_zero {d : ℕ} (hd : 0 < d) {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d) (w : ℝ) :
    (P w).coeff d ≠ 0 := by
  have hp0 : P w ≠ 0 := ne_zero_of_natDegree_pos hd (hdeg w)
  have hlc : (P w).leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_ne_zero]
    exact hp0
  simpa [Polynomial.leadingCoeff, hdeg w] using hlc

/-- Roots of `P w` for `w ∈ [0,1]` are never real. -/
lemma root_im_ne_zero_of_mem_Icc {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hnoReal : ∀ w : ℝ, w ∈ Set.Icc 0 1 → ∀ t : ℝ, Polynomial.eval (t : ℂ) (P w) ≠ 0)
    {w : ℝ} (hw : w ∈ Set.Icc 0 1) {z : ℂ} (hz : (P w).eval z = 0) :
    z.im ≠ 0 := by
  intro him0
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him0]
  have hzroot : (P w).eval (z.re : ℂ) = 0 := by
    rw [← hzreal]
    exact hz
  exact hnoReal w hw z.re hzroot

/-- The evaluation map `(w, z) ↦ eval z (P w)` is jointly continuous. -/
lemma eval_continuous {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hcont : ∀ j : ℕ, Continuous fun w : ℝ => (P w).coeff j)
    (hdeg : ∀ w : ℝ, (P w).natDegree = d) :
    Continuous (fun wz : ℝ × ℂ => (P wz.1).eval wz.2) := by
  have hfun : (fun wz : ℝ × ℂ => (P wz.1).eval wz.2) =
      (fun wz : ℝ × ℂ => ∑ i : Fin (d + 1), (P wz.1).coeff (i : ℕ) * wz.2 ^ (i : ℕ)) := by
    funext wz
    exact eval_eq_sum hdeg wz.1 wz.2
  rw [hfun]
  apply continuous_finsetSum
  intro i hi
  exact ((hcont (i : ℕ)).comp continuous_fst).mul (continuous_snd.pow (i : ℕ))


/-- Difference of evaluations, expanded by degree-`d` coefficients. -/
lemma eval_sub_eq_sum {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d) (w0 w : ℝ) (z : ℂ) :
    (P w).eval z - (P w0).eval z =
      ∑ i : Fin (d + 1), ((P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)) * z ^ (i : ℕ) := by
  classical
  rw [eval_eq_sum hdeg w z, eval_eq_sum hdeg w0 z]
  rw [show (fun i : Fin (d + 1) =>
      ((P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)) * z ^ (i : ℕ)) =
      (fun i : Fin (d + 1) =>
        (P w).coeff (i : ℕ) * z ^ (i : ℕ) - (P w0).coeff (i : ℕ) * z ^ (i : ℕ)) by
    funext i
    ring]
  exact (Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin (d + 1))))
    (f := fun i : Fin (d + 1) => (P w).coeff (i : ℕ) * z ^ (i : ℕ))
    (g := fun i : Fin (d + 1) => (P w0).coeff (i : ℕ) * z ^ (i : ℕ))).symm

/-- If `P` has degree `d` with continuous coefficients, then `eval z (P w)` is
uniformly close to `eval z (P w0)` for `z` in a bounded set and `w` close to `w0`. -/
lemma uniform_eval_close {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hcont : ∀ j : ℕ, Continuous fun w : ℝ => (P w).coeff j)
    (hdeg : ∀ w : ℝ, (P w).natDegree = d)
    (s : Set ℂ) {B : ℝ} (hB : ∀ z : ℂ, z ∈ s → ‖z‖ ≤ B)
    (w0 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ w : ℝ, |w - w0| < η → ∀ z : ℂ, z ∈ s →
      ‖(P w).eval z - (P w0).eval z‖ < ε := by
  classical
  let M : ℝ := max B 1
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_right B 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hMdpos : 0 < M ^ d := pow_pos hMpos d
  let f : ℝ → ℝ := fun w => ∑ i : Fin (d + 1),
    ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖
  have hf_cont : Continuous f := by
    dsimp [f]
    apply continuous_finsetSum
    intro i hi
    exact (((hcont (i : ℕ)).sub
      (continuous_const : Continuous fun _ : ℝ => (P w0).coeff (i : ℕ))).norm)
  have hf0 : f w0 = 0 := by
    dsimp [f]
    simp
  have hlim0 : Tendsto f (𝓝 w0) (𝓝 (0 : ℝ)) := by
    simpa [hf0] using hf_cont.tendsto w0
  have hnh : ∀ᶠ w in 𝓝 w0, dist (f w) (0 : ℝ) < ε / M ^ d := by
    exact Metric.tendsto_nhds.mp hlim0 (ε / M ^ d) (div_pos hε hMdpos)
  rcases Metric.mem_nhds_iff.mp hnh with ⟨η, hη0, hηball⟩
  refine ⟨η, hη0, ?_⟩
  intro w hw z hz
  have hfw : f w < ε / M ^ d := by
    have hd : dist (f w) (0 : ℝ) < ε / M ^ d :=
      hηball (by simpa [Real.dist_eq, Metric.mem_ball] using hw)
    have hnonneg : 0 ≤ f w := by
      dsimp [f]
      exact Finset.sum_nonneg (by intro i hi; exact norm_nonneg _)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hd
  have hzM : ‖z‖ ≤ M := by
    exact le_trans (hB z hz) (by dsimp [M]; exact le_max_left B 1)
  have hzpow : ∀ i : ℕ, i ≤ d → ‖z‖ ^ i ≤ M ^ d := by
    intro i hi
    calc
      ‖z‖ ^ i ≤ M ^ i := by
        exact pow_le_pow_left₀ (norm_nonneg z) hzM i
      _ ≤ M ^ d := pow_le_pow_right₀ hM1 hi
  have hsub : ∀ i : Fin (d + 1),
      ‖((P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)) * z ^ (i : ℕ)‖ ≤
        ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖ * M ^ d := by
    intro i
    calc
      ‖((P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)) * z ^ (i : ℕ)‖
          = ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖ * ‖z ^ (i : ℕ)‖ := by
              simp
      _ = ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖ * ‖z‖ ^ (i : ℕ) := by
              simp [norm_pow]
      _ ≤ ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖ * M ^ d := by
              exact mul_le_mul_of_nonneg_left (hzpow (i : ℕ) (by omega))
                (norm_nonneg _)
  have hdiff : ‖(P w).eval z - (P w0).eval z‖ ≤ f w * M ^ d := by
    calc
      ‖(P w).eval z - (P w0).eval z‖
          ≤ ∑ i : Fin (d + 1),
              ‖((P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)) * z ^ (i : ℕ)‖ := by
              rw [eval_sub_eq_sum hdeg w0 w z]
              simpa using (norm_sum_le (Finset.univ : Finset (Fin (d + 1)))
                (fun i : Fin (d + 1) =>
                  ((P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)) * z ^ (i : ℕ)))
      _ ≤ ∑ i : Fin (d + 1),
              ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖ * M ^ d := by
              exact Finset.sum_le_sum (by intro i hi; exact hsub i)
      _ = (∑ i : Fin (d + 1),
              ‖(P w).coeff (i : ℕ) - (P w0).coeff (i : ℕ)‖) * M ^ d := by
              rw [Finset.sum_mul]
      _ = f w * M ^ d := by rfl
  exact lt_of_le_of_lt hdiff ((lt_div_iff₀ hMdpos).mp hfw)


/-- A crude Cauchy bound for roots, in terms of coefficient bounds. -/
lemma norm_root_le {d : ℕ} (hd : 0 < d) {p : Polynomial ℂ} {C c : ℝ}
    (hpdeg : p.natDegree = d) (hC : 0 ≤ C) (hc : 0 < c)
    (hcoeff : ∀ i : ℕ, i < d → ‖p.coeff i‖ ≤ C)
    (hlead : c ≤ ‖p.coeff d‖) :
    ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1 + C * d / c := by
  classical
  intro z hz
  have hc0 : 0 ≤ C * (d : ℝ) / c := by
    exact div_nonneg (mul_nonneg hC (Nat.cast_nonneg d)) (le_of_lt hc)
  by_cases hzle : ‖z‖ ≤ 1
  · linarith
  · have hzgt1 : 1 < ‖z‖ := lt_of_not_ge hzle
    have hzpos : 0 < ‖z‖ := lt_trans zero_lt_one hzgt1
    have hsplit := Finset.sum_range_succ (fun i : ℕ => p.coeff i * z ^ i) d
    have hsum0 : (∑ i ∈ Finset.range d, p.coeff i * z ^ i) + p.coeff d * z ^ d = 0 := by
      have heval := Polynomial.eval_eq_sum_range' (p := p) (n := d + 1) (by rw [hpdeg]; omega) z
      rw [← hsplit, ← heval]
      exact hz
    have hneg : p.coeff d * z ^ d = - (∑ i ∈ Finset.range d, p.coeff i * z ^ i) := by
      exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at hsum0)
    have hmain1 : ‖p.coeff d‖ * ‖z‖ ^ d = ‖∑ i ∈ Finset.range d, p.coeff i * z ^ i‖ := by
      calc
        ‖p.coeff d‖ * ‖z‖ ^ d = ‖p.coeff d * z ^ d‖ := by simp [norm_pow]
        _ = ‖∑ i ∈ Finset.range d, p.coeff i * z ^ i‖ := by rw [hneg]; simp
    have hsum_bound : ‖∑ i ∈ Finset.range d, p.coeff i * z ^ i‖ ≤
        C * (∑ i ∈ Finset.range d, ‖z‖ ^ i) := by
      calc
        ‖∑ i ∈ Finset.range d, p.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range d, ‖p.coeff i * z ^ i‖ := by
                exact norm_sum_le (Finset.range d) (fun i : ℕ => p.coeff i * z ^ i)
        _ ≤ ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖z‖ ^ i := by
                exact Finset.sum_le_sum (by
                  intro i hi
                  simp [norm_pow])
        _ ≤ ∑ i ∈ Finset.range d, C * ‖z‖ ^ i := by
                exact Finset.sum_le_sum (by
                  intro i hi
                  exact mul_le_mul_of_nonneg_right (hcoeff i (Finset.mem_range.mp hi))
                    (pow_nonneg (norm_nonneg z) i))
        _ = C * (∑ i ∈ Finset.range d, ‖z‖ ^ i) := by
                rw [Finset.mul_sum]
    have hineqA : ‖p.coeff d‖ * ‖z‖ ^ d * ‖z‖ ≤ C * (∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖ := by
      exact mul_le_mul_of_nonneg_right (le_trans hmain1.le hsum_bound) (norm_nonneg z)
    have hineqB : C * (∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖ ≤ C * d * ‖z‖ ^ d := by
      have hsum_le : (∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖ ≤ d * ‖z‖ ^ d := by
        calc
          (∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖
              = ∑ i ∈ Finset.range d, (‖z‖ ^ i * ‖z‖) := by rw [Finset.sum_mul]
          _ = ∑ i ∈ Finset.range d, ‖z‖ ^ (i + 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [pow_succ]
          _ ≤ ∑ i ∈ Finset.range d, ‖z‖ ^ d := by
              exact Finset.sum_le_sum (by
                intro i hi
                exact pow_le_pow_right₀ (le_of_lt hzgt1) (by
                  have hi' : i < d := Finset.mem_range.mp hi
                  omega))
          _ = d * ‖z‖ ^ d := by
              rw [Finset.sum_const, Finset.card_range]
              simp
      calc
        C * (∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖
            = C * ((∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖) := by ring
        _ ≤ C * (d * ‖z‖ ^ d) := by exact mul_le_mul_of_nonneg_left hsum_le hC
        _ = C * d * ‖z‖ ^ d := by ring
    have hineq0 : ‖p.coeff d‖ * ‖z‖ ^ (d + 1) ≤ C * d * ‖z‖ ^ d := by
      calc
        ‖p.coeff d‖ * ‖z‖ ^ (d + 1) = ‖p.coeff d‖ * ‖z‖ ^ d * ‖z‖ := by rw [pow_succ]; ring
        _ ≤ C * (∑ i ∈ Finset.range d, ‖z‖ ^ i) * ‖z‖ := hineqA
        _ ≤ C * d * ‖z‖ ^ d := hineqB
    have hLHS : c * ‖z‖ ^ (d + 1) ≤ ‖p.coeff d‖ * ‖z‖ ^ (d + 1) := by
      exact mul_le_mul_of_nonneg_right hlead (pow_nonneg (norm_nonneg z) (d + 1))
    have hineqC : c * ‖z‖ ^ (d + 1) ≤ C * d * ‖z‖ ^ d := le_trans hLHS hineq0
    have hzpowpos : 0 < ‖z‖ ^ d := pow_pos hzpos d
    have hineqD : c * ‖z‖ ≤ C * d := by
      have hstep : c * (‖z‖ ^ d * ‖z‖) ≤ C * d * ‖z‖ ^ d := by
        have hrew : ‖z‖ ^ (d + 1) = ‖z‖ ^ d * ‖z‖ := by rw [pow_succ]
        rwa [hrew] at hineqC
      -- c * (‖z‖^d * ‖z‖) = (c*‖z‖) * ‖z‖^d;  (C*d) * ‖z‖^d
      have hstep' : (c * ‖z‖) * ‖z‖ ^ d ≤ (C * d) * ‖z‖ ^ d := by
        convert hstep using 1; ring
      exact (mul_le_mul_iff_of_pos_right hzpowpos).mp hstep'
    have hineqE : ‖z‖ ≤ C * d / c := by
      have hstep'' : ‖z‖ * c ≤ C * d := by
        simpa [mul_comm] using hineqD
      exact (le_div_iff₀ hc).mpr hstep''
    have hdiv : C * d / c ≤ 1 + C * d / c := by linarith
    exact le_trans hineqE hdiv


/-- Around a root in the open lower half plane there is a circle free of other roots,
inside the lower half plane. -/
lemma exists_radius_rootfree_lower (p : Polynomial ℂ) (hp : p ≠ 0) (r : ℂ) (hrIm : r.im < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < -r.im ∧ ∀ z : ℂ, z ∈ sphere r ρ → p.eval z ≠ 0 := by
  classical
  let S : Set ℂ := {z | IsRoot p z}
  have hSfin : S.Finite := p.finite_setOfPred_isRoot hp
  let T : Finset ℂ := (hSfin.sdiff (t := ({r} : Set ℂ))).toFinset
  let s : Finset ℝ := T.image (fun w => ‖w - r‖)
  have hs_pos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    have hwS : w ∈ S \ {r} := by
      simpa [T, Set.Finite.mem_toFinset] using hw
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hwS.2)
  have hpos : 0 < -r.im := by linarith
  rcases rrl_exists_pos_lt_of_finite_ne_zero hpos s hs_pos with ⟨ρ, hρ0, hρc, hρavoid⟩
  refine ⟨ρ, hρ0, hρc, ?_⟩
  intro z hz hz0
  have hzIs : IsRoot p z := IsRoot.def.mpr hz0
  have hzS : z ∈ S := by
    dsimp [S]
    exact hzIs
  by_cases hzr : z = r
  · subst z
    have hzsp : ‖r - r‖ = ρ := by
      simpa using hz
    have : (0 : ℝ) = ρ := by simpa using hzsp
    linarith
  · have hzmem : z ∈ (S \ {r}) := ⟨hzS, hzr⟩
    have hzfin : z ∈ T := by
      simpa [T, Set.Finite.mem_toFinset] using hzmem
    have htmp : ‖z - r‖ ∈ s := Finset.mem_image.mpr ⟨z, hzfin, rfl⟩
    have hne : ‖z - r‖ ≠ ρ := hρavoid ‖z - r‖ htmp
    have hzsp : ‖z - r‖ = ρ := by
      simpa using hz
    exact hne hzsp

/-- An isolated root of `P w0` in the open lower half plane persists for nearby `w`. -/
lemma root_persist_lower {d : ℕ} {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d) (hd : 0 < d)
    (hcont : ∀ j : ℕ, Continuous fun w : ℝ => (P w).coeff j)
    (w0 : ℝ) {r : ℂ} (hr : (P w0).eval r = 0) (hrIm : r.im < 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ w : ℝ, |w - w0| < η →
      ∃ z : ℂ, (P w).eval z = 0 ∧ z.im < 0 := by
  classical
  have hp0 : P w0 ≠ 0 := ne_zero_of_natDegree_pos hd (hdeg w0)
  rcases exists_radius_rootfree_lower (P w0) hp0 r hrIm with ⟨ρ, hρ0, hρlt, hρsphere⟩
  rcases rrl_exists_pos_lower_bound_on_sphere (P w0) (r := r) (ρ := ρ) hρ0 hρsphere with ⟨δ, hδ0, hδsphere⟩
  have hB : ∀ z : ℂ, z ∈ closedBall r ρ → ‖z‖ ≤ ‖r‖ + ρ := by
    intro z hz
    have hzr : ‖z - r‖ ≤ ρ := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
    calc
      ‖z‖ = ‖(z - r) + r‖ := by congr 1; abel
      _ ≤ ‖z - r‖ + ‖r‖ := norm_add_le _ _
      _ ≤ ρ + ‖r‖ := by linarith
      _ = ‖r‖ + ρ := by linarith
  rcases uniform_eval_close hcont hdeg (closedBall r ρ) hB w0 (ε := δ / 2) (by positivity)
    with ⟨ηu, hηu0, hηu⟩
  refine ⟨ηu, hηu0, ?_⟩
  intro w hw
  have hclose : ∀ z : ℂ, z ∈ closedBall r ρ → ‖(P w).eval z - (P w0).eval z‖ < δ / 2 :=
    hηu w hw
  have hcl_sphere : ∀ z : ℂ, z ∈ sphere r ρ →
      ‖(P w).eval z - (P w0).eval z‖ < δ / 2 := by
    intro z hz
    exact hclose z (Metric.sphere_subset_closedBall hz)
  have hsmall : ‖(P w).eval r‖ < δ / 2 := by
    have hrcl : r ∈ closedBall r ρ := by
      exact Metric.mem_closedBall.mpr (by simp [hρ0.le])
    have hc := hclose r hrcl
    simpa [hr] using hc
  rcases rrl_root_in_closedBall (p := P w) (q := P w0) (r := r) (ρ := ρ) (δ := δ)
    hρ0 hδ0 hr hcl_sphere hsmall hδsphere with ⟨z, hzball, hzroot⟩
  refine ⟨z, hzroot, ?_⟩
  have himb : |z.im - r.im| ≤ ‖z - r‖ := by
    simpa [Complex.sub_im] using (abs_im_le_norm (z - r))
  have him1 : z.im ≤ r.im + ρ := by
    have hsub : z.im - r.im ≤ ρ := by
      exact le_trans (le_trans (le_abs_self (z.im - r.im)) himb) hzball
    linarith
  have him2 : r.im + ρ < 0 := by linarith
  exact lt_of_le_of_lt him1 him2


/-- Continuity in the metric sense: a continuous function is close to its value. -/
lemma metric_near {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    (w0 : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ w : ℝ, |w - w0| < η → ‖f w - f w0‖ < ε := by
  have hnh : ∀ᶠ w in 𝓝 w0, dist (f w) (f w0) < ε := by
    exact Metric.tendsto_nhds.mp (hf.continuousAt.tendsto) ε hε
  rcases Metric.mem_nhds_iff.mp hnh with ⟨η, hη0, hηb⟩
  refine ⟨η, hη0, ?_⟩
  intro w hw
  have hb := hηb (by simpa [Metric.mem_ball, Real.dist_eq] using hw)
  simpa [dist_eq_norm] using hb

/-- Roots of `P w` are uniformly bounded for `w` in a small neighborhood of `w0`
(where the degree-`d` coefficient stays away from zero). -/
lemma roots_bounded_near {d : ℕ} (hd : 0 < d) {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d)
    (hcont : ∀ j : ℕ, Continuous fun w : ℝ => (P w).coeff j)
    (w0 : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ w : ℝ, |w - w0| < η → ∀ z : ℂ,
      (P w).eval z = 0 → ‖z‖ ≤ R := by
  classical
  have hlead0 : (P w0).coeff d ≠ 0 := coeff_d_ne_zero hd hdeg w0
  have hg0pos : 0 < ‖(P w0).coeff d‖ := norm_pos_iff.mpr hlead0
  let c : ℝ := ‖(P w0).coeff d‖ / 2
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos hg0pos zero_lt_two
  rcases metric_near (hcont d) w0 c hcpos with ⟨η1, hη10, hη1⟩
  have hlead_lower : ∀ w : ℝ, |w - w0| < η1 → c ≤ ‖(P w).coeff d‖ := by
    intro w hw
    have hsmall := hη1 w hw
    have hsmall' : ‖(P w0).coeff d - (P w).coeff d‖ < c := by
      simpa [norm_sub_rev] using hsmall
    have htri : ‖(P w0).coeff d‖ ≤ ‖(P w0).coeff d - (P w).coeff d‖ + ‖(P w).coeff d‖ := by
      simpa [sub_add_cancel] using
        (norm_add_le ((P w0).coeff d - (P w).coeff d) ((P w).coeff d))
    have hgt : c < ‖(P w).coeff d‖ := by
      dsimp [c] at hsmall' ⊢
      linarith
    exact le_of_lt hgt
  let g : ℝ → ℝ := fun w => ∑ i : Fin (d + 1), ‖(P w).coeff (i : ℕ)‖
  have hg_cont : Continuous g := by
    dsimp [g]
    apply continuous_finsetSum
    intro i hi
    exact (hcont (i : ℕ)).norm
  have hg0nn : 0 ≤ g w0 := by
    dsimp [g]
    exact Finset.sum_nonneg (by intro i hi; exact norm_nonneg _)
  let C : ℝ := g w0 + 1
  have hC0 : 0 ≤ C := by
    dsimp [C]
    linarith
  rcases metric_near hg_cont w0 1 (by norm_num) with ⟨η2, hη20, hη2⟩
  have hcoeff_bound : ∀ w : ℝ, |w - w0| < η2 → ∀ i : Fin (d + 1),
      ‖(P w).coeff (i : ℕ)‖ ≤ C := by
    intro w hw i
    have hsmall := hη2 w hw
    have hlt : g w < C := by
      have hle_abs : g w - g w0 ≤ |g w - g w0| := le_abs_self (g w - g w0)
      have hnorm : |g w - g w0| = ‖g w - g w0‖ := by rfl
      dsimp [C]
      linarith
    have hle_sum : ‖(P w).coeff (i : ℕ)‖ ≤ g w := by
      change ‖(P w).coeff (i : ℕ)‖ ≤ (∑ j : Fin (d + 1), ‖(P w).coeff (j : ℕ)‖)
      exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin (d + 1))))
        (f := fun j : Fin (d + 1) => ‖(P w).coeff (j : ℕ)‖)
        (fun j hj => norm_nonneg ((P w).coeff (j : ℕ))) (Finset.mem_univ i)
    exact le_trans hle_sum (le_of_lt hlt)
  let η : ℝ := min η1 η2
  have hη0 : 0 < η := lt_min hη10 hη20
  refine ⟨η, hη0, 1 + C * d / c, ?_⟩
  intro w hw z hzroot
  have hwmin : |w - w0| < min η1 η2 := by simpa [η] using hw
  have hw1 : |w - w0| < η1 := lt_of_lt_of_le hwmin (min_le_left η1 η2)
  have hw2 : |w - w0| < η2 := lt_of_lt_of_le hwmin (min_le_right η1 η2)
  have hlead_w : c ≤ ‖(P w).coeff d‖ := hlead_lower w hw1
  have hcoeff_lt : ∀ i : ℕ, i < d → ‖(P w).coeff i‖ ≤ C := by
    intro i hi
    exact hcoeff_bound w hw2 ⟨i, by omega⟩
  exact norm_root_le (d := d) hd (p := P w) (hpdeg := hdeg w) hC0 hcpos hcoeff_lt hlead_w z hzroot

/-- A cluster point (in the parameter) of lower-half-plane roots is a lower root of
the limit polynomial: `W ∩ [0,1]` is sequentially closed. -/
lemma lowerSeq_closed {d : ℕ} (hd : 0 < d) {P : ℝ → Polynomial ℂ}
    (hdeg : ∀ w : ℝ, (P w).natDegree = d)
    (hcont : ∀ j : ℕ, Continuous fun w : ℝ => (P w).coeff j)
    (hnoReal : ∀ w : ℝ, w ∈ Set.Icc 0 1 → ∀ t : ℝ, Polynomial.eval (t : ℂ) (P w) ≠ 0)
    {w : ℕ → ℝ} (w0 : ℝ) (hw0 : w0 ∈ Set.Icc 0 1)
    (hw : ∀ k : ℕ, w k ∈ Set.Icc 0 1)
    (hlim : Tendsto w atTop (𝓝 w0))
    (hlower : ∀ k : ℕ, ∃ z : ℂ, (P (w k)).eval z = 0 ∧ z.im < 0) :
    ∃ z : ℂ, (P w0).eval z = 0 ∧ z.im < 0 := by
  classical
  rcases roots_bounded_near hd hdeg hcont w0 with ⟨η, hη0, R, hR⟩
  have hevη : ∀ᶠ k in atTop, |w k - w0| < η := by
    have h := Metric.tendsto_nhds.mp hlim η hη0
    filter_upwards [h] with k hk
    simpa [Real.dist_eq] using hk
  rcases (Filter.eventually_atTop.mp hevη) with ⟨K, hK⟩
  let r : ℕ → ℂ := fun k => Classical.choose (hlower k)
  have hrk : ∀ k : ℕ, (P (w k)).eval (r k) = 0 ∧ (r k).im < 0 := by
    intro k
    exact Classical.choose_spec (hlower k)
  have hrmem : ∀ m : ℕ, r (K + m) ∈ closedBall (0 : ℂ) R := by
    intro m
    have hwKm : |w (K + m) - w0| < η := hK (K + m) (by omega)
    have hle : ‖r (K + m)‖ ≤ R := hR (w (K + m)) hwKm (r (K + m)) (hrk (K + m)).1
    exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hle)
  have hcmem : ∀ m : ℕ, r (K + m) ∈ closedBall (0 : ℂ) (max R 0) := by
    intro m
    exact Metric.closedBall_subset_closedBall (le_max_left R 0) (hrmem m)
  have hRge0 : 0 ≤ max R 0 := le_max_right R 0
  rcases (isCompact_closedBall (0 : ℂ) (max R 0)).tendsto_subseq (x := fun m => r (K + m)) hcmem
    with ⟨a, ha, φ, hφmono, hφlim⟩
  -- a ∈ closedBall, Tendsto (fun m => r (K + φ m)) atTop (𝓝 a)
  let g : ℕ → ℕ := fun m => K + φ m
  have hgmono : StrictMono g := by
    intro m n hmn
    dsimp [g]
    exact Nat.add_lt_add_left (hφmono hmn) K
  have hgtend : Tendsto g atTop atTop := StrictMono.tendsto_atTop hgmono
  have hwlim : Tendsto (fun m => w (g m)) atTop (𝓝 w0) := hlim.comp hgtend
  have hzlim : Tendsto (fun m => r (g m)) atTop (𝓝 a) := by
    simpa [g, Function.comp_def] using hφlim
  have heval_cont := eval_continuous hcont hdeg
  have hpair : Tendsto (fun m : ℕ => (w (g m), r (g m))) atTop (𝓝 (w0, a)) := by
    simpa [← nhds_prod_eq] using (hwlim.prodMk hzlim)
  have hlimval : Tendsto (fun m : ℕ => (P (w (g m))).eval (r (g m))) atTop
      (𝓝 ((P w0).eval a)) :=
    heval_cont.continuousAt.tendsto.comp hpair
  have hzero : (fun m : ℕ => (P (w (g m))).eval (r (g m))) = fun _ : ℕ => (0 : ℂ) := by
    funext m
    exact (hrk (g m)).1
  have hroot_lim : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 ((P w0).eval a)) := by
    simpa [hzero] using hlimval
  have hroot_a : (P w0).eval a = 0 := by
    exact tendsto_nhds_unique hroot_lim (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (0 : ℂ)))
  -- imaginary part
  have himlim : Tendsto (fun m : ℕ => (r (g m)).im) atTop (𝓝 a.im) := by
    exact (Complex.continuous_im.tendsto a).comp hzlim
  have hima_le0 : a.im ∈ (Set.Iic (0 : ℝ)) := by
    exact (isClosed_Iic (a := (0 : ℝ))).mem_of_tendsto himlim
      (Filter.Eventually.of_forall (fun m => le_of_lt (hrk (g m)).2))
  have hima_le : a.im ≤ 0 := by
    simpa using hima_le0
  have hima_ne : a.im ≠ 0 := by
    intro ha0
    have haz : a = (a.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using ha0
    have hroot_real : (P w0).eval (a.re : ℂ) = 0 := by
      rw [← haz]
      exact hroot_a
    exact hnoReal w0 hw0 a.re hroot_real
  have hima : a.im < 0 := lt_of_le_of_ne hima_le hima_ne
  exact ⟨a, hroot_a, hima⟩

end LHR


theorem lowerHalfRoots_path {d : ℕ} (hd : 0 < d) (P : ℝ → Polynomial ℂ)
    (hdeg : ∀ w : ℝ, (P w).natDegree = d)
    (hcont : ∀ j : ℕ, Continuous fun w : ℝ => (P w).coeff j)
    (hnoReal : ∀ w : ℝ, w ∈ Set.Icc 0 1 → ∀ t : ℝ, Polynomial.eval (t : ℂ) (P w) ≠ 0)
    (hroot0 : ∀ z : ℂ, Polynomial.eval z (P 0) = 0 → 0 < z.im) :
    ∀ z : ℂ, Polynomial.eval z (P 1) = 0 → 0 < z.im := by
  classical
  let W : Set ℝ := {w | ∃ z : ℂ, (P w).eval z = 0 ∧ z.im < 0}
  let C : Set ℝ := W ∩ Set.Icc 0 1
  have hW0 : 0 ∉ W := by
    intro h
    rcases h with ⟨z, hz, hzIm⟩
    have hpos : 0 < z.im := hroot0 z hz
    linarith
  have hC0 : 0 ∉ C := by
    intro h
    exact hW0 h.1
  intro z hz
  by_contra hzneg
  have hzle : z.im ≤ 0 := le_of_not_gt hzneg
  have hzne : z.im ≠ 0 := by
    intro him0
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [him0]
    have hzr : (P 1).eval (z.re : ℂ) = 0 := by
      rw [← hzreal]
      exact hz
    exact hnoReal 1 (by norm_num) z.re hzr
  have hzlt : z.im < 0 := lt_of_le_of_ne hzle hzne
  have h1W : 1 ∈ W := ⟨z, hz, hzlt⟩
  have h1C : 1 ∈ C := ⟨h1W, by norm_num⟩
  have hCne : C.Nonempty := ⟨1, h1C⟩
  have hCbdd : BddBelow C := by
    refine ⟨0, ?_⟩
    intro x hx
    exact hx.2.1
  let w0 : ℝ := sInf C
  have hwlts : ∀ k : ℕ, ∃ w : ℝ, w ∈ C ∧ w < w0 + (1 : ℝ) / (k + 1) := by
    intro k
    have hk : 0 < (1 : ℝ) / (k + 1) := by positivity
    have hb : sInf C < w0 + (1 : ℝ) / (k + 1) := by
      dsimp [w0]
      linarith
    exact exists_lt_of_csInf_lt hCne hb
  let w : ℕ → ℝ := fun k => Classical.choose (hwlts k)
  have hwC : ∀ k : ℕ, w k ∈ C := by
    intro k
    exact (Classical.choose_spec (hwlts k)).1
  have hwlt : ∀ k : ℕ, w k < w0 + (1 : ℝ) / (k + 1) := by
    intro k
    exact (Classical.choose_spec (hwlts k)).2
  have hwge : ∀ k : ℕ, w0 ≤ w k := by
    intro k
    exact csInf_le hCbdd (hwC k)
  have hwIcc : ∀ k : ℕ, w k ∈ Set.Icc 0 1 := by
    intro k
    exact (hwC k).2
  have hw0Icc : w0 ∈ Set.Icc 0 1 := by
    constructor
    · dsimp [w0]
      exact le_csInf hCne (by intro b hb; exact hb.2.1)
    · dsimp [w0]
      exact csInf_le hCbdd h1C
  have hdist_le : ∀ k : ℕ, dist (w k) w0 ≤ (1 : ℝ) / (k + 1) := by
    intro k
    have hnonneg : 0 ≤ w k - w0 := sub_nonneg.mpr (hwge k)
    have habs : |w k - w0| = w k - w0 := abs_of_nonneg hnonneg
    have hlt : w k - w0 < (1 : ℝ) / (k + 1) := by
      have := hwlt k
      linarith
    rw [Real.dist_eq]
    calc
      |w k - w0| = w k - w0 := habs
      _ ≤ (1 : ℝ) / (k + 1) := le_of_lt hlt
  have hwlim : Tendsto w atTop (𝓝 w0) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    have hg : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 (0 : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact squeeze_zero (fun k => dist_nonneg) hdist_le hg
  have hlower : ∀ k : ℕ, ∃ z : ℂ, (P (w k)).eval z = 0 ∧ z.im < 0 := by
    intro k
    exact (hwC k).1
  have hw0C : w0 ∈ C := by
    rcases LHR.lowerSeq_closed hd hdeg hcont hnoReal w0 hw0Icc hwIcc hwlim hlower
      with ⟨zz, hzz, hzzim⟩
    exact ⟨⟨zz, hzz, hzzim⟩, hw0Icc⟩
  have hw0ge0 : 0 ≤ w0 := by
    dsimp [w0]
    exact le_csInf hCne (by intro b hb; exact hb.2.1)
  have hw0ne0 : w0 ≠ 0 := by
    intro h
    exact hC0 (by simpa [h] using hw0C)
  have hw0pos : 0 < w0 := lt_of_le_of_ne hw0ge0 (Ne.symm hw0ne0)
  rcases hw0C with ⟨hw0W, hw0Icc'⟩
  rcases hw0W with ⟨r, hrroot, hrIm⟩
  rcases LHR.root_persist_lower hdeg hd hcont w0 hrroot hrIm with ⟨ηp, hηp0, hηp⟩
  let δ : ℝ := min ηp (w0 / 2) / 2
  have hmin0 : 0 < min ηp (w0 / 2) := lt_min hηp0 (by positivity)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact half_pos hmin0
  have hδ_lt_η : δ < ηp := by
    dsimp [δ]
    have h1 : min ηp (w0 / 2) / 2 ≤ ηp / 2 :=
      (div_le_div_of_nonneg_right (min_le_left ηp (w0 / 2)) (by norm_num))
    linarith
  have hδ_lt_w0 : δ < w0 := by
    dsimp [δ]
    have h1 : min ηp (w0 / 2) / 2 ≤ w0 / 4 := by
      have hle : min ηp (w0 / 2) ≤ w0 / 2 := min_le_right ηp (w0 / 2)
      calc
        min ηp (w0 / 2) / 2 ≤ (w0 / 2) / 2 := by
          exact (div_le_div_of_nonneg_right hle (by norm_num))
        _ = w0 / 4 := by ring
    linarith [hw0pos]
  let w1 : ℝ := w0 - δ
  have hw1pos : 0 < w1 := by
    dsimp [w1]
    linarith
  have hw1le1 : w1 ≤ 1 := by
    dsimp [w1]
    linarith [hw0Icc.2]
  have hw1dist : |w1 - w0| < ηp := by
    have heq : |w1 - w0| = δ := by
      have hw1_le : w1 ≤ w0 := by dsimp [w1]; linarith
      have hnonpos : w1 - w0 ≤ 0 := sub_nonpos.mpr hw1_le
      rw [abs_of_nonpos hnonpos]
      dsimp [w1]
      ring
    rw [heq]
    exact hδ_lt_η
  have hw1W : w1 ∈ W := by
    rcases hηp w1 hw1dist with ⟨zz, hzz, hzzim⟩
    exact ⟨zz, hzz, hzzim⟩
  have hw1C : w1 ∈ C := ⟨hw1W, by constructor; linarith; linarith⟩
  have hcontr : w0 ≤ w1 := csInf_le hCbdd hw1C
  have hw1lt0 : w1 < w0 := by
    dsimp [w1]
    linarith
  exact (not_le_of_gt hw1lt0) hcontr

end Commons.Analysis.MvPolynomial

