import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Limits of real-rooted polynomials of bounded degree are zero or real-rooted

`realRooted_limit_closed`: if a sequence of real polynomials of degree at most `d` is
coefficientwise convergent and every member is either zero or has only real complex roots,
then the limit is either zero or has only real complex roots (Hurwitz's theorem in the
coefficientwise setting).

The proof: the set of (zero or) real-rooted polynomials is closed.  We argue by
contradiction through the contrapositive: a nonzero limit with a non-real root `r` in the
upper half-plane must be approached by polynomials with a root in a small closed disk around
`r`, and that disk can be chosen strictly inside the upper half-plane, so the approximating
polynomial has a non-real root.
-/

noncomputable section
open Polynomial BigOperators Filter Set Metric Complex
open scoped Topology BigOperators ComplexConjugate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Analysis.MvPolynomial

-- ============================================================
-- Part 1: polynomial coefficient facts (generic)
-- ============================================================

lemma rrl_coeff_sum_monomial {R : Type*} [Semiring R] {d : ℕ} (a : Fin (d+1) → R) (j : ℕ) :
    ((∑ i : Fin (d+1), Polynomial.monomial (i : ℕ) (a i)).coeff j) =
      if h : j < d + 1 then a ⟨j,h⟩ else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hj : j < d + 1
  · have hsum : (∑ i : Fin (d+1), if (i : ℕ) = j then a i else 0) = a ⟨j, hj⟩ := by
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b hb hbne
        have hbj : (b : ℕ) ≠ j := by
          intro hbj'
          apply hbne
          apply Fin.ext
          exact hbj'
        simp [hbj]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    rw [hsum]
    simp [hj]
  · have hsum : (∑ i : Fin (d+1), if (i : ℕ) = j then a i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : (i : ℕ) ≠ j := by omega
      simp [hij]
    rw [hsum]
    simp [hj]

lemma rrl_coeff_sum_monomial' {R : Type*} [Semiring R] {d : ℕ} (a : Fin (d+1) → R)
    (i : Fin (d+1)) :
    ((∑ j : Fin (d+1), Polynomial.monomial (j : ℕ) (a j)).coeff (i : ℕ)) = a i := by
  rw [rrl_coeff_sum_monomial]
  simp [i.isLt]

lemma rrl_sum_monomial_eq_zero_iff {R : Type*} [Semiring R] {d : ℕ} (a : Fin (d+1) → R) :
    (∑ i : Fin (d+1), Polynomial.monomial (i : ℕ) (a i)) = 0 ↔ ∀ i, a i = 0 := by
  classical
  constructor
  · intro h i
    have hc : ((∑ j : Fin (d+1), Polynomial.monomial (j : ℕ) (a j)).coeff (i : ℕ)) = 0 := by
      rw [h]; simp
    exact (rrl_coeff_sum_monomial' a i).symm.trans hc
  · intro h
    simp [h]

lemma rrl_eval_map_sum_eq (d : ℕ) (a : Fin (d+1) → ℝ) (z : ℂ) :
    (Polynomial.map (algebraMap ℝ ℂ) (∑ i : Fin (d+1), Polynomial.monomial (i : ℕ) (a i))).eval z =
      ∑ i : Fin (d+1), (a i : ℂ) * z ^ (i : ℕ) := by
  rw [Polynomial.map_sum]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_monomial]
  rw [Polynomial.eval_monomial]
  simp

lemma rrl_eval_map_sum_conj (d : ℕ) (a : Fin (d+1) → ℝ) (z : ℂ) :
    (Polynomial.map (algebraMap ℝ ℂ) (∑ i : Fin (d+1), Polynomial.monomial (i : ℕ) (a i))).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((Polynomial.map (algebraMap ℝ ℂ) (∑ i : Fin (d+1), Polynomial.monomial (i : ℕ) (a i))).eval z) := by
  rw [rrl_eval_map_sum_eq]
  rw [rrl_eval_map_sum_eq]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [map_mul, map_pow]
  congr 1
  · simp [Complex.conj_ofReal]

lemma rrl_exists_ofReal_eq_iff (r : ℂ) : (∃ s : ℝ, r = (s : ℂ)) ↔ r.im = 0 := by
  constructor
  · rintro ⟨s, rfl⟩
    simp
  · intro him
    refine ⟨r.re, ?_⟩
    apply Complex.ext
    · rfl
    · simp [him]

lemma rrl_norm_real_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

-- ============================================================
-- Part 2: complex analysis / roots
-- ============================================================

lemma rrl_norm_lower_bound_of_no_roots {p : Polynomial ℂ} {r : ℂ} {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hp_ball : ∀ z : ℂ, z ∈ closedBall r ρ → p.eval z ≠ 0)
    (hbound : ∀ z : ℂ, z ∈ sphere r ρ → δ ≤ ‖p.eval z‖) :
    δ ≤ ‖p.eval r‖ := by
  classical
  have hdif : DiffContOnCl ℂ (fun z : ℂ => p.eval z) (ball r ρ) := by
    have hd : Differentiable ℂ (fun z : ℂ => p.eval z) := Polynomial.differentiable p
    exact hd.diffContOnCl.mono (Set.subset_univ _)
  have hcl_sub : closure (ball r ρ) ⊆ closedBall r ρ := closure_ball_subset_closedBall
  have hne_on_cl : ∀ z ∈ closure (ball r ρ), p.eval z ≠ 0 := by
    intro z hz
    exact hp_ball z (hcl_sub hz)
  have hdinv : DiffContOnCl ℂ (fun z : ℂ => (p.eval z)⁻¹) (ball r ρ) := hdif.inv hne_on_cl
  have hC : ∀ z ∈ frontier (ball r ρ), ‖(p.eval z)⁻¹‖ ≤ δ⁻¹ := by
    intro z hz
    have hzs : z ∈ sphere r ρ := by
      rw [frontier_ball r (ne_of_gt hρ)] at hz
      exact hz
    have hle : δ ≤ ‖p.eval z‖ := hbound z hzs
    have hne : p.eval z ≠ 0 := by
      intro h
      have hz0 : ‖p.eval z‖ = 0 := by simp [h]
      have : δ ≤ (0 : ℝ) := by simpa [hz0] using hle
      linarith
    have hpos : 0 < ‖p.eval z‖ := norm_pos_iff.mpr hne
    rw [norm_inv]
    exact (inv_le_inv₀ hpos hδ).mpr hle
  have hmain := Complex.norm_le_of_forall_mem_frontier_norm_le
    (E := ℂ) (F := ℂ) (U := ball r ρ) (f := fun z : ℂ => (p.eval z)⁻¹)
    Metric.isBounded_ball hdinv hC (subset_closure (Metric.mem_ball_self hρ))
  have hne_r : p.eval r ≠ 0 := by
    exact hp_ball r (mem_closedBall.mpr (by simp [hρ.le]))
  have hpos_r : 0 < ‖p.eval r‖ := norm_pos_iff.mpr hne_r
  have hmain' : ‖(p.eval r)⁻¹‖ ≤ δ⁻¹ := by
    simpa using hmain
  rw [norm_inv] at hmain'
  exact (inv_le_inv₀ hpos_r hδ).mp hmain'

lemma rrl_exists_pos_lt_of_finite_ne_zero {c : ℝ} (hc : 0 < c) (s : Finset ℝ)
    (hs : ∀ x ∈ s, 0 < x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < c ∧ ∀ x ∈ s, x ≠ ρ := by
  classical
  let m : ℝ := if h : s.Nonempty then s.min' h else 1
  have hm_pos : 0 < m := by
    dsimp [m]
    by_cases hsne : s.Nonempty
    · have hmem : s.min' hsne ∈ s := Finset.min'_mem s hsne
      simpa [hsne] using hs (s.min' hsne) hmem
    · simp [hsne]
  have hm_le : ∀ x ∈ s, m ≤ x := by
    intro x hx
    dsimp [m]
    by_cases hsne : s.Nonempty
    · simpa [hsne] using Finset.min'_le s x hx
    · exact False.elim (hsne ⟨x, hx⟩)
  let ρ : ℝ := min (m / 2) (c / 2)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · dsimp [ρ]
    exact lt_min (by linarith) (by linarith)
  · dsimp [ρ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro x hx
    have hxlt : ρ < x := by
      dsimp [ρ]
      have hm_le_x := hm_le x hx
      have hm2 : m / 2 < m := by linarith
      have hle : min (m / 2) (c / 2) ≤ m / 2 := min_le_left _ _
      have hlt : min (m / 2) (c / 2) < m := lt_of_le_of_lt hle hm2
      exact lt_of_lt_of_le hlt hm_le_x
    exact (ne_of_lt hxlt).symm

lemma rrl_exists_radius_rootfree (p : Polynomial ℂ) (hp : p ≠ 0) (r : ℂ)
    (hIm : 0 < r.im) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r.im ∧ ∀ z : ℂ, z ∈ sphere r ρ → p.eval z ≠ 0 := by
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
  rcases rrl_exists_pos_lt_of_finite_ne_zero hIm s hs_pos with ⟨ρ, hρ0, hρc, hρavoid⟩
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

lemma rrl_exists_pos_lower_bound_on_sphere (p : Polynomial ℂ) {r : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsphere : ∀ z : ℂ, z ∈ sphere r ρ → p.eval z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ∈ sphere r ρ → δ ≤ ‖p.eval z‖ := by
  classical
  have hs : IsCompact (sphere r ρ) := isCompact_sphere r ρ
  have hsne : (sphere r ρ).Nonempty := by
    refine ⟨r + ρ, ?_⟩
    rw [mem_sphere_iff_norm]
    simp [hρ.le]
  have hcont : ContinuousOn (fun z : ℂ => ‖p.eval z‖) (sphere r ρ) := by
    exact (Polynomial.differentiable p).continuous.norm.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := hs.exists_isMinOn hsne hcont
  refine ⟨‖p.eval z₀‖, ?_, ?_⟩
  · exact norm_pos_iff.mpr (hsphere z₀ hz₀)
  · intro z hz
    exact hmin hz

-- ============================================================
-- Part 3: coefficient closeness
-- ============================================================

noncomputable def rrl_qC (d : ℕ) (a : Fin (d+1) → ℝ) (z : ℂ) : ℂ :=
  ∑ i : Fin (d+1), (a i : ℂ) * z ^ (i : ℕ)

lemma rrl_tendsto_sum_abs_sub (d : ℕ) (c : ℕ → Fin (d+1) → ℝ) (cf : Fin (d+1) → ℝ)
    (hlim : ∀ i : Fin (d+1), Tendsto (fun k : ℕ => c k i) atTop (𝓝 (cf i))) :
    Tendsto (fun k : ℕ => (∑ i : Fin (d+1), |c k i - cf i|)) atTop (𝓝 (0 : ℝ)) := by
  classical
  have hterm : ∀ i : Fin (d+1), Tendsto (fun k : ℕ => |c k i - cf i|) atTop (𝓝 (0 : ℝ)) := by
    intro i
    have hsub : Tendsto (fun k : ℕ => c k i - cf i) atTop (𝓝 (cf i - cf i)) :=
      (hlim i).sub tendsto_const_nhds
    have hnorm : Tendsto (fun k : ℕ => ‖c k i - cf i‖) atTop (𝓝 ‖cf i - cf i‖) := hsub.norm
    simpa using hnorm
  have hsum : Tendsto (fun k : ℕ => (∑ i : Fin (d+1), |c k i - cf i|)) atTop
      (𝓝 (∑ i : Fin (d+1), (0 : ℝ))) :=
    tendsto_finsetSum (Finset.univ : Finset (Fin (d+1))) (by intro i hi; exact hterm i)
  simpa using hsum

lemma rrl_eventually_sum_abs_sub_lt (d : ℕ) (c : ℕ → Fin (d+1) → ℝ) (cf : Fin (d+1) → ℝ)
    (hlim : ∀ i : Fin (d+1), Tendsto (fun k : ℕ => c k i) atTop (𝓝 (cf i)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop, (∑ i : Fin (d+1), |c k i - cf i|) < η := by
  have ht := rrl_tendsto_sum_abs_sub d c cf hlim
  have hev : ∀ᶠ k in atTop, |(∑ i : Fin (d+1), |c k i - cf i|)| < η := by
    simpa [dist_eq_norm] using ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hη)
  filter_upwards [hev] with k hk
  have hnonneg : 0 ≤ ∑ i : Fin (d+1), |c k i - cf i| := Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
  rw [← abs_of_nonneg hnonneg]
  exact hk

lemma rrl_eval_sub_bound (d : ℕ) (a b : Fin (d+1) → ℝ) (z : ℂ) {B : ℝ} (hB : ‖z‖ ≤ B) :
    ‖rrl_qC d a z - rrl_qC d b z‖ ≤ (max B 1) ^ d * (∑ i : Fin (d+1), |a i - b i|) := by
  classical
  set M : ℝ := max B 1
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_right B 1
  have hzM : ‖z‖ ≤ M := le_trans hB (by dsimp [M]; exact le_max_left B 1)
  have hterm : ∀ i : Fin (d+1),
      ‖((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ ≤ |a i - b i| * M ^ d := by
    intro i
    calc
      ‖((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ = ‖((a i : ℂ) - (b i : ℂ))‖ * ‖z ^ (i : ℕ)‖ := norm_mul _ _
      _ = |a i - b i| * ‖z‖ ^ (i : ℕ) := by
        have h₁ : ‖((a i : ℂ) - (b i : ℂ))‖ = |a i - b i| := by
          have hs : ((a i : ℂ) - (b i : ℂ)) = ((a i - b i : ℝ) : ℂ) := by simp
          rw [hs]
          exact rrl_norm_real_complex (a i - b i)
        rw [h₁, norm_pow]
      _ ≤ |a i - b i| * M ^ (i : ℕ) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzM (i : ℕ)) (abs_nonneg _)
      _ ≤ |a i - b i| * M ^ d := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 (Nat.le_of_lt_succ i.isLt)) (abs_nonneg _)
  have hstep : rrl_qC d a z - rrl_qC d b z =
      ∑ i : Fin (d+1), ((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ) := by
    dsimp [rrl_qC]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    ‖rrl_qC d a z - rrl_qC d b z‖ =
        ‖∑ i : Fin (d+1), ((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ := by rw [hstep]
    _ ≤ ∑ i : Fin (d+1), ‖((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (d+1), |a i - b i| * M ^ d := Finset.sum_le_sum (by intro i hi; exact hterm i)
    _ = (∑ i : Fin (d+1), |a i - b i|) * M ^ d := by rw [Finset.sum_mul]
    _ ≤ (max B 1) ^ d * (∑ i : Fin (d+1), |a i - b i|) := by
      dsimp [M]
      rw [mul_comm]

lemma rrl_eventually_uniform_eval_sub_lt (d : ℕ) (c : ℕ → Fin (d+1) → ℝ)
    (cf : Fin (d+1) → ℝ)
    (hlim : ∀ i : Fin (d+1), Tendsto (fun k : ℕ => c k i) atTop (𝓝 (cf i)))
    (s : Set ℂ) {B : ℝ} (hB : ∀ z : ℂ, z ∈ s → ‖z‖ ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ z : ℂ, z ∈ s → ‖rrl_qC d (c k) z - rrl_qC d cf z‖ < ε := by
  classical
  set M : ℝ := max B 1
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_right B 1
  have hMge0 : 0 ≤ M := le_of_lt (lt_of_lt_of_le zero_lt_one hM1)
  have hη : 0 < ε / (M ^ d + 1) := by positivity
  have hev := rrl_eventually_sum_abs_sub_lt d c cf hlim (ε / (M ^ d + 1)) hη
  filter_upwards [hev] with k hk
  intro z hz
  have hb := rrl_eval_sub_bound d (c k) cf z (hB z hz)
  have hsum_lt : (∑ i : Fin (d+1), |c k i - cf i|) < ε / (M ^ d + 1) := by
    simpa [M] using hk
  have hdenpos : 0 < M ^ d + 1 := by positivity
  have hmul_lt : (max B 1) ^ d * (∑ i : Fin (d+1), |c k i - cf i|) < ε := by
    have hsnonneg : 0 ≤ ∑ i : Fin (d+1), |c k i - cf i| :=
      Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
    have hmul_le : (max B 1) ^ d * (∑ i : Fin (d+1), |c k i - cf i|) ≤
        (max B 1) ^ d * (ε / (M ^ d + 1)) := by
      dsimp [M]
      exact mul_le_mul_of_nonneg_left (le_of_lt hk) (pow_nonneg hMge0 d)
    have hfrac : M ^ d / (M ^ d + 1) < (1 : ℝ) := (div_lt_one hdenpos).mpr (by linarith)
    have hmul2 : (max B 1) ^ d * (ε / (M ^ d + 1)) < ε := by
      dsimp [M]
      calc
        M ^ d * (ε / (M ^ d + 1)) = ε * (M ^ d / (M ^ d + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := by ring
    exact lt_of_le_of_lt hmul_le hmul2
  exact lt_of_le_of_lt hb hmul_lt

lemma rrl_root_in_closedBall (p q : Polynomial ℂ) (r : ℂ) {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hqroot : q.eval r = 0)
    (hcl_sphere : ∀ z : ℂ, z ∈ sphere r ρ → ‖p.eval z - q.eval z‖ < δ / 2)
    (hsmall : ‖p.eval r‖ < δ / 2)
    (hq_sphere : ∀ z : ℂ, z ∈ sphere r ρ → δ ≤ ‖q.eval z‖) :
    ∃ w : ℂ, ‖w - r‖ ≤ ρ ∧ p.eval w = 0 := by
  by_contra hnone
  have hp_ball : ∀ z : ℂ, z ∈ closedBall r ρ → p.eval z ≠ 0 := by
    intro z hz hz0
    apply hnone
    refine ⟨z, ?_, hz0⟩
    simpa [dist_eq_norm] using hz
  have hbound : ∀ z : ℂ, z ∈ sphere r ρ → δ / 2 ≤ ‖p.eval z‖ := by
    intro z hz
    have hq : δ ≤ ‖q.eval z‖ := hq_sphere z hz
    have hclose : ‖p.eval z - q.eval z‖ < δ / 2 := hcl_sphere z hz
    have hrev : ‖q.eval z - p.eval z‖ < δ / 2 := by
      simpa [norm_sub_rev] using hclose
    have htri : ‖q.eval z‖ ≤ ‖q.eval z - p.eval z‖ + ‖p.eval z‖ := by
      simpa [sub_add_cancel] using (norm_add_le (q.eval z - p.eval z) (p.eval z))
    have hadd : ‖q.eval z - p.eval z‖ + ‖p.eval z‖ < ‖p.eval z‖ + δ / 2 := by
      simpa [add_comm] using (add_lt_add_right hrev (‖p.eval z‖))
    have hlt : δ < ‖p.eval z‖ + δ / 2 := by
      exact lt_of_le_of_lt (le_trans hq htri) hadd
    have : δ / 2 < ‖p.eval z‖ := by linarith
    exact le_of_lt this
  have hlb := rrl_norm_lower_bound_of_no_roots (p := p) (r := r) (ρ := ρ) (δ := δ / 2)
    hρ (by positivity) hp_ball hbound
  have hcontr : δ / 2 < δ / 2 := lt_of_le_of_lt hlb hsmall
  exact (lt_irrefl (δ / 2)) hcontr


-- ============================================================
-- Main theorem
-- ============================================================

theorem realRooted_limit_closed (d : ℕ) (c : ℕ → Fin (d + 1) → ℝ) (cf : Fin (d + 1) → ℝ)
    (hlim : ∀ i : Fin (d + 1), Filter.Tendsto (fun k : ℕ => c k i) Filter.atTop (nhds (cf i)))
    (hc : ∀ k : ℕ,
      (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c k i)) = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
            (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c k i))) = 0 →
          ∃ s : ℝ, r = (s : Complex)) :
    (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (cf i)) = 0 ∨
      ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (cf i))) = 0 →
        ∃ s : ℝ, r = (s : Complex) := by
  classical
  set P : Polynomial ℝ := ∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (cf i)
  set PC : Polynomial ℂ := Polynomial.map (algebraMap ℝ ℂ) P
  by_contra hneg
  have hP0 : P ≠ 0 := by
    intro h
    apply hneg
    left
    simpa [P] using h
  have hnotB : ¬ ∀ r : ℂ, PC.eval r = 0 → ∃ s : ℝ, r = (s : ℂ) := by
    intro hB
    apply hneg
    right
    simpa [P, PC] using hB
  rcases Classical.not_forall.mp hnotB with ⟨r, h⟩
  rcases Classical.not_imp.mp h with ⟨hrroot, hrnotreal⟩
  have hrIm_ne : r.im ≠ 0 := by
    intro him0
    exact hrnotreal ((rrl_exists_ofReal_eq_iff r).mpr him0)
  let r0 : ℂ := if 0 < r.im then r else starRingEnd ℂ r
  have hr0root : PC.eval r0 = 0 := by
    dsimp [r0]
    by_cases h : 0 < r.im
    · simp [h, hrroot]
    · have hcc := rrl_eval_map_sum_conj d cf r
      have hcce : PC.eval (starRingEnd ℂ r) = starRingEnd ℂ (PC.eval r) := by
        simp [P, PC, hcc]
      simp [h]
      rw [hcce, hrroot]
      simp
  have hr0im : 0 < r0.im := by
    dsimp [r0]
    by_cases h : 0 < r.im
    · simp [h]
    · have hle : r.im ≤ 0 := le_of_not_gt h
      have hnegim : r.im < 0 := lt_of_le_of_ne hle hrIm_ne
      simp [h]
      linarith
  -- i0 with cf i0 ≠ 0
  have hex_i0 : ∃ i0 : Fin (d + 1), cf i0 ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hP0
    simpa [P] using (rrl_sum_monomial_eq_zero_iff cf).mpr hnone
  obtain ⟨i0, hcfi0⟩ := hex_i0
  -- PC ≠ 0 (for the root-free radius)
  have hPC0 : PC ≠ 0 := by
    intro hz
    have hci0 : PC.coeff (i0 : ℕ) ≠ 0 := by
      have hm : PC.coeff (i0 : ℕ) = (cf i0 : ℂ) := by
        dsimp [PC, P]
        rw [Polynomial.coeff_map]
        rw [rrl_coeff_sum_monomial]
        simp [i0.isLt]
      rw [hm]
      exact_mod_cast hcfi0
    exact hci0 (by rw [hz]; simp)
  -- radius
  obtain ⟨ρ, hρ0, hρlt, hρsphere⟩ := rrl_exists_radius_rootfree PC hPC0 r0 hr0im
  -- δ
  obtain ⟨δ, hδ0, hδsphere⟩ := rrl_exists_pos_lower_bound_on_sphere PC (ρ := ρ) hρ0 hρsphere
  -- smallness bound lemmas for the eventual arguments
  have hev_pk_ne0 : ∀ᶠ k in atTop, (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c k i)) ≠ 0 := by
    have ht := hlim i0
    have hne_ev : ∀ᶠ k in atTop, c k i0 ≠ 0 := by
      exact ht.eventually_ne hcfi0
    filter_upwards [hne_ev] with k hk
    intro hk0
    have hck : c k i0 = 0 := by
      have hc' := rrl_coeff_sum_monomial' (c k) i0
      rw [hk0] at hc'
      simpa using hc'.symm
    exact hk hck
  -- uniform closeness on sphere r0 ρ, ε = δ / 2
  have hBsphere : ∀ z : ℂ, z ∈ sphere r0 ρ → ‖z‖ ≤ ‖r0‖ + ρ := by
    intro z hz
    have hzr : ‖z - r0‖ = ρ := by
      simpa using hz
    calc
      ‖z‖ = ‖(z - r0) + r0‖ := by congr 1; abel
      _ ≤ ‖z - r0‖ + ‖r0‖ := norm_add_le _ _
      _ = ρ + ‖r0‖ := by rw [hzr]
      _ ≤ ‖r0‖ + ρ := by linarith
  have hev_sphere : ∀ᶠ k in atTop, ∀ z : ℂ, z ∈ sphere r0 ρ →
      ‖rrl_qC d (c k) z - rrl_qC d cf z‖ < δ / 2 := by
    exact rrl_eventually_uniform_eval_sub_lt d c cf hlim (sphere r0 ρ) (B := ‖r0‖ + ρ)
      hBsphere (δ / 2) (by positivity)
  -- smallness at r0
  have hB_r0 : ∀ z : ℂ, z ∈ ({r0} : Set ℂ) → ‖z‖ ≤ ‖r0‖ := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact le_rfl
  have hev_close_r0 : ∀ᶠ k in atTop, ‖rrl_qC d (c k) r0 - rrl_qC d cf r0‖ < δ / 2 := by
    have h := rrl_eventually_uniform_eval_sub_lt d c cf hlim ({r0} : Set ℂ) (B := ‖r0‖)
      hB_r0 (δ / 2) (by positivity)
    filter_upwards [h] with k hk
    exact hk r0 (by simp)
  have hev_small_r0 : ∀ᶠ k in atTop, ‖rrl_qC d (c k) r0‖ < δ / 2 := by
    have hqf0 : rrl_qC d cf r0 = 0 := by
      -- rrl_qC cf r0 = PC.eval r0 = 0
      dsimp [rrl_qC]
      rw [← rrl_eval_map_sum_eq]
      -- now: (map (algebraMap ℝ ℂ)(∑ monomial cf)).eval r0 = 0: same as PC.eval r0
      simpa [P, PC] using hr0root
    filter_upwards [hev_close_r0] with k hk
    have htri : ‖rrl_qC d (c k) r0‖ ≤ ‖rrl_qC d (c k) r0 - rrl_qC d cf r0‖ + ‖rrl_qC d cf r0‖ := by
      simpa [sub_add_cancel] using (norm_add_le (rrl_qC d (c k) r0 - rrl_qC d cf r0) (rrl_qC d cf r0))
    have htri' : ‖rrl_qC d (c k) r0‖ < δ / 2 := by
      have hsumlt : ‖rrl_qC d (c k) r0 - rrl_qC d cf r0‖ + ‖rrl_qC d cf r0‖ < δ / 2 := by
        rw [hqf0] at hk ⊢
        simpa using hk
      exact lt_of_le_of_lt htri hsumlt
    exact htri'
  -- combine eventuals
  have hev_all : ∀ᶠ k in atTop,
      (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c k i)) ≠ 0 ∧
        (∀ z : ℂ, z ∈ sphere r0 ρ → ‖rrl_qC d (c k) z - rrl_qC d cf z‖ < δ / 2) ∧
          ‖rrl_qC d (c k) r0‖ < δ / 2 := by
    exact hev_pk_ne0.and (hev_sphere.and hev_small_r0)
  rw [Filter.eventually_atTop] at hev_all
  rcases hev_all with ⟨N, hN⟩
  have hk_all := hN N (le_rfl)
  -- pick a specific large k
  rcases hk_all with ⟨hk_ne0, hk_sphere, hk_small⟩
  -- per-k: pkC := map (algebraMap ℝ ℂ)(pksum k)
  let pks : Polynomial ℝ := ∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c N i)
  let pkC : Polynomial ℂ := Polynomial.map (algebraMap ℝ ℂ) pks
  have hcl_sphere : ∀ z : ℂ, z ∈ sphere r0 ρ → ‖pkC.eval z - PC.eval z‖ < δ / 2 := by
    intro z hz
    have h := hk_sphere z hz
    have h1 : rrl_qC d (c N) z = pkC.eval z := by
      dsimp [pkC, pks]
      exact (rrl_eval_map_sum_eq d (c N) z).symm
    have h2 : rrl_qC d cf z = PC.eval z := by
      dsimp [PC, P]
      exact (rrl_eval_map_sum_eq d cf z).symm
    rwa [h1, h2] at h
  have hsmall : ‖pkC.eval r0‖ < δ / 2 := by
    have h := hk_small
    have h1 : rrl_qC d (c N) r0 = pkC.eval r0 := by
      dsimp [pkC, pks]
      exact (rrl_eval_map_sum_eq d (c N) r0).symm
    simpa [h1] using h
  obtain ⟨w, hwball, hwroot⟩ := rrl_root_in_closedBall pkC PC r0 (ρ := ρ) (δ := δ)
    hρ0 hδ0 hr0root hcl_sphere hsmall hδsphere
  -- w has positive imaginary part
  have himdiff : |w.im - r0.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (w - r0)
    have hsub : (w - r0).im = w.im - r0.im := by simp
    have hnorm : ‖w - r0‖ ≤ ρ := hwball
    simpa [hsub] using le_trans h hnorm
  have hwim : 0 < w.im := by
    have hle : -(ρ) ≤ w.im - r0.im := (abs_le.mp himdiff).1
    have hwge : r0.im - ρ ≤ w.im := by linarith
    linarith
  -- hc at N
  have hcN := hc N
  -- root of pkC is root in hc's sense:
  have hwroot_hc : Polynomial.eval w (Polynomial.map (algebraMap ℝ ℂ)
      (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c N i))) = 0 := by
    simpa [pkC, pks] using hwroot
  rcases hcN with hk0 | hkreal
  · exact hk_ne0 hk0
  · have hwr := hkreal w hwroot_hc
    rcases hwr with ⟨s, hs⟩
    have hwim0 : w.im = 0 := by
      rw [hs]
      simp
    linarith

end Commons.Analysis.MvPolynomial