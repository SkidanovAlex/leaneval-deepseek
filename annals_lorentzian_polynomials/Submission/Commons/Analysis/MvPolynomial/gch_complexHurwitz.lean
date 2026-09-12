import Mathlib
import Submission.Commons.Analysis.MvPolynomial.realRooted_limit_closed

/-!
# Complex Hurwitz theorem (coefficientwise)

`gch_complexHurwitz`: if a sequence of complex polynomials of degree at most `d`
is coefficientwise convergent to a polynomial which has a root at `r` and no
other root in the closed disk around `r` of radius `ρ`, then eventually every
member of the sequence has a root inside that open disk.

This is a companion to `realRooted_limit_closed` in the same directory: the
"roots vary continuously with the coefficients" half of Hurwitz's theorem,
stated directly for complex coefficient vectors.
-/

noncomputable section
open Polynomial BigOperators Filter Set Metric Complex
open scoped Topology BigOperators ComplexConjugate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Analysis.MvPolynomial

-- ============================================================
-- polynomial coefficient facts (generic R), complex version
-- ============================================================

/-- The value of `∑ i, monomial i (a i)` at `z`, expanded. -/
noncomputable def gch_qC (d : ℕ) (a : Fin (d + 1) → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin (d + 1), a i * z ^ (i : ℕ)

lemma gch_eval_qC (d : ℕ) (a : Fin (d + 1) → ℂ) (z : ℂ) :
    (∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (a i)).eval z = gch_qC d a z := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_monomial]

lemma gch_tendsto_sum_norm_sub (d : ℕ) (c : ℕ → Fin (d + 1) → ℂ) (cf : Fin (d + 1) → ℂ)
    (hlim : ∀ i : Fin (d + 1), Tendsto (fun k : ℕ => c k i) atTop (𝓝 (cf i))) :
    Tendsto (fun k : ℕ => (∑ i : Fin (d + 1), ‖c k i - cf i‖)) atTop (𝓝 (0 : ℝ)) := by
  classical
  have hterm : ∀ i : Fin (d + 1), Tendsto (fun k : ℕ => ‖c k i - cf i‖) atTop (𝓝 (0 : ℝ)) := by
    intro i
    have hsub : Tendsto (fun k : ℕ => c k i - cf i) atTop (𝓝 (cf i - cf i)) :=
      (hlim i).sub tendsto_const_nhds
    have hnorm : Tendsto (fun k : ℕ => ‖c k i - cf i‖) atTop (𝓝 ‖cf i - cf i‖) := hsub.norm
    simpa using hnorm
  have hsum : Tendsto (fun k : ℕ => (∑ i : Fin (d + 1), ‖c k i - cf i‖)) atTop
      (𝓝 (∑ i : Fin (d + 1), (0 : ℝ))) :=
    tendsto_finsetSum (Finset.univ : Finset (Fin (d + 1))) (by intro i hi; exact hterm i)
  simpa using hsum

lemma gch_eventually_sum_norm_sub_lt (d : ℕ) (c : ℕ → Fin (d + 1) → ℂ) (cf : Fin (d + 1) → ℂ)
    (hlim : ∀ i : Fin (d + 1), Tendsto (fun k : ℕ => c k i) atTop (𝓝 (cf i)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop, (∑ i : Fin (d + 1), ‖c k i - cf i‖) < η := by
  have ht := gch_tendsto_sum_norm_sub d c cf hlim
  have hev : ∀ᶠ k in atTop, |(∑ i : Fin (d + 1), ‖c k i - cf i‖)| < η := by
    simpa [dist_eq_norm] using ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hη)
  filter_upwards [hev] with k hk
  have hnonneg : 0 ≤ ∑ i : Fin (d + 1), ‖c k i - cf i‖ :=
    Finset.sum_nonneg (by intro i hi; exact norm_nonneg _)
  rw [← abs_of_nonneg hnonneg]
  exact hk

lemma gch_eval_sub_bound (d : ℕ) (a b : Fin (d + 1) → ℂ) (z : ℂ) {B : ℝ} (hB : ‖z‖ ≤ B) :
    ‖gch_qC d a z - gch_qC d b z‖ ≤ (max B 1) ^ d * (∑ i : Fin (d + 1), ‖a i - b i‖) := by
  classical
  set M : ℝ := max B 1
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_right B 1
  have hzM : ‖z‖ ≤ M := le_trans hB (by dsimp [M]; exact le_max_left B 1)
  have hterm : ∀ i : Fin (d + 1),
      ‖((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ ≤ ‖a i - b i‖ * M ^ d := by
    intro i
    calc
      ‖((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ = ‖(a i : ℂ) - (b i : ℂ)‖ * ‖z ^ (i : ℕ)‖ :=
        norm_mul _ _
      _ = ‖a i - b i‖ * ‖z‖ ^ (i : ℕ) := by rw [norm_pow]
      _ ≤ ‖a i - b i‖ * M ^ (i : ℕ) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzM (i : ℕ))
          (norm_nonneg _)
      _ ≤ ‖a i - b i‖ * M ^ d := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 (Nat.le_of_lt_succ i.isLt))
          (norm_nonneg _)
  have hstep : gch_qC d a z - gch_qC d b z =
      ∑ i : Fin (d + 1), ((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ) := by
    dsimp [gch_qC]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    ‖gch_qC d a z - gch_qC d b z‖ =
        ‖∑ i : Fin (d + 1), ((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ := by rw [hstep]
    _ ≤ ∑ i : Fin (d + 1), ‖((a i : ℂ) - (b i : ℂ)) * z ^ (i : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (d + 1), ‖a i - b i‖ * M ^ d := Finset.sum_le_sum (by intro i hi; exact hterm i)
    _ = (∑ i : Fin (d + 1), ‖a i - b i‖) * M ^ d := by rw [Finset.sum_mul]
    _ ≤ (max B 1) ^ d * (∑ i : Fin (d + 1), ‖a i - b i‖) := by
      dsimp [M]
      rw [mul_comm]

lemma gch_eventually_uniform_eval_sub_lt (d : ℕ) (c : ℕ → Fin (d + 1) → ℂ)
    (cf : Fin (d + 1) → ℂ)
    (hlim : ∀ i : Fin (d + 1), Tendsto (fun k : ℕ => c k i) atTop (𝓝 (cf i)))
    (s : Set ℂ) {B : ℝ} (hB : ∀ z : ℂ, z ∈ s → ‖z‖ ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ z : ℂ, z ∈ s → ‖gch_qC d (c k) z - gch_qC d cf z‖ < ε := by
  classical
  set M : ℝ := max B 1
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_right B 1
  have hMge0 : 0 ≤ M := le_of_lt (lt_of_lt_of_le zero_lt_one hM1)
  have hη : 0 < ε / (M ^ d + 1) := by positivity
  have hev := gch_eventually_sum_norm_sub_lt d c cf hlim (ε / (M ^ d + 1)) hη
  filter_upwards [hev] with k hk
  intro z hz
  have hb := gch_eval_sub_bound d (c k) cf z (hB z hz)
  have hsum_lt : (∑ i : Fin (d + 1), ‖c k i - cf i‖) < ε / (M ^ d + 1) := by
    simpa [M] using hk
  have hdenpos : 0 < M ^ d + 1 := by positivity
  have hmul_lt : (max B 1) ^ d * (∑ i : Fin (d + 1), ‖c k i - cf i‖) < ε := by
    have hsnonneg : 0 ≤ ∑ i : Fin (d + 1), ‖c k i - cf i‖ :=
      Finset.sum_nonneg (by intro i hi; exact norm_nonneg _)
    have hmul_le : (max B 1) ^ d * (∑ i : Fin (d + 1), ‖c k i - cf i‖) ≤
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

-- ============================================================
-- Main theorem
-- ============================================================

theorem gch_complexHurwitz (d : ℕ) (c : ℕ → Fin (d + 1) → ℂ) (cf : Fin (d + 1) → ℂ)
    (hlim : ∀ i : Fin (d + 1), Filter.Tendsto (fun k : ℕ => c k i) Filter.atTop (nhds (cf i)))
    (r : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hroot : Polynomial.eval r (Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (cf i))) = 0)
    (hpunct : ∀ z : ℂ, z ∈ Metric.closedBall r ρ → z ≠ r →
      Polynomial.eval z (Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (cf i))) ≠ 0) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ w : ℂ, dist w r < ρ ∧
      Polynomial.eval w (Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (c k i))) = 0 := by
  classical
  set P : Polynomial ℂ := ∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (cf i)
  -- The limit polynomial has no roots on the boundary circle.
  have hsphere_ne : ∀ z : ℂ, z ∈ sphere r ρ → P.eval z ≠ 0 := by
    intro z hz
    apply hpunct z (Metric.sphere_subset_closedBall hz)
    intro hzr
    have hdist : dist z r = ρ := Metric.mem_sphere.mp hz
    rw [hzr] at hdist
    have : (0 : ℝ) = ρ := by simpa using hdist
    linarith
  -- positive lower bound for |P| on the circle
  obtain ⟨δ, hδ0, hδsphere⟩ := rrl_exists_pos_lower_bound_on_sphere P hρ hsphere_ne
  -- uniform closeness of the sequence on the circle
  have hBsphere : ∀ z : ℂ, z ∈ sphere r ρ → ‖z‖ ≤ ‖r‖ + ρ := by
    intro z hz
    have hzr : ‖z - r‖ = ρ := by
      simpa using hz
    calc
      ‖z‖ = ‖(z - r) + r‖ := by congr 1; abel
      _ ≤ ‖z - r‖ + ‖r‖ := norm_add_le _ _
      _ = ρ + ‖r‖ := by rw [hzr]
      _ ≤ ‖r‖ + ρ := by linarith
  have hev_sphere : ∀ᶠ k in atTop, ∀ z : ℂ, z ∈ sphere r ρ →
      ‖gch_qC d (c k) z - gch_qC d cf z‖ < δ / 2 := by
    exact gch_eventually_uniform_eval_sub_lt d c cf hlim (sphere r ρ) (B := ‖r‖ + ρ)
      hBsphere (δ / 2) (by positivity)
  -- closeness at the centre r
  have hB_r : ∀ z : ℂ, z ∈ ({r} : Set ℂ) → ‖z‖ ≤ ‖r‖ := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact le_rfl
  have hev_close_r : ∀ᶠ k in atTop, ‖gch_qC d (c k) r - gch_qC d cf r‖ < δ / 2 := by
    have h := gch_eventually_uniform_eval_sub_lt d c cf hlim ({r} : Set ℂ) (B := ‖r‖)
      hB_r (δ / 2) (by positivity)
    filter_upwards [h] with k hk
    exact hk r (by simp)
  -- eventually the value at r is small
  have hev_small_r : ∀ᶠ k in atTop, ‖gch_qC d (c k) r‖ < δ / 2 := by
    have hqf0 : gch_qC d cf r = 0 := by
      rw [← gch_eval_qC d cf r]
      simpa [P] using hroot
    filter_upwards [hev_close_r] with k hk
    have htri : ‖gch_qC d (c k) r‖ ≤ ‖gch_qC d (c k) r - gch_qC d cf r‖ + ‖gch_qC d cf r‖ := by
      simpa [sub_add_cancel] using
        (norm_add_le (gch_qC d (c k) r - gch_qC d cf r) (gch_qC d cf r))
    have htri' : ‖gch_qC d (c k) r - gch_qC d cf r‖ + ‖gch_qC d cf r‖ < δ / 2 := by
      rw [hqf0] at hk ⊢
      simpa using hk
    exact lt_of_le_of_lt htri htri'
  -- combine the two eventual properties
  have hev_all : ∀ᶠ k in atTop,
      (∀ z : ℂ, z ∈ sphere r ρ → ‖gch_qC d (c k) z - gch_qC d cf z‖ < δ / 2) ∧
        ‖gch_qC d (c k) r‖ < δ / 2 := by
    exact hev_sphere.and hev_small_r
  rw [Filter.eventually_atTop] at hev_all
  rcases hev_all with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  have hprops := hN k hk
  rcases hprops with ⟨hk_sphere, hk_small⟩
  -- the k-th polynomial
  let pk : Polynomial ℂ := ∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (c k i)
  have hcl_sphere : ∀ z : ℂ, z ∈ sphere r ρ → ‖pk.eval z - P.eval z‖ < δ / 2 := by
    intro z hz
    have h := hk_sphere z hz
    have h1 : gch_qC d (c k) z = pk.eval z := by
      exact (gch_eval_qC d (c k) z).symm
    have h2 : gch_qC d cf z = P.eval z := by
      exact (gch_eval_qC d cf z).symm
    rwa [h1, h2] at h
  have hsmall : ‖pk.eval r‖ < δ / 2 := by
    have h1 : gch_qC d (c k) r = pk.eval r := (gch_eval_qC d (c k) r).symm
    simpa [h1] using hk_small
  -- pk has no roots on the circle: |pk| ≥ δ/2 there
  have hpk_sphere_ne : ∀ z : ℂ, z ∈ sphere r ρ → pk.eval z ≠ 0 := by
    intro z hz hz0
    have hδz : δ ≤ ‖P.eval z‖ := hδsphere z hz
    have htri : ‖P.eval z‖ ≤ ‖P.eval z - pk.eval z‖ + ‖pk.eval z‖ := by
      simpa [sub_add_cancel] using (norm_add_le (P.eval z - pk.eval z) (pk.eval z))
    have hrev : ‖P.eval z - pk.eval z‖ < δ / 2 := by
      have := hcl_sphere z hz
      simpa [norm_sub_rev] using this
    have hsum_lt : ‖P.eval z - pk.eval z‖ + ‖pk.eval z‖ < δ / 2 := by
      have hpk0norm : ‖pk.eval z‖ = 0 := by
        simp [hz0]
      rw [hpk0norm, add_zero]
      exact hrev
    have hδlt : δ < δ / 2 := lt_of_le_of_lt (le_trans hδz htri) hsum_lt
    linarith
  -- transfer the root at r of P to a root of pk in the closed disk
  obtain ⟨w, hwball, hwroot⟩ := rrl_root_in_closedBall pk P r (ρ := ρ) (δ := δ)
    hρ hδ0 (by simpa [P] using hroot) hcl_sphere hsmall hδsphere
  -- the root cannot lie on the circle
  have hwnot : ¬ w ∈ sphere r ρ := by
    intro hwsphere
    exact hpk_sphere_ne w hwsphere (by simpa using hwroot)
  have hwnorm_lt : ‖w - r‖ < ρ := by
    have hle : ‖w - r‖ ≤ ρ := hwball
    have hne : ‖w - r‖ ≠ ρ := by
      intro h
      apply hwnot
      exact mem_sphere_iff_norm.mpr h
    exact lt_of_le_of_ne hle hne
  refine ⟨w, ?_, ?_⟩
  · rw [dist_eq_norm]
    exact hwnorm_lt
  · simpa [pk] using hwroot

end Commons.Analysis.MvPolynomial
