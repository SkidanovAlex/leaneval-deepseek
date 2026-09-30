import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.Analysis.Asymptotics.dyadicAnnulusTail

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Metric
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Commons.NumberTheory.Linnik

lemma log_four_ge_one : (1 : ℝ) ≤ Real.log 4 := by
  have he : Real.exp 1 ≤ (4 : ℝ) := by
    have h3 : Real.exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
    linarith
  have h := Real.log_le_log (Real.exp_pos 1) he
  simpa using h

lemma logN_nonneg {N : ℕ} [NeZero N] : 0 ≤ Real.log (N : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))

lemma partialFrac_term_norm_le {s u : ℂ} {R : ℝ} (hR : 2 ≤ R) (hs : ‖s‖ ≤ R / 4) (huR : R ≤ ‖u‖) :
    ‖(1 / (s - u) + 1 / u)‖ ≤ (4 / 3) * ‖s‖ / ‖u‖ ^ 2 := by
  have hu0 : u ≠ 0 := by
    intro h
    subst h
    norm_num at huR
    linarith
  have hRpos : 0 < R := by linarith
  have hupos : 0 < ‖u‖ := lt_of_lt_of_le hRpos huR
  have hden : (3 / 4) * ‖u‖ ≤ ‖s - u‖ := by
    have hsub : ‖u‖ - ‖s‖ ≤ ‖s - u‖ := by
      have h := abs_norm_sub_norm_le u s
      rw [norm_sub_rev] at h
      exact le_trans (le_abs_self _) h
    have hmain : (3 / 4 : ℝ) * ‖u‖ ≤ ‖u‖ - ‖s‖ := by
      nlinarith
    exact le_trans hmain hsub
  have hsune : s - u ≠ 0 := by
    intro hz
    have hz' : ‖s - u‖ = 0 := by simpa [hz]
    have hgt : 0 < ‖s - u‖ := by
      have h0 : 0 < (3 / 4) * ‖u‖ := by positivity
      exact lt_of_lt_of_le h0 hden
    linarith
  have hident : 1 / (s - u) + 1 / u = s / ((s - u) * u) := by
    field_simp [hu0, hsune]
    ring
  calc
    ‖(1 / (s - u) + 1 / u)‖ = ‖s / ((s - u) * u)‖ := by rw [hident]
    _ = ‖s‖ / (‖s - u‖ * ‖u‖) := by
        rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / ((3 / 4) * ‖u‖ * ‖u‖) := by
        have hdb : (3 / 4) * ‖u‖ * ‖u‖ ≤ ‖s - u‖ * ‖u‖ := by
          exact mul_le_mul_of_nonneg_right hden (norm_nonneg u)
        exact div_le_div₀ (norm_nonneg s) le_rfl (by positivity : 0 < (3/4) * ‖u‖ * ‖u‖) hdb
    _ = (4 / 3) * ‖s‖ / ‖u‖ ^ 2 := by
        field_simp

/-- Divisor on a set at a point outside the set is zero. -/
lemma divisor_eq_zero_of_nmem {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} (hz : z ∉ U) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_def]
  simp [hz]

/-- Divisor on a closed ball at a point inside the ball equals the order of the function. -/
lemma divisor_closedBall_eq_order {f : ℂ → ℂ} (hf : ∀ U : Set ℂ, MeromorphicOn f U)
    {ρ : ℝ} {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    MeromorphicOn.divisor f (closedBall 0 ρ) u = (meromorphicOrderAt f u).untop₀ := by
  exact MeromorphicOn.divisor_apply (hf (closedBall 0 ρ))
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)

/-- Divisors on two closed balls agree at points lying in both balls. -/
lemma divisor_closedBall_eq_of_le {f : ℂ → ℂ} (hf : ∀ U : Set ℂ, MeromorphicOn f U)
    {ρ₁ ρ₂ : ℝ} {u : ℂ} (hu₁ : ‖u‖ ≤ ρ₁) (hu₂ : ‖u‖ ≤ ρ₂) :
    MeromorphicOn.divisor f (closedBall 0 ρ₁) u = MeromorphicOn.divisor f (closedBall 0 ρ₂) u := by
  rw [divisor_closedBall_eq_order hf hu₁, divisor_closedBall_eq_order hf hu₂]

/-- Divisor on a closed ball at a point strictly outside the ball is zero. -/
lemma divisor_closedBall_eq_zero_of_lt_norm {f : ℂ → ℂ} {ρ : ℝ} {u : ℂ} (hu : ρ < ‖u‖) :
    MeromorphicOn.divisor f (closedBall 0 ρ) u = 0 := by
  exact divisor_eq_zero_of_nmem (by
    intro hmem
    have hle : ‖u‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
    linarith)

/-- For `0 < R` and any real `ρ`, some power `2^(j+1) R` reaches past `ρ`. -/
lemma exists_dyadic_ge (R ρ : ℝ) (hR : 0 < R) : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R := by
  by_cases hρ : ρ ≤ 0
  · refine ⟨0, ?_⟩
    norm_num
    nlinarith [hρ, hR]
  · have hρpos : 0 < ρ := lt_of_not_ge hρ
    rcases exists_nat_ge (ρ / R) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      have hlt1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_succ_self n)
      have hlt2 : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
        have hltn : (n + 1 : ℕ) < (2 : ℕ) ^ (n + 1) :=
          Nat.lt_pow_self (a := 2) (n := n + 1) (by norm_num : (1 : ℕ) < 2)
        exact_mod_cast (le_of_lt hltn)
      exact le_trans (le_of_lt hlt1) hlt2
    have hdiv : ρ ≤ (n : ℝ) * R := by
      rw [div_le_iff₀ hR] at hn
      simpa using hn
    calc
      ρ ≤ (n : ℝ) * R := hdiv
      _ ≤ (2 : ℝ) ^ (n + 1) * R := by
        exact mul_le_mul_of_nonneg_right hn2 (le_of_lt hR)

/-- Index of the dyadic annulus containing `ρ`: the least `j` with `ρ ≤ 2^(j+1) R`. -/
noncomputable def dyadIdx (R ρ : ℝ) (hρ : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R) : ℕ :=
  Nat.find hρ

lemma dyadIdx_spec_le (R ρ : ℝ) (hρ : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R) :
    ρ ≤ (2 : ℝ) ^ (dyadIdx R ρ hρ + 1) * R := by
  simpa [dyadIdx] using Nat.find_spec hρ

lemma dyadIdx_le_of (R ρ : ℝ) (hρ : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R) {K : ℕ}
    (hK : ρ ≤ (2 : ℝ) ^ (K + 1) * R) : dyadIdx R ρ hρ ≤ K := by
  simpa [dyadIdx] using Nat.find_min' hρ hK

lemma dyadIdx_lower {R ρ : ℝ} (hρ : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R) (hRρ : R < ρ) :
    (2 : ℝ) ^ dyadIdx R ρ hρ * R < ρ := by
  by_contra hnot
  have hle : ρ ≤ (2 : ℝ) ^ dyadIdx R ρ hρ * R := by
    rw [not_lt] at hnot
    exact hnot
  by_cases hj : dyadIdx R ρ hρ = 0
  · have hle0 : ρ ≤ R := by simpa [hj] using hle
    linarith
  · obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hw : ρ ≤ (2 : ℝ) ^ (j' + 1) * R := by
      simpa [hj'] using hle
    have hmin := Nat.find_min' hρ hw
    have hjle : dyadIdx R ρ hρ ≤ j' := by simpa [dyadIdx] using hmin
    omega

lemma Finset.sum_eq_sum_image_filter {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (s : Finset ι) (g : ι → ℕ) (f : ι → M) :
    (∑ i ∈ s, f i) = ∑ k ∈ s.image g, ∑ i ∈ s.filter (fun i => g i = k), f i := by
  let t : Finset ℕ := s.image g
  calc
    (∑ i ∈ s, f i) = ∑ i ∈ s, (∑ k ∈ t, if g i = k then f i else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hgi : g i ∈ t := by
          dsimp [t]
          exact Finset.mem_image_of_mem g hi
        rw [Finset.sum_ite_eq]
        simp [hgi]
    _ = ∑ k ∈ t, ∑ i ∈ s, (if g i = k then f i else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ k ∈ t, ∑ i ∈ s.filter (fun i => g i = k), f i := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [Finset.sum_filter]

/-- Splitting the logarithm of a dyadic quantity. -/
lemma log_two_pow_mul_add_two_le {R : ℝ} (hR : 2 ≤ R) (k : ℕ) :
    Real.log ((2 : ℝ) ^ (k + 1) * R + 2) ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (R + 2) := by
  have h1 : 0 < ((2 : ℝ) ^ (k + 1) * R + 2) := by positivity
  have hle0 : 2 ≤ (2 : ℝ) ^ (k + 1) * 2 := by
    have h4 : (2 : ℝ) * 2 ≤ (2 : ℝ) ^ (k + 1) * 2 :=
      mul_le_mul_of_nonneg_right (by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by omega : (1 : ℕ) ≤ k + 1)
        simpa using this) (by norm_num : (0 : ℝ) ≤ 2)
    exact le_trans (by norm_num : (2 : ℝ) ≤ 2 * 2) h4
  have hle : (2 : ℝ) ^ (k + 1) * R + 2 ≤ (2 : ℝ) ^ (k + 1) * (R + 2) := by
    calc
      (2 : ℝ) ^ (k + 1) * R + 2 ≤ (2 : ℝ) ^ (k + 1) * R + (2 : ℝ) ^ (k + 1) * 2 :=
        add_le_add_right hle0 ((2 : ℝ) ^ (k + 1) * R)
      _ = (2 : ℝ) ^ (k + 1) * (R + 2) := by ring
  have hlog := Real.log_le_log h1 hle
  have hmul := Real.log_mul (pow_ne_zero (k + 1) (by norm_num : (2 : ℝ) ≠ 0)) (by nlinarith : R + 2 ≠ 0)
  rw [hmul] at hlog
  have hpow := Real.log_pow (2 : ℝ) (k + 1)
  rw [hpow] at hlog
  simpa using hlog


/-- Squaring the dyadic annulus bounds: `4^j R^2 ≤ ρ^2` when `2^j R < ρ`. -/
lemma dyadIdx_sq_le {R ρ : ℝ} (hR : 0 < R)
    (hρ : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R) (hRρ : R < ρ) :
    (4 : ℝ) ^ dyadIdx R ρ hρ * R ^ 2 ≤ ρ ^ 2 := by
  let j : ℕ := dyadIdx R ρ hρ
  have hl : (2 : ℝ) ^ j * R < ρ := by simpa [j] using (dyadIdx_lower hρ hRρ)
  have h0l : 0 ≤ (2 : ℝ) ^ j * R := by positivity
  have h0ρ : 0 ≤ ρ := le_of_lt (lt_trans hR hRρ)
  have hsq := (sq_le_sq₀ h0l h0ρ).2 (le_of_lt hl)
  have hrew : ((2 : ℝ) ^ j * R) ^ 2 = (4 : ℝ) ^ j * R ^ 2 := by
    rw [mul_pow]
    have hp : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
      calc
        ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (j * 2) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (2 * j) := by congr 1; omega
        _ = ((2 : ℝ) ^ 2) ^ j := by rw [pow_mul]
        _ = (4 : ℝ) ^ j := by norm_num
    rw [hp]
  have hsq' : (4 : ℝ) ^ j * R ^ 2 ≤ ρ ^ 2 := by
    rwa [← hrew]
  simpa [j] using hsq'

/-- Inverted square bound at the dyadic level. -/
lemma dyadIdx_inv_sq_le {R ρ : ℝ} (hR : 0 < R)
    (hρ : ∃ j : ℕ, ρ ≤ (2 : ℝ) ^ (j + 1) * R) (hRρ : R < ρ) :
    1 / ρ ^ 2 ≤ 1 / ((4 : ℝ) ^ dyadIdx R ρ hρ * R ^ 2) := by
  have hle := dyadIdx_sq_le (R := R) (ρ := ρ) hR hρ hRρ
  have h0ρ : 0 < ρ := lt_trans hR hRρ
  have hd1 : 0 < (4 : ℝ) ^ dyadIdx R ρ hρ * R ^ 2 := by
    exact mul_pos (pow_pos (by norm_num : (0 : ℝ) < 4) _) (sq_pos_of_pos hR)
  have hd2 : 0 < ρ ^ 2 := sq_pos_of_pos h0ρ
  exact one_div_le_one_div_of_le hd1 hle

lemma pow_two_ratio (k : ℕ) : (2 : ℝ) ^ (k + 1) / (4 : ℝ) ^ k = 2 / (2 : ℝ) ^ k := by
  have hk2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)
  have hk4 : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)
  field_simp [hk2, hk4]
  calc
    (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k = (2 : ℝ) ^ ((k + 1) + k) := by rw [← pow_add]
    _ = (2 : ℝ) ^ (2 * k + 1) := by rw [show ((k + 1) + k : ℕ) = 2 * k + 1 by omega]
    _ = (2 : ℝ) ^ (2 * k) * 2 := by rw [pow_succ]
    _ = 2 * (2 : ℝ) ^ (2 * k) := by rw [mul_comm]
    _ = 2 * ((2 : ℝ) ^ 2) ^ k := by rw [← pow_mul]
    _ = 2 * (4 : ℝ) ^ k := by rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    _ = (4 : ℝ) ^ k * 2 := by rw [mul_comm]

lemma dyadic_weight_eq {C M R B : ℝ} (hR : R ≠ 0) (j : ℕ) :
    C * (2 : ℝ) ^ (j + 1) * R * (((j + 1 : ℕ) : ℝ) * B) * (M / ((4 : ℝ) ^ j * R ^ 2))
      = (2 * C * M / R) * B * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j)) := by
  calc
    C * (2 : ℝ) ^ (j + 1) * R * (((j + 1 : ℕ) : ℝ) * B) * (M / ((4 : ℝ) ^ j * R ^ 2))
        = (C * M * B * (((j + 1 : ℕ) : ℝ)) * ((2 : ℝ) ^ (j + 1) / (4 : ℝ) ^ j)) / R := by
            field_simp [hR, pow_ne_zero j (by norm_num : (4 : ℝ) ≠ 0)]
    _ = (C * M * B * (((j + 1 : ℕ) : ℝ)) * (2 / (2 : ℝ) ^ j)) / R := by rw [pow_two_ratio j]
    _ = (2 * C * M / R) * B * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j)) := by
            have hpow : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := one_div_pow (2 : ℝ) j
            rw [hpow]
            field_simp [hR, pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0)]

/-- The main theorem: difference of partial-fraction-type divisor sums over two balls. -/
theorem partialFraction_tail {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ s : ℂ, ∀ R R' : ℝ, 2 ≤ R → R ≤ R' → ‖s‖ ≤ R / 4 →
      ‖(∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R')) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))‖ ≤
        c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U z hz
    exact hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  have hdiv_nonneg : ∀ U u, 0 ≤ (MeromorphicOn.divisor Λ U) u := by
    intro U u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan U) u
  rcases Commons.NumberTheory.Linnik.completedL_zeroCount χ hχ hχprim with ⟨zc, hzc⟩
  let C : ℝ := max zc 0
  have hC0 : 0 ≤ C := by dsimp [C]; exact le_max_right zc 0
  have hzcC : ∀ (ρ : ℝ), 2 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall 0 ρ)) u : ℤ) : ℝ)) ≤
        C * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by
    intro ρ hρ
    have h1 := hzc ρ hρ
    have hT0 : 0 ≤ Real.log (ρ + 2) + Real.log (N : ℝ) + 2 := by
      have h1 : 0 ≤ Real.log (ρ + 2) := by exact Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
      linarith
    have hρ0 : 0 ≤ ρ := by linarith
    have hzcC' : zc * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) ≤
        C * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by
      have hCge : zc ≤ C := by dsimp [C]; exact le_max_left zc 0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge hρ0) hT0
    exact le_trans h1 hzcC'
  refine ⟨128 * C, ?_⟩
  intro s R R' hR hRR' hs
  let w : ℂ → ℂ := fun u => 1 / (s - u) + 1 / u
  let m : ℝ → ℂ → ℤ := fun ρ u => MeromorphicOn.divisor Λ (closedBall 0 ρ) u
  let F : ℝ → ℂ := fun ρ => ∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℂ) * w u)
  -- finite support finsets
  have hfin (ρ : ℝ) : (m ρ).support.Finite := by
    dsimp [m]
    exact (MeromorphicOn.divisor Λ (closedBall 0 ρ)).finiteSupport (isCompact_closedBall (0 : ℂ) ρ)
  let S : Finset ℂ := (hfin R').toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ m R' u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hRpos : 0 < R := by linarith
  have hR'_ge_R : R ≤ R' := hRR'
  -- rewrite F into finite sums over S
  have hF' : F R' = ∑ u ∈ S, (((m R' u : ℤ) : ℂ) * w u) := by
    dsimp [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R' u ≠ 0 := by
      intro hz
      apply hu
      simp [hz]
    exact (hS_mem u).mpr hm
  have hF : F R = ∑ u ∈ S, (((m R u : ℤ) : ℂ) * w u) := by
    dsimp [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R u ≠ 0 := by
      intro hz
      apply hu
      simp [hz]
    have huB : u ∈ closedBall 0 R := (MeromorphicOn.divisor Λ (closedBall 0 R)).supportWithinDomain hm
    have hle : ‖u‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hEq : m R u = m R' u := by
      dsimp [m]
      exact divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := R) (ρ₂ := R') hle (le_trans hle hRR')
    have hm' : m R' u ≠ 0 := by rwa [← hEq]
    exact (hS_mem u).mpr hm'
  -- difference
  have hD : F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) := by
    rw [hF', hF]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro u hu
    simp [Int.cast_sub, sub_mul]
  -- collapse to the annulus R < |u|
  let T : Finset ℂ := S.filter (fun u => R < ‖u‖)
  have hDcoll : F R' - F R = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := by
    have hstep : ∀ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) =
        if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0 := by
      intro u huS
      by_cases hbig : R < ‖u‖
      · have hmR0 : m R u = 0 := by
          dsimp [m]
          exact divisor_closedBall_eq_zero_of_lt_norm (f := Λ) hbig
        simp [hbig, hmR0]
      · have hle : ‖u‖ ≤ R := le_of_not_gt hbig
        have hEq : m R u = m R' u := by
          dsimp [m]
          exact divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := R) (ρ₂ := R') hle (le_trans hle hRR')
        simp [hbig, hEq]
    calc
      F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) := hD
      _ = ∑ u ∈ S, (if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hstep u hu
      _ = ∑ u ∈ S.filter (fun u => R < ‖u‖), (((m R' u : ℤ) : ℂ) * w u) := by
          rw [Finset.sum_filter]
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := rfl
  -- norm bound
  have hnorm : ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := by
    rw [hDcoll]
    exact norm_sum_le T (fun u => (((m R' u : ℤ) : ℂ) * w u))
  have hterm : ∀ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ = (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    intro u huT
    have hm0 : 0 ≤ m R' u := hdiv_nonneg (closedBall 0 R') u
    rw [norm_mul, Complex.norm_int_of_nonneg hm0]
  have hnorm2 : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := hnorm
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hterm u hu
  have hwu : ∀ u ∈ T, ‖w u‖ ≤ (4 / 3) * ‖s‖ / ‖u‖ ^ 2 := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    exact partialFrac_term_norm_le (s := s) (u := u) (R := R) hR hs (le_of_lt hbig)
  have hbnd : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ((4 / 3) * ‖s‖ / ‖u‖ ^ 2)) := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := hnorm2
      _ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ((4 / 3) * ‖s‖ / ‖u‖ ^ 2)) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          have hm0 : 0 ≤ ((m R' u : ℤ) : ℝ) := by exact_mod_cast (hdiv_nonneg (closedBall 0 R') u)
          exact mul_le_mul_of_nonneg_left (hwu u huT) hm0
  let M : ℝ := (4 / 3) * ‖s‖
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  let jl : ℂ → ℕ := fun u => dyadIdx R ‖u‖ (exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_spec_le : ∀ u : ℂ, ‖u‖ ≤ (2 : ℝ) ^ (jl u + 1) * R := by
    intro u
    dsimp [jl]
    exact dyadIdx_spec_le R ‖u‖ (exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_lower : ∀ u : ℂ, R < ‖u‖ → (2 : ℝ) ^ jl u * R < ‖u‖ := by
    intro u hu
    dsimp [jl]
    exact dyadIdx_lower (exists_dyadic_ge R ‖u‖ hRpos) hu
  rcases exists_dyadic_ge R R' hRpos with ⟨K, hK⟩
  have hjl_le_K : ∀ u ∈ T, jl u ≤ K := by
    intro u huT
    have hmem := Finset.mem_filter.mp huT
    have hbig : R < ‖u‖ := hmem.2
    have huS : u ∈ S := hmem.1
    have hm : m R' u ≠ 0 := (hS_mem u).mp huS
    have huB : u ∈ closedBall 0 R' := (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm
    have huR' : ‖u‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hK' : ‖u‖ ≤ (2 : ℝ) ^ (K + 1) * R := le_trans huR' hK
    dsimp [jl]
    exact dyadIdx_le_of R ‖u‖ (exists_dyadic_ge R ‖u‖ hRpos) hK'
  let Tj : ℕ → Finset ℂ := fun j => S.filter (fun u => (2 : ℝ) ^ j * R < ‖u‖ ∧ ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R)
  let b : ℕ → ℝ := fun j => ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ)
  let c : ℂ → ℝ := fun u => ((m R' u : ℤ) : ℝ)
  have hc0 : ∀ u, 0 ≤ c u := by
    intro u
    dsimp [c]
    exact_mod_cast (hdiv_nonneg (closedBall 0 R') u)
  have hc_eq : ∀ u, c u = ((m R' u : ℤ) : ℝ) := by intro u; rfl
  -- (a) pointwise weight bound at the level of u
  have hwM : ∀ u ∈ T, M / ‖u‖ ^ 2 ≤ M / (((4 : ℝ) ^ jl u) * R ^ 2) := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hsq := dyadIdx_sq_le (R := R) (ρ := ‖u‖) hRpos (exists_dyadic_ge R ‖u‖ hRpos) hbig
    have hy0 : 0 < (4 : ℝ) ^ jl u * R ^ 2 := by positivity
    exact div_le_div₀ hM0 le_rfl hy0 hsq
  have hw1 : ∀ u ∈ T, c u * (M / ‖u‖ ^ 2) ≤ c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)) := by
    intro u huT
    exact mul_le_mul_of_nonneg_left (hwM u huT) (hc0 u)
  have hc_def (u : ℂ) : c u = ((m R' u : ℤ) : ℝ) := rfl
  have hbndM : ‖F R' - F R‖ ≤ ∑ u ∈ T, (c u * (M / ‖u‖ ^ 2)) := by
    simpa [c, M] using hbnd
  -- (b) split into dyadic fibres
  let Afib : ℕ → ℝ := fun j => ∑ u ∈ T.filter (fun u => jl u = j), (c u * (M / (((4 : ℝ) ^ j) * R ^ 2)))
  have hfib_le_Tj : ∀ j : ℕ, T.filter (fun u => jl u = j) ⊆ Tj j := by
    intro j
    intro u hu
    have hmem := Finset.mem_filter.mp hu
    have huT : u ∈ T := hmem.1
    have hEq : jl u = j := hmem.2
    have hS' : u ∈ S := (Finset.mem_filter.mp huT).1
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hlow' : (2 : ℝ) ^ jl u * R < ‖u‖ := hjl_lower u hbig
    have hlow : (2 : ℝ) ^ j * R < ‖u‖ := by simpa [hEq] using hlow'
    have hup : ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R := by
      simpa [hEq] using hjl_spec_le u
    exact Finset.mem_filter.mpr ⟨hS', ⟨hlow, hup⟩⟩
  have hfib_b : ∀ j : ℕ, (∑ u ∈ T.filter (fun u => jl u = j), c u) ≤ b j := by
    intro j
    dsimp [b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hfib_le_Tj j)
      (fun u huTj hnot => hc0 u)
  have hpart : (∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)))) =
      ∑ j ∈ Finset.range (K + 1), Afib j := by
    have hpf := Finset.sum_eq_sum_image_filter (s := T) (g := jl)
      (f := fun u => c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)))
    have himg : T.image jl ⊆ Finset.range (K + 1) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨u, huT, hEq⟩
      have hle : j ≤ K := by simpa [hEq] using (hjl_le_K u huT)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
    calc
      (∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2))))
          = ∑ j ∈ T.image jl, ∑ u ∈ T.filter (fun u => jl u = j),
              (c u * (M / (((4 : ℝ) ^ j) * R ^ 2))) := by
              rw [hpf]
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro u hu
              have hEq : jl u = j := (Finset.mem_filter.mp hu).2
              simp [hEq]
      _ = ∑ j ∈ T.image jl, Afib j := rfl
      _ = ∑ j ∈ Finset.range (K + 1), Afib j := by
          refine Finset.sum_subset himg ?_
          intro j hj hnot
          -- j ∉ image: the fibre filter is empty
          have hfib_empty : (T.filter (fun u => jl u = j)) = ∅ := by
            ext u
            constructor
            · intro hu
              have hmem2 := Finset.mem_filter.mp hu
              exact False.elim (hnot (Finset.mem_image.mpr ⟨u, hmem2.1, hmem2.2⟩))
            · intro hu
              simp at hu
          simp [Afib, hfib_empty]
  have hweight : ∀ j : ℕ, 0 ≤ M / (((4 : ℝ) ^ j) * R ^ 2) := by
    intro j
    exact div_nonneg hM0 (by positivity)
  have hfib_nonneg : ∀ j : ℕ, 0 ≤ ∑ u ∈ T.filter (fun u => jl u = j), c u := by
    intro j
    exact Finset.sum_nonneg (fun u hu => hc0 u)
  -- (c) the tail bound via dyadicAnnulusTail
  let L : ℝ := Real.log (N : ℝ) + 2
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have h1 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
    linarith
  -- count bound for each dyadic annulus
  have hb_le : ∀ j : ℕ, b j ≤ C * (2 : ℝ) ^ (j + 1) * R *
      (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L) := by
    intro j
    let ρ : ℝ := (2 : ℝ) ^ (j + 1) * R
    have hρ2 : 2 ≤ ρ := by
      dsimp [ρ]
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by omega : (1 : ℕ) ≤ j + 1)
        simpa using this
      nlinarith
    have hρ0 : 0 ≤ ρ := by linarith
    let Sρ : Finset ℂ := (hfin ρ).toFinset
    have hSρ_mem : ∀ u : ℂ, u ∈ Sρ ↔ m ρ u ≠ 0 := by
      intro u
      dsimp [Sρ]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hcount : (∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ)) ≤ C * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by
      have hc1 := hzcC ρ hρ2
      -- convert finsum count to the finite sum over Sρ
      have hc2 : (∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℝ))) = ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Function.mem_support] at hu
        have hm : m ρ u ≠ 0 := by
          intro hz
          apply hu
          simp [hz]
        exact (hSρ_mem u).mpr hm
      rwa [hc2] at hc1
    -- b j ≤ the count over Sρ
    have hb_le_count : b j ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
      -- map each u ∈ Tj j to its value mρu = mR'u, subset Sρ
      have hEq_val : ∀ u ∈ Tj j, m ρ u = m R' u := by
        intro u huTj
        have hmem := Finset.mem_filter.mp huTj
        have huS : u ∈ S := hmem.1
        have hbounds := hmem.2
        have huρ : ‖u‖ ≤ ρ := by
          dsimp [ρ]
          exact hbounds.2
        have huR' : ‖u‖ ≤ R' := by
          have hm' : m R' u ≠ 0 := (hS_mem u).mp huS
          have huB : u ∈ closedBall 0 R' :=
            (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm'
          simpa [Metric.mem_closedBall, dist_eq_norm] using huB
        dsimp [m]
        exact divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := ρ) (ρ₂ := R') huρ huR'
      have hsub : Tj j ⊆ Sρ := by
        intro u huTj
        have hmem := Finset.mem_filter.mp huTj
        have huρ : ‖u‖ ≤ ρ := by
          dsimp [ρ]
          exact hmem.2.2
        have hm' : m R' u ≠ 0 := (hS_mem u).mp hmem.1
        have hmρ : m ρ u ≠ 0 := by
          rw [hEq_val u huTj]
          exact hm'
        exact (hSρ_mem u).mpr hmρ
      calc
        b j = ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ) := by rfl
        _ = ∑ u ∈ Tj j, ((m ρ u : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro u huTj
            rw [hEq_val u huTj]
        _ ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun u huSρ hnot => by
                exact_mod_cast (hdiv_nonneg (closedBall 0 ρ) u))
    calc
      b j ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := hb_le_count
      _ ≤ C * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := hcount
      _ = C * (2 : ℝ) ^ (j + 1) * R * (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L) := by
          dsimp [ρ, L]
          ring
  have hb0 : ∀ j : ℕ, 0 ≤ b j := by
    intro j
    dsimp [b]
    exact Finset.sum_nonneg (fun u hu => hc0 u)
  let G : ℝ := (2 * C * M / R) * (1 + Real.log (R + 2) + L)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    have h1 : 0 ≤ 2 * C * M / R := by positivity
    have h2 : 0 ≤ 1 + Real.log (R + 2) + L := by
      have h : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      linarith
    positivity
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogR0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hsum_dyadic : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1 / 2 : ℝ))
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    simpa [Nat.choose_one_right] using h.summable
  have hsummable : Summable (fun j : ℕ => b j * (M / ((4 : ℝ) ^ j * R ^ 2))) := by
    refine Summable.of_nonneg_of_le (g := fun j : ℕ => b j * (M / ((4 : ℝ) ^ j * R ^ 2)))
      (f := fun j : ℕ => G * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j))) ?_ ?_ ?_
    · intro j
      exact mul_nonneg (hb0 j) (div_nonneg hM0 (by positivity : 0 ≤ (4 : ℝ) ^ j * R ^ 2))
    · intro j
      have hX : Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L ≤
          ((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L) := by
        have hlog := log_two_pow_mul_add_two_le hR j
        have hA : ((j + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (R + 2) + L ≤
            ((j + 1 : ℕ) : ℝ) + Real.log (R + 2) + L := by
          have hm : ((j + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((j + 1 : ℕ) : ℝ) := by
            have hjp : 0 ≤ ((j + 1 : ℕ) : ℝ) := by positivity
            calc
              ((j + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((j + 1 : ℕ) : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left hlog2le1 hjp
              _ = ((j + 1 : ℕ) : ℝ) := by ring
          linarith
        have hC : ((j + 1 : ℕ) : ℝ) + Real.log (R + 2) + L ≤
            ((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L) := by
          have hjp : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos j)
          nlinarith
        exact le_trans (le_trans (add_le_add_left hlog L) hA) hC
      have hb'' : b j ≤ C * (2 : ℝ) ^ (j + 1) * R *
          (((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L)) := by
        exact le_trans (hb_le j)
          (mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ C * (2 : ℝ) ^ (j + 1) * R))
      calc
        b j * (M / ((4 : ℝ) ^ j * R ^ 2))
            ≤ (C * (2 : ℝ) ^ (j + 1) * R * (((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L))) *
                (M / ((4 : ℝ) ^ j * R ^ 2)) := by
                exact mul_le_mul_of_nonneg_right hb''
                  (div_nonneg hM0 (by positivity : 0 ≤ (4 : ℝ) ^ j * R ^ 2))
        _ = G * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j)) := by
            have hw := dyadic_weight_eq (C := C) (M := M) (R := R)
              (B := 1 + Real.log (R + 2) + L) (ne_of_gt hRpos) j
            dsimp [G]
            rw [← hw]
    · exact Summable.mul_left G hsum_dyadic

  have hpartial : (∑ j ∈ Finset.range (K + 1), b j * (M / ((4 : ℝ) ^ j * R ^ 2))) ≤
      ∑' j : ℕ, b j * (M / ((4 : ℝ) ^ j * R ^ 2)) := by
    exact Summable.sum_le_tsum (Finset.range (K + 1))
      (fun i hi => by
        -- nonneg for i outside range (i.e. i ≥ K+1)
        exact mul_nonneg (hb0 i) (by positivity : 0 ≤ M / ((4 : ℝ) ^ i * R ^ 2)))
      hsummable
  have htail := Commons.Analysis.Asymptotics.dyadicAnnulusTail (C := C) (R := R) (M := M) (L := L)
    hC0 hR hM0 hL0 b hb0 hb_le
  -- assemble the finite dyadic bound
  have hdybnd : (∑ u ∈ T, (c u * (M / ‖u‖ ^ 2))) ≤
      64 * C * M * (Real.log (R + 2) + L + 1) / R := by
    calc
      (∑ u ∈ T, (c u * (M / ‖u‖ ^ 2))) ≤ ∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2))) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          exact hw1 u huT
      _ = ∑ j ∈ Finset.range (K + 1), Afib j := hpart
      _ = ∑ j ∈ Finset.range (K + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) *
          (∑ u ∈ T.filter (fun u => jl u = j), c u) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          dsimp [Afib]
          -- factor the weight out
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro u hu
          ring
      _ ≤ ∑ j ∈ Finset.range (K + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) * b j := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left (hfib_b j) (hweight j)
      _ = ∑ j ∈ Finset.range (K + 1), b j * (M / (((4 : ℝ) ^ j) * R ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
      _ ≤ ∑' j : ℕ, b j * (M / ((4 : ℝ) ^ j * R ^ 2)) := hpartial
      _ ≤ 64 * C * M * (Real.log (R + 2) + L + 1) / R := htail
  -- final real arithmetic
  let Tlog : ℝ := Real.log (R + 2) + Real.log (N : ℝ) + 2
  have hT2 : 2 ≤ Tlog := by
    dsimp [Tlog]
    have h1 : 0 ≤ Real.log (R + 2) := hlogR0
    have h2 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
    linarith
  have hT0 : 0 ≤ Tlog := by linarith
  have hfrac : (64 : ℝ) * (4 / 3) * (Tlog + 1) ≤ 128 * Tlog := by
    nlinarith
  have hconst : (64 : ℝ) * C * M * (Tlog + 1) ≤ (128 * C) * ‖s‖ * Tlog := by
    have hfrac' : (64 : ℝ) * (4 / 3 : ℝ) * (Tlog + 1) ≤ 128 * Tlog := by
      nlinarith
    dsimp [M]
    have hstep : 64 * (4 / 3 : ℝ) * ‖s‖ * (Tlog + 1) ≤ 128 * ‖s‖ * Tlog := by
      have hm := mul_le_mul_of_nonneg_right hfrac' hs0
      nlinarith
    have hstepC : C * (64 * (4 / 3 : ℝ) * ‖s‖ * (Tlog + 1)) ≤ C * (128 * ‖s‖ * Tlog) :=
      mul_le_mul_of_nonneg_left hstep hC0
    nlinarith
  have hgoal : ‖F R' - F R‖ ≤ (128 * C) * ‖s‖ * Tlog / R := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, (c u * (M / ‖u‖ ^ 2)) := hbndM
      _ ≤ 64 * C * M * (Real.log (R + 2) + L + 1) / R := hdybnd
      _ = 64 * C * M * (Tlog + 1) / R := by
          dsimp [Tlog, L]
          ring
      _ ≤ (128 * C) * ‖s‖ * Tlog / R := by
          have hdiv := div_le_div_of_nonneg_right hconst (le_of_lt hRpos)
          simpa [M] using hdiv
  simpa [F, w, m, Tlog] using hgoal


end Commons.NumberTheory.Linnik
