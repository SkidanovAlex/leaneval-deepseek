import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc
import Submission.Commons.NumberTheory.DirichletPolynomial.smooth_range_localization_variable
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length

/-!
# The pairwise (Kerr) reflection `lem:main1` assembled from the commons
-/

namespace Work.GM.HB

open Finset
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

/-- The Dirichlet block `Σ_{A ≤ n ≤ B} n^{iθ}/√n`. -/
def hbm (A B : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc A B, (n : ℂ) ^ (Complex.I * ((θ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)

lemma hbm_term_conj {n : ℕ} (hn : 1 ≤ n) (σ : ℝ) :
    starRingEnd ℂ ((n : ℂ) ^ (Complex.I * (σ : ℂ)))
      = (n : ℂ) ^ (Complex.I * ((-σ : ℝ) : ℂ)) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    have h : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Ne.symm Real.pi_ne_zero
  have h2 := Complex.cpow_conj (n : ℂ) (Complex.I * (σ : ℂ)) harg
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast] at h2
  rw [← h2]
  congr 1
  push_cast
  ring

lemma hbm_neg_eq_conj {A B : ℕ} (hA : 1 ≤ A) (σ : ℝ) :
    hbm A B (-σ) = starRingEnd ℂ (hbm A B σ) := by
  rw [hbm, hbm, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := le_trans hA (Finset.mem_Icc.mp hn).1
  rw [map_div₀, Complex.conj_ofReal, hbm_term_conj hn1 σ]

lemma hbm_norm_neg (A B : ℕ) (hA : 1 ≤ A) (σ : ℝ) : ‖hbm A B (-σ)‖ = ‖hbm A B σ‖ := by
  rw [hbm_neg_eq_conj hA σ, Complex.norm_conj]

/-- Norms are unchanged by replacing the frequency by its absolute value. -/
lemma hbm_norm_abs {A B : ℕ} (hA : 1 ≤ A) (θ : ℝ) : ‖hbm A B θ‖ = ‖hbm A B |θ|‖ := by
  rcases abs_choice θ with h | h
  · rw [h]
  · rw [h]
    exact (hbm_norm_neg A B hA θ).symm

/-- The honest dual range is dominated by the enlarged range. -/
lemma hbm_sub_le (c₁ c₂ : ℕ) (θ : ℝ) : ‖hbm c₁ c₂ θ‖ ≤ ‖hbm c₁ (max c₁ c₂) θ‖ := by
  rcases lt_or_ge c₂ c₁ with h | h
  · have hempty : hbm c₁ c₂ θ = 0 := by
      rw [hbm]
      apply Finset.sum_eq_zero
      intro n hn
      exfalso
      simp only [Finset.mem_Icc] at hn
      omega
    rw [hempty, norm_zero, max_eq_left h.le]; positivity
  · rw [max_eq_right h]

/-- Range bookkeeping for the main regime `Δ ≥ 100N`. -/
lemma hbm_range_facts {N : ℕ} (hN : 1 ≤ N) {Δ θ : ℝ} (hN100 : 100 * (N:ℝ) ≤ Δ)
    (hθ1 : Δ ≤ |θ|) (hθ2 : |θ| ≤ 2 * Δ) :
    let A₀ : ℕ := Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))
    let M₁ : ℕ := Nat.ceil (Δ / (2 * (N:ℝ)))
    let B₂ : ℕ := 2 * Nat.ceil (Δ / (N:ℝ))
    let a₁ : ℕ := Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ)))
    let b₁ : ℕ := Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))
    (1 ≤ A₀ ∧ A₀ ≤ a₁ ∧ max a₁ b₁ ≤ 4 * A₀ ∧ 2 * A₀ ≤ M₁ ∧ 4 * A₀ ≤ M₁ ∧
      2 * M₁ ≤ B₂ ∧ M₁ ≤ B₂) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hΔpos : (0:ℝ) < Δ := by nlinarith
  have hA₀ge1 : 1 ≤ Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) :=
    Nat.ceil_pos.mpr (by positivity)
  have hmono : Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) ≤ Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))) :=
    Nat.ceil_mono (div_le_div_of_nonneg_right hθ1 (by positivity))
  have hA₀le : Δ / (4 * Real.pi * (N:ℝ)) ≤ ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ) :=
    Nat.le_ceil _
  have hA₀lt : ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ) < Δ / (4 * Real.pi * (N:ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hM₁ge : Δ / (2 * (N:ℝ)) ≤ ((Nat.ceil (Δ / (2 * (N:ℝ)))):ℝ) := Nat.le_ceil _
  have hC1 : Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ)))
      ≤ 4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) := by
    apply Nat.ceil_le.mpr
    have h1 : |θ| / (4 * Real.pi * (N:ℝ)) ≤ 2 * Δ / (4 * Real.pi * (N:ℝ)) :=
      div_le_div_of_nonneg_right hθ2 (by positivity)
    have h2 : 2 * Δ / (4 * Real.pi * (N:ℝ)) = Δ / (2 * Real.pi * (N:ℝ)) := by
      field_simp
      try ring
    have h3 : Δ / (2 * Real.pi * (N:ℝ)) ≤ Δ / (Real.pi * (N:ℝ)) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [Real.pi_pos])
    have h4 : Δ / (Real.pi * (N:ℝ)) ≤ 4 * (Δ / (4 * Real.pi * (N:ℝ))) := by
      rw [show 4 * (Δ / (4 * Real.pi * (N:ℝ))) = Δ / (Real.pi * (N:ℝ)) by field_simp; try ring]
    have h5 : 4 * (Δ / (4 * Real.pi * (N:ℝ)))
        ≤ 4 * ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ) := by linarith [hA₀le]
    have h6 : ((4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) : ℕ):ℝ)
        = 4 * ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ) := by push_cast; ring
    rw [h6]; linarith
  have hC2 : Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))
      ≤ 4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) := by
    have h1 : |θ| / (2 * Real.pi * (N:ℝ)) ≤ 2 * Δ / (2 * Real.pi * (N:ℝ)) :=
      div_le_div_of_nonneg_right hθ2 (by positivity)
    have h2 : 2 * Δ / (2 * Real.pi * (N:ℝ)) = Δ / (Real.pi * (N:ℝ)) := by field_simp; try ring
    have h3 : Δ / (Real.pi * (N:ℝ)) ≤ 4 * (Δ / (4 * Real.pi * (N:ℝ))) := by
      rw [show 4 * (Δ / (4 * Real.pi * (N:ℝ))) = Δ / (Real.pi * (N:ℝ)) by field_simp; try ring]
    have h4 : ((Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))):ℝ) ≤ |θ| / (2 * Real.pi * (N:ℝ)) :=
      Nat.floor_le (by positivity)
    have h5 : 4 * (Δ / (4 * Real.pi * (N:ℝ)))
        ≤ 4 * ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ) := by linarith [hA₀le]
    have h6 : ((4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) : ℕ):ℝ)
        = 4 * ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ) := by push_cast; ring
    have h7 : ((Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))):ℝ)
        ≤ ((4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) : ℕ):ℝ) := by rw [h6]; linarith
    exact_mod_cast h7
  have hD : 2 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) ≤ Nat.ceil (Δ / (2 * (N:ℝ))) := by
    have h : ((2 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) : ℕ):ℝ)
        ≤ ((Nat.ceil (Δ / (2 * (N:ℝ)))):ℝ) := by
      have h2 : (2:ℝ) * ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ)
          < 2 * (Δ / (4 * Real.pi * (N:ℝ))) + 2 := by linarith [hA₀lt]
      have h3 : 2 * (Δ / (4 * Real.pi * (N:ℝ))) + 2 ≤ Δ / (2 * (N:ℝ)) := by
        have h4 : 2 * (Δ / (4 * Real.pi * (N:ℝ))) = Δ / (2 * Real.pi * (N:ℝ)) := by field_simp; try ring
        rw [h4]
        have h5 : Δ / (2 * (N:ℝ)) - Δ / (2 * Real.pi * (N:ℝ)) = Δ * (Real.pi - 1) / (2 * Real.pi * (N:ℝ)) := by
          field_simp; try ring
        have h6 : (2:ℝ) ≤ Δ / (2 * (N:ℝ)) - Δ / (2 * Real.pi * (N:ℝ)) := by
          rw [h5, le_div_iff₀ (by positivity)]
          nlinarith [hN100, Real.pi_gt_three]
        linarith
      push_cast
      linarith [hM₁ge]
    exact_mod_cast h
  have hE : 4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) ≤ Nat.ceil (Δ / (2 * (N:ℝ))) := by
    have h : ((4 * Nat.ceil (Δ / (4 * Real.pi * (N:ℝ))) : ℕ):ℝ)
        ≤ ((Nat.ceil (Δ / (2 * (N:ℝ)))):ℝ) := by
      have h2 : (4:ℝ) * ((Nat.ceil (Δ / (4 * Real.pi * (N:ℝ)))):ℝ)
          < 4 * (Δ / (4 * Real.pi * (N:ℝ))) + 4 := by linarith [hA₀lt]
      have h3 : 4 * (Δ / (4 * Real.pi * (N:ℝ))) + 4 ≤ Δ / (2 * (N:ℝ)) := by
        have h4 : 4 * (Δ / (4 * Real.pi * (N:ℝ))) = Δ / (Real.pi * (N:ℝ)) := by field_simp; try ring
        rw [h4]
        have h5 : Δ / (2 * (N:ℝ)) - Δ / (Real.pi * (N:ℝ)) = Δ * (Real.pi - 2) / (2 * Real.pi * (N:ℝ)) := by
          field_simp; try ring
        have h6 : (4:ℝ) ≤ Δ / (2 * (N:ℝ)) - Δ / (Real.pi * (N:ℝ)) := by
          rw [h5, le_div_iff₀ (by positivity)]
          nlinarith [hN100, Real.pi_gt_three]
        linarith
      push_cast
      linarith [hM₁ge]
    exact_mod_cast h
  have hcmono : Nat.ceil (Δ / (2 * (N:ℝ))) ≤ Nat.ceil (Δ / (N:ℝ)) :=
    Nat.ceil_mono (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hN100])
  refine ⟨hA₀ge1, hmono, max_le hC1 hC2, hD, hE, ?_, ?_⟩
  · exact Nat.mul_le_mul_left 2 hcmono
  · exact le_trans hcmono (Nat.le_mul_of_pos_left (Nat.ceil (Δ / (N:ℝ))) (by norm_num))

/-- Per-pair step: the pointwise van der Corput transform with the frequency replaced by its
absolute value (conjugation) and the log factor dominated by `Δ`. -/
lemma hbm_per_pair {Cv : ℝ} (hCv : 0 < Cv)
    (hvdc : ∀ (N : ℕ), 1 ≤ N → ∀ (τ : ℝ), (N : ℝ) ≤ τ →
      ‖hbm N (2 * N) τ‖ ^ 2 ≤ Cv * (1 + Real.log (2 + τ)) ^ 4 *
        (1 + ‖hbm (Nat.ceil (τ / (4 * Real.pi * (N:ℝ)))) (Nat.floor (τ / (2 * Real.pi * (N:ℝ)))) τ‖ ^ 2))
    {N : ℕ} (hN : 1 ≤ N) {Δ θ : ℝ} (hΔ1 : 1 ≤ Δ) (hNΔ : (N:ℝ) ≤ Δ) (hθ : Δ ≤ |θ|)
    (hθ2 : |θ| ≤ 2 * Δ) :
    ‖hbm N (2 * N) θ‖ ^ 2 ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
      (1 + ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ)))) (Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))) θ‖ ^ 2) := by
  have habs : (N:ℝ) ≤ |θ| := le_trans hNΔ hθ
  have hθpos : 0 < |θ| := lt_of_lt_of_le (by linarith) hθ
  have hA1 : 1 ≤ Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))) :=
    Nat.ceil_pos.mpr (div_pos hθpos (by positivity))
  have hv := hvdc N hN |θ| habs
  have hL := hbm_norm_abs (A := N) (B := 2 * N) hN θ
  have hR := hbm_norm_abs (A := Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))))
    (B := Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))) hA1 θ
  rw [← hL, ← hR] at hv
  refine le_trans hv ?_
  have hlog : (1 + Real.log (2 + |θ|)) ^ 4 ≤ (1 + Real.log (2 + 2 * Δ)) ^ 4 := by
    have h1 : (2:ℝ) + |θ| ≤ 2 + 2 * Δ := by linarith
    have h2 : (0:ℝ) < 2 + |θ| := by positivity
    have h3 : Real.log (2 + |θ|) ≤ Real.log (2 + 2 * Δ) := Real.log_le_log h2 h1
    have ha : (0:ℝ) ≤ 1 + Real.log (2 + |θ|) := by
      have h4 : (1:ℝ) ≤ 2 + |θ| := by have := abs_nonneg θ; linarith
      have h5 := Real.log_nonneg h4
      linarith
    exact pow_le_pow_left₀ ha (by linarith) 4
  have hRHSnn : (0:ℝ) ≤ 1 + ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))))
        (Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))) θ‖ ^ 2 := by positivity
  calc Cv * (1 + Real.log (2 + |θ|)) ^ 4 *
        (1 + ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))))
              (Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))) θ‖ ^ 2)
      ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
        (1 + ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))))
              (Nat.floor (|θ| / (2 * Real.pi * (N:ℝ)))) θ‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hRHSnn
        exact mul_le_mul_of_nonneg_left hlog (le_of_lt hCv)


lemma hbm_split {a b c : ℕ} (hab : a ≤ b + 1) (hbc : b ≤ c) (θ : ℝ) :
    hbm a c θ = hbm a b θ + hbm (b + 1) c θ := by
  have hset : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b+1) c := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    apply Finset.disjoint_left.mpr; intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2; omega
  rw [hbm, hbm, hbm, hset, Finset.sum_union hdisj]

lemma hbm_term_norm (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    ‖(k:ℂ)^(Complex.I*(θ:ℂ))/(Real.sqrt (k:ℝ):ℂ)‖ = (Real.sqrt (k:ℝ))⁻¹ := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h1 : ‖(k:ℂ)^(Complex.I*(θ:ℂ))‖ = 1 := by
    rw [show (k:ℂ) = (((k:ℝ)):ℂ) by simp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hkpos]; simp
  have h2 : ‖((Real.sqrt (k:ℝ):ℝ):ℂ)‖ = Real.sqrt (k:ℝ) := Complex.norm_of_nonneg (Real.sqrt_nonneg _)
  rw [norm_div, h1, h2, one_div]

lemma hbm_single_norm_le (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) : ‖hbm k k θ‖ ≤ 1 := by
  have h : hbm k k θ = (k:ℂ)^(Complex.I*(θ:ℂ))/(Real.sqrt (k:ℝ):ℂ) := by simp [hbm]
  rw [h, hbm_term_norm k hk θ]
  have : (1:ℝ) ≤ Real.sqrt (k:ℝ) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  exact inv_le_one_of_one_le₀ this

lemma hbm_abs_le_sum (A B : ℕ) (hA : 1 ≤ A) (θ : ℝ) :
    ‖hbm A B θ‖ ≤ ∑ n ∈ Finset.Icc A B, (Real.sqrt (n:ℝ))⁻¹ := by
  rw [hbm]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  exact le_of_eq (hbm_term_norm n (le_trans hA (Finset.mem_Icc.mp hn).1) θ)

lemma hbm_sum2_mul_sum {R : ℕ} (a : ℝ) (g : Fin R → Fin R → ℝ) :
    (∑ i, ∑ j, a * g i j) = a * ∑ i, ∑ j, g i j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

lemma hbm_sum2_add {R : ℕ} (g h k : Fin R → Fin R → ℝ) (a b c : ℝ) :
    (∑ i, ∑ j, (a * g i j + b * h i j + c * k i j))
      = a * (∑ i, ∑ j, g i j) + b * (∑ i, ∑ j, h i j) + c * (∑ i, ∑ j, k i j) := by
  simp only [Finset.sum_add_distrib, hbm_sum2_mul_sum]


/-! ## The remaining recipe (steps C–G), verified numerically and mathematically

With the notation
`A₀ = ⌈Δ/(4πN)⌉`, `M₁ = A₂ = ⌈Δ/(2N)⌉`, `B₂ = 2⌈Δ/N⌉`, `θ_ij = t i - t j`,
`av i j = ⌈|θ_ij|/(4πN)⌉` and `bv i j = max ⌈|θ_ij|/(4πN)⌉ ⌊|θ_ij|/(2πN)⌋` for the pairs with
`Δ ≤ |θ_ij| ≤ 2Δ` (and `av = bv = A₀` otherwise), the proof of the target proceeds as:

* **A** (proved above, `hbm_per_pair` + `hbm_sub_le`): per pair, `‖hbm N (2N) θ‖² ≤
  Cv (1+log(2+2Δ))⁴ (1 + ‖hbm (av i j) (bv i j) θ‖²)`;
* **B**: split `1 + ‖·‖²` into the count term and the range-sum term;
* **C** *localization 1*: `smooth_range_localization_variable` with `A = A₀`, `B = 4A₀`,
  `W = 2Δ`, using `hbm_range_facts` (`A₀ ≤ av ≤ bv ≤ 4A₀`) — note `hbm (av) (bv) = hbm (av) (max …)`
  dominates the honest dual range by `hbm_sub_le`;
* **D** *split*: `hbm_split` at `2A₀` gives `hbm A₀ (4A₀) = hbm A₀ (2A₀) + hbm (2A₀+1) (4A₀)`, and
  `hbm (2A₀+1) (4A₀)` is bounded by `hbm (2A₀) (4A₀) + 1` (`hbm_single_norm_le`); hence
  `‖hbm A₀ (4A₀)‖² ≤ 2‖hbm A₀ (2A₀)‖² + 4‖hbm (2A₀) (4A₀)‖² + 4`;
* **E** *increase length* (Kerr's `cor:larger`, twice): `dirichlet_poly_increase_length` with
  `(N,M) = (A₀, M₁)` and `(2A₀, M₁)` (both need `2N ≤ M`, guaranteed by `hbm_range_facts` since
  `Δ ≥ 100N`), coefficients `c ≡ 1`, `B = 1`, and the lemma's `Δ`-parameter set to `2Δ`;
* **F** *localization 2*: `smooth_range_localization_variable` with `A = M₁`, `B = B₂` and the
  variable range `[M₁, 2M₁] ⊆ [A₂, B₂]` (`hbm_range_facts`);
* **G** *constants*: `(1+log(2+2Δ))⁴ ≤ Cl4 Δ^{ε/8}`, `log(4A₀+2)² ≤ Cl2 32^{ε/8} Δ^{ε/8}`,
  `M₁^{ε/8} ≤ 32^{ε/8} Δ^{ε/8}`, `log(B₂+2)² ≤ Cl2 32^{ε/8} Δ^{ε/8}` (all from
  `real_log_pow_le` / `real_log_sq_le_rpow` and `X ≤ 4Δ` for `X ∈ {A₀, M₁, B₂}`), giving
  `annulus ≤ K Δ^{ε/2} (Σ_{|θ|≤2Δ}‖hbm M₁ B₂ θ‖² + #pairs) ≤ K Δ^ε (…)` since `Δ ≥ 1`;
* the complementary regime `Δ < 100N` is trivial: the dual ranges are contained in `[1,31]`
  (`⌊|θ|/2πN⌋ ≤ ⌊200/2π⌋ = 31`), so `‖hbm (av)(bv) θ‖² ≤ 31²` by `hbm_abs_le_sum`, and the
  per-pair step closes the bound with `Δ^ε ≥ 1`.
-/


/-! # PROOF RECIPE for `kerr_main1` (Kerr's `lem:main1`, arXiv:1909.12075)

Setting: `N ≥ 1`, `Δ ≥ 1`, `N ≤ Δ`, `t : Fin R → ℝ` with `|t i - t j| ≥ 1` for `i ≠ j`,
`θ_ij := t i - t j`, `A₀ := A0 N Δ = ⌈Δ/(4πN)⌉`, `M₁ := M1 N Δ = ⌈Δ/(2N)⌉`,
`B₂ := B2 N Δ = 2⌈Δ/N⌉`.

* `annSum N Δ R t = Σ_{i,j} 1_{Δ ≤ |θ_ij| ≤ 2Δ} ‖hbm N (2N) θ_ij‖²` (the object to bound);
* `annDual N Δ R t = Σ_{i,j} 1_{Δ ≤ |θ_ij| ≤ 2Δ} ‖hbm ⌈|θ_ij|/(4πN)⌉ ⌊|θ_ij|/(2πN)⌋ θ_ij‖²`
  (the honest dual sum, i.e. the output of the pointwise van der Corput transform);
* `winS A B W R t = Σ_{i,j} 1_{|θ_ij| ≤ W} ‖hbm A B θ_ij‖²`, `pcount W R t = Σ_{i,j} 1_{|θ_ij| ≤ W}`.

**STEP A** (both regimes). `Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc`
gives `Cv > 0` with
`‖hbm N (2N) τ‖² ≤ Cv (1+log(2+τ))⁴ (1 + ‖hbm ⌈τ/(4πN)⌉ ⌊τ/(2πN)⌋ τ‖²)` for `N ≥ 1`, `τ ≥ N`.
For an annulus pair (`Δ ≤ |θ| ≤ 2Δ`, so `N ≤ |θ|`) combine with `hbm_per_pair` (proved in this
file) and `hbm_norm_abs`:
`‖hbm N (2N) θ‖² ≤ Cv (1+log(2+2Δ))⁴ (1 + ‖hbm ⌈|θ|/(4πN)⌉ ⌊|θ|/(2πN)⌋ θ‖²)`.
Summing over the annulus pairs (note `Σ_{annulus} 1 ≤ pcount (2Δ) R t`):
`annSum ≤ Cv (1+log(2+2Δ))⁴ (pcount (2Δ) R t + annDual)`.  Absorb the log with
`log_pow_four_le_rpow` (proved in this file).

**STEP B/C** (regime `Δ ≥ 100 N`). Define, for **all** pairs (`Δ`-condition *not* imposed — for
non-annulus pairs the summands are `≥ 0` and the localization sum is larger),
`a_ij := ⌈|θ_ij|/(4πN)⌉`, `b_ij := max a_ij ⌊|θ_ij|/(2πN)⌋`.  For the annulus pairs
`hbm_range_facts` (proved in this file) gives `A₀ ≤ a_ij ≤ b_ij ≤ 4A₀`; for the others take
`a = b = A₀`.  `Commons.NumberTheory.DirichletPolynomial.smooth_range_localization_variable`
(with its `A := A₀`, `B := 4A₀`, `W := 2Δ`) then gives
`annDual ≤ C log(4A₀+2)² * winS A₀ (4A₀) (2Δ) R t`.
Use `hbm_sub_le` to see that `hbm a b θ` dominates the honest `hbm ⌈|θ|/(4πN)⌉ ⌊|θ|/(2πN)⌋ θ`:
when `⌊⌋ ≥ ⌈⌉` we have `b = ⌊⌋`; when `⌊⌋ < ⌈⌉` the honest sum is `0` (empty `Finset.Icc`).

**STEP D**. `hbm_split` gives `hbm A₀ (4A₀) = hbm A₀ (2A₀) + hbm (2A₀+1) (4A₀)`, and
`hbm (2A₀+1) (4A₀) = hbm (2A₀) (4A₀) - hbm (2A₀) (2A₀)`, so with `hbm_single_norm_le`
(`‖hbm k k θ‖ ≤ 1`): `‖hbm A₀ (4A₀) θ‖² ≤ 2‖hbm A₀ (2A₀) θ‖² + 4‖hbm (2A₀) (4A₀) θ‖² + 4`.
Hence `winS A₀ (4A₀) (2Δ) ≤ 2 winS A₀ (2A₀) (2Δ) + 4 winS (2A₀) (4A₀) (2Δ) + 4 pcount (2Δ)`.

**STEP E**. `Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length`, twice, with
its window parameter set to `2Δ`, coefficients `c ≡ 1`, `B := 1`, and `(N,M) = (A₀, M₁)`
resp. `(2A₀, M₁)` — both legitimate since `2A₀ ≤ M₁` and `4A₀ ≤ M₁` (`hbm_range_facts`):
`winS A₀ (2A₀) (2Δ) ≤ Cin M₁^{ε/8} winS M₁ (2M₁) (2Δ)` and
`winS (2A₀) (4A₀) (2Δ) ≤ Cin M₁^{ε/8} winS M₁ (2M₁) (2Δ)`.

**STEP F**. `smooth_range_localization_variable` again with `A := M₁`, `B := B₂` and the *constant*
ranges `a_ij = M₁`, `b_ij = 2M₁` (valid: `M₁ ≤ 2M₁ ≤ B₂`, `hbm_range_facts`):
`winS M₁ (2M₁) (2Δ) ≤ C log(B₂+2)² winS M₁ B₂ (2Δ) R t`.

**STEP G**. Constants: `log(4A₀+2)² ≤ K Δ^{ε/4}` and `log(B₂+2)² ≤ K Δ^{ε/4}` by `log_sq_le_rpow`
(valid since `4A₀ + 2 ≥ 3` and `B₂ + 2 ≥ 3`); `M₁^{ε/8} ≤ (2Δ)^{ε/8} ≤ K Δ^{ε/8}` by
`M1_le_two_delta`.  Collecting, `annSum ≤ K Δ^{ε/2}(winS M₁ B₂ (2Δ) + pcount (2Δ)) ≤
K Δ^ε (winS M₁ B₂ (2Δ) + pcount (2Δ))` since `Δ ≥ 1`.

**REGIME `Δ < 100 N`** (`kerr_main1_small`). Then `|θ| ≤ 2Δ < 200 N`, so the honest dual range
satisfies `⌊|θ|/(2πN)⌋ ≤ 31`, and each of its terms has modulus `1/√n ≤ 1`, so `‖hbm a b θ‖ ≤ 31`
(`hbm_abs_le_sum`; if `⌊⌋ < ⌈⌉` the sum is `0`).  STEP A + `log_pow_four_le_rpow` + `Δ^ε ≥ 1`
gives `annSum ≤ K Δ^ε pcount (2Δ) ≤ K Δ^ε (winS M₁ B₂ (2Δ) + pcount (2Δ))`.

All the auxiliary lemmas named above are proved (sorry-free) in this file, EXCEPT the three
imported commons theorems, whose fully qualified names are
`Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc`,
`Commons.NumberTheory.DirichletPolynomial.smooth_range_localization_variable`,
`Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length`.
-/

/-! ## The vocabulary for `kerr_main1` (Kerr `lem:main1`) -/

/-- `A₀ = ⌈Δ/(4πN)⌉`: the honest dual lower scale. -/
def A0 (N : ℕ) (Δ : ℝ) : ℕ := Nat.ceil (Δ / (4 * Real.pi * (N : ℝ)))

/-- `M₁ = ⌈Δ/(2N)⌉`: the reflected lower scale of `lem:main1`. -/
def M1 (N : ℕ) (Δ : ℝ) : ℕ := Nat.ceil (Δ / (2 * (N : ℝ)))

/-- `B₂ = 2⌈Δ/N⌉`: the reflected upper scale of `lem:main1`. -/
def B2 (N : ℕ) (Δ : ℝ) : ℕ := 2 * Nat.ceil (Δ / (N : ℝ))

/-- The annulus difference sum at scale `N`:
`Σ_{i,j} 1_{Δ ≤ |θ_ij| ≤ 2Δ} ‖Σ_{n ∈ [N,2N]} n^{iθ_ij}/√n‖²`. -/
noncomputable def annSum (N : ℕ) (Δ : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R,
    (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then ‖hbm N (2 * N) (t i - t j)‖ ^ 2 else 0)

/-- The honest dual (reflected) annulus sum:
`Σ_{i,j} 1_{Δ ≤ |θ_ij| ≤ 2Δ} ‖Σ_{⌈|θ_ij|/(4πN)⌉ ≤ n ≤ ⌊|θ_ij|/(2πN)⌋} n^{iθ_ij}/√n‖²`. -/
noncomputable def annDual (N : ℕ) (Δ : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R,
    (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
      ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N : ℝ))))
           (Nat.floor (|t i - t j| / (2 * Real.pi * (N : ℝ)))) (t i - t j)‖ ^ 2 else 0)

/-- Windowed difference sum over a block: `Σ_{i,j} 1_{|θ_ij| ≤ W} ‖Σ_{n ∈ [A,B]} n^{iθ_ij}/√n‖²`. -/
noncomputable def winS (A B : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ W then ‖hbm A B (t i - t j)‖ ^ 2 else 0)

/-- The number of pairs with `|θ_ij| ≤ W`. -/
noncomputable def pcount (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ W then (1 : ℝ) else 0)

lemma annSum_nonneg (N : ℕ) (Δ : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ annSum N Δ R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma annDual_nonneg (N : ℕ) (Δ : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ annDual N Δ R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma winS_nonneg (A B : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ winS A B W R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma pcount_nonneg (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ pcount W R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma winS_mono_window {W₁ W₂ : ℝ} (h : W₁ ≤ W₂) (A B : ℕ) (R : ℕ) (t : Fin R → ℝ) :
    winS A B W₁ R t ≤ winS A B W₂ R t := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : |t i - t j| ≤ W₁
  · rw [if_pos hc, if_pos (le_trans hc h)]
  · rw [if_neg hc]; split_ifs <;> positivity

lemma pcount_mono_window {W₁ W₂ : ℝ} (h : W₁ ≤ W₂) (R : ℕ) (t : Fin R → ℝ) :
    pcount W₁ R t ≤ pcount W₂ R t := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : |t i - t j| ≤ W₁
  · rw [if_pos hc, if_pos (le_trans hc h)]
  · rw [if_neg hc]; split_ifs <;> norm_num

/-- The annulus is contained in the window `|θ| ≤ 2Δ`. -/
lemma annSum_le_winS (N : ℕ) (Δ : ℝ) (R : ℕ) (t : Fin R → ℝ) :
    annSum N Δ R t ≤ winS N (2 * N) (2 * Δ) R t := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ
  · rw [if_pos hc, if_pos hc.2]
  · rw [if_neg hc]; split_ifs <;> positivity

/-- Power-of-a-power for real exponents: `(x^a)^n = x^(a*n)` for `x ≥ 0`. -/
lemma rpow_pow_eq (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x ^ a) ^ n = x ^ (a * (n : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx a (n : ℝ)]

/-- `log`-absorption (step G): `(1 + log(2+2Δ))⁴ ≤ C Δ^η` for `Δ ≥ 1`. -/
lemma log_pow_four_le_rpow {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 1 ≤ Δ → (1 + Real.log (2 + 2 * Δ)) ^ 4 ≤ C * Δ ^ η := by
  set δ : ℝ := η / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  refine ⟨((1 + Real.log 4) + 1 / δ) ^ 4, by positivity, ?_⟩
  intro Δ hΔ
  have hΔ0 : (0:ℝ) < Δ := by linarith
  have hlog4 : Real.log (2 + 2 * Δ) ≤ Real.log 4 + Real.log Δ := by
    have h4 : 2 + 2 * Δ ≤ 4 * Δ := by linarith
    have h := Real.log_le_log (by linarith : (0:ℝ) < 2 + 2 * Δ) h4
    rwa [Real.log_mul (by norm_num) (ne_of_gt hΔ0)] at h
  have hlogΔ : Real.log Δ ≤ Δ ^ δ / δ := Real.log_le_rpow_div hΔ0.le hδpos
  have hpow1 : (1:ℝ) ≤ Δ ^ δ := Real.one_le_rpow hΔ hδpos.le
  have hlog4nn : (0:ℝ) ≤ 1 + Real.log 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hstep : 1 + Real.log (2 + 2 * Δ) ≤ ((1 + Real.log 4) + 1 / δ) * Δ ^ δ := by
    have h1 : 1 + Real.log (2 + 2 * Δ) ≤ 1 + Real.log 4 + Δ ^ δ / δ := by linarith
    have h2 : Δ ^ δ / δ = (1 / δ) * Δ ^ δ := by ring
    have h3 : (1 + Real.log 4) ≤ (1 + Real.log 4) * Δ ^ δ := by nlinarith [hlog4nn, hpow1]
    calc 1 + Real.log (2 + 2 * Δ) ≤ 1 + Real.log 4 + Δ ^ δ / δ := h1
      _ = (1 + Real.log 4) + (1 / δ) * Δ ^ δ := by rw [h2]
      _ ≤ (1 + Real.log 4) * Δ ^ δ + (1 / δ) * Δ ^ δ := by linarith
      _ = ((1 + Real.log 4) + 1 / δ) * Δ ^ δ := by ring
  have hbase : (0:ℝ) ≤ 1 + Real.log (2 + 2 * Δ) := by
    have h : (1:ℝ) ≤ 2 + 2 * Δ := by linarith
    have := Real.log_nonneg h; linarith
  have hpow4 : (Δ ^ δ) ^ 4 = Δ ^ η := by
    have he : δ * ((4:ℕ):ℝ) = η := by rw [hδ]; norm_num
    rw [rpow_pow_eq Δ hΔ0.le δ 4, he]
  calc (1 + Real.log (2 + 2 * Δ)) ^ 4 ≤ (((1 + Real.log 4) + 1 / δ) * Δ ^ δ) ^ 4 :=
        pow_le_pow_left₀ hbase hstep 4
    _ = ((1 + Real.log 4) + 1 / δ) ^ 4 * (Δ ^ δ) ^ 4 := by rw [mul_pow]
    _ = ((1 + Real.log 4) + 1 / δ) ^ 4 * Δ ^ η := by rw [hpow4]

/-- `log²`-absorption (step G): `(log x)² ≤ C x^η` for `x ≥ 3`. -/
lemma log_sq_le_rpow {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → (Real.log x) ^ 2 ≤ C * x ^ η := by
  set δ : ℝ := η / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  refine ⟨1 / δ ^ 2, by positivity, ?_⟩
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδpos
  have hlog0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hsq : (Real.log x) ^ 2 ≤ (x ^ δ / δ) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hpow2 : (x ^ δ) ^ 2 = x ^ η := by
    have he : δ * ((2:ℕ):ℝ) = η := by rw [hδ]; norm_num
    rw [rpow_pow_eq x hx0.le δ 2, he]
  calc (Real.log x) ^ 2 ≤ (x ^ δ / δ) ^ 2 := hsq
    _ = 1 / δ ^ 2 * (x ^ δ) ^ 2 := by rw [div_pow]; ring
    _ = 1 / δ ^ 2 * x ^ η := by rw [hpow2]

/-- The reflected lower scale is at most `2Δ` (step G, used to absorb `M₁^η`). -/
lemma M1_le_two_delta (N : ℕ) (hN : 1 ≤ N) {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    ((M1 N Δ : ℕ) : ℝ) ≤ 2 * Δ := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have h2 : ((M1 N Δ : ℕ) : ℝ) ≤ Δ / (2 * (N:ℝ)) + 1 := by
    rw [M1]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have h1 : Δ / (2 * (N:ℝ)) ≤ Δ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hΔ, hN1]
  linarith

/-- The reflected upper scale is at most `4Δ` (step G, used to absorb `log(B₂+2)²`). -/
lemma B2_le_four_delta (N : ℕ) (hN : 1 ≤ N) {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    ((B2 N Δ : ℕ) : ℝ) ≤ 4 * Δ := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have h2 : ((Nat.ceil (Δ / (N:ℝ)) : ℕ) : ℝ) ≤ Δ / (N:ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have h1 : Δ / (N:ℝ) ≤ Δ := by
    rw [div_le_iff₀ hNpos]; nlinarith [hΔ, hN1]
  have h3 : ((B2 N Δ : ℕ) : ℝ) = 2 * ((Nat.ceil (Δ / (N:ℝ)) : ℕ) : ℝ) := by
    rw [B2]; push_cast; ring
  rw [h3]
  linarith

end

end Work.GM.HB
