import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Gauss sum: `∑_{k=1}^{K} k = K(K+1)/2` over the reals. -/
lemma sum_Icc_one_id (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (k : ℝ) = (K : ℝ) * ((K : ℝ) + 1) / 2 := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega), ih]
    push_cast
    ring

/-- The Fejér weight normalisation: `∑_{k=1}^{K} (1 - k/(K+1)) = K/2`. -/
lemma fejer_sum (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (1 - (k : ℝ) / (K + 1)) = (K : ℝ) / 2 := by
  have hterm : ∀ k : ℕ, (1 - (k : ℝ) / (K + 1))
      = (((K : ℝ) + 1) - (k : ℝ)) / ((K : ℝ) + 1) := by
    intro k
    have h : (K : ℝ) + 1 ≠ 0 := by positivity
    field_simp <;> ring
  have hcongr : ∑ k ∈ Finset.Icc 1 K, (1 - (k : ℝ) / (K + 1))
      = ∑ k ∈ Finset.Icc 1 K, (((K : ℝ) + 1) - (k : ℝ)) / ((K : ℝ) + 1) :=
    Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hcongr]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  rw [show K + 1 - 1 = K by omega]
  rw [sum_Icc_one_id]
  simp only [nsmul_eq_mul]
  have hK1 : ((K : ℝ) + 1) ≠ 0 := by positivity
  field_simp <;> ring

/-- Weighted interval bound: if `t ≤ x i ≤ M` on `s` and the weighted mean of `x` is at most
`A`, then the weighted mean square is at most `(t+M)*A - t*M*∑ w`. -/
lemma weighted_sq_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ) {t M A : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, t ≤ x i) (hxu : ∀ i ∈ s, x i ≤ M)
    (hm : ∑ i ∈ s, w i * x i ≤ A) (hTM : 0 ≤ t + M) :
    ∑ i ∈ s, w i * (x i) ^ 2 ≤ (t + M) * A - t * M * ∑ i ∈ s, w i := by
  have hpt : ∀ i ∈ s, w i * (x i) ^ 2 ≤ w i * ((t + M) * x i - t * M) := by
    intro i hi
    have h1 : 0 ≤ x i - t := sub_nonneg.mpr (hx i hi)
    have h2 : 0 ≤ M - x i := sub_nonneg.mpr (hxu i hi)
    have h3 : 0 ≤ (x i - t) * (M - x i) := mul_nonneg h1 h2
    have h4 : (x i) ^ 2 ≤ (t + M) * x i - t * M := by nlinarith [h3]
    exact mul_le_mul_of_nonneg_left h4 (hw i hi)
  calc ∑ i ∈ s, w i * (x i) ^ 2
      ≤ ∑ i ∈ s, w i * ((t + M) * x i - t * M) := Finset.sum_le_sum hpt
    _ = ∑ i ∈ s, ((t + M) * (w i * x i) - t * M * w i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (t + M) * (∑ i ∈ s, w i * x i) - t * M * (∑ i ∈ s, w i) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (t + M) * A - t * M * (∑ i ∈ s, w i) := by
          have h := mul_le_mul_of_nonneg_left hm hTM
          linarith

/-- Final algebra step: the threshold `2(AM-B)/(KM-2A)` controls the quadratic expression. -/
lemma final_algebra {K : ℕ} {A B M t : ℝ} (hden : 2 * A < (K : ℝ) * M)
    (ht : 2 * (A * M - B) / ((K : ℝ) * M - 2 * A) < t) :
    (t + M) * A - t * M * ((K : ℝ) / 2) < B := by
  have hpos : 0 < (K : ℝ) * M - 2 * A := by linarith
  have hkey : 2 * (A * M - B) < t * ((K : ℝ) * M - 2 * A) := (div_lt_iff₀ hpos).mp ht
  nlinarith [hkey]

/-- **Pigeonhole / "cancellation" step** (Blanksby–Montgomery, Lemma 3).

Let `σ : ℕ → ℝ` be bounded above by `N log 2` on `{1,…,K}` and suppose that its Fejér-weighted
mean is at most `A` while its Fejér-weighted mean square is at least `B`:
`∑_{k=1}^K (1-k/(K+1)) σ_k ≤ A` and `B ≤ ∑_{k=1}^K (1-k/(K+1)) σ_k²`.
Then some `σ_k` is very negative: either `σ_k ≤ -N log 2` (trivial case), or
`σ_k ≤ 2(A·N log 2 − B)/(K·N log 2 − 2A)`.

This is the algebraic core: a bounded mean together with a large mean square forces large
negative values. -/
theorem sigma_pigeonhole {N K : ℕ} (σ : ℕ → ℝ) {A B : ℝ} (hK : 1 ≤ K) (hA : 0 < A)
    (hden : 2 * A < K * N * Real.log 2)
    (hub : ∀ k ∈ Finset.Icc 1 K, σ k ≤ N * Real.log 2)
    (hmean : ∑ k ∈ Finset.Icc 1 K, (1 - (k : ℝ) / (K + 1)) * σ k ≤ A)
    (hms : B ≤ ∑ k ∈ Finset.Icc 1 K, (1 - (k : ℝ) / (K + 1)) * (σ k) ^ 2) :
    ∃ k ∈ Finset.Icc 1 K, σ k ≤ max (-(N : ℝ) * Real.log 2)
      (2 * (A * N * Real.log 2 - B) / (K * N * Real.log 2 - 2 * A)) := by
  obtain ⟨k0, hk0mem, hk0min⟩ :=
    Finset.exists_min_image (Finset.Icc 1 K) σ (Finset.nonempty_Icc.mpr hK)
  refine ⟨k0, hk0mem, ?_⟩
  let M : ℝ := (N : ℝ) * Real.log 2
  have hKN : K * N * Real.log 2 = (K : ℝ) * M := by push_cast; ring
  have hMhub : ∀ k ∈ Finset.Icc 1 K, σ k ≤ M := by intro k hk; exact hub k hk
  have hdenM : 2 * A < (K : ℝ) * M := by rw [← hKN]; exact hden
  have hMneg : -(N : ℝ) * Real.log 2 = -M := by ring
  have hAM : A * N * Real.log 2 = A * M := by ring
  have hgoal_eq : max (-(N : ℝ) * Real.log 2)
        (2 * (A * N * Real.log 2 - B) / (K * N * Real.log 2 - 2 * A)) =
      max (-M) (2 * (A * M - B) / ((K : ℝ) * M - 2 * A)) := by
    rw [hMneg, hAM, hKN]
  rw [hgoal_eq]
  by_cases hle : σ k0 ≤ -M
  · exact le_trans hle (le_max_left _ _)
  · push_neg at hle
    refine le_trans ?_ (le_max_right _ _)
    by_contra hc
    push_neg at hc
    let w : ℕ → ℝ := fun k => 1 - (k : ℝ) / (K + 1)
    have hw : ∀ i ∈ Finset.Icc 1 K, 0 ≤ w i := by
      intro i hi
      obtain ⟨_, hi2⟩ := Finset.mem_Icc.mp hi
      have hcast : (i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hi2
      have hpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      show (0 : ℝ) ≤ 1 - (i : ℝ) / ((K : ℝ) + 1)
      have h1 : (i : ℝ) / ((K : ℝ) + 1) ≤ 1 := by rw [div_le_one hpos]; linarith
      linarith
    have hTM : (0 : ℝ) ≤ σ k0 + M := by linarith [hle]
    have hsq := weighted_sq_le (Finset.Icc 1 K) w σ hw hk0min hMhub hmean hTM
    have hwfejer : ∑ i ∈ Finset.Icc 1 K, w i = (K : ℝ) / 2 := fejer_sum K
    rw [hwfejer] at hsq
    have hfinal : (σ k0 + M) * A - σ k0 * M * ((K : ℝ) / 2) < B := final_algebra hdenM hc
    have hms' : B ≤ ∑ i ∈ Finset.Icc 1 K, w i * (σ i) ^ 2 := hms
    linarith [hms', hsq, hfinal]

end Work.BW
