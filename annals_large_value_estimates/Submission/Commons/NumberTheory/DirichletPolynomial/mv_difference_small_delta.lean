import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.logsum_partial_bound
import Submission.Commons.Analysis.Series.harmonic_sum_le_rpow
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div
import Submission.Commons.NumberTheory.DirichletPolynomial.dirPolyA_neg_eq_conj
import Submission.Commons.NumberTheory.DirichletPolynomial.kerr_coefficient_majorant

open Finset
open scoped BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletPolynomial

noncomputable section

open Complex

/-! ## 1. Pointwise bound for the weighted log-phase `∑_{N ≤ n ≤ 2N} n^{-1/2+iθ}` -/

private lemma reindex_range (N : ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc N (2*N), b n) = ∑ i ∈ Finset.range (N+1), b (N + i) := by
  have hIcc : Finset.Icc N (2*N) = Finset.Ico N (2*N+1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range b N (2*N+1)]
  have h : 2*N+1 - N = N+1 := by omega
  rw [h]

/-- For `N ≥ 2` and `θ ≥ 1`: `‖∑_{N ≤ n ≤ 2N} n^{-1/2+iθ}‖² ≤ K·(θ/N + N/θ + 1)`. -/
theorem weighted_logsum_pointwise :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 2 ≤ N → ∀ (θ : ℝ), 1 ≤ θ →
      ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖^2
        ≤ K * (θ/(N:ℝ) + (N:ℝ)/θ + 1) := by
  obtain ⟨K', hK'pos, hK'⟩ := logsum_partial_bound
  refine ⟨2*K'^2, by positivity, ?_⟩
  intro N hN θ hθ
  have hθ0 : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set B : ℝ := K'*(Real.sqrt θ + (N:ℝ)/Real.sqrt θ) with hBdef
  have hBnonneg : 0 ≤ B := by rw [hBdef]; positivity
  have hP : ∀ i : ℕ, i ≤ N →
      ‖∑ j ∈ Finset.range (i+1), (((N+j:ℕ):ℂ)^(Complex.I*(θ:ℂ)))‖ ≤ B := by
    intro i hi
    have hsum : (∑ j ∈ Finset.range (i+1), ((N+j:ℕ):ℂ)^(Complex.I*(θ:ℂ)))
        = ∑ n ∈ Finset.Icc N (N+i), (n:ℂ)^(Complex.I*(θ:ℂ)) := by
      have hIcc : Finset.Icc N (N+i) = Finset.Ico N (N+i+1) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range (fun n => (n:ℂ)^(Complex.I*(θ:ℂ))) N (N+i+1)]
      have h : N+i+1 - N = i+1 := by omega
      rw [h]
    rw [hsum, hBdef]
    exact hK' θ hθ N (N+i) hN (by omega) (by omega)
  set F : ℕ → ℝ := fun i => (Real.sqrt (((N+i:ℕ):ℝ)))⁻¹ with hFdef
  set G : ℕ → ℂ := fun i => (((N+i:ℕ):ℂ)^(Complex.I*(θ:ℂ))) with hGdef
  have hFpos : ∀ i, 0 < F i := by
    intro i; rw [hFdef]; simp only
    apply inv_pos.mpr; apply Real.sqrt_pos.mpr
    have : (1:ℝ) ≤ ((N+i:ℕ):ℝ) := by
      have : 1 ≤ N + i := by omega
      exact_mod_cast this
    linarith
  have hFanti : ∀ i, F (i+1) ≤ F i := by
    intro i
    rw [hFdef]; simp only
    have ha : (0:ℝ) < Real.sqrt (((N+i:ℕ):ℝ)) := by
      apply Real.sqrt_pos.mpr
      exact_mod_cast (by omega : 0 < N + i)
    have hnn : (0:ℝ) ≤ (((N+i:ℕ)):ℝ) := by positivity
    have hle' : (((N+i:ℕ)):ℝ) ≤ ((((N+(i+1)):ℕ)):ℝ) := by
      exact_mod_cast (by omega : N+i ≤ N+(i+1))
    have hle : Real.sqrt (((N+i:ℕ):ℝ)) ≤ Real.sqrt (((N+(i+1):ℕ):ℝ)) :=
      Real.sqrt_le_sqrt hle'
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (a := Real.sqrt (((N+i:ℕ):ℝ)))
      (b := Real.sqrt (((N+(i+1):ℕ):ℝ))) ha hle
  have habel := Finset.sum_range_by_parts F G (N+1)
  have hN1 : N + 1 - 1 = N := by omega
  rw [hN1] at habel
  have hGN : ‖∑ i ∈ Finset.range (N+1), G i‖ ≤ B := by
    have := hP N (le_refl N); simpa [hGdef] using this
  have hsum_norm : ‖∑ i ∈ Finset.range (N+1), F i • G i‖ ≤ B * F 0 := by
    rw [habel]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖F N • ∑ i ∈ Finset.range (N+1), G i‖ ≤ B * F N := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hFpos N)]
      calc F N * ‖∑ i ∈ Finset.range (N+1), G i‖ ≤ F N * B :=
            mul_le_mul_of_nonneg_left hGN (le_of_lt (hFpos N))
        _ = B * F N := by ring
    have h2 : ‖∑ i ∈ Finset.range N, (F (i+1) - F i) • ∑ j ∈ Finset.range (i+1), G j‖
        ≤ B * (F 0 - F N) := by
      have hterm : ∀ i ∈ Finset.range N,
          ‖(F (i+1) - F i) • ∑ j ∈ Finset.range (i+1), G j‖ ≤ (F i - F (i+1)) * B := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hFanti i]), neg_sub]
        have hGi : ‖∑ j ∈ Finset.range (i+1), G j‖ ≤ B := by
          have := hP i (le_of_lt hi); simpa [hGdef] using this
        exact mul_le_mul_of_nonneg_left hGi (sub_nonneg.mpr (hFanti i))
      calc ‖∑ i ∈ Finset.range N, (F (i+1) - F i) • ∑ j ∈ Finset.range (i+1), G j‖
          ≤ ∑ i ∈ Finset.range N, ‖(F (i+1) - F i) • ∑ j ∈ Finset.range (i+1), G j‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range N, (F i - F (i+1)) * B := Finset.sum_le_sum hterm
        _ = B * (∑ i ∈ Finset.range N, (F i - F (i+1))) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        _ = B * (F 0 - F N) := by
              congr 1
              have htel : (∑ i ∈ Finset.range N, (F i - F (i+1)))
                  = - ∑ i ∈ Finset.range N, (F (i+1) - F i) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl; intro i _; ring
              rw [htel, Finset.sum_range_sub]; ring
    linarith [h1, h2]
  have hAeq : (∑ i ∈ Finset.range (N+1), F i • G i)
      = ∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ) := by
    rw [reindex_range N (fun n => (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hFdef, hGdef]; simp only
    rw [Complex.real_smul, Complex.ofReal_inv]
    rw [div_eq_mul_inv, mul_comm]
  have hnorm : ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖
      ≤ B * F 0 := by rw [← hAeq]; exact hsum_norm
  have hF0 : F 0 = (Real.sqrt (N:ℝ))⁻¹ := by rw [hFdef]; simp
  have hBF0 : B * F 0 = K' * (Real.sqrt θ + (N:ℝ)/Real.sqrt θ) * (Real.sqrt (N:ℝ))⁻¹ := by
    rw [hBdef, hF0]
  have hfinal : (B * F 0)^2 ≤ 2*K'^2 * (θ/(N:ℝ) + (N:ℝ)/θ + 1) := by
    rw [hBF0]
    have hsq : (Real.sqrt (N:ℝ))⁻¹ * (Real.sqrt (N:ℝ))⁻¹ = ((N:ℝ))⁻¹ := by
      rw [← mul_inv]; congr 1
      rw [← pow_two, Real.sq_sqrt hN0.le]
    have hkey : (K' * (Real.sqrt θ + (N:ℝ)/Real.sqrt θ) * (Real.sqrt (N:ℝ))⁻¹)^2
        = K'^2 * ((Real.sqrt θ + (N:ℝ)/Real.sqrt θ)^2 * ((N:ℝ))⁻¹) := by
      rw [mul_pow, mul_pow, ← hsq]; ring
    rw [hkey]
    have hcore : (Real.sqrt θ + (N:ℝ)/Real.sqrt θ)^2 * ((N:ℝ)⁻¹)
        = θ/(N:ℝ) + 2 + (N:ℝ)/θ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have h1 : (Real.sqrt θ)^2 = θ := Real.sq_sqrt hθ0.le
      field_simp
      rw [h1]; ring
    rw [hcore]
    have hx : (0:ℝ) ≤ θ/(N:ℝ) := div_nonneg hθ0.le hN0.le
    have hy : (0:ℝ) ≤ (N:ℝ)/θ := div_nonneg hN0.le hθ0.le
    nlinarith [sq_nonneg (K'), hK'pos, hx, hy]
  have hnn : 0 ≤ ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ :=
    norm_nonneg _
  have hBF0nn : 0 ≤ B * F 0 := mul_nonneg hBnonneg (hFpos 0).le
  calc ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖^2
      ≤ (B * F 0)^2 := by nlinarith [hnorm, hnn, hBF0nn]
    _ ≤ 2*K'^2 * (θ/(N:ℝ) + (N:ℝ)/θ + 1) := hfinal

/-- Combined pointwise bound valid for all `N ≥ 1`. -/
theorem weighted_logsum_pointwise_all :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (θ : ℝ), 1 ≤ θ →
      ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖^2
        ≤ K * (θ/(N:ℝ) + (N:ℝ)/θ + 1) := by
  obtain ⟨K', hK'pos, hK'⟩ := weighted_logsum_pointwise
  refine ⟨max K' (4/3), lt_max_of_lt_left hK'pos, ?_⟩
  intro N hN θ hθ
  have hθ0 : 0 < θ := by linarith
  have hsum3 : (3:ℝ) ≤ θ/(N:ℝ) + (N:ℝ)/θ + 1 := by
    have hNp : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have h2 : 2 ≤ θ/(N:ℝ) + (N:ℝ)/θ := by
      have he : θ/(N:ℝ) + (N:ℝ)/θ - 2 = (θ - (N:ℝ))^2 / (θ * (N:ℝ)) := by
        field_simp; ring
      rw [← sub_nonneg, he]
      positivity
    linarith
  rcases eq_or_lt_of_le hN with h | h
  · subst h
    have hgoal : (max K' (4/3)) * (θ / ((1:ℕ):ℝ) + ((1:ℕ):ℝ) / θ + 1)
        = (max K' (4/3)) * (θ / (1:ℝ) + (1:ℝ) / θ + 1) := by norm_num
    rw [hgoal]
    have hb : ‖∑ n ∈ Finset.Icc (1:ℕ) (2*1), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ≤ 2 := by
      calc ‖∑ n ∈ Finset.Icc (1:ℕ) 2, (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖
          ≤ ∑ n ∈ Finset.Icc (1:ℕ) 2, ‖(n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Icc (1:ℕ) 2, (1:ℝ) := by
            apply Finset.sum_le_sum; intro n hn
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
            have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
            rw [norm_div]
            have hc : ‖(n:ℂ)^(Complex.I*(θ:ℂ))‖ = 1 := by
              rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n) (Complex.I*(θ:ℂ))]
              have hre : (Complex.I*(θ:ℂ)).re = 0 := by simp
              rw [hre, Real.rpow_zero]
            rw [hc]
            rw [show ‖((Real.sqrt (n:ℝ) : ℝ) : ℂ)‖ = Real.sqrt (n:ℝ) from by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]]
            rw [one_div]
            have hsqrt1 : (1:ℝ) ≤ Real.sqrt (n:ℝ) := by
              rw [show (1:ℝ) = Real.sqrt 1 by simp]
              exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
            exact inv_le_one_of_one_le₀ hsqrt1
        _ = 2 := by
            rw [Finset.sum_const, Nat.card_Icc]
            norm_num
    calc ‖∑ n ∈ Finset.Icc (1:ℕ) (2*1), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖^2
        ≤ 2^2 := by nlinarith [hb, norm_nonneg (∑ n ∈ Finset.Icc (1:ℕ) (2*1), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ))]
      _ = 4 := by norm_num
      _ ≤ (4/3) * (θ/(1:ℝ) + (1:ℝ)/θ + 1) := by
          have hm : (4/3 : ℝ) * 3 = 4 := by norm_num
          nlinarith
      _ ≤ (max K' (4/3)) * (θ/(1:ℝ) + (1:ℝ)/θ + 1) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  · have h2 : 2 ≤ N := by omega
    have h := hK' N h2 θ hθ
    refine le_trans h ?_
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    exact hsum3.trans' (by linarith)

open Commons.Analysis.ExpLog in
lemma sum_inv_le_of_sep_A {s : Finset ℝ} {A : ℕ}
    (h1 : ∀ u ∈ s, 1 ≤ u) (hle : ∀ u ∈ s, u ≤ (A:ℝ))
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → 1 ≤ |u - v|) :
    ∑ u ∈ s, (1:ℝ)/u ≤ ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) := by
  rcases Nat.eq_zero_or_pos s.card with hc | hc
  · have hs : s = ∅ := Finset.card_eq_zero.mp hc
    rw [hs]; simp only [Finset.sum_empty]; positivity
  have hsum_eq : ∑ u ∈ s, (1:ℝ)/u = ∑ i : Fin s.card, (1:ℝ)/((s.orderEmbOfFin rfl) i) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ s (rfl : s.card = s.card)]
    rw [Finset.sum_map]; rfl
  have hkey : ∀ (i : ℕ) (hi : i < s.card), ((i:ℝ)+1) ≤ (s.orderEmbOfFin rfl) ⟨i,hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hmem : (s.orderEmbOfFin rfl) ⟨0, hi⟩ ∈ s := Finset.orderEmbOfFin_mem s rfl _
      have := h1 _ hmem
      simpa using this
    | succ i ih =>
      intro hi
      have hilt : i < s.card := Nat.lt_of_succ_lt hi
      have hrec := ih hilt
      have hmem1 : (s.orderEmbOfFin rfl) ⟨i, hilt⟩ ∈ s := Finset.orderEmbOfFin_mem s rfl _
      have hmem2 : (s.orderEmbOfFin rfl) ⟨i+1, hi⟩ ∈ s := Finset.orderEmbOfFin_mem s rfl _
      have hlt : (⟨i, hilt⟩ : Fin s.card) < ⟨i+1, hi⟩ := Fin.mk_lt_mk.mpr (Nat.lt_succ_self i)
      have hlt' : (s.orderEmbOfFin rfl) ⟨i, hilt⟩ < (s.orderEmbOfFin rfl) ⟨i+1, hi⟩ :=
        (OrderEmbedding.lt_iff_lt (s.orderEmbOfFin rfl)).mpr hlt
      have hsp := hsep _ hmem1 _ hmem2 (ne_of_lt hlt')
      have hsp' : 1 ≤ (s.orderEmbOfFin rfl) ⟨i+1,hi⟩ - (s.orderEmbOfFin rfl) ⟨i,hilt⟩ := by
        rw [abs_of_neg (by linarith)] at hsp; linarith
      push_cast
      linarith
  have hcard_le : s.card ≤ A := by
    have := hkey (s.card - 1) (by omega)
    have hmem : (s.orderEmbOfFin rfl) ⟨s.card-1, by omega⟩ ∈ s := Finset.orderEmbOfFin_mem s rfl _
    have hAle := hle _ hmem
    have hck : ((s.card - 1 : ℕ) : ℝ) + 1 = (s.card : ℝ) := by
      rw [Nat.cast_sub hc, Nat.cast_one]; ring
    rw [hck] at this
    have : (s.card : ℝ) ≤ (A : ℝ) := le_trans this hAle
    exact_mod_cast this
  rw [hsum_eq]
  calc ∑ i : Fin s.card, (1:ℝ)/((s.orderEmbOfFin rfl) i)
      ≤ ∑ i : Fin s.card, (1:ℝ)/(((i:ℕ):ℝ)+1) := by
        apply Finset.sum_le_sum; intro i _
        have hk := hkey i.val i.isLt
        have hp : (0:ℝ) < ((i:ℕ):ℝ)+1 := by positivity
        exact one_div_le_one_div_of_le hp hk
    _ = ∑ k ∈ Finset.Icc 1 s.card, (1:ℝ)/(k:ℝ) := by
        rw [Fin.sum_univ_eq_sum_range (fun k => (1:ℝ)/(((k:ℕ):ℝ)+1)) s.card]
        have hIcc : Finset.Icc 1 s.card = Finset.Ico 1 (s.card+1) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hIcc, Finset.sum_Ico_eq_sum_range (fun k => (1:ℝ)/(k:ℝ)) 1 (s.card+1)]
        have h : s.card + 1 - 1 = s.card := by omega
        rw [h]
        apply Finset.sum_congr rfl; intro j _
        congr 1; push_cast; ring
    _ ≤ ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_Icc] at hx ⊢
          exact ⟨hx.1, le_trans hx.2 hcard_le⟩
        · intro x _ _; positivity

-- injectivity helper
lemma u_injective {R : ℕ} {u : Fin R → ℝ} (hsep : ∀ i j : Fin R, i ≠ j → 1 ≤ |u i - u j|) :
    Function.Injective u := by
  intro a b hab
  by_contra hne
  have := hsep a b hne
  rw [hab, sub_self, abs_zero] at this
  linarith

-- one-sided bound
lemma side_bound {R : ℕ} {u : Fin R → ℝ}
    (hsep : ∀ i j : Fin R, i ≠ j → 1 ≤ |u i - u j|)
    (i : Fin R) {Δ : ℝ} {A : ℕ} (hΔleA : Δ ≤ (A:ℝ))
    (T : Finset (Fin R)) (hTsub : ∀ j ∈ T, j ≠ i ∧ |u i - u j| ≤ Δ)
    (hTside : ∀ j ∈ T, u j < u i) :
    ∑ j ∈ T, (1:ℝ)/|u i - u j| ≤ ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) := by
  have hinj := u_injective hsep
  have hcong : ∑ j ∈ T, (1:ℝ)/|u i - u j| = ∑ j ∈ T, (1:ℝ)/(u i - u j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_of_nonneg (by linarith [hTside j hj])]
  rw [hcong]
  have hinjT : Set.InjOn (fun j : Fin R => u i - u j) ↑T := by
    intro x _ y _ hxy
    exact hinj (by linarith)
  rw [← Finset.sum_image (f := fun v : ℝ => (1:ℝ)/v) (g := fun j : Fin R => u i - u j) hinjT]
  apply sum_inv_le_of_sep_A
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hjT, rfl⟩ := hv
    have hj := hTsub j hjT
    have hlt := hTside j hjT
    have h1 : 1 ≤ |u i - u j| := by rw [abs_sub_comm]; exact hsep j i hj.1
    rw [abs_of_nonneg (by linarith)] at h1; linarith
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hjT, rfl⟩ := hv
    have hj := hTsub j hjT
    have hlt := hTside j hjT
    rw [abs_of_nonneg (by linarith)] at hj
    linarith [hj.2, hΔleA]
  · intro v hv w hw hvw
    rw [Finset.mem_image] at hv hw
    obtain ⟨j, hjT, rfl⟩ := hv
    obtain ⟨j', hjT', hjj'⟩ := hw
    have hne : j ≠ j' := by intro h; apply hvw; rw [h, hjj']
    have h := hsep j j' hne
    rw [← hjj', show u i - u j - (u i - u j') = -(u j - u j') by ring, abs_neg]
    exact h

theorem harmonic_separated :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (u : Fin R → ℝ),
      (∀ i j : Fin R, i ≠ j → 1 ≤ |u i - u j|) → ∀ (i : Fin R) (Δ : ℝ), 1 ≤ Δ →
      ∑ j ∈ (Finset.univ.filter (fun j : Fin R => j ≠ i ∧ |u i - u j| ≤ Δ)),
        (1 : ℝ) / |u i - u j| ≤ C * (1 + Real.log (Δ + 1)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro R u hsep i Δ hΔ
  have hA1 : 1 ≤ Nat.ceil Δ := Nat.ceil_pos.mpr (by linarith)
  have hAle : ((Nat.ceil Δ : ℕ):ℝ) ≤ Δ + 1 := le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hΔleA : Δ ≤ ((Nat.ceil Δ : ℕ):ℝ) := Nat.le_ceil Δ
  set A : ℕ := Nat.ceil Δ with hAdef
  set S : Finset (Fin R) := Finset.univ.filter (fun j : Fin R => j ≠ i ∧ |u i - u j| ≤ Δ) with hS
  have hSprop : ∀ j, j ∈ S ↔ (j ≠ i ∧ |u i - u j| ≤ Δ) := by intro j; rw [hS]; simp
  set P : Finset (Fin R) := S.filter (fun j => u j < u i) with hP
  set N : Finset (Fin R) := S.filter (fun j => u i < u j) with hN
  have hPN : S = P ∪ N := by
    ext j; rw [hP, hN]; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hj
      rcases lt_trichotomy (u j) (u i) with h | h | h
      · exact Or.inl ⟨hj, h⟩
      · exfalso; exact ((hSprop j).mp hj).1 (u_injective hsep h)
      · exact Or.inr ⟨hj, h⟩
    · rintro (⟨hj,_⟩ | ⟨hj,_⟩) <;> exact hj
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]; intro j hjP hjN
    rw [hP, Finset.mem_filter] at hjP; rw [hN, Finset.mem_filter] at hjN
    linarith [hjP.2, hjN.2]
  have hPbound : ∑ j ∈ P, (1:ℝ)/|u i - u j| ≤ ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) :=
    side_bound hsep i (by rw [hAdef]; exact hΔleA) P
      (fun j hj => (hSprop j).mp (by rw [hP, Finset.mem_filter] at hj; exact hj.1))
      (fun j hj => by rw [hP, Finset.mem_filter] at hj; exact hj.2)
  have hNbound : ∑ j ∈ N, (1:ℝ)/|u i - u j| ≤ ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) := by
    have hinj := u_injective hsep
    have hcong : ∑ j ∈ N, (1:ℝ)/|u i - u j| = ∑ j ∈ N, (1:ℝ)/(u j - u i) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hN, Finset.mem_filter] at hj
      rw [abs_of_nonpos (by linarith [hj.2])]; ring
    rw [hcong]
    have hinjN : Set.InjOn (fun j : Fin R => u j - u i) ↑N := by
      intro x _ y _ hxy; exact hinj (by linarith)
    rw [← Finset.sum_image (f := fun v : ℝ => (1:ℝ)/v) (g := fun j : Fin R => u j - u i) hinjN]
    apply sum_inv_le_of_sep_A
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨j, hjN, rfl⟩ := hv
      rw [hN, Finset.mem_filter] at hjN
      have hj := (hSprop j).mp hjN.1
      have h1 : 1 ≤ |u i - u j| := by rw [abs_sub_comm]; exact hsep j i hj.1
      rw [abs_of_nonpos (by linarith [hjN.2])] at h1; linarith
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨j, hjN, rfl⟩ := hv
      rw [hN, Finset.mem_filter] at hjN
      have hj := (hSprop j).mp hjN.1
      rw [abs_of_nonpos (by linarith [hjN.2])] at hj
      linarith [hj.2, hΔleA]
    · intro v hv w hw hvw
      rw [Finset.mem_image] at hv hw
      obtain ⟨j, hjN, rfl⟩ := hv
      obtain ⟨j', hjN', hjj'⟩ := hw
      have hne : j ≠ j' := by intro h; apply hvw; rw [h, hjj']
      have h := hsep j j' hne
      rw [← hjj', show u j - u i - (u j' - u i) = u j - u j' by ring]
      exact h
  have hlog : ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) ≤ 1 + Real.log (Δ + 1) := by
    have h1 : ∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ) ≤ 1 + Real.log (A:ℝ) :=
      Commons.Analysis.ExpLog.harmonic_le_one_add_log A hA1
    have h2 : Real.log (A:ℝ) ≤ Real.log (Δ+1) := by
      apply Real.log_le_log (by positivity)
      rw [hAdef]; exact hAle
    linarith
  rw [hPN, Finset.sum_union hdisj]
  calc ∑ j ∈ P, (1:ℝ)/|u i - u j| + ∑ j ∈ N, (1:ℝ)/|u i - u j|
      ≤ (∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ)) + (∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ)) :=
        add_le_add hPbound hNbound
    _ = 2 * (∑ k ∈ Finset.Icc 1 A, (1:ℝ)/(k:ℝ)) := by ring
    _ ≤ 2 * (1 + Real.log (Δ+1)) := by linarith

/-- Log absorption: for every `ε > 0`, `1 + log(x+1) ≤ C·x^ε` for all `x ≥ 1`. -/
private lemma log_absorb (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → 1 + Real.log (x+1) ≤ C * x^ε := by
  refine ⟨1 + Real.log 2 + 1/ε, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : 0 < x + 1 := by linarith
  have hle : Real.log (x+1) ≤ Real.log (2*x) := Real.log_le_log hx1 (by nlinarith)
  have h2x : Real.log (2*x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) (ne_of_gt hx0)
  have hlogx : Real.log x ≤ x^ε / ε := Commons.Analysis.ExpLog.log_le_rpow_div hx hε
  have hxe : 1 ≤ x^ε := Real.one_le_rpow hx hε.le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc 1 + Real.log (x+1) ≤ 1 + Real.log (2*x) := by linarith
    _ = 1 + (Real.log 2 + Real.log x) := by rw [h2x]
    _ ≤ 1 + (Real.log 2 + x^ε / ε) := by linarith
    _ = (1 + Real.log 2) + x^ε * (1/ε) := by ring
    _ ≤ (1 + Real.log 2) * x^ε + (1/ε) * x^ε := by
        have : (1 + Real.log 2) * 1 ≤ (1 + Real.log 2) * x^ε :=
          mul_le_mul_of_nonneg_left hxe (by linarith)
        nlinarith [this]
    _ = (1 + Real.log 2 + 1/ε) * x^ε := by ring

/-- Row arithmetic for the `c ≡ 1` estimate, valid for all `N > 0` (no `N ≤ Δ` needed). -/
private lemma arith_final (K Ch Cl ε : ℝ) (hK : 0 ≤ K) (hCh : 0 ≤ Ch) (hCl : 0 ≤ Cl)
    (N R Δ IT : ℝ) (hN : 0 < N) (hR : 0 ≤ R) (hIT : 0 ≤ IT) (hΔ0 : 0 ≤ Δ)
    (hΔε : 1 ≤ Δ ^ ε) (hlog : 1 + Real.log (Δ + 1) ≤ Cl * Δ ^ ε) :
    4*N*R + 2*K * ((Δ/N)*IT + R*(N*(Ch*(1+Real.log (Δ+1)))))
      ≤ (4 + 2*K*Ch*Cl + 2*K) * Δ^ε * (N*R + (Δ/N)*IT) := by
  have hG : 0 ≤ (Δ/N)*IT := by positivity
  have hNR : 0 ≤ N*R := by positivity
  have hΔε0 : 0 ≤ Δ^ε := by linarith
  have h2K : (0:ℝ) ≤ 2*K := by linarith
  have hstep1 : 4*N*R ≤ 4*Δ^ε*(N*R) := by nlinarith [hΔε, hNR]
  have hstep2 : 2*K*((Δ/N)*IT) ≤ 2*K*Δ^ε*((Δ/N)*IT) := by
    have h : (Δ/N)*IT ≤ Δ^ε*((Δ/N)*IT) := by nlinarith [hΔε, hG]
    nlinarith [mul_le_mul_of_nonneg_left h h2K]
  have hstep3 : 2*K*(R*(N*(Ch*(1+Real.log (Δ+1))))) ≤ 2*K*Ch*Cl*Δ^ε*(N*R) := by
    have he1 : Ch*(1+Real.log (Δ+1)) ≤ Ch*(Cl*Δ^ε) := mul_le_mul_of_nonneg_left hlog hCh
    have he1' : Ch*(1+Real.log (Δ+1)) ≤ Ch*Cl*Δ^ε := by nlinarith [he1]
    have hL : 2*K*(R*(N*(Ch*(1+Real.log (Δ+1))))) = (2*K)*(R*N)*(Ch*(1+Real.log (Δ+1))) := by ring
    have hR' : 2*K*Ch*Cl*Δ^ε*(N*R) = (2*K)*(R*N)*(Ch*Cl*Δ^ε) := by ring
    rw [hL, hR']
    exact mul_le_mul_of_nonneg_left he1' (by positivity : (0:ℝ) ≤ (2*K)*(R*N))
  have hfin : 4*Δ^ε*(N*R) + 2*K*Δ^ε*((Δ/N)*IT) + 2*K*Ch*Cl*Δ^ε*(N*R)
      ≤ (4 + 2*K*Ch*Cl + 2*K) * Δ^ε * (N*R + (Δ/N)*IT) := by
    rw [show 4*Δ^ε*(N*R) + 2*K*Δ^ε*((Δ/N)*IT) + 2*K*Ch*Cl*Δ^ε*(N*R)
        = Δ^ε * (4*(N*R) + 2*K*((Δ/N)*IT) + 2*K*Ch*Cl*(N*R)) from by ring]
    rw [show (4 + 2*K*Ch*Cl + 2*K) * Δ^ε * (N*R + (Δ/N)*IT)
        = Δ^ε * ((4 + 2*K*Ch*Cl + 2*K) * (N*R + (Δ/N)*IT)) from by ring]
    apply mul_le_mul_of_nonneg_left _ hΔε0
    have hexp : (4 + 2*K*Ch*Cl + 2*K) * (N*R + (Δ/N)*IT)
        = 4*(N*R) + 2*K*Ch*Cl*(N*R) + 2*K*(N*R) + 4*((Δ/N)*IT)
          + 2*K*Ch*Cl*((Δ/N)*IT) + 2*K*((Δ/N)*IT) := by ring
    rw [hexp]
    have h2KNR : 0 ≤ 2*K*(N*R) := by positivity
    have h4G : 0 ≤ 4*((Δ/N)*IT) := by linarith [hG]
    have hKChClG : 0 ≤ 2*K*Ch*Cl*((Δ/N)*IT) := by positivity
    linarith [h2KNR, h4G, hKChClG]
  calc 4*N*R + 2*K * ((Δ/N)*IT + R*(N*(Ch*(1+Real.log (Δ+1)))))
      = 4*N*R + 2*K*((Δ/N)*IT) + 2*K*(R*(N*(Ch*(1+Real.log (Δ+1))))) := by ring
    _ ≤ 4*Δ^ε*(N*R) + 2*K*Δ^ε*((Δ/N)*IT) + 2*K*Ch*Cl*Δ^ε*(N*R) := by
        linarith [hstep1, hstep2, hstep3]
    _ ≤ (4 + 2*K*Ch*Cl + 2*K) * Δ^ε * (N*R + (Δ/N)*IT) := hfin

/-- **Mean-value difference-set bound, `c ≡ 1`.** For every `ε > 0` there is `C > 0` such
that for all `N ≥ 1`, `Δ ≥ 1` and every `1`-separated family `t : Fin R → ℝ`,
`∑_{i,j: |t_i-t_j|≤Δ} ‖∑_{N≤n≤2N} n^{-1/2+i(t_i-t_j)}‖² ≤ C·Δ^ε·(N·R + (Δ/N)·#{|t_i-t_j|≤Δ})`.
Unlike the earlier `N ≤ Δ` version this needs no restriction between `N` and `Δ`. -/
theorem mv_difference_small_delta_one :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * Δ ^ ε *
      ((N : ℝ) * (R : ℝ) + Δ * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then (1 : ℝ) else 0)) / (N : ℝ)) := by
  intro ε hε
  obtain ⟨K, hKpos, hK⟩ := weighted_logsum_pointwise_all
  obtain ⟨Ch, hChpos, hCh⟩ := harmonic_separated
  obtain ⟨Cl, hClpos, hCl⟩ := log_absorb ε hε
  refine ⟨4 + 2 * K * Ch * Cl + 2 * K, by positivity, ?_⟩
  intro N hN Δ hΔ R t hsep
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hΔ1 : (0:ℝ) < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hΔε1 : (1:ℝ) ≤ Δ^ε := Real.one_le_rpow hΔ hε.le
  set D : ℝ → ℂ := fun θ => ∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ) with hDdef
  have hDval : ∀ θ : ℝ, D θ = ∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ) := by
    intro θ; simp only [hDdef]
  have hDconj : ∀ θ : ℝ, D (-θ) = starRingEnd ℂ (D θ) := by
    intro θ
    rw [hDval, hDval, map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hcj : starRingEnd ℂ (Complex.I*(θ:ℂ)) = -(Complex.I*(θ:ℂ)) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    have hden : starRingEnd ℂ (((Real.sqrt (n:ℝ):ℝ)):ℂ) = (((Real.sqrt (n:ℝ):ℝ)):ℂ) := by simp
    have hexp : -(Complex.I*(θ:ℂ)) = Complex.I*((-θ:ℝ):ℂ) := by push_cast; ring
    have hkey : starRingEnd ℂ ((n:ℂ)^(Complex.I*(θ:ℂ))) = (n:ℂ)^(Complex.I*((-θ:ℝ):ℂ)) := by
      rw [← Complex.ofReal_natCast n]
      rw [starRingEnd_cpow_ofReal_nonneg (n:ℝ) hnpos.le (Complex.I*(θ:ℂ)), hcj, hexp]
    rw [map_div₀, hkey, hden]
  have hDabs : ∀ θ : ℝ, ‖D θ‖ = ‖D |θ|‖ := by
    intro θ
    by_cases h : 0 ≤ θ
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), hDconj θ, Complex.norm_conj]
  have hDpoint : ∀ θ : ℝ, 1 ≤ |θ| → ‖D θ‖^2 ≤ K*(|θ|/(N:ℝ) + (N:ℝ)/|θ| + 1) := by
    intro θ hθ
    rw [hDabs θ, hDval (|θ|)]
    exact hK N hN |θ| hθ
  have hDpoint2 : ∀ θ : ℝ, 1 ≤ |θ| → ‖D θ‖^2 ≤ 2*K*(|θ|/(N:ℝ) + (N:ℝ)/|θ|) := by
    intro θ hθ
    have ha : (0:ℝ) < |θ| := lt_of_lt_of_le zero_lt_one hθ
    have hx0 : 0 ≤ |θ|/(N:ℝ) := div_nonneg (abs_nonneg θ) hNpos.le
    have hy0 : 0 ≤ (N:ℝ)/|θ| := div_nonneg hNpos.le (abs_nonneg θ)
    have hxy : (|θ|/(N:ℝ)) * ((N:ℝ)/|θ|) = 1 := by
      rw [div_mul_div_comm, mul_comm (N:ℝ) |θ|, div_self (mul_ne_zero ha.ne' hNpos.ne')]
    have h1 : 1 ≤ |θ|/(N:ℝ) + (N:ℝ)/|θ| := by
      nlinarith [sq_nonneg (|θ|/(N:ℝ) - (N:ℝ)/|θ|), hx0, hy0, hxy]
    have hle : |θ|/(N:ℝ) + (N:ℝ)/|θ| + 1 ≤ 2*(|θ|/(N:ℝ) + (N:ℝ)/|θ|) := by linarith
    have hstep := mul_le_mul_of_nonneg_left hle hKpos.le
    have hp := hDpoint θ hθ
    nlinarith [hp, hstep]
  have hDle : ∀ θ : ℝ, ‖D θ‖ ≤ 2*Real.sqrt (N:ℝ) := by
    intro θ
    rw [hDval θ]
    calc ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖
        ≤ ∑ n ∈ Finset.Icc N (2*N), ‖(n:ℂ)^(Complex.I*(θ:ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc N (2*N), (Real.sqrt (n:ℝ))⁻¹ := by
          apply Finset.sum_le_sum; intro n hn
          have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
          have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          rw [norm_div]
          have hc : ‖(n:ℂ)^(Complex.I*(θ:ℂ))‖ = 1 := by
            rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n) (Complex.I*(θ:ℂ))]
            have hre : (Complex.I*(θ:ℂ)).re = 0 := by simp
            rw [hre, Real.rpow_zero]
          have hden : ‖((Real.sqrt (n:ℝ):ℝ):ℂ)‖ = Real.sqrt (n:ℝ) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [hc, hden, one_div]
      _ ≤ 2*Real.sqrt (N:ℝ) := by
          have hterm : ∀ n ∈ Finset.Icc N (2*N), (Real.sqrt (n:ℝ))⁻¹ ≤ (Real.sqrt (N:ℝ))⁻¹ := by
            intro n hn
            have hnN : N ≤ n := (Finset.mem_Icc.mp hn).1
            have hle : Real.sqrt (N:ℝ) ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hnN)
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hNpos) hle
          calc ∑ n ∈ Finset.Icc N (2*N), (Real.sqrt (n:ℝ))⁻¹
              ≤ ∑ _n ∈ Finset.Icc N (2*N), (Real.sqrt (N:ℝ))⁻¹ := Finset.sum_le_sum hterm
            _ = ((Finset.Icc N (2*N)).card : ℝ) * (Real.sqrt (N:ℝ))⁻¹ := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 2*Real.sqrt (N:ℝ) := by
                have hcard : ((Finset.Icc N (2*N)).card : ℝ) = (N:ℝ) + 1 := by
                  rw [Nat.card_Icc]
                  have : 2*N + 1 - N = N + 1 := by omega
                  rw [this]; push_cast; ring
                rw [hcard, inv_eq_one_div, mul_one_div, div_le_iff₀ (Real.sqrt_pos.mpr hNpos)]
                have hs : Real.sqrt (N:ℝ) * Real.sqrt (N:ℝ) = (N:ℝ) := Real.mul_self_sqrt hNpos.le
                have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
                nlinarith [hs]
  have hD0 : ‖D 0‖^2 ≤ 4*(N:ℝ) := by
    have h1 := hDle 0
    have h2 : (2*Real.sqrt (N:ℝ))^2 = 4*(N:ℝ) := by
      rw [mul_pow, Real.sq_sqrt hNpos.le]; ring
    nlinarith [h1, norm_nonneg (D 0), Real.sqrt_nonneg (N:ℝ)]
  set Si : Fin R → Finset (Fin R) := fun i => Finset.univ.filter (fun j => j ≠ i ∧ |t i - t j| ≤ Δ) with hSidef
  have hSiprop : ∀ i j : Fin R, j ∈ Si i ↔ (j ≠ i ∧ |t i - t j| ≤ Δ) := by
    intro i j; rw [hSidef]; simp
  have hrow : ∀ i : Fin R,
      (∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
      ≤ 4*(N:ℝ) + 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ)
          + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) ) := by
    intro i
    have hsplit : (∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
        = (∑ j ∈ Finset.univ.erase i, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
          + (if |t i - t i| ≤ Δ then ‖D (t i - t i)‖^2 else 0) :=
      (Finset.sum_erase_add Finset.univ
        (fun j : Fin R => (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
        (Finset.mem_univ i)).symm
    rw [hsplit]
    have hfi : (if |t i - t i| ≤ Δ then ‖D (t i - t i)‖^2 else 0) ≤ 4*(N:ℝ) := by
      have hc : |t i - t i| ≤ Δ := by rw [sub_self, abs_zero]; linarith
      rw [if_pos hc, sub_self]
      exact hD0
    have hcong : ∑ j ∈ Finset.univ.erase i, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0)
        = ∑ j ∈ Si i, ‖D (t i - t j)‖^2 := by
      have he : Finset.univ.erase i = Finset.univ.filter (fun j : Fin R => j ≠ i) := by
        ext j; simp [Finset.mem_erase]
      rw [he, ← Finset.sum_filter, hSidef, Finset.filter_filter]
    have hpt2 : ∀ j ∈ Si i, ‖D (t i - t j)‖^2 ≤ 2*K*(|t i - t j|/(N:ℝ) + (N:ℝ)/|t i - t j|) := by
      intro j hj
      have hjne : j ≠ i := ((hSiprop i j).mp hj).1
      have h1 : 1 ≤ |t i - t j| := by
        have := hsep j i hjne
        rwa [abs_sub_comm] at this
      exact hDpoint2 (t i - t j) h1
    have hsum1 : ∑ j ∈ Si i, |t i - t j|/(N:ℝ) ≤ (Δ/(N:ℝ)) * ((Si i).card : ℝ) := by
      rw [← Finset.sum_div]
      have h2 : (∑ j ∈ Si i, |t i - t j|) ≤ Δ * ((Si i).card : ℝ) := by
        calc ∑ j ∈ Si i, |t i - t j| ≤ ∑ _j ∈ Si i, Δ :=
              Finset.sum_le_sum (fun j hj => ((hSiprop i j).mp hj).2)
          _ = Δ * ((Si i).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      calc (∑ j ∈ Si i, |t i - t j|)/(N:ℝ) ≤ (Δ * ((Si i).card : ℝ))/(N:ℝ) :=
            div_le_div_of_nonneg_right h2 hNpos.le
        _ = (Δ/(N:ℝ)) * ((Si i).card : ℝ) := by ring
    have hsum2 : ∑ j ∈ Si i, (N:ℝ)/|t i - t j| ≤ (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) := by
      have he : ∑ j ∈ Si i, (N:ℝ)/|t i - t j| = (N:ℝ) * ∑ j ∈ Si i, 1/|t i - t j| := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [div_eq_mul_inv, one_div]
      rw [he]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      rw [hSidef]
      exact hCh R t hsep i Δ hΔ
    have hmain : ∑ j ∈ Si i, ‖D (t i - t j)‖^2
        ≤ 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ) + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) ) := by
      calc ∑ j ∈ Si i, ‖D (t i - t j)‖^2
          ≤ ∑ j ∈ Si i, 2*K*(|t i - t j|/(N:ℝ) + (N:ℝ)/|t i - t j|) := Finset.sum_le_sum hpt2
        _ = 2*K * (∑ j ∈ Si i, |t i - t j|/(N:ℝ)) + 2*K * (∑ j ∈ Si i, (N:ℝ)/|t i - t j|) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ 2*K * ((Δ/(N:ℝ)) * ((Si i).card : ℝ)) + 2*K * ((N:ℝ) * (Ch * (1 + Real.log (Δ+1)))) := by
            have ha := mul_le_mul_of_nonneg_left hsum1 (by linarith [hKpos.le] : (0:ℝ) ≤ 2*K)
            have hb := mul_le_mul_of_nonneg_left hsum2 (by linarith [hKpos.le] : (0:ℝ) ≤ 2*K)
            linarith [ha, hb]
        _ = 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ) + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) ) := by ring
    rw [hcong]
    linarith [hfi, hmain]
  have hcard_le : ∀ i : Fin R, ((Si i).card : ℝ)
      ≤ ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1:ℝ) else 0) := by
    intro i
    have hsub : Si i ⊆ Finset.univ.filter (fun j : Fin R => |t i - t j| ≤ Δ) := by
      intro j hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, ((hSiprop i j).mp hj).2⟩
    have h1 : (Si i).card ≤ (Finset.univ.filter (fun j : Fin R => |t i - t j| ≤ Δ)).card :=
      Finset.card_le_card hsub
    have h2 : ((Finset.univ.filter (fun j : Fin R => |t i - t j| ≤ Δ)).card : ℝ)
        = ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1:ℝ) else 0) := by
      rw [Finset.card_filter]; push_cast; rfl
    have : ((Si i).card : ℝ) ≤ ((Finset.univ.filter (fun j : Fin R => |t i - t j| ≤ Δ)).card : ℝ) := by
      exact_mod_cast h1
    rw [h2] at this
    exact this
  set IT : ℝ := ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1:ℝ) else 0) with hITdef
  have hM : (∑ i : Fin R, ((Si i).card : ℝ)) ≤ IT := by
    rw [hITdef]
    calc ∑ i : Fin R, ((Si i).card : ℝ) ≤ ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1:ℝ) else 0) :=
          Finset.sum_le_sum (fun i _ => hcard_le i)
      _ = _ := rfl
  have hITnn : 0 ≤ IT := by
    rw [hITdef]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
  have hmain : (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
      ≤ 4*(N:ℝ)*(R:ℝ) + 2*K * ((Δ/(N:ℝ))*IT + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1))))) := by
    have h1 : (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
        ≤ ∑ i : Fin R, (4*(N:ℝ) + 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ)
            + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) )) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    have heq : (∑ i : Fin R, (4*(N:ℝ) + 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ)
            + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) )))
        = 4*(N:ℝ)*(R:ℝ) + 2*K * ((Δ/(N:ℝ))*(∑ i, ((Si i).card : ℝ))
            + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1))))) := by
      have h1' : (∑ i : Fin R, 4*(N:ℝ)) = 4*(N:ℝ)*(R:ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have h2' : (∑ i : Fin R, 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ)
              + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) ))
          = 2*K * ((Δ/(N:ℝ))*(∑ i, ((Si i).card : ℝ))
              + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1))))) := by
        rw [← Finset.mul_sum]
        congr 1
        have hs1 : (∑ i : Fin R, (Δ/(N:ℝ)) * ((Si i).card : ℝ))
            = (Δ/(N:ℝ))*(∑ i, ((Si i).card : ℝ)) := by rw [Finset.mul_sum]
        have hs2 : (∑ _i : Fin R, (N:ℝ) * (Ch * (1 + Real.log (Δ+1))))
            = (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.sum_add_distrib, hs1, hs2]
      calc ∑ i : Fin R, (4*(N:ℝ) + 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ)
              + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) ))
          = (∑ i : Fin R, 4*(N:ℝ))
            + (∑ i : Fin R, 2*K * ( (Δ/(N:ℝ)) * ((Si i).card : ℝ)
              + (N:ℝ) * (Ch * (1 + Real.log (Δ+1))) )) := by
              rw [Finset.sum_add_distrib]
        _ = 4*(N:ℝ)*(R:ℝ) + 2*K * ((Δ/(N:ℝ))*(∑ i, ((Si i).card : ℝ))
            + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1))))) := by
              rw [h1', h2']
    rw [heq] at h1
    have hle : 2*K * ((Δ/(N:ℝ))*(∑ i, ((Si i).card : ℝ))
            + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1)))))
        ≤ 2*K * ((Δ/(N:ℝ))*IT + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1))))) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith [hKpos.le] : (0:ℝ) ≤ 2*K)
      have hd : (0:ℝ) ≤ Δ/(N:ℝ) := by positivity
      have h1'' : (Δ/(N:ℝ))*(∑ i, ((Si i).card : ℝ)) ≤ (Δ/(N:ℝ))*IT :=
        mul_le_mul_of_nonneg_left hM hd
      linarith [h1'']
    linarith [h1, hle]
  have hlog : (1 + Real.log (Δ+1)) ≤ Cl * Δ^ε := hCl Δ hΔ
  calc (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖D (t i - t j)‖^2 else 0))
      ≤ 4*(N:ℝ)*(R:ℝ) + 2*K * ((Δ/(N:ℝ))*IT + (R:ℝ)*((N:ℝ)*(Ch*(1+Real.log (Δ+1))))) := hmain
    _ ≤ (4 + 2*K*Ch*Cl + 2*K) * Δ^ε * ((N:ℝ)*(R:ℝ) + (Δ/(N:ℝ))*IT) :=
        arith_final K Ch Cl ε hKpos.le hChpos.le hClpos.le (N:ℝ) (R:ℝ) Δ IT hNpos
          (Nat.cast_nonneg R) hITnn hΔ1.le hΔε1 hlog
    _ = (4 + 2*K*Ch*Cl + 2*K) * Δ^ε * ((N:ℝ)*(R:ℝ) + Δ*(∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1:ℝ) else 0))/(N:ℝ)) := by
        rw [hITdef]; ring

/-- **Main theorem.** For every `ε > 0` there is `C > 0` such that for all `N ≥ 1`, `Δ ≥ 1`,
all `B ≥ 1`, every coefficient sequence `c` with `‖c n‖ ≤ B`, and every `1`-separated family
`t : Fin R → ℝ`,
`∑_{i,j: |t_i-t_j|≤Δ} ‖∑_{N≤n≤2N} c_n n^{-1/2+i(t_i-t_j)}‖²
   ≤ C·B²·Δ^ε·(N·R + (Δ/N)·#{|t_i-t_j|≤Δ})`. -/
theorem mv_difference_small_delta :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * B ^ 2 * Δ ^ ε *
      ((N : ℝ) * (R : ℝ)
        + Δ * (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0)) / (N : ℝ)) := by
  intro ε hε
  obtain ⟨C1, hC1pos, hC1⟩ := mv_difference_small_delta_one ε hε
  obtain ⟨Cm, hCmpos, hMaj⟩ := kerr_coefficient_majorant
  refine ⟨Cm * C1, by positivity, ?_⟩
  intro N hN Δ hΔ B hB c hc R t hsep
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hmaj := hMaj N hN Δ hΔ0 B hB c hc R t hsep
  have hone := hC1 N hN Δ hΔ R t hsep
  have hB2 : (0:ℝ) ≤ Cm * B^2 := by positivity
  calc (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      ≤ Cm * B^2 * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) := hmaj
    _ ≤ Cm * B^2 * (C1 * Δ^ε * ((N:ℝ)*(R:ℝ) + Δ * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ Δ then (1:ℝ) else 0)) / (N:ℝ))) := mul_le_mul_of_nonneg_left hone hB2
    _ = (Cm * C1) * B^2 * Δ^ε * ((N:ℝ)*(R:ℝ) + Δ * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ Δ then (1:ℝ) else 0)) / (N:ℝ)) := by ring

end

end Commons.NumberTheory.DirichletPolynomial
