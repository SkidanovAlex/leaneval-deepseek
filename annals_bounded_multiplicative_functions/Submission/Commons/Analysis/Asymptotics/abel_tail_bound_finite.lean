import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Real BigOperators Interval
set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

private lemma cpow_integral_sub (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ((-s) * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1)))
      = (((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)) := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    rw [Set.uIcc_of_le hkle, Set.mem_Icc] at hx
    linarith [show 0 < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
  have hne : -s - 1 ≠ (-1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hs]
  have hint := integral_cpow (r := -s - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
    (Or.inr ⟨hne, hnot0⟩)
  have hD : -s - 1 + 1 = -s := by ring
  have hsnz : -s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hs]
  rw [hint, hD]
  rw [mul_div_cancel₀ _ hsnz]
  simp

private lemma rpow_integral_sub (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1))
      = ((k : ℝ) ^ (-σ) - (((k + 1 : ℕ) : ℝ) ^ (-σ))) / σ := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    rw [Set.uIcc_of_le hkle, Set.mem_Icc] at hx
    linarith [show 0 < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
  have hne : -σ - 1 ≠ (-1 : ℝ) := by linarith
  have hint := integral_rpow (r := -σ - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
    (Or.inr ⟨hne, hnot0⟩)
  rw [hint]
  have hD : -σ - 1 + 1 = -σ := by ring
  rw [hD]
  field_simp [show σ ≠ 0 by linarith]
  ring

private lemma integral_norm_cpow_sub (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖)
      = (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖)
        = ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-(s.re) - 1) := by
            apply intervalIntegral.integral_congr
            intro x hx
            dsimp
            have hx0 : (k : ℝ) ≤ x := by
              have : x ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := hx
              rw [Set.uIcc_of_le hkle, Set.mem_Icc] at this
              exact this.1
            have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
            have hxpos : 0 < x := lt_of_lt_of_le hkpos hx0
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (y := -s - 1)]
            have hre : Complex.re (-s - 1) = -(s.re) - 1 := by
              simp [Complex.neg_re, Complex.sub_re, Complex.one_re]
            rw [hre]
    _ = (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re := by
            simpa using (rpow_integral_sub k hk (s.re) hs)

private lemma norm_cpow_sub_le (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ‖((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)‖
      ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
  have hdiff : ((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s) = (-s) * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1)) :=
    (cpow_integral_sub k hk s hs).symm
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    ‖((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)‖
        = ‖(-s) * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))‖ := by rw [hdiff]
    _ ≤ ‖(-s)‖ * ‖∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1)‖ := norm_mul_le _ _
    _ = ‖s‖ * ‖∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1)‖ := by rw [norm_neg]
    _ ≤ ‖s‖ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖) := by
            exact mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm hkle) (norm_nonneg s)
    _ = ‖s‖ * ((((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re) := by rw [integral_norm_cpow_sub k hk s hs]
    _ = (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            ring

private lemma sum_Icc_mul_eq (a f : ℕ → ℂ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Icc N M, a k * f k)
      = (∑ k ∈ Finset.Icc N M, a k) * f M
        + ∑ k ∈ Finset.Icc N (M - 1), (∑ n ∈ Finset.Icc N k, a n) * (f k - f (k + 1)) := by
  let S : ℕ → ℂ := fun k => ∑ n ∈ Finset.Icc N k, a n
  let P : ℕ → Prop := fun m => N ≤ m →
      (∑ k ∈ Finset.Icc N m, a k * f k)
        = (∑ k ∈ Finset.Icc N m, a k) * f m
          + ∑ k ∈ Finset.Icc N (m - 1), S k * (f k - f (k + 1))
  have hbase : P N := by
    intro hNle
    have hmm : Finset.Icc N (N - 1) = ∅ := by
      exact Finset.Icc_eq_empty_iff.mpr (by omega : ¬ N ≤ N - 1)
    simp [S, hmm]
  have hstep : ∀ m : ℕ, N ≤ m → P m → P (m + 1) := by
    intro m hm hPm hNle
    have hmpos : 0 < m := by omega
    have hsplit (g : ℕ → ℂ) : (∑ k ∈ Finset.Icc N m, g k)
        = (∑ k ∈ Finset.Icc N (m - 1), g k) + g m := by
      have htop : m = m - 1 + 1 := by omega
      calc
        (∑ k ∈ Finset.Icc N m, g k)
            = ∑ k ∈ Finset.Icc N (m - 1 + 1), g k := by
                exact congrArg (fun t => ∑ k ∈ Finset.Icc N t, g k) htop
        _ = (∑ k ∈ Finset.Icc N (m - 1), g k) + g (m - 1 + 1) := by
                rw [Finset.sum_Icc_succ_top (a := N) (b := m - 1) (f := g)
                  (by simpa [show (m - 1) + 1 = m by omega] using hm)]
        _ = (∑ k ∈ Finset.Icc N (m - 1), g k) + g m := by
                exact congrArg (fun x => (∑ k ∈ Finset.Icc N (m - 1), g k) + g x)
                  (by omega : (m - 1) + 1 = m)
    calc
      (∑ k ∈ Finset.Icc N (m + 1), a k * f k)
          = (∑ k ∈ Finset.Icc N m, a k * f k) + a (m + 1) * f (m + 1) := by
              simpa using (Finset.sum_Icc_succ_top (a := N) (b := m) (f := fun k => a k * f k)
                (by omega : N ≤ m + 1))
      _ = (∑ k ∈ Finset.Icc N m, a k) * f m + a (m + 1) * f (m + 1)
            + ∑ k ∈ Finset.Icc N (m - 1), S k * (f k - f (k + 1)) := by
            rw [hPm hm]
            ring
      _ = (∑ k ∈ Finset.Icc N (m + 1), a k) * f (m + 1)
            + ∑ k ∈ Finset.Icc N m, S k * (f k - f (k + 1)) := by
            have hAm : (∑ k ∈ Finset.Icc N (m + 1), a k) = (∑ k ∈ Finset.Icc N m, a k) + a (m + 1) := by
              simpa using (Finset.sum_Icc_succ_top (a := N) (b := m) (f := a) (by omega : N ≤ m + 1))
            rw [hAm]
            rw [hsplit (fun k => S k * (f k - f (k + 1)))]
            dsimp [S]
            ring
  have hall : ∀ m : ℕ, N ≤ m → P m := by
    intro m
    induction' m with m ih
    · intro h; omega
    · intro hNle
      by_cases hm : N ≤ m
      · exact hstep m hm (ih hm)
      · have hm_eq : m + 1 = N := by omega
        rw [hm_eq]
        exact hbase
  exact hall M hNM hNM

private lemma sum_Icc_sub_down (g : ℕ → ℝ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Icc N (M - 1), (g k - g (k + 1))) = g N - g M := by
  by_cases hMN : M = N
  · subst M
    have hmm : Finset.Icc N (N - 1) = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega : ¬ N ≤ N - 1)
    simp [hmm]
  · have hNltM : N < M := lt_of_le_of_ne hNM (by omega : N ≠ M)
    have hle : N ≤ M - 1 := by omega
    have hM1 : M - 1 + 1 = M := by omega
    have h := Finset.sum_Icc_sub (m := N) (n := M - 1) (f := g) hle
    rw [hM1] at h
    calc
      (∑ k ∈ Finset.Icc N (M - 1), (g k - g (k + 1)))
          = -∑ k ∈ Finset.Icc N (M - 1), (g (k + 1) - g k) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = -(g M - g N) := by rw [h]
      _ = g N - g M := by ring

private lemma norm_cpow_neg (k : ℕ) (hk : 1 ≤ k) (s : ℂ) :
    ‖(k : ℂ) ^ (-s)‖ = (k : ℝ) ^ (-s.re) := by
  have hk0 : 0 < k := by omega
  rw [Complex.norm_natCast_cpow_of_pos hk0 (-s)]
  simp

private lemma rpow_neg_mono {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (σ : ℝ) (hσ : 0 < σ) :
    (y : ℝ) ^ (-σ) ≤ (x : ℝ) ^ (-σ) := by
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hy0 : 0 < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hle : (x : ℝ) ^ σ ≤ (y : ℝ) ^ σ := by
    exact Real.rpow_le_rpow (le_of_lt hx0) (by exact_mod_cast hxy) (le_of_lt hσ)
  calc
    (y : ℝ) ^ (-σ) = ((y : ℝ) ^ σ)⁻¹ := by rw [Real.rpow_neg (le_of_lt hy0)]
    _ ≤ ((x : ℝ) ^ σ)⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hy0 σ) (Real.rpow_pos_of_pos hx0 σ)).mpr hle
    _ = (x : ℝ) ^ (-σ) := by rw [Real.rpow_neg (le_of_lt hx0)]

private lemma rpow_neg_pos (x : ℕ) (hx : 1 ≤ x) (σ : ℝ) : 0 < (x : ℝ) ^ (-σ) := by
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  exact Real.rpow_pos_of_pos hx0 (-σ)

/-- Finite Abel (partial summation) tail bound: if contiguous sums of `a : ℕ → ℂ`
over `Icc x y` are bounded by `B`, then for `0 < s.re` and `1 ≤ N ≤ M`,
`‖∑_{k=N}^{M} a k · k^(-s)‖ ≤ B · N^(-s.re) · (1 + ‖s‖ / s.re)`. -/
theorem abel_tail_bound_finite {a : ℕ → ℂ} (B : ℝ) (hB : ∀ x y : ℕ, x ≤ y →
    ‖∑ n ∈ Finset.Icc x y, a n‖ ≤ B) (s : ℂ) (hs : 0 < s.re)
    {N M : ℕ} (hNM : N ≤ M) (hN1 : 1 ≤ N) :
    ‖∑ k ∈ Finset.Icc N M, a k * (k : ℂ) ^ (-s)‖
      ≤ B * (N : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  let f : ℕ → ℂ := fun k => (k : ℂ) ^ (-s)
  let A : ℕ → ℂ := fun k => ∑ n ∈ Finset.Icc N k, a n
  let g : ℕ → ℝ := fun k => (k : ℝ) ^ (-s.re)
  let C : ℝ := ‖s‖ / s.re
  have hf (k : ℕ) (hk : 1 ≤ k) : ‖f k‖ = g k := by
    dsimp [f, g]
    exact norm_cpow_neg k hk s
  have hA (k : ℕ) (hk : N ≤ k) : ‖A k‖ ≤ B := by
    dsimp [A]
    exact hB N k hk
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB N M hNM)
  have hC0 : 0 ≤ C := div_nonneg (norm_nonneg s) (le_of_lt hs)
  have hBC0 : 0 ≤ B * C := mul_nonneg hB0 hC0
  have hM1 : 1 ≤ M := le_trans hN1 hNM
  have hgMN : g M ≤ g N := by
    dsimp [g]
    exact rpow_neg_mono hN1 hNM (s.re) hs
  have hgM0 : 0 ≤ g M := le_of_lt (by dsimp [g]; exact rpow_neg_pos M hM1 (s.re))
  have hgN0 : 0 ≤ g N := le_of_lt (by dsimp [g]; exact rpow_neg_pos N hN1 (s.re))
  -- per-k bound summed:
  have hb1 : (∑ k ∈ Finset.Icc N (M - 1), ‖f k - f (k + 1)‖) ≤ C * (g N - g M) := by
    calc
      (∑ k ∈ Finset.Icc N (M - 1), ‖f k - f (k + 1)‖)
          ≤ ∑ k ∈ Finset.Icc N (M - 1), C * (g k - g (k + 1)) := by
              apply Finset.sum_le_sum
              intro k hk
              have hNk : N ≤ k := (Finset.mem_Icc.mp hk).1
              have hk1 : 1 ≤ k := le_trans hN1 hNk
              have hper := norm_cpow_sub_le k hk1 s hs
              dsimp [f, g, C]
              -- norm of f k - f(k+1) vs ‖(k+1)^{-s} - k^{-s}‖:
              rw [norm_sub_rev]  -- hmm orientation
              exact hper
      _ = C * (∑ k ∈ Finset.Icc N (M - 1), (g k - g (k + 1))) := by
              rw [Finset.mul_sum]
      _ = C * (g N - g M) := by
              rw [sum_Icc_sub_down g hN1 hNM]
  -- boundary
  have hbnd1 : ‖A M * f M‖ ≤ B * g M := by
    calc
      ‖A M * f M‖ ≤ ‖A M‖ * ‖f M‖ := norm_mul_le _ _
      _ ≤ B * ‖f M‖ := mul_le_mul_of_nonneg_right (hA M hNM) (norm_nonneg (f M))
      _ = B * g M := by rw [hf M hM1]
  -- the whole correction sum:
  have hbnd2 : ‖∑ k ∈ Finset.Icc N (M - 1), A k * (f k - f (k + 1))‖ ≤ B * C * (g N - g M) := by
    calc
      ‖∑ k ∈ Finset.Icc N (M - 1), A k * (f k - f (k + 1))‖
          ≤ ∑ k ∈ Finset.Icc N (M - 1), ‖A k * (f k - f (k + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Icc N (M - 1), B * ‖f k - f (k + 1)‖ := by
              apply Finset.sum_le_sum
              intro k hk
              have hNk : N ≤ k := (Finset.mem_Icc.mp hk).1
              calc
                ‖A k * (f k - f (k + 1))‖ ≤ ‖A k‖ * ‖f k - f (k + 1)‖ := norm_mul_le _ _
                _ ≤ B * ‖f k - f (k + 1)‖ := mul_le_mul_of_nonneg_right (hA k hNk) (norm_nonneg _)
      _ = B * (∑ k ∈ Finset.Icc N (M - 1), ‖f k - f (k + 1)‖) := by rw [Finset.mul_sum]
      _ ≤ B * (C * (g N - g M)) := mul_le_mul_of_nonneg_left hb1 hB0
      _ = B * C * (g N - g M) := by ring
  -- assemble
  calc
    ‖∑ k ∈ Finset.Icc N M, a k * (k : ℂ) ^ (-s)‖
        = ‖A M * f M + ∑ k ∈ Finset.Icc N (M - 1), A k * (f k - f (k + 1))‖ := by
            rw [sum_Icc_mul_eq a f hN1 hNM]
    _ ≤ ‖A M * f M‖ + ‖∑ k ∈ Finset.Icc N (M - 1), A k * (f k - f (k + 1))‖ := norm_add_le _ _
    _ ≤ B * g M + B * C * (g N - g M) := add_le_add hbnd1 hbnd2
    _ ≤ B * g N + B * C * g N := by
            have h1 : B * g M ≤ B * g N := mul_le_mul_of_nonneg_left hgMN hB0
            have h2 : B * C * (g N - g M) ≤ B * C * g N := by
              apply mul_le_mul_of_nonneg_left _ hBC0
              have hle' : g N - g M ≤ g N := by linarith
              exact hle'
            linarith
    _ = B * (N : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
            dsimp [g, C]
            ring

end Commons.Analysis.Asymptotics
