import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Submission.Commons.Analysis.TensorApprox.sum_univ_pi_prod

namespace Commons.Analysis.Trig

open scoped BigOperators
open Filter

/-! ### Generic finite-sum rewrites -/

private lemma symmetric_sum (F : ℤ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), F k
      = F 0 + ∑ m ∈ Finset.Icc 1 N, (F (m:ℤ) + F (-(m:ℤ))) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show (((n+1:ℕ):ℤ)) = (n:ℤ)+1 from by push_cast; ring]
    rw [Finset.Icc_succ_succ, Finset.sum_union]
    · rw [ih, Finset.sum_pair (by omega), Finset.sum_Icc_succ_top (by omega)]
      push_cast
      ring
    · rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      omega

private lemma triangular_sum (c : ℕ → ℂ) (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, (((K - m : ℕ)) : ℂ) * c m
      = ∑ j ∈ Finset.range K, ∑ m ∈ Finset.Icc 1 j, c m := by
  induction K with
  | zero => simp
  | succ n ih =>
    have h : ∑ m ∈ Finset.Icc 1 n, ((((n+1) - m : ℕ)) : ℂ) * c m
           = ∑ m ∈ Finset.Icc 1 n, (((n - m : ℕ)) : ℂ) * c m
             + ∑ m ∈ Finset.Icc 1 n, c m := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Icc] at hm
      have hcast : ((((n+1) - m : ℕ)) : ℂ) = (((n - m : ℕ)) : ℂ) + 1 := by
        have : ((n+1) - m : ℕ) = ((n - m : ℕ)) + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast]; ring
    rw [Finset.sum_Icc_succ_top (by omega), h, ih, Finset.sum_range_succ]
    rw [show (((n+1) - (n+1) : ℕ) : ℂ) = 0 by simp]
    ring

private lemma cotTerm_reindex (x : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, cotTerm x n
      = ∑ m ∈ Finset.Icc 1 N, (1/(x - (m:ℂ)) + 1/(x + (m:ℂ))) := by
  have hset : (Finset.range N).image (fun n => n+1) = Finset.Icc 1 N := by
    ext m
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨n, hn, rfl⟩; omega
    · intro hm; exact ⟨m-1, by omega, by omega⟩
  rw [← hset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [cotTerm]
    push_cast
    ring
  · intro a ha b hb hab
    exact Nat.succ_inj.mp (by simpa [Nat.succ_eq_add_one] using hab)

private lemma even_reindex (c : ℕ → ℂ) (j : ℕ) :
    ∑ m ∈ (Finset.Icc 1 j).filter (fun m => Even m), c m
      = ∑ m ∈ Finset.Icc 1 (j/2), c (2*m) := by
  have hset : (Finset.Icc 1 j).filter (fun m => Even m)
      = (Finset.Icc 1 (j/2)).image (fun m => 2*m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, r, rfl⟩
      exact ⟨r, ⟨by omega, by (rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)⟩, by omega⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le (by norm_num)] at ht2
      exact ⟨⟨by omega, by omega⟩, t, by omega⟩
  rw [hset, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.mul_left_cancel (n := 2) (by norm_num) (by simpa using hab)

private lemma alt_split (c : ℕ → ℂ) (j : ℕ) :
    ∑ m ∈ Finset.Icc 1 j, (-1:ℂ)^(m:ℤ) * c m
      = 2 * (∑ m ∈ Finset.Icc 1 (j/2), c (2*m)) - ∑ m ∈ Finset.Icc 1 j, c m := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 j) (fun m => Even m)
    (fun m => (-1:ℂ)^(m:ℤ) * c m)
  have hE : ∑ m ∈ Finset.Icc 1 (j/2), c (2*m)
      = ∑ m ∈ (Finset.Icc 1 j).filter (fun m => Even m), c m := (even_reindex c j).symm
  have heven : ∑ m ∈ (Finset.Icc 1 j).filter (fun m => Even m), (-1:ℂ)^(m:ℤ) * c m
      = ∑ m ∈ (Finset.Icc 1 j).filter (fun m => Even m), c m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [zpow_natCast, (Finset.mem_filter.mp hm).2.neg_one_pow, one_mul]
  have hodd : ∑ m ∈ (Finset.Icc 1 j).filter (fun m => ¬ Even m), (-1:ℂ)^(m:ℤ) * c m
      = - ∑ m ∈ (Finset.Icc 1 j).filter (fun m => ¬ Even m), c m := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hodd' : Odd m := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hm).2
    rw [zpow_natCast, hodd'.neg_one_pow]; ring
  have hS : ∑ m ∈ (Finset.Icc 1 j).filter (fun m => ¬ Even m), c m
      = ∑ m ∈ Finset.Icc 1 j, c m - ∑ m ∈ (Finset.Icc 1 j).filter (fun m => Even m), c m := by
    have := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 j) (fun m => Even m) c
    rw [← this]; ring
  rw [← hsplit, heven, hodd, hS, ← hE]
  ring

/-! ### Analytic lemmas -/

private lemma cot_two_identity (z : ℂ) (h : Complex.sin (2*z) ≠ 0) :
    Complex.cot z - Complex.cot (2*z) = 1/Complex.sin (2*z) := by
  have hs : Complex.sin z ≠ 0 := fun hz => h (by rw [Complex.sin_two_mul, hz]; ring)
  have hc : Complex.cos z ≠ 0 := fun hc => h (by rw [Complex.sin_two_mul, hc]; ring)
  have h1 : Complex.cos z / Complex.sin z = (Complex.cos (2*z) + 1)/Complex.sin (2*z) := by
    rw [Complex.sin_two_mul, Complex.cos_two_mul]
    field_simp
    ring
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, h1]
  field_simp
  ring

private lemma Psum_tendsto (x : ℂ) (hx : x ∈ Complex.integerComplement) :
    Tendsto (fun N:ℕ => (1/x : ℂ) + ∑ j ∈ Finset.range N, cotTerm x j) atTop
      (nhds ((Real.pi : ℂ) * Complex.cot ((Real.pi:ℂ) * x))) := by
  have h := tendsto_logDeriv_euler_cot_sub hx
  have h2 : Tendsto (fun N:ℕ => (1/x : ℂ) + ∑ j ∈ Finset.range N, cotTerm x j) atTop
      (nhds ((1/x : ℂ) + ((Real.pi:ℂ) * Complex.cot ((Real.pi:ℂ)*x) - 1/x))) := by
    apply Tendsto.add
    · exact tendsto_const_nhds
    · exact h
  have heq : (1/x : ℂ) + ((Real.pi:ℂ) * Complex.cot ((Real.pi:ℂ)*x) - 1/x)
      = (Real.pi:ℂ) * Complex.cot ((Real.pi:ℂ)*x) := by ring
  rwa [heq] at h2

private lemma tendsto_div_two_atTop : Tendsto (fun j : ℕ => j/2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨2*b, fun a ha => by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega⟩

private lemma trig_value (u : ℝ) (h : Real.sin (Real.pi*u) ≠ 0) :
    (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((u/2 : ℝ) : ℂ))
      - (Real.pi : ℂ) * Complex.cot ((Real.pi:ℂ) * (u:ℂ))
      = (Real.pi : ℂ) / ((Real.sin (Real.pi*u) : ℝ) : ℂ) := by
  set z : ℂ := (Real.pi : ℂ) * ((u/2 : ℝ) : ℂ) with hz
  have h2 : (2:ℂ) * z = (Real.pi : ℂ) * (u:ℂ) := by rw [hz]; push_cast; ring
  have hsin : Complex.sin (2*z) ≠ 0 := by
    rw [h2, ← Complex.ofReal_mul, ← Complex.ofReal_sin]
    exact_mod_cast h
  have hkey := cot_two_identity z hsin
  rw [h2] at hkey
  have hsin2 : Complex.sin ((Real.pi:ℂ)*(u:ℂ)) = ((Real.sin (Real.pi*u) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_sin]
  rw [hsin2] at hkey
  rw [show (Real.pi : ℂ) * Complex.cot z - (Real.pi : ℂ) * Complex.cot ((Real.pi:ℂ)*(u:ℂ))
        = (Real.pi : ℂ) * (Complex.cot z - Complex.cot ((Real.pi:ℂ)*(u:ℂ))) by ring, hkey]
  rw [mul_one_div]

/-! ### Combinatorial/algebraic set-up -/

private noncomputable def aTerm (v : ℂ) (k : ℤ) : ℂ := (-1:ℂ)^k / (v + (k:ℂ))
private noncomputable def Dsum (v : ℂ) (j : ℕ) : ℂ := ∑ k ∈ Finset.Icc (-(j:ℤ)) (j:ℤ), aTerm v k
private noncomputable def Psum (x : ℂ) (N : ℕ) : ℂ := (1/x : ℂ) + ∑ j ∈ Finset.range N, cotTerm x j
private noncomputable def cTerm (v : ℂ) (m : ℕ) : ℂ := 1/(v + (m:ℂ)) + 1/(v - (m:ℂ))
private noncomputable def Tsum (u : ℝ) (K : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), ((1 - (|k| : ℝ) / K : ℝ) : ℂ) * (-1:ℂ)^k / ((u + k : ℝ) : ℂ)

private lemma aTerm_symm (v : ℂ) (m : ℕ) :
    aTerm v (m:ℤ) + aTerm v (-(m:ℤ)) = (-1:ℂ)^(m:ℤ) * cTerm v m := by
  unfold aTerm cTerm
  rw [show (-1:ℂ)^(-(m:ℤ)) = (-1:ℂ)^(m:ℤ) from by rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one]]
  push_cast
  ring

private lemma half_cterm (v : ℂ) (m : ℕ) :
    cTerm (v/2) m = 2 * cTerm v (2*m) := by
  unfold cTerm
  push_cast
  rw [show v/2 + (m:ℂ) = (v + 2*(m:ℂ))/2 by ring,
      show v/2 - (m:ℂ) = (v - 2*(m:ℂ))/2 by ring]
  rw [one_div_div, one_div_div]
  ring

private lemma Dsum_expand (v : ℂ) (j : ℕ) :
    Dsum v j = 1/v + ∑ m ∈ Finset.Icc 1 j, (-1:ℂ)^(m:ℤ) * cTerm v m := by
  rw [Dsum, symmetric_sum]
  congr 1
  · simp [aTerm]
  · apply Finset.sum_congr rfl
    intro m hm
    exact aTerm_symm v m

private lemma Psum_expand (x : ℂ) (N : ℕ) :
    Psum x N = 1/x + ∑ m ∈ Finset.Icc 1 N, cTerm x m := by
  rw [Psum, cotTerm_reindex]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [cTerm]; ring

private lemma Tsum_expand (u : ℝ) (K : ℕ) :
    Tsum u K = 1/(u:ℂ) + ∑ m ∈ Finset.Icc 1 K,
      ((1 - (m:ℝ)/K : ℝ) : ℂ) * ((-1:ℂ)^(m:ℤ) * cTerm (u:ℂ) m) := by
  have h1 : Tsum u K = ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
      ((1 - (|k|:ℝ)/K : ℝ) : ℂ) * aTerm (u:ℂ) k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show ((u + k : ℝ) : ℂ) = (u:ℂ) + (k:ℂ) from by push_cast; ring, aTerm, mul_div_assoc]
  rw [h1, symmetric_sum]
  congr 1
  · simp [aTerm]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [show (|(((m:ℤ)))|:ℝ) = (m:ℝ) from by
          simp only [Int.cast_natCast]; exact abs_of_nonneg (Nat.cast_nonneg m),
        show (|(((-(m:ℤ)) : ℤ))|:ℝ) = (m:ℝ) from by
          simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
          exact abs_of_nonneg (Nat.cast_nonneg m),
        ← mul_add, aTerm_symm]

private lemma Dsum_eq_Psum (v : ℂ) (j : ℕ) :
    Dsum v j = Psum (v/2) (j/2) - Psum v j := by
  rw [Dsum_expand, Psum_expand, Psum_expand]
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.Icc 1 (j/2)) => half_cterm v m)]
  rw [show (∑ m ∈ Finset.Icc 1 (j/2), 2*cTerm v (2*m))
      = 2*(∑ m ∈ Finset.Icc 1 (j/2), cTerm v (2*m)) from by rw [Finset.mul_sum]]
  rw [alt_split (cTerm v) j]
  rw [show (1/(v/2) : ℂ) = 2/v from by rw [one_div_div]]
  ring

private lemma coeff_eq (K m : ℕ) (hK : 0 < K) (hm : m ≤ K) :
    ((1 - (m:ℝ)/K : ℝ) : ℂ) = (K:ℂ)⁻¹ * ((K-m : ℕ) : ℂ) := by
  rw [Nat.cast_sub hm]
  have hK0 : ((K:ℝ)) ≠ 0 := by exact_mod_cast hK.ne'
  have hKc : ((K:ℂ)) ≠ 0 := by exact_mod_cast hK.ne'
  rw [show ((1 - (m:ℝ)/K : ℝ) : ℂ) = 1 - (m:ℂ)/K from by push_cast; ring]
  field_simp

private lemma Fejer_identity (u : ℝ) (K : ℕ) (hK : 0 < K) :
    Tsum u K = (K:ℂ)⁻¹ * ∑ j ∈ Finset.range K, Dsum (u:ℂ) j := by
  rw [Tsum_expand]
  have hsum : ∑ j ∈ Finset.range K, Dsum (u:ℂ) j
      = (K:ℂ) * (1/(u:ℂ))
        + ∑ m ∈ Finset.Icc 1 K, (((K-m:ℕ)):ℂ) * ((-1:ℂ)^(m:ℤ) * cTerm (u:ℂ) m) := by
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range K) => Dsum_expand (u:ℂ) j)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    rw [← triangular_sum (fun m => (-1:ℂ)^(m:ℤ) * cTerm (u:ℂ) m) K]
    simp only [nsmul_eq_mul]
  rw [hsum, mul_add, Finset.mul_sum]
  rw [show (K:ℂ)⁻¹ * ((K:ℂ) * (1/(u:ℂ))) = 1/(u:ℂ) from by
        rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hK.ne'), one_mul]]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Icc] at hm
  rw [coeff_eq K m hK hm.2]
  ring

/-- The Fejér-weighted partial fractions of the cosecant converge. -/
theorem cosec_fejer_limit (u : ℝ) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ k : ℤ, δ ≤ |u - k|) :
    Filter.Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
        ((1 - (|k| : ℝ) / K : ℝ) : ℂ) * (-1 : ℂ) ^ k / ((u + k : ℝ) : ℂ))
      Filter.atTop (nhds ((Real.pi : ℂ) / ((Real.sin (Real.pi * u) : ℝ) : ℂ))) := by
  have hui : (u:ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hn' : (n:ℝ) = u := by
      have : ((n:ℝ):ℂ) = ((u:ℝ):ℂ) := by rw [← hn]; push_cast; ring
      exact Complex.ofReal_inj.mp this
    have h0 : |u - (n:ℝ)| = 0 := by rw [← hn']; simp
    have := hsep n
    rw [h0] at this
    linarith
  have hu2i : ((u/2:ℝ):ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    apply (Complex.mem_integerComplement_iff.mp hui)
    refine ⟨2*n, ?_⟩
    have h2 : (u:ℂ) = ((2*n : ℤ):ℂ) := by
      have h3 : (u:ℂ) = 2*((u/2:ℝ):ℂ) := by push_cast; ring
      rw [h3, ← hn]; push_cast; ring
    exact h2.symm
  have hsin_ne : Real.sin (Real.pi*u) ≠ 0 := by
    intro h0
    rw [Real.sin_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    have hk' : u = (k:ℝ) := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp at hk
      linarith
    exact (Complex.mem_integerComplement_iff.mp hui) ⟨k, by rw [hk']; push_cast; ring⟩
  have hP_u : Tendsto (Psum (u:ℂ)) atTop
      (nhds ((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*(u:ℂ)))) := Psum_tendsto (u:ℂ) hui
  have hP_u2 : Tendsto (Psum ((u/2:ℝ):ℂ)) atTop
      (nhds ((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*((u/2:ℝ):ℂ)))) := Psum_tendsto _ hu2i
  have hDlim : Tendsto (Dsum (u:ℂ)) atTop
      (nhds ((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*((u/2:ℝ):ℂ))
              - (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*(u:ℂ)))) := by
    have h1 := (hP_u2.comp tendsto_div_two_atTop).sub hP_u
    refine h1.congr' ?_
    exact Filter.Eventually.of_forall (fun j => by
      simp only [Function.comp_apply, Complex.ofReal_div]
      exact (Dsum_eq_Psum (u:ℂ) j).symm)
  have hces := hDlim.cesaro_smul
  have hev : (fun K : ℕ => (K:ℝ)⁻¹ • ∑ j ∈ Finset.range K, Dsum (u:ℂ) j)
      =ᶠ[atTop] (fun K => Tsum u K) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
    rw [Fejer_identity u K hK, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hL : (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*((u/2:ℝ):ℂ))
      - (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*(u:ℂ))
      = (Real.pi : ℂ) / ((Real.sin (Real.pi * u) : ℝ) : ℂ) := trig_value u hsin_ne
  change Tendsto (fun K : ℕ => Tsum u K) Filter.atTop
      (nhds ((Real.pi : ℂ) / ((Real.sin (Real.pi * u) : ℝ) : ℂ)))
  rw [← hL]
  exact hces.congr' hev

end Commons.Analysis.Trig