import Mathlib

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Auxiliary real-variable lemmas -/

lemma trsc_min_one_div_sqrt_step (θ : ℝ) (hθ : 0 ≤ θ) (m : ℕ) :
    min 1 (θ / Real.sqrt ((m + 1 : ℕ) : ℝ))
      ≤ 2 * θ * (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt ((m : ℕ) : ℝ)) := by
  set s : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ) with hs
  set t : ℝ := Real.sqrt ((m : ℕ) : ℝ) with ht
  have hs2 : s ^ 2 = (m : ℝ) + 1 := by rw [hs]; rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have ht2 : t ^ 2 = (m : ℝ) := by rw [ht, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hst : t ≤ s := by rw [hs, ht]; exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hpos : 0 < s + t := by linarith
  have hdiff : s - t = 1 / (s + t) := by
    rw [eq_div_iff (ne_of_gt hpos)]
    nlinarith [hs2, ht2]
  rw [hdiff]
  rw [show 2 * θ * (1 / (s + t)) = 2 * θ / (s + t) by ring]
  by_cases h : θ ≤ s
  · have hmin : min 1 (θ / s) = θ / s :=
      min_eq_right (by rw [div_le_one hs0]; exact h)
    rw [hmin]
    rw [div_le_div_iff₀ hs0 hpos]
    nlinarith [hst, hθ]
  · have h' : s < θ := lt_of_not_ge h
    have hmin : min 1 (θ / s) = 1 := min_eq_left (by rw [one_le_div hs0]; linarith)
    rw [hmin]
    rw [le_div_iff₀ hpos]
    nlinarith [hst, h', hθ]

lemma trsc_min_one_div_sqrt_sum_le (θ : ℝ) (hθ : 0 ≤ θ) (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m, min 1 (θ / Real.sqrt (j : ℝ))) ≤ 2 * θ * Real.sqrt (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (by omega : 1 ≤ m + 1)]
    have hstep := trsc_min_one_div_sqrt_step θ hθ m
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hstep ⊢
    have hsq : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hle : Real.sqrt (m:ℝ) ≤ Real.sqrt ((m:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
    nlinarith [ih, hstep, hθ, Real.sqrt_nonneg ((m:ℝ))]

/-- Reflection of an `Icc`-sum in `ℕ`. -/
lemma trsc_sum_Icc_reflect (f : ℕ → ℝ) (n : ℕ) :
    (∑ c ∈ Finset.Icc 1 n, f (n + 1 - c)) = ∑ j ∈ Finset.Icc 1 n, f j := by
  refine Finset.sum_bij' (fun c _ => n + 1 - c) (fun j _ => n + 1 - j)
    (fun c hc => by simp only [Finset.mem_Icc] at hc ⊢; omega)
    (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
    (fun c hc => by simp only [Finset.mem_Icc] at hc; omega)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun _ _ => rfl)


/-- Cast an `Icc`-sum over `ℤ` (with nonnegative lower bound) to one over `ℕ`. -/
lemma trsc_sum_Icc_int_eq_sum_Icc_nat (f : ℤ → ℝ) (n : ℕ) :
    (∑ c ∈ Finset.Icc (1 : ℤ) (n : ℤ), f c) = ∑ d ∈ Finset.Icc 1 n, f (d : ℤ) := by
  refine Finset.sum_bij' (fun (c : ℤ) _ => c.toNat) (fun (d : ℕ) _ => (d : ℤ))
    (fun c hc => by simp only [Finset.mem_Icc] at hc ⊢; omega)
    (fun d hd => by simp only [Finset.mem_Icc] at hd ⊢; constructor <;> omega)
    (fun c hc => by simp only [Finset.mem_Icc] at hc; omega)
    (fun d hd => by simp)
    (fun c hc => by simp only [Finset.mem_Icc] at hc; congr 1; omega)

/-- A symmetric sum over `Icc (-K) K` in `ℤ` is `H 0` plus twice the positive part. -/
lemma trsc_even_Icc_sum (H : ℤ → ℝ) (hH : ∀ c, H (-c) = H c) (K : ℕ) :
    (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), H c) ≤ H 0 + 2 * ∑ d ∈ Finset.Icc 1 K, H (d : ℤ) := by
  have hU : Finset.Icc (-(K : ℤ)) (K : ℤ)
      = (Finset.Icc (-(K : ℤ)) (-1)) ∪ Finset.Icc 0 0 ∪ Finset.Icc (1 : ℤ) (K : ℤ) := by
    ext c
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd1 : Disjoint (Finset.Icc (-(K : ℤ)) (-1)) (Finset.Icc 0 0) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_Icc] at hc hc'
    omega
  have hd2 : Disjoint ((Finset.Icc (-(K : ℤ)) (-1)) ∪ Finset.Icc 0 0)
      (Finset.Icc (1 : ℤ) (K : ℤ)) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_union, Finset.mem_Icc] at hc hc'
    omega
  have hneg : (∑ c ∈ Finset.Icc (-(K : ℤ)) (-1), H c)
      = ∑ d ∈ Finset.Icc (1 : ℤ) (K : ℤ), H d := by
    refine Finset.sum_bij' (fun c _ => -c) (fun d _ => -d)
      (fun c hc => by simp only [Finset.mem_Icc] at hc ⊢; omega)
      (fun d hd => by simp only [Finset.mem_Icc] at hd ⊢; omega)
      (fun c hc => by simp only [Finset.mem_Icc] at hc; omega)
      (fun d hd => by simp only [Finset.mem_Icc] at hd; omega)
      (fun c hc => by simp only [Finset.mem_Icc] at hc; rw [hH c])
  have hzero : (∑ c ∈ Finset.Icc (0 : ℤ) 0, H c) = H 0 := by simp
  rw [hU, Finset.sum_union hd2, Finset.sum_union hd1, hzero, hneg,
    trsc_sum_Icc_int_eq_sum_Icc_nat H K]
  linarith


/-- `√(u+d) - √u ≤ √d`. -/
lemma trsc_sqrt_add_sub_sqrt_le (u d : ℝ) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    Real.sqrt (u + d) - Real.sqrt u ≤ Real.sqrt d := by
  have h : Real.sqrt (u + d) ≤ Real.sqrt u + Real.sqrt d := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt (by linarith), Real.sq_sqrt hd]
    nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg d]
  linarith

/-- `√(max y 0) = √y`. -/
lemma trsc_sqrt_max_zero (y : ℝ) : Real.sqrt (max y 0) = Real.sqrt y := by
  rcases le_total 0 y with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, Real.sqrt_eq_zero_of_nonpos h, Real.sqrt_zero]

/-- **The real-variable core.**  For `1 ≤ X₁ ≤ X₂ ≤ 2X₁`, `1 ≤ N` and `(X₂N)^{1/4} ≤ K`,

`Σ_{|c| ≤ K} (√((X₂N - c⁴)₊) - √((X₁N - c⁴)₊)) ≤ C ((X₂ - X₁)N (X₁N)^{-1/4} + √((X₂ - X₁)N))`.

The target `thin_real_sum_core` is the case `X₁ = A`, `X₂ = B`, `N = 1`. -/
theorem trsc_real_sum_general :
    ∃ C : ℝ, 0 < C ∧ ∀ (X₁ X₂ N : ℝ) (K : ℕ),
      1 ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 2 * X₁ → 1 ≤ N →
      (X₂ * N) ^ ((1 : ℝ) / 4) ≤ (K : ℝ) →
      (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (Real.sqrt (max (X₂ * N - (c : ℝ) ^ 4) 0)
          - Real.sqrt (max (X₁ * N - (c : ℝ) ^ 4) 0)))
        ≤ C * ((X₂ - X₁) * N * ((X₁ * N) ^ ((1 : ℝ) / 4))⁻¹
            + Real.sqrt ((X₂ - X₁) * N)) := by
  refine ⟨20, by norm_num, ?_⟩
  intro X₁ X₂ N K hX1 hX12 hX2 hN hK1

  have hX10 : 0 < X₁ := by linarith
  have hN0 : 0 < N := by linarith
  have hA0 : 0 < X₁ * N := mul_pos hX10 hN0
  have hB0 : 0 ≤ X₂ * N := by nlinarith
  have hA1 : 1 ≤ X₁ * N := by nlinarith
  have hB1 : 1 ≤ X₂ * N := by nlinarith
  have hN12 : X₁ * N ≤ X₂ * N := mul_le_mul_of_nonneg_right hX12 hN0.le
  set D : ℝ := X₂ - X₁ with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; linarith
  have hDle : D ≤ X₁ := by rw [hDdef]; linarith
  set α : ℝ := (X₁ * N) ^ ((1:ℝ)/4) with hαdef
  set β : ℝ := (X₂ * N) ^ ((1:ℝ)/4) with hβdef
  have hα0 : 0 < α := by rw [hαdef]; exact Real.rpow_pos_of_pos hA0 _
  have hβ0 : 0 < β := by rw [hβdef]; exact Real.rpow_pos_of_pos (by linarith : 0 < X₂*N) _
  have hβge : 0 ≤ β := hβ0.le
  have hα1 : 1 ≤ α := by rw [hαdef]; exact Real.one_le_rpow hA1 (by norm_num)
  have hβ1 : 1 ≤ β := by rw [hβdef]; exact Real.one_le_rpow hB1 (by norm_num)
  have hα4 : α^4 = X₁*N := by rw [hαdef, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hβ4 : β^4 = X₂*N := by rw [hβdef, ← Real.rpow_natCast, ← Real.rpow_mul hB0]; norm_num
  have hαβ : α ≤ β := by
    rw [hαdef, hβdef]; exact Real.rpow_le_rpow hA0.le (by nlinarith) (by norm_num)
  have hβ2α : β ≤ 2*α := by
    have hle : β^4 ≤ (2*α)^4 := by rw [hβ4]; nlinarith [hα4, hα0.le]
    exact le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity) hle
  have hDN' : X₂*N - X₁*N = D*N := by rw [hDdef]; ring
  have hDN0 : 0 ≤ D*N := mul_nonneg hDnn hN0.le
  have hβα : β - α ≤ D*N/(4*α^3) := by
    rw [← hDN', ← hβ4, ← hα4, le_div_iff₀ (by positivity : (0:ℝ) < 4*α^3)]
    rcases le_total α β with h | h
    · have h1 : 0 ≤ β - α := sub_nonneg.mpr h
      have h2 : 0 ≤ β^3 + β^2*α + β*α^2 - 3*α^3 := by
        rw [show β^3 + β^2*α + β*α^2 - 3*α^3
              = (β-α)*(β^2 + β*α + α^2 + α*(β+α) + α^2) by ring]
        exact mul_nonneg h1 (by nlinarith [h, hα0, sq_nonneg α])
      nlinarith [h1, h2]
    · have h1 : β - α ≤ 0 := sub_nonpos.mpr h
      have h2 : β^3 + β^2*α + β*α^2 - 3*α^3 ≤ 0 := by
        rw [show β^3 + β^2*α + β*α^2 - 3*α^3
              = (β-α)*(β^2 + β*α + α^2 + α*(β+α) + α^2) by ring]
        exact mul_nonpos_of_nonpos_of_nonneg h1 (by nlinarith [h, hα0, sq_nonneg α])
      nlinarith [h1, h2]
  have hK1' : β ≤ (K:ℝ) := by rw [hβdef]; exact hK1
  set H : ℤ → ℝ := fun c => Real.sqrt (max (X₂ * N - (c : ℝ) ^ 4) 0)
      - Real.sqrt (max (X₁ * N - (c : ℝ) ^ 4) 0) with hHdef
  have hHeven : ∀ c : ℤ, H (-c) = H c := by
    intro c
    have h1 : ((-c : ℤ) : ℝ) ^ 4 = ((c:ℤ):ℝ)^4 := by push_cast; ring
    show Real.sqrt (max (X₂ * N - ((-c : ℤ) : ℝ) ^ 4) 0)
        - Real.sqrt (max (X₁ * N - ((-c : ℤ) : ℝ) ^ 4) 0)
      = Real.sqrt (max (X₂ * N - ((c : ℤ) : ℝ) ^ 4) 0)
        - Real.sqrt (max (X₁ * N - ((c : ℤ) : ℝ) ^ 4) 0)
    rw [h1]
  set n : ℕ := ⌊α⌋₊ with hndef
  have hnα : (n:ℝ) ≤ α := by rw [hndef]; exact Nat.floor_le hα0.le
  have hαn : α < (n:ℝ) + 1 := by rw [hndef]; exact Nat.lt_floor_add_one α
  have hnK : n ≤ K := by
    have h1 : (n:ℝ) ≤ (K:ℝ) := le_trans hnα (le_trans hαβ hK1')
    exact_mod_cast h1
  -- ## Region I
  have hRI : (∑ c ∈ Finset.Icc 1 n, H (c:ℤ)) ≤ Real.sqrt (D*N) + D*N/α := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · rw [hn0]
      have hz : (Finset.Icc 1 0 : Finset ℕ) = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [hz, Finset.sum_empty]
      positivity
    · have hsplit_top : (∑ c ∈ Finset.Icc 1 n, H (c:ℤ))
          = (∑ c ∈ Finset.Icc 1 (n-1), H (c:ℤ)) + H (n:ℤ) := by
        have h2 : ((n - 1 + 1 : ℕ) : ℤ) = ((n : ℕ) : ℤ) := by
          have : n - 1 + 1 = n := by omega
          rw [this]
        conv_lhs => rw [show n = n - 1 + 1 from by omega]
        rw [Finset.sum_Icc_succ_top (a := 1) (b := n - 1) (by omega : 1 ≤ n - 1 + 1), h2]
      rw [hsplit_top]
      have hHn : H (n:ℤ) ≤ Real.sqrt (D*N) := by
        have hnα'' : ((n:ℤ):ℝ) ≤ α := by push_cast; exact hnα
        have hx4 : ((n:ℤ):ℝ)^4 ≤ α^4 := pow_le_pow_left₀ (by positivity) hnα'' 4
        have hX1 : ((n:ℤ):ℝ)^4 ≤ X₁*N := by rw [← hα4]; exact hx4
        have hHc : H (n:ℤ) = Real.sqrt (X₂*N - ((n:ℤ):ℝ)^4) - Real.sqrt (X₁*N - ((n:ℤ):ℝ)^4) := by
          show Real.sqrt (max (X₂*N - ((n:ℤ):ℝ)^4) 0) - Real.sqrt (max (X₁*N - ((n:ℤ):ℝ)^4) 0)
              = Real.sqrt (X₂*N - ((n:ℤ):ℝ)^4) - Real.sqrt (X₁*N - ((n:ℤ):ℝ)^4)
          rw [max_eq_left (by linarith : (0:ℝ) ≤ X₂*N - ((n:ℤ):ℝ)^4),
            max_eq_left (by linarith : (0:ℝ) ≤ X₁*N - ((n:ℤ):ℝ)^4)]
        rw [hHc]
        have h2 : X₂*N - ((n:ℤ):ℝ)^4 = (X₁*N - ((n:ℤ):ℝ)^4) + D*N := by rw [hDdef]; ring
        rw [h2]
        exact trsc_sqrt_add_sub_sqrt_le _ _ (by linarith) hDN0
      set θ : ℝ := Real.sqrt (D*N)/(2*α*Real.sqrt α) with hθdef
      have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
      have hstep : ∀ c ∈ Finset.Icc 1 (n-1),
          H (c:ℤ) ≤ Real.sqrt (D*N) * min 1 (θ / Real.sqrt ((n - c : ℕ):ℝ)) := by
        intro c hc
        rw [Finset.mem_Icc] at hc
        obtain ⟨hc1, hc2⟩ := hc
        have hcn : c ≤ n := by omega
        have hxc : ((c:ℤ):ℝ) = (c:ℝ) := by push_cast; ring
        have hxα : ((c:ℤ):ℝ) ≤ α := by rw [hxc]; exact le_trans (by exact_mod_cast hcn) hnα
        have hx4 : ((c:ℤ):ℝ)^4 ≤ α^4 := pow_le_pow_left₀ (by positivity) hxα 4
        have hX1 : ((c:ℤ):ℝ)^4 ≤ X₁*N := by rw [← hα4]; exact hx4
        have hX2 : ((c:ℤ):ℝ)^4 ≤ X₂*N := le_trans hX1 hN12
        have hHc : H (c:ℤ) = Real.sqrt (X₂*N - ((c:ℤ):ℝ)^4) - Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4) := by
          show Real.sqrt (max (X₂*N - ((c:ℤ):ℝ)^4) 0) - Real.sqrt (max (X₁*N - ((c:ℤ):ℝ)^4) 0)
              = Real.sqrt (X₂*N - ((c:ℤ):ℝ)^4) - Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4)
          rw [max_eq_left (by linarith : (0:ℝ) ≤ X₂*N - ((c:ℤ):ℝ)^4),
            max_eq_left (by linarith : (0:ℝ) ≤ X₁*N - ((c:ℤ):ℝ)^4)]
        rw [hHc]
        have hu : 0 ≤ X₁*N - ((c:ℤ):ℝ)^4 := by linarith
        have hDNu : Real.sqrt (X₂*N - ((c:ℤ):ℝ)^4) - Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4) ≤ Real.sqrt (D*N) := by
          have h2 : X₂*N - ((c:ℤ):ℝ)^4 = (X₁*N - ((c:ℤ):ℝ)^4) + D*N := by rw [hDdef]; ring
          rw [h2]; exact trsc_sqrt_add_sub_sqrt_le _ _ hu hDN0
        have hj : 0 < n - c := by omega
        have hjR : 0 < ((n - c : ℕ):ℝ) := by exact_mod_cast hj
        have hiden : Real.sqrt (D*N) * (θ / Real.sqrt ((n - c : ℕ):ℝ))
            = D*N/(2*α*Real.sqrt α*Real.sqrt ((n - c : ℕ):ℝ)) := by
          have hJ : Real.sqrt ((n - c : ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr hjR).ne'
          have hA : (2*α*Real.sqrt α) ≠ 0 := by positivity
          rw [hθdef]
          field_simp
          ring_nf
          try rw [Real.sq_sqrt hDN0]
        by_cases hsmall : θ / Real.sqrt ((n - c : ℕ):ℝ) ≤ 1
        · rw [min_eq_right hsmall, hiden]
          have hx0 : 0 ≤ ((c:ℤ):ℝ) := by rw [hxc]; positivity
          have hna : ((n - c : ℕ):ℝ) ≤ α - ((c:ℤ):ℝ) := by
            rw [hxc, Nat.cast_sub hcn]; linarith [hnα]
          have h3 : 0 ≤ α - ((c:ℤ):ℝ) := by linarith [hna, hjR]
          have hlow : α^3 * ((n - c : ℕ):ℝ) ≤ X₁*N - ((c:ℤ):ℝ)^4 := by
            have e1 : X₁*N - ((c:ℤ):ℝ)^4 = α^4 - ((c:ℤ):ℝ)^4 := by rw [hα4]
            rw [e1]
            rw [show α^4 - ((c:ℤ):ℝ)^4
                = (α - ((c:ℤ):ℝ))*(α^3 + α^2*((c:ℤ):ℝ) + α*((c:ℤ):ℝ)^2 + ((c:ℤ):ℝ)^3) by ring]
            have h4 : α^3 ≤ α^3 + α^2*((c:ℤ):ℝ) + α*((c:ℤ):ℝ)^2 + ((c:ℤ):ℝ)^3 :=
              by nlinarith [hα0.le, hx0, sq_nonneg ((c:ℤ):ℝ)]
            calc α^3 * ((n - c : ℕ):ℝ) ≤ α^3 * (α - ((c:ℤ):ℝ)) :=
                  mul_le_mul_of_nonneg_left hna (by positivity)
              _ = (α - ((c:ℤ):ℝ)) * α^3 := by ring
              _ ≤ (α - ((c:ℤ):ℝ))*(α^3 + α^2*((c:ℤ):ℝ) + α*((c:ℤ):ℝ)^2 + ((c:ℤ):ℝ)^3) :=
                  mul_le_mul_of_nonneg_left h4 h3
          have hsden : α*Real.sqrt α*Real.sqrt ((n - c : ℕ):ℝ)
              = Real.sqrt (α^3 * ((n - c : ℕ):ℝ)) := by
            rw [show α^3 * ((n-c:ℕ):ℝ) = (α*Real.sqrt α)^2 * ((n-c:ℕ):ℝ) by
              rw [mul_pow, Real.sq_sqrt hα0.le]; ring]
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
          have hxlt : ((c:ℤ):ℝ) < α := by
            rw [hxc]
            have h1 : (c:ℝ) ≤ ((n-1:ℕ):ℝ) := by exact_mod_cast hc2
            have h2 : ((n-1:ℕ):ℝ) < α := by
              have h3' : ((n-1:ℕ):ℝ) < (n:ℝ) := by
                have : n - 1 < n := by omega
                exact_mod_cast this
              linarith [h3', hnα]
            linarith
          have hX1pos : 0 < X₁*N - ((c:ℤ):ℝ)^4 := by
            rw [← hα4]
            exact sub_pos.mpr (pow_lt_pow_left₀ hxlt (by positivity) (by norm_num : (4:ℕ) ≠ 0))
          have h1le : α*Real.sqrt α*Real.sqrt ((n - c : ℕ):ℝ) ≤ Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4) := by
            rw [hsden]; exact Real.sqrt_le_sqrt hlow
          have hsp : 0 < Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4) := Real.sqrt_pos.mpr hX1pos
          have step1 : Real.sqrt (X₂*N - ((c:ℤ):ℝ)^4) - Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4)
              ≤ D*N/(2*Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4)) := by
            have h2 : X₂*N - ((c:ℤ):ℝ)^4 = (X₁*N - ((c:ℤ):ℝ)^4) + D*N := by rw [hDdef]; ring
            rw [h2, le_div_iff₀ (by linarith : (0:ℝ) < 2*Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4))]
            have hprod : (Real.sqrt ((X₁*N - ((c:ℤ):ℝ)^4)+D*N) - Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4))
                * (Real.sqrt ((X₁*N - ((c:ℤ):ℝ)^4)+D*N) + Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4)) = D*N := by
              nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ X₁*N - ((c:ℤ):ℝ)^4),
                Real.sq_sqrt (by linarith : (0:ℝ) ≤ X₁*N - ((c:ℤ):ℝ)^4 + D*N)]
            have hnn : 0 ≤ Real.sqrt ((X₁*N - ((c:ℤ):ℝ)^4)+D*N) - Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4) := by
              apply sub_nonneg.mpr; exact Real.sqrt_le_sqrt (by linarith)
            nlinarith [hprod, hnn, Real.sqrt_nonneg ((X₁*N - ((c:ℤ):ℝ)^4)+D*N),
              Real.sqrt_nonneg (X₁*N - ((c:ℤ):ℝ)^4)]
          have step2 : D*N/(2*Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4))
              ≤ D*N/(2*α*Real.sqrt α*Real.sqrt ((n - c : ℕ):ℝ)) := by
            have hsp2 : 0 < 2*α*Real.sqrt α*Real.sqrt ((n - c : ℕ):ℝ) := by positivity
            rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2*Real.sqrt (X₁*N - ((c:ℤ):ℝ)^4)) hsp2]
            nlinarith [h1le, hDN0]
          linarith [step1, step2]
        · rw [min_eq_left (le_of_not_ge hsmall), mul_one]
          exact hDNu
      have hreidx : (∑ c ∈ Finset.Icc 1 (n-1), min 1 (θ / Real.sqrt ((n - c : ℕ):ℝ)))
          = ∑ j ∈ Finset.Icc 1 (n-1), min 1 (θ / Real.sqrt (j:ℝ)) := by
        refine Finset.sum_bij' (fun c _ => n - c) (fun j _ => n - j)
          (fun c hc => by simp only [Finset.mem_Icc] at hc ⊢; omega)
          (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
          (fun c hc => by simp only [Finset.mem_Icc] at hc; omega)
          (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
          (fun c hc => by simp only [Finset.mem_Icc] at hc; rfl)
      have hrest : (∑ c ∈ Finset.Icc 1 (n-1), H (c:ℤ))
          ≤ Real.sqrt (D*N) * (2*θ*Real.sqrt ((n-1:ℕ):ℝ)) := by
        have h1 : (∑ c ∈ Finset.Icc 1 (n-1), H (c:ℤ))
            ≤ ∑ c ∈ Finset.Icc 1 (n-1), Real.sqrt (D*N) * min 1 (θ / Real.sqrt ((n - c : ℕ):ℝ)) :=
          Finset.sum_le_sum hstep
        rw [← Finset.mul_sum, hreidx] at h1
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left (trsc_min_one_div_sqrt_sum_le θ hθ0 (n-1)) (Real.sqrt_nonneg _)
      have hsqrtα : Real.sqrt ((n-1:ℕ):ℝ) ≤ Real.sqrt α := by
        apply Real.sqrt_le_sqrt
        have h1 : ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by
          have : n - 1 ≤ n := Nat.sub_le n 1
          exact_mod_cast this
        linarith [h1, hnα]
      have hfin : Real.sqrt (D*N) * (2*θ*Real.sqrt ((n-1:ℕ):ℝ)) ≤ D*N/α := by
        have hmono : Real.sqrt (D*N) * (2*θ*Real.sqrt ((n-1:ℕ):ℝ))
            ≤ Real.sqrt (D*N) * (2*θ*Real.sqrt α) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hsqrtα (by positivity)
        have heq : Real.sqrt (D*N) * (2*θ*Real.sqrt α) = D*N/α := by
          have hA : (2*α*Real.sqrt α) ≠ 0 := by positivity
          rw [hθdef]
          field_simp
          ring_nf
          try rw [Real.sq_sqrt hDN0]
        linarith [hmono, heq]
      linarith [hHn, hrest, hfin]
  -- ## Region II: the summands vanish once `c > β`, so no upper bound on `K` is needed
  have hRII : (∑ c ∈ Finset.Icc (n+1) K, H (c:ℤ))
      ≤ 2*β*Real.sqrt β*((β-α)*Real.sqrt (β-α) + 2*Real.sqrt (β-α)) := by
    have hstep : ∀ c ∈ Finset.Icc (n+1) K,
        H (c:ℤ) ≤ 2*β*Real.sqrt β*Real.sqrt (max (β - (c:ℝ)) 0) := by
      intro c hc
      rw [Finset.mem_Icc] at hc
      have hcR : ((n+1:ℕ):ℝ) ≤ (c:ℝ) := by exact_mod_cast hc.1
      push_cast at hcR
      have hcn : α < (c:ℝ) := by linarith [hαn]
      have hx0 : 0 ≤ (c:ℝ) := by linarith
      have hxc : ((c:ℤ):ℝ) = (c:ℝ) := by push_cast; ring
      have hlt4 : X₁*N < (c:ℝ)^4 := by
        have hpow : α^4 < (c:ℝ)^4 := pow_lt_pow_left₀ hcn hα0.le (by norm_num : (4:ℕ) ≠ 0)
        rwa [hα4] at hpow
      have hHc : H (c:ℤ) = Real.sqrt (max (X₂*N - (c:ℝ)^4) 0) := by
        show Real.sqrt (max (X₂*N - ((c:ℤ):ℝ)^4) 0)
              - Real.sqrt (max (X₁*N - ((c:ℤ):ℝ)^4) 0)
            = Real.sqrt (max (X₂*N - (c:ℝ)^4) 0)
        rw [hxc, max_eq_right (by linarith : X₁*N - (c:ℝ)^4 ≤ 0), Real.sqrt_zero, sub_zero]
      rw [hHc, ← hβ4]
      rcases lt_or_ge (c:ℝ) β with hlt | hle
      · have hle' : (c:ℝ) ≤ β := le_of_lt hlt
        have h3 : 0 ≤ β - (c:ℝ) := by linarith
        have hnon : (0:ℝ) ≤ β^4 - (c:ℝ)^4 := by
          have hp := pow_le_pow_left₀ hx0 hle' 4
          linarith
        have h1 : β^4 - (c:ℝ)^4 ≤ 4*β^3*(β - (c:ℝ)) := by
          have hb1 : β^3 + β^2*(c:ℝ) ≤ 2*β^3 := by
            have hm := mul_le_mul_of_nonneg_left hle' (show (0:ℝ) ≤ β^2 by positivity)
            nlinarith [hm]
          have hb2 : β*(c:ℝ)^2 + (c:ℝ)^3 ≤ 2*β^3 := by
            have h2 : (c:ℝ)^2 ≤ β^2 := by nlinarith [hx0, hle', hβ0]
            have h4 : β + (c:ℝ) ≤ 2*β := by linarith
            have h5 := mul_le_mul h2 h4 (by linarith : (0:ℝ) ≤ β + (c:ℝ))
              (by positivity : (0:ℝ) ≤ β^2)
            nlinarith [h5]
          have hfac : β^4 - (c:ℝ)^4
              = (β - (c:ℝ))*(β^3 + β^2*(c:ℝ) + β*(c:ℝ)^2 + (c:ℝ)^3) := by ring
          rw [hfac]
          nlinarith [hb1, hb2, h3]
        rw [max_eq_left hnon, max_eq_left h3]
        calc Real.sqrt (β^4 - (c:ℝ)^4) ≤ Real.sqrt (4*β^3*(β - (c:ℝ))) := Real.sqrt_le_sqrt h1
          _ = 2*β*Real.sqrt β*Real.sqrt (β - (c:ℝ)) := by
              rw [show 4*β^3*(β - (c:ℝ)) = (2*β*Real.sqrt β)^2*(β - (c:ℝ)) by
                    rw [mul_pow, Real.sq_sqrt hβge]; ring]
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      · have h1 : β^4 - (c:ℝ)^4 ≤ 0 := by
          have hp := pow_le_pow_left₀ hβ0.le hle 4
          linarith
        have h2 : β - (c:ℝ) ≤ 0 := by linarith
        rw [max_eq_right h1, max_eq_right h2, Real.sqrt_zero, mul_zero]
    -- the `√(max (β - c) 0)`-sum has at most `⌈m⌉+1` nonvanishing terms, `m = β - n - 1`
    have hsum : (∑ c ∈ Finset.Icc (n+1) K, Real.sqrt (max (β - (c:ℝ)) 0))
        ≤ (β-α)*Real.sqrt (β-α) + 2*Real.sqrt (β-α) := by
      set m : ℝ := β - (n:ℝ) - 1 with hmdef
      have hnm : β - ((n:ℝ)+1) = m := by rw [hmdef]; ring
      have hmle : m ≤ β - α := by rw [hmdef]; linarith [hnα]
      have hαβ' : 0 ≤ β - α := by linarith [hαβ]
      rcases lt_or_ge m 0 with hm | hm
      · have hzero : ∀ c ∈ Finset.Icc (n+1) K, Real.sqrt (max (β - (c:ℝ)) 0) = 0 := by
          intro c hc
          rw [Finset.mem_Icc] at hc
          have hcR : ((n+1:ℕ):ℝ) ≤ (c:ℝ) := by exact_mod_cast hc.1
          push_cast at hcR
          have hneg : β - (c:ℝ) ≤ 0 := by linarith
          rw [max_eq_right hneg, Real.sqrt_zero]
        rw [Finset.sum_eq_zero hzero]
        have h1 : 0 ≤ (β-α)*Real.sqrt (β-α) := mul_nonneg hαβ' (Real.sqrt_nonneg _)
        have h2 : 0 ≤ Real.sqrt (β-α) := Real.sqrt_nonneg _
        linarith
      · have hkey : ∀ c : ℕ, n + 2 + Nat.ceil m ≤ c →
            Real.sqrt (max (β - (c:ℝ)) 0) = 0 := by
          intro c hc
          have hcR : ((n + 2 + Nat.ceil m : ℕ) : ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
          push_cast at hcR
          have hceil : m ≤ ((Nat.ceil m : ℕ) : ℝ) := Nat.le_ceil m
          have hneg : β - (c:ℝ) ≤ 0 := by linarith
          rw [max_eq_right hneg, Real.sqrt_zero]
        have hfilter : (∑ c ∈ Finset.Icc (n+1) K, Real.sqrt (max (β - (c:ℝ)) 0))
            = ∑ c ∈ (Finset.Icc (n+1) K).filter (fun c => c ≤ n+1+Nat.ceil m),
                Real.sqrt (max (β - (c:ℝ)) 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun c hc => ?_
          by_cases hp : c ≤ n+1+Nat.ceil m
          · rw [if_pos hp]
          · rw [if_neg hp]
            rw [Finset.mem_Icc] at hc
            exact hkey c (by omega)
        rw [hfilter]
        have hsub : (Finset.Icc (n+1) K).filter (fun c => c ≤ n+1+Nat.ceil m)
            ⊆ Finset.Icc (n+1) (n+1+Nat.ceil m) := by
          intro c hc
          rw [Finset.mem_filter, Finset.mem_Icc] at hc
          exact Finset.mem_Icc.mpr ⟨hc.1.1, hc.2⟩
        have hstep2 : (∑ c ∈ (Finset.Icc (n+1) K).filter (fun c => c ≤ n+1+Nat.ceil m),
              Real.sqrt (max (β - (c:ℝ)) 0))
            ≤ ∑ c ∈ Finset.Icc (n+1) (n+1+Nat.ceil m),
                Real.sqrt (max (β - (c:ℝ)) 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Real.sqrt_nonneg _)
        have hcard : (Finset.Icc (n+1) (n+1+Nat.ceil m)).card = Nat.ceil m + 1 := by
          rw [Nat.card_Icc]; omega
        have hbd : (∑ c ∈ Finset.Icc (n+1) (n+1+Nat.ceil m),
              Real.sqrt (max (β - (c:ℝ)) 0))
            ≤ (((Nat.ceil m : ℕ) : ℝ) + 1) * Real.sqrt (max m 0) := by
          have hb1 : (∑ c ∈ Finset.Icc (n+1) (n+1+Nat.ceil m),
                Real.sqrt (max (β - (c:ℝ)) 0))
              ≤ ∑ _c ∈ Finset.Icc (n+1) (n+1+Nat.ceil m), Real.sqrt (max m 0) := by
            refine Finset.sum_le_sum fun c hc => ?_
            rw [Finset.mem_Icc] at hc
            have hcR : ((n+1:ℕ):ℝ) ≤ (c:ℝ) := by exact_mod_cast hc.1
            push_cast at hcR
            have h2 : β - (c:ℝ) ≤ m := by linarith
            exact Real.sqrt_le_sqrt (max_le_max h2 le_rfl)
          rw [Finset.sum_const, hcard, nsmul_eq_mul] at hb1
          push_cast at hb1
          linarith [hb1]
        have hceil2 : ((Nat.ceil m : ℕ) : ℝ) < m + 1 := Nat.ceil_lt_add_one hm
        have hmm : ((Nat.ceil m : ℕ) : ℝ) + 1 ≤ (β - α) + 2 := by linarith [hceil2, hmle]
        have hsq : Real.sqrt (max m 0) ≤ Real.sqrt (β - α) := by
          rw [max_eq_left hm]
          exact Real.sqrt_le_sqrt hmle
        have hbd2 : (((Nat.ceil m : ℕ) : ℝ) + 1) * Real.sqrt (max m 0)
            ≤ (β-α)*Real.sqrt (β-α) + 2*Real.sqrt (β-α) := by
          have h5 := mul_le_mul hmm hsq (Real.sqrt_nonneg _)
            (by linarith [hαβ] : (0:ℝ) ≤ (β-α)+2)
          have he : ((β-α)+2)*Real.sqrt (β-α)
              = (β-α)*Real.sqrt (β-α) + 2*Real.sqrt (β-α) := by ring
          linarith [h5, he]
        linarith [hstep2, hbd, hbd2]
    calc (∑ c ∈ Finset.Icc (n+1) K, H (c:ℤ))
        ≤ ∑ c ∈ Finset.Icc (n+1) K, 2*β*Real.sqrt β*Real.sqrt (max (β - (c:ℝ)) 0) :=
          Finset.sum_le_sum hstep
      _ = 2*β*Real.sqrt β * (∑ c ∈ Finset.Icc (n+1) K,
            Real.sqrt (max (β - (c:ℝ)) 0)) := by rw [Finset.mul_sum]
      _ ≤ 2*β*Real.sqrt β * ((β-α)*Real.sqrt (β-α) + 2*Real.sqrt (β-α)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  -- ## The c-sum
  have hS : (∑ c ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), H c)
      ≤ H 0 + 2 * ((∑ c ∈ Finset.Icc 1 n, H (c:ℤ)) + (∑ c ∈ Finset.Icc (n+1) K, H (c:ℤ))) := by
    have h1 := trsc_even_Icc_sum H hHeven K
    have hU : Finset.Icc 1 K = Finset.Icc 1 n ∪ Finset.Icc (n+1) K := by
      ext c; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd : Disjoint (Finset.Icc 1 n) (Finset.Icc (n+1) K) := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      simp only [Finset.mem_Icc] at hc hc'
      omega
    have h2 : (∑ d ∈ Finset.Icc 1 K, H (d:ℤ))
        = (∑ c ∈ Finset.Icc 1 n, H (c:ℤ)) + (∑ c ∈ Finset.Icc (n+1) K, H (c:ℤ)) := by
      rw [hU, Finset.sum_union hd]
    linarith [h1, h2]
  have hH0 : H 0 ≤ D*N/(2*α^2) := by
    have h1 : H 0 = Real.sqrt (X₂*N) - Real.sqrt (X₁*N) := by
      show Real.sqrt (max (X₂*N - ((0:ℤ):ℝ)^4) 0) - Real.sqrt (max (X₁*N - ((0:ℤ):ℝ)^4) 0)
          = Real.sqrt (X₂*N) - Real.sqrt (X₁*N)
      simp only [Int.cast_zero, zero_pow (by norm_num : (4:ℕ) ≠ 0), sub_zero]
      rw [max_eq_left (by positivity), max_eq_left (by positivity)]
    rw [h1]
    have hβ2 : Real.sqrt (X₂*N) = β^2 := by
      rw [hβdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hB0]
      norm_num
    have hα2 : Real.sqrt (X₁*N) = α^2 := by
      rw [hαdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]
      norm_num
    rw [hβ2, hα2, le_div_iff₀ (by positivity : (0:ℝ) < 2*α^2)]
    nlinarith [hαβ, hα0, hβ0, hDN', hβ4, hα4, sq_nonneg α, sq_nonneg β]
  -- ## Assembly
  have hDNN : D*N ≤ α^4 := by
    rw [hα4]
    exact mul_le_mul_of_nonneg_right hDle hN0.le
  have hsDN : Real.sqrt (D*N) ≤ α^2 := by
    have hsq : (α^2)^2 = α^4 := by ring
    calc Real.sqrt (D*N) ≤ Real.sqrt ((α^2)^2) := Real.sqrt_le_sqrt (by rw [hsq]; exact hDNN)
      _ = α^2 := Real.sqrt_sq (sq_nonneg α)
  have hH0' : H 0 ≤ D*N/α := by
    have h5 : α ≤ 2*α^2 := by
      have h6 : 1 ≤ 2*α := by linarith [hα1]
      have h7 := mul_le_mul_of_nonneg_left h6 hα0.le
      nlinarith [h7]
    have h1 : D*N/(2*α^2) ≤ D*N/α := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*α^2) hα0]
      exact mul_le_mul_of_nonneg_left h5 hDN0
    linarith [hH0, h1]
  have hS1 : 2*(∑ c ∈ Finset.Icc 1 n, H (c:ℤ))
      ≤ 2*Real.sqrt (D*N) + 2*(D*N/α) := by linarith [hRI]
  set p : ℝ := Real.sqrt (β*(β-α)) with hpdef
  have hp2 : p^2 = β*(β-α) := by rw [hpdef]; exact Real.sq_sqrt (mul_nonneg hβ0.le (by linarith [hαβ]))
  have hp0 : 0 ≤ p := by rw [hpdef]; exact Real.sqrt_nonneg _
  have hsqrtmul : Real.sqrt β * Real.sqrt (β-α) = p := by
    rw [hpdef, Real.sqrt_mul hβge]
  have hterm1 : β*Real.sqrt β*((β-α)*Real.sqrt (β-α)) = p^3 := by
    calc β*Real.sqrt β*((β-α)*Real.sqrt (β-α))
        = (β*(β-α))*(Real.sqrt β*Real.sqrt (β-α)) := by ring
      _ = (β*(β-α))*p := by rw [hsqrtmul]
      _ = p^2*p := by rw [hp2]
      _ = p^3 := by ring
  have hterm2 : β*Real.sqrt β*Real.sqrt (β-α) = β*p := by
    calc β*Real.sqrt β*Real.sqrt (β-α) = β*(Real.sqrt β*Real.sqrt (β-α)) := by ring
      _ = β*p := by rw [hsqrtmul]
  have hS2 : 2*(∑ c ∈ Finset.Icc (n+1) K, H (c:ℤ)) ≤ 4*p^3 + 8*(β*p) := by
    have h2 := mul_le_mul_of_nonneg_left hRII (by norm_num : (0:ℝ) ≤ 2)
    have he : 2*(2*β*Real.sqrt β*((β-α)*Real.sqrt (β-α) + 2*Real.sqrt (β-α)))
        = 4*(β*Real.sqrt β*((β-α)*Real.sqrt (β-α)))
          + 8*(β*Real.sqrt β*Real.sqrt (β-α)) := by ring
    rw [he, hterm1, hterm2] at h2
    linarith [h2]
  have hp2b : p^2 ≤ D*N/(2*α^2) := by
    rw [hp2]
    have h1 : β*(β-α) ≤ 2*α*(D*N/(4*α^3)) :=
      mul_le_mul hβ2α hβα (by linarith [hαβ]) (by positivity)
    calc β*(β-α) ≤ 2*α*(D*N/(4*α^3)) := h1
      _ = D*N/(2*α^2) := by field_simp; ring
  have hp_le : p ≤ Real.sqrt (D*N)/α := by
    have h1 : p ≤ Real.sqrt (D*N/(2*α^2)) := by
      rw [← Real.sqrt_sq hp0]
      exact Real.sqrt_le_sqrt hp2b
    have h2 : Real.sqrt (D*N/(2*α^2)) ≤ Real.sqrt (D*N)/α := by
      rw [Real.sqrt_div hDN0]
      apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hα0
      rw [show (2:ℝ)*α^2 = (Real.sqrt 2*α)^2 by rw [mul_pow, Real.sq_sqrt (by norm_num)]]
      rw [Real.sqrt_sq (by positivity)]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hα0]
    linarith [h1, h2]
  have h4p3 : 4*p^3 ≤ 4*(D*N/α) := by
    have h1 : p^3 = p*p^2 := by ring
    have h2 : p*p^2 ≤ (Real.sqrt (D*N)/α)*(D*N/(2*α^2)) :=
      mul_le_mul hp_le hp2b (by positivity) (by positivity)
    have h3 : (Real.sqrt (D*N)/α)*(D*N/(2*α^2)) ≤ D*N/α := by
      have he : (Real.sqrt (D*N)/α)*(D*N/(2*α^2))
          = Real.sqrt (D*N)*(D*N)/(2*α^3) := by field_simp
      rw [he, div_le_div_iff₀ (by positivity : (0:ℝ) < 2*α^3) hα0]
      have h4 : Real.sqrt (D*N)*(D*N)*α ≤ α^2*(D*N)*α := by
        apply mul_le_mul_of_nonneg_right _ hα0.le
        exact mul_le_mul_of_nonneg_right hsDN hDN0
      have h5 : α^2*(D*N)*α ≤ (D*N)*(2*α^3) := by
        have h6 : (0:ℝ) ≤ D*N*α^3 := mul_nonneg hDN0 (by positivity)
        rw [show α^2*(D*N)*α = D*N*α^3 by ring]
        nlinarith [h6]
      linarith [h4, h5]
    rw [h1]
    linarith [h2, h3]
  have h8bp : 8*(β*p) ≤ 16*Real.sqrt (D*N) := by
    have h1 : β*p ≤ 2*α*(Real.sqrt (D*N)/α) :=
      mul_le_mul hβ2α hp_le hp0 (by positivity)
    have h2 : 2*α*(Real.sqrt (D*N)/α) = 2*Real.sqrt (D*N) := by field_simp
    linarith [h1, h2]
  have hkey : (∑ c ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), H c)
      ≤ 20 * (D*N/α + Real.sqrt (D*N)) := by
    have hx : 0 ≤ D*N/α := div_nonneg hDN0 hα0.le
    have hy : 0 ≤ Real.sqrt (D*N) := Real.sqrt_nonneg _
    linarith [hS, hH0', hS1, hS2, h4p3, h8bp, hx, hy]
  have hDα : D*N/α = (X₂ - X₁)*N*((X₁*N)^((1:ℝ)/4))⁻¹ := by
    rw [div_eq_mul_inv, hDdef, hαdef]
  have hDNsq : Real.sqrt (D*N) = Real.sqrt ((X₂ - X₁)*N) := by rw [hDdef]
  rw [hDα, hDNsq] at hkey
  exact hkey

end

/-
**Key real-variable estimate for the thin-annulus count.**

For `1 ≤ A ≤ B ≤ 2A` and `K ≥ B^{1/4}`,
`Σ_{|c| ≤ K} (√((B-c⁴)₊) - √((A-c⁴)₊)) ≤ C((B-A)A^{-1/4} + √(B-A))`.

Only `c` with `c⁴ ≤ B` contribute, and for those `|c| ≤ B^{1/4} ≤ K`; so the range `Icc (-K) K`
contains every nonzero term and enlarging `K` past `B^{1/4}` adds only `0`s.

Proof sketch (write `δ = B - A ≥ 0`, `γ = A^{1/4} ≥ 1`; note `δ ≤ A` because `B ≤ 2A`).
Split the `c` into three blocks according to the position of `c⁴` in `[0,B]`.

*(i)* `c⁴ ≤ A - δ`.  Here both maxima are the plain arguments and
`√(B-c⁴)-√(A-c⁴) = δ/(√(B-c⁴)+√(A-c⁴)) ≤ δ/(2√(A-c⁴))`.
Put `γ' = (A-δ)^{1/4} ≥ (A/2)^{1/4}`.  For `|c| ≤ γ'/2` we have `A-c⁴ ≥ γ'⁴ - c⁴ ≥ (15/16)γ'⁴`,
so `(A-c⁴)^{-1/2} ≤ 2γ'^{-2}` and there are at most `γ'+1` such `c`; for `γ'/2 < |c| < γ'`,
`A-c⁴ ≥ γ'⁴-c⁴ ≥ (γ'-|c|)·γ'³`, so `(A-c⁴)^{-1/2} ≤ (γ'-|c|)^{-1/2}γ'^{-3/2}` and
`Σ_{k≥1}k^{-1/2} ≤ 2√(γ')` bounds that piece by `4γ'^{-1}`.  Hence
`Σ_{c⁴ ≤ A-δ}(A-c⁴)^{-1/2} ≤ C₁γ^{-1} = C₁A^{-1/4}` and this block is `≤ (C₁/2)δA^{-1/4}`.

*(ii)* `A-δ < c⁴ < A`.  Each summand is `≤ √(B-c⁴) ≤ √(2δ)`, and the number of integers `c`
in that range is `≤ 2(γ-γ')+2 ≤ δ/(2γ'³)+2` (concavity of `t ↦ t^{1/4}`), so this block is
`≤ √(2δ)·(δ/(2γ'³)+2) ≤ δ^{3/2}/(√2γ'³) + 2√(2δ) ≤ C(δA^{-1/4} + √δ)` using `δ ≤ A`.

*(iii)* `c⁴ ≥ A`.  The summand is `√((B-c⁴)₊)`, so only `c⁴ ≤ B` contributes.  The contributing
`c` are symmetric under `c ↦ -c` and `c ≠ 0`, so it suffices to double the contribution of `c ≥ 0`.
With `a = ⌈γ⌉` (so `a⁴ ≥ A`) write `c = a+j`, `j ≥ 0`; then
`c⁴ - A ≥ a⁴-A+4a³j ≥ 4γ³j`, hence `B-c⁴ ≤ δ - 4γ³j`, and
`Σ_{j≥0}√(max(δ-4γ³j,0)) ≤ √δ + Σ_{j≥1}√(δ-4γ³j) ≤ √δ + (2/3)δ^{3/2}/(4γ³) = √δ + δ^{3/2}/(6γ³)`,
which is `≤ C(δA^{-1/4} + √δ)` by `δ ≤ A`.  Doubling it keeps the same shape.

Adding the three blocks gives the claim with a uniform constant.
-/
theorem thin_real_sum_core :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℝ) (K : ℕ),
      (1 : ℝ) ≤ A → A ≤ B → B ≤ 2 * A → B ^ ((1 : ℝ) / 4) ≤ (K : ℝ) →
      (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (Real.sqrt (max (B - (c : ℝ) ^ 4) 0) - Real.sqrt (max (A - (c : ℝ) ^ 4) 0)))
        ≤ C * ((B - A) * A ^ (-(1 : ℝ) / 4) + Real.sqrt (B - A)) := by
  obtain ⟨C, hC0, hC⟩ := trsc_real_sum_general
  refine ⟨C, hC0, ?_⟩
  intro A B K hA hAB hB2A hK
  have hA0 : 0 < A := by linarith
  have h := hC A B 1 K hA hAB hB2A (by norm_num) (by simpa using hK)
  have hAinv : A ^ (-(1:ℝ)/4) = (A ^ ((1:ℝ)/4))⁻¹ := by
    rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) by ring, Real.rpow_neg hA0.le]
  have hmain : (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (Real.sqrt (max (B - (c : ℝ) ^ 4) 0) - Real.sqrt (max (A - (c : ℝ) ^ 4) 0)))
      ≤ C * ((B - A) * (A ^ ((1:ℝ)/4))⁻¹ + Real.sqrt (B - A)) := by
    simpa [mul_one] using h
  have hgoal : C * ((B - A) * A ^ (-(1 : ℝ) / 4) + Real.sqrt (B - A))
      = C * ((B - A) * (A ^ ((1:ℝ)/4))⁻¹ + Real.sqrt (B - A)) := by rw [hAinv]
  rw [hgoal]
  exact hmain

end Work.FITop4.Red5
