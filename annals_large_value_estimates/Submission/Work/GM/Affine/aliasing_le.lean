import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# GM §9: the aliasing mass is bounded by the main term plus the Fourier decay tail

`aliasing f m = Σ_{k ∈ ℤ} ‖Fhat f (k * m)‖`.  The `k = 0` term equals `‖Fhat f 0‖ = ∫ f` because
`f ≥ 0`, and every other term is controlled by `DecayHyp`; summing the resulting series against
`Σ_{k ≠ 0} 1 / |k| ^ j ≤ 4` (valid for `j ≥ 2`) gives the claim.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-- `∑_{n ≥ 0} 1/(n+1)^2 ≤ 2`, by an elementary telescoping comparison with `∑ 2/(n(n+1))`. -/
lemma tsum_nat_succ_inv_sq_le_two : (∑' n : ℕ, (1:ℝ)/(((n:ℝ)+1)^2)) ≤ 2 := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => ?_)
  have hle : ∀ i ∈ Finset.range N,
      (1:ℝ)/(((i:ℝ)+1)^2) ≤ 2/((i:ℝ)+1) - 2/((i:ℝ)+2) := by
    intro i _
    have h' : 2/((i:ℝ)+1) - 2/((i:ℝ)+2) = 2/(((i:ℝ)+1)*((i:ℝ)+2)) := by
      field_simp
      ring
    rw [h']
    have h : (0:ℝ) ≤ 2/(((i:ℝ)+1)*((i:ℝ)+2)) - 1/(((i:ℝ)+1)^2) := by
      have heq : 2/(((i:ℝ)+1)*((i:ℝ)+2)) - 1/(((i:ℝ)+1)^2)
          = (i:ℝ)/(((i:ℝ)+1)^2 * ((i:ℝ)+2)) := by
        field_simp
        ring
      rw [heq]; positivity
    linarith
  calc ∑ i ∈ Finset.range N, (1:ℝ)/(((i:ℝ)+1)^2)
      ≤ ∑ i ∈ Finset.range N, (2/((i:ℝ)+1) - 2/((i:ℝ)+2)) := Finset.sum_le_sum hle
    _ = ∑ i ∈ Finset.range N,
          ((fun k : ℕ => 2/((k:ℝ)+1)) i - (fun k : ℕ => 2/((k:ℝ)+1)) (i+1)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    _ = 2/(((0:ℕ):ℝ)+1) - 2/((N:ℝ)+1) := Finset.sum_range_sub' (fun k : ℕ => 2/((k:ℝ)+1)) N
    _ ≤ 2 := by
        have h : (0:ℝ) ≤ 2/((N:ℝ)+1) := by positivity
        norm_num
        linarith

lemma summable_nat_inv_sq : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)^2)) :=
  (Real.summable_one_div_nat_pow (p:=2)).mpr (by norm_num)

/-- `∑_{k ∈ ℤ} 1/(k:ℝ)^2 ≤ 4` (with Mathlib's convention `1/0 = 0`, so the `k = 0` term is `0`).
This is the numerical input for summing the Fourier decay bound over the lattice, for any exponent
`j ≥ 2` (since `|k| ^ j ≥ |k| ^ 2` for `|k| ≥ 1`). -/
lemma tsum_int_inv_sq_le_four : (∑' k : ℤ, (1:ℝ)/((k:ℝ)^2)) ≤ 4 := by
  have hnat := summable_nat_inv_sq
  have hneg : Summable (fun n : ℕ => (1:ℝ)/(((-((n:ℤ)+1) : ℤ) : ℝ)^2)) := by
    have h1 : Summable (fun n : ℕ => (1:ℝ)/(((n:ℝ)+1)^2)) := by
      have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^2)) 1).mpr hnat
      simpa [Nat.cast_add, Nat.cast_one] using h2
    exact h1.congr (fun n => by
      have hcast : (((-((n:ℤ)+1) : ℤ) : ℝ)) = -((n:ℝ)+1) := by
        rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [hcast]
      ring)
  have hsplit : (∑' k : ℤ, (1:ℝ)/((k:ℝ)^2)) =
      (∑' n : ℕ, (1:ℝ)/((n:ℝ)^2)) + (∑' n : ℕ, (1:ℝ)/(((-((n:ℤ)+1):ℤ):ℝ)^2)) :=
    tsum_of_nat_of_neg_add_one hnat hneg
  have hp1 : (∑' n : ℕ, (1:ℝ)/(((n:ℕ):ℝ)^2)) ≤ 2 := by
    rw [Summable.tsum_eq_zero_add hnat]
    rw [show (1:ℝ)/(((0:ℕ):ℝ)^2) = 0 by norm_num, zero_add]
    simpa [Nat.cast_add, Nat.cast_one] using tsum_nat_succ_inv_sq_le_two
  have hp2 : (∑' n : ℕ, (1:ℝ)/(((-((n:ℤ)+1):ℤ):ℝ)^2)) ≤ 2 := by
    have hcongr : (∑' n : ℕ, (1:ℝ)/(((-((n:ℤ)+1):ℤ):ℝ)^2))
        = ∑' n : ℕ, (1:ℝ)/(((n:ℝ)+1)^2) := by
      apply tsum_congr
      intro n
      have hcast : (((-((n:ℤ)+1) : ℤ) : ℝ)) = -((n:ℝ)+1) := by
        rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [hcast]
      ring
    rw [hcongr]
    exact tsum_nat_succ_inv_sq_le_two
  calc (∑' k : ℤ, (1:ℝ)/((k:ℝ)^2))
      = (∑' n : ℕ, (1:ℝ)/((n:ℝ)^2)) + (∑' n : ℕ, (1:ℝ)/(((-((n:ℤ)+1):ℤ):ℝ)^2)) := hsplit
    _ ≤ 2 + 2 := add_le_add hp1 hp2
    _ = 4 := by norm_num

lemma fhat_zero_eq_integral (f : ℝ → ℝ) : Fhat f 0 = (((∫ u : ℝ, f u) : ℝ) : ℂ) := by
  have h1 : Fhat f 0 = ∫ v : ℝ, (f v : ℂ) := by
    simp only [Fhat]
    rw [Real.fourier_eq]
    congr 1
    funext v
    simp
  rw [h1]
  exact integral_ofReal

/-- `(T/m)^j * (m/|ξ|)^j = (T/|ξ|)^j` for `m ≠ 0 ≠ ξ`: the exponent of the decay hypothesis is
the same when the lattice step `m` is traded for the point `ξ`. -/
lemma div_pow_mul_div_pow (T m ξ : ℝ) (j : ℕ) (hm : m ≠ 0) (hξ : ξ ≠ 0) :
    (T/m)^j * (m/|ξ|)^j = (T/|ξ|)^j := by
  rw [← mul_pow]
  congr 1
  field_simp

theorem aliasing_le {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f) (hdec : DecayHyp c T f) {m : ℝ}
    (hm : 0 < m) {j : ℕ} (hj : 2 ≤ j) {ε : ℝ} (hε : 0 < ε) (hc : 0 ≤ c j ε) :
    aliasing f m ≤ (∫ u, f u) + 4 * (c j ε) * T ^ ε * (T / m) ^ j * supf f := by
  have hInn : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hsupnn : 0 ≤ supf f := supf_nonneg hf hcs hnn
  have hmne : m ≠ 0 := ne_of_gt hm
  -- the `k = 0` term of the aliasing sum
  have hg0 : ‖Fhat f 0‖ = ∫ u, f u := by
    rw [fhat_zero_eq_integral f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hInn]
  have hhsum : Summable (fun k : ℤ => (1:ℝ)/((k:ℝ)^2)) :=
    (Real.summable_one_div_int_pow (p:=2)).mpr (by norm_num)
  set B : ℝ := c j ε * T ^ ε * (T / m) ^ j * supf f with hB
  -- The decay hypothesis forces `B ≥ 0`: otherwise it would give a negative bound for `‖Fhat f ξ‖`.
  have hBnn : 0 ≤ B := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 := hdec j ε hε 1 one_ne_zero
    have h2 : c j ε * T ^ ε * (T / |(1:ℝ)|) ^ j * supf f = B * (m / |(1:ℝ)|) ^ j := by
      rw [← div_pow_mul_div_pow T m 1 j hmne one_ne_zero, hB]
      ring
    have h3 : B * (m / |(1:ℝ)|) ^ j < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    rw [h2] at h1
    exact absurd (lt_of_le_of_lt h1 h3) (not_lt.mpr (norm_nonneg _))
  -- the decay bound for `k ≠ 0`, normalised against `B`
  have hdec' : ∀ k : ℤ, k ≠ 0 → ‖Fhat f ((k:ℝ) * m)‖ ≤ B / ((k:ℝ)^2) := by
    intro k hk
    have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    have hk0 : (k:ℝ) * m ≠ 0 := mul_ne_zero hkR hmne
    have h1 := hdec j ε hε ((k:ℝ)*m) hk0
    have hTm : T / (|(k:ℝ)| * m) = (T/m)/|(k:ℝ)| := by
      rw [div_div]
      congr 1
      ring
    have h2 : c j ε * T ^ ε * (T / |(k:ℝ) * m|) ^ j * supf f = B / |(k:ℝ)|^j := by
      rw [abs_mul, abs_of_pos hm, hTm, div_pow, hB]
      ring
    have hk1 : (1:ℝ) ≤ |(k:ℝ)| := by
      have := Int.one_le_abs hk
      exact_mod_cast this
    have hpow : |(k:ℝ)|^2 ≤ |(k:ℝ)|^j := pow_le_pow_right₀ hk1 hj
    have hpos : (0:ℝ) < |(k:ℝ)|^2 := by positivity
    calc ‖Fhat f ((k:ℝ) * m)‖
        ≤ c j ε * T ^ ε * (T / |(k:ℝ) * m|) ^ j * supf f := h1
      _ = B / |(k:ℝ)|^j := h2
      _ ≤ B / |(k:ℝ)|^2 := div_le_div_of_nonneg_left hBnn hpos hpow
      _ = B / (k:ℝ)^2 := by rw [sq_abs]
  -- the aliasing sum is summable (decay with `j = 2` supplies a summable majorant)
  have hgsum : Summable (fun k : ℤ => ‖Fhat f ((k:ℝ) * m)‖) := by
    set B₂ : ℝ := c 2 ε * T ^ ε * T ^ 2 * supf f / m ^ 2 with hB₂
    have hle : ∀ k : ℤ, k ≠ 0 → ‖Fhat f ((k:ℝ) * m)‖ ≤ max B₂ 0 / ((k:ℝ)^2) := by
      intro k hk
      have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
      have hk0 : (k:ℝ) * m ≠ 0 := mul_ne_zero hkR hmne
      have hd := hdec 2 ε hε ((k:ℝ)*m) hk0
      have h1 : (T / |(k:ℝ) * m|) ^ 2 = T^2 / ((k:ℝ)^2 * m^2) := by
        rw [div_pow, abs_mul, abs_of_pos hm, mul_pow, sq_abs]
      calc ‖Fhat f ((k:ℝ) * m)‖ ≤ c 2 ε * T ^ ε * (T / |(k:ℝ) * m|) ^ 2 * supf f := hd
        _ = B₂ / ((k:ℝ)^2) := by rw [h1, hB₂]; ring
        _ ≤ max B₂ 0 / ((k:ℝ)^2) :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    have hsum : Summable fun k : ℤ => max B₂ 0 / ((k:ℝ)^2) := by
      have h2 := hhsum.mul_left (max B₂ 0)
      refine h2.congr (fun k => ?_)
      ring
    refine Summable.of_norm_bounded_eventually hsum ?_
    filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hle k hk
  -- majorant obtained from the decay bound, separated at `k = 0`
  have h1G : Summable (fun k : ℤ => if k = 0 then ‖Fhat f 0‖ else (0:ℝ)) := by
    refine summable_of_hasFiniteSupport ?_
    apply Set.Finite.subset (Set.finite_singleton (0:ℤ))
    intro k hk
    simp only [Function.mem_support, Set.mem_singleton_iff] at hk ⊢
    by_cases h : k = 0
    · exact h
    · exact absurd (if_neg h) hk
  have h2G : Summable (fun k : ℤ => B * ((1:ℝ)/((k:ℝ)^2))) := hhsum.mul_left B
  set G : ℤ → ℝ := fun k => (if k = 0 then ‖Fhat f 0‖ else 0) + B * ((1:ℝ)/((k:ℝ)^2)) with hG
  have hGsum : Summable G := by
    rw [hG]; exact h1G.add h2G
  have hleG : ∀ k : ℤ, ‖Fhat f ((k:ℝ) * m)‖ ≤ G k := by
    intro k
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      rw [hG]
      simp
    · rw [hG]
      simp only [if_neg hk, zero_add]
      rw [div_eq_mul_inv, one_mul]
      exact hdec' k hk
  have hsum_le : (∑' k : ℤ, ‖Fhat f ((k:ℝ) * m)‖) ≤ ∑' k : ℤ, G k :=
    Summable.tsum_le_tsum hleG hgsum hGsum
  -- evaluate the majorant's sum
  have hGtsum : (∑' k : ℤ, G k)
      = ‖Fhat f 0‖ + B * (∑' k : ℤ, (1:ℝ)/((k:ℝ)^2)) := by
    rw [hG, Summable.tsum_add h1G h2G]
    congr 1
    · exact tsum_ite_eq (0:ℤ) (fun _ => ‖Fhat f 0‖)
    · exact tsum_mul_left
  have hGle : (∑' k : ℤ, G k) ≤ ‖Fhat f 0‖ + B * 4 := by
    rw [hGtsum]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left tsum_int_inv_sq_le_four hBnn)
  show (∑' k : ℤ, ‖Fhat f ((k:ℝ) * m)‖) ≤
    (∫ u, f u) + 4 * (c j ε) * T ^ ε * (T / m) ^ j * supf f
  calc (∑' k : ℤ, ‖Fhat f ((k:ℝ) * m)‖) ≤ ∑' k : ℤ, G k := hsum_le
    _ ≤ ‖Fhat f 0‖ + B * 4 := hGle
    _ = (∫ u, f u) + 4 * (c j ε) * T ^ ε * (T / m) ^ j * supf f := by
        rw [hg0, hB]; ring

end

end Work.GM.Affine
