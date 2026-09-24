import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.Commons.Algebra.BigOperators.sum_Icc_filter_dvd

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

/-- For `m ≥ 1`, the divisors of `m` that are `≤ T` are exactly the elements of `[1, T]`
that divide `m`. -/
private lemma divisors_filter_le_eq (m T : ℕ) (hm : 1 ≤ m) :
    m.divisors.filter (fun d => d ≤ T) = (Finset.Icc 1 T).filter (fun d => d ∣ m) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, hne⟩, hle⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hle⟩, hdvd⟩
  · rintro ⟨⟨h1, hle⟩, hdvd⟩
    exact ⟨⟨hdvd, by omega⟩, hle⟩

/-- Reindexing the double sum over divisors: for `n ≥ 1`, summing `g d e` over pairs of
divisors `d ∣ n` with `e ∣ n/d`, both `≤ T`, equals summing `g d e` over all pairs
`d, e ∈ [1, T]` with `d * e ∣ n`. -/
private lemma divisor_pair_reindex {T n : ℕ} (hn : 1 ≤ n) {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → M) :
    (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
        ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T), g d e)
      = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          (if d * e ∣ n then g d e else 0) := by
  rw [divisors_filter_le_eq n T hn, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hnd1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
    rw [divisors_filter_le_eq (n / d) T hnd1, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e he => ?_)
    by_cases hev : e ∣ n / d
    · rw [if_pos hev, if_pos ((Nat.dvd_div_iff_mul_dvd hdn).mp hev)]
    · rw [if_neg hev, if_neg (fun hh => hev ((Nat.dvd_div_iff_mul_dvd hdn).mpr hh))]
  · rw [if_neg hdn]
    symm
    refine Finset.sum_eq_zero (fun e he => ?_)
    have hde : ¬ d * e ∣ n := fun h => hdn (dvd_trans (dvd_mul_right d e) h)
    rw [if_neg hde]

/-- Twisted sum over the multiples of `t` in `[1, y]`. -/
private lemma char_sum_multiples {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y t : ℕ) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ∣ n), χ (n : ZMod q))
      = χ (t : ZMod q) * ∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q) := by
  rw [Commons.Algebra.BigOperators.sum_Icc_filter_dvd t y (fun n => χ (n : ZMod q))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Nat.cast_mul, map_mul]

/-- **Reindexing identity for the `λ₃` piece of Vaughan's decomposition.**  Writing
`λ₃(n) = Σ_{d|n, d≤T} Σ_{e|n/d, e≤T} μ d · Λ e` and
`a_t = Σ_{d e = t, d,e ≤ T} μ d · Λ e` (so that `λ₃(n) = Σ_{t|n} a_t`), the twisted sum over
`n ≤ y` equals the double sum `Σ_{t≤T²} a_t χ(t) Σ_{r≤y/t} χ(r)`:
this is the splitting `S₃ = S₃' + S₃''` of Vaughan's mean value theorem (the ranges
`t ≤ T` and `T < t ≤ T²` being the two type-I / type-II parts). -/
theorem vaughan_lambda3_reindex (T y q : ℕ) (hT : 1 ≤ T) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 y,
        (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ))
        * χ (n : ZMod q))
      = ∑ t ∈ Finset.Icc 1 (T ^ 2),
          (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
          * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) := by
  have hchi_sum : ∀ t : ℕ,
      (∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ∣ n), χ (n : ZMod q))
        = χ (t : ZMod q) * ∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q) :=
    fun t => char_sum_multiples χ y t
  -- Step L1: turn the double divisor sum into a pair sum over [1,T]².
  have hL1 : (∑ n ∈ Finset.Icc 1 y,
        (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ))
        * χ (n : ZMod q))
      = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          (if d * e ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) else 0) * χ (n : ZMod q) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [divisor_pair_reindex (T := T) hn1
          (fun d e => ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ))]
    simp only [Finset.sum_mul]
  -- Step L2: swap summations and reattach the character.
  have hL2 : (∑ n ∈ Finset.Icc 1 y, ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          (if d * e ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) else 0) * χ (n : ZMod q))
      = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * (∑ n ∈ (Finset.Icc 1 y).filter (fun n => d * e ∣ n), χ (n : ZMod q)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hpt : ∀ n : ℕ, (if d * e ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) else 0) * χ (n : ZMod q)
        = (if d * e ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) * χ (n : ZMod q) else 0) := by
      intro n; by_cases h : d * e ∣ n <;> simp [h]
    simp only [hpt]
    rw [← Finset.sum_filter (s := Finset.Icc 1 y) (p := fun n => d * e ∣ n)
          (f := fun n => ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) * χ (n : ZMod q))]
    rw [Finset.mul_sum]
  -- Step M: apply the character sum identity.
  have hM : (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * (∑ n ∈ (Finset.Icc 1 y).filter (fun n => d * e ∣ n), χ (n : ZMod q)))
      = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * (χ ((d * e : ℕ) : ZMod q) *
                ∑ r ∈ Finset.Icc 1 (y / (d * e)), χ (r : ZMod q)) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [hchi_sum (d * e)]
  -- Step R1: push the character and the `r`-sum inside the fiber sums.
  have hR1 : (∑ t ∈ Finset.Icc 1 (T ^ 2),
          (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
          * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
      = ∑ t ∈ Finset.Icc 1 (T ^ 2),
          ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
              * (χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [mul_assoc, Finset.sum_mul]
  -- Step R2: replace `t` by `kl.1 * kl.2` inside the fiber.
  have hR2 : (∑ t ∈ Finset.Icc 1 (T ^ 2),
          ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
              * (χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))))
      = ∑ t ∈ Finset.Icc 1 (T ^ 2),
          ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
              * (χ ((kl.1 * kl.2 : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (kl.1 * kl.2)), χ (r : ZMod q))) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    refine Finset.sum_congr rfl (fun kl hkl => ?_)
    have h : kl.1 * kl.2 = t := (Finset.mem_filter.mp hkl).2
    rw [← h]
  -- Step R3: collapse the fiber sums.
  have hR3 : (∑ t ∈ Finset.Icc 1 (T ^ 2),
          ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
              * (χ ((kl.1 * kl.2 : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (kl.1 * kl.2)), χ (r : ZMod q))))
      = ∑ kl ∈ Finset.Icc 1 T ×ˢ Finset.Icc 1 T,
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
              * (χ ((kl.1 * kl.2 : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (kl.1 * kl.2)), χ (r : ZMod q))) := by
    refine Finset.sum_fiberwise_of_maps_to ?_ _
    intro kl hkl
    rw [Finset.mem_Icc]
    rw [Finset.mem_product] at hkl
    obtain ⟨h1, h2⟩ := hkl
    rw [Finset.mem_Icc] at h1 h2
    refine ⟨Nat.mul_pos (by omega) (by omega), ?_⟩
    calc kl.1 * kl.2 ≤ T * T := Nat.mul_le_mul h1.2 h2.2
      _ = T ^ 2 := by ring
  -- Step R4: expand the product set.
  have hR4 : (∑ kl ∈ Finset.Icc 1 T ×ˢ Finset.Icc 1 T,
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
              * (χ ((kl.1 * kl.2 : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (kl.1 * kl.2)), χ (r : ZMod q))))
      = ∑ a ∈ Finset.Icc 1 T, ∑ b ∈ Finset.Icc 1 T,
            ((ArithmeticFunction.moebius b : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt a : ℝ) : ℂ)
              * (χ ((a * b : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (a * b)), χ (r : ZMod q))) := by
    rw [Finset.sum_product]
  -- Step R5: swap the two summation variables.
  have hR5 : (∑ a ∈ Finset.Icc 1 T, ∑ b ∈ Finset.Icc 1 T,
            ((ArithmeticFunction.moebius b : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt a : ℝ) : ℂ)
              * (χ ((a * b : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (a * b)), χ (r : ZMod q))))
      = ∑ a ∈ Finset.Icc 1 T, ∑ b ∈ Finset.Icc 1 T,
            ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)
              * (χ ((a * b : ℕ) : ZMod q) *
                  (∑ r ∈ Finset.Icc 1 (y / (a * b)), χ (r : ZMod q))) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Nat.mul_comm a b]
  rw [hL1, hL2, hM, hR1, hR2, hR3, hR4, hR5]

end Commons.NumberTheory.BombieriVinogradov