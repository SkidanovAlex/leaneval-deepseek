import Mathlib
import Submission.Commons.Analysis.Series.sum_Icc_inv_mul_sqrt_le_three

namespace Commons.Data.Nat

open scoped BigOperators

/-- For `b ≥ 1`, `√(X / b³) = √X · (1 / (b · √b))`. -/
private lemma sqrt_div_cube_eq (X b : ℕ) (hb : 1 ≤ b) :
    Real.sqrt ((X:ℝ)/(b:ℝ)^3) = Real.sqrt X * (1/((b:ℝ)*Real.sqrt b)) := by
  have hX : (0:ℝ) ≤ X := by positivity
  have hb0 : (0:ℝ) ≤ b := by positivity
  rw [Real.sqrt_div hX]
  have hsqrtb3 : Real.sqrt ((b:ℝ)^3) = (b:ℝ)*Real.sqrt b := by
    have h3 : (b:ℝ)^3 = (b:ℝ)^2 * b := by ring
    rw [h3, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (b:ℝ)^2), Real.sqrt_sq hb0]
  rw [hsqrtb3, div_eq_mul_inv, one_div]

/-- `√X ≤ ⌊√X⌋ + 1` for a natural `X`. -/
private lemma sqrt_le_sqrt_cast_succ (X : ℕ) : Real.sqrt X ≤ (Nat.sqrt X : ℝ) + 1 := by
  have hle : (X:ℝ) ≤ ((Nat.sqrt X : ℝ) + 1)^2 := by
    have h := Nat.lt_succ_sqrt X
    have h' : (X:ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) * ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    nlinarith [h']
  calc Real.sqrt X ≤ Real.sqrt (((Nat.sqrt X:ℝ)+1)^2) := Real.sqrt_le_sqrt hle
    _ = (Nat.sqrt X:ℝ)+1 := Real.sqrt_sq (by positivity)

/-- The number of pairs `(a, b)` of positive integers with `a ^ 2 * b ^ 3 ≤ X` is at most
`3 * (⌊√X⌋ + 1)`.

Write the count as the sum over `b` of the number of admissible `a`; for fixed `b` this is at most
`⌊√(X / b³)⌋ ≤ √(X / b³) = √X · b^{-3/2}`, and `∑_{b ≥ 1} b^{-3/2} ≤ 3`. -/
theorem ncard_pairs_sq_mul_cube_le (X : ℕ) :
    ({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ X} : Set (ℕ × ℕ)).ncard
      ≤ 3 * (Nat.sqrt X + 1) := by
  let B := Nat.sqrt X
  let Sfin : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter (fun p => p.1^2 * p.2^3 ≤ X)
  -- The set of interest is exactly the Finset `Sfin`.
  have hS : ({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ X} : Set (ℕ × ℕ))
      = (Sfin : Set (ℕ × ℕ)) := by
    ext p
    simp only [Finset.mem_coe, Sfin, Finset.mem_filter, Finset.mem_product, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨?_, ?_⟩, h3⟩
      · refine Finset.mem_Icc.mpr ⟨h1, ?_⟩
        have hp : p.1^2 ≤ X := by
          calc p.1^2 = p.1^2 * 1 := by ring
            _ ≤ p.1^2 * p.2^3 := Nat.mul_le_mul_left _ (Nat.one_le_pow 3 p.2 (by omega))
            _ ≤ X := h3
        exact Nat.le_sqrt'.mpr hp
      · refine Finset.mem_Icc.mpr ⟨h2, ?_⟩
        have hp : p.2^2 ≤ X := by
          have h1' : p.2^2 ≤ p.2^3 := by
            calc p.2^2 = p.2^2 * 1 := by ring
              _ ≤ p.2^2 * p.2 := Nat.mul_le_mul_left _ h2
              _ = p.2^3 := by ring
          have h2' : p.2^3 ≤ p.1^2 * p.2^3 := by
            calc p.2^3 = 1 * p.2^3 := by rw [Nat.one_mul]
              _ ≤ p.1^2 * p.2^3 := Nat.mul_le_mul_right _ (Nat.one_le_pow 2 p.1 (by omega))
          exact h1'.trans (h2'.trans h3)
        exact Nat.le_sqrt'.mpr hp
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(Finset.mem_Icc.mp h1).1, (Finset.mem_Icc.mp h2).1, h3⟩
  rw [hS, Set.ncard_coe_finset]
  -- Decompose over the second coordinate.
  have hmaps : Set.MapsTo Prod.snd (↑Sfin : Set (ℕ×ℕ)) (↑(Finset.Icc 1 B) : Set ℕ) := by
    intro p hp
    simp only [Finset.mem_coe, Sfin, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.2
  have hcard : Sfin.card = ∑ b ∈ Finset.Icc 1 B, (Sfin.filter (fun p => p.2 = b)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- Each fiber is bounded by `√(X / b³)`.
  have hbound : ∀ b ∈ Finset.Icc 1 B,
      ((Sfin.filter (fun p => p.2 = b)).card : ℝ) ≤ Real.sqrt ((X:ℝ)/(b:ℝ)^3) := by
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hAa : (Sfin.filter (fun p => p.2 = b)).card
        ≤ ((Finset.Icc 1 B).filter (fun a => a^2 * b^3 ≤ X)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        simp only [Finset.mem_coe, Sfin, Finset.mem_filter, Finset.mem_product] at hp
        obtain ⟨⟨⟨hp1, hp2⟩, hpX⟩, hpb⟩ := hp
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨hp1, ?_⟩
        rw [← hpb]
        exact hpX
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
        obtain ⟨_, hpb⟩ := hp
        obtain ⟨_, hqb⟩ := hq
        exact Prod.ext hpq (by rw [hpb, hqb])
    have hAcard : ((Finset.Icc 1 B).filter (fun a => a^2 * b^3 ≤ X)).card
        ≤ Nat.sqrt (X / b^3) := by
      calc ((Finset.Icc 1 B).filter (fun a => a^2 * b^3 ≤ X)).card
          ≤ (Finset.Icc 1 (Nat.sqrt (X / b^3))).card := by
            apply Finset.card_le_card
            intro a ha
            rw [Finset.mem_filter] at ha
            obtain ⟨haIcc, haX⟩ := ha
            rw [Finset.mem_Icc] at haIcc ⊢
            refine ⟨haIcc.1, ?_⟩
            exact Nat.le_sqrt'.mpr (by
              rw [Nat.le_div_iff_mul_le (by positivity : 0 < b^3)]
              exact haX)
        _ = Nat.sqrt (X / b^3) := by
            rw [Nat.card_Icc]; omega
    have hcast : ((Nat.sqrt (X / b^3) : ℕ) : ℝ) ≤ Real.sqrt ((X:ℝ)/(b:ℝ)^3) := by
      calc ((Nat.sqrt (X / b^3) : ℕ) : ℝ) ≤ Real.sqrt ((X / b^3 : ℕ) : ℝ) := by
            rw [Real.le_sqrt (by positivity) (by positivity)]
            exact_mod_cast (Nat.sqrt_le' (X / b^3))
        _ ≤ Real.sqrt ((X:ℝ)/(b:ℝ)^3) := by
            apply Real.sqrt_le_sqrt
            have h := Nat.cast_div_le (α := ℝ) (m := X) (n := b^3)
            rwa [Nat.cast_pow] at h
    calc ((Sfin.filter (fun p => p.2 = b)).card : ℝ)
        ≤ (((Finset.Icc 1 B).filter (fun a => a^2 * b^3 ≤ X)).card : ℝ) := by exact_mod_cast hAa
      _ ≤ ((Nat.sqrt (X / b^3) : ℕ) : ℝ) := by exact_mod_cast hAcard
      _ ≤ Real.sqrt ((X:ℝ)/(b:ℝ)^3) := hcast
  have hsum : (Sfin.card : ℝ) ≤ ∑ b ∈ Finset.Icc 1 B, Real.sqrt ((X:ℝ)/(b:ℝ)^3) := by
    rw [hcard, Nat.cast_sum]
    exact Finset.sum_le_sum hbound
  -- The analytical estimate `∑_{b=1}^{⌊√X⌋} √(X / b³) = √X · ∑ b^{-3/2} ≤ 3√X`.
  have hsum2 : ∑ b ∈ Finset.Icc 1 B, Real.sqrt ((X:ℝ)/(b:ℝ)^3) ≤ 3 * ((B:ℝ)+1) := by
    have hsplit : ∑ b ∈ Finset.Icc 1 B, Real.sqrt ((X:ℝ)/(b:ℝ)^3)
        = Real.sqrt X * ∑ b ∈ Finset.Icc 1 B, (1/((b:ℝ)*Real.sqrt b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b hb => sqrt_div_cube_eq X b (Finset.mem_Icc.mp hb).1)
    rw [hsplit]
    have hg : ∑ b ∈ Finset.Icc 1 B, (1/((b:ℝ)*Real.sqrt b)) ≤ 3 :=
      Commons.Analysis.Series.sum_Icc_inv_mul_sqrt_le_three B
    have hsqrtX : (0:ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
    calc Real.sqrt X * (∑ b ∈ Finset.Icc 1 B, (1/((b:ℝ)*Real.sqrt b)))
        ≤ Real.sqrt X * 3 := mul_le_mul_of_nonneg_left hg hsqrtX
      _ ≤ 3 * ((B:ℝ)+1) := by
          have := sqrt_le_sqrt_cast_succ X
          nlinarith [this]
  have : (Sfin.card : ℝ) ≤ ((3 * (B + 1) : ℕ) : ℝ) := by
    calc (Sfin.card : ℝ) ≤ ∑ b ∈ Finset.Icc 1 B, Real.sqrt ((X:ℝ)/(b:ℝ)^3) := hsum
      _ ≤ 3 * ((B:ℝ)+1) := hsum2
      _ = ((3 * (B + 1) : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast this

end Commons.Data.Nat
