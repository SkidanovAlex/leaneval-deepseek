import Mathlib
import Submission.Szemeredi.Basic

open scoped BigOperators
open Filter Finset

namespace Szemeredi

/-- A sorted 3-term configuration `x < y < z` with `x + z = 2y`, all in `A`, gives an AP. -/
lemma hasAP_three_of_sorted {A : Set ℕ} {x y z : ℕ}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (_hxy : x < y) (_hyz : y < z) (hmid : x + z = y + y) : HasAP A 3 := by
  let d : ℕ := y - x
  have hxd : y = x + d := by
    dsimp [d]
    omega
  have hmain : x + 2 * d = z := by
    dsimp [d]
    omega
  refine ⟨x, d, ?_, ?_⟩
  · dsimp [d]
    omega
  · intro j hj
    interval_cases j
    · simpa using hx
    · have hmem : x + d ∈ A := by
        rw [← hxd]
        exact hy
      simpa using hmem
    · have hz' : x + d * 2 = z := by
        rw [Nat.mul_comm d 2]
        exact hmain
      rw [hz']
      exact hz

/-- A set of naturals which is not `ThreeAPFree` contains a 3-term AP. -/
theorem hasAP_three_of_not_threeAPFree {A : Set ℕ} (h : ¬ ThreeAPFree A) : HasAP A 3 := by
  classical
  rw [threeAPFree_iff_eq_right] at h
  push Not at h
  rcases h with ⟨a, ha, b, hb, c, hc, hsum, hne⟩
  rcases lt_or_gt_of_ne hne with hac | hca
  · have hab : a < b := by omega
    have hbc : b < c := by omega
    exact hasAP_three_of_sorted ha hb hc hab hbc hsum
  · have hcb : c < b := by omega
    have hba : b < a := by omega
    exact hasAP_three_of_sorted hc hb ha hcb hba (by omega)

/-- The finite form of Szemerédi's theorem for `k = 3` (Roth's theorem). -/
theorem finiteSzemeredi_three (δ : ℝ) (hδ : 0 < δ) : FiniteSzemeredi 3 δ := by
  refine ⟨cornersTheoremBound (δ / 3), ?_⟩
  intro N hN A hAsub hAδ
  exact hasAP_three_of_not_threeAPFree
    (roth_3ap_theorem_nat (n := N) (ε := δ) hδ hN A hAsub hAδ)

/-- Roth's theorem in density form: a set of positive upper density contains a 3-term AP. -/
theorem roth_upperDensity (A : Set ℕ) (hd : PositiveUpperDensity A) : HasAP A 3 := by
  exact ap_of_finite (k := 3) (fun δ hδ => finiteSzemeredi_three δ hδ) hd

/-- The finite form for `k = 0` is vacuous. -/
theorem finiteSzemeredi_zero (δ : ℝ) (_hδ : 0 < δ) : FiniteSzemeredi 0 δ := by
  refine ⟨0, ?_⟩
  intro N hN A hAsub hAδ
  exact hasAP_zero (A : Set ℕ)

/-- The finite form for `k = 1`: a positive-density subset of `{0,…,N-1}` is nonempty. -/
theorem finiteSzemeredi_one (δ : ℝ) (hδ : 0 < δ) : FiniteSzemeredi 1 δ := by
  refine ⟨1, ?_⟩
  intro N hN A hAsub hAδ
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hδN : 0 < δ * (N : ℝ) := mul_pos hδ hNpos
  have hden : 0 < (A.card : ℝ) := lt_of_lt_of_le hδN hAδ
  have hc : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hden)
  exact hasAP_one (by simpa using hc)

/-- The finite form for `k = 2`: a positive-density subset of `{0,…,N-1}` has two distinct
elements, which form a 2-term AP. -/
theorem finiteSzemeredi_two (δ : ℝ) (hδ : 0 < δ) : FiniteSzemeredi 2 δ := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 / δ)
  refine ⟨N₀, ?_⟩
  intro N hN A hAsub hAδ
  have hδN₀ : (2 : ℝ) ≤ δ * (N₀ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hN₀ (le_of_lt hδ)
    calc
      (2 : ℝ) = (2 / δ) * δ := by field_simp [ne_of_gt hδ]
      _ ≤ (N₀ : ℝ) * δ := hm
      _ = δ * (N₀ : ℝ) := by ring
  have hδN : (2 : ℝ) ≤ δ * (N : ℝ) := by
    have hmono : δ * (N₀ : ℝ) ≤ δ * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (le_of_lt hδ)
    nlinarith
  have hcard2 : (2 : ℝ) ≤ (A.card : ℝ) := le_trans hδN hAδ
  have hcard2' : 2 ≤ A.card := by exact_mod_cast hcard2
  have hpair : ∃ a ∈ A, ∃ b ∈ A, a ≠ b := (Finset.one_lt_card).mp (by omega)
  rcases hpair with ⟨a, ha, b, hb, hab⟩
  rcases lt_or_gt_of_ne hab with hablt | hblt
  · -- a < b: AP a, b
    refine ⟨a, b - a, ?_, ?_⟩
    · omega
    · intro j hj
      interval_cases j
      · simpa using ha
      · -- j = 1: a + (b-a) = b ∈ A
        have hab' : a + (b - a) = b := by omega
        simpa [hab'] using hb
  · -- b < a: AP b, a
    refine ⟨b, a - b, ?_, ?_⟩
    · omega
    · intro j hj
      interval_cases j
      · simpa using hb
      · -- j = 1: b + (a-b) = a ∈ A
        have hba' : b + (a - b) = a := by omega
        simpa [hba'] using ha


/-- In density form, the theorem is fully proved for every length `k ≤ 3`
(the case `k = 3` is Roth's theorem; `k = 0, 1, 2` are elementary). -/
theorem density_hasAP_of_le_three (A : Set ℕ) (hd : PositiveUpperDensity A) :
    ∀ k : ℕ, k ≤ 3 → HasAP A k := by
  intro k hk
  interval_cases k
  · exact ap_of_finite (k := 0) (fun δ hδ => finiteSzemeredi_zero δ hδ) hd
  · exact ap_of_finite (k := 1) (fun δ hδ => finiteSzemeredi_one δ hδ) hd
  · exact ap_of_finite (k := 2) (fun δ hδ => finiteSzemeredi_two δ hδ) hd
  · exact roth_upperDensity A hd

end Szemeredi
