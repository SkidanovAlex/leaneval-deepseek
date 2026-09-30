import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- A `q₀`-separated set `A` of naturals all lying in `[0, L]` satisfies
`A.card * q₀ ≤ L + q₀`.  Equivalent to the target bound but slightly more
convenient for induction (it has no truncated subtraction). -/
lemma card_mul_le_add (q₀ : ℕ) : ∀ n, ∀ (A : Finset ℕ) (L : ℕ), A.card = n →
    (∀ a ∈ A, a ≤ L) →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → q₀ ≤ (max a b - min a b)) →
    A.card * q₀ ≤ L + q₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A L hcard hA hsep
    rcases Nat.lt_or_ge A.card 2 with hlt | hge
    · -- `A.card ≤ 1`
      have h1 : A.card ≤ 1 := by omega
      calc A.card * q₀ ≤ 1 * q₀ := Nat.mul_le_mul_right q₀ h1
        _ = q₀ := one_mul q₀
        _ ≤ L + q₀ := by omega
    · -- `2 ≤ A.card`: peel off the maximal element
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      let m := A.max' hne
      have hm : m ∈ A := Finset.max'_mem A hne
      have hle : ∀ b ∈ A, b ≤ m := fun b hb => Finset.le_max' A b hb
      let B := A.erase m
      have hBcard : B.card + 1 = A.card := Finset.card_erase_add_one hm
      have hBsub : ∀ b ∈ B, b ∈ A := fun b hb => (Finset.mem_erase.mp hb).2
      have hBne : ∀ b ∈ B, b ≠ m := fun b hb => (Finset.mem_erase.mp hb).1
      have hqm : q₀ ≤ m := by
        have hBpos : 0 < B.card := by omega
        obtain ⟨b, hb⟩ := Finset.card_pos.mp hBpos
        have h := hsep b (hBsub b hb) m hm (hBne b hb)
        have hb2 : b ≤ m := hle b (hBsub b hb)
        rw [max_eq_right hb2, min_eq_left hb2] at h
        omega
      have hBbound : ∀ b ∈ B, b ≤ m - q₀ := by
        intro b hb
        have h := hsep b (hBsub b hb) m hm (hBne b hb)
        have hb2 : b ≤ m := hle b (hBsub b hb)
        rw [max_eq_right hb2, min_eq_left hb2] at h
        omega
      have hBsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → q₀ ≤ (max a b - min a b) :=
        fun a ha b hb hab => hsep a (hBsub a ha) b (hBsub b hb) hab
      have hlt2 : B.card < n := by rw [← hcard]; omega
      have ihB : B.card * q₀ ≤ (m - q₀) + q₀ :=
        ih B.card hlt2 B (m - q₀) rfl hBbound hBsep
      have hmL : m ≤ L := hA m hm
      calc A.card * q₀ = (B.card + 1) * q₀ := by rw [← hBcard]
        _ = B.card * q₀ + q₀ := by ring
        _ ≤ ((m - q₀) + q₀) + q₀ := add_le_add_left ihB q₀
        _ = m + q₀ := by rw [Nat.sub_add_cancel hqm]
        _ ≤ L + q₀ := add_le_add_left hmL q₀

theorem separated_card_bound (A : Finset ℕ) (q₀ L : ℕ) (hq₀ : 1 ≤ q₀)
    (hA : ∀ a ∈ A, a ≤ L)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → q₀ ≤ (max a b - min a b)) :
    (A.card - 1) * q₀ ≤ L := by
  have h := card_mul_le_add q₀ A.card A L rfl hA hsep
  rcases Nat.eq_zero_or_pos A.card with hc | hc
  · simp [hc]
  · have h1 : A.card - 1 + 1 = A.card := Nat.sub_add_cancel hc
    have h3 : (A.card - 1) * q₀ + q₀ ≤ L + q₀ := by
      calc (A.card - 1) * q₀ + q₀ = A.card * q₀ := by
              conv_rhs => rw [← h1]
              rw [add_mul, one_mul]
        _ ≤ L + q₀ := h
    exact Nat.add_le_add_iff_right.mp h3

end Work.BMF.SD
