import Mathlib

namespace Work.HP

/-- The number of integers `x` with `-(B : ℤ) ≤ x ≤ B` that are divisible by `g`
equals `2 * (B / g) + 1` (for `g ≥ 1`): the multiples in the interval are precisely
`-g*(B/g), …, g*(B/g)`. -/
lemma card_multiples_Icc (B g : ℕ) (hg : 1 ≤ g) :
    ((Finset.Icc (-(B : ℤ)) (B : ℤ)).filter (fun x => (g : ℤ) ∣ x)).card = 2 * (B / g) + 1 := by
  have hgpos : (0 : ℤ) < (g : ℤ) := by omega
  have hgnz : (g : ℤ) ≠ 0 := ne_of_gt hgpos
  have hle : (g : ℤ) * (((B / g : ℕ) : ℤ)) ≤ (B : ℤ) := by
    have := Nat.mul_div_le B g
    exact_mod_cast this
  have hlt : (B : ℤ) < (g : ℤ) * (((B / g : ℕ) : ℤ) + 1) := by
    have h1 : B / g < B / g + 1 := Nat.lt_succ_self _
    have h2 : B < (B / g + 1) * g := (Nat.div_lt_iff_lt_mul (by omega : 0 < g)).mp h1
    have h3 : (B : ℤ) < (((B / g + 1) * g : ℕ) : ℤ) := by exact_mod_cast h2
    rw [show (((B / g + 1) * g : ℕ) : ℤ) = (g : ℤ) * (((B / g : ℕ) : ℤ) + 1) by
      push_cast; ring] at h3
    exact h3
  have key : ∀ z : ℤ, z * (g : ℤ) ≤ (B : ℤ) → z ≤ ((B / g : ℕ) : ℤ) := by
    intro z _
    have h : z * (g : ℤ) < (((B / g : ℕ) : ℤ) + 1) * (g : ℤ) := by
      have hl := hlt
      rw [mul_comm (g : ℤ) (((B / g : ℕ) : ℤ) + 1)] at hl
      linarith
    have := (mul_lt_mul_iff_of_pos_right hgpos).mp h
    exact Int.lt_add_one_iff.mp this
  have hset : (Finset.Icc (-(B : ℤ)) (B : ℤ)).filter (fun x => (g : ℤ) ∣ x)
      = (Finset.Icc (-((B / g : ℕ) : ℤ)) (((B / g : ℕ) : ℤ))).image
          (fun k => k * (g : ℤ)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hdvd⟩
      obtain ⟨k, hk⟩ := dvd_iff_exists_eq_mul_left.mp hdvd
      refine ⟨k, ⟨?_, ?_⟩, hk.symm⟩
      · have hneg : (-k) * (g : ℤ) ≤ (B : ℤ) := by
          have hh : (-k) * (g : ℤ) = -(k * (g : ℤ)) := by ring
          rw [hh, ← hk]; linarith
        have := key (-k) hneg
        linarith
      · exact key k (by rw [← hk]; exact hhi)
    · rintro ⟨k, ⟨hklo, hkhi⟩, hk⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hqg : ((B / g : ℕ) : ℤ) * (g : ℤ) ≤ (B : ℤ) := by rw [mul_comm]; exact hle
        have hm : (-((B / g : ℕ) : ℤ)) * (g : ℤ) ≤ k * (g : ℤ) :=
          mul_le_mul_of_nonneg_right hklo (le_of_lt hgpos)
        have hm2 : -(((B / g : ℕ) : ℤ) * (g : ℤ)) ≤ k * (g : ℤ) := by
          rwa [neg_mul] at hm
        rw [← hk]; linarith
      · have hqg : ((B / g : ℕ) : ℤ) * (g : ℤ) ≤ (B : ℤ) := by rw [mul_comm]; exact hle
        have hm : k * (g : ℤ) ≤ ((B / g : ℕ) : ℤ) * (g : ℤ) :=
          mul_le_mul_of_nonneg_right hkhi (le_of_lt hgpos)
        rw [← hk]; linarith
      · rw [← hk]; exact dvd_mul_left (g : ℤ) k
  rw [hset, Finset.card_image_of_injective _ (mul_left_injective₀ hgnz), Int.card_Icc]
  have : ((B / g : ℕ) : ℤ) + 1 - (-((B / g : ℕ) : ℤ)) = ((2 * (B / g) + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

theorem div_count {ι : Type*} [Fintype ι] [DecidableEq ι] (B g : ℕ) (hg : 1 ≤ g) :
    (((Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => ∀ i, (g : ℤ) ∣ a i)).card)
      ≤ (2 * (B / g) + 1) ^ (Fintype.card ι) := by
  classical
  have hset : (Fintype.piFinset (fun _ : ι => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
        (fun a => ∀ i, (g : ℤ) ∣ a i)
      = Fintype.piFinset (fun _ : ι => (Finset.Icc (-(B : ℤ)) (B : ℤ)).filter
        (fun x => (g : ℤ) ∣ x)) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    card_multiples_Icc B g hg]

end Work.HP
