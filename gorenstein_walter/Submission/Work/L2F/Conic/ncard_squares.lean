import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Conic

/-- A finite field of odd characteristic has `(q+1)/2` squares (including `0`).
Proof: `x ↦ x²` on `Fˣ` has kernel `{±1}` of order `2`, so its image has `(q-1)/2` elements; adding
`0` gives `(q+1)/2`. -/
theorem ncard_squares (F : Type*) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    {x : F | IsSquare x}.ncard = (Nat.card F + 1) / 2 := by
  -- The squaring map on the units, as a monoid homomorphism.
  let φ : Fˣ →* Fˣ := MonoidHom.id Fˣ * MonoidHom.id Fˣ
  have hφ : ∀ u : Fˣ, φ u = u * u := fun u => by simp [φ, MonoidHom.mul_apply]
  -- Its range is exactly the set of units whose underlying field element is a square.
  have hmem : ∀ u : Fˣ, u ∈ φ.range ↔ IsSquare (u : F) := by
    intro u
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨(v : F), by rw [← hv, hφ v]; simp⟩
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hy
        exact Units.ne_zero u hy
      refine ⟨Units.mk0 y hy0, ?_⟩
      apply Units.ext
      rw [hφ]
      simp only [Units.val_mul, Units.val_mk0]
      exact hy.symm
  -- Its kernel is `{1, -1}`, of order `2` since `2 ≠ 0`.
  have hker : Nat.card φ.ker = 2 := by
    have hset : (φ.ker : Set Fˣ) = {(1 : Fˣ), -1} := by
      ext u
      change u ∈ φ.ker ↔ _
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, MonoidHom.mem_ker, hφ u]
      constructor
      · intro h
        have h' : (u : F) * (u : F) = 1 := by
          have := congrArg (Units.val) h
          simpa using this
        rcases mul_self_eq_one_iff.mp h' with h1 | h1
        · exact Or.inl (Units.ext (by simpa using h1))
        · exact Or.inr (Units.ext (by simpa using h1))
      · rintro (rfl | rfl)
        · simp
        · show (-1 : Fˣ) * (-1 : Fˣ) = 1
          simp
    have hne : (1 : Fˣ) ≠ -1 := by
      intro h
      have h1 : (1 : F) = -1 := by simpa using congrArg (Units.val) h
      have h3 : (2 : F) = 0 := by
        rw [show (2 : F) = 1 + 1 by norm_num]
        exact neg_eq_iff_add_eq_zero.mp h1.symm
      exact h2 h3
    calc Nat.card φ.ker = (φ.ker : Set Fˣ).ncard := Nat.card_coe_set_eq _
      _ = 2 := by rw [hset]; exact Set.ncard_pair hne
  -- Hence `2 * #{squares in Fˣ} = #Fˣ = #F - 1`.
  have hcard : (φ.range : Set Fˣ).ncard * 2 = Nat.card F - 1 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hker, Nat.card_units, mul_comm] at h
    have h' : Nat.card ↥(φ.range : Set Fˣ) * 2 = Nat.card F - 1 := h
    simpa using h'
  -- The set of all squares is `{0}` together with the nonzero squares.
  have hS : {x : F | IsSquare x} = insert 0 {x : F | IsSquare x ∧ x ≠ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr ⟨hx, hx0⟩
    · rintro (rfl | ⟨hx, _⟩)
      · exact ⟨0, by simp⟩
      · exact hx
  have hS' : {x : F | IsSquare x ∧ x ≠ 0} = Units.val '' (φ.range : Set Fˣ) := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨Units.mk0 x hx0, ?_, ?_⟩
      · exact (hmem _).mpr (by rw [Units.val_mk0]; exact hx)
      · rw [Units.val_mk0]
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(hmem u).mp hu, Units.ne_zero u⟩
  rw [hS, Set.ncard_insert_of_notMem (by simp), hS',
    Set.ncard_image_of_injective _ Units.val_injective]
  have hkey : Nat.card F + 1 = 2 * ((φ.range : Set Fˣ).ncard + 1) := by
    have := Nat.card_pos (α := F)
    omega
  rw [hkey, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]

end Work.L2F.Conic
