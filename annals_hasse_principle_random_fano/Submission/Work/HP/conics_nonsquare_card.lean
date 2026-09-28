import Mathlib

namespace Work.HP

/-- Auxiliary: for a unit `u` of `ZMod p`, being a square in `ZMod p` is the same as being a
square of the multiplicative group of units. -/
private lemma unit_isSquare_iff {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    IsSquare (u : ZMod p) ↔ IsSquare u := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact Units.ne_zero u hr
    exact ⟨Units.mk0 r hr0, by ext; simpa using hr⟩
  · rintro ⟨v, hv⟩
    exact ⟨(v : ZMod p), by simpa using congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) hv⟩

/-- Auxiliary: the set of units of `ZMod p` that are squares has `(p - 1) / 2` elements. -/
private lemma card_square_units {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    {u : (ZMod p)ˣ | IsSquare (u : ZMod p)}.ncard = (p - 1) / 2 := by
  classical
  -- The kernel of squaring on the units is `{1, -1}`.
  have hne : (1 : (ZMod p)ˣ) ≠ -1 := by
    intro h
    have h' : (1 : ZMod p) = -1 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    have hne' : (-1 : ZMod p) ≠ 1 :=
      Ring.neg_one_ne_one_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; exact hp)
    exact hne' h'.symm
  have hker_set :
      (↑(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).ker : Set (ZMod p)ˣ) = {1, -1} := by
    ext u
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h2 : (u : ZMod p) ^ 2 = 1 := by
        have := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h
        simpa [Units.val_pow_eq_pow_val] using this
      rcases sq_eq_one_iff.mp h2 with h1 | h1
      · left; exact Units.ext h1
      · right; exact Units.ext h1
    · rintro (rfl | rfl)
      · simp
      · simp
  have hker : Nat.card ↥(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).ker = 2 := by
    rw [show Nat.card ↥(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).ker
          = (↑(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).ker : Set (ZMod p)ˣ).ncard
          from Nat.card_coe_set_eq _,
        hker_set, Set.ncard_pair hne]
  have hcardG : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  -- Multiplicativity of the index: `|ker| * |range| = |G|`, and `|ker| = 2` gives `|range|
  -- = (p - 1) / 2`.
  have hrange : Nat.card ↥(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range = (p - 1) / 2 := by
    have hmul := Subgroup.card_mul_index (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).ker
    rw [Subgroup.index_ker (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ)] at hmul
    rw [hker, hcardG] at hmul
    have h2 : (p - 1) / 2 = Nat.card ↥(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
      rw [← hmul, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    exact h2.symm
  have hrange_set : (↑(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range : Set (ZMod p)ˣ)
      = {u : (ZMod p)ˣ | IsSquare (u : ZMod p)} := by
    have h1 : (↑(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range : Set (ZMod p)ˣ)
        = {u : (ZMod p)ˣ | IsSquare u} := by
      ext u
      rw [SetLike.mem_coe, MonoidHom.mem_range]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [← hv]
        show v ^ 2 = v * v
        rw [pow_two]
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        show v ^ 2 = u
        rw [hv, pow_two]
    rw [h1]
    exact Set.ext fun u => (unit_isSquare_iff u).symm
  rw [← hrange,
    show Nat.card ↥(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
        = (↑(powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range : Set (ZMod p)ˣ).ncard
        from Nat.card_coe_set_eq _,
    hrange_set]

/-- In `ZMod p` for an odd prime `p`, the number of non-squares is `(p-1)/2`. -/
theorem conics_nonsquare_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    {x : ZMod p | ¬ IsSquare x}.ncard = (p - 1) / 2 := by
  classical
  -- Transfer from `ZMod p` to its unit group: `0` is a square, so every non-square is a unit.
  have htransfer : {x : ZMod p | ¬ IsSquare x}.ncard
      = {u : (ZMod p)ˣ | ¬ IsSquare (u : ZMod p)}.ncard := by
    have himg : {x : ZMod p | ¬ IsSquare x}
        = (fun u : (ZMod p)ˣ => (u : ZMod p)) ''
            {u : (ZMod p)ˣ | ¬ IsSquare (u : ZMod p)} := by
      ext x
      constructor
      · intro hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hx ⟨0, by simp⟩
        exact ⟨Units.mk0 x hx0, by simpa using hx, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact hu
    rw [himg]
    exact Set.ncard_image_of_injective (f := fun u : (ZMod p)ˣ => (u : ZMod p)) _
      (fun a b h => Units.ext h)
  rw [htransfer]
  -- Nonsquares among the units are the complement of the squares among the units.
  have hcompl : {u : (ZMod p)ˣ | ¬ IsSquare (u : ZMod p)}
      = {u : (ZMod p)ˣ | IsSquare (u : ZMod p)}ᶜ := by
    ext u; simp
  rw [hcompl, Set.ncard_compl, Nat.card_eq_fintype_card, ZMod.card_units,
    card_square_units (p := p) hp]
  -- Now `(p - 1) - (p - 1) / 2 = (p - 1) / 2` because `p` is odd.
  have hk : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two (Fact.out) hp
    rw [hk]
    have h3 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [h3, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  omega

end Work.HP
