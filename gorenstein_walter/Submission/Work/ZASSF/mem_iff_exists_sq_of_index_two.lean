import Mathlib

namespace Work.ZASSF

/-- In the units of a finite field, the subgroup of the squares (the range of the squaring
map) has index `gcd (Nat.card Eˣ) 2`, and index `2` exactly when `Nat.card Eˣ` is even.
Since any index-two subgroup `K` contains every square, `K` coincides with the range. -/
theorem mem_iff_exists_sq_of_index_two {E : Type*} [Field E] [Finite E] {K : Subgroup Eˣ} (hK : K.index = 2) : ∀ e : Eˣ, e ∈ K ↔ ∃ f : Eˣ, f ^ 2 = e := by
  -- Cardinality bookkeeping: `|Eˣ| = |K| * 2`, hence `|Eˣ|` is even and `gcd |Eˣ| 2 = 2`.
  have hcardG : Nat.card ↥K * 2 = Nat.card Eˣ := by
    rw [← Subgroup.card_mul_index K, hK]
  have h2dvd : 2 ∣ Nat.card Eˣ := ⟨Nat.card ↥K, by omega⟩
  have hgcd : (Nat.card Eˣ).gcd 2 = 2 := Nat.gcd_eq_right h2dvd
  -- The range of the squaring map also has index `2` (using cyclicity of the units of a
  -- finite field), so it has the same cardinality as `K`.
  have hrangeidx : ((powMonoidHom 2 : Eˣ →* Eˣ).range).index = 2 := by
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have hcardR : Nat.card ↥((powMonoidHom 2 : Eˣ →* Eˣ).range) = Nat.card ↥K := by
    have h1 : Nat.card ↥((powMonoidHom 2 : Eˣ →* Eˣ).range) * 2 = Nat.card Eˣ := by
      rw [← Subgroup.card_mul_index (powMonoidHom 2 : Eˣ →* Eˣ).range, hrangeidx]
    omega
  -- Every square lies in `K`, i.e. the range of the squaring map is contained in `K`.
  have hle : (powMonoidHom 2 : Eˣ →* Eˣ).range ≤ K := by
    rintro x ⟨y, rfl⟩
    rw [powMonoidHom_apply]
    exact Subgroup.sq_mem_of_index_two hK y
  -- Equal cardinality then forces equality.
  have hEq : (powMonoidHom 2 : Eˣ →* Eˣ).range = K :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardR.symm)
  intro e
  rw [← hEq]
  constructor
  · intro he
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp he
    exact ⟨f, by rw [powMonoidHom_apply] at hf; exact hf⟩
  · rintro ⟨f, hf⟩
    exact MonoidHom.mem_range.mpr ⟨f, by rw [powMonoidHom_apply]; exact hf⟩

end Work.ZASSF
