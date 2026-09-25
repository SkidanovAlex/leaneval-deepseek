import Mathlib

namespace NK.NUV2.TamePrimeLevel

/-- If a commutative group `G` is the internal direct product of its subgroups `A` and `B`
(`A ⊓ B = ⊥`, `A ⊔ B = ⊤`), then the quotient of `G` by the subgroup of `ℓ`-th powers is the
product of the corresponding quotients of `A` and `B`.

The proof builds the internal direct product isomorphism `A × B ≃* G`, transports the `ℓ`-th power
subgroup through it, and uses `QuotientGroup.prodMulEquiv` to split the quotient of a product. -/
theorem natCard_quot_range_powMonoidHom_sup_inf {G : Type*} [CommGroup G]
    (A B : Subgroup G) (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤) (ℓ : ℕ) :
    Nat.card (G ⧸ (powMonoidHom ℓ : G →* G).range) =
      Nat.card (↥A ⧸ (powMonoidHom ℓ : ↥A →* ↥A).range) *
        Nat.card (↥B ⧸ (powMonoidHom ℓ : ↥B →* ↥B).range) := by
  set PA : Subgroup ↥A := (powMonoidHom ℓ : ↥A →* ↥A).range with hPA
  set PB : Subgroup ↥B := (powMonoidHom ℓ : ↥B →* ↥B).range with hPB
  set PG : Subgroup G := (powMonoidHom ℓ : G →* G).range with hPG
  -- the internal direct product isomorphism `A × B ≃* G`, given by `(a, b) ↦ a * b`
  let φ : ↥A × ↥B →* G :=
    (A.subtype.comp (MonoidHom.fst ↥A ↥B)) * (B.subtype.comp (MonoidHom.snd ↥A ↥B))
  have hφ : ∀ (a : ↥A) (b : ↥B), φ (a, b) = (a : G) * (b : G) := fun a b => rfl
  have hinj : Function.Injective φ := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [hφ] at h
    -- rearrange `a1 * b1 = a2 * b2` into `a1 * a2⁻¹ = b2 * b1⁻¹`
    have hEq : (a1 : G) * (a2 : G)⁻¹ = (b2 : G) * (b1 : G)⁻¹ := by
      rw [mul_inv_eq_mul_inv_iff_mul_eq_mul, h, mul_comm]
    have hmemA : ((a1 : G) * (a2 : G)⁻¹) ∈ A := A.mul_mem a1.2 (A.inv_mem a2.2)
    have hmemB : ((a1 : G) * (a2 : G)⁻¹) ∈ B := by
      rw [hEq]
      exact B.mul_mem b2.2 (B.inv_mem b1.2)
    have hmem : ((a1 : G) * (a2 : G)⁻¹) ∈ A ⊓ B := ⟨hmemA, hmemB⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hae : (a1 : G) = (a2 : G) := mul_inv_eq_one.mp hmem
    have ha : a1 = a2 := Subtype.ext hae
    have hb : b1 = b2 := by
      apply Subtype.ext
      have hh : (a1 : G) * (b1 : G) = (a1 : G) * (b2 : G) := by
        rw [← hae] at h
        exact h
      exact mul_left_cancel hh
    rw [ha, hb]
  have hsurj : Function.Surjective φ := by
    intro g
    have hg : g ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top g
    rw [Subgroup.mem_sup] at hg
    obtain ⟨a, ha, b, hb, hab⟩ := hg
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by rw [hφ]; exact hab⟩
  let e : ↥A × ↥B ≃* G := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  -- the `ℓ`-th power subgroup of `A × B` is `PA.prod PB`
  have hA : (powMonoidHom ℓ : ↥A × ↥B →* ↥A × ↥B).range = PA.prod PB := by
    rw [hPA, hPB]
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_prod, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  -- the power map commutes with `e`
  have hpow : e.toMonoidHom.comp (powMonoidHom ℓ : ↥A × ↥B →* ↥A × ↥B) =
      (powMonoidHom ℓ : G →* G).comp e.toMonoidHom := by
    ext x
    exact map_pow e.toMonoidHom x ℓ
  -- `e` carries `PA.prod PB` onto `PG`
  have hmap : Subgroup.map e.toMonoidHom (PA.prod PB) = PG := by
    rw [← hA, hPG]
    rw [MonoidHom.map_range, hpow, ← MonoidHom.map_range]
    rw [MonoidHom.range_eq_top.mpr e.surjective, MonoidHom.range_eq_map]
  have iso1 : (↥A × ↥B) ⧸ (PA.prod PB) ≃* G ⧸ PG :=
    QuotientGroup.congr (PA.prod PB) PG e hmap
  have iso2 : (↥A × ↥B) ⧸ (PA.prod PB) ≃* (↥A ⧸ PA) × (↥B ⧸ PB) :=
    QuotientGroup.prodMulEquiv PA PB
  calc Nat.card (G ⧸ PG)
      = Nat.card ((↥A ⧸ PA) × (↥B ⧸ PB)) := Nat.card_congr (iso1.symm.trans iso2).toEquiv
    _ = Nat.card (↥A ⧸ PA) * Nat.card (↥B ⧸ PB) := Nat.card_prod _ _

end NK.NUV2.TamePrimeLevel
