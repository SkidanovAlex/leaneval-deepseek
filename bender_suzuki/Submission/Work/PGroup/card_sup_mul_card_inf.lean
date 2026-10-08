import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- For two elementwise commuting subgroups `H K` of a group `G`, the join and the
intersection satisfy `|H ⊔ K| * |H ⊓ K| = |H| * |K|`.

The product map `↥H × ↥K → ↥(H ⊔ K)`, `(h, k) ↦ h * k`, is a surjective homomorphism
whose kernel is `{(h, h⁻¹) | h ∈ H ⊓ K} ≅ H ⊓ K`, so the first isomorphism theorem gives
the identity. -/
theorem card_sup_mul_card_inf {G : Type*} [Group G] (H K : Subgroup G) [Finite ↥H] [Finite ↥K]
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  -- Since `H` and `K` commute, the product set `H * K` is a subgroup, containing `H` and `K`,
  -- hence it contains `H ⊔ K`.  Thus every element of `H ⊔ K` is a product `h * k`.
  have hprod : ∀ x ∈ (H ⊔ K : Subgroup G), ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
    have hsub : (H ⊔ K : Subgroup G) ≤
        { carrier := {x : G | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
          mul_mem' := by
            rintro a b ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
            refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
            simp only [mul_assoc]
            rw [← mul_assoc h2 k1 k2, hcomm h2 hh2 k1 hk1]
            group
          one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
          inv_mem' := by
            rintro a ⟨h, hh, k, hk, rfl⟩
            refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
            rw [hcomm h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)]
            group } := by
      apply sup_le
      · intro h hh; exact ⟨h, hh, 1, K.one_mem, by simp⟩
      · intro k hk; exact ⟨1, H.one_mem, k, hk, by simp⟩
    intro x hx; exact hsub hx
  -- The product map.
  let φ : ↥H × ↥K →* ↥(H ⊔ K) :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), Subgroup.mul_mem_sup x.1.2 x.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        rintro ⟨a1, a2⟩ ⟨b1, b2⟩
        ext
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        simp only [mul_assoc]
        rw [← mul_assoc (b1 : G) (a2 : G) (b2 : G), hcomm b1 b1.2 a2 a2.2]
        group }
  -- The value of `φ` at a kernel element is `(h * k) = 1`, hence `h = k⁻¹`.
  have hxval : ∀ x : ↥φ.ker, ((x.1.1 : ↥H) : G) * ((x.1.2 : ↥K) : G) = 1 := fun x => by
    have h := congrArg (fun y : ↥(H ⊔ K) => (y : G)) x.2
    simpa [φ] using h
  -- The kernel of `φ` is isomorphic to `H ⊓ K` via `(h, k) ↦ h`.
  have hker : Nat.card ↥φ.ker = Nat.card ↥(H ⊓ K) := by
    refine Nat.card_congr ?_
    refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro x
      exact ⟨(x.1.1 : G), Subgroup.mem_inf.mpr ⟨x.1.1.2, by
        have h1 : (x.1.1 : G) = ((x.1.2 : G))⁻¹ := mul_eq_one_iff_eq_inv.mp (hxval x)
        rw [h1]; exact K.inv_mem x.1.2.2⟩⟩
    · intro y
      exact ⟨((⟨y.1, y.2.1⟩ : ↥H), (⟨y.1⁻¹, K.inv_mem y.2.2⟩ : ↥K)), by
        apply Subtype.ext
        simp [φ]⟩
    · intro x
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext; rfl
      · apply Subtype.ext
        exact (eq_inv_of_mul_eq_one_right (hxval x)).symm
    · intro y
      apply Subtype.ext
      rfl
  -- `φ` is surjective.
  have hrange : φ.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    rintro ⟨x, hx⟩
    obtain ⟨h, hh, k, hk, hkx⟩ := hprod x hx
    refine ⟨(⟨h, hh⟩, ⟨k, hk⟩), ?_⟩
    apply Subtype.ext
    simpa [φ] using hkx
  have hrange_card : Nat.card ↥φ.range = Nat.card ↥(H ⊔ K) := by
    rw [hrange]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have h1 : Nat.card ↥φ.range * Nat.card ↥φ.ker = Nat.card (↥H × ↥K) := by
    rw [← Subgroup.index_ker φ, ← Subgroup.card_mul_index φ.ker]
    ring
  calc Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K)
      = Nat.card ↥φ.range * Nat.card ↥φ.ker := by rw [← hrange_card, ← hker]
    _ = Nat.card (↥H × ↥K) := h1
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

end Work.PGroup
