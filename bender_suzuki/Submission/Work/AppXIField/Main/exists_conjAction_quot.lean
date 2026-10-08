import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.Main

theorem exists_conjAction_quot {G : Type} [Group G] (A R : Subgroup G) (K : Subgroup ↥R)
    [K.Normal] (c : ↥A →* MulAut ↥R) (hcK : ∀ (a : ↥A) (x : ↥R), x ∈ K → c a x ∈ K) :
    ∃ act : ↥A →* MulAut (↥R ⧸ K),
      ∀ (a : ↥A) (x : ↥R), act a (QuotientGroup.mk' K x) = QuotientGroup.mk' K (c a x) := by
  -- For each `a`, the automorphism `c a` of `↥R` descends to `↥R ⧸ K` because it
  -- preserves `K`.
  let φ : ↥A → (↥R ⧸ K) →* (↥R ⧸ K) :=
    fun a => QuotientGroup.map K K (c a).toMonoidHom (fun x hx => hcK a x hx)
  have hφ : ∀ (a : ↥A) (x : ↥R), φ a (QuotientGroup.mk' K x) = QuotientGroup.mk' K (c a x) := by
    intro a x
    exact QuotientGroup.map_mk' K K (c a).toMonoidHom (fun x hx => hcK a x hx) x
  -- `K` is preserved by the inverse too, since `hcK` holds for every element of `↥A`,
  -- in particular for `a⁻¹`.
  have hcKinv : ∀ (a : ↥A) (x : ↥R), x ∈ K → ((c a)⁻¹) x ∈ K := by
    intro a x hx
    have hmul : c a * c a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hinv : (c a)⁻¹ = c a⁻¹ := inv_eq_of_mul_eq_one_right hmul
    rw [hinv]
    exact hcK a⁻¹ x hx
  -- The inverse descends as well, and provides the two-sided inverse of `φ a`.
  let ψ : ↥A → (↥R ⧸ K) →* (↥R ⧸ K) :=
    fun a => QuotientGroup.map K K ((c a)⁻¹).toMonoidHom (fun x hx => hcKinv a x hx)
  have hψ : ∀ (a : ↥A) (x : ↥R),
      ψ a (QuotientGroup.mk' K x) = QuotientGroup.mk' K (((c a)⁻¹) x) := by
    intro a x
    exact QuotientGroup.map_mk' K K ((c a)⁻¹).toMonoidHom (fun x hx => hcKinv a x hx) x
  have hleft : ∀ (a : ↥A) (y : ↥R ⧸ K), ψ a (φ a y) = y := by
    intro a y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    rw [hφ a x, hψ a (c a x)]
    congr 1
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hright : ∀ (a : ↥A) (y : ↥R ⧸ K), φ a (ψ a y) = y := by
    intro a y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    rw [hψ a x, hφ a (((c a)⁻¹) x)]
    congr 1
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hbij : ∀ a : ↥A, Function.Bijective (φ a) := fun a =>
    ⟨fun y z h => by rw [← hleft a y, h, hleft a z],
     fun y => ⟨ψ a y, hright a y⟩⟩
  -- Package `φ a` as an automorphism of `↥R ⧸ K`.
  let e : ↥A → MulAut (↥R ⧸ K) := fun a => MulEquiv.ofBijective (φ a) (hbij a)
  have he : ∀ (a : ↥A) (y : ↥R ⧸ K), e a y = φ a y := fun a y =>
    MulEquiv.ofBijective_apply (φ a) (hbij a) y
  refine ⟨{ toFun := e, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    rw [he, hφ]
    simp
  · intro a b
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    simp only [he, hφ, MulAut.mul_apply]
    congr 1
    rw [map_mul c a b, MulAut.mul_apply]
  · intro a x
    change e a (QuotientGroup.mk' K x) = QuotientGroup.mk' K (c a x)
    rw [he, hφ]

end Work.AppXIField.Main
