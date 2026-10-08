import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- The center of a subgroup is natural under homomorphisms that are injective on it: if
`K ⊓ f.ker = ⊥` then `Z(K).map f = Z(K.map f)`.

Restricted to `K`, such an `f` is an isomorphism onto `K.map f`, and the center transports across
a group isomorphism (`Subgroup.map_center_eq`). -/
theorem centerIn_map_of_ker_inf_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (hker : K ⊓ f.ker = ⊥) :
    Work.PGroup.centerIn (K.map f) = (Work.PGroup.centerIn K).map f := by
  -- `f` restricted to `K` is a bijection onto `K.map f`.
  let φ : K →* K.map f :=
    { toFun := fun x => ⟨f x, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : G) (y : G)) }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hxy' : f (x : G) = f (y : G) := congrArg Subtype.val hxy
    apply Subtype.ext
    have hmem : (x : G)⁻¹ * (y : G) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', inv_mul_cancel]
    have hK : (x : G)⁻¹ * (y : G) ∈ K := K.mul_mem (K.inv_mem x.2) y.2
    have hbot : (x : G)⁻¹ * (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hker]; exact ⟨hK, hmem⟩
    have hone : (x : G)⁻¹ * (y : G) = 1 := by simpa using hbot
    exact inv_mul_eq_one.mp hone
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨w, hw⟩
    rw [Subgroup.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : K ≃* K.map f := MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hmap : Subgroup.map e.toMonoidHom (Subgroup.center ↥K) = Subgroup.center ↥(K.map f) :=
    Subgroup.map_center_eq e
  have hcomp : (K.map f).subtype.comp e.toMonoidHom = f.comp K.subtype := by
    ext x
    change ((e x : K.map f) : H) = f (x : G)
    rfl
  calc Work.PGroup.centerIn (K.map f)
      = (Subgroup.center ↥(K.map f)).map (K.map f).subtype := rfl
    _ = (Subgroup.map e.toMonoidHom (Subgroup.center ↥K)).map (K.map f).subtype := by rw [hmap]
    _ = (Subgroup.center ↥K).map ((K.map f).subtype.comp e.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (Subgroup.center ↥K).map (f.comp K.subtype) := by rw [hcomp]
    _ = ((Subgroup.center ↥K).map K.subtype).map f := by rw [← Subgroup.map_map]
    _ = (Work.PGroup.centerIn K).map f := rfl

end Work.PGroup
