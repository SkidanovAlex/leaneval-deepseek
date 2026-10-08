import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- The sign homomorphism attached to a subgroup of index two: it is `1` on the subgroup
and `-1` outside it.  (Multiplicativity on two elements outside `H` uses that the quotient
`G ⧸ H` has order two, so that a product of two non-elements lies in `H`.) -/
noncomputable def signHom {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2) : G →* ℂˣ := by
  classical
  exact
    { toFun := fun x => if x ∈ H then 1 else -1
      map_one' := by simp
      map_mul' := fun a b => by
        rw [Subgroup.mul_mem_iff_of_index_two hH]
        by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp_all }

@[simp]
lemma signHom_apply_of_mem {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2) {x : G}
    (hx : x ∈ H) : signHom H hH x = 1 := by
  classical
  simp [signHom, hx]

@[simp]
lemma signHom_apply_of_notMem {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2) {x : G}
    (hx : x ∉ H) : signHom H hH x = -1 := by
  classical
  simp [signHom, hx]

theorem signHom_index_two {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2) :
    ∃ φ : G →* ℂˣ, (∀ x ∈ H, φ x = 1) ∧ (∀ x ∉ H, φ x = -1) :=
  ⟨signHom H hH, fun _ hx => signHom_apply_of_mem hH hx,
    fun _ hx => signHom_apply_of_notMem hH hx⟩

end Work.BrauerSuzuki.Quaternion
