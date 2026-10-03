import Mathlib

namespace Work.OROneRel

variable {G H : Type*} [Group G] [Group H]

/-- The isomorphism between a subgroup `A ≤ G` and its image `A.map e` under an isomorphism
`e : G ≃* H`, sending `a` to `e a`. -/
noncomputable def subgroupMapEquiv (e : G ≃* H) (A : Subgroup G) :
    A ≃* A.map e.toMonoidHom :=
  { (e : G ≃ H).image A with map_mul' := fun a b => Subtype.ext (e.map_mul' a b) }

@[simp]
theorem subgroupMapEquiv_apply_coe (e : G ≃* H) (A : Subgroup G) (a : A) :
    ((subgroupMapEquiv e A a : A.map e.toMonoidHom) : H) = e (a : G) := rfl

@[simp]
theorem subgroupMapEquiv_symm_apply_coe (e : G ≃* H) (A : Subgroup G)
    (b : A.map e.toMonoidHom) :
    (((subgroupMapEquiv e A).symm b : A) : G) = e.symm (b : H) := rfl

theorem hnnExtension_iso_of_baseMulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (A B : Subgroup G) (φ : A ≃* B) :
    ∃ (A' B' : Subgroup H) (φ' : A' ≃* B')
      (E : HNNExtension G A B φ ≃* HNNExtension H A' B' φ'),
      A' = A.map e.toMonoidHom ∧ B' = B.map e.toMonoidHom ∧
      (∀ g : G, E (HNNExtension.of g) = HNNExtension.of (e g)) ∧
      E HNNExtension.t = HNNExtension.t := by
  let φ' : (A.map e.toMonoidHom) ≃* (B.map e.toMonoidHom) :=
    (subgroupMapEquiv e A).symm.trans (φ.trans (subgroupMapEquiv e B))
  have hφ'a : ∀ a : A, φ' (subgroupMapEquiv e A a) = subgroupMapEquiv e B (φ a) := by
    intro a
    simp only [φ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  let fwd : G →* HNNExtension H (A.map e.toMonoidHom) (B.map e.toMonoidHom) φ' :=
    HNNExtension.of.comp e.toMonoidHom
  have hc : ∀ a : A, HNNExtension.t * fwd ↑a = fwd ↑(φ a) * HNNExtension.t := by
    intro a
    have h := HNNExtension.t_mul_of (φ := φ') (subgroupMapEquiv e A a)
    rw [hφ'a] at h
    rw [subgroupMapEquiv_apply_coe] at h
    rw [subgroupMapEquiv_apply_coe] at h
    have e1 : fwd (a : G) = HNNExtension.of (e (a : G)) := by
      simp only [fwd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have e2 : fwd ((φ a : B) : G) = HNNExtension.of (e ((φ a : B) : G)) := by
      simp only [fwd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [e1, e2]
    exact h
  let E : HNNExtension G A B φ →*
      HNNExtension H (A.map e.toMonoidHom) (B.map e.toMonoidHom) φ' :=
    HNNExtension.lift fwd HNNExtension.t hc
  let fwdInv : H →* HNNExtension G A B φ := HNNExtension.of.comp e.symm.toMonoidHom
  have hcInv : ∀ b : A.map e.toMonoidHom,
      HNNExtension.t * fwdInv ↑b = fwdInv ↑(φ' b) * HNNExtension.t := by
    intro b
    obtain ⟨a, ha, hb⟩ := Subgroup.mem_map.1 b.2
    let a' : A := ⟨a, ha⟩
    have hb' : (b : H) = e (a' : G) := hb.symm
    have hbφ : (φ' b : H) = e ((φ a' : B) : G) := by
      have h1 : b = subgroupMapEquiv e A a' := by
        ext
        rw [subgroupMapEquiv_apply_coe]
        exact hb.symm
      rw [h1, hφ'a, subgroupMapEquiv_apply_coe]
    rw [hb', hbφ]
    have e1 : fwdInv (e (a' : G)) = HNNExtension.of (a' : G) := by
      simp only [fwdInv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]
    have e2 : fwdInv (e ((φ a' : B) : G)) = HNNExtension.of ((φ a' : B) : G) := by
      simp only [fwdInv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]
    rw [e1, e2]
    exact HNNExtension.t_mul_of (φ := φ) a'
  let Einv : HNNExtension H (A.map e.toMonoidHom) (B.map e.toMonoidHom) φ' →*
      HNNExtension G A B φ := HNNExtension.lift fwdInv HNNExtension.t hcInv
  have hleft : Einv.comp E = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · ext g
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, E, Einv, HNNExtension.lift_of, fwd,
        fwdInv, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, E, Einv, HNNExtension.lift_t]
  have hright : E.comp Einv = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · ext h
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, E, Einv, HNNExtension.lift_of, fwd,
        fwdInv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, E, Einv, HNNExtension.lift_t]
  refine ⟨A.map e.toMonoidHom, B.map e.toMonoidHom, φ',
    MonoidHom.toMulEquiv E Einv hleft hright, rfl, rfl, ?_, ?_⟩
  · intro g
    change E (HNNExtension.of g) = HNNExtension.of (e g)
    simp only [E, HNNExtension.lift_of, fwd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  · change E HNNExtension.t = HNNExtension.t
    simp only [E, HNNExtension.lift_t]

end Work.OROneRel
