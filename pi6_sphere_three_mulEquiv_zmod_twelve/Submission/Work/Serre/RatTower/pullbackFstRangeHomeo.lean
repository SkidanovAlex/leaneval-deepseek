import Mathlib
import Submission.Work.StemsB.Fibrations

namespace Work.Serre.RatTower

set_option maxHeartbeats 800000

-- `Work.StemsB.Pullback p q = {x : E × E' // p x.1 = q x.2}` and
-- `Work.StemsB.pullbackFst p q x = x.1.1`, so `Pullback g' p = {(γ',e) : Γ' × E // g' γ' = p e}`
-- and the domain is `{(γ',e,·) // γ' ∈ Set.range incl}`.
-- Forward map: `x ↦ ⟨(incl⁻¹ x.1.1.1, x.1.1.2), ·⟩` where `incl⁻¹` is the inverse of `incl` on its
-- range (`Topology.IsEmbedding.toHomeomorph (⟨hind, hinj⟩ : Topology.IsEmbedding incl)`).
-- Inverse map: `y ↦ ⟨⟨(incl y.1.1, y.1.2), ·⟩, ⟨y.1.1, rfl⟩⟩`.
-- Continuity of the forward map follows from that homeomorphism; use `Continuous.subtype_mk`,
-- `Homeomorph.continuous_invFun`, `continuous_fst`, `continuous_snd`, `continuous_subtype_val`.
theorem pullbackFstRangeHomeo {B E Γ Γ' : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] [TopologicalSpace Γ'] (incl : C(Γ, Γ')) (hinj : Function.Injective incl)
    (hind : Topology.IsInducing incl) (g : C(Γ, B)) (g' : C(Γ', B))
    (hg : ∀ γ, g' (incl γ) = g γ) (p : C(E, B)) :
    ∃ e : ↥((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl)) ≃ₜ (Work.StemsB.Pullback g p),
      (∀ x, incl ((e x).1.1) = x.1.1.1) ∧
      (∀ x, (e x).1.2 = x.1.1.2) ∧
      (∀ y : Work.StemsB.Pullback g p, (e.symm y).1.1.1 = incl y.1.1) ∧
      (∀ y : Work.StemsB.Pullback g p, (e.symm y).1.1.2 = y.1.2) := by
  -- `incl` is an embedding, so it is a homeomorphism onto its range.
  have hE : Topology.IsEmbedding (incl : Γ → Γ') := ⟨hind, hinj⟩
  let hom : ↥(Set.range incl) ≃ₜ Γ := hE.toHomeomorph.symm
  have hom_spec : ∀ x : ↥(Set.range incl), incl (hom x) = x.1 := fun x =>
    congrArg Subtype.val (Homeomorph.apply_symm_apply hE.toHomeomorph x)
  have hom_symm_spec : ∀ γ : Γ, hom ⟨incl γ, ⟨γ, rfl⟩⟩ = γ := fun γ =>
    hE.toHomeomorph_symm_apply γ
  have hom_apply_eq : ∀ (y : ↥(Set.range incl)) (γ : Γ), incl γ = y.1 → hom y = γ := by
    intro y γ h
    have hy : y = ⟨incl γ, ⟨γ, rfl⟩⟩ := Subtype.ext h.symm
    rw [hy, hom_symm_spec]
  -- The domain and the two maps.
  let D := ↥((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl))
  let F : D → Work.StemsB.Pullback g p := fun x =>
    ⟨(hom ⟨x.1.1.1, x.2⟩, x.1.1.2), by
      show g (hom ⟨x.1.1.1, x.2⟩) = p x.1.1.2
      rw [← hg (hom ⟨x.1.1.1, x.2⟩), hom_spec]
      exact x.1.2⟩
  let G : Work.StemsB.Pullback g p → D := fun y =>
    ⟨⟨(incl y.1.1, y.1.2), by
        show g' (incl y.1.1) = p y.1.2
        rw [hg y.1.1]; exact y.2⟩,
      ⟨y.1.1, rfl⟩⟩
  -- Continuity of the two maps.
  have hfst : Continuous fun x : D => x.1.1.1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hsnd : Continuous fun x : D => x.1.1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hhomcont : Continuous fun x : D => hom ⟨x.1.1.1, x.2⟩ :=
    hom.continuous.comp (Continuous.subtype_mk hfst (fun x => x.2))
  have hFcont : Continuous F := by
    apply Continuous.subtype_mk
    exact hhomcont.prodMk hsnd
  have hGcont : Continuous G := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop
  -- The two maps are mutually inverse.
  have hleft : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hom_spec _
    · rfl
  have hright : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    apply Prod.ext
    · show hom ⟨(G y).1.1.1, (G y).2⟩ = y.1.1
      exact hom_apply_eq _ _ rfl
    · rfl
  let e : ↥((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl)) ≃ₜ (Work.StemsB.Pullback g p) :=
    Homeomorph.mk { toFun := F, invFun := G, left_inv := hleft, right_inv := hright }
      hFcont hGcont
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro x
    change incl ((F x).1.1) = x.1.1.1
    exact hom_spec _
  · intro x
    change (F x).1.2 = x.1.1.2
    rfl
  · intro y
    change (G y).1.1.1 = incl y.1.1
    rfl
  · intro y
    change (G y).1.1.2 = y.1.2
    rfl

end Work.Serre.RatTower
