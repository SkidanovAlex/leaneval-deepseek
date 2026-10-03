import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm

universe u

namespace Work.ORLocInd.CohenLyndon.magnusStep

open Work.CohenLyndon

theorem cohenLyndonNC_of_mulEquiv {G H : Type u} [Group G] [Group H] (e : G ≃* H) (r : G) :
    Work.CohenLyndon.CohenLyndonNC (e r) → Work.CohenLyndon.CohenLyndonNC r := by
  rintro ⟨T, hT, eT, heT⟩
  classical
  -- The image of the normal closure of `r` under `e` is the normal closure of `e r`.
  have hNC : (Subgroup.normalClosure ({r} : Set G)).map (e : G →* H) =
      Subgroup.normalClosure ({e r} : Set H) := by
    rw [Subgroup.map_normalClosure _ _ e.surjective]
    show Subgroup.normalClosure (⇑(e : G →* H) '' {r}) = Subgroup.normalClosure {e r}
    rw [Set.image_singleton]
    rfl
  -- The image of `⟪r⟫ ⊔ C_G(r)` is `⟪e r⟫ ⊔ C_H(e r)`.
  have hmap : (Subgroup.normalClosure ({r} : Set G) ⊔
        Subgroup.centralizer ({r} : Set G)).map (e : G →* H) =
      Subgroup.normalClosure ({e r} : Set H) ⊔ Subgroup.centralizer ({e r} : Set H) := by
    have hC : (Subgroup.centralizer ({r} : Set G)).map (e : G →* H) =
        Subgroup.centralizer ({e r} : Set H) := by
      refine le_antisymm ?_ ?_
      · simpa [Set.image_singleton] using
          Subgroup.map_centralizer_le_centralizer_image ({r} : Set G) (e : G →* H)
      · intro x hx
        obtain ⟨y, rfl⟩ := e.surjective x
        refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact e.injective (by rw [map_mul, map_mul]; exact hx (e r) (by simp))
    rw [Subgroup.map_sup, hNC, hC]
  refine ⟨e ⁻¹' T, ?_, ?_⟩
  · -- The preimage of a transversal for `e r` is a transversal for `r`.
    intro g
    obtain ⟨t0, ⟨ht0T, ht0K⟩, huniq0⟩ := hT (e g)
    refine ⟨e.symm t0, ⟨?_, ?_⟩, ?_⟩
    · show e (e.symm t0) ∈ T
      rwa [e.apply_symm_apply]
    · have hmem : (e g)⁻¹ * t0 ∈
          (Subgroup.normalClosure ({r} : Set G) ⊔
            Subgroup.centralizer ({r} : Set G)).map (e : G →* H) := by
        rw [hmap]; exact ht0K
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
      have : y = g⁻¹ * e.symm t0 := by
        refine e.injective ?_
        rw [map_mul, map_inv, e.apply_symm_apply]
        exact hyeq
      rw [← this]; exact hy
    · intro t ht
      have h1 : e t ∈ T := ht.1
      have h2 : (e g)⁻¹ * e t ∈
          (Subgroup.normalClosure ({r} : Set G) ⊔
            Subgroup.centralizer ({r} : Set G)).map (e : G →* H) :=
        ⟨g⁻¹ * t, ht.2, by rw [map_mul, map_inv]; rfl⟩
      have h3 : (e g)⁻¹ * e t ∈
          Subgroup.normalClosure ({e r} : Set H) ⊔ Subgroup.centralizer ({e r} : Set H) := by
        rwa [hmap] at h2
      have h4 := huniq0 (e t) ⟨h1, h3⟩
      calc t = e.symm (e t) := (e.symm_apply_apply t).symm
        _ = e.symm t0 := by rw [h4]
  · -- Transport the basis isomorphism back along `e`.
    let ψ : ↥(e ⁻¹' T) ≃ T :=
      { toFun := fun t => ⟨e t, t.2⟩
        invFun := fun t => ⟨e.symm t, by
          show e (e.symm (t : H)) ∈ T
          rw [e.apply_symm_apply]; exact t.2⟩
        left_inv := fun t => Subtype.ext (e.symm_apply_apply (t : G))
        right_inv := fun t => Subtype.ext (e.apply_symm_apply (t : H)) }
    have hψ : ∀ t : ↥(e ⁻¹' T), ((ψ t : T) : H) = e (t : G) := fun t => rfl
    let res : ↥(Subgroup.normalClosure ({e r} : Set H)) ≃*
        ↥(Subgroup.normalClosure ({r} : Set G)) :=
      ((e.subgroupMap (Subgroup.normalClosure ({r} : Set G))).trans
        (MulEquiv.subgroupCongr hNC)).symm
    have hres : ∀ x : ↥(Subgroup.normalClosure ({e r} : Set H)),
        ((res x : ↥(Subgroup.normalClosure ({r} : Set G))) : G) = e.symm (x : H) := by
      intro x
      simp [res, MulEquiv.symm_trans_apply]
    refine ⟨(FreeGroup.freeGroupCongr ψ).trans (eT.trans res), fun t => ?_⟩
    have hcongr : (FreeGroup.freeGroupCongr ψ) (FreeGroup.of t) = FreeGroup.of (ψ t) :=
      FreeGroup.map.of
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hcongr]
    have key : ((eT (FreeGroup.of (ψ t)) :
          ↥(Subgroup.normalClosure ({e r} : Set H))) : H) = e ((t : G) * r * (t : G)⁻¹) := by
      rw [heT (ψ t), hψ t, map_mul, map_mul, map_inv]
    rw [hres, key, e.symm_apply_apply]

end Work.ORLocInd.CohenLyndon.magnusStep
