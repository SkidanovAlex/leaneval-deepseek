import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- The multiplicative automorphism group of a commutative group `A` (endowed with its
canonical `ZMod 2`-vector-space structure on `Additive A`) maps to the group of `ZMod 2`-linear
equivalences of `Additive A`, by viewing a multiplicative automorphism as an additive (and hence
`ZMod 2`-linear) automorphism. -/
private noncomputable def mulAutToLin {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)] :
    MulAut A →* (Additive A ≃ₗ[ZMod 2] Additive A) where
  toFun σ := (MulEquiv.toAdditive σ).toLinearEquiv (fun c x => ZMod.map_smul _ c x)
  map_one' := by
    ext x
    simp [AddEquiv.coe_toLinearEquiv]
  map_mul' σ τ := by
    ext x
    simp [AddEquiv.coe_toLinearEquiv, LinearEquiv.mul_apply]

/-- The inverse direction: a `ZMod 2`-linear equivalence of `Additive A` yields a multiplicative
automorphism of `A`. -/
private noncomputable def linToMulAut {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)] :
    (Additive A ≃ₗ[ZMod 2] Additive A) → MulAut A :=
  fun e => MulEquiv.toAdditive.symm (e.toAddEquiv)

private lemma mulAutToLin_linToMulAut {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    (e : Additive A ≃ₗ[ZMod 2] Additive A) : mulAutToLin (linToMulAut e) = e := by
  ext x
  simp [mulAutToLin, linToMulAut]

private lemma linToMulAut_mulAutToLin {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    (σ : MulAut A) : linToMulAut (mulAutToLin σ) = σ := by
  ext x
  simp [mulAutToLin, linToMulAut]

/-- A group isomorphism sends the centralizer of a singleton onto the centralizer of the image. -/
private lemma map_centralizer_singleton' {G H : Type} [Group G] [Group H] (f : G ≃* H) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map f.toMonoidHom =
      Subgroup.centralizer ({f g} : Set H) := by
  apply le_antisymm
  · have h := Subgroup.map_centralizer_le_centralizer_image ({g} : Set G) f.toMonoidHom
    simpa using h
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_map]
    refine ⟨f.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

/-- The centralizers of a group element and of its image under a group isomorphism are isomorphic. -/
private lemma centralizer_mulEquiv_singleton' {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (g : G) :
    Nonempty (↥(Subgroup.centralizer ({g} : Set G)) ≃*
      ↥(Subgroup.centralizer ({f g} : Set H))) := by
  refine ⟨?_⟩
  have hmap := map_centralizer_singleton' f g
  exact (Subgroup.equivMapOfInjective (Subgroup.centralizer ({g} : Set G)) f.toMonoidHom
    f.injective).trans (hmap ▸ MulEquiv.refl _)

/-- For a commutative group `A` carrying its `ZMod 2`-vector-space structure on `Additive A`, the
centralizer of a multiplicative automorphism `σ` in `MulAut A` is isomorphic to the centralizer of
the corresponding linear automorphism of `Additive A`.

This is the instance at `p = 2` of the standard identification between `Aut(A)` and `GL(V)` for
`A` an elementary abelian `p`-group, transported to centralizers. -/
theorem centralizer_mulAut_linear_equiv {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    (σ : MulAut A) :
    let σL : Additive A ≃ₗ[ZMod 2] Additive A :=
      (σ.toAdditive).toLinearEquiv (fun (c : ZMod 2) x => ZMod.map_smul _ c x)
    Nonempty (↥(Subgroup.centralizer ({σ} : Set (MulAut A))) ≃*
      ↥(Subgroup.centralizer ({σL} : Set (Additive A ≃ₗ[ZMod 2] Additive A)))) := by
  have hbij : Function.Bijective ⇑(mulAutToLin (A := A)) :=
    ⟨fun x y h => by rw [← linToMulAut_mulAutToLin x, ← linToMulAut_mulAutToLin y, h],
     fun y => ⟨linToMulAut y, mulAutToLin_linToMulAut y⟩⟩
  let f : MulAut A ≃* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    MulEquiv.ofBijective (mulAutToLin (A := A)) hbij
  exact centralizer_mulEquiv_singleton' f σ

end Work.ThmF.ChV12
