import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of `μ_p` along an isomorphism of algebraic closures, compatible with the
Galois action

Let `e : AlgebraicClosure F ≃ₐ[F] A₂` be an `F`-algebra isomorphism (in practice
`A₂` is another algebraic closure of `F`) and `p : ℕ`.  The map `e` restricts to an
isomorphism of the groups `μ_p(AlgebraicClosure F) ≅ μ_p(A₂)` of `p`-th roots of unity,
and this isomorphism intertwines the two Galois actions: on the source the action of
`σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F` is the one of
`Work.AbsoluteKummer.instDistribMulActionAddRootsOfUnity`, and on the target the action of
`AlgEquiv.autCongr e σ` is the one of
`Work.SSGRoute.PTembedding.MupKummer.instDistribMulActionAddRootsOfUnityOfField`.

The point is that `e` is *not* an isomorphism of `F`-algebras over a common ambient field, so
the two actions live on different coefficient modules; the intertwining statement is what makes
`μ_p` a well-defined coefficient system independently of the chosen algebraic closure.

The proof is a direct computation: both sides have underlying element of `A₂` equal to
`e (σ z)`, where `z` is the underlying field element of the unit `Additive.toMul x`.
-/

namespace Work.SSGRoute.PTembedding

noncomputable section

/-! ## Auxiliary constructions -/

/-- The units of two fields, transported along an `F`-algebra isomorphism. -/
def rootsOfUnityAutCongrAux_unitsMapEquiv {F E E' : Type*} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (e : E ≃ₐ[F] E') : Eˣ ≃* E'ˣ :=
  Units.mapEquiv (e.toRingEquiv : E ≃+* E')

/-- The isomorphism of groups of `p`-th roots of unity induced by an `F`-algebra isomorphism. -/
def rootsOfUnityAutCongrAux_rootsOfUnityEquiv {F E E' : Type*} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (e : E ≃ₐ[F] E') (p : ℕ) :
    rootsOfUnity p E ≃* rootsOfUnity p E' where
  toFun u := ⟨rootsOfUnityAutCongrAux_unitsMapEquiv e u, by
    rw [mem_rootsOfUnity]
    change (rootsOfUnityAutCongrAux_unitsMapEquiv e (u : Eˣ)) ^ p = 1
    rw [← map_pow, (mem_rootsOfUnity p (u : Eˣ)).mp u.2, map_one]⟩
  invFun v := ⟨(rootsOfUnityAutCongrAux_unitsMapEquiv e).symm v, by
    rw [mem_rootsOfUnity]
    change ((rootsOfUnityAutCongrAux_unitsMapEquiv e).symm (v : E'ˣ)) ^ p = 1
    rw [← map_pow, (mem_rootsOfUnity p (v : E'ˣ)).mp v.2, map_one]⟩
  left_inv u := Subtype.ext ((rootsOfUnityAutCongrAux_unitsMapEquiv e).left_inv (u : Eˣ))
  right_inv v := Subtype.ext ((rootsOfUnityAutCongrAux_unitsMapEquiv e).right_inv (v : E'ˣ))
  map_mul' u v :=
    Subtype.ext ((rootsOfUnityAutCongrAux_unitsMapEquiv e).map_mul (u : Eˣ) (v : Eˣ))

/-- The image of `u : rootsOfUnity p E` under the induced isomorphism is the unit-map of `u`
(as elements of the unit group). -/
theorem rootsOfUnityAutCongrAux_rootsOfUnityEquiv_coe {F E E' : Type*} [Field F] [Field E]
    [Field E'] [Algebra F E] [Algebra F E'] (e : E ≃ₐ[F] E') (p : ℕ) (u : rootsOfUnity p E) :
    ((rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p u : rootsOfUnity p E') : E'ˣ) =
      Units.mapEquiv (e.toRingEquiv : E ≃+* E') (u : Eˣ) := rfl

/-- The induced isomorphism computes as `e` on the underlying field elements. -/
theorem rootsOfUnityAutCongrAux_rootsOfUnityEquiv_val {F E E' : Type*} [Field F] [Field E]
    [Field E'] [Algebra F E] [Algebra F E'] (e : E ≃ₐ[F] E') (p : ℕ) (u : rootsOfUnity p E) :
    (((rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p u : rootsOfUnity p E') : E'ˣ) : E') =
      e ((u : Eˣ) : E) := by
  rw [rootsOfUnityAutCongrAux_rootsOfUnityEquiv_coe, Units.coe_mapEquiv]
  rfl

/-- The additive version of the induced isomorphism, on `Additive (rootsOfUnity p _)`. -/
def rootsOfUnityAutCongrAux_addEquiv {F E E' : Type*} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (e : E ≃ₐ[F] E') (p : ℕ) :
    Additive (rootsOfUnity p E) ≃+ Additive (rootsOfUnity p E') where
  toFun y := Additive.ofMul (rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p (Additive.toMul y))
  invFun y := Additive.ofMul
    ((rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p).symm (Additive.toMul y))
  left_inv y := by simp
  right_inv y := by simp
  map_add' y z := by
    show Additive.ofMul
        (rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p
          (Additive.toMul (y + z))) =
      Additive.ofMul
          (rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p (Additive.toMul y)) +
        Additive.ofMul
          (rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p (Additive.toMul z))
    rw [show Additive.toMul (y + z) = Additive.toMul y * Additive.toMul z from rfl, map_mul]
    rfl

/-- The computation rule for the additive induced isomorphism. -/
theorem rootsOfUnityAutCongrAux_addEquiv_apply {F E E' : Type*} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] (e : E ≃ₐ[F] E') (p : ℕ)
    (y : Additive (rootsOfUnity p E)) :
    Additive.toMul ((rootsOfUnityAutCongrAux_addEquiv e p) y) =
      rootsOfUnityAutCongrAux_rootsOfUnityEquiv e p (Additive.toMul y) := rfl

/-! ## The requested lemma -/

theorem rootsOfUnity_autCongr_equiv
    (F : Type*) [Field F] {A₂ : Type*} [Field A₂] [Algebra F A₂]
    (e : AlgebraicClosure F ≃ₐ[F] A₂) (p : ℕ) :
    ∃ Ψ : Additive (rootsOfUnity p (AlgebraicClosure F)) ≃+ Additive (rootsOfUnity p A₂),
      ∀ (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
        (x : Additive (rootsOfUnity p (AlgebraicClosure F))),
        Ψ (σ • x) = (AlgEquiv.autCongr e σ) • Ψ x := by
  refine ⟨rootsOfUnityAutCongrAux_addEquiv e p, ?_⟩
  intro σ x
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [rootsOfUnityAutCongrAux_addEquiv_apply,
    rootsOfUnityAutCongrAux_rootsOfUnityEquiv_val]
  rw [Work.AbsoluteKummer.addRootsOfUnity_smul_toMul_val,
    Work.AbsoluteKummer.algEquivUnitsMap_coe]
  rw [Work.SSGRoute.PTembedding.MupKummer.addRootsOfUnity_smul_toMul_val,
    Work.SSGRoute.PT.algEquivUnitsMapOfField_coe]
  simp only [rootsOfUnityAutCongrAux_addEquiv_apply,
    rootsOfUnityAutCongrAux_rootsOfUnityEquiv_val]
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

end

end Work.SSGRoute.PTembedding
