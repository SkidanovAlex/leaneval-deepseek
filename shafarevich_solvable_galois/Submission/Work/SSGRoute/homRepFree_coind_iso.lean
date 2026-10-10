import Mathlib.RepresentationTheory.Coinduced
import Submission.Work.SSGRoute.homRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Hom_G(k[G]^α, N) ≅ Coind_1^G(α → N)`

For a group `G`, a type `α` and a `Rep Coeff G` `N`, the internal `Hom`-representation
`homRep (Rep.free Coeff G α) N` — the `Coeff`-linear maps `(α →₀ Coeff[G]) →ₗ N.V` with the
conjugation action `(g · f) x = N.ρ g (f (R.ρ g⁻¹ x))` — is isomorphic to the coinduced
representation `Coind_1^G(α → N)` = functions `G → (α → N.V)` with the right-translation action.

This is the Shapiro / Frobenius reciprocity identification
`Hom_G(Ind_1^G k[α], N) ≅ Coind_1^G(Hom_k(k[α], N))` in the shape needed by the `Ext`-core
computation: `Rep.free Coeff G α = k[G] ⊗ k[α]` is `Ind_1^G(k[α])` and
`Rep.coind ⊥.subtype X` is `Coind_1^G(X)`.

The isomorphism is the composite
* `domAux`  : `(α →₀ Coeff[G]) ≃ₗ (α × G →₀ Coeff)` (the free module over the group ring),
* `llift`   : `Hom_Coeff(α × G →₀ Coeff, N) ≃ (α × G → N)`,
* `twistAux`: the "conjugation versus right translation" twist
  `F ↦ (g ↦ i ↦ N.ρ g (F (i, g⁻¹)))`,
* the identity `G → (α → N) ≅ ↑(coindV ⊥.subtype X)` for `X = trivial (α → N)` (the equivariance
  condition defining `coindV` is vacuous for the trivial subgroup).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

variable (G : Type) [Group G] (α : Type) (N : Rep.{0} Coeff G)

/-- The twist `(α × G → N) ≃ (G → α → N)`, `F ↦ (g ↦ i ↦ N.ρ g (F (i, g⁻¹)))`, which converts
the conjugation action into the right-translation action. -/
def twistAux : ((α × G) → N.V) ≃ₗ[Coeff] (G → α → N.V) where
  toFun F := fun g i => N.ρ g (F (i, g⁻¹))
  invFun F := fun p => N.ρ p.2 (F p.2⁻¹ p.1)
  left_inv F := by funext p; simp
  right_inv F := by funext g i; simp
  map_add' F₁ F₂ := by funext g i; simp only [Pi.add_apply, map_add]
  map_smul' c F := by
    funext g i
    obtain ⟨n⟩ := c
    show N.ρ g (n • F (i, g⁻¹)) = n • N.ρ g (F (i, g⁻¹))
    exact AddMonoidHom.map_zsmul (N.ρ g).toAddMonoidHom n (F (i, g⁻¹))

@[simp] lemma twistAux_apply (F : (α × G) → N.V) (g : G) (i : α) :
    twistAux G α N F g i = N.ρ g (F (i, g⁻¹)) := rfl

@[simp] lemma twistAux_symm_apply (F : G → α → N.V) (p : α × G) :
    (twistAux G α N).symm F p = N.ρ p.2 (F p.2⁻¹ p.1) := rfl

/-- The identification `(α →₀ Coeff[G]) ≃ₗ (α × G →₀ Coeff)` obtained from
`MonoidAlgebra.coeffLinearEquiv` and `Finsupp.curryLinearEquiv`. -/
def domAux : (α →₀ MonoidAlgebra Coeff G) ≃ₗ[Coeff] (α × G →₀ Coeff) :=
  (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv Coeff)).trans
    (Finsupp.curryLinearEquiv Coeff).symm

@[simp] lemma domAux_symm_single (i : α) (g : G) (c : Coeff) :
    (domAux G α).symm (Finsupp.single (i, g) c) = Finsupp.single i (MonoidAlgebra.single g c) := by
  apply (domAux G α).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [domAux, LinearEquiv.trans_apply]
  rw [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single,
      MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single]
  rw [show (Finsupp.single i (Finsupp.single g c))
        = (Finsupp.curryLinearEquiv Coeff) (Finsupp.single (i, g) c) by
      rw [Finsupp.curryLinearEquiv_apply, Finsupp.curry_single]]
  rw [LinearEquiv.symm_apply_apply]

/-- The middle piece: `Hom_Coeff(α × G →₀ Coeff, N) ≃ (α × G → N) ≃ (G → α → N)`. -/
def midAux : ((α × G →₀ Coeff) →ₗ[Coeff] N.V) ≃ₗ[Coeff] (G → α → N.V) :=
  (Finsupp.llift N.V Coeff Coeff (α × G)).symm.trans (twistAux G α N)

@[simp] lemma midAux_apply (y : (α × G →₀ Coeff) →ₗ[Coeff] N.V) (g : G) (i : α) :
    midAux G α N y g i = N.ρ g (y (Finsupp.single (i, g⁻¹) 1)) := by
  simp only [midAux, LinearEquiv.trans_apply, Finsupp.llift_symm_apply, twistAux_apply]

/-- The `Coeff`-linear equivalence underlying the Shapiro identification. -/
def equivAux : ((α →₀ MonoidAlgebra Coeff G) →ₗ[Coeff] N.V) ≃ₗ[Coeff] (G → α → N.V) :=
  ((domAux G α).arrowCongr (LinearEquiv.refl Coeff N.V)).trans (midAux G α N)

@[simp] lemma equivAux_apply (x : (α →₀ MonoidAlgebra Coeff G) →ₗ[Coeff] N.V) (g : G) (i : α) :
    equivAux G α N x g i = N.ρ g (x (Finsupp.single i (MonoidAlgebra.single (g⁻¹) 1))) := by
  simp only [equivAux, LinearEquiv.trans_apply, midAux_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.refl_apply, domAux_symm_single]

/-- The trivial `⊥`-representation `α → N.V`. -/
abbrev targetRep : Rep.{0} Coeff (⊥ : Subgroup G) :=
  Rep.trivial Coeff (⊥ : Subgroup G) (α → N.V)

/-- Computation rule for `homSMul`: the conjugation action of `g` on a linear map. -/
lemma homSMul_apply {G : Type} [Group G] (R N : Rep.{0} Coeff G) (g : G)
    (f : R.V →ₗ[Coeff] N.V) (x : R.V) :
    homSMul R N g f x = N.ρ g (f (R.ρ g⁻¹ x)) := rfl

/-- The action of the left regular representation on a basis element. -/
lemma free_ρ_single {G : Type} [Group G] (α : Type) (g h : G) (i : α) (r : Coeff) :
    (Rep.free Coeff G α).ρ g (Finsupp.single i (MonoidAlgebra.single h r))
      = Finsupp.single i (MonoidAlgebra.single (g * h) r) := by
  show ((Representation.free Coeff G α) g) (Finsupp.single i (MonoidAlgebra.single h r)) = _
  rw [Representation.free_single_single]

/-- The membership condition of `coindV` for the trivial subgroup is vacuous. -/
lemma memTarget (G : Type) [Group G] (α : Type) (N : Rep.{0} Coeff G) (f : G → α → N.V) :
    f ∈ Representation.coindV (⊥ : Subgroup G).subtype (targetRep G α N).ρ := by
  intro g h
  simp only [Subgroup.coe_subtype]
  rw [Subgroup.mem_bot.1 g.2, one_mul]
  exact (Representation.trivial_apply (k := Coeff) (G := ↥(⊥ : Subgroup G)) (V := α → N.V)
    g (f h)).symm

theorem homRepFree_coind_iso (G : Type) [Group G] (α : Type)
    (N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∃ (X : Rep.{0} SSGRoute.PTExt.Coeff (⊥ : Subgroup G)),
      Nonempty (Work.SSGRoute.homRep (Rep.free SSGRoute.PTExt.Coeff G α) N ≅
        Rep.coind (⊥ : Subgroup G).subtype X) := by
  -- The `Coeff`-linear isomorphism whose underlying map is `equivAux` with values in `coindV`.
  let e : ((α →₀ MonoidAlgebra Coeff G) →ₗ[Coeff] N.V) ≃ₗ[Coeff]
      ↑(Representation.coindV (⊥ : Subgroup G).subtype (targetRep G α N).ρ) :=
    { toFun := fun x => ⟨equivAux G α N x, memTarget G α N _⟩
      invFun := fun w => (equivAux G α N).symm w.1
      left_inv := fun x => by simp
      right_inv := fun w => by apply Subtype.ext; simp
      map_add' := fun x y => Subtype.ext (map_add (equivAux G α N) x y)
      map_smul' := fun c x => Subtype.ext (map_smul (equivAux G α N) c x) }
  refine ⟨targetRep G α N, ⟨Rep.mkIso (Representation.Equiv.mk e ?_)⟩⟩
  intro g
  ext x h i
  dsimp only [e]
  simp only [LinearMap.comp_apply]
  -- Both sides are the value of `equivAux` at corresponding points; the actions differ by the
  -- conjugation/right-translation twist of `equivAux`.
  change (equivAux G α N (homSMul (Rep.free Coeff G α) N g x)) h i
      = (equivAux G α N x) (h * g) i
  rw [equivAux_apply, equivAux_apply, homSMul_apply, free_ρ_single, mul_inv_rev, Rep.ρ_mul,
    LinearMap.comp_apply]

end

end Work.SSGRoute
