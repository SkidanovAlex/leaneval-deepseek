import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transfer of `H¹` along a homeomorphic isomorphism of Galois groups

The workspace's continuous cohomology `Work.AbsoluteKummer.H1 G M` is the quotient of the locally
constant crossed homomorphisms `G → M` by the principal ones.  It has functoriality in the
*coefficients* over a fixed group (`Work.AbsoluteKummer.mapH1`) and an inflation map for
surjections (`Work.AbsoluteKummer.Inflation.inflH1_injective`), but **no functoriality in the
group** — which is what Hilbert 90 at an open subgroup of a Galois group (Milne, *ADT*, class
formation axiom 1.1a for `\bar k^×`) needs.

For a group isomorphism `Φ : G' ≃* G` which is moreover a **homeomorphism** and a compatible
coefficient isomorphism `Ψ : M' ≃+ M` (`Ψ (g' • m') = Φ g' • Ψ m'`), the assignment

  `f ↦ (fun g => Ψ (f (Φ.symm g)))`

transfers locally constant crossed homomorphisms, principal ones, and hence descends to

  `Work.SSGRoute.PT.h1Transfer Φ hΦ Ψ hΨ : H1 G' M' ≃+ H1 G M`.

Note that the hypothesis on `Φ` must be `IsHomeomorph Φ` and *not* `IsLocallyConstant Φ`: an
injective homomorphism of profinite groups has trivial kernel, so local constancy at `1` would
force `1` to be open.  Local constancy is preserved because `Φ.symm` is continuous, so preimages
of the open fibres of `f` are open.
-/

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PT

noncomputable section

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- The inverse of a homeomorphic group isomorphism is continuous. -/
theorem continuous_symm_of_isHomeomorph_mulEquiv (Φ : G' ≃* G)
    (hΦ : IsHomeomorph (Φ : G' → G)) : Continuous (Φ.symm : G → G') := by
  rw [continuous_def]
  intro s hs
  have h : (Φ.symm : G → G') ⁻¹' s = Φ '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨Φ.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [h]
  exact hΦ.isOpenMap s hs

variable {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup M'] [DistribMulAction G' M']

/-- **The cochain transfer** along `Φ : G' ≃* G` and `Ψ : M' ≃+ M`:
`f ↦ (fun g => Ψ (f (Φ.symm g)))`. -/
noncomputable def cochainTransfer (Φ : G' ≃* G) (Ψ : M' ≃+ M) :
    (G' → M') →+ (G → M) where
  toFun f := fun g => Ψ (f (Φ.symm g))
  map_zero' := by funext g; simp
  map_add' f h := by funext g; simp

@[simp] theorem cochainTransfer_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G' → M') (g : G) :
    cochainTransfer Φ Ψ f g = Ψ (f (Φ.symm g)) := rfl

/-- Local constancy is preserved by precomposition with a continuous map (the workspace's
`Work.AbsoluteKummer.IsLocallyConstant.comp` forces the two domains into the *same* universe, so
we restate it here for use with groups in different universes). -/
theorem isLocallyConstant_comp_continuous {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : Y → M} (hg : Work.AbsoluteKummer.IsLocallyConstant g) {φ : X → Y}
    (hφ : Continuous φ) : Work.AbsoluteKummer.IsLocallyConstant (g ∘ φ) := by
  intro x
  obtain ⟨U, hU, hxU, hgU⟩ := hg (φ x)
  exact ⟨φ ⁻¹' U, hU.preimage hφ, hxU, fun y hy => hgU (φ y) hy⟩

/-- The transfer of a locally constant cochain is locally constant. -/
theorem cochainTransfer_isLocallyConstant (Φ : G' ≃* G)
    (hΦc : Continuous (Φ.symm : G → G')) (Ψ : M' ≃+ M) {f : G' → M'}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    Work.AbsoluteKummer.IsLocallyConstant (cochainTransfer Φ Ψ f) :=
  (isLocallyConstant_comp_continuous hf hΦc).map (Ψ : M' → M)

/-- The transfer of a crossed homomorphism is a crossed homomorphism. -/
theorem cochainTransfer_isCrossedHom (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {f : G' → M'} (hf : Work.GroupCohomology.IsCrossedHom G' M' f) :
    Work.GroupCohomology.IsCrossedHom G M (cochainTransfer Φ Ψ f) := by
  intro g h
  have h1 : Φ.symm (g * h) = Φ.symm g * Φ.symm h := map_mul _ _ _
  show Ψ (f (Φ.symm (g * h))) = g • Ψ (f (Φ.symm h)) + Ψ (f (Φ.symm g))
  rw [h1, hf, map_add, hΨ, MulEquiv.apply_symm_apply]

/-- The transfer sends the coboundary of `m'` to the coboundary of `Ψ m'`. -/
theorem cochainTransfer_d0 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (m' : M') :
    cochainTransfer Φ Ψ (Work.GroupCohomology.d0 G' M' m') =
      Work.GroupCohomology.d0 G M (Ψ m') := by
  funext g
  rw [cochainTransfer_apply, Work.GroupCohomology.d0_apply, Work.GroupCohomology.d0_apply,
    map_sub, hΨ, MulEquiv.apply_symm_apply]

/-- **The transfer on continuous `1`-cocycles.** -/
noncomputable def z1Transfer (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    ↥(Z1 G' M') →+ ↥(Z1 G M) where
  toFun f := ⟨cochainTransfer Φ Ψ (f : G' → M'), by
    have hf := (Work.AbsoluteKummer.mem_Z1_iff (f : G' → M')).mp f.2
    exact (Work.AbsoluteKummer.mem_Z1_iff _).mpr
      ⟨cochainTransfer_isCrossedHom Φ Ψ hΨ hf.1,
        cochainTransfer_isLocallyConstant Φ hΦc Ψ hf.2⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' f h := Subtype.ext (map_add _ _ _)

@[simp] theorem z1Transfer_coe (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (f : ↥(Z1 G' M')) :
    ((z1Transfer Φ hΦc Ψ hΨ f : ↥(Z1 G M)) : G → M)
      = cochainTransfer Φ Ψ (f : G' → M') := rfl

/-- **The transfer on `H¹`**, as an additive homomorphism. -/
noncomputable def h1TransferAddHom (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    H1 G' M' →+ H1 G M :=
  QuotientAddGroup.lift ((B1 G' M').comap (Z1 G' M').subtype)
    ((H1π G M).comp (z1Transfer Φ hΦc Ψ hΨ)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.AbsoluteKummer.H1π_eq_zero_iff]
      have hx' : (x : G' → M') ∈ B1 G' M' := AddSubgroup.mem_comap.mp hx
      obtain ⟨a, ha⟩ := (Work.AbsoluteKummer.mem_B1_iff _).mp hx'
      refine (Work.AbsoluteKummer.mem_B1_iff _).mpr ⟨Ψ a, ?_⟩
      show Work.GroupCohomology.d0 G M (Ψ a) = cochainTransfer Φ Ψ (x : G' → M')
      rw [← ha, cochainTransfer_d0 Φ Ψ hΨ a])

theorem h1TransferAddHom_mk (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (f : ↥(Z1 G' M')) :
    h1TransferAddHom Φ hΦc Ψ hΨ (H1π G' M' f) = H1π G M (z1Transfer Φ hΦc Ψ hΨ f) :=
  QuotientAddGroup.lift_mk' _ _ f

/-- Compatibility of `Ψ.symm` with the actions. -/
theorem symm_compat (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (g : G) (m : M) : Ψ.symm (g • m) = Φ.symm g • Ψ.symm m := by
  apply Ψ.injective
  simp [hΨ]

/-- The two cochain transfers are inverse to each other. -/
theorem cochainTransfer_symm_comp (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G' → M') :
    cochainTransfer Φ.symm Ψ.symm (cochainTransfer Φ Ψ f) = f := by
  funext g'
  simp [cochainTransfer_apply]

/-- The two cochain transfers are inverse to each other, in the other order. -/
theorem cochainTransfer_comp_symm (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G → M) :
    cochainTransfer Φ Ψ (cochainTransfer Φ.symm Ψ.symm f) = f := by
  funext g
  simp [cochainTransfer_apply]

/-- The transfer along `Φ` followed by the transfer along `Φ.symm` is the identity. -/
theorem h1TransferAddHom_leftInverse (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hΦc' : Continuous (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (x : H1 G' M') :
    h1TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
      (h1TransferAddHom Φ hΦc Ψ hΨ x) = x := by
  obtain ⟨f, hf⟩ :=
    QuotientAddGroup.mk'_surjective ((B1 G' M').comap (Z1 G' M').subtype) x
  rw [← hf]
  change h1TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
      (h1TransferAddHom Φ hΦc Ψ hΨ (H1π G' M' f)) = H1π G' M' f
  rw [h1TransferAddHom_mk, h1TransferAddHom_mk,
    congrArg (H1π G' M') (Subtype.ext (cochainTransfer_symm_comp Φ Ψ (f : G' → M')))]

/-- The transfer along `Φ.symm` followed by the transfer along `Φ` is the identity. -/
theorem h1TransferAddHom_rightInverse (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hΦc' : Continuous (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (y : H1 G M) :
    h1TransferAddHom Φ hΦc Ψ hΨ
      (h1TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ) y) = y := by
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk'_surjective ((B1 G M).comap (Z1 G M).subtype) y
  rw [← hf]
  change h1TransferAddHom Φ hΦc Ψ hΨ
      (h1TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
        (H1π G M f)) = H1π G M f
  rw [h1TransferAddHom_mk, h1TransferAddHom_mk,
    congrArg (H1π G M) (Subtype.ext (cochainTransfer_comp_symm Φ Ψ (f : G → M)))]

/-- **Transfer of `H¹` along a homeomorphic group isomorphism with compatible coefficients.**
This is the functoriality of continuous `H¹` in the *group*, which the workspace lacked; it is what
reduces Hilbert 90 at an open subgroup of `Gal(\bar k/k)` (Milne, *ADT*, class formation axiom
1.1a) to the absolute case `Submission.hilbert90_H1_eq_zero`, using that the isomorphism of
absolute Galois groups induced by an isomorphism of algebraic closures is a homeomorphism
(`NK.Mine.isHomeomorph_autCongr`). -/
noncomputable def h1Transfer (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    H1 G' M' ≃+ H1 G M where
  toFun := h1TransferAddHom Φ (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) Ψ hΨ
  invFun := h1TransferAddHom Φ.symm (by simpa using hΦ.continuous) Ψ.symm
    (symm_compat Φ Ψ hΨ)
  left_inv := h1TransferAddHom_leftInverse Φ
    (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) hΦ.continuous Ψ hΨ
  right_inv := h1TransferAddHom_rightInverse Φ
    (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) hΦ.continuous Ψ hΨ
  map_add' := map_add _

end

end Work.SSGRoute.PT
