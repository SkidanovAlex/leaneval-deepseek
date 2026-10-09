import Mathlib
import Submission.Work.SSGRoute.PT.e1aBetaCan_localAPI
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.hom_dualMod_local_units
import Submission.Work.SSGRoute.ext_continuous_descent_fg
import Submission.Work.SSGRoute.PT.e1aBetaLocalChain.ext_two_local_descent_injective
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.ext_one_iso_lattice_cohomology
import Submission.Work.SSGRoute.homRep
import Submission.Work.GroupCohomology.Inflation
import Submission.Work.GroupCohomology.ConnectingMap
import Submission.Work.GroupCohomology.range_mapH1_eq_ker_deltaH1
import Submission.Work.GroupCohomology.range_infH1_eq_ker_resH1
import Submission.Work.GroupCohomology.ker_infH1_eq_bot
import Submission.Work.GroupCohomology.Shapiro
import Submission.Work.GroupCohomology.ShortExact
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
import Submission.Work.SSGRoute.PT.devissageLinear
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.h3_H3_subsingleton_of_image
import Submission.Work.SSGRoute.PT.mkb_ld02_defs
import Submission.Work.SSGRoute.PT.decompK_subgroupOf_facts
import Submission.Work.SSGRoute.PT.frobenius_coindAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-!
## Transfer of the abstract second cohomology along a group isomorphism

The degree-two, continuity-free companion of `Work.SSGRoute.PT.h2Transfer` (which lives in the
continuous model `Work.AbsoluteKummer`).  For a group isomorphism `Φ : G' ≃* G` and an equivariant
additive equivalence `Ψ : M' ≃+ M`, the assignment `c ↦ (fun p => Ψ (c (Φ.symm p.1, Φ.symm p.2)))`
transfers abstract `2`-cochains, `2`-cocycles and `2`-coboundaries (both `Z2` and `B2` are defined
by the *same* formulas as in the continuous model, so the proofs are those of `H2Transfer` with the
continuity clauses dropped), and descends to `gcH2Transfer Φ Ψ : H²(G',M') ≃+ H²(G,M)`.
-/

section GCTransfer

variable {G G' : Type} [Group G] [Group G']
variable {M M' : Type} [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup M'] [DistribMulAction G' M']

/-- The `1`-cochain transfer along `Φ : G' ≃* G` and `Ψ : M' ≃+ M`. -/
noncomputable def gcCochain1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) : (G' → M') →+ (G → M) where
  toFun f g := Ψ (f (Φ.symm g))
  map_zero' := by funext g; simp
  map_add' f f' := by funext g; simp only [Pi.add_apply, map_add]

@[simp] theorem gcCochain1_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G' → M') (g : G) :
    gcCochain1 Φ Ψ f g = Ψ (f (Φ.symm g)) := rfl

/-- The `2`-cochain transfer along `Φ : G' ≃* G` and `Ψ : M' ≃+ M`. -/
noncomputable def gcCochain2 (Φ : G' ≃* G) (Ψ : M' ≃+ M) :
    (G' × G' → M') →+ (G × G → M) where
  toFun c p := Ψ (c (Φ.symm p.1, Φ.symm p.2))
  map_zero' := by funext p; simp
  map_add' c d := by funext p; simp only [Pi.add_apply, map_add]

@[simp] theorem gcCochain2_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G' × G' → M') (p : G × G) :
    gcCochain2 Φ Ψ c p = Ψ (c (Φ.symm p.1, Φ.symm p.2)) := rfl

/-- The transfer of an abstract `2`-cocycle is an abstract `2`-cocycle. -/
theorem gcCochain2_mem_Z2 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {c : G' × G' → M'} (hc : c ∈ Work.GroupCohomology.Z2 G' M') :
    gcCochain2 Φ Ψ c ∈ Work.GroupCohomology.Z2 G M := by
  rw [Work.GroupCohomology.mem_Z2_iff] at hc ⊢
  intro g h k
  have h1 : Φ.symm (g * h) = Φ.symm g * Φ.symm h := map_mul _ _ _
  have h2 : Φ.symm (h * k) = Φ.symm h * Φ.symm k := map_mul _ _ _
  have key := hc (Φ.symm g) (Φ.symm h) (Φ.symm k)
  simp only [gcCochain2_apply]
  rw [h1, h2, ← map_add, key, map_add, hΨ, MulEquiv.apply_symm_apply]

/-- The `2`-cochain transfer intertwines `d¹` with the `1`-cochain transfer. -/
theorem gcCochain2_d1 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (f : G' → M') :
    gcCochain2 Φ Ψ (Work.GroupCohomology.d1 G' M' f)
      = Work.GroupCohomology.d1 G M (gcCochain1 Φ Ψ f) := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [gcCochain2_apply, gcCochain1_apply, Work.GroupCohomology.d1_apply, map_sub, map_add]
  rw [hΨ, map_mul, MulEquiv.apply_symm_apply]

/-- The transfer sends abstract `2`-coboundaries to abstract `2`-coboundaries. -/
theorem gcCochain2_mem_B2 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {c : G' × G' → M'} (hc : c ∈ Work.GroupCohomology.B2 G' M') :
    gcCochain2 Φ Ψ c ∈ Work.GroupCohomology.B2 G M := by
  rw [Work.GroupCohomology.mem_B2_iff] at hc ⊢
  obtain ⟨f, rfl⟩ := hc
  exact ⟨gcCochain1 Φ Ψ f, (gcCochain2_d1 Φ Ψ hΨ f).symm⟩

/-- The transfer on abstract `2`-cocycles. -/
noncomputable def gcZ2Transfer (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Work.GroupCohomology.Z2 G' M' →+ Work.GroupCohomology.Z2 G M where
  toFun c := ⟨gcCochain2 Φ Ψ (c : G' × G' → M'),
    gcCochain2_mem_Z2 Φ Ψ hΨ c.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _c _d := Subtype.ext (map_add _ _ _)

@[simp] theorem gcZ2Transfer_coe (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (c : Work.GroupCohomology.Z2 G' M') :
    ((gcZ2Transfer Φ Ψ hΨ c : Work.GroupCohomology.Z2 G M) : G × G → M)
      = gcCochain2 Φ Ψ (c : G' × G' → M') := rfl

/-- The transfer on the abstract second cohomology, as an additive homomorphism. -/
noncomputable def gcH2TransferAddHom (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Work.GroupCohomology.H2 G' M' →+ Work.GroupCohomology.H2 G M :=
  QuotientAddGroup.lift
    ((Work.GroupCohomology.B2 G' M').comap (Work.GroupCohomology.Z2 G' M').subtype)
    ((Work.GroupCohomology.H2π G M).comp (gcZ2Transfer Φ Ψ hΨ)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.GroupCohomology.H2pi_eq_zero_iff,
        gcZ2Transfer_coe]
      have hx' : (x : G' × G' → M') ∈ Work.GroupCohomology.B2 G' M' :=
        AddSubgroup.mem_comap.mp hx
      exact gcCochain2_mem_B2 Φ Ψ hΨ hx')

theorem gcH2TransferAddHom_mk (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (c : Work.GroupCohomology.Z2 G' M') :
    gcH2TransferAddHom Φ Ψ hΨ (Work.GroupCohomology.H2π G' M' c)
      = Work.GroupCohomology.H2π G M (gcZ2Transfer Φ Ψ hΨ c) :=
  QuotientAddGroup.lift_mk' _ _ c

/-- The equivariance needed for the reverse transfer. -/
theorem gcSymmCompat (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    ∀ (g : G) (m : M), Ψ.symm (g • m) = Φ.symm g • Ψ.symm m := by
  intro g m
  have h : Ψ (Φ.symm g • Ψ.symm m) = g • m := by
    rw [hΨ, Φ.apply_symm_apply, Ψ.apply_symm_apply]
  rw [← h, AddEquiv.symm_apply_apply]

/-- The two `2`-cochain transfers are inverse to each other. -/
theorem gcCochain2_symm_comp (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G' × G' → M') :
    gcCochain2 Φ.symm Ψ.symm (gcCochain2 Φ Ψ c) = c := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [gcCochain2_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- The two `2`-cochain transfers are inverse to each other, in the other order. -/
theorem gcCochain2_comp_symm (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G × G → M) :
    gcCochain2 Φ Ψ (gcCochain2 Φ.symm Ψ.symm c) = c := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [gcCochain2_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

theorem gcH2TransferAddHom_leftInverse (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (x : Work.GroupCohomology.H2 G' M') :
    gcH2TransferAddHom Φ.symm Ψ.symm (gcSymmCompat Φ Ψ hΨ)
      (gcH2TransferAddHom Φ Ψ hΨ x) = x := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.GroupCohomology.B2 G' M').comap (Work.GroupCohomology.Z2 G' M').subtype) x
  rw [← hc]
  change gcH2TransferAddHom Φ.symm Ψ.symm (gcSymmCompat Φ Ψ hΨ)
      (gcH2TransferAddHom Φ Ψ hΨ (Work.GroupCohomology.H2π G' M' c))
    = Work.GroupCohomology.H2π G' M' c
  rw [gcH2TransferAddHom_mk, gcH2TransferAddHom_mk,
    congrArg (Work.GroupCohomology.H2π G' M')
      (Subtype.ext (gcCochain2_symm_comp Φ Ψ (c : G' × G' → M')))]

theorem gcH2TransferAddHom_rightInverse (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (y : Work.GroupCohomology.H2 G M) :
    gcH2TransferAddHom Φ Ψ hΨ
      (gcH2TransferAddHom Φ.symm Ψ.symm (gcSymmCompat Φ Ψ hΨ) y) = y := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.GroupCohomology.B2 G M).comap (Work.GroupCohomology.Z2 G M).subtype) y
  rw [← hc]
  change gcH2TransferAddHom Φ Ψ hΨ
      (gcH2TransferAddHom Φ.symm Ψ.symm (gcSymmCompat Φ Ψ hΨ)
        (Work.GroupCohomology.H2π G M c)) = Work.GroupCohomology.H2π G M c
  rw [gcH2TransferAddHom_mk, gcH2TransferAddHom_mk,
    congrArg (Work.GroupCohomology.H2π G M)
      (Subtype.ext (gcCochain2_comp_symm Φ Ψ (c : G × G → M)))]

/-- **Transfer of the abstract `H²` along a group isomorphism with compatible coefficients.** -/
noncomputable def gcH2Transfer (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Work.GroupCohomology.H2 G' M' ≃+ Work.GroupCohomology.H2 G M where
  toFun := gcH2TransferAddHom Φ Ψ hΨ
  invFun := gcH2TransferAddHom Φ.symm Ψ.symm (gcSymmCompat Φ Ψ hΨ)
  left_inv := gcH2TransferAddHom_leftInverse Φ Ψ hΨ
  right_inv := gcH2TransferAddHom_rightInverse Φ Ψ hΨ
  map_add' := map_add _

end GCTransfer

theorem localDictionary_fin_injective
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 2 →+
      @Work.GroupCohomology.H2 (SSGRoute.decomp k A) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (SSGRoute.decomp k A)),
      Function.Injective Λ := by
  sorry

end Work.SSGRoute.PT
