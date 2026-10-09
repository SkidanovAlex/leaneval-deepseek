import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat
import Submission.Work.SSGRoute.PT.e1aBetaCan_placeExists
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
import Submission.Work.SSGRoute.PT.e1aBetaCan_splitPlaces
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
import Submission.Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective
import Submission.Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero
import Submission.Work.SSGRoute.isLocConstOn_of_isLocallyConstant
import Submission.Work.SSGRoute.HS.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.SSGStage

open CategoryTheory

-- The finiteness of the canonical syzygy `ker(freeCover N)` from finiteness of `N`: the local
-- instance registration that the canonical chain modules rely on (`PT/e1a_can_chain.lean`).
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-- **The two constructions of the restriction of continuous `2`-cohomology agree.**  The map
`akRes` (`PT/e1aBetaCan_localDictionary_fin_compat.lean`, `Classical.choose`d from
`akH2_restriction_natural`) and `PT.resH2` (`PT/resH2.lean`, built by hand) both restrict a locally
constant `2`-cocycle to a subgroup; the computation rules `akRes_H2π` and `resH2_H2π` therefore
pin them to the same map, since `H2π` is surjective.

This is the bridge needed to combine the *cocycle-level* restriction statements of `PT/resH2.lean`
(and of `ExtChain/deltaH2_restriction.lean`, which is stated for `resH2`) with the `akRes`-spelled
hypothesis of the interface lemmas of the E1a lane. -/
theorem akRes_eq_resH2 {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
    (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.akRes H M x = Work.SSGRoute.PT.resH2 H x := by
  classical
  refine QuotientAddGroup.induction_on x ?_
  intro c
  show Work.AbsoluteKummer.akRes H M (Work.AbsoluteKummer.H2π G M c)
      = Work.SSGRoute.PT.resH2 H (Work.AbsoluteKummer.H2π G M c)
  rw [Work.AbsoluteKummer.akRes_H2π H M c.1 c.2,
    Work.SSGRoute.PT.resH2_H2π H c]
  congr 1

/-- **The continuous hypothesis implies the abstract one.**  For any subgroup `H ≤ Gal(Ω/k)`,
the vanishing of the *continuous* restriction `akRes H` of a class of `H²_c(Gal(Ω/k),E)` implies
the vanishing of the *abstract* restriction of its forgetful image: this is the computation rule
`akToGCH2_akRes` of the restriction map together with `map_zero`.

This is the (formal, cheap) reduction that lets the per-place landing clauses stated with the
*continuous* hypothesis (`akRes`) be read off the class-level localisation comparison, whose
hypothesis is the *abstract* one (`resH2 ∘ akToGCH2`). -/
theorem akRes_eq_zero_imp_resH2_akToGCH2_eq_zero {G : Type} [TopologicalSpace G] [Group G]
    (H : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.akRes H M x = 0 →
      Work.GroupCohomology.resH2 G H (Work.SSGRoute.PT.akToGCH2 G M x) = 0 := by
  intro hx
  rw [← Work.AbsoluteKummer.akToGCH2_akRes H M x, hx, map_zero]

/-! ## The two reductions of the hypothesis along the chain `e1aChainC = e1aCoeffH2 ∘ e1aChainH`

`e1aChainC = e1aCoeffH2 ∘ e1aChainH` and `e1aChainH = e1aDelta ∘ e1cEquiv ∘ e1aSyzShift⁻¹`
(`PT/e1a_can_chain.lean`).  The first factor of `e1aChainC` is a *coefficient change*, so it can be
stripped from the vanishing hypothesis; the second factor is a *connecting map of a short exact
sequence*, which commutes with restriction to a subgroup (`ExtChain.deltaH2_restriction`).  Together
these reduce the hypothesis of the landing clause to the vanishing of the connecting class of the
*restricted* `E1c` class:

  `akRes_{D_A}(e1aChainC y) = 0  ⟹  δ_{S|D_A}(resH1_{D_A}(e1cEquiv ((e1aSyzShift N)⁻¹ y))) = 0`,

which is the input consumed by the localisation comparison (`PT/NOTE_e1aChainC_localComparison.md`
§11.1).  Both steps are formal and independent of the open comparison square. -/

section ChainReduction

open scoped TensorProduct

/-- **Stripping an equivariant coefficient change from a vanishing restricted class.**  If the
restriction of `mapH2 φ x` to a subgroup `H` vanishes and `φ` is an equivariant additive
*equivalence*, then the restriction of `x` itself vanishes: the restricted coefficient map is
injective (`mapH2_injective_of_addEquiv`).

This is the abstract form of the first reduction of the landing clause: there
`φ = e1aCoeffNat.symm` identifies `Hom_ℤ(E^∨(1),Ωˣ)` with `E` and `x = e1aChainH y`. -/
theorem akRes_eq_zero_of_mapH2_akRes_eq_zero {G : Type} [TopologicalSpace G] [Group G]
    (H : Subgroup G) {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N]
    (φ : M ≃+ N) (hφ : Work.GroupCohomology.IsEquivariant G (φ : M →+ N))
    (hφ' : Work.GroupCohomology.IsEquivariant G (φ.symm : N →+ M))
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.akRes H N (Work.AbsoluteKummer.mapH2 (φ : M →+ N) hφ x) = 0 →
      Work.AbsoluteKummer.akRes H M x = 0 := by
  intro h
  have hφH : Work.GroupCohomology.IsEquivariant ↥H (φ : M →+ N) := fun h' m => hφ (h' : G) m
  have hφH' : Work.GroupCohomology.IsEquivariant ↥H (φ.symm : N →+ M) := fun h' n => hφ' (h' : G) n
  rw [Work.AbsoluteKummer.akRes_mapH2 H (φ : M →+ N) hφ x] at h
  exact Work.SSGRoute.sha2_coeff.mapH2_injective_of_addEquiv φ hφH hφH'
    (by rw [h, map_zero])

/-- The canonical coefficient `E' = DualMod p (E ⊗ T)` of the E1a chain. -/
abbrev e1aN0 (p : ℕ) (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] :
    Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))

/-- **First reduction of the landing hypothesis.**  The vanishing of the continuous restriction of
the canonical chain class `e1aChainC y = e1aCoeffH2 (e1aChainH y)` on a subgroup `D` implies the
vanishing of the continuous restriction of the `Hom`-side chain class `e1aChainH y`: strip the
coefficient change `e1aCoeffH2 = mapH2 (e1aCoeffNat.symm)`. -/
theorem akRes_e1aChainH_eq_zero_of_akRes_e1aChainC_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [_hTfin : Finite T] [hNfin : Finite ↑(e1aN0 p k Ω K T E)]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (y : CategoryTheory.Abelian.Ext.{0} (e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2) :
    @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ D E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      Work.SSGRoute.PT.resH2 D
        (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y) = 0 := by
  intro h
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  have key : Work.AbsoluteKummer.akRes D E (Work.AbsoluteKummer.mapH2
      ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm.toAddMonoidHom)
      (fun σ e =>
        Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ e)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y)) = 0 := h
  have h2 : Work.AbsoluteKummer.akRes D
      (Work.SSGRoute.homCoind k Ω K (e1aN0 p k Ω K T E))
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y) = 0 :=
    akRes_eq_zero_of_mapH2_akRes_eq_zero D
      ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm)
      (fun σ e =>
        Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ e)
      (fun σ e =>
        Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
      _ key
  rw [← akRes_eq_resH2 D (Work.SSGRoute.homCoind k Ω K (e1aN0 p k Ω K T E))
    (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y)]
  exact h2

/-- **Second reduction of the landing hypothesis.**  The vanishing of the continuous restriction of
the `Hom`-side chain class `e1aChainH y = δ (ζ z)`, `z = (e1aSyzShift N)⁻¹ y`, is equivalent to the
vanishing of the connecting class of the *restricted* dualised canonical resolution, evaluated on
the restricted `E1c` class:

  `δ_{S|D}(resH1_D(ζ z)) = 0`   in `H²_c(D, Hom_ℤ(N,Ωˣ))`.

Indeed `e1aChainH y = e1aDelta (ζ z)` unfolds by definition, `akRes = resH2`
(`akRes_eq_resH2`), and the connecting map commutes with restriction to a subgroup
(`ExtChain.deltaH2_restriction`).  No injectivity of the restricted connecting map is needed. -/
theorem deltaH2_restrictSES_e1cEquiv_eq_zero_of_akRes_e1aChainH_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [_hTfin : Finite T] [hNfin : Finite ↑(e1aN0 p k Ω K T E)]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (y : CategoryTheory.Abelian.Ext.{0} (e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2) :
    Work.SSGRoute.PT.resH2 D
        (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y) = 0 →
      (Work.SSGRoute.ExtChain.restrictSES
          (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E)) D).deltaH2
        (Work.SSGRoute.PT.H2Fin.resH1 D
          (Work.SSGRoute.homCoind k Ω K
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (e1aN0 p k Ω K T E))))
          (Work.SSGRoute.ExtChain.e1cEquiv
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (e1aN0 p k Ω K T E)))
              ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) (e1aN0 p k Ω K T E)).symm
                y))) = 0 := by
  intro h
  have h2 : Work.SSGRoute.PT.resH2 D
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y) = 0 := h
  rw [Work.SSGRoute.PT.e1aChainH_apply (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E) y] at h2
  have h3 : Work.SSGRoute.PT.resH2 D
      ((Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E)).deltaH2
        (Work.SSGRoute.ExtChain.e1cEquiv
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (e1aN0 p k Ω K T E)))
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) (e1aN0 p k Ω K T E)).symm
              y))) = 0 := h2
  rw [Work.SSGRoute.ExtChain.deltaH2_restriction
    (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) (e1aN0 p k Ω K T E)) D
    (Work.SSGRoute.ExtChain.e1cEquiv
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (e1aN0 p k Ω K T E)))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) (e1aN0 p k Ω K T E)).symm y))] at h3
  exact h3

/-- **The landing hypothesis, stripped to the `E1c` level.**  For a *closed* subgroup
`D ≤ Gal(Ω/k)`, the hypothesis `akRes_D (e1aChainC y) = 0` implies the vanishing of the restricted
`E1c` class `resH1_D (e1cEquiv ((e1aSyzShift N)⁻¹ y))`.

This is the form consumed by the localisation comparison square (`(★')` of
`PT/NOTE_e1a_square_session10.md`).  The last step uses the injectivity of the connecting map of
the dualised canonical resolution, restricted to `D`: its kernel is
`H¹(D, homCoindFreeT k Ω K N.V)`, which vanishes for closed `D` by the subgroup Hilbert 90
`Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup` (Shapiro at `D ⊓ Gal(Ω/K)` plus Hilbert 90 at
that closed subgroup). -/
theorem resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [_hTfin : Finite T] [hNfin : Finite ↑(e1aN0 p k Ω K T E)]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω)))
    (y : CategoryTheory.Abelian.Ext.{0} (e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2) :
    @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ D E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      Work.SSGRoute.PT.H2Fin.resH1 D
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cEquiv
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (e1aN0 p k Ω K T E)))
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) (e1aN0 p k Ω K T E)).symm
              y)) = 0 := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro hy
  have h1 := akRes_e1aChainH_eq_zero_of_akRes_e1aChainC_eq_zero p k Ω K ζ hζ hζK T hT E D y hy
  have h2 := deltaH2_restrictSES_e1cEquiv_eq_zero_of_akRes_e1aChainH_eq_zero p k Ω K ζ hζ hζK T hT E
    D y h1
  exact Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective' (k := k) (Ω := Ω) (K := K)
    (e1aN0 p k Ω K T E) D hD (by rw [h2, map_zero])

end ChainReduction




/-! ## The continuous hypothesis in the *cocycle* form

`SSGRoute.IsCoboundary2On` asks for a `1`-cochain on the *ambient* group `Ω ≃ₐ[k] Ω` (local
constancy *on* `D`), whereas `B²_c(D)` is about functions on the subgroup `↥D`.  The bridge is
`Work.SSGRoute.exists_isLocConstOn_extension_krull` (the naive extension by `0` of a locally
constant function on a closed subgroup, which is `IsLocConstOn` on it), and it shows that the
vanishing continuous restriction is exactly the cocycle-level hypothesis of
`PT.e1aChainC_localComparison`. -/

section CocycleForm

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **A vanishing continuous restriction is a coboundary on the subgroup, with an ambient
primitive.**  If the restriction of the class of the locally constant `2`-cocycle `c` to a closed
subgroup `D` vanishes, then `c` restricted to `D` satisfies `SSGRoute.IsCoboundary2On (res k K) D`.

Proof: `akRes_H2π` computes the restriction, `H2π_eq_zero_iff` + `mem_B2_iff` produce a *locally
constant* `↥D`-valued primitive, `exists_isLocConstOn_extension_krull` extends it to an ambient
`IsLocConstOn D`-function `b`, and the pointwise clause is `d1_apply`. -/
theorem isCoboundary2On_of_akRes_H2π_eq_zero
    (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω)))
    (c : ↥(@Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)))) :
    @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ D E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) c) = 0 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) D (fun g h => c.1 (g, h)) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro hx
  rw [Work.AbsoluteKummer.akRes_H2π D E c.1 c.2] at hx
  rw [Work.AbsoluteKummer.H2π_eq_zero_iff, Work.AbsoluteKummer.mem_B2_iff] at hx
  obtain ⟨f, hf, hfd⟩ := hx
  obtain ⟨b, hb, hblc⟩ :=
    exists_isLocConstOn_extension_krull (k := k) (Ω := Ω) D hD (f := f) hf
  refine ⟨b, hblc, ?_⟩
  intro g hg h hh
  show c.1 (g, h) = (SSGRoute.res k K) g • b h - b (g * h) + b g
  have h1 : (Work.GroupCohomology.d1 ↥D E) f (⟨g, hg⟩, ⟨h, hh⟩) = c.1 (g, h) :=
    congrFun hfd (⟨g, hg⟩, ⟨h, hh⟩)
  rw [← h1, Work.GroupCohomology.d1_apply]
  rw [hb ⟨h, hh⟩, hb ⟨g * h, D.mul_mem hg hh⟩, hb ⟨g, hg⟩]
  rfl

/-- **The landing clause from the cocycle-level comparison.**  If the per-place comparison
`PT.e1aChainC_localComparison` holds, then so does `e1aLandingFinCompat`: a locally constant
representative of `e1aChainC y` is produced from the surjectivity of `H2π`, and its restriction to
`D_A` is a coboundary by `isCoboundary2On_of_akRes_H2π_eq_zero`
(using `isClosed_decomp`). -/
theorem e1aLandingFinCompat_of_localComparison
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
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (h : ∀ y : CategoryTheory.Abelian.Ext.{0} (e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ c : @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K)) c =
            Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y ∧
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun g h => c.1 (g, h))) →
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
          (SSGRoute.PTExt.extToIdeles (k := k) y) = 0) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (SSGRoute.decomp k A) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro y hy
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 (Ω ≃ₐ[k] Ω) E).comap
      (Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E).subtype)
    (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)
  refine h y ⟨c, ?_, ?_⟩
  · rw [Work.AbsoluteKummer.H2π, hc]
  · rw [← hc] at hy
    exact isCoboundary2On_of_akRes_H2π_eq_zero p K ζ hζ hζK T hT E
      (SSGRoute.decomp k A) (Work.SSGRoute.HS.isClosed_decomp A) c hy

end CocycleForm

/-- **Per-place landing clause, finite place (compatibility form).**

Let `A` be a finite place of `Ω` over `k` whose trace on the finite Galois extension `K/k` is the
prime `q` of `K` (the lying-over condition `hAq`), and let `y ∈ Ext²_{Gal(K/k)}(E^∨(1), Kˣ)`.  If
the canonical chain class `e1aChainC y ∈ H²_c(Gal(Ω/k), E)` is *locally trivial* on the
decomposition group `D_A = decomp k A` — i.e. its continuous restriction `akRes_{D_A}` vanishes —
then the `q`-component of the idèle localisation of `y` vanishes:

  `extLoc_q (extToIdeles y) = 0`  in  `Ext²_{D_q}(E^∨(1), K_qˣ)`.

This is the *finite-place* half of the place-by-place comparison of the canonical chain
(`PT/NOTE_e1aChainC_localComparison.md`), the form consumed by the landing clause
`SSGStage.e1aLandingClause`; the completely split places are
`PT.extLoc_extToIdeles_eq_zero_of_decompK_eq_bot` and the archimedean ones are
`SSGStage.e1aLandingInfLocal`.

The *class-level* localisation comparison `PT.e1aBetaCan_localDictionary_fin_compat` (the target of
the sibling node, whose hypothesis is the abstract restriction
`resH2_{D_A} (akToGCH2 (e1aChainC y)) = 0`) implies this statement, because the continuous vanishing
implies the abstract one (`akRes_eq_zero_imp_resH2_akToGCH2_eq_zero`). -/
theorem e1aLandingFinCompat (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (SSGRoute.decomp k A) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  intro y hy
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  -- (1) the landing hypothesis, stripped to the `E1c` level
  have hz := resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero p k Ω K ζ hζ hζK T hT E
    (SSGRoute.decomp k A) (Work.SSGRoute.HS.isClosed_decomp A) y hy
  -- (2) the localisation comparison square: the restricted `E1c` class controls the localisation
  have hsq := Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero k Ω K
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) A hA q hAq
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm y) hz
  -- (3) the degree reduction of the conclusion
  have hloc := extLoc_extToIdeles_e1aSyzShift_eq_zero K
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (NK.GlobalCFT.Place.ofFinite q)
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm y) hsq
  rw [AddEquiv.apply_symm_apply] at hloc
  exact hloc

end Work.SSGRoute.SSGStage
