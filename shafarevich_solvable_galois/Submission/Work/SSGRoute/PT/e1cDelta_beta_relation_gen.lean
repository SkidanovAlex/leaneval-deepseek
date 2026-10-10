import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1cGeneric.Canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The field-generic δ-form of the `E1c` dictionary

`Submission/Work/SSGRoute/PT/e1cDelta_beta_relation.lean` proves, for a *number field* `k`, the two
facts

* `betaEquiv_e1aE1cDelta`: `betaEquiv V ((e1aSES V).delta x) = mk' x` for
  `x ∈ H⁰(Γ, Hom_ℤ(R,Ωˣ))`, `R = E1cR1 V`, and
* `e1cMap_PhiE_eq_delta`: `e1cMap V (PhiE V y) = (e1aSES V).delta (PsiEMap (E1cR1 V) y)`,

where `e1aSES V` is the dualised canonical resolution `0 → Hom(V,Ωˣ) → Hom(F,Ωˣ) → Hom(R,Ωˣ) → 0`
of `ExtChain/ChainGamma.lean`.  Both proofs use only the *pointwise* form of the two structural
rules of `e1aSES` (`iota`/`pi` are the precompositions by the canonical cover and its kernel), and
the generic material already present in `E1cGeneric/Canonical.lean`
(`betaEquiv`, `betaH`, `liftOf`, `d0_eq_zero_iff`, `iotaH`, `piH`, `e1cMap`, `PhiE`, `PsiEMap`).

The present module replays them with the number-field hypotheses dropped, using the field-generic
short exact sequence `e1aSESgen` produced by `PT.homCoind_SES` (which is stated with `[CharZero k]`).
This is what makes the δ-form available at a *local* field, where the dictionary is needed:
`(L, M, K') = (localFieldAt k A hA, localClosureAt k A hA, K')` is not a number field.
-/

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **The field-generic dualised canonical resolution**
`0 → Hom_ℤ(V,Ωˣ) → Hom_ℤ(F_V,Ωˣ) → Hom_ℤ(R_V,Ωˣ) → 0`, the generic form of
`ExtChain.e1aSES`. -/
noncomputable def e1aSESgen (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V] :
    Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K V)
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K V.V)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover V))) :=
  Classical.choose (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K) (ι := V.V)
    (Work.SSGRoute.freeCover V) (Work.SSGRoute.freeCover_surjective V))

/-- The `iota` of `e1aSESgen` is the precomposition by the canonical cover. -/
theorem e1aSESgen_iota (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V] :
    (e1aSESgen (k := k) (Ω := Ω) (K := K) V).iota =
      Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (Work.SSGRoute.freeCover V)).toAddMonoidHom :=
  (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
    (ι := V.V) (Work.SSGRoute.freeCover V)
    (Work.SSGRoute.freeCover_surjective V))).1

/-- The `pi` of `e1aSESgen` is the precomposition by the kernel inclusion. -/
theorem e1aSESgen_pi (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V] :
    (e1aSESgen (k := k) (Ω := Ω) (K := K) V).pi =
      Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover V))).toAddMonoidHom :=
  (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
    (ι := V.V) (Work.SSGRoute.freeCover V)
    (Work.SSGRoute.freeCover_surjective V))).2

/-- The `ι` of `e1aSESgen` is `E1cGeneric.iotaH` (pointwise form; the `AddMonoidHom`-level
statement does not elaborate because of the two `AddCommGroup` instances on `homCoindFreeT`). -/
theorem e1aSESgen_iota_apply_eq_iotaH (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V]
    (x : Work.SSGRoute.homCoind k Ω K V) :
    (e1aSESgen (k := k) (Ω := Ω) (K := K) V).iota x
      = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) V x := by
  rw [e1aSESgen_iota]
  rfl

/-- The `π` of `e1aSESgen` is `E1cGeneric.piH` (pointwise form). -/
theorem e1aSESgen_pi_apply_eq_piH (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V]
    (x : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V) :
    (e1aSESgen (k := k) (Ω := Ω) (K := K) V).pi x
      = Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) V x := by
  rw [e1aSESgen_pi]
  rfl

/-- **The β-dictionary is the δ-dictionary** (field-generic form).  For
`x ∈ H⁰(Γ, Hom_ℤ(R,Ωˣ))`, `R = E1cR1 V`, the pull-back map `betaEquiv V` sends the connecting image
`(e1aSESgen V).delta x` to the class of `x` in `cokerH V`. -/
theorem betaEquiv_e1aSESgen_delta (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V]
    [Module.Finite ℤ V.V]
    (x : Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) V))) :
    Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv (k := k) (Ω := Ω) (K := K) V
        ((e1aSESgen (k := k) (Ω := Ω) (K := K) V).delta x) =
      QuotientAddGroup.mk'
        (Work.SSGRoute.ExtChain.E1cGeneric.piH0 (k := k) (Ω := Ω) (K := K) V).range x := by
  classical
  set S := e1aSESgen (k := k) (Ω := Ω) (K := K) V with hS
  set c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K V)) :=
    S.cocycleOf (S.liftOf x) (S.liftOf_invariant x) with hc
  have hdelta : (e1aSESgen (k := k) (Ω := Ω) (K := K) V).delta x
      = QuotientAddGroup.mk'
          ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K V)).comap
            (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K V)).subtype) c := by
    rw [Work.AbsoluteKummer.ShortExactSeq.delta_apply, Work.AbsoluteKummer.H1π]
  rw [hdelta, Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv_apply,
    Work.SSGRoute.ExtChain.E1cGeneric.betaH_mk]
  set n : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V :=
    Work.SSGRoute.ExtChain.E1cGeneric.liftOf (k := k) (Ω := Ω) (K := K) V c with hn
  set n₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V :=
    S.liftOf x with hn₀
  have hd0 : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V) (n - n₀) = 0 := by
    funext g
    have h1 : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V) n g
        = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) V
            ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K V) g) := by
      rw [congrFun
        (Work.SSGRoute.ExtChain.E1cGeneric.liftOf_spec (k := k) (Ω := Ω) (K := K) V c) g,
        Work.AbsoluteKummer.mapZ1_apply]
    have h2 : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V) n₀ g
        = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) V
            ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K V) g) := by
      rw [hn₀, Work.GroupCohomology.d0_apply,
        ← Work.AbsoluteKummer.ShortExactSeq.iota_cocycleOf (S := S) (n := S.liftOf x)
          (hn := S.liftOf_invariant x) g]
      exact e1aSESgen_iota_apply_eq_iotaH (k := k) (Ω := Ω) (K := K) V _
    rw [map_sub, Pi.sub_apply, h1, h2]
    exact sub_self _
  have hmem : (n - n₀) ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V) :=
    (Work.SSGRoute.ExtChain.E1cGeneric.d0_eq_zero_iff
      (M := Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) V)
      (n - n₀)).mp hd0
  have hpin : Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) V n₀
      = (x : Work.SSGRoute.homCoind k Ω K
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) V)) := by
    rw [hn₀]
    exact (e1aSESgen_pi_apply_eq_piH (k := k) (Ω := Ω) (K := K) V (S.liftOf x)).symm.trans
      (Work.AbsoluteKummer.ShortExactSeq.pi_liftOf S x)
  refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
  refine ⟨⟨n - n₀, hmem⟩, ?_⟩
  apply Subtype.ext
  show Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) V (n - n₀)
    = Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) V n
      - (x : Work.SSGRoute.homCoind k Ω K
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) V))
  rw [map_sub, hpin]

/-- **The δ-form of the `E1c` dictionary** (field-generic form).  On the `PhiE`-generators the
`E1c` dictionary is the connecting map of the generic dualised canonical resolution applied to the
coefficient identification:

    e1cMap V (PhiE V y) = (e1aSESgen V).delta (PsiEMap (E1cR1 V) y). -/
theorem e1cMap_PhiE_eq_delta_gen (V : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V]
    [Module.Finite ℤ V.V]
    (y : CategoryTheory.Abelian.Ext
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) V)
      (SSGRoute.PTExt.unitsK k K) 0) :
    Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) V
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) V y)
      = (e1aSESgen (k := k) (Ω := Ω) (K := K) V).delta
          (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) V) y) := by
  rw [Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_Phi]
  refine (AddEquiv.symm_apply_eq _).mpr ?_
  rw [betaEquiv_e1aSESgen_delta]

end

end Work.SSGRoute.PT
