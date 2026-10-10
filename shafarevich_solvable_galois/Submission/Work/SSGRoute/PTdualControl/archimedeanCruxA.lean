import Mathlib.FieldTheory.KrullTopology
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTdualControl.archimedeanLocalPush
import Submission.Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
import Submission.Work.SSGRoute.PTdualControl.glue_infinite_place_with_link
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **The converse of `resH1_e1cMap_eq_zero_of_extension`.**

If the restricted `E1c` class of a `PhiE`-generator vanishes on a subgroup `D`, then the
`Kˣ`-valued coefficient data `(ΨE y)(x)` extends to a `D`-equivariant `Ωˣ`-valued map on the
canonical cover `F = Rep.free Coeff Gal(K/k) R.V`.

This is the `⟹` direction of the "sharp per-place form": for `D = ⟨σ⟩` with
`⟨σ⟩ ∩ Gal(Ω/K) = 1` the relevant coefficient field is `Ω´ = K·Ω^D = Ω`, so that the extension
into `Ωˣ` is exactly `cc_{K·Ω^D}(res_D z) = 0` (cf. `ExtChain/NOTE_himg_status_session11.md` §2(b)
and session 13's sharpening).  Proof: `e1cMap_PhiE_eq_delta_gen` writes the class as `δ(ΨE y)`;
`delta_restrictSES` computes its restriction as the connecting map of the restricted dualised
resolution; exactness at `H⁰` (`SES.ker_le_range_mapH0`) then produces the invariant lift `Φ`. -/
theorem exists_extension_of_resH1_e1cMap_PhiE_eq_zero
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V] [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (y : CategoryTheory.Abelian.Ext (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)
      (SSGRoute.PTExt.unitsK k K) 0)
    (h : Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE R y)) = 0) :
    ∃ Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R,
      Φ ∈ Work.AbsoluteKummer.H0 ↥D
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R) ∧
      Φ.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa R)
        = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1 := by
  set Ψ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R))) :=
    Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y with hΨ
  rw [Work.SSGRoute.PT.e1cMap_PhiE_eq_delta_gen R y] at h
  have hker : (⟨(Ψ : Work.SSGRoute.homCoind k Ω K
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)),
        fun u => Ψ.2 (u : Ω ≃ₐ[k] Ω)⟩ :
      ↥(Work.AbsoluteKummer.H0 ↥D (Work.SSGRoute.homCoind k Ω K
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R))))
      ∈ (Work.SSGRoute.ExtChain.restrictSES
          (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R) D).delta.ker := by
    rw [AddMonoidHom.mem_ker]
    rw [← Work.SSGRoute.PT.delta_restrictSES
      (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R) D Ψ]
    exact h
  obtain ⟨Φ, hΦ⟩ := AddMonoidHom.mem_range.mp
    (Work.AbsoluteKummer.SES.ker_le_range_mapH0
      (Work.SSGRoute.ExtChain.restrictSES
        (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R) D) hker)
  refine ⟨(Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R), Φ.2, ?_⟩
  have h2 : (Work.SSGRoute.ExtChain.restrictSES
        (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R) D).pi
        (Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R)
      = (Ψ : Work.SSGRoute.homCoind k Ω K
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)) := by
    have hh := congrArg Subtype.val hΦ
    simpa [Work.GroupCohomology.mapH0] using hh
  rw [show (Work.SSGRoute.ExtChain.restrictSES
        (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R) D).pi
      = (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R).pi from rfl,
    Work.SSGRoute.PT.e1aSESgen_pi] at h2
  simpa only [Work.SSGRoute.precompAddHom_apply,
    Work.SSGRoute.ExtChain.E1cGeneric.kappa] using h2


end

/-- **The degenerate case `D_w = ⊥` of the crux.**  If the decomposition group of the infinite
place is trivial, then `Local_{D_w}` is `Ext¹` over the trivial group with first argument the
syzygy `Res R₀`; shifting along the restricted free-cover resolution (`Res (freeCoverSES N)`,
whose middle term is projective) identifies it with `Ext²_{⊥}(Res N, K_wˣ)`, which is a
subsingleton by `PT.subsingleton_ext2_of_subsingleton` (`N` is finite). -/
theorem extRes_comp_eq_zero_of_decompK_eq_bot
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (w : NumberField.InfinitePlace ↥K)
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [hRfin : Module.Finite ℤ
      ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hbot : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) = ⊥) :
    (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)).subtype z).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w)))
      (add_zero 1) = 0 := by
  rw [← Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq (k := k) (K := ↥K)
    (NK.GlobalCFT.Place.ofInfinite w) z]
  haveI hfinN : Module.Finite ℤ N.V := Work.SSGRoute.PT.module_finite_int_of_finite N
  haveI : Subsingleton (↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite w))) := by
    rw [hbot]; infer_instance
  haveI hSproj : CategoryTheory.Projective
      ((Work.SSGRoute.freeCoverSES N).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
          (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype)).X₂ :=
    Functor.projective_obj
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype)
      (Work.SSGRoute.freeCoverSES N).X₂
  haveI hS : ((Work.SSGRoute.freeCoverSES N).map
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype)).ShortExact :=
    (Work.SSGRoute.freeCoverSES_shortExact N).map_of_exact
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype)
  haveI hfinX : Module.Finite ℤ
      (((Work.SSGRoute.freeCoverSES N).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
          (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype)).X₃).V := hfinN
  haveI hsub2 : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (((Work.SSGRoute.freeCoverSES N).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
          (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype)).X₃)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w)) 2) :=
    Work.SSGRoute.PT.subsingleton_ext2_of_subsingleton _ _
  haveI hsub1 : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w)) 1) :=
    ⟨fun a b => (Work.SSGRoute.PT.e1aShiftEquiv
        ((Work.SSGRoute.freeCoverSES N).map
          (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
            (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofInfinite w)).subtype)) hS
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)) 1 le_rfl).injective
      (Subsingleton.elim _ _)⟩
  exact Subsingleton.elim _ _


set_option maxHeartbeats 1000000 in
/-- **The archimedean instance of the `E1a` crux, with the seam clause (corrected statement).**

This is `Work.SSGRoute.PTdualControl.ArchimedeanCruxA` with its hypotheses, and it is the *single*
missing arithmetic input of the archimedean half of node `E1a`: by the proved, axiom-clean
`Work.SSGRoute.PTdualControl.e1aLandingInfLocal_via_cruxA` /
`archimedeanLocalDictionary_via_cruxA` it implies `SSGStage.archimedeanLocalDictionary` and the
`akRes` form of `SSGStage.e1aLandingInfLocal`, and — together with the finite crux — the whole of
leaf 5 `Work.SSGRoute.PT.e1aBetaCan_le_ker` (`e1aBetaCan_le_ker_via_cruxA`).

An earlier version of this statement (filed at this same path) omitted the **seam clause** `hlink`;
a delegated prover **declared it false**, with the analysis that the crux is equivalent to "a lift of
`(ΨE y)|_H` along `κ` with values in `Ωˣ` implies a lift of the local datum along `κ` with values in
`K_wˣ`", which needs the coefficient change `Ωˣ → K_wˣ` induced by the completion to be
`⟨σ⟩`-equivariant.  That is exactly `hlink` — the archimedean analogue of the lying-over clause
`hAq` of the finite-place crux `PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero` (without it,
e.g. for `k = ℚ(√2)`, `K = ℚ(ζ₈)`, the involution belonging to the *other* real place of `k`
satisfies `hσ` and `hle` but not the conclusion).  The pair `(σ, hlink)` is supplied by the
delegated `PTdualControl.glue_infinite_place_with_link` (a verbatim re-exposure of data already
constructed in the proof of `SSGRoute.glue_infinite_place`).

Proved inputs around it: `SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero`,
`SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero` (brick (F)),
`PTdualControl.decompK_zpowers_iso`, `PTdualControl.T_trivial_p2`, `PTdualControl.coeffEquiv_p2`,
`SSGStage.archimedeanExt2Subsingleton` (for `p ≠ 2`, when the target `Ext²` is a subsingleton),
`Work.SSGRoute.ext_two_iso_divisible_cohomology` (the divisible-coefficient dictionary), and the
finite-place local-data machinery `E1aClean.exists_localData`, `E1cGeneric.coeffChange`,
`E1cGeneric.localModuleMap`, whose archimedean instantiation (local field `ℝ`, local closure `ℂ`,
seam `Ω →+* ℂ`) is the intended route.  Only `p = 2` matters (`archimedeanLocalDictionary_odd`
handles odd `p` unconditionally). -/
theorem archimedeanCruxA (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hlink : (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
      = NumberField.ComplexEmbedding.conjugate
          (NumberField.ComplexEmbedding.lift Ω w.embedding))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K)) :
    Work.SSGRoute.PTdualControl.ArchimedeanCruxA p k Ω K ζ hζ hζK T hT E w σ hσ hlink hle := by
  intro N hN hRfin z h
  haveI : Finite N.V := hN
  haveI : Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V := hRfin
  by_cases hbot : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) = ⊥
  · exact extRes_comp_eq_zero_of_decompK_eq_bot (k := k) (Ω := Ω) K w N z hbot
  · haveI hFintypeG : Fintype (K ≃ₐ[k] K) := inferInstance
    haveI hFintypeD : Fintype ↥(SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)) := Fintype.ofFinite _
    obtain ⟨y, hy⟩ := Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K)
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z
    rw [← hy] at h ⊢
    obtain ⟨Φ, hΦ, hκ⟩ :=
      exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (Subgroup.zpowers σ) y h
    obtain ⟨Φ₁, hΦ₁⟩ := archimedeanLocalPush k Ω K w σ hσ hlink hle hbot
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) y Φ hΦ hκ
    refine Work.SSGRoute.E1aClean.extRes_PhiEgen_comp_mk₀_eq_zero
      (f := (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype)
      (M := CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
      (R := SSGRoute.PTExt.unitsK k K)
      (Z := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w))
      (ι := NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w))
      (w := y) (φ := Φ₁) ?_
    intro r
    exact hΦ₁ r

end Work.SSGRoute.PTdualControl
