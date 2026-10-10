import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.localDuality02
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open Classical

namespace Work.SSGRoute.LTD02Proved

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

noncomputable section

/-- For `x ∈ levelFixSub k Ω A K` the restriction `res k K x` is trivial. -/
theorem res_eq_one_of_mem_levelFixSub
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [Normal k K]
    (A : ValuationSubring Ω) {x : ↥(SSGRoute.decomp k A)}
    (hx : x ∈ Work.SSGRoute.PT.levelFixSub k Ω A K) : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) = 1 := by
  have hfix : (x : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun y hy => (Work.SSGRoute.PT.mem_levelFixSub).mp hx y hy
  have hmem : (x : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
    rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
      IntermediateField.restrictNormalHom_ker]
    exact hfix
  exact MonoidHom.mem_ker.mp hmem

/-- Discreteness passes from a group to a subgroup. -/
theorem isDiscreteModule_subgroup {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
    {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (h : Work.AbsoluteKummer.IsDiscreteModule G M) :
    Work.AbsoluteKummer.IsDiscreteModule ↥U M := by
  intro m
  have hset : (MulAction.stabilizer ↥U m : Set ↥U)
      = Subtype.val ⁻¹' ((MulAction.stabilizer G m) : Set G) := by
    ext u
    exact Iff.rfl
  rw [hset]
  exact (h m).preimage continuous_subtype_val

/-- **Milne's first pass.**  For an open finite-index subgroup `U ≤ G` acting trivially on a finite
`𝔽_p`-module `N`, the map `α²(G,N)` is *surjective* as soon as the base case at `U` holds and the
corestriction is bijective on the `p`-torsion of `H²(·,C)`.

This is the first of the two passes of the dévissage of Milne, *Arithmetic Duality Theorems*,
Theorem I.1.8: it is what makes the "quotient" input `hN₁` of
`Work.SSGRoute.PT.alphaTwo_bijective_of_devissage` available for an arbitrary coefficient module. -/
theorem alphaTwo_surjective_of_hcor
    (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N]
    (hc : Function.Bijective (fun z : {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} =>
      (⟨Work.SSGRoute.PT.corH2 U hUo C z.1, by rw [← map_nsmul, z.2, map_zero]⟩ :
        {x : Work.AbsoluteKummer.H2 G C // p • x = 0})))
    (hNp : ∀ n : N, p • n = 0)
    (htriv : ∀ (u : ↥U) (n : N), u • n = n)
    (hbaseU : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := U) (N := N) (C := C))) :
    Function.Surjective (Work.SSGRoute.PT.alphaTwo (G := G) (N := N) (C := C)) := by
  classical
  let ι : N →+ Work.SSGRoute.PT.Coind G U N := Work.SSGRoute.PT.devissageIota (M := N) U
  have hι : Work.GroupCohomology.IsEquivariant G ι :=
    Work.SSGRoute.PT.devissageIota_equivariant (M := N) U
  have hpreι : Work.GroupCohomology.IsEquivariant G
      (Work.SSGRoute.PT.ConjHom.precomp (C := C) ι) :=
    Work.SSGRoute.PTUr.ptu_isEquivariant_conjHom_precomp ι hι
  obtain ⟨r, hr⟩ := Work.SSGRoute.PT.retraction_invariantsHom (p := p) (G := G)
    (N₁ := N) (N₂ := Work.SSGRoute.PT.Coind G U N) (φ := ι) (hφ := hι)
    (Work.SSGRoute.PT.devissageIota_injective (M := N) U)
  have hg' := Work.SSGRoute.PT.mkb_precompHom_surjective_of_retraction
    (X := Work.AbsoluteKummer.H2 G C) (Work.SSGRoute.PT.invariantsHom ι hι) r hr
  have hcoind := Work.SSGRoute.PT.mkb_alphaTwo_coind_bijective (p := p) (G := G) U hUo
    hc hNp hbaseU
  exact Work.SSGRoute.PT.alphaTwo_surjective_of_precomp
    (N₁ := N) (N₂ := Work.SSGRoute.PT.Coind G U N) ι hι hpreι hcoind.2 hg'

/-- **The target from the `α²`-bijectivity.**  Tate duality in degrees `0` and `2` at a finite
place follows from the bijectivity of the local cup-product map `α²` at `D_A` with coefficients in
the Tate dual `N = M^∨(1)`, by `Work.SSGRoute.PT.finrank_eq_of_alphaTwo_bijective` (Milne, *ADT*,
Theorem I.1.8 at `r = 2`) together with the equivariant double-Tate-twist
(`Work.SSGRoute.PT.localDuality02_of_core`). -/
theorem target_from_alphaTwo
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (h : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        [instN : DistribMulAction ↥(SSGRoute.decomp k A)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))],
        (hpinN : instN = SSGRoute.decompDistribMulAction K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A) →
        Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥(SSGRoute.decomp k A))
          (N := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (C := Additive (Units Ω)))) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) := by
  refine Work.SSGRoute.PT.localDuality02_of_core p k Ω K ζ hζ hζK T hT ?_
  intro A hA M _ _ _ _ _
  letI : DistribMulAction ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    SSGRoute.decompDistribMulAction K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A
  exact Work.SSGRoute.PT.finrank_eq_of_alphaTwo_bijective p k Ω K ζ hζ hζK T hT A hA M
    (instN := _) (hpinN := rfl) (h := h A hA M (instN := _) (hpinN := rfl))


end

end Work.SSGRoute.LTD02Proved
