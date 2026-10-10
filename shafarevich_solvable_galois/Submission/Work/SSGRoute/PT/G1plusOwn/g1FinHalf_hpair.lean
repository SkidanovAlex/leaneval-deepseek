import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.decomp_injective_of_finPlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct
open Work.SSGRoute.PT.G1pOwn

set_option maxHeartbeats 200000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **`finAtLevel` depends on the finite place only through its value.**  Two equal places `A = A'`
give the same value, the auxiliary data (`hA`, the cocycle witnesses and the factorisation `hb₀`)
being proof-irrelevant. -/
theorem finAtLevel_eq_of_place_eq
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A A' : ValuationSubring Ω) (h : A = A')
    (hA : SSGRoute.IsFinPlace k A) (hA' : SSGRoute.IsFinPlace k A')
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A') b)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A', b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    Work.SSGRoute.PT.finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀
      = Work.SSGRoute.PT.finAtLevel p k Ω K ζ hζ hζK T hT χ M A' hA' L hKL a b hb' b₀ hb₀' := by
  subst h
  rfl

/-- The interface supply for `G1⁺`'s clause (4): the `hpair` level-value formula for
`pair := G1pOwn.g1FinHalf χ M` and `βl := PT.finZB`.

Route (lead's v4 note).  Unfold `g1FinHalf` through its two guards (`g1FinHalf_eq_of_guard`), which
evaluates it at the place `h.choose` of the guard, a finite place with `decomp k A = decomp k
h.choose`; `decomp_injective_of_finPlace` identifies that place with `A`.  Then
`PT.finAtValue_eq_finAtLevel` (which needs the inflation-coherence `hχcompat`) and
`PT.finAtLevel_eq_of_le` move the value to the prescribed level `L` (with the prescribed
factorisation `b₀`), and the definition of `finAtLevel`/`finZZ` gives the stated right-hand side
with `finZB` as the dictionary.

Two bookkeeping points.

* The `Classical.choose`d place of `g1FinHalf`'s guard is not syntactically `A`, so after the two
  value rewrites the level data are those of `hw.choose`; `finAtLevel_eq_of_place_eq` (above) moves
  them to `A` using `decomp_injective_of_finPlace`.
* The right-hand side carries the ambient `Algebra ↥K ↥L`-instance, whereas `finAtLevel`'s body uses
  the canonical `(IntermediateField.inclusion hKL).toAlgebra`.  These are *propositionally* equal
  (`hinst` below): `IsScalarTower ↥K ↥L Ω` pins the algebra map `↥K → ↥L` down to the inclusion, so
  `Algebra.algebra_ext` applies.  `cases` on that equality makes the two sides of the unfolded goal
  syntactically identical (`rfl`) -- no transport of `finZI`/`finZH` is needed. -/
theorem g1FinHalf_hpair
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b =
      χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
          (Work.SSGRoute.PT.finZI hKL A hA)
          (Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA a)
          (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))) := by
  classical
  -- the ambient `Algebra ↥K ↥L` instance equals the canonical one: `IsScalarTower ↥K ↥L Ω` forces
  -- the algebra map `↥K → ↥L` to be the inclusion (`Algebra.algebra_ext` + the tower law)
  have hinst : (IntermediateField.inclusion hKL).toAlgebra = (inferInstance : Algebra ↥K ↥L) := by
    refine Algebra.algebra_ext _ _ (fun x => Subtype.ext ?_)
    exact IsScalarTower.algebraMap_apply ↥K ↥L Ω (x := x)
  -- the guard witness: the finite place `A` itself
  let hw : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A = SSGRoute.decomp k A' := ⟨A, hA, rfl⟩
  have hA' : SSGRoute.IsFinPlace k hw.choose := hw.choose_spec.1
  have hH : SSGRoute.decomp k A = SSGRoute.decomp k hw.choose := hw.choose_spec.2
  have hbc' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k hw.choose) b := hH ▸ hb
  have hb₀' : ∀ σ ∈ SSGRoute.decomp k hw.choose, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) :=
    fun σ hσ => hb₀ σ (hH.symm ▸ hσ)
  -- unfold `g1FinHalf` through its two guards and move the value to the prescribed level `L`
  rw [g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b hw ⟨hla, hlb⟩,
      finAtValue_eq_finAtLevel p k Ω K ζ hζ hζK T hT χ hχcompat M hw.choose hA' a b
        (hw.choose_spec.2 ▸ hla) (hw.choose_spec.2 ▸ hlb) hbc' L hKL b₀ hb₀']
  -- identify the `Classical.choose`d place `hw.choose` with `A`
  rw [finAtLevel_eq_of_place_eq p k Ω K ζ hζ hζK T hT χ M hw.choose A
        (SSGRoute.decomp_injective_of_finPlace hA' hA hH.symm) hA' hA a b hbc' hb L hKL b₀ hb₀' hb₀]
  -- the definition of `finAtLevel`/`finZZ` gives the right-hand side, at the canonical instance
  simp only [Work.SSGRoute.PT.finAtLevel, Work.SSGRoute.PT.finZZ]
  -- rewrite the ambient instance to the canonical one on the right-hand side
  cases hinst
  rfl

/-- **The `letI` form of the value formula**, derived from the binder form above by instantiating it
at the canonical instances.  This is the shape the *abstract* clause (4)/(6)/(7) interfaces use
(`G1plusOwn/pairLevelLeft.lean`, `G1plusOwn/unramifiedPairClause.lean`,
`G1plusOwn/reciprocityFiniteClause.lean`): their `hpair` hypothesis binds the level data's
`Algebra ↥K ↥L`-family by `letI`, and the `let`s instantiate to exactly the terms of the canonical
instances, so the binder form specialises to it definitionally. -/
theorem g1FinHalf_hpair_letI
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
    letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b =
      χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
          (Work.SSGRoute.PT.finZI hKL A hA)
          (Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA a)
          (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))) := by
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA a b hla hlb hb L hKL b₀ hb₀

end Work.SSGRoute.PT.G1plusOwn
