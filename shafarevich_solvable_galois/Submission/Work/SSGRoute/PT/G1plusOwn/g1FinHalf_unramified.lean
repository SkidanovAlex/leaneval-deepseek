import Mathlib
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.E1aClean.natFamilyClauses
import Submission.Work.SSGRoute.PT.levelPair_unramified_eq_zero
import Submission.Work.SSGRoute.ZConstruction.levelK_completion_iso_of_localGroup_eq
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_unramified_level_factors
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

/-- Clause (6) of the finite-place pairing: two local cocycles vanishing on inertia at a good place
(not over `p`, unramified in `K`) pair to zero.

Route.  `b` vanishes on the inertia `I_A` and `A` is unramified in `K`
(`hramA : ¬ SSGRoute.IsRamifiedIn k K A` unfolds to `I_A ⊆ K.fixingSubgroup`), so `b` factors
through the Galois group of a finite Galois level `L ≥ K` which has **trivial inertia** at the prime
`finQW L A hA` below `A`: this is
`Work.SSGRoute.PT.G1plusOwn.exists_unramified_level_factors`, the arithmetic input of the clause
(its docstring records the two routes; the point is that the constancy subgroup of `b` can be
enlarged by `I_A`, on which `b` vanishes).

* `hpair` evaluated at that level `L` writes `pair (decomp k A) a b` as
  `χ L hKL (iota (finQW L A hA) (levelPair (finZF hKL A hA) (finZI hKL A hA) (βl A hA a)
  (finZH … b …)))`;
* `hβl_unr` makes `βl A hA a` unramified at the base place `finQ K A hA`
  (`a` vanishes on `I_A` by `hiner`);
* with `hunr` (the level is unramified), `PT.levelPair_unramified_eq_zero` (Herbrand: `H²` of the
  units of an unramified local extension vanishes) gives the level pairing `0`;
* `iota 0 = 0` (`PT.iota_zero`) and `χ 0 = 0` follows from `hχadd` (`χ (0 + 0) = χ 0 + χ 0`).

Interface (v4_0215): the local dictionary `βl` and the pairing `pair` are variables with their
clauses `hβl_*` and the level-value formula `hpair`; the declared name and the conclusion are
unchanged. -/
theorem g1FinHalf_unramified (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) :
    pair (SSGRoute.decomp k A) a b = 0 := by
  classical
  -- ## a finite Galois level `L ≥ K`, unramified at `A`, on which `b` factors
  obtain ⟨L, hLnf, hLfd, hLgal, hKL, hunr, b₀, hb₀⟩ :=
    exists_unramified_level_factors p k Ω K T M A hA hramA b hb.1 hb.2
      (fun σ hσ => (hiner σ hσ).2)
  letI : NumberField ↥L := hLnf
  letI : FiniteDimensional k L := hLfd
  letI : IsGalois k L := hLgal
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## the value formula at that level
  rw [hpair A hA a b ha.2 hb.2 hb.1 L hKL b₀ hb₀]
  -- ## the level pairing vanishes: `βl A hA a` is unramified, and so is the level at `A`
  have hz : SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
      (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
      (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb.1 b₀ hb₀) = 0 := by
    have hw' : NK.GlobalCFT.Place.LiesOver
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) :=
      (Work.SSGRoute.PT.place_glue_level k Ω K L hKL A hA (Work.SSGRoute.PT.finQ K A hA)
        (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
        (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)).1
    refine Work.SSGRoute.PT.levelPair_unramified_eq_zero (k := k) (K := ↥K)
      (M := SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
      (w := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (L := ↥L)
      (q' := Work.SSGRoute.PT.finQW L A hA) (hw' := hw') (hunr := hunr)
      (f := Work.SSGRoute.PT.finZF hKL A hA) (hf := Work.SSGRoute.PT.finZF_spec hKL A hA)
      (ι := Work.SSGRoute.PT.finZI hKL A hA) ?_
      (y := βl A hA a)
      (hy := hβl_unr A hA hpA hramA a ha.1 ha.2 (fun σ hσ => (hiner σ hσ).1))
      (h := Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb.1 b₀ hb₀)
    -- ## `finZI` is the canonical local embedding of unit groups
    intro u
    simp only [Work.SSGRoute.PT.finZI]
    exact Work.SSGRoute.PT.localUnitsMapAt_spec k ↥K ↥L
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) hw'
      (Work.SSGRoute.PT.finZF hKL A hA) (Work.SSGRoute.PT.finZF_spec hKL A hA) u
  rw [hz, Work.SSGRoute.PT.iota_zero]
  -- ## `χ 0 = 0`, from the additivity clause
  have hχ0 : χ L hKL (0 : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) = 0 := by
    have h := hχadd L hKL 0 0 (by simp) (by simp)
    rw [add_zero] at h
    have h2 : χ L hKL 0 + χ L hKL 0 = χ L hKL 0 + 0 := by rw [h.symm, add_zero]
    exact add_left_cancel h2
  exact hχ0

end Work.SSGRoute.PT.G1plusOwn
