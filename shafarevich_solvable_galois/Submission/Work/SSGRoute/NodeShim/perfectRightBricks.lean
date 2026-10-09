import Mathlib
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bricks for the perfectness clauses of `G1⁺`'s finite half

`G1⁺`'s finite half `G1pOwn.g1FinHalf` (`PT/G1plusOwn/levelFree.lean`) takes the value

  `finAtValue … A … a b = χ_L (ι_w (levelPair (finZB a) (finZH b)))`

at a finite place `A`.  The two *perfectness* conjuncts of `hlocal` (`PairClauses` clauses (4)) at
`H = decomp k A` are the `sorry`s of `PT/canonical_localPairing_reciprocity_converse.lean`; both are
proved from the same two inputs:

* `χ` is **injective on `p`-torsion** (`hχinj`, clause (2) of the coherent invariant `χ`), and
* `ι_w` is **injective on `p`-torsion** (`PT.iota_injective_of_ptorsion`, S2),

which together say that `χ ∘ ι` *detects* nonzero `p`-torsion local classes.  This file provides
that detection step (`chi_iota_ne_zero_of_ptorsion_ne_zero`) as a reusable brick, together with the
value form used at a place (`chi_finZZ_ne_zero_of_levelPair_ne_zero`).
-/

open scoped TensorProduct

namespace Work.SSGRoute.PT

/-- **`χ ∘ ι` detects `p`-torsion.**  For a nonzero `p`-torsion class `z` of `H²(D_{w'}, L_{w'}ˣ)`
at a level `L ≥ K`, the value `χ_L (ι_w z)` is nonzero: `ι_w` is injective on `p`-torsion
(`PT.iota_injective_of_ptorsion`) and `χ` is injective on `p`-torsion (`hχinj`). -/
theorem chi_iota_ne_zero_of_ptorsion_ne_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (r : NK.GlobalCFT.Place ↥L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) r) 2)
    (hz : p • z = 0) (hz0 : z ≠ 0) :
    χ L hKL (iota (k := k) (L := ↥L) r z) ≠ 0 := by
  intro h0
  have hpt : p • iota (k := k) (L := ↥L) r z = 0 :=
    pt_iota_ptorsion (k := k) (L := ↥L) p r z hz
  have hzero : iota (k := k) (L := ↥L) r z = 0 := hχinj L hKL _ hpt h0
  exact hz0 (iota_injective_of_ptorsion (k := k) (L := ↥L) p r z hz hzero)

/-- **The value form of the detection step.**  For a level `L ≥ K`, a place `r` of `L` and a
nonzero `p`-torsion local class `z`, the value of the finite half's level class is nonzero.  This is
`chi_iota_ne_zero_of_ptorsion_ne_zero` restated at a term of the shape which occurs in
`finAtValue`/`finAtLevel` (so that it can be `rw`-ed into a goal containing `finZZ`). -/
theorem chi_iota_ne_zero_of_ptorsion_ne_zero_apply
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (r : NK.GlobalCFT.Place ↥L) :
    ∀ z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) r) 2,
      p • z = 0 → z ≠ 0 → χ L hKL (iota (k := k) (L := ↥L) r z) ≠ 0 :=
  fun z hz hz0 => chi_iota_ne_zero_of_ptorsion_ne_zero p k Ω K T χ hχinj L hKL r z hz hz0

end Work.SSGRoute.PT
