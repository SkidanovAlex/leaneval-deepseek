import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.NK.GlobalCFTdeep.NormIndex.GaloisCase

/-!
# The norm index of a finite extension of number fields is finite

This file proves `NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero`: for a finite extension
`L / K` of number fields, `C[K] ⧸ N_{L/K} C[L]` is finite.  The proof has two steps:

* the finite **Galois** case (`NormIndex.index_ne_zero_of_isGalois`), by the elementary idèlic
  argument: a finite set `S` of places, local norm subgroups at the places of `S`, and the
  restricted-product computation of the index;
* the reduction of the general finite case to the Galois case: pass to the Galois closure
  `M = normalClosure K L (AlgebraicClosure L)` of `L / K`, which is finite Galois over `K`
  (and contains `L`), and use `N_{M/K} C_M ≤ N_{L/K} C_L`, so that the finiteness of the index
  descends along `normClassSubgroup K M ≤ normClassSubgroup K L` (`Subgroup.finiteIndex_of_le`).
-/

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- The **Galois closure** of a finite extension `L / K` of number fields, realised as an
intermediate field of the algebraic closure of `L`.  It is finite Galois over `K` and carries a
`K`-algebra structure and an `L`-algebra structure forming a tower `K ⊆ L ⊆ M`. -/
abbrev galoisClosure (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Type :=
  ↥(IntermediateField.normalClosure K L (AlgebraicClosure L))

/-- **The norm index of a finite extension of number fields is finite.**

For a finite extension `L / K` of number fields the quotient `C[K] ⧸ N_{L/K} C[L]` is finite,
i.e. the index of the norm class subgroup is non-zero.  Equivalently
`(NK.GlobalCFT.Idele.normClassSubgroup K L).FiniteIndex`. -/
theorem normClassSubgroup_index_ne_zero {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≠ 0 := by
  haveI : FiniteDimensional L (galoisClosure K L) := Module.Finite.right K L _
  haveI : NumberField (galoisClosure K L) := NumberField.of_module_finite K (galoisClosure K L)
  haveI : IsGalois K (galoisClosure K L) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hle : Idele.normClassSubgroup K (galoisClosure K L) ≤ Idele.normClassSubgroup K L :=
    Idele.normClassSubgroup_le_of_tower
  haveI : (Idele.normClassSubgroup K (galoisClosure K L)).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr
      (NormIndex.index_ne_zero_of_isGalois (K := K) (L := galoisClosure K L))
  exact Subgroup.finiteIndex_iff.mp (Subgroup.finiteIndex_of_le hle)

end NK.GlobalCFTdeep
