import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Minpoly

open Polynomial

theorem conjRootClass_card_carrier {K L : Type*} [Field K] [Field L] [Fintype L] [DecidableEq L]
    [Algebra K L] [Normal K L] [Fintype (Gal(L/K))] (c : ConjRootClass K L) :
    c.carrier.toFinset.card = c.minpoly.natDegree := by
  -- `L` is a finite type, hence a finite field; `K` embeds into `L`, so `K` is a finite
  -- field as well and therefore perfect.  As `L/K` is algebraic (from `Normal`), it is separable.
  have : Finite K := Finite.of_injective (algebraMap K L) (algebraMap K L).injective
  have : Algebra.IsSeparable K L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField (K := K) (L := L)
  have hcarrier : c.carrier.toFinset.card = (c.minpoly.aroots L).card := by
    rw [ConjRootClass.carrier_eq_mk_aroots_minpoly]
    rfl
  have hroots : (c.minpoly.aroots L).card = (c.minpoly.map (algebraMap K L)).natDegree := by
    have hsplit : (c.minpoly.map (algebraMap K L)).Splits := c.splits_minpoly
    rw [hsplit.natDegree_eq_card_roots]
  have hmap : (c.minpoly.map (algebraMap K L)).natDegree = c.minpoly.natDegree :=
    natDegree_map_eq_of_injective (algebraMap K L).injective _
  rw [hcarrier, hroots, hmap]

end Commons.FieldTheory.Minpoly