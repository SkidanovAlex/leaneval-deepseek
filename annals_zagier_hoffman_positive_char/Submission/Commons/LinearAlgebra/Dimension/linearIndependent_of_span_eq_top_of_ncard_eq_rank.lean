import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open scoped Cardinal

namespace Commons.LinearAlgebra.Dimension

theorem linearIndependent_of_span_eq_top_of_ncard_eq_rank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {s : Set V}
    (hfin : s.Finite) (hspan : Submodule.span K s = ⊤)
    (hrank : Module.rank K V = (s.ncard : Cardinal)) :
    LinearIndependent K (fun x : s => (x : V)) := by
  classical
  rw [linearIndependent_subtype_iff, linearIndepOn_iff_notMem_span]
  intro x hx hxmem
  have hxmem' : x ∈ Submodule.span K (s \ {x}) := by simpa using hxmem
  -- x ∈ span K (s \ {x}), so s \ {x} already spans
  have hspanx : Submodule.span K (s \ {x}) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro y hy
    rcases eq_or_ne y x with hyx | hyx
    · rwa [hyx]
    · exact Submodule.subset_span (by simp [hy, hyx])
  -- rank V ≤ #(s \ {x})
  have hle : Module.rank K V ≤ #(s \ {x} : Set V) := by
    have hrankx : Module.rank K V = Module.rank K ↥(Submodule.span K (s \ {x})) := by
      rw [← rank_top K V, ← hspanx]
    rw [hrankx]
    exact rank_span_le (s \ {x})
  -- #(s \ {x}) < s.ncard
  have hlt : #(s \ {x} : Set V) < (s.ncard : Cardinal) := by
    have ht : (hfin.toFinset : Set V) = s := hfin.coe_toFinset
    have hxmem_t : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx
    have hcard_erase : ((hfin.toFinset.erase x).card : Cardinal) < (hfin.toFinset.card : Cardinal) :=
      Nat.cast_lt.mpr (Finset.card_erase_lt_of_mem hxmem_t)
    have hset : (hfin.toFinset.erase x : Set V) = s \ {x} := by
      rw [Finset.coe_erase, ht]
    have h1 : #(s \ {x} : Set V) = ((hfin.toFinset.erase x).card : Cardinal) := by
      rw [← hset]
      exact Cardinal.mk_coe_finset
    have h2 : (s.ncard : Cardinal) = (hfin.toFinset.card : Cardinal) := by
      rw [Set.ncard_eq_toFinset_card s hfin]
    rw [h1, h2]
    exact hcard_erase
  have : Module.rank K V < (s.ncard : Cardinal) := lt_of_le_of_lt hle hlt
  rw [hrank] at this
  exact lt_irrefl _ this

end Commons.LinearAlgebra.Dimension