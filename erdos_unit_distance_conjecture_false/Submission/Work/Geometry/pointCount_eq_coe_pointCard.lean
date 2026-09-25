import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

theorem pointCount_eq_coe_pointCard (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (a : mixedEmbedding.mixedSpace K)
    (hfin : (Xset K I R a).Finite) :
    pointCount K I R a = (pointCard K I R a : ENNReal) := by
  classical
  -- `S` is the set of lattice points `l` with `a + l` in the window `B_R`.
  set S : Set (Lattice K I) := {l | a + (l : mixedEmbedding.mixedSpace K) ∈ Window K R} with hS
  -- the summand `l ↦ 1_{B_R}(a + l)` is supported on `S`
  have hsupp : Function.support
      (fun l : Lattice K I => (Window K R).indicator (fun _ => (1 : ENNReal))
        (a + (l : mixedEmbedding.mixedSpace K))) ⊆ S := by
    intro l hl
    rw [Function.mem_support] at hl
    by_contra hmem
    simp only [hS, Set.mem_ofPred_eq] at hmem
    exact hl (Set.indicator_of_notMem hmem _)
  -- translation by `a` is injective on the lattice
  have hinj : Function.Injective
      (fun l : Lattice K I => a + (l : mixedEmbedding.mixedSpace K)) :=
    (add_right_injective a).comp Subtype.coe_injective
  -- the image of `S` under `l ↦ a + l` is exactly `Xset K I R a`
  have himg : (fun l : Lattice K I => a + (l : mixedEmbedding.mixedSpace K)) '' S
      = Xset K I R a := by
    ext x
    simp only [Set.mem_image, hS, Set.mem_ofPred_eq, mem_Xset']
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, rfl, hl⟩
    · rintro ⟨l, rfl, hl⟩
      exact ⟨l, hl, rfl⟩
  -- hence `S` and `Xset K I R a` have the same cardinality
  have hcard : S.encard = (Xset K I R a).encard := by
    rw [← himg]
    exact (hinj.encard_image S).symm
  unfold pointCount
  calc ∑' l : Lattice K I, (Window K R).indicator (fun _ => (1 : ENNReal))
          (a + (l : mixedEmbedding.mixedSpace K))
      = ∑' l : S, (Window K R).indicator (fun _ => (1 : ENNReal))
          (a + ((l : Lattice K I) : mixedEmbedding.mixedSpace K)) :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' _ : S, (1 : ENNReal) :=
        tsum_congr fun l => Set.indicator_of_mem (s := Window K R)
          (a := a + ((l : Lattice K I) : mixedEmbedding.mixedSpace K)) (by exact l.2) _
    _ = (S.encard : ENNReal) := ENNReal.tsum_set_one S
    _ = ((Xset K I R a).encard : ENNReal) := by rw [hcard]
    _ = (pointCard K I R a : ENNReal) := by
        rw [← hfin.cast_ncard_eq, pointCard]
        norm_cast

end Work.Geometry
