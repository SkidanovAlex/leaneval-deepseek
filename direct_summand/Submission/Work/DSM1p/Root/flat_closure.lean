import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.stepMap_alg
import Submission.Work.DSM1p.Root.closureAlg

/-!
# `R[a^{1/p^∞}]` is a flat `R`-module

The root closure `RootClosure R p a` of an element `a` of a commutative ring `R` is the filtered
colimit of the tower

`RootTower R p a m = R[x]/(x ^ (p ^ m) - a)`

along the maps `RootTower.stepMap R p a i j h` (`root i ↦ root j ^ (p ^ (j - i))`).  Each stage is
a *free* `R`-module of rank `p ^ m`, because `X ^ (p ^ m) - C a` is monic whenever `p ≠ 0`
(`RootExt.free`), so each stage is flat (`flat_stage`); a filtered colimit of flat modules is flat.

The formal proof of the colimit step is the equational criterion of flatness
(`Module.Flat.of_forall_isTrivialRelation`): every relation `∑ fᵢ • xᵢ = 0` in `RootClosure R p a`
is trivial.  Indeed, each `xᵢ` comes from some stage `m i` (`Ring.DirectLimit.exists_of`); moving
all of them to the common stage `N = max m i` (`stepMap_algebraMap` makes the transition maps
`R`-linear) we obtain `w = ∑ fᵢ • zᵢ` in stage `N` whose image in the colimit is `0`.  A zero in the
colimit is zero in some later stage `j ≥ N` (`Ring.DirectLimit.of.zero_exact`, available because of
the `DirectedSystem` instance `stepMap_directedSystem`), so that the relation `∑ fᵢ • zᵢ = 0` holds
in the flat stage `RootTower R p a j`; flatness there makes it trivial, and the trivialisation
transfers back to the colimit.

## Main result

* `flat_closure` : `Module.Flat R (RootClosure R p a)` for `p ≠ 0`.
-/

namespace Work.DSM1p.Root

universe u

set_option maxHeartbeats 1000000

/-- **The root closure `R[a^{1/p^∞}]` is flat over `R`** (for `p ≠ 0`): it is a filtered colimit of
the free `R`-modules `R[x]/(x^{p^m} - a)`, and filtered colimits of flat modules are flat. -/
theorem flat_closure (R : Type*) [CommRing R] (p : ℕ) (a : R) (hp : p ≠ 0) :
    Module.Flat R (Work.DSM1p.RootClosure R p a) := by
  classical
  refine Module.Flat.of_forall_isTrivialRelation (M := RootClosure R p a) ?_
  intro l f x hx
  -- Each `x i` is the image of an element of some stage of the tower.
  have hex : ∀ i : Fin l, ∃ (n : ℕ) (y : RootTower R p a n), RootClosure.of R p a n y = x i :=
    fun i => Ring.DirectLimit.exists_of (x i)
  choose m y hy using hex
  -- Move everything to the common stage `N = sup m`.
  let N : ℕ := Finset.univ.sup m
  have hle : ∀ i, m i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  let z : Fin l → RootTower R p a N := fun i => RootTower.stepMap R p a (m i) N (hle i) (y i)
  have hz : ∀ i, RootClosure.of R p a N (z i) = x i := fun i => by
    have h1 : RootClosure.of R p a N (z i) = RootClosure.of R p a (m i) (y i) := by
      simp only [z]
      exact Ring.DirectLimit.of_f (hle i) (y i)
    rw [h1, hy i]
  -- The relation, pushed to the stage `N`.
  let w : RootTower R p a N := ∑ i, f i • z i
  have hwlin : ofLinearMap R p a N w = 0 := by
    have h1 : ofLinearMap R p a N w = ∑ i, f i • x i := by
      simp only [w, map_sum, map_smul, ofLinearMap_apply]
      exact Finset.sum_congr rfl (fun i _ => by rw [hz i])
    rw [h1, hx]
  have hw : RootClosure.of R p a N w = 0 := by
    simpa only [ofLinearMap_apply] using hwlin
  -- A vanishing element of the colimit already vanishes in a later stage.
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (G := RootTower R p a)
    (f' := RootTower.stepMap R p a) hw
  let z' : Fin l → RootTower R p a j := fun i => RootTower.stepMap R p a N j hij (z i)
  have hz' : ∀ i, RootClosure.of R p a j (z' i) = x i := fun i => by
    have h1 : RootClosure.of R p a j (z' i) = RootClosure.of R p a N (z i) := by
      simp only [z']
      exact Ring.DirectLimit.of_f hij (z i)
    rw [h1, hz i]
  have hwsum : ∑ i, f i • z' i = 0 := by
    have h1 : stepMapLinear R p a N j hij w = ∑ i, f i • z' i := by
      simp only [w, z', map_sum, map_smul, stepMapLinear_apply]
    rw [← h1]
    exact hj
  -- The relation holds in the flat stage `RootTower R p a j`, where it is trivial.
  haveI : Module.Flat R (RootTower R p a j) := flat_stage R p a hp j
  obtain ⟨k, aa, yy, hdec, hrel⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := f) (x := z') hwsum
  refine ⟨k, aa, fun n => RootClosure.of R p a j (yy n), fun i => ?_, hrel⟩
  have h1 : ofLinearMap R p a j (z' i) =
      ∑ n, aa i n • RootClosure.of R p a j (yy n) := by
    rw [hdec i, map_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [map_smul, ofLinearMap_apply])
  rw [← hz' i]
  exact h1

end Work.DSM1p.Root
