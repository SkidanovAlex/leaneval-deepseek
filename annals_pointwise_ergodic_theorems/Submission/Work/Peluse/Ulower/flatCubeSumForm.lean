import Mathlib
import Submission.Work.Peluse.Ulower.flatCubeSum

/-!
# The target's sums in flat-cube form

The two sums of `Work.Peluse.Ulower.flatCubeTransform` (over the `piFinset` of the shift set
`arithIcc 1 D`) are reindexed as `Concat.cubeSum`s over the subtype `↥(arithIcc 1 D)`.  This puts
them in the form where `Concat.cubeSum_const_succ` (the recursion) and `Concat.gcsRecurse`
(positivity) apply.
-/

open scoped BigOperators

namespace Work.Peluse.Ulower

/-- The `ω`-corner of the flat cube, transported to the subtype. -/
private lemma mix_coe {s D : ℕ} (ω : Fin s → Bool) (v0 v1 : Fin s → ↥(Work.Peluse.arithIcc 1 D)) :
    (fun i => (Work.Peluse.Concat.mix ω v0 v1 i).1)
      = Work.Peluse.Concat.mix ω (fun i => (v0 i).1) (fun i => (v1 i).1) := by
  funext i
  by_cases h : ω i = true <;> simp [Work.Peluse.Concat.mix, h]

/-- The corner shift of the mixed tuple is the mixed sum. -/
private lemma cornerShift_coe {s D : ℕ} (ω : Fin s → Bool)
    (v0 v1 : Fin s → ↥(Work.Peluse.arithIcc 1 D)) :
    Work.Peluse.cornerShift (fun i => (v1 i).1) (fun i => (v0 i).1) ω
      = ∑ i : Fin s, (Work.Peluse.Concat.mix ω v0 v1 i).1 := by
  unfold Work.Peluse.cornerShift
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : ω i = true <;> simp [Work.Peluse.Concat.mix, h]

theorem flatCubeSumForm (s : ℕ) (hs : 1 ≤ s) (D : ℕ) (h : Fin s → ℤ) (g : ℤ → ℂ) :
    (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
        ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
          (Work.Peluse.cubeTerm h (Work.Peluse.Concat.mix ω v0 v1) g 0))
      = Work.Peluse.Concat.cubeSum
          (fun (_ : Fin s → Bool) => fun (v : Fin s → ↥(Work.Peluse.arithIcc 1 D)) =>
            Work.Peluse.cubeTerm h (fun i => (v i).1) g 0)
    ∧ (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
      ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
        ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
          (g (Work.Peluse.cornerShift v1 v0 ω)))
      = Work.Peluse.Concat.cubeSum
          (fun (_ : Fin s → Bool) => fun (v : Fin s → ↥(Work.Peluse.arithIcc 1 D)) =>
            g (∑ i : Fin s, (v i).1)) := by
  constructor
  · rw [sum_piFinset₂_eq_sum_subtype' (Work.Peluse.arithIcc 1 D)
      (fun v0 v1 : Fin s → ℤ => ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
        (Work.Peluse.cubeTerm h (Work.Peluse.Concat.mix ω v0 v1) g 0))]
    simp only [Work.Peluse.Concat.cubeSum, Work.Peluse.Concat.cubeProd]
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [mix_coe ω v0 v1]
  · rw [sum_piFinset₂_eq_sum_subtype' (Work.Peluse.arithIcc 1 D)
      (fun v0 v1 : Fin s → ℤ => ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
        (g (Work.Peluse.cornerShift v1 v0 ω)))]
    simp only [Work.Peluse.Concat.cubeSum, Work.Peluse.Concat.cubeProd]
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [cornerShift_coe ω v0 v1]

end Work.Peluse.Ulower
