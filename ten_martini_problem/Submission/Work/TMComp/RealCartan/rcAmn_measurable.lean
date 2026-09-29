import Mathlib
import Submission.Work.TMComp.RealCartanDefs

/-!
# Measurability of the "good set" pieces `Amn`

`Work.TMComp.RC.Amn U f w s m n` is the set of `x : ℝ` with `(x : ℂ) ∈ U` and
`‖f k x‖ ≤ w k * exp (-(s k / (m + 1)))` for all `k ≥ n`.  Here `U` is open and each
`f k` is holomorphic (in particular continuous) on `U`.

The set is a countable intersection of sets of the form
`{x | (x : ℂ) ∈ U ∧ ‖f k x‖ ≤ c k}`.  Each such set is measurable because the
preimage of a closed set under a function that is continuous on the *open* set
`{x | (x : ℂ) ∈ U} ⊆ ℝ` is measurable; this is the content of
`measurableSet_inter_preimage_isClosed` below.
-/

namespace Work.TMComp.RealCartan

open MeasureTheory Filter Topology Set

/-- If `V ⊆ ℝ` is open and `f : ℝ → γ` is continuous on `V`, then `V ∩ f ⁻¹' C` is
measurable for every closed `C`.  Indeed, replacing `f` by `0` off `V` gives a
measurable function (`ContinuousOn.measurable_piecewise`), and on `V` the two agree. -/
lemma measurableSet_inter_preimage_isClosed {V : Set ℝ} (hV : IsOpen V)
    {γ : Type*} [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ] [Zero γ]
    {f : ℝ → γ} (hf : ContinuousOn f V) {C : Set γ} (hC : IsClosed C) :
    MeasurableSet (V ∩ f ⁻¹' C) := by
  classical
  have hmeas : Measurable (V.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hV.measurableSet
  have hset : V ∩ f ⁻¹' C = V ∩ (V.piecewise f (fun _ => 0)) ⁻¹' C := by
    ext x
    constructor
    · rintro ⟨hxV, hx⟩
      exact ⟨hxV, by
        simpa only [Set.mem_preimage, Set.piecewise_eq_of_mem V f (fun _ => 0) hxV]
          using hx⟩
    · rintro ⟨hxV, hx⟩
      exact ⟨hxV, by
        simpa only [Set.mem_preimage, Set.piecewise_eq_of_mem V f (fun _ => 0) hxV]
          using hx⟩
  rw [hset]
  exact hV.measurableSet.inter (hmeas hC.measurableSet)

/-- The tail `Set.Ici n ⊆ ℕ` is countable. -/
lemma rc_countable_Ici (n : ℕ) : (Set.Ici n).Countable := by
  have h : Set.Ici n = Set.range (fun k : ℕ => n + k) := by
    ext k; simp only [Set.mem_Ici, Set.mem_range]
    constructor
    · intro hk; exact ⟨k - n, by omega⟩
    · rintro ⟨j, rfl⟩; omega
  rw [h]; exact Set.countable_range _

theorem rcAmn_measurable {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → ℂ}
    (hf : ∀ k, DifferentiableOn ℂ (f k) U) {w s : ℕ → ℝ} (m n : ℕ) :
    MeasurableSet (Work.TMComp.RC.Amn U f w s m n) := by
  classical
  have hKey : Work.TMComp.RC.Amn U f w s m n
      = ⋂ k ∈ Set.Ici n,
          (((fun x : ℝ => (x : ℂ)) ⁻¹' U)
            ∩ {x : ℝ | ‖f k (x : ℂ)‖ ≤ w k * Real.exp (-(s k / (m + 1)))}) := by
    ext x
    simp only [Work.TMComp.RC.Amn, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ici,
      Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxU, hk⟩
      exact fun k hk' => ⟨hxU, hk k hk'⟩
    · intro h
      exact ⟨(h n le_rfl).1, fun k hk' => (h k hk').2⟩
  rw [hKey]
  apply MeasurableSet.biInter (rc_countable_Ici n)
  intro k _
  have hcont : ContinuousOn (fun x : ℝ => ‖f k (x : ℂ)‖) ((fun x : ℝ => (x : ℂ)) ⁻¹' U) :=
    ((hf k).continuousOn.comp Complex.continuous_ofReal.continuousOn (fun x hx => hx)).norm
  exact measurableSet_inter_preimage_isClosed (hU.preimage Complex.continuous_ofReal) hcont
    isClosed_Iic

end Work.TMComp.RealCartan
