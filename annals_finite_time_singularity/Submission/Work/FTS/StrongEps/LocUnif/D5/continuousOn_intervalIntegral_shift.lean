import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

/-- Continuity in `z` of the sliding interval integral `z ↦ ∫ u in z..(z+h), f u`, for `f`
continuous on `[a, b+h]` and `z ∈ [a,b]`.  We write the sliding integral as the difference of
the primitive `z ↦ ∫_a^z f` evaluated at `z+h` and at `z`, and use continuity of the primitive
(`intervalIntegral.continuousOn_primitive_interval'`). -/
theorem continuousOn_intervalIntegral_shift {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a (b + h))) :
    ContinuousOn (fun z => ∫ u in z..(z + h), f u) (Set.Icc a b) := by
  have hle : a ≤ b + h := by linarith
  have hf_int : IntervalIntegrable f MeasureTheory.volume a (b + h) :=
    hf.intervalIntegrable_of_Icc hle
  -- The primitive `y ↦ ∫_a^y f` is continuous on `[a, b+h]`.
  have hG' : ContinuousOn (fun y => ∫ t in a..y, f t) (Set.Icc a (b + h)) := by
    rw [← Set.uIcc_of_le hle]
    exact intervalIntegral.continuousOn_primitive_interval' hf_int Set.left_mem_uIcc
  have h1 : ContinuousOn (fun z => ∫ t in a..(z + h), f t) (Set.Icc a b) :=
    hG'.comp ((continuous_id.add continuous_const).continuousOn)
      (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  have h2 : ContinuousOn (fun z => ∫ t in a..z, f t) (Set.Icc a b) :=
    hG'.mono (fun z hz => ⟨hz.1, by linarith [hz.2]⟩)
  refine (h1.sub h2).congr fun z hz => ?_
  have hz1 : a ≤ z := hz.1
  have hz2 : z ≤ b := hz.2
  have haz : IntervalIntegrable f MeasureTheory.volume a z := by
    refine ContinuousOn.intervalIntegrable (u := f) (μ := MeasureTheory.volume) ?_
    rw [Set.uIcc_of_le hz1]
    exact hf.mono (fun t ht => ⟨ht.1, by linarith [ht.2, hz2]⟩)
  have hazh : IntervalIntegrable f MeasureTheory.volume a (z + h) := by
    refine ContinuousOn.intervalIntegrable (u := f) (μ := MeasureTheory.volume) ?_
    rw [Set.uIcc_of_le (by linarith : a ≤ z + h)]
    exact hf.mono (fun t ht => ⟨ht.1, by linarith [ht.2, hz2]⟩)
  simp only [Pi.sub_apply]
  rw [intervalIntegral.integral_interval_sub_left hazh haz]

end Work.FTS.StrongEps.LocUnif.D5
