import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.jordan_compl_atMostTwo
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Topology.PlaneCurve.exists_windNumber_ne_zero_of_rectSetup

/-!
# A simple closed plane curve has a point of non-zero winding number

For a continuous `2π`-periodic curve `γ : ℝ → ℂ` which is injective on one period `[0, 2π)`
(a *Jordan curve*) there is a point `z` of the plane, off the trace of `γ`, whose winding number
`windNumber γ z` is non-zero.

## Proof

The argument is a reduction to the normalised situation of Maehara's proof of the Jordan curve
theorem (the same normalisation that the sibling file
`Submission/Work/Smooth/SphereJordan/jordan_compl_atMostTwo.lean` uses for its
`exists_normalized`): after a similarity of the plane, the trace passes through `±1` and its
remaining points lie in the open rectangle `rectR = (-1,1) × (-2,2)`.  In that situation the
*window lemma* `Work.Topology.PlaneCurve.exists_windNumber_ne_zero_of_rectSetup` produces a point of the vertical
segment with non-zero winding number, and the winding number is carried back along the similarity
(`windNumber_div_sub` below: dividing by a non-zero constant and translating does not change the
winding number). -/

namespace Work.Smooth.SphereJordan

/-- **Translating and scaling the plane does not change the winding number.**  For `w ≠ 0` the
winding number of the loop `t ↦ (γ t - c)/w` about the image of `z` equals the winding number of
`γ` about `z`. -/
theorem windNumber_div_sub {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (c w : ℂ) (hw : w ≠ 0) {z : ℂ}
    (hz : ∀ t : ℝ, γ t ≠ z) :
    windNumber (fun t : ℝ => (γ t - c) / w) ((hγ.sub continuous_const).div_const w) ((z - c) / w)
      = windNumber γ hγ z := by
  have hcont1 : Continuous fun t : ℝ => γ t - z := hγ.sub continuous_const
  have hcont2 : Continuous fun t : ℝ => (γ t - c) / w - (z - c) / w := by fun_prop
  have h1 : ∀ t : ℝ, (γ t - c) / w - (z - c) / w = (γ t - z) / w := by
    intro t; ring
  have hloop1 : (curveLoop (fun t : ℝ => γ t - z) hcont1) 0
      = (curveLoop (fun t : ℝ => γ t - z) hcont1) 1 := by
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    have h1 : γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) = γ 0 := by simpa using hper 0
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
    rw [h0, h1]
  have hne2 : ∀ t : unitInterval, (curveLoop (fun t : ℝ => γ t - z) hcont1) t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - z ≠ 0
    exact sub_ne_zero.mpr (hz _)
  have hmul : ∀ t : unitInterval,
      (curveLoop (fun t : ℝ => (γ t - c) / w - (z - c) / w) hcont2) t
        = (curveLoop (fun t : ℝ => γ t - z) hcont1) t * (1 / w) := by
    intro t
    show (γ (2 * Real.pi * (t : ℝ)) - c) / w - (z - c) / w
      = (γ (2 * Real.pi * (t : ℝ)) - z) * (1 / w)
    rw [h1 (2 * Real.pi * (t : ℝ))]; ring
  have hcm : (curveLoop (fun t : ℝ => (γ t - c) / w - (z - c) / w) hcont2)
      = (curveLoop (fun t : ℝ => γ t - z) hcont1) * ContinuousMap.const unitInterval (1 / w) := by
    ext t; exact hmul t
  unfold windNumber
  rw [hcm, loopIndex_mul _ _ hne2 (fun _ => by simp [hw]) hloop1 (by simp)]
  rw [loopIndex_const (1 / w) (by simp [hw])]
  ring

theorem exists_windNumber_ne_zero {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    ∃ z : ℂ, (∀ t : ℝ, γ t ≠ z) ∧ windNumber γ hγ z ≠ 0 := by
  -- Step 1: normalise by the diameter similarity: `e = toUnitHomeo a b hab`, i.e.
  -- `z ↦ (z - c)/w` with `c = (a+b)/2`, `w = (b-a)/2`.
  obtain ⟨a, ha, b, hb, hab, hmax⟩ := Work.Smooth.SphereJordan.exists_diam_pair hγ hper hinj
  obtain ⟨sa, hsa⟩ := ha
  obtain ⟨sb, hsb⟩ := hb
  set c : ℂ := (a + b) / 2 with hc
  set w : ℂ := (b - a) / 2 with hw
  have hwne : w ≠ 0 := by
    rw [hw]; exact div_ne_zero (sub_ne_zero.mpr hab.symm) (by norm_num)
  have he_apply : ∀ z : ℂ,
      (Work.Smooth.SphereJordan.toUnitHomeo a b hab) z = (z - c) / w := by
    intro z
    rw [Work.Smooth.SphereJordan.toUnitHomeo_apply]
    rw [hc, hw]
    field_simp
  have hsub : ∀ t : ℝ,
      (γ t - c) / w ∈ Work.Topology.PlaneCurve.rectR ∨ (γ t - c) / w = -1 ∨ (γ t - c) / w = 1 := by
    intro t
    obtain ⟨hza, hzb⟩ := hmax (γ t) ⟨t, rfl⟩
    obtain ⟨h1, h2⟩ := Work.Smooth.SphereJordan.toUnit_norm_bounds (z := γ t) hab hzb hza
    obtain ⟨hre, hre1, him⟩ := Work.Smooth.SphereJordan.re_im_data h1 h2
    have key : (Work.Smooth.SphereJordan.toUnitHomeo a b hab) (γ t) =
        (γ t - c) / w := he_apply (γ t)
    rw [key] at hre hre1 him
    rcases lt_trichotomy |((γ t - c) / w).re| 1 with hlt | heq | hgt
    · refine Or.inl ?_
      rw [Work.Topology.PlaneCurve.rectR]
      exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2, (abs_lt.mp him).1, (abs_lt.mp him).2⟩
    · rcases hre1 heq with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact absurd hgt (not_lt.mpr hre)
  have hm1 : ∃ t : ℝ, (γ t - c) / w = -1 := by
    refine ⟨sa, ?_⟩
    rw [hsa, ← he_apply]
    exact Work.Smooth.SphereJordan.toUnitHomeo_neg_one a b hab
  have h1 : ∃ t : ℝ, (γ t - c) / w = 1 := by
    refine ⟨sb, ?_⟩
    rw [hsb, ← he_apply]
    exact Work.Smooth.SphereJordan.toUnitHomeo_one a b hab
  have hcont' : Continuous fun t : ℝ => (γ t - c) / w := (hγ.sub continuous_const).div_const w
  have hper' : Function.Periodic (fun t : ℝ => (γ t - c) / w) (2 * Real.pi) := by
    intro t
    show (γ (t + 2 * Real.pi) - c) / w = (γ t - c) / w
    rw [hper t]
  have hinj' : Set.InjOn (fun t : ℝ => (γ t - c) / w) (Set.Ico 0 (2 * Real.pi)) := by
    intro s hs u hu hsu
    have h2 : γ s - c = γ u - c := by
      have h3 := congrArg (fun v => v * w) hsu
      simpa [div_mul_cancel₀ _ hwne] using h3
    have h2' : γ s - c + c = γ u - c + c := by rw [h2]
    exact hinj hs hu (by simpa using h2')
  -- Step 3: the window lemma.
  obtain ⟨z', hz're, hz'ne, hz'w⟩ :=
    Work.Topology.PlaneCurve.exists_windNumber_ne_zero_of_rectSetup hcont' hper' hinj' hsub hm1 h1
  -- Step 4: transfer back.
  set z : ℂ := z' * w + c with hzdef
  have hz : ∀ t : ℝ, γ t ≠ z := by
    intro t ht
    have h2 : (γ t - c) / w = z' := by
      rw [ht, hzdef]
      field_simp
      ring
    exact hz'ne t h2
  refine ⟨z, hz, ?_⟩
  have htransfer := windNumber_div_sub hγ hper c w hwne hz
  rw [← htransfer]
  -- the argument of the transferred winding number is `z'`
  have harg : (z - c) / w = z' := by
    rw [hzdef]; field_simp; ring
  rw [harg]
  exact hz'w

end Work.Smooth.SphereJordan
