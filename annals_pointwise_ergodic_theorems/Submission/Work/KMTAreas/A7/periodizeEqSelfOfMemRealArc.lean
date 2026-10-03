import Mathlib
import Submission.Work.KMTAreas.A7.liftCollapse

namespace Work.KMTAreas.A7

/-- If `φ` is supported in the arc `ℝ_{≤k} = [-2^k, 2^k]` with `2^k ≤ 1/4`, then the periodisation
of `φ` to the circle takes at a point `x` of the arc the value `φ x` itself: the arc is so narrow
that the fundamental domain `[0,1)` contains only one representative of `x` (`x` itself, if
`x ≥ 0`, or `x + 1`, if `x < 0`), and only that representative lies in the support. -/
theorem periodizeEqSelfOfMemRealArc {φ : ℝ → ℂ} {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 4)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) {x : ℝ}
    (hx : x ∈ Work.Analysis.IonescuWainger.realArc k) :
    Work.Analysis.IonescuWainger.periodize φ (x : Work.Analysis.IonescuWainger.Circle) = φ x := by
  -- the support condition in the absolute-value form used by `periodize_eq_lift`
  have hsupp : ∀ y : ℝ, φ y ≠ 0 → |y| ≤ (2 : ℝ) ^ k := by
    intro y hy
    have h := hφ y hy
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at h
    rw [abs_le]
    exact h
  have hw : (2 : ℝ) ^ k < 1 / 2 := by linarith
  -- the periodisation collapses to the canonical lift `[-1/2,1/2)`
  rw [periodize_eq_lift hw hsupp]
  -- on the arc, the canonical lift is `x` itself
  have harc := hx
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at harc
  have habs : |x| ≤ (2 : ℝ) ^ k := by
    rw [abs_le]
    exact ⟨harc.1, harc.2⟩
  have hquarter : |x| ≤ 1 / 4 := le_trans habs hk
  have hmem : x ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico]
    exact ⟨by linarith [(abs_le.mp hquarter).1], by linarith [(abs_le.mp hquarter).2]⟩
  have hlift : lift ((x : ℝ) : Work.Analysis.IonescuWainger.Circle) = x := by
    rw [lift]
    exact AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -(1 / 2)) (y := x) hmem
  rw [hlift]

end Work.KMTAreas.A7
