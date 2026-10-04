import Mathlib
import Submission.Work.Diff.STE.Lead.CompJetDefs
import Submission.Work.Diff.STE.Lead.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability of the jet tower

The jet tower `y ↦ compTower u m y` of a smooth `u` is differentiable, with derivative the linear
map `towerScan m (compTower u (m+1) y)`: the `(m+1)`-tower read off along the shifts `ishift c i`.

This is componentwise the statement that a word derivative has as derivative the sum of the next
word derivatives (`pdW_hasFDerivAt`), combined with the identification
`π i ∘ towerScan m J = frameLin (fun c => J (ishift c i))`.
-/

open scoped ContDiff BigOperators

namespace Work.Diff.STE.Lead.CompJet

open Work.Diff.STE.Lead

/-- The `i`-th component of the tower scan is the linear form of the shifted `(m+1)`-tower. -/
private lemma proj_comp_towerScan {n : ℕ} (m : ℕ) (J : Idx n (m + 1) → ℂ) (i : Idx n m) :
    (ContinuousLinearMap.proj i).comp (towerScan m J) = frameLin (fun c => J (ishift c i)) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, towerScan_apply,
    frameLin_apply]

theorem tower_hasFDerivAt {n : ℕ} {u : Work.Diff.STE.Lead.Modl n → Work.Diff.STE.Lead.Mtrx n}
    {Ω : Set (Work.Diff.STE.Lead.Modl n)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {y : Work.Diff.STE.Lead.Modl n} (hy : y ∈ Ω) (m : ℕ) :
    HasFDerivAt (fun y' => Work.Diff.STE.Lead.compTower u m y')
      (Work.Diff.STE.Lead.towerScan m (Work.Diff.STE.Lead.compTower u (m + 1) y)) y := by
  rw [hasFDerivAt_pi']
  intro i
  rw [show (ContinuousLinearMap.proj i).comp
        (towerScan m (compTower u (m + 1) y)) =
      frameLin (fun c => compTower u (m + 1) y (ishift c i)) from
    proj_comp_towerScan m (compTower u (m + 1) y) i]
  exact pdW_hasFDerivAt hΩ (by fun_prop) hy i.2.1.val i.2.2

end Work.Diff.STE.Lead.CompJet
