import Mathlib
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.wC_im_neg

namespace Work.A14D

open Complex Metric

/-- The integrand
`z ↦ dyC z · (yC z)⁻¹ ^ j · jumpH D z = y'(z)·y(z)^{−j}·(D z − D (w z))`
of the `j`-th `y`-integral jump is holomorphic on the upper half plane.

`yC` and `dyC` are rational with their only pole at `1`, and `yC` has its only zero at `0`;
both points lie off `{0 < im z}`.  The jump `jumpH D z = D z − D (wC z)` is holomorphic there
because `D` is holomorphic on `Om1` and the deck involution `wC(z) = z/(z−1)` maps the upper
half plane into the lower one (`Work.A14D.wC_im_neg`), hence into `Om1`. -/
theorem integrandJFI_diffOn_upperHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) :
    DifferentiableOn ℂ (fun z => dyC z * (yC z)⁻¹ ^ j * jumpH D z) {z : ℂ | 0 < z.im} := by
  set s : Set ℂ := {z : ℂ | 0 < z.im} with hs
  -- `1` lies off the upper half plane, so the poles of `yC`/`dyC` are avoided
  have hs1 : ∀ z ∈ s, z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    simp [s] at hz
  have hdydiff : DifferentiableOn ℂ dyC s := by
    unfold dyC
    exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
      ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
      (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (hs1 z hz)))
  have hyCdiff : DifferentiableOn ℂ yC s := by
    unfold yC
    exact (differentiableOn_id.pow 2).div
      (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (hs1 z hz))
  -- `0` lies off the upper half plane, so `yC` does not vanish there
  have hyCne : ∀ z ∈ s, yC z ≠ 0 := by
    intro z hz hz0
    have hz1 : z ≠ 1 := hs1 z hz
    have h : z ^ 2 = 0 := by
      have hh := hz0
      rw [yC] at hh
      field_simp at hh
      simpa using hh
    have hz0' : z = 0 := sq_eq_zero_iff.mp h
    rw [hz0'] at hz
    simp [s] at hz
  have hinv : DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ j) s := (hyCdiff.inv hyCne).pow j
  have hwCd : DifferentiableOn ℂ wC s := by
    unfold wC
    exact differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (hs1 z hz))
  -- `wC` maps the upper half plane into `Om1` (indeed into the lower half plane)
  have hmaps : Set.MapsTo wC s Om1 := by
    intro z hz
    rw [Om1]
    exact Or.inl (ne_of_lt (wC_im_neg (z := z) hz))
  have hDd : DifferentiableOn ℂ D s := hD.mono (fun z hz => by
    rw [Om1]; exact Or.inl (ne_of_gt hz))
  have hcomp : DifferentiableOn ℂ (fun z => D (wC z)) s := hD.comp hwCd hmaps
  have hkey : (fun z => dyC z * (yC z)⁻¹ ^ j * jumpH D z)
      = (fun z => dyC z * ((fun z => (yC z)⁻¹ ^ j) z) * (D z - D (wC z))) := by
    funext z; rw [jumpH]
  rw [hkey]
  exact (hdydiff.mul hinv).mul (hDd.sub hcomp)

end Work.A14D
