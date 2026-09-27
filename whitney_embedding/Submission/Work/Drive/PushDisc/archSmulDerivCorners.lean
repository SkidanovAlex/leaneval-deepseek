import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens

/-!
# The two corner derivatives of the arch relation

`Work.Drive.PushDisc.arch x = 1 - x ^ 2` vanishes at `x = ±1`, so from a smooth identity

    arch x • g x = B x - (x, 0, 0, 0)

on the model space `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k` one reads off, by differentiating at the two
corners `x = ±1`, the slope conditions

    (-2) • g 1  = fderiv ℝ B 1 1  - (1, 0, 0, 0),
     2  • g (-1) = fderiv ℝ B (-1) 1 - (1, 0, 0, 0).

The whole content is the product rule at a zero of `arch`: the term `arch x • deriv g x`
disappears, and the remaining coefficient is `deriv arch (∓1) = ∓2`.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff

theorem archSmulDerivCorners {k : ℕ} (B g : ℝ → Work.Drive.Whitney.Mdl k)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hgval : ∀ x : ℝ, Work.Drive.PushDisc.arch x • g x = B x - ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) :
    (-2 : ℝ) • g 1 = fderiv ℝ B 1 1 - (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) ∧
      (2 : ℝ) • g (-1) = fderiv ℝ B (-1) 1 - (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hBd : Differentiable ℝ B := hB.differentiable (by simp)
  -- the derivative of the arch
  have harch : ∀ x : ℝ, HasDerivAt arch (-2 * x) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (0 - (2 * x ^ (2 - 1))) x :=
      (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)
    have hd : 0 - (2 * x ^ (2 - 1)) = -2 * x := by
      have h21 : (2 : ℕ) - 1 = 1 := rfl
      rw [h21, pow_one]; ring
    exact h.congr_deriv hd
  have hfun : (fun y : ℝ => arch y • g y)
      = (fun y : ℝ => B y - ((y, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) := funext hgval
  -- differentiating the identity at an arbitrary point
  have key : ∀ x : ℝ, fderiv ℝ B x 1 =
      arch x • deriv g x + deriv arch x • g x + (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    intro x
    have hc : HasDerivAt (fun t : ℝ => ((t, 0, 0, 0) : Work.Drive.Whitney.Mdl k))
        (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x
        ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)), (0 : EuclideanSpace ℝ (Fin k))))
    have hF : deriv (fun y : ℝ => arch y • g y) x
        = arch x • deriv g x + deriv arch x • g x :=
      (((harch x).differentiableAt).hasDerivAt.smul ((hgd x).hasDerivAt)).deriv
    have hG : deriv (fun y : ℝ => B y - ((y, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) x
        = deriv B x - deriv (fun t : ℝ => ((t, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) x :=
      deriv_sub (hBd x) hc.differentiableAt
    have heq : deriv (fun y : ℝ => arch y • g y) x
        = deriv B x - (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
      rw [hfun, hG, hc.deriv]
    have h1 : deriv B x
        = deriv (fun y : ℝ => arch y • g y) x + (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) :=
      sub_eq_iff_eq_add.mp heq.symm
    rw [hF] at h1
    have hdB : deriv B x = fderiv ℝ B x 1 := ((hBd x).hasFDerivAt.hasDerivAt).deriv
    rw [← hdB]
    exact h1
  have h1 := key 1
  have h2 := key (-1)
  have ha1 : deriv arch 1 = -2 := by
    have := (harch 1).deriv
    simpa using this
  have ha2 : deriv arch (-1) = 2 := by
    have := (harch (-1)).deriv
    rw [this]; norm_num
  have haa1 : arch 1 = 0 := by norm_num [arch]
  have haa2 : arch (-1) = 0 := by norm_num [arch]
  rw [haa1, zero_smul, zero_add, ha1] at h1
  rw [haa2, zero_smul, zero_add, ha2] at h2
  exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩

end Work.Drive.PushDisc
