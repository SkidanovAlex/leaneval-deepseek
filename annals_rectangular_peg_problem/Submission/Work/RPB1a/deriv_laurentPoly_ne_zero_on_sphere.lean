import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.laurentPoly_exp
import Submission.Work.RPB1a.laurentPoly_differentiableOn
import Submission.Work.RPB.B1a.laurentAux

/-!
# The derivative of a Laurent polynomial does not vanish on the unit circle

Let `v = trigPoly N a` be a trigonometric polynomial and `Γ = laurentPoly N a` its Laurent form,
so that `Γ (e^{it}) = v t` (`laurentPoly_exp`).  If `v` is a smooth immersed loop, i.e.
`deriv v t ≠ 0` for every `t`, then the chain rule through the parametrisation `t ↦ e^{it}` gives
`deriv v t = deriv Γ (e^{it}) · (i e^{it})`, and since `i e^{it} ≠ 0` we conclude `deriv Γ z ≠ 0`
for every `z` on the unit circle.
-/

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- The value of the derivative of a Laurent polynomial at a nonzero point. -/
theorem deriv_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    deriv (Work.RPB1a.laurentPoly N a) w =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * (n : ℂ) * w ^ (n - 1) :=
  (Work.RPB1a.hasDerivAt_laurentPoly N a hw).deriv

theorem deriv_laurentPoly_ne_zero_on_sphere (N : ℕ) (a : ℤ → ℂ) (hv : Work.RPB1a.IsSmoothLoop (Work.RPB1a.trigPoly N a)) :
    ∀ z ∈ Metric.sphere (0 : ℂ) 1, deriv (Work.RPB1a.laurentPoly N a) z ≠ 0 := by
  intro z hz
  -- write `z = e^{it}`
  obtain ⟨t, rfl⟩ := Work.RPB.B1a.exists_exp_of_mem_sphere hz
  have hw : Complex.exp ((t : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  -- derivative of the parametrisation `s ↦ s * I`
  have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (I : ℂ) t := by
    simpa using (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM (x := t)).mul_const (I : ℂ)
  -- derivative of `s ↦ e^{is}`
  have hcirc : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * I))
      (Complex.exp ((t : ℂ) * I) * I) t :=
    (Complex.hasDerivAt_exp ((t : ℂ) * I)).comp t hinner
  -- derivative of `Γ` at `e^{it}`
  have houter : HasDerivAt (Work.RPB1a.laurentPoly N a)
      (deriv (Work.RPB1a.laurentPoly N a) (Complex.exp ((t : ℂ) * I)))
      (Complex.exp ((t : ℂ) * I)) := by
    rw [Work.RPB1a.deriv_laurentPoly N a hw]
    exact Work.RPB1a.hasDerivAt_laurentPoly N a hw
  -- chain rule through `s ↦ e^{is}`
  have hcomp := houter.comp t hcirc
  have hF : deriv (Work.RPB1a.laurentPoly N a ∘ fun s : ℝ => Complex.exp ((s : ℂ) * I)) t
      = deriv (Work.RPB1a.laurentPoly N a) (Complex.exp ((t : ℂ) * I))
        * (Complex.exp ((t : ℂ) * I) * I) :=
    hcomp.deriv
  -- `Γ ∘ exp = v`
  have hfun : (Work.RPB1a.laurentPoly N a ∘ fun s : ℝ => Complex.exp ((s : ℂ) * I))
      = Work.RPB1a.trigPoly N a := by
    funext s
    exact Work.RPB1a.laurentPoly_exp N a s
  rw [hfun] at hF
  -- the loop is immersed, so `deriv v t ≠ 0`
  have hv' := hv.2.2.2 t
  rw [hF] at hv'
  intro hzero
  exact hv' (by rw [hzero, zero_mul])

end Work.RPB1a
