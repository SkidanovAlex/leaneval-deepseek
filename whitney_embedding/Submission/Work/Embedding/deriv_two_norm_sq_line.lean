import Mathlib

/-!
# The second derivative of the squared distance along a line

The main analytic input to Whitney's strong embedding theorem (the step `2n+1 → 2n`) is a
second-order expansion of the squared distance `‖w - ψ x‖²` along a line `t ↦ c + t • d`.
This file supplies it: for a `C²` map `ψ` between real inner product spaces, the second
derivative of `t ↦ ‖w - ψ (c + t • d)‖ ^ 2` at `s` is
`2 * (‖Dψ(c+s•d) d‖² - ⟪w - ψ(c+s•d), D²ψ(c+s•d) (d, d)⟫)`.
-/

open Filter

namespace Work.Embedding

/-- **Squared norm of a `C²` curve.**  If `γ` has derivative `γ'` at every point of a
neighbourhood of `s` and `γ'` has derivative `γ'' s` at `s`, then the second derivative at `s`
of `t ↦ ‖γ t‖ ^ 2` is `2 * (⟪γ s, γ'' s⟫ + ‖γ' s‖²)`. -/
theorem iteratedDeriv_two_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (γ γ' γ'' : ℝ → F) (s : ℝ)
    (hγ : ∀ᶠ t in nhds s, HasDerivAt γ (γ' t) t)
    (h2 : HasDerivAt γ' (γ'' s) s) :
    deriv^[2] (fun t => ‖γ t‖ ^ 2) s =
      2 * (inner ℝ (γ s) (γ'' s) + ‖γ' s‖ ^ 2) := by
  have h1 : HasDerivAt γ (γ' s) s := hγ.self_of_nhds
  have hderiv : deriv (fun t => ‖γ t‖ ^ 2) =ᶠ[nhds s] fun t => 2 * inner ℝ (γ t) (γ' t) := by
    filter_upwards [hγ] with t ht
    exact ht.norm_sq.deriv
  have hiter : deriv^[2] (fun t => ‖γ t‖ ^ 2) s = deriv (deriv (fun t => ‖γ t‖ ^ 2)) s := rfl
  rw [hiter, hderiv.deriv_eq]
  have hh : HasDerivAt (fun t => 2 * inner ℝ (γ t) (γ' t))
      (2 * (inner ℝ (γ s) (γ'' s) + inner ℝ (γ' s) (γ' s))) s :=
    (HasDerivAt.inner ℝ h1 h2).const_mul 2
  rw [hh.deriv, real_inner_self_eq_norm_sq]

/-- Second derivative along a line: for a `C²` map `ψ` between real inner product spaces, the
second derivative of `t ↦ ‖w - ψ (c + t • d)‖ ^ 2` at `s` is twice
`‖Dψ(c+s•d) d‖² - ⟪w - ψ(c+s•d), D²ψ(c+s•d) (d, d)⟫`. -/
theorem deriv_two_norm_sq_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (ψ : E → F) (w : F) (c d : E) (s : ℝ)
    (hψ : ContDiffAt ℝ 2 ψ (c + s • d)) :
    deriv^[2] (fun t : ℝ => ‖w - ψ (c + t • d)‖ ^ 2) s =
      2 * (‖fderiv ℝ ψ (c + s • d) d‖ ^ 2 -
        inner ℝ (w - ψ (c + s • d)) ((fderiv ℝ (fderiv ℝ ψ) (c + s • d)) d d)) := by
  -- the line `t ↦ c + t • d` and its (constant) derivative `d`
  have hline : ∀ t : ℝ, HasDerivAt (fun u : ℝ => c + u • d) d t := fun t =>
    by simpa using ((hasDerivAt_id' t).smul_const d).const_add c
  -- `ψ` is `C²` on a neighbourhood of `c + s • d`, hence along the line near `s`
  have hψnear : ∀ᶠ y in nhds (c + s • d), ContDiffAt ℝ 2 ψ y :=
    hψ.eventually (by norm_num)
  -- first part of the chain rule: `γ = w - ψ ∘ line` has derivative `-(Dψ (line t)) d`
  have hA : ∀ᶠ t in nhds s, HasDerivAt (fun u : ℝ => w - ψ (c + u • d))
      (-(fderiv ℝ ψ (c + t • d) d)) t := by
    have hcont : ContinuousAt (fun u : ℝ => c + u • d) s := (hline s).continuousAt
    filter_upwards [hcont.tendsto.eventually hψnear] with t ht
    have hPψ : HasFDerivAt ψ (fderiv ℝ ψ (c + t • d)) (c + t • d) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    exact (hPψ.comp_hasDerivAt t (hline t)).const_sub w
  -- second part: `t ↦ -(Dψ (line t)) d` has derivative `-D²ψ (line s) d d` at `s`
  have hB : HasDerivAt (fun t : ℝ => -(fderiv ℝ ψ (c + t • d) d))
      (-((fderiv ℝ (fderiv ℝ ψ) (c + s • d)) d d)) s := by
    have hpp : ContDiffAt ℝ 1 (fderiv ℝ ψ) (c + s • d) := hψ.fderiv_right (by norm_num)
    have hfdiff : DifferentiableAt ℝ (fderiv ℝ ψ) (c + s • d) := hpp.differentiableAt (by norm_num)
    have hPfd : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (c + s • d)) (c + s • d) :=
      hfdiff.hasFDerivAt
    have hu : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (c + t • d))
        ((fderiv ℝ (fderiv ℝ ψ) (c + s • d)) d) s :=
      hPfd.comp_hasDerivAt s (hline s)
    have hv : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (c + t • d) d)
        (((fderiv ℝ (fderiv ℝ ψ) (c + s • d)) d) d) s :=
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ F d)).comp_hasDerivAt s hu
    exact hv.neg
  have key := iteratedDeriv_two_norm_sq (fun t : ℝ => w - ψ (c + t • d))
      (fun t : ℝ => -(fderiv ℝ ψ (c + t • d) d))
      (fun t : ℝ => -((fderiv ℝ (fderiv ℝ ψ) (c + t • d)) d d)) s hA hB
  rw [key, inner_neg_right, norm_neg]
  ring

end Work.Embedding
