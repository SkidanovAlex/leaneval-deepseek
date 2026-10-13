import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `V`-form of the stream function field `psiField`

The stream function `ψ(r,z) = r · V(r², z)` depends on the radial variable only through `r²`, so the
velocity field it generates is an `axiField` (a field whose radial profile is a function of `r²`).
This file computes that form:

  `psiField (fun r z => r * V (r^2) z)
     = axiField (fun w z => ∂_z V(w,z)) (fun w z => -2 V(w,z) - 2 w ∂_w V(w,z))`.

Concretely, `psiField ψ = cylField (∂_zψ) (-(ψ/r) - ∂_rψ)` and, by the product and chain rules,

* `∂_z ψ = r · ∂_z V(r²,·)`, so the radial component of the field is
  `∂_zψ/r = ∂_z V(r²,·)`, a function of `r²`;
* `∂_r ψ = V(r²,z) + 2r² ∂_wV(r²,z)` and `ψ/r = V(r²,z)`, so the axial component is
  `-2V(r²,z) - 2r² ∂_wV(r²,z)` — which is `b(r²,z)` for `b(w,z) = -2V(w,z) - 2w ∂_wV(w,z)`.

The hypothesis `V(0,z) = 0` is what makes the identity hold *on the axis* `r = 0`: there
`ψ(0,z) = 0` so the axial profile `ψ/r` contributes `0`, while the product rule gives
`∂_rψ(0,z) = V(0,z) = 0`; correspondingly `b(0,z) = -2V(0,z) - 0 = 0`.  Off the axis the identity
is a pure product/chain rule computation.
-/

noncomputable section

namespace Work.FTS.BSIdent.Cyl

/-! ## Differentiability of the slices of `V` -/

/-- A jointly `C²` two-variable function is differentiable at every point. -/
private lemma diffAt2_of_contDiff (V : ℝ → ℝ → ℝ) (hV : ContDiff ℝ 2 (Function.uncurry V))
    (w z : ℝ) : Work.Cyl.DiffAt2 V w z := by
  have h : ContDiff ℝ 2 (fun p : ℝ × ℝ => V p.1 p.2) := hV
  exact (h.differentiable (by norm_num)).differentiableAt

/-- **The derivative of `r' ↦ r' · V(r'², z)`**: product rule plus chain rule,
`∂_r (r V(r²,z)) = V(r²,z) + 2r² ∂_wV(r²,z)`. -/
private lemma deriv_id_mul_V_sq (V : ℝ → ℝ → ℝ) (hV : ContDiff ℝ 2 (Function.uncurry V))
    (r z : ℝ) :
    deriv (fun r' => r' * V (r' ^ 2) z) r
      = V (r ^ 2) z + 2 * r ^ 2 * deriv (fun w' => V w' z) (r ^ 2) := by
  have hVw : DifferentiableAt ℝ (fun w' : ℝ => V w' z) (r ^ 2) :=
    Work.Cyl.differentiableAt_slice_fst V (r ^ 2) z (diffAt2_of_contDiff V hV (r ^ 2) z)
  have hg : DifferentiableAt ℝ (fun r' : ℝ => r' ^ 2) r := by fun_prop
  -- chain rule: `∂_r V(r²,z) = 2r ∂_wV(r²,z)`
  have hchain : deriv (fun r' : ℝ => V (r' ^ 2) z) r
      = deriv (fun w' : ℝ => V w' z) (r ^ 2) * (2 * r) := by
    have hfun : (fun r' : ℝ => V (r' ^ 2) z)
        = (fun w' : ℝ => V w' z) ∘ (fun r' : ℝ => r' ^ 2) := rfl
    rw [hfun, deriv_comp (x := r) (h := fun r' : ℝ => r' ^ 2)
      (h₂ := fun w' : ℝ => V w' z) hVw hg]
    have hs : deriv (fun r' : ℝ => r' ^ 2) r = 2 * r := by
      rw [(hg.hasDerivAt).deriv]
      norm_num
    rw [hs]
  have hd : DifferentiableAt ℝ (fun r' : ℝ => V (r' ^ 2) z) r := by
    have hfun : (fun r' : ℝ => V (r' ^ 2) z)
        = (fun w' : ℝ => V w' z) ∘ (fun r' : ℝ => r' ^ 2) := rfl
    rw [hfun]
    exact DifferentiableAt.comp r hVw hg
  -- product rule
  have hmul : deriv (fun r' : ℝ => r' * V (r' ^ 2) z) r
      = deriv (id : ℝ → ℝ) r * V (r ^ 2) z
        + id r * deriv (fun r' : ℝ => V (r' ^ 2) z) r := by
    have heq : deriv (fun r' : ℝ => r' * V (r' ^ 2) z) r
        = deriv ((id : ℝ → ℝ) * (fun r' : ℝ => V (r' ^ 2) z)) r := rfl
    rw [heq, deriv_mul (by fun_prop : DifferentiableAt ℝ (id : ℝ → ℝ) r) hd]
  rw [hmul, hchain, deriv_id]
  simp only [id_eq]
  ring_nf

/-- **The radial component.**  `∂_z ψ = r ∂_z V(r²,·)`, so off the axis `∂_zψ/r = ∂_z V(r²,·)`. -/
private lemma deriv_const_mul_div (V : ℝ → ℝ → ℝ) (hV : ContDiff ℝ 2 (Function.uncurry V))
    (r z : ℝ) (hr : r ≠ 0) :
    deriv (fun z' => r * V (r ^ 2) z') z / r = deriv (fun z' => V (r ^ 2) z') z := by
  have hf : DifferentiableAt ℝ (fun z' => V (r ^ 2) z') z :=
    Work.Cyl.differentiableAt_slice_snd V (r ^ 2) z (diffAt2_of_contDiff V hV (r ^ 2) z)
  rw [deriv_const_mul r hf, mul_div_cancel_left₀ _ hr]

/-- **The axial component.**  `-(ψ/r) - ∂_rψ = -2V(r²,z) - 2r² ∂_wV(r²,z)`; the hypothesis
`V(0,z) = 0` is used at `r = 0`. -/
private lemma axial_coeff (V : ℝ → ℝ → ℝ) (hV : ContDiff ℝ 2 (Function.uncurry V))
    (hV0 : ∀ z, V 0 z = 0) (r z : ℝ) :
    -(r * V (r ^ 2) z / r) - deriv (fun r' => r' * V (r' ^ 2) z) r
      = -2 * V (r ^ 2) z - 2 * r ^ 2 * deriv (fun w' => V w' z) (r ^ 2) := by
  rw [deriv_id_mul_V_sq V hV r z]
  by_cases hr : r = 0
  · -- on the axis: `r V(r²,z)/r = 0` and `∂_rψ(0,z) = V(0,z) = 0`, and likewise for `b(0,z)`
    subst hr
    have h02 : ((0 : ℝ) ^ 2) = 0 := by norm_num
    rw [h02, hV0 z]
    norm_num
  · rw [mul_div_cancel_left₀ _ hr]
    ring

theorem psiField_r_mul_V_eq_axiField (V : ℝ → ℝ → ℝ)
    (hV : ContDiff ℝ 2 (Function.uncurry V)) (hV0 : ∀ z, V 0 z = 0) :
    Work.Cyl.psiField (fun r z => r * V (r ^ 2) z)
      = Work.Cyl.axiField (fun w z => deriv (fun z' => V w z') z)
          (fun w z => -2 * V w z - 2 * w * deriv (fun w' => V w' z) w) := by
  funext x
  -- unfold both sides into `(radial coeff) • radialVec x + (axial coeff) • eZ`
  simp only [Work.Cyl.psiField, Work.Cyl.cylField, Work.Cyl.axiField, Work.Cyl.pdZ, Work.Cyl.pdR]
  rw [← Work.Cyl.radial_sq x]
  -- the axial components agree for every `r` (this uses `hV0`)
  rw [axial_coeff V hV hV0 (Work.Cyl.radial x) (Work.Cyl.axial x)]
  by_cases hr : Work.Cyl.radial x = 0
  · -- on the axis the radial vector vanishes, so the radial components are irrelevant
    have h0 : x.ofLp 0 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hr).1
    have h1 : x.ofLp 1 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hr).2
    have hrv : Work.Cyl.radialVec x = 0 := by
      refine Work.Cyl.ext_coord ?_ ?_ ?_
      · rw [Work.Cyl.radialVec_apply_zero, h0]; simp
      · rw [Work.Cyl.radialVec_apply_one, h1]; simp
      · simp [Work.Cyl.radialVec]
    rw [hrv]
    simp
  · -- off the axis the radial components agree as well
    rw [deriv_const_mul_div V hV (Work.Cyl.radial x) (Work.Cyl.axial x) hr]

end Work.FTS.BSIdent.Cyl
