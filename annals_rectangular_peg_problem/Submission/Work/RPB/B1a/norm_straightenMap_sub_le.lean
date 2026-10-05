import Mathlib
import Submission.Work.RPB.B1a.HalfBallDefs

/-!
# `Work.RPB.B1a`: the straightening map is `1`-Lipschitz up to its linearisation

For a `C¹` curve `v : ℝ → ℂ` and a parameter `t₀`, the straightening chart is

`straightenMap v t₀ p = v (t₀ + p.1) + p.2 * (I * deriv v t₀)`.

Its differential at `0` is the affine map `z ↦ v t₀ + (z.1 + z.2 * I) * deriv v t₀`, so the
remainder of the chart between two points `p`, `q` is

`v (t₀ + p.1) - v (t₀ + q.1) - (p.1 - q.1) * deriv v t₀`

(the vertical parts cancel *exactly*, because the chart is affine in the second variable).  This is
the error term of the linearisation, and it is bounded by `|p.1 - q.1| * Δ` whenever the derivative
of `v` stays within `Δ` of `deriv v t₀` on the relevant interval.

The proof is the mean value inequality applied to the affine correction
`s ↦ v (t₀ + s) - v t₀ - s • deriv v t₀`, whose derivative is `deriv v (t₀ + s) - deriv v t₀`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

open Complex Set Metric

/-- The derivative of the affine correction of `v` around `t₀`:
`deriv (fun s ↦ v (t₀ + s) - v t₀ - s • deriv v t₀) s = deriv v (t₀ + s) - deriv v t₀`. -/
lemma deriv_affineCorrection (v : ℝ → ℂ) (hv : Differentiable ℝ v) (t₀ : ℝ) :
    deriv (fun s : ℝ => v (t₀ + s) - v t₀ - s • deriv v t₀) =
      fun s => deriv v (t₀ + s) - deriv v t₀ := by
  funext s
  have hA : HasDerivAt (fun x : ℝ => v (t₀ + x)) (deriv v (t₀ + s)) s :=
    (hv (t₀ + s)).hasDerivAt.comp_const_add t₀ s
  have hB : HasDerivAt (fun _ : ℝ => v t₀) 0 s := hasDerivAt_const s (v t₀)
  have hC : HasDerivAt (fun x : ℝ => x • deriv v t₀) (deriv v t₀) s := by
    simpa using (hasDerivAt_id s).smul_const (deriv v t₀)
  have hfull : HasDerivAt
      (((fun x : ℝ => v (t₀ + x)) - (fun _ : ℝ => v t₀)) - (fun x : ℝ => x • deriv v t₀))
      (deriv v (t₀ + s) - 0 - deriv v t₀) s := (hA.sub hB).sub hC
  rw [show (fun s : ℝ => v (t₀ + s) - v t₀ - s • deriv v t₀)
      = ((fun x : ℝ => v (t₀ + x)) - (fun _ : ℝ => v t₀)) - (fun x : ℝ => x • deriv v t₀)
      from rfl]
  rw [hfull.deriv]
  simp

/-- **The straightening map is linear up to a controlled error.**  The difference of the straightening
chart at two points `p`, `q` differs from its linearisation `(p₁ - q₁ + (p₂ - q₂) I) * deriv v t₀`
by the horizontal error of the curve, which is bounded by `|p₁ - q₁| Δ` when `deriv v` does not
deviate from `deriv v t₀` by more than `Δ` on the interval `[-R, R]` containing `p.1` and `q.1`. -/
theorem norm_straightenMap_sub_le (v : ℝ → ℂ) (hv : ContDiff ℝ 1 v) (t₀ : ℝ) {R Δ : ℝ}
    (hΔ : ∀ s : ℝ, |s| ≤ R → ‖deriv v (t₀ + s) - deriv v t₀‖ ≤ Δ)
    {p q : ℝ × ℝ} (hp : |p.1| ≤ R) (hq : |q.1| ≤ R) :
    ‖Work.RPB.B1a.straightenMap v t₀ p - Work.RPB.B1a.straightenMap v t₀ q
        - (((p.1 : ℝ) - q.1 : ℝ) + ((p.2 : ℝ) - q.2 : ℝ) * Complex.I) * deriv v t₀‖
      ≤ |p.1 - q.1| * Δ := by
  have hd : Differentiable ℝ v := hv.differentiable_one
  -- The vertical coordinates cancel exactly, leaving the horizontal error of the curve.
  have halg : straightenMap v t₀ p - straightenMap v t₀ q
        - (((p.1 : ℝ) - q.1 : ℝ) + ((p.2 : ℝ) - q.2 : ℝ) * Complex.I) * deriv v t₀
      = (v (t₀ + p.1) - v t₀ - p.1 • deriv v t₀)
        - (v (t₀ + q.1) - v t₀ - q.1 • deriv v t₀) := by
    simp only [straightenMap, Complex.real_smul]
    push_cast
    ring
  rw [halg]
  -- Mean value estimate on the interval spanned by `p.1` and `q.1`.
  have hp' : p.1 ∈ Set.Icc (min q.1 p.1) (max q.1 p.1) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  have hq' : q.1 ∈ Set.Icc (min q.1 p.1) (max q.1 p.1) :=
    ⟨min_le_left _ _, le_max_left _ _⟩
  have hdiff : ∀ x ∈ Set.Icc (min q.1 p.1) (max q.1 p.1),
      DifferentiableAt ℝ (fun s : ℝ => v (t₀ + s) - v t₀ - s • deriv v t₀) x := by
    intro x _
    have hA : HasDerivAt (fun y : ℝ => v (t₀ + y)) (deriv v (t₀ + x)) x :=
      (hd (t₀ + x)).hasDerivAt.comp_const_add t₀ x
    have hB : HasDerivAt (fun _ : ℝ => v t₀) 0 x := hasDerivAt_const x (v t₀)
    have hC : HasDerivAt (fun y : ℝ => y • deriv v t₀) (deriv v t₀) x := by
      simpa using (hasDerivAt_id x).smul_const (deriv v t₀)
    exact ((hA.sub hB).sub hC).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (min q.1 p.1) (max q.1 p.1),
      ‖deriv (fun s : ℝ => v (t₀ + s) - v t₀ - s • deriv v t₀) x‖ ≤ Δ := by
    intro x hx
    rw [congrFun (deriv_affineCorrection v hd t₀) x]
    refine hΔ x ?_
    rw [abs_le] at hp hq ⊢
    constructor
    · have h1 : -R ≤ min q.1 p.1 := le_min (by linarith [hq.1]) (by linarith [hp.1])
      linarith [hx.1]
    · have h2 : max q.1 p.1 ≤ R := max_le (by linarith [hq.2]) (by linarith [hp.2])
      linarith [hx.2]
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _) hq' hp'
  rw [Real.norm_eq_abs, mul_comm] at hmvt
  exact hmvt

end Work.RPB.B1a
