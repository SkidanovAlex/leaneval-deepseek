import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.curve_tangent_chart

/-!
# The chart direction of a curve in a local graph chart has a non-vanishing chart coordinate

Let `K ⊆ ℝⁿ` be a set which, on an open set `U`, is the graph of `η` over the `i`-th coordinate
(`IsGraphChart K i U η`).  The chart tangent direction at a point `y ∈ U ∩ K` is
`eᵢ + η'(yᵢ)(1)`, whose `i`-th coordinate is `1` because `η` takes values in the coordinate
hyperplane `xᵢ = 0`.

Consequently, if `γ` is a `C^∞` curve with values in `K`, `γ t₀ ∈ U`, and `γ'(t₀) ≠ 0`, then the
`i`-th coordinate of `γ'(t₀)` does not vanish: by `curve_tangent_chart`, `γ'(t₀)` is a non-zero
multiple of the chart tangent direction.

* `coord_fderiv_apply_one` — the `i`-th coordinate of `fderiv ℝ f x 1` is the derivative of the
  `i`-th coordinate of `f`;
* `coord_fderiv_ne_zero` — the statement of the file.
-/

namespace Work.ManifoldParity

noncomputable section

open Set

variable {n : ℕ}

/-- The `i`-th coordinate of `fderiv ℝ f x 1` is the derivative at `x` of the `i`-th coordinate of
`f`, evaluated at `1`. -/
theorem coord_fderiv_apply_one (f : ℝ → EuclideanSpace ℝ (Fin n)) (x : ℝ) (i : Fin n)
    (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ f x (1 : ℝ)) i = fderiv ℝ (fun u => (f u) i) x (1 : ℝ) := by
  have hproj : ∀ v : EuclideanSpace ℝ (Fin n),
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i) v = v.ofLp i := by
    intro v; rw [PiLp.proj_apply]
  have hfun : (fun u : ℝ => (f u) i)
      = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i) ∘ f := by
    funext u; rw [Function.comp_apply, hproj]
  rw [hfun, ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp x
    hf.hasFDerivAt).fderiv]
  simp [hproj]

theorem coord_fderiv_ne_zero {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {i : Fin n}
    {U : Set (EuclideanSpace ℝ (Fin n))} {η : ℝ → EuclideanSpace ℝ (Fin n)}
    (hchart : Work.ManifoldParity.IsGraphChart K i U η)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (hγK : ∀ t, γ t ∈ K) {t₀ : ℝ}
    (hγU : γ t₀ ∈ U) (hvel : fderiv ℝ γ t₀ 1 ≠ 0) :
    ((fderiv ℝ γ t₀ 1) i) ≠ 0 := by
  obtain ⟨c, hc, hfeq⟩ := curve_tangent_chart K i U η hchart γ hsm hγK t₀ hγU hvel
  obtain ⟨-, hηsm, hηi, -⟩ := hchart
  -- `η` is constant in the `i`-th coordinate, so the chart tangent has `i`-th coordinate `1`.
  have hcoordη : (deriv η (γ t₀ i)) i = 0 := by
    have hd : DifferentiableAt ℝ η (γ t₀ i) :=
      (hηsm.contDiffAt).differentiableAt (by simp)
    show (fderiv ℝ η (γ t₀ i) (1 : ℝ)) i = 0
    rw [coord_fderiv_apply_one η (γ t₀ i) i hd]
    have hconst : (fun u : ℝ => (η u) i) = fun _ => (0 : ℝ) := by
      funext u; exact hηi u
    rw [hconst]
    simp
  intro hzero
  have hcon := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hfeq
  rw [hzero] at hcon
  simp [hcoordη] at hcon
  exact hc hcon.symm

end

end Work.ManifoldParity
