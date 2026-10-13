import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.Cyl.Coords
import Submission.Work.FTS_BSIdentP.Slim.HasDerivAtOddExtensionZero
import Submission.Work.FTS_BSIdentP.Slim.DerivSliceEqFderiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity at `θ = 0` of the `θ`-derivative of the odd extension of `Φ`

Let `Φ` be a family of self-similar profiles which, near every point `(w, θ)` of the strip
`-1 < w`, `|θ| < π/2 + 1`, is `C²` as a function of `(w, θ)` (hypothesis `hsm`), and which
vanishes on the axis `θ = 0` for `w > 0` (`h0`).  Then the `θ`-derivative of the odd extension
in `θ`,

  `G = fun w θ => PhiOdd Φ w θ τ = if 0 ≤ θ then Φ w θ τ else -(Φ w (-θ) τ)`,

is continuous at `(w₀, 0)` for every `w₀ > 0`.

Mathematically the reason is that the odd extension of a `C¹` function vanishing at `0` is again
`C¹`, with derivative the *even* function `θ ↦ ∂_θΦ(w, |θ|, τ)`: the two one-sided derivatives at
`θ = 0` agree precisely because `Φ w 0 τ = 0`, and the resulting derivative is continuous because
`∂_θΦ` is continuous (indeed, because `(w, θ) ↦ ∂_θΦ(w, θ, τ)`, which is the Fréchet derivative
of `Φ` evaluated in the direction `(0,1)`, is continuous by `ContDiffAt.continuousAt_fderiv`).

The formal content is therefore

* a pointwise evaluation of `pdZ G` — `pdZ_PhiOdd_eq_deriv` below, splitting on the sign of `θ`
  (`θ > 0` and `θ < 0` are the two smooth branches; `θ = 0` is the odd-extension-at-`0` lemma
  `hasDerivAt_oddExtension_zero`), and
* the identification of `fderiv ℝ Φ · (0,1)` with the `θ`-slice derivative
  (`deriv_slice_eq_fderiv`), which together with the continuity of `fderiv` gives the result.

Both auxiliary facts are proved separately (`hasDerivAt_oddExtension_zero`,
`deriv_slice_eq_fderiv`).
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

/-- **The pointwise value of the `θ`-derivative of the odd extension** in the strip
`|θ| < 1`, `w > 0`: it is the `θ`-derivative of `Φ` evaluated at `|θ|` (the derivative of the
odd extension is even).  This is the pointwise core of `continuousAt_pdZ_G_zero`. -/
theorem pdZ_PhiOdd_eq_deriv {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < 1) :
    Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ
      = deriv (fun θ' => Φ w θ' τ) |θ| := by
  have hd0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, 0) := by
    refine ((hsm w 0 (by linarith) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).of_le ?_).differentiableAt_one
    norm_num
  show deriv (fun θ' => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) θ = deriv (fun θ' => Φ w θ' τ) |θ|
  rcases lt_trichotomy θ 0 with h | h | h
  · -- `θ < 0`: the odd branch, differentiated with the chain rule
    rw [abs_of_neg h]
    have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => -Φ w (-θ') τ := by
      filter_upwards [isOpen_Iio.mem_nhds h] with θ' hθ'
      rw [Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ')]
    rw [Filter.EventuallyEq.deriv_eq hev]
    change deriv (-(fun θ' : ℝ => Φ w (-θ') τ)) θ = deriv (fun θ' : ℝ => Φ w θ' τ) (-θ)
    rw [deriv.neg]
    have h2 : deriv (fun θ' : ℝ => Φ w (-θ') τ) θ = - deriv (fun y : ℝ => Φ w y τ) (-θ) :=
      deriv_comp_neg (fun y : ℝ => Φ w y τ) θ
    rw [h2]
    ring
  · -- `θ = 0`: the odd extension is differentiable there with derivative `∂_θ Φ w 0 τ`
    subst h
    simp only [abs_zero]
    have hfun : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ)
        = fun θ : ℝ => if 0 ≤ θ then Φ w θ τ else -Φ w (-θ) τ := rfl
    have hcur : HasDerivAt (fun t : ℝ => (w, t)) (0, 1) 0 :=
      (hasDerivAt_const 0 w).prodMk (hasDerivAt_id 0)
    have hsl : HasDerivAt (fun θ' => Φ w θ' τ)
        (fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, 0) (0, 1)) 0 :=
      hd0.hasFDerivAt.comp_hasDerivAt 0 hcur
    have hc := hasDerivAt_oddExtension_zero (h0 w hw) hsl
    rw [hfun, hc.deriv]
    exact (deriv_slice_eq_fderiv (F := fun x y => Φ x y τ) hd0).symm
  · -- `θ > 0`: the smooth branch
    rw [abs_of_pos h]
    have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => Φ w θ' τ := by
      filter_upwards [isOpen_Ioi.mem_nhds h] with θ' hθ'
      rw [Work.FTS.BSIdent.PhiOdd_of_nonneg hθ'.le]
    rw [Filter.EventuallyEq.deriv_eq hev]

theorem continuousAt_pdZ_G_zero {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) p.1 p.2)
      (w₀, 0) := by
  -- `Φ(·,·,τ)` is `C²`, hence `fderiv` is continuous at `(w₀, 0)` (`ContDiffAt` version)
  have hC2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, 0) :=
    hsm w₀ 0 (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hfd : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) q) (w₀, 0) :=
    hC2.continuousAt_fderiv (by norm_num)
  have hfd1 : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) q (0, 1)) (w₀, 0) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).continuous.continuousAt).comp hfd
  -- composing with the (continuous) folding map `p ↦ (p.1, |p.2|)`
  have hpair : ContinuousAt (fun p : ℝ × ℝ => (p.1, |p.2|)) (w₀, 0) :=
    continuous_fst.continuousAt.prodMk
      (continuous_abs.continuousAt.comp continuous_snd.continuousAt)
  have hpair2 : Filter.Tendsto (fun p : ℝ × ℝ => (p.1, |p.2|)) (𝓝 (w₀, 0)) (𝓝 (w₀, 0)) := by
    simpa using hpair.tendsto
  have hcont : ContinuousAt (fun p : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (p.1, |p.2|) (0, 1)) (w₀, 0) := by
    have ht : Filter.Tendsto (fun p : ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (p.1, |p.2|) (0, 1)) (𝓝 (w₀, 0))
        (𝓝 (fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, |0|) (0, 1))) := by
      simpa [Function.comp_def] using hfd1.tendsto.comp hpair2
    exact ht
  refine hcont.congr ?_
  -- on the neighbourhood `|p.1 - w₀| < w₀/2`, `|p.2| < 1` the two functions agree
  have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, 0), |p.1 - w₀| < w₀ / 2 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
    · simp only [Set.mem_ofPred_eq]; rw [sub_self, abs_zero]; linarith
  have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, 0), |p.2| < 1 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
    · simp
  filter_upwards [h1, h2] with p hp1 hp2
  have hpw : 0 < p.1 := by
    have h := abs_lt.mp hp1
    linarith [h.1, h.2, hw₀]
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (p.1, |p.2|) := by
    have h₁ : 0 < p.1 := hpw
    have h₂ : -Real.pi / 2 - 1 < |p.2| := by linarith [abs_nonneg p.2, Real.pi_pos]
    have h₃ : |p.2| < Real.pi / 2 + 1 := by linarith [Real.pi_pos]
    exact ((hsm p.1 |p.2| h₁ h₂ h₃).of_le (by norm_num)).differentiableAt_one
  rw [pdZ_PhiOdd_eq_deriv hsm h0 hpw hp2]
  exact (deriv_slice_eq_fderiv (F := fun x y => Φ x y τ) hd).symm

end Work.FTS.BSIdentP.Levels
