/-
# The low/spike/tail decomposition of the CKMRV layer on the tangency region

The CKMRV contour integral `∫_0^∞ K(τ,it) e^{-πr²t} dt` is an integral along the *imaginary
axis*.  For `τ` in the tangency region (near `±1/2 + i/2 ∈ ∂𝒟`) the pole of `z ↦ K(τ,z)` at
`z₁ = poleOne τ` (which is `TS•τ` when `Re τ > 0` and `TST•τ` when `Re τ < 0`) approaches
the contour point `z = i`; the modulus of the integrand blows up like `1/‖z₁ - iℝ‖`, and the
*unsigned* integral diverges logarithmically, while the signed contour integral stays bounded.

The cut at `t = 1` of the paper's layer `paperLayer` (i.e. the pieces `layerLow` and
`layerTrunc`) is therefore *not* adapted to this region: each of the two pieces has a
logarithmically divergent `τ → ∂𝒟` limit that cancels between them.  The decomposition used
here instead cuts at `1/2` and `3/2`, so that the pole (whose height lies in `(0.78, 1.28)`)
sits in the *interior* of the middle window `[1/2,3/2]`, where the signed contour shift of
Cauchy's theorem makes the integral bounded and exponentially decaying in `x = r²`:

* `tangLow  τ x = ∫_0^{1/2} K(τ,it)e^{-πxt}dt`     — below the poles, flat at the cusp `0`;
* `tangSpike τ x = ∫_{1/2}^{3/2} K(τ,it)e^{-πxt}dt` — the contoured window;
* `tangTail τ x = ∫_{3/2}^∞ (K - Aexp)(τ,it)e^{-πxt}dt` — above every pole of `z ↦ K(τ,z)`,
  where the cusp-`i∞` expansion holds;
* `tangA τ x = ∫_1^{3/2} Aexp(τ,it)e^{-πxt}dt` — the compact part of the non-decaying piece.

The `tangLayer` of `tangLayerDefs` is `4 sin²(πr²/2)·(tangLow + tangSpike + tangTail - tangA)
+ highPart`, punctured at `r = 0`; it agrees with `paperLayer` (hence with `kernelTransform`)
away from `r = 0`.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRect
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane

noncomputable section

/-- **The closed tangency region**: a compact superset of `closure ctanRegion` on which every
orbit-theoretic input of the tangency analysis holds (no coincidence with the contour at
heights `≤ 1/2` or `≥ 3/2`, and the rectangle `[0,1/4] × [1/2,3/2]` contains only the pole
`poleOne τ`). -/
def ctanCl : Set ℍ :=
  {τ | (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 5 / 8 ∧
    (1 : ℝ) / 2 ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ∧ (1 : ℝ) / 2 ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ∧
    (‖(τ : ℂ) - ctanP‖ ≤ 1 / 8 ∨ ‖(τ : ℂ) - ctanM‖ ≤ 1 / 8)}

lemma ctanRegion_subset_ctanCl {τ : ℍ} (hτ : τ ∈ ctanRegion) : τ ∈ ctanCl := by
  obtain ⟨⟨hy1, hy2⟩, hxcase⟩ := ctanRegion_bounds τ hτ
  refine ⟨hy1, le_of_lt hy2, le_of_lt (hτ.1).2.2.1, le_of_lt (hτ.1).2.2.2, ?_⟩
  rcases hτ.2.2.2 with h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inr (le_of_lt h)

lemma isClosed_ctanCl : IsClosed (ctanCl : Set ℍ) := by
  have h1 : IsClosed {τ : ℍ | (1 : ℝ) / 2 ≤ τ.im} := isClosed_le continuous_const continuous_im
  have h2 : IsClosed {τ : ℍ | τ.im ≤ 5 / 8} := isClosed_le continuous_im continuous_const
  have h3 : IsClosed {τ : ℍ | (1 : ℝ) / 2 ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖} :=
    isClosed_le continuous_const ((continuous_coe.sub continuous_const).norm)
  have h4 : IsClosed {τ : ℍ | (1 : ℝ) / 2 ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖} :=
    isClosed_le continuous_const ((continuous_coe.add continuous_const).norm)
  have h5 : IsClosed {τ : ℍ | ‖(τ : ℂ) - ctanP‖ ≤ 1 / 8} :=
    isClosed_le ((continuous_coe.sub continuous_const).norm) continuous_const
  have h6 : IsClosed {τ : ℍ | ‖(τ : ℂ) - ctanM‖ ≤ 1 / 8} :=
    isClosed_le ((continuous_coe.sub continuous_const).norm) continuous_const
  have h : ctanCl = {τ : ℍ | (1 : ℝ) / 2 ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ 5 / 8} ∩
      {τ : ℍ | (1 : ℝ) / 2 ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖} ∩
      {τ : ℍ | (1 : ℝ) / 2 ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖} ∩
      ({τ : ℍ | ‖(τ : ℂ) - ctanP‖ ≤ 1 / 8} ∪ {τ : ℍ | ‖(τ : ℂ) - ctanM‖ ≤ 1 / 8}) := by
    ext τ
    simp only [ctanCl, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [h]
  exact ((((h1.inter h2).inter h3).inter h4).inter (h5.union h6))

lemma closure_ctanRegion_subset_ctanCl : closure ctanRegion ⊆ ctanCl := by
  refine closure_minimal ?_ isClosed_ctanCl
  intro τ hτ
  obtain ⟨hD, h1, h2, hb⟩ := hτ
  refine ⟨h1, ?_, le_of_lt hD.2.2.1, le_of_lt hD.2.2.2, ?_⟩
  · rcases hb with h | h
    · have hcoe : ((τ : ℂ) - ctanP).im = τ.im - 1 / 2 := by
        simp [ctanP, Complex.sub_im]
      have hle : |τ.im - 1 / 2| ≤ 1 / 8 := by
        have h2' := Complex.abs_im_le_norm ((τ : ℂ) - ctanP)
        rw [hcoe] at h2'
        exact le_of_lt (lt_of_le_of_lt h2' h)
      exact by linarith [(abs_le.mp hle).2]
    · have hcoe : ((τ : ℂ) - ctanM).im = τ.im - 1 / 2 := by
        simp [ctanM, Complex.sub_im]
      have hle : |τ.im - 1 / 2| ≤ 1 / 8 := by
        have h2' := Complex.abs_im_le_norm ((τ : ℂ) - ctanM)
        rw [hcoe] at h2'
        exact le_of_lt (lt_of_le_of_lt h2' h)
      exact by linarith [(abs_le.mp hle).2]
  · rcases hb with h | h
    · exact Or.inl (le_of_lt h)
    · exact Or.inr (le_of_lt h)

/-- `ctanCl` is bounded (in the hyperbolic metric). -/
lemma isBounded_ctanCl : Bornology.IsBounded (ctanCl : Set ℍ) := by
  rw [Metric.isBounded_iff_subset_closedBall (UpperHalfPlane.I)]
  refine ⟨10, fun τ hτ => ?_⟩
  obtain ⟨hy1, hy2, h3, h4, hb⟩ := hτ
  rw [Metric.mem_closedBall]
  have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 3 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
    rw [show ((τ : ℂ) - Complex.I).re = τ.re by simp,
      show ((τ : ℂ) - Complex.I).im = τ.im - 1 by simp] at h
    have hre : |τ.re| ≤ 1 := by
      rcases hb with hbP | hbM
      · have hcoe : ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 := by
          simp [ctanP, Complex.sub_re]
        have hle : |τ.re - 1 / 2| ≤ 1 / 8 := by
          have h2' := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
          rw [hcoe] at h2'
          exact le_trans h2' hbP
        have hb' := abs_le.mp hle
        rw [abs_le]
        constructor <;> linarith [hb'.1, hb'.2]
      · have hcoe : ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 := by
          simp [ctanM, Complex.sub_re]
        have hle : |τ.re + 1 / 2| ≤ 1 / 8 := by
          have h2' := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
          rw [hcoe] at h2'
          exact le_trans h2' hbM
        have hb' := abs_le.mp hle
        rw [abs_le]
        constructor <;> linarith [hb'.1, hb'.2]
    have him : |τ.im - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith [hre, him]
  have hstep : dist τ UpperHalfPlane.I ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * 1) := by
    have := UpperHalfPlane.dist_le_dist_coe_div_sqrt τ UpperHalfPlane.I
    simpa [UpperHalfPlane.coe_I, UpperHalfPlane.I_im, dist_eq_norm] using this
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt (τ.im * 1) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  calc dist τ UpperHalfPlane.I ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * 1) := hstep
    _ ≤ 3 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
    _ = 6 := by norm_num
    _ ≤ 10 := by norm_num

lemma isCompact_ctanCl : IsCompact (ctanCl : Set ℍ) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_ctanCl, isBounded_ctanCl⟩

/-- The Gaussian weight `e^{-π x t}` of the contour integral. -/
def tangGauss (x t : ℝ) : ℂ := Complex.exp (-(Real.pi * x * t))

/-- The `low` piece: the contour integral below the poles. -/
def tangLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..(1 / 2), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * tangGauss x t

/-- The `spike` piece: the window containing the pole of `z ↦ K(τ,z)`. -/
def tangSpike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in (1 / 2 : ℝ)..(3 / 2), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * tangGauss x t

/-- The `tail` piece: above every pole of `z ↦ K(τ,z)`, with the cusp expansion subtracted. -/
def tangTail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioi (3 / 2 : ℝ),
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
      * tangGauss x t

/-- The compact part `∫_1^{3/2} Aexp(τ,it)e^{-πxt}dt` of the non-decaying piece. -/
def tangA (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..(3 / 2), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * tangGauss x t

/-- The `x`-profile of the decomposition: `tangLow + tangSpike + tangTail - tangA`. -/
def tangPhi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  tangLow ℓ d τ x + tangSpike ℓ d τ x + tangTail ℓ d τ x - tangA ℓ d τ x

/-- **The layer used for the tangency region**: the `low + spike + tail - A` decomposition times
`4 sin²(πr²/2)`, plus the paper's `highPart`, punctured at `r = 0` (where the paper's layer has
the non-zero limit `i·𝒢_{0,1}(τ)` while both `kernelTransform` and this layer take the value
`0`). -/
def tangLayer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  if r = 0 then 0
  else sinSq r * tangPhi ℓ d τ (r ^ 2) + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r

end

end Work.Asymptotics.HalfFunnel
