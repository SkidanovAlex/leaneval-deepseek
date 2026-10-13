/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets.pinHardy` — the angular Hardy inequality behind the pinning estimate

The pinning estimate `PkgJets.pinningBound` reduces, through the reconstruction
`∂_θ(cos θ·Ψ) = cos θ · Vop Ψ`, to the following one-dimensional weighted Hardy inequality:
with `A := cos θ·Ψ`, `A' := cos θ·Vop Ψ`, `ν := sin(2θ)^{-η}`,

`∫_θ A²·W₁ ≤ K · ∫_θ (A')²·W₂`,   `W₁ = ν/cos⁴θ`, `W₂ = ν/cos²θ`,

for `A` whose `π/2`-boundary value vanishes (`cos θ·Ψ → 0`, the *pinning*).  The proof is the
classical proof of the weighted Hardy inequality: integrate `(A²Λ)' = 2AA'Λ + A²W₁` by parts
against the primitive `Λ` of `W₁` (here the primitive `pinL x` based at the *regular* end `x`, so
that the boundary term at `x` vanishes exactly), then Cauchy–Schwarz, with the two *pointwise /
quantitative* inputs

* `Λ(θ)² ≤ C₁·W₁(θ)·W₂(θ)` (`cosWeightPrim_sq_le`), which makes the Cauchy–Schwarz factor
  `∫ (A')²Λ²/W₁` comparable with `∫ (A')²W₂`;
* `(∫_T^{π/2} cos²s·sin(2s)^η ds)·Λ(T) ≤ C₂` (`cosWeightTail_le`), which bounds the boundary term
  at the singular end `π/2` using the *vanishing* of `A` there (the pinning, through the a-priori
  bound `A(T)² ≤ 2A(T')² + 2(∫_T^{T'}cos·V)² → 2(∫_T^{T'}cos·V)²`).

The two inputs are stated here as *hypotheses* `hLamB`, `hTailB`, so that this module is
independent of the two numerical lemmas; `PkgJets.pinningBound` instantiates them.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_EllLimOK.PkgJets.pinWeights
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## The two slices, and the running primitive -/

/-- The angular slice `A θ = cos θ · Ψ(z,θ)`. -/
def pinA (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun θ => Real.cos θ * Ψ z θ

/-- The angular slice `θ ↦ Vop Ψ(z,θ)`. -/
def pinV (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun θ => Work.Construction.Vop Ψ z θ

/-- The running primitive `Λ_x θ = ∫_x^θ W₁` of `W₁` based at `x`. -/
def pinL (x : ℝ) : ℝ → ℝ := fun θ => ∫ s in x..θ, wOne s

/-! ## Continuity of the pieces on subintervals of the open quadrant -/

theorem continuousOn_wNu {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (π / 2)) : ContinuousOn wNu s := by
  have h1 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) s :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact h1.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo (hs hx))))

theorem continuousOn_wOne {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (π / 2)) : ContinuousOn wOne s := by
  have h1 : ContinuousOn (fun θ : ℝ => wNu θ / (Real.cos θ) ^ 4) s :=
    (continuousOn_wNu hs).div (Real.continuous_cos.continuousOn.pow 4)
      (fun x hx => pow_ne_zero 4 (ne_of_gt (cos_pos_of_mem_Ioo (hs hx))))
  exact h1

/-- The `θ`-slice of an open-quadrant-smooth `Ψ` is differentiable, with derivative `pth Ψ`. -/
theorem hasDerivAt_slice {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun s => Ψ z s) (Work.Spaces.pth Ψ z θ) θ := by
  have hs : ContDiffOn ℝ 1 (fun s => Ψ z s) (Set.Ioo 0 (π / 2)) :=
    (hsm.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have h2 : DifferentiableAt ℝ (fun s => Ψ z s) θ :=
    (hs.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  simpa only [Work.Spaces.pth] using h2.hasDerivAt

/-- `θ ↦ A θ = cos θ·Ψ(z,θ)` has derivative `cos θ·Vop Ψ(z,θ)`. -/
theorem pinA_hasDerivAt {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (pinA Ψ z) (Real.cos θ * pinV Ψ z θ) θ := by
  have h1 : HasDerivAt (fun s => Real.cos s * Ψ z s)
      (-Real.sin θ * Ψ z θ + Real.cos θ * Work.Spaces.pth Ψ z θ) θ :=
    (Real.hasDerivAt_cos θ).mul (hasDerivAt_slice hsm hz hθ)
  refine h1.congr_deriv ?_
  show -Real.sin θ * Ψ z θ + Real.cos θ * Work.Spaces.pth Ψ z θ
    = Real.cos θ * Work.Construction.Vop Ψ z θ
  rw [Work.FTS_EllLimOK.cos_mul_Vop_eq Ψ hθ]
  ring

theorem continuousOn_pinA {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (π / 2)) :
    ContinuousOn (pinA Ψ z) s := by
  have h1 : ContinuousOn (fun θ => Ψ z θ) s := ((hsm.curry_θ hz).continuousOn).mono hs
  exact Real.continuous_cos.continuousOn.mul h1

theorem continuousOn_pinV {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (π / 2)) :
    ContinuousOn (pinV Ψ z) s := by
  have h1 : ContinuousOn (fun θ => Work.Spaces.pth Ψ z θ) s :=
    ((hsm.pth.curry_θ hz).continuousOn).mono hs
  have h2 : ContinuousOn (fun θ => Real.tan θ * Ψ z θ) s :=
    ContinuousOn.mul
      (Real.continuousOn_tan.mono (fun x hx => ne_of_gt (cos_pos_of_mem_Ioo (hs hx))))
      ((hsm.curry_θ hz).continuousOn.mono hs)
  have h3 : ContinuousOn (fun θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ) s := h1.sub h2
  refine h3.congr ?_
  intro θ _
  simp only [pinV, Work.Construction.Vop]

/-- `Λ_x` has derivative `W₁` on `(x,π/2)` for `x > 0`. -/
theorem pinL_hasDerivAt {x : ℝ} (hx : 0 < x) {θ : ℝ} (hθ : θ ∈ Set.Ioo x (π / 2)) :
    HasDerivAt (pinL x) (wOne θ) θ := by
  have hθ' : θ ∈ Set.Ioo 0 (π / 2) := ⟨lt_trans hx hθ.1, hθ.2⟩
  have hsub : Set.uIcc x θ ⊆ Set.Ioo 0 (π / 2) := by
    intro y hy
    rw [Set.uIcc_of_le hθ.1.le] at hy
    exact ⟨lt_of_lt_of_le hx hy.1, lt_of_le_of_lt hy.2 hθ.2⟩
  have hint : IntervalIntegrable wOne volume x θ :=
    ContinuousOn.intervalIntegrable (continuousOn_wOne hsub)
  have hcont : ContinuousAt wOne θ :=
    (continuousOn_wOne (fun y hy => hy)).continuousAt (isOpen_Ioo.mem_nhds hθ')
  have hsm' : StronglyMeasurableAtFilter wOne (𝓝 θ) volume :=
    measurable_wOne.aestronglyMeasurable.stronglyMeasurableAtFilter
  exact intervalIntegral.integral_hasDerivAt_right hint hsm' hcont
/-- The primitive based at `x` is nonnegative on `[x,π/2]`. -/
theorem pinL_nonneg {x θ : ℝ} (hx : 0 ≤ x) (hxθ : x ≤ θ) (hθ : θ ≤ π / 2) :
    0 ≤ pinL x θ := by
  rw [pinL]
  exact intervalIntegral.integral_nonneg hxθ
    (fun u hu => wOne_nonneg ⟨le_trans hx hu.1, le_trans hu.2 hθ⟩)

/-- The primitive `pinL x` is continuous on `[x,y]` for `0 < x ≤ y < π/2`. -/
theorem continuousOn_pinL_Icc {x y : ℝ} (hx : 0 < x) (hy : y < π / 2) (hxy : x ≤ y) :
    ContinuousOn (pinL x) (Set.Icc x y) := by
  have hsub : Set.Icc x y ⊆ Set.Ioo 0 (π / 2) := fun t ht =>
    ⟨lt_of_lt_of_le hx ht.1, lt_of_le_of_lt ht.2 hy⟩
  have hint : IntegrableOn wOne (Set.Icc x y) :=
    (continuousOn_wOne hsub).integrableOn_compact isCompact_Icc
  have hprim := intervalIntegral.continuousOn_primitive hint
  refine hprim.congr ?_
  intro θ hθ
  rw [pinL, intervalIntegral.integral_of_le hθ.1]

/-- The derivative of `pinL x` at `x` itself. -/
theorem pinL_hasDerivAt_self {x : ℝ} (hx : 0 < x) (hx2 : x < π / 2) :
    HasDerivAt (pinL x) (wOne x) x := by
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · rw [IntervalIntegrable]
    constructor <;> simp
  · exact measurable_wOne.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuousOn_wOne (fun y hy => hy)).continuousAt (isOpen_Ioo.mem_nhds ⟨hx, hx2⟩)


end Work.FTS_EllLimOK.PkgJets
