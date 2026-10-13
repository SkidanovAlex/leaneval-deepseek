/-
Copyright: work module for the Elgindi finite-time singularity project.

# The self-adjointness (integration-by-parts) identity for `bslOp`

`Work.Elliptic.bslOp α` is the elliptic operator of (PolarBSL),
`L(Ψ) = -α²z²∂_zzΨ - α(5+α)z∂_zΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`.

This module proves that `bslOp α` is *symmetric* against the weight
`w(z,θ) = z^{(5-α)/α} cos θ` on the open quadrant `Q0 = (0,∞) × (0,π/2)`:

  `∫_{Q0} u·(bslOp α φ)·w = ∫_{Q0} (bslOp α u)·φ·w`

for `u` smooth on the open quadrant and `φ` smooth with compact support inside `Q0`.
The boundary terms of the two integrations by parts vanish because `φ` and all its
derivatives vanish in a neighbourhood of the boundary of `Q0`.

## Structure of the proof

* `Rz α Ψ = -(α²z²∂_zzΨ + α(5+α)z∂_zΨ)` is the radial part, so that
  `bslOp α Ψ = Rz α Ψ + Lzero Ψ`.
* Writing `D = (u·bslOp α φ - (bslOp α u)·φ)·w` and `D = Drad + Dang` with `Drad` the radial
  and `Dang` the angular contribution, the two one-variable identities

  `∫_a^b (f (Rz g) - (Rz f) g) z^{(5-α)/α} dz = 0` (weight `z^{(5-α)/α}`, `g` supported in `[a,b]`),
  `∫_c^d (f (Lzero g) - (Lzero f) g) cos θ dθ = 0` (weight `cos θ`, `g` supported in `[c,d]`)

  are applied on the two slices.  They are the content of
  `Work.EllipticEst.ModalSolution.radial_ibp_zero` and
  `Work.EllipticEst.ModalSolution.angular_ibp_zero`.
* `Work.EllipticEst.ModalSolution.box_of_compactSupport` produces the box on which `φ` lives.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.pth_tan_mul
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.EllipticEst.ModalSolution.radial_ibp_zero
import Submission.Work.EllipticEst.ModalSolution.angular_ibp_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Slices of `C²` functions -/

/-- The `z`-slice of a `C²` function on a product of sets is `C²`. -/
theorem contDiffOn_slice_z_two {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ 2 (fun z => G z θ) s := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ)) s :=
    contDiffOn_id.prodMk (contDiffOn_const (c := θ))
  exact (hG.comp h1 (fun z _ => ⟨by assumption, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a `C²` function on a product of sets is `C²`. -/
theorem contDiffOn_slice_θ_two {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ 2 (fun θ => G z θ) t := by
  have h1 : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) t :=
    (contDiffOn_const (c := z)).prodMk contDiffOn_id
  exact (hG.comp h1 (fun θ _ => ⟨hz, by assumption⟩)).congr (fun θ _ => rfl)

/-! ## `Lzero` on a slice -/

/-- `Lzero` read on the `θ`-slice. -/
theorem Lzero_eq_slice (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero Ψ z θ
      = -deriv (deriv (fun θ' => Ψ z θ')) θ
        + deriv (fun θ' => Real.tan θ' * Ψ z θ') θ - 6 * Ψ z θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero]

/-! ## The radial part of `bslOp`, the weight, and the integrands -/

/-- The radial part `Rz α Ψ = -(α²z²∂_zzΨ + α(5+α)z∂_zΨ)` of `bslOp α`. -/
private def Rz (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
    + α * (5 + α) * z * Work.Spaces.pz Ψ z θ)

/-- The weight `w(z,θ) = z^{(5-α)/α} cos θ`. -/
private def weight (α : ℝ) (p : ℝ × ℝ) : ℝ := p.1 ^ ((5 - α) / α) * Real.cos p.2

private def DI (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => u p.1 p.2 * Work.Elliptic.bslOp α φ p.1 p.2 * weight α p

private def DJ (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Elliptic.bslOp α u p.1 p.2 * φ p.1 p.2 * weight α p

/-- The integrand of the difference of the two sides. -/
private def DD (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => DI α u φ p - DJ α u φ p

/-- The radial contribution to `DD`. -/
private def Drad (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (u p.1 p.2 * Rz α φ p.1 p.2 - Rz α u p.1 p.2 * φ p.1 p.2) * weight α p

/-- The angular contribution to `DD`. -/
private def Dang (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (u p.1 p.2 * Work.Elliptic.Lzero φ p.1 p.2
    - Work.Elliptic.Lzero u p.1 p.2 * φ p.1 p.2) * weight α p

/-- `bslOp = Rz + Lzero`, hence `DD = Drad + Dang` pointwise. -/
theorem DD_eq (α : ℝ) (u φ : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    DD α u φ p = Drad α u φ p + Dang α u φ p := by
  simp only [DD, DI, DJ, Drad, Dang, Rz, Work.Elliptic.bslOp_apply]
  ring

/-! ## Continuity of the required pieces on the open quadrant -/

theorem isOpen_Q0 : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0

/-- `tan θ` is continuous on the open quadrant. -/
theorem continuousOn_tan_quad :
    ContinuousOn (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
  rw [show (fun p : ℝ × ℝ => Real.tan p.2) = fun p => Real.sin p.2 / Real.cos p.2 from by
    funext p; rw [Real.tan_eq_sin_div_cos]]
  refine ContinuousOn.div ((Real.continuous_sin.comp continuous_snd).continuousOn)
    ((Real.continuous_cos.comp continuous_snd).continuousOn) ?_
  intro p hp
  have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp2.1, Real.pi_pos],
    by linarith [hp2.2]⟩).ne'

theorem contDiffOn_pthIter_two {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.LocData.contDiffOn_pth isOpen_Q0
    (Work.FTS.LocData.contDiffOn_pth isOpen_Q0 hΨ)
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h

theorem contDiffOn_pzIter_two {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.LocData.contDiffOn_pz isOpen_Q0
    (Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hΨ)
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h

/-- `Lzero Ψ` is continuous on the open quadrant for `Ψ` smooth there. -/
theorem continuousOn_Lzero {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth isOpen_Q0 hΨ
  have hpth2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_pthIter_two hΨ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => -(Work.Spaces.pthIter 2 Ψ p.1 p.2)
      + (Ψ p.1 p.2 / Real.cos p.2 ^ 2 + Real.tan p.2 * Work.Spaces.pth Ψ p.1 p.2)
      - 6 * Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hpth2.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      hΨ.continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hpth.continuousOn
    have hcos : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_cos.comp continuous_snd).continuousOn
    have hcosne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
      intro p hp
      have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp2.1, Real.pi_pos],
        by linarith [hp2.2]⟩).ne'
    have hdiv : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2 / Real.cos p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      h2.div (hcos.pow 2) (fun p hp => pow_ne_zero 2 (hcosne p hp))
    have hmul : ContinuousOn
        (fun p : ℝ × ℝ => Real.tan p.2 * Work.Spaces.pth Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := continuousOn_tan_quad.mul h3
    exact ((h1.neg).add (hdiv.add hmul)).sub (h2.const_mul 6)
  refine hcont.congr (fun p hp => ?_)
  show Work.Elliptic.Lzero Ψ p.1 p.2 = -(Work.Spaces.pthIter 2 Ψ p.1 p.2)
    + (Ψ p.1 p.2 / Real.cos p.2 ^ 2 + Real.tan p.2 * Work.Spaces.pth Ψ p.1 p.2)
    - 6 * Ψ p.1 p.2
  have hp1 : p.1 ∈ Set.Ioi (0 : ℝ) := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  have hcosne : Real.cos p.2 ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp2.1, Real.pi_pos],
      by linarith [hp2.2]⟩).ne'
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Ψ p.1 θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ hΨ hp1
  have hdiff : DifferentiableAt ℝ (fun θ' => Ψ p.1 θ') p.2 :=
    (hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hp2)
  rw [← Work.Elliptic.pth_tan_mul Ψ p.1 p.2 hcosne hdiff]
  rfl

/-- The weight is continuous on the open quadrant. -/
theorem continuousOn_weight (α : ℝ) :
    ContinuousOn (weight α) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ ((5 - α) / α))
      Work.FTS.EllipticEst.Q0 :=
    (continuous_fst.continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_cos.comp continuous_snd).continuousOn
  exact h1.mul h2

/-- The radial integrand is continuous on the open quadrant. -/
theorem continuousOn_Drad (α : ℝ) {u φ : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry φ)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Drad α u φ) Work.FTS.EllipticEst.Q0 := by
  have hpzu : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hu).continuousOn
  have hpz2u : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (contDiffOn_pzIter_two hu).continuousOn
  have hpzφ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hφ).continuousOn
  have hpz2φ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (contDiffOn_pzIter_two hφ).continuousOn
  have hu' : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hu.continuousOn
  have hφ' : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hφ.continuousOn
  have hRzφ : ContinuousOn (fun p : ℝ × ℝ => Rz α φ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have heq : (fun p : ℝ × ℝ => Rz α φ p.1 p.2)
        = fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 φ p.1 p.2
            + α * (5 + α) * p.1 * Work.Spaces.pz φ p.1 p.2) := by
      funext p; simp only [Rz]
    rw [heq]
    exact (((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)).mul hpz2φ).add
      ((continuousOn_const.mul continuous_fst.continuousOn).mul hpzφ)).neg
  have hRzu : ContinuousOn (fun p : ℝ × ℝ => Rz α u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have heq : (fun p : ℝ × ℝ => Rz α u p.1 p.2)
        = fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) := by
      funext p; simp only [Rz]
    rw [heq]
    exact (((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)).mul hpz2u).add
      ((continuousOn_const.mul continuous_fst.continuousOn).mul hpzu)).neg
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ => u p.1 p.2 * Rz α φ p.1 p.2 - Rz α u p.1 p.2 * φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hu'.mul hRzφ).sub (hRzu.mul hφ')
  exact hprod.mul (continuousOn_weight α)

/-- The angular integrand is continuous on the open quadrant. -/
theorem continuousOn_Dang (α : ℝ) {u φ : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry φ)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Dang α u φ) Work.FTS.EllipticEst.Q0 := by
  have hu' : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hu.continuousOn
  have hφ' : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hφ.continuousOn
  have hLφ : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_Lzero hφ
  have hLu : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_Lzero hu
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ => u p.1 p.2 * Work.Elliptic.Lzero φ p.1 p.2
        - Work.Elliptic.Lzero u p.1 p.2 * φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hu'.mul hLφ).sub (hLu.mul hφ')
  exact hprod.mul (continuousOn_weight α)

/-! ## `bslOp` vanishes where its argument vanishes in a neighbourhood -/

/-- Every term of `bslOp α Ψ z θ` is a derivative (in `z` or `θ`) of a slice of `Ψ`, so if `Ψ`
vanishes on a neighbourhood of `(z,θ)` then `bslOp α Ψ z θ = 0`. -/
theorem bslOp_eq_zero_of_eventually_zero (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ q in 𝓝 (z, θ), Ψ q.1 q.2 = 0) :
    Work.Elliptic.bslOp α Ψ z θ = 0 := by
  obtain ⟨V, hVU, hVopen, hzθV⟩ := mem_nhds_iff.mp h
  have hVz : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hzθV
  have hVt : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hzθV
  have hevZ : (fun z' => Ψ z' θ) =ᶠ[𝓝 z] (fun _ => 0) :=
    hVz.mono (fun z' hz' => hVU hz')
  have hevT : (fun θ' => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => 0) :=
    hVt.mono (fun θ' ht' => hVU ht')
  have hevTtan : (fun θ' => Real.tan θ' * Ψ z θ') =ᶠ[𝓝 θ] (fun _ => 0) :=
    hVt.mono (fun θ' ht' => by
      have h0 : Ψ z θ' = 0 := hVU ht'
      simp [h0])
  have hevZ2 : (fun z' => Work.Spaces.pz Ψ z' θ) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hVz] with z' hz'
    have hmem : ∀ᶠ z'' in 𝓝 z', (z'', θ) ∈ V :=
      (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz'
    have hev : (fun z'' => Ψ z'' θ) =ᶠ[𝓝 z'] (fun _ => 0) :=
      hmem.mono (fun z'' hz'' => hVU hz'')
    rw [show Work.Spaces.pz Ψ z' θ = deriv (fun z'' => Ψ z'' θ) z' from rfl,
      Filter.EventuallyEq.deriv_eq hev]
    simp
  have hevT2 : (fun θ' => Work.Spaces.pth Ψ z θ') =ᶠ[𝓝 θ] (fun _ => 0) := by
    filter_upwards [hVt] with θ' ht'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds ht'
    have hev : (fun θ'' => Ψ z θ'') =ᶠ[𝓝 θ'] (fun _ => 0) :=
      hmem.mono (fun θ'' hθ'' => hVU hθ'')
    rw [show Work.Spaces.pth Ψ z θ' = deriv (fun θ'' => Ψ z θ'') θ' from rfl,
      Filter.EventuallyEq.deriv_eq hev]
    simp
  have hval : Ψ z θ = 0 := hVU hzθV
  have hpz0 : Work.Spaces.pz Ψ z θ = 0 := by
    rw [show Work.Spaces.pz Ψ z θ = deriv (fun z' => Ψ z' θ) z from rfl,
      Filter.EventuallyEq.deriv_eq hevZ]
    simp
  have hpz20 : Work.Spaces.pzIter 2 Ψ z θ = 0 := by
    rw [show Work.Spaces.pzIter 2 Ψ z θ = deriv (fun z' => Work.Spaces.pz Ψ z' θ) z from rfl,
      Filter.EventuallyEq.deriv_eq hevZ2]
    simp
  have hpth20 : Work.Spaces.pthIter 2 Ψ z θ = 0 := by
    rw [show Work.Spaces.pthIter 2 Ψ z θ = deriv (fun θ' => Work.Spaces.pth Ψ z θ') θ
      from rfl, Filter.EventuallyEq.deriv_eq hevT2]
    simp
  have hpthtan : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ = 0 := by
    rw [show Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        = deriv (fun θ' => Real.tan θ' * Ψ z θ') θ from rfl,
      Filter.EventuallyEq.deriv_eq hevTtan]
    simp
  rw [Work.Elliptic.bslOp_apply]
  simp only [hpz20, hpz0, Work.Elliptic.Lzero, hpth20, hpthtan, hval]
  ring

/-! ## The two one-variable IBP identities, applied to the slices -/

/-- The radial identity, applied to the slices of `u` and `φ` at the angle `θ`. -/
theorem radial_slice_zero (α : ℝ) {u φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hu2 : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hφ2 : ContDiffOn ℝ 2 (Function.uncurry φ) Work.FTS.EllipticEst.Q0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hg0 : ∀ z, z ∉ Set.Icc a b → φ z θ = 0) :
    ∫ z in Set.Icc a b, (u z θ * Rz α φ z θ - Rz α u z θ * φ z θ)
        * z ^ ((5 - α) / α) = 0 := by
  rw [show (∫ z in Set.Icc a b, (u z θ * Rz α φ z θ - Rz α u z θ * φ z θ)
        * z ^ ((5 - α) / α))
      = ∫ z in Set.Icc a b, ((fun z' => u z' θ) z
          * (-(α ^ 2 * z ^ 2 * deriv (deriv (fun z' => φ z' θ)) z
              + α * (5 + α) * z * deriv (fun z' => φ z' θ) z))
          - (-(α ^ 2 * z ^ 2 * deriv (deriv (fun z' => u z' θ)) z
              + α * (5 + α) * z * deriv (fun z' => u z' θ) z)) * (fun z' => φ z' θ) z)
          * z ^ ((5 - α) / α) from by
    apply setIntegral_congr_fun measurableSet_Icc
    intro z hz
    simp only [Rz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]]
  exact radial_ibp_zero (α := α) ha hab (contDiffOn_slice_z_two hu2 hθ)
    (contDiffOn_slice_z_two hφ2 hθ) hg0

/-- The angular identity, applied to the slices of `u` and `φ` at the radius `z`. -/
theorem angular_slice_zero {u φ : ℝ → ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    (hd : d < π / 2)
    (hu2 : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hφ2 : ContDiffOn ℝ 2 (Function.uncurry φ) Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) (hg0 : ∀ θ, θ ∉ Set.Icc c d → φ z θ = 0) :
    ∫ θ in Set.Icc c d, (u z θ * Work.Elliptic.Lzero φ z θ
        - Work.Elliptic.Lzero u z θ * φ z θ) * Real.cos θ = 0 := by
  have h := angular_ibp_zero (f := fun t => u z t) (g := fun t => φ z t) hc hcd hd
    (contDiffOn_slice_θ_two hu2 hz) (contDiffOn_slice_θ_two hφ2 hz) hg0
  refine (setIntegral_congr_fun measurableSet_Icc ?_).trans h
  intro θ hθ
  simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero]

/-! ## The main theorem -/

theorem bslOp_ibp (α : ℝ) {u φ : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (h1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => u p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0)
    (h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Elliptic.bslOp α u p.1 p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, u p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, (Work.Elliptic.bslOp α u p.1 p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  classical
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ := box_of_compactSupport hφc hφs
  have hsm_u : Work.FTS.EllipticEst.SmoothOpen u :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mpr hu
  have hsm_φ : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hbox_sub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hbox_meas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- ### the integrands
  have hint_Drad : MeasureTheory.IntegrableOn (Drad α u φ) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((continuousOn_Drad α hsm_u hsm_φ).mono hbox_sub)
  have hint_Dang : MeasureTheory.IntegrableOn (Dang α u φ) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((continuousOn_Dang α hsm_u hsm_φ).mono hbox_sub)
  -- ### `D` vanishes off the box
  have hzero : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ (Set.Icc a b ×ˢ Set.Icc c d),
      DD α u φ p = 0 := by
    rintro ⟨z, θ⟩ ⟨hpQ, hpB⟩
    have hφ0 : φ z θ = 0 :=
      hbox (z, θ) (fun hm => hpB ⟨⟨le_of_lt hm.1.1, le_of_lt hm.1.2⟩,
        ⟨le_of_lt hm.2.1, le_of_lt hm.2.2⟩⟩)
    have hev : ∀ᶠ q in 𝓝 (z, θ), φ q.1 q.2 = 0 := by
      have hpB' : ¬ (z ∈ Set.Icc a b ∧ θ ∈ Set.Icc c d) := fun hh =>
        hpB (by simp only [Set.mem_prod]; exact hh)
      have hcases : z < a ∨ b < z ∨ θ < c ∨ d < θ := by
        by_contra hcon
        have h1 : a ≤ z := le_of_not_gt (fun h => hcon (Or.inl h))
        have h2 : z ≤ b := le_of_not_gt (fun h => hcon (Or.inr (Or.inl h)))
        have h3 : c ≤ θ := le_of_not_gt (fun h => hcon (Or.inr (Or.inr (Or.inl h))))
        have h4 : θ ≤ d := le_of_not_gt (fun h => hcon (Or.inr (Or.inr (Or.inr h))))
        exact hpB' ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      rcases hcases with h | h | h | h
      · filter_upwards [(isOpen_Iio.prod isOpen_univ).mem_nhds
            (show (z, θ) ∈ Set.Iio a ×ˢ Set.univ from ⟨h, trivial⟩)] with q hq
        exact hbox q (fun hm => absurd hm.1.1 (not_lt.mpr (le_of_lt hq.1)))
      · filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds
            (show (z, θ) ∈ Set.Ioi b ×ˢ Set.univ from ⟨h, trivial⟩)] with q hq
        exact hbox q (fun hm => absurd hm.1.2 (not_lt.mpr (le_of_lt hq.1)))
      · filter_upwards [(isOpen_univ.prod isOpen_Iio).mem_nhds
            (show (z, θ) ∈ Set.univ ×ˢ Set.Iio c from ⟨trivial, h⟩)] with q hq
        exact hbox q (fun hm => absurd hm.2.1 (not_lt.mpr (le_of_lt hq.2)))
      · filter_upwards [(isOpen_univ.prod isOpen_Ioi).mem_nhds
            (show (z, θ) ∈ Set.univ ×ˢ Set.Ioi d from ⟨trivial, h⟩)] with q hq
        exact hbox q (fun hm => absurd hm.2.2 (not_lt.mpr (le_of_lt hq.2)))
    have hbsl : Work.Elliptic.bslOp α φ z θ = 0 := bslOp_eq_zero_of_eventually_zero α hev
    simp only [DD, DI, DJ, hφ0, hbsl, mul_zero, zero_mul, sub_self]
  -- ### the angular integral vanishes
  have hAng : ∀ z ∈ Set.Icc a b, (∫ θ in Set.Icc c d, Dang α u φ (z, θ)) = 0 := by
    intro z hz
    have hz1 : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le ha hz.1
    have hg0θ : ∀ θ, θ ∉ Set.Icc c d → φ z θ = 0 := fun θ hθ =>
      hbox (z, θ) (fun hm => hθ ⟨le_of_lt hm.2.1, le_of_lt hm.2.2⟩)
    have hang := angular_slice_zero hc hcd hd (hu 2) ((hφ 2).contDiffOn) hz1 hg0θ
    have hstep : (∫ θ in Set.Icc c d, Dang α u φ (z, θ))
        = z ^ ((5 - α) / α) * ∫ θ in Set.Icc c d, (u z θ * Work.Elliptic.Lzero φ z θ
            - Work.Elliptic.Lzero u z θ * φ z θ) * Real.cos θ := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [Dang, weight]; ring)
    rw [hstep, hang, mul_zero]
  have hAbox : ∫ p in (Set.Icc a b ×ˢ Set.Icc c d), Dang α u φ p = 0 := by
    rw [Measure.volume_eq_prod]
    rw [MeasureTheory.setIntegral_prod _ (by rwa [Measure.volume_eq_prod] at hint_Dang)]
    rw [show (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, Dang α u φ (z, θ))
        = ∫ z in Set.Icc a b, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Icc (fun z hz => hAng z hz)]
    simp
  -- ### the radial integral vanishes
  have hRad : ∀ θ ∈ Set.Icc c d, (∫ z in Set.Icc a b, Drad α u φ (z, θ)) = 0 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
    have hg0z : ∀ z, z ∉ Set.Icc a b → φ z θ = 0 := fun z hz =>
      hbox (z, θ) (fun hm => hz ⟨le_of_lt hm.1.1, le_of_lt hm.1.2⟩)
    have hrad := radial_slice_zero (α := α) ha hab (hu 2) ((hφ 2).contDiffOn) hθ' hg0z
    have hstep : (∫ z in Set.Icc a b, Drad α u φ (z, θ))
        = Real.cos θ * ∫ z in Set.Icc a b, (u z θ * Rz α φ z θ - Rz α u z θ * φ z θ)
            * z ^ ((5 - α) / α) := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Icc (fun z _ => by
        simp only [Drad, weight]; ring)
    rw [hstep, hrad, mul_zero]
  have hRbox : ∫ p in (Set.Icc a b ×ˢ Set.Icc c d), Drad α u φ p = 0 := by
    rw [Measure.volume_eq_prod]
    rw [MeasureTheory.setIntegral_prod _ (by rwa [Measure.volume_eq_prod] at hint_Drad)]
    rw [MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Icc a b))
      (ν := volume.restrict (Set.Icc c d)) (f := fun z θ => Drad α u φ (z, θ))
      (by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact hint_Drad)]
    rw [show (∫ θ in Set.Icc c d, ∫ z in Set.Icc a b, Drad α u φ (z, θ))
        = ∫ θ in Set.Icc c d, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hRad θ hθ)]
    simp
  -- ### assemble
  have hgoal : ∫ p in Work.FTS.EllipticEst.Q0, DD α u φ p = 0 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_Q0.measurableSet hbox_sub hzero]
    rw [setIntegral_congr_fun hbox_meas (fun p _ => DD_eq α u φ p)]
    rw [MeasureTheory.integral_add hint_Drad hint_Dang]
    rw [hRbox, hAbox]
    ring
  have hfinal : ∫ p in Work.FTS.EllipticEst.Q0, DI α u φ p
      = ∫ p in Work.FTS.EllipticEst.Q0, DJ α u φ p := by
    have hsub : (∫ p in Work.FTS.EllipticEst.Q0, DI α u φ p)
        - ∫ p in Work.FTS.EllipticEst.Q0, DJ α u φ p = 0 := by
      rw [← MeasureTheory.integral_sub (f := DI α u φ) (g := DJ α u φ) h1 h2]
      exact hgoal
    linarith
  exact hfinal

end Work.EllipticEst.ModalSolution
