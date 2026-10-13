import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shifted slice decomposition

`sliceShiftedDecomposition`: differentiating the elliptic equation `bslOp α Ψ = F` in the
radial variable `z` and rearranging gives, at every point `(z,θ)` of the open quadrant,

  `Lzero1 (∂_zΨ z ·) θ - α(5+α)·∂_zΨ(z,θ)`
    `= ∂_zF(z,θ) + α²·∂_z(z²∂_zzΨ)(z,θ) + (α²+5α)·z·∂_zzΨ(z,θ)`.

Since `bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + Lzero Ψ`, the content is (i) the commutation
of `∂_z` with the angular operator `Lzero` (`pz_Lzero_eq`, via Clairaut/Schwarz
`Work.Spaces.pz_pth_comm` and the locality lemmas `pz_congr_of_isOpen`/`pth_congr_of_isOpen`)
and (ii) the elementary product rule for the two radial terms.  The source `F` is only known
to agree with `bslOp α Ψ` on the open half-line, so `∂_zF` is computed from that local
equality (`Filter.EventuallyEq.deriv_eq`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Auxiliary vocabulary and elementary facts -/

/-- `tan θ · g` as a two-variable function: the angular factor of `Work.Elliptic.Lzero`. -/
private def tanMul (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.tan θ * g z θ

/-- `∂_z` commutes with multiplication by `tan θ`. -/
private lemma pz_tanMul (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (tanMul g) = tanMul (Work.Spaces.pz g) := by
  funext z θ
  simp only [tanMul, Work.Spaces.pz]
  rw [deriv_const_mul_field]

/-- `ContDiffAt`-form of `SmoothOpen` at an interior point of the open quadrant. -/
private lemma smoothOpen_contDiffAt_two' {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hf.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- `SmoothOpen` of `(z,θ) ↦ tan θ · Ψ z θ` (the angular factor `tan` is smooth on the
open quadrant). -/
private lemma smoothOpen_tanMul {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (tanMul Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (tanMul Ψ))
    Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (tanMul Ψ)
      = fun p : ℝ × ℝ => Real.tan p.2 * Ψ p.1 p.2 from rfl]
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have hs : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.sin ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_sin.comp_contDiffOn contDiffOn_snd
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.cos ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_cos.comp_contDiffOn contDiffOn_snd
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h1], h2⟩)
    have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      hs.div hc hne
    refine hdiv.congr (fun p _ => ?_)
    rw [Real.tan_eq_sin_div_cos]
  have hΨ' : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 := hΨ
  exact htan.mul hΨ'

/-! ## Commutation of `∂_z` with the angular operator `Lzero` -/

/-- `∂_z ∂_θ² Ψ = ∂_θ² ∂_z Ψ` on the open quadrant (two instances of Clairaut). -/
private lemma pz_pthIter_two_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
  have hV : IsOpen (Work.FTS.EllipticEst.Q0) := Work.FTS.EllipticEst.isOpen_Q0
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two' hΨ.pth hz hθ)
  have heqon : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Ψ)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz Ψ))) Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp'
    exact Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two' hΨ hz' ⟨hθ'1, hθ'2⟩)
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen hV heqon hp
  show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ
  rw [h1, h2]

/-- `∂_z ∂_θ(tan θ · Ψ) = ∂_θ ∂_z(tan θ · Ψ)` on the open quadrant. -/
private lemma pz_pth_tanMul_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ
      = Work.Spaces.pth (tanMul (Work.Spaces.pz Ψ)) z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hC2 : ContDiffAt ℝ 2 (Function.uncurry (tanMul Ψ)) (z, θ) :=
    ((smoothOpen_tanMul hΨ).forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  rw [Work.Spaces.pz_pth_comm hC2, pz_tanMul]

/-! ## The differentiated `Lzero`-slice -/

/-- **The derivative of the `θ`-slice of `Lzero`.**  The derivative at `z` of
`z' ↦ Lzero Ψ z' θ` is `Lzero1` applied to the slice `t ↦ ∂_zΨ(z,t)`. -/
private lemma hasDerivAt_Lzero_slice {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) z := by
  have htanmul : Work.FTS.EllipticEst.SmoothOpen (tanMul Ψ) := smoothOpen_tanMul hΨ
  have hd1 : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Ψ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z :=
    (hΨ.pth.pth).hasDerivAt_slice hθ hz
  have hd2 : HasDerivAt (fun z' => Work.Spaces.pth (tanMul Ψ) z' θ)
      (Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ) z :=
    htanmul.pth.hasDerivAt_slice hθ hz
  have hd3 : HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z :=
    hΨ.hasDerivAt_slice hθ hz
  have hsum : HasDerivAt (fun z' => -(Work.Spaces.pthIter 2 Ψ z' θ)
        + Work.Spaces.pth (tanMul Ψ) z' θ - 6 * Ψ z' θ)
      ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ) - 6 * Work.Spaces.pz Ψ z θ) z :=
    (hd1.neg.add hd2).sub (hd3.const_mul 6)
  have hval : ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ) - 6 * Work.Spaces.pz Ψ z θ)
      = Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ := by
    rw [pz_pthIter_two_eq hΨ hz hθ, pz_pth_tanMul_eq hΨ hz hθ, Lzero1_slice_eq]
    rfl
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => ?_))
  rfl

/-- **Commutation of `∂_z` with `Lzero`.** -/
private lemma pz_Lzero_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Elliptic.Lzero Ψ) z θ
      = Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ := by
  show deriv (fun z' => Work.Elliptic.Lzero Ψ z' θ) z
    = Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
  exact (hasDerivAt_Lzero_slice hΨ hz hθ).deriv

/-! ## The decomposition -/

theorem sliceShiftedDecomposition {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
          - (α * (5 + α)) * Work.Spaces.pz Ψ z θ
        = Work.Spaces.pz F z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ) := by
  intro z hz θ hθ
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- `F` agrees with `bslOp α Ψ` on a neighbourhood of `z` along the slice `θ`
  have hloc : (fun z' => F z' θ) =ᶠ[𝓝 z] (fun z' => Work.Elliptic.bslOp α Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact (h.eq z' hz' θ hθ.1 hθ.2).symm
  have hpzF : Work.Spaces.pz F z θ = deriv (fun z' => Work.Elliptic.bslOp α Ψ z' θ) z := by
    show deriv (fun z' => F z' θ) z = deriv (fun z' => Work.Elliptic.bslOp α Ψ z' θ) z
    exact hloc.deriv_eq
  -- the three summands of `bslOp`, differentiated along `z`
  have hd1 : HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) z := by
    have hdiff : DifferentiableAt ℝ (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z :=
      (((hasDerivAt_id z).pow 2).mul (hΨ.hasDerivAt_slice_pzIter 2 hθ hz)).differentiableAt
    exact hdiff.hasDerivAt
  have hd2a : HasDerivAt (fun z' => z' * Work.Spaces.pz Ψ z' θ)
      (1 * Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) z := by
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ)
        (Work.Spaces.pzIter 2 Ψ z θ) z := hΨ.hasDerivAt_slice_pzIter 1 hθ hz
    exact (hasDerivAt_id z).mul h2
  have hd2 : HasDerivAt (fun z' => z' * Work.Spaces.pz Ψ z' θ)
      (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) z := by
    refine hd2a.congr_deriv ?_
    ring
  have hd3 : HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) z :=
    hasDerivAt_Lzero_slice hΨ hz hθ
  have hbsl : HasDerivAt (fun z' => Work.Elliptic.bslOp α Ψ z' θ)
      (-(α ^ 2) * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + -(α * (5 + α)) * (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) z := by
    have h1 := hd1.const_mul (-(α ^ 2))
    have h2 := hd2.const_mul (-(α * (5 + α)))
    have hsum := (h1.add h2).add hd3
    refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => ?_))
    change Work.Elliptic.bslOp α Ψ z' θ
      = -(α ^ 2) * (z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
        + -(α * (5 + α)) * (z' * Work.Spaces.pz Ψ z' θ) + Work.Elliptic.Lzero Ψ z' θ
    rw [Work.Elliptic.bslOp_apply]
    ring
  have hkey : Work.Spaces.pz F z θ
      = -(α ^ 2) * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - (α * (5 + α)) * (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ := by
    rw [hpzF, hbsl.deriv]
    ring
  rw [hkey]
  ring

end Work.FTS.EllipticEst.remov.SourceBound
