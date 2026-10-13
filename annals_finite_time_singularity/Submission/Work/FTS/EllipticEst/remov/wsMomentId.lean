/-
Copyright: work module for the Elgindi finite-time singularity project.

# The moment identity of the angular operator `Lzero1`

For a datum `h : EllWeakPos α k F Ψ` of the weak class and `z > 0`, the angular slice
`Lzero1 (Ψ z ·)` is orthogonal to the kernel element `sinθcos²θ` of the adjoint:

  `∫ θ in Iθ, Lzero1 (fun t => Ψ z t) θ * sinθcos²θ = 0`.

This is the last analytic input of the left-end argument of `remov.weakSliceRegular`: combined
with `Work.Elliptic.LzeroAdj_sinCos2` it forces `lim_{θ→0+} Ψ z θ = 0`.

The proof is the decomposition of the equation.  On the open interval the equation
`bslOp α Ψ z θ = F z θ` reads

  `Lzero1 (Ψ z ·) θ = F z θ + α²z²·∂_zzΨ(z,θ) + α(5+α)·(D_zΨ)(z,θ)`,

so integrating against `sinθcos²θ` and using `F_*(F) = 0`, `F_*(D_zΨ) = 0` together with
`z²∂_zzΨ = D_z²Ψ - D_zΨ` gives `F_*(D_z²Ψ) - F_*(D_zΨ) = 0 - 0 = 0`.

The three moment conditions are taken as hypotheses (`hchain`) so that this module is
independent of the module that proves the moment chain; the assembly replaces them.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2

/-- `F` is `C^∞` on the open quadrant: it agrees there with `bslOp α Ψ`. -/
theorem ws_smoothOpen_F {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))
    (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')

/-- `z² ∂_zzΨ` is `C^∞` on the open quadrant. -/
theorem ws_smoothOpen_zsq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨ 2))
    (fun z θ _ _ _ => rfl)

/-- **The moment identity.**  `∫_θ Lzero1 (Ψ z ·) θ · sinθcos²θ = 0`. -/
theorem wsMomentIdentity {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (hk : 1 ≤ k)
    (hchain : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0)
    (hint1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 Ψ z θ * sg θ) Iθ)
    (hsplit : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter 2 Ψ z θ
        = Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :
    ∀ z : ℝ, 0 < z →
      (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ) = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hF : Work.FTS.EllipticEst.SmoothOpen F := ws_smoothOpen_F h
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := ws_smoothOpen_zsq hΨ
  intro z hz
  -- integrability of the three pieces
  have hFint : MeasureTheory.IntegrableOn (fun θ => F z θ * sg θ) Iθ :=
    (ws_absMoment (ws_aesm_slice hF hz)
      (ws_slot_slice hF h.memF 0 (by omega) hz)).1
  have hAint : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ) Iθ :=
    (ws_absMoment (ws_aesm_slice hA hz)
      (ws_slot_slice hA h.memA 0 (by omega) hz)).1
  have hD1int : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 Ψ z θ * sg θ) Iθ := hint1 z hz
  -- the pointwise decomposition on the open interval
  have hpw : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ
        = ((fun θ' => F z θ' * sg θ')
            + (fun θ' => α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') * sg θ'))
            + (fun θ' => (α * (5 + α)) * (Work.Spaces.DzIter 1 Ψ z θ' * sg θ'))) θ := by
    intro θ hθ
    have heq := h.eq z hz θ hθ.1 hθ.2
    have hbs := Work.Elliptic.bslOp_apply α Ψ z θ
    have hLz : Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = Work.Elliptic.Lzero Ψ z θ := rfl
    have hDz : Work.Spaces.DzIter 1 Ψ z θ = z * Work.Spaces.pz Ψ z θ := rfl
    -- `bslOp α Ψ z θ = -(α²z²)·∂_zzΨ - (α(5+α)z)·∂_zΨ + Lzero Ψ z θ`
    have h1 : Work.Elliptic.Lzero Ψ z θ
        = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α)) * (Work.Spaces.DzIter 1 Ψ z θ) := by
      rw [hbs] at heq
      rw [hDz]
      linarith
    rw [hLz, h1]
    simp only [Pi.add_apply]
    ring
  -- integrate
  have hcongr : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ)
      = ∫ θ in Iθ, ((fun θ' => F z θ' * sg θ')
          + (fun θ' => α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') * sg θ'))
          + (fun θ' => (α * (5 + α)) * (Work.Spaces.DzIter 1 Ψ z θ' * sg θ'))) θ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ws_ae_mem_Ioo] with θ hθ
    exact hpw θ hθ
  have hI : (∫ θ in Iθ, ((fun θ' => F z θ' * sg θ')
        + (fun θ' => α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') * sg θ'))
        + (fun θ' => (α * (5 + α)) * (Work.Spaces.DzIter 1 Ψ z θ' * sg θ'))) θ)
      = (∫ θ in Iθ, F z θ * sg θ)
        + α ^ 2 * (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ)
        + (α * (5 + α)) * (∫ θ in Iθ, Work.Spaces.DzIter 1 Ψ z θ * sg θ) := by
    have h1 := MeasureTheory.integral_add
      (f := (fun θ' => F z θ' * sg θ')
        + (fun θ' => α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') * sg θ')))
      (g := fun θ' => (α * (5 + α)) * (Work.Spaces.DzIter 1 Ψ z θ' * sg θ'))
      (hFint.add (hAint.const_mul _)) (hD1int.const_mul _)
    have h2 := MeasureTheory.integral_add (f := fun θ' => F z θ' * sg θ')
      (g := fun θ' => α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') * sg θ'))
      hFint (hAint.const_mul _)
    simp only [Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hcongr, hI]
  -- identify the three integrals
  have e1 : (∫ θ in Iθ, F z θ * sg θ) = 0 := by
    have := h.orthF z hz
    simpa only [Work.Elliptic.Fstar] using this
  have e2 : (∫ θ in Iθ, Work.Spaces.DzIter 1 Ψ z θ * sg θ) = 0 := by
    have := hchain 1 (by omega) z hz
    simpa only [Work.Elliptic.Fstar] using this
  have e3 : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ) = 0 := by
    have hsub : (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ
            - Work.Spaces.DzIter 1 Ψ z θ * sg θ) := by
      filter_upwards [ws_ae_mem_Ioo] with θ hθ
      rw [hsplit z hz θ hθ]
      ring
    rw [MeasureTheory.integral_congr_ae hsub]
    have hD2 : (∫ θ in Iθ, Work.Spaces.DzIter 2 Ψ z θ * sg θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z := rfl
    have hD1 : (∫ θ in Iθ, Work.Spaces.DzIter 1 Ψ z θ * sg θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z := rfl
    -- integrability of `D_z²Ψ · sg`
    have hD2int : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ) Iθ := by
      have hcong : (fun θ => Work.Spaces.DzIter 1 Ψ z θ * sg θ
            + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * sg θ)
          =ᵐ[MeasureTheory.volume.restrict Iθ]
          (fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ) := by
        filter_upwards [ws_ae_mem_Ioo] with θ hθ
        rw [hsplit z hz θ hθ]
        ring
      exact (hD1int.add hAint).congr hcong
    rw [MeasureTheory.integral_sub
      (f := fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ)
      (g := fun θ => Work.Spaces.DzIter 1 Ψ z θ * sg θ) hD2int hD1int, hD2, hD1,
      hchain 2 (by omega) z hz, hchain 1 (by omega) z hz]
    ring
  rw [e1, e2, e3]
  ring

end Work.FTS.EllipticEst.remov
