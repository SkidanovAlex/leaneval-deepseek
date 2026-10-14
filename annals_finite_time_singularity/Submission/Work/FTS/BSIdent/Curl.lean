import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.R1G.vorticity_psiField_bslOp
import Submission.Work.R1G3.bslOp_scale

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology Real

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The odd extension of a single self-similar slice -/

/-- **The odd extension in `θ` of one self-similar slice** `F z θ`: `F z θ` for `θ ≥ 0` and
`−F z (−θ)` for `θ < 0`.  It is the slice of `PhiOdd`:

  `PhiOdd Φ z θ τ = PhiOddSlice (fun z θ => Φ z θ τ) z θ`. -/
abbrev PhiOddSlice (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => if 0 ≤ θ then F z θ else -(F z (-θ))

theorem PhiOddSlice_of_nonneg {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : 0 ≤ θ) :
    PhiOddSlice F z θ = F z θ := ite_eq_left h

theorem PhiOddSlice_of_neg {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : ¬ 0 ≤ θ) :
    PhiOddSlice F z θ = -(F z (-θ)) := ite_eq_right h

/-- The slice of the odd extension is the odd extension of the slice. -/
theorem PhiOdd_eq_PhiOddSlice (Φ : Fam) (z θ τ : ℝ) :
    PhiOdd Φ z θ τ = PhiOddSlice (fun z θ => Φ z θ τ) z θ := rfl


/-! ## Smoothness of the odd-extended slice at `θ ≠ 0` -/

theorem contDiffAt_PhiOddSlice_of_pos {F : ℝ → ℝ → ℝ} {w θ : ℝ} (hθ : 0 < θ)
    (h : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 q.2) (w, θ)) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => PhiOddSlice F q.1 q.2) (w, θ) := by
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd) hθ] with q hq
  exact PhiOddSlice_of_nonneg (le_of_lt hq)

theorem contDiffAt_PhiOddSlice_of_neg {F : ℝ → ℝ → ℝ} {w θ : ℝ} (hθ : θ < 0)
    (h : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 q.2) (w, -θ)) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => PhiOddSlice F q.1 q.2) (w, θ) := by
  have hcomp : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 (-q.2)) (w, θ) :=
    ContDiffAt.comp (w, θ) h (contDiffAt_fst.prodMk contDiffAt_snd.neg)
  refine hcomp.neg.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const) hθ] with q hq
  show PhiOddSlice F q.1 q.2 = -(F q.1 (-q.2))
  rw [PhiOddSlice_of_neg (not_le.mpr hq)]

/-! ## The abstract curl identity -/

/-- **The curl identity, `θ > 0` branch.**  For `a, b > 0`, an elliptic datum `(F, G)` on the
open quadrant (law and `C²`-regularity) and a point `x ∈ Uax` with `θ(x) > 0`, the vorticity of
the stream-function field of `ψ = ρ²·a⁻¹·F̂(ρ^p/b, θ)` is `−(a⁻¹·profile p G (ρ^p/b, θ))·e_θ`. -/
theorem vorticity_psiField_PhiOddSlice_of_pos {p a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {F G : ℝ → ℝ → ℝ}
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp p F w θ = Work.Construction.Fstar p w θ + G w θ)
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 q.2) (w, θ))
    {x : R3} (hx : x ∈ Uax) (hθx : 0 < Work.Cyl.theta x) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2 * a⁻¹ *
        PhiOddSlice F (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))) x
      = -(a⁻¹ * Work.ConstructionInstance.profile p G
            (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)) • Work.Cyl.eTheta x := by
  have hr : 0 < Work.Cyl.radial x := radial_pos_of_mem_Uax hx
  have hρ : 0 < Work.Cyl.rho x := rho_pos_of_mem_Uax hx
  have hθlt : Work.Cyl.theta x < π / 2 := Real.arctan_lt_pi_div_two _
  have hw : 0 < Work.Cyl.rho x ^ p / b := div_pos (Real.rpow_pos_of_pos hρ p) hb
  have hsm' := hsm (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x) hw hθx hθlt
  have hΨsm : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => a⁻¹ * PhiOddSlice F q.1 q.2)
      (Work.Cyl.rho x ^ p / b, Work.Cyl.theta x) :=
    contDiffAt_const.mul (contDiffAt_PhiOddSlice_of_pos hθx hsm')
  have hcurl := Physical.Ident.vorticity_psiField_scaled (p := p) (B := b) (ne_of_gt hb)
    (Φ := fun w θ => a⁻¹ * PhiOddSlice F w θ) x hr hΨsm
  have hfun : (fun r z => Work.Cyl.rhoP r z ^ 2 * a⁻¹ *
        PhiOddSlice F (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
      = fun r z => Work.Cyl.rhoP r z ^ 2 * (fun w θ => a⁻¹ * PhiOddSlice F w θ)
          (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z) := by
    funext r z; ring
  rw [hfun, hcurl]
  -- the operator value
  have hval : Work.Elliptic.bslOp p (fun w θ => a⁻¹ * PhiOddSlice F w θ)
        (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)
      = a⁻¹ * (Work.Construction.Fstar p (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)
          + G (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)) := by
    rw [OddExt.bslOp_const_mul]
    congr 1
    have hbranch := OddExt.bslOp_PhiOdd_of_pos (p := p) (Φ := fun z θ _ => F z θ) (τ := 0)
      (z := Work.Cyl.rho x ^ p / b) (θ := Work.Cyl.theta x) hθx
    rw [show PhiOddSlice F = (fun z θ' => PhiOdd (fun z θ _ => F z θ) z θ' 0) from rfl, hbranch]
    exact hlaw _ _ hw hθx hθlt
  rw [hval, ← Work.ConstructionInstance.profile_of_nonneg (le_of_lt hθx)]

/-- **The curl identity, `θ < 0` branch.**  Same as the `θ > 0` branch, with the elliptic law read
at the reflected angle `−θ > 0`. -/
theorem vorticity_psiField_PhiOddSlice_of_neg {p a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {F G : ℝ → ℝ → ℝ}
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp p F w θ = Work.Construction.Fstar p w θ + G w θ)
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 q.2) (w, θ))
    {x : R3} (hx : x ∈ Uax) (hθx : Work.Cyl.theta x < 0) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2 * a⁻¹ *
        PhiOddSlice F (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))) x
      = -(a⁻¹ * Work.ConstructionInstance.profile p G
            (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)) • Work.Cyl.eTheta x := by
  have hr : 0 < Work.Cyl.radial x := radial_pos_of_mem_Uax hx
  have hρ : 0 < Work.Cyl.rho x := rho_pos_of_mem_Uax hx
  have hθpos : 0 < -Work.Cyl.theta x := neg_pos.mpr hθx
  have hθlt : -Work.Cyl.theta x < π / 2 := by
    have hlow : -(π / 2) < Work.Cyl.theta x := Real.neg_pi_div_two_lt_arctan _
    linarith
  have hw : 0 < Work.Cyl.rho x ^ p / b := div_pos (Real.rpow_pos_of_pos hρ p) hb
  have hsm' := hsm (Work.Cyl.rho x ^ p / b) (-Work.Cyl.theta x) hw hθpos hθlt
  have hΨsm : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => a⁻¹ * PhiOddSlice F q.1 q.2)
      (Work.Cyl.rho x ^ p / b, Work.Cyl.theta x) :=
    contDiffAt_const.mul (contDiffAt_PhiOddSlice_of_neg hθx hsm')
  have hcurl := Physical.Ident.vorticity_psiField_scaled (p := p) (B := b) (ne_of_gt hb)
    (Φ := fun w θ => a⁻¹ * PhiOddSlice F w θ) x hr hΨsm
  have hfun : (fun r z => Work.Cyl.rhoP r z ^ 2 * a⁻¹ *
        PhiOddSlice F (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
      = fun r z => Work.Cyl.rhoP r z ^ 2 * (fun w θ => a⁻¹ * PhiOddSlice F w θ)
          (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z) := by
    funext r z; ring
  rw [hfun, hcurl]
  have hval : Work.Elliptic.bslOp p (fun w θ => a⁻¹ * PhiOddSlice F w θ)
        (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)
      = a⁻¹ * (-(Work.Construction.Fstar p (Work.Cyl.rho x ^ p / b) (-Work.Cyl.theta x)
          + G (Work.Cyl.rho x ^ p / b) (-Work.Cyl.theta x))) := by
    rw [OddExt.bslOp_const_mul]
    congr 1
    have hΦC2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (fun z θ _ => F z θ) q.1 q.2 0)
        (Work.Cyl.rho x ^ p / b, -Work.Cyl.theta x) := hsm'
    have hbranch := OddExt.bslOp_PhiOdd_of_neg (p := p) (Φ := fun z θ _ => F z θ) (τ := 0)
      (z := Work.Cyl.rho x ^ p / b) (θ := Work.Cyl.theta x) hθx hΦC2
    rw [show PhiOddSlice F = (fun z θ' => PhiOdd (fun z θ _ => F z θ) z θ' 0) from rfl, hbranch]
    rw [hlaw _ _ hw hθpos hθlt]
  rw [hval, ← Work.ConstructionInstance.profile_of_neg (not_le.mpr hθx)]

/-- **The curl identity of the reconstruction, abstract form.** -/
theorem vorticity_psiField_PhiOddSlice {p a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {F G : ℝ → ℝ → ℝ}
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp p F w θ = Work.Construction.Fstar p w θ + G w θ)
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 q.2) (w, θ))
    {x : R3} (hx : x ∈ Uax) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2 * a⁻¹ *
        PhiOddSlice F (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))) x
      = -(a⁻¹ * Work.ConstructionInstance.profile p G
            (Work.Cyl.rho x ^ p / b) (Work.Cyl.theta x)) • Work.Cyl.eTheta x := by
  rcases lt_trichotomy (Work.Cyl.theta x) 0 with h | h | h
  · exact vorticity_psiField_PhiOddSlice_of_neg ha hb hlaw hsm hx h
  · exact absurd h (theta_ne_zero_of_mem_Uax hx)
  · exact vorticity_psiField_PhiOddSlice_of_pos ha hb hlaw hsm hx h

/-! ## The curl identity for the meridian stream function -/

/-- **THE CURL IDENTITY OF THE RECONSTRUCTION.**  If the self-similar stream function `Φ(·,·,τ)`
of the reconstruction solves the paper's elliptic law with source the full profile
`F_* + g(·,·,τ)`, then the meridian stream function `merPsi α A B Φ C` is the stream function of
the **re-signed** physical vorticity: on `Uax`,

  `vorticity (psiField (merPsi … · t)) x = −physOmega α A B g C x t`.

The hypotheses are: `A(τ) > 0`, `B(τ) > 0` (the clock), the elliptic law on the open quadrant, and
the `C²` regularity of `Φ(·,·,τ)` there. -/
theorem vorticity_psiField_merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam)
    (C : Physical.PhysClock) (g : ℝ → ℝ → ℝ → ℝ) (t : ℝ)
    (hA : 0 < A (Physical.clockInv C t)) (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {x : R3} (hx : x ∈ Uax) :
    vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x
      = -((A (Physical.clockInv C t))⁻¹ * Work.ConstructionInstance.profile
            (Work.FTS.Regularity.pExp α)
            (Work.FTS.Regularity.gSlice g (Physical.clockInv C t))
            (Work.Cyl.rho x ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.theta x)) • Work.Cyl.eTheta x := by
  have hmain := vorticity_psiField_PhiOddSlice (p := Work.FTS.Regularity.pExp α)
    (a := A (Physical.clockInv C t)) (b := B (Physical.clockInv C t)) hA hB
    (F := fun z θ => Φ z θ (Physical.clockInv C t))
    (G := fun z θ => g z θ (Physical.clockInv C t)) hlaw hsm hx
  have hfun : (fun r z => merPsi α A B Φ C r z t)
      = fun r z => Work.Cyl.rhoP r z ^ 2 * (A (Physical.clockInv C t))⁻¹ *
          PhiOddSlice (fun z θ => Φ z θ (Physical.clockInv C t))
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.thetaP r z) := by
    funext r z
    rw [merPsi_apply]
    simp only [PhiOdd_eq_PhiOddSlice]
  rw [hfun]
  rw [show Work.FTS.Regularity.gSlice g (Physical.clockInv C t)
      = (fun z θ => g z θ (Physical.clockInv C t)) from rfl]
  exact hmain

/-- The meridian stream function of the reconstruction is the stream function of the **re-signed**
physical vorticity `−physOmega α A B g C` of the design (`FTS_PHYS_BRIDGE.md`, correction 1). -/
theorem vorticity_psiField_merPsi_eq_neg_physOmega (α : ℝ) (A B : ℝ → ℝ)
    (C : Physical.PhysClock) (g : ℝ → ℝ → ℝ → ℝ) (t : ℝ) {x : R3} :
    -((A (Physical.clockInv C t))⁻¹ * Work.ConstructionInstance.profile
          (Work.FTS.Regularity.pExp α) (Work.FTS.Regularity.gSlice g (Physical.clockInv C t))
          (Work.Cyl.rho x ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.theta x)) • Work.Cyl.eTheta x
      = -(Physical.physOmega α A B g C x t) := by
  rw [Physical.physOmega_apply, Work.FTS.Regularity.physVort_apply,
    Work.ConstructionInstance.omegaSz_apply, neg_smul, smul_smul]

end Work.FTS.BSIdent
