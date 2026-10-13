import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C²` regularity of the meridian slice of `merPsi`

`merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ), θ(r,z), τ)`, `τ = clockInv C t`,
where `Φ̂ = PhiOdd Φ` is the odd extension in `θ` and `θ(r,z) = arctan(z/r)`.

Off the degenerate set `r > 0`, `z ≠ 0` the point `(r,z)` sees the *interior* of one of the two
branches of the odd extension: `θ(r,z) ≠ 0` (because `z ≠ 0`, `r > 0`), and by continuity the sign
of `θ` is constant on a neighbourhood of `(r,z)`.  On that neighbourhood `Φ̂` agrees with either
`Φ` (branch `θ > 0`) or the smooth reflection `(w,θ) ↦ -Φ(w,-θ)` (branch `θ < 0`), so the
hypothesis `hsm` — the `C²`-ness of `Φ(·,·,τ)` on the open quadrant — applies.

The lemma is the `hsm2` hypothesis of `Work.FTS.BSIdent.hid`; it is a purely analytic
(non-elliptic) statement about the polar dictionary.
-/

open scoped Topology

namespace Work.FTS.BSIdent.Defs

theorem contDiffAt_merPsi_slice (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ)
    (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi α A B Φ C p.1 p.2 t) (r, z) := by
  set τ := Physical.clockInv C t with hτ
  -- ### Step 1: the polar dictionary `ρ`, `ρ^p/B(τ)`, `θ` is `C²` in `(r,z)`
  have hρ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) := by fun_prop
    have h2 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) ≠ 0 := by
      show r ^ 2 + z ^ 2 ≠ 0
      positivity
    have h3 := (Real.contDiffAt_sqrt (n := 2) h2).comp (r, z) h1
    simpa [Work.Cyl.rhoP, Function.comp_def] using h3
  have hρp : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ) (r, z) := by
    have h4 := hρ.rpow_const_of_ne (p := Work.FTS.Regularity.pExp α)
      (Work.Cyl.rhoP_ne_zero hr z)
    simpa [div_eq_mul_inv] using
      h4.mul (contDiffAt_const (c := (B τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (B τ)⁻¹) (r, z))
  have hθ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / q.1) (r, z) := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa using hr.ne'
    have h3 := Real.contDiff_arctan.contDiffAt.comp (r, z) h1
    simpa [Work.Cyl.thetaP, Function.comp_def] using h3
  -- ### Step 2: the self-similar argument is positive, and `θ(r,z) ≠ 0`
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  have hθ0 : Work.Cyl.thetaP r z ≠ 0 := by
    simp only [Work.Cyl.thetaP]
    exact fun h => (div_ne_zero hz hr.ne') (Real.arctan_eq_zero_iff.mp h)
  rcases lt_or_gt_of_ne hθ0 with hneg | hpos
  · -- ### Step 3a: the branch `θ < 0`, i.e. `Φ̂ = -Φ(w,-θ)`
    have hpos' : 0 < -Work.Cyl.thetaP r z := by linarith
    have hlt' : -Work.Cyl.thetaP r z < Real.pi / 2 := by
      have h := Real.neg_pi_div_two_lt_arctan (z / r)
      simp only [Work.Cyl.thetaP]
      linarith
    have hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, -Work.Cyl.thetaP r z) :=
      hsm _ _ hw hpos' hlt'
    have hnegθ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => -Work.Cyl.thetaP q.1 q.2) (r, z) := hθ.neg
    have hcomp := hΦ.comp (r, z) (hρp.prodMk hnegθ)
    have hc : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (-(Work.Cyl.thetaP q.1 q.2)) τ) (r, z) := by
      simpa [Function.comp_def] using hcomp
    have hfinal : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => (A τ)⁻¹ * (-Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (-(Work.Cyl.thetaP q.1 q.2)) τ)) (r, z) :=
      (contDiffAt_const (c := (A τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (A τ)⁻¹) (r, z)).mul
        hc.neg
    have hprod : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2 *
          ((A τ)⁻¹ * (-Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (-(Work.Cyl.thetaP q.1 q.2)) τ))) (r, z) :=
      (hρ.pow 2).mul hfinal
    refine hprod.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | Work.Cyl.thetaP q.1 q.2 < 0} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hnb] with q hq
    rw [Work.FTS.BSIdent.merPsi_apply, Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hq)]
    ring
  · -- ### Step 3b: the branch `θ > 0`, i.e. `Φ̂ = Φ(w,θ)`
    have hlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
      simpa only [Work.Cyl.thetaP] using Real.arctan_lt_pi_div_two (z / r)
    have hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, Work.Cyl.thetaP r z) :=
      hsm _ _ hw hpos hlt
    have hcomp := hΦ.comp (r, z) (hρp.prodMk hθ)
    have hc : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP q.1 q.2) τ) (r, z) := by
      simpa [Function.comp_def] using hcomp
    have hfinal : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => (A τ)⁻¹ * Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP q.1 q.2) τ) (r, z) :=
      (contDiffAt_const (c := (A τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (A τ)⁻¹) (r, z)).mul hc
    have hprod : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2 *
          ((A τ)⁻¹ * Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP q.1 q.2) τ)) (r, z) :=
      (hρ.pow 2).mul hfinal
    refine hprod.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | 0 < Work.Cyl.thetaP q.1 q.2} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hnb] with q hq
    rw [Work.FTS.BSIdent.merPsi_apply, Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hq)]
    ring

end Work.FTS.BSIdent.Defs
