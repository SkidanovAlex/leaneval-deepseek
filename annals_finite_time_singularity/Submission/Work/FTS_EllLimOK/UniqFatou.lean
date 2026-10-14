import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS_EllLimOK.EnergyGap
import Submission.Work.FTS_LocDatum3a.L12_Jeps_interchange_mine
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.one_le_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The homogeneous elliptic problem has only the trivial solution in the Fatou class.**

Two solutions of the same elliptic law, `C²` on every closed box away from `z = 0` (i.e.
`BoxReg`), satisfying the Dirichlet *values* at `θ = 0, π/2`, and with the `ℋ⁰`-memberships of
`FatouPkg` (and of their difference), agree on the open quadrant.  This is the mathematical
content of `Defs3.ClosedUniq3`. -/
theorem eqOn_of_same_law {α : ℝ} (hα : 0 < α) {f Ψ Ψ' : Fn}
    (hsolΨ : Work.FTS.StrongGlobal.IsBslSolPos α f Ψ)
    (hsolΨ' : Work.FTS.StrongGlobal.IsBslSolPos α f Ψ')
    (hboxΨ : BoxReg Ψ) (hboxΨ' : BoxReg Ψ')
    (hHkΨ : Work.Spaces.HkMem α 0 Ψ)
    (hHkcΨ : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ))
    (hHkΨ' : Work.Spaces.HkMem α 0 Ψ')
    (hHkcΨ' : Work.Spaces.HkMem α 0 (fun z θ => Ψ' z θ / Real.cos θ))
    (hHkδ : Work.Spaces.HkMem α 0 (diff Ψ Ψ')) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Ψ z θ = Ψ' z θ := by
  have hboxδ : BoxReg (diff Ψ Ψ') := hboxΨ.diff hboxΨ'
  -- the difference solves the homogeneous problem
  have hsolδ : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α (diff Ψ Ψ') z θ = 0 := by
    intro z hz θ hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
    have hca : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) := hboxΨ.contDiffAt ⟨hz, hθ⟩
    have hca' : ContDiffAt ℝ 2 (Function.uncurry Ψ') (z, θ) := hboxΨ'.contDiffAt ⟨hz, hθ⟩
    have hsub := Work.FTS.EllipticEst.bslOp_sub α Ψ Ψ' z θ hcos hca hca'
    change Work.Elliptic.bslOp α (fun z θ => Ψ z θ - Ψ' z θ) z θ = 0
    rw [hsub, hsolΨ.1 z hz θ hθ.1 hθ.2, hsolΨ'.1 z hz θ hθ.1 hθ.2, sub_self]
  -- the Dirichlet values of the difference
  have h0 : ∀ z ∈ Set.Ioi (0 : ℝ), diff Ψ Ψ' z 0 = 0 := by
    intro z hz
    simp only [diff_apply]
    rw [hsolΨ.2.1 z hz.le, hsolΨ'.2.1 z hz.le, sub_self]
  have h1 : ∀ z ∈ Set.Ioi (0 : ℝ), diff Ψ Ψ' z (π / 2) = 0 := by
    intro z hz
    simp only [diff_apply]
    rw [hsolΨ.2.2.1 z hz.le, hsolΨ'.2.2.1 z hz.le, sub_self]
  -- (1) the angular moment vanishes
  have horth : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar (diff Ψ Ψ') z = 0 :=
    Fstar_zero hα hboxδ hsolδ h0 h1 hHkδ
  -- (2) the Euler gap data
  obtain ⟨hder1, hder2, hnonneg, hint, hweight, hineq⟩ :=
    EnergyGap hα hboxΨ hboxΨ' hsolδ h0 h1 horth hHkΨ hHkcΨ hHkΨ' hHkcΨ'
  -- (3) Grönwall
  have hzero : ∀ z ∈ Set.Ioi (0 : ℝ), PhiD Ψ Ψ' z = 0 :=
    phi_eq_zero_of_euler_gap_weighted α hα (PhiD Ψ Ψ') hder1 hder2 hineq hnonneg hint hweight
  -- (4) the slices vanish
  intro z θ hzθ
  obtain ⟨hz, hθ⟩ := hzθ
  have hsq := eq_zero_of_integral_sq_eq_zero ((hboxδ.slice hz).continuousOn) (hzero z hz)
  have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h : diff Ψ Ψ' z θ = 0 := hsq θ hmem
  simp only [diff_apply] at h
  linarith

end Work.FTS_EllLimOK
