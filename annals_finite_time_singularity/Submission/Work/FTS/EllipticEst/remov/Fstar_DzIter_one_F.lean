import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The angular moment of `D_z F` vanishes for `k ≥ 2`.**

For `k ≥ 2` the moment chain `F_*(D_z^j F) z - F_*(D_z^j F) s = ∫_s^z F_*(D_z^{j+1}F) r/r dr`
(`FstarDzIter_chain_open`) is available *both* at `j = 0` and at `j = 1`.  From `j = 0`, with
`F_*(F) ≡ 0` (the hypothesis), the primitive of `r ↦ F_*(D_zF)(r)/r` vanishes identically, so
`F_*(D_zF) = 0` almost everywhere; from `j = 1` that function is itself an indefinite integral of
the locally integrable function `r ↦ F_*(D_z^2F)(r)/r`, hence continuous; a continuous function
which vanishes almost everywhere is identically zero. -/
theorem Fstar_DzIter_one_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
  -- the source is `C^∞` on the open quadrant
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (smoothOpen_slices_weak h 0).1
  -- and honestly in `ℋ¹`
  have hmem1 : Work.Spaces.HkMem α 1 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega : 1 ≤ k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hF) h.memF
  -- `B₁ = F_*(D_zF)` vanishes almost everywhere on `(0,∞)`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.EllipticEst.Bmom F 1 z = 0 := by
    have hd := Work.FTS.EllipticEst.Cert.radIter_bmom_ae_hasDerivAt α 1 hF hmem1
      (le_refl 1)
    rw [show (1 : ℕ) - 1 = 0 from rfl, MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hd
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hd] with z hzimp hzmem
    have hz0 : 0 < z := hzmem
    have hev : (fun w : ℝ => Work.FTS.EllipticEst.Bmom F 0 w) =ᶠ[𝓝 z]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz0] with w hw
      rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
      simpa using h.orthF w hw
    have hder0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (Work.FTS.EllipticEst.Bmom F 1 z / z) z :=
      hev.hasDerivAt_iff.mp (hzimp hzmem)
    have hval : Work.FTS.EllipticEst.Bmom F 1 z / z = 0 :=
      (hder0.unique (hasDerivAt_const z 0))
    rw [div_eq_zero_iff] at hval
    rcases hval with h' | h'
    · exact h'
    · exact absurd h' hz0.ne'
  -- `B₁` is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.Bmom F 1 z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn α k hF h.memF 1 (by omega)
  -- hence it is everywhere zero
  have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae hcont continuousOn_const
    (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
  intro z hz
  rw [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  exact hEq hz

theorem Fstar_DzIter_one_F {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by sorry

end Work.FTS.EllipticEst.remov
