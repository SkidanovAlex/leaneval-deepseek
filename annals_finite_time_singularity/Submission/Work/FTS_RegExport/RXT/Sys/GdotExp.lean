import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_le2
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_Dz_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.GdotExp` -- the expansion of the transport operator (S5b, core)

`mixed_transport_expand`: the Leibniz expansion of `D_z^j D_θ^i` applied to the transport
expression `a·D_zX + d·D_θX + c·X`, in the *shifted* form in which the principal parts are
`a·mixed (j+1) i X` and `d·mixed j (i+1) X`.  This is the finite-order (`C²`/`C³`) instance of
the iterated Leibniz rule for the two derivation-like operators `D_z = z ∂_z`, `D_θ = sin 2θ ∂_θ`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7 ω phiTil)
open Work.FTS.RegExportIface.RXT (VR bR cR SigR μR GR ΦR idx)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## The expansion of the transport operator on the jets -/

/-! ## The expansion of the transport operator on the jets -/

theorem mixed_transport_expand {a d c X : ℝ → ℝ → ℝ}
    (ha : ContDiffOn ℝ 2 (Function.uncurry a) Q0)
    (hd : ContDiffOn ℝ 2 (Function.uncurry d) Q0)
    (hc : ContDiffOn ℝ 2 (Function.uncurry c) Q0)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ) z θ
      = (∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u a z θ * Work.Spaces.mixed (j - v + 1) (i - u) X z θ))
        + (∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
            ((i.choose u : ℝ) * (j.choose v : ℝ)) *
              (Work.Spaces.mixed v u d z θ * Work.Spaces.mixed (j - v) (i - u + 1) X z θ))
        + (∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
            ((i.choose u : ℝ) * (j.choose v : ℝ)) *
              (Work.Spaces.mixed v u c z θ * Work.Spaces.mixed (j - v) (i - u) X z θ)) := by
  have hzθ : (z, θ) ∈ Q0 := Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hX2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.Dz X)) Q0 :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dz_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 hX
  have hX2' : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.Dth X)) Q0 :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dth_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 hX
  have hX2'' : ContDiffOn ℝ 2 (Function.uncurry X) Q0 := hX.of_le (by norm_num)
  have hu1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => a z θ * Work.Spaces.Dz X z θ)) Q0 :=
    ha.mul hX2
  have hu2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => d z θ * Work.Spaces.Dth X z θ)) Q0 :=
    hd.mul hX2'
  have hu3 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => c z θ * X z θ)) Q0 := hc.mul hX2''
  have hadd : Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => d z θ * Work.Spaces.Dth X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => c z θ * X z θ) z θ := by
    rw [show (fun z θ : ℝ => a z θ * Work.Spaces.Dz X z θ
          + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ)
        = ((fun z θ => a z θ * Work.Spaces.Dz X z θ)
            + (fun z θ => d z θ * Work.Spaces.Dth X z θ))
          + (fun z θ => c z θ * X z θ) from rfl]
    have h12 : ContDiffOn ℝ 2 (Function.uncurry ((fun z θ => a z θ * Work.Spaces.Dz X z θ)
        + (fun z θ => d z θ * Work.Spaces.Dth X z θ))) Q0 := hu1.add hu2
    rw [mixed_add_pt h12 hu3 (Nat.add_comm j i ▸ hji) hzθ]
    rw [mixed_add_pt hu1 hu2 (Nat.add_comm j i ▸ hji) hzθ]
  have hexp1 : Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ) z θ
      = ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u a z θ * Work.Spaces.mixed (j - v + 1) (i - u) X z θ) := by
    rw [GdotAux.mixed_mul_le2 ha hX2 hji hz hθ0 hθ1]
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    rw [GdotAux.mixed_Dz_shift hX (p := j - v) (q := i - u) (by
      have hu' : u ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu
      have hv' : v ≤ j := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv
      omega) hz hθ0 hθ1]
    try ring
  have hexp2 : Work.Spaces.mixed j i (fun z θ => d z θ * Work.Spaces.Dth X z θ) z θ
      = ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u d z θ * Work.Spaces.mixed (j - v) (i - u + 1) X z θ) := by
    rw [GdotAux.mixed_mul_le2 hd hX2' hji hz hθ0 hθ1]
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    rw [mixed_Dth_succ (j - v) (i - u) X]
  have hexp3 : Work.Spaces.mixed j i (fun z θ => c z θ * X z θ) z θ
      = ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u c z θ * Work.Spaces.mixed (j - v) (i - u) X z θ) :=
    GdotAux.mixed_mul_le2 hc hX2'' hji hz hθ0 hθ1
  rw [hadd, hexp1, hexp2, hexp3]
  try ring


end Work.FTS_RegExport.RXT.Sys
