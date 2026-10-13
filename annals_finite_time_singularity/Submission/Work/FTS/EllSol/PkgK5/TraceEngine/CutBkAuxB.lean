/-
Integrability of the two joint integrands of `cutBkBound`, and the fibre bridges that
turn the `θ`-integrals of the two pieces of the radial integration by parts into integrals
over the strip `Iz ×ˢ Iθ`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAux
import Submission.Work.FTS.EllSol.PkgK5.gK_ibp_fts
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine
namespace CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The θ-slice bridge -/

/-- Off the support window of `χ k` the derivative of `χ k` vanishes (the cut-off is locally
zero there). -/
lemma deriv_chi_eq_zero_of_supp {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {z : ℝ} (hz : 0 < z)
    (hout : z < cA k ∨ cB k < z) : deriv (χ k) z = 0 := by
  have hev : χ k =ᶠ[𝓝 z] fun _ : ℝ => 0 := by
    rcases hout with h | h
    · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) (cA k) from ⟨hz, h⟩)]
        with y hy
      exact hχ.supp k y hy.1 (Or.inl hy.2.le)
    · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (cB k) (2 * z - cB k)
          from ⟨h, by linarith⟩)] with y hy
      exact hχ.supp k y (by linarith [hy.1, cB_pos k]) (Or.inr hy.1.le)
  rw [hev.deriv_eq, deriv_const]

lemma bridge_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} (θ : ℝ) :
    (∫ z in Work.Spaces.Iz, cutRho (z, θ) * χ k z * cutXi G (z, θ) * cutD2 G (z, θ))
      = Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
          * cutXi G (z, θ) * cutD2 G (z, θ)) := by
  have hb := Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval hχ k
    (fun z => cutRho (z, θ) * χ k z * cutXi G (z, θ) * cutD2 G (z, θ))
    (fun z hz hout => by
      have hχz : χ k z = 0 := hχ.supp k z hz
        (hout.elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
      simp [hχz])
  rw [hb, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun z _ => ?_)
  simp only [cutRho]
  ring

lemma bridge_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} (θ : ℝ) :
    (∫ z in Work.Spaces.Iz,
        (z * deriv (χ k) z) * cutRho (z, θ) * cutPs G (z, θ) * cutD2 G (z, θ))
      = Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * cutPs G (z, θ) * cutD2 G (z, θ)) := by
  have hb := Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval hχ k
    (fun z => (z * deriv (χ k) z) * cutRho (z, θ) * cutPs G (z, θ) * cutD2 G (z, θ))
    (fun z hz hout => by
      have hdχ : deriv (χ k) z = 0 := deriv_chi_eq_zero_of_supp hχ k hz hout
      simp [hdχ])
  rw [hb, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun z _ => ?_)
  simp only [cutRho]
  ring

end CutBk
end Work.FTS.EllSol.PkgK5.TraceEngine
