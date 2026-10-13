import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.wsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option maxHeartbeats 1600000

/-- **Clairaut at order `3` on the open quadrant**: for `f` of class `C^∞` on
`(0,∞) × (0,π/2)`, the partial derivatives `∂_z` and `∂_θ²` commute there, i.e.
`∂_θ²(∂_z f) = ∂_z(∂_θ² f)`.

This is the statement `pthIter2_pz_eqOn` of the `SourceBound` development, reproduced here
(so that this file does not have to import the heavy `weakSliceRegular` closure): the
`θ`-derivative is transported across the first Clairaut identity `Work.Spaces.pz_pth_comm`
for `f`, which is then applied a second time to `Work.Spaces.pth f`. -/
theorem pthIter2_pz_eqOn_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz f)))
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 f)))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- `∂_θ (∂_θ ∂_z f) = ∂_θ (∂_z ∂_θ f)`: the `θ`-derivative of the Clairaut identity for `f`
  have hstep1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ := by
    have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.pz f) z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.pz (Work.Spaces.pth f) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθIoo] with θ' hθ'
      exact (Work.Spaces.pz_pth_comm (f := f)
        ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩))).of_le (by simp))).symm
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.pz f) z θ') θ
        = deriv (fun θ' : ℝ => Work.Spaces.pz (Work.Spaces.pth f) z θ') θ
    rw [hev.deriv_eq]
  -- `∂_θ (∂_z ∂_θ f) = ∂_z (∂_θ ∂_θ f)`: Clairaut for `∂_θ f`
  have hstep2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) z θ :=
    (Work.Spaces.pz_pth_comm (f := Work.Spaces.pth f)
      (((hf.pth).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))).of_le (by simp))).symm
  show Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [hstep1, hstep2]

/-- **The `θ`-energy of `∂_z∂_θ²Ψ` is the rescaled `θ`-energy of `D_z∂_θ²Ψ`**: for a datum
smooth on the open quadrant and a radius `s > 0`,

`∫_θ (∂_z∂_θ²Ψ(s,θ))² sEta(θ) = s⁻² ∫_θ (D_z∂_θ²Ψ(s,θ))² sEta(θ)`,

because `D_z = s ∂_z` at the radius `s` and `∂_z` commutes with `∂_θ²` on the open quadrant
(`pthIter2_pz_eqOn_open`), the two endpoints `θ = 0, π/2` being null. -/
theorem wsPzPthIterThetaE {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ) {s : ℝ}
    (hs : 0 < s) :
    Work.FTS.EllipticEst.remov.thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s
      = (s ^ 2)⁻¹ * Work.FTS.EllipticEst.remov.thetaE
          (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
  have hcl := pthIter2_pz_eqOn_open hS
  -- pointwise identity on the open interval, `D_z g = s · ∂_z g` there
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2
        = s ^ 2 * (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ) ^ 2 := by
    intro θ hθ
    have h1 : Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) s θ
        = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ :=
      (hcl (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hθ.1, hθ.2⟩)).symm
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    rw [h1]
    ring
  -- hence an a.e. identity of integrands
  have hae : (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => (s ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)) := by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [hpt θ hθ]
    field_simp
  simp only [Work.FTS.EllipticEst.remov.thetaE]
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]

end Work.FTS.EllipticEst.remov
