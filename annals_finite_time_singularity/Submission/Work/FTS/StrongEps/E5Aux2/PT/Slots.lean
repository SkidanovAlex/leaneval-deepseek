import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12densFstar_deriv
import Submission.Work.Stability.ZcutSmoothCompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The `pz`/`pth` splitting of `PhiTil` -/

/-- **The `z`-derivative of `PhiTil`** splits as soon as the `L₁₂`-part is differentiable at the
point and the `z`-slice of `Ψ` is. -/
theorem pz_PhiTil_eq_of_contDiffOn_one {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hL : DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z)
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pz (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Real.sin (2 * θ)
            * deriv (fun z' => Work.Construction.L12 F z') z := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hfun : (fun z' => Work.Construction.PhiTil α F Ψ z' θ)
      = fun z' => Ψ z' θ
          - ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 F z' := by
    funext z'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have hd1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    differentiableAt_zslice_of_contDiffOn_one hΨ hzθ
  have hd2 : DifferentiableAt ℝ
      (fun z' => ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 F z') z :=
    hL.const_mul _
  simp only [Work.Spaces.pz]
  rw [hfun]
  rw [show (fun z' => Ψ z' θ
        - ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 F z')
      = (fun z' => Ψ z' θ)
        - (fun z' => ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 F z') from rfl,
    deriv_sub hd1 hd2, deriv_const_mul _ hL]

/-- **The `θ`-derivative of `PhiTil`** splits unconditionally (the only `θ`-dependence of the
correction is the explicit factor `sin 2θ`). -/
theorem pth_PhiTil_eq_of_contDiffOn_one {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pth Ψ z θ
        - (1 / (4 * α)) * Work.Construction.L12 F z * (2 * Real.cos (2 * θ)) := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hfun : (fun θ' => Work.Construction.PhiTil α F Ψ z θ')
      = fun θ' => Ψ z θ'
          - ((1 / (4 * α)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    ring
  have hd1 : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    differentiableAt_tslice_of_contDiffOn_one hΨ hzθ
  have hd2 : DifferentiableAt ℝ
      (fun θ' => ((1 / (4 * α)) * Work.Construction.L12 F z) * Real.sin (2 * θ')) θ :=
    (by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ).const_mul _
  have hsin : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
    have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    rw [h2.deriv]; ring
  simp only [Work.Spaces.pth]
  rw [hfun]
  rw [show (fun θ' => Ψ z θ'
        - ((1 / (4 * α)) * Work.Construction.L12 F z) * Real.sin (2 * θ'))
      = (fun θ' => Ψ z θ')
        - (fun θ' => ((1 / (4 * α)) * Work.Construction.L12 F z) * Real.sin (2 * θ')) from rfl,
    deriv_sub hd1 hd2, deriv_const_mul _ (by fun_prop : DifferentiableAt ℝ
      (fun θ' : ℝ => Real.sin (2 * θ')) θ), hsin]

/-! ## The `N₀`-block, with the `L₁₂`-hypothesis only at the point -/

/-- **Pointwise convergence of `N₀`** (`Ioi 0`-form of `Work.FTS.StrongEps.N0_tendsto`). -/
theorem N0_tendsto_Ioi {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {Flim : ℝ → ℝ → ℝ}
    {w : ℕ → ℝ → ℝ → ℝ} {wlim : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hF : ∀ j i : ℕ, j + i ≤ 1 → Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hw : ∀ j i : ℕ, j + i ≤ 1 → Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed j i wlim z θ)))
    (hlw : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z) Filter.atTop
      (nhds (Work.Construction.L12 wlim z))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N0 α (F n) (w n) z θ) Filter.atTop
      (nhds (Work.Construction.N0 α Flim wlim z θ)) := by
  have hL : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z) Filter.atTop
      (nhds (Work.Construction.L12 wlim z)) := hlw
  have hg : Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (wlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using
      hw 0 0 (by norm_num)
  have hZg : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz wlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hw 1 0 (by norm_num)
  have hZF : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  have hDth : Filter.Tendsto
      (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  have hA : Filter.Tendsto (fun _ : ℕ =>
        (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - (Real.cos (2 * θ) - Real.sin θ ^ 2)
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      Filter.atTop (nhds _) := tendsto_const_nhds
  have hB : Filter.Tendsto (fun n : ℕ =>
        (1 / α) * Work.Construction.L12 (w n) z * (w n z θ))
      Filter.atTop (nhds ((1 / α) * Work.Construction.L12 wlim z * (wlim z θ))) :=
    (hL.const_mul (1 / α)).mul hg
  have hC : Filter.Tendsto (fun n : ℕ =>
        (3 / (2 * α)) * Work.Construction.L12 (w n) z
          * (Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ))
      Filter.atTop (nhds ((3 / (2 * α)) * Work.Construction.L12 wlim z
          * (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ))) :=
    (hL.const_mul (3 / (2 * α))).mul hDth
  have hD : Filter.Tendsto (fun n : ℕ =>
        (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 (w n) z
          * Work.Spaces.Dz (F n) z θ)
      Filter.atTop (nhds ((Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 wlim z
          * Work.Spaces.Dz Flim z θ)) :=
    (tendsto_const_nhds.mul hL).mul hZF
  have hE : Filter.Tendsto (fun n : ℕ =>
        (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (w n) z θ)
      Filter.atTop (nhds ((Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz wlim z θ)) :=
    hZg.const_mul ((Real.cos (2 * θ) - Real.sin θ ^ 2)
      * Work.Construction.L12 (Work.Construction.Fstar α) z)
  have hmain := (((hA.add hB).add hC).sub hD).sub hE
  convert hmain using 1
  · funext n
    simp only [Work.Construction.N0, Work.Construction.s2, Work.Construction.c2m]
    ring
  · congr 1
    simp only [Work.Construction.N0, Work.Construction.s2, Work.Construction.c2m]
    ring

/-! ## The transport block -/

/-- `Transport f = 3 D_θ f/(1+z)` is the slot `(0,1)`. -/
theorem Transport_eq_slot (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.Transport f z θ
      = 3 * Work.Spaces.mixed 0 1 f z θ / (1 + z) := by
  rw [Work.Coercivity.Transport, Work.Spaces.Dth]
  rw [mixed_zero_one]
  simp only [Work.Spaces.Dth]

/-- Pointwise convergence of the transport block, from the slot `(0,1)`. -/
theorem Transport_tendsto {w : ℕ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hs : Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed 0 1 (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed 0 1 W z θ))) :
    Filter.Tendsto (fun n : ℕ => Work.Coercivity.Transport (w n) z θ) Filter.atTop
      (nhds (Work.Coercivity.Transport W z θ)) := by
  have h := hs.const_mul (3 / (1 + z))
  have hfun : ∀ n : ℕ, Work.Coercivity.Transport (w n) z θ
      = (3 / (1 + z)) * Work.Spaces.mixed 0 1 (w n) z θ := by
    intro n; rw [Transport_eq_slot]; ring
  have hlim : Work.Coercivity.Transport W z θ
      = (3 / (1 + z)) * Work.Spaces.mixed 0 1 W z θ := by
    rw [Transport_eq_slot]; ring
  simp only [hfun, hlim]
  exact h

end Work.FTS.StrongEps.E5Aux2.PT
