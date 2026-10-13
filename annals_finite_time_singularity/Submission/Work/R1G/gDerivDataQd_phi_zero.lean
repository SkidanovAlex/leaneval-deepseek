import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.Defs
import Submission.Work.Stability.L12Add
import Submission.Work.Stability.ThetaPzFtot
import Submission.Work.Stability.PthFstarAdd
import Submission.Work.Stability.PzFstarAdd
import Submission.Work.Coercivity.L12dens_integrableOn
import Submission.Work.Coercivity.L12_facts_n
import Submission.Work.Construction.Basic
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.R1G.L12densFstar_integrableOn
import Submission.Work.R1G.L12dens_g_integrableOn
import Submission.Work.R1G.L12densFtot_add
import Submission.Work.R1G.L12densFtot_continuousAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `GDerivDataQd` for the stationary zero-stream-function data of a `ProfileData`

The restricted derivation bundle `Work.R1G.GDerivDataQd` is *derivable from `ProfileData`*: at the
stationary perturbation `g = gOf3 P` and the *zero* stream function `φ = phiOf3 0` all seven fields
are theorems.  The two that carry analytic content are

* `h5` (`z ∂_z Θ = -(1/(4α)) sin(2θ)(F,K)`) — the Construction area's `Dz_Theta_eq`, whose
  hypotheses are integrability of the `L₁₂`-density of the *full* profile `F_* + P.g` on `(0,∞)`
  and its continuity at `z > 0`;
* `hL` (`L₁₂(F_* + g) = L₁₂(F_*) + L₁₂(g)` for `z ≥ 0`) — the additivity of the tail integral,
  which needs the integrability of both densities on `(z,∞)`.  This is precisely the place where
  the restriction `z ≥ 0` of `GDerivDataQd` (as opposed to `GDerivData`'s all-`z` version) is
  needed: for `z ≥ 0` the integration range misses the pole of `L12dens (F_*)` at `s = -1`, and
  `HkMem (profExp α) 2 P.g` makes the density of the perturbation integrable
  (`Work.Coercivity.L12dens_integrableOn`).

Everything else is bookkeeping: `h2`/`h3` are the *definitional* decomposition
`Φ = Φ̃ + Θ` at `Φ = 0` (`PhiTil α F 0 = -Theta α F`), `h6` is `pth_Theta_eq`, and `hDz`/`hpth` are
the additivity of `∂_z` resp. `∂_θ` over `F = F_* + g`, which holds on the open quadrant because
`P.g` is smooth on a neighbourhood of the closed quadrant.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.R1G

/-! ## Integrability of the angular slices -/

/-- The angular slice `θ ↦ K(θ)·P.g(s,θ)/s` of the perturbation is integrable on `Iθ` for `s > 0`:
it is continuous there by the `SmoothNbhd`-smoothness of `P.g` and the compactness of `Iθ`. -/
theorem integrableOn_slice_g {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * P.g s θ / s) Work.Spaces.Iθ := by
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  have hslice : ContinuousOn (fun θ => P.g s θ) Work.Spaces.Iθ :=
    Work.Elliptic.continuousOn_slice_theta_Iθ P.g P.hsmooth
      (by simp only [Set.mem_Ioi]; linarith)
  exact ((hK.mul hslice).div_const s).integrableOn_compact isCompact_Icc

/-- The angular slice of the **full** profile `F = F_* + P.g` is integrable on `Iθ` for `s > 0`:
both `F_*`-slices and `P.g`-slices are continuous there. -/
theorem integrableOn_slice_Ftot {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) {s : ℝ}
    (hs : 0 < s) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ
        * (Work.Construction.Fstar (Work.ConstructionInstance.profExp α) s θ + P.g s θ) / s)
      Work.Spaces.Iθ := by
  have hp : 0 < Work.ConstructionInstance.profExp α := profExp_pos_of_data P
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  have hGam : ContinuousOn
      (fun θ => Work.Spaces.Gam (Work.ConstructionInstance.profExp α) θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.Gam
    intro θ _
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp_continuousWithinAt
      (by fun_prop)
  have hF : ContinuousOn
      (fun θ => Work.Construction.Fstar (Work.ConstructionInstance.profExp α) s θ)
      Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact ((continuousOn_const.mul
      (hGam.div_const (Work.Spaces.c (Work.ConstructionInstance.profExp α)))).mul
        continuousOn_const)
  have hg : ContinuousOn (fun θ => P.g s θ) Work.Spaces.Iθ :=
    Work.Elliptic.continuousOn_slice_theta_Iθ P.g P.hsmooth
      (by simp only [Set.mem_Ioi]; linarith)
  exact ((hK.mul (hF.add hg)).div_const s).integrableOn_compact isCompact_Icc

/-! ## The `L₁₂`-density of the full profile -/

/-- **The `L₁₂`-density of the full profile is integrable on `(0,∞)`**: pointwise it is the sum of
the densities of `F_*` and of `P.g` (`L12densFtot_add`, valid for `r > 0`), and both are integrable
there (`L12densFstar_integrableOn`, `L12dens_g_integrableOn` at `z = 0`).  This is the
integrability input of `Work.Construction.Dz_Theta_eq` at the full profile. -/
theorem L12densFtot_integrableOn {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar (Work.ConstructionInstance.profExp α) z θ + P.g z θ))
      (Set.Ioi 0) := by
  have h1 := L12densFstar_integrableOn P (le_refl (0 : ℝ))
  have h2 := L12dens_g_integrableOn P (le_refl (0 : ℝ))
  refine (h1.add h2).congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (L12densFtot_add P (Set.mem_Ioi.mp hr)).symm

/-! ## Additivity of `L₁₂` over `F = F_* + g` -/

/-- **The `hL`-field**: for `z ≥ 0` the tail integral splits,
`L₁₂(F_* + g)(z) = L₁₂(F_*)(z) + L₁₂(g)(z)`.  The three hypotheses of
`Work.Stability.L12Add` are the integrability of the densities of `F_*` and of `P.g` on `(z,∞)`
(children of `Work.Coercivity.L12dens_integrableOn` for the first, of the explicit
`L12dens (F_*) = profExp α · F_*(s)/s` for the second) and the integrability of the angular
slices of the sum (continuity on the compact `Iθ`). -/
theorem L12_add_Ftot {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) (z : ℝ) (hz : 0 ≤ z) :
    Work.Construction.L12
        (fun z θ => Work.Construction.Fstar (Work.ConstructionInstance.profExp α) z θ + P.g z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar (Work.ConstructionInstance.profExp α)) z
        + Work.Construction.L12 P.g z := by
  have hp : 0 < Work.ConstructionInstance.profExp α := profExp_pos_of_data P
  have h1 := L12densFstar_integrableOn P hz
  have h2 := L12dens_g_integrableOn P hz
  have h3 : ∀ r ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ
        * (Work.Construction.Fstar (Work.ConstructionInstance.profExp α) r θ + P.g r θ) / r)
      Work.Spaces.Iθ := by
    intro r hr
    exact integrableOn_slice_Ftot P (by have := hr.out; linarith)
  exact Work.Stability.L12Add (Work.ConstructionInstance.profExp α) hp h1 h2 h3

/-! ## Differentiability of the slices of the perturbation on the quadrant -/

/-- `P.g` is differentiable at every point of the closed quadrant, hence so are its slices. -/
theorem differentiableAt_uncurry_g {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry P.g) (z, θ) := by
  have hz0 : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < Real.pi / 2 := hzθ.2.2
  have hmem : (z, θ) ∈ Work.Spaces.U :=
    Work.Spaces.mem_U_of_dom
      (by simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith)
      (by simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
  exact ((P.hsmooth : ContDiffOn ℝ ⊤ (Function.uncurry P.g) Work.Spaces.U).differentiableOn
    (n := ⊤) (by simp)).differentiableAt (Work.Spaces.isOpen_U.mem_nhds hmem)

/-! ## The derivation bundle at the stationary data with zero stream function -/

/-- **`GDerivDataQd` is derivable from `ProfileData`** at the stationary perturbation `P.g` and the
zero stream function.  All seven fields are proved; the analytic inputs are the integrability and
continuity facts of the `L₁₂`-density collected above. -/
theorem gDerivDataQd_phi_zero {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    Work.R1G.GDerivDataQd (Work.ConstructionInstance.profExp α) (Work.R1G.gOf3 P)
      (Work.R1G.phiOf3 (fun _ _ : ℝ => 0)) := by
  refine { h2 := ?_, h3 := ?_, h5 := ?_, h6 := ?_, hDz := ?_, hpth := ?_, hL := ?_ }
  · -- h2: the `Φ = Φ̃ + Θ` decomposition at `Φ = 0` is definitional (`PhiTil = Φ - Θ`)
    intro z θ s _
    simp only [Work.Stability.slice, Work.R1G.phiOf3, Work.Construction.PhiTil, Work.Spaces.pz]
    rw [deriv_const, deriv_const_sub]
    ring
  · -- h3: same for `∂_θ`
    intro z θ s _
    simp only [Work.Stability.slice, Work.R1G.phiOf3, Work.Construction.PhiTil, Work.Spaces.pth]
    rw [deriv_const, deriv_const_sub]
    ring
  · -- h5: `z∂_z Θ = -(1/(4α)) sin(2θ)(F,K)` (the Construction area's `Dz_Theta_eq`)
    intro z θ s hzθ
    have hz : 0 < z := hzθ.1
    exact Work.Stability.ThetaPzFtot (Work.ConstructionInstance.profExp α)
      (profExp_pos_of_data P) (Work.R1G.gOf3 P) z θ s (L12densFtot_integrableOn P)
      (L12densFtot_continuousAt P hz) hz
  · -- h6: `∂_θ Θ = (1/(2α)) cos(2θ) L₁₂(F)`
    intro z θ s _
    exact Work.Construction.pth_Theta_eq (profExp_pos_of_data P) z θ
  · -- hDz: `D_z(F_* + g) = D_zF_* + D_zg` on the quadrant
    intro z θ s hzθ
    have hz0 : 0 < z := hzθ.1
    have hz : -1 < z := by linarith
    have hg : DifferentiableAt ℝ (fun z' => Work.R1G.gOf3 P z' θ s) z := by
      simpa [Work.R1G.gOf3] using
        Work.Spaces.differentiableAt_curry_left (differentiableAt_uncurry_g P hzθ)
    simp only [Work.Spaces.Dz]
    rw [Work.Stability.PzFstarAdd (g := Work.R1G.gOf3 P) (s := s) hz hg]
    ring
  · -- hpth: `∂_θ(F_* + g) = ∂_θF_* + ∂_θg` on the quadrant
    intro z θ s hzθ
    have hθ : 0 < θ ∧ θ < Real.pi / 2 := ⟨hzθ.2.1, hzθ.2.2⟩
    have hg : DifferentiableAt ℝ (fun θ' => Work.R1G.gOf3 P z θ' s) θ := by
      simpa [Work.R1G.gOf3] using
        Work.Spaces.differentiableAt_curry_right (differentiableAt_uncurry_g P hzθ)
    rw [Work.Stability.PthFstarAdd (g := Work.R1G.gOf3 P) (s := s) hθ hg]
  · -- hL: additivity of `L₁₂` over `F = F_* + g` for `z ≥ 0`
    intro z s hz
    exact L12_add_Ftot P z hz

end Work.R1G
