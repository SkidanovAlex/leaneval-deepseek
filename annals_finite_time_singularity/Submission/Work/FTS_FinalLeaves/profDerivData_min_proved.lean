import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS_FinalLeaves.Min.FstarFacts
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_FinalLeaves.Min.ChainCont
import Submission.Work.FTS_FinalLeaves.Min.L12Cont
import Submission.Work.Construction.Defs
import Submission.Work.FM.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`ProfDerivData` from the finite-order package `RegPkgMin`.**

The seven static derivation fields of the meridian bridge follow from the finite-order regularity
package `Work.FTS.StrongGlobal.RegPkgMin α g` (joint `C¹` in `(z,θ,τ)`, spatial `C⁴` of each
slice, `ℋ⁴`-membership) and the interior `C²`-regularity of the stream function `Φ` on the open
quadrant.  This is the `RegPkgMin`-analogue of
`Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed`.

The two `L₁₂`-facts about the full profile `F_τ = F_* + g(·,·,τ)` (integrability of the density
on `(0,∞)`, continuity at `z > 0`) are obtained by additivity of the density from the slice
`g(·,·,τ)` — where `ContDiffOn ℝ 4` + `HkMem α 4` suffice (`Min.L12Cont`) — and from the explicit
profile `F_* α` (`Min.FstarFacts`).  No hypothesis on `α` is needed: when `c α = 0` the profile
`F_* α` vanishes identically. -/
theorem profDerivData_min_proved {α : ℝ} {Φ g : Work.FTS.Galerkin.Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin α g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd) :
    Work.FTS.MeridianDyn.ProfDerivData α Φ g := by
  have hQd_open : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- spatial regularity of the slices of `g`
  have hslice4 : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := fun τ hτ => hmin.c4 τ hτ.le
  have hmem4 : ∀ τ : ℝ, 0 < τ → Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice g τ) :=
    fun τ hτ => hmin.mem4 τ hτ.le
  -- the `L₁₂`-facts about the slice `g(τ)`
  have hsliceDenInt : ∀ τ : ℝ, 0 < τ → MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ)) (Set.Ioi 0) :=
    fun τ hτ => Min.L12dens_integrableOn_of_continuousOn (hslice4 τ hτ).continuousOn
      (hmem4 τ hτ)
  have hsliceDenCont : ∀ τ z : ℝ, 0 < τ → 0 < z → ContinuousAt
      (Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ)) z :=
    fun τ z hτ hz => Min.L12dens_continuousAt_of_contDiffOn_four α hz (hslice4 τ hτ)
      (hmem4 τ hτ)
  have hsliceSlice : ∀ τ : ℝ, 0 < τ → ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS.Galerkin.slice g τ s θ / s) Work.Spaces.Iθ :=
    fun τ hτ => Min.sliceK_integrableOn_of_continuousOn (hslice4 τ hτ).continuousOn
      (hmem4 τ hτ)
  -- the `L₁₂`-facts about `F_*`
  obtain ⟨hFsSlice, hFsInt, hFsCont⟩ := Min.Fstar_L12_facts α
  -- the `L₁₂`-facts about the full profile `F_τ = F_* + g(τ)`
  have hadd : ∀ τ : ℝ, 0 < τ → ∀ s : ℝ, 0 < s →
      Work.Construction.L12dens (Work.Construction.Ftau α g τ) s
        = Work.Construction.L12dens (Work.Construction.Fstar α) s
          + Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) s := by
    intro τ hτ s hs
    have h := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (a := Work.Construction.Fstar α) (b := Work.FTS.Galerkin.slice g τ)
      (s := s) (hFsSlice s hs) (hsliceSlice τ hτ s hs)
    rw [← Min.Ftau_eq_Fstar_add_slice α g τ] at h
    exact h
  have hdenInt : ∀ τ : ℝ, 0 < τ → MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Ftau α g τ)) (Set.Ioi 0) := by
    intro τ hτ
    have hsum := hFsInt.add (hsliceDenInt τ hτ)
    exact hsum.congr_fun (fun s hs => (hadd τ hτ s hs).symm) measurableSet_Ioi
  have hdenCont : ∀ τ z : ℝ, 0 < τ → 0 < z → ContinuousAt
      (Work.Construction.L12dens (Work.Construction.Ftau α g τ)) z := by
    intro τ z hτ hz
    have hsum := (hFsCont z hz).add (hsliceDenCont τ z hτ hz)
    refine hsum.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    exact (hadd τ hτ s hs).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `h2`
    intro z θ τ hQd hτ
    have hz : 0 < z := hQd.1
    have hzth : DifferentiableAt ℝ (fun z' => Φ z' θ τ) z := by
      have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, θ) :=
        ((hΦ τ hτ).contDiffAt (hQd_open.mem_nhds hQd)).differentiableAt (by norm_num)
      exact Work.Spaces.differentiableAt_curry_left (G := fun z' θ' => Φ z' θ' τ) hd
    have hthz : DifferentiableAt ℝ
        (fun z' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z :=
      Min.differentiableAt_Theta_slice_z (hdenInt τ hτ) (hdenCont τ z hτ hz) hz
    have hsub : deriv (fun z' => Φ z' θ τ
          - Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z
        = deriv (fun z' => Φ z' θ τ) z
          - deriv (fun z' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z :=
      deriv_sub hzth hthz
    simp only [Work.Spaces.pz, Work.Construction.PhiTil, Work.FTS.Galerkin.slice]
    rw [hsub]
    ring
  · -- `h3`
    intro z θ τ hQd hτ
    have hzth : DifferentiableAt ℝ (fun θ' => Φ z θ' τ) θ := by
      have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, θ) :=
        ((hΦ τ hτ).contDiffAt (hQd_open.mem_nhds hQd)).differentiableAt (by norm_num)
      exact Work.Spaces.differentiableAt_curry_right (G := fun z' θ' => Φ z' θ' τ) hd
    have htht : DifferentiableAt ℝ
        (fun θ' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ :=
      Min.differentiableAt_Theta_slice_theta
    have hsub : deriv (fun θ' => Φ z θ' τ
          - Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ
        = deriv (fun θ' => Φ z θ' τ) θ
          - deriv (fun θ' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ :=
      deriv_sub hzth htht
    simp only [Work.Spaces.pth, Work.Construction.PhiTil, Work.FTS.Galerkin.slice]
    rw [hsub]
    ring
  · -- `h5`
    intro z θ τ hQd hτ
    exact Min.Dz_Theta_eq_any (hdenInt τ hτ) (hdenCont τ z hτ hQd.1) hQd.1
  · -- `h6`
    intro z θ τ hQd hτ
    exact Min.pth_Theta_eq_any z θ
  · -- `hDz`
    intro z θ τ hQd hτ
    exact (Min.Dzg_pthg_split_c4 (α := α) (hslice4 τ hτ)).1 z θ hQd
  · -- `hpth`
    intro z θ τ hQd hτ
    exact (Min.Dzg_pthg_split_c4 (α := α) (hslice4 τ hτ)).2 z θ hQd
  · -- `hL`
    intro z τ hz hτ
    have hsum : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K
          (fun z θ => Work.Construction.Fstar α z θ + Work.FTS.Galerkin.slice g τ z θ))
        (Set.Ioi 0) := by
      have h := hdenInt τ hτ
      rwa [Min.Ftau_eq_Fstar_add_slice α g τ] at h
    have hsplit := Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
      (α := α) (a := Work.Construction.Fstar α) (b := Work.FTS.Galerkin.slice g τ)
      hFsSlice (hsliceSlice τ hτ) hsum hFsInt z hz
    rwa [← Min.Ftau_eq_Fstar_add_slice α g τ] at hsplit

end Work.FTS_FinalLeaves
