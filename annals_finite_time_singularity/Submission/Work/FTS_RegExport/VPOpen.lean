import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.VPDefs
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.hbase_gS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

open scoped Topology Real
open Set Filter MeasureTheory

/-!
# `Work.FTS_RegExport.RXR1.hbase_gS` — the `hbase` field of `R1Block` at `gS α (tauExt g)`

The joint `C¹` regularity of `(z,τ) ↦ gS α (tauExt g) z θ τ` on `z > 0, τ > -1`, at every fixed
angle `θ ∈ Iθ`; the `hbase` field of the R1 block (`RegExportIface.R1Block`).

At `z > 0`, `θ ∈ Iθ` the sanitiser is transparent, so the function is the right-Taylor extension
`tauExt g`: for `τ ≥ 0` it is `g`, for `τ < 0` the affine jet `g z θ 0 + τ · ∂_τ⁺g(z,θ,0)`.  The
two branches are glued at `τ = 0` by the one-sided Taylor expansion of `g` at `τ = 0⁺` (the FTC in
`τ` plus the `Jet` property of the equation's right-hand side, uniform in `(z,θ)`); the `τ = 0`
slice is the explicit datum `locG6`, and the continuity of the candidate derivative at `τ = 0`
comes from the uniform `z`-derivative bound of the right-hand side.  At `θ = 0, π/2` the function
vanishes identically. -/

theorem hbase_gS {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hSt1 : ∀ S > 0,
      Work.FTS.RegPkgGal.St1Class α S (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
    (hR : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun z : ℝ =>
        Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) 0 z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) 0 z θ) (Set.Ioi 0)) :
    ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
      (fun q : ℝ × ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) q.1 θ q.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1))) := by
  intro θ hθ
  by_cases hint : 0 < θ ∧ θ < Real.pi / 2
  · -- ### the interior case `0 < θ < π/2`
    obtain ⟨L, β, hL1, hdat'⟩ := hdat
    have hθ0 : 0 < θ := hint.1
    have hθ1 : θ < Real.pi / 2 := hint.2
    have hθIoo : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    obtain ⟨Nc, hjet⟩ := hbg_RHS_jet hα hα13 H5
    obtain ⟨Nz, hNz0, hzbd⟩ := hbg_RHS_zderiv hα hα13 H5
    -- the `τ = 0` slice is the explicit datum `locG6`, hence `C¹` in `z`
    have hloc : ContDiffOn ℝ 1 (fun z : ℝ => g z θ 0) (Set.Ioi 0) := by
      have h3 : ContDiffOn ℝ 1
          (fun z : ℝ => Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
          (Set.Ioi 0) :=
        hbg_locG6_slice hθIoo (Work.FTS.Regularity.pExp_pos hα)
          (Work.FTS.Regularity.pExp_le_one hα13)
      have heq : (fun z : ℝ => g z θ 0)
          = (fun z : ℝ => Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ) :=
        funext (fun z => hdat' z θ)
      rwa [← heq] at h3
    have hder0 : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z' : ℝ => g z' θ 0)
        (deriv (fun z' : ℝ => g z' θ 0) z) z := by
      intro z hz
      exact ((hloc.differentiableOn one_ne_zero z hz).differentiableAt
        (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    -- the `τ ≥ 0` branch is `C¹` on the slab
    have hbc1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) := by
      have hmap : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => (q.1, (θ, q.2)))
          (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) :=
        contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
      refine (hOK.1.1.c1.comp hmap ?_).congr (fun q hq => rfl)
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      exact ⟨hz, ⟨hθ0, hθ1⟩, hτ⟩
    -- the jet is `C¹` on `z > 0, τ > -1`
    have hjc1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * hbgRHS α Φs E g q.1 θ 0)
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := by
      have hr0 : ContDiffOn ℝ 1 (fun z : ℝ => hbgRHS α Φs E g z θ 0) (Set.Ioi 0) := hR θ hθ
      have h1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ 0)
          (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) :=
        hloc.comp contDiffOn_fst (fun q hq => hq.1)
      have h2 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => q.2 * hbgRHS α Φs E g q.1 θ 0)
          (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) :=
        contDiffOn_snd.mul (hr0.comp contDiffOn_fst (fun q hq => hq.1))
      exact h1.add h2
    -- the slope of the jet is the one-sided `τ`-derivative at `0`
    have hslope : ∀ z ∈ Set.Ioi (0:ℝ),
        derivWithin (fun s : ℝ => g z θ s) (Set.Ici 0) 0 = hbgRHS α Φs E g z θ 0 := by
      intro z hz
      have h0 := (H5 1 one_pos).h0 z θ hz ⟨hz, hθ0, hθ1⟩
      have hfun : (fun s : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s)
          = fun s : ℝ => Work.FTS.FinalV2.tauExt g z θ s := by
        funext s; exact hbg_gS_eq hz hθ
      rw [hfun] at h0
      have h1 : derivWithin (fun s : ℝ => Work.FTS.FinalV2.tauExt g z θ s) (Set.Ici 0) 0
          = hbgRHS α Φs E g z θ 0 := h0.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
      have h2 : derivWithin (fun s : ℝ => Work.FTS.FinalV2.tauExt g z θ s) (Set.Ici 0) 0
          = derivWithin (fun s : ℝ => g z θ s) (Set.Ici 0) 0 :=
        derivWithin_congr (fun s hs => Work.FTS.FinalV2.tauExt_of_nonneg g hs)
          (Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl)
      rw [h2] at h1
      exact h1
    have hGb : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), 0 ≤ q.2 →
        Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) q.1 θ q.2 = g q.1 θ q.2 := by
      rintro ⟨z, τ⟩ hq hτ
      rw [hbg_gS_eq hq.1 hθ, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    have hGj : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), q.2 ≤ 0 →
        Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) q.1 θ q.2
          = g q.1 θ 0 + q.2 * hbgRHS α Φs E g q.1 θ 0 := by
      rintro ⟨z, τ⟩ hq hτ
      rw [hbg_gS_eq hq.1 hθ]
      rcases lt_or_eq_of_le hτ with h | h
      · rw [Work.FTS.FinalV2.tauExt_of_neg g h, hslope z hq.1]
      · subst h
        rw [Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl]
        ring
    have hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) := (H5 1 one_pos).hsol
    have hRderiv : ∀ z ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Ioi (0:ℝ),
        deriv (fun s : ℝ => g z θ s) τ = hbgRHS α Φs E g z θ τ := by
      intro z hz τ hτ
      have h0 := hsol z θ τ hτ.le ⟨hz, hθ0, hθ1⟩
      have hfun : (fun s : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s)
          =ᶠ[𝓝 τ] (fun s : ℝ => g z θ s) := by
        filter_upwards [isOpen_Ioi.mem_nhds hτ] with s hs
        rw [hbg_gS_eq hz hθ, Work.FTS.FinalV2.tauExt_of_nonneg g hs.le]
      exact ((h0.hasDerivAt (Ici_mem_nhds hτ)).congr_of_eventuallyEq hfun.symm).deriv
    have hFTC : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ k ∈ Set.Icc (0:ℝ) 1,
        g z' θ k - g z' θ 0 = ∫ s in (0:ℝ)..k, hbgRHS α Φs E g z' θ s := by
      intro z' hz' k hk
      have hRcont : ContinuousOn (fun s : ℝ => hbgRHS α Φs E g z' θ s) (Set.Icc (0:ℝ) 1) := by
        refine hbg_contOn_of_holder (Work.FTS.Regularity.Jet.nonneg hjet) hα (fun x hx y hy => ?_)
        have h := hjet.2.2 z' z' θ θ x y hz'.le hz'.le hθ hθ hx hy
        simpa using h
      exact ftc_slice hθ0 hθ1 hz' hk hsol (hOK.1.1.cont z' θ ⟨hz', hθ0, hθ1⟩) hRcont
    have hE3 : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
        |deriv (fun z'' => g z'' θ τ) z' - deriv (fun z'' => g z'' θ 0) z'| ≤ Nz * τ := by
      refine dz_tau_cont (z := 0) hNz0 hFTC (fun τ hτ z' hz' => hzbd τ hτ θ hθ z' hz') ?_ ?_
      · intro z' hz'
        exact ((hloc.differentiableOn one_ne_zero z' hz').differentiableAt
          (isOpen_Ioi.mem_nhds hz')).hasDerivAt
      · intro τ hτ z' hz'
        exact hbg_hasDerivAt_slice_z (isOpen_Ioi.prod isOpen_Ioi) hbc1 ⟨hz', hτ.1⟩
    have hexp : ∀ z ∈ Set.Ioi (0:ℝ), ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ × ℝ,
        ‖y - (z, (0:ℝ))‖ < δ → 0 ≤ y.2 →
        ‖(fun q : ℝ × ℝ => g q.1 θ q.2) y - (fun q : ℝ × ℝ => g q.1 θ q.2) (z, (0:ℝ))
          - fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * hbgRHS α Φs E g q.1 θ 0) (z, (0:ℝ))
              (y - (z, (0:ℝ)))‖ ≤ ε * ‖y - (z, (0:ℝ))‖ := by
      intro z hz ε hε
      obtain ⟨δ, hδpos, hδ⟩ := oneSided_expansion hα (Work.FTS.Regularity.Jet.nonneg hjet)
        hθ hz hFTC hjet (hder0 z hz) ε hε
      refine ⟨δ, hδpos, ?_⟩
      intro y hy hy2
      have hfd : fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * hbgRHS α Φs E g q.1 θ 0)
            (z, (0:ℝ)) (y - (z, (0:ℝ)))
          = deriv (fun z' : ℝ => g z' θ 0) z * (y.1 - z) + hbgRHS α Φs E g z θ 0 * y.2 := by
        have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * hbgRHS α Φs E g q.1 θ 0)
            (z, (0:ℝ)) :=
          (Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one
            (isOpen_Ioi.prod isOpen_Ioi) hjc1 ⟨hz, by norm_num⟩).differentiableAt
        rw [Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hd]
        have e1 : deriv (fun z' : ℝ => g z' θ 0 + (0:ℝ) * hbgRHS α Φs E g z' θ 0) z
            = deriv (fun z' : ℝ => g z' θ 0) z :=
          Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall (fun z' => by ring))
        have e2 : deriv (fun s : ℝ => g z θ 0 + s * hbgRHS α Φs E g z θ 0) (0:ℝ)
            = hbgRHS α Φs E g z θ 0 := by
          have hh : HasDerivAt (fun s : ℝ => g z θ 0 + id s * hbgRHS α Φs E g z θ 0)
              (0 + 1 * hbgRHS α Φs E g z θ 0) (0:ℝ) :=
            (hasDerivAt_const (0:ℝ) (g z θ 0)).add
              ((hasDerivAt_id (0:ℝ)).mul_const (hbgRHS α Φs E g z θ 0))
          have hh2 : HasDerivAt (fun s : ℝ => g z θ 0 + s * hbgRHS α Φs E g z θ 0)
              (hbgRHS α Φs E g z θ 0) (0:ℝ) := by
            simpa using hh
          exact hh2.deriv
        rw [e1, e2]
        have hv : (y - (z, (0:ℝ)) : ℝ × ℝ) = (y.1 - z, y.2) := by ext <;> simp
        rw [hv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        change deriv (fun z' : ℝ => g z' θ 0) z * (y.1 - z) + hbgRHS α Φs E g z θ 0 * y.2
            = deriv (fun z' : ℝ => g z' θ 0) z * (y.1 - z) + hbgRHS α Φs E g z θ 0 * y.2
        ring
      rw [hfd]
      simpa only [sub_add_eq_sub_sub] using hδ y hy hy2
    have hcd := hbg_hcd hα hθ hloc hbc1 hjc1 hjet hNz0 hE3 hRderiv
    exact hbg_glue hjc1 hbc1 hGj hGb hexp hcd
  · -- ### the boundary angles `θ = 0, π/2`: the function vanishes on the domain
    have hzero : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)),
        Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) q.1 θ q.2 = 0 := by
      rintro ⟨z, τ⟩ hq
      have hz : 0 < z := hq.1
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases lt_or_ge 0 θ with h | h
        · right
          have : ¬ (θ < Real.pi / 2) := fun hh => hint ⟨h, hh⟩
          linarith [hθ.2]
        · left; linarith [hθ.1]
      rw [hbg_gS_eq hz hθ]
      have hv : ∀ s : ℝ, 0 ≤ s → g z θ s = 0 := by
        intro s hs
        rcases hcases with h | h
        · rw [h]; exact (hOK.1.1.vanish s hs z hz.le).1
        · rw [h]; exact (hOK.1.1.vanish s hs z hz.le).2
      by_cases hτ : τ < 0
      · rw [Work.FTS.FinalV2.tauExt_of_neg g hτ]
        have h1 : g z θ 0 = 0 := hv 0 le_rfl
        have h2 : derivWithin (fun s : ℝ => g z θ s) (Set.Ici 0) 0 = 0 := by
          have hc : derivWithin (fun _ : ℝ => (0:ℝ)) (Set.Ici 0) (0:ℝ) = 0 :=
            (hasDerivWithinAt_const (0:ℝ) (Set.Ici 0) (0:ℝ)).derivWithin
              (uniqueDiffWithinAt_Ici 0)
          exact (derivWithin_congr (fun s hs => (hv s hs).symm) (hv 0 le_rfl).symm).symm.trans hc
        rw [h1, h2]; ring
      · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (le_of_not_gt hτ)]
        exact hv τ (le_of_not_gt hτ)
    exact (contDiffOn_const (c := (0:ℝ))).congr (fun q hq => hzero q hq)

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.hj_cluster =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

theorem hj_cluster {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hSt1 : ∀ S > 0,
      Work.FTS.RegPkgGal.St1Class α S (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∀ S > 0,
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ p.2)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ p.2)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ =>
            deriv (fun z => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ p.2) p.1)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) := by
  intro S hS
  have hS2 : (0 : ℝ) < S + 2 := by linarith
  -- the two hypotheses, restated about the abbreviations `Gs`/`Ps`
  have hSt1' : ∀ S' > 0, Work.FTS.RegPkgGal.St1Class α S' (Gs α g) := hSt1
  have H5' : ∀ S' > 0, Work.FTS.RegPkgGal.R5Parts α S' (Gs α g) (Ps α Φs E g) := H5
  obtain ⟨K, Q, hK, hQ, hquad⟩ := (hSt1' (S + 2) hS2).quad
  obtain ⟨NZ, hNZ, hRbd, hRder⟩ :=
    exists_RHS_bound (S := S + 2) hα hα13 hS2 (H5' (S + 2) hS2)
  have H : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
      (Tendsto (fun p : ℝ × ℝ => Gs α g p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
      (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * Gs α g p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
      (Tendsto (fun p : ℝ × ℝ => deriv (fun z => Gs α g z θ p.2) p.1) (Filt τ₀) (nhds 0)) := by
    intro θ hθ τ₀ hτ₀
    by_cases hends : θ = 0 ∨ θ = Real.pi / 2
    · have hz : ∀ z τ : ℝ, Gs α g z θ τ = 0 :=
        Gs_eq_zero_of_ends (hOK.1.1).vanish hθ hends
      refine ⟨?_, ?_, ?_⟩
      · exact tendsto_const_nhds.congr' (Eventually.of_forall fun p => (hz p.1 p.2).symm)
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun p => ?_)
        show (0 : ℝ) = p.1⁻¹ * Gs α g p.1 θ p.2
        rw [hz p.1 p.2]
        ring
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun p => ?_)
        show (0 : ℝ) = deriv (fun z : ℝ => Gs α g z θ p.2) p.1
        rw [show (fun z : ℝ => Gs α g z θ p.2) = fun _ => (0 : ℝ) from
          funext fun z => hz z p.2]
        simp
    · have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (fun h => hends (Or.inl h.symm)),
          lt_of_le_of_ne hθ.2 (fun h => hends (Or.inr h))⟩
      have hquadv : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
          |Gs α g z θ τ| ≤ K * z ^ 2 := by
        intro τ hτ z hz
        have h := (hquad τ hτ θ hθ).1 z hz.1.le hz.2.le
        rwa [Work.FTS.RegPkgGal.extG_of_pos hz.1 hτ.1] at h
      have hquadd : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
          |deriv (fun z' => Gs α g z' θ τ) z| ≤ Q * z := by
        intro τ hτ z hz
        have h := (hquad τ hτ θ hθ).2 z hz.1.le hz.2.le
        have hcongr : Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG (Gs α g)) τ) z θ
            = deriv (fun z' => Gs α g z' θ τ) z := by
          simp only [Work.Spaces.pz]
          exact (Filter.EventuallyEq.deriv_eq (by
            filter_upwards [isOpen_Ioi.mem_nhds hz.1] with z' hz'
            show Gs α g z' θ τ
              = Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG (Gs α g)) τ z' θ
            rw [show Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG (Gs α g)) τ z' θ
                = Work.FTS.RegPkgGal.extG (Gs α g) z' θ τ from rfl,
              Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1])).symm
        rwa [hcongr] at h
      have hneg : ∀ z ∈ Set.Ioo (0 : ℝ) 2, ∀ τ < 0,
          Gs α g z θ τ = g z θ 0 + τ * RHSo α (Gs α g) (Ps α Φs E g) z θ := by
        intro z hz τ hτ
        rw [Gs_of_neg hz.1 hθ hτ, derivWithin_g_eq hz.1 hθ,
          derivWithin_eq_RHS (H5 (S + 2) hS2) hθIoo hz.1]
      have hdat0 : ∀ z ∈ Set.Ioo (0 : ℝ) 2, |g z θ 0| ≤ K * z ^ 2 := by
        intro z hz
        have h := hquadv 0 ⟨le_rfl, by linarith⟩ z hz
        rwa [Gs_of_nonneg hz.1 hθ le_rfl] at h
      have hA : ∀ z ∈ Set.Ioo (0 : ℝ) 2,
          ∃ A : ℝ, HasDerivAt (fun z' => g z' θ 0) A z ∧ |A| ≤ Q * z := by
        intro z hz
        have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz.1, hθIoo⟩
        have hsm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g 0))
            Work.FTS.EllipticEst.Q0 := (hOK.1.1).c4 0 le_rfl
        have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g 0)) (z, θ) :=
          (hsm.differentiableOn (by norm_num)).differentiableAt
            (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
        have hcomp : HasFDerivAt
            (fun z' : ℝ => Function.uncurry (Work.FTS.Galerkin.slice g 0) (z', θ))
            ((fderiv ℝ (Function.uncurry (Work.FTS.Galerkin.slice g 0)) (z, θ))
              ∘SL ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
          HasFDerivAt.comp z (g := Function.uncurry (Work.FTS.Galerkin.slice g 0))
            (f := fun z' : ℝ => (z', θ)) hdiff.hasFDerivAt (hasFDerivAt_prodMk_left z θ)
        have hAd : HasDerivAt (fun z' => g z' θ 0)
            ((fderiv ℝ (Function.uncurry (Work.FTS.Galerkin.slice g 0)) (z, θ)) (1, 0)) z := by
          have h := hcomp.hasDerivAt
          simpa only [Function.uncurry, Work.FTS.Galerkin.slice_apply,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using h
        refine ⟨_, hAd, ?_⟩
        rw [← hAd.deriv]
        have hcongr2 : deriv (fun z' => g z' θ 0) z = deriv (fun z' => Gs α g z' θ 0) z :=
          Filter.EventuallyEq.deriv_eq (by
            filter_upwards [isOpen_Ioi.mem_nhds hz.1] with z' hz'
            exact (Gs_of_nonneg hz' hθ le_rfl).symm)
        rw [hcongr2]
        exact hquadd 0 ⟨le_rfl, by linarith⟩ z hz
      rcases lt_or_eq_of_le hτ₀.1 with hτpos | hτzero
      · exact hj_triple_pos (G := Gs α g) hτpos (by linarith [hτ₀.2]) hquadv hquadd
      · subst hτzero
        exact hj_triple_zero (G := Gs α g)
          (R := fun z θ => RHSo α (Gs α g) (Ps α Φs E g) z θ) (gd := fun z => g z θ 0)
          hK hNZ hS2 hdat0 hquadv hquadd hneg (fun z hz => hRbd θ hθ z hz.1)
          (fun z hz => hRder θ hθ z hz.1) hA
  exact ⟨fun θ hθ τ₀ hτ₀ => (H θ hθ τ₀ hτ₀).1,
    fun θ hθ τ₀ hτ₀ => (H θ hθ τ₀ hτ₀).2.1,
    fun θ hθ τ₀ hτ₀ => (H θ hθ τ₀ hτ₀).2.2⟩

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.jc3_tau =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `cth` inverts `ψ ↦ log (tan ·)` on the open quadrant. -/
lemma cth_log_tan {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi / 2) :
    cth (Real.log (Real.tan θ)) = θ := by
  rw [cth, Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two h0 hπ),
    Real.arctan_tan (by linarith [Real.pi_pos]) hπ]

/-- The final step of the Landau estimate: on a compact time interval a `√`-Hölder bound,
available up to the size `δ₀` of the space interval of the Landau step, gives continuity. -/
lemma continuousWithinAt_of_sqrt_bound {f : ℝ → ℝ} {T τ K ε δ₀ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hδ₀ : 0 < δ₀)
    (h : ∀ σ ∈ Set.Icc (0:ℝ) T, |σ - τ| ≤ δ₀ → |f σ - f τ| ≤ K * Real.sqrt |σ - τ|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Set.Icc (0:ℝ) T, |σ - τ| < δ → |f σ - f τ| < ε := by
  refine ⟨min δ₀ ((ε / (K + 1)) ^ 2), lt_min hδ₀ (by positivity), fun σ hσ hd => ?_⟩
  have h1 : |σ - τ| ≤ δ₀ := le_of_lt (lt_of_lt_of_le hd (min_le_left _ _))
  have h2 : |σ - τ| ≤ (ε / (K + 1)) ^ 2 := le_of_lt (lt_of_lt_of_le hd (min_le_right _ _))
  have hpos : (0:ℝ) ≤ ε / (K + 1) := by positivity
  have hs : Real.sqrt |σ - τ| ≤ ε / (K + 1) := by
    calc Real.sqrt |σ - τ| ≤ Real.sqrt ((ε / (K + 1)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ε / (K + 1) := Real.sqrt_sq hpos
  have hfin : K * (ε / (K + 1)) < ε := by
    have h3 : K * (ε / (K + 1)) = ε * (K / (K + 1)) := by ring
    rw [h3]
    have h4 : K / (K + 1) < 1 := by
      rw [div_lt_one (by linarith : (0:ℝ) < K + 1)]
      linarith
    nlinarith
  calc |f σ - f τ| ≤ K * Real.sqrt |σ - τ| := h σ hσ h1
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hs hK
    _ < ε := hfin

theorem tau_cont_mixed {g : Work.FTS.Galerkin.Fam} {T z θ dθ Lτ Cs : ℝ}
    (hT : 0 < T) (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hdθpos : 0 < dθ) (hdθle : dθ ≤ (Real.pi / 2 - θ) / 2)
    (hLτnn : 0 ≤ Lτ) (hCsnn : 0 ≤ Cs) {j i : ℕ} (hji : j + i ≤ 3)
    (hc4 : ∀ σ ∈ Set.Icc (0:ℝ) T, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice g σ)) Work.FTS.EllipticEst.Q0)
    (hTau : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ x y : ℝ, 0 < x → 0 < y → y < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g σ) x y
          - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g σ') x y| ≤ Lτ * |σ - σ'|)
    (hSpaceZ : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ j' i' : ℕ, j' + i' ≤ 3 →
      ∀ x ∈ Set.Icc (z / 2) (3 * z / 2), ∀ y ∈ Set.Icc (θ - dθ) (θ + dθ),
      ∀ x' ∈ Set.Icc (z / 2) (3 * z / 2),
        |Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x y
          - Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x' y| ≤ Cs * |x - x'|)
    (hSpaceθ : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ j' i' : ℕ, j' + i' ≤ 3 →
      ∀ x ∈ Set.Icc (z / 2) (3 * z / 2), ∀ y ∈ Set.Icc (θ - dθ) (θ + dθ),
      ∀ y' ∈ Set.Icc (θ - dθ) (θ + dθ),
        |Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x y
          - Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x y'| ≤ Cs * |y - y'|)
    (hLandau : ∀ {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ}, 0 < δc → 0 ≤ L → 0 ≤ K →
      (∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |V x τ - V x τ'| ≤ L * |τ - τ'|) →
      (∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc))) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |W x τ - W x₀ τ| ≤ K * |x - x₀|) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        HasDerivAt (fun x' => V x' τ) (W x τ) x) →
      ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δc ^ 2 →
        |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'|)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    ContinuousWithinAt (fun σ : ℝ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ)
      (Set.Icc (0:ℝ) T) τ := by
  have hθmem' : θ ∈ Set.Icc (θ - dθ) (θ + dθ) := ⟨by linarith, by linarith⟩
  have hzmem' : z ∈ Set.Icc (z / 2) (3 * z / 2) := ⟨by linarith, by linarith⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- `j = 0`
    subst hj0
    rcases lt_or_ge i 3 with hi3 | hi3
    · -- `i ≤ 2`: the slot itself is Lipschitz in `τ`
      have hi2 : i ≤ 2 := by omega
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      refine ⟨ε / (Lτ + 1), by positivity, ?_⟩
      intro σ hσ hd
      rw [Real.dist_eq] at hd ⊢
      have hb := hTau σ hσ τ hτ 0 i hi2 z θ hz hθ0 hθπ
      have hstep : Lτ * |σ - τ| ≤ Lτ * (ε / (Lτ + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hd) hLτnn
      have hfin : Lτ * (ε / (Lτ + 1)) < ε := by
        have h1 : Lτ * (ε / (Lτ + 1)) = ε * (Lτ / (Lτ + 1)) := by ring
        rw [h1]
        have h2 : Lτ / (Lτ + 1) < 1 := by
          rw [div_lt_one (by linarith : (0:ℝ) < Lτ + 1)]
          linarith
        nlinarith
      linarith
    · -- `i = 3`: the Landau step in the `θ`-direction
      have hi3' : i = 3 := by omega
      subst hi3'
      set ψ₀ : ℝ := Real.log (Real.tan θ) with hψ₀def
      set ψhi : ℝ := Real.log (Real.tan (θ + dθ)) with hψhidef
      set δc : ℝ := (ψhi - ψ₀) / 2 with hδcdef
      have hθhipos : 0 < θ + dθ := by linarith
      have hθhilt : θ + dθ < Real.pi / 2 := by linarith
      have htanθ : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ
      have htanθhi : 0 < Real.tan (θ + dθ) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two hθhipos hθhilt
      have htan_lt : Real.tan θ < Real.tan (θ + dθ) :=
        Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos]) hθhilt
          (by linarith)
      have hδcpos : 0 < δc := by
        rw [hδcdef]
        have h := Real.log_lt_log htanθ htan_lt
        linarith
      set Θ : ℝ → ℝ := fun x => cth (ψ₀ + 2 * x) with hΘdef
      have hΘderiv : ∀ x : ℝ, HasDerivAt Θ (Real.sin (2 * Θ x)) x := by
        intro x
        have h1 : HasDerivAt cth (Real.sin (2 * cth (ψ₀ + 2 * x)) / 2) (ψ₀ + 2 * x) :=
          hasDerivAt_cth (ψ₀ + 2 * x)
        have h2 : HasDerivAt (fun x' : ℝ => ψ₀ + 2 * x') 2 x := by
          simpa using ((hasDerivAt_id x).const_mul (2:ℝ)).const_add ψ₀
        have h3 := h1.comp x h2
        have hv : (Real.sin (2 * cth (ψ₀ + 2 * x)) / 2) * 2 = Real.sin (2 * Θ x) := by
          rw [hΘdef]; ring
        rw [hv] at h3
        exact h3
      have hΘ0 : Θ 0 = θ := by
        rw [hΘdef]
        show cth (ψ₀ + 2 * 0) = θ
        rw [show ψ₀ + 2 * 0 = ψ₀ by ring, hψ₀def]
        exact cth_log_tan hθ0 hθπ
      have hΘδ : Θ δc = θ + dθ := by
        rw [hΘdef]
        show cth (ψ₀ + 2 * δc) = θ + dθ
        rw [show ψ₀ + 2 * δc = ψhi by rw [hδcdef]; ring, hψhidef]
        exact cth_log_tan hθhipos hθhilt
      have hΘx_eq : ∀ x : ℝ, Real.arctan (Real.exp (ψ₀ + 2 * x)) = Θ x := by
        intro x; rw [hΘdef]; rfl
      have hΘmono : ∀ x ∈ Set.Icc (0:ℝ) δc, Θ x ≤ Θ δc := by
        intro x hx
        have h1 : Real.exp (ψ₀ + 2 * x) ≤ Real.exp (ψ₀ + 2 * δc) :=
          Real.exp_le_exp.mpr (by linarith [hx.2])
        have h2 := Real.arctan_mono h1
        rwa [hΘx_eq x, show Real.arctan (Real.exp (ψ₀ + 2 * δc)) = Θ δc from hΘx_eq δc] at h2
      have hΘge : ∀ x ∈ Set.Icc (0:ℝ) δc, θ ≤ Θ x := by
        intro x hx
        have h1 : Real.exp (ψ₀ + 2 * 0) ≤ Real.exp (ψ₀ + 2 * x) :=
          Real.exp_le_exp.mpr (by linarith [hx.1])
        have h2 := Real.arctan_mono h1
        have h3 : Real.arctan (Real.exp (ψ₀ + 2 * 0)) = θ := by
          rw [show ψ₀ + 2 * 0 = ψ₀ by ring, hψ₀def]
          exact cth_log_tan hθ0 hθπ
        rwa [h3, hΘx_eq x] at h2
      have hΘmem : ∀ x ∈ Set.Icc (0:ℝ) δc, Θ x ∈ Set.Icc (θ - dθ) (θ + dθ) := by
        intro x hx
        have h1 := hΘge x hx
        have h2 := hΘmono x hx
        rw [hΘδ] at h2
        exact ⟨by linarith, h2⟩
      have hΘlip : ∀ x ∈ Set.Icc (0:ℝ) δc, |Θ x - θ| ≤ 1 * |x| := by
        intro x hx
        have hdiff : ∀ y ∈ Set.Icc (0:ℝ) δc, DifferentiableAt ℝ Θ y :=
          fun y _ => (hΘderiv y).differentiableAt
        have hbnd : ∀ y ∈ Set.Icc (0:ℝ) δc, ‖deriv Θ y‖ ≤ 1 := by
          intro y hy
          rw [Real.norm_eq_abs, (hΘderiv y).deriv]
          exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
        have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd
          (convex_Icc (0:ℝ) δc) ⟨le_rfl, hδcpos.le⟩ hx
        rw [Real.norm_eq_abs, Real.norm_eq_abs, hΘ0, sub_zero] at h
        exact h
      set Vt : ℝ → ℝ → ℝ := fun x σ =>
        Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g σ) z (Θ x) with hVtdef
      set Wt : ℝ → ℝ → ℝ := fun x σ =>
        Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z (Θ x) with hWtdef
      have hVh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T,
          ∀ x ∈ Set.Icc (0:ℝ) (0 + δc), |Vt x σ - Vt x σ'| ≤ Lτ * |σ - σ'| := by
        intro σ hσ σ' hσ' x hx
        have h := hTau σ hσ σ' hσ' 0 2 (by omega) z (Θ x) hz
          (cth_pos (ψ₀ + 2 * x)) (cth_lt (ψ₀ + 2 * x))
        simpa only [hVtdef] using h
      have hch : ∀ σ ∈ Set.Icc (0:ℝ) T,
          ContinuousOn (fun x => Wt x σ) (Set.Icc (0:ℝ) (0 + δc)) := by
        intro σ hσ
        have hc : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) p.1 p.2)
            Work.FTS.EllipticEst.Q0 := continuousOn_mixed_of_four (hc4 σ hσ) (by omega)
        have hΘc : Continuous Θ := by
          rw [hΘdef]
          exact (Real.continuous_arctan.comp Real.continuous_exp).comp
            (continuous_const.add (continuous_const.mul continuous_id))
        have hmap : ∀ x ∈ Set.Icc (0:ℝ) (0 + δc), (z, Θ x) ∈ Work.FTS.EllipticEst.Q0 :=
          fun x _ => Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨hz, cth_pos (ψ₀ + 2 * x), cth_lt (ψ₀ + 2 * x)⟩
        have hcomp := hc.comp (continuousOn_const.prodMk hΘc.continuousOn) hmap
        simpa only [hWtdef, Function.comp_def] using hcomp
      have hWh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + δc),
          |Wt x σ - Wt 0 σ| ≤ (1 * Cs) * |x - 0| := by
        intro σ hσ x hx
        have hx' : x ∈ Set.Icc (0:ℝ) δc := by simpa only [zero_add] using hx
        have h := hSpaceθ σ hσ 0 3 (by omega) z hzmem' (Θ x) (hΘmem x hx') θ hθmem'
        have h2 : |Θ x - θ| ≤ 1 * |x - 0| := by
          rw [sub_zero]; exact hΘlip x hx'
        rw [hWtdef]
        simp only [mul_zero, add_zero, hΘ0]
        calc |Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z (Θ x)
              - Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z θ|
            ≤ Cs * |Θ x - θ| := h
          _ ≤ Cs * (1 * |x - 0|) := mul_le_mul_of_nonneg_left h2 hCsnn
          _ = (1 * Cs) * |x - 0| := by ring
      have hdh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + δc),
          HasDerivAt (fun x' => Vt x' σ) (Wt x σ) x := by
        intro σ hσ x hx
        have hslice := hasDerivAt_slice_snd_of_contDiffOn (z := z) (θ := Θ x)
          Work.FTS.EllipticEst.isOpen_Q0
          (contDiffOn_mixed_of_four (hc4 σ hσ) (by omega : 0 + 2 ≤ 3))
          (Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨hz, cth_pos (ψ₀ + 2 * x), cth_lt (ψ₀ + 2 * x)⟩)
        have hcomp := hslice.comp x (hΘderiv x)
        have hv : Work.Spaces.pth (Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g σ))
              z (Θ x) * Real.sin (2 * Θ x)
            = Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z (Θ x) := by
          rw [mixed_zero_three_eq]
          ring
        rw [hv] at hcomp
        simpa only [hVtdef, hWtdef, Function.comp_def] using hcomp
      have hLand := tau_lip_sqrt_of_primitive_Icc hT hLandau (V := Vt) (W := Wt)
        (x₀ := 0) (δc := δc) (L := Lτ) (K := 1 * Cs)
        hδcpos (by positivity) (by positivity) hVh hch hWh hdh
      have hW0 : ∀ σ : ℝ, Wt 0 σ
          = Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z θ := by
        intro σ
        rw [hWtdef]
        simp only [mul_zero, add_zero, hΘ0]
      have hcontWt : ContinuousWithinAt (fun σ : ℝ => Wt 0 σ) (Set.Icc (0:ℝ) T) τ := by
        rw [Metric.continuousWithinAt_iff]
        intro ε hε
        obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := continuousWithinAt_of_sqrt_bound
          (f := fun σ : ℝ => Wt 0 σ) (T := T) (τ := τ) (K := 2 * Lτ + 1 * Cs)
          (δ₀ := δc ^ 2) hε (by positivity) (by positivity)
          (fun σ hσ hστ => hLand σ hσ τ hτ hστ)
        refine ⟨min δ₂ (δc ^ 2), by positivity, ?_⟩
        intro σ hσ hd
        rw [Real.dist_eq] at hd
        exact hδ₂ σ hσ (lt_of_lt_of_le hd (min_le_left _ _))
      rw [show (fun σ : ℝ => Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z θ)
          = fun σ : ℝ => Wt 0 σ from funext (fun σ => (hW0 σ).symm)]
      exact hcontWt
  · -- `j ≥ 1`: the Landau step in the `z`-direction
    have hj1 : 1 ≤ j := hjpos
    have hji' : i + (j - 1) ≤ 2 := by omega
    set Vz : ℝ → ℝ → ℝ := fun x σ =>
      Work.Spaces.mixed (j - 1) i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ with hVzdef
    set Wz : ℝ → ℝ → ℝ := fun x σ =>
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ with hWzdef
    have hδc : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    have hexp2 : Real.exp (Real.log (3 / 2)) = 3 / 2 := Real.exp_log (by norm_num)
    have hKc : 0 ≤ 2 * z * Cs := by positivity
    have hVh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T,
        ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)), |Vz x σ - Vz x σ'| ≤ Lτ * |σ - σ'| := by
      intro σ hσ σ' hσ' x hx
      have h := hTau σ hσ σ' hσ' (j - 1) i hji' (z * Real.exp x) θ
        (by positivity) hθ0 hθπ
      simpa only [hVzdef] using h
    have hch : ∀ σ ∈ Set.Icc (0:ℝ) T,
        ContinuousOn (fun x => Wz x σ) (Set.Icc (0:ℝ) (0 + Real.log (3 / 2))) := by
      intro σ hσ
      have hc : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) p.1 p.2)
          Work.FTS.EllipticEst.Q0 := continuousOn_mixed_of_four (hc4 σ hσ) (by omega)
      have hexpc : Continuous fun x : ℝ => z * Real.exp x :=
        continuous_const.mul Real.continuous_exp
      have hmap : ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)),
          (z * Real.exp x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        fun x _ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨by positivity, hθ0, hθπ⟩
      have hcomp := hc.comp (hexpc.continuousOn.prodMk continuousOn_const) hmap
      simpa only [hWzdef, Function.comp_def] using hcomp
    have hWh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)),
        |Wz x σ - Wz 0 σ| ≤ (2 * z * Cs) * |x - 0| := by
      intro σ hσ x hx
      have hx' : x ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)) := by simpa only [zero_add] using hx
      have hx0 : 0 ≤ x := hx'.1
      have hexp_le : Real.exp x ≤ 3 / 2 := by
        calc Real.exp x ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr hx'.2
          _ = 3 / 2 := hexp2
      have hexp_ge : 1 ≤ Real.exp x := Real.one_le_exp hx0
      have hmem : z * Real.exp x ∈ Set.Icc (z / 2) (3 * z / 2) :=
        ⟨by nlinarith, by nlinarith⟩
      have h := hSpaceZ σ hσ j i hji (z * Real.exp x) hmem θ hθmem' z hzmem'
      have h2 : |z * Real.exp x - z| ≤ 2 * z * |x| := by
        have h3 : z * Real.exp x - z = z * (Real.exp x - 1) := by ring
        rw [h3, abs_mul, abs_of_pos hz]
        have h4 : |Real.exp x - 1| ≤ 2 * |x| := by
          have hdiff : ∀ y ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)),
              DifferentiableAt ℝ Real.exp y := fun y _ => Real.differentiableAt_exp
          have hbnd : ∀ y ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)),
              ‖deriv Real.exp y‖ ≤ 3 / 2 := by
            intro y hy
            rw [Real.norm_eq_abs, Real.deriv_exp, abs_of_pos (Real.exp_pos y)]
            calc Real.exp y ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr hy.2
              _ = 3 / 2 := hexp2
          have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd
            (convex_Icc (0:ℝ) (Real.log (3 / 2)))
            (show (0:ℝ) ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)) from ⟨le_rfl, hδc.le⟩) hx'
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.exp_zero, sub_zero] at hmvt
          nlinarith [abs_nonneg x]
        nlinarith [abs_nonneg x]
      rw [hWzdef]
      simp only [Real.exp_zero, mul_one]
      calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ|
          ≤ Cs * |z * Real.exp x - z| := h
        _ ≤ Cs * (2 * z * |x|) := mul_le_mul_of_nonneg_left h2 hCsnn
        _ = (2 * z * Cs) * |x - 0| := by rw [sub_zero]; ring
    have hdh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)),
        HasDerivAt (fun x' => Vz x' σ) (Wz x σ) x := by
      intro σ hσ x hx
      have hslice := hasDerivAt_slice_fst_of_contDiffOn (z := z * Real.exp x) (θ := θ)
        Work.FTS.EllipticEst.isOpen_Q0
        (contDiffOn_mixed_of_four (hc4 σ hσ) (by omega : (j - 1) + i ≤ 3))
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨by positivity, hθ0, hθπ⟩)
      have hexpd : HasDerivAt (fun x' : ℝ => z * Real.exp x') (z * Real.exp x) x :=
        (Real.hasDerivAt_exp x).const_mul z
      have hcomp := hslice.comp x hexpd
      have hv : Work.Spaces.pz (Work.Spaces.mixed (j - 1) i (Work.FTS.Galerkin.slice g σ))
            (z * Real.exp x) θ * (z * Real.exp x)
          = Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ := by
        rw [mixed_fst_eq_mul_pz _ hj1]
        ring
      rw [hv] at hcomp
      simpa only [hVzdef, hWzdef, Function.comp_def] using hcomp
    have hLand := tau_lip_sqrt_of_primitive_Icc hT hLandau (V := Vz) (W := Wz)
      (x₀ := 0) (δc := Real.log (3 / 2)) (L := Lτ) (K := 2 * z * Cs)
      hδc hLτnn hKc hVh hch hWh hdh
    have hW0 : ∀ σ : ℝ, Wz 0 σ
        = Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ := by
      intro σ
      rw [hWzdef]
      simp only [Real.exp_zero, mul_one]
    have hcontWz : ContinuousWithinAt (fun σ : ℝ => Wz 0 σ) (Set.Icc (0:ℝ) T) τ := by
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := continuousWithinAt_of_sqrt_bound
        (f := fun σ : ℝ => Wz 0 σ) (T := T) (τ := τ) (K := 2 * Lτ + 2 * z * Cs)
        (δ₀ := (Real.log (3 / 2)) ^ 2) hε (by positivity) (by positivity)
        (fun σ hσ hστ => hLand σ hσ τ hτ hστ)
      refine ⟨min δ ((Real.log (3 / 2)) ^ 2), by positivity, ?_⟩
      intro σ hσ hd
      rw [Real.dist_eq] at hd
      exact hδ σ hσ (lt_of_lt_of_le hd (min_le_left _ _))
    rw [show (fun σ : ℝ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ)
        = fun σ : ℝ => Wz 0 σ from funext (fun σ => (hW0 σ).symm)]
    exact hcontWz

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.VPOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.FinalV2 (gS tauExt Sol DynOK' EllLimOK3)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **The repaired velocity package**: `VelPkgEnd`'s fields with the three former
closed-quantifier clauses taken on `0 < θ < π/2`, and without `axis`. -/
structure VelPkgOpen (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  bnd : ∃ M : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ →
    |Vz7 αG μ G Φ z θ τ| ≤ M ∧ |Vθ7 αG Φ z θ τ| ≤ M * Real.sin (2 * θ) ∧
      |cs7 αG μ G Φ z θ τ| ≤ M
  vz0 : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ → 0 ≤ Vz7 αG μ G Φ z θ τ
  vth_ends : ∀ z τ, 0 < z → 0 ≤ τ → Vθ7 αG Φ z 0 τ = 0 ∧ Vθ7 αG Φ z (π / 2) τ = 0
  c2 : ∀ τ ∈ Icc (0:ℝ) S, ContDiffOn ℝ 2 (Function.uncurry (slice Φ τ)) Work.FTS.EllipticEst.Q0
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Vθ7 αG Φ z θ τ / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Vz7 αG μ G Φ p.1 p.2.1 p.2.2, Vθ7 αG Φ p.1 p.2.1 p.2.2, cs7 αG μ G Φ p.1 p.2.1 p.2.2))
    (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S)
  vanish0 : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ∀ Q ∈ ({(Work.Construction.Rop αG (phiTil αG G Φ τ)), Work.Construction.Vop (phiTil αG G Φ τ),
        fun z θ => Work.Construction.Uop αG (phiTil αG G Φ τ) z θ / Real.sin (2 * θ)} :
          Set (ℝ → ℝ → ℝ)),
      |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dz Q z θ| ≤ M * min z 1 ∧
        |Work.Spaces.Dth Q z θ| ≤ M * min z 1
  vanishK : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    |Work.Construction.FK (slice G τ) z| + |Work.Construction.L12 (slice G τ) z| ≤ M * min z 1

end Work.FTS_RegExport
end
end
