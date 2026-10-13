import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.RegPkgGal.R1b.General
import Submission.Work.FTS.RegPkgGal.R1b.C1Facts
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS_RegExport.RXR1.hbase_gS_aux
import Submission.Work.FTS_RegExport.RXR1.ftc_slice
import Submission.Work.FTS_RegExport.RXR1.dz_tau_cont
import Submission.Work.FTS_RegExport.RXR1.oneSided_expansion

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

