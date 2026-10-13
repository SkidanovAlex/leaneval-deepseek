import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RegExportProved
import Submission.Work.FTS_RegExport.RXR5.r5Parts_hVP
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXR7.r7Block_proved
import Submission.Work.FTS_RegExport.RXR1.r1Block_proved
import Submission.Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
import Submission.Work.FTS_RegExport.Supp
import Submission.Work.FTS_RegExport.RX0.forallRegPkgOfParts
import Submission.Work.FTS_RegExport.RXT.weighted_system

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.r1Block

noncomputable section

open scoped Topology Real
open Set Filter

/-- The clock function of the sanitised family — the `m` of `RegExportIface.GalMin'`. -/
abbrev MM (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ :=
  Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g

theorem regExport_hVop {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hclock : (∀ τ : ℝ, 0 ≤ τ →
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ|
          ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α))
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        ≤ 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ) :
    ∀ S > 0, Work.FTS.RegPkgGal.RegPkg' α S
      (Work.FTS.RegPkgGal.Avort (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.Bdyn (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.extG (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) := by
  -- ## the three derived hypotheses of the assembly
  have hμ : Work.FTS.RegExportIface.ClockBd α Φs E g :=
    Work.FTS.RegExportIface.ClockBd.of_clock hclock
  have hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (MM α Φs E g) (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) S := fun S hS =>
    Work.FTS_RegExport.RXVP.velPkg_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVop S hS
  have hSt1 : ∀ S > 0, Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g) :=
    fun S hS => Work.FTS_RegExport.st1Export_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  have H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) := fun S hS =>
    Work.FTS_RegExport.RXR5.r5Parts_hVP (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hSt1 hdat hμ hVP S hS
  -- ## the two blocks
  obtain ⟨a, b, c, Lz7, hR7⟩ := Work.FTS_RegExport.RXR7.r7Block_proved
    (Φs := Φs) (E := E) (g := g) hα hα13 hSol hOK hdat hμ hVP
  have hR1 : ∀ S > 0, Work.FTS.RegExportIface.R1Block α S (Work.FTS_RegExport.RXR5.SG α g) :=
    Work.FTS_RegExport.RXR1.r1Block_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hSol hOK hdat hSt1 H5
  -- ## the assembly: the `GalMin'` bundle for every horizon
  refine Work.FTS_RegExport.RX0.forallRegPkgOfParts (g := Work.FTS_RegExport.RXR5.SG α g)
    (Φ := Work.FTS_RegExport.RXR5.SΨ α Φs E g) (m := MM α Φs E g)
    (Vz := Work.FTS.RegExportIface.edgeExt (Work.FTS.RegExportIface.Vz7
      (Work.FTS.Regularity.pExp α) (MM α Φs E g) (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g)))
    (Vθ := Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g))
    (cs := Work.FTS.RegExportIface.edgeExt (Work.FTS.RegExportIface.cs7
      (Work.FTS.Regularity.pExp α) (MM α Φs E g) (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g)))
    (a := a) (b := b) (c := c) ?_ H5
  intro S hS
  refine ⟨Lz7, ?_⟩
  -- the regularity package of the raw family, read on the quadrant
  have hreg : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.1
  have hC₀nn : (0 : ℝ) ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Real.sqrt_nonneg (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Galerkin.slice g 0))) (hOK.1.Xn_le 0 le_rfl)
  -- ## the `RegPkgMin` of the sanitised family
  have hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SG α g) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- joint `C¹`
      refine hreg.c1.congr ?_
      rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩
      show Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1.le hθ.2.le,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.le]
    · -- `C⁴` in space
      intro τ hτ
      refine (hreg.c4 τ hτ).congr ?_
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      show Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1.le hθ.2.le,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    · -- continuity in fake time
      intro z θ hzθ
      refine (hreg.cont z θ hzθ).congr ?_
      intro τ hτ
      show Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hzθ.1 hzθ.2.1.le hzθ.2.2.le,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    · -- `ℋ⁴`-membership of the slices
      intro τ hτ
      refine Work.Coercivity.HkMem_congr_of_eqOn_Ioi (Work.FTS.Regularity.pExp α) 4
        (u := Work.FTS.Galerkin.slice (Work.FTS.FinalV2.tauExt g) τ) ?_ ?_
      · rw [Work.FTS.FinalV2.slice_tauExt g hτ]
        exact hreg.mem4 τ hτ
      · intro z hz θ hθ
        show Work.FTS.FinalV2.tauExt g z θ τ = Work.FTS_RegExport.RXR5.SG α g z θ τ
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1 hθ.2]
    · -- the `ℋ³`-bound on `∂_τ`
      intro T hT
      obtain ⟨Cd, hCd⟩ := hreg.dbd T hT
      refine ⟨Cd, fun τ hτ hτT => ⟨?_, ?_⟩⟩
      · have hmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 3
            (Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ) := by
          rw [Work.FTS.FinalV2.gdot_tauExt hτ]
          exact (hCd τ hτ hτT).1
        refine Work.Coercivity.HkMem_congr_of_eqOn_Ioi (Work.FTS.Regularity.pExp α) 3 hmem ?_
        intro z hz θ hθ
        show Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ z θ
            = Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ z θ
        simp only [Work.FTS.Galerkin.gdot]
        rw [show (fun s => Work.FTS_RegExport.RXR5.SG α g z θ s)
              = fun s => Work.FTS.FinalV2.tauExt g z θ s from
            funext fun s => Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1 hθ.2]
      · have hnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 3
            (Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ)
            = Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 3
              (Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ) := by
          show Real.sqrt (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 3
              (Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ))
            = Real.sqrt (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 3
              (Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ))
          congr 1
          exact Work.FTS.EllipticEst.HkSq_congr_open (Work.FTS.Regularity.pExp α) 3
            (fun z θ hz hθ hθ2 => by
              show Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ z θ
                  = Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ z θ
              simp only [Work.FTS.Galerkin.gdot]
              rw [show (fun s => Work.FTS_RegExport.RXR5.SG α g z θ s)
                    = fun s => Work.FTS.FinalV2.tauExt g z θ s from
                  funext fun s => Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le])
        rw [hnorm, Work.FTS.FinalV2.gdot_tauExt hτ]
        exact (hCd τ hτ hτT).2
    · -- the angular vanishing
      intro τ hτ z hz
      by_cases hz0 : 0 < z
      · have h0 := hreg.vanish τ hτ z hz0.le
        refine ⟨?_, ?_⟩
        · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz0 (le_refl (0 : ℝ))
              (by linarith [Real.pi_pos]), Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
          exact h0.1
        · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz0 (by linarith [Real.pi_pos])
              (le_refl (Real.pi / 2)), Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
          exact h0.2
      · have hz' : z ≤ 0 := le_of_not_gt hz0
        exact ⟨Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (g := g) hz',
          Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (g := g) hz'⟩
  -- ## the clock fields, for `M = maxMu …`
  have hm : ContinuousOn (MM α Φs E g) (Set.Ioo (-1 : ℝ) (S + 1)) := by
    have hmax : ContinuousOn (fun s : ℝ => max s 0) (Set.Ioo (-1 : ℝ) (S + 1)) :=
      (continuous_id.max continuous_const).continuousOn
    have hcomp := hclock.2.1.comp hmax (fun s _ => le_max_right s 0)
    show ContinuousOn (fun s : ℝ => Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS.Nonlin.PsiCan Φs E g) g (max s 0)) (Set.Ioo (-1 : ℝ) (S + 1))
    exact hcomp
  have hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |MM α Φs E g τ| ≤ 1 / 2 := by
    intro τ hτ
    show |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0)| ≤ 1 / 2
    exact hclock.1 (max τ 0) (le_max_right τ 0)
  have hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |MM α Φs E g τ - MM α Φs E g τ'| ≤ L * |τ - τ'| ^ α := by
    obtain ⟨L, hL0, hL⟩ := hclock.2.2 S hS
    refine ⟨L, hL0, fun τ hτ τ' hτ' => ?_⟩
    have e1 : MM α Φs E g τ = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ := by
      show Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0) = _
      rw [max_eq_left hτ.1]
    have e2 : MM α Φs E g τ' = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ' := by
      show Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ' 0) = _
      rw [max_eq_left hτ'.1]
    simpa only [e1, e2] using hL τ hτ τ' hτ'
  -- ## the interior sup bound `hIS`
  have hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ)
          z θ| ≤ M := by
    obtain ⟨Lm, hLm0, hLm⟩ := Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
      (αG := Work.FTS.Regularity.pExp α) (C₀ := C₀) (g := g)
      (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) hOK.2 S hS
    refine ⟨10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2), ?_, ?_⟩
    · exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) hC₀nn
    · intro τ hτ b a hab z θ hz hθ hθ2
      have hb := (hLm τ hτ τ hτ b a hab z θ hz hθ hθ2).1
      have hEQ : Set.EqOn (Function.uncurry
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
          (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 := by
        rintro ⟨z', θ'⟩ ⟨hz', hθ'0, hθ'1⟩
        show Work.FTS_RegExport.RXR5.SG α g z' θ' τ = g z' θ' τ
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ'0.le hθ'1.le,
          Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      have hcongr : Work.Spaces.mixed b a
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
          = Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ := by
        have h := Work.FTS.RegPkgGal.mixed_congr_of_isOpen (V := Work.FTS.EllipticEst.Q0)
          (isOpen_Ioi.prod isOpen_Ioo) hEQ b a
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ, hθ2⟩)
        simpa only [Function.uncurry] using h
      rw [hcongr]
      exact hb
  -- ## the uniform `ℋ⁴` bound `hHkn`
  have hHkn : ∃ C₀' : ℝ, 0 ≤ C₀' ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) ≤ C₀' := by
    refine ⟨C₀ * (Work.FTS.Regularity.pExp α) ^ 2, hC₀nn, fun τ hτ => ?_⟩
    have h1 : Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ)
        = Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.tauExt g) τ) :=
      Work.FTS.EllipticEst.HkSq_congr_open (Work.FTS.Regularity.pExp α) 4
        (fun z θ hz hθ hθ2 => by
          show Work.FTS_RegExport.RXR5.SG α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ
          exact Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le)
    have h2 : Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.tauExt g) τ
        = Work.FTS.Regularity.gSlice g τ := by
      funext z θ
      exact Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1
    show Real.sqrt (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2
    rw [h1, h2]
    exact hOK.1.Xn_le τ hτ.1
  -- ## the bundle
  exact
    { toR1Block := hR1 S hS
      toR7Block := hR7 S hS
      hα := hα
      hα13 := hα13
      hS := hS
      hmin := hmin
      hm := hm
      hmb := hmb
      hmh := hmh
      hSt1 := hSt1 S hS
      hIS := hIS
      hHkn := hHkn
      hsuppOut := Work.FTS.FinalV2.hsuppOut_gS α S (Work.FTS.FinalV2.tauExt g) }

end

end Work.FTS_RegExport.r1Block
