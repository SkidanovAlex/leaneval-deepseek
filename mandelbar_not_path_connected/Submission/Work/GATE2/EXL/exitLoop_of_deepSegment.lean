/-
# GATE2 / EXL — the exit loop from the data of a deep real segment

The `ρ`-max construction of `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §4 chooses the leak
centre `y₀` at a near-maximum of `ρ = hExp − Re` over a Stolz sector.  The consumers
(`Work.GATE2.EXL.OfRay`, `Work.GATE2.EXL.At`) instead supply the data on a *segment* of the real
axis: the deviation window, the escaping property and the near-constancy of `ρ` are given for
`x ∈ [y₀ − 2, y₀ + 1]`, a real interval that (for small `r₀ < 1`) contains the projection of the
leak rectangle `Λ = loopRegion y₀ r₀`.

This module turns that one-dimensional data into the two-dimensional fields of `ExitLoop`: the
window and escaping properties propagate to the `r₀`-thickening of the segment by continuity and
compactness, and the near-constancy of `ρ` on the segment gives the potential floor

    (3/4)·G(Ψ(u−1)) ≤ G(Ψ w)

on the rectangle via the identity `hExp w = ρ w + Re w` and `G = 1024^(hExp)`.
-/
import Mathlib
import Submission.Work.GATE2.EXL.Region
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.EXL.Defs
import Submission.Work.GATE2.deviation_continuousAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The numerical input -/

/-- `log (3/4)/log 1024 ≥ −1/28`: the logarithmic slack of the potential floor. -/
theorem log_four_thirds_div_log_1024 :
    (1 / 28 : ℝ) ≤ Real.log (4 / 3) / Real.log 1024 := by
  have h1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have hpos1024 : 0 < Real.log (1024 : ℝ) := Real.log_pos (by norm_num)
  have hlog43 : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    rw [show ((4 / 3 : ℝ))⁻¹ = 3 / 4 by norm_num] at h
    linarith
  have hle7 : Real.log (1024 : ℝ) ≤ 7 := by
    rw [h1024]; linarith [Real.log_two_lt_d9]
  rw [le_div_iff₀ hpos1024]
  have h28 : (1 / 28 : ℝ) * Real.log (1024 : ℝ) ≤ 1 / 4 := by
    calc (1 / 28 : ℝ) * Real.log 1024 ≤ (1 / 28) * 7 := by nlinarith
      _ = 1 / 4 := by norm_num
  linarith

/-! ## The leak rectangle lies in a thickening of the segment -/

/-- The distance of a complex number to its real projection is the absolute value of its
imaginary part. -/
theorem dist_re_eq_abs_im (w : ℂ) : dist w ((w.re : ℝ) : ℂ) = |w.im| := by
  rw [dist_eq_norm]
  have hh : w - ((w.re : ℝ) : ℂ) = (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hh, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **The leak rectangle lies in a thickening of the real segment.**  For `r₀ ≤ 1` and `r₀ < r₁`,
`loopRegion y₀ r₀` is contained in the `r₁`-thickening of `((y₀ − 2)..(y₀ + 1))`. -/
theorem loopRegion_subset_thickening {y₀ r₀ r₁ : ℝ} (hr : r₀ < r₁) (hr1 : r₀ ≤ 1) :
    loopRegion y₀ r₀ ⊆
      Metric.thickening r₁ ((fun x : ℝ => (x : ℂ)) '' Set.Icc (y₀ - 2) (y₀ + 1)) := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := mem_loopRegion.mp hw
  rw [Metric.mem_thickening_iff]
  refine ⟨((w.re : ℝ) : ℂ), ?_, ?_⟩
  · refine (Set.mem_image _ _ _).mpr ⟨w.re, ?_, rfl⟩
    rw [Set.mem_Icc]
    constructor <;> linarith
  · rw [dist_re_eq_abs_im]; linarith

/-! ## `ExitLoop` from the window/floor data of a rectangle, for an arbitrary angle `α` -/

/-- **EXL from the properties of the leak rectangle, at an arbitrary angle `α`** (the
`α`-generalisation of `Work.GATE2.EXL.exitLoop_of_region`, whose conclusion is specialised to
`α₁`).  The only field of `ExitLoop` mentioning `α` is the deviation window. -/
theorem exitLoop_of_region_alpha {c₀ : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (x₀ r₀ v α : ℝ)
    (hre : ∀ w ∈ loopRegion x₀ r₀, w.re < -1)
    (hoffK : ∀ w ∈ loopRegion x₀ r₀, fl.Ψ w ∉ Work.EL.K c₀)
    (hwin : ∀ w ∈ loopRegion x₀ r₀,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)| < (1 / 16384 : ℝ))
    (hgreen : ∀ u ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) r₀, ∀ w ∈ loopRegion x₀ r₀,
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u - 1)) ≤ Work.Bottcher.green c₀ (fl.Ψ w)) :
    Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v α) := by
  refine ⟨{ 𝒦 := fl.Ψ '' (loopRegion x₀ r₀)
            isCompact := (isCompact_loopRegion x₀ r₀).image fl.Ψ_diff.continuous
            offK := ?_
            win := ?_
            discs := ?_
            K₀ := loopRegion x₀ r₀
            isCompact_K₀ := isCompact_loopRegion x₀ r₀
            K₀_re := hre
            K₀_sub := fun w hw => ⟨w, hw, rfl⟩
            loop := ?_ }⟩
  · rintro z ⟨w, hw, rfl⟩
    exact hoffK w hw
  · rintro z ⟨w, hw, rfl⟩
    exact hwin w hw
  · intro u hu
    refine ⟨⟨u - 1 + ((0 : ℝ) : ℂ), loopRegion_mem_of_disc hu ⟨le_refl 0, zero_le_one⟩, ?_⟩,
      ⟨u - 1 + ((1 : ℝ) : ℂ), loopRegion_mem_of_disc hu ⟨zero_le_one, le_refl 1⟩, ?_⟩⟩
    · show fl.Ψ (u - 1 + ((0 : ℝ) : ℂ)) = fl.Ψ (u - 1)
      rw [Complex.ofReal_zero, add_zero]
    · show fl.Ψ (u - 1 + ((1 : ℝ) : ℂ)) = fl.Ψ u
      rw [Complex.ofReal_one, sub_add_cancel]
  · intro u hu
    refine ⟨⟨fun t => u - 1 + ((t : ℝ) : ℂ), by fun_prop⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro t
      exact loopRegion_mem_of_disc hu t.2
    · intro t
      exact hgreen u hu _ (loopRegion_mem_of_disc hu t.2)
    · intro t
      exact linearLoop_slitAt t.2

/-! ## The main statement -/

theorem exitLoop_of_deepSegment {c₀ : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) z₁)
    (hM : c₀ ∈ LeanEval.ComplexAnalysis.Mandelbar)
    {y₀ v α : ℝ} (hdeep : y₀ < -3)
    (hdev : ∀ x ∈ Set.Icc (y₀ - 2) (y₀ + 1),
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ))| < (1 / 65536 : ℝ))
    (hoffK : ∀ x ∈ Set.Icc (y₀ - 2) (y₀ + 1), fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀)
    (hgr : ∀ x ∈ Set.Icc (y₀ - 2) (y₀ + 1), ∀ x' ∈ Set.Icc (y₀ - 2) (y₀ + 1),
      Work.GATE2.EXL.rho fl ((x : ℝ) : ℂ) ≤ Work.GATE2.EXL.rho fl ((x' : ℝ) : ℂ) + (1 / 32 : ℝ)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ y₀ r₀ v α) := by
  classical
  set Sℂ : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc (y₀ - 2) (y₀ + 1) with hSℂdef
  have hSℂmem : ∀ z : ℂ, z ∈ Sℂ ↔
      ∃ x ∈ Set.Icc (y₀ - 2) (y₀ + 1), ((x : ℝ) : ℂ) = z := by
    intro z; rw [hSℂdef]; exact Set.mem_image _ _ _
  have hScomp : IsCompact Sℂ := by
    rw [hSℂdef]
    exact isCompact_Icc.image Complex.continuous_ofReal
  -- #### per-point good neighbourhood
  have htot : ∀ z : ℂ, ∃ d : ℝ, z ∈ Sℂ → 0 < d ∧
      (∀ ζ : ℂ, dist ζ z < d →
        (fl.Ψ ζ ∉ Work.EL.K c₀ ∧
          |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ)| < (1 / 16384 : ℝ)) ∧
        |Work.GATE2.EXL.rho fl ζ - Work.GATE2.EXL.rho fl z| < (1 / 1024 : ℝ)) := by
    intro z
    by_cases hz : z ∈ Sℂ
    · obtain ⟨x, hx, rfl⟩ := (hSℂmem z).mp hz
      -- (a) escaping neighbourhood
      obtain ⟨δa, hδapos, hδa⟩ : ∃ δa > 0, ∀ ζ : ℂ, dist ζ ((x : ℝ) : ℂ) < δa →
          fl.Ψ ζ ∉ Work.EL.K c₀ := by
        have hnhds : fl.Ψ ⁻¹' ((Work.EL.K c₀)ᶜ) ∈ 𝓝 ((x : ℝ) : ℂ) :=
          (fl.Ψ_diff.continuous.continuousAt).preimage_mem_nhds
            ((Work.ParamRays.isClosed_filledJulia c₀).isOpen_compl.mem_nhds (hoffK x hx))
        obtain ⟨δa, hδapos, hball⟩ := Metric.mem_nhds_iff.mp hnhds
        exact ⟨δa, hδapos, fun ζ hζ => hball (Metric.mem_ball.mpr hζ)⟩
      -- (b) deviation neighbourhood
      obtain ⟨δb, hδbpos, hδb⟩ : ∃ δb > 0, ∀ ζ : ℂ, dist ζ ((x : ℝ) : ℂ) < δb →
          |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ) -
            Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ))|
              < (1 / 65536 : ℝ) := by
        have hnotK : fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀ := hoffK x hx
        have hEsc : Work.ParamRays.Escaping c₀ (fl.Ψ ((x : ℝ) : ℂ)) :=
          (Work.ParamRays.greenFun_pos_iff_escaping c₀ _).mp
            (by rw [← Work.Bottcher.CritBasic.green_eq]
                exact Work.PARIMPL.green_pos_of_notMem_K hnotK)
        have hzdom : fl.Ψ ((x : ℝ) : ℂ) ∈ Work.ParamRays.critDomain c₀ := by
          rw [Work.ParamRays.critDomain_eq_escapingSet hM, Work.ParamRays.mem_escapingSet]
          exact hEsc
        have hquarter : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α
            (fl.Ψ ((x : ℝ) : ℂ))| < 1 / 4 := lt_trans (hdev x hx) (by norm_num)
        obtain ⟨ρd, hρdpos, hρd⟩ :=
          Work.GATE2.deviation_continuousAt (α := α) hzdom hquarter (1 / 65536) (by norm_num)
        obtain ⟨δb, hδbpos, hδb'⟩ :=
          Metric.continuousAt_iff.mp (fl.Ψ_diff.continuous.continuousAt (x := ((x : ℝ) : ℂ)))
            ρd hρdpos
        refine ⟨δb, hδbpos, fun ζ hζ => ?_⟩
        have h1 : ‖fl.Ψ ζ - fl.Ψ ((x : ℝ) : ℂ)‖ < ρd := by
          have := hδb' hζ; rwa [dist_eq_norm] at this
        exact hρd c₀ (by rw [sub_self, norm_zero]; exact hρdpos) (fl.Ψ ζ) h1
      -- (c) rho neighbourhood
      obtain ⟨δc, hδcpos, hδc⟩ : ∃ δc > 0, ∀ ζ : ℂ, dist ζ ((x : ℝ) : ℂ) < δc →
          |Work.GATE2.EXL.rho fl ζ - Work.GATE2.EXL.rho fl ((x : ℝ) : ℂ)|
            < (1 / 1024 : ℝ) := by
        have hGcont : Continuous (fun ζ : ℂ => Work.Bottcher.green c₀ (fl.Ψ ζ)) :=
          (Work.Escape.continuous_green_Tantibar c₀).comp fl.Ψ_diff.continuous
        have hpos : 0 < Work.Bottcher.green c₀ (fl.Ψ ((x : ℝ) : ℂ)) :=
          Work.PARIMPL.green_pos_of_notMem_K (hoffK x hx)
        have hlogcont : ContinuousAt
            (fun ζ : ℂ => Real.log (Work.Bottcher.green c₀ (fl.Ψ ζ))) ((x : ℝ) : ℂ) :=
          ContinuousAt.comp (f := fun ζ : ℂ => Work.Bottcher.green c₀ (fl.Ψ ζ))
            (g := Real.log) (Real.continuousAt_log (ne_of_gt hpos)) hGcont.continuousAt
        have hrhocont : ContinuousAt (fun ζ : ℂ => Work.GATE2.EXL.rho fl ζ) ((x : ℝ) : ℂ) := by
          have heq : (fun ζ : ℂ => Work.GATE2.EXL.rho fl ζ) =
              fun ζ : ℂ =>
                Real.log (Work.Bottcher.green c₀ (fl.Ψ ζ)) / Real.log 1024 - ζ.re := by
            funext ζ; simp only [rho_def, hExp_def]
          rw [heq]
          exact (hlogcont.div_const _).sub Complex.continuous_re.continuousAt
        obtain ⟨δc, hδcpos, hδc'⟩ := Metric.continuousAt_iff.mp hrhocont (1 / 1024) (by norm_num)
        refine ⟨δc, hδcpos, fun ζ hζ => ?_⟩
        have hh := hδc' hζ
        rwa [Real.dist_eq] at hh
      refine ⟨min (min δa δb) δc,
        fun _ => ⟨lt_min (lt_min hδapos hδbpos) hδcpos, fun ζ hζ => ⟨?_, ?_⟩⟩⟩
      · refine ⟨hδa ζ ?_, ?_⟩
        · exact lt_of_lt_of_le hζ (le_trans (min_le_left _ _) (min_le_left _ _))
        · have hb : dist ζ ((x : ℝ) : ℂ) < δb :=
            lt_of_lt_of_le hζ (le_trans (min_le_left _ _) (min_le_right _ _))
          have hh : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ)|
              < 1 / 65536 + 1 / 65536 := by
            have hsplit : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ)| ≤
                |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ) -
                  Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ))| +
                |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ))| := by
              have h := abs_add_le
                (Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ) -
                  Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ)))
                (Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ)))
              rwa [sub_add_cancel] at h
            have hb' := hδb ζ hb
            have hx' := hdev x hx
            linarith
          linarith [hh]
      · exact hδc ζ (lt_of_lt_of_le hζ (min_le_right _ _))
    · exact ⟨1, fun h => absurd h hz⟩
  let δ : ℂ → ℝ := fun z => Classical.choose (htot z)
  have hδ : ∀ z ∈ Sℂ, 0 < δ z ∧
      (∀ ζ : ℂ, dist ζ z < δ z →
        (fl.Ψ ζ ∉ Work.EL.K c₀ ∧
          |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ)| < (1 / 16384 : ℝ)) ∧
        |Work.GATE2.EXL.rho fl ζ - Work.GATE2.EXL.rho fl z| < (1 / 1024 : ℝ)) :=
    fun z hz => (Classical.choose_spec (htot z)) hz
  have hcov : Sℂ ⊆ ⋃ z ∈ Sℂ, Metric.ball z (δ z) := by
    intro z hz
    rw [Set.mem_iUnion]
    exact ⟨z, Set.mem_iUnion.mpr ⟨hz, Metric.mem_ball_self (hδ z hz).1⟩⟩
  obtain ⟨r₁, hr₁pos, hr₁⟩ := IsCompact.exists_thickening_subset_open hScomp
    (isOpen_iUnion fun z => isOpen_iUnion fun _ => Metric.isOpen_ball) hcov
  have hpack : ∀ ζ : ℂ, ζ ∈ Metric.thickening r₁ Sℂ → ∃ z ∈ Sℂ,
      (fl.Ψ ζ ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ζ)| < (1 / 16384 : ℝ)) ∧
      |Work.GATE2.EXL.rho fl ζ - Work.GATE2.EXL.rho fl z| < (1 / 1024 : ℝ) := by
    intro ζ hζ
    have hm := hr₁ hζ
    rw [Set.mem_iUnion] at hm
    obtain ⟨z, hm2⟩ := hm
    rw [Set.mem_iUnion] at hm2
    obtain ⟨hzS, hball⟩ := hm2
    rw [Metric.mem_ball] at hball
    exact ⟨z, hzS, (hδ z hzS).2 ζ hball⟩
  have hgr' : ∀ z ∈ Sℂ, ∀ z' ∈ Sℂ,
      Work.GATE2.EXL.rho fl z ≤ Work.GATE2.EXL.rho fl z' + (1 / 32 : ℝ) := by
    intro z hz z' hz'
    obtain ⟨x, hx, rfl⟩ := (hSℂmem z).mp hz
    obtain ⟨x', hx', rfl⟩ := (hSℂmem z').mp hz'
    exact hgr x hx x' hx'
  -- #### the radius
  set r₀ : ℝ := (min (min r₁ 1) (1 / 1024)) / 2 with hr₀def
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; positivity
  have hr₀_lt_r₁ : r₀ < r₁ := by
    rw [hr₀def]
    have h1 : min (min r₁ 1) (1 / 1024) ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr₀_le1 : r₀ ≤ 1 := by
    rw [hr₀def]
    have h1 : min (min r₁ 1) (1 / 1024) ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hr₀_two : 2 * r₀ ≤ 1 / 1024 := by
    rw [hr₀def]
    have h1 : min (min r₁ 1) (1 / 1024) ≤ 1 / 1024 := min_le_right _ _
    linarith
  have hloop_sub : loopRegion y₀ r₀ ⊆ Metric.thickening r₁ Sℂ := by
    rw [hSℂdef]
    exact loopRegion_subset_thickening hr₀_lt_r₁ hr₀_le1
  refine ⟨r₀, hr₀pos, ?_, ?_⟩
  · rw [hr₀def]
    have h1 : min (min r₁ 1) (1 / 1024) ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 : 0 < min (min r₁ 1) (1 / 1024) := lt_min (lt_min hr₁pos one_pos) (by norm_num)
    linarith
  refine exitLoop_of_region_alpha fl y₀ r₀ v α ?_ ?_ ?_ ?_
  · -- confinement
    intro w hw
    obtain ⟨_, h2, _⟩ := mem_loopRegion.mp hw
    linarith
  · -- escaping
    intro w hw
    obtain ⟨z, hzS, hh, -⟩ := hpack w (hloop_sub hw)
    exact hh.1
  · -- window
    intro w hw
    obtain ⟨z, hzS, hh, -⟩ := hpack w (hloop_sub hw)
    exact hh.2
  · -- potential floor
    intro u hu w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have hure : |u.re - y₀| ≤ r₀ := by
      have h := Complex.abs_re_le_norm (u - ((y₀ : ℝ) : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at h
      linarith
    have huim : |u.im| ≤ r₀ := by
      have h := Complex.abs_im_le_norm (u - ((y₀ : ℝ) : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
      linarith
    obtain ⟨hur1, hur2⟩ := abs_le.mp hure
    obtain ⟨hw1, hw2, hw3⟩ := mem_loopRegion.mp hw
    have ha_loop : u - 1 ∈ loopRegion y₀ r₀ := by
      rw [mem_loopRegion]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Complex.sub_re, Complex.one_re]; linarith
      · simp only [Complex.sub_re, Complex.one_re]; linarith
      · simpa using huim
    obtain ⟨za, hzaS, hza_ow, hza_rho⟩ := hpack (u - 1) (hloop_sub ha_loop)
    obtain ⟨zb, hzbS, hzb_ow, hzb_rho⟩ := hpack w (hloop_sub hw)
    have hposa : 0 < Work.Bottcher.green c₀ (fl.Ψ (u - 1)) :=
      Work.PARIMPL.green_pos_of_notMem_K hza_ow.1
    have hposb : 0 < Work.Bottcher.green c₀ (fl.Ψ w) :=
      Work.PARIMPL.green_pos_of_notMem_K hzb_ow.1
    have hre_diff : (w.re - (u - 1).re) ≥ -2 * r₀ := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hrho_diff : Work.GATE2.EXL.rho fl w - Work.GATE2.EXL.rho fl (u - 1)
        ≥ -(1 / 32 : ℝ) - 2 * (1 / 1024) := by
      have a1 := (abs_lt.mp hzb_rho).1
      have a2 := (abs_lt.mp hzb_rho).2
      have b1 := (abs_lt.mp hza_rho).1
      have b2 := (abs_lt.mp hza_rho).2
      have c := hgr' za hzaS zb hzbS
      linarith
    have hExpdiff : hExp fl w - hExp fl (u - 1)
        = (Work.GATE2.EXL.rho fl w - Work.GATE2.EXL.rho fl (u - 1))
          + (w.re - (u - 1).re) := by
      rw [rho_def, rho_def]; ring
    have hbnd : hExp fl w - hExp fl (u - 1) ≥ -(1 / 28 : ℝ) := by
      rw [hExpdiff]
      have hconst : -(1 / 28 : ℝ) ≤ -2 * r₀ - 1 / 32 - 2 * (1 / 1024) := by
        have h := hr₀_two
        have h2 : (35 : ℝ) / 1024 ≤ 1 / 28 := by norm_num
        linarith
      linarith
    have hlog34 : Real.log (3 / 4) = -Real.log (4 / 3) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    have hratio : Real.log (3 / 4) / Real.log 1024 ≤ -(1 / 28 : ℝ) := by
      rw [hlog34, neg_div]
      have := log_four_thirds_div_log_1024
      linarith
    have hL : 0 < Real.log 1024 := log_1024_pos
    have hLm : hExp fl (u - 1) + Real.log (3 / 4) / Real.log 1024 ≤ hExp fl w := by
      linarith
    have hkey : Real.log 1024 * hExp fl (u - 1) + Real.log (3 / 4)
        ≤ Real.log 1024 * hExp fl w := by
      have h := mul_le_mul_of_nonneg_left hLm (le_of_lt hL)
      rwa [mul_add, mul_div_cancel₀ _ log_1024_ne] at h
    have hGb : Work.Bottcher.green c₀ (fl.Ψ w)
        = Real.exp (Real.log 1024 * hExp fl w) := by
      rw [← Real.exp_log hposb]
      congr 1
      simp only [hExp_def]
      rw [mul_div_cancel₀ _ log_1024_ne]
    have hGa : Work.Bottcher.green c₀ (fl.Ψ (u - 1))
        = Real.exp (Real.log 1024 * hExp fl (u - 1)) := by
      rw [← Real.exp_log hposa]
      congr 1
      simp only [hExp_def]
      rw [mul_div_cancel₀ _ log_1024_ne]
    calc (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u - 1))
        = (3 / 4) * Real.exp (Real.log 1024 * hExp fl (u - 1)) := by rw [hGa]
      _ = Real.exp (Real.log 1024 * hExp fl (u - 1)) * (3 / 4) := by ring
      _ = Real.exp (Real.log 1024 * hExp fl (u - 1)) * Real.exp (Real.log (3 / 4)) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 4)]
      _ = Real.exp (Real.log 1024 * hExp fl (u - 1) + Real.log (3 / 4)) := by rw [Real.exp_add]
      _ ≤ Real.exp (Real.log 1024 * hExp fl w) := Real.exp_le_exp.mpr hkey
      _ = Work.Bottcher.green c₀ (fl.Ψ w) := hGb.symm

end Work.GATE2.EXL

