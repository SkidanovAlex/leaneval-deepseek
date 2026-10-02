/-
# GATE2 / EXL — the exit loop from an arbitrary compact curve

`Work.GATE2.EXL.exitLoop_exists` produces the exit loop at a leak centre `x₀` from the data of a
*ray piece* `γ₁ '' [s₀−1, s₀]`: the deviation window, the escaping property, the potential floor and
the offset-avoidance are read off the external ray.  The consumers of the dichotomy
(`NOTES_LEAD_mandelbar_gaps3.md` §2.3 (b0)) instead hand in a **general compact curve**
`λ : [0,1] → ℂ` running from `x₀ − 1` to `x₀`, together with the same four pieces of data on it:

* `hre` — the curve lies in `{Re < −1}` (the exit window of UT);
* `hK` — its `Ψ`-image avoids the filled Julia set `K c₀` (so the transit is off `K c₀`);
* `hwin` — the `α`-deviation of the critical Böttcher coordinate is `< 1/16384` along it;
* `hfloor` — the potential floor `(3/4)·G(Ψ(λ 0)) < G(Ψ(λ t))`;
* `hslit` — the offset-avoidance `(W)`: `λ t − λ 0 ∈ Ω₀`.

The construction is *verbatim* the one of `exitLoop_exists`, with the ray `L.γ₁ '' [s₀−1, s₀]`
replaced by `range λ`:

* *per point of the curve* the deviation and the escaping property propagate to a neighbourhood
  (`hpt`, by continuity of `Ψ` and of the deviation at a point of `critDomain c₀`);
* *compactness* of `range λ` turns the pointwise neighbourhoods into a uniform tube radius `rU`
  (`hrU'`) and the pointwise floor into a uniform floor radius `rG` (`hfloor'`, the thickening
  argument of `exitLoop_exists`); the confinement `{Re < −1}` gives a third radius `rM`;
* with `K₀ := curveTube (range λ) r₀` (the closed `r₀`-tube about the curve) and
  `𝒦 := Ψ '' K₀`, the loops are the translates `λ_u t = λ t + (u − x₀)`, `u ∈ closedBall x₀ r₀`:
  `λ_u 0 = u − 1`, `λ_u 1 = u`, and for `r₀` below the three radii every field of
  `Work.GATE2.ExitLoop` follows.
-/
import Mathlib
import Submission.Work.GATE2.EXL.exitLoop_exists
import Submission.Work.GATE2.ExitPathInputs

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

theorem exitLoop_of_curve {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁)
    {α x₀ : ℝ} (lam : C(unitInterval, ℂ))
    (h0 : lam 0 = ((x₀ - 1 : ℝ) : ℂ)) (h1 : lam 1 = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t : unitInterval, (lam t).re < -1)
    (hK : ∀ t : unitInterval, fl.Ψ (lam t) ∉ Work.EL.K c₀)
    (hwin : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t))| < 1 / 16384)
    (hfloor : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (lam 0)) <
        Work.Bottcher.green c₀ (fl.Ψ (lam t)))
    (hslit : ∀ t : unitInterval, lam t - lam 0 ∈ Work.GATE2.slitAt 0) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧ Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v α) := by
  classical
  have hM : c₀ ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  -- ### (0) the curve as a compact set
  set C : Set ℂ := Set.range (fun t : unitInterval => lam t) with hCdef
  have hCmem : ∀ a : ℂ, a ∈ C ↔ ∃ t : unitInterval, lam t = a := by
    intro a; rw [hCdef]; exact Set.mem_range
  have hCcomp : IsCompact C := by
    rw [hCdef, ← Set.image_univ]
    exact isCompact_univ.image lam.continuous
  -- ### (1) a safe neighbourhood of every point of the curve
  have hpt : ∀ t : unitInterval, ∃ dd : ℝ, 0 < dd ∧ ∀ w : ℂ, ‖w - lam t‖ < dd →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)| < (1 / 16384 : ℝ)) := by
    intro t
    have hznotK : fl.Ψ (lam t) ∉ Work.EL.K c₀ := hK t
    have hEsc : Work.ParamRays.Escaping c₀ (fl.Ψ (lam t)) :=
      (Work.ParamRays.greenFun_pos_iff_escaping c₀ _).mp
        (by rw [← Work.Bottcher.CritBasic.green_eq]
            exact Work.PARIMPL.green_pos_of_notMem_K hznotK)
    have hzdom : fl.Ψ (lam t) ∈ Work.ParamRays.critDomain c₀ := by
      rw [Work.ParamRays.critDomain_eq_escapingSet hM, Work.ParamRays.mem_escapingSet]
      exact hEsc
    -- a neighbourhood avoiding `K c₀`
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :
        ∃ δ₁ > 0, Metric.ball (fl.Ψ (lam t)) δ₁ ⊆ (Work.EL.K c₀)ᶜ :=
      Metric.isOpen_iff.mp (Work.ParamRays.isClosed_filledJulia c₀).isOpen_compl _
        hznotK
    -- a neighbourhood in which the deviation moves by less than half of the remaining margin
    have hmarg : 0 < (1 / 16384 : ℝ)
        - |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t))| := by
      linarith [hwin t]
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
      Work.GATE2.deviation_continuousAt (α := α) hzdom
        (lt_trans (hwin t) (by norm_num))
        (((1 / 16384 : ℝ)
          - |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t))|) / 2)
        (by linarith [hmarg])
    -- and the `Ψ`-preimage of that neighbourhood
    obtain ⟨δ₃, hδ₃pos, hδ₃'⟩ :=
      Metric.continuousAt_iff.mp (fl.Ψ_diff.continuous.continuousAt (x := lam t))
        (min δ₁ δ₂) (by positivity)
    have hδ₃ : ∀ w : ℂ, ‖w - lam t‖ < δ₃ → ‖fl.Ψ w - fl.Ψ (lam t)‖ < min δ₁ δ₂ := by
      intro w hw
      have hw' : dist w (lam t) < δ₃ := by rw [dist_eq_norm]; exact hw
      have h := hδ₃' hw'
      rwa [dist_eq_norm] at h
    refine ⟨δ₃, hδ₃pos, fun w hw => ⟨?_, ?_⟩⟩
    · have hmem : fl.Ψ w ∈ Metric.ball (fl.Ψ (lam t)) δ₁ := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le (hδ₃ w hw) (min_le_left _ _)
      exact hδ₁ hmem
    · have h2 := hδ₂ c₀ (by rw [sub_self, norm_zero]; exact hδ₂pos) (fl.Ψ w)
        (lt_of_lt_of_le (hδ₃ w hw) (min_le_right _ _))
      have habs : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)|
          ≤ |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)
              - Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t))|
            + |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t))| := by
        have h := abs_add_le
          (Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)
            - Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t)))
          (Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ (lam t)))
        rwa [sub_add_cancel] at h
      linarith
  -- ### (2) a uniform safe tube about the curve
  have htot : ∀ a : ℂ, ∃ dd : ℝ, a ∈ C → 0 < dd ∧ ∀ w : ℂ, ‖w - a‖ < dd →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)| < (1 / 16384 : ℝ)) := by
    intro a
    by_cases ha : a ∈ C
    · obtain ⟨t, rfl⟩ := (hCmem a).mp ha
      obtain ⟨dd, hdd, hP⟩ := hpt t
      exact ⟨dd, fun _ => ⟨hdd, hP⟩⟩
    · exact ⟨1, fun h => absurd h ha⟩
  let δ : ℂ → ℝ := fun a => Classical.choose (htot a)
  have hδ : ∀ a ∈ C, 0 < δ a ∧ ∀ w : ℂ, ‖w - a‖ < δ a →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)| < (1 / 16384 : ℝ)) :=
    fun a ha => (Classical.choose_spec (htot a)) ha
  have hCU : C ⊆ ⋃ a ∈ C, Metric.ball a (δ a) := by
    intro a ha
    rw [Set.mem_iUnion]
    exact ⟨a, Set.mem_iUnion.mpr ⟨ha, Metric.mem_ball_self (hδ a ha).1⟩⟩
  obtain ⟨rU, hrUpos, hrU⟩ := IsCompact.exists_thickening_subset_open hCcomp
    (isOpen_iUnion fun a => isOpen_iUnion fun _ => Metric.isOpen_ball) hCU
  have hrU' : ∀ w : ℂ, w ∈ Metric.thickening rU C →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)| < (1 / 16384 : ℝ)) := by
    intro w hw
    have hmem := hrU hw
    rw [Set.mem_iUnion] at hmem
    obtain ⟨a, hmem2⟩ := hmem
    rw [Set.mem_iUnion] at hmem2
    obtain ⟨ha, hwab⟩ := hmem2
    rw [Metric.mem_ball, dist_eq_norm] at hwab
    exact (hδ a ha).2 w hwab
  -- ### (3) a uniform potential floor on a thin ribbon about the curve
  have hHcont : Continuous (fun p : unitInterval × ℂ =>
      Work.Bottcher.green c₀ (fl.Ψ (lam p.1 + p.2)) -
        (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (lam 0 + p.2))) := by
    have hgreen : Continuous (Work.Bottcher.green c₀) := Work.Escape.continuous_green_Tantibar c₀
    have h1 : Continuous (fun p : unitInterval × ℂ => fl.Ψ (lam p.1 + p.2)) :=
      fl.Ψ_diff.continuous.comp (by fun_prop)
    have h2 : Continuous (fun p : unitInterval × ℂ => fl.Ψ (lam 0 + p.2)) :=
      fl.Ψ_diff.continuous.comp (by fun_prop)
    exact (hgreen.comp h1).sub (continuous_const.mul (hgreen.comp h2))
  have hsub0 : (Set.univ ×ˢ ({0} : Set ℂ)) ⊆
      (fun p : unitInterval × ℂ =>
        Work.Bottcher.green c₀ (fl.Ψ (lam p.1 + p.2)) -
          (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (lam 0 + p.2))) ⁻¹' Set.Ioi 0 := by
    rintro ⟨t, w⟩ ⟨-, hw⟩
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    simp only [Set.mem_preimage, Set.mem_Ioi, add_zero]
    linarith [hfloor t]
  obtain ⟨rG, hrGpos, hrG⟩ := IsCompact.exists_thickening_subset_open
    (isCompact_univ.prod isCompact_singleton) (isOpen_Ioi.preimage hHcont) hsub0
  have hfloor' : ∀ t : unitInterval, ∀ w : ℂ, ‖w‖ < rG →
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (lam 0 + w)) ≤
        Work.Bottcher.green c₀ (fl.Ψ (lam t + w)) := by
    intro t w hw
    have hmem : (t, w) ∈ Metric.thickening rG (Set.univ ×ˢ ({0} : Set ℂ)) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(t, (0 : ℂ)), ⟨Set.mem_univ _, Set.mem_singleton 0⟩, ?_⟩
      have hdist : dist (t, w) (t, (0 : ℂ)) = ‖w‖ := by
        simp [Prod.dist_eq, dist_eq_norm]
      rw [hdist]; exact hw
    have h := hrG hmem
    simp only [Set.mem_preimage, Set.mem_Ioi] at h
    linarith
  -- ### (4) a uniform left bound on the curve
  obtain ⟨rM, hrMpos, hrM⟩ : ∃ rM > 0, ∀ c ∈ C, c.re < -1 - rM := by
    have hne : C.Nonempty := ⟨lam 0, (hCmem _).mpr ⟨0, rfl⟩⟩
    obtain ⟨c₁, hc₁, hmax⟩ :=
      hCcomp.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨t₁, ht₁⟩ := (hCmem c₁).mp hc₁
    have hlt : c₁.re < -1 := by rw [← ht₁]; exact hre t₁
    refine ⟨(-1 - c₁.re) / 2, by linarith, fun c hc => ?_⟩
    have hle : c.re ≤ c₁.re := hmax hc
    linarith
  -- ### (5) the exit loop
  have hmain : ∀ r₀ : ℝ, 0 < r₀ → r₀ < rU → r₀ < rG → r₀ < rM →
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ 0 α) := by
    intro r₀ hr₀pos hr₀U hr₀G hr₀M
    have hmono : ∀ w ∈ curveTube C r₀,
        fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ w)| < (1 / 16384 : ℝ) := by
      intro w hw
      rw [mem_curveTube] at hw
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      have hthick : c + e ∈ Metric.thickening rU C :=
        Metric.mem_thickening_iff.mpr ⟨c, hc, by
          rw [dist_eq_norm, show (c + e) - c = e by ring]
          exact lt_of_le_of_lt he hr₀U⟩
      exact hrU' (c + e) hthick
    refine ⟨{ 𝒦 := fl.Ψ '' curveTube C r₀
              isCompact := (isCompact_curveTube hCcomp r₀).image fl.Ψ_diff.continuous
              offK := ?_
              win := ?_
              discs := ?_
              K₀ := curveTube C r₀
              isCompact_K₀ := isCompact_curveTube hCcomp r₀
              K₀_re := ?_
              K₀_sub := fun w hw => ⟨w, hw, rfl⟩
              loop := ?_ }⟩
    · rintro z ⟨w, hw, rfl⟩
      exact (hmono w hw).1
    · rintro z ⟨w, hw, rfl⟩
      exact (hmono w hw).2
    · intro u hu
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      constructor
      · refine ⟨u - 1, ?_, rfl⟩
        rw [mem_curveTube]
        exact ⟨lam 0, (hCmem _).mpr ⟨0, rfl⟩, u - (x₀ : ℂ), hu,
          by rw [h0]; push_cast; ring⟩
      · refine ⟨u, ?_, rfl⟩
        rw [mem_curveTube]
        exact ⟨lam 1, (hCmem _).mpr ⟨1, rfl⟩, u - (x₀ : ℂ), hu,
          by rw [h1]; ring⟩
    · intro w hw
      rw [mem_curveTube] at hw
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      have h1 : (c + e).re = c.re + e.re := Complex.add_re c e
      have h2 : e.re ≤ ‖e‖ := Complex.re_le_norm e
      have h3 : c.re < -1 - rM := hrM c hc
      linarith
    · intro u hu
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      refine ⟨⟨fun t : unitInterval => lam t + (u - (x₀ : ℂ)), by fun_prop⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · show lam (0 : unitInterval) + (u - (x₀ : ℂ)) = u - 1
        rw [h0]; push_cast; ring
      · show lam (1 : unitInterval) + (u - (x₀ : ℂ)) = u
        rw [h1]; ring
      · intro t
        rw [mem_curveTube]
        exact ⟨lam t, (hCmem _).mpr ⟨t, rfl⟩, u - (x₀ : ℂ), hu, rfl⟩
      · intro t
        have hsub : u - 1 = lam 0 + (u - (x₀ : ℂ)) := by rw [h0]; push_cast; ring
        rw [hsub]
        exact hfloor' t (u - (x₀ : ℂ)) (lt_of_le_of_lt hu hr₀G)
      · intro t
        show ((0 : ℝ) : ℂ) + (lam t + (u - (x₀ : ℂ)) - (u - 1)) ∈ Work.GATE2.slitAt 0
        have hval : ((0 : ℝ) : ℂ) + (lam t + (u - (x₀ : ℂ)) - (u - 1))
            = lam t - lam 0 := by
          rw [h0]; push_cast; ring
        rw [hval]
        exact hslit t
  refine ⟨min (min rU rG) rM / 2, 0, ?_, ?_⟩
  · have h1 : 0 < min (min rU rG) rM := lt_min (lt_min hrUpos hrGpos) hrMpos
    linarith
  · refine hmain _ ?_ ?_ ?_ ?_
    · have h1 : 0 < min (min rU rG) rM := lt_min (lt_min hrUpos hrGpos) hrMpos
      linarith
    · have h1 : min (min rU rG) rM ≤ min rU rG := min_le_left _ _
      have h2 : min rU rG ≤ rU := min_le_left _ _
      linarith
    · have h1 : min (min rU rG) rM ≤ min rU rG := min_le_left _ _
      have h2 : min rU rG ≤ rG := min_le_right _ _
      linarith
    · have h1 : min (min rU rG) rM ≤ rM := min_le_right _ _
      linarith

end Work.GATE2.EXL
