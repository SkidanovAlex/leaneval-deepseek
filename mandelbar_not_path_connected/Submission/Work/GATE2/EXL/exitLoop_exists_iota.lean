/-
# GATE2 / EXL — `exitLoop_exists_iota`: the `ι`-ray case of residual 1

The companion of `Work.GATE2.EXL.exitLoop_exists`.  There the real leak point `x₀` lies on the
`α₁`-lift `γ₁`; here it lies on the *second* lift `γ₂ = ι γ₁` (`L.anti`), which maps onto the ray
`R(α₂)` at the level `(τ s)^32` (`L.hΨ₂`).  The construction is verbatim that of the first case,
with the two substitutions

* the deviation of the canonical critical Böttcher coordinate `varphiCrit c₀` on the ray of angle
  `α₂` is `0` (`deviation_varphiCrit_eq_zero_iota`), so a thin ribbon around `γ₂ '' [s₀−1, s₀]` is
  carried into the `1/16384`-window and off `K c₀`;
* the potential along the lift is `G(Ψ (γ₂ s)) = 32 · log (τ s)` (`green_lift_iota`), strictly
  monotone in `s`, which gives the `3/4`-floor with room on a thin ribbon.

Everything else — compactness, the uniform left bound and the offset-avoidance `(W)` — is
independent of the ray.
-/
import Mathlib
import Submission.Work.GATE2.EXL.exitLoop_exists
import Submission.Work.GATE2.Access
import Submission.Work.ELRig.CylLift
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

/-! ## Helper lemmas for the second lift -/

/-- **The Green function along the second ray lift**: `G_{c₀} (Ψ (γ₂ s)) = 32 · log (τ s)`.
Indeed `Ψ (γ₂ s)` is the `R(α₂)`-point of level `(τ s)^32` (`L.hΨ₂`) and the potential of a ray
point of level `t > 1` is `log t` (`Work.EL.pot_rayPt`). -/
theorem green_lift_iota {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    Work.Bottcher.green c (fl.Ψ (L.γ₂ s)) = 32 * Real.log (L.τ s) := by
  rw [green_eq_pot d.hN d.bottcher
        (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha2 (L.img₂ s)),
      L.hΨ₂ s, Work.EL.pot_rayPt d.hN (one_lt_pow₀ (L.hτ1 s) (by norm_num)),
      Real.log_pow]
  norm_num

/-- On a dynamical ray of angle `α₂` the `α₂`-deviation of the canonical critical Böttcher
coordinate `varphiCrit c` is exactly `0` (the `α₂`-analogue of
`Work.GATE2.EXL.deviation_varphiCrit_eq_zero`). -/
theorem deviation_varphiCrit_eq_zero_iota {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hb : Work.ParamRays.IsDynBottcher c φ) (hM : c ∈ Mandelbar)
    {z : ℂ} (hz : z ∈ Work.EL.paramRay hN Work.EL.alpha2) :
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2 z = 0 := by
  have hnotK : z ∉ Work.EL.K c := Work.EL.paramRay_subset_compl hN Work.EL.alpha2 hz
  have hEsc : Work.ParamRays.Escaping c z :=
    (Work.ParamRays.greenFun_pos_iff_escaping c z).mp
      (by rw [← Work.Bottcher.CritBasic.green_eq]
          exact Work.PARIMPL.green_pos_of_notMem_K hnotK)
  have hcrit : z ∈ Work.ParamRays.critDomain c := by
    rw [Work.ParamRays.critDomain_eq_escapingSet hM, Work.ParamRays.mem_escapingSet]
    exact hEsc
  have heq : Work.Bottcher.varphiCrit c z = φ z :=
    Work.Bottcher.varphiCrit_unique (Work.ParamRays.IsDynBottcher.isCritBottcher hb) hcrit
  have hdev0 : Work.GATE.deviation φ Work.EL.alpha2 z = 0 :=
    Work.GATE2.deviation_eq_zero_of_mem_paramRay_alpha2 hN hz
  have hcongr : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2 z
      = Work.GATE.deviation φ Work.EL.alpha2 z := by
    simp only [Work.GATE.deviation, Work.GATE.liftAngle, Work.GATE.bAngle, heq]
  rw [hcongr, hdev0]

/-! ## The main statement -/

theorem exitLoop_exists_iota_slit {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₂ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).re < -1)
    (hslit : ∀ t ∈ Set.Icc (0 : ℝ) 1, ¬ ((L.γ₂ (s₀ - 1 + t)).im = 0 ∧
      (L.γ₂ (s₀ - 1 + t)).re ≤ x₀ - 3 / 2)) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧ Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha2) := by
  classical
  have hM : c₀ ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  -- ### (1) the endpoints of the fundamental piece
  have hx₀ : x₀ < -1 := by
    have h := hre 1 ⟨zero_le_one, le_refl 1⟩
    rw [sub_add_cancel, hγ, Complex.ofReal_re] at h
    exact h
  have hγ0 : L.γ₂ (s₀ - 1) = ((x₀ - 1 : ℝ) : ℂ) := by
    have h := L.per₂ (s₀ - 1)
    rw [sub_add_cancel, hγ] at h
    have h' := eq_sub_iff_add_eq.mpr h.symm
    rw [h']
    push_cast
    ring
  -- ### (2) the curve segment and the pointwise safe neighbourhood
  set C : Set ℂ := L.γ₂ '' Set.Icc (s₀ - 1) s₀ with hCdef
  have hCmem : ∀ a : ℂ, a ∈ C ↔ ∃ s ∈ Set.Icc (s₀ - 1) s₀, L.γ₂ s = a := by
    intro a; rw [hCdef]; exact Set.mem_image ..
  have hCcomp : IsCompact C := hCdef.symm ▸ isCompact_Icc.image L.cont₂
  have hpt : ∀ s ∈ Set.Icc (s₀ - 1) s₀, ∃ dd : ℝ, 0 < dd ∧ ∀ w : ℂ, ‖w - L.γ₂ s‖ < dd →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 (fl.Ψ w)|
          < (1 / 16384 : ℝ)) := by
    intro s hs
    set z : ℂ := fl.Ψ (L.γ₂ s) with hzdef
    have hznotK : z ∉ Work.EL.K c₀ :=
      Work.EL.paramRay_subset_compl d.hN Work.EL.alpha2 (L.img₂ s)
    have hEsc : Work.ParamRays.Escaping c₀ z :=
      (Work.ParamRays.greenFun_pos_iff_escaping c₀ z).mp
        (by rw [← Work.Bottcher.CritBasic.green_eq]
            exact Work.PARIMPL.green_pos_of_notMem_K hznotK)
    have hzdom : z ∈ Work.ParamRays.critDomain c₀ := by
      rw [Work.ParamRays.critDomain_eq_escapingSet hM, Work.ParamRays.mem_escapingSet]
      exact hEsc
    have hzdev : Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 z = 0 :=
      deviation_varphiCrit_eq_zero_iota d.hN d.bottcher hM (L.img₂ s)
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ > 0, Metric.ball z δ₁ ⊆ (Work.EL.K c₀)ᶜ :=
      Metric.isOpen_iff.mp (Work.ParamRays.isClosed_filledJulia c₀).isOpen_compl z hznotK
    have hquarter : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 z|
        < 1 / 4 := by rw [hzdev]; norm_num
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
      Work.GATE2.deviation_continuousAt (α := Work.EL.alpha2) hzdom hquarter (1 / 16384)
        (by norm_num)
    obtain ⟨δ₃, hδ₃pos, hδ₃'⟩ :=
      Metric.continuousAt_iff.mp (fl.Ψ_diff.continuous.continuousAt (x := L.γ₂ s))
        (min δ₁ δ₂) (by positivity)
    have hδ₃ : ∀ w : ℂ, ‖w - L.γ₂ s‖ < δ₃ → ‖fl.Ψ w - z‖ < min δ₁ δ₂ := by
      intro w hw
      have hw' : dist w (L.γ₂ s) < δ₃ := by rw [dist_eq_norm]; exact hw
      have h := hδ₃' hw'
      rw [dist_eq_norm] at h
      exact h
    refine ⟨δ₃, hδ₃pos, fun w hw => ⟨?_, ?_⟩⟩
    · have hmem : fl.Ψ w ∈ Metric.ball z δ₁ := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le (hδ₃ w hw) (min_le_left _ _)
      exact hδ₁ hmem
    · have h := hδ₂ c₀ (by rw [sub_self, norm_zero]; exact hδ₂pos) (fl.Ψ w)
        (lt_of_lt_of_le (hδ₃ w hw) (min_le_right _ _))
      rwa [hzdev, sub_zero] at h
  -- the name-free safe set
  have htot : ∀ a : ℂ, ∃ dd : ℝ, a ∈ C → 0 < dd ∧ ∀ w : ℂ, ‖w - a‖ < dd →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 (fl.Ψ w)|
          < (1 / 16384 : ℝ)) := by
    intro a
    by_cases ha : a ∈ C
    · obtain ⟨s, hs, rfl⟩ := (hCmem a).mp ha
      obtain ⟨dd, hdd, hP⟩ := hpt s hs
      exact ⟨dd, fun _ => ⟨hdd, hP⟩⟩
    · exact ⟨1, fun h => absurd h ha⟩
  let δ : ℂ → ℝ := fun a => Classical.choose (htot a)
  have hδ : ∀ a ∈ C, 0 < δ a ∧ ∀ w : ℂ, ‖w - a‖ < δ a →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 (fl.Ψ w)|
          < (1 / 16384 : ℝ)) :=
    fun a ha => (Classical.choose_spec (htot a)) ha
  have hCU : C ⊆ (⋃ a ∈ C, Metric.ball a (δ a)) := by
    intro a ha
    rw [Set.mem_iUnion]
    exact ⟨a, Set.mem_iUnion.mpr ⟨ha, Metric.mem_ball_self (hδ a ha).1⟩⟩
  obtain ⟨rU, hrUpos, hrU⟩ := IsCompact.exists_thickening_subset_open hCcomp
    (isOpen_iUnion fun a => isOpen_iUnion fun _ => Metric.isOpen_ball) hCU
  have hrU' : ∀ w : ℂ, w ∈ Metric.thickening rU C →
      (fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 (fl.Ψ w)|
          < (1 / 16384 : ℝ)) := by
    intro w hw
    have hmem := hrU hw
    rw [Set.mem_iUnion] at hmem
    obtain ⟨a, hmem2⟩ := hmem
    rw [Set.mem_iUnion] at hmem2
    obtain ⟨ha, hwab⟩ := hmem2
    rw [Metric.mem_ball, dist_eq_norm] at hwab
    exact (hδ a ha).2 w hwab
  -- ### (3) the potential floor on a thin ribbon
  have hgreencont : Continuous (Work.Bottcher.green c₀) :=
    Work.Escape.continuous_green_Tantibar c₀
  have hHcont : Continuous (fun p : ℝ × ℂ =>
      Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + p.1) + p.2)) -
        (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1) + p.2))) := by
    have hγ1 : Continuous (fun p : ℝ × ℂ => L.γ₂ (s₀ - 1 + p.1)) :=
      L.cont₂.comp (continuous_fst.const_add (s₀ - 1))
    have h1 : Continuous (fun p : ℝ × ℂ => fl.Ψ (L.γ₂ (s₀ - 1 + p.1) + p.2)) :=
      fl.Ψ_diff.continuous.comp (hγ1.add continuous_snd)
    have h2 : Continuous (fun p : ℝ × ℂ => fl.Ψ (L.γ₂ (s₀ - 1) + p.2)) :=
      fl.Ψ_diff.continuous.comp ((L.cont₂.comp continuous_const).add continuous_snd)
    exact (hgreencont.comp h1).sub (continuous_const.mul (hgreencont.comp h2))
  have hH0 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + t) + (0 : ℂ))) -
        (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1) + (0 : ℂ))) := by
    intro t ht
    have h1 : Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + t) + (0 : ℂ)))
        = 32 * Real.log (L.τ (s₀ - 1 + t)) := by
      rw [add_zero]; exact green_lift_iota L (s₀ - 1 + t)
    have h2 : Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1) + (0 : ℂ)))
        = 32 * Real.log (L.τ (s₀ - 1)) := by
      rw [add_zero]; exact green_lift_iota L (s₀ - 1)
    rw [h1, h2]
    have hmono : L.τ (s₀ - 1) ≤ L.τ (s₀ - 1 + t) :=
      L.hτmono.monotone (by linarith [ht.1])
    have hpos : 0 < Real.log (L.τ (s₀ - 1)) := Real.log_pos (L.hτ1 (s₀ - 1))
    have hle : Real.log (L.τ (s₀ - 1)) ≤ Real.log (L.τ (s₀ - 1 + t)) :=
      Real.log_le_log (by linarith [L.hτ1 (s₀ - 1)]) hmono
    linarith
  have hsub0 : Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℂ) ⊆
      (fun p : ℝ × ℂ =>
        Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + p.1) + p.2)) -
          (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1) + p.2))) ⁻¹'
        Set.Ioi 0 := by
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    have hw0 : w = 0 := by simpa using hw
    rw [hw0]
    simpa using hH0 t ht
  obtain ⟨rG, hrGpos, hrG⟩ := IsCompact.exists_thickening_subset_open
    (isCompact_Icc.prod isCompact_singleton) (isOpen_Ioi.preimage hHcont) hsub0
  have hfloor : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w : ℂ, ‖w‖ < rG →
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1) + w)) ≤
        Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + t) + w)) := by
    intro t ht w hw
    have hmem : (t, w) ∈ Metric.thickening rG (Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℂ)) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(t, (0 : ℂ)), ⟨ht, Set.mem_singleton 0⟩, ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, max_eq_right dist_nonneg,
        dist_eq_norm, sub_zero]
      exact hw
    have hH0' : 0 < Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + t) + w)) -
        (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1) + w)) := by
      have h := hrG hmem
      simp only [Set.mem_preimage, Set.mem_Ioi] at h
      simpa using h
    linarith
  -- ### (4) a uniform left bound on the curve piece
  obtain ⟨rM, hrMpos, hrM⟩ :
      ∃ rM > 0, ∀ s ∈ Set.Icc (s₀ - 1) s₀, (L.γ₂ s).re < -1 - rM := by
    have hne : (Set.Icc (s₀ - 1) s₀).Nonempty := ⟨s₀, ⟨by linarith, le_refl s₀⟩⟩
    obtain ⟨s₁, hs₁, hmax⟩ := (isCompact_Icc (a := s₀ - 1) (b := s₀)).exists_isMaxOn hne
      ((Complex.continuous_re.comp L.cont₂).continuousOn)
    have hs₁t : s₁ - (s₀ - 1) ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc] at hs₁ ⊢
      exact ⟨by linarith [hs₁.1], by linarith [hs₁.2]⟩
    have hlt : (L.γ₂ s₁).re < -1 := by
      have h := hre (s₁ - (s₀ - 1)) hs₁t
      have he : s₀ - 1 + (s₁ - (s₀ - 1)) = s₁ := by ring
      rwa [he] at h
    refine ⟨(-1 - (L.γ₂ s₁).re) / 2, by linarith, fun s hs => ?_⟩
    have hle : (L.γ₂ s).re ≤ (L.γ₂ s₁).re := hmax hs
    linarith
  -- ### (5) the exit loop
  have hmain : ∀ r₀ : ℝ, 0 < r₀ → r₀ < rU → r₀ < rG → r₀ < rM →
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ 0 Work.EL.alpha2) := by
    intro r₀ hr₀pos hr₀U hr₀G hr₀M
    have hK₀comp : IsCompact (curveTube C r₀) := isCompact_curveTube hCcomp r₀
    have hmono : ∀ w ∈ curveTube C r₀, fl.Ψ w ∉ Work.EL.K c₀ ∧
        |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2 (fl.Ψ w)|
          < (1 / 16384 : ℝ) := by
      intro w hw
      rw [mem_curveTube] at hw
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      have hthick : c + e ∈ Metric.thickening rU C :=
        Metric.mem_thickening_iff.mpr ⟨c, hc, by
          rw [dist_eq_norm, show (c + e) - c = e by ring]
          exact lt_of_le_of_lt he hr₀U⟩
      exact hrU' (c + e) hthick
    refine ⟨{ 𝒦 := fl.Ψ '' curveTube C r₀
              isCompact := hK₀comp.image fl.Ψ_diff.continuous
              offK := ?_
              win := ?_
              discs := ?_
              K₀ := curveTube C r₀
              isCompact_K₀ := hK₀comp
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
        exact ⟨L.γ₂ (s₀ - 1),
          (hCmem _).mpr ⟨s₀ - 1, ⟨le_refl _, by linarith⟩, rfl⟩, u - x₀,
          hu, by rw [hγ0]; push_cast; ring⟩
      · refine ⟨u, ?_, rfl⟩
        rw [mem_curveTube]
        exact ⟨L.γ₂ s₀, (hCmem _).mpr ⟨s₀, ⟨by linarith, le_refl _⟩, rfl⟩, u - x₀,
          hu, by rw [hγ]; ring⟩
    · intro w hw
      rw [mem_curveTube] at hw
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      have hc' : c.re < -1 - rM := by
        obtain ⟨s, hs, rfl⟩ := (hCmem c).mp hc
        exact hrM s hs
      have he' : e.re ≤ r₀ := le_trans (Complex.re_le_norm e) he
      have := Complex.add_re c e
      linarith
    · intro u hu
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      refine ⟨⟨fun t : unitInterval => L.γ₂ (s₀ - 1 + (t : ℝ)) + (u - x₀), ?_⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · exact (L.cont₂.comp (continuous_subtype_val.const_add (s₀ - 1))).add continuous_const
      · show L.γ₂ (s₀ - 1 + (((0 : unitInterval) : ℝ))) + (u - x₀) = u - 1
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, add_zero, hγ0]
        push_cast
        ring
      · show L.γ₂ (s₀ - 1 + (((1 : unitInterval) : ℝ))) + (u - x₀) = u
        rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, show s₀ - 1 + 1 = s₀ from by ring, hγ]
        ring
      · intro t
        rw [mem_curveTube]
        exact ⟨L.γ₂ (s₀ - 1 + (t : ℝ)),
          (hCmem _).mpr ⟨s₀ - 1 + (t : ℝ),
            ⟨by linarith [(t : unitInterval).2.1], by linarith [(t : unitInterval).2.2]⟩, rfl⟩,
          u - x₀, hu, rfl⟩
      · intro t
        show (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u - 1)) ≤
          Work.Bottcher.green c₀ (fl.Ψ (L.γ₂ (s₀ - 1 + (t : ℝ)) + (u - x₀)))
        have hsub : u - 1 = L.γ₂ (s₀ - 1) + (u - x₀) := by rw [hγ0]; push_cast; ring
        rw [hsub]
        exact hfloor (t : ℝ) (t : unitInterval).2 (u - x₀)
          (lt_of_le_of_lt hu hr₀G)
      · intro t
        have ht : ((t : unitInterval) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := (t : unitInterval).2
        show (0 : ℂ) + (L.γ₂ (s₀ - 1 + (t : ℝ)) + (u - x₀) - (u - 1))
          ∈ Work.GATE2.slitAt 0
        rw [Work.GATE2.slitAt]
        intro hcon
        refine hslit ((t : unitInterval) : ℝ) ht ⟨by simpa using hcon.1, ?_⟩
        have h2 := hcon.2
        simp only [zero_add, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.one_re] at h2
        linarith
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

/-- **`exitLoop_exists_iota` with the no-dip hypothesis needed only at the real points.** -/
theorem exitLoop_exists_iota {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₂ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).re < -1)
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).im = 0 →
      x₀ - 3 / 2 < (L.γ₂ (s₀ - 1 + t)).re) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧ Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha2) :=
  exitLoop_exists_iota_slit fl L hγ hre fun t ht h => not_lt.mpr h.2 (hno t ht h.1)

/-- **The original no-overshoot bound** (the `iota` twin of `exitLoop_exists_of_noDip`). -/
theorem exitLoop_exists_iota_of_noDip {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₂ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).re < -1)
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, (x₀ - 1 : ℝ) ≤ (L.γ₂ (s₀ - 1 + t)).re) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧ Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha2) :=
  exitLoop_exists_iota fl L hγ hre fun t ht _ => by linarith [hno t ht]

end Work.GATE2.EXL
