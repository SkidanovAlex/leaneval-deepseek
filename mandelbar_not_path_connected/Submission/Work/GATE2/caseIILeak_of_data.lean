import Mathlib
import Submission.Work.GATE2.caseIILeak_of_arcAngle
import Submission.Work.GATE2.CaseII
import Submission.Work.GATE2.EXL.arc_exists
import Submission.Work.GATE2.EXL.deepLeak_point
import Submission.Work.GATE2.EXL.shrinks_esc
import Submission.Work.GATE2.EXL.LastReal
import Submission.Work.GATE2.EXL.arc_front_data
import Submission.Work.GATE2.EXL.deviation_arc_back
import Submission.Work.GATE2.EXL.deviation_arc_iota
import Submission.Work.GATE2.EXL.green_arc_legs
import Submission.Work.GATE2.EXL.exitLoop_exists
import Submission.Work.GATE2.EXL.exitLoop_exists_iota
import Submission.Work.GATE2.EXL.log_tau_sub_one
import Submission.Work.FSeed.API.mem_Mandelbar
import Submission.Work.GATE2.Dichotomy2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
**SUPERSEDED (`NOTES.md` §20).**  This module's `Work.GATE2.caseIILeak_of_data` carries the
hypothesis `hnθ` (the *universal* "every deep real point of the Ψ-plane has its angle in the
`α₁`-window" statement), which is not derivable from the nest geometry: only the *disjunction*
of `Work.GATE.Nest.ray_angle_of_near_sides` is.  Its replacement, with the angle produced by the
dichotomy `Work.GATE2.exists_alpha1_angle_or_shift` and the nest-shrinking datum derived from the
side memberships, is `Work.GATE2.caseIILeak_of_sides` (`Submission/Work/GATE2/SidesDrive.lean`).
The public lemma `deviation_varphiCrit_rayPt_window` of this module is still used.
-/

open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `α`-deviation of a ray point for the canonical critical Böttcher coordinate**, in the
window `(α - 1/2, α + 1/2]` where the lift of the Böttcher argument is the angle itself.  This is
the closed form `θ - α` of `Work.GATE.Gate.deviation_rayPt`, transferred from the dynamical
Böttcher coordinate `d.φ` to `varphiCrit c` by uniqueness on the critical domain. -/
theorem deviation_varphiCrit_rayPt_window {c : ℂ} {d : Work.EL.RootParabolic c}
    {α θ t : ℝ} (ht : 1 < t) (hlo : α - 1 / 2 < θ) (hhi : θ ≤ α + 1 / 2) :
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.rayPt d.hN θ t) = θ - α := by
  have hM : c ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  have hcritB : Work.ParamRays.IsCritBottcher c d.φ :=
    Work.ParamRays.IsDynBottcher.isCritBottcher d.bottcher
  have hnotK : Work.EL.rayPt d.hN θ t ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN ht
  have hcrit : Work.EL.rayPt d.hN θ t ∈ Work.ParamRays.critDomain c := by
    rw [Work.ParamRays.mem_critDomain,
      (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hM,
      ← Work.Bottcher.CritBasic.green_eq]
    exact Work.PARIMPL.green_pos_of_notMem_K hnotK
  have heq : Work.Bottcher.varphiCrit c (Work.EL.rayPt d.hN θ t) =
      d.φ (Work.EL.rayPt d.hN θ t) :=
    Work.Bottcher.varphiCrit_unique hcritB hcrit
  rw [show Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.rayPt d.hN θ t)
      = Work.GATE.deviation d.φ α (Work.EL.rayPt d.hN θ t) by
    simp only [Work.GATE.deviation, Work.GATE.liftAngle, Work.GATE.bAngle, heq]]
  exact Work.GATE.Gate.deviation_rayPt d.hN ht hlo hhi

/-- **Total invariance of `K c` under the high return map `F c = (T_c)^{10}`.** -/
private theorem mem_K_F_iff (c z : ℂ) :
    Work.EL.F c z ∈ Work.EL.K c ↔ z ∈ Work.EL.K c := by
  rw [Work.EL.F_eq_tantibar]
  exact Work.PARIMPL.mem_K_tantibar_iterate_iff c z 10

/-- If the `F c`-image of `z` lies off `K c`, then so does `z`. -/
private theorem notMem_K_of_F_image {c : ℂ} {z : ℂ} (hz : Work.EL.F c z ∉ Work.EL.K c) :
    z ∉ Work.EL.K c := fun h => hz ((mem_K_F_iff c z).mpr h)

/-- If `z` lies off `K c`, then so does its image under the square root `g = (T_c)^5`. -/
private theorem notMem_K_image_five {c : ℂ} {z : ℂ} (hz : z ∉ Work.EL.K c) :
    ((Tantibar c)^[5]) z ∉ Work.EL.K c :=
  fun h => hz ((Work.PARIMPL.mem_K_tantibar_iterate_iff c z 5).mp h)

theorem caseIILeak_of_data {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    (n : ℕ)
    (hbn0 : 0 ≤ Work.ELNest.bAng n)
    (hnw : Work.EL.alpha1 - Work.ELNest.bAng n < 1 / (32 * 16384))
    (hnθ : ∃ R : ℝ, ∀ x : ℝ, x < -R → ∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
      ∃ t : ℝ, 1 < t ∧ fl.Ψ ((x : ℝ) : ℂ) = Work.EL.rayPt d.hN θ t)
    (hss : ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < r₀ →
        z ∈ fl.Pa ∨ ∃ w : ℂ, w.re < -Lray.R ∧ fl.Ψ w = z) ∧
      ∃ g : ℝ, 0 < g ∧ ∀ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 →
        z ∈ Work.EL.pairSideNear (nest.Q n) → Work.EL.pot d.hN z < g → ‖z - d.z₁‖ < r₀)
    (hleak₀ : ∃ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c)
    (htailP0 : ∃ R : ℝ, ∀ x : ℝ, x < -R → fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (hballQ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball d.z₁ ρ ⊆ Work.EL.pairSideNear (nest.Q n))
    (hpot : ∀ g : ℝ, 0 < g → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Work.EL.pot d.hN (fl.Ψ w) < g)
    (hΨsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → ‖fl.Ψ w - d.z₁‖ < ε)
    (hγim : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0)
    (hs₁ : ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ p ∈ Set.Ioo (0 : ℝ) P₀, ∃ s₁ : ℝ, Lray.τ s₁ = Real.exp p ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -Lray.R) :
    Work.GATE2.CaseIILeak c fl.Ψ := by
  -- ## 0. unpack the data
  obtain ⟨Rc, hRcpos, hcover, g₀, hg₀pos, hsmall⟩ := hss
  obtain ⟨P₀, hP₀pos, hs₁prop⟩ := hs₁
  obtain ⟨Rθ, hRθ⟩ := hnθ
  set G : ℝ := min g₀ P₀ with hGdef
  have hGpos : 0 < G := by rw [hGdef]; exact lt_min hg₀pos hP₀pos
  obtain ⟨Rpot, hpotG⟩ := hpot G hGpos
  set N : ℝ := max Lray.R (max Rθ Rpot) with hNdef
  -- ## 1. the deep real leak point
  obtain ⟨x₀, hx₀lt, hx₀leak, hx₀P0, hx₀Q, hx₀pot⟩ :=
    Work.GATE2.EXL.deepLeak_point (N := N) (g := G) (d := d) fl nest (nest.Q n)
      hleak₀ htailP0 hballQ hΨsmall hGpos ⟨Rpot, hpotG⟩
  have hx₀R : x₀ < -Lray.R := by
    have h : Lray.R ≤ N := by rw [hNdef]; exact le_max_left _ _
    linarith
  have hx₀θ : x₀ < -Rθ := by
    have h : Rθ ≤ N := by
      rw [hNdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  -- ## 2. the ray-point datum at `x₀`
  obtain ⟨θ, hθmem, t, ht, hΨx₀⟩ := hRθ x₀ hx₀θ
  have hθ₀ : θ < Work.EL.alpha1 := hθmem.2
  have hθbn : Work.ELNest.bAng n < θ := hθmem.1
  have hθ₀' : Work.EL.alpha1 - θ < 1 / (32 * 16384) := by linarith [hnw]
  set p : ℝ := Real.log t with hpdef
  have hp : 0 < p := by rw [hpdef]; exact Real.log_pos ht
  have hexpp : Real.exp p = t := by rw [hpdef]; exact Real.exp_log (by linarith)
  have hp1 : (1 : ℝ) < Real.exp p := by rw [hexpp]; exact ht
  have hx₀ray : fl.Ψ ((x₀ : ℝ) : ℂ) = Work.EL.rayPt d.hN θ (Real.exp p) := by
    rw [hexpp]; exact hΨx₀
  have hp_pot : p = Work.EL.pot d.hN (fl.Ψ ((x₀ : ℝ) : ℂ)) := by
    rw [hΨx₀, hpdef, Work.EL.pot_rayPt d.hN ht]
  have hpg : p < G := by rw [hp_pot]; exact hx₀pot
  have hpg₀ : p < g₀ := lt_of_lt_of_le hpg (by rw [hGdef]; exact min_le_left _ _)
  have hpP₀ : p < P₀ := lt_of_lt_of_le hpg (by rw [hGdef]; exact min_le_right _ _)
  -- ## 3. the level `s₁` on the ray lift
  obtain ⟨s₁, hτ, hγreR⟩ := hs₁prop p ⟨hp, hpP₀⟩
  have hγ₁R : (Lray.γ₁ s₁).re < -Lray.R := by
    have h := hγreR 1 ⟨zero_le_one, le_refl 1⟩
    rw [sub_add_cancel] at h
    exact h
  -- ## 4. the lifted equipotential arc
  obtain ⟨A, hA0, hA1, hAreL, hangle⟩ :=
    Work.GATE2.EXL.arc_exists (d := d) fl nest Lray hQa hQb n hθmem hp hx₀R hx₀ray
      hcover hg₀pos hpg₀ hsmall hτ hγ₁R
  have hAre : ∀ r : unitInterval, (A r).re < -(3 / 2 : ℝ) := fun r =>
    lt_of_lt_of_le (hAreL r) (by linarith [hR])
  have hγre : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -(3 / 2 : ℝ) := fun u hu =>
    lt_of_lt_of_le (hγreR u hu) (by linarith [hR])
  have hM : c ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  -- ## 5. the front leg: off `K c`, with `α₁`-deviation `< 1/524288`
  obtain ⟨hKA, hdevA⟩ := Work.GATE2.EXL.arc_front_data (d := d) fl A hangle hp hθ₀ hθ₀'
  -- ## 6. the equivariance `Ψ (A r) = F c (Ψ (A r - 1))`
  have hsh : ∀ r : unitInterval, fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)) := by
    intro r
    have h := fl.Ψ_shift (A r - 1)
    rwa [sub_add_cancel] at h
  -- ## 7. the four legs avoid `K c` (total invariance of `K c` under `(T_c)^5`, `(T_c)^{10}`)
  have hKA1 : ∀ r : unitInterval, fl.Ψ (A r - 1) ∉ Work.EL.K c := by
    intro r
    have h := hKA r
    rw [hsh r] at h
    exact notMem_K_of_F_image h
  have hKA2 : ∀ r : unitInterval, fl.Ψ (star (A r) + 1 / 2) ∉ Work.EL.K c := by
    intro r
    rw [fl.Ψ_anti (A r)]
    exact notMem_K_image_five (hKA r)
  have hKA3 : ∀ r : unitInterval, fl.Ψ (star (A r - 1) + 1 / 2) ∉ Work.EL.K c := by
    intro r
    rw [fl.Ψ_anti (A r - 1)]
    exact notMem_K_image_five (hKA1 r)
  -- ## 8. the phases `hzero`, `hbase`, `hbase1` of the `deviation_shift` machinery
  have hdevFront : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))| <
        1 / 16384 := fun r => lt_trans (hdevA r) (by norm_num)
  have hzero : ∀ r : unitInterval,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r)) = 0 →
        r = 1 := by
    intro r hr
    set θr : ℝ := θ + (r : ℝ) * (Work.EL.alpha1 - θ) with hθrdef
    have hδpos : 0 < Work.EL.alpha1 - θ := by linarith
    have hδlt : Work.EL.alpha1 - θ < 1 / 2 := by
      linarith [hθ₀', (by norm_num : (1 : ℝ) / (32 * 16384) < 1 / 2)]
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.2.1
    have hr1 : (r : ℝ) ≤ 1 := r.2.2
    have hlo : Work.EL.alpha1 - 1 / 2 < θr := by
      rw [hθrdef]; nlinarith [hr0, hδpos, hδlt]
    have hhi : θr ≤ Work.EL.alpha1 + 1 / 2 := by
      rw [hθrdef]; nlinarith [hr1, hδpos]
    have hdev := deviation_varphiCrit_rayPt_window (d := d) (α := Work.EL.alpha1)
      (θ := θr) (t := Real.exp p) hp1 hlo hhi
    have hψ : fl.Ψ (A r) = Work.EL.rayPt d.hN θr (Real.exp p) := by
      rw [hθrdef]; exact hangle r
    rw [hψ, hdev] at hr
    have hfac : θr - Work.EL.alpha1 = ((r : ℝ) - 1) * (Work.EL.alpha1 - θ) := by
      rw [hθrdef]; ring
    rw [hfac] at hr
    have hne : Work.EL.alpha1 - θ ≠ 0 := ne_of_gt hδpos
    have hr1' : (r : ℝ) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hne)
    exact Subtype.ext hr1'
  have hbase1 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1
      (fl.Ψ (A 1)) = 0 := by
    rw [hA1]
    exact Work.GATE2.EXL.deviation_varphiCrit_eq_zero d.hN d.bottcher hM (Lray.img₁ s₁)
  have hbase : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1
      (fl.Ψ (A 1 - 1)) = 0 := by
    have hA1' : A 1 - 1 = Lray.γ₁ (s₁ - 1) := by
      rw [hA1]
      have hper : Lray.γ₁ (s₁ - 1) + 1 = Lray.γ₁ s₁ := by
        have h := Lray.per₁ (s₁ - 1)
        rw [sub_add_cancel] at h
        exact h.symm
      rw [← hper]; ring
    rw [hA1']
    exact Work.GATE2.EXL.deviation_varphiCrit_eq_zero d.hN d.bottcher hM (Lray.img₁ (s₁ - 1))
  -- ## 9. the two `α₁`-legs
  have hback := Work.GATE2.EXL.deviation_arc_back (d := d) fl A hKA hKA1 hdevFront
    hzero hbase hbase1
  have hdevBack : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))| <
        1 / 524288 := by
    intro r
    have h1 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1
        (fl.Ψ (A r - 1)) =
        Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r)) / 1024 := by
      linarith [hback r]
    rw [h1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
    linarith [hdevA r]
  have hdev1 : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))| <
        1 / 16384 := fun r => lt_trans (hdevBack r) (by norm_num)
  -- ## 10. the reflected legs carry the `α₂`-deviation `-32` times the `α₁`-deviation
  obtain ⟨hdev2, hdev3⟩ :=
    Work.GATE2.EXL.deviation_arc_iota (d := d) fl A hKA hKA1 hdevA hdevBack
  -- ## 11. the `γ₂`-leg of the second lift
  have hKγ₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, fl.Ψ (Lray.γ₂ (s₁ - 1 + u)) ∉ Work.EL.K c := by
    intro u hu
    rw [Lray.hΨ₂ (s₁ - 1 + u)]
    exact Work.EL.rayPt_notMem_K d.hN
      (one_lt_pow₀ (Lray.hτ1 (s₁ - 1 + u)) (by norm_num : (32 : ℕ) ≠ 0))
  have hdevγ₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (Lray.γ₂ (s₁ - 1 + u)))| < 1 / 16384 := by
    intro u hu
    rw [Work.GATE2.EXL.deviation_varphiCrit_eq_zero_iota d.hN d.bottcher hM
      (Lray.img₂ (s₁ - 1 + u))]
    norm_num
  -- ## 12. the potentials along the arc and along the two fundamental pieces
  obtain ⟨hgreenA, hgreenA1⟩ := Work.GATE2.EXL.green_arc_legs (d := d) fl A hangle hp
  have hp1024 : (0 : ℝ) < p / 1024 := by positivity
  have hp32 : (0 : ℝ) < p / 32 := by positivity
  have hgreenS : ∀ r : unitInterval,
      Work.Bottcher.green c (fl.Ψ (star (A r) + 1 / 2)) = 32 * p := by
    intro r
    rw [fl.Ψ_anti (A r), Work.GATE2.EXL.green_iterate, hgreenA r]
    norm_num
  have hgreenS1 : ∀ r : unitInterval,
      Work.Bottcher.green c (fl.Ψ (star (A r - 1) + 1 / 2)) = p / 32 := by
    intro r
    rw [fl.Ψ_anti (A r - 1), Work.GATE2.EXL.green_iterate, hgreenA1 r]
    ring
  -- ## 13. the six potential floors
  have hfloor1 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A r₁ - 1)) <
        Work.Bottcher.green c (fl.Ψ (A r₂ - 1)) := by
    intro r₁ r₂
    rw [hgreenA1 r₁, hgreenA1 r₂]
    linarith [hp1024]
  have hfloor2 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A r₁ - 1)) <
        Work.Bottcher.green c (fl.Ψ (A r₂)) := by
    intro r₁ r₂
    rw [hgreenA1 r₁, hgreenA r₂]
    linarith [hp1024]
  have hfloorγ₁ : ∀ (r₁ : unitInterval) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A r₁ - 1)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₁ (s₁ - 1 + u))) := by
    intro r₁ u hu
    rw [hgreenA1 r₁, Work.GATE2.EXL.green_lift Lray (s₁ - 1 + u)]
    have hlog1 : Real.log (Lray.τ (s₁ - 1)) = p / 1024 :=
      Work.GATE2.EXL.log_tau_sub_one Lray hτ
    have hmono : Lray.τ (s₁ - 1) ≤ Lray.τ (s₁ - 1 + u) :=
      Lray.hτmono.monotone (by linarith [hu.1])
    have hle : Real.log (Lray.τ (s₁ - 1)) ≤ Real.log (Lray.τ (s₁ - 1 + u)) :=
      Real.log_le_log (by linarith [Lray.hτ1 (s₁ - 1)]) hmono
    rw [hlog1] at hle
    linarith [hp1024, hle]
  have hfloorι1 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A r₁ - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (A r₂ - 1) + 1 / 2)) := by
    intro r₁ r₂
    rw [hgreenS1 r₁, hgreenS1 r₂]
    linarith [hp32]
  have hfloorι2 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A r₁ - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (A r₂) + 1 / 2)) := by
    intro r₁ r₂
    rw [hgreenS1 r₁, hgreenS r₂]
    linarith [hp32]
  have hfloorγ₂ : ∀ (r₁ : unitInterval) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A r₁ - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₂ (s₁ - 1 + u))) := by
    intro r₁ u hu
    rw [hgreenS1 r₁, Work.GATE2.EXL.green_lift_iota Lray (s₁ - 1 + u)]
    have hlog1 : Real.log (Lray.τ (s₁ - 1)) = p / 1024 :=
      Work.GATE2.EXL.log_tau_sub_one Lray hτ
    have hmono : Lray.τ (s₁ - 1) ≤ Lray.τ (s₁ - 1 + u) :=
      Lray.hτmono.monotone (by linarith [hu.1])
    have hle : Real.log (Lray.τ (s₁ - 1)) ≤ Real.log (Lray.τ (s₁ - 1 + u)) :=
      Real.log_le_log (by linarith [Lray.hτ1 (s₁ - 1)]) hmono
    rw [hlog1] at hle
    have hle' : p / 32 ≤ 32 * Real.log (Lray.τ (s₁ - 1 + u)) := by
      have h32 : p / 32 = 32 * (p / 1024) := by ring
      rw [h32]; linarith [hle]
    linarith [hp32, hle']
  -- ## 14. assemble `CaseIILeak` from the arc data
  exact Work.GATE2.caseIILeak_of_arc (d := d) fl Lray A hA0 hA1 hAre hγim hγre
    hKA hKA1 hKA2 hKA3 hKγ₂ hdevFront hdev1 hdev2 hdev3 hdevγ₂
    hfloor1 hfloor2 hfloorγ₁ hfloorι1 hfloorι2 hfloorγ₂

end Work.GATE2
