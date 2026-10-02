/-
# GATE2 — the case-(ii) leak with the two reviewer-flagged hypotheses eliminated

This module replaces the residual hypothesis list of `Work.GATE2.caseIILeak_of_data` by one in
which the two items the reviewer named are *derived*:

* the nest-shrinking datum (whose second conjunct needed `hQy`, the shrinking of the landing
  points `(Q n).y`) is derived from the two side memberships `(Q (n+1)).y ∈ pairSideNear P0` and
  `(Q (n+1)).y ∈ pairSideNear (Q n)` via `Work.GATE2.EXL.Qy_shrinks` +
  `Work.GATE2.EXL.shrinks_esc` (the reviewer's item 1);
* the angle window `hnθ` (the universal "every deep real point of the Ψ-plane has its angle in
  `(βₙ, α₁)`") is replaced by the *dichotomy* `Work.GATE2.EXL.exists_alpha1_angle_or_shift`,
  which produces, for the point actually used, either the `α₁`-window angle directly or the
  `α₁`-window angle of the half-integer shift `x + 1/2` (via the antiholomorphic symmetry
  `Ψ (w̄ + 1/2) = g (Ψ w)` and `T^[5] θ = α₁ - 32 (θ - α₂)` on the `α₂`-window).  This is the
  design's §7 ι-symmetry (the reviewer's item 2).

The level `n` of the case-(ii) construction is no longer a hypothesis: it is *chosen* as
`max (shrinking threshold) (window threshold)`, both derived (`shrinks_esc_of_sides`,
`exists_bAng_lt`).
-/
import Submission.Work.GATE2.caseIILeak_of_data
import Submission.Work.GATE2.EXL.Qy_shrinks
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELAssembly.pot_iterate

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
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- Total invariance of `K c` under the high return map `F c` (a local copy of the private
helper of `caseIILeak_of_data`). -/
private theorem mem_K_F_iff' (c z : ℂ) : Work.EL.F c z ∈ Work.EL.K c ↔ z ∈ Work.EL.K c := by
  rw [Work.EL.F_eq_tantibar]
  exact Work.PARIMPL.mem_K_tantibar_iterate_iff c z 10

/-- If the `F c`-image of `z` lies off `K c`, then so does `z`. -/
private theorem notMem_K_of_F_image {c : ℂ} {z : ℂ} (hz : Work.EL.F c z ∉ Work.EL.K c) :
    z ∉ Work.EL.K c := fun h => hz ((mem_K_F_iff' c z).mpr h)

/-- If `z` lies off `K c`, then so does its image under the square root `g = (T_c)^5`. -/
private theorem notMem_K_image_five {c : ℂ} {z : ℂ} (hz : z ∉ Work.EL.K c) :
    ((Tantibar c)^[5]) z ∉ Work.EL.K c :=
  fun h => hz ((Work.PARIMPL.mem_K_tantibar_iterate_iff c z 5).mp h)

/-- **The `δ`-window of the nest angles.** -/
theorem exists_bAng_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, Work.EL.alpha1 - Work.ELNest.bAng n < δ := by
  have hc : 0 < Work.EL.alpha1 - Work.ELNest.beta0 := by
    norm_num [Work.EL.alpha1, Work.ELNest.beta0]
  have htend : Filter.Tendsto (fun n : ℕ => (1024 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (Work.EL.alpha1 - Work.ELNest.beta0) / δ < (1024 : ℝ) ^ N :=
    (htend.eventually_gt_atTop ((Work.EL.alpha1 - Work.ELNest.beta0) / δ)).exists
  refine ⟨N, fun n hn => ?_⟩
  have hmono : (1024 : ℝ) ^ N ≤ (1024 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hlt : (Work.EL.alpha1 - Work.ELNest.beta0) / δ < (1024 : ℝ) ^ n := lt_of_lt_of_le hN hmono
  have hdeq : Work.EL.alpha1 - Work.ELNest.bAng n
      = (Work.EL.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n := by
    have h1 : Work.ELNest.alpha1 = Work.EL.alpha1 := rfl
    rw [Work.ELNest.bAng, h1]
    field_simp
    ring
  rw [hdeq, div_lt_iff₀ (by positivity : (0 : ℝ) < (1024 : ℝ) ^ n)]
  rw [div_lt_iff₀ hδ] at hlt
  linarith

/-- **The nest shrinking on the escaping side, from the side memberships of the landing points.**
The nest field `Z1Nest.shrinks` controls the points of `K c` in the nest region; the only points
of `K c` on the pair curve `Q n` are the landing point `(Q n).y`, and those are controlled by
`Work.GATE2.EXL.Qy_shrinks` once the *consecutive* landing points lie in the two near sides. -/
theorem shrinks_esc_of_sides {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) (Pa : Set ℂ)
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hPsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ g : ℝ, 0 < g ∧
      ∀ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 → z ∈ Work.EL.pairSideNear (nest.Q n) →
        Work.EL.pot hN z < g → ‖z - z₁‖ < ε := fun ε hε =>
  Work.GATE2.EXL.shrinks_esc hN z₁ Pa nest hQa hQb
    (Work.GATE2.EXL.Qy_shrinks hN z₁ Pa nest hPsides hQsides) ε hε

/-- **The case-(ii) construction from the arc data.**  This is the engine of
`caseIILeak_of_data`: from the lifted equipotential arc of level `exp p` running from the deep
real point `x₀` to `γ₁ s₁`, with the `α₁`-window angle `θ`, it produces the `CaseIILeak`. -/
theorem caseIILeak_of_arcData {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    {Rc : ℝ} (hcover : ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < Rc →
      z ∈ fl.Pa ∨ ∃ w : ℂ, w.re < -Lray.R ∧ fl.Ψ w = z)
    {g : ℝ} (hg : 0 < g) (n : ℕ)
    (hnwin : Work.EL.alpha1 - Work.ELNest.bAng n < 1 / (32 * 16384))
    (hsmall : ∀ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 →
      z ∈ Work.EL.pairSideNear (nest.Q n) → Work.EL.pot d.hN z < g → ‖z - d.z₁‖ < Rc)
    {x₀ θ p s₁ : ℝ} (hθmem : θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1)
    (hp : 0 < p) (hx₀R : x₀ < -Lray.R)
    (hx₀ray : fl.Ψ ((x₀ : ℝ) : ℂ) = Work.EL.rayPt d.hN θ (Real.exp p))
    (hpg : p < g) (hτ : Lray.τ s₁ = Real.exp p)
    (hγreR : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -Lray.R)
    (hγim : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0) :
    Work.GATE2.CaseIILeak c fl.Ψ := by
  have hθ₀ : θ < Work.EL.alpha1 := hθmem.2
  have hθbn : Work.ELNest.bAng n < θ := hθmem.1
  have hp1 : (1 : ℝ) < Real.exp p := by rw [Real.one_lt_exp_iff]; exact hp
  have hM : c ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  obtain ⟨A, hA0, hA1, hAreL, hangle⟩ :=
    Work.GATE2.EXL.arc_exists (d := d) fl nest Lray hQa hQb n hθmem hp hx₀R hx₀ray
      hcover hg hpg hsmall hτ (by simpa using hγreR 1 ⟨zero_le_one, le_refl 1⟩)
  have hAre : ∀ r : unitInterval, (A r).re < -(3 / 2 : ℝ) := fun r =>
    lt_of_lt_of_le (hAreL r) (by linarith [hR])
  have hγre : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -(3 / 2 : ℝ) :=
    fun u hu => lt_of_lt_of_le (hγreR u hu) (by linarith [hR])
  have hθ₀' : Work.EL.alpha1 - θ < 1 / (32 * 16384) := by linarith [hθbn, hnwin]
  obtain ⟨hKA, hdevA⟩ := Work.GATE2.EXL.arc_front_data (d := d) fl A hangle hp hθ₀ hθ₀'
  have hsh : ∀ r : unitInterval, fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)) := by
    intro r
    have h := fl.Ψ_shift (A r - 1)
    rwa [sub_add_cancel] at h
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
  obtain ⟨hdev2, hdev3⟩ :=
    Work.GATE2.EXL.deviation_arc_iota (d := d) fl A hKA hKA1 hdevA hdevBack
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
  exact Work.GATE2.caseIILeak_of_arc (d := d) fl Lray A hA0 hA1 hAre hγim hγre
    hKA hKA1 hKA2 hKA3 hKγ₂ hdevFront hdev1 hdev2 hdev3 hdevγ₂
    hfloor1 hfloor2 hfloorγ₁ hfloorι1 hfloorι2 hfloorγ₂

/-- **`CaseIILeak` with the level, the leak point and the angle all produced internally.**

The hypotheses are: the flower, the nest, the cylinder lift of the two root rays, the angle
identifications `hQa`/`hQb`, the depth `hR`, the two side memberships of the consecutive nest
landing points (`hPsides`, `hQsides`), the angle dichotomy `hangle` (supplied by
`Work.GATE2.EXL.exists_alpha1_angle_or_shift`), and the far-left data `hleak₀`, `htailP0`,
`hpot`, `hΨsmall`, `hγim`, `hs₁` of the equator tail.  No level `n` and no shrinking level `g`
are hypotheses. -/
theorem caseIILeak_of_sides {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    (hPsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n))
    (hangle : ∀ n : ℕ, ∀ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c →
      fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0 →
      fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear (nest.Q (n + 1)) →
      (∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
          ∃ t : ℝ, 1 < t ∧ fl.Ψ ((x : ℝ) : ℂ) = Work.EL.rayPt d.hN θ t) ∨
        (∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
          ∃ t : ℝ, 1 < t ∧ fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) = Work.EL.rayPt d.hN θ t))
    (hleak₀ : ∃ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c)
    (htailP0 : ∃ R : ℝ, ∀ x : ℝ, x < -R → fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (hpot : ∀ g : ℝ, 0 < g → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Work.EL.pot d.hN (fl.Ψ w) < g)
    (hΨsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → ‖fl.Ψ w - d.z₁‖ < ε)
    (hγim : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0)
    (hs₁ : ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ p ∈ Set.Ioo (0 : ℝ) P₀, ∃ s₁ : ℝ, Lray.τ s₁ = Real.exp p ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -Lray.R) :
    Work.GATE2.CaseIILeak c fl.Ψ := by
  obtain ⟨Rc, hRcpos, hcover₀⟩ := fl.cover Lray.R
  obtain ⟨Nshr, hNshr⟩ := shrinks_esc_of_sides d.hN d.z₁ fl.Pa nest hQa hQb hPsides hQsides
    Rc hRcpos
  obtain ⟨Nwin, hNwin⟩ := exists_bAng_lt (1 / (32 * 16384)) (by norm_num)
  set n : ℕ := max Nshr Nwin with hndef
  have hnshr : Nshr ≤ n := le_max_left _ _
  have hnwin : Work.EL.alpha1 - Work.ELNest.bAng n < 1 / (32 * 16384) :=
    hNwin n (le_max_right _ _)
  obtain ⟨g, hgpos, hsmall⟩ := hNshr n hnshr
  have hcover : ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < Rc →
      z ∈ fl.Pa ∨ ∃ w : ℂ, w.re < -Lray.R ∧ fl.Ψ w = z := by
    intro z hz hd
    have h0 : 0 < ‖z - d.z₁‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hz
    exact hcover₀ z h0 hd
  obtain ⟨P₀, hP₀pos, hs₁prop⟩ := hs₁
  set H : ℝ := min g P₀ / 32 with hHdef
  have hHpos : 0 < H := by rw [hHdef]; positivity
  have h32H_le_g : 32 * H ≤ g := by rw [hHdef]; linarith [min_le_left g P₀]
  have h32H_le_P : 32 * H ≤ P₀ := by rw [hHdef]; linarith [min_le_right g P₀]
  obtain ⟨Rpot, hpotH⟩ := hpot H hHpos
  obtain ⟨ρ, hρpos, hballQ⟩ : ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball d.z₁ ρ ⊆ Work.EL.pairSideNear (nest.Q (n + 1)) := by
    have hopen : IsOpen (Work.EL.pairSideNear (nest.Q (n + 1))) :=
      (Work.ELTop.isOpen_pairSide d.hN (nest.Q (n + 1))).2
    exact Metric.isOpen_iff.mp hopen d.z₁ (nest.z1_near_Q (n + 1))
  obtain ⟨x, hxN, hxK, hxP0, hxQ, hxpot⟩ :=
    Work.GATE2.EXL.deepLeak_point (N := Lray.R + 1) (g := H) (d := d) fl nest
      (nest.Q (n + 1)) hleak₀ htailP0 ⟨ρ, hρpos, hballQ⟩ hΨsmall hHpos ⟨Rpot, hpotH⟩
  have hxR : x < -Lray.R := by linarith
  rcases hangle n x hxK hxP0 hxQ with ⟨θ, hθ, t, ht, hray⟩ | ⟨θ, hθ, t, ht, hray⟩
  · have hpotx : Work.EL.pot d.hN (fl.Ψ ((x : ℝ) : ℂ)) = Real.log t := by
      rw [hray, Work.EL.pot_rayPt d.hN ht]
    have hpg : Real.log t < g := by
      rw [← hpotx]; linarith [hxpot, hHpos, h32H_le_g]
    have hp : 0 < Real.log t := Real.log_pos ht
    have hpP : Real.log t < P₀ := by
      rw [← hpotx]; linarith [hxpot, h32H_le_P]
    obtain ⟨s₁, hτ, hγreR⟩ := hs₁prop (Real.log t) ⟨hp, hpP⟩
    have hx₀ray : fl.Ψ ((x : ℝ) : ℂ) = Work.EL.rayPt d.hN θ (Real.exp (Real.log t)) := by
      rw [Real.exp_log (by linarith : (0:ℝ) < t)]; exact hray
    exact caseIILeak_of_arcData fl nest Lray hQa hQb hR hcover hgpos n hnwin hsmall hθ hp
      hxR hx₀ray hpg hτ hγreR hγim
  · have hanti : fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) =
        ((Tantibar c)^[5]) (fl.Ψ ((x : ℝ) : ℂ)) := by
      have h := fl.Ψ_anti ((x : ℝ) : ℂ)
      have hs : star (((x : ℝ) : ℂ)) + 1 / 2 = (((x + 1 / 2 : ℝ)) : ℂ) := by
        simp only [Complex.star_def, Complex.conj_ofReal]
        push_cast; ring
      rwa [hs] at h
    have hpotx : Work.EL.pot d.hN (fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ)) = Real.log t := by
      rw [hray, Work.EL.pot_rayPt d.hN ht]
    have hpot32 : Work.EL.pot d.hN (fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ)) =
        32 * Work.EL.pot d.hN (fl.Ψ ((x : ℝ) : ℂ)) := by
      rw [hanti, Work.ELAssembly.pot_iterate d 5]
      norm_num
    have hpg : Real.log t < g := by
      rw [← hpotx, hpot32]; linarith [hxpot, h32H_le_g]
    have hp : 0 < Real.log t := Real.log_pos ht
    have hpP : Real.log t < P₀ := by
      rw [← hpotx, hpot32]; linarith [hxpot, h32H_le_P]
    have hx₀R : x + 1 / 2 < -Lray.R := by linarith
    obtain ⟨s₁, hτ, hγreR⟩ := hs₁prop (Real.log t) ⟨hp, hpP⟩
    have hx₀ray : fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) =
        Work.EL.rayPt d.hN θ (Real.exp (Real.log t)) := by
      rw [Real.exp_log (by linarith : (0:ℝ) < t)]; exact hray
    exact caseIILeak_of_arcData fl nest Lray hQa hQb hR hcover hgpos n hnwin hsmall hθ hp
      hx₀R hx₀ray hpg hτ hγreR hγim

end Work.GATE2
