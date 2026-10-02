/-
# GATE2 — residual 1: ACCESS (§2.2 of the design)

The design's §2.2 answers the question *which ray carries the base point of the connecting path*,
and it does so by a dichotomy on the real line of the repelling coordinate `Ψ`:

* **case (i)**: `ℝ ∩ range γ₁ ≠ ∅` — some real number `x₁` lies on the lift of `R(α₁)`, so that
  `Ψ x₁` is a point of the `α₁`-ray (the design's "leak point with angle exactly `α₁`"); the
  base point is a real translate of it, still on `R(α₁)` (`TailId`, the `F`-inverse branch fixing
  `z₁` preserves the `α₁`-tail);
* **case (ii)**: `ℝ` avoids both lifts — the crossing-parity lemma (ELRig §3.2 (c)) puts the deep
  equator tail `Ψ (ℝ_{< -R'})` in the near side `pairSideNear P0` of the `α`-pair.

In both cases the point is *off* the filled Julia set, and `A1`
(`Work.GATE.Nest.nest_angle_design`) then puts its ray angle into one of the two windows; this is
the input `Work.GATE.Nest.base_window_disjunction` converts into the base window of the gate
transport (`Work.GATE.gate_window`).

This module proves all of that, in the two forms the design distinguishes:

* `deviation_eq_zero_of_mem_paramRay_alpha1` — **case (i)**: a point of the ray of angle `α₁` has
  `α₁`-deviation `0`, hence lies in the `α₁`-window; no nest and no `A1` are needed;
* `nest_access_exists` — a point of the nest region off `K` exists (the statement
  `∃ n, z ∈ pairSideNear P0 ∩ pairSideNear (Q n) ∧ z ∉ K c` of the design);
* `basePointWindow_of_nest_mem` — **case (ii)**, the `A1` conversion: a point of the level-`n`
  nest region off `K` (with `n` past the `δ`-threshold of the certificate) has its Böttcher
  deviation in one of the two windows;
* `access_of_dichotomy` — the two cases assembled.

The *level* membership of the deep tail in the nest region — the reduction of case (ii) to
ELRig's `htail` together with the flower's `Ψ_small` and the openness of `pairSideNear (Q n)` —
is `mem_pairSideNear_of_deep`, using the design's fallback "choose `j₀` larger": `j₀` is exactly
the shift that makes the leak level deep enough for both `htail` and `Ψ_small`.
-/
import Submission.Work.GATE2.Defs
import Submission.Work.ELTop.isOpen_pairSide

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## Case (i): a point of the `αᵢ`-ray has deviation `0` -/

/-- **A point of the ray of angle `α₁` lies in the `α₁`-window.**  Its `α₁`-relative Böttcher
deviation is `0` (`deviation_eq_of_mem_paramRay`). -/
theorem deviation_eq_zero_of_mem_paramRay_alpha1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {z : ℂ} (hz : z ∈ Work.EL.paramRay hN Work.EL.alpha1) :
    Work.GATE.deviation φ Work.EL.alpha1 z = 0 := by
  rw [Work.GATE.Nest.deviation_eq_of_mem_paramRay hN (α := Work.EL.alpha1)
    (ϑ := Work.EL.alpha1) (by norm_num) hz]
  ring

/-- The same at `α₂`. -/
theorem deviation_eq_zero_of_mem_paramRay_alpha2 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {z : ℂ} (hz : z ∈ Work.EL.paramRay hN Work.EL.alpha2) :
    Work.GATE.deviation φ Work.EL.alpha2 z = 0 := by
  rw [Work.GATE.Nest.deviation_eq_of_mem_paramRay hN (α := Work.EL.alpha2)
    (ϑ := Work.EL.alpha2) (by norm_num) hz]
  ring

/-- **Case (i) of the design's §2.2, in the form consumed by the gate.**  A point off the filled
Julia set which lies on the ray of angle `α₁` satisfies the base window `BasePointWindow`. -/
theorem basePointWindow_of_mem_paramRay_alpha1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {z : ℂ} (hz : z ∈ Work.EL.paramRay hN Work.EL.alpha1) :
    BasePointWindow φ z :=
  Or.inl (by rw [deviation_eq_zero_of_mem_paramRay_alpha1 hN hz]; simpa using Work.GATE.windowEps_pos)

/-! ## The deep tail of the equator lies in the level-`n` nest region -/

/-- **`pairSideNear (Q n)` contains a ball around the parabolic point** (openness at
`z₁ ∈ pairSideNear (Q n)`). -/
theorem exists_ball_subset_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {Q : Work.EL.CoPair hN} {z₁ : ℂ} (hQ : z₁ ∈ Work.EL.pairSideNear Q) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z₁ ρ ⊆ Work.EL.pairSideNear Q :=
  Metric.isOpen_iff.mp (Work.ELTop.isOpen_pairSide hN Q).2 z₁ hQ

/-- **The deep equator tail lies in every level of the nest.**  If `Ψ` maps the far left half
plane into the ball of radius `ρ` around `z₁`, and that ball is contained in
`pairSideNear (Q n)`, then for every `x` below the (level-`n`) threshold the point `Ψ x` lies in
`pairSideNear (Q n)`.

This is the design's fallback "choose `j₀` larger" in the form of an explicit threshold: the level
`R n` supplied by the flower's `Ψ_small` at the radius `ρ` of the openness ball of `Q n`. -/
theorem mem_pairSideNear_of_deep {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁)
    {Q : Work.EL.CoPair hN} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball z₁ ρ ⊆ Work.EL.pairSideNear Q)
    {R x : ℝ} (hR : ∀ w : ℂ, w.re < -R → ‖fl.Ψ w - z₁‖ < ρ) (hx : x < -R) :
    fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear Q :=
  hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hR _ (by simpa using hx))

/-! ## The nest region off `K` is nonempty (the statement of the design) -/

/-- **A point of the nest region off the filled Julia set exists.**  The design's statement
`∃ n, z ∈ pairSideNear P0 ∩ pairSideNear (Q n) ∧ z ∉ K c` (residual 1, "the base point of the
connecting path lies in the nest region off `K c`").

The point exhibited is the ray point of level `2` at the angle mid-way between the certificate
angle `β₀ = bAng 0` and the root angle `α₁`: `θ = (β₀ + α₁)/2 + 1` lies both in the near arc
`(α₂, α₁ + 1)` of `P0` and in the near arc `(β₀ + 1, β₀' + 1)` of `Q 0`, so it is a ray point of
level `> 1` (hence off `K`) in both near sides (`ELTop.mem_pairSideNear_of_nearArc`).

The angle identifications `(Q n).a = bAng' n`, `(Q n).b = bAng n + 1` are ELNest's `NestData.Qpa`,
`Qpb` (the certificate); they are the same hypotheses as in `Work.GATE.Nest.nest_angle_design`. -/
theorem nest_access_exists {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ : ℂ} {Pa : Set ℂ}
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1) :
    ∃ n : ℕ, ∃ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 ∧
      z ∈ Work.EL.pairSideNear (nest.Q n) ∧ z ∉ Work.EL.K c := by
  -- the angle arithmetic of the certificate
  have hβ₀ : Work.ELNest.bAng 0 < Work.ELNest.alpha1 := (Work.ELNest.bAng_range 0).1.2
  have hβ₀' : Work.ELNest.alpha2 < Work.ELNest.bAng' 0 := (Work.ELNest.bAng_range 0).2.1
  have hβ₀'1 : Work.ELNest.bAng' 0 < 1 := Work.ELNest.bAng'_lt_one 0
  have hβpos : (0 : ℝ) < Work.ELNest.bAng 0 := (Work.ELNest.bAng_range 0).1.1
  have hα12 : Work.EL.alpha1 < Work.EL.alpha2 := by
    rw [show Work.EL.alpha1 = Work.ELNest.alpha1 from rfl,
      show Work.EL.alpha2 = Work.ELNest.alpha2 from rfl]
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hα1eq : Work.EL.alpha1 = Work.ELNest.alpha1 := rfl
  have hα2eq : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl
  set mid : ℝ := (Work.ELNest.bAng 0 + Work.EL.alpha1) / 2 with hmid
  have hmid1 : Work.ELNest.bAng 0 < mid := by rw [hmid]; linarith
  have hmid2 : mid < Work.EL.alpha1 := by rw [hmid]; linarith
  refine ⟨0, Work.EL.rayPt hN (mid + 1) 2, ?_, ?_, Work.EL.rayPt_notMem_K hN (by norm_num)⟩
  · -- the near side of `P0`: the near arc is `(α₂, α₁ + 1)`
    refine Work.ELTop.mem_pairSideNear_of_nearArc hN nest.P0 ?_ ?_ (by norm_num)
    · rw [nest.P0_spec.1, nest.P0_spec.2.1, hα1eq, hα2eq]; exact hα12
    · refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · rw [nest.P0_spec.2.1, hα2eq]
        have hα₂1 : Work.ELNest.alpha2 < 1 := by norm_num [Work.ELNest.alpha2]
        linarith
      · rw [nest.P0_spec.1, hα1eq]; linarith
  · -- the near side of `Q 0`: the near arc is `(β₀ + 1, β₀' + 1)`
    refine Work.ELTop.mem_pairSideNear_of_nearArc hN (nest.Q 0) ?_ ?_ (by norm_num)
    · rw [hQa 0, hQb 0]
      linarith [hβ₀'1, hβpos]
    · refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · rw [hQb 0]; linarith
      · rw [hQa 0]; linarith

/-! ## Case (i) from ELRig's lift curves -/

/-- **Case (i) of §2.2, from ELRig's lift.**  If some *real* number lies on the lift curve `γ₁` of
the ray `R(α₁)` (`ℝ ∩ range γ₁ ≠ ∅`), then the corresponding point `Ψ (γ₁ s)` of the repelling
coordinate is a point of the `α₁`-ray off the filled Julia set.

The deep translate `Ψ (x₁ - j₀)` used by the design is the same statement one step further along
the ray: by `RayCylLift.tailId₁` the preimages of `R(α₁)` in the far-left half plane are exactly
the points of `range γ₁`, and `Ψ` of a real translate is the `F`-image (`Ψ_shift`), so the design's
`b = Ψ (x₁ - j₀)` is a ray point as soon as `x₁ - j₀` lies on `γ₁`. -/
theorem access_of_lift_real {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (h : ∃ t : ℝ, (t : ℂ) ∈ Set.range L.γ₁) :
    ∃ z : ℂ, z ∉ Work.EL.K c ∧ z ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
  obtain ⟨t, ⟨s, hs⟩⟩ := h
  refine ⟨fl.Ψ (L.γ₁ s), ?_, L.img₁ s⟩
  exact Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1 (L.img₁ s)


/-! ## The `A1` conversion: nest region off `K` ⟹ base window -/

/-- **The base window from `A1`, at a prescribed level of the nest.**  A point off the filled
Julia set which lies in the near side of the `α`-pair and in the near side of the level-`n` pair of
the nest (`n` large enough for the certificate windows, `hn1`/`hn2`) has its Böttcher deviation in
one of the two windows.

This is the *content* of residual 1: `A1`
(`Work.GATE.Nest.nest_angle_design`/`nest_angle_z1`) supplies the ray angle of the point, and
`Work.GATE.Nest.base_window_disjunction` converts the ray into the deviation of the gate
transports' `BaseWindow`. -/
theorem basePointWindow_of_nest_mem {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ : ℂ}
    {Pa : Set ℂ} (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    {n : ℕ}
    (hn1 : (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n < Work.Final.windowEps)
    (hn2 : (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n < Work.Final.windowEps)
    {z : ℂ} (hzK : z ∉ Work.EL.K c)
    (hzP : z ∈ Work.EL.pairSideNear nest.P0)
    (hzQ : z ∈ Work.EL.pairSideNear (nest.Q n)) :
    BasePointWindow φ z := by
  obtain ⟨ϑ, hz, hwin⟩ :=
    Work.GATE.Nest.nest_angle_z1 hN nest.P0 (nest.Q n) n Work.GATE.windowEps_pos
      nest.P0_spec.1 nest.P0_spec.2.1 (hQa n) (hQb n) nest.sides_P0 (nest.sides_Q n)
      (fun w hw => Work.GATE.Nest.mem_paramRay_of_notMem_K hN hw) hzK hzP hzQ hn1 hn2
  exact Work.GATE.Nest.base_window_disjunction hN hz hwin

/-! ## The dichotomy of §2.2, assembled -/

/-- **Residual 1, the positive dichotomy of §2.2.**  If either

* (case (i)) some point off `K` lies on the ray of angle `α₁` — the design's "the leak point is
  on the `α₁`-ray" (`ℝ ∩ range γ₁ ≠ ∅` via `TailId`), or
* (case (ii)) some point off `K` lies in the near sides of the `α`-pair and of the level-`n` pair
  of the nest, at a level `n` past the certificate threshold (the design's "the deep equator tail
  lies in the near side"),

then there is a point off `K` whose Böttcher deviation lies in one of the two windows: the base
window of the gate transport. -/
theorem access_of_dichotomy {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ : ℂ} {Pa : Set ℂ}
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (h :
      (∃ z : ℂ, z ∉ Work.EL.K c ∧ z ∈ Work.EL.paramRay hN Work.EL.alpha1) ∨
      (∃ n : ℕ, ∃ z : ℂ,
        (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n < Work.Final.windowEps ∧
        (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n < Work.Final.windowEps ∧
        z ∈ Work.EL.pairSideNear nest.P0 ∧
        z ∈ Work.EL.pairSideNear (nest.Q n) ∧ z ∉ Work.EL.K c)) :
    ∃ z : ℂ, z ∉ Work.EL.K c ∧ BasePointWindow φ z := by
  rcases h with ⟨z, hzK, hz⟩ | ⟨n, z, hn1, hn2, hzP, hzQ, hzK⟩
  · exact ⟨z, hzK, basePointWindow_of_mem_paramRay_alpha1 hN hz⟩
  · exact ⟨z, hzK, basePointWindow_of_nest_mem hN nest hQa hQb hn1 hn2 hzK hzP hzQ⟩

/-! ## Case (ii): the deep equator tail off `K` in the level-`0` nest region -/

/-- **The level-`0` certificate windows.**  The angles `β₀ = bAng 0`, `β₀' = bAng' 0` of the
level-`0` pair of the `z₁`-nest are *already* inside the `windowEps`-windows of the two root
angles (`45/1047552 < 1/2048` and `417/1047552 < 1/2048`).  Hence the `A1` conversion of
`basePointWindow_of_nest_mem` can be used at the *fixed* level `n = 0`, where the nest region
`pairSideNear (Q 0)` has a fixed openness radius at `z₁` — which is what makes case (ii) of the
design's §2.2 an honest statement rather than one with a level-dependent threshold. -/
theorem level_zero_windows :
    (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ 0 < Work.Final.windowEps ∧
      (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ 0 < Work.Final.windowEps := by
  constructor
  · rw [pow_zero, div_one]
    norm_num [Work.ELNest.alpha1, Work.ELNest.beta0, Work.Final.windowEps, Work.Landing.windowEps]
  · rw [pow_zero, div_one]
    norm_num [Work.ELNest.beta0', Work.ELNest.alpha2, Work.Final.windowEps,
      Work.Landing.windowEps]

/-- **Case (ii) of the design's §2.2.**  Let the deep equator tail of the repelling coordinate lie
in the near side of the `α`-pair (ELRig's R-a3, `htail`), and let a point `Ψ x` of that tail be off
the filled Julia set (PARIMPL's leak data) and close enough to `z₁` to lie in the near side of the
level-`0` pair of the nest.  Then `Ψ x` is in the nest region off `K`, and `A1` puts its Böttcher
deviation in one of the two windows: the base window of the gate transport.

The closeness hypothesis is the design's fallback "choose `j₀` larger": `x` is the deep leak level
`x* - j₀`, and for `j₀` large it is below both the level of ELRig's `htail` (`hx2`) and the level
`R` of the flower's `Ψ_small` for the openness radius `ρ` of `pairSideNear (Q 0)` (`hx1`). -/
theorem access_of_leak_deep {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ : ℂ} {Pa : Set ℂ}
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁)
    {ρ R R' x : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball z₁ ρ ⊆ Work.EL.pairSideNear (nest.Q 0))
    (hR : ∀ w : ℂ, w.re < -R → ‖fl.Ψ w - z₁‖ < ρ)
    (hhtail : ∀ y : ℝ, y < -R' → fl.Ψ ((y : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (hxK : fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c)
    (hx1 : x < -R) (hx2 : x < -R') :
    fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0 ∧
      fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear (nest.Q 0) ∧
      fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c ∧ BasePointWindow φ (fl.Ψ ((x : ℝ) : ℂ)) := by
  refine ⟨hhtail x hx2, mem_pairSideNear_of_deep hN fl hρ hball hR hx1, hxK, ?_⟩
  exact basePointWindow_of_nest_mem hN nest hQa hQb level_zero_windows.1 level_zero_windows.2
    hxK (hhtail x hx2) (mem_pairSideNear_of_deep hN fl hρ hball hR hx1)


/-- **The certificate windows persist above the threshold.**  If the window bounds hold at a level
`m` then they hold at every level `n ≥ m` (the differences `α₁ - bAng n`, `bAng' n - α₂` decrease
geometrically in `n`).  This is what makes the interface of `basePointWindow_of_nest_mem` usable:
the caller chooses the level of the nest region and only has to know that it is large enough. -/
theorem nest_window_bounds_mono {m n : ℕ} (hmn : m ≤ n)
    (h : (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ m < Work.Final.windowEps) :
    (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n < Work.Final.windowEps := by
  have hpos : (0 : ℝ) < Work.ELNest.alpha1 - Work.ELNest.beta0 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.beta0]
  have hpow : (0 : ℝ) < (1024 : ℝ) ^ n := pow_pos (by norm_num) n
  have hpowe : (1024 : ℝ) ^ m ≤ (1024 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
  have hw : (0 : ℝ) < Work.Final.windowEps := Work.GATE.windowEps_pos
  rw [div_lt_iff₀ hpow]
  rw [div_lt_iff₀ (pow_pos (by norm_num) m)] at h
  nlinarith [mul_le_mul_of_nonneg_left hpowe (le_of_lt hw)]

/-- **The second certificate window persists above the threshold.** -/
theorem nest_window_bounds_mono' {m n : ℕ} (hmn : m ≤ n)
    (h : (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ m < Work.Final.windowEps) :
    (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n < Work.Final.windowEps := by
  have hpos : (0 : ℝ) < Work.ELNest.beta0' - Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.beta0', Work.ELNest.alpha2]
  have hpow : (0 : ℝ) < (1024 : ℝ) ^ n := pow_pos (by norm_num) n
  have hpowe : (1024 : ℝ) ^ m ≤ (1024 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
  have hw : (0 : ℝ) < Work.Final.windowEps := Work.GATE.windowEps_pos
  rw [div_lt_iff₀ hpow]
  rw [div_lt_iff₀ (pow_pos (by norm_num) m)] at h
  nlinarith [mul_le_mul_of_nonneg_left hpowe (le_of_lt hw)]


/-- **Residual 1, unconditional (case (ii)).**  The design's §2.2 dichotomy is *discharged* by the
level-`0` certificate: `nest_access_exists` produces a point of the near sides of `P0` and of
`Q 0` off `K c`, and the level-`0` windows `level_zero_windows` (which persist at every level,
`nest_window_bounds_mono`) put it in the second branch of `access_of_dichotomy`.  Hence there is
always a point off `K c` whose Böttcher deviation lies in one of the two windows — no case
assumption. -/
theorem access_positive {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ : ℂ} {Pa : Set ℂ}
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1) :
    ∃ z : ℂ, z ∉ Work.EL.K c ∧ BasePointWindow φ z := by
  obtain ⟨n, z, hzP, hzQ, hzK⟩ := nest_access_exists hN nest hQa hQb
  exact access_of_dichotomy hN nest hQa hQb
    (Or.inr ⟨n, z,
      nest_window_bounds_mono (Nat.zero_le n) level_zero_windows.1,
      nest_window_bounds_mono' (Nat.zero_le n) level_zero_windows.2, hzP, hzQ, hzK⟩)


end Work.GATE2
