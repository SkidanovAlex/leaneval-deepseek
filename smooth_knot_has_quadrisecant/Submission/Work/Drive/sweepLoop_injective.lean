import Mathlib
import Submission.Work.Drive.chordSweepDefs

/-!
# The chord-sweep loop is a simple closed curve

`Work.Drive.sweepLoop r D s : ℝ → Space` walks once along the retained knot arc `K ∩ [a s, b s]`
(from the `b`-end to the `a`-end) and returns along the straight chord from `K (a s)` to `K (b s)`.
The two pieces share only their two endpoints — no point of the knot lies strictly inside the
chord, because the chord class avoids the trisecant set `O` (`havoid`) — so the loop is a *simple*
closed curve on one period.  That is this file's theorem.

## Note on the binder of `hw` in the requested statement (do not "fix" the text!)

The requested statement writes its width hypothesis as

    (hw : ∀ s ∈ Set.Ioo (0 : ℝ) 1, 0 < Work.Drive.sweepW D s ∧ Work.Drive.sweepW D s < period)

but `Work.Drive.sweepW D : I → ℝ` takes an element of the *unit interval*, while `∀ s ∈ Set.Ioo (0:ℝ) 1`
binds a *real* `s`.  So the sentence as written does not elaborate.  Its intended reading is
nevertheless unambiguous, and it is the hypothesis that rules out the multi-wrapping counterexample
to the sibling pin `sweepCurve_injective`: *the retained arc is a proper sub-arc of the knot*,
`0 < sweepW D s < period` for `0 < s < 1` (which is in fact a consequence of the band data alone,
see `Work.Drive.sweepW_pos_lt`).

Rather than alter the requested text, we keep it **verbatim** and install the canonical *clamping*
coercion `ℝ → I` below (a global instance, so that the sentence also elaborates in any module that
imports this one), so that `sweepW D s` (with `s : ℝ`) is read as `sweepW D ⟨s, _⟩` — the clamping
is the identity on `[0,1]`, hence on the open interval where `hw` is evaluated, so the hypothesis
means exactly what was intended.  `coe_unitClamp_eq` records that unfolding, and the companion
`sweepLoop_injective_natural` below is the same theorem with the natural binder
(`∀ s : I, (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → …`), i.e. the form a consumer should use if it does not
want to handle the coercion.

The mathematical content is entirely independent of that coercion: the core lemma
`sweepLoop_injective_core` does not mention `hw` at all (the width bounds are inputs `hW0`, `hWT`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

/-! ## The clamping coercion `ℝ → I` (so that the requested statement elaborates verbatim) -/

/-- Clamping a real number into the unit interval: the identity on `[0,1]`, `0` below and `1`
above. -/
def unitClamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨min 1 (max 0 x), le_min (by norm_num) (le_max_left (0 : ℝ) x), min_le_left 1 (max 0 x)⟩

/-- The clamping coercion `ℝ → I`, used only to read the hypothesis `hw` of the requested statement
(see the module docstring). -/
instance instCoeRealUnitInterval : Coe ℝ (Set.Icc (0 : ℝ) 1) := ⟨unitClamp⟩

/-- On `[0,1]` the clamping coercion is the identity. -/
lemma coe_unitClamp_eq (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((x : ℝ) : Set.Icc (0 : ℝ) 1) = ⟨x, hx⟩ := by
  apply Subtype.ext
  show min 1 (max 0 x) = x
  rw [max_eq_right hx.1, min_eq_right hx.2]

/-! ## The loop parameter on the fundamental half-open period -/

/-- On the fundamental domain `[0, period)` the loop parameter is `t ↦ t / period`. -/
lemma sweepParam_eq_div {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) period) :
    sweepParam t = t / period := by
  have hT : (0 : ℝ) < period := period_pos
  have hfl : ⌊t / period⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨div_nonneg ht.1 hT.le, (div_lt_one hT).mpr ht.2⟩
  simp only [sweepParam, hfl, Int.cast_zero, sub_zero]

/-- `sweepParam` is injective on the fundamental domain: there it is the profile map
`t ↦ t / period`. -/
lemma sweepParam_injOn_Ico : Set.InjOn sweepParam (Set.Ico (0 : ℝ) period) := by
  intro t₁ ht₁ t₂ ht₂ h
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at h
  have h' : t₁ / period * period = t₂ / period * period := by rw [h]
  rwa [div_mul_cancel₀ t₁ period_ne_zero, div_mul_cancel₀ t₂ period_ne_zero] at h'

/-! ## The two pieces of the loop -/

/-- **The retained arc is injective.**  If `0 < w < period`, the map `ξ ↦ r (ta + ξ w)` is
injective on `[0,1]`: it runs over a sub-arc of one period of the knot. -/
lemma sweepArc_injOn_Icc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (s : Set.Icc (0 : ℝ) 1)
    (hW0 : 0 < sweepW D s) (hWT : sweepW D s < period) :
    Set.InjOn (sweepArc r D s) (Set.Icc (0 : ℝ) 1) := by
  intro ξ₁ hξ₁ ξ₂ hξ₂ h
  have hmem : ∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 →
      D.ta s + ξ * sweepW D s ∈ Set.Ico (D.ta s) (D.ta s + period) := by
    intro ξ hξ
    have hle : ξ * sweepW D s ≤ sweepW D s := by
      simpa using mul_le_mul_of_nonneg_right hξ.2 hW0.le
    have hge : 0 ≤ ξ * sweepW D s := mul_nonneg hξ.1 hW0.le
    exact ⟨by linarith, by linarith⟩
  have hkm : ((D.ta s + ξ₁ * sweepW D s : ℝ) : AddCircle period) =
      ((D.ta s + ξ₂ * sweepW D s : ℝ) : AddCircle period) := by
    apply knotMap_injective hr
    rw [knotMap_coe' hr.periodic, knotMap_coe' hr.periodic]
    simpa only [sweepArc_eq] using h
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem ξ₁ hξ₁) (hmem ξ₂ hξ₂)).mp hkm
  have hmul : ξ₁ * sweepW D s = ξ₂ * sweepW D s := by linarith
  exact mul_right_cancel₀ (ne_of_gt hW0) hmul

/-- **The chord does not collapse.**  At an interior parameter of the band arc the two endpoints of
the chord are distinct points of the knot (`d.offdiag` transported to the lifts). -/
lemma sweepChord_endpoints_ne {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {s : Set.Icc (0 : ℝ) 1} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1) :
    r (D.ta s) ≠ r (D.tb s) := by
  intro h
  have h1 : knotMap r ((D.ta s : ℝ) : AddCircle period) =
      knotMap r ((D.tb s : ℝ) : AddCircle period) := by
    rw [knotMap_coe' hr.periodic, knotMap_coe' hr.periodic]
    exact h
  have h2 : ((D.ta s : ℝ) : AddCircle period) = ((D.tb s : ℝ) : AddCircle period) :=
    knotMap_injective hr h1
  refine d.offdiag s hs0 hs1 ?_
  rw [← D.lift_a s, ← D.lift_b s, h2]

/-- **The chord is injective.**  On `[0,1]` the chord parametrization
`ξ ↦ (1-ξ) • r (ta) + ξ • r (tb)` is injective as soon as its endpoints differ. -/
lemma sweepChord_injOn_Icc (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (s : Set.Icc (0 : ℝ) 1) (hAB : r (D.ta s) ≠ r (D.tb s)) :
    Set.InjOn (sweepChord r D s) (Set.Icc (0 : ℝ) 1) := by
  have hv : r (D.tb s) - r (D.ta s) ≠ 0 := sub_ne_zero.mpr hAB.symm
  have key : ∀ ξ : ℝ, sweepChord r D s ξ = r (D.ta s) + ξ • (r (D.tb s) - r (D.ta s)) := by
    intro ξ
    simp only [sweepChord]
    exact smul_add_smul_eq_add_smul_sub (E := Space) (A := r (D.ta s)) (B := r (D.tb s))
      (s := 1 - ξ) (t := ξ) (by ring)
  intro ξ₁ _ ξ₂ _ h
  rw [key ξ₁, key ξ₂] at h
  exact coeff_eq_of_smul_eq_smul hv (add_left_cancel h)

/-- **The arc and the chord meet only at the endpoints.**  A point of the retained arc never lies
strictly inside the chord: that would exhibit the chord (a class of the band) as a trisecant, i.e.
a point of the trisecant set `O`, contradicting `havoid`. -/
lemma sweepArc_ne_sweepChord {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {s : Set.Icc (0 : ℝ) 1} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1)
    {η ξ : ℝ} (_hη : η ∈ Set.Icc (0 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    sweepArc r D s η ≠ sweepChord r D s ξ := by
  intro h
  have hkey : r (D.ta s + η * sweepW D s) =
      (1 - ξ) • r (D.ta s) + ξ • r (D.tb s) := by
    rw [← sweepArc_eq r D s η, h]
    simp only [sweepChord]
  have hmid : IsMiddleOnChord r (d.a s) (d.b s)
      (((D.ta s + η * sweepW D s : ℝ)) : AddCircle period) := by
    show knotMap r (((D.ta s + η * sweepW D s : ℝ)) : AddCircle period) ∈
      openSegment ℝ (knotMap r (d.a s)) (knotMap r (d.b s))
    rw [knotMap_coe' hr.periodic, ← D.lift_a s, ← D.lift_b s,
      knotMap_coe' hr.periodic, knotMap_coe' hr.periodic, hkey]
    exact ⟨1 - ξ, ξ, sub_pos.mpr hξ.2, hξ.1, by ring, rfl⟩
  exact havoid s hs0 hs1
    ((HasMiddleOnClass_iff r ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩).mpr ⟨_, hmid⟩)

/-! ## The half-period profile

`p ↦ if p ≤ 1/2 then arc (2p) else chord (2 - 2p)` is the loop seen through the parameter
`sweepParam : ℝ → [0,1)`; the loop is the composite of that profile with `sweepParam`. -/

/-- **The half-period profile is injective.**  Each piece is injective on its half, and the two
pieces meet only at the two endpoints `p = 0` and `p = 1/2`. -/
lemma sweepProfile_injOn {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {s : Set.Icc (0 : ℝ) 1} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1)
    (hW0 : 0 < sweepW D s) (hWT : sweepW D s < period) :
    Set.InjOn (fun p : ℝ => if p ≤ 1 / 2 then sweepArc r D s (2 * p)
      else sweepChord r D s (2 - 2 * p)) (Set.Ico (0 : ℝ) 1) := by
  have harc := sweepArc_injOn_Icc hr D s hW0 hWT
  have hAB := sweepChord_endpoints_ne hr D hs0 hs1
  have hchord := sweepChord_injOn_Icc r D s hAB
  intro p₁ hp₁ p₂ hp₂ h
  simp only at h
  by_cases h1 : p₁ ≤ 1 / 2
  · by_cases h2 : p₂ ≤ 1 / 2
    · rw [if_pos h1, if_pos h2] at h
      have hξ := harc ⟨by linarith [hp₁.1], by linarith⟩ ⟨by linarith [hp₂.1], by linarith⟩ h
      linarith
    · rw [if_pos h1, if_neg h2] at h
      exact absurd h (sweepArc_ne_sweepChord hr D havoid hs0 hs1
        ⟨by linarith [hp₁.1], by linarith⟩
        ⟨by linarith [hp₂.2], by linarith [lt_of_not_ge h2]⟩)
  · by_cases h2 : p₂ ≤ 1 / 2
    · rw [if_neg h1, if_pos h2] at h
      exact absurd h.symm (sweepArc_ne_sweepChord hr D havoid hs0 hs1
        ⟨by linarith [hp₂.1], by linarith⟩
        ⟨by linarith [hp₁.2], by linarith [lt_of_not_ge h1]⟩)
    · rw [if_neg h1, if_neg h2] at h
      have hξ := hchord ⟨by linarith [hp₁.2], by linarith [lt_of_not_ge h1]⟩
        ⟨by linarith [hp₂.2], by linarith [lt_of_not_ge h2]⟩ h
      linarith

/-! ## The core injectivity statement -/

/-- **The sweep loop is injective on one period** (core form, with the width bounds as explicit
inputs).  `sweepLoop r D s` is the composite of the half-period profile with `sweepParam`, which is
injective on the fundamental domain `[0, period)`. -/
lemma sweepLoop_injective_core {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {s : Set.Icc (0 : ℝ) 1} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1)
    (hW0 : 0 < sweepW D s) (hWT : sweepW D s < period) :
    Set.InjOn (sweepLoop r D s) (Set.Ico (0 : ℝ) period) := by
  have hprof := sweepProfile_injOn hr D havoid hs0 hs1 hW0 hWT
  intro t₁ ht₁ t₂ ht₂ hEq
  have hp₁ : sweepParam t₁ ∈ Set.Ico (0 : ℝ) 1 := sweepParam_mem t₁
  have hp₂ : sweepParam t₂ ∈ Set.Ico (0 : ℝ) 1 := sweepParam_mem t₂
  have hpar : sweepParam t₁ = sweepParam t₂ := hprof hp₁ hp₂ hEq
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at hpar
  have h3 : t₁ / period * period = t₂ / period * period := by rw [hpar]
  rwa [div_mul_cancel₀ t₁ period_ne_zero, div_mul_cancel₀ t₂ period_ne_zero] at h3

/-! ## The requested theorem, and its natural-binder companion -/

/-- **The same statement as `sweepLoop_injective` with the width hypothesis in the natural binder
form** `∀ s : I, (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → …`.  This is the form to use as a consumer: the
canonical witness of the hypothesis is a direct application, e.g.

    `sweepLoop_injective_natural hr D havoid (sweepW_pos_lt D) hs0 hs1`

(`Work.Drive.sweepW_pos_lt` derives the width bound `0 < tb σ - ta σ < period` from the band-arc
data alone).  Use this instead of `sweepLoop_injective` whenever the clamping coercion of the
module docstring is inconvenient. -/
lemma sweepLoop_injective_natural {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    (hw : ∀ s : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 →
      0 < Work.Drive.sweepW D s ∧
      Work.Drive.sweepW D s < LeanEval.KnotTheory.Quadrisecant.period)
    {s : Set.Icc (0 : ℝ) 1} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1) :
    Set.InjOn (Work.Drive.sweepLoop r D s)
      (Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period) := by
  have hsI : (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne s.2.1 (Ne.symm hs0), lt_of_le_of_ne s.2.2 hs1⟩
  exact sweepLoop_injective_core hr D havoid hs0 hs1 (hw s hsI).1 (hw s hsI).2

theorem sweepLoop_injective {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    (hw : ∀ s ∈ Set.Ioo (0 : ℝ) 1, 0 < Work.Drive.sweepW D s ∧
      Work.Drive.sweepW D s < LeanEval.KnotTheory.Quadrisecant.period)
    {s : Set.Icc (0 : ℝ) 1} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1) :
    Set.InjOn (Work.Drive.sweepLoop r D s)
      (Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period) := by
  have hsI : (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne s.2.1 (Ne.symm hs0), lt_of_le_of_ne s.2.2 hs1⟩
  have hw_s := hw (s : ℝ) hsI
  have hcoe : (((s : ℝ) : Set.Icc (0 : ℝ) 1)) = s :=
    (coe_unitClamp_eq (s : ℝ) ⟨le_of_lt hsI.1, le_of_lt hsI.2⟩).trans (Subtype.ext rfl)
  rw [hcoe] at hw_s
  exact sweepLoop_injective_core hr D havoid hs0 hs1 hw_s.1 hw_s.2

end

end Work.Drive
