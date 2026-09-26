/-
# A clash-free port of `sweepFamFarSep`

Verbatim copy of `sweepFamFarSep.lean` with
* the import of `sweepFam_close_chamfer` replaced by `sweepChamferClean` (a renamed copy), and
* every declaration renamed by a prime,

so that the far-separation is available in the import world of `sweepFam_slices_knots` (the
world that also contains `sweepFam_wideEnd_tol`), which the name clash between
`sweepFam_close_chamfer` and `sweepFam_slices_knots` otherwise forbids.
-/
import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.sweepLoopProfile_uniformCont_loop
import Submission.Work.Drive.sweepChamferClean

set_option maxHeartbeats 1000000

/-!
# Far separation of the doubly smoothed chord sweep

For a smooth knot `r`, an `O`-avoiding band arc `d` and a compact window `[a,b] ⊂ (0,1)` of sweep
parameters, the doubly smoothed sweep slices `sweepFam r D lam δ₁ δ₂ σ` are *uniformly separated*
on loop parameters that are far apart in one period: there are `L, ρ > 0` such that for all
`lam, δ₁, δ₂ ∈ (0,L]`, all `σ ∈ [a,b]` and all `t₁, t₂ ∈ [0, period)` with
`η ≤ |t₂ - t₁| ≤ period - η`,

    ρ ≤ ‖sweepFam r D lam δ₁ δ₂ σ t₁ - sweepFam r D lam δ₁ δ₂ σ t₂‖.

This is `sweepFamFarSep'`, the "far" half of the injectivity of a sweep slice (the "near" half is
`Work.Drive.sweepFamLocalInj`).

## The argument

Write `R_σ` for the *raw* chord-sweep loop `sweepLoop r D σ` (the retained arc joined to the chord
with corners), and `Γ_σ` for the chamfered loop `sweepLoopChamfer r D lam σ`.  Three estimates:

1. `rawProfile_farSep'`: `R_σ` is uniformly separated at scale `ρ₀ > 0` over `σ ∈ [a,b]`.  For fixed
   `σ` the loop `R_σ` is injective on one period (`sweepLoop_injective_core`, which uses `havoid`),
   and it depends continuously on `(σ, t)` (the two branches of its profile agree at the junction),
   so the continuous function `(σ,t₁,t₂) ↦ ‖R_σ t₁ - R_σ t₂‖` is positive on the compact set
   `|t₂ - t₁| ∈ [η, period - η]`, hence bounded below by a positive constant.
2. `sweepLoopChamfer_close_raw`: cutting the corners moves the loop by `ε` once `lam` is small.
3. `sweepFam_close_chamfer'`: the double blur is `ε`-close to the chamfered loop once
   `lam, δ₁, δ₂` are small.

The triangle inequality through the raw loop then gives the statement with `ρ = ρ₀/2`.
-/

namespace Work.Drive

section Helpers

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

/-! ## The raw sweep loop as a profile

`sweepLoop r D σ t` sees the loop parameter through the sawtooth `sweepParam`, which is
discontinuous at the multiples of `period`; the loop itself is not, because the two branches of the
profile agree at the junction.  For the compactness argument it is therefore much better to use
the *profile* coordinate `p ∈ [0,1]`, on which everything is continuous. -/

/-- The raw (uncut) sweep profile: the retained arc on `p ≤ 1/2`, the chord back on `p ≥ 1/2`. -/
def rawProfile' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (p : ℝ) : Space :=
  if p ≤ 1 / 2 then sweepArc r D s (2 * p) else sweepChord r D s (2 - 2 * p)

/-- `sweepLoop` is the raw profile composed with the loop parameter `sweepParam`. -/
lemma sweepLoop_eq_rawProfile' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I)
    (t : ℝ) : sweepLoop r D s t = rawProfile' r D s (sweepParam t) := rfl

/-- The two ends of the raw profile carry the same point (the loop is closed). -/
lemma rawProfile_one_eq_zero' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) :
    rawProfile' r D s 1 = rawProfile' r D s 0 := by
  rw [rawProfile', if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2)),
    rawProfile', if_pos (by norm_num : ((0 : ℝ) ≤ 1 / 2))]
  norm_num
  rw [sweepChord_zero, sweepArc_zero]

/-- The separation of the raw profile at the point `(σ,p₁,p₂)` of the compact parameter set:
`‖R_σ p₁ - R_σ p₂‖`.  (Packaging the min-function of the compactness argument as a definition keeps
the elaborator from having to beta-reduce a `fun`-expression at every use.) -/
def rawSep' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (q : I × ℝ × ℝ) : ℝ :=
  ‖rawProfile' r D q.1 q.2.1 - rawProfile' r D q.1 q.2.2‖

/-! ## Continuity of the raw profile -/

lemma continuous_sweepArc_comp' (r : ℝ → Space) (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) : Continuous (fun q : I × ℝ => sweepArc r D q.1 (2 * q.2)) := by
  have h1 : Continuous (fun q : I × ℝ => D.ta q.1) := D.cont_ta.comp continuous_fst
  have h2 : Continuous (fun q : I × ℝ => D.tb q.1) := D.cont_tb.comp continuous_fst
  have h3 : Continuous (fun q : I × ℝ => (2 : ℝ) * q.2) := by fun_prop
  have harg : Continuous (fun q : I × ℝ => D.ta q.1 + (2 * q.2) * (D.tb q.1 - D.ta q.1)) :=
    h1.add (h3.mul (h2.sub h1))
  have hc : Continuous (fun q : I × ℝ => r (D.ta q.1 + (2 * q.2) * (D.tb q.1 - D.ta q.1))) :=
    hr.comp harg
  simpa only [sweepArc, sweepW] using hc

lemma continuous_sweepChord_comp' (r : ℝ → Space) (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) : Continuous (fun q : I × ℝ => sweepChord r D q.1 (2 - 2 * q.2)) := by
  have hta : Continuous (fun q : I × ℝ => r (D.ta q.1)) := hr.comp (D.cont_ta.comp continuous_fst)
  have htb : Continuous (fun q : I × ℝ => r (D.tb q.1)) := hr.comp (D.cont_tb.comp continuous_fst)
  have h4 : Continuous (fun q : I × ℝ => (1 - (2 - 2 * q.2) : ℝ)) := by fun_prop
  have h5 : Continuous (fun q : I × ℝ => ((2 - 2 * q.2 : ℝ))) := by fun_prop
  have hc : Continuous (fun q : I × ℝ =>
      (1 - (2 - 2 * q.2)) • r (D.ta q.1) + (2 - 2 * q.2) • r (D.tb q.1)) :=
    (h4.smul hta).add (h5.smul htb)
  simpa only [sweepChord] using hc

/-- **The raw profile is continuous** in `(σ, p)`: the arc and the chord branches agree at the
junction `p = 1/2` (both give `r (tb σ)`), and away from the junction one branch is locally
constant. -/
lemma continuous_rawProfile' (r : ℝ → Space) (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) : Continuous (fun q : I × ℝ => rawProfile' r D q.1 q.2) := by
  have hF : Continuous (fun q : I × ℝ => sweepArc r D q.1 (2 * q.2)) :=
    continuous_sweepArc_comp' r hr D
  have hG : Continuous (fun q : I × ℝ => sweepChord r D q.1 (2 - 2 * q.2)) :=
    continuous_sweepChord_comp' r hr D
  have hkey : ∀ s : I, sweepArc r D s 1 = sweepChord r D s 1 := by
    intro s; rw [sweepArc_one, sweepChord_one]
  rw [continuous_iff_continuousAt]
  intro q₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δF, hδF0, hδF⟩ := (Metric.continuousAt_iff.mp hF.continuousAt) ε hε
  obtain ⟨δG, hδG0, hδG⟩ := (Metric.continuousAt_iff.mp hG.continuousAt) ε hε
  rcases lt_trichotomy q₀.2 (1 / 2) with hlt | heq | hgt
  · refine ⟨min δF (1 / 2 - q₀.2), lt_min hδF0 (by linarith), ?_⟩
    intro y hy
    have hy2 : dist y.2 q₀.2 ≤ dist y q₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hylt : y.2 < 1 / 2 := by
      have h1 : dist y.2 q₀.2 < 1 / 2 - q₀.2 :=
        lt_of_le_of_lt hy2 (lt_of_lt_of_le hy (min_le_right _ _))
      rw [Real.dist_eq] at h1
      have h2 : y.2 - q₀.2 < 1 / 2 - q₀.2 := (abs_lt.mp h1).2
      linarith
    have hyF : rawProfile' r D y.1 y.2 = sweepArc r D y.1 (2 * y.2) := by
      rw [rawProfile', if_pos hylt.le]
    have hqF : rawProfile' r D q₀.1 q₀.2 = sweepArc r D q₀.1 (2 * q₀.2) := by
      rw [rawProfile', if_pos hlt.le]
    rw [hyF, hqF]
    exact hδF (lt_of_lt_of_le hy (min_le_left _ _))
  · refine ⟨min δF δG, lt_min hδF0 hδG0, ?_⟩
    intro y hy
    have h1 : dist y q₀ < δF := lt_of_lt_of_le hy (min_le_left _ _)
    have h2 : dist y q₀ < δG := lt_of_lt_of_le hy (min_le_right _ _)
    have hqF : rawProfile' r D q₀.1 q₀.2 = sweepArc r D q₀.1 (2 * q₀.2) := by
      rw [rawProfile', if_pos heq.le]
    have hqG : rawProfile' r D q₀.1 q₀.2 = sweepChord r D q₀.1 (2 - 2 * q₀.2) := by
      rw [hqF, heq]; norm_num; exact hkey q₀.1
    by_cases hy2 : y.2 ≤ 1 / 2
    · have hyF : rawProfile' r D y.1 y.2 = sweepArc r D y.1 (2 * y.2) := by
        rw [rawProfile', if_pos hy2]
      rw [hyF, hqF]
      exact hδF h1
    · have hyG : rawProfile' r D y.1 y.2 = sweepChord r D y.1 (2 - 2 * y.2) := by
        rw [rawProfile', if_neg hy2]
      rw [hyG, hqG]
      exact hδG h2
  · refine ⟨min δG (q₀.2 - 1 / 2), lt_min hδG0 (by linarith), ?_⟩
    intro y hy
    have hy2 : dist y.2 q₀.2 ≤ dist y q₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hygt : 1 / 2 < y.2 := by
      have h1 : dist y.2 q₀.2 < q₀.2 - 1 / 2 :=
        lt_of_le_of_lt hy2 (lt_of_lt_of_le hy (min_le_right _ _))
      rw [Real.dist_eq] at h1
      have h2 : -(q₀.2 - 1 / 2) < y.2 - q₀.2 := (abs_lt.mp h1).1
      linarith
    have hyG : rawProfile' r D y.1 y.2 = sweepChord r D y.1 (2 - 2 * y.2) := by
      rw [rawProfile', if_neg (not_le.mpr hygt)]
    have hqG : rawProfile' r D q₀.1 q₀.2 = sweepChord r D q₀.1 (2 - 2 * q₀.2) := by
      rw [rawProfile', if_neg (not_le.mpr hgt)]
    rw [hyG, hqG]
    exact hδG (lt_of_lt_of_le hy (min_le_left _ _))

/-! ## Injectivity of the raw profile on one period -/

/-- The raw profile is injective on the fundamental domain `[0,1)` (this is
`sweepProfile_injOn`, transported to the profile of the raw loop). -/
lemma rawProfile_injOn' {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {s : I} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1) :
    Set.InjOn (rawProfile' r D s) (Set.Ico (0 : ℝ) 1) := by
  obtain ⟨hW0, hWT⟩ := sweepW_pos_lt D s
    ⟨lt_of_le_of_ne s.2.1 (Ne.symm hs0), lt_of_le_of_ne s.2.2 hs1⟩
  exact sweepProfile_injOn hr D havoid hs0 hs1 hW0 hWT

/-! ## Uniform far separation of the raw loop -/

/-! ## Bridge lemmas: real sweep parameters versus the unit interval -/

lemma clampI_coe'' (s : I) : clampI (s : ℝ) = s := by
  apply Subtype.ext
  show min 1 (max 0 (s : ℝ)) = (s : ℝ)
  rw [max_eq_right s.2.1, min_eq_right s.2.2]

lemma taR_coe'' {d : BandArcData} (D : SweepData d) (s : I) : taR D (s : ℝ) = D.ta s := by
  simp [taR, clampI_coe'']

lemma tbR_coe'' {d : BandArcData} (D : SweepData d) (s : I) : tbR D (s : ℝ) = D.tb s := by
  simp [tbR, clampI_coe'']

lemma sweepW'_coe'' {d : BandArcData} (D : SweepData d) (s : I) :
    sweepW' D (s : ℝ) = sweepW D s := by
  simp [sweepW', sweepW, taR_coe'', tbR_coe'']

lemma sweepArc'_coe'' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (ξ : ℝ) :
    sweepArc' r D (s : ℝ) ξ = sweepArc r D s ξ := by
  simp [sweepArc', sweepArc, taR_coe'', sweepW'_coe'']

lemma sweepChord'_coe'' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s : I) (ξ : ℝ) :
    sweepChord' r D (s : ℝ) ξ = sweepChord r D s ξ := by
  simp [sweepChord', sweepChord, taR_coe'', tbR_coe'']

/-! ## A global Lipschitz constant for the knot -/

/-- Shifted derivatives: `deriv (r (· + c)) t = deriv r (t + c)`. -/
lemma deriv_comp_add_const'' {r : ℝ → Space} (hr : IsSmoothKnot r) (c t : ℝ) :
    deriv (fun y : ℝ => r (y + c)) t = deriv r (t + c) := by
  have h1 : HasDerivAt (fun y : ℝ => y + c) 1 t := (hasDerivAt_id t).add_const c
  have h2 : HasDerivAt r (deriv r (t + c)) (t + c) :=
    ((hr.smooth.differentiable (by simp)) (t + c)).hasDerivAt
  have h3 := h2.scomp t h1
  have h4 := h3.deriv
  rw [show (r ∘ fun y : ℝ => y + c) = (fun y : ℝ => r (y + c)) from
    funext fun y => rfl] at h4
  simpa only [one_smul] using h4

/-- The velocity of a smooth knot is `period`-periodic. -/
lemma velocity_periodic' {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Function.Periodic (velocity r) period := by
  intro t
  have h1 : (fun y : ℝ => r (y + period)) = r := funext fun y => hr.periodic y
  have h2 : deriv (fun y : ℝ => r (y + period)) t = deriv r (t + period) :=
    deriv_comp_add_const'' hr period t
  rw [h1] at h2
  exact h2.symm

/-- **A global Lipschitz constant for a smooth knot.** -/
lemma exists_knot_lipschitz' {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ M : ℝ, 0 < M ∧ ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y| := by
  have hvper : Function.Periodic (velocity r) period := velocity_periodic' hr
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hne : (Set.Icc (0 : ℝ) period).Nonempty := ⟨0, le_rfl, period_pos.le⟩
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hvcont.norm.continuousOn
  refine ⟨‖velocity r t₁‖ + 1, by positivity, fun x y => ?_⟩
  have hbound : ∀ t : ℝ, ‖velocity r t‖ ≤ ‖velocity r t₁‖ + 1 := by
    intro t
    obtain ⟨z, hz, htz⟩ := hvper.exists_mem_Ico period_pos t 0
    have hz' : z ∈ Set.Icc (0 : ℝ) period := ⟨hz.1, by linarith [hz.2]⟩
    calc ‖velocity r t‖ = ‖velocity r z‖ := by rw [htz]
      _ ≤ ‖velocity r t₁‖ := hmax hz'
      _ ≤ ‖velocity r t₁‖ + 1 := by linarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := r) (s := Set.univ)
    (C := ‖velocity r t₁‖ + 1) (fun t _ => (hr.smooth.differentiable (by simp)) t)
    (fun t _ => hbound t) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs] at h
  simpa [abs_sub_comm, norm_sub_rev] using h

/-! ## The corner-cut bound

Cutting the two corners of the raw loop at arc fraction `lam` moves the curve by `O(lam)`:
on the arc branch the loop parameter is shifted by `lam * (1 - 4u)`, on the chord branch the two
loops agree exactly, and on the two chamfers the segment joins two points that are both within
`O(lam)` of the corresponding chord point. -/

theorem chamfer_close_raw' {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 / 2 → ∀ s : I,
      (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → ∀ t : ℝ,
        ‖sweepLoopChamfer r D lam (s : ℝ) t - sweepLoop r D s t‖ ≤ C * lam := by
  obtain ⟨M, hM, hlip⟩ := exists_knot_lipschitz' hr
  have hMnn : 0 ≤ M := hM.le
  have hp : 0 < period := period_pos
  refine ⟨3 * M * period, by positivity, ?_⟩
  intro lam hlam0 hlam12 s hsI t
  obtain ⟨hwpos, hwlt⟩ := sweepW_pos_lt D s hsI
  have hwle : sweepW D s ≤ period := hwlt.le
  have hlam1 : lam < 1 := by linarith
  have hV : ‖r (D.tb s) - r (D.ta s)‖ ≤ M * period := by
    have h := hlip (D.tb s) (D.ta s)
    have habs : |D.tb s - D.ta s| = sweepW D s := by
      have h' : D.tb s - D.ta s = sweepW D s := rfl
      rw [h', abs_of_pos hwpos]
    calc ‖r (D.tb s) - r (D.ta s)‖ ≤ M * |D.tb s - D.ta s| := h
      _ = M * sweepW D s := by rw [habs]
      _ ≤ M * period := mul_le_mul_of_nonneg_left hwle hMnn
  have harcLip : ∀ ξ ξ' : ℝ,
      ‖sweepArc r D s ξ - sweepArc r D s ξ'‖ ≤ M * period * |ξ - ξ'| := by
    intro ξ ξ'
    have h := hlip (D.ta s + ξ * sweepW D s) (D.ta s + ξ' * sweepW D s)
    have harg : (D.ta s + ξ * sweepW D s) - (D.ta s + ξ' * sweepW D s)
        = (ξ - ξ') * sweepW D s := by ring
    rw [harg, abs_mul, abs_of_pos hwpos] at h
    have hstep : M * (|ξ - ξ'| * sweepW D s) ≤ M * (|ξ - ξ'| * period) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle (abs_nonneg _)) hMnn
    calc ‖sweepArc r D s ξ - sweepArc r D s ξ'‖
        = ‖r (D.ta s + ξ * sweepW D s) - r (D.ta s + ξ' * sweepW D s)‖ := by
          rw [sweepArc_eq, sweepArc_eq]
      _ ≤ M * (|ξ - ξ'| * period) := le_trans h hstep
      _ = M * period * |ξ - ξ'| := by ring
  have hchordLip : ∀ ξ ξ' : ℝ,
      ‖sweepChord r D s ξ - sweepChord r D s ξ'‖ ≤ M * period * |ξ - ξ'| := by
    intro ξ ξ'
    have hsub : sweepChord r D s ξ - sweepChord r D s ξ'
        = (ξ - ξ') • (r (D.tb s) - r (D.ta s)) := by
      simp only [sweepChord]; module
    rw [hsub, norm_smul, Real.norm_eq_abs]
    calc |ξ - ξ'| * ‖r (D.tb s) - r (D.ta s)‖ ≤ |ξ - ξ'| * (M * period) :=
          mul_le_mul_of_nonneg_left hV (abs_nonneg _)
      _ = M * period * |ξ - ξ'| := by ring
  have hchordLip' : ∀ ξ ξ' : ℝ,
      ‖sweepChord' r D (s : ℝ) ξ - sweepChord' r D (s : ℝ) ξ'‖ ≤ M * period * |ξ - ξ'| := by
    intro ξ ξ'
    have hsub : sweepChord' r D (s : ℝ) ξ - sweepChord' r D (s : ℝ) ξ'
        = (ξ - ξ') • (r (D.tb s) - r (D.ta s)) := by
      rw [sweepChord'_sub, taR_coe'', tbR_coe'']
    rw [hsub, norm_smul, Real.norm_eq_abs]
    calc |ξ - ξ'| * ‖r (D.tb s) - r (D.ta s)‖ ≤ |ξ - ξ'| * (M * period) :=
          mul_le_mul_of_nonneg_left hV (abs_nonneg _)
      _ = M * period * |ξ - ξ'| := by ring
  have hgap : ∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 → (ξ ≤ lam ∨ 1 - ξ ≤ lam) →
      ‖sweepArc r D s ξ - sweepChord r D s ξ‖ ≤ 2 * M * period * lam := by
    intro ξ hξ hend
    have hdecomp : sweepArc r D s ξ - sweepChord r D s ξ
        = (1 - ξ) • (r (D.ta s + ξ * sweepW D s) - r (D.ta s))
          + ξ • (r (D.ta s + ξ * sweepW D s) - r (D.tb s)) := by
      rw [sweepArc_eq, sweepChord]
      module
    have h1 : ‖r (D.ta s + ξ * sweepW D s) - r (D.ta s)‖ ≤ M * (ξ * sweepW D s) := by
      have h := hlip (D.ta s + ξ * sweepW D s) (D.ta s)
      have harg : |D.ta s + ξ * sweepW D s - D.ta s| = ξ * sweepW D s := by
        rw [show D.ta s + ξ * sweepW D s - D.ta s = ξ * sweepW D s by ring,
          abs_of_nonneg (mul_nonneg hξ.1 hwpos.le)]
      rwa [harg] at h
    have h2 : ‖r (D.ta s + ξ * sweepW D s) - r (D.tb s)‖ ≤ M * ((1 - ξ) * sweepW D s) := by
      have h := hlip (D.ta s + ξ * sweepW D s) (D.tb s)
      have harg : |D.ta s + ξ * sweepW D s - D.tb s| = (1 - ξ) * sweepW D s := by
        have he : D.ta s + ξ * sweepW D s - D.tb s = -(1 - ξ) * sweepW D s := by
          rw [sweepW]; ring
        rw [he, abs_mul, abs_neg, abs_of_nonneg (by linarith [hξ.2]), abs_of_pos hwpos]
      rwa [harg] at h
    have hfac : ξ * (1 - ξ) ≤ lam := by
      rcases hend with h | h
      · nlinarith [hξ.1, hξ.2, h]
      · nlinarith [hξ.1, hξ.2, h]
    have hstep : 2 * M * (ξ * (1 - ξ) * sweepW D s) ≤ 2 * M * (lam * period) := by
      have h1' : ξ * (1 - ξ) * sweepW D s ≤ lam * period := by
        nlinarith [hfac, hwle, hξ.1, hξ.2, hwpos, hlam0.le]
      nlinarith [h1', hMnn, hp]
    calc ‖sweepArc r D s ξ - sweepChord r D s ξ‖
        = ‖(1 - ξ) • (r (D.ta s + ξ * sweepW D s) - r (D.ta s))
            + ξ • (r (D.ta s + ξ * sweepW D s) - r (D.tb s))‖ := by rw [hdecomp]
      _ ≤ ‖(1 - ξ) • (r (D.ta s + ξ * sweepW D s) - r (D.ta s))‖
            + ‖ξ • (r (D.ta s + ξ * sweepW D s) - r (D.tb s))‖ := norm_add_le _ _
      _ = (1 - ξ) * ‖r (D.ta s + ξ * sweepW D s) - r (D.ta s)‖
            + ξ * ‖r (D.ta s + ξ * sweepW D s) - r (D.tb s)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [hξ.2]), abs_of_nonneg hξ.1]
      _ ≤ (1 - ξ) * (M * (ξ * sweepW D s)) + ξ * (M * ((1 - ξ) * sweepW D s)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith [hξ.2]))
            (mul_le_mul_of_nonneg_left h2 hξ.1)
      _ = 2 * M * (ξ * (1 - ξ) * sweepW D s) := by ring
      _ ≤ 2 * M * (lam * period) := hstep
      _ = 2 * M * period * lam := by ring
  rw [sweepLoopChamfer_eq_profile r D hlam0 hlam1 (s : ℝ) t,
    show sweepLoop r D s t = rawProfile' r D s (sweepParam t) from rfl]
  set w : ℝ := sweepParam t with hwdef
  have hw0 : 0 ≤ w := (sweepParam_mem t).1
  have hw1 : w < 1 := (sweepParam_mem t).2
  have hCnn : 0 ≤ 3 * M * period * lam := by positivity
  by_cases hA : w ≤ 1 / 2
  · rw [sweepLoopProfile_eq_arc D hA, rawProfile', if_pos hA, sweepArc'_coe'']
    have hdiff : |(lam + (1 - 2 * lam) * (2 * w)) - 2 * w| ≤ lam := by
      rw [show lam + (1 - 2 * lam) * (2 * w) - 2 * w = lam * (1 - 4 * w) by ring, abs_mul,
        abs_of_pos hlam0]
      have h4 : |1 - 4 * w| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      nlinarith [hlam0.le]
    have hb := harcLip (lam + (1 - 2 * lam) * (2 * w)) (2 * w)
    have hb2 : M * period * |(lam + (1 - 2 * lam) * (2 * w)) - 2 * w| ≤ M * period * lam :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    linarith [hb, hb2, hMnn, hp]
  · have hA' : 1 / 2 < w := not_le.mp hA
    by_cases hB : w ≤ 1 / 2 + lam / 2
    · rw [sweepLoopProfile_eq_lin2 D hA'.le hB, rawProfile', if_neg hA, sweepArc'_coe'',
        sweepChord'_coe'']
      set al : ℝ := (2 * w - 1) / lam with hal
      have hal0 : 0 ≤ al := div_nonneg (by linarith) hlam0.le
      have hal1 : al ≤ 1 := by
        rw [hal, div_le_one hlam0]; linarith
      have hdecomp : (1 - al) • sweepArc r D s (1 - lam) + al • sweepChord r D s (1 - lam)
            - sweepChord r D s (2 - 2 * w)
          = (1 - al) • (sweepArc r D s (1 - lam) - sweepChord r D s (1 - lam))
            + (sweepChord r D s (1 - lam) - sweepChord r D s (2 - 2 * w)) := by
        module
      rw [hdecomp]
      have hgap2 : ‖sweepArc r D s (1 - lam) - sweepChord r D s (1 - lam)‖
          ≤ 2 * M * period * lam :=
        hgap (1 - lam) ⟨by linarith, by linarith⟩ (Or.inr (by linarith))
      have hcd : ‖sweepChord r D s (1 - lam) - sweepChord r D s (2 - 2 * w)‖
          ≤ M * period * lam := by
        have h := hchordLip (1 - lam) (2 - 2 * w)
        have habs : |(1 - lam) - (2 - 2 * w)| ≤ lam := by
          rw [abs_le]; constructor <;> linarith
        nlinarith [h, habs, hMnn, hp]
      refine le_trans (norm_add_le _ _) ?_
      have hb1 : ‖(1 - al) • (sweepArc r D s (1 - lam) - sweepChord r D s (1 - lam))‖
          ≤ 1 * (2 * M * period * lam) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - al)]
        calc (1 - al) * ‖sweepArc r D s (1 - lam) - sweepChord r D s (1 - lam)‖
            ≤ ‖sweepArc r D s (1 - lam) - sweepChord r D s (1 - lam)‖ :=
              mul_le_of_le_one_left (norm_nonneg _) (by linarith)
          _ ≤ 2 * M * period * lam := hgap2
          _ = 1 * (2 * M * period * lam) := by ring
      have hfin : 1 * (2 * M * period * lam) + M * period * lam ≤ 3 * M * period * lam := by
        nlinarith [hMnn, hp, hlam0.le]
      linarith
    · have hB' : 1 / 2 + lam / 2 < w := not_le.mp hB
      by_cases hC : w ≤ 1 - lam / 2
      · rw [sweepLoopProfile_eq_chord3 D hlam0 hB'.le hC, rawProfile', if_neg hA,
          sweepChord'_coe'']
        rw [sub_self, norm_zero]
        exact hCnn
      · have hC' : 1 - lam / 2 < w := not_le.mp hC
        have hw12 : 1 / 2 < w := by linarith
        have hw23 : 1 / 2 + lam / 2 < w := by linarith
        rw [sweepLoopProfile, if_neg (not_le.mpr hw12), if_neg (not_le.mpr hw23),
          if_neg (not_le.mpr hC'), rawProfile', if_neg hA, sweepChord'_coe'', sweepArc'_coe'']
        set be : ℝ := (w - (1 - lam / 2)) / (lam / 2) with hbe
        have hbe0 : 0 ≤ be := div_nonneg (by linarith) (by linarith)
        have hbe1 : be ≤ 1 := by
          rw [hbe, div_le_one (by linarith)]; linarith
        have hdecomp : (1 - be) • sweepChord r D s lam + be • sweepArc r D s lam
            - sweepChord r D s (2 - 2 * w)
            = be • (sweepArc r D s lam - sweepChord r D s lam)
              + (sweepChord r D s lam - sweepChord r D s (2 - 2 * w)) := by
          module
        rw [hdecomp]
        have hgap3 : ‖sweepArc r D s lam - sweepChord r D s lam‖ ≤ 2 * M * period * lam :=
          hgap lam ⟨hlam0.le, by linarith⟩ (Or.inl le_rfl)
        have hcd : ‖sweepChord r D s lam - sweepChord r D s (2 - 2 * w)‖
            ≤ M * period * lam := by
          have h := hchordLip lam (2 - 2 * w)
          have habs : |lam - (2 - 2 * w)| ≤ lam := by
            rw [abs_le]; constructor <;> linarith
          nlinarith [h, habs, hMnn, hp]
        refine le_trans (norm_add_le _ _) ?_
        have hb1 : ‖be • (sweepArc r D s lam - sweepChord r D s lam)‖
            ≤ 1 * (2 * M * period * lam) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbe0]
          calc be * ‖sweepArc r D s lam - sweepChord r D s lam‖
              ≤ ‖sweepArc r D s lam - sweepChord r D s lam‖ :=
                mul_le_of_le_one_left (norm_nonneg _) hbe1
            _ ≤ 2 * M * period * lam := hgap3
            _ = 1 * (2 * M * period * lam) := by ring
        calc ‖be • (sweepArc r D s lam - sweepChord r D s lam)‖
              + ‖sweepChord r D s lam - sweepChord r D s (2 - 2 * w)‖
            ≤ 1 * (2 * M * period * lam) + M * period * lam := add_le_add hb1 hcd
          _ ≤ 3 * M * period * lam := by nlinarith [hMnn, hp, hlam0.le]

/-- **The raw sweep loop is uniformly separated at scale `η` over a compact window of sweep
parameters.**  For `σ ∈ [a,b] ⊂ (0,1)` the loop `sweepLoop r D σ` is injective on one period
(`havoid`), and the separation is uniform in `σ` by compactness of the constraint set. -/
theorem rawProfile_farSep' {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {η : ℝ} (hη : 0 < η)
    (hη2 : 2 * η ≤ period) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : I, (s : ℝ) ∈ Set.Icc a b → ∀ p₁ p₂ : ℝ,
      p₁ ∈ Set.Icc (0 : ℝ) 1 → p₂ ∈ Set.Icc (0 : ℝ) 1 →
      η / period ≤ |p₂ - p₁| → |p₂ - p₁| ≤ 1 - η / period →
      ρ ≤ rawSep' r D (s, p₁, p₂) := by
  have hp : 0 < period := period_pos
  have hη'pos : 0 < η / period := div_pos hη hp
  have hη'le : η / period ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
  have hη'le1 : η / period ≤ 1 := by linarith
  set K : Set (I × ℝ × ℝ) := {q | (q.1 : ℝ) ∈ Set.Icc a b ∧ q.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |q.2.2 - q.2.1| ∈ Set.Icc (η / period) (1 - η / period)}
    with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    have h1 : IsClosed {q : I × ℝ × ℝ | (q.1 : ℝ) ∈ Set.Icc a b} :=
      isClosed_Icc.preimage (continuous_subtype_val.comp continuous_fst)
    have h2 : IsClosed {q : I × ℝ × ℝ | q.2.1 ∈ Set.Icc (0 : ℝ) 1} :=
      isClosed_Icc.preimage (continuous_fst.comp continuous_snd)
    have h3 : IsClosed {q : I × ℝ × ℝ | q.2.2 ∈ Set.Icc (0 : ℝ) 1} :=
      isClosed_Icc.preimage (continuous_snd.comp continuous_snd)
    have h4 : IsClosed {q : I × ℝ × ℝ | |q.2.2 - q.2.1| ∈ Set.Icc (η / period) (1 - η / period)} :=
      isClosed_Icc.preimage
        (((continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd)).abs)
    exact h1.inter (h2.inter (h3.inter h4))
  have hKc : IsCompact K := by
    have hc : IsCompact ({s : I | (s : ℝ) ∈ Set.Icc a b} ×ˢ
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
      ((isClosed_Icc.preimage
        (continuous_subtype_val : Continuous fun s : I => (s : ℝ))).isCompact).prod
        (isCompact_Icc.prod isCompact_Icc)
    exact hc.of_isClosed_subset hKclosed (fun q hq => ⟨hq.1, hq.2.1, hq.2.2.1⟩)
  have hne : K.Nonempty := by
    refine ⟨(⟨a, ⟨ha.le, (hab.trans hb).le⟩⟩, 0, η / period), ?_⟩
    refine ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, zero_le_one⟩, ⟨hη'pos.le, hη'le1⟩, ?_⟩
    rw [sub_zero, abs_of_pos hη'pos]
    exact ⟨le_rfl, by linarith⟩
  have hf : Continuous (fun q : I × ℝ × ℝ => rawSep' r D q) := by
    have h1 : Continuous (fun q : I × ℝ × ℝ => rawProfile' r D q.1 q.2.1) :=
      (continuous_rawProfile' r hr.smooth.continuous D).comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have h2 : Continuous (fun q : I × ℝ × ℝ => rawProfile' r D q.1 q.2.2) :=
      (continuous_rawProfile' r hr.smooth.continuous D).comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    have hsub : Continuous (fun q : I × ℝ × ℝ =>
        (rawProfile' r D q.1 q.2.1 - rawProfile' r D q.1 q.2.2)) := h1.sub h2
    simpa only [rawSep'] using hsub.norm
  obtain ⟨q₀, hq₀K, hmin⟩ := hKc.exists_isMinOn hne hf.continuousOn
  refine ⟨rawSep' r D q₀, ?_, ?_⟩
  · simp only [rawSep']
    rw [norm_pos_iff]
    intro hsub
    have heq : rawProfile' r D q₀.1 q₀.2.1 = rawProfile' r D q₀.1 q₀.2.2 := sub_eq_zero.mp hsub
    have hp₁ := hq₀K.2.1
    have hp₂ := hq₀K.2.2.1
    have hdist := hq₀K.2.2.2
    have hne12 : q₀.2.1 ≠ q₀.2.2 := by
      intro h
      have hzero : |q₀.2.2 - q₀.2.1| = 0 := by rw [← h, sub_self, abs_zero]
      have hlow := hdist.1
      rw [hzero] at hlow
      linarith [hη'pos]
    have hs0 : (q₀.1 : ℝ) ≠ 0 := by
      intro h
      have hmem := hq₀K.1
      rw [h] at hmem
      linarith [hmem.1, ha]
    have hs1 : (q₀.1 : ℝ) ≠ 1 := by
      intro h
      have hmem := hq₀K.1
      rw [h] at hmem
      linarith [hmem.2, hb]
    by_cases hA : q₀.2.1 = 1
    · have hne₂ : q₀.2.2 ≠ 1 := by
        intro h
        have hlow := hdist.1
        rw [hA, h, sub_self, abs_zero] at hlow
        linarith [hη'pos]
      have hlt₂ : q₀.2.2 < 1 := lt_of_le_of_ne hp₂.2 hne₂
      have h1 : |q₀.2.2 - 1| ≤ 1 - η / period := by
        have h := hdist.2
        rw [hA] at h
        exact h
      have hpos₂ : 0 < q₀.2.2 := by
        have h := (abs_le.mp h1).1
        linarith [hη'pos]
      have h0 : rawProfile' r D q₀.1 0 = rawProfile' r D q₀.1 q₀.2.2 := by
        rw [← rawProfile_one_eq_zero' r D q₀.1]
        rw [hA] at heq
        exact heq
      have hres : (0 : ℝ) = q₀.2.2 :=
        rawProfile_injOn' hr D havoid hs0 hs1 ⟨le_rfl, zero_lt_one⟩ ⟨hp₂.1, hlt₂⟩ h0
      linarith
    · by_cases hB : q₀.2.2 = 1
      · have hlt₁ : q₀.2.1 < 1 := lt_of_le_of_ne hp₁.2 hA
        have h1 : |1 - q₀.2.1| ≤ 1 - η / period := by
          have h := hdist.2
          rw [hB] at h
          exact h
        have hpos₁ : 0 < q₀.2.1 := by
          have h := (abs_le.mp h1).2
          linarith [hη'pos]
        have h0 : rawProfile' r D q₀.1 0 = rawProfile' r D q₀.1 q₀.2.1 := by
          rw [← rawProfile_one_eq_zero' r D q₀.1]
          rw [hB] at heq
          exact heq.symm
        have hres : (0 : ℝ) = q₀.2.1 :=
          rawProfile_injOn' hr D havoid hs0 hs1 ⟨le_rfl, zero_lt_one⟩ ⟨hp₁.1, hlt₁⟩ h0
        linarith
      · have hm₁ : q₀.2.1 ∈ Set.Ico (0 : ℝ) 1 := ⟨hp₁.1, lt_of_le_of_ne hp₁.2 hA⟩
        have hm₂ : q₀.2.2 ∈ Set.Ico (0 : ℝ) 1 := ⟨hp₂.1, lt_of_le_of_ne hp₂.2 hB⟩
        exact hne12 (rawProfile_injOn' hr D havoid hs0 hs1 hm₁ hm₂ heq)
  · intro s hs p₁ p₂ hp₁ hp₂ hlo hhi
    exact hmin ⟨hs, hp₁, hp₂, hlo, hhi⟩

end

/-! ## A five-term triangle inequality -/

lemma norm_sub_le_five' {E : Type*} [SeminormedAddCommGroup E] (x₀ x₁ x₂ x₃ x₄ x₅ : E) :
    ‖x₀ - x₅‖ ≤ ‖x₀ - x₁‖ + ‖x₁ - x₂‖ + ‖x₂ - x₃‖ + ‖x₃ - x₄‖ + ‖x₄ - x₅‖ := by
  have h1 := norm_sub_le_trans' x₀ x₁ x₅
  have h2 := norm_sub_le_trans' x₁ x₂ x₅
  have h3 := norm_sub_le_trans' x₂ x₃ x₅
  have h4 := norm_sub_le_trans' x₃ x₄ x₅
  linarith [norm_nonneg (x₁ - x₂), norm_nonneg (x₂ - x₃), norm_nonneg (x₃ - x₄)]

end Helpers

section Main

open LeanEval.KnotTheory.Quadrisecant

theorem sweepFamFarSep' {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ L ρ : ℝ, 0 < L ∧ 0 < ρ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ : ℝ, a ≤ σ → σ ≤ b →
          ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period →
            t₂ ∈ Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period →
            η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ LeanEval.KnotTheory.Quadrisecant.period - η →
              ρ ≤ ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ t₁ -
                Work.Drive.sweepFam r D lam δ₁ δ₂ σ t₂‖ := by
  by_cases hη2 : 2 * η ≤ period
  · -- the constraint set is non-empty: use the compactness separation of the raw loop
    obtain ⟨ρ₀, hρ₀pos, hρ₀sep⟩ := rawProfile_farSep' hr D havoid ha hab hb hη hη2
    obtain ⟨C, hCnn, hCbound⟩ := chamfer_close_raw' hr D
    obtain ⟨L₁, hL₁pos, hL₁bound⟩ :=
      sweepFam_close_chamfer' hr.smooth.continuous D (ρ₀ / 8) (by linarith)
    have hC1pos : 0 < C + 1 := by linarith
    refine ⟨min (1 / 2) (min L₁ (ρ₀ / (8 * (C + 1)))), ρ₀ / 2, ?_, by linarith, ?_⟩
    · positivity
    · intro lam δ₁ δ₂ hlam0 hlamL hδ₁0 hδ₁L hδ₂0 hδ₂L σ hσa hσb t₁ t₂ ht₁ ht₂ hge hle
      have hper : 0 < period := period_pos
      have hlam12 : lam ≤ 1 / 2 := hlamL.trans (min_le_left _ _)
      have hL₁ : lam ≤ L₁ := hlamL.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hδ₁L₁ : δ₁ ≤ L₁ := hδ₁L.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hδ₂L₁ : δ₂ ≤ L₁ := hδ₂L.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hLc : lam ≤ ρ₀ / (8 * (C + 1)) :=
        hlamL.trans ((min_le_right _ _).trans (min_le_right _ _))
      set s : Set.Icc (0 : ℝ) 1 := ⟨σ, ⟨(ha.trans_le hσa).le, hσb.trans hb.le⟩⟩ with hsdef
      have hsval : (s : ℝ) = σ := rfl
      have hsI : (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha.trans_le hσa, hσb.trans_lt hb⟩
      have hsc : (s : ℝ) ∈ Set.Icc a b := ⟨hσa, hσb⟩
      set p₁ : ℝ := t₁ / period with hp₁def
      set p₂ : ℝ := t₂ / period with hp₂def
      have hp₁0 : 0 ≤ p₁ := by rw [hp₁def]; exact div_nonneg ht₁.1 hper.le
      have hp₁1 : p₁ < 1 := by rw [hp₁def]; exact (div_lt_one hper).mpr ht₁.2
      have hp₂0 : 0 ≤ p₂ := by rw [hp₂def]; exact div_nonneg ht₂.1 hper.le
      have hp₂1 : p₂ < 1 := by rw [hp₂def]; exact (div_lt_one hper).mpr ht₂.2
      have habs : |p₂ - p₁| = |t₂ - t₁| / period := by
        rw [hp₁def, hp₂def, ← sub_div, abs_div, abs_of_pos hper]
      have hlo : η / period ≤ |p₂ - p₁| := by
        rw [habs]; exact div_le_div_of_nonneg_right hge hper.le
      have hhi : |p₂ - p₁| ≤ 1 - η / period := by
        rw [habs, div_le_iff₀ hper]
        have h2 : (1 - η / period) * period = period - η := by field_simp
        linarith
      have hsep := hρ₀sep s hsc p₁ p₂ ⟨hp₁0, hp₁1.le⟩ ⟨hp₂0, hp₂1.le⟩ hlo hhi
      have hR₁ : rawProfile' r D s p₁ = sweepLoop r D s t₁ := by
        rw [hp₁def, ← sweepParam_eq_div ht₁]
        exact (sweepLoop_eq_rawProfile' r D s t₁).symm
      have hR₂ : rawProfile' r D s p₂ = sweepLoop r D s t₂ := by
        rw [hp₂def, ← sweepParam_eq_div ht₂]
        exact (sweepLoop_eq_rawProfile' r D s t₂).symm
      simp only [rawSep'] at hsep
      rw [hR₁, hR₂] at hsep
      have hClam : C * lam ≤ ρ₀ / 8 := by
        have h1 : C * lam ≤ (C + 1) * lam := by nlinarith [hCnn, hlam0.le]
        have h2 : (C + 1) * lam ≤ (C + 1) * (ρ₀ / (8 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hLc hC1pos.le
        have h3 : (C + 1) * (ρ₀ / (8 * (C + 1))) = ρ₀ / 8 := by field_simp
        linarith
      have hcut₁ : ‖sweepLoop r D s t₁ - sweepLoopChamfer r D lam σ t₁‖ ≤ ρ₀ / 8 := by
        rw [norm_sub_rev]
        exact le_trans (hCbound lam hlam0 hlam12 s hsI t₁) hClam
      have hcut₂ : ‖sweepLoopChamfer r D lam σ t₂ - sweepLoop r D s t₂‖ ≤ ρ₀ / 8 :=
        le_trans (hCbound lam hlam0 hlam12 s hsI t₂) hClam
      have hsm₁ : ‖sweepLoopChamfer r D lam σ t₁ - sweepFam r D lam δ₁ δ₂ σ t₁‖ ≤ ρ₀ / 8 := by
        rw [norm_sub_rev]
        exact hL₁bound lam δ₁ δ₂ hlam0 hL₁ hδ₁0 hδ₁L₁ hδ₂0 hδ₂L₁ σ t₁
      have hsm₂ : ‖sweepFam r D lam δ₁ δ₂ σ t₂ - sweepLoopChamfer r D lam σ t₂‖ ≤ ρ₀ / 8 :=
        hL₁bound lam δ₁ δ₂ hlam0 hL₁ hδ₁0 hδ₁L₁ hδ₂0 hδ₂L₁ σ t₂
      have hfive := norm_sub_le_five' (sweepLoop r D s t₁) (sweepLoopChamfer r D lam σ t₁)
        (sweepFam r D lam δ₁ δ₂ σ t₁) (sweepFam r D lam δ₁ δ₂ σ t₂)
        (sweepLoopChamfer r D lam σ t₂) (sweepLoop r D s t₂)
      linarith [hsep, hfive, hcut₁, hsm₁, hsm₂, hcut₂, hρ₀pos]
  · -- the constraint on the two loop parameters is empty
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro lam δ₁ δ₂ hlam0 hlamL hδ₁0 hδ₁L hδ₂0 hδ₂L σ hσa hσb t₁ t₂ ht₁ ht₂ hge hle
    exfalso
    linarith

end Main

end Work.Drive
