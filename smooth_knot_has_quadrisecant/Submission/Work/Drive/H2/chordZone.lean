import Mathlib
import Submission.Work.Drive.Generic.needleShiftedAngVelDep_of_bounds
import Submission.Work.Drive.H2.zoneClose
import Submission.Work.Drive.chamferVelBranch

/-!
# The chord zone of the per-loop margin `Work.Drive.ChartLoopMargin`

Lane H2.  The last pin of the needle's angular-velocity route is the *per-loop margin*: the
numerator of the loop velocity about the needle's chart centre is bounded below, uniformly in the
box.  The loop is piecewise (arc, first chamfer, chord, second chamfer); this module closes the
**chord zone**.

The chord branch of the loop is the straight segment from the blurred `b`-end to the blurred
`a`-end of the retained arc, travelled backwards at the constant speed
`c₀ = (1 - 2*lam)/((1/2 - lam)*period) = 2/period`.  On a straight piece the numerator is
*constant* (`Work.Drive.H2.angNum_segment`), and it equals `c₀` times the oriented area of the
triangle `(centre, loop point, chord point)`.  The chart centre sits *below* the needle's chord
line by half the base height `h = ‖chartUp‖`, and the loop's chord is within `ν` of the needle's,
so the oriented area is `≈ h·ℓ/2` with `ℓ = ‖chordEndB - chordEndA‖` the blurred chord length.

The quantitative core is `Work.Drive.H2.chordZoneCore` (abstract, for any normed space): with
`B - p = δ - M•v`, `‖δ‖ ≤ μ`, `⟪p-c,e⟫ ≤ -Y`, `‖p-c‖ ≤ R` and `μ ≤ M/2` one gets

    c₀ * (Y * (M - μ) - R * μ) ≤ ⟪p-c,e⟫⟪c₀•(B-p),v⟫ - ⟪p-c,v⟫⟪c₀•(B-p),e⟫ .

The main theorem `Work.Drive.H2.chordZone_margin` instantiates the core at the chord branch of the
loop, with the hypotheses exactly the data available from the window estimates
(`Work.Drive.windowDataSmall`, `Work.Drive.H2.loopChord_close_blurredChord`), and produces the
explicit margin `h*ℓ/(128*period)`.

## The hypotheses (all of them uniform in the box and verified elsewhere)

* `hℓ` — `v` is the unit direction of the needle's chord;
* `hνh`, `hνℓ` — the base height and the chord length dominate the mismatch `ν`;
* `hbase` — the needle's base point is within `2ℓ` of the chart's chord end (used only through
  `h ≤ 2ℓ`);
* `hclose` — the loop's chord is within `ν` of the needle's chord;
* `hA`, `hB` — the two endpoints of the loop's chord are within `ν` of the corresponding blurred
  chord ends.
-/

noncomputable section
namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

set_option maxHeartbeats 1000000

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## The branch identities of the chord zone -/

/-- On the chord branch the loop is `sweepChord'` at an affine fraction of the loop parameter. -/
lemma chordZone_loop_eq {lam σ t : ℝ} (hlam0 : 0 < lam)
    (h0 : 1 / 2 + lam / 2 < sweepParam t) (h1 : sweepParam t ≤ 1 - lam / 2) :
    sweepLoopChamfer r D lam σ t = sweepChord' r D σ
      ((1 - lam) - ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)) := by
  rw [sweepLoopChamfer]
  rw [if_neg (by linarith), if_neg (by linarith), if_pos h1]

/-- On the chord branch the velocity is `chamferVelChord`. -/
lemma chordZone_vel_eq {lam σ t : ℝ} (hlam0 : 0 < lam)
    (h0 : 1 / 2 + lam / 2 < sweepParam t) (h1 : sweepParam t ≤ 1 - lam / 2) :
    chamferVel r D lam σ t = chamferVelChord r D lam σ t := by
  rw [chamferVel_eq_ite]
  rw [if_neg (by linarith), if_neg (by linarith), if_pos h1]

/-! ## The quantitative core -/

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The quantitative chord-zone core.**  If the velocity direction `B - p` is `δ`-close to
`-M • v` with `‖δ‖ ≤ μ`, the point `p` is below the centre (`⟪p - c, e⟫ ≤ -Y`) at distance at most
`R` from it, and `μ ≤ M/2`, then the numerator of the loop velocity `c₀ • (B - p)` about the centre
`c` in the frame `(v, e)` is at least `c₀ * (Y * (M - μ) - R * μ)`.

This is `Work.Drive.H2.chordZone_close` with constants: the same geometry, but the conclusion is a
*quantitative* lower bound rather than bare positivity (the pin needs the quantitative form, since
the margin must survive the box's limiting process). -/
theorem chordZoneCore {v e c p B : E} {c₀ M μ Y R : ℝ}
    (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : inner ℝ v e = 0)
    (hc₀ : 0 < c₀) (hM : 0 < M) (hY : 0 < Y) (_hμ0 : 0 ≤ μ) (hμM : μ ≤ M / 2)
    (hdir : ‖(B - p) + M • v‖ ≤ μ)
    (hpe : inner ℝ (p - c) e ≤ -Y)
    (hR : ‖p - c‖ ≤ R) :
    c₀ * (Y * (M - μ) - R * μ)
      ≤ inner ℝ (p - c) e * inner ℝ (c₀ • (B - p)) v
        - inner ℝ (p - c) v * inner ℝ (c₀ • (B - p)) e := by
  set δ : E := (B - p) + M • v with hδ
  have hδn : ‖δ‖ ≤ μ := by rw [hδ]; exact hdir
  have hBp : B - p = δ - M • v := by rw [hδ]; abel
  have hδv : |inner ℝ δ v| ≤ μ := by
    have h := abs_real_inner_le_norm δ v
    rw [hv, mul_one] at h
    exact le_trans h hδn
  have hδe : |inner ℝ δ e| ≤ μ := by
    have h := abs_real_inner_le_norm δ e
    rw [he, mul_one] at h
    exact le_trans h hδn
  have hpv : |inner ℝ (p - c) v| ≤ R := by
    have h := abs_real_inner_le_norm (p - c) v
    rw [hv, mul_one] at h
    exact le_trans h hR
  have hTv : inner ℝ (c₀ • (B - p)) v = c₀ * (inner ℝ δ v - M) := by
    rw [hBp, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hv]
    ring
  have hTe : inner ℝ (c₀ • (B - p)) e = c₀ * inner ℝ δ e := by
    rw [hBp, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hve, mul_zero, sub_zero]
  rw [hTv, hTe]
  set A : ℝ := inner ℝ (p - c) e with hA
  set F : ℝ := inner ℝ δ v - M with hF
  set Bv : ℝ := inner ℝ (p - c) v with hBv
  set G : ℝ := inner ℝ δ e with hG
  have hA0 : A ≤ 0 := by rw [hA]; linarith
  have hδv2 : inner ℝ δ v ≤ μ := (abs_le.mp hδv).2
  have hδe2 : inner ℝ δ e ≤ μ := (abs_le.mp hδe).2
  have hδe1 : -μ ≤ inner ℝ δ e := (abs_le.mp hδe).1
  have hF0 : F ≤ 0 := by rw [hF]; linarith [hδv2, hμM]
  have hFμ : F ≤ μ - M := by rw [hF]; linarith [hδv2]
  have hstep1 : Y * (M - μ) ≤ A * F := by
    have ha : Y ≤ -A := by rw [hA]; linarith
    have hb : M - μ ≤ -F := by rw [hF]; linarith [hδv2]
    have hprod : Y * (M - μ) ≤ (-A) * (-F) :=
      mul_le_mul ha hb (by linarith) (by linarith)
    rwa [neg_mul_neg] at hprod
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
  have hstep2 : -(R * μ) ≤ -(Bv * G) := by
    have h1 : |Bv| ≤ R := by rw [hBv]; exact hpv
    have h2 : |G| ≤ μ := by rw [hG]; exact hδe
    have h3 : |Bv * G| ≤ R * μ := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hR0
    have h4 : Bv * G ≤ |Bv * G| := le_abs_self _
    linarith
  have hfin : Y * (M - μ) - R * μ ≤ A * F - Bv * G := by linarith
  have hgoal : A * (c₀ * F) - Bv * (c₀ * G) = c₀ * (A * F - Bv * G) := by ring
  rw [hgoal]
  exact mul_le_mul_of_nonneg_left hfin hc₀.le

/-- **The orthogonal projection onto `v^⊥` is a contraction.** -/
lemma norm_sub_inner_smul_le {v : Space} (hv : ‖v‖ = 1) (z : Space) :
    ‖z - (inner ℝ z v) • v‖ ≤ ‖z‖ := by
  have h1 : ‖z - (inner ℝ z v) • v‖ ^ 2 = ‖z‖ ^ 2 - (inner ℝ z v) ^ 2 := by
    rw [← inner_self_sub_smul z v hv, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have h2 : ‖z - (inner ℝ z v) • v‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h1]; nlinarith [sq_nonneg (inner ℝ z v)]
  nlinarith [norm_nonneg (z - (inner ℝ z v) • v), norm_nonneg z]


end Core

/-! ## The chart identities -/

/-- The `chartE`-coordinate of an arbitrary point about the chart centre. -/
lemma inner_sub_chartC_chartE {lam δ₁ δ₂ ε : ℝ} {v : Space}
    (hv : ‖v‖ = 1) (hup : chartUp r D lam δ₁ δ₂ ε v ≠ 0) (p : Space) :
    inner ℝ (p - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (p - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        - ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  have h1 : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := Generic.AngVelDep.inner_v_chartE hv
  have h2 : inner ℝ (chartE r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v) = 1 :=
    Generic.AngVelDep.inner_chartE_self hup
  rw [chartC, inner_sub_left, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, h1, h2, inner_sub_left]
  ring

/-- The chart centre is within `|nCoord 0| + h/2` of the `a`-end of the needle's chord. -/
lemma norm_chartC_sub_chordEndA {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    ‖chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε‖
      ≤ |nCoord r D lam δ₁ δ₂ ε v 0| + ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  have h2 : ‖(‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v‖
      = ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
    rcases eq_or_ne (chartUp r D lam δ₁ δ₂ ε v) 0 with hz | hz
    · rw [hz]; simp [chartE]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Generic.AngVelDep.norm_chartE hz, mul_one]
  have h3 : chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε
      = (nCoord r D lam δ₁ δ₂ ε v 0) • v
        + (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v := by
    rw [chartC]
    abel
  have h4 : ‖(nCoord r D lam δ₁ δ₂ ε v 0) • v‖ = |nCoord r D lam δ₁ δ₂ ε v 0| := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one]
  rw [h3]
  calc ‖(nCoord r D lam δ₁ δ₂ ε v 0) • v
        + (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v‖
      ≤ ‖(nCoord r D lam δ₁ δ₂ ε v 0) • v‖
        + ‖(‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v‖ := norm_add_le _ _
    _ = |nCoord r D lam δ₁ δ₂ ε v 0| + ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by rw [h4, h2]

/-! ## The chord zone of the loop -/

/-- **The chord zone of the per-loop margin.**
On the chord branch of the loop the numerator of the loop velocity about the chart centre is at
least `h * ℓ / (8 * period)`, where `h = ‖chartUp‖` is the base height and
`ℓ = ‖chordEndB - chordEndA‖` the (blurred) chord length.

The hypotheses are exactly the window data: `hνh`, `hνℓ` bound the mismatch `ν` by the geometric
scales, `hbase` is the distance of the needle's base point to the chart's `a`-end, `hclose` the
displacement of the loop's chord from the needle's, and `hA`/`hB` the displacements of its two
endpoints from the corresponding blurred chord ends. -/
theorem chordZone_margin {r : ℝ → Space} {d : BandArcData} {D : SweepData d}
    {lam δ₁ δ₂ ε σ t ν : ℝ} {v : Space} (hv : ‖v‖ = 1) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hℓ : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v)
    (hν0 : 0 < ν)
    (hνh : 1024 * ν ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖)
    (hνℓ : 1024 * ν ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
    (hbase : ‖shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε‖
      ≤ 2 * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
    (hclose : ‖(r (tbR D σ) - r (taR D σ))
      - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ ≤ ν)
    (hA : ‖r (taR D σ) - chordEndA r D δ₂ ε‖ ≤ ν)
    (hB : ‖r (tbR D σ) - chordEndB r D δ₂ ε‖ ≤ ν)
    (hz0 : 1 / 2 + lam / 2 < sweepParam t) (hz1 : sweepParam t ≤ 1 - lam / 2) :
    ‖chartUp r D lam δ₁ δ₂ ε v‖ * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
        / (8 * period)
      ≤ inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v)
            (chartE r D lam δ₁ δ₂ ε v)
          * inner ℝ (chamferVel r D lam σ t) v
        - inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v) v
          * inner ℝ (chamferVel r D lam σ t) (chartE r D lam δ₁ δ₂ ε v) := by
  have hP : 0 < period := period_pos
  set h : ℝ := ‖chartUp r D lam δ₁ δ₂ ε v‖ with hh
  set ℓ : ℝ := ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ with hℓ'
  set e : Space := chartE r D lam δ₁ δ₂ ε v with he
  set c : Space := chartC r D lam δ₁ δ₂ ε v with hc
  set U : Space := r (tbR D σ) - r (taR D σ) with hU
  set M : ℝ := ‖U‖ with hMdef
  set ξ : ℝ := (1 - lam) - ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
    with hξ
  set p : Space := sweepChord' r D σ ξ with hp
  set c₀ : ℝ := (1 - 2 * lam) / ((1 / 2 - lam) * period) with hc₀def
  set Y : ℝ := h / 2 - ν with hYdef
  set μ : ℝ := 2 * ν with hμdef
  set R : ℝ := 4 * ℓ + h with hRdef
  have hhpos : 0 < h := by linarith
  have hup_ne : chartUp r D lam δ₁ δ₂ ε v ≠ 0 := by
    rw [hh] at hhpos
    exact norm_pos_iff.mp hhpos
  have he1 : ‖e‖ = 1 := by rw [he]; exact Generic.AngVelDep.norm_chartE hup_ne
  have hve : inner ℝ v e = 0 := by rw [he]; exact Generic.AngVelDep.inner_v_chartE hv
  have hℓpos : 0 < ℓ := by linarith
  have hW : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε = ℓ • v := by
    simpa only [hℓ'] using hℓ
  have hh_le : h ≤ 2 * ℓ := by
    rw [hh]
    refine le_trans ?_ hbase
    rw [chartUp]
    exact norm_sub_inner_smul_le hv _
  -- the displacement of the loop's chord
  have hclose' : ‖U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ ≤ ν := by
    rw [hU]; exact hclose
  have hUv : |inner ℝ U v - ℓ| ≤ ν := by
    have h2 : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v = ℓ := by
      rw [hW, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      ring
    have h3 : inner ℝ U v - ℓ
        = inner ℝ (U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v := by
      rw [← h2, ← inner_sub_left U (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v]
    rw [h3]
    calc |inner ℝ (U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v|
        ≤ ‖U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ := by rw [hv, mul_one]
      _ ≤ ν := hclose'
  have hUe : |inner ℝ U e| ≤ ν := by
    have h2 : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e = 0 := by
      rw [hW, real_inner_smul_left, hve, mul_zero]
    have h3 : inner ℝ U e = inner ℝ (U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) e := by
      have h4 : inner ℝ (U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) e
          = inner ℝ U e - inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e :=
        inner_sub_left U (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e
      rw [h4, h2, sub_zero]
    rw [h3]
    calc |inner ℝ (U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) e|
        ≤ ‖U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = ‖U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ := by rw [he1, mul_one]
      _ ≤ ν := hclose'
  have hM_low : ℓ - ν ≤ M := by
    have h2 : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ = ℓ := by rw [← hℓ']
    have h1 := abs_norm_sub_norm_le U (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
    rw [h2, ← hMdef] at h1
    have := (abs_le.mp h1).1
    linarith [hclose']
  have hMpos : 0 < M := by linarith
  -- the direction mismatch
  have hdir : ‖(-U) + M • v‖ ≤ μ := by
    rw [hμdef]
    have heq : (-U) + M • v = (M - ℓ) • v + (ℓ • v - U) := by rw [sub_smul]; abel
    rw [heq]
    have h1 : ‖(M - ℓ) • v‖ = |M - ℓ| := by rw [norm_smul, Real.norm_eq_abs, hv, mul_one]
    have h2 : |M - ℓ| ≤ ν := by
      have h2' : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ = ℓ := by rw [← hℓ']
      have h1' := abs_norm_sub_norm_le U (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
      rw [h2', ← hMdef] at h1'
      exact le_trans h1' hclose'
    have h3 : ‖ℓ • v - U‖ ≤ ν := by
      have h3' : ℓ • v - U = -(U - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) := by
        rw [hW]; abel
      rw [h3', norm_neg]; exact hclose'
    calc ‖(M - ℓ) • v + (ℓ • v - U)‖ ≤ ‖(M - ℓ) • v‖ + ‖ℓ • v - U‖ := norm_add_le _ _
      _ ≤ ν + ν := add_le_add (by rw [h1]; exact h2) h3
      _ = 2 * ν := by ring
  -- the chord fraction of the loop point
  have hτ0 : 0 ≤ (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) :=
    div_nonneg (by linarith) (by linarith)
  have hτ1 : (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hξmem : ξ ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hξ]
    have h1 : (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) * (1 - 2 * lam)
        ≤ 1 * (1 - 2 * lam) := mul_le_mul_of_nonneg_right hτ1 (by linarith)
    have h2 : 0 ≤ (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) * (1 - 2 * lam) :=
      mul_nonneg hτ0 (by linarith)
    constructor <;> linarith
  -- the loop point and its velocity
  have hloop : sweepLoopChamfer r D lam σ t = p := by
    rw [hp, chordZone_loop_eq (D := D) hlam0 hz0 hz1, hξ]
  have hvel : chamferVel r D lam σ t = c₀ • (-U) := by
    rw [chordZone_vel_eq (D := D) hlam0 hz0 hz1, chamferVelChord, hU, hc₀def]
    rw [smul_neg, neg_smul]
  -- the chart of the loop point
  have hpdef : p = (1 - ξ) • r (taR D σ) + ξ • r (tbR D σ) := by
    rw [hp, sweepChord']
  have hpdecomp : p - chordEndA r D δ₂ ε
      = (1 - ξ) • (r (taR D σ) - chordEndA r D δ₂ ε)
        + ξ • (r (tbR D σ) - chordEndA r D δ₂ ε) := by
    have h2 : (1 - ξ) • chordEndA r D δ₂ ε + ξ • chordEndA r D δ₂ ε
        = chordEndA r D δ₂ ε := by
      rw [← add_smul, show (1 - ξ) + ξ = 1 by ring, one_smul]
    calc p - chordEndA r D δ₂ ε
        = ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)) - chordEndA r D δ₂ ε := by rw [hpdef]
      _ = ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ))
            - ((1 - ξ) • chordEndA r D δ₂ ε + ξ • chordEndA r D δ₂ ε) := by rw [h2]
      _ = (1 - ξ) • (r (taR D σ) - chordEndA r D δ₂ ε)
            + ξ • (r (tbR D σ) - chordEndA r D δ₂ ε) := by
          rw [smul_sub, smul_sub]
          abel
  have hpheightE : inner ℝ (p - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v) ≤ ν := by
    rw [hpdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h1 : inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v) ≤ ν := by
      have h' := abs_real_inner_le_norm (r (taR D σ) - chordEndA r D δ₂ ε)
        (chartE r D lam δ₁ δ₂ ε v)
      rw [he1, mul_one] at h'
      linarith [(abs_le.mp h').2, hA]
    have h2 : inner ℝ (r (tbR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v) ≤ ν := by
      have hsplit : r (tbR D σ) - chordEndA r D δ₂ ε
          = (r (tbR D σ) - chordEndB r D δ₂ ε)
            + (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) := by abel
      rw [hsplit, inner_add_left]
      have h3 : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
          (chartE r D lam δ₁ δ₂ ε v) = 0 := by
        rw [hW, real_inner_smul_left, hve, mul_zero]
      rw [h3, add_zero]
      have h' := abs_real_inner_le_norm (r (tbR D σ) - chordEndB r D δ₂ ε)
        (chartE r D lam δ₁ δ₂ ε v)
      rw [he1, mul_one] at h'
      linarith [(abs_le.mp h').2, hB]
    have hx1 : (0 : ℝ) ≤ 1 - ξ := by linarith [hξmem.2]
    have hx2 : (0 : ℝ) ≤ ξ := hξmem.1
    have hsum := add_le_add (mul_le_mul_of_nonneg_left h1 hx1)
      (mul_le_mul_of_nonneg_left h2 hx2)
    linarith
  -- the height of the loop point below the centre
  have hpe : inner ℝ (p - c) e ≤ -Y := by
    have key := inner_sub_chartC_chartE (r := r) (D := D) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂)
      (ε := ε) (v := v) hv hup_ne p
    rw [hc, he, hYdef, key, ← hh]
    linarith
  -- the distance from the loop point to the centre
  have hpdist : ‖p - chordEndA r D δ₂ ε‖ ≤ ℓ + ν := by
    rw [hpdecomp]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - ξ by linarith [hξmem.2]), abs_of_nonneg hξmem.1]
    have h1 : ‖r (taR D σ) - chordEndA r D δ₂ ε‖ ≤ ν := hA
    have h2 : ‖r (tbR D σ) - chordEndA r D δ₂ ε‖ ≤ ℓ + ν := by
      have hsplit : r (tbR D σ) - chordEndA r D δ₂ ε
          = (r (tbR D σ) - chordEndB r D δ₂ ε)
            + (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) := by abel
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [hW, norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓpos.le, hv, mul_one]
      linarith
    have hx1 : (0 : ℝ) ≤ 1 - ξ := by linarith [hξmem.2]
    have hx2 : (0 : ℝ) ≤ ξ := hξmem.1
    nlinarith [mul_le_mul_of_nonneg_left h1 hx1, mul_le_mul_of_nonneg_left h2 hx2]
  have hcdist : ‖chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε‖ ≤ 2 * ℓ + h / 2 := by
    have key := norm_chartC_sub_chordEndA (r := r) (D := D) (lam := lam) (δ₁ := δ₁)
      (δ₂ := δ₂) (ε := ε) (v := v) hv
    rw [← hh] at key
    have hn0 : |nCoord r D lam δ₁ δ₂ ε v 0| ≤ 2 * ℓ := by
      rw [nCoord]
      have h' := abs_real_inner_le_norm (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v
      rw [hv, mul_one] at h'
      exact le_trans h' hbase
    linarith
  have hR : ‖p - c‖ ≤ R := by
    rw [hRdef, hc]
    have hsplit : p - chartC r D lam δ₁ δ₂ ε v
        = (p - chordEndA r D δ₂ ε)
          + (chordEndA r D δ₂ ε - chartC r D lam δ₁ δ₂ ε v) := by abel
    have hcdist' : ‖chordEndA r D δ₂ ε - chartC r D lam δ₁ δ₂ ε v‖ ≤ 2 * ℓ + h / 2 := by
      rw [norm_sub_rev]; exact hcdist
    calc ‖p - chartC r D lam δ₁ δ₂ ε v‖
        = ‖(p - chordEndA r D δ₂ ε)
            + (chordEndA r D δ₂ ε - chartC r D lam δ₁ δ₂ ε v)‖ := by rw [hsplit]
      _ ≤ ‖p - chordEndA r D δ₂ ε‖ + ‖chordEndA r D δ₂ ε - chartC r D lam δ₁ δ₂ ε v‖ :=
            norm_add_le _ _
      _ ≤ (ℓ + ν) + (2 * ℓ + h / 2) := add_le_add hpdist hcdist'
      _ ≤ 4 * ℓ + h := by linarith [hμdef]
  -- the core
  have hYpos : 0 < Y := by rw [hYdef]; linarith
  have hμ0 : 0 ≤ μ := by rw [hμdef]; linarith
  have hμM : μ ≤ M / 2 := by rw [hμdef]; linarith
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    exact div_pos (by linarith) (by nlinarith [hP])
  have hBp : (p - U) - p = -U := by abel
  have hcore := chordZoneCore (v := v) (e := e) (c := c) (p := p) (B := p - U)
    (c₀ := c₀) (M := M) (μ := μ) (Y := Y) (R := R)
    hv he1 hve hc₀pos hMpos hYpos hμ0 hμM (by rw [hBp]; exact hdir) hpe hR
  rw [hBp] at hcore
  -- the numeric margin
  have hkey : h * ℓ / 16 ≤ Y * (M - μ) - R * μ := by
    have hX : 0 ≤ h * ℓ := by positivity
    have hY4 : h / 4 ≤ Y := by rw [hYdef]; linarith
    have hMl : ℓ / 2 ≤ M - μ := by rw [hμdef]; linarith
    have hμh : μ ≤ h / 512 := by rw [hμdef]; linarith
    have hR6 : R ≤ 6 * ℓ := by rw [hRdef]; linarith
    have h1 : h / 4 * (ℓ / 2) ≤ Y * (M - μ) :=
      mul_le_mul hY4 hMl (by linarith) (by linarith)
    have h1' : h * ℓ / 8 ≤ Y * (M - μ) := by
      have e1 : h / 4 * (ℓ / 2) = h * ℓ / 8 := by ring
      linarith
    have h2 : R * μ ≤ (6 * ℓ) * (h / 512) :=
      mul_le_mul hR6 hμh (by linarith) (by positivity)
    have h2' : R * μ ≤ h * ℓ / 64 := by
      have e2 : 6 * ℓ * (h / 512) = 3 * (h * ℓ) / 256 := by ring
      rw [e2] at h2
      linarith
    linarith
  have hc₀eq : c₀ = 2 / period := by
    rw [eq_div_iff (ne_of_gt hP), hc₀def, div_mul_eq_mul_div,
      mul_div_mul_right (1 - 2 * lam) ((1 : ℝ) / 2 - lam) (ne_of_gt hP)]
    rw [div_eq_iff (by linarith : ((1 : ℝ) / 2 - lam) ≠ 0)]
    ring
  have hfin : h * ℓ / (8 * period) ≤ c₀ * (Y * (M - μ) - R * μ) := by
    rw [hc₀eq]
    have heq : h * ℓ / (8 * period) = (2 / period) * (h * ℓ / 16) := by
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  rw [hloop, hvel]
  exact le_trans hfin hcore


end Work.Drive.H2
