import Mathlib
import Submission.Helpers
import Submission.Work.Drive.chordFrame

/-!
# The thin-crossing theorem for the sweep chamfer

This module isolates, in the chamfer vocabulary of the sweep
(`Work.Drive.sweepLoopChamfer`, `Submission/Work/Drive/chordSweepSmooth.lean`), the **first
quantitative fact about a chamfer crossing**: a crossing of the tail chamfer `[C, D]`
(`C = (1 - lam) • r ta + lam • r tb`, `D = r (ta + lam * (tb - ta))`) with the retained arc forces
the chord `[r ta, r tb]` to be *nearly tangent to the curve at `ta`*, at the scale of the chamfer
depth `lam`:

    ‖π_{(r tb - r ta)}(velocity r ta)‖ ≤ 2 * C * C₀ * lam ,

where `C` is a Lipschitz constant for the velocity of the knot and `C₀` is the localisation
constant of the crossing (`Work.Drive.chamfer_crossing_localized`,
`Submission/Work/Drive/residualSepChain.lean`: `x - ta ≤ C₀ * lam`, or the mirror case, modulo the
period).

## The mechanism (two lines)

Let `n` be the component of `v := velocity r ta` orthogonal to the chord direction, and put
`h (θ) := ⟪r (ta + θ) - r ta, n⟫`.  Two facts:

1. **exact projection of the crossing.**  For *any* `n ⊥ (r tb - r ta)`, the crossing identity
   `r x - r ta = (1 - c) • (lam • (r tb - r ta)) + c • (r (ta + lam*(tb-ta)) - r ta)`
   (`chamfer_crossing_vec`) gives, when paired with `n`,
   `h (x - ta) = c * h (lam * (tb - ta))`;
2. **monotonicity at the scale of the tilt.**  `h '(θ) = ⟪velocity r (ta + θ), n⟫` equals
   `‖n‖ ^ 2` at `θ = 0` (because `n` is the *orthogonal projection* of `v`, `inner_chordTilt_self`)
   and is Lipschitz with constant `C ‖n‖`; hence `h` is strictly increasing on `[0, ξ]` as soon as
   `2 * C * ξ < ‖n‖`.

Since `x - ta ≥ lam * (tb - ta) > 0` and `c < 1`, the identity of 1. contradicts the strict
monotonicity of 2. — *unless* `2 * C * (x - ta) ≥ ‖n‖`, which is the conclusion.

This is the exact shape of the project lead's `E2` remark ("at a thin crossing
`μ_nt = O (K τ / m)`, the same order as `lam ≥ τ / W`"): the quantity `μ_nt` that the corner
half-space argument produces is *not* bounded below uniformly along a crosscut, it is only bounded
below by a constant times `lam` — and this module proves that bound, with explicit constants.

## Consequences recorded here

* `chamfer_crossing_thin_tilt` — the theorem;
* `no_chamfer_crossing_of_tilt_margin` — the corollary: if the tilt is bounded below by `μ > 0`
  (which on a *compact* window of the sweep is automatic by continuity and non-tangency), then for
  `lam ≤ μ / (2 * C * C₀)` the chamfer cannot cross the arc at all: **the standard chamfer separates
  on any window carrying a tilt margin**, with no `havoid` and no trisecant input.  The remaining
  ("thin") configurations are exactly those in which the *fold*/tilt analysis of the lead's `E1`,
  or the OFat fatness input, has to be used.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

variable {r : ℝ → Space}

/-! ## 1. The tilt of a chord -/

/-- **The tilt of the vector `w` relative to the chord `A B`**: the component of `w` orthogonal to
the chord direction.  For `w = velocity r ta` it measures how far the chord `r ta → r tb` is from
being tangent to the curve at `ta`. -/
def chordTilt (A B w : Space) : Space := w - inner ℝ w (chordDir A B) • chordDir A B

lemma chordTilt_def (A B w : Space) :
    chordTilt A B w = w - inner ℝ w (chordDir A B) • chordDir A B := rfl

lemma inner_chordDir_self {A B : Space} (hAB : A ≠ B) :
    inner ℝ (chordDir A B) (chordDir A B) = 1 := by
  rw [real_inner_self_eq_norm_sq, chordDir_norm A B hAB, one_pow]

lemma inner_chordTilt_chordDir {A B : Space} (hAB : A ≠ B) (w : Space) :
    inner ℝ (chordTilt A B w) (chordDir A B) = 0 := by
  rw [chordTilt_def, inner_sub_left, real_inner_smul_left, inner_chordDir_self hAB]
  ring

/-- The tilt is the *orthogonal projection* of `w` onto the plane orthogonal to the chord, so
`⟪chordTilt w, w⟫ = ‖chordTilt w‖ ^ 2`. -/
lemma inner_chordTilt_self {A B : Space} (hAB : A ≠ B) (w : Space) :
    inner ℝ (chordTilt A B w) w = ‖chordTilt A B w‖ ^ 2 := by
  set n : Space := chordTilt A B w with hn
  have hnperp : inner ℝ n (chordDir A B) = 0 := by rw [hn]; exact inner_chordTilt_chordDir hAB w
  have hw : w = n + inner ℝ w (chordDir A B) • chordDir A B := by
    rw [hn, chordTilt_def]; abel
  calc inner ℝ n w
      = inner ℝ n (n + inner ℝ w (chordDir A B) • chordDir A B) := by
          conv_lhs => rw [hw]
    _ = inner ℝ n n + inner ℝ n (inner ℝ w (chordDir A B) • chordDir A B) := by
          rw [inner_add_right]
    _ = ‖n‖ ^ 2 + inner ℝ w (chordDir A B) * inner ℝ n (chordDir A B) := by
          rw [inner_smul_right, real_inner_self_eq_norm_sq]
    _ = ‖n‖ ^ 2 := by rw [hnperp]; ring

/-! ## 2. The crossing identity -/

/-- **The crossing in vector form** (the tail chamfer).  With `C = (1 - lam) • r ta + lam • r tb`
and `D = r (ta + lam*(tb-ta))`, a crossing point `r x = (1 - c) • C + c • D` satisfies the exact
vector identity `r x - r ta = (1 - c) • (lam • (r tb - r ta)) + c • (D - r ta)`. -/
theorem chamfer_crossing_vec {ta tb lam x c : ℝ}
    (hcross : (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta)) = r x) :
    r x - r ta = (1 - c) • (lam • (r tb - r ta)) + c • (r (ta + lam * (tb - ta)) - r ta) := by
  rw [← hcross]
  module

/-! ## 3. Distinct images inside one period -/

/-- **Injectivity modulo the period.**  If `0 < t - s < period` then `r s ≠ r t`. -/
lemma knot_ne_of_sub_mem_Ioo {r : ℝ → Space} (hr : IsSmoothKnot r) {s t : ℝ}
    (h0 : 0 < t - s) (hlt : t - s < period) : r s ≠ r t := by
  intro heq
  have hp : 0 < period := period_pos
  set k : ℤ := ⌊s / period⌋ with hk
  have hf1 : Int.fract (s / period) < 1 := Int.fract_lt_one _
  have hsplit : (k : ℝ) + Int.fract (s / period) = s / period := by
    rw [hk]; exact Int.floor_add_fract (s / period)
  have hs_eq : s = Int.fract (s / period) * period + k * period := by
    have h1 := congrArg (fun y : ℝ => y * period) hsplit
    rw [add_mul, div_mul_cancel₀ s (ne_of_gt hp)] at h1
    linarith
  set s₀ : ℝ := Int.fract (s / period) * period with hs₀
  have hs₀_mem : s₀ ∈ Set.Ico (0 : ℝ) period := by
    refine ⟨by rw [hs₀]; positivity, ?_⟩
    rw [hs₀]
    simpa using mul_lt_mul_of_pos_right hf1 hp
  have hs_per : r s = r s₀ := by
    have h1 : r s = r (s₀ + k * period) := by rw [hs_eq, hs₀]
    rw [h1]
    exact hr.periodic.int_mul k s₀
  have ht_eq : t = s₀ + (t - s) + k * period := by rw [hs_eq]; ring
  have hper : ∀ y : ℝ, r (y + k * period) = r y := fun y => by
    simpa [add_comm] using hr.periodic.int_mul k y
  rcases lt_or_ge (s₀ + (t - s)) period with hcase | hcase
  · have ht_mem : s₀ + (t - s) ∈ Set.Ico (0 : ℝ) period :=
      ⟨by linarith [hs₀_mem.1, h0], hcase⟩
    have hne : s₀ ≠ s₀ + (t - s) := by intro h; linarith [h0]
    have hgoal : r (s₀ + (t - s)) = r s₀ :=
      calc r (s₀ + (t - s)) = r t := by
            conv_rhs => rw [ht_eq]
            exact (hper _).symm
        _ = r s := heq.symm
        _ = r s₀ := hs_per
    exact (hr.image_ne hs₀_mem ht_mem hne) hgoal.symm
  · have ht_mem : s₀ + (t - s) - period ∈ Set.Ico (0 : ℝ) period :=
      ⟨by linarith, by linarith [hs₀_mem.2]⟩
    have hne : s₀ + (t - s) - period ≠ s₀ := by intro h; linarith [h0]
    have hgoal : r (s₀ + (t - s) - period) = r s₀ :=
      calc r (s₀ + (t - s) - period) = r (s₀ + (t - s) - period + period) :=
            (hr.periodic_eq (s₀ + (t - s) - period)).symm
        _ = r (s₀ + (t - s)) := by congr 1; ring
        _ = r t := by
              conv_rhs => rw [ht_eq]
              exact (hper _).symm
        _ = r s := heq.symm
        _ = r s₀ := hs_per
    exact (hr.image_ne ht_mem hs₀_mem hne) hgoal

/-! ## 4. The monotonicity lemma -/

/-- The derivative of `θ ↦ ⟪n, r θ⟫` is `⟪n, velocity r θ⟫`. -/
lemma deriv_inner_knot (hr : IsSmoothKnot r) (n : Space) (x : ℝ) :
    deriv (fun y : ℝ => inner ℝ n (r y)) x = inner ℝ n (velocity r x) := by
  have h1 : HasDerivAt r (velocity r x) x := by
    simpa [velocity] using
      (hr.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun _ : ℝ => n) 0 x := hasDerivAt_const x n
  have h3 := HasDerivAt.inner ℝ h2 h1
  simpa [velocity] using h3.deriv

/-- **Slacked monotonicity.**  If `ν ≤ ⟪n, velocity r θ⟫` on `[a, b]`, then
`ν * (y - x) ≤ ⟪n, r y - r x⟫` for `a ≤ x ≤ y ≤ b`. -/
lemma inner_knot_slack_mono {r : ℝ → Space} (hr : IsSmoothKnot r) {n : Space} {ν a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, ν ≤ inner ℝ n (velocity r x)) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      ν * (y - x) ≤ inner ℝ n (r y - r x) := by
  have hmono : MonotoneOn (fun x : ℝ => inner ℝ n (r x) - ν * x) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?hc ?hd ?hder
    · exact ((continuous_const.inner hr.continuous).sub
        (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      have h1 : HasDerivAt (fun y : ℝ => inner ℝ n (r y)) (inner ℝ n (velocity r x)) x := by
        have := HasDerivAt.inner ℝ (hasDerivAt_const x n)
          ((hr.smooth.differentiable (by simp)).differentiableAt.hasDerivAt)
        simpa [velocity] using this
      exact (h1.sub ((hasDerivAt_id x).const_mul ν)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
      have hd : deriv (fun y : ℝ => inner ℝ n (r y) - ν * y) x
          = inner ℝ n (velocity r x) - ν := by
        have h1 : HasDerivAt (fun y : ℝ => inner ℝ n (r y)) (inner ℝ n (velocity r x)) x := by
          have := HasDerivAt.inner ℝ (hasDerivAt_const x n)
            ((hr.smooth.differentiable (by simp)).differentiableAt.hasDerivAt)
          simpa [velocity] using this
        have h2 : HasDerivAt (fun y : ℝ => ν * y) ν x := by
          simpa using (hasDerivAt_id x).const_mul ν
        exact (h1.sub h2).deriv
      rw [hd]
      linarith [h x hxI]
  intro x hx y hy hxy
  have h1 := hmono hx hy hxy
  simp only at h1
  rw [inner_sub_right]
  linarith

/-! ## 5. The thin-crossing theorem -/

/-- **A chamfer crossing forces a nearly tangent chord.**  There is a constant `K` (twice a
Lipschitz constant for the velocity of the knot) such that, whenever `0 < lam`,
`0 < tb - ta < period`, the crossing point `x ∈ [ta + lam*(tb-ta), tb]` is *localised* at scale
`lam` (`x - ta ≤ C₀ * lam`, the conclusion of `Work.Drive.chamfer_crossing_localized` in the
non-wrap case) and `c < 1` with `r x = (1 - c) • ((1 - lam) • r ta + lam • r tb)
+ c • r (ta + lam*(tb-ta))`, the tilt of the chord at `ta` is at most `K * C₀ * lam`:

    ‖chordTilt (r ta) (r tb) (velocity r ta)‖ ≤ K * C₀ * lam . -/
theorem chamfer_crossing_thin_tilt {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ta tb lam c x C₀ : ℝ),
      0 < lam → 0 < tb - ta → tb - ta < period → c < 1 →
      ta + lam * (tb - ta) ≤ x → x ≤ tb →
      x - ta ≤ C₀ * lam →
      (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta)) = r x →
      ‖chordTilt (r ta) (r tb) (velocity r ta)‖ ≤ K * C₀ * lam := by
  obtain ⟨m, M, C, hm, hM, hC, hspeed, hspeedM, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨2 * C, by positivity, ?_⟩
  intro ta tb lam c x C₀ hlam hw hwper hclt hxlo hxhi hloc hcross
  have hAB : r ta ≠ r tb := knot_ne_of_sub_mem_Ioo hr hw hwper
  set et : ℝ := lam * (tb - ta) with het
  have het_pos : 0 < et := mul_pos hlam hw
  have het_le : et ≤ x - ta := by rw [het]; linarith
  have hxi_nonneg : 0 ≤ x - ta := le_trans het_pos.le het_le
  set n : Space := chordTilt (r ta) (r tb) (velocity r ta) with hn
  have hnn : inner ℝ n (velocity r ta) = ‖n‖ ^ 2 := by
    rw [hn]; exact inner_chordTilt_self hAB (velocity r ta)
  have hC₀pos : 0 < C₀ := by
    have h2 : 0 < C₀ * lam := lt_of_lt_of_le (lt_of_lt_of_le het_pos het_le) hloc
    have h3 : 0 < lam * C₀ := by rwa [mul_comm] at h2
    exact pos_of_mul_pos_right h3 hlam.le

  rcases lt_or_ge (2 * C * (x - ta)) ‖n‖ with hthick | hthin
  · exfalso
    have hnpos : 0 < ‖n‖ := by nlinarith [hC, hxi_nonneg]
    -- the arc functional is bounded below by `‖n‖ ^ 2 / 2` on `[ta, x]`
    have harc : ∀ θ ∈ Set.Icc ta x, ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r θ) := by
      intro θ hθ
      have h1 : inner ℝ n (velocity r θ)
          = inner ℝ n (velocity r ta) + inner ℝ n (velocity r θ - velocity r ta) := by
        rw [inner_sub_right]; ring
      have h2 : ‖velocity r θ - velocity r ta‖ ≤ C * (θ - ta) := by
        have h := hlip θ ta
        have habs : |ta - θ| = θ - ta := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hθ.1])]
        rwa [habs] at h
      have h3 : -(‖n‖ * (C * (θ - ta))) ≤ inner ℝ n (velocity r θ - velocity r ta) := by
        have h4 : |inner ℝ n (velocity r θ - velocity r ta)|
            ≤ ‖n‖ * ‖velocity r θ - velocity r ta‖ := abs_real_inner_le_norm n _
        have h5 : ‖n‖ * ‖velocity r θ - velocity r ta‖ ≤ ‖n‖ * (C * (θ - ta)) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
        linarith [neg_abs_le (inner ℝ n (velocity r θ - velocity r ta))]
      have h4 : C * (θ - ta) ≤ C * (x - ta) := by nlinarith [hC, hθ.2]
      have h5 : ‖n‖ * (C * (θ - ta)) ≤ ‖n‖ ^ 2 / 2 := by
        nlinarith [hnpos, hC, hxi_nonneg, h4]
      linarith [h1, hnn, h3, h5]
    have hslack := inner_knot_slack_mono hr (n := n) (ν := ‖n‖ ^ 2 / 2) (a := ta) (b := x) harc
    have hta_mem : ta ∈ Set.Icc ta x := ⟨le_rfl, by linarith [het_pos]⟩
    have hD_mem : ta + et ∈ Set.Icc ta x := ⟨by linarith, by linarith [het_le]⟩
    have hx_mem : x ∈ Set.Icc ta x := ⟨by linarith [het_pos], le_rfl⟩
    have hDle : ta ≤ ta + et := by linarith
    have hDpos : 0 < inner ℝ n (r (ta + et) - r ta) := by
      have h := hslack ta hta_mem (ta + et) hD_mem hDle
      have h1 : 0 < (‖n‖ ^ 2 / 2) * et := mul_pos (by positivity) het_pos
      linarith [h, h1]
    have htail : 0 ≤ inner ℝ n (r x - r (ta + et)) := by
      have h := hslack (ta + et) hD_mem x hx_mem (by linarith [het_le])
      have h1 : 0 ≤ (‖n‖ ^ 2 / 2) * (x - (ta + et)) :=
        mul_nonneg (by positivity) (by linarith [het_le])
      linarith [h, h1]
    -- the exact scalar form of the crossing
    have hVn : inner ℝ n (r tb - r ta) = 0 := by
      have hsmul : r tb - r ta = ‖r tb - r ta‖ • chordDir (r ta) (r tb) :=
        (chordDir_smul (r ta) (r tb) hAB).symm
      rw [hsmul, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
      ring
    have hscal : inner ℝ n (r x - r ta)
        = c * inner ℝ n (r (ta + et) - r ta) := by
      rw [chamfer_crossing_vec hcross, inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right, hVn, ← het]
      ring
    have hsplit : inner ℝ n (r x - r ta)
        = inner ℝ n (r x - r (ta + et)) + inner ℝ n (r (ta + et) - r ta) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      ring
    nlinarith [hscal, hsplit, hDpos, htail, hclt]
  · calc ‖n‖ ≤ 2 * C * (x - ta) := hthin
      _ ≤ 2 * C * (C₀ * lam) := by nlinarith [hC, hC₀pos, hlam, hloc, hxi_nonneg]
      _ = 2 * C * C₀ * lam := by ring

/-! ## 6. Corollary: a tilt margin excludes the crossing -/

/-- **No chamfer crossing when the chord has a uniform tilt margin.**  If the tilt of the chord is at
least `μ > 0` (on the window under consideration), then for `lam * (K * C₀) < μ` — with `K` the
constant of `chamfer_crossing_thin_tilt` and `C₀` the localisation constant of the crossing — the
tail chamfer cannot meet the retained arc. -/
theorem no_chamfer_crossing_of_tilt_margin {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ C₀ : ℝ), 0 < μ → 0 < C₀ →
      ∀ (ta tb lam c x : ℝ), 0 < lam → lam * (K * C₀) < μ →
        0 < tb - ta → tb - ta < period → c < 1 →
        ta + lam * (tb - ta) ≤ x → x ≤ tb → x - ta ≤ C₀ * lam →
        μ ≤ ‖chordTilt (r ta) (r tb) (velocity r ta)‖ →
        (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta)) = r x →
        False := by
  obtain ⟨K, hK, hmain⟩ := chamfer_crossing_thin_tilt hr
  refine ⟨K, hK, ?_⟩
  intro μ C₀ hμ hC₀ ta tb lam c x hlam hlamμ hw hwper hclt hxlo hxhi hloc hμtilt hcross
  have hthin := hmain ta tb lam c x C₀ hlam hw hwper hclt hxlo hxhi hloc hcross
  nlinarith [hthin, hμtilt, hμ, hC₀, hlam, hK, hlamμ]


/-! ## 7. The mirror: crossings localised at the *head* of the chamfer -/

/-- **A crossing localised near `tb` forces a nearly tangent chord at `tb`.**  This is the mirror of
`chamfer_crossing_thin_tilt`: it covers the second alternative of
`Work.Drive.chamfer_crossing_localized`, in which the crossing point lies within `O(lam)` of `tb`
(equivalently `period - (tb - ta) = O(lam)`, a chord of nearly period length).  Pairing the crossing
with `n := chordTilt (r ta) (r tb) (velocity r tb)` gives, using
`C - r tb = -(1 - lam) * (r tb - r ta) ⟂ n` and the periodicity `r (ta + lam*(tb-ta)) = r (tb + ε)`
with `ε := period - (1 - lam)*(tb - ta) > 0`, the exact identity

    ⟪r x - r tb, n⟫ = c * ⟪r (tb + ε) - r tb, n⟫ .

Here `x ≤ tb` and `ε > 0` lie on *opposite* sides of `tb`, and the functional
`G (θ) := ⟪r (tb + θ) - r tb, n⟫` has `G (0) = 0` and `G' (0) = ‖n‖ ^ 2 > 0`; so `G (x - tb) ≤ 0 <
G (ε)` whenever `G` is strictly increasing on the segment `[x - tb, ε]`, which is a segment of
length `≤ (C₀ + period) * lam`.  Hence the crossing forces
`‖chordTilt (r ta) (r tb) (velocity r tb)‖ ≤ K * (C₀ + period) * lam`. -/
theorem chamfer_crossing_thin_tilt_mirror {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ta tb lam c x C₀ : ℝ),
      0 < lam → 0 < tb - ta → tb - ta < period → 0 < c → c < 1 →
      ta + lam * (tb - ta) ≤ x → x ≤ tb →
      period - (tb - ta) ≤ C₀ * lam → tb - x ≤ C₀ * lam →
      (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta)) = r x →
      ‖chordTilt (r ta) (r tb) (velocity r tb)‖ ≤ K * (C₀ + period) * lam := by
  obtain ⟨m, M, C, hm, hM, hC, hspeed, hspeedM, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨2 * C, by positivity, ?_⟩
  intro ta tb lam c x C₀ hlam hw hwper hcpos hclt hxlo hxhi hwrap hltx hcross
  have hAB : r ta ≠ r tb := knot_ne_of_sub_mem_Ioo hr hw hwper
  set n : Space := chordTilt (r ta) (r tb) (velocity r tb) with hn
  have hnv : inner ℝ n (velocity r tb) = ‖n‖ ^ 2 := by
    rw [hn]; exact inner_chordTilt_self hAB (velocity r tb)
  have hVn : inner ℝ n (r tb - r ta) = 0 := by
    have hsmul : r tb - r ta = ‖r tb - r ta‖ • chordDir (r ta) (r tb) :=
      (chordDir_smul (r ta) (r tb) hAB).symm
    rw [hsmul, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
    ring
  have hC₀pos : 0 < C₀ := by
    have h1 : 0 < C₀ * lam := lt_of_lt_of_le (by linarith [hwper, hwrap]) hwrap
    have h2 : 0 < lam * C₀ := by rwa [mul_comm] at h1
    exact pos_of_mul_pos_right h2 hlam.le
  set Mx : ℝ := (C₀ + period) * lam with hMx
  have hMxpos : 0 < Mx := by
    rw [hMx]
    exact mul_pos (by linarith [hC₀pos, period_pos]) hlam
  have hC₀le : C₀ * lam ≤ Mx := by
    rw [hMx]; nlinarith [hlam, hC₀pos, period_pos]
  rcases lt_or_ge (2 * C * Mx) ‖n‖ with hthick | hthin
  · exfalso
    have hnpos : 0 < ‖n‖ := by nlinarith [hC, hMxpos]
    have harc : ∀ θ ∈ Set.Icc (tb - Mx) (tb + Mx), ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r θ) := by
      intro θ hθ
      have h1 : inner ℝ n (velocity r θ)
          = inner ℝ n (velocity r tb) + inner ℝ n (velocity r θ - velocity r tb) := by
        rw [inner_sub_right]; ring
      have h2 : ‖velocity r θ - velocity r tb‖ ≤ C * Mx := by
        have h := hlip θ tb
        have habs : |tb - θ| ≤ Mx := by
          rw [abs_le]
          exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
        have h3 : C * |tb - θ| ≤ C * Mx := mul_le_mul_of_nonneg_left habs hC.le
        linarith [h, h3]
      have h3 : -(‖n‖ * (C * Mx)) ≤ inner ℝ n (velocity r θ - velocity r tb) := by
        have h4 : |inner ℝ n (velocity r θ - velocity r tb)|
            ≤ ‖n‖ * ‖velocity r θ - velocity r tb‖ := abs_real_inner_le_norm n _
        have h5 : ‖n‖ * ‖velocity r θ - velocity r tb‖ ≤ ‖n‖ * (C * Mx) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
        linarith [neg_abs_le (inner ℝ n (velocity r θ - velocity r tb))]
      have h4 : ‖n‖ * (C * Mx) ≤ ‖n‖ ^ 2 / 2 := by
        nlinarith [hnpos, hC, hMxpos, hthick]
      linarith [h1, hnv, h3, h4]
    have hslack := inner_knot_slack_mono hr (n := n) (ν := ‖n‖ ^ 2 / 2)
      (a := tb - Mx) (b := tb + Mx) harc
    set ep : ℝ := period - (1 - lam) * (tb - ta) with hep
    have hep_pos : 0 < ep := by
      rw [hep]
      nlinarith [hwper, hlam, hw]
    have hep_le : ep ≤ Mx := by
      rw [hep, hMx]
      nlinarith [hwrap, hwper, hlam, hw, period_pos]
    have hx_mem : x ∈ Set.Icc (tb - Mx) (tb + Mx) :=
      ⟨by linarith [hltx, hC₀le], by linarith [hxhi]⟩
    have htb_mem : tb ∈ Set.Icc (tb - Mx) (tb + Mx) := ⟨by linarith [hMxpos], by linarith [hMxpos]⟩
    have htep_mem : tb + ep ∈ Set.Icc (tb - Mx) (tb + Mx) :=
      ⟨by linarith [hep_pos, hMxpos], by linarith [hep_le]⟩
    have h1 : inner ℝ n (r x - r tb) ≤ 0 := by
      have h := hslack x hx_mem tb htb_mem hxhi
      have h' : 0 ≤ (‖n‖ ^ 2 / 2) * (tb - x) := mul_nonneg (by positivity) (by linarith [hxhi])
      rw [inner_sub_right] at h
      rw [inner_sub_right]
      linarith
    have h2 : 0 < inner ℝ n (r (tb + ep) - r tb) := by
      have h := hslack tb htb_mem (tb + ep) htep_mem (by linarith [hep_pos])
      have h' : 0 < (‖n‖ ^ 2 / 2) * ep := mul_pos (by positivity) hep_pos
      linarith [h]
    have hC_id : inner ℝ n ((1 - lam) • r ta + lam • r tb - r tb) = 0 := by
      have hrew : (1 - lam) • r ta + lam • r tb - r tb = (1 - lam) • (r ta - r tb) := by module
      rw [hrew, inner_smul_right]
      have hzero : inner ℝ n (r ta - r tb) = 0 := by
        rw [show r ta - r tb = -(r tb - r ta) by abel, inner_neg_right, hVn, neg_zero]
      rw [hzero, mul_zero]
    have hDper : r (ta + lam * (tb - ta)) = r (tb + ep) := by
      have h1 : ta + lam * (tb - ta) = tb + ep - period := by rw [hep]; ring
      rw [h1]
      have hper := hr.periodic_eq (tb + ep - period)
      rw [show tb + ep - period + period = tb + ep by ring] at hper
      exact hper.symm
    have hid : r x - r tb
        = (1 - c) • ((1 - lam) • r ta + lam • r tb - r tb)
          + c • (r (ta + lam * (tb - ta)) - r tb) := by
      rw [← hcross]
      module
    have hscal : inner ℝ n (r x - r tb) = c * inner ℝ n (r (tb + ep) - r tb) := by
      rw [hid, hDper]
      rw [inner_add_right, inner_smul_right, inner_smul_right, hC_id]
      ring
    nlinarith [h1, h2, hscal, hclt]
  · calc ‖n‖ ≤ 2 * C * Mx := hthin
      _ = 2 * C * (C₀ + period) * lam := by rw [hMx]; ring

end Work.Drive
