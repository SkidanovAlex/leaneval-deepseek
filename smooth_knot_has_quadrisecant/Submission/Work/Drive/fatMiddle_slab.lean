import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.separation_of_far_parameters

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# The fat-middle slab

`Work.Drive.fatMiddle_slab`: for a smooth knot `r₀` there is a `C¹`-neighbourhood radius `ε₁` such
that, for every `ρ > 0`, every knot `r'` that is `ε₁`-close to `r₀` in `C⁰` and `C¹` has all its
*retained fat middles* at parameter-distance `≥ η = η(ρ) > 0` from a single arithmetic progression
`t₀ + ℤ·period`.

The point `t₀` is a point of `r'` of maximal distance from the origin (the *farthest point*).
-/

/-! ## Elementary helpers -/

/-- A continuous function of period `period` is bounded in norm. -/
lemma exists_periodic_norm_bound {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (hper : Function.Periodic f period) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, ‖f t‖ ≤ R := by
  obtain ⟨R, hR⟩ := (hper.isBounded_of_continuous period_pos.ne' hf).exists_norm_le
  exact ⟨max R 0, le_max_right _ _, fun t => le_trans (hR (f t) ⟨t, rfl⟩) (le_max_left _ _)⟩

/-- The velocity of a knot is `period`-periodic. -/
lemma velocity_periodic_of {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Function.Periodic (velocity r) period := by
  have h : (fun s : ℝ => r (s + period)) = r := funext fun s => hr.periodic s
  intro t
  simp only [velocity]
  rw [← deriv_comp_add_const r period t, h]

/-- `round` of a real number of modulus `< 1` is `-1`, `0` or `1`. -/
lemma round_eq_neg_one_or_zero_or_one {u : ℝ} (hu : |u| < 1) :
    round u = -1 ∨ round u = 0 ∨ round u = 1 := by
  have hb : |((round u : ℤ) : ℝ) - u| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round u
  have htri : |((round u : ℤ) : ℝ)| ≤ |((round u : ℤ) : ℝ) - u| + |u| := by
    have h : (((round u : ℤ) : ℝ) - u) + u = ((round u : ℤ) : ℝ) := by ring
    calc |((round u : ℤ) : ℝ)| = |(((round u : ℤ) : ℝ) - u) + u| := by rw [h]
      _ ≤ _ := abs_add_le _ _
  have hlt : |((round u : ℤ) : ℝ)| < 3 / 2 := by linarith
  have hle : ((|round u| : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
    rw [Int.cast_abs]; norm_num; linarith
  have h2 : (|round u| : ℤ) < 2 := Int.cast_lt.mp hle
  have h3 : (|round u| : ℤ) ≤ 1 := by omega
  have h4 : round u ≤ 1 := le_trans (le_abs_self _) h3
  have h5 : -1 ≤ round u := by
    have h := neg_le_abs (round u)
    omega
  omega

/-- A linear lower bound for the norm in the additive circle: if `|z| ∈ [ρ, period - ρ]` then the
class of `z` in `AddCircle period` is at distance at least `ρ` from `0`. -/
lemma le_norm_coe_addCircle {z ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ |z|)
    (h2 : |z| ≤ period - ρ) : ρ ≤ ‖(z : AddCircle period)‖ := by
  have hp : 0 < period := period_pos
  have hzlt : |z| < period := by linarith
  have hzinv : |period⁻¹ * z| < 1 := by
    rw [abs_mul, abs_inv, abs_of_pos hp]
    have h : period⁻¹ * |z| < period⁻¹ * period := mul_lt_mul_of_pos_left hzlt (inv_pos.mpr hp)
    rwa [inv_mul_cancel₀ hp.ne'] at h
  rw [AddCircle.norm_eq]
  rcases round_eq_neg_one_or_zero_or_one hzinv with h | h | h
  · -- `round = -1`
    rw [h]
    have hsub := abs_sub_abs_le_abs_sub (-period) z
    rw [abs_neg, abs_of_pos hp] at hsub
    have hzeq : |(-period) - z| = |z - ((-1 : ℤ) : ℝ) * period| := by
      rw [show ((-1 : ℤ) : ℝ) * period = -period by norm_num]
      rw [abs_sub_comm]
    rw [hzeq] at hsub
    linarith
  · -- `round = 0`
    rw [h, show ((0 : ℤ) : ℝ) * period = 0 by norm_num, sub_zero]
    exact h1
  · -- `round = 1`
    rw [h]
    have hsub := abs_sub_abs_le_abs_sub period z
    rw [abs_of_pos hp] at hsub
    have hzeq : |period - z| = |z - ((1 : ℤ) : ℝ) * period| := by
      rw [show ((1 : ℤ) : ℝ) * period = period by norm_num]
      rw [abs_sub_comm]
    rw [hzeq] at hsub
    linarith

/-- The circular separation is bounded below by linear data. -/
lemma circSep_ge_of_abs_sub {x y ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ |x - y|)
    (h2 : |x - y| ≤ period - ρ) : ρ ≤ circSep x y := by
  have h : circSep x y = ‖((x - y : ℝ) : AddCircle period)‖ := by
    simp only [circSep, dist_eq_norm, ← AddCircle.coe_sub]
  rw [h]
  exact le_norm_coe_addCircle hρ h1 h2

/-! ## Chord identities -/

/-- **Stewart's identity** (squared form) for a point of the affine segment `A + t • (B - A)`. -/
lemma norm_stewart (A B : Space) (t : ℝ) :
    ‖A + t • (B - A)‖ ^ 2 = (1 - t) * ‖A‖ ^ 2 + t * ‖B‖ ^ 2 - t * (1 - t) * ‖B - A‖ ^ 2 := by
  have hPt : ‖A + t • (B - A)‖ ^ 2
      = ‖A‖ ^ 2 + 2 * t * inner ℝ A (B - A) + t ^ 2 * ‖B - A‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hB : ‖B‖ ^ 2 = ‖A‖ ^ 2 + 2 * inner ℝ A (B - A) + ‖B - A‖ ^ 2 := by
    have h := norm_add_sq_real A (B - A)
    rw [show A + (B - A) = B by abel] at h
    exact h
  have key : ‖A‖ ^ 2 + 2 * t * inner ℝ A (B - A) + t ^ 2 * ‖B - A‖ ^ 2
      = (1 - t) * ‖A‖ ^ 2 + t * ‖B‖ ^ 2 - t * (1 - t) * ‖B - A‖ ^ 2 := by
    linear_combination (-t) * hB
  linarith [hPt, key]

/-- The product of the two chord sub-lengths of a point of the open segment. -/
lemma norm_sub_mul_norm_sub (A B : Space) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ‖A - (A + θ • (B - A))‖ * ‖(A + θ • (B - A)) - B‖ = θ * (1 - θ) * ‖B - A‖ ^ 2 := by
  have h1 : A - (A + θ • (B - A)) = (-θ) • (B - A) := by module
  have h2 : (A + θ • (B - A)) - B = (θ - 1) • (B - A) := by module
  rw [h1, h2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_neg (by linarith), abs_of_neg (by linarith)]
  ring

/-- The first-order deficit of the modulus at a chord point: if `‖y‖ ≤ ‖x‖` then
`‖x‖² - ‖y‖² ≤ 2 ‖x‖ ‖x - y‖`. -/
lemma norm_sq_sub_sq_le {x y : Space} (hy : ‖y‖ ≤ ‖x‖) :
    ‖x‖ ^ 2 - ‖y‖ ^ 2 ≤ 2 * ‖x‖ * ‖x - y‖ := by
  have hfac : ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ + ‖y‖) * (‖x‖ - ‖y‖) := by ring
  have h1 : ‖x‖ + ‖y‖ ≤ 2 * ‖x‖ := by linarith [norm_nonneg x]
  have h2 : 0 ≤ ‖x‖ - ‖y‖ := sub_nonneg.mpr hy
  have h3 : 0 ≤ 2 * ‖x‖ := by positivity
  have h4 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
    have h := abs_norm_sub_norm_le x y
    rw [abs_le] at h
    exact h.2
  rw [hfac]
  exact mul_le_mul h1 h4 h2 h3

/-- **A retained middle lies strictly inside the ball of radius the farthest distance.**  If `P` is
a point of the open segment `[A,B]` at distance at least `δ` from both endpoints, and both endpoints
are at distance at most `Mx` from the origin, then `‖P‖² ≤ Mx² - δ²`. -/
lemma chord_deficit {A B P : Space} {θ δ Mx : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hP : A + θ • (B - A) = P) (hAnorm : ‖A‖ ≤ Mx) (hBnorm : ‖B‖ ≤ Mx)
    (hδA : δ ≤ ‖A - P‖) (hδB : δ ≤ ‖P - B‖) : ‖P‖ ^ 2 ≤ Mx ^ 2 - δ ^ 2 := by
  have hstew := norm_stewart A B θ
  rw [hP] at hstew
  have hprod := norm_sub_mul_norm_sub A B hθ hθ1
  rw [hP] at hprod
  have hprodge : δ * δ ≤ ‖A - P‖ * ‖P - B‖ :=
    mul_le_mul hδA hδB hδ.le (norm_nonneg _)
  have hprodge' : δ ^ 2 ≤ ‖A - P‖ * ‖P - B‖ := by simpa [pow_two] using hprodge
  have hkey : ‖P‖ ^ 2 = (1 - θ) * ‖A‖ ^ 2 + θ * ‖B‖ ^ 2 - ‖A - P‖ * ‖P - B‖ := by
    rw [hstew, hprod]
  have ha2 : ‖A‖ ^ 2 ≤ Mx ^ 2 := by
    have := norm_nonneg A; nlinarith
  have hb2 : ‖B‖ ^ 2 ≤ Mx ^ 2 := by
    have := norm_nonneg B; nlinarith
  have hup : (1 - θ) * ‖A‖ ^ 2 + θ * ‖B‖ ^ 2 ≤ Mx ^ 2 := by nlinarith
  nlinarith [hkey, hup, hprodge']

/-- The final arithmetic of the slab: from `δ² ≤ 2 Mx L z`, `Mx ≤ M̄`, all constants positive,
`z > δ² / (4 M̄ L)`. -/
lemma slab_estimate {δ Mx Mbar L z : ℝ} (hδ : 0 < δ) (hMx : 0 < Mx) (hMbar : 0 < Mbar)
    (hMxle : Mx ≤ Mbar) (hL : 0 < L) (hz : δ ^ 2 ≤ (2 * (Mx * L)) * z) :
    δ ^ 2 / (4 * (Mbar * L)) < z := by
  have h1 : 0 < 2 * (Mx * L) := by positivity
  have h2 : δ ^ 2 / (2 * (Mx * L)) ≤ z := by
    rw [div_le_iff₀ h1, mul_comm]
    exact hz
  have h3 : δ ^ 2 / (2 * (Mbar * L)) ≤ δ ^ 2 / (2 * (Mx * L)) := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [hMxle, hL]
  have h4 : δ ^ 2 / (4 * (Mbar * L)) < δ ^ 2 / (2 * (Mbar * L)) := by
    have hpos : 0 < δ ^ 2 / (2 * (Mbar * L)) := by positivity
    have heq : δ ^ 2 / (4 * (Mbar * L)) = δ ^ 2 / (2 * (Mbar * L)) / 2 := by
      field_simp
      ring
    rw [heq]
    linarith
  linarith [h2, h3, h4]

/-! ## The main theorem -/

theorem fatMiddle_slab
    {r₀ : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr₀ : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r₀) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ η : ℝ, 0 < η ∧
        ∀ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
          LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' →
          (∀ t : ℝ, ‖r' t - r₀ t‖ < ε₁ ∧
            ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
              LeanEval.KnotTheory.Quadrisecant.velocity r₀ t‖ < ε₁) →
          ∃ t₀ : ℝ, ∀ u : ℝ, Work.Drive.FatMiddle r' ρ u →
            ∀ k : ℤ, η < |u - (t₀ + (k : ℝ) * LeanEval.KnotTheory.Quadrisecant.period)| := by
  obtain ⟨εs, hεspos, hsep⟩ := separation_of_far_parameters hr₀
  obtain ⟨M₀, hM₀nn, hM₀⟩ := exists_periodic_norm_bound hr₀.continuous hr₀.periodic
  obtain ⟨L₀, hL₀nn, hL₀⟩ :=
    exists_periodic_norm_bound (hr₀.smooth.continuous_deriv (by simp)) (velocity_periodic_of hr₀)
  refine ⟨min (εs / 2) (1 / 2), lt_min (by linarith) (by norm_num), ?_⟩
  intro ρ hρ
  obtain ⟨δ, hδpos, hδ⟩ := hsep ρ hρ
  set Mbar : ℝ := M₀ + 1 with hMbardef
  set L : ℝ := L₀ + 1 with hLdef
  have hMbarpos : 0 < Mbar := by rw [hMbardef]; linarith
  have hLpos : 0 < L := by rw [hLdef]; linarith
  refine ⟨δ ^ 2 / (4 * (Mbar * L)), by positivity, ?_⟩
  intro r' hr' hclose
  have he₁ : min (εs / 2) (1 / 2) ≤ εs := by
    have := min_le_left (εs / 2) (1 / 2); linarith
  have he₂ : min (εs / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hclose' : ∀ t : ℝ, ‖r' t - r₀ t‖ < εs ∧ ‖velocity r' t - velocity r₀ t‖ < εs := fun t =>
    ⟨lt_of_lt_of_le (hclose t).1 he₁, lt_of_lt_of_le (hclose t).2 he₁⟩
  have hsepr := hδ r' hr' hclose'
  -- global velocity bound for `r'`
  have hvel : ∀ t : ℝ, ‖velocity r' t‖ ≤ L := by
    intro t
    have h1 : ‖velocity r' t - velocity r₀ t‖ < 1 / 2 := lt_of_lt_of_le (hclose t).2 he₂
    have h2 : ‖velocity r₀ t‖ ≤ L₀ := hL₀ t
    have h3 : ‖velocity r' t‖ ≤ ‖velocity r₀ t‖ + ‖velocity r' t - velocity r₀ t‖ := by
      have h := norm_add_le (velocity r₀ t) (velocity r' t - velocity r₀ t)
      rwa [add_sub_cancel] at h
    rw [hLdef]; linarith
  have hlip : ∀ s t : ℝ, ‖r' t - r' s‖ ≤ L * |t - s| :=
    norm_sub_le_of_velocity_bound hr'.smooth hvel
  -- the farthest point
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) period)
    ⟨0, le_rfl, period_pos.le⟩ (hr'.continuous.norm.continuousOn)
  refine ⟨t₀, ?_⟩
  set Mx : ℝ := ‖r' t₀‖ with hMxdef
  have hMxnn : 0 ≤ Mx := by rw [hMxdef]; exact norm_nonneg _
  have hMxle : Mx ≤ Mbar := by
    have h1 : ‖r' t₀‖ ≤ ‖r₀ t₀‖ + ‖r' t₀ - r₀ t₀‖ := by
      have h := norm_add_le (r₀ t₀) (r' t₀ - r₀ t₀)
      rwa [add_sub_cancel] at h
    have h2 : ‖r' t₀ - r₀ t₀‖ < 1 / 2 := lt_of_lt_of_le (hclose t₀).1 he₂
    have h3 : ‖r₀ t₀‖ ≤ M₀ := hM₀ t₀
    rw [hMxdef, hMbardef]; linarith
  -- every knot point is at distance at most `Mx`
  have harg : ∀ z : ℝ, ‖r' z‖ ≤ Mx := by
    intro z
    obtain ⟨z', hz', hze⟩ := hr'.periodic.exists_mem_Ico period_pos z 0
    have hmem : z' ∈ Set.Icc (0 : ℝ) period := ⟨hz'.1, by linarith [hz'.2]⟩
    calc ‖r' z‖ = ‖r' z'‖ := by rw [hze]
      _ ≤ ‖r' t₀‖ := hmax hmem
      _ = Mx := rfl
  intro u hu k
  obtain ⟨a, y, hy0, hyP, hu1, hu2, hu3⟩ := hu
  rw [openSegment_eq_image'] at hu3
  obtain ⟨θ, hθ, hθeq⟩ := hu3
  have hθeq' : r' a + θ • (r' (a + y) - r' a) = r' u := hθeq
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < 1 := hθ.2
  -- the two chord distances are bounded below by `δ(ρ)`
  have hsepA : δ ≤ ‖r' u - r' a‖ := by
    have hcirc : ρ ≤ circSep u a := by
      refine circSep_ge_of_abs_sub hρ ?_ ?_
      · rw [abs_of_nonneg (by linarith [hu1])]; linarith [hu1]
      · rw [abs_of_nonneg (by linarith [hu1])]; linarith [hyP]
    have h := hsepr (u : AddCircle period) (a : AddCircle period) hcirc
    rwa [knotMap_eq_of_periodic hr'.periodic u, knotMap_eq_of_periodic hr'.periodic a] at h
  have hsepB : δ ≤ ‖r' u - r' (a + y)‖ := by
    have hcirc : ρ ≤ circSep u (a + y) := by
      refine circSep_ge_of_abs_sub hρ ?_ ?_
      · rw [abs_of_nonpos (by linarith [hu2])]; linarith [hu2]
      · rw [abs_of_nonpos (by linarith [hu2])]; linarith [hyP]
    have h := hsepr (u : AddCircle period) ((a + y) : AddCircle period) hcirc
    simp only [← AddCircle.coe_add] at h
    rwa [knotMap_eq_of_periodic hr'.periodic u, knotMap_eq_of_periodic hr'.periodic (a + y)] at h
  have hsepA' : δ ≤ ‖r' a - r' u‖ := by rwa [norm_sub_rev] at hsepA
  -- the chord point is strictly inside the ball of radius `Mx`
  have hbound : ‖r' u‖ ^ 2 ≤ Mx ^ 2 - δ ^ 2 :=
    chord_deficit hθ0 hθ1 hδpos hθeq' (harg a) (harg (a + y)) hsepA' hsepB
  have hMxpos : 0 < Mx := by
    have h1 : δ ^ 2 ≤ Mx ^ 2 := by nlinarith [hbound, norm_nonneg (r' u)]
    nlinarith [h1, hδpos, hMxnn]
  -- the deficit is controlled by the distance to `t₀`
  have hdef2 : Mx ^ 2 - ‖r' u‖ ^ 2 ≤ 2 * Mx * ‖r' t₀ - r' u‖ := by
    have h := norm_sq_sub_sq_le (x := r' t₀) (y := r' u) (by have := harg u; rwa [hMxdef] at this)
    rw [hMxdef]
    exact h
  have hdef : δ ^ 2 ≤ Mx ^ 2 - ‖r' u‖ ^ 2 := by linarith
  have hdef3 : δ ^ 2 ≤ 2 * Mx * ‖r' t₀ - r' u‖ := le_trans hdef hdef2
  -- periodicity and the Lipschitz bound
  have hperk : r' (t₀ + (k : ℝ) * period) = r' t₀ := by
    have h := hr'.periodic.int_mul k t₀
    simpa [zsmul_eq_mul] using h
  have hlipk : ‖r' t₀ - r' u‖ ≤ L * |u - (t₀ + (k : ℝ) * period)| := by
    have h := hlip (t₀ + (k : ℝ) * period) u
    rw [hperk, norm_sub_rev] at h
    exact h
  have hfin : δ ^ 2 ≤ (2 * (Mx * L)) * |u - (t₀ + (k : ℝ) * period)| := by
    have hstep : (2 * Mx) * ‖r' t₀ - r' u‖
        ≤ (2 * Mx) * (L * |u - (t₀ + (k : ℝ) * period)|) :=
      mul_le_mul_of_nonneg_left hlipk (by positivity)
    have h2 : δ ^ 2 ≤ (2 * Mx) * (L * |u - (t₀ + (k : ℝ) * period)|) := le_trans hdef3 hstep
    have h3 : (2 * Mx) * (L * |u - (t₀ + (k : ℝ) * period)|)
        = (2 * (Mx * L)) * |u - (t₀ + (k : ℝ) * period)| := by ring
    rwa [h3] at h2
  exact slab_estimate hδpos hMxpos hMbarpos hMxle hLpos hfin

end Work.Drive
