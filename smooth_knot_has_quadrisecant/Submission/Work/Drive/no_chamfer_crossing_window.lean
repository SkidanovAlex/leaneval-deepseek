import Mathlib
import Submission.Work.Drive.chamferCrossingThin
import Submission.Work.Drive.chamferSepAux

/-!
# No chamfer crossing on a compact window carrying a non-tangency margin

The theorem `Work.Drive.no_chamfer_crossing_window` (statement below, unchanged) is proved here.

The mechanism is the one recorded in `chamferCrossingThin.lean`, made uniform over a compact
window:

* the crossing identity gives an exact scalar identity for *any* functional vanishing on the
  chord: with `n := chordTilt (r ta) (r tb) (velocity r ta)` and `g (θ) := ⟪r (ta + θ) - r ta, n⟫`,
  a crossing at the parameter `x` forces `g (x - ta) = c * g (ξ)` with `ξ = lam * (tb - ta)`;
* the crossing also bounds `‖r x - r ta‖ ≤ 2 * M * period * lam`, so that `x` is within `C * lam` of
  `ta` *or* within `C * lam` of `ta + period` (the global `knot_bounds` of `chamferSepAux.lean`
  gives the two-sided injectivity modulus); this is the localisation;
* in the first case the thin-crossing theorem `chamfer_crossing_thin_tilt` forces the tilt
  `‖n‖ ≤ K * C * lam`, contradicting the uniform tilt margin `μ > 0` supplied by the compactness of
  `[a,b]` together with the non-tangency hypothesis `hnt`;
* in the second case `g (-e) = c * g (ξ)` with `e = period - (x - ta) ∈ (0, C * lam]`, and both
  `-e` and `ξ` lie in the window on which `g` is strictly increasing (`g' ≥ ‖n‖ ^ 2 / 2 > 0`, the
  quantitative form of `g' (0) = ‖n‖ ^ 2`), so the left side is negative and the right side positive.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

variable {r : ℝ → Space}

/-! ## 1. Elementary helpers -/

/-- **A global Lipschitz constant for a smooth knot**, from the global upper bound on its speed.
-/
lemma exists_curve_lipschitz {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ M : ℝ, 0 < M ∧ ∀ s t : ℝ, ‖r s - r t‖ ≤ M * |s - t| := by
  obtain ⟨m, M, C, hm, hM, hC, hspeed, hspeedM, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨M, hM, ?_⟩
  intro s t
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ r x :=
    fun x _ => (hr.smooth.differentiable (by simp)) x
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv r x‖ ≤ M :=
    fun x _ => by simpa [velocity] using hspeedM x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := r) (s := Set.univ) (x := s) (y := t)
    (C := M) hdiff hderiv convex_univ (Set.mem_univ s) (Set.mem_univ t)
  rw [Real.norm_eq_abs, abs_sub_comm] at h
  rwa [norm_sub_rev]

/-- The tilt `chordTilt A B w` vanishes only if the chord `B - A` is parallel to `w`. -/
lemma chordTilt_ne_zero_of_not_smul {A B w : Space} (hAB : A ≠ B) (hw : w ≠ 0)
    (h : ∀ m : ℝ, B - A ≠ m • w) : chordTilt A B w ≠ 0 := by
  intro h0
  have hwdecomp : w = inner ℝ w (chordDir A B) • chordDir A B := by
    have h1 : w - inner ℝ w (chordDir A B) • chordDir A B = 0 := by
      rw [← chordTilt_def, h0]
    exact sub_eq_zero.mp h1
  have hc : inner ℝ w (chordDir A B) ≠ 0 := by
    intro hc0
    exact hw (by rw [hwdecomp, hc0, zero_smul])
  have hu : chordDir A B = (inner ℝ w (chordDir A B))⁻¹ • w := by
    have h1 := congrArg (fun z : Space => (inner ℝ w (chordDir A B))⁻¹ • z) hwdecomp
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
    exact h1.symm
  refine h (‖B - A‖ * (inner ℝ w (chordDir A B))⁻¹) ?_
  have hfinal : ‖B - A‖ • chordDir A B
      = (‖B - A‖ * (inner ℝ w (chordDir A B))⁻¹) • w := by
    conv_lhs => rw [hu]
    rw [smul_smul]
  exact (chordDir_smul A B hAB).symm.trans hfinal

/-- **Uniform tilt margin on a compact window.**  If the chord `[r (ta s), r (tb s)]` is never
parallel to the velocity at `ta s` on `[a, b]`, then the norm of the tilt is bounded below by a
positive constant on `[a, b]` (continuity and compactness). -/
lemma exists_tilt_margin {r : ℝ → Space} (hr : IsSmoothKnot r) (ta tb : ℝ → ℝ)
    (hta : Continuous ta) (htb : Continuous tb) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ s ∈ Set.Icc a b, 0 < tb s - ta s ∧ tb s - ta s < period)
    (hnt : ∀ s ∈ Set.Icc a b, ∀ m : ℝ, r (tb s) - r (ta s) ≠ m • velocity r (ta s)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ s ∈ Set.Icc a b,
      μ ≤ ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖ := by
  have hrc : Continuous r := hr.continuous
  have hvc : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hAB : ∀ s ∈ Set.Icc a b, r (ta s) ≠ r (tb s) := fun s hs =>
    knot_ne_of_sub_mem_Ioo hr (hpos s hs).1 (hpos s hs).2
  have hdel : ContinuousOn (fun s => r (tb s) - r (ta s)) (Set.Icc a b) :=
    ((hrc.comp htb).sub (hrc.comp hta)).continuousOn
  have hnorm : ContinuousOn (fun s => ‖r (tb s) - r (ta s)‖) (Set.Icc a b) := hdel.norm
  have hinv : ContinuousOn (fun s => (‖r (tb s) - r (ta s)‖)⁻¹) (Set.Icc a b) :=
    hnorm.inv₀ (fun s hs => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hAB s hs))))
  have hcd : ContinuousOn (fun s => chordDir (r (ta s)) (r (tb s))) (Set.Icc a b) := by
    show ContinuousOn (fun s => (‖r (tb s) - r (ta s)‖)⁻¹ • (r (tb s) - r (ta s))) (Set.Icc a b)
    exact hinv.smul hdel
  have hv : ContinuousOn (fun s => velocity r (ta s)) (Set.Icc a b) := (hvc.comp hta).continuousOn
  have hinner : ContinuousOn
      (fun s => inner ℝ (velocity r (ta s)) (chordDir (r (ta s)) (r (tb s)))) (Set.Icc a b) :=
    hv.inner hcd
  have htilt : ContinuousOn
      (fun s => chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))) (Set.Icc a b) := by
    show ContinuousOn (fun s => velocity r (ta s)
      - inner ℝ (velocity r (ta s)) (chordDir (r (ta s)) (r (tb s)))
        • chordDir (r (ta s)) (r (tb s))) (Set.Icc a b)
    exact hv.sub (hinner.smul hcd)
  have hF : ContinuousOn
      (fun s => ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖) (Set.Icc a b) :=
    htilt.norm
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hF
  refine ⟨‖chordTilt (r (ta s₀)) (r (tb s₀)) (velocity r (ta s₀))‖, ?_, fun s hs => hmin hs⟩
  exact norm_pos_iff.mpr
    (chordTilt_ne_zero_of_not_smul (hAB s₀ hs₀) (hr.regular (ta s₀)) (hnt s₀ hs₀))

/-! ## 2. The theorem -/

/-- **The head case of the localisation.**  Let `A`, `B` be the chord endpoints, `x` the crossing
point with `x - period = A - e`, and let `ξ` be the chamfer parameter.  If the crossing holds in
vector form and `2 κ e ≤ μ`, `2 κ ξ ≤ μ` with `μ` a lower bound for the tilt and `κ` a Lipschitz
constant for the velocity, then `g (-e) = c * g (ξ)` where `g` is the tilt functional; both `-e` and
`ξ` lie in the window on which `g` is strictly increasing, so the left side is negative and the right
side positive — a contradiction. -/
lemma no_crossing_head {r : ℝ → Space} (hr : IsSmoothKnot r)
    {A B x ξ e c μ κ lam : ℝ} (hκ : 0 < κ) (hμpos : 0 < μ) (hc : 0 < c)
    (hAB : r A ≠ r B)
    (hμle : μ ≤ ‖chordTilt (r A) (r B) (velocity r A)‖)
    (hκlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ κ * |t' - t|)
    (hper : r (x - period) = r x) (hAe : A - e = x - period)
    (he : 0 < e) (hξ : 0 < ξ) (heμ : e * (2 * κ) ≤ μ) (hξμ : ξ * (2 * κ) ≤ μ)
    (hvec : r x - r A = (1 - c) • (lam • (r B - r A)) + c • (r (A + ξ) - r A)) : False := by
  set N : Space := chordTilt (r A) (r B) (velocity r A) with hNdef
  have hNpos : 0 < ‖N‖ := lt_of_lt_of_le hμpos hμle
  have hNν : 0 < ‖N‖ ^ 2 / 2 := div_pos (pow_pos hNpos 2) (by norm_num)
  have hperp : inner ℝ N (r B - r A) = 0 := by
    have hsmul : r B - r A = ‖r B - r A‖ • chordDir (r A) (r B) :=
      (chordDir_smul (r A) (r B) hAB).symm
    rw [hsmul, inner_smul_right, hNdef, inner_chordTilt_chordDir hAB]
    ring
  have hself : inner ℝ N (velocity r A) = ‖N‖ ^ 2 := by
    rw [hNdef]; exact inner_chordTilt_self hAB (velocity r A)
  have hscal : inner ℝ N (r x - r A) = c * inner ℝ N (r (A + ξ) - r A) := by
    rw [hvec, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right, hperp]
    ring
  have hmem : ∀ y ∈ Set.Icc (A - e) (A + ξ), ‖N‖ ^ 2 / 2 ≤ inner ℝ N (velocity r y) := by
    intro y hy
    have hy1 : A - e ≤ y := hy.1
    have hy2 : y ≤ A + ξ := hy.2
    have hden : 0 < 2 * κ := by positivity
    have he' : e ≤ μ / (2 * κ) := (le_div_iff₀ hden).mpr heμ
    have hξ' : ξ ≤ μ / (2 * κ) := (le_div_iff₀ hden).mpr hξμ
    have hyabs : |y - A| ≤ ‖N‖ / (2 * κ) := by
      have h3 : |y - A| ≤ μ / (2 * κ) := by
        rw [abs_le]
        exact ⟨by linarith [hy1, he'], by linarith [hy2, hξ']⟩
      have h4 : μ / (2 * κ) ≤ ‖N‖ / (2 * κ) :=
        div_le_div_of_nonneg_right hμle hden.le
      linarith [h3, h4]
    have herr : |inner ℝ N (velocity r y - velocity r A)| ≤ ‖N‖ * (κ * |y - A|) := by
      refine le_trans (abs_real_inner_le_norm N _) ?_
      have h1 : ‖velocity r y - velocity r A‖ ≤ κ * |y - A| := by
        have h := hκlip y A
        rwa [abs_sub_comm] at h
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg N)
    have hkey : ‖N‖ * (κ * |y - A|) ≤ ‖N‖ ^ 2 / 2 := by
      have h6 : |y - A| * (2 * κ) ≤ ‖N‖ := (le_div_iff₀ hden).mp hyabs
      have h7 : ‖N‖ * (|y - A| * (2 * κ)) ≤ ‖N‖ * ‖N‖ :=
        mul_le_mul_of_nonneg_left h6 (norm_nonneg N)
      nlinarith [h7, hκ, norm_nonneg N]
    have hdecomp : inner ℝ N (velocity r y) - ‖N‖ ^ 2
        = inner ℝ N (velocity r y - velocity r A) := by
      rw [inner_sub_right, hself]
    linarith [hdecomp, neg_abs_le (inner ℝ N (velocity r y - velocity r A)), herr, hkey]
  have hslack := inner_knot_slack_mono hr (n := N) (ν := ‖N‖ ^ 2 / 2)
    (a := A - e) (b := A + ξ) hmem
  have hm1 : A - e ∈ Set.Icc (A - e) (A + ξ) := ⟨le_rfl, by linarith⟩
  have hm2 : A ∈ Set.Icc (A - e) (A + ξ) := ⟨by linarith, by linarith⟩
  have hm3 : A + ξ ∈ Set.Icc (A - e) (A + ξ) := ⟨by linarith, le_rfl⟩
  have hneg : inner ℝ N (r x - r A) < 0 := by
    have h0 := hslack (A - e) hm1 A hm2 (by linarith)
    have h1 : A - (A - e) = e := by ring
    rw [h1, hAe, hper, inner_sub_right] at h0
    have h3 : 0 < (‖N‖ ^ 2 / 2) * e := mul_pos hNν he
    have h4 : -inner ℝ N (r x - r A) = inner ℝ N (r A) - inner ℝ N (r x) := by
      rw [inner_sub_right]; ring
    linarith [h0, h3, h4]
  have hpos : 0 < inner ℝ N (r (A + ξ) - r A) := by
    have h0 := hslack A hm2 (A + ξ) hm3 (by linarith)
    have h1 : A + ξ - A = ξ := by ring
    rw [h1] at h0
    have h3 : 0 < (‖N‖ ^ 2 / 2) * ξ := mul_pos hNν hξ
    linarith [h0, h3]
  have hcontra : 0 < c * inner ℝ N (r (A + ξ) - r A) := mul_pos hc hpos
  linarith [hscal, hneg, hcontra]

/-- **No chamfer crossing on a compact window carrying a non-tangency margin.**  Let `ta`, `tb` be a
continuous family of chord endpoints over the compact window `[a,b]` with `0 < tb s - ta s < period`
and with the chord *never parallel to the velocity at its left endpoint* (`SweepNonTangent` in the
vocabulary of `Submission/Work/Drive/sweepNonTangentDefs.lean`).  Then there is `L > 0` such that for
every `lam ∈ (0, L]` and every crossing point `x ∈ [ta s + lam*(tb s - ta s), tb s]` with
`0 < c < 1`, `r x = (1 - c) • ((1 - lam) • r (ta s) + lam • r (tb s)) + c • r (ta s + lam * (tb s -
ta s))` forces the degenerate value `x = ta s + lam * (tb s - ta s)` (where the two sides agree for
every `c`, since the chamfer endpoint `D = r (ta + lam*(tb-ta))` is a point of the arc).

This is the `havoid`-free, *non-tangent* form of the corner-separation statements
(`Submission/Work/Drive/_stubSep.lean`), and it is what the chord sweep of the `OFat` lane
(`StripCrosscutAvoidingOFat` avoids the tangency set `TCset`) consumes.  Its local inputs are

* the proved thin-crossing theorem `Work.Drive.chamfer_crossing_thin_tilt`
  (`Submission/Work/Drive/chamferCrossingThin.lean`): a crossing with `c < 1` and
  `x - ta ≤ C₀ * lam` forces `‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖ ≤ K * C₀ * lam`;
* compactness: on `[a,b]` the tilt `s ↦ ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖`
  is continuous and pointwise nonzero by `hnt`, hence bounded below by `μ > 0`; so
  `lam < μ / (K * C₀)` rules the crossing out;
* the localisation `Work.Drive.chamfer_crossing_localized` (`residualSepChain.lean`) and its
  *mirror* at the right endpoint `tb` (the crossing point can instead be localised near
  `ta + period`, i.e. at the head of a nearly-period-long chord; this is the mirror statement with
  `chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))`). -/
theorem no_chamfer_crossing_window
    {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (ta tb : ℝ → ℝ) (hta : Continuous ta) (htb : Continuous tb)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hpos : ∀ s ∈ Set.Icc a b, 0 < tb s - ta s ∧ tb s - ta s < LeanEval.KnotTheory.Quadrisecant.period)
    (hnt : ∀ s ∈ Set.Icc a b, ∀ m : ℝ,
      r (tb s) - r (ta s) ≠ m • LeanEval.KnotTheory.Quadrisecant.velocity r (ta s)) :
    ∃ L : ℝ, 0 < L ∧ ∀ (lam x c : ℝ), 0 < lam → lam ≤ L → 0 < c → c < 1 →
      ∀ s ∈ Set.Icc a b,
        ta s + lam * (tb s - ta s) ≤ x → x ≤ tb s →
        (1 - c) • ((1 - lam) • r (ta s) + lam • r (tb s))
            + c • r (ta s + lam * (tb s - ta s)) = r x →
        x = ta s + lam * (tb s - ta s) := by
  obtain ⟨m, δ, sep, hm, hδ, hsep, hspeed, hnear, hfar⟩ := knot_bounds hr
  obtain ⟨Mc, hMc, hcurveLip⟩ := exists_curve_lipschitz hr
  obtain ⟨m₂, M₂, κ, hm₂, hM₂, hκ, hspeed₂, hspeedM₂, hκlip⟩ := exists_knot_c2_bounds hr
  obtain ⟨K, hK, hthin⟩ := chamfer_crossing_thin_tilt hr
  obtain ⟨μ, hμpos, hμ⟩ := exists_tilt_margin hr ta tb hta htb hab.le hpos hnt
  have hp : 0 < period := period_pos
  obtain ⟨Cloc, hClocdef⟩ : ∃ C : ℝ, C = 4 * Mc * period / m := ⟨_, rfl⟩
  have hClocpos : 0 < Cloc := by rw [hClocdef]; exact div_pos (by positivity) hm
  refine ⟨min (min (sep / (4 * Mc * period)) (μ / (2 * K * Cloc)))
      (μ / (2 * κ * (Cloc + period))), ?_, ?_⟩
  · refine lt_min (lt_min ?_ ?_) ?_
    · exact div_pos hsep (by positivity)
    · exact div_pos hμpos (by positivity)
    · exact div_pos hμpos (by positivity)
  · intro lam x c hlam hlamL hc0 hc1 s hs hxlo hxhi hcross
    have hL1 : lam ≤ sep / (4 * Mc * period) :=
      le_trans hlamL (le_trans (min_le_left _ _) (min_le_left _ _))
    have hL2 : lam ≤ μ / (2 * K * Cloc) :=
      le_trans hlamL (le_trans (min_le_left _ _) (min_le_right _ _))
    have hL3 : lam ≤ μ / (2 * κ * (Cloc + period)) := le_trans hlamL (min_le_right _ _)
    have hw_pos : 0 < tb s - ta s := (hpos s hs).1
    have hw_lt : tb s - ta s < period := (hpos s hs).2
    have hAB : r (ta s) ≠ r (tb s) := knot_ne_of_sub_mem_Ioo hr hw_pos hw_lt
    set ξ : ℝ := lam * (tb s - ta s) with hξdef
    have hξ_pos : 0 < ξ := by rw [hξdef]; exact mul_pos hlam hw_pos
    have hξ_lt : ξ < period := by rw [hξdef]; linarith
    have hξ_le : ξ ≤ period * lam := by rw [hξdef]; nlinarith [hw_lt, hlam]
    -- the crossing, in vector form
    have hvec : r x - r (ta s)
        = (1 - c) • (lam • (r (tb s) - r (ta s))) + c • (r (ta s + ξ) - r (ta s)) :=
      chamfer_crossing_vec hcross
    -- periodicity at the crossing point
    have hper : r (x - period) = r x := by
      have h := hr.periodic (x - period)
      rw [sub_add_cancel] at h
      exact h.symm
    -- size bounds
    have hB : ‖r (tb s) - r (ta s)‖ ≤ Mc * period := by
      have h := hcurveLip (tb s) (ta s)
      rw [abs_of_pos hw_pos] at h
      nlinarith [h, hw_lt, hMc]
    have hD : ‖r (ta s + ξ) - r (ta s)‖ ≤ Mc * period * lam := by
      have h := hcurveLip (ta s + ξ) (ta s)
      have h1 : ta s + ξ - ta s = ξ := by ring
      rw [h1, abs_of_pos hξ_pos] at h
      nlinarith [h, hξ_le, hMc]
    have hrx : ‖r x - r (ta s)‖ ≤ 2 * (Mc * period * lam) := by
      rw [hvec]
      have h1 : ‖(1 - c) • (lam • (r (tb s) - r (ta s)))
          + c • (r (ta s + ξ) - r (ta s))‖
          ≤ (1 - c) * (lam * ‖r (tb s) - r (ta s)‖)
            + c * ‖r (ta s + ξ) - r (ta s)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [hc1] : (0 : ℝ) ≤ 1 - c),
          abs_of_nonneg (le_of_lt hc0), abs_of_pos hlam]
      have h2 : (1 - c) * (lam * ‖r (tb s) - r (ta s)‖) ≤ lam * (Mc * period) := by
        calc (1 - c) * (lam * ‖r (tb s) - r (ta s)‖)
            ≤ 1 * (lam * (Mc * period)) := by
              exact mul_le_mul (by linarith [hc0]) (mul_le_mul_of_nonneg_left hB hlam.le)
                (by positivity) (by norm_num)
          _ = lam * (Mc * period) := by ring
      have h3 : c * ‖r (ta s + ξ) - r (ta s)‖ ≤ Mc * period * lam := by
        calc c * ‖r (ta s + ξ) - r (ta s)‖ ≤ 1 * (Mc * period * lam) :=
              mul_le_mul hc1.le hD (norm_nonneg _) (by positivity)
          _ = Mc * period * lam := by ring
      linarith [h1, h2, h3]
    -- localisation of the crossing point at scale `lam`
    have hθ_pos : 0 < x - ta s := by linarith [hxlo, hξ_pos]
    have hθ_lt : x - ta s < period := by linarith [hxhi, hw_lt]
    have hloc : x - ta s ≤ Cloc * lam ∨ period - (x - ta s) ≤ Cloc * lam := by
      by_cases hle : x - ta s ≤ δ
      · left
        have h1 := hnear (ta s) x (by rw [abs_of_pos hθ_pos]; exact hle)
        rw [abs_of_pos hθ_pos, norm_sub_rev] at h1
        have h2 : (m / 2) * (x - ta s) ≤ 2 * (Mc * period * lam) := le_trans h1 hrx
        rw [hClocdef, div_mul_eq_mul_div, le_div_iff₀ hm]
        nlinarith [h2, hm, hlam]
      · by_cases hle2 : period - (x - ta s) ≤ δ
        · right
          have he_pos : 0 < period - (x - ta s) := by linarith [hθ_lt]
          have h1 := hnear (ta s) (x - period) (by
            have h3 : (x - period) - ta s = -(period - (x - ta s)) := by ring
            rw [h3, abs_neg, abs_of_pos he_pos]
            exact hle2)
          rw [show (x - period) - ta s = -(period - (x - ta s)) from by ring, abs_neg,
            abs_of_pos he_pos, hper, norm_sub_rev] at h1
          have h2 : (m / 2) * (period - (x - ta s)) ≤ 2 * (Mc * period * lam) :=
            le_trans h1 hrx
          rw [hClocdef, div_mul_eq_mul_div, le_div_iff₀ hm]
          nlinarith [h2, hm, hlam]
        · exfalso
          have h1 := hfar (ta s) x
            (by rw [abs_of_pos hθ_pos]; exact le_of_lt (lt_of_not_ge hle))
            (by rw [abs_of_pos hθ_pos]; linarith [lt_of_not_ge hle2])
          rw [norm_sub_rev] at h1
          have h2 : sep ≤ 2 * (Mc * period * lam) := le_trans h1 hrx
          have h3 : 2 * (Mc * period * lam) < sep := by
            have hden : 0 < 4 * Mc * period := by positivity
            have h5 : lam * (4 * Mc * period) ≤ sep := (le_div_iff₀ hden).mp hL1
            have h6 : 2 * (Mc * period * lam) * 2 = lam * (4 * Mc * period) := by ring
            nlinarith [h5, h6]
          linarith [h2, h3]
    rcases hloc with hlocA | hlocB
    · -- Case A: the crossing point is localised near `ta`; the thin-crossing theorem applies.
      exfalso
      have htilt := hthin (ta s) (tb s) lam c x Cloc hlam hw_pos hw_lt hc1 hxlo hxhi hlocA hcross
      have hμs : μ ≤ ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖ := hμ s hs
      have hden : 0 < 2 * K * Cloc := by positivity
      have h5 : lam * (2 * K * Cloc) ≤ μ := (le_div_iff₀ hden).mp hL2
      have h6 : K * Cloc * lam ≤ μ / 2 := by nlinarith [h5, hK, hClocpos]
      linarith [htilt, hμs, h6, hμpos]
    · -- Case B: the crossing point is localised at the head of the chord (`x ≈ ta + period`).
      exfalso
      have hden3 : 0 < 2 * κ * (Cloc + period) := by positivity
      have h5 : lam * (2 * κ * (Cloc + period)) ≤ μ := (le_div_iff₀ hden3).mp hL3
      have h8' : (Cloc + period) * lam * (2 * κ) ≤ μ := by nlinarith [h5]
      have heμ : (period - (x - ta s)) * (2 * κ) ≤ μ := by
        have h1 : (period - (x - ta s)) * (2 * κ) ≤ (Cloc * lam) * (2 * κ) :=
          mul_le_mul_of_nonneg_right hlocB (by positivity)
        have h2 : (Cloc * lam) * (2 * κ) ≤ (Cloc + period) * lam * (2 * κ) := by
          nlinarith [hClocpos, hp, hlam, hκ]
        linarith [h1, h2, h8']
      have hξμ : ξ * (2 * κ) ≤ μ := by
        have h1 : ξ * (2 * κ) ≤ (period * lam) * (2 * κ) :=
          mul_le_mul_of_nonneg_right hξ_le (by positivity)
        have h2 : (period * lam) * (2 * κ) ≤ (Cloc + period) * lam * (2 * κ) := by
          nlinarith [hClocpos, hp, hlam, hκ]
        linarith [h1, h2, h8']
      exact no_crossing_head (A := ta s) (B := tb s) (x := x) (ξ := ξ)
        (e := period - (x - ta s)) (c := c) (μ := μ) (κ := κ) (lam := lam) hr
        hκ hμpos hc0 hAB (hμ s hs) hκlip hper
        (by ring : ta s - (period - (x - ta s)) = x - period)
        (by linarith [hθ_lt] : 0 < period - (x - ta s)) hξ_pos heμ hξμ hvec

end Work.Drive
