import Mathlib
import Submission.Work.Drive.chamferCrossingThin
import Submission.Work.Drive.chamferSepAux

/-!
# The windowed no-chamfer-crossing theorem with non-tangency at both ends

This module proves `Work.Drive.no_chamfer_crossing_window_nt` together with the (self-contained)
ingredients it needs, above the target statement:

* `Work.Drive.exists_smul_of_chordTilt_eq_zero` — a vanishing tilt forces the chord to be parallel
  to the vector, so non-tangency implies a non-vanishing tilt;
* `Work.Drive.continuousOn_chordTilt_comp` — continuity of the chord tilt along a continuous family
  of chords with distinct endpoints;
* `Work.Drive.knot_lipschitz_global_nt` — a global Lipschitz bound for a smooth knot (from the uniform
  speed bound `Work.Drive.exists_knot_c2_bounds`);
* `Work.Drive.inner_slack_of_reach` — the slack estimate `⟪n, velocity⟫ ≥ ‖n‖ ^ 2 / 2` on the
  symmetric reach `[t - ξ, t + ξ]`, `C ξ ≤ ‖n‖ / 2`;
* `Work.Drive.chamfer_crossing_localized_nt` — **localisation of a chamfer crossing**: a crossing
  whose parameter is not within `C₀ lam` of `ta` must be within `C₀ lam` of `ta + period`
  (i.e. of `tb` from below, as `tb - ta < period`);
* `Work.Drive.chamfer_crossing_thin_tilt_tb` — the **mirror** of the proved thin-crossing theorem
  `Work.Drive.chamfer_crossing_thin_tilt`: a crossing localised at the *head* (`tb`) of a nearly
  period-long chord forces the tilt of the chord at `tb` to be `O(lam)`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

variable {r : ℝ → Space}

/-! ## 1. The tilt of a chord: non-vanishing and continuity -/

/-- **A vanishing chord tilt makes the chord parallel to the vector.**  If the tilt of `w` relative
to the chord `A B` vanishes and `w ≠ 0`, then `B - A` is a multiple of `w`.  Consequently, *no*
multiple relation `B - A = m • v` (non-tangency) forces the tilt of `v` to be non-zero. -/
lemma exists_smul_of_chordTilt_eq_zero {A B w : Space} (hAB : A ≠ B) (hw : w ≠ 0)
    (h : chordTilt A B w = 0) : ∃ m : ℝ, B - A = m • w := by
  have hw_eq : w = inner ℝ w (chordDir A B) • chordDir A B := by
    have h' := h
    rw [chordTilt_def] at h'
    exact sub_eq_zero.mp h'
  have ha : inner ℝ w (chordDir A B) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hw_eq
    exact hw hw_eq
  let a : ℝ := inner ℝ w (chordDir A B)
  have ha' : a ≠ 0 := ha
  have hw_eq' : w = a • chordDir A B := hw_eq
  refine ⟨‖B - A‖ * a⁻¹, ?_⟩
  have hBA : B - A = ‖B - A‖ • chordDir A B := (chordDir_smul A B hAB).symm
  have hu : chordDir A B = a⁻¹ • w := by
    calc chordDir A B = (a⁻¹ * a) • chordDir A B := by rw [inv_mul_cancel₀ ha', one_smul]
      _ = a⁻¹ • (a • chordDir A B) := by rw [mul_smul]
      _ = a⁻¹ • w := by rw [← hw_eq']
  calc B - A = ‖B - A‖ • chordDir A B := (chordDir_smul A B hAB).symm
    _ = ‖B - A‖ • (a⁻¹ • w) := by rw [hu]
    _ = (‖B - A‖ * a⁻¹) • w := by rw [smul_smul]

/-- **The chord direction depends continuously on the pair** (away from the diagonal). -/
lemma continuousOn_chordDir_comp {A B : ℝ → Space} {S : Set ℝ}
    (hA : Continuous A) (hB : Continuous B) (hne : ∀ s ∈ S, B s ≠ A s) :
    ContinuousOn (fun s => chordDir (A s) (B s)) S := by
  have h1 : ContinuousOn (fun s => ‖B s - A s‖⁻¹) S :=
    ((hB.sub hA).continuousOn.norm).inv₀ (fun s hs => by
      rw [norm_ne_zero_iff]
      exact sub_ne_zero.mpr (hne s hs))
  have h2 : ContinuousOn (fun s => B s - A s) S := (hB.sub hA).continuousOn
  have h3 : ContinuousOn (fun s => ‖B s - A s‖⁻¹ • (B s - A s)) S :=
    (h1.smul h2).congr (fun s _ => rfl)
  simpa [chordDir] using h3

/-- **The chord tilt depends continuously on the pair and the vector** (away from the diagonal). -/
lemma continuousOn_chordTilt_comp {A B W : ℝ → Space} {S : Set ℝ}
    (hA : Continuous A) (hB : Continuous B) (hW : Continuous W) (hne : ∀ s ∈ S, A s ≠ B s) :
    ContinuousOn (fun s => chordTilt (A s) (B s) (W s)) S := by
  have hdir : ContinuousOn (fun s => chordDir (A s) (B s)) S :=
    continuousOn_chordDir_comp hA hB (fun s hs => (hne s hs).symm)
  have h3 : ContinuousOn (fun s => inner ℝ (W s) (chordDir (A s) (B s))) S :=
    hW.continuousOn.inner hdir
  have h4 : ContinuousOn
      (fun s => (inner ℝ (W s) (chordDir (A s) (B s))) • chordDir (A s) (B s)) S :=
    (h3.smul hdir).congr (fun s _ => rfl)
  have h5 : ContinuousOn
      (fun s => W s - (inner ℝ (W s) (chordDir (A s) (B s))) • chordDir (A s) (B s)) S :=
    hW.continuousOn.sub h4
  simpa [chordTilt_def] using h5

/-! ## 2. A global Lipschitz bound for a smooth knot -/

/-- **A smooth knot is globally Lipschitz.** -/
lemma knot_lipschitz_global_nt {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ M : ℝ, 0 < M ∧ ∀ s t : ℝ, ‖r s - r t‖ ≤ M * |s - t| := by
  obtain ⟨m, M, C, hm, hM, hC, hmin, hmax, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨M, hM, fun s t => ?_⟩
  have hst : min s t ≤ max s t := le_trans (min_le_left s t) (le_max_left s t)
  have hdiff : ∀ x ∈ Set.Icc (min s t) (max s t), DifferentiableAt ℝ r x :=
    fun x _ => (hr.smooth.differentiable (by simp)) x
  have hbound : ∀ x ∈ Set.Icc (min s t) (max s t), ‖velocity r x‖ ≤ M := fun x _ => hmax x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := r)
    (s := Set.Icc (min s t) (max s t)) (C := M) (x := min s t) (y := max s t) hdiff hbound
    (convex_Icc _ _) ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
  have h1 : ‖r (max s t) - r (min s t)‖ ≤ M * (max s t - min s t) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using h
  rcases le_total s t with hle | hle
  · rw [max_eq_right hle, min_eq_left hle] at h1
    have habs : |s - t| = t - s := by rw [abs_of_nonpos (sub_nonpos.mpr hle)]; ring
    rw [habs, norm_sub_rev]
    exact h1
  · rw [max_eq_left hle, min_eq_right hle] at h1
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h1


/-- `lam ≤ μ / (2 * c)` with `c > 0` gives `c * lam ≤ μ / 2`. -/
lemma mul_le_half_of_le_div {c μ lam : ℝ} (hc : 0 < c) (h : lam ≤ μ / (2 * c)) :
    c * lam ≤ μ / 2 := by
  have h2 : lam * c ≤ (μ / (2 * c)) * c := mul_le_mul_of_nonneg_right h hc.le
  have h3 : (μ / (2 * c)) * c = μ / 2 := by
    field_simp
  have h4 : lam * c ≤ μ / 2 := by linarith [h2, h3.le, h3.ge]
  rwa [mul_comm] at h4

/-! ## 3. The slack estimate on a symmetric reach -/

/-- **The slack estimate.**  If `⟪n, velocity r t⟫ = ‖n‖ ^ 2` (i.e. `n` is the projection of the
velocity at `t` onto the orthogonal complement of a chord) and the velocity is `C`-Lipschitz, then
on the symmetric reach `[t - ξ, t + ξ]` of size `C ξ ≤ ‖n‖ / 2` the velocity keeps at least half of
its projection on `n`: `‖n‖ ^ 2 / 2 ≤ ⟪n, velocity r y⟫`. -/
lemma inner_slack_of_reach {r : ℝ → Space} {n : Space} {C t ξ : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ a b : ℝ, ‖velocity r a - velocity r b‖ ≤ C * |b - a|)
    (ht : inner ℝ n (velocity r t) = ‖n‖ ^ 2) (hξ : C * ξ ≤ ‖n‖ / 2) :
    ∀ y ∈ Set.Icc (t - ξ) (t + ξ), ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
  intro y hy
  have hyabs : |y - t| ≤ ξ := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h2 : ‖velocity r y - velocity r t‖ ≤ C * ξ := by
    have h := hlip y t
    rw [abs_sub_comm] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hyabs hC)
  have h3 : -(‖n‖ * (C * ξ)) ≤ inner ℝ n (velocity r y - velocity r t) := by
    have h4 : |inner ℝ n (velocity r y - velocity r t)|
        ≤ ‖n‖ * ‖velocity r y - velocity r t‖ := abs_real_inner_le_norm n _
    have h5 : ‖n‖ * ‖velocity r y - velocity r t‖ ≤ ‖n‖ * (C * ξ) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
    linarith [neg_abs_le (inner ℝ n (velocity r y - velocity r t)), h4, h5]
  have h6 : inner ℝ n (velocity r y)
      = inner ℝ n (velocity r t) + inner ℝ n (velocity r y - velocity r t) := by
    rw [inner_sub_right]
    ring
  have h7 : ‖n‖ * (C * ξ) ≤ ‖n‖ ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hξ (norm_nonneg n)
    nlinarith [this]
  linarith [h6, ht, h3, h7]

/-! ## 4. Localisation of a chamfer crossing -/

/-- **Localisation of a chamfer crossing.**  There are constants `L₀ > 0`, `C > 0` (depending only
on the knot) such that for `lam ∈ (0, L₀]`, `0 < tb - ta < period` and a crossing
`r x = (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta))` with
`c ∈ (0,1)`, `ta + lam * (tb - ta) ≤ x ≤ tb`, the crossing parameter `x` is within `C * lam` of
either `ta` or `ta + period` (the latter meaning: within `C * lam` of `tb` from below, since
`tb - ta < period`).

(The statement is invariant under a common shift of `ta`, `tb`, `x` by a period, so no normalisation
of `ta` is needed.) -/
theorem chamfer_crossing_localized_nt {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ L₀ C : ℝ, 0 < L₀ ∧ 0 < C ∧ ∀ (ta tb lam c x : ℝ),
      0 < lam → lam ≤ L₀ → 0 < tb - ta → tb - ta < period → 0 < c → c < 1 →
      ta + lam * (tb - ta) ≤ x → x ≤ tb →
      (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta)) = r x →
      x - ta ≤ C * lam ∨ period - (x - ta) ≤ C * lam := by
  obtain ⟨m, δ, sep, hm, hδ, hsep, hspeed, hnear, hfar⟩ := knot_bounds hr
  obtain ⟨M, hM, hlip⟩ := knot_lipschitz_global_nt hr
  have hp : 0 < period := period_pos
  have hMp : 0 < M * period := mul_pos hM hp
  refine ⟨sep / (2 * (M * period)), 2 * M * period / m, by positivity, by positivity, ?_⟩
  intro ta tb lam c x hlam hL hw hwlt hc0 hc1 hxlo hxhi hcross
  have hwle : tb - ta ≤ period := le_of_lt hwlt
  -- the displacement of the crossing from `r ta` is `O(lam)`
  have hdisp : ‖r x - r ta‖ ≤ M * period * lam := by
    have hvec : r x - r ta
        = (1 - c) • (lam • (r tb - r ta)) + c • (r (ta + lam * (tb - ta)) - r ta) :=
      chamfer_crossing_vec hcross
    have hV : ‖r tb - r ta‖ ≤ M * period := by
      have h := hlip tb ta
      rw [abs_of_pos hw] at h
      have h2 : M * (tb - ta) ≤ M * period := mul_le_mul_of_nonneg_left hwle hM.le
      linarith [h, h2]
    have hD : ‖r (ta + lam * (tb - ta)) - r ta‖ ≤ M * period * lam := by
      have h := hlip (ta + lam * (tb - ta)) ta
      rw [add_sub_cancel_left, abs_of_pos (mul_pos hlam hw)] at h
      have h2 : M * (lam * (tb - ta)) ≤ M * (lam * period) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hlam.le) hM.le
      have h3 : M * (lam * period) = M * period * lam := by ring
      linarith [h, h2, h3.le, h3.ge]
    have h1 : ‖(1 - c) • (lam • (r tb - r ta))‖ ≤ (1 - c) * (lam * (M * period)) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hc1.le), abs_of_pos hlam]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV hlam.le)
        (sub_nonneg.mpr hc1.le)
    have h2 : ‖c • (r (ta + lam * (tb - ta)) - r ta)‖ ≤ c * (M * period * lam) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
      exact mul_le_mul_of_nonneg_left hD hc0.le
    calc ‖r x - r ta‖
        = ‖(1 - c) • (lam • (r tb - r ta)) + c • (r (ta + lam * (tb - ta)) - r ta)‖ := by
          rw [hvec]
      _ ≤ ‖(1 - c) • (lam • (r tb - r ta))‖
            + ‖c • (r (ta + lam * (tb - ta)) - r ta)‖ := norm_add_le _ _
      _ ≤ (1 - c) * (lam * (M * period)) + c * (M * period * lam) := add_le_add h1 h2
      _ = M * period * lam := by ring
  have hxta_pos : 0 < x - ta := lt_of_lt_of_le (mul_pos hlam hw) (by linarith [hxlo])
  have hxta_lt : x - ta < period := lt_of_le_of_lt (by linarith [hxhi]) hwlt
  have habs : |x - ta| = x - ta := abs_of_pos hxta_pos
  by_cases hA : x - ta ≤ δ
  · left
    have h1 := hnear ta x (by rw [habs]; exact hA)
    rw [norm_sub_rev, habs] at h1
    have h2 : (m / 2) * (x - ta) ≤ M * period * lam := le_trans h1 hdisp
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith [h2, hM, hp]
  · by_cases hC : period - δ < x - ta
    · right
      have hper : r (x - period) = r x := by
        simpa [sub_add_cancel] using (hr.periodic (x - period)).symm
      have hd : |ta - (x - period)| = period - (x - ta) := by
        have h0 : ta - (x - period) = period - (x - ta) := by ring
        rw [h0, abs_of_pos (by linarith [hxta_lt])]
      have h1 := hnear (x - period) ta (by rw [hd]; linarith [hC.le, hδ])
      rw [hper, hd] at h1
      have h2 : (m / 2) * (period - (x - ta)) ≤ M * period * lam := le_trans h1 hdisp
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith [h2, hM, hp]
    · exfalso
      have hbig : δ ≤ x - ta := le_of_not_ge hA
      have hle : x - ta ≤ period - δ := le_of_not_gt hC
      have h1 := hfar ta x (by rw [habs]; exact hbig) (by rw [habs]; exact hle)
      rw [norm_sub_rev] at h1
      have h2 : sep ≤ M * period * lam := le_trans h1 hdisp
      have h3 : sep / (2 * (M * period)) < sep / (M * period) :=
        div_lt_div_of_pos_left hsep hMp (by linarith [hMp])
      have h4 : sep / (M * period) ≤ lam := by
        rw [div_le_iff₀ hMp]
        linarith [h2]
      linarith [h3, h4, hL]

/-! ## 5. The mirror thin-crossing theorem (localisation at the head) -/

/-- **A crossing localised at the head forces the tilt at `tb` to be small.**  This is the mirror of
`Work.Drive.chamfer_crossing_thin_tilt`.  Hypotheses: `0 < lam`, `0 < tb - ta < period`,
`c ∈ (0,1)`, the crossing `r x = (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam*(tb-ta))`
with `ta + lam*(tb-ta) ≤ x ≤ tb`, the *head localisation* `tb - x ≤ C₀ * lam` and the
*near-period-length* condition `period - (1 - lam) * (tb - ta) ≤ C₁ * lam`.  Conclusion:
`‖chordTilt (r ta) (r tb) (velocity r tb)‖ ≤ K * (C₀ + C₁) * lam`, with `K` twice a Lipschitz
constant for the velocity of the knot.

Mechanism: for `n` the component of `velocity r tb` orthogonal to the chord, the functional
`θ ↦ ⟪n, r (tb - θ) - r tb⟫` is non-positive for `0 ≤ θ < ξ` and strictly positive at `-ξ < 0`
(i.e. `⟪n, r (tb + e) - r tb⟫ > 0` for `0 < e < ξ`), where `ξ = ‖n‖ / (2 K)`, while the crossing is
the exact identity `⟪n, r x - r tb⟫ = c * ⟪n, r (ta + lam*(tb-ta)) - r tb⟫` in which the left
argument is `tb - x ∈ [0, ξ)` and the right argument equals `r (tb + e)` with
`e = period - (1 - lam)*(tb - ta) ∈ (0, ξ)` after using the periodicity of `r`. -/
theorem chamfer_crossing_thin_tilt_tb {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ta tb lam c x C₀ C₁ : ℝ),
      0 < lam → 0 < tb - ta → tb - ta < period → 0 < c → c < 1 →
      0 ≤ C₀ → 0 ≤ C₁ →
      ta + lam * (tb - ta) ≤ x → x ≤ tb →
      tb - x ≤ C₀ * lam → period - (1 - lam) * (tb - ta) ≤ C₁ * lam →
      (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta)) = r x →
      ‖chordTilt (r ta) (r tb) (velocity r tb)‖ ≤ K * (C₀ + C₁) * lam := by
  obtain ⟨m, M, C, hm, hM, hC, hmin, hmax, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨2 * C, by positivity, ?_⟩
  intro ta tb lam c x C₀ C₁ hlam hw hwlt hc0 hc1 hC₀ hC₁ hxlo hxhi hxC₀ hxC₁ hcross
  by_contra hcon
  rw [not_le] at hcon
  have hAB : r ta ≠ r tb := knot_ne_of_sub_mem_Ioo hr hw hwlt
  let n : Space := chordTilt (r ta) (r tb) (velocity r tb)
  have hnn : inner ℝ n (velocity r tb) = ‖n‖ ^ 2 := inner_chordTilt_self hAB (velocity r tb)
  have hcon' : 2 * C * (C₀ + C₁) * lam < ‖n‖ := hcon
  have hsub : 0 ≤ 2 * C * (C₀ + C₁) * lam := by positivity
  have hnvpos : 0 < ‖n‖ := lt_of_le_of_lt hsub hcon'
  -- the two localisation bounds, at scale `‖n‖ / (2 * C)`
  have hC0lam : C₀ * lam < ‖n‖ / (2 * C) := by
    have hsplit : 2 * C * (C₀ + C₁) * lam = 2 * C * C₀ * lam + 2 * C * C₁ * lam := by ring
    have hnn2 : 0 ≤ 2 * C * C₁ * lam := by positivity
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hcon', hsplit, hnn2]
  have hC1lam : C₁ * lam < ‖n‖ / (2 * C) := by
    have hsplit : 2 * C * (C₀ + C₁) * lam = 2 * C * C₀ * lam + 2 * C * C₁ * lam := by ring
    have hnn2 : 0 ≤ 2 * C * C₀ * lam := by positivity
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hcon', hsplit, hnn2]
  have hθ0 : 0 ≤ tb - x := by linarith [hxhi]
  have hθlt : tb - x < ‖n‖ / (2 * C) := lt_of_le_of_lt hxC₀ hC0lam
  set e : ℝ := period - (1 - lam) * (tb - ta) with he
  have he_pos : 0 < e := by
    have h1 : (1 - lam) * (tb - ta) < tb - ta := by
      calc (1 - lam) * (tb - ta) < 1 * (tb - ta) := mul_lt_mul_of_pos_right (by linarith) hw
        _ = tb - ta := one_mul _
    rw [he]
    linarith [h1, hwlt]
  have he_lt : e < ‖n‖ / (2 * C) := lt_of_le_of_lt hxC₁ hC1lam
  -- (A) the functional is non-positive at the crossing parameter
  have hneg : inner ℝ n (r x - r tb) ≤ 0 := by
    have hslack : ∀ y ∈ Set.Icc (tb - (tb - x)) tb, ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
      intro y hy
      have hy' : y ∈ Set.Icc (tb - (tb - x)) (tb + (tb - x)) :=
        ⟨hy.1, by linarith [hy.2, hθ0]⟩
      exact inner_slack_of_reach (n := n) (C := C) (t := tb) (ξ := tb - x) hC.le hlip hnn
        (mul_le_half_of_le_div hC hθlt.le) y hy'
    have hmono := inner_knot_slack_mono hr (n := n) (ν := ‖n‖ ^ 2 / 2)
      (a := tb - (tb - x)) (b := tb) hslack
    have h1 := hmono (tb - (tb - x)) ⟨by linarith [hθ0], by linarith [hθ0]⟩ tb
      ⟨by linarith [hθ0], le_rfl⟩ (by linarith [hθ0])
    have hxx : tb - (tb - x) = x := by ring
    rw [hxx] at h1
    have h2 : inner ℝ n (r tb - r x) = -inner ℝ n (r x - r tb) := by
      rw [inner_sub_right, inner_sub_right]
      ring
    rw [h2] at h1
    have h3 : 0 ≤ ‖n‖ ^ 2 / 2 * (tb - x) := mul_nonneg (by positivity) hθ0
    linarith [h1, h3]
  -- (B) the functional is strictly positive at the mirrored (period-shifted) point
  have hpos : 0 < inner ℝ n (r (tb + e) - r tb) := by
    have hslack : ∀ y ∈ Set.Icc tb (tb + e), ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
      intro y hy
      have hy' : y ∈ Set.Icc (tb - e) (tb + e) := ⟨by linarith [hy.1, he_pos], hy.2⟩
      exact inner_slack_of_reach (n := n) (C := C) (t := tb) (ξ := e) hC.le hlip hnn
        (mul_le_half_of_le_div hC he_lt.le) y hy'
    have hmono := inner_knot_slack_mono hr (n := n) (ν := ‖n‖ ^ 2 / 2)
      (a := tb) (b := tb + e) hslack
    have h1 := hmono tb ⟨le_rfl, by linarith [he_pos]⟩ (tb + e)
      ⟨by linarith [he_pos], le_rfl⟩ (by linarith [he_pos])
    have h2 : 0 < ‖n‖ ^ 2 / 2 * (tb + e - tb) := by
      have h3 : 0 < tb + e - tb := by linarith [he_pos]
      have h4 : 0 < ‖n‖ ^ 2 / 2 := by
        have h5 := pow_pos hnvpos 2
        linarith
      exact mul_pos h4 h3
    linarith [h1, h2]
  -- the exact crossing identity
  have hEq : inner ℝ n (r x - r tb) = c * inner ℝ n (r (tb + e) - r tb) := by
    have hperp : inner ℝ n (r tb - r ta) = 0 := by
      have hsmul : r tb - r ta = ‖r tb - r ta‖ • chordDir (r ta) (r tb) :=
        (chordDir_smul (r ta) (r tb) hAB).symm
      rw [hsmul, inner_smul_right, inner_chordTilt_chordDir hAB]
      ring
    have hvec : r x - r tb
        = (1 - c) • ((-(1 - lam)) • (r tb - r ta)) + c • (r (ta + lam * (tb - ta)) - r tb) := by
      rw [← hcross]
      module
    have hper2 : r (tb + e) = r (ta + lam * (tb - ta)) := by
      have harg : tb + e = ta + lam * (tb - ta) + period := by rw [he]; ring
      rw [harg]
      exact hr.periodic (ta + lam * (tb - ta))
    rw [hvec, hper2, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right, hperp]
    ring
  nlinarith [hEq, hneg, hpos, hc0]

/-! ## 6. The target -/

/-- **No chamfer crossing on a compact window carrying a non-tangency margin at BOTH endpoints.**
Same as `Work.Drive.no_chamfer_crossing_window`, but with non-tangency of the chord at *both* ends of
the retained arc — the hypothesis actually supplied by `Work.Drive.SweepNonTangent`
(`Submission/Work/Drive/sweepNonTangentDefs.lean`: `cross3 V (velocity r (taR s)) ≠ 0 ∧
cross3 V (velocity r (tbR s)) ≠ 0`), and the one the `OFat` lane has on the whole crosscut, because
`StripCrosscutAvoidingOFat` avoids the tangency set `TCset`.  The extra hypothesis is genuinely
needed: `Work.Drive.chamfer_crossing_localized` has the two alternatives `x - ta ≤ C * lam` and
`period - (x - ta) ≤ C * lam`, the first handled by the proved thin-crossing theorem
`Work.Drive.chamfer_crossing_thin_tilt` (tilt at `ta`), the second by its *mirror* (tilt at `tb`).

Proof ingredients (both cases reduce to the same "monotone functional" mechanism):

* **tail branch** (`x - ta ≤ C * lam`): `Work.Drive.chamfer_crossing_thin_tilt` verbatim;
* **mirror branch** (`period - (x - ta) ≤ C * lam`, so `tb - ta` is within `O(lam)` of `period` and
  `tb - x ≤ C * lam`): pair the crossing equation with `n := chordTilt (r ta) (r tb) (velocity r tb)`
  (which is `⊥ (r tb - r ta)`).  Since the chord point `C = (1-lam) r ta + lam r tb` satisfies
  `C - r tb = -(1-lam) * (r tb - r ta)`, this gives the exact identity
  `⟪r x - r tb, n⟫ = c * ⟪r (ta + lam*(tb-ta)) - r tb, n⟫`; with
  `h (θ) := ⟪r (tb - θ) - r tb, n⟫` and the periodicity of `r` this is
  `h (tb - x) = c * h ((1-lam)*(tb-ta) - period)`, and the right argument equals
  `r` of `ta + lam*(tb-ta) + period`; one then uses the analogue of
  `Work.Drive.inner_knot_slack_mono` for `h` near `0` (where `h'(0) = ‖n‖ ^ 2`), monotonicity in
  modulus, and `c < 1`;
* **compactness**: on `[a,b]` both tilt functions are continuous and pointwise nonzero (by `hntA`,
  `hntB`), hence bounded below by `μ > 0`; `lam < μ / (K * C₀)` (with `K`, `C₀` the constants of
  `chamfer_crossing_thin_tilt` and of the localisation) rules every crossing out. -/
theorem no_chamfer_crossing_window_nt
    {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (ta tb : ℝ → ℝ) (hta : Continuous ta) (htb : Continuous tb)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hpos : ∀ s ∈ Set.Icc a b, 0 < tb s - ta s ∧ tb s - ta s < LeanEval.KnotTheory.Quadrisecant.period)
    (hntA : ∀ s ∈ Set.Icc a b, ∀ m : ℝ,
      r (tb s) - r (ta s) ≠ m • LeanEval.KnotTheory.Quadrisecant.velocity r (ta s))
    (hntB : ∀ s ∈ Set.Icc a b, ∀ m : ℝ,
      r (tb s) - r (ta s) ≠ m • LeanEval.KnotTheory.Quadrisecant.velocity r (tb s)) :
    ∃ L : ℝ, 0 < L ∧ ∀ (lam x c : ℝ), 0 < lam → lam ≤ L → 0 < c → c < 1 →
      ∀ s ∈ Set.Icc a b,
        ta s + lam * (tb s - ta s) ≤ x → x ≤ tb s →
        (1 - c) • ((1 - lam) • r (ta s) + lam • r (tb s))
            + c • r (ta s + lam * (tb s - ta s)) = r x →
        x = ta s + lam * (tb s - ta s) := by
  obtain ⟨L₀, C, hL₀, hC, hloc⟩ := chamfer_crossing_localized_nt hr
  obtain ⟨K, hK, htilt⟩ := chamfer_crossing_thin_tilt hr
  obtain ⟨Kb, hKb, htiltb⟩ := chamfer_crossing_thin_tilt_tb hr
  -- the tilt functions and their lower bound on the window
  have hvel : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hAne : ∀ s ∈ Set.Icc a b, r (ta s) ≠ r (tb s) :=
    fun s hs => knot_ne_of_sub_mem_Ioo hr (hpos s hs).1 (hpos s hs).2
  have hTa_c : ContinuousOn
      (fun s => ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖) (Set.Icc a b) :=
    (continuousOn_chordTilt_comp (hA := hr.continuous.comp hta) (hB := hr.continuous.comp htb)
      (hW := hvel.comp hta) hAne).norm
  have hTb_c : ContinuousOn
      (fun s => ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))‖) (Set.Icc a b) :=
    (continuousOn_chordTilt_comp (hA := hr.continuous.comp hta) (hB := hr.continuous.comp htb)
      (hW := hvel.comp htb) hAne).norm
  have hTa_pos : ∀ s ∈ Set.Icc a b, 0 < ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖ := by
    intro s hs
    rw [norm_pos_iff]
    intro h0
    obtain ⟨mm, hmm⟩ :=
      exists_smul_of_chordTilt_eq_zero (A := r (ta s)) (B := r (tb s)) (w := velocity r (ta s))
        (hAne s hs) (hr.regular (ta s)) h0
    exact hntA s hs mm hmm
  have hTb_pos : ∀ s ∈ Set.Icc a b, 0 < ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))‖ := by
    intro s hs
    rw [norm_pos_iff]
    intro h0
    obtain ⟨mm, hmm⟩ :=
      exists_smul_of_chordTilt_eq_zero (A := r (ta s)) (B := r (tb s)) (w := velocity r (tb s))
        (hAne s hs) (hr.regular (tb s)) h0
    exact hntB s hs mm hmm
  obtain ⟨μa, hμa_gt, hμa⟩ := isCompact_Icc.exists_forall_le'
    (f := fun s => ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖) hTa_c hTa_pos
  obtain ⟨μb, hμb_gt, hμb⟩ := isCompact_Icc.exists_forall_le'
    (f := fun s => ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))‖) hTb_c hTb_pos
  refine ⟨min L₀ (min (μa / (2 * (K * C))) (μb / (2 * (Kb * (C + (C + period)))))), ?_, ?_⟩
  · have hKC : 0 < K * C := mul_pos hK hC
    have h1 : 0 < C + (C + period) := by linarith [hC, period_pos]
    have h2 : 0 < Kb * (C + (C + period)) := mul_pos hKb h1
    exact lt_min hL₀ (lt_min (div_pos hμa_gt (by linarith)) (div_pos hμb_gt (by linarith)))
  · intro lam x c hlam hL hc0 hc1 s hs hxlo hxhi hcross
    have hLK : lam ≤ μa / (2 * (K * C)) :=
      le_trans hL (le_trans (min_le_right _ _) (min_le_left _ _))
    have hLKb : lam ≤ μb / (2 * (Kb * (C + (C + period)))) :=
      le_trans hL (le_trans (min_le_right _ _) (min_le_right _ _))
    have hL₀' : lam ≤ L₀ := le_trans hL (min_le_left _ _)
    have hw : 0 < tb s - ta s := (hpos s hs).1
    have hwlt : tb s - ta s < period := (hpos s hs).2
    rcases hloc (ta s) (tb s) lam c x hlam hL₀' hw hwlt hc0 hc1 hxlo hxhi hcross with htail | hhead
    · -- tail branch: the chord is nearly tangent at `ta`
      exfalso
      have ht := htilt (ta s) (tb s) lam c x C hlam hw hwlt hc1 hxlo hxhi htail hcross
      have h1 : K * C * lam ≤ μa / 2 := mul_le_half_of_le_div (mul_pos hK hC) hLK
      have h2 : μa ≤ ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (ta s))‖ := hμa s hs
      linarith [ht, h1, h2, hμa_gt]
    · -- head branch: the chord is nearly tangent at `tb`
      exfalso
      have hx0 : tb s - x ≤ C * lam := by
        have hxx : tb s - x = period - (x - ta s) + ((tb s - ta s) - period) := by ring
        linarith [hhead, hwlt]
      have hw0 : period - (tb s - ta s) ≤ C * lam := by linarith [hhead, hxhi]
      have he0 : period - (1 - lam) * (tb s - ta s) ≤ (C + period) * lam := by
        have h1 : period - (1 - lam) * (tb s - ta s)
            = (period - (tb s - ta s)) + lam * (tb s - ta s) := by ring
        have h2 : lam * (tb s - ta s) ≤ lam * period := mul_le_mul_of_nonneg_left hwlt.le hlam.le
        linarith [h1, hw0, h2]
      have ht := htiltb (ta s) (tb s) lam c x C (C + period) hlam hw hwlt hc0 hc1 hC.le
        (by linarith [hC, period_pos]) hxlo hxhi hx0 he0 hcross
      have h3 : 0 < C + (C + period) := by linarith [hC, period_pos]
      have h1 : Kb * (C + (C + period)) * lam ≤ μb / 2 :=
        mul_le_half_of_le_div (mul_pos hKb h3) hLKb
      have h2 : μb ≤ ‖chordTilt (r (ta s)) (r (tb s)) (velocity r (tb s))‖ := hμb s hs
      linarith [ht, h1, h2, hμb_gt]

end Work.Drive
