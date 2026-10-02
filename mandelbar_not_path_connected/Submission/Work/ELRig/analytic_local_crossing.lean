/-
# `Work.ELRig.analytic_local_crossing`

The analytic local-crossing lemma for the mandelbar (tricorn) development: an analytic
`G : ℂ → ℂ` with `G 0 = 0` and `G'(0) ≠ 0` is, near the origin, *radially strictly
monotone* along the real axis and its norm grows at least linearly off `0`.

Concretely, there are `δ > 0`, `c > 0`, `μ₀ > 0` with

* `c * |t| ≤ ‖G t‖` for `0 < |t| < δ` (a two-sided lower bound), and
* for every `μ ∈ (0, μ₀)` the level `‖G t‖ = μ` is attained at a **unique** real `t ∈ (0, δ)`
  and at a **unique** real `t ∈ (-δ, 0)`.

The proof has two halves.

* The **analytic core** (`alc_core`): `analyt`icity gives the first-order expansion
  `G z = z · G'(0) + o(z)` (extracted from `HasFDerivAt` via `Asymptotics.IsLittleO`)
  and continuity of `z ↦ deriv G z` at `0`.  Writing `U t = ‖G t‖²`, its derivative
  `U' t = 2 * ⟪G t, G' t⟫` (chain rule `HasDerivAt.norm_sq` + `HasDerivAt.comp_ofReal`)
  is shown positive on `(0, δ)` and negative on `(-δ, 0)` by an explicit bilinear
  estimate `alc_inner_bound`.  `strictMonoOn_of_deriv_pos` /
  `strictAntiOn_of_deriv_neg` upgrade this to `StrictMonoOn U` / `StrictAntiOn U`, and
  transporting through `Real.sqrt` (which is strictly increasing on `[0, ∞)`) gives the
  strict monotonicity of `t ↦ ‖G t‖` itself.
* The **order-theoretic half** (`alc_existsUnique_Ioo_of_strictMonoOn` /
  `alc_existsUnique_Ioo_of_strictAntiOn`): a continuous function that is strictly
  monotone on `[0, δ]` with `v 0 = 0` is a bijection onto `[0, v δ]`, so each level
  `μ ∈ (0, v δ)` is attained exactly once; the intermediate value theorem supplies
  existence and strict monotonicity gives uniqueness.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter Metric Asymptotics

noncomputable section

/-- A bilinear "crossing" estimate.  If `e` is small (`‖e‖ ≤ ‖w‖/6 · |t|`) and `f` is
small (`‖f‖ ≤ ‖w‖/2`), then

`inner ℝ (t • w + e) (w + f)` differs from `t * ‖w‖²` by at most `|t| * ‖w‖² * 3/4`;
equivalently the real part of `conj (G t) · G' t` grows like `‖w‖² |t|` with a relative
error of at most `3/4`. -/
lemma alc_inner_bound (t : ℝ) (w e f : ℂ) (he : ‖e‖ ≤ (‖w‖/6) * |t|) (hf : ‖f‖ ≤ ‖w‖/2) :
    |inner ℝ (t • w + e) (w + f) - t * ‖w‖^2| ≤ |t| * ‖w‖^2 * (3/4) := by
  have hA : inner ℝ (t • w) w = t * ‖w‖^2 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hde : inner ℝ (t • w + e) (w + f)
      = t * ‖w‖^2 + (inner ℝ (t•w) f + inner ℝ e w + inner ℝ e f) := by
    rw [inner_add_left, inner_add_right, inner_add_right, hA]
    ring
  rw [hde]
  have hB : |inner ℝ (t•w) f| ≤ |t| * ‖w‖ * (‖w‖/2) := by
    calc |inner ℝ (t•w) f| ≤ ‖t•w‖ * ‖f‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖t•w‖ * (‖w‖/2) := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
      _ = |t| * ‖w‖ * (‖w‖/2) := by rw [norm_smul, Real.norm_eq_abs]
  have hC : |inner ℝ e w| ≤ (‖w‖/6) * |t| * ‖w‖ := by
    calc |inner ℝ e w| ≤ ‖e‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ ((‖w‖/6) * |t|) * ‖w‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
  have hD : |inner ℝ e f| ≤ ((‖w‖/6) * |t|) * (‖w‖/2) := by
    calc |inner ℝ e f| ≤ ‖e‖ * ‖f‖ := abs_real_inner_le_norm _ _
      _ ≤ ((‖w‖/6) * |t|) * (‖w‖/2) := mul_le_mul he hf (norm_nonneg _) (by positivity)
  have h1 : |inner ℝ (t•w) f + inner ℝ e w + inner ℝ e f|
      ≤ |inner ℝ (t•w) f| + |inner ℝ e w| + |inner ℝ e f| := by
    have a := abs_add_le (inner ℝ (t•w) f) (inner ℝ e w)
    have b := abs_add_le (inner ℝ (t•w) f + inner ℝ e w) (inner ℝ e f)
    linarith
  calc |t * ‖w‖^2 + (inner ℝ (t•w) f + inner ℝ e w + inner ℝ e f) - t * ‖w‖^2|
      = |inner ℝ (t•w) f + inner ℝ e w + inner ℝ e f| := by congr 1; ring
    _ ≤ |inner ℝ (t•w) f| + |inner ℝ e w| + |inner ℝ e f| := h1
    _ ≤ |t| * ‖w‖ * (‖w‖/2) + (‖w‖/6) * |t| * ‖w‖ + ((‖w‖/6) * |t|) * (‖w‖/2) := by
          linarith [hB, hC, hD]
    _ = |t| * ‖w‖^2 * (3/4) := by ring

/-- The derivative of `t ↦ ‖G t‖²` is positive just to the right of `0`. -/
lemma alc_deriv_pos {G : ℂ → ℂ} {w : ℂ} {t : ℝ} (htpos : 0 < t) (hwpos : 0 < ‖w‖)
    (he : ‖G (t:ℂ) - t • w‖ ≤ (‖w‖/6) * |t|) (hf : ‖deriv G (t:ℂ) - w‖ ≤ ‖w‖/2) :
    0 < 2 * inner ℝ (G (t:ℂ)) (deriv G (t:ℂ)) := by
  have hGe : G (t:ℂ) = t • w + (G (t:ℂ) - t • w) := by abel
  have hdf : deriv G (t:ℂ) = w + (deriv G (t:ℂ) - w) := by abel
  have hb := alc_inner_bound t w (G (t:ℂ) - t • w) (deriv G (t:ℂ) - w) he hf
  have h1 := (abs_le.mp hb).1
  rw [abs_of_pos htpos] at h1
  have h2 : 0 < t * ‖w‖^2 := mul_pos htpos (pow_pos hwpos 2)
  rw [hGe, hdf]
  nlinarith [h1, h2]

/-- The derivative of `t ↦ ‖G t‖²` is negative just to the left of `0`. -/
lemma alc_deriv_neg {G : ℂ → ℂ} {w : ℂ} {t : ℝ} (htneg : t < 0) (hwpos : 0 < ‖w‖)
    (he : ‖G (t:ℂ) - t • w‖ ≤ (‖w‖/6) * |t|) (hf : ‖deriv G (t:ℂ) - w‖ ≤ ‖w‖/2) :
    2 * inner ℝ (G (t:ℂ)) (deriv G (t:ℂ)) < 0 := by
  have hGe : G (t:ℂ) = t • w + (G (t:ℂ) - t • w) := by abel
  have hdf : deriv G (t:ℂ) = w + (deriv G (t:ℂ) - w) := by abel
  have hb := alc_inner_bound t w (G (t:ℂ) - t • w) (deriv G (t:ℂ) - w) he hf
  have h1 := (abs_le.mp hb).2
  rw [abs_of_neg htneg] at h1
  have h2 : t * ‖w‖^2 < 0 := mul_neg_of_neg_of_pos htneg (pow_pos hwpos 2)
  rw [hGe, hdf]
  nlinarith [h1, h2]

/-- **The analytic core.**  The analytic hypotheses alone produce a single `δ > 0` together
with a linear lower bound `c * |t| ≤ ‖G t‖` and strict monotonicity of `t ↦ ‖G t‖` on
`[0, δ]` (increasing) and on `[-δ, 0]` (decreasing). -/
theorem alc_core {G : ℂ → ℂ} (han : AnalyticAt ℂ G 0) (h0 : G 0 = 0)
    (hd : deriv G 0 ≠ 0) :
    ∃ δ > 0, ∃ c > 0,
      (∀ t : ℝ, |t| < δ → c * |t| ≤ ‖G (t : ℂ)‖) ∧
      StrictMonoOn (fun t : ℝ => ‖G (t : ℂ)‖) (Set.Icc 0 δ) ∧
      StrictAntiOn (fun t : ℝ => ‖G (t : ℂ)‖) (Set.Icc (-δ) 0) := by
  set w : ℂ := deriv G 0 with hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hd
  -- first order expansion `G z - z * w = o z`
  obtain ⟨ρo, hρopos, hρo⟩ : ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → ‖G z - z * w‖ ≤ (‖w‖/6) * ‖z‖ := by
    have hfd : HasFDerivAt G (ContinuousLinearMap.toSpanSingleton ℂ w) 0 :=
      han.differentiableAt.hasDerivAt.hasFDerivAt
    have hlo := hfd.isLittleO
    have hev : ∀ᶠ z in nhds (0:ℂ),
        ‖G z - G 0 - (ContinuousLinearMap.toSpanSingleton ℂ w) (z - 0)‖
          ≤ (‖w‖/6) * ‖z - 0‖ := (isLittleO_iff.mp hlo) (by linarith)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ρ, hρ, hh⟩ := hev
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    have hz' : dist z 0 < ρ := by rwa [dist_zero_right]
    have h := hh hz'
    simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, h0] using h
  -- continuity of `z ↦ deriv G z` at `0`
  obtain ⟨ρc, hρcpos, hρc⟩ : ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → ‖deriv G z - w‖ ≤ ‖w‖/2 := by
    have hcont : ContinuousAt (deriv G) 0 := han.deriv.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨ρ, hρ, hh⟩ := hcont (‖w‖/2) (by linarith)
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    have hz' : dist z 0 < ρ := by rwa [dist_zero_right]
    have h := hh hz'
    rw [dist_eq_norm] at h
    exact le_of_lt h
  -- analyticity radius
  obtain ⟨ρa, hρapos, hρa⟩ : ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ G z := by
    have h := han.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ρ, hρ, hh⟩ := h
    exact ⟨ρ, hρ, fun z hz => hh (by rwa [dist_zero_right])⟩
  set ρ : ℝ := min (min ρo ρc) ρa with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hρopos hρcpos) hρapos
  have hρ_le_ρo : ρ ≤ ρo := by rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ_le_ρc : ρ ≤ ρc := by rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ_le_ρa : ρ ≤ ρa := by rw [hρdef]; exact min_le_right _ _
  set δ : ℝ := ρ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδ_lt_ρ : δ < ρ := by rw [hδdef]; linarith
  set U : ℝ → ℝ := fun t => ‖G (t:ℂ)‖^2 with hUdef
  have hUhasderiv : ∀ t : ℝ, |t| < ρ →
      HasDerivAt U (2 * inner ℝ (G (t:ℂ)) (deriv G (t:ℂ))) t := by
    intro t ht
    have hlt : ‖(t:ℂ)‖ < ρa := by rw [Complex.norm_real]; exact lt_of_lt_of_le ht hρ_le_ρa
    have hdiff : DifferentiableAt ℂ G (t:ℂ) := (hρa (t:ℂ) hlt).differentiableAt
    have hφ : HasDerivAt (fun s : ℝ => G (s:ℂ)) (deriv G (t:ℂ)) t := hdiff.hasDerivAt.comp_ofReal
    have hu : HasDerivAt (fun s : ℝ => ‖G (s:ℂ)‖^2)
        (2 * inner ℝ (G (t:ℂ)) (deriv G (t:ℂ))) t := hφ.norm_sq
    rw [hUdef]
    exact hu
  have hbounds : ∀ t : ℝ, |t| < δ →
      ‖G (t:ℂ) - t • w‖ ≤ (‖w‖/6) * |t| ∧ ‖deriv G (t:ℂ) - w‖ ≤ ‖w‖/2 := by
    intro t ht
    have htρ : |t| < ρ := lt_trans ht hδ_lt_ρ
    have htρo : ‖(t:ℂ)‖ < ρo := by rw [Complex.norm_real]; exact lt_of_lt_of_le htρ hρ_le_ρo
    have htρc : ‖(t:ℂ)‖ < ρc := by rw [Complex.norm_real]; exact lt_of_lt_of_le htρ hρ_le_ρc
    refine ⟨?_, ?_⟩
    · have h := hρo (t:ℂ) htρo
      simpa [Complex.real_smul, Complex.norm_real] using h
    · exact hρc (t:ℂ) htρc
  have hmonoU : StrictMonoOn U (Set.Icc 0 δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · intro t ht
      have htabs : |t| ≤ δ := by rw [abs_of_nonneg ht.1]; exact ht.2
      exact (hUhasderiv t (lt_of_le_of_lt htabs hδ_lt_ρ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxabs : |x| < δ := by rw [abs_of_pos hx.1]; exact hx.2
      obtain ⟨he, hf⟩ := hbounds x hxabs
      rw [(hUhasderiv x (lt_trans hxabs hδ_lt_ρ)).deriv]
      exact alc_deriv_pos hx.1 hwpos he hf
  have hantiU : StrictAntiOn U (Set.Icc (-δ) 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · intro t ht
      have htabs : |t| ≤ δ := by rw [abs_of_nonpos ht.2]; linarith [ht.1]
      exact (hUhasderiv t (lt_of_le_of_lt htabs hδ_lt_ρ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxabs : |x| < δ := by rw [abs_of_neg hx.2]; linarith [hx.1]
      obtain ⟨he, hf⟩ := hbounds x hxabs
      rw [(hUhasderiv x (lt_trans hxabs hδ_lt_ρ)).deriv]
      exact alc_deriv_neg hx.2 hwpos he hf
  have hv : ∀ t : ℝ, ‖G (t:ℂ)‖ = Real.sqrt (U t) := by
    intro t
    rw [hUdef]
    exact (Real.sqrt_sq (norm_nonneg (G (t:ℂ)))).symm
  have hvmono : StrictMonoOn (fun t : ℝ => ‖G (t:ℂ)‖) (Set.Icc 0 δ) := by
    intro a ha b hb hab
    change ‖G (a:ℂ)‖ < ‖G (b:ℂ)‖
    rw [hv a, hv b]
    exact Real.sqrt_lt_sqrt (by rw [hUdef]; positivity) (hmonoU ha hb hab)
  have hvanti : StrictAntiOn (fun t : ℝ => ‖G (t:ℂ)‖) (Set.Icc (-δ) 0) := by
    intro a ha b hb hab
    change ‖G (b:ℂ)‖ < ‖G (a:ℂ)‖
    rw [hv a, hv b]
    exact Real.sqrt_lt_sqrt (by rw [hUdef]; positivity) (hantiU ha hb hab)
  have hlow : ∀ t : ℝ, |t| < δ → (5*‖w‖/6) * |t| ≤ ‖G (t:ℂ)‖ := by
    intro t ht
    have htρ : |t| < ρ := lt_trans ht hδ_lt_ρ
    have htρo : ‖(t:ℂ)‖ < ρo := by rw [Complex.norm_real]; exact lt_of_lt_of_le htρ hρ_le_ρo
    have h := hρo (t:ℂ) htρo
    have hb : ‖G (t:ℂ) - (t:ℂ)*w‖ ≤ (‖w‖/6) * |t| := by
      simpa [Complex.norm_real] using h
    have key : ‖(t:ℂ) * w‖ ≤ ‖G (t:ℂ)‖ + ‖G (t:ℂ) - (t:ℂ)*w‖ := by
      have hh := norm_sub_le (G (t:ℂ)) (G (t:ℂ) - (t:ℂ)*w)
      simpa using hh
    have hnorm : ‖(t:ℂ) * w‖ = |t| * ‖w‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at key
    nlinarith [key, hb]
  exact ⟨δ, hδpos, 5*‖w‖/6, by linarith, hlow, hvmono, hvanti⟩

/-- If `v` is continuous on `[0, δ]`, strictly increasing there, `v 0 = 0` and
`0 < μ < v δ`, then `μ` has a unique preimage in `(0, δ)`. -/
lemma alc_existsUnique_Ioo_of_strictMonoOn {v : ℝ → ℝ} {δ μ : ℝ} (hδpos : 0 < δ)
    (hcont : ContinuousOn v (Set.Icc 0 δ)) (hmono : StrictMonoOn v (Set.Icc 0 δ))
    (hv0 : v 0 = 0) (hμpos : 0 < μ) (hμδ : μ < v δ) :
    ∃! t : ℝ, t ∈ Set.Ioo (0:ℝ) δ ∧ v t = μ := by
  have hmem : μ ∈ v '' Set.Ioo (0:ℝ) δ :=
    (intermediate_value_Ioo hδpos.le hcont) (by rw [hv0]; exact ⟨hμpos, hμδ⟩)
  obtain ⟨t, ht, hvt⟩ := hmem
  refine ⟨t, ⟨ht, hvt⟩, ?_⟩
  intro y hy
  exact hmono.injOn ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    (by rw [hy.2, hvt])

/-- If `v` is continuous on `[-δ, 0]`, strictly decreasing there, `v 0 = 0` and
`0 < μ < v (-δ)`, then `μ` has a unique preimage in `(-δ, 0)`. -/
lemma alc_existsUnique_Ioo_of_strictAntiOn {v : ℝ → ℝ} {δ μ : ℝ} (hδpos : 0 < δ)
    (hcont : ContinuousOn v (Set.Icc (-δ) 0)) (hanti : StrictAntiOn v (Set.Icc (-δ) 0))
    (hv0 : v 0 = 0) (hμpos : 0 < μ) (hμδ : μ < v (-δ)) :
    ∃! t : ℝ, t ∈ Set.Ioo (-δ) 0 ∧ v t = μ := by
  have hcont' : ContinuousOn (fun t => -v t) (Set.Icc (-δ) 0) := hcont.neg
  have hmem : (-μ) ∈ (fun t => -v t) '' Set.Ioo (-δ) 0 :=
    (intermediate_value_Ioo (by linarith : -δ ≤ (0:ℝ)) hcont')
      (by constructor <;> linarith [hv0, hμpos, hμδ])
  obtain ⟨t, ht, hvt⟩ := hmem
  have hvt' : v t = μ := by linarith [hvt]
  refine ⟨t, ⟨ht, hvt'⟩, ?_⟩
  intro y hy
  exact hanti.injOn ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    (by rw [hy.2, hvt'])

theorem analytic_local_crossing {G : ℂ → ℂ} (han : AnalyticAt ℂ G 0) (h0 : G 0 = 0)
    (hd : deriv G 0 ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∃ μ₀ > 0,
      (∀ t : ℝ, |t| < δ → t ≠ 0 → c * |t| ≤ ‖G (t : ℂ)‖) ∧
      (∀ μ ∈ Set.Ioo (0 : ℝ) μ₀,
        (∃! t : ℝ, t ∈ Set.Ioo (0 : ℝ) δ ∧ ‖G (t : ℂ)‖ = μ) ∧
        (∃! t : ℝ, t ∈ Set.Ioo (-δ) 0 ∧ ‖G (t : ℂ)‖ = μ)) := by
  obtain ⟨δ, hδpos, c, hcpos, hlow, hmono, hanti⟩ := alc_core han h0 hd
  obtain ⟨ρa, hρapos, haρ⟩ : ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ G z := by
    have h := han.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ρ, hρ, hh⟩ := h
    exact ⟨ρ, hρ, fun z hz => hh (by rwa [dist_zero_right])⟩
  set δ' : ℝ := min δ (ρa / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos (by linarith)
  have hδ'leδ : δ' ≤ δ := min_le_left _ _
  have hδ'ltrho : δ' < ρa := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hvcont_at : ∀ t : ℝ, |t| < ρa → ContinuousAt (fun t : ℝ => ‖G (t:ℂ)‖) t := by
    intro t ht
    have hlt : ‖(t:ℂ)‖ < ρa := by simpa [Complex.norm_real] using ht
    exact ((haρ (t:ℂ) hlt).continuousAt.comp Complex.continuous_ofReal.continuousAt).norm
  have hvcont0 : ContinuousOn (fun t : ℝ => ‖G (t:ℂ)‖) (Set.Icc 0 δ') := by
    intro t ht
    refine (hvcont_at t ?_).continuousWithinAt
    rw [abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hδ'ltrho
  have hvcontneg : ContinuousOn (fun t : ℝ => ‖G (t:ℂ)‖) (Set.Icc (-δ') 0) := by
    intro t ht
    refine (hvcont_at t ?_).continuousWithinAt
    rw [abs_of_nonpos ht.2]
    linarith [ht.1, hδ'ltrho]
  have hmono' : StrictMonoOn (fun t : ℝ => ‖G (t:ℂ)‖) (Set.Icc 0 δ') :=
    hmono.mono (Set.Icc_subset_Icc_right hδ'leδ)
  have hanti' : StrictAntiOn (fun t : ℝ => ‖G (t:ℂ)‖) (Set.Icc (-δ') 0) :=
    hanti.mono (Set.Icc_subset_Icc_left (by linarith))
  have hv0 : (fun t : ℝ => ‖G (t:ℂ)‖) 0 = 0 := by simp [h0]
  have hvδ'pos : 0 < (fun t : ℝ => ‖G (t:ℂ)‖) δ' := by
    have h1 : (fun t : ℝ => ‖G (t:ℂ)‖) 0 < (fun t : ℝ => ‖G (t:ℂ)‖) δ' :=
      hmono' ⟨le_rfl, hδ'pos.le⟩ ⟨hδ'pos.le, le_rfl⟩ hδ'pos
    rwa [hv0] at h1
  have hvnegpos : 0 < (fun t : ℝ => ‖G (t:ℂ)‖) (-δ') := by
    have h1 : (fun t : ℝ => ‖G (t:ℂ)‖) 0 < (fun t : ℝ => ‖G (t:ℂ)‖) (-δ') :=
      hanti' ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    rwa [hv0] at h1
  refine ⟨δ', hδ'pos, c, hcpos,
    min ((fun t : ℝ => ‖G (t:ℂ)‖) δ') ((fun t : ℝ => ‖G (t:ℂ)‖) (-δ')),
    lt_min hvδ'pos hvnegpos, ?_, ?_⟩
  · intro t ht _
    exact hlow t (lt_of_lt_of_le ht hδ'leδ)
  · intro μ hμ
    have hμpos : 0 < μ := hμ.1
    have hμlt1 : μ < (fun t : ℝ => ‖G (t:ℂ)‖) δ' := lt_of_lt_of_le hμ.2 (min_le_left _ _)
    have hμlt2 : μ < (fun t : ℝ => ‖G (t:ℂ)‖) (-δ') := lt_of_lt_of_le hμ.2 (min_le_right _ _)
    exact ⟨alc_existsUnique_Ioo_of_strictMonoOn hδ'pos hvcont0 hmono' hv0 hμpos hμlt1,
           alc_existsUnique_Ioo_of_strictAntiOn hδ'pos hvcontneg hanti' hv0 hμpos hμlt2⟩

end

end Work.ELRig
