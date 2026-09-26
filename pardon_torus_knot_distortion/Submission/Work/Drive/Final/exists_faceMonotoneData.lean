import Mathlib

namespace Work.Drive.Final

open Set Filter
open scoped Topology

/-- The norm on `ℝ × ℝ` is the sup norm. -/
private lemma norm_pair (a b : ℝ) : ‖((a, b) : ℝ × ℝ)‖ = max |a| |b| := by
  rw [Prod.norm_def]; simp [Real.norm_eq_abs]

/-- The norm of a difference of pairs. -/
private lemma norm_pair_sub (a b c d : ℝ) :
    ‖((a, b) : ℝ × ℝ) - ((c, d) : ℝ × ℝ)‖ = max |a - c| |b - d| := by
  rw [show ((a, b) : ℝ × ℝ) - ((c, d) : ℝ × ℝ) = (a - c, b - d) from by simp, norm_pair]

/-- Mean value bound for `p ↦ V p - c * p.1`: if `fderiv V` is `ε`-close to `fst` on a ball of
radius `R` around the origin, then `V p - c * p.1` is Lipschitz with constant `ε + |1 - c|`
there.  (The constant `c` is chosen so that the derivative `fderiv V - c • fst` stays small.) -/
private lemma norm_diff_mul_fst_bound (V : ℝ × ℝ → ℝ) {R ε c : ℝ}
    (hdiff : ∀ q : ℝ × ℝ, ‖q‖ < R → DifferentiableAt ℝ V q)
    (hbdd : ∀ q : ℝ × ℝ, ‖q‖ < R → ‖fderiv ℝ V q - ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ ε)
    {p₁ p₂ : ℝ × ℝ} (h₁ : ‖p₁‖ < R) (h₂ : ‖p₂‖ < R) :
    |(V p₂ - c * p₂.1) - (V p₁ - c * p₁.1)| ≤ (ε + |1 - c|) * ‖p₂ - p₁‖ := by
  have hconv : Convex ℝ (Metric.ball (0 : ℝ × ℝ) R) := convex_ball 0 R
  have hGdiff : ∀ q ∈ Metric.ball (0 : ℝ × ℝ) R,
      DifferentiableAt ℝ (fun p : ℝ × ℝ => V p - c * p.1) q := by
    intro q hq
    have hq' : ‖q‖ < R := by simpa [Metric.mem_ball] using hq
    exact (hdiff q hq').sub (differentiableAt_fst.const_mul c)
  have hGderiv : ∀ q ∈ Metric.ball (0 : ℝ × ℝ) R,
      fderiv ℝ (fun p : ℝ × ℝ => V p - c * p.1) q
        = fderiv ℝ V q - c • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    intro q hq
    have hq' : ‖q‖ < R := by simpa [Metric.mem_ball] using hq
    change fderiv ℝ (V - fun y : ℝ × ℝ => c * y.1) q
        = fderiv ℝ V q - c • ContinuousLinearMap.fst ℝ ℝ ℝ
    rw [fderiv_sub (hdiff q hq') (differentiableAt_fst.const_mul c),
      fderiv_const_mul differentiableAt_fst c, fderiv_fst]
  have hbound : ∀ q ∈ Metric.ball (0 : ℝ × ℝ) R,
      ‖fderiv ℝ (fun p : ℝ × ℝ => V p - c * p.1) q‖ ≤ ε + |1 - c| := by
    intro q hq
    have hq' : ‖q‖ < R := by simpa [Metric.mem_ball] using hq
    rw [hGderiv q hq]
    have heq : fderiv ℝ V q - c • ContinuousLinearMap.fst ℝ ℝ ℝ
        = (fderiv ℝ V q - ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (1 - c) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
      rw [sub_smul (1:ℝ) c (ContinuousLinearMap.fst ℝ ℝ ℝ),
        one_smul ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)]
      abel
    rw [heq]
    calc ‖(fderiv ℝ V q - ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (1 - c) • ContinuousLinearMap.fst ℝ ℝ ℝ‖
        ≤ ‖fderiv ℝ V q - ContinuousLinearMap.fst ℝ ℝ ℝ‖
          + ‖(1 - c) • ContinuousLinearMap.fst ℝ ℝ ℝ‖ := norm_add_le _ _
      _ ≤ ε + |1 - c| := by
          have hb := hbdd q hq'
          have h2 : ‖(1 - c) • ContinuousLinearMap.fst ℝ ℝ ℝ‖ = |1 - c| := by
            rw [norm_smul, ContinuousLinearMap.norm_fst]
            simp
          rw [h2]; linarith
  have h1' : p₁ ∈ Metric.ball (0:ℝ×ℝ) R := by simpa [Metric.mem_ball] using h₁
  have h2' : p₂ ∈ Metric.ball (0:ℝ×ℝ) R := by simpa [Metric.mem_ball] using h₂
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Metric.ball (0:ℝ×ℝ) R)
      (f := fun p : ℝ × ℝ => V p - c * p.1) hGdiff hbound hconv h1' h2'
  simpa using hmain

/-- Local monotonicity data of a function `V : ℝ × ℝ → ℝ` whose derivative at the origin is
`fst`: there is a radius `δ₀` such that for every `0 < δ ≤ δ₀` one finds `xstar ∈ (-δ, δ)` with
`V (xstar, ·) > 0` on `(-δ, δ)`, and with `V` monotone in the first variable throughout the box
on the region where it is positive.

This is the elementary "face monotonicity" input of Pardon's argument: near a point where the
`x`-derivative is `1` and the `y`-derivative vanishes, the positive set is a vertical graph-like
monotone region. -/
theorem exists_faceMonotoneData (V : ℝ × ℝ → ℝ) (hV0 : V 0 = 0)
    (hVsmooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V 0)
    (hdV : fderiv ℝ V 0 = ContinuousLinearMap.fst ℝ ℝ ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ xstar : ℝ, xstar ∈ Set.Ioo (-δ) δ ∧
        (∀ x x' y : ℝ, x ∈ Set.Ioo (-δ) δ → x' ∈ Set.Ioo x δ → y ∈ Set.Ioo (-δ) δ →
          0 < V (x, y) → 0 < V (x', y)) ∧
        (∀ y ∈ Set.Ioo (-δ) δ, 0 < V (xstar, y)) := by
  -- `fderiv V` is continuous at the origin, where it equals `fst`.
  have hcont : ContinuousAt (fderiv ℝ V) (0 : ℝ × ℝ) :=
    hVsmooth.continuousAt_fderiv (by simp)
  obtain ⟨R₁, hR₁pos, hR₁⟩ := (Metric.continuousAt_iff.mp hcont) (1/4) (by norm_num)
  -- `V` is differentiable on a neighbourhood of the origin.
  have hdiffev : ∀ᶠ q : ℝ × ℝ in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ V q := by
    have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞) V 0 := hVsmooth.of_le (by simp)
    have h2 : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), ContDiffAt ℝ (1 : WithTop ℕ∞) V q :=
      h1.eventually (by simp)
    filter_upwards [h2] with q hq
    exact hq.differentiableAt (by norm_num)
  obtain ⟨R₂, hR₂pos, hR₂⟩ := Metric.eventually_nhds_iff.mp hdiffev
  set R := min R₁ R₂ with hRdef
  have hRpos : 0 < R := lt_min hR₁pos hR₂pos
  have hdiffR : ∀ q : ℝ × ℝ, ‖q‖ < R → DifferentiableAt ℝ V q := by
    intro q hq
    exact hR₂ (by simpa using lt_of_lt_of_le hq (min_le_right _ _))
  have hbddR : ∀ q : ℝ × ℝ, ‖q‖ < R →
      ‖fderiv ℝ V q - ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1/4 := by
    intro q hq
    have h := hR₁ (by simpa using lt_of_lt_of_le hq (min_le_left _ _))
    rw [hdV, dist_eq_norm] at h
    exact le_of_lt h
  refine ⟨R/2, by linarith, ?_⟩
  intro δ hδ hδR
  have hδR' : δ < R := by linarith
  -- every point of the box `(-δ,δ)²` lies in the ball of radius `R`.
  have hbox : ∀ a b : ℝ, |a| < δ → |b| < δ → ‖((a, b) : ℝ × ℝ)‖ < R := by
    intro a b h1 h2
    rw [norm_pair]
    exact lt_of_lt_of_le (max_lt h1 h2) (le_of_lt hδR')
  refine ⟨δ/2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · -- monotonicity in the first variable
    intro x x' y hx hx' hy hVpos
    have hxδ : |x| < δ := abs_lt.mpr ⟨hx.1, hx.2⟩
    have hx'δ : |x'| < δ := abs_lt.mpr ⟨by linarith [hx.1, hx'.1], hx'.2⟩
    have hyδ : |y| < δ := abs_lt.mpr ⟨hy.1, hy.2⟩
    have hxx' : x < x' := hx'.1
    have hpx : ‖((x, y) : ℝ × ℝ)‖ < R := hbox x y hxδ hyδ
    have hpx' : ‖((x', y) : ℝ × ℝ)‖ < R := hbox x' y hx'δ hyδ
    have hb : |(V (x', y) - 3/4 * x') - (V (x, y) - 3/4 * x)|
        ≤ (1/2 : ℝ) * (x' - x) := by
      have h := norm_diff_mul_fst_bound V hdiffR hbddR (c := 3/4) hpx hpx'
      have hc : (1/4 : ℝ) + |1 - (3/4:ℝ)| = 1/2 := by norm_num
      have hnorm : ‖((x', y) : ℝ × ℝ) - ((x, y) : ℝ × ℝ)‖ = x' - x := by
        rw [norm_pair_sub, sub_self, abs_zero, max_eq_left (abs_nonneg _),
          abs_of_pos (sub_pos.mpr hxx')]
      rw [hc, hnorm] at h
      simpa using h
    have hb1 := (abs_le.mp hb).1
    have : (0 : ℝ) < V (x', y) - V (x, y) := by linarith
    linarith
  · -- `xstar = δ/2` is a level above zero
    intro y hy
    have hyδ : |y| < δ := abs_lt.mpr ⟨hy.1, hy.2⟩
    have hhalfδ : |(δ/2 : ℝ)| < δ := by
      rw [abs_of_pos (by linarith : (0:ℝ) < δ/2)]; linarith
    have hp : ‖((δ/2, y) : ℝ × ℝ)‖ < R := hbox (δ/2) y hhalfδ hyδ
    have hzero : ‖(0 : ℝ × ℝ)‖ < R := by simpa using hRpos
    have hb : |V ((δ/2, y) : ℝ × ℝ) - δ/2| ≤ (1/4) * ‖((δ/2, y) : ℝ × ℝ)‖ := by
      have h := norm_diff_mul_fst_bound V hdiffR hbddR (c := 1) hzero hp
      have hc : (1/4 : ℝ) + |1 - (1:ℝ)| = 1/4 := by norm_num
      rw [hc] at h
      simpa [hV0] using h
    have hnormp : ‖((δ/2, y) : ℝ × ℝ)‖ < δ := by
      rw [norm_pair]
      exact max_lt hhalfδ hyδ
    have h2 : (1/4) * ‖((δ/2, y) : ℝ × ℝ)‖ < (1/4) * δ :=
      mul_lt_mul_of_pos_left hnormp (by norm_num)
    have h3 := (abs_lt.mp (lt_of_le_of_lt hb h2)).1
    have : (0 : ℝ) < V ((δ/2, y) : ℝ × ℝ) := by linarith
    exact this

end Work.Drive.Final
