import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_EllLimOK.SliceTrace.tendsto_self_at_pi_div_two_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pinning lemma: `cos θ · f θ → 0` at `π/2`

If `∫_0^{π/2} (f θ / cos θ)² dθ` is finite and `cos θ · f θ` has a limit `J` as
`θ → (π/2)⁻`, then `J = 0`.

The reason is quantitative.  Writing `g θ = cos θ · f θ`, the integrand is
`(g θ / cos²θ)² = g θ² / cos⁴θ`, and near `θ = π/2` we have `cos x ≤ π/2 - x`, so
`1/cos⁴x ≥ 1/(π/2 - x)⁴`.  If `|g| > d > 0` on a tail `(t, π/2)`, then on the short
interval `(π/2 - θ, π/2)` (length `θ`) the integrand exceeds `d²/θ⁴`, whence

`d²/θ³ ≤ ∫_{π/2-θ}^{π/2} (f/cos)² ≤ ∫_t^{π/2} (f/cos)²`,

which is impossible for small `θ`.  So every `d > 0` is attained as a bound on `g`
somewhere in the tail, which forces the limit to be `0`.

This is the `1/cos⁴`-analogue of
`Work.FTS_EllLimOK.SliceTrace.exists_abs_le_of_integrable_inv_cos_sq_aux` (which is the
`1/cos²` statement for `f` itself).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_EllLimOK.Pinning

/-- **No small value of `cos · f` forces a divergent integral of `(f / cos)²`.**  If
`∫_t^{π/2} (f θ / cos θ)² dθ` is finite and `t ∈ (0, π/2)`, then for every `d > 0` the
function `cos · f` takes a value of modulus at most `d` somewhere on `(t, π/2)`.

Indeed, if `|cos x · f x| > d` on all of `(t, π/2)`, then on `(π/2 - θ, π/2)` we have
`cos x ≤ θ`, hence `(f x / cos x)² = (cos x · f x)²/cos⁴x > d²/θ⁴`, so
`d²/θ³ ≤ ∫_{π/2-θ}^{π/2} (f/cos)² ≤ ∫_t^{π/2} (f/cos)²`, impossible for small `θ`. -/
theorem exists_abs_le_cos_mul_of_integrable_div_cos_sq {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2)
      (Set.Ioo t (Real.pi / 2)))
    {d : ℝ} (hd : 0 < d) :
    ∃ τ ∈ Set.Ioo t (Real.pi / 2), |Real.cos τ * f τ| ≤ d := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set G : ℝ → ℝ := fun θ => (f θ / Real.cos θ) ^ 2 with hG
  set D : ℝ := ∫ θ in Set.Ioo t (Real.pi / 2), G θ with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact MeasureTheory.integral_nonneg fun x => by rw [hG]; positivity
  -- the key lower bound `d²/θ³ ≤ D` for every short tail length `θ`
  have hmain : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2 - t), d ^ 2 / θ ^ 3 ≤ D := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθu : θ < Real.pi / 2 - t := hθ.2
    have hsub : Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2) ⊆ Set.Ioo t (Real.pi / 2) := by
      intro x hx
      exact ⟨by linarith [hx.1, hθu], hx.2⟩
    have hGs : IntegrableOn G (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) := hint.mono_set hsub
    have hconst : IntegrableOn (fun _ : ℝ => d ^ 2 / θ ^ 4)
        (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) := by
      apply integrableOn_const
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · finiteness
    have hpoint : ∀ x ∈ Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), d ^ 2 / θ ^ 4 ≤ G x := by
      intro x hx
      have hx1 : Real.pi / 2 - θ < x := hx.1
      have hx2 : x < Real.pi / 2 := hx.2
      have hxpos : 0 < x := by linarith [hx1, hθu, ht.1, Real.pi_pos]
      have hcos_pos : 0 < Real.cos x :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hxpos], hx2⟩
      have hcos_le : Real.cos x ≤ θ := by
        have hc : Real.cos x = Real.sin (Real.pi / 2 - x) := (Real.sin_pi_div_two_sub x).symm
        rw [hc]
        calc Real.sin (Real.pi / 2 - x) ≤ Real.pi / 2 - x := Real.sin_le (by linarith)
          _ ≤ θ := by linarith [hx1]
      have hfx : d < |Real.cos x * f x| := hcon x ⟨by linarith [hx1, hθu], hx2⟩
      -- `d ≤ cos x · |f x|`, hence `d² ≤ cos²x · f x²`
      have hP : d ≤ Real.cos x * |f x| := by
        rw [abs_mul, abs_of_pos hcos_pos] at hfx
        exact hfx.le
      have hg2 : d ^ 2 ≤ (Real.cos x) ^ 2 * (f x) ^ 2 := by
        have h1 : d ^ 2 ≤ (Real.cos x * |f x|) ^ 2 := pow_le_pow_left₀ hd.le hP 2
        have h2 : (Real.cos x * |f x|) ^ 2 = (Real.cos x) ^ 2 * (f x) ^ 2 := by
          rw [mul_pow, sq_abs]
        rwa [h2] at h1
      -- `(cos x)⁴ ≤ θ⁴`
      have hcos4 : (Real.cos x) ^ 4 ≤ θ ^ 4 := pow_le_pow_left₀ hcos_pos.le hcos_le 4
      have hkey : d ^ 2 * (Real.cos x) ^ 2 ≤ (f x) ^ 2 * θ ^ 4 :=
        calc d ^ 2 * (Real.cos x) ^ 2
            ≤ ((Real.cos x) ^ 2 * (f x) ^ 2) * (Real.cos x) ^ 2 :=
              mul_le_mul_of_nonneg_right hg2 (sq_nonneg _)
          _ = (f x) ^ 2 * (Real.cos x) ^ 4 := by ring
          _ ≤ (f x) ^ 2 * θ ^ 4 := mul_le_mul_of_nonneg_left hcos4 (sq_nonneg _)
      have hgoal : d ^ 2 / θ ^ 4 ≤ (f x / Real.cos x) ^ 2 := by
        rw [div_pow, div_le_div_iff₀ (by positivity : (0 : ℝ) < θ ^ 4)
          (by positivity : (0 : ℝ) < Real.cos x ^ 2)]
        exact hkey
      simpa [hG] using hgoal
    have hmono : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 / θ ^ 4 : ℝ)
        ≤ ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), G x :=
      setIntegral_mono_on hconst hGs measurableSet_Ioo hpoint
    have hval : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 / θ ^ 4 : ℝ)
        = d ^ 2 / θ ^ 3 := by
      rw [setIntegral_const, Real.volume_real_Ioo,
        max_eq_left (show (0 : ℝ) ≤ Real.pi / 2 - (Real.pi / 2 - θ) by linarith), smul_eq_mul]
      field_simp
      ring
    have hb : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), G x ≤ D := by
      rw [hD]
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => by rw [hG]; positivity) ?_
      exact Filter.Eventually.of_forall fun x hx => hsub hx
    linarith [hval ▸ hmono, hb]
  -- choose a tail length short enough that `d²/θ³ > D`
  set δ : ℝ := min 1 (d ^ 2 / (D + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos (by positivity) (by linarith))
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hδle : δ ≤ d ^ 2 / (D + 1) := min_le_right _ _
  have hD1 : 0 < D + 1 := by linarith
  have hδ3 : δ ^ 3 ≤ d ^ 2 / (D + 1) := by
    have h1 : δ ^ 2 ≤ d ^ 2 / (D + 1) :=
      calc δ ^ 2 = δ * δ := by ring
        _ ≤ δ * (d ^ 2 / (D + 1)) := mul_le_mul_of_nonneg_left hδle hδpos.le
        _ ≤ 1 * (d ^ 2 / (D + 1)) := mul_le_mul_of_nonneg_right hδle1 (by positivity)
        _ = d ^ 2 / (D + 1) := one_mul _
    calc δ ^ 3 = δ ^ 2 * δ := by ring
      _ ≤ (d ^ 2 / (D + 1)) * δ := mul_le_mul_of_nonneg_right h1 hδpos.le
      _ ≤ (d ^ 2 / (D + 1)) * 1 := mul_le_mul_of_nonneg_left hδle1 (by positivity)
      _ = d ^ 2 / (D + 1) := mul_one _
  set m : ℝ := min δ (Real.pi / 2 - t) with hm
  have hmpos : 0 < m := lt_min hδpos (by linarith [ht.2])
  have hmleδ : m ≤ δ := min_le_left _ _
  have hmlept : m ≤ Real.pi / 2 - t := min_le_right _ _
  have hmem : m / 2 ∈ Set.Ioo 0 (Real.pi / 2 - t) := ⟨by linarith, by linarith⟩
  have h1 := hmain (m / 2) hmem
  have hθ3 : (m / 2) ^ 3 ≤ d ^ 2 / (D + 1) := by
    have hm2 : m / 2 ≤ δ := by linarith [hmleδ, hmpos]
    calc (m / 2) ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (by linarith) hm2 3
      _ ≤ d ^ 2 / (D + 1) := hδ3
  have hθ3pos : 0 < (m / 2) ^ 3 := by positivity
  have h2 : D + 1 ≤ d ^ 2 / (m / 2) ^ 3 := by
    rw [le_div_iff₀ hθ3pos]
    calc (D + 1) * (m / 2) ^ 3 ≤ (D + 1) * (d ^ 2 / (D + 1)) :=
          mul_le_mul_of_nonneg_left hθ3 hD1.le
      _ = d ^ 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ (d ^ 2) (ne_of_gt hD1)]
  linarith [h1, h2]

theorem tendsto_cos_mul_eq_zero_of_integrable_div_cos_sq {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ / Real.cos θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)))
    (hlim : ∃ J : ℝ, Filter.Tendsto (fun θ : ℝ => Real.cos θ * f θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds J)) :
    Filter.Tendsto (fun θ : ℝ => Real.cos θ * f θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨J, hJ⟩ := hlim
  -- the limit `J` must be `0`: otherwise `|cos · f| > d > 0` on a tail, contradicting
  -- the existence of a point where `|cos · f| ≤ d`
  have hJ0 : J = 0 := by
    by_contra hJne
    have hJpos : 0 < |J| := abs_pos.mpr hJne
    set d : ℝ := |J| / 2 with hddef
    have hd : 0 < d := by rw [hddef]; linarith [hJpos]
    have hdJ : d < |J| := by rw [hddef]; exact half_lt_self hJpos
    have hopen : IsOpen {y : ℝ | d < |y|} := isOpen_lt continuous_const continuous_abs
    have hgood : {y : ℝ | d < |y|} ∈ 𝓝 J := hopen.mem_nhds hdJ
    have hev : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), d < |Real.cos θ * f θ| := hJ.eventually hgood
    obtain ⟨t₀, ht₀lt, hsub₀⟩ := (nhdsLT_basis (Real.pi / 2)).mem_iff.mp hev
    set t : ℝ := max t₀ (Real.pi / 4) with htdef
    have ht_mem : t ∈ Set.Ioo 0 (Real.pi / 2) := by
      rw [htdef, Set.mem_Ioo]
      exact ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) (le_max_right t₀ (Real.pi / 4)),
        max_lt ht₀lt (by linarith [Real.pi_pos])⟩
    have hsub : Set.Ioo t (Real.pi / 2) ⊆ {θ | d < |Real.cos θ * f θ|} := by
      intro θ hθ
      exact hsub₀ ⟨lt_of_le_of_lt (le_max_left t₀ (Real.pi / 4)) hθ.1, hθ.2⟩
    have hint' : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2)
        (Set.Ioo t (Real.pi / 2)) :=
      hint.mono_set (Set.Ioo_subset_Ioo ht_mem.1.le le_rfl)
    obtain ⟨τ, hτ, hτle⟩ := exists_abs_le_cos_mul_of_integrable_div_cos_sq ht_mem hint' hd
    exact absurd (hsub hτ) (not_lt.mpr hτle)
  rw [hJ0] at hJ
  exact hJ

end Work.FTS_EllLimOK.Pinning
