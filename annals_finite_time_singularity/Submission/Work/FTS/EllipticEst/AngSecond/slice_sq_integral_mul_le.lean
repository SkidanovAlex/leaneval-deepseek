import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open MeasureTheory

/-- **Nonnegativity of a set integral without measurability of the set.**

If `f` is a.e. measurable for `volume.restrict s` and `f ≥ 0` pointwise on `s`, then
`0 ≤ ∫ x in s, f x`.  No measurability of `s` is assumed, which is what the weighted
Cauchy–Schwarz inequality below needs: the slice integrands are only known to be integrable.

Route: if `g` is a measurable function with `f =ᵐ[volume.restrict s] g`, then
`{x | f x < 0} ⊆ {x | f x ≠ g x} ∪ {x | g x < 0}`; the first piece is null by the a.e. equality,
and the second is a *measurable* set, so `Measure.restrict_apply` computes its measure as
`volume ({g < 0} ∩ s)`, which vanishes since `{g < 0} ∩ s ⊆ {f ≠ g} ∩ s` (here `f ≥ 0` on `s` is
used) and `volume ({f ≠ g} ∩ s) ≤ (volume.restrict s) {f ≠ g} = 0`. -/
private lemma setIntegral_nonneg_of_forall_mem {s : Set ℝ} {f : ℝ → ℝ}
    (hf : AEMeasurable f (MeasureTheory.volume.restrict s)) (h : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ ∫ x in s, f x := by
  obtain ⟨g, hgm, hfg⟩ := hf
  refine MeasureTheory.setIntegral_nonneg_of_ae_restrict ?_
  have hne : (MeasureTheory.volume.restrict s) {x : ℝ | f x ≠ g x} = 0 :=
    (MeasureTheory.ae_iff).mp hfg
  have hmeas : MeasurableSet {x : ℝ | g x < 0} := by
    simpa using measurableSet_lt hgm measurable_const
  have hg0 : (MeasureTheory.volume.restrict s) {x : ℝ | g x < 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hmeas]
    refine MeasureTheory.measure_mono_null ?_
      (MeasureTheory.Measure.measure_inter_eq_zero_of_restrict hne)
    intro x hx
    refine ⟨?_, hx.2⟩
    intro hc
    have h1 : 0 ≤ g x := hc ▸ h x hx.2
    exact absurd h1 (not_le.mpr hx.1)
  have hsub : {x : ℝ | ¬ 0 ≤ f x} ⊆ {x : ℝ | f x ≠ g x} ∪ {x : ℝ | g x < 0} := by
    intro x hx
    by_cases h1 : f x = g x
    · refine Or.inr ?_
      show g x < 0
      rw [← h1]
      exact not_le.mp hx
    · exact Or.inl h1
  have h0 : (MeasureTheory.volume.restrict s) {x : ℝ | ¬ 0 ≤ f x} = 0 := by
    refine MeasureTheory.measure_mono_null hsub ?_
    rw [MeasureTheory.measure_union_null_iff]
    exact ⟨hne, hg0⟩
  exact (MeasureTheory.ae_iff).mpr h0

/-- A real quadratic `t ↦ a - 2 b t + c t²` that is nonnegative for every real `t` has
nonnegative discriminant: `b ^ 2 ≤ a * c`. -/
private lemma quad_nonneg_discr {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  have ha : 0 ≤ a := by simpa using h 0
  -- adding the inequality at `u` and at `-u` kills the linear term
  have hsum : ∀ u : ℝ, 0 ≤ a + u ^ 2 * c := by
    intro u
    nlinarith [h u, h (-u)]
  have hc : 0 ≤ c := by
    by_contra hneg
    simp only [not_le] at hneg
    have hpos : (0 : ℝ) < -c := by linarith
    have hsq : a / (-c) < (a / (-c) + 1) ^ 2 := by
      have hK : 0 ≤ a / (-c) := div_nonneg ha (le_of_lt hpos)
      nlinarith
    have h2 : a < (a / (-c) + 1) ^ 2 * (-c) := (div_lt_iff₀ hpos).mp hsq
    have hbad := hsum (a / (-c) + 1)
    have hfin : a + (a / (-c) + 1) ^ 2 * c < 0 := by nlinarith [h2]
    linarith
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- `c = 0`: the hypothesis forces `b = 0`
    have hb : b = 0 := by
      by_contra hb
      have h' := h ((a + |a| + 1) / (2 * b))
      have h2 : 2 * ((a + |a| + 1) / (2 * b)) * b = a + |a| + 1 := by
        field_simp
      rw [hc0] at h'
      nlinarith [h', h2, abs_nonneg a]
    rw [hb, hc0.symm]
    norm_num
  · -- `c > 0`: evaluate at `t = b / c`
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have h' := h (b / c)
    have h2 : 2 * (b / c) * b = 2 * (b ^ 2 / c) := by ring
    have h3 : (b / c) ^ 2 * c = b ^ 2 / c := by
      rw [div_pow]; field_simp
    rw [h2, h3] at h'
    have h4 : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hcpos] at h4
    exact h4

/-- **Weighted Cauchy–Schwarz on a single angular slice.**

For integrable `F²κ`, `G²κ`, `FGκ` with `κ ≥ 0` on `s`, the square of `∫_s FGκ` is bounded by
the product of the integrals of `F²κ` and `G²κ`.  No measurability of `F`, `G` themselves is
assumed (only the three weight products are integrable), which is exactly the form needed by
`IP_cauchy_schwarz`: the slice integrands there are `g²·w²σ`, `h²·w²σ`, `gh·w²σ` and nothing
is known about the measurability of the slices of `g`, `h`.

Route: for every real `t`, the function `(F - t·G)²·κ ≥ 0` is integrable and a.e. strongly
measurable (it is a.e. equal to `F²κ - 2t·FGκ + t²·G²κ`), so `0 ≤ ∫_s (F-tG)²κ`, and by
linearity this is `a - 2bt + ct²` with `a = ∫_s F²κ`, `b = ∫_s FGκ`, `c = ∫_s G²κ`.  A
quadratic that is everywhere nonnegative has nonnegative discriminant, i.e. `b² ≤ ac`: if
`c > 0` evaluate at `t = b/c`; if `c = 0` the inequality at `t = (a + |a| + 1)/(2b)` (for
`b ≠ 0`) reads `0 ≤ -|a| - 1`, a contradiction, so `b = 0`. -/
theorem slice_sq_integral_mul_le {s : Set ℝ} {F G κ : ℝ → ℝ} (hκ : ∀ θ ∈ s, 0 ≤ κ θ)
    (hF : MeasureTheory.IntegrableOn (fun θ => F θ * F θ * κ θ) s)
    (hG : MeasureTheory.IntegrableOn (fun θ => G θ * G θ * κ θ) s)
    (hFG : MeasureTheory.IntegrableOn (fun θ => F θ * G θ * κ θ) s) :
    (∫ θ in s, F θ * G θ * κ θ) ^ 2
      ≤ (∫ θ in s, F θ * F θ * κ θ) * (∫ θ in s, G θ * G θ * κ θ) := by
  have hkey : ∀ t : ℝ,
      0 ≤ (∫ θ in s, F θ * F θ * κ θ) - 2 * t * (∫ θ in s, F θ * G θ * κ θ)
        + t ^ 2 * (∫ θ in s, G θ * G θ * κ θ) := by
    intro t
    -- integrability of the three pieces of the quadratic form
    have hA : MeasureTheory.Integrable (fun θ => F θ * F θ * κ θ)
        (MeasureTheory.volume.restrict s) := hF
    have hB : MeasureTheory.Integrable (fun θ => F θ * G θ * κ θ)
        (MeasureTheory.volume.restrict s) := hFG
    have hC : MeasureTheory.Integrable (fun θ => G θ * G θ * κ θ)
        (MeasureTheory.volume.restrict s) := hG
    have hB' : MeasureTheory.Integrable (fun θ => (2 * t) * (F θ * G θ * κ θ))
        (MeasureTheory.volume.restrict s) := hB.const_mul (2 * t)
    have hC' : MeasureTheory.Integrable (fun θ => t ^ 2 * (G θ * G θ * κ θ))
        (MeasureTheory.volume.restrict s) := hC.const_mul (t ^ 2)
    have hAB : MeasureTheory.Integrable
        (fun θ => F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ))
        (MeasureTheory.volume.restrict s) := hA.sub hB'
    -- the pointwise expansion of `(F - t·G)²·κ`
    have hpt : ∀ θ : ℝ, (F θ - t * G θ) * (F θ - t * G θ) * κ θ
        = F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ) + t ^ 2 * (G θ * G θ * κ θ) := by
      intro θ; ring
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (F θ - t * G θ) * (F θ - t * G θ) * κ θ) s := by
      rw [show (fun θ => (F θ - t * G θ) * (F θ - t * G θ) * κ θ)
          = fun θ => F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)
            + t ^ 2 * (G θ * G θ * κ θ) from funext fun θ => hpt θ]
      exact hAB.add hC'
    -- nonnegativity of the integral
    have hnn : 0 ≤ ∫ θ in s, (F θ - t * G θ) * (F θ - t * G θ) * κ θ :=
      setIntegral_nonneg_of_forall_mem hint.aemeasurable
        (fun θ hθ => mul_nonneg (mul_self_nonneg (F θ - t * G θ)) (hκ θ hθ))
    -- linearity of the integral
    have e0 : ∫ θ in s, (F θ - t * G θ) * (F θ - t * G θ) * κ θ
        = ∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)
            + t ^ 2 * (G θ * G θ * κ θ)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    have e1 : ∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)
            + t ^ 2 * (G θ * G θ * κ θ))
        = (∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)))
          + ∫ θ in s, t ^ 2 * (G θ * G θ * κ θ) :=
      MeasureTheory.integral_add hAB hC'
    have e2 : ∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ))
        = (∫ θ in s, F θ * F θ * κ θ) - (2 * t) * (∫ θ in s, F θ * G θ * κ θ) := by
      rw [MeasureTheory.integral_sub hA hB', MeasureTheory.integral_const_mul]
    have e3 : ∫ θ in s, t ^ 2 * (G θ * G θ * κ θ)
        = t ^ 2 * (∫ θ in s, G θ * G θ * κ θ) :=
      MeasureTheory.integral_const_mul (t ^ 2) (fun θ => G θ * G θ * κ θ)
    have hlin : ∫ θ in s, (F θ - t * G θ) * (F θ - t * G θ) * κ θ
        = (∫ θ in s, F θ * F θ * κ θ) - 2 * t * (∫ θ in s, F θ * G θ * κ θ)
          + t ^ 2 * (∫ θ in s, G θ * G θ * κ θ) := by
      rw [e0, e1, e2, e3]
    rwa [hlin] at hnn
  exact quad_nonneg_discr hkey

end Work.FTS.EllipticEst.AngSecond
