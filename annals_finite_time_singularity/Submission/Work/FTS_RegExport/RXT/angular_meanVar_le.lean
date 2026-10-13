/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular mean-value / Agmon inequality

The pointwise bound

`g θ² ≤ (4/π) ∫_{[0,π/2]} g² + 2 (∫_{[0,π/2]} sin(2·)^{γ-2}) (∫_{[0,π/2]} g'² sin(2·)^{2-γ})`

for `θ ∈ (0,π/2)`, `γ > 1`, valid for any `g` differentiable on `(0,π/2)` with derivative `g'`
and the stated weighted `L²` bounds.

## Mathematics

Let `Iθ = [0,π/2]` (length `π/2`), `A = ∫_{Iθ} g²`, `M = ∫_{Iθ} sin(2·)^{γ-2}` and
`W = ∫_{Iθ} g'² sin(2·)^{2-γ}`.

1. *Mean value.* Some interior point `t ∈ (0,π/2)` has `2 g t² ≤ (4/π) A` — the average of `g²`
   over `Iθ` is `(2/π) A`, and the two endpoints are a null set, so the point can be taken
   interior (`Angular.meanValue`).
2. *FTC.* For `0 < a ≤ b < π/2` the segment `[a,b]` stays strictly inside `(0,π/2)`, so `g` is
   continuous there and `∫_a^b g' = g b - g a`; the weighted `L²` hypothesis `hint2` (with
   `sin(2·)^{2-γ}` bounded below on `[a,b]`) supplies the interval-integrability of `g'`
   (`Angular.integral_deriv_eq_sub`).
3. *Weighted Cauchy–Schwarz.* On `[a,b]`, `|g'| = (|g'| sin^{(2-γ)/2}) · sin^{(γ-2)/2}`, so
   `(∫_a^b |g'|)² ≤ (∫_a^b g'² sin^{2-γ})(∫_a^b sin^{γ-2})`, and both factors increase when the
   interval is enlarged to `Iθ` (`Angular.cs_weighted`, where `∫_{Iθ} sin^{γ-2} < ∞` is exactly
   `γ > 1`).
4. *Assembly* (`angular_meanVar_le_aux`): `|g θ - g t| ≤ ∫ |g'|` between two interior points,
   hence `(g θ - g t)² ≤ W M`, and `(x+y)² ≤ 2x² + 2y²` gives the claim.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.Flat.integrableOnSinTwoRpow
import Submission.Work.FTS_RegExport.RXT.Angular.meanValue
import Submission.Work.FTS_RegExport.RXT.Angular.integral_deriv_eq_sub
import Submission.Work.FTS_RegExport.RXT.Angular.cs_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- The derivative datum `g'` of a function differentiable on the open angular interval is
a.e. strongly measurable for the Lebesgue measure restricted to `Iθ`. -/
lemma aeStronglyMeasurable_deriv_of_hasDerivAt {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ) :
    AEStronglyMeasurable g' (volume.restrict Work.Spaces.Iθ) := by
  have hset : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hm : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ := Measure.restrict_congr_set hset
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      deriv g x = g' x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun x hx => (hg x hx).deriv)
  have hae' : ∀ᵐ x ∂(volume.restrict Work.Spaces.Iθ), deriv g x = g' x := hm.symm ▸ hae
  exact ((measurable_deriv g).aemeasurable.congr hae').aestronglyMeasurable

/-- `sin(2θ)^{γ-2}` is interval integrable on `[0,π/2]` for `γ > 1`. -/
lemma intervalIntegrable_sin_rpow {γ : ℝ} (hγ : 1 < γ) :
    IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) volume 0 (Real.pi / 2) := by
  have hc : (-1 : ℝ) < γ - 2 := by linarith
  have hInt : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (γ - 2))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllSol.Flat.integrableOn_sin_two_rpow_Icc hc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)).2 hInt

/-- Assembly step: from the mean-value point, the FTC on interior subintervals and the weighted
Cauchy–Schwarz bound, the pointwise angular inequality follows. -/
theorem angular_meanVar_le_aux {γ : ℝ} {g g' : ℝ → ℝ}
    (hA : ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      2 * g t ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2))
    (hB : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      ∫ x in a..b, g' x = g b - g a)
    (hC : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      (∫ x in a..b, |g' x|) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  intro θ hθ
  obtain ⟨t, ht, htle⟩ := hA
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2) with hM
  set W : ℝ := ∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) with hW
  have step : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      (∫ x in a..b, g' x) ^ 2 ≤ W * M := by
    intro a b ha hab hb
    have h2 := hC a b ha hab hb
    rw [hM, hW] at h2
    refine le_trans ?_ h2
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := g') hab
    calc (∫ x in a..b, g' x) ^ 2 = |∫ x in a..b, g' x| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ x in a..b, |g' x|) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg _) habs
  have key : (g θ - g t) ^ 2 ≤ W * M := by
    rcases le_total t θ with h | h
    · have h1 : g θ - g t = ∫ x in t..θ, g' x := (hB t θ ht.1 h hθ.2).symm
      rw [h1]; exact step t θ ht.1 h hθ.2
    · have h1 : g θ - g t = -(∫ x in θ..t, g' x) := by
        rw [hB θ t hθ.1 h ht.2]; ring
      rw [h1, neg_sq]; exact step θ t hθ.1 h ht.2
  have hfin : g θ ^ 2 ≤ 2 * (g θ - g t) ^ 2 + 2 * g t ^ 2 := by
    nlinarith [sq_nonneg ((g θ - g t) - g t)]
  linarith [hfin, key, htle]

theorem angular_meanVar_le {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint1 : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  refine angular_meanVar_le_aux (γ := γ) ?_ ?_ ?_
  · exact Work.FTS_RegExport.RXT.Angular.meanValue hint1
  · intro a b ha hab hb
    exact Work.FTS_RegExport.RXT.Angular.integral_deriv_eq_sub hγ hg hint2 ha hab hb
  · intro a b ha hab hb
    exact Work.FTS_RegExport.RXT.Angular.cs_weighted hγ
      (aeStronglyMeasurable_deriv_of_hasDerivAt hg) hint2 (intervalIntegrable_sin_rpow hγ)
      ha hab hb

end Work.FTS_RegExport.RXT
