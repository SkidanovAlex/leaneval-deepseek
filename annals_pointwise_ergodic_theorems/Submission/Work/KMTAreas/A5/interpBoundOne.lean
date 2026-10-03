import Mathlib
import Submission.Work.KMTAreas.A5.eLpNorm_one_le_of_pairing_le
import Submission.Work.KMTAreas.A5.pairIntegral_le
import Submission.Work.KMTAreas.A5.memLp_pairing_indicator
import Submission.Work.KMTAreas.A5.pairIntegral_expansion

/-!
# Interpolation of two `ℓ¹`-valued endpoint estimates

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), §5 uses Stein's multilinear interpolation to pass from two endpoint
estimates of a bilinear operator `T` to the full range of exponents.  This file treats the case in
which **both** endpoint estimates take values in `ℓ¹`:

`‖T u v‖_{ℓ¹} ≤ M₀ ‖u‖_{ℓ^{p₀}} ‖v‖_{ℓ^{q₀}}`, `‖T u v‖_{ℓ¹} ≤ M₁ ‖u‖_{ℓ^{p₁}} ‖v‖_{ℓ^{q₁}}`

imply, at the reciprocally interpolated exponents `1/p = (1-θ)/p₀ + θ/p₁`,
`1/q = (1-θ)/q₀ + θ/q₁`,

`‖T f g‖_{ℓ¹} ≤ M₀^{1-θ} M₁^θ ‖f‖_{ℓ^p} ‖g‖_{ℓ^q}`

for finitely supported `f`, `g`.

The interpolation is the classical bilinear one.  Note that the *trilinear* formulation
(`Work.KMTAreas.A5.stein_trilinear_top`, `Work.KMTAreas.A5.interpBound`) cannot express this case
directly: pairing the output against a third test function `φ` puts `φ` in `ℓ^∞` at *both*
endpoints, and the analytic family of a variable third argument would have to take the exponents
`r/r₀ = r/r₁ = 0` on the two edges while taking the exponent `1` at `z = θ`, which is impossible.
The correct (and classical) reduction is therefore to *fix* the test function `φ` and to interpolate
the bilinear form `(u,v) ↦ ∫ x, T u v x * φ x` with Stein's bilinear three-lines theorem
(`Work.Analysis.Interpolation.stein_bilinear_of_decomposition`), the three lines argument being run
on the analytic families of the two *arguments* only.

The two analytic inputs of that theorem (the level-set decomposition of the form and its
boundedness on the strip) are supplied by

* `Work.KMTAreas.A5.pairIntegral_expansion` — the expansion of `∫ x, T u v x * φ x` on the
  analytic families of two simple functions as a finite double sum over level sets;
* `Work.Analysis.Interpolation.bddAbove_bilinear_family` — boundedness of a finite sum of
  exponentials of affine functions on the closed strip.

The two endpoint estimates of the fixed-`φ` form are `Work.KMTAreas.A5.pairIntegral_le`
(Hölder in the limit form `ℓ¹`–`ℓ^∞`), and the level-set pairings are in `ℓ¹` by
`Work.KMTAreas.A5.memLp_pairing_indicator`.  Finally, the duality `(ℓ¹)' = ℓ^∞`
(`Work.KMTAreas.A5.eLpNorm_one_le_of_pairing_le`, realised through the phase of the function)
removes the fixed test function `φ`.

Since the operator `T` is only linear on *bounded* functions (as in the whole §5 interpolation of
this project), the fixed-`φ` form is guarded by boundedness of its two arguments (`pairPhi`); the
guard is invisible on the analytic families and on the level-set indicators, which are all bounded.
-/

namespace Work.KMTAreas.A5

open MeasureTheory Classical
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary facts about finitely supported functions -/

/-- **Finitely supported functions are bounded.** -/
theorem boundedZ_of_finite_support (f : ℤ → ℂ) (hf : (Function.support f).Finite) : BoundedZ f := by
  obtain ⟨C, hC⟩ := (hf.image (fun x => ‖f x‖)).bddAbove
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Function.support f
  · exact le_trans (hC ⟨x, hx, rfl⟩) (le_max_left _ _)
  · rw [Function.notMem_support] at hx
    rw [hx, norm_zero]
    exact le_max_right _ _

/-- The non-zero level sets of a finitely supported function have finite counting measure. -/
theorem count_fiber_lt_top_of_finite_support {f : ℤ → ℂ} (hf : (Function.support f).Finite)
    {c : ℂ} (hc : c ≠ 0) : Measure.count (f ⁻¹' {c}) < ⊤ := by
  refine Measure.count_apply_lt_top.mpr ?_
  refine hf.subset fun x hx => ?_
  have hxc : f x = c := by simpa using hx
  rw [Function.mem_support, hxc]
  exact hc

/-- A finitely supported function, regarded as a simple function. -/
noncomputable def simpleOfFiniteSupport (f : ℤ → ℂ) (hf : (Function.support f).Finite) :
    MeasureTheory.SimpleFunc ℤ ℂ :=
  SimpleFunc.mk f (fun c => (measurable_of_countable f) (measurableSet_singleton c)) (by
    refine ((hf.image f).union (Set.finite_singleton 0)).subset ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Or.inr (by simp [hx])
    · exact Or.inl ⟨x, by simpa [Function.mem_support] using hx, rfl⟩)

@[simp] theorem coe_simpleOfFiniteSupport (f : ℤ → ℂ) (hf : (Function.support f).Finite) :
    (simpleOfFiniteSupport f hf : ℤ → ℂ) = f := rfl

/-! ## The fixed-`φ` pairing, guarded by boundedness -/

/-- The pairing `∫ x, T u v x * φ x` of `T u v` against a fixed test function `φ`, guarded by
boundedness of `u` and `v`: `T` is only linear on bounded functions, so only those inputs are
used in the interpolation.  On *unbounded* inputs the form is defined to be zero, which makes the
endpoint estimates hold for all inputs (see the proof of `interpBoundOne`). -/
noncomputable def pairPhi (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)) (φ u v : ℤ → ℂ) : ℂ :=
  if BoundedZ u ∧ BoundedZ v then ∫ x, T u v x * φ x ∂Measure.count else 0

theorem pairPhi_of_bounded {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)} {φ u v : ℤ → ℂ}
    (hu : BoundedZ u) (hv : BoundedZ v) :
    pairPhi T φ u v = ∫ x, T u v x * φ x ∂Measure.count := if_pos ⟨hu, hv⟩

theorem pairPhi_of_not_bounded {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)} {φ u v : ℤ → ℂ}
    (h : ¬ (BoundedZ u ∧ BoundedZ v)) : pairPhi T φ u v = 0 := if_neg h

/-! ## The interpolation -/

theorem interpBoundOne (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), Work.KMTAreas.A5.BoundedZ u → Work.KMTAreas.A5.BoundedZ u' → Work.KMTAreas.A5.BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), Work.KMTAreas.A5.BoundedZ u → Work.KMTAreas.A5.BoundedZ v → Work.KMTAreas.A5.BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    {p₀ p₁ q₀ q₁ p q θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hp : 0 < p) (hq : 0 < q) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁)
    {M₀ M₁ : NNReal}
    (h₀ : ∀ u v : ℤ → ℂ, MeasureTheory.eLpNorm (T u v) 1 MeasureTheory.Measure.count
      ≤ (M₀ : ENNReal) * MeasureTheory.eLpNorm u (ENNReal.ofReal p₀) MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm v (ENNReal.ofReal q₀) MeasureTheory.Measure.count)
    (h₁ : ∀ u v : ℤ → ℂ, MeasureTheory.eLpNorm (T u v) 1 MeasureTheory.Measure.count
      ≤ (M₁ : ENNReal) * MeasureTheory.eLpNorm u (ENNReal.ofReal p₁) MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm v (ENNReal.ofReal q₁) MeasureTheory.Measure.count) :
    ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
      MeasureTheory.eLpNorm (T f g) 1 MeasureTheory.Measure.count
        ≤ (M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  intro f g hf hg
  -- the two inputs are simple functions
  obtain ⟨F, hFc⟩ : ∃ F : MeasureTheory.SimpleFunc ℤ ℂ, (F : ℤ → ℂ) = f :=
    ⟨simpleOfFiniteSupport f hf, rfl⟩
  obtain ⟨G, hGc⟩ : ∃ G : MeasureTheory.SimpleFunc ℤ ℂ, (G : ℤ → ℂ) = g :=
    ⟨simpleOfFiniteSupport g hg, rfl⟩
  have hFb : BoundedZ (F : ℤ → ℂ) := by rw [hFc]; exact boundedZ_of_finite_support f hf
  have hGb : BoundedZ (G : ℤ → ℂ) := by rw [hGc]; exact boundedZ_of_finite_support g hg
  -- finiteness of the non-zero level sets
  have hFfib : ∀ c ∈ F.range, c ≠ 0 → Measure.count (F ⁻¹' {c}) < ⊤ := by
    intro c _ hc
    rw [hFc]
    exact count_fiber_lt_top_of_finite_support hf hc
  have hGfib : ∀ d ∈ G.range, d ≠ 0 → Measure.count (G ⁻¹' {d}) < ⊤ := by
    intro d _ hd
    rw [hGc]
    exact count_fiber_lt_top_of_finite_support hg hd
  -- the level-set pairings are in `ℓ¹`
  have hMem : ∀ c ∈ F.range, c ≠ 0 → ∀ d ∈ G.range, d ≠ 0 →
      MemLp (T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
        (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) 1 Measure.count :=
    fun c hc hc0 d hd hd0 =>
      memLp_pairing_indicator T hp₀ hq₀ h₀ hFfib hGfib hc hd hc0 hd0
  -- the two endpoint estimates of the fixed-`φ` form
  have hEnd0 : ∀ (φ : ℤ → ℂ), (∀ x, ‖φ x‖ ≤ 1) → ∀ u v : ℤ → ℂ,
      ‖pairPhi T φ u v‖ₑ ≤ (M₀ : ENNReal) * eLpNorm u (ENNReal.ofReal p₀) Measure.count
        * eLpNorm v (ENNReal.ofReal q₀) Measure.count := by
    intro φ hφ u v
    by_cases hb : BoundedZ u ∧ BoundedZ v
    · rw [pairPhi_of_bounded hb.1 hb.2]
      exact pairIntegral_le T h₀ hφ hb.1 hb.2
    · rw [pairPhi_of_not_bounded hb]
      simp
  have hEnd1 : ∀ (φ : ℤ → ℂ), (∀ x, ‖φ x‖ ≤ 1) → ∀ u v : ℤ → ℂ,
      ‖pairPhi T φ u v‖ₑ ≤ (M₁ : ENNReal) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
        * eLpNorm v (ENNReal.ofReal q₁) Measure.count := by
    intro φ hφ u v
    by_cases hb : BoundedZ u ∧ BoundedZ v
    · rw [pairPhi_of_bounded hb.1 hb.2]
      exact pairIntegral_le T h₁ hφ hb.1 hb.2
    · rw [pairPhi_of_not_bounded hb]
      simp
  -- the level-set decomposition of the pairing along the analytic families
  have hExp : ∀ (φ : ℤ → ℂ), (∀ x, ‖φ x‖ ≤ 1) → ∀ z : ℂ,
      pairPhi T φ
        (Work.Analysis.Interpolation.analyticFamily (F : ℤ → ℂ) ((p / p₀ : ℝ) : ℂ)
          ((p / p₁ : ℝ) : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily (G : ℤ → ℂ) ((q / q₀ : ℝ) : ℂ)
          ((q / q₁ : ℝ) : ℂ) z)
      = ∑ c ∈ F.range, ∑ d ∈ G.range,
          (Work.Analysis.Interpolation.phasePow c
              (Work.Analysis.Interpolation.expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            * Work.Analysis.Interpolation.phasePow d
              (Work.Analysis.Interpolation.expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z))
          * pairPhi T φ (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
              (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ))) := by
    intro φ hφ z
    rw [pairPhi_of_bounded (boundedZ_analyticFamily F _ _ z) (boundedZ_analyticFamily G _ _ z),
      pairIntegral_expansion T hlin₁ hlin₂ F G φ hφ hMem ((p / p₀ : ℝ) : ℂ)
        ((p / p₁ : ℝ) : ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    rw [pairPhi_of_bounded (boundedZ_indicator _) (boundedZ_indicator _)]
  -- the same expansion, in the shape required by Stein's bilinear interpolation
  have hΛstein : ∀ (φ : ℤ → ℂ), (∀ x, ‖φ x‖ ≤ 1) → ∀ z : ℂ,
      Work.Analysis.Interpolation.bilinearFamily (pairPhi T φ) (F : ℤ → ℂ) (G : ℤ → ℂ)
        ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z
      = ∑ c ∈ F.range, ∑ d ∈ G.range,
          (Work.Analysis.Interpolation.phasePow c
              (Work.Analysis.Interpolation.expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            * Work.Analysis.Interpolation.phasePow d
              (Work.Analysis.Interpolation.expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z))
          * pairPhi T φ (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
              (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ))) := by
    intro φ hφ z
    rw [Work.Analysis.Interpolation.bilinearFamily_apply]
    exact hExp φ hφ z
  -- boundedness of the analytic family on the strip
  have hBdd : ∀ (φ : ℤ → ℂ), (∀ x, ‖φ x‖ ≤ 1) → BddAbove ((norm ∘
      Work.Analysis.Interpolation.bilinearFamily (pairPhi T φ) (F : ℤ → ℂ) (G : ℤ → ℂ)
        ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ))
        '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    intro φ hφ
    refine Work.Analysis.Interpolation.bddAbove_bilinear_family (pairPhi T φ) F G
      (p / p₀) (p / p₁) (q / q₀) (q / q₁) ?_
    intro z
    exact hExp φ hφ z
  -- duality: the estimate for every pairing against a `ℓ^∞` test function of norm `≤ 1`
  refine eLpNorm_one_le_of_pairing_le (T f g)
    ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ
      * eLpNorm f (ENNReal.ofReal p) Measure.count
      * eLpNorm g (ENNReal.ofReal q) Measure.count) ?_
  intro φ hφ
  have hstein := Work.Analysis.Interpolation.stein_bilinear_of_decomposition (pairPhi T φ) F G
    hp₀ hp₁ hq₀ hq₁ hp hq hθ₀ hθ₁ hpθ hqθ (hEnd0 φ hφ) (hEnd1 φ hφ) (hΛstein φ hφ)
    (hBdd φ hφ)
  rw [pairPhi_of_bounded hFb hGb, hFc, hGc] at hstein
  exact hstein

end

end Work.KMTAreas.A5
