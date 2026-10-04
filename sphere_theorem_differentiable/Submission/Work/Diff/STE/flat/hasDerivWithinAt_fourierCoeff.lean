import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiating a Fourier coefficient in time (the flat STE development)

The Fourier coefficient `Work.Diff.STE.fourierCoeff (G s) k` of a family `s ↦ G s` of functions on
the unit cube is an integral over the cube.  This file proves that it can be differentiated under
the integral sign **at a point `t` of the half-open interval `Ico 0 τ`**, i.e. one-sidedly at
`t = 0`.

The hypotheses are exactly the ones available in the Arzelà–Ascoli/compactness step of the flat
short-time-existence argument (`Work.Diff.STE.flat.limit_solves`): a pointwise *one-sided*
difference bound `‖G s x - G t x‖ ≤ |s - t| g x` with `g` integrable on the cube, a.e. strong
measurability of the `G s`, and pointwise one-sided differentiability of `s ↦ G s x` on
`Ico 0 τ` at `t`.

The proof is a direct application of the dominated convergence theorem, carried out on the
punctured interval `Ico 0 τ \ {t}` so that the dominating function `g` is available everywhere:
`((fourierCoeff (G s) k - fourierCoeff (G t) k) / (s - t)) = ∫_cube exp(-2πi k·x) ·
((G s x - G t x)/(s - t))`, and the integrand is bounded by `g` uniformly in `s`, while converging
pointwise to `exp(-2πi k·x) · G' x` by hypothesis.

## Main results

* `Work.Diff.STE.flat.hasDerivWithinAt_integral_Ico` : the general differentiation-under-the-
  integral lemma on `Ico 0 τ` for a family of integrable complex functions (no Fourier theory);
* `Work.Diff.STE.flat.hasDerivWithinAt_fourierCoeff` : the requested statement.
-/

namespace Work.Diff.STE.flat

open MeasureTheory Filter Topology
open scoped Topology

noncomputable section

/-! ## Differentiation under the integral sign on a half-open interval

This is the general (Fourier-free) form of the argument: the derivative of `s ↦ ∫ G s ∂μ` at a
point `t` of `Ico 0 τ` is `∫ G' ∂μ`, from an *a.e. one-sided* difference bound against an
integrable `g` and pointwise one-sided differentiability a.e. -/
theorem hasDerivWithinAt_integral_Ico {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {G : ℝ → X → ℂ} {G' : X → ℂ} {g : X → ℝ} {τ t : ℝ}
    (hg : Integrable g μ) (hGint : Integrable (G t) μ)
    (hmeas : ∀ s ∈ Set.Ico (0 : ℝ) τ, AEStronglyMeasurable (G s) μ)
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ᵐ x ∂μ, ‖G s x - G t x‖ ≤ |s - t| * g x)
    (hder : ∀ᵐ x ∂μ, HasDerivWithinAt (fun s : ℝ => G s x) (G' x) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => ∫ x, G s x ∂μ) (∫ x, G' x ∂μ) (Set.Ico (0 : ℝ) τ) t := by
  have hmem : (Set.Ico (0 : ℝ) τ \ {t}) ∈ 𝓝[Set.Ico (0 : ℝ) τ \ {t}] t := self_mem_nhdsWithin
  -- `G s` is integrable for every `s ∈ Ico 0 τ`, being `G t` plus a difference dominated by `g`.
  have hGs : ∀ s ∈ Set.Ico (0 : ℝ) τ, Integrable (G s) μ := by
    intro s hs
    have h1 : Integrable (fun x => G s x - G t x) μ :=
      Integrable.mono' (hg.const_mul |s - t|) ((hmeas s hs).sub hGint.aestronglyMeasurable)
        (hdiff s hs)
    have h2 : Integrable (fun x => G t x + (G s x - G t x)) μ := hGint.add h1
    simpa using h2
  -- Dominated convergence for the difference quotients on the punctured interval.
  have hDCT : Tendsto (fun s : ℝ => ∫ x, (s - t)⁻¹ • (G s x - G t x) ∂μ)
      (𝓝[(Set.Ico (0 : ℝ) τ) \ {t}] t) (𝓝 (∫ x, G' x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := g)
      (F := fun s x => (s - t)⁻¹ • (G s x - G t x)) (f := fun x => G' x) ?_ ?_ hg ?_
    · refine Filter.eventually_of_mem hmem fun s hs => ?_
      exact ((hmeas s hs.1).sub hGint.aestronglyMeasurable).const_smul (𝕜 := ℝ) ((s - t)⁻¹)
    · refine Filter.eventually_of_mem hmem fun s hs =>
        (hdiff s hs.1).mono fun x hx => ?_
      have hst : |s - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hs.2)
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      calc |s - t|⁻¹ * ‖G s x - G t x‖ ≤ |s - t|⁻¹ * (|s - t| * g x) :=
            mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (abs_nonneg _))
        _ = g x := by rw [← mul_assoc, inv_mul_cancel₀ hst, one_mul]
    · filter_upwards [hder] with x hx
      exact hasDerivWithinAt_iff_tendsto_slope.mp hx
  -- On the punctured interval the difference quotient of the integral is the integral of the
  -- difference quotient.
  have hEq : (fun s : ℝ => ∫ x, (s - t)⁻¹ • (G s x - G t x) ∂μ)
      =ᶠ[𝓝[(Set.Ico (0 : ℝ) τ) \ {t}] t] slope (fun s : ℝ => ∫ x, G s x ∂μ) t := by
    refine Filter.eventually_of_mem hmem fun s hs => ?_
    simp only [slope, vsub_eq_sub]
    rw [← integral_sub (hGs s hs.1) hGint,
      ← integral_smul (μ := μ) (c := (s - t)⁻¹) (f := fun x => G s x - G t x)]
  have hTendsto := hDCT.congr' hEq
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact hTendsto

/-- The character `x ↦ exp (-2πi k·x)` has norm `1`. -/
private lemma norm_fourierExp_neg_eq_one {n : ℕ} (k : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖Work.Diff.STE.fourierExp (-k) x‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (((-k) i : ℤ) : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, (((-k) i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Work.Diff.STE.fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

/-- Continuity (hence a.e. strong measurability) of the character `x ↦ exp (-2πi k·x)`. -/
private lemma continuous_fourierExp_neg {n : ℕ} (k : Fin n → ℤ) :
    Continuous (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-k) x) := by
  simp only [Work.Diff.STE.fourierExp]
  refine Complex.continuous_exp.comp ?_
  refine continuous_const.mul ?_
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i))

theorem hasDerivWithinAt_fourierCoeff {n : ℕ} {τ t : ℝ} (hτ : 0 < τ) (ht : t ∈ Set.Ico (0 : ℝ) τ)
    (k : Fin n → ℤ) (G : ℝ → (Fin n → ℝ) → ℂ) (G' : (Fin n → ℝ) → ℂ)
    (g : (Fin n → ℝ) → ℝ)
    (hg : MeasureTheory.IntegrableOn g (Work.Diff.STE.unitCube (ι := Fin n)) MeasureTheory.volume)
    (hGint : MeasureTheory.IntegrableOn (G t) (Work.Diff.STE.unitCube (ι := Fin n))
      MeasureTheory.volume)
    (hmeas : ∀ s ∈ Set.Ico (0 : ℝ) τ, MeasureTheory.AEStronglyMeasurable (G s)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))))
    (hmeas' : MeasureTheory.AEStronglyMeasurable G'
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))))
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
      ‖G s x - G t x‖ ≤ |s - t| * g x)
    (hder : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
      HasDerivWithinAt (fun s : ℝ => G s x) (G' x) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.fourierCoeff (G s) k)
      (Work.Diff.STE.fourierCoeff G' k) (Set.Ico (0 : ℝ) τ) t := by
  have hcube : MeasurableSet (Work.Diff.STE.unitCube (ι := Fin n)) := by
    rw [Work.Diff.STE.unitCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)
  have hφcont : Continuous (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-k) x) :=
    continuous_fourierExp_neg k
  have hφmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-k) x)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    hφcont.aestronglyMeasurable
  have hnorm : ∀ x : Fin n → ℝ, ‖Work.Diff.STE.fourierExp (-k) x‖ = 1 :=
    norm_fourierExp_neg_eq_one k
  -- the constant family `x ↦ exp (-2πi k·x) · G t` is integrable on the cube
  have hGint' : Integrable
      (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-k) x * G t x)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    Integrable.bdd_mul (c := 1) hGint hφmeas
      (Filter.Eventually.of_forall fun x => by simp [hnorm x])
  -- a.e. strong measurability of the products
  have hmeas_mul : ∀ s ∈ Set.Ico (0 : ℝ) τ, MeasureTheory.AEStronglyMeasurable
      (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-k) x * G s x)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    fun s hs => hφmeas.mul (hmeas s hs)
  -- the difference bound for the products (a.e. in `x`)
  have hdiff_mul : ∀ s ∈ Set.Ico (0 : ℝ) τ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))),
      ‖Work.Diff.STE.fourierExp (-k) x * G s x - Work.Diff.STE.fourierExp (-k) x * G t x‖
        ≤ |s - t| * g x := by
    intro s hs
    rw [MeasureTheory.ae_restrict_iff' hcube]
    exact Filter.Eventually.of_forall fun x hx => by
      rw [← mul_sub, norm_mul, hnorm x, one_mul]
      exact hdiff s hs x hx
  -- pointwise one-sided differentiability of the products, a.e. in `x`
  have hder' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.fourierExp (-k) x * G s x)
        (Work.Diff.STE.fourierExp (-k) x * G' x) (Set.Ico (0 : ℝ) τ) t := by
    rw [MeasureTheory.ae_restrict_iff' hcube]
    exact Filter.Eventually.of_forall fun x hx => (hder x hx).const_mul _
  have hmain := hasDerivWithinAt_integral_Ico
    (X := Fin n → ℝ)
    (μ := MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n)))
    (G := fun s x => Work.Diff.STE.fourierExp (-k) x * G s x)
    (G' := fun x => Work.Diff.STE.fourierExp (-k) x * G' x) (g := g) (τ := τ) (t := t)
    hg hGint' hmeas_mul hdiff_mul hder'
  simpa only [Work.Diff.STE.fourierCoeff] using hmain

end

end Work.Diff.STE.flat
