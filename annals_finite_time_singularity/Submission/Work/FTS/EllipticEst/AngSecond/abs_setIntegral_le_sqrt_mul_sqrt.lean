import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open MeasureTheory

/-- Helper: if `f` is integrable on `s` and nonnegative on `s`, then `f ≥ 0` almost everywhere for
`volume.restrict s`.

Note that `s` is *not* assumed measurable, so `∀ᵐ z ∂(volume.restrict s), z ∈ s` is in general
false and one has to argue through `Measure.restrict_apply₀`, which evaluates
`(volume.restrict s) t` for null-measurable `t`. -/
private lemma ae_nonneg_of_on {s : Set ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f s)
    (hn : ∀ z ∈ s, 0 ≤ f z) : ∀ᵐ z ∂(volume.restrict s), 0 ≤ f z := by
  rw [ae_iff]
  have hset : {a : ℝ | ¬ 0 ≤ f a} = {z : ℝ | f z < 0} := by ext z; exact not_le
  rw [hset]
  rw [Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const)]
  have hempty : {z : ℝ | f z < 0} ∩ s = ∅ := by
    ext z; constructor
    · intro hz; exact absurd (hn z hz.2) (not_le.mpr hz.1)
    · intro hz; exact absurd hz (Set.notMem_empty z)
  rw [hempty, measure_empty]

/-- Helper: a pointwise inequality on `s` between two a.e. strongly measurable functions is an
a.e. inequality for `volume.restrict s` (again for arbitrary `s`: only the null-measurable set
`{z | g z < f z}` is measured, via `Measure.restrict_apply₀`). -/
private lemma ae_le_of_on {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (h : ∀ z ∈ s, f z ≤ g z) : f ≤ᵐ[volume.restrict s] g := by
  show ∀ᵐ z ∂(volume.restrict s), f z ≤ g z
  rw [ae_iff]
  have hset : {a : ℝ | ¬ f a ≤ g a} = {z : ℝ | g z < f z} := by ext z; exact not_le
  rw [hset]
  rw [Measure.restrict_apply₀ (hg.nullMeasurableSet_lt hf)]
  have hempty : {z : ℝ | g z < f z} ∩ s = ∅ := by
    ext z; constructor
    · intro hz; exact absurd (h z hz.2) (not_le.mpr hz.1)
    · intro hz; exact absurd hz (Set.notMem_empty z)
  rw [hempty, measure_empty]

/-- Helper: for `f ≥ 0` on `s`, `z ↦ √(f z)²` agrees with `f` a.e. for `volume.restrict s`. -/
private lemma sqrt_sq_ae_eq {s : Set ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f s)
    (hn : ∀ z ∈ s, 0 ≤ f z) : (fun z => Real.sqrt (f z) ^ 2) =ᵐ[volume.restrict s] f := by
  filter_upwards [ae_nonneg_of_on hf hn] with z hz
  exact Real.sq_sqrt hz

/-- **The radial ("in `z`") Cauchy–Schwarz step.**

If `C` is pointwise dominated by `√A · √B` on `s`, where `A` and `B` are integrable and
nonnegative on `s`, then `|∫_s C| ≤ √(∫_s A) · √(∫_s B)`.

Route: `|∫_s C| ≤ ∫_s |C| ≤ ∫_s √A·√B` (the last integrand is integrable by
`Work.Coercivity.integrable_sqrt_mul_sqrt`, dominated by `(A+B)/2`), then Cauchy–Schwarz
(`Work.Coercivity.holder_two_mul`) with `u = √∘A`, `v = √∘B` — whose a.e. strong measurability
comes from the integrability of `A`, `B` — gives `(∫_s √A·√B)² ≤ (∫_s A)(∫_s B)`, and taking
square roots (both sides are nonnegative) yields `∫_s √A·√B ≤ √(∫_s A)·√(∫_s B)`. -/
theorem abs_setIntegral_le_sqrt_mul_sqrt {s : Set ℝ} {A B C : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hC : MeasureTheory.IntegrableOn C s)
    (hAn : ∀ z ∈ s, 0 ≤ A z) (hBn : ∀ z ∈ s, 0 ≤ B z)
    (h : ∀ z ∈ s, |C z| ≤ Real.sqrt (A z) * Real.sqrt (B z)) :
    |∫ z in s, C z| ≤ Real.sqrt (∫ z in s, A z) * Real.sqrt (∫ z in s, B z) := by
  set ν : Measure ℝ := volume.restrict s with hν
  -- `√∘A` and `√∘B` are a.e. strongly measurable, and their squares are integrable
  have aA : AEStronglyMeasurable (fun z => Real.sqrt (A z)) ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have aB : AEStronglyMeasurable (fun z => Real.sqrt (B z)) ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hsqA : Integrable (fun z => Real.sqrt (A z) ^ 2) ν :=
    hA.congr (sqrt_sq_ae_eq hA hAn).symm
  have hsqB : Integrable (fun z => Real.sqrt (B z) ^ 2) ν :=
    hB.congr (sqrt_sq_ae_eq hB hBn).symm
  -- Cauchy–Schwarz for `L²` (also gives integrability of the product)
  obtain ⟨hABint, hABcs⟩ :=
    Work.Coercivity.holder_two_mul ν (fun z => Real.sqrt (A z)) (fun z => Real.sqrt (B z))
      aA aB hsqA hsqB
  have hABcs' : |∫ z, Real.sqrt (A z) * Real.sqrt (B z) ∂ν| ≤
      Real.sqrt (∫ z, A z ∂ν) * Real.sqrt (∫ z, B z ∂ν) := by
    have hh := hABcs
    rwa [integral_congr_ae (sqrt_sq_ae_eq hA hAn),
      integral_congr_ae (sqrt_sq_ae_eq hB hBn)] at hh
  -- the pointwise domination on `s`, upgraded to an a.e. domination
  have hle : (fun z => |C z|) ≤ᵐ[ν] (fun z => Real.sqrt (A z) * Real.sqrt (B z)) :=
    ae_le_of_on (continuous_abs.comp_aestronglyMeasurable hC.aestronglyMeasurable)
      (aA.mul aB) h
  have h1 : |∫ z, C z ∂ν| ≤ ∫ z, |C z| ∂ν := abs_integral_le_integral_abs
  calc |∫ z, C z ∂ν| ≤ ∫ z, |C z| ∂ν := h1
    _ ≤ ∫ z, Real.sqrt (A z) * Real.sqrt (B z) ∂ν := integral_mono_ae hC.abs hABint hle
    _ ≤ |∫ z, Real.sqrt (A z) * Real.sqrt (B z) ∂ν| := le_abs_self _
    _ ≤ Real.sqrt (∫ z, A z ∂ν) * Real.sqrt (∫ z, B z ∂ν) := hABcs'

end Work.FTS.EllipticEst.AngSecond
