import Mathlib
import Submission.Work.A3.HausdorffYoungDefs
import Submission.Work.A3.parseval_finsupp
import Submission.Port.Aesm

/-!
# The `ℓ²` bound for the truncated Fourier sum (Plancherel, in `eLpNorm` form)

For a coefficient function `u : ℤ → ℂ` supported in a finite set `s`, the truncated Fourier
sum `kmtSum s u θ = ∑_{x ∈ s} u x · e(-xθ)` is a trigonometric polynomial, and the
orthonormality of the characters `e(-x·)` on `[0,1]` (Plancherel/Parseval) gives the exact
identity

`‖kmtSum s u‖_{L²(kmtNu)} = (∑_{x ∈ s} ‖u x‖²)^(1/2) ≤ (∑'_x ‖u x‖²)^(1/2) = ‖u‖_{ℓ²(ℤ)}`,

which is the `ℒ²`-part of the Hausdorff--Young package for area `A3`: it is the endpoint
estimate that the `(ℓ², L²)` bound `kmtPair s u v ≤ ‖u‖_{ℓ²} ‖v‖_{L²}` of
`Work.A3.kmtPair_le_one` is paired with.

The `ℓ²` norm of `u` is `eLpNorm u 2 Measure.count`, the `eLpNorm` with respect to the
counting measure on `ℤ`.  The proof is a direct computation in `ℝ≥0∞`:

* `Work.A3.kmtSum_integral_norm_sq` : `∫₀¹ ‖kmtSum s u θ‖² dθ = ∑_{x ∈ s} ‖u x‖²`
  (the real form of the finite Parseval identity `Work.A3.parseval_integral_star_finsum`);
* `Work.A3.kmtSum_lintegral_enorm_sq` : the same in `ℝ≥0∞` form, for the `eLpNorm`;
* `MeasureTheory.lintegral_count` turns the `eLpNorm` for `Measure.count` into the `tsum`
  `∑'_x ‖u x‖ₑ ^ 2`, and `ENNReal.sum_le_tsum` compares the finite sum over `s` with it.
-/

namespace Work.A3

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- For a complex number `z`, the `ℝ≥0∞`-valued power `‖z‖ₑ ^ 2` is the coercion of the real
number `‖z‖ ^ 2`. -/
lemma enorm_rpow_two_eq_ofReal_norm_sq (z : ℂ) :
    ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) (by norm_num),
    Real.rpow_two]

/-- **Real Parseval identity for the truncated Fourier sum**: the `L²` norm squared of
`kmtSum s u` on `[0,1]` (with Lebesgue measure) is the `ℓ²` norm squared of the coefficients
over the support `s`. -/
lemma kmtSum_integral_norm_sq (s : Finset ℤ) (u : ℤ → ℂ) :
    ∫ θ, ‖kmtSum s u θ‖ ^ 2 ∂kmtNu = ∑ x ∈ s, ‖u x‖ ^ 2 := by
  have hG : ∀ θ : ℝ,
      ((‖kmtSum s u θ‖ ^ 2 : ℝ) : ℂ) = star (kmtSum s u θ) * kmtSum s u θ := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  have h2 : ∫ θ in Set.Icc (0 : ℝ) 1, ((‖kmtSum s u θ‖ ^ 2 : ℝ) : ℂ)
      = ((∑ x ∈ s, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
    calc ∫ θ in Set.Icc (0 : ℝ) 1, ((‖kmtSum s u θ‖ ^ 2 : ℝ) : ℂ)
        = ∫ θ in Set.Icc (0 : ℝ) 1, star (kmtSum s u θ) * kmtSum s u θ :=
          integral_congr_ae (Filter.Eventually.of_forall hG)
      _ = ∫ θ in Set.Icc (0 : ℝ) 1,
            star (∑ x ∈ s, u x * parsevalE x θ) * (∑ y ∈ s, u y * parsevalE y θ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          simp only [kmtSum_apply, kmtChar, parsevalE]
      _ = ∑ x ∈ s, ((‖u x‖ ^ 2 : ℝ) : ℂ) := parseval_integral_star_finsum s u
      _ = ((∑ x ∈ s, ‖u x‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum s (fun x => ‖u x‖ ^ 2)).symm
  have h3 : ((∫ θ in Set.Icc (0 : ℝ) 1, ‖kmtSum s u θ‖ ^ 2 : ℝ) : ℂ)
      = ((∑ x ∈ s, ‖u x‖ ^ 2 : ℝ) : ℂ) :=
    (integral_ofReal (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (𝕜 := ℂ)
      (f := fun θ : ℝ => ‖kmtSum s u θ‖ ^ 2)).symm.trans h2
  have h4 : (∫ θ in Set.Icc (0 : ℝ) 1, ‖kmtSum s u θ‖ ^ 2 : ℝ) = ∑ x ∈ s, ‖u x‖ ^ 2 :=
    Complex.ofReal_injective h3
  simpa [kmtNu] using h4

/-- The `ℝ≥0∞`-valued (Lebesgue) integral of `‖kmtSum s u‖ₑ ^ 2` over `[0,1]`, i.e. the
integrand defining `eLpNorm (kmtSum s u) 2 kmtNu`: by Parseval it is the coercion of
`∑_{x ∈ s} ‖u x‖²`. -/
lemma kmtSum_lintegral_enorm_sq (s : Finset ℤ) (u : ℤ → ℂ) :
    ∫⁻ θ, ‖kmtSum s u θ‖ₑ ^ (2 : ℝ) ∂kmtNu = ENNReal.ofReal (∑ x ∈ s, ‖u x‖ ^ 2) := by
  have hint : Integrable (fun θ : ℝ => ‖kmtSum s u θ‖ ^ 2) kmtNu := by
    have hcont : Continuous fun θ : ℝ => ‖kmtSum s u θ‖ ^ 2 :=
      (continuous_kmtSum s u).norm.pow 2
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  rw [lintegral_congr_ae
        (ae_of_all _ fun θ => enorm_rpow_two_eq_ofReal_norm_sq (kmtSum s u θ)),
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun θ => by positivity),
      kmtSum_integral_norm_sq]

/-- The `ℒ²` seminorm of the truncated Fourier sum, in the explicit form produced by Parseval:
it is the square root of `∑_{x ∈ s} ‖u x‖²`. -/
lemma kmtSum_eLpNorm_eq (s : Finset ℤ) (u : ℤ → ℂ) :
    eLpNorm (kmtSum s u) 2 kmtNu = (ENNReal.ofReal (∑ x ∈ s, ‖u x‖ ^ 2)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := (continuous_kmtSum s u).aestronglyMeasurable) (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [kmtSum_lintegral_enorm_sq]

/-- The `ℒ²` seminorm with respect to the counting measure on `ℤ` is the `ℓ²` norm
`(∑'_x ‖u x‖²)^(1/2)`. -/
lemma eLpNorm_count_two_eq_tsum (u : ℤ → ℂ) :
    eLpNorm u 2 Measure.count = (∑' x : ℤ, ‖u x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_count]

theorem kmtSum_eLpNorm_two_le (s : Finset ℤ) (u : ℤ → ℂ) : MeasureTheory.eLpNorm (Work.A3.kmtSum s u) 2 Work.A3.kmtNu ≤ MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count := by
  have hbase : ENNReal.ofReal (∑ x ∈ s, ‖u x‖ ^ 2) ≤ ∑' x : ℤ, ‖u x‖ₑ ^ (2 : ℝ) := by
    refine le_trans ?_ (ENNReal.sum_le_tsum s)
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)]
    exact Finset.sum_le_sum fun x _ => (enorm_rpow_two_eq_ofReal_norm_sq (u x)).ge
  rw [kmtSum_eLpNorm_eq, eLpNorm_count_two_eq_tsum]
  exact ENNReal.rpow_le_rpow hbase (by norm_num)

end

end Work.A3
