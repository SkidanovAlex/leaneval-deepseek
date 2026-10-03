import Submission.Work.KMTFinal.AllAreas

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The closed hole: Theorem "end-var" and its consequences

The paper's main analytic estimate for the halved averages at finite `λ`-lacunary sets of scales
(`exists_varEstHalfFin_Cv`, formerly the single `sorry` of `Submission.ShiftHole`) is now proved
from the eight areas A1--A8 of the KMT contract (`Work.KMTFinal.allAreas`) through the composition
`Work.KMTContract.exists_varEstHalfFin_Cv_of_allAreas`.  The declarations below were moved here
from `Submission.ShiftHole` (unchanged statements) because the area development imports
`Submission.ShiftHole` itself.
-/

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- **The remaining gap.**  The variational ergodic theorem on the integers
(Krause--Mirek--Tao, Theorem "end-var", Annals 195 (2022)): for a polynomial `P` of degree `≥ 2`,
exponents `1 < p₁, p₂ < ∞` with `p₁⁻¹ + p₂⁻¹ ≤ 1`, `p := (p₁⁻¹ + p₂⁻¹)⁻¹` and `r > 2`, there is a
constant `Cv(Λ)` such that for every `Λ`-lacunary sequence of scales `a` with `a n ≥ 1`, every
`f ∈ ℓ^{p₁}(ℤ)` and every `g ∈ ℓ^{p₂}(ℤ)`,

`‖ (Ã^{n,P(n)}_{a n}(f, g))_n ‖_{ℓᵖ(ℤ; V^r)} ≤ Cv(Λ) ‖f‖_{ℓᵖ₁(ℤ)} ‖g‖_{ℓᵖ₂(ℤ)}`,

where `Ã_N` denotes the upper-half average
`Ã_N(f,g)(x) = (1/⌊N⌋) ∑_{⌊N/2⌋ < n ≤ ⌊N⌋} f(x + n) g(x + P(n))`
and `V^r` is the `r`-variation seminorm.

This is the main analytic estimate of the paper: its proof occupies the bulk of the article and
uses the Ionescu--Wainger multiplier theorem, the inverse theory of Peluse--Prendiville for the
minor arcs, two-parameter Rademacher--Menshov theory and `ℓᵖ`-improving estimates.  Everything
else in the reduction chain leading to Theorem 1.17 is formalised in this development; this
statement was the single `sorry` of the submission and is now closed from the KMT areas.  It is stated for every `K` simultaneously
(i.e. for the finite sets of scales `{a 0, …, a K}`, with a constant independent of `K`), which is
the paper's finite-`λ`-lacunary-set formulation.

The paper's own route to this estimate (Section 4 of the article) is
`end-var` ⟸ `varp` (the variational paraproduct estimates) together with `improv` (the
single-scale minor-arc estimate) and Lemma `iw-prop` (properties of the Ionescu--Wainger Fourier
projections); `varp` is then reduced to `improv` plus the paraproduct case analysis of
Sections 6--9.  The *elementary* harmonic-analytic tools on which that route rests have been
collected in the shared commons (they are Mathlib+commons lemmas, independent of this
development); the following are available:

* `Commons.Analysis.Variation.rademacher_menshov_variation_one_dim`,
  `…rademacher_menshov_variation_two_dim` (the paper's Lemma 2drm and its one-dimensional
  analogue) and `…rademacher_menshov_bilinear` (the paper's Corollary rm-bil);
* `Commons.Analysis.Walsh.exists_khintchine_hilbert` (two-sided Khintchine /
  Marcinkiewicz--Zygmund in Hilbert space), `…khintchine_bilinear`,
  `…exists_khintchine_le_of_two_le`, `…exists_rademacher_kahane` (Kahane's moment comparison),
  `…exists_rademacher_maximal_lp_le`, `…exists_rademacher_maximal_l2_le_hilbert`,
  `…khintchine_lower_hilbert` and `…rademacher_levy_le`;
* `Commons.Analysis.Fourier.hausdorff_young_zmod` and `…nikolskii_zmod_sup_sq_le`
  (finite harmonic analysis on `ZMod n`);
* `Commons.Analysis.Integral.riesz_thorin_finite` and `…riesz_thorin_finite_linfty`
  (Riesz--Thorin interpolation for finite measure spaces, including the `L¹ → L^∞` endpoint)
  together with `Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two`
  (real Marcinkiewicz interpolation, as used in Appendix B of the paper);
* `Commons.MeasureTheory.Function.eLpNorm_eq_iSup_lintegral_mul_sigmaFinite` (`Lᵖ` duality),
  `…eLpNorm_rpow_sum_le` (the `ℓ^r`-valued Minkowski inequality),
  `…eLpNorm_mul_le_eLpNorm_mul_eLpNorm_complex` (Hölder) and
  `Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm`;
* `Commons.Analysis.InnerProductSpace.cotlar_stein` (Cotlar--Stein almost orthogonality) and
  `Commons.LinearAlgebra.Matrix.schur_test_finite` (the Schur test);
* `Commons.Analysis.Polynomial.real_level_set_volume_le` (the real analogue of the
  concentration estimate of Appendix C).

* the tensor-product norm factorisations of the paper's Notation section,
  `Commons.Analysis.Tensor.bilinear_tensor_norm_le` and `…linear_tensor_norm_le`
  (the paper's `ttensor`/`ttensor-bil`), together with
  `Commons.NumberTheory.ZModPolynomial.averaging_bilinear_factor_coprime` (the
  Chinese-remainder factorisation of the arithmetic averaging operator) and
  `Commons.MeasureTheory.Function.eLpNorm_integral_le_lintegral_eLpNorm` (Minkowski's
  integral inequality for `eLpNorm`);
* the Calderón--Zygmund toolkit of the paper's Appendix B:
  `Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d` (and its
  Banach-valued form `…calderon_zygmund_decomposition_1d_banach`),
  `Commons.Analysis.CalderonZygmund.lacunary_shifted_kernel_sum_le` (the lacunary
  off-diagonal kernel estimate) and
  `Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_banach` (vector-valued
  Marcinkiewicz interpolation);
* the crude multiplier bounds of the paper's Lemma `crude-mult`:
  `Commons.Analysis.Fourier.fourier_transform_rescaled_decay`,
  `…fourier_transform_min_decay`, `…fourierCoeffOn_second_deriv_decay`,
  `…fourierCoeffOn_rescaled_decay`, `…l2_multiplier_bound`, and their consequences
  `Commons.Analysis.Fourier.crude_multiplier_lp_le`,
  `Commons.Analysis.Fourier.crude_bilinear_multiplier_lp_le` and
  `Commons.Analysis.Convolution.bilinear_kernel_lp_le` (with the kernel sums
  `Commons.Analysis.Convolution.rescaled_kernel_tsum_le` and
  `…rescaled_kernel_integral_le`); and
* `Commons.Analysis.CalderonZygmund.cz_shift` (the paper's Theorem `cz-shift`, Appendix B:
  the shifted Calderón--Zygmund multiplier bound for lacunary families, with its whole proof --
  Calderón--Zygmund decomposition, the lacunary off-diagonal kernel estimate, Plancherel and
  Marcinkiewicz interpolation -- assembled from the commons) and its square-function
  consequence `…cz_shift_square_function`; and
* `Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_euclidean` (the
  Calderón--Zygmund decomposition on `ℝⁿ`, built on the 1-D dyadic grid of
  `…calderon_zygmund_decomposition_1d`);
* the vector-valued quantitative Shannon sampling estimates
  `Commons.Analysis.Fourier.sampling_lp_integral_le_pi` and `…sampling_lp_lattice_le_pi`
  (`ℓ^p ∼ L^p` for band-limited `ℂ^n`-valued functions, the form of Theorem `Sampling` used
  in the paper); and
* the miscellaneous tools `Commons.Analysis.Fourier.smooth_approx_interval` (Lemma `calc`),
  `Commons.Analysis.InnerProductSpace.hahn_banach_convexHull` (Lemma `hahn`) and
  `Commons.NumberTheory.IonescuWainger.iw_height_element_le` (Lemma `mag-lem`(ii)).

The genuinely hard inputs -- the Ionescu--Wainger multiplier theorem, the Peluse--Prendiville
inverse theory for the minor arcs, and the vector-valued Lépingle inequality of Section 8 --
are *not* available and are not formalised anywhere; they are the mathematical obstruction.
Further commons material (the prime-uniform form of the Appendix C concentration estimates,
needed for the arithmetic bilinear estimates of Section 10 and for the modulus-independence
emphasised there, together with the discrete Calderón--Zygmund theory and the discrete Hilbert
transform for harmonic analysis on the integers `Z` on which the whole paper takes place):

* Appendix C, uniformly in the prime: `Commons.NumberTheory.ZModPolynomial.level_set_ncard_uniform_in_p`,
  `…prime_power_fiber_weak_uniform`, `…prime_power_fiber_ls_le_uniform`,
  `…poly_average_lp_improving_uniform`, `…bilinear_average_lq_uniform`;
* Ionescu--Wainger height arithmetic (Appendix A): `Commons.NumberTheory.IonescuWainger.iw_height_card_le`
  (`mag-lem`(iii)), `…iw_height_separated` (the non-aliasing separation of the height set), and
  the arithmetic symbol: `Commons.Analysis.Fourier.arith_symbol_complete_period`,
  `Commons.NumberTheory.IonescuWainger.arith_symbol_multiplicative`;
* discrete Calderón--Zygmund theory on `Z` (with the underlying integer CZ decomposition):
  `Commons.Analysis.DiscreteCZ.discrete_convolution_weak_type_one`,
  `…discrete_convolution_lp_bounded` (`1 < p < 2`) and `…discrete_convolution_lp_bounded_large`
  (`p > 2`, by duality); the almost-orthogonality tool `Commons.Analysis.OperatorTheory.cotlar_stein_finset`;
* the discrete Hilbert transform: `Commons.Analysis.Hilbert.discrete_hilbert_transform_l2`,
  `…discrete_hilbert_transform_lp`, `…discrete_hilbert_transform_lp_hilbert`
  (Hilbert-space-valued, the vector-valued form needed here) and the maximal-truncation bound
  `…discrete_hilbert_transform_maximal_lp` (Cotlar's maximal inequality on `Z`);
* the `n`-dimensional Calderón--Zygmund package:
  `Commons.Analysis.CalderonZygmund.cz_weak_type_one_euclidean`, `…cz_lp_euclidean`;
* `Commons.Dynamics.Ergodic.mean_ergodic_Lp` (mean convergence of ergodic averages in `Lᵖ`,
  `1 ≤ p < ∞`);
* `Commons.Analysis.Convolution.discrete_riesz_potential_lp` and its Hilbert-space-valued form
  `…discrete_riesz_potential_lp_hilbert` (the discrete Hardy--Littlewood--Sobolev / fractional
  integration inequality on `Z`). -/
theorem exists_varEstHalfFin_Cv (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0) :
    ∃ Cv : ℝ≥0 → ℝ≥0,
      (P.degree ≥ 2) → (1 < p₁) → (1 < p₂) → (p₁ < ⊤) → (p₂ < ⊤) →
        (p₁⁻¹ + p₂⁻¹ ≤ 1) → (2 < r) →
          VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv :=
  Work.KMTContract.exists_varEstHalfFin_Cv_of_allAreas Work.KMTFinal.allAreas P p₁ p₂ r

/-- The variational estimate for the halved averages over the whole `Λ`-lacunary sequence,
obtained from the paper's finite-set estimate `exists_varEstHalfFin_Cv` by clamping and monotone
convergence (`varEstHalf_of_varEstHalfFin`). -/
theorem exists_varEstHalf_Cv (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0) :
    ∃ Cv : ℝ≥0 → ℝ≥0,
      (P.degree ≥ 2) → (1 < p₁) → (1 < p₂) → (p₁ < ⊤) → (p₂ < ⊤) →
        (p₁⁻¹ + p₂⁻¹ ≤ 1) → (2 < r) →
          VarEstHalfR TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv := by
  obtain ⟨CvH, hCvH⟩ := exists_varEstHalfFin_Cv P p₁ p₂ r
  refine ⟨CvH, fun hP h1p₁ h1p₂ h2p₁ h2p₂ hH hr => ?_⟩
  have hA0 : p₁⁻¹ + p₂⁻¹ ≠ 0 := by
    intro hz
    have hle : p₁⁻¹ ≤ 0 := by rw [← hz]; exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ _)
    exact (ENNReal.inv_ne_zero.mpr h2p₁.ne) (le_antisymm hle (zero_le : (0 : ℝ≥0∞) ≤ _))
  have hA1 : p₁⁻¹ + p₂⁻¹ ≠ ⊤ :=
    (lt_of_le_of_lt hH (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  exact varEstHalf_of_varEstHalfFin (ENNReal.inv_ne_zero.mpr hA1) (ENNReal.inv_ne_top.mpr hA0)
    (lt_trans (by norm_num) hr) measurePreserving_TZ (hCvH hP h1p₁ h1p₂ h2p₁ h2p₂ hH hr)

/-- The long variational estimate on the integer shift, obtained from the paper's halved
estimate (Theorem "end-var") by the telescoping argument of Proposition 3.1 (iii). -/
theorem exists_varEstZ_Cv (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0) :
    ∃ Cv : ℝ≥0 → ℝ≥0,
      (P.degree ≥ 2) → (1 < p₁) → (1 < p₂) → (p₁ < ⊤) → (p₂ < ⊤) →
        (p₁⁻¹ + p₂⁻¹ ≤ 1) → (2 < r) →
          VarEstZ P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv := by
  obtain ⟨CvH, hCvH⟩ := exists_varEstHalf_Cv P p₁ p₂ r
  refine ⟨cvLong CvH, fun hP h1p₁ h1p₂ h2p₁ h2p₂ hH hr => ?_⟩
  have hA0 : p₁⁻¹ + p₂⁻¹ ≠ 0 := by
    intro hz
    have hle : p₁⁻¹ ≤ 0 := by rw [← hz]; exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ _)
    exact (ENNReal.inv_ne_zero.mpr h2p₁.ne) (le_antisymm hle (zero_le : (0 : ℝ≥0∞) ≤ _))
  have h1p : (1 : ℝ≥0∞) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hH
  have hpT : (p₁⁻¹ + p₂⁻¹)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hA0
  exact varEstZ_of_varEstHalf h1p₁ h1p₂ h1p hpT
    (le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_of_lt hr))
    (hCvH hP h1p₁ h1p₂ h2p₁ h2p₂ hH hr)

/-- The constant of the integer-shift variational estimate, extracted from
`exists_varEstZ_Cv` (Krause--Mirek--Tao, Theorem "end-var"). -/
noncomputable def CvShift (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  Classical.choose (exists_varEstZ_Cv P p₁ p₂ r)

/-- The defining property of `CvShift`: for admissible parameters it satisfies the integer-shift
variational estimate. -/
theorem varEstZ_CvShift (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0)
    (h : (P.degree ≥ 2) ∧ (1 < p₁) ∧ (1 < p₂) ∧ (p₁ < ⊤) ∧ (p₂ < ⊤) ∧
      (p₁⁻¹ + p₂⁻¹ ≤ 1) ∧ (2 < r)) :
    VarEstZ P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r (CvShift P p₁ p₂ r) :=
  Classical.choose_spec (exists_varEstZ_Cv P p₁ p₂ r)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

end PointwiseErgodicTheorems

end Submission
