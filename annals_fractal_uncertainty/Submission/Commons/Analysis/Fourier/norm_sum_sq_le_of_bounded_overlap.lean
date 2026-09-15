import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

/-!
# `L²` almost-orthogonality for functions with bounded-overlap Fourier support

If `F i : EuclideanSpace ℝ ι → ℂ` (`i : Fin N`) are integrable functions whose Fourier
transforms are supported (up to a null set) in sets `S i`, and if no point of `EuclideanSpace ℝ ι`
lies in more than `C` of the sets `S i`, then

`∫ x, ‖∑ i, F i x‖ ^ 2 ≤ C * ∑ i, ∫ x, ‖F i x‖ ^ 2`.

This is the elementary `L²` almost-orthogonality estimate that underlies square-function and
decoupling arguments: on the Fourier side each summand is localised to `S i`, so at a frequency
`ξ` only the at most `C` summands with `ξ ∈ S i` contribute, and Cauchy–Schwarz over that set
costs a factor `C`.

The proof is Plancherel's theorem (in the form `∫ ‖h‖² = ∫ ‖𝓕 h‖²` for an `L¹ ∩ L²` function,
built here on top of
`Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp` and Plancherel in `L²`) together
with the linearity of the pointwise Fourier transform over finite sums and the pointwise
Cauchy–Schwarz inequality.

## Main statements

* `Commons.Analysis.Fourier.integral_norm_sq_eq_integral_fourier_norm_sq`: Plancherel.
* `Commons.Analysis.Fourier.fourier_finsetSum`: linearity of `𝓕` over a finite sum.
* `Commons.Analysis.Fourier.norm_sum_sq_le_of_bounded_overlap`: the almost-orthogonality bound.
-/

open MeasureTheory
open scoped FourierTransform ENNReal BigOperators

namespace Commons.Analysis.Fourier

/-- The square of the `L²` norm of an `L²` class is the integral of the square of the norm of a
representative. -/
theorem lp_integral_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (f : Lp ℂ 2 (volume : Measure V)) :
    ∫ x, ‖(f : V → ℂ) x‖ ^ 2 = ‖f‖ ^ 2 := by
  have hf : AEStronglyMeasurable (f : V → ℂ) (volume : Measure V) := Lp.aestronglyMeasurable f
  have hnorm : ‖f‖ = lpNorm (f : V → ℂ) 2 (volume : Measure V) := by
    rw [Lp.norm_def, toReal_eLpNorm hf]
  have hrpow : ∀ x : V, ‖(f : V → ℂ) x‖ ^ (2:ℝ) = ‖(f : V → ℂ) x‖ ^ 2 :=
    fun x => Real.rpow_two _
  have hInt : ∫ x, ‖(f : V → ℂ) x‖ ^ 2 = (∫ x, ‖(f : V → ℂ) x‖ ^ (2:ℝ)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hrpow)]
  rw [hnorm, lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [hInt]
  have hA : 0 ≤ ∫ x, ‖(f : V → ℂ) x‖ ^ (2:ℝ) :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA]

/-- **Plancherel's theorem** for an `L¹ ∩ L²` function `h` on a finite-dimensional real inner
product space: `∫ x, ‖h x‖² = ∫ ξ, ‖𝓕 h ξ‖²`. -/
theorem integral_norm_sq_eq_integral_fourier_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {h : V → ℂ} (h1 : MemLp h 1 (volume : Measure V)) (h2 : MemLp h 2 (volume : Measure V)) :
    ∫ x, ‖h x‖ ^ 2 = ∫ ξ, ‖𝓕 h ξ‖ ^ 2 := by
  calc ∫ x, ‖h x‖ ^ 2
      = ∫ x, ‖(h2.toLp h : V → ℂ) x‖ ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [h2.coeFn_toLp] with x hx
        rw [hx]
    _ = ‖h2.toLp h‖ ^ 2 := lp_integral_norm_sq _
    _ = ‖(𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V))‖ ^ 2 := by
          rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x‖ ^ 2 :=
          (lp_integral_norm_sq _).symm
    _ = ∫ ξ, ‖𝓕 h ξ‖ ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [fourier_toLp_ae_eq_fourier_of_memLp h1 h2] with x hx
        rw [hx]

/-- Linearity of the pointwise Fourier transform over a finite sum of integrable functions. -/
theorem fourier_finsetSum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} (s : Finset ι) (f : ι → V → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i) (volume : Measure V)) (ξ : V) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  rw [Real.fourier_eq]
  have h1 : (fun v : V => 𝐞 (-inner ℝ v ξ) • (∑ i ∈ s, f i v))
      = (fun v : V => ∑ i ∈ s, 𝐞 (-inner ℝ v ξ) • f i v) := by
    funext v
    rw [Circle.smul_def, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Circle.smul_def]
  rw [h1]
  rw [integral_finsetSum s (fun i hi =>
    (Real.fourierIntegral_convergent_iff (μ := volume) ξ).2 (hf i hi))]
  rfl

/-- **`L²` almost-orthogonality for functions with bounded-overlap Fourier support.**  If the
Fourier transform of `F i` vanishes a.e. off a set `S i`, and every point lies in at most `C` of
the sets `S i`, then `‖∑ i, F i‖_{L²}² ≤ C ∑ i ‖F i‖_{L²}²`. -/
theorem norm_sum_sq_le_of_bounded_overlap {ι : Type*} [Fintype ι] {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (F : Fin N → EuclideanSpace ℝ ι → ℂ) (S : Fin N → Set (EuclideanSpace ℝ ι))
    [∀ ξ, DecidablePred (fun i : Fin N => ξ ∈ S i)]
    (hF1 : ∀ i, MeasureTheory.Integrable (F i) MeasureTheory.volume)
    (hF2 : ∀ i, MeasureTheory.Integrable (fun x => ‖F i x‖ ^ 2) MeasureTheory.volume)
    (hsupp : ∀ i, ∀ᵐ ξ ∂(MeasureTheory.volume),
      ξ ∉ S i → FourierTransform.fourier (F i) ξ = 0)
    (hover : ∀ ξ, ((Finset.univ : Finset (Fin N)).filter (fun i => ξ ∈ S i)).card ≤ C) :
    ∫ x, ‖∑ i, F i x‖ ^ 2 ≤ C * ∑ i, ∫ x, ‖F i x‖ ^ 2 := by
  classical
  set G : EuclideanSpace ℝ ι → ℂ := fun x => ∑ i, F i x with hGdef
  have hmem1 : ∀ i, MemLp (F i) 1 volume := fun i => memLp_one_iff_integrable.2 (hF1 i)
  have hmem2 : ∀ i, MemLp (F i) 2 volume := fun i =>
    (memLp_two_iff_integrable_sq_norm (hF1 i).aestronglyMeasurable).2 (hF2 i)
  have hG1 : Integrable G volume := by
    rw [hGdef]
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i x => F i x) (fun i _ => hF1 i)
  have hGmem2 : MemLp G 2 volume := by
    rw [hGdef]
    simpa using memLp_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i x => F i x) (fun i _ => hmem2 i)
  have hGmem1 : MemLp G 1 volume := memLp_one_iff_integrable.2 hG1
  -- a.e. vanishing of the individual Fourier transforms off their sets
  have hae : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ i, ξ ∉ S i → 𝓕 (F i) ξ = 0 := by
    simpa using (Finset.eventually_all (Finset.univ : Finset (Fin N))).mpr (fun i _ => hsupp i)
  -- linearity of the Fourier transform over the finite sum
  have hFourG : ∀ ξ, 𝓕 G ξ = ∑ i, 𝓕 (F i) ξ := by
    intro ξ
    rw [hGdef]
    simpa using fourier_finsetSum (Finset.univ : Finset (Fin N)) F (fun i _ => hF1 i) ξ
  -- Fourier transforms are `L²`
  have hFMemG : MemLp (fun ξ => 𝓕 G ξ) 2 (volume : Measure (EuclideanSpace ℝ ι)) := by
    exact (memLp_congr_ae (fourier_toLp_ae_eq_fourier_of_memLp hGmem1 hGmem2)).mp
      (Lp.memLp (𝓕 (hGmem2.toLp G) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))))
  have hFMem : ∀ i, MemLp (fun ξ => 𝓕 (F i) ξ) 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
    fun i => (memLp_congr_ae (fourier_toLp_ae_eq_fourier_of_memLp (hmem1 i) (hmem2 i))).mp
      (Lp.memLp (𝓕 ((hmem2 i).toLp (F i)) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))))
  have hintG : Integrable (fun ξ => ‖𝓕 G ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hFMemG.aestronglyMeasurable).mp hFMemG
  have hintF : ∀ i, Integrable (fun ξ => ‖𝓕 (F i) ξ‖ ^ 2) volume := fun i =>
    (memLp_two_iff_integrable_sq_norm (hFMem i).aestronglyMeasurable).mp (hFMem i)
  have hintSum : Integrable (fun ξ => ∑ i, ‖𝓕 (F i) ξ‖ ^ 2) volume := by
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i ξ => ‖𝓕 (F i) ξ‖ ^ 2) (fun i _ => hintF i)
  -- the pointwise Cauchy–Schwarz bound on the Fourier side
  have hpoint : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ‖𝓕 G ξ‖ ^ 2 ≤ C * ∑ i, ‖𝓕 (F i) ξ‖ ^ 2 := by
    filter_upwards [hae] with ξ hξ
    set T := (Finset.univ : Finset (Fin N)).filter (fun i => ξ ∈ S i) with hTdef
    have hcard : (T.card : ℝ) ≤ C := by simpa [hTdef] using hover ξ
    have hsum_eq : (∑ i, 𝓕 (F i) ξ) = ∑ i ∈ T, 𝓕 (F i) ξ := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x _ hx
      exact hξ x (by simpa [hTdef, Finset.mem_filter] using hx)
    rw [hFourG ξ, hsum_eq]
    calc ‖∑ i ∈ T, 𝓕 (F i) ξ‖ ^ 2
        ≤ (∑ i ∈ T, ‖𝓕 (F i) ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le T (fun i => 𝓕 (F i) ξ)) 2
      _ ≤ (T.card : ℝ) * ∑ i ∈ T, ‖𝓕 (F i) ξ‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq (s := T) (f := fun i => ‖𝓕 (F i) ξ‖)
      _ ≤ (T.card : ℝ) * ∑ i, ‖𝓕 (F i) ξ‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => by positivity)
      _ ≤ C * ∑ i, ‖𝓕 (F i) ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun i _ => by positivity))
  have hIntRHS : Integrable (fun ξ => C * ∑ i, ‖𝓕 (F i) ξ‖ ^ 2) volume := hintSum.const_mul C
  have key : ∫ x, ‖G x‖ ^ 2 ≤ C * ∑ i, ∫ x, ‖F i x‖ ^ 2 := by
    calc ∫ x, ‖G x‖ ^ 2
        = ∫ ξ, ‖𝓕 G ξ‖ ^ 2 := integral_norm_sq_eq_integral_fourier_norm_sq hGmem1 hGmem2
      _ ≤ ∫ ξ, C * ∑ i, ‖𝓕 (F i) ξ‖ ^ 2 := integral_mono_ae hintG hIntRHS hpoint
      _ = C * ∫ ξ, ∑ i, ‖𝓕 (F i) ξ‖ ^ 2 := integral_const_mul C _
      _ = C * ∑ i, ∫ ξ, ‖𝓕 (F i) ξ‖ ^ 2 := by
            rw [integral_finsetSum (Finset.univ : Finset (Fin N))
              (f := fun i ξ => ‖𝓕 (F i) ξ‖ ^ 2) (fun i _ => hintF i)]
      _ = C * ∑ i, ∫ x, ‖F i x‖ ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            exact (integral_norm_sq_eq_integral_fourier_norm_sq (hmem1 i) (hmem2 i)).symm
  rw [hGdef] at key
  simpa using key

end Commons.Analysis.Fourier