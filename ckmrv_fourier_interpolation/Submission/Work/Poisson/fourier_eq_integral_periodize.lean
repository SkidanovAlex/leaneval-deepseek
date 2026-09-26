import Mathlib
import Submission.Work.Modular.Poisson.Periodize

/-!
# The Fourier transform as the integral of the periodisation against a character

We prove that for a discrete lattice `L ⊆ EuclideanSpace ℝ (Fin n)` spanning `ℝⁿ`, for a point
`y` of the dual lattice `L*`, and for a Schwartz function `f`,

`𝓕 f y = ∫_{d ⁻¹' (0,1]ⁿ} charFun y z * periodize L f z`,

where `periodize L f z = ∑_{x' ∈ L} f (z + x')` and `d` is a linear isomorphism carrying `L`
onto the standard integer lattice.

The proof: the character `charFun y` is `L`-periodic when `y ∈ L*`, so
`charFun y z * f z` unfolded over the fundamental domain `d ⁻¹' (0,1]ⁿ` of `L` equals the
integral of `charFun y z * f (z + x')` over the domain, summed over `x' ∈ L`; exchanging the
sum and the integral (which is legitimate because the family of norms is summable) gives the
integral of `charFun y z * periodize L f z`.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Work.Poisson

open MeasureTheory
open scoped Pointwise

variable {n : ℕ}

/-- The Fourier character `exp (-2π i ⟪·, y⟫)` is multiplicative. -/
lemma charFun_add (y a w : EuclideanSpace ℝ (Fin n)) :
    Work.Modular.charFun y (a + w)
      = Work.Modular.charFun y a * Work.Modular.charFun y w := by
  simp only [Work.Modular.charFun, inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The Fourier character is unimodular. -/
lemma norm_charFun (y z : EuclideanSpace ℝ (Fin n)) : ‖Work.Modular.charFun y z‖ = 1 := by
  rw [Work.Modular.charFun, Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

/-- The Fourier character is continuous. -/
lemma continuous_charFun (y : EuclideanSpace ℝ (Fin n)) :
    Continuous (Work.Modular.charFun y) := by
  unfold Work.Modular.charFun
  fun_prop

/-- If `y` belongs to the dual lattice of `L`, the character `charFun y` is trivial on `L`. -/
lemma charFun_eq_one_of_mem_dual (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Work.Modular.dualLattice L) (a : ↥L) :
    Work.Modular.charFun y (a : EuclideanSpace ℝ (Fin n)) = 1 := by
  obtain ⟨m, hm⟩ := hy (a : EuclideanSpace ℝ (Fin n)) a.2
  rw [Work.Modular.charFun, real_inner_comm, hm, Complex.ofReal_intCast]
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ)
        = ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-- If `y` belongs to the dual lattice of `L`, then `charFun y` is invariant under translation
by elements of `L`. -/
lemma charFun_add_mem_dual (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Work.Modular.dualLattice L) (a : ↥L)
    (w : EuclideanSpace ℝ (Fin n)) :
    Work.Modular.charFun y (a + w) = Work.Modular.charFun y w := by
  rw [charFun_add, charFun_eq_one_of_mem_dual L hy a, one_mul]

/-- The function `z ↦ charFun y z * f z` is integrable for a Schwartz function `f`. -/
lemma integrable_charFun_mul (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (y : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => Work.Modular.charFun y z * f z) volume := by
  refine Integrable.bdd_mul (c := 1) (f.integrable (μ := volume))
    (continuous_charFun y).aestronglyMeasurable ?_
  filter_upwards with z
  rw [norm_charFun]

/-- The set `d ⁻¹' (0,1]ⁿ` is measurable. -/
lemma measurableSet_preimage_cubeE (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (d ⁻¹' Work.Modular.cubeE (Fin n)) :=
  (Work.Modular.measurableSet_unitCube (ι := Fin n)).preimage
    ((EuclideanSpace.equiv (Fin n) ℝ).continuous.measurable.comp
      (LinearMap.continuous_of_finiteDimensional d.toLinearMap).measurable)

/-- A global bound for a Schwartz function. -/
lemma exists_bound_norm (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    ∃ C, ∀ x : EuclideanSpace ℝ (Fin n), ‖f x‖ ≤ C := by
  obtain ⟨C, _, hC'⟩ := f.decay 0 0
  exact ⟨C, fun x => by simpa using hC' x⟩

/-- The family of translates of `‖f‖` restricted to the fundamental domain `d ⁻¹' (0,1]ⁿ` is
summable. This is the summability input needed to exchange the lattice sum with the integral. -/
lemma summable_integral_norm_translates
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ Work.Modular.intLatticeE (Fin n))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable fun x' : ↥L =>
      ∫ w in (d ⁻¹' Work.Modular.cubeE (Fin n)), ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖ := by
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  haveI : VAddInvariantMeasure ↥L (EuclideanSpace ℝ (Fin n)) volume := by
    haveI : VAddInvariantMeasure ↥(L.toAddSubgroup) (EuclideanSpace ℝ (Fin n)) volume :=
      inferInstance
    infer_instance
  have hF := Work.Modular.isAddFundamentalDomain_preimage L d hd
  have hFmeas := measurableSet_preimage_cubeE d
  haveI : IsFiniteMeasure (volume.restrict (d ⁻¹' Work.Modular.cubeE (Fin n))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    rw [Measure.addHaar_preimage_linearEquiv volume d, Work.Modular.volume_cubeE, mul_one]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := exists_bound_norm f
  have hterm : ∀ x' : ↥L, ∫⁻ w in (d ⁻¹' Work.Modular.cubeE (Fin n)),
        ENNReal.ofReal ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖
      = ENNReal.ofReal (∫ w in (d ⁻¹' Work.Modular.cubeE (Fin n)),
          ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖) := by
    intro x'
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · refine Integrable.of_bound ?_ C ?_
      · exact ((f.continuous.comp (continuous_const.add continuous_id)).norm).aestronglyMeasurable
      · filter_upwards with w
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hC _
    · filter_upwards with w; exact norm_nonneg _
  have hlin := hF.lintegral_eq_tsum'' (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ‖f z‖)
  have h1 : (∑' x' : ↥L, ENNReal.ofReal (∫ w in (d ⁻¹' Work.Modular.cubeE (Fin n)),
        ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖))
      = ∑' x' : ↥L, ∫⁻ w in (d ⁻¹' Work.Modular.cubeE (Fin n)), ENNReal.ofReal
          ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖ :=
    tsum_congr fun x' => (hterm x').symm
  have h2 : (∑' x' : ↥L, ∫⁻ w in (d ⁻¹' Work.Modular.cubeE (Fin n)), ENNReal.ofReal
        ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖)
      = ∑' x' : ↥L, ∫⁻ w in (d ⁻¹' Work.Modular.cubeE (Fin n)), ENNReal.ofReal
          ‖f (x' +ᵥ w)‖ :=
    tsum_congr fun x' => setLIntegral_congr_fun hFmeas
      (fun w _ => by rw [Submodule.vadd_def, vadd_eq_add])
  have hne : (∑' x' : ↥L, ENNReal.ofReal (∫ w in (d ⁻¹' Work.Modular.cubeE (Fin n)),
        ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖)) ≠ ⊤ := by
    rw [h1, h2, ← hlin]
    rw [← ofReal_integral_eq_lintegral_ofReal f.integrable.norm
      (ae_of_all _ fun z => norm_nonneg _)]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.summable_toReal hne).congr
    (fun x' => ENNReal.toReal_ofReal (integral_nonneg (fun w => norm_nonneg _)))

/-- The integrand `w ↦ charFun y w * f (w + x')` is integrable over the finite-measure
fundamental domain. -/
lemma integrable_charFun_mul_shift (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (x' : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n) => Work.Modular.charFun y w * f (w + x'))
      (volume.restrict (d ⁻¹' Work.Modular.cubeE (Fin n))) := by
  haveI : IsFiniteMeasure (volume.restrict (d ⁻¹' Work.Modular.cubeE (Fin n))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    rw [Measure.addHaar_preimage_linearEquiv volume d, Work.Modular.volume_cubeE, mul_one]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := exists_bound_norm f
  refine Integrable.of_bound ?_ C ?_
  · exact ((continuous_charFun y).mul
      (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · filter_upwards with w
    rw [norm_mul, norm_charFun, one_mul]
    exact hC _

theorem fourier_eq_integral_periodize {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ Work.Modular.intLatticeE (Fin n))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ Work.Modular.dualLattice L) :
    FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) f y
      = ∫ z in (d ⁻¹' Work.Modular.cubeE (Fin n)),
        Work.Modular.charFun y z * Work.Modular.periodize L f z := by
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  haveI : VAddInvariantMeasure ↥L (EuclideanSpace ℝ (Fin n)) volume := by
    haveI : VAddInvariantMeasure ↥(L.toAddSubgroup) (EuclideanSpace ℝ (Fin n)) volume :=
      inferInstance
    infer_instance
  have hF := Work.Modular.isAddFundamentalDomain_preimage L d hd
  have hFmeas := measurableSet_preimage_cubeE d
  rw [FourierTransform.fourierCLM_apply, Work.Modular.fourier_eq_integral_charFun]
  -- unfold `∫ z, charFun y z * f z` over the fundamental domain `d ⁻¹' (0,1]ⁿ`
  rw [hF.integral_eq_tsum'' (fun z : EuclideanSpace ℝ (Fin n) => Work.Modular.charFun y z * f z)
    (integrable_charFun_mul f y)]
  -- rewrite each summand: the character is `L`-periodic
  rw [show (∑' x' : ↥L, ∫ w in (d ⁻¹' Work.Modular.cubeE (Fin n)),
          Work.Modular.charFun y (x' +ᵥ w) * f (x' +ᵥ w))
        = ∑' x' : ↥L, ∫ w in (d ⁻¹' Work.Modular.cubeE (Fin n)),
            Work.Modular.charFun y w * f (w + (x' : EuclideanSpace ℝ (Fin n))) from
      tsum_congr fun x' => setIntegral_congr_fun hFmeas fun w _ => by
        rw [Submodule.vadd_def, vadd_eq_add, charFun_add, add_comm,
          charFun_eq_one_of_mem_dual L hy x', one_mul]]
  -- exchange the lattice sum and the integral
  haveI : IsFiniteMeasure (volume.restrict (d ⁻¹' Work.Modular.cubeE (Fin n))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    rw [Measure.addHaar_preimage_linearEquiv volume d, Work.Modular.volume_cubeE, mul_one]
    exact ENNReal.ofReal_lt_top
  rw [integral_tsum_of_summable_integral_norm
    (fun x' : ↥L => integrable_charFun_mul_shift f d y (x' : EuclideanSpace ℝ (Fin n)))
    (by
      refine (summable_integral_norm_translates L hspan d hd f).congr fun x' => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      show ‖f ((x' : EuclideanSpace ℝ (Fin n)) + w)‖
        = ‖Work.Modular.charFun y w * f (w + (x' : EuclideanSpace ℝ (Fin n)))‖
      rw [norm_mul, norm_charFun, one_mul, add_comm])]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  show (∑' i : ↥L, Work.Modular.charFun y w * f (w + (i : EuclideanSpace ℝ (Fin n))))
      = Work.Modular.charFun y w * Work.Modular.periodize L f w
  rw [tsum_mul_left, Work.Modular.periodize_apply]

end Work.Poisson
