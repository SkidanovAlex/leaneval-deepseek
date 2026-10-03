import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.A7.ModelApproxCore_kernelComp
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTPlan.A6.SymSeq2_kernComp_coeff
import Submission.Work.KMTPlan.A6.tsum_norm_kernComp_le
import Submission.Work.KMTAreas.A7.tmKernel_varphitildeNt_decay
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

set_option maxHeartbeats 10000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract
open Work.KMTAreas.A7

noncomputable section

/-! ## §1a.  The arithmetic kernel `arithKernelEx` is bounded

The two elementary facts (`‖fourier‖ = 1`, `‖m_Ẑ‖ ≤ 1`) which bound the arithmetic kernel
`arithKernelEx` by the product of the cardinalities of the exact-height frequency sets.  They are
local copies of the corresponding lemmas of `Work.KMTPlan.A6.modelKernel_l1`, which is not
imported here because it depends on the currently missing module
`Submission.Work.KMTAreas.A7.ModelApproxCore`. -/

/-- The characters of the circle have modulus one. -/
lemma norm_fourier_circle' (n : Int) (alpha : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) n alpha‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The arithmetic symbol mZ is an average of unimodular terms, hence has modulus at most one. -/
lemma norm_mZ_le_one' (P : Polynomial Int) (q : Nat)
    (alpha1 alpha2 : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q alpha1 alpha2‖ ≤ 1 := by
  rw [mZ]
  by_cases hq : q = 0
  · subst hq; simp
  · have hqr : (0 : Real) < q := by
      have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
      exact_mod_cast h1
    have hsum : ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : Int) alpha1 * fourier (T := 1) (P.eval (n : Int)) alpha2‖
        ≤ (q : Real) := by
      calc ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : Int) alpha1
              * fourier (T := 1) (P.eval (n : Int)) alpha2‖
          ≤ ∑ n ∈ Finset.range q, ‖fourier (T := 1) (n : Int) alpha1
              * fourier (T := 1) (P.eval (n : Int)) alpha2‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.range q, (1 : Real) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [norm_mul, norm_fourier_circle', norm_fourier_circle', mul_one]
        _ = (q : Real) := by simp
    have hqnorm : ‖(q : Complex)⁻¹‖ = (q : Real)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
    calc ‖(q : Complex)⁻¹ * ∑ n ∈ Finset.range q, fourier (T := 1) (n : Int) alpha1
            * fourier (T := 1) (P.eval (n : Int)) alpha2‖
        = ‖(q : Complex)⁻¹‖ * ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : Int) alpha1
            * fourier (T := 1) (P.eval (n : Int)) alpha2‖ := norm_mul _ _
      _ ≤ (q : Real)⁻¹ * (q : Real) := by
          rw [hqnorm]
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqr.le)
      _ = 1 := by field_simp

/-- The arithmetic kernel of the exact-height symbol is bounded by the product of the
cardinalities of the two frequency sets. -/
lemma arithKernelEx_norm_le' (rho : Real) (P : Polynomial Int) (q : Nat) (l1 l2 : Nat)
    (j1 j2 : Int) :
    ‖arithKernelEx rho P q l1 l2 j1 j2‖
      ≤ ((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real) := by
  rw [arithKernelEx]
  calc ‖∑ a1 ∈ diffFreqs rho l1, ∑ a2 ∈ diffFreqs rho l2,
          mZ P q a1 a2 * fourier (T := 1) (-j1) a1 * fourier (T := 1) (-j2) a2‖
      ≤ ∑ a1 ∈ diffFreqs rho l1, ‖∑ a2 ∈ diffFreqs rho l2,
          mZ P q a1 a2 * fourier (T := 1) (-j1) a1 * fourier (T := 1) (-j2) a2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a1 ∈ diffFreqs rho l1, ∑ a2 ∈ diffFreqs rho l2,
          ‖mZ P q a1 a2 * fourier (T := 1) (-j1) a1 * fourier (T := 1) (-j2) a2‖ :=
        Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a1 ∈ diffFreqs rho l1, ∑ _a2 ∈ diffFreqs rho l2, (1 : Real) := by
        refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
        rw [norm_mul, norm_mul, norm_fourier_circle', norm_fourier_circle', mul_one, mul_one]
        exact norm_mZ_le_one' P q a b
    _ = ((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## §1b.  The `ℓ¹` and measurability facts about the two model kernels

The model column is the `t`-integral of the twisted bilinear multiplier `BtwistEx` applied to the
two modulated exact-height pieces `T^{l₁}_{φ_{N,t}}f`, `T^{l₂}_{φ̃_{N,t}}g`; its symbol `symM` is
the `t`-integral of the *product of symbols*.  Comparing the two requires the `ℓ¹(ℤ)`-bounds of
the kernels `tmKer ρ l (φ_{N,t})`, `tmKer ρ l (φ̃_{N,t})` (uniformly in `t`), their measurability
in `t`, and the `ℓ¹(ℤ²)`-bound of the arithmetic kernel `arithKerM`. -/

/-- The modulated first bump is jointly measurable as a function of the pair (t, xi). -/
theorem measurable_varphiNt_uncurry (N k : Nat) :
    Measurable (fun q : Real × Real => varphiNt N k q.1 q.2) := by
  have h1 : Measurable (fun q : Real × Real => varphiN N k q.2) :=
    (contDiff_varphiN N k).continuous.measurable.comp measurable_snd
  have h2 : Measurable (fun q : Real × Real => ee ((N : Real) * q.1 * q.2)) := by
    have : Continuous (fun q : Real × Real => ee ((N : Real) * q.1 * q.2)) := by
      unfold ee; fun_prop
    exact this.measurable
  have hgoal : (fun q : Real × Real => varphiNt N k q.1 q.2)
      = (fun q : Real × Real => varphiN N k q.2)
        * (fun q : Real × Real => ee ((N : Real) * q.1 * q.2)) := by
    funext q
    simp only [varphiNt, Pi.mul_apply]
  rw [hgoal]
  exact h1.mul h2

/-- Measurability in t of the kernel coefficients of the modulated first bump. -/
theorem measurable_tmKer_varphiNt (rho : Real) (l N k : Nat) (j : Int) :
    Measurable (fun t : Real => tmKer rho l (varphiNt N k t) j) := by
  have h := Work.KMTAreas.A7.measurable_fourierCoeff_iwSymbolSet (diffFreqs rho l) j
    (measurable_varphiNt_uncurry N k)
  simpa only [tmKer, Work.Analysis.IWMultiplier.iwKernel] using h

/-- Measurability in t of the kernel coefficients of the modulated second bump. -/
theorem measurable_tmKer_varphitildeNt (rho : Real) (P : Polynomial Int) (l N k : Nat)
    (j : Int) :
    Measurable (fun t : Real => tmKer rho l (varphitildeNt P P.natDegree N k t) j) := by
  have h := Work.KMTAreas.A7.measurable_fourierCoeff_iwSymbolSet (diffFreqs rho l) j
    (Work.KMTAreas.A7.measurable_varphitildeNt_uncurry P N k)
  simpa only [tmKer, Work.Analysis.IWMultiplier.iwKernel] using h

/-- From a t-uniform quadratic decay bound, the l1 mass bound against the weight kmtKernWeight. -/
theorem l1_of_weight_decay {kappa : Int → Complex} {C : Real} (hC : 0 ≤ C)
    (h : ∀ j : Int, ‖kappa j‖ ≤ C * ‖kmtKernWeight j‖) :
    Summable (fun j : Int => ‖kappa j‖) ∧ (∑' j : Int, ‖kappa j‖) ≤ C * (∑' j : Int, ‖kmtKernWeight j‖) := by
  have hsum : Summable (fun j : Int => ‖kappa j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) h (summable_kmtKernWeight.mul_left C)
  refine ⟨hsum, ?_⟩
  calc (∑' j : Int, ‖kappa j‖) ≤ ∑' j : Int, C * ‖kmtKernWeight j‖ :=
        Summable.tsum_le_tsum h hsum (summable_kmtKernWeight.mul_left C)
    _ = C * (∑' j : Int, ‖kmtKernWeight j‖) := tsum_mul_left

/-- Quadratic decay, uniform in t, of the kernel of the modulated first bump. -/
theorem weight_decay_tmKer_varphiNt (rho : Real) (l N k : Nat) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : Real) 1, ∀ j : Int,
      ‖tmKer rho l (varphiNt N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k
  refine ⟨4 * ((diffFreqs rho l).card * S) + 1, ?_, fun t ht j => ?_⟩
  · have : (0 : Real) ≤ ((diffFreqs rho l).card : Real) * S := mul_nonneg (Nat.cast_nonneg _) hSnn
    linarith
  · obtain ⟨_, hcd, hcs, h1, h2⟩ := hB t ht
    simpa only [tmKer] using iwKernel_decay_of_bump (diffFreqs rho l) hcd hcs hSnn h1 h2 j

/-- Quadratic decay, uniform in t, of the kernel of the modulated second bump. -/
theorem weight_decay_tmKer_varphitildeNt (rho : Real) (P : Polynomial Int) (l N k : Nat) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : Real) 1, ∀ j : Int,
      ‖tmKer rho l (varphitildeNt P P.natDegree N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨C, hCpos, hdec⟩ := tmKernel_varphitildeNt_decay P rho l N k
  refine ⟨C, hCpos.le, fun t ht j => ?_⟩
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [tmKer] using hdec t ht j

/-- Uniform l1 bound for the kernel of the modulated first bump. -/
theorem uniform_tmKer_varphiNt (rho : Real) (l N k : Nat) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : Real) 1,
      Summable (fun j : Int => ‖tmKer rho l (varphiNt N k t) j‖) ∧
      (∑' j : Int, ‖tmKer rho l (varphiNt N k t) j‖) ≤ C := by
  obtain ⟨C0, hC0, hdec⟩ := weight_decay_tmKer_varphiNt rho l N k
  refine ⟨C0 * (∑' j : Int, ‖kmtKernWeight j‖),
    mul_nonneg hC0 (tsum_nonneg (fun j => norm_nonneg _)), fun t ht => ?_⟩
  exact l1_of_weight_decay hC0 (fun j => hdec t ht j)

/-- Uniform l1 bound for the kernel of the modulated second bump. -/
theorem uniform_tmKer_varphitildeNt (rho : Real) (P : Polynomial Int) (l N k : Nat) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : Real) 1,
      Summable (fun j : Int => ‖tmKer rho l (varphitildeNt P P.natDegree N k t) j‖) ∧
      (∑' j : Int, ‖tmKer rho l (varphitildeNt P P.natDegree N k t) j‖) ≤ C := by
  obtain ⟨C0, hC0, hdec⟩ := weight_decay_tmKer_varphitildeNt rho P l N k
  refine ⟨C0 * (∑' j : Int, ‖kmtKernWeight j‖),
    mul_nonneg hC0 (tsum_nonneg (fun j => norm_nonneg _)), fun t ht => ?_⟩
  exact l1_of_weight_decay hC0 (fun j => hdec t ht j)

/-- l1-summability of the arithmetic kernel arithKerM of the A6 low case. -/
theorem summable_arithKerM (rho : Real) (P : Polynomial Int) (l1 l2 k1 k2 : Nat) :
    Summable (fun p : Int × Int => ‖arithKerM rho P l1 l2 k1 k2 p.1 p.2‖) := by
  obtain ⟨C1, _hC1, hdec1⟩ := cw_etaCut_decay (-(2 * (uScale rho (lcL l1 l2 k1 k2) : Int)))
  obtain ⟨C2, _hC2, hdec2⟩ :=
    cw_etaCut_decay (-((P.natDegree : Int) * 2 * (uScale rho (lcL l1 l2 k1 k2) : Int)))
  have hdec1' : ∀ j : Int, ‖cw (mStarF (uScale rho (lcL l1 l2 k1 k2))) j‖
      ≤ C1 / (1 + |(j : Real)|) ^ 2 := fun j => by simpa only [mStarF] using hdec1 j
  have hdec2' : ∀ j : Int, ‖cw (mStargF P.natDegree (uScale rho (lcL l1 l2 k1 k2))) j‖
      ≤ C2 / (1 + |(j : Real)|) ^ 2 := fun j => by simpa only [mStargF] using hdec2 j
  have h1 : Summable (fun j : Int => ‖cw (mStarF (uScale rho (lcL l1 l2 k1 k2))) j‖) :=
    kernel_l1_of_decay hdec1'
  have h2 : Summable (fun j : Int => ‖cw (mStargF P.natDegree (uScale rho (lcL l1 l2 k1 k2))) j‖) :=
    kernel_l1_of_decay hdec2'
  have hprod : Summable (fun p : Int × Int =>
      ‖cw (mStarF (uScale rho (lcL l1 l2 k1 k2))) p.1‖
        * ‖cw (mStargF P.natDegree (uScale rho (lcL l1 l2 k1 k2))) p.2‖) :=
    Summable.mul_of_nonneg h1 h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (hprod.mul_left (((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real)))
  have hkb := arithKernelEx_norm_le' rho P (arithQ rho (max l1 l2)) l1 l2 p.1 p.2
  rw [arithKerM, norm_mul, norm_mul]
  calc ‖arithKernelEx rho P (arithQ rho (max l1 l2)) l1 l2 p.1 p.2‖
        * ‖cw (mStarF (uScale rho (lcL l1 l2 k1 k2))) p.1‖
        * ‖cw (mStargF P.natDegree (uScale rho (lcL l1 l2 k1 k2))) p.2‖
      ≤ (((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real))
        * ‖cw (mStarF (uScale rho (lcL l1 l2 k1 k2))) p.1‖
        * ‖cw (mStargF P.natDegree (uScale rho (lcL l1 l2 k1 k2))) p.2‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkb (norm_nonneg _))
          (norm_nonneg _)
    _ = (((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real))
        * (‖cw (mStarF (uScale rho (lcL l1 l2 k1 k2))) p.1‖
          * ‖cw (mStargF P.natDegree (uScale rho (lcL l1 l2 k1 k2))) p.2‖) := by ring

/-! ## §2.  Fubini: the `coeff2` of a `t`-integral is the `t`-integral of the `coeff2` -/

private lemma coeff2_integral_swap_aux (sigma : Real → Real → Real → Complex)
    (hsigma_m : Measurable (fun p : Real × Real × Real => sigma p.1 p.2.1 p.2.2))
    {C : Real} (hsigma_b : ∀ t, t ∈ Set.Icc (1/2 : Real) 1 → ∀ x y : Real, ‖sigma t x y‖ ≤ C)
    (a b : Int) :
    coeff2 (fun x y => ∫ t in (1/2 : Real)..1, sigma t x y) a b
      = ∫ t in (1/2 : Real)..1, coeff2 (sigma t) a b := by
  have hE : ∀ z : Real, ‖eeC z‖ = 1 := fun z => by
    rw [eeC]; simp [Complex.norm_exp]
  unfold coeff2
  simp only [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by norm_num : (1/2:Real) ≤ 1)]
  set mx : Measure Real := volume.restrict (Set.Ioc (0:Real) 1) with hmx
  set mt : Measure Real := volume.restrict (Set.Ioc (1/2:Real) 1) with hmt
  have hrealx : mx.real Set.univ = 1 := by
    show (((volume : Measure Real).restrict (Set.Ioc (0:Real) 1)) Set.univ).toReal = 1
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    simp
  have step1 : ∀ x y : Real, (∫ t, sigma t x y ∂mt) * eeC (-(a : Real) * x - (b : Real) * y)
      = ∫ t, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y) ∂mt :=
    fun x y => (MeasureTheory.integral_mul_const _ _).symm
  simp_rw [step1]
  have hInt1 : ∀ x : Real, Integrable (fun z : Real × Real =>
      sigma z.1 x z.2 * eeC (-(a : Real) * x - (b : Real) * z.2)) (mt.prod mx) := by
    intro x
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · have h1 : Measurable (fun z : Real × Real => sigma z.1 x z.2) :=
        hsigma_m.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      have h2 : Measurable (fun z : Real × Real =>
          eeC (-(a : Real) * x - (b : Real) * z.2)) := by
        have hc : Continuous (fun z : Real × Real =>
            eeC (-(a : Real) * x - (b : Real) * z.2)) := by
          unfold eeC; fun_prop
        exact hc.measurable
      exact (h1.mul h2).aestronglyMeasurable
    · have hbox : mt.prod mx = (volume.prod volume).restrict
          (Set.Ioc (1/2 : Real) 1 ×ˢ Set.Ioc (0 : Real) 1) := by
        rw [hmt, hmx, Measure.prod_restrict]
      rw [hbox]
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      have ht : z.1 ∈ Set.Icc (1/2 : Real) 1 := ⟨le_of_lt hz.1.1, hz.1.2⟩
      rw [norm_mul, hE]
      simpa using hsigma_b z.1 ht x z.2
  have step2 : ∀ x : Real, (∫ y, ∫ t, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y)
        ∂mt ∂mx)
      = ∫ t, ∫ y, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y) ∂mx ∂mt := by
    intro x
    exact (MeasureTheory.integral_integral_swap 
      (f := fun t y => sigma t x y * eeC (-(a : Real) * x - (b : Real) * y))
      (hInt1 x)).symm
  simp_rw [step2]
  refine MeasureTheory.integral_integral_swap 
    (f := fun x t => ∫ y, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y) ∂mx) ?_
  refine MeasureTheory.Integrable.of_bound ?_ C ?_
  · have hf : Measurable (fun w : (Real × Real) × Real =>
        sigma w.1.2 w.1.1 w.2 * eeC (-(a : Real) * w.1.1 - (b : Real) * w.2)) := by
      have h1 : Measurable (fun w : (Real × Real) × Real => sigma w.1.2 w.1.1 w.2) :=
        hsigma_m.comp ((measurable_snd.comp measurable_fst).prodMk
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      have h2 : Measurable (fun w : (Real × Real) × Real =>
          eeC (-(a : Real) * w.1.1 - (b : Real) * w.2)) := by
        have hc : Continuous (fun w : (Real × Real) × Real =>
            eeC (-(a : Real) * w.1.1 - (b : Real) * w.2)) := by
          unfold eeC; fun_prop
        exact hc.measurable
      exact h1.mul h2
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' hf.aestronglyMeasurable
  · have hbox : mx.prod mt = (volume.prod volume).restrict
        (Set.Ioc (0 : Real) 1 ×ˢ Set.Ioc (1/2 : Real) 1) := by
      rw [hmx, hmt, Measure.prod_restrict]
    rw [hbox]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    have ht : z.2 ∈ Set.Icc (1/2 : Real) 1 := ⟨le_of_lt hz.2.1, hz.2.2⟩
    have hbound : ∀ᵐ y ∂mx, ‖sigma z.2 z.1 y * eeC (-(a : Real) * z.1 - (b : Real) * y)‖ ≤ C := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      rw [norm_mul, hE]
      simpa using hsigma_b z.2 ht z.1 y
    calc ‖∫ y, sigma z.2 z.1 y * eeC (-(a : Real) * z.1 - (b : Real) * y) ∂mx‖
        ≤ C * mx.real Set.univ := MeasureTheory.norm_integral_le_of_norm_le_const hbound
      _ = C := by rw [hrealx, mul_one]

/-! ## §3.  Fubini: `bilinOp` commutes with the `t`-integral -/

private lemma bilinOp_intervalIntegral_swap_aux {K : Real → Int → Int → Complex}
    {u v : Int → Complex} {Cu Cv : Real}
    (hKs : ∀ t ∈ Set.Icc (1/2 : Real) 1, Summable fun p : Int × Int => ‖K t p.1 p.2‖)
    (hmeas : ∀ p : Int × Int, MeasureTheory.AEStronglyMeasurable (fun t : Real => K t p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure Real).restrict (Set.Ioc (1/2 : Real) 1)))
    (hdom : (∑' p : Int × Int, ∫⁻ t, ‖K t p.1 p.2‖ₑ
      ∂((MeasureTheory.volume : MeasureTheory.Measure Real).restrict (Set.Ioc (1/2 : Real) 1))) ≠ ⊤)
    (hu : ∀ y : Int, ‖u y‖ ≤ Cu) (hv : ∀ y : Int, ‖v y‖ ≤ Cv) (x : Int) :
    ∫ t in (1/2 : Real)..1, Work.KMTAreas.A7.bilinOp (K t) u v x
      = Work.KMTAreas.A7.bilinOp (fun a b => ∫ t in (1/2 : Real)..1, K t a b) u v x := by
  set mt : Measure Real := volume.restrict (Set.Ioc (1/2 : Real) 1) with hmt
  have hae : ∀ᵐ t ∂mt, t ∈ Set.Icc (1/2 : Real) 1 := by
    rw [hmt]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hpt : ∀ᵐ t ∂mt, Work.KMTAreas.A7.bilinOp (K t) u v x
      = ∑' p : Int × Int, K t p.1 p.2 * u (x - p.1) * v (x - p.2) := by
    filter_upwards [hae] with t ht
    exact Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (hKs t ht) hu hv x
  set cu : ℝ≥0∞ := ENNReal.ofReal (max Cu 0) with hcu
  set cv : ℝ≥0∞ := ENNReal.ofReal (max Cv 0) with hcv
  have hcu_top : cu ≠ ⊤ := by rw [hcu]; exact ENNReal.ofReal_ne_top
  have hcv_top : cv ≠ ⊤ := by rw [hcv]; exact ENNReal.ofReal_ne_top
  have hcoe : ∀ z : Complex, (‖z‖ₑ).toReal = ‖z‖ := fun z => by
    rw [show ‖z‖ₑ = ENNReal.ofReal ‖z‖ from by simp [enorm_eq_nnnorm]]; simp
  have hsec : ∀ p : Int × Int, (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) ≠ ⊤ :=
    fun p => ne_top_of_le_ne_top hdom
      (ENNReal.le_tsum (f := fun p : Int × Int => ∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) p)
  have hterm : ∀ p : Int × Int, ∫⁻ t, ‖K t p.1 p.2 * u (x - p.1) * v (x - p.2)‖ₑ ∂mt
      ≤ (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) * cu * cv := by
    intro p
    calc ∫⁻ t, ‖K t p.1 p.2 * u (x - p.1) * v (x - p.2)‖ₑ ∂mt
        ≤ ∫⁻ t, (‖K t p.1 p.2‖ₑ * cu * cv) ∂mt := by
          refine lintegral_mono (fun t => ?_)
          have h1 : ‖u (x - p.1)‖ₑ ≤ cu := by
            rw [hcu]
            calc ‖u (x - p.1)‖ₑ = ENNReal.ofReal ‖u (x - p.1)‖ := by simp [enorm_eq_nnnorm]
              _ ≤ ENNReal.ofReal (max Cu 0) :=
                  ENNReal.ofReal_le_ofReal (le_trans (hu _) (le_max_left Cu 0))
          have h2 : ‖v (x - p.2)‖ₑ ≤ cv := by
            rw [hcv]
            calc ‖v (x - p.2)‖ₑ = ENNReal.ofReal ‖v (x - p.2)‖ := by simp [enorm_eq_nnnorm]
              _ ≤ ENNReal.ofReal (max Cv 0) :=
                  ENNReal.ofReal_le_ofReal (le_trans (hv _) (le_max_left Cv 0))
          rw [enorm_mul, enorm_mul]
          gcongr
      _ = (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) * cu * cv := by
            rw [lintegral_mul_const' cv _ hcv_top, lintegral_mul_const' cu _ hcu_top]
  have hdom2 : (∑' p : Int × Int, ∫⁻ t, ‖K t p.1 p.2 * u (x - p.1) * v (x - p.2)‖ₑ ∂mt) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    exact ne_of_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hdom)
      (lt_top_iff_ne_top.mpr hcu_top)) (lt_top_iff_ne_top.mpr hcv_top))
  have hsum_int : Summable (fun p : Int × Int => ‖∫ t, K t p.1 p.2 ∂mt‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => by
        have h1 : ‖∫ t, K t p.1 p.2 ∂mt‖ₑ ≤ ∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt :=
          MeasureTheory.enorm_integral_le_lintegral_enorm _
        calc ‖∫ t, K t p.1 p.2 ∂mt‖ = (‖∫ t, K t p.1 p.2 ∂mt‖ₑ).toReal := (hcoe _).symm
          _ ≤ (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt).toReal := ENNReal.toReal_mono (hsec p) h1)
      (ENNReal.summable_toReal hdom)
  simp only [intervalIntegral.integral_of_le (by norm_num : (1/2:Real) ≤ 1)]
  rw [← hmt]
  rw [integral_congr_ae hpt]
  rw [MeasureTheory.integral_tsum (fun p : Int × Int =>
    ((hmeas p).mul_const (u (x - p.1))).mul_const (v (x - p.2))) hdom2]
  rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := fun a b : Int => ∫ t, K t a b ∂mt)
    hsum_int hu hv x]
  exact tsum_congr (fun p => by
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const])

/-! ## §4.  Auxiliary facts about the two symbols -/

/-- The character `eeC` has modulus one. -/
private lemma norm_eeC' (z : ℝ) : ‖eeC z‖ = 1 := by
  rw [eeC, show (2 : ℂ) * ↑Real.pi * Complex.I * ↑z = ↑(2 * Real.pi * z) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The symbol `symSeq2 Kar` of a summable kernel is bounded by the `ℓ¹` mass of the kernel. -/
private lemma norm_symSeq2_le {Kar : ℤ → ℤ → ℂ}
    (hKar : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖) (x y : ℝ) :
    ‖symSeq2 Kar x y‖ ≤ ∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖ := by
  have hF : Summable (fun p : ℤ × ℤ =>
      Kar p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)) :=
    Summable.of_norm_bounded hKar (fun p => by rw [norm_mul, norm_eeC', mul_one])
  have htsum : (∑' p : ℤ × ℤ, Kar p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y))
      = ∑' p : ℤ, ∑' r : ℤ, Kar p r * eeC ((p : ℝ) * x + (r : ℝ) * y) :=
    Summable.tsum_prod hF
  rw [symSeq2, ← htsum]
  calc ‖∑' p : ℤ × ℤ, Kar p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)‖
      ≤ ∑' p : ℤ × ℤ, ‖Kar p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)‖ :=
        norm_tsum_le_tsum_norm hF.norm
    _ = ∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖ :=
        tsum_congr (fun p => by rw [norm_mul, norm_eeC', mul_one])

/-- The symbol `symSeq κ` of a summable kernel is bounded by the `ℓ¹` mass of the kernel. -/
private lemma norm_symSeq_le {κ : ℤ → ℂ} (hκ : Summable fun j : ℤ => ‖κ j‖) (x : ℝ) :
    ‖symSeq κ x‖ ≤ ∑' j : ℤ, ‖κ j‖ := by
  have hF : Summable (fun j : ℤ => κ j * eeC ((j : ℝ) * x)) :=
    Summable.of_norm_bounded hκ (fun j => by rw [norm_mul, norm_eeC', mul_one])
  rw [symSeq]
  calc ‖∑' j : ℤ, κ j * eeC ((j : ℝ) * x)‖
      ≤ ∑' j : ℤ, ‖κ j * eeC ((j : ℝ) * x)‖ := norm_tsum_le_tsum_norm hF.norm
    _ = ∑' j : ℤ, ‖κ j‖ := tsum_congr (fun j => by rw [norm_mul, norm_eeC', mul_one])

/-- The joint measurability of the symbol of a two-dimensional kernel. -/
private lemma measurable_symSeq2 (Kar : ℤ → ℤ → ℂ) :
    Measurable (fun q : ℝ × ℝ => symSeq2 Kar q.1 q.2) := by
  rw [show (fun q : ℝ × ℝ => symSeq2 Kar q.1 q.2) = fun q : ℝ × ℝ =>
      ∑' p : ℤ, ∑' r : ℤ, Kar p r * eeC ((p : ℝ) * q.1 + (r : ℝ) * q.2) from by
    funext q; rw [symSeq2]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun p => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun r => ?_)
  have hc : Continuous (fun q : ℝ × ℝ => eeC ((p : ℝ) * q.1 + (r : ℝ) * q.2)) := by
    unfold eeC; fun_prop
  exact hc.measurable.const_mul _

/-- The joint measurability of `(x,t) ↦ symSeq (κ t) x` for a family whose coefficients are
measurable in `t`. -/
private lemma measurable_symSeq_pair {κ : ℝ → ℤ → ℂ}
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) := by
  rw [show (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) = fun q : ℝ × ℝ =>
      ∑' j : ℤ, κ q.2 j * eeC ((j : ℝ) * q.1) from by
    funext q; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun q : ℝ × ℝ => κ q.2 j) := (hκ j).comp measurable_snd
  have h2 : Measurable (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) := by
    have hc : Continuous (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) := by unfold eeC; fun_prop
    exact hc.measurable
  exact h1.mul h2

/-- The joint measurability of the three-factor symbol `(t,x,y) ↦ symSeq2 K x y · symSeq (κ₁ t) x ·
symSeq (κ₂ t) y`. -/
private lemma measurable_sym_product {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hKar : Measurable (fun q : ℝ × ℝ => symSeq2 Kar q.1 q.2))
    (h₁ : Measurable (fun q : ℝ × ℝ => symSeq (κ₁ q.2) q.1))
    (h₂ : Measurable (fun q : ℝ × ℝ => symSeq (κ₂ q.2) q.1)) :
    Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 Kar q.2.1 q.2.2 * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2) := by
  have hA : Measurable (fun q : ℝ × ℝ × ℝ => symSeq2 Kar q.2.1 q.2.2) :=
    hKar.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  have hB : Measurable (fun q : ℝ × ℝ × ℝ => symSeq (κ₁ q.1) q.2.1) :=
    h₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hC : Measurable (fun q : ℝ × ℝ × ℝ => symSeq (κ₂ q.1) q.2.2) :=
    h₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  exact (hA.mul hB).mul hC

/-- The three-factor norm bound. -/
private lemma norm_sym_product_le {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {S B₁ B₂ : ℝ}
    {t x y : ℝ} (hKar : ‖symSeq2 Kar x y‖ ≤ S) (h₁ : ‖symSeq (κ₁ t) x‖ ≤ B₁)
    (h₂ : ‖symSeq (κ₂ t) y‖ ≤ B₂) (hS : 0 ≤ S) (hB₁ : 0 ≤ B₁) :
    ‖symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖ ≤ S * B₁ * B₂ := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hKar h₁ (norm_nonneg _) hS) h₂ (norm_nonneg _)
    (mul_nonneg hS hB₁)

/-- **The coefficient identity, abstractly**: the `(a,b)`-Fourier coefficient of the `t`-integral
of the product symbol is the `t`-integral of the composed kernel. -/
private lemma coeff2_sym_eq_integral_kernComp {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hKar : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hσm : Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 Kar q.2.1 q.2.2 * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2))
    {S : ℝ} (hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
      ‖symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖ ≤ S) :
    coeff2 (fun x y : ℝ => ∫ t in (1/2 : ℝ)..1,
        symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y)
      = fun a b : ℤ => ∫ t in (1/2 : ℝ)..1, kernComp Kar (κ₁ t) (κ₂ t) a b := by
  funext a b
  rw [coeff2_integral_swap_aux
    (fun t x y => symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y) hσm hσb a b]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
  exact SymSeq2_kernComp_coeff Kar (κ₁ t) (κ₂ t) hKar (hκ₁ t ht).of_norm (hκ₂ t ht).of_norm a b

/-- Measurability in `t` of the composed kernel `kernComp Kar (κ₁ t) (κ₂ t)`. -/
private lemma measurable_kernComp_family {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j)
    (hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j) :
    ∀ p : ℤ × ℤ, Measurable (fun t : ℝ => kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2) := by
  intro p
  show Measurable (fun t : ℝ => ∑' a' : ℤ, ∑' b' : ℤ,
    Kar (p.1 - a') (p.2 - b') * κ₁ t a' * κ₂ t b')
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun a' => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun b' => ?_)
  exact (measurable_const.mul (hm₁ a')).mul (hm₂ b')

/-- **The domination bound** for the composed kernels: the `t`-integral of their `ℓ¹` masses is
finite. -/
private lemma hdom_kernComp {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {B₁ B₂ : ℝ}
    (hKar : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hb₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ₁ t j‖) ≤ B₁)
    (hb₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ₂ t j‖) ≤ B₂)
    (hB₁0 : 0 ≤ B₁)
    (hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j)
    (hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j) :
    (∑' p : ℤ × ℤ, ∫⁻ t, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (1/2 : ℝ) 1))) ≠ ⊤ := by
  set mt : Measure ℝ := volume.restrict (Set.Ioc (1/2 : ℝ) 1) with hmt
  have hae : ∀ᵐ t ∂mt, t ∈ Set.Icc (1/2 : ℝ) 1 := by
    rw [hmt]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hunivt : mt Set.univ = ENNReal.ofReal (1/2) := by
    rw [hmt, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    congr 1
    norm_num
  have hKtMeas : ∀ p : ℤ × ℤ, Measurable (fun t : ℝ => kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2) :=
    measurable_kernComp_family hm₁ hm₂
  have hKtsum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      Summable (fun p : ℤ × ℤ => ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖) :=
    fun t ht => Work.A7.ModelApproxCore_aux.summable_kernComp hKar (hκ₁ t ht) (hκ₂ t ht)
  have hKtbound : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖)
        ≤ (∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂ := by
    intro t ht
    refine le_trans (tsum_norm_kernComp_le hKar (hκ₁ t ht) (hκ₂ t ht)) ?_
    have h0 : (0 : ℝ) ≤ ∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖ := tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hb₁ t ht) h0) (hb₂ t ht)
      (tsum_nonneg (fun _ => norm_nonneg _)) (mul_nonneg h0 hB₁0)
  have hpoint : ∀ᵐ t ∂mt, (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ)
      ≤ ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) := by
    filter_upwards [hae] with t ht
    have h1 : (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ :=
      tsum_congr (fun p => by simp [enorm_eq_nnnorm])
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hKtsum t ht)]
    exact ENNReal.ofReal_le_ofReal (hKtbound t ht)
  rw [← MeasureTheory.lintegral_tsum (fun p => ((hKtMeas p).enorm).aemeasurable)]
  exact ne_of_lt (by
    calc ∫⁻ t, (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ) ∂mt
        ≤ ∫⁻ t, ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) ∂mt :=
          lintegral_mono_ae hpoint
      _ = ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) * mt Set.univ :=
          lintegral_const _
      _ = ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) * ENNReal.ofReal (1/2) := by
          rw [hunivt]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- **The pointwise identity**: the integrand of the model column is a bilinear convolution with
the composed kernel. -/
private lemma btwistEx_eq_bilinOp_kernComp (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ)
    {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {f g : ℤ → ℂ} {Cf Cg : ℝ} (t : ℝ) (x : ℤ)
    (hKar : Kar = arithKerM ρ P l₁ l₂ k₁ k₂)
    (hκ₁ : κ₁ t = tmKer ρ l₁ (varphiNt N k₁ t))
    (hκ₂ : κ₂ t = tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
    (hKsum : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁s : Summable fun j : ℤ => ‖κ₁ t j‖) (hκ₂s : Summable fun j : ℤ => ‖κ₂ t j‖)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    BtwistEx ρ P l₁ l₂ (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x
      = Work.KMTAreas.A7.bilinOp (kernComp Kar (κ₁ t) (κ₂ t)) f g x := by
  rw [BtwistEx_eq_bilinOp, ← hKar, Tm_eq_convOp, Tm_eq_convOp, ← hκ₁, ← hκ₂]
  exact (Work.A7.ModelApproxCore_kernelComp (K := Kar) (κ := κ₁ t) (κ' := κ₂ t)
    (u := f) (v := g) (Cu := Cf) (Cv := Cg) hKsum hκ₁s hκ₂s hf hg x).symm

/-- **The model column as the `t`-integral of a bilinear convolution.** -/
private lemma lowModel_eq_integral_kernComp (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {Cf Cg : ℝ}
    (h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n)
    (hKar : Kar = arithKerM ρ P l₁ l₂ k₁ k₂)
    (hκ₁ : ∀ t : ℝ, κ₁ t = tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t))
    (hκ₂ : ∀ t : ℝ, κ₂ t = tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t))
    (hKsum : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁s : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂s : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = ∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.bilinOp (kernComp Kar (κ₁ t) (κ₂ t)) f g x := by
  rw [lowModel_apply, if_pos h]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
  exact btwistEx_eq_bilinOp_kernComp ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ t x hKar
    (hκ₁ t) (hκ₂ t) hKsum (hκ₁s t ht) (hκ₂s t ht) hf hg

/-! ## §5.  The main identity -/

theorem lowModel_eq_bilinOp_symM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp
          (fun u v => Work.KMTPlan.A6.coeff2
            (Work.KMTPlan.A6.symM ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) u v) f g x := by
  obtain ⟨Cf, hfC⟩ := hf
  obtain ⟨Cg, hgC⟩ := hg
  set Kar : ℤ → ℤ → ℂ := arithKerM ρ P l₁ l₂ k₁ k₂ with hKar
  set κ₁ : ℝ → ℤ → ℂ := fun t => tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) with hκ₁
  set κ₂ : ℝ → ℤ → ℂ :=
    fun t => tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) with hκ₂
  obtain ⟨B₁, hB₁0, hB₁⟩ := uniform_tmKer_varphiNt ρ l₁ (Nat.floor (a n)) k₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := uniform_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂
  have hKsum : Summable (fun p : ℤ × ℤ => ‖Kar p.1 p.2‖) := by
    rw [hKar]; exact summable_arithKerM ρ P l₁ l₂ k₁ k₂
  have hκ₁sum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ₁ t j‖) :=
    fun t ht => (hB₁ t ht).1
  have hκ₂sum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ₂ t j‖) :=
    fun t ht => (hB₂ t ht).1
  have hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j := by
    intro j; rw [hκ₁]; exact measurable_tmKer_varphiNt ρ l₁ (Nat.floor (a n)) k₁ j
  have hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j := by
    intro j; rw [hκ₂]; exact measurable_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂ j
  have hσm : Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 Kar q.2.1 q.2.2 * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2) :=
    measurable_sym_product (measurable_symSeq2 Kar)
      (measurable_symSeq_pair hm₁) (measurable_symSeq_pair hm₂)
  have hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
      ‖symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖
        ≤ (∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂ :=
    fun t ht x y => norm_sym_product_le (norm_symSeq2_le hKsum x y)
      (le_trans (norm_symSeq_le (hκ₁sum t ht) x) (hB₁ t ht).2)
      (le_trans (norm_symSeq_le (hκ₂sum t ht) y) (hB₂ t ht).2)
      (tsum_nonneg (fun _ => norm_nonneg _)) hB₁0
  have hsM : symM ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ = fun x y : ℝ => ∫ t in (1/2 : ℝ)..1,
      symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y := by
    funext x y
    show (∫ t in (1/2 : ℝ)..1, symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
        * symSeq (tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t)) x
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) y)
      = ∫ t in (1/2 : ℝ)..1, symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y
    rfl
  have hLHS := lowModel_eq_integral_kernComp ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
    (Kar := Kar) (κ₁ := κ₁) (κ₂ := κ₂) h hKar (fun t => congrFun hκ₁ t)
    (fun t => congrFun hκ₂ t) hKsum hκ₁sum hκ₂sum hfC hgC
  have hdom := hdom_kernComp (Kar := Kar) (κ₁ := κ₁) (κ₂ := κ₂) (B₁ := B₁) (B₂ := B₂)
    hKsum hκ₁sum hκ₂sum (fun t ht => (hB₁ t ht).2) (fun t ht => (hB₂ t ht).2) hB₁0 hm₁ hm₂
  have hcoeff := coeff2_sym_eq_integral_kernComp (Kar := Kar) (κ₁ := κ₁) (κ₂ := κ₂)
    hKsum hκ₁sum hκ₂sum hσm hσb
  have hcoeff' : coeff2 (symM ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂)
      = fun a b : ℤ => ∫ t in (1/2 : ℝ)..1, kernComp Kar (κ₁ t) (κ₂ t) a b := by
    rw [hsM]; exact hcoeff
  rw [hLHS, bilinOp_intervalIntegral_swap_aux
    (K := fun t a b => kernComp Kar (κ₁ t) (κ₂ t) a b)
    (fun t ht => Work.A7.ModelApproxCore_aux.summable_kernComp hKsum (hκ₁sum t ht) (hκ₂sum t ht))
    (fun p => (measurable_kernComp_family hm₁ hm₂ p).aestronglyMeasurable) hdom hfC hgC x]
  exact (congrArg (fun K : ℤ → ℤ → ℂ => Work.KMTAreas.A7.bilinOp K f g x) hcoeff').symm

end

end Work.KMTPlan.A6
