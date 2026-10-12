import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseRowsL.LatticeCoulomb.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.cosCellAverage`

The **exact cell-average identity** of `FINDING_latticeKernel.md` §(3c): for every
lattice point `n : Fin 3 → ℤ` and every `z : E3`,

  `⨍_{ucell n} cos(2π⟪q,z⟫) dq = (∏ᵢ sinc(π zᵢ)) · cos(2π⟪nvec n,z⟫)`,

where `ucell n` is the unit cube centred at the lattice point `n` (`volume (ucell n) = 1`,
so the average is the plain integral).

The proof computes the *complex* integral
`∫_{ucell n} e^{i·2π⟪q,z⟫} dq = (∏ᵢ sinc(π zᵢ)) · e^{i·2π⟪nvec n,z⟫}`
and takes real parts.  The complex integral is reduced, by the volume-preserving
identification `E3 ≃ (Fin 3 → ℝ)` (`PiLp.volume_preserving_ofLp`), to an integral over the
product of the three intervals `Icc (nᵢ - 1/2) (nᵢ + 1/2)`; there Fubini
(`MeasureTheory.integral_fintype_prod_eq_prod`) factorises it into the product of the three
one-dimensional integrals, each of which is the elementary
`∫_{a-1/2}^{a+1/2} e^{iwy} dy = e^{iwa}·sinc(w/2)`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The inner product on `E3 = EuclideanSpace ℝ (Fin 3)` in coordinates. -/
private lemma inner_eq_sum (q z : E3) : inner ℝ q z = ∑ i, q.ofLp i * z.ofLp i := by
  simp [PiLp.inner_apply, mul_comm]

/-- Real part of `e^{iθ}` for real `θ`. -/
private lemma cexp_I_re (x : ℝ) : (Complex.exp (Complex.I * ((x : ℝ) : ℂ))).re = Real.cos x := by
  rw [show Complex.I * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) * Complex.I by rw [mul_comm]]
  exact Complex.exp_ofReal_mul_I_re x

/-- Imaginary part of `e^{iθ}` for real `θ`. -/
private lemma cexp_I_im (x : ℝ) : (Complex.exp (Complex.I * ((x : ℝ) : ℂ))).im = Real.sin x := by
  rw [show Complex.I * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) * Complex.I by rw [mul_comm]]
  exact Complex.exp_ofReal_mul_I_im x

/-- `e^{iθ}` has modulus one for real `θ`. -/
private lemma cexp_I_norm (x : ℝ) : ‖Complex.exp (Complex.I * ((x : ℝ) : ℂ))‖ = 1 := by
  rw [show Complex.I * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) * Complex.I by rw [mul_comm]]
  exact Complex.norm_exp_ofReal_mul_I x

/-- The elementary one-dimensional integral:
`∫_{a-1/2}^{a+1/2} e^{i w y} dy = e^{i w a} · sinc (w/2)`. -/
private lemma integral_Icc_cexp (a w : ℝ) :
    ∫ y in Set.Icc (a - 1/2) (a + 1/2), Complex.exp (Complex.I * (((w * y : ℝ) : ℂ)))
      = Complex.exp (Complex.I * (((w * a : ℝ) : ℂ))) * (Real.sinc (w / 2) : ℂ) := by
  by_cases hw : w = 0
  · subst hw
    simp [Real.sinc_zero]
    norm_num
  · -- `(e^{i w/2} - (e^{i w/2})⁻¹)/(i w) = sinc (w/2)`
    have key : (Complex.exp (Complex.I * (((w * (1/2) : ℝ)) : ℂ)) -
          (Complex.exp (Complex.I * (((w * (1/2) : ℝ)) : ℂ)))⁻¹) / (Complex.I * ↑w)
        = (Real.sinc (w / 2) : ℂ) := by
      have hV : Complex.exp (Complex.I * (((w * (1/2) : ℝ)) : ℂ)) =
          ↑(Real.cos (w / 2)) + ↑(Real.sin (w / 2)) * Complex.I := by
        rw [show Complex.I * (((w * (1/2) : ℝ)) : ℂ) = ((w / 2 : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hV' : (Complex.exp (Complex.I * (((w * (1/2) : ℝ)) : ℂ)))⁻¹ =
          ↑(Real.cos (w / 2)) - ↑(Real.sin (w / 2)) * Complex.I := by
        rw [← Complex.exp_neg]
        rw [show -(Complex.I * (((w * (1/2) : ℝ)) : ℂ)) =
            ((-(w / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
        ring
      rw [hV', hV]
      have hw2 : (w / 2 : ℝ) ≠ 0 := div_ne_zero hw two_ne_zero
      have hsinc : (Real.sinc (w / 2) : ℂ) = (↑(Real.sin (w / 2)) : ℂ) / (↑(w / 2) : ℂ) := by
        rw [Real.sinc_of_ne_zero hw2, Complex.ofReal_div]
      rw [hsinc]
      rw [show (↑(Real.cos (w / 2)) + ↑(Real.sin (w / 2)) * Complex.I -
          (↑(Real.cos (w / 2)) - ↑(Real.sin (w / 2)) * Complex.I)) =
          2 * (↑(Real.sin (w / 2)) * Complex.I) by ring]
      rw [show ((w / 2 : ℝ) : ℂ) = (↑w : ℂ) / 2 by push_cast; ring]
      field_simp
    have hIw : Complex.I * (↑w : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hw)
    -- the antiderivative `y ↦ e^{i w y}/(i w)`
    have hderiv : ∀ y ∈ Set.uIcc (a - 1/2) (a + 1/2),
        HasDerivAt (fun y : ℝ =>
            Complex.exp (Complex.I * (((w * y : ℝ)) : ℂ)) / (Complex.I * ↑w))
          (Complex.exp (Complex.I * (((w * y : ℝ)) : ℂ))) y := by
      intro y _
      have h2 : HasDerivAt (fun y : ℝ => ((w * y : ℝ) : ℂ)) (↑w : ℂ) y := by
        have h : HasDerivAt (fun y : ℝ => w * y) w y := by
          simpa using (hasDerivAt_id y).const_mul w
        simpa using h.ofReal_comp
      have h1 : HasDerivAt (fun y : ℝ => Complex.I * (((w * y : ℝ)) : ℂ))
          (Complex.I * (↑w : ℂ)) y := h2.const_mul Complex.I
      have h3 : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (((w * y : ℝ)) : ℂ)))
          (Complex.exp (Complex.I * (((w * y : ℝ)) : ℂ)) * (Complex.I * (↑w : ℂ))) y :=
        (Complex.hasDerivAt_exp _).comp y h1
      refine (h3.div_const (Complex.I * (↑w : ℂ))).congr_deriv ?_
      rw [mul_div_cancel_right₀ _ hIw]
    have hint : IntervalIntegrable
        (fun y : ℝ => Complex.exp (Complex.I * (((w * y : ℝ)) : ℂ)))
        volume (a - 1/2) (a + 1/2) :=
      (by continuity : Continuous
        fun y : ℝ => Complex.exp (Complex.I * (((w * y : ℝ)) : ℂ))).intervalIntegrable _ _
    have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : a - 1/2 ≤ a + 1/2), hsub]
    have e1 : Complex.I * (((w * (a + 1/2) : ℝ)) : ℂ) =
        Complex.I * (((w * a : ℝ)) : ℂ) + Complex.I * (((w * (1/2) : ℝ)) : ℂ) := by
      push_cast; ring
    have e2 : Complex.I * (((w * (a - 1/2) : ℝ)) : ℂ) =
        Complex.I * (((w * a : ℝ)) : ℂ) + -(Complex.I * (((w * (1/2) : ℝ)) : ℂ)) := by
      push_cast; ring
    simp only [e1, e2, Complex.exp_add, Complex.exp_neg]
    rw [div_sub_div_same, ← mul_sub, mul_div_assoc, key]

/-- The three exponentials multiply to the exponential of the sum. -/
private lemma cexp_sum_expand (x : Fin 3 → ℝ) (z : E3) :
    Complex.exp (Complex.I * (((2 * Real.pi) * ∑ i, x i * z.ofLp i : ℝ) : ℂ))
      = ∏ i, Complex.exp (Complex.I * ((((2 * Real.pi) * (x i * z.ofLp i) : ℝ)) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.mul_sum]

theorem cosCellAverage (n : Fin 3 → ℤ) (z : E3) :
    ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z)
      = (∏ i : Fin 3, Real.sinc (Real.pi * z.ofLp i))
        * Real.cos (2 * Real.pi * inner ℝ (nvec n) z) := by
  -- ### The complex version of the identity
  have hmain : ∫ q in ucell n,
        Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ))
      = ((∏ i : Fin 3, Real.sinc (Real.pi * z.ofLp i) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ (nvec n) z : ℝ) : ℂ)) := by
    -- ### Step A: transport from `E3` to `Fin 3 → ℝ`
    have hA : ∫ q in ucell n,
          Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ))
        = ∫ x in Set.pi Set.univ
              (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2)),
            Complex.exp (Complex.I * (((2 * Real.pi) * ∑ i, x i * z.ofLp i : ℝ) : ℂ)) := by
      have hcast : ∀ q : E3,
          Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ))
            = Complex.exp (Complex.I *
                (((2 * Real.pi) * ∑ i, q.ofLp i * z.ofLp i : ℝ) : ℂ)) := by
        intro q
        rw [inner_eq_sum]
      have hemb : MeasurableEmbedding (WithLp.ofLp : E3 → (Fin 3 → ℝ)) :=
        MeasurableEquiv.measurableEmbedding ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm)
      have h := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb hemb
          (fun x : Fin 3 → ℝ =>
            Complex.exp (Complex.I * (((2 * Real.pi) * ∑ i, x i * z.ofLp i : ℝ) : ℂ)))
          (Set.pi Set.univ (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2)))
      rw [← ucell_eq_preimage n] at h
      simpa only [hcast] using h
    -- ### Step B: Fubini over the three coordinates
    have hB : ∫ x in Set.pi Set.univ
              (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2)),
            Complex.exp (Complex.I * (((2 * Real.pi) * ∑ i, x i * z.ofLp i : ℝ) : ℂ))
        = ∏ i : Fin 3,
            Complex.exp (Complex.I * (((((2 * Real.pi) * z.ofLp i)) * ((n i : ℝ)) : ℝ) : ℂ))
            * (Real.sinc (Real.pi * z.ofLp i) : ℂ) := by
      have hSmeas : MeasurableSet (Set.pi Set.univ
          (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2))) :=
        MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
      rw [← integral_indicator hSmeas]
      have hind : (Set.pi Set.univ
            (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2))).indicator
              (fun x : Fin 3 → ℝ =>
                Complex.exp (Complex.I * (((2 * Real.pi) * ∑ i, x i * z.ofLp i : ℝ) : ℂ)))
          = fun x => ∏ i, (Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2)).indicator
              (fun y : ℝ =>
                Complex.exp (Complex.I * ((((2 * Real.pi) * z.ofLp i) * y : ℝ) : ℂ))) (x i) := by
        rw [show (fun x : Fin 3 → ℝ =>
                Complex.exp (Complex.I * (((2 * Real.pi) * ∑ i, x i * z.ofLp i : ℝ) : ℂ)))
            = (fun x => ∏ i,
                Complex.exp (Complex.I * ((((2 * Real.pi) * (x i * z.ofLp i) : ℝ)) : ℂ))) from
            funext (fun x => cexp_sum_expand x z)]
        funext x
        by_cases hx : x ∈ Set.pi Set.univ
            (fun i : Fin 3 => Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2))
        · rw [Set.indicator_of_mem hx]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [Set.indicator_of_mem]
          · ring_nf
          · exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
        · rw [Set.indicator_of_notMem hx]
          have hx' : ∃ i, x i ∉ Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2) := by
            by_contra h
            exact hx (Set.mem_pi.mpr (fun i _ => not_not.mp (not_exists.mp h i)))
          obtain ⟨i, hi⟩ := hx'
          exact (Finset.prod_eq_zero (Finset.mem_univ i)
            (Set.indicator_of_notMem hi _)).symm
      rw [hind, volume_pi]
      rw [integral_fintype_prod_eq_prod (fun i y =>
        (Set.Icc ((n i : ℝ) - 1/2) ((n i : ℝ) + 1/2)).indicator
          (fun y : ℝ =>
            Complex.exp (Complex.I * ((((2 * Real.pi) * z.ofLp i) * y : ℝ) : ℂ))) y)]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [integral_indicator measurableSet_Icc, integral_Icc_cexp]
      rw [show ((2 * Real.pi) * z.ofLp i) / 2 = Real.pi * z.ofLp i by ring]
    -- ### Step C: the product of the three one-dimensional results
    have hC : (∏ i : Fin 3,
            Complex.exp (Complex.I * (((((2 * Real.pi) * z.ofLp i)) * ((n i : ℝ)) : ℝ) : ℂ))
            * (Real.sinc (Real.pi * z.ofLp i) : ℂ))
        = ((∏ i : Fin 3, Real.sinc (Real.pi * z.ofLp i) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ (nvec n) z : ℝ) : ℂ)) := by
      have hexp : ∏ i : Fin 3,
            Complex.exp (Complex.I * (((((2 * Real.pi) * z.ofLp i)) * ((n i : ℝ)) : ℝ) : ℂ))
          = Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ (nvec n) z : ℝ) : ℂ)) := by
        rw [← Complex.exp_sum]
        congr 1
        rw [← Finset.mul_sum]
        congr 1
        rw [← Complex.ofReal_sum]
        congr 1
        rw [inner_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [nvec_apply]
        ring
      rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, hexp, mul_comm]
    rw [hA, hB, hC]
  -- ### Taking real parts
  haveI : IsFiniteMeasure (volume.restrict (ucell n)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_ucell n]
        exact ENNReal.one_lt_top⟩
  have hInt : Integrable
      (fun q : E3 => Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ)))
      (volume.restrict (ucell n)) :=
    Integrable.of_bound
      ((by fun_prop : Continuous (fun q : E3 =>
        Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ)))).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall (fun q =>
        le_of_eq (cexp_I_norm ((2 * Real.pi) * inner ℝ q z))))
  have hre := congrArg Complex.re hmain
  have hstep1 : (∫ q in ucell n,
        Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ))).re
      = ∫ q in ucell n,
        RCLike.re (Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ))) :=
    (integral_re hInt).symm
  rw [hstep1] at hre
  have hcos : ∫ q in ucell n,
        RCLike.re (Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ)))
      = ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun q => by
      show (Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ q z : ℝ) : ℂ))).re
        = Real.cos (2 * Real.pi * inner ℝ q z)
      exact cexp_I_re _))
  rw [hcos] at hre
  rw [show (((∏ i : Fin 3, Real.sinc (Real.pi * z.ofLp i) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ (nvec n) z : ℝ) : ℂ))).re
      = (∏ i : Fin 3, Real.sinc (Real.pi * z.ofLp i))
        * Real.cos (2 * Real.pi * inner ℝ (nvec n) z) from by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, cexp_I_re, cexp_I_im]
    ring] at hre
  exact hre

end Work.BoseRowsL.LatticeCoulomb
