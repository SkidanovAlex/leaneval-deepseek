import Mathlib
import Submission.Work.KMTAreas.A4.fejerKern_mass
import Submission.Work.KMTAreas.A4.fejerKern_conv

/-!
# The Erdős–Turán/Fejér engine behind `denseMultiples_engine`

Given a set `T ⊆ [-N,N]` of lattice points all of whose multiples `α n` are within `δ` of an
integer, we bound `|T|` in terms of the exponential sums `∑_{l=-N}^{N} e(q α l)`.  The proof is the
classical Fejér-kernel (Erdős–Turán) argument: the trig polynomial

`fejerMajor Q a x = 2a + 2 ∑_{1 ≤ q ≤ Q-1} (1 - q/Q) (sin (2πqa)/(πq)) cos (2πqx)`

is `∫_{x-a}^{x+a} κ` where `κ = fejerKern (Q-1)` is the mass-one Fejér kernel of order `Q`, hence it
is nonnegative, it dominates `∫_{-1/(2Q)}^{1/(2Q)} κ` on the arc `|x| ≤ δ ≤ a - 1/(2Q)`, and it is
`1`-periodic.
-/

namespace Work.KMTAreas.A4

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The Fejér trigonometric majorant of the arc `[-δ, δ]` (with `a = δ + 1/(2Q)`). -/
def fejerMajor (Q : ℕ) (a x : ℝ) : ℝ :=
  2 * a + 2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
    (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
      * Real.cos (2 * Real.pi * (q : ℝ) * x)

theorem continuous_fejerKern (N : ℕ) : Continuous (fejerKern N) := by
  have h : fejerKern N = fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (1 - |(n : ℝ)| / ((N : ℝ) + 1)) * Real.cos (2 * Real.pi * (n : ℝ) * x) := by
    funext x
    rw [fejerKern_trig]
  rw [h]
  fun_prop

/-- `fejerMajor` is the sliding integral of the Fejér kernel. -/
theorem fejerMajor_eq_integral (Q : ℕ) (hQ : 1 ≤ Q) (a x : ℝ) :
    fejerMajor Q a x = ∫ y in (-a)..a, fejerKern (Q - 1) (x - y) := by
  have hcast : (((Q - 1 : ℕ) : ℝ) + 1) = (Q : ℝ) := by rw [Nat.cast_sub hQ]; ring
  have hs : (∑ q ∈ Finset.Icc 1 (Q - 1),
        (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
          * Real.cos (2 * Real.pi * (q : ℝ) * x))
      = (∑ n ∈ Finset.Icc 1 (Q - 1),
        (1 - (n : ℝ) / (((Q - 1 : ℕ) : ℝ) + 1))
          * (Real.sin (2 * Real.pi * (n : ℝ) * a) / (Real.pi * (n : ℝ)))
          * Real.cos (2 * Real.pi * (n : ℝ) * x)) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hcast]
  rw [fejerMajor, fejerKern_conv (Q - 1) a x, hs]

/-- `fejerMajor` is nonnegative (it is the integral of a nonnegative kernel). -/
theorem fejerMajor_nonneg (Q : ℕ) (hQ : 1 ≤ Q) (a : ℝ) (ha : 0 ≤ a) (x : ℝ) :
    0 ≤ fejerMajor Q a x := by
  rw [fejerMajor_eq_integral Q hQ a x]
  have hsub : ∫ y in (-a)..a, fejerKern (Q - 1) (x - y)
      = ∫ z in x - a..x + a, fejerKern (Q - 1) z := by
    rw [intervalIntegral.integral_comp_sub_left (fun z => fejerKern (Q - 1) z) x]
    ring_nf
  rw [hsub]
  exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => fejerKern_nonneg _ _)

/-- `fejerMajor` is `1`-periodic. -/
theorem fejerMajor_periodic (Q : ℕ) (a x : ℝ) (m : ℤ) :
    fejerMajor Q a (x + (m : ℝ)) = fejerMajor Q a x := by
  have hcos : ∀ q : ℕ, Real.cos (2 * Real.pi * (q : ℝ) * (x + (m : ℝ)))
      = Real.cos (2 * Real.pi * (q : ℝ) * x) := by
    intro q
    rw [show 2 * Real.pi * (q : ℝ) * (x + (m : ℝ))
          = 2 * Real.pi * (q : ℝ) * x + (((q : ℤ) * m : ℤ) : ℝ) * (2 * Real.pi) from by
        push_cast; ring]
    exact Real.cos_add_int_mul_two_pi _ ((q : ℤ) * m)
  simp only [fejerMajor, hcos]

/-- On the arc `|x| ≤ δ` the majorant dominates the mass `c = ∫_{-1/(2Q)}^{1/(2Q)} κ`. -/
theorem fejerMajor_ge_mass (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ) (hδ : 0 ≤ δ) (x : ℝ) (hx : |x| ≤ δ) :
    (∫ z in (-(1 / (2 * (Q : ℝ))))..(1 / (2 * (Q : ℝ))), fejerKern (Q - 1) z)
      ≤ fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) x := by
  rw [fejerMajor_eq_integral Q hQ (δ + 1 / (2 * (Q : ℝ))) x]
  have hsub : ∫ y in (-(δ + 1 / (2 * (Q : ℝ))))..(δ + 1 / (2 * (Q : ℝ))),
        fejerKern (Q - 1) (x - y)
      = ∫ z in x - (δ + 1 / (2 * (Q : ℝ)))..x + (δ + 1 / (2 * (Q : ℝ))),
        fejerKern (Q - 1) z := by
    rw [intervalIntegral.integral_comp_sub_left (fun z => fejerKern (Q - 1) z) x]
    ring_nf
  rw [hsub]
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have h2 : x - (δ + 1 / (2 * (Q : ℝ))) ≤ -(1 / (2 * (Q : ℝ))) := by
    rw [abs_le] at hx; linarith [hx.2]
  have h3 : (1 / (2 * (Q : ℝ))) ≤ x + (δ + 1 / (2 * (Q : ℝ))) := by
    rw [abs_le] at hx; linarith [hx.1]
  have h4 : -(1 / (2 * (Q : ℝ))) ≤ 1 / (2 * (Q : ℝ)) := by
    have hQpos : (0 : ℝ) < 1 / (2 * (Q : ℝ)) := by positivity
    linarith
  have hint : IntervalIntegrable (fejerKern (Q - 1)) volume
      (x - (δ + 1 / (2 * (Q : ℝ)))) (x + (δ + 1 / (2 * (Q : ℝ)))) :=
    (continuous_fejerKern (Q - 1)).intervalIntegrable _ _
  exact intervalIntegral.integral_mono_interval h2 h4 h3
    (Filter.Eventually.of_forall (fun u => fejerKern_nonneg _ _)) hint

private lemma cos_eq_re_exp (q : ℕ) (θ : ℝ) :
    Real.cos (2 * Real.pi * (q : ℝ) * θ)
      = (Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (θ : ℂ))).re := by
  have h : 2 * Real.pi * Complex.I * (q : ℂ) * (θ : ℂ)
      = (((2 * Real.pi * (q : ℝ) * θ : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

private lemma expsum_re (q : ℕ) (α : ℝ) (N : ℕ) :
    (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ))))
      = (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h : 2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ)
      = 2 * Real.pi * Complex.I * (q : ℂ) * ((α * (l : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [h, cos_eq_re_exp]

/-- The summation form of the majorant bound. -/
theorem fejerMajor_sum_le (Q N : ℕ) (hQ : 1 ≤ Q) (α a : ℝ) :
    (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fejerMajor Q a (α * (l : ℝ)))
      ≤ 2 * a * (2 * (N : ℝ) + 1) + (2 / Real.pi) * ∑ q ∈ Finset.Icc 1 (Q - 1),
          (1 / (q : ℝ)) * ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖ := by
  have hcard : (((Finset.Icc (-(N : ℤ)) (N : ℤ)) : Finset ℤ).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Int.card_Icc]
    have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
    push_cast
    ring
  have hstep : (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
          (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
            * Real.cos (2 * Real.pi * (q : ℝ) * (α * (x : ℝ))))
      = 2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
          (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
            * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
                Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ)))) := by
    calc (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
            (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
              * Real.cos (2 * Real.pi * (q : ℝ) * (α * (x : ℝ))))
        = 2 * ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∑ q ∈ Finset.Icc 1 (Q - 1),
              (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
                * Real.cos (2 * Real.pi * (q : ℝ) * (α * (x : ℝ))) := by
          rw [Finset.mul_sum]
      _ = 2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
            ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
                * Real.cos (2 * Real.pi * (q : ℝ) * (α * (x : ℝ))) := by
          rw [Finset.sum_comm]
      _ = 2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
            (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
              * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
                  Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ)))) := by
          congr 1
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [← Finset.mul_sum]
  have hexp : (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fejerMajor Q a (α * (l : ℝ)))
      = 2 * a * (((Finset.Icc (-(N : ℤ)) (N : ℤ)) : Finset ℤ).card : ℝ)
        + 2 * ∑ q ∈ Finset.Icc 1 (Q - 1),
            (1 - (q : ℝ) / (Q : ℝ))
              * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
              * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
                  Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ)))) := by
    simp only [fejerMajor]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [show ((((Finset.Icc (-(N : ℤ)) (N : ℤ)) : Finset ℤ).card : ℝ)) * (2 * a)
        = 2 * a * (((Finset.Icc (-(N : ℤ)) (N : ℤ)) : Finset ℤ).card : ℝ) from by ring]
    rw [hstep]
  rw [hexp, hcard]
  have key : ∀ q ∈ Finset.Icc 1 (Q - 1),
      (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
        * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ))))
      ≤ (1 / Real.pi) * ((1 / (q : ℝ)) * ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
    have hqQ : (q : ℝ) ≤ (Q : ℝ) - 1 := by
      have h : (q : ℝ) ≤ ((Q - 1 : ℕ) : ℝ) := by exact_mod_cast hq2
      rw [Nat.cast_sub hQ] at h
      simpa using h
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have hf1 : 0 ≤ 1 - (q : ℝ) / (Q : ℝ) := by
      have : (q : ℝ) / (Q : ℝ) ≤ 1 := by rw [div_le_one hQpos]; linarith
      linarith
    have hf2 : 1 - (q : ℝ) / (Q : ℝ) ≤ 1 := by
      have : 0 ≤ (q : ℝ) / (Q : ℝ) := by positivity
      linarith
    have hsin : |Real.sin (2 * Real.pi * (q : ℝ) * a)| ≤ 1 := Real.abs_sin_le_one _
    have hqpos : (0 : ℝ) < Real.pi * (q : ℝ) := by positivity
    have hC : |∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ)))|
        ≤ ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖ := by
      rw [expsum_re q α N]
      exact Complex.abs_re_le_norm _
    have hsin_abs : |Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ))|
        ≤ 1 / (Real.pi * (q : ℝ)) := by
      rw [abs_div, abs_of_pos hqpos]
      exact div_le_div_of_nonneg_right hsin hqpos.le
    have hfac : |(1 - (q : ℝ) / (Q : ℝ))
        * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))|
        ≤ 1 / (Real.pi * (q : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hf1]
      calc (1 - (q : ℝ) / (Q : ℝ)) * |Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ))|
          ≤ 1 * (1 / (Real.pi * (q : ℝ))) :=
            mul_le_mul hf2 hsin_abs (abs_nonneg _) (by linarith)
        _ = 1 / (Real.pi * (q : ℝ)) := one_mul _
    have hmain : (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
          * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ))))
        ≤ (1 / (Real.pi * (q : ℝ))) * ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖ := by
      calc (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
            * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ))))
          ≤ |(1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
              * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ))))| :=
            le_abs_self _
        _ = |(1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))|
              * |∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ)))| := by
            rw [abs_mul]
        _ ≤ (1 / (Real.pi * (q : ℝ))) * ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖ :=
            mul_le_mul hfac hC (abs_nonneg _) (by positivity)
    calc (1 - (q : ℝ) / (Q : ℝ)) * (Real.sin (2 * Real.pi * (q : ℝ) * a) / (Real.pi * (q : ℝ)))
          * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.cos (2 * Real.pi * (q : ℝ) * (α * (l : ℝ))))
        ≤ (1 / (Real.pi * (q : ℝ))) * ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖ := hmain
      _ = (1 / Real.pi) * ((1 / (q : ℝ)) * ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖) := by
            ring_nf
  have hsum := Finset.sum_le_sum key
  have hlast : 2 * (∑ q ∈ Finset.Icc 1 (Q - 1), (1 / Real.pi) * ((1 / (q : ℝ)) *
        ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖))
      = (2 / Real.pi) * ∑ q ∈ Finset.Icc 1 (Q - 1), (1 / (q : ℝ)) *
        ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖ := by
    conv_lhs => rw [Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  linarith [hsum, hlast]

/-- **The Erdős–Turán/Fejér engine.** -/
theorem denseMultiples_et_engine (Q N : ℕ) (hQ : 1 ≤ Q) (α δ : ℝ) (hδ : 0 ≤ δ)
    (T : Finset ℤ) (hT : ∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ))
    (hgood : ∀ n ∈ T, nDist (α * n) ≤ δ) :
    (T.card : ℝ) ≤ (1 / (∫ x in (-(1 / (2 * (Q : ℝ))))..(1 / (2 * (Q : ℝ))),
        fejerKern (Q - 1) x)) *
      (2 * (δ + 1 / (2 * (Q : ℝ))) * (2 * (N : ℝ) + 1) + (2 / Real.pi) *
        ∑ q ∈ Finset.Icc 1 (Q - 1), (1 / (q : ℝ)) *
          ‖∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (α : ℂ) * (l : ℂ))‖) := by
  set c : ℝ := ∫ x in (-(1 / (2 * (Q : ℝ))))..(1 / (2 * (Q : ℝ))), fejerKern (Q - 1) x with hc
  have hcast : (((Q - 1 : ℕ) : ℝ) + 1) = (Q : ℝ) := by rw [Nat.cast_sub hQ]; ring
  have hc_low : (3 : ℝ) / 4 ≤ c := by
    have hm := fejerKern_mass (Q - 1)
    rw [hc, show (-(1 / (2 * (Q : ℝ)))) = -(1 / (2 * (((Q - 1 : ℕ) : ℝ) + 1))) by rw [hcast],
      show (1 / (2 * (Q : ℝ))) = (1 / (2 * (((Q - 1 : ℕ) : ℝ) + 1))) by rw [hcast]]
    exact hm
  have hcpos : 0 < c := by linarith
  have hcinv : 0 < 1 / c := by positivity
  have ha : (0 : ℝ) ≤ δ + 1 / (2 * (Q : ℝ)) := by positivity
  have hTsub : T ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := fun x hx => Finset.mem_Icc.mpr (hT x hx)
  have hge : ∀ l ∈ T, 1 ≤ (1 / c) * fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ)) := by
    intro l hl
    have hgoodl : |α * (l : ℝ) - ((round (α * (l : ℝ)) : ℤ) : ℝ)| ≤ δ := by
      simpa [nDist] using hgood l hl
    have hp := fejerMajor_periodic Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ))
      (-(round (α * (l : ℝ))))
    have hxp : α * (l : ℝ) + ((-(round (α * (l : ℝ))) : ℤ) : ℝ)
        = α * (l : ℝ) - ((round (α * (l : ℝ)) : ℤ) : ℝ) := by push_cast; ring
    rw [hxp] at hp
    have h3 := fejerMajor_ge_mass Q hQ δ hδ (α * (l : ℝ) - ((round (α * (l : ℝ)) : ℤ) : ℝ)) hgoodl
    rw [← hc] at h3
    have h4 : c ≤ fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ)) := by
      rw [← hp]; exact h3
    rw [show (1 / c) * fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ))
        = fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ)) / c from by ring,
      le_div_iff₀ hcpos]
    linarith [h4]
  have hcardsum : (T.card : ℝ) ≤ (1 / c) *
      ∑ l ∈ T, fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ)) := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    push_cast
    exact Finset.sum_le_sum hge
  have hTsum : (1 / c) * ∑ l ∈ T, fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ))
      ≤ (1 / c) * ∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fejerMajor Q (δ + 1 / (2 * (Q : ℝ))) (α * (l : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hcinv.le
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub
      (fun l _ _ => fejerMajor_nonneg Q hQ _ ha _)
  have hsumBound := fejerMajor_sum_le Q N hQ α (δ + 1 / (2 * (Q : ℝ)))
  have := le_trans hcardsum (le_trans hTsum (mul_le_mul_of_nonneg_left hsumBound hcinv.le))
  rw [show c = ∫ x in (-(1 / (2 * (Q : ℝ))))..(1 / (2 * (Q : ℝ))), fejerKern (Q - 1) x from hc] at this
  exact this

end

end Work.KMTAreas.A4
