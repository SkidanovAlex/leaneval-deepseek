import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs
import Submission.Work.BourgainPlan.Maximal.genWindow_eq_genBlock
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.polyGeneral_window_lp_leading
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_leading
import Submission.Work.BourgainPlan.Maximal.genWindow_maximal_lp_shift_const

/-!
# Bourgain (7.31): the Gauss-weight **dressing** of the §7.2 model (Lemma 7.29)

Bourgain's Lemma 7.20 / (7.21) bounds the maximal function of the *undressed* model

`genWindow P k q D φ g s m
  = Σ_{a<q} ∫_{|β| ≤ 1/(2D)} ĝ(a/q+β) · conj(Φ_{2^k}(β)) · φ(Dβ) · e(m (a/q+β)) dβ`

(single denominator `q`, all residues `a < q`, no arithmetic weights).  The §7.4 assembly, however,
consumes the **dressed** model of Lemma 7.29 / (7.30), in which every arc carries the complete-sum
(Gauss-sum) weight `W_q(a) = q⁻¹ Σ_{r<q} e(a P(r)/q)` of Bourgain (6.6):

`genWindowGauss P k q D φ g s m
  = Σ_{a<q} W_q(a) ∫_{|β| ≤ 1/(2D)} ĝ(a/q+β) · conj(Φ_{2^k}(β)) · φ(Dβ) · e(m (a/q+β)) dβ`.

Bourgain's (7.31) observes that the weight can be *absorbed into the function*.  The identity proved
here is the exact mechanism,

`genWindowGauss P k q D φ g s m
   = q⁻¹ Σ_{r<q} genWindow (P + C (P (r : ℤ))) k q D φ g s (m + P (r : ℤ))`,

i.e. the Gauss-weighted model is the average over `r < q` of the *undressed* model of the
**constant shift** `P + P(r)` of `P`, evaluated at the shifted output `m + P(r)`.

The mechanism is that `conj (polyProfile (P + C c) N β) = conj (polyProfile P N β) · e(-c β)`
(`genProf_add_C` below): this supplies exactly the factor which turns `e(m (a/q+β))` into
`e((m+c) (a/q+β))`, and `W_q(a) = q⁻¹Σ_r e(a P(r)/q)` then telescopes the weight against the
residue phase.

Consequence (with the companion §7.2 input): the §7.2 model bound for a constant shift `P + C c`
holds *uniformly in `c`* — the shift is a translation of the dilation average along `P(N s)`, and
the §7.1 bound is translation covariant — so the dressed model obeys the same `ℓᵖ` maximal bound as
the undressed one.  That is Bourgain's Lemma 7.29: (7.30) follows from (7.21).
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-! ## The dressed (Gauss-weighted) model -/

/-- The **Gauss-weighted (dressed) model** of Bourgain (7.30): the §7.2 model with the complete
sum `W_q(a) = polyWeight P q a` attached to each arc `a/q`. -/
noncomputable def genWindowGauss (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) : ℂ :=
  ∑ a ∈ Finset.range q,
    polyWeight P q (a : ℤ) *
      ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
        (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
        * (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
            (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))))
        * φ (D * β)
        * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))

/-- The summand of the `a`-th arc of the model, with the profile written as `genProf`. -/
noncomputable def dressSummand (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) (a : ℕ) (β : ℝ) : ℂ :=
  (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
      ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
  * genProf P k β * φ (D * β)
  * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
      ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))

/-- `genWindow` in the `genProf` form. -/
lemma genWindow_eq_sum_dressSummand (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) :
    genWindow P k q D φ g s m
      = ∑ a ∈ Finset.range q, ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
          dressSummand P k q D φ g s m a β := by
  simp only [genWindow, dressSummand, ← genProf_eq_integral]

/-- `genWindowGauss` in the `genProf` form. -/
lemma genWindowGauss_eq_sum_dressSummand (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) :
    genWindowGauss P k q D φ g s m
      = ∑ a ∈ Finset.range q, polyWeight P q (a : ℤ) *
          ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
            dressSummand P k q D φ g s m a β := by
  simp only [genWindowGauss, dressSummand, ← genProf_eq_integral]

/-! ## The conjugated profile of a constant shift -/

/-- The conjugated profile of the constant shift `P + C c` factors out the character `e(-c β)`. -/
lemma star_polyProfile_add_C (P : Polynomial ℤ) (c : ℤ) (N : ℕ) (β : ℝ) :
    starRingEnd ℂ (polyProfile (P + Polynomial.C c) N β)
      = starRingEnd ℂ (polyProfile P N β) * polyE (-((c : ℝ) * β)) := by
  rw [star_polyProfile, star_polyProfile]
  have hfun : (fun s : ℝ => polyE (-(β * (toRealPoly (P + Polynomial.C c)).eval ((N:ℝ)*s))))
      = fun s : ℝ => polyE (-(β * (toRealPoly P).eval ((N:ℝ)*s))) * polyE (-((c:ℝ) * β)) := by
    funext s
    have hev : (toRealPoly (P + Polynomial.C c)).eval ((N:ℝ)*s)
        = (toRealPoly P).eval ((N:ℝ)*s) + (c:ℝ) := by
      unfold toRealPoly
      rw [Polynomial.map_add, Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_C]
      norm_num
    rw [hev]
    rw [show -(β * ((toRealPoly P).eval ((N:ℝ)*s) + (c:ℝ)))
        = -(β * (toRealPoly P).eval ((N:ℝ)*s)) + (-((c:ℝ) * β)) by ring]
    exact (polyE_add _ _).symm
  rw [hfun, intervalIntegral.integral_mul_const]

/-- **The dressing factor**: the conjugated profile of the constant shift `P + C r`. -/
lemma genProf_add_C (P : Polynomial ℤ) (k : ℕ) (r : ℤ) (β : ℝ) :
    genProf (P + Polynomial.C r) k β = genProf P k β * polyE (-((r : ℝ) * β)) := by
  rw [genProf, genProf, star_polyProfile_add_C]

/-! ## The pointwise dressing identity -/

/-- The character `polyE` written as an exponential. -/
lemma polyE_eq_exp (t : ℝ) :
    polyE t = Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := rfl

/-- The swap of the two finite sums of the dressing identity. -/
lemma dress_sum_swap (q : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.range q, (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, F a r)
      = (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, ∑ a ∈ Finset.range q, F a r := by
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]

/-- **The pointwise dressing identity** (Bourgain (7.31)): the complete-sum weight turns the
undressed summand of `P` at the output `m` into the summand of the constant shift `P + C c` at the
output `m + c`. -/
lemma dressSummand_gauss (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) (a : ℕ) (r : ℤ) (β : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((((a : ℝ) / (q : ℝ)) * ((P.eval r : ℤ) : ℝ) : ℝ) : ℂ))
      * dressSummand P k q D φ g s m a β
      = dressSummand (P + Polynomial.C (P.eval r)) k q D φ g s (m + P.eval r) a β := by
  have hp : genProf (P + Polynomial.C (P.eval r)) k β
      = genProf P k β * polyE (-(((P.eval r : ℤ) : ℝ) * β)) := genProf_add_C P k (P.eval r) β
  have hkey : Complex.exp (2 * Real.pi * Complex.I *
        ((((a : ℝ) / (q : ℝ)) * ((P.eval r : ℤ) : ℝ) : ℝ) : ℂ))
      * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
          ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))
      = polyE (-(((P.eval r : ℤ) : ℝ) * β))
        * Complex.exp (2 * Real.pi * Complex.I * (((m + P.eval r : ℤ) : ℂ) *
          ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))) := by
    rw [polyE_eq_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc Complex.exp (2 * Real.pi * Complex.I *
        ((((a : ℝ) / (q : ℝ)) * ((P.eval r : ℤ) : ℝ) : ℝ) : ℂ))
      * dressSummand P k q D φ g s m a β
      = (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
        * genProf P k β * φ (D * β)
        * (Complex.exp (2 * Real.pi * Complex.I *
            ((((a : ℝ) / (q : ℝ)) * ((P.eval r : ℤ) : ℝ) : ℝ) : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))) := by
        simp only [dressSummand]; ring
    _ = (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
        * genProf P k β * φ (D * β)
        * (polyE (-(((P.eval r : ℤ) : ℝ) * β))
          * Complex.exp (2 * Real.pi * Complex.I * (((m + P.eval r : ℤ) : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))) := by rw [hkey]
    _ = dressSummand (P + Polynomial.C (P.eval r)) k q D φ g s (m + P.eval r) a β := by
        simp only [dressSummand]
        rw [hp]
        ring

/-! ## The dressing identity -/

/-- **Bourgain (7.31) / Lemma 7.29.**  The Gauss-weighted model at a single denominator `q` is the
average over `r < q` of the undressed model of the constant shift `P + P(r)`, evaluated at the
shifted output `m + P(r)`. -/
theorem genWindowGauss_eq (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) :
    genWindowGauss P k q D φ g s m
      = (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q,
          genWindow (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s (m + P.eval (r : ℤ)) := by
  have hgen : ∀ r : ℕ,
      genWindow (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s (m + P.eval (r : ℤ))
        = ∑ a ∈ Finset.range q, ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
            dressSummand (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s
              (m + P.eval (r : ℤ)) a β :=
    fun r => genWindow_eq_sum_dressSummand (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s
      (m + P.eval (r : ℤ))
  rw [genWindowGauss_eq_sum_dressSummand]
  rw [Finset.sum_congr rfl (fun r _ => hgen r)]
  rw [← dress_sum_swap q (fun a r => ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
        dressSummand (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s
          (m + P.eval (r : ℤ)) a β)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [polyWeight, mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun β _ => dressSummand_gauss P k q D φ g s m a (r : ℤ) β)


/-! ## The `ℓᵖ` maximal bound for the dressed model -/

/-- Translation invariance of the counting measure on `ℤ`. -/
lemma lintegral_count_add_right (F : ℤ → ℝ≥0∞) (c : ℤ) :
    ∫⁻ m : ℤ, F (m + c) ∂Measure.count = ∫⁻ m : ℤ, F m ∂Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  rw [show (fun a : ℤ => F (a + c)) = fun a => F ((Equiv.addRight c) a) by
    funext a; rw [show (Equiv.addRight c) a = a + c from rfl]]
  rw [Equiv.tsum_eq (Equiv.addRight c) F]

/-- `(q⁻¹)^p · q^{p-1} = q⁻¹` for `q > 0`, `p ≥ 0` (the factor by which the convexity inequality
over the `q` residues is cancelled). -/
lemma ofReal_inv_rpow_mul (q p : ℝ) (hq : 0 < q) (hp : 1 ≤ p) :
    (ENNReal.ofReal q⁻¹) ^ p * (ENNReal.ofReal q) ^ (p - 1) = ENNReal.ofReal q⁻¹ := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg hq.le (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.inv_rpow hq.le, ← Real.rpow_neg hq.le, ← Real.rpow_add hq,
    ← Real.rpow_neg_one]
  ring

/-- The pointwise norm bound for the dressed model: the `q`-average of the undressed models of the
constant shifts `P + P(r)`, evaluated at the shifted outputs `m + P(r)`. -/
lemma enorm_genWindowGauss_le (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) :
    ‖genWindowGauss P k q D φ g s m‖ₑ ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
      ∑ r ∈ Finset.range q,
        ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s (m + P.eval (r:ℤ))‖ₑ := by
  rw [genWindowGauss_eq, enorm_mul]
  rw [show ‖((q:ℂ))⁻¹‖ₑ = ENNReal.ofReal (((q:ℝ)))⁻¹ by
        rw [← ofReal_norm, norm_inv, Complex.norm_natCast]]
  exact mul_le_mul_right (enorm_sum_le _ _) _

/-- **The dressed model obeys the `ℓᵖ` maximal bound whenever the undressed model does so
uniformly over the constant shifts of the polynomial.**  This is the (easy) second half of
Bourgain's Lemma 7.29: the dressing identity `genWindowGauss_eq` plus the convexity inequality
over the `q` residues, plus translation invariance of the counting measure. -/
theorem genWindowGauss_maximal_lp_of_shift (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    {C : ℝ} (hC : 0 < C)
    (hshift : ∀ (c : ℤ) (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
        (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindow (P + Polynomial.C c) k q D φ g s m‖ₑ) ^ p
          ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count) :
    ∀ (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
      (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindowGauss P k q D φ g s m‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
  intro q hq D hD hDq g s hs
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hp1 : (1:ℝ) ≤ p := le_of_lt hp
  -- the sup of the dressed model, bounded by the average of the sup of the shifts
  have hstep : ∀ m : ℤ,
      (⨆ k : ℕ, ‖genWindowGauss P k q D φ g s m‖ₑ)
        ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
            ∑ r ∈ Finset.range q,
              (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
                (m + P.eval (r:ℤ))‖ₑ) := by
    intro m
    refine iSup_le (fun k => ?_)
    refine le_trans (enorm_genWindowGauss_le P k q D φ g s m) ?_
    refine mul_le_mul_right ?_ _
    exact Finset.sum_le_sum
      (fun r _ => le_iSup (fun k => ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
        (m + P.eval (r:ℤ))‖ₑ) k)
  have hstep2 : ∀ m : ℤ,
      (⨆ k : ℕ, ‖genWindowGauss P k q D φ g s m‖ₑ) ^ p
        ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
            ∑ r ∈ Finset.range q,
              (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
                (m + P.eval (r:ℤ))‖ₑ) ^ p := by
    intro m
    set Z : ℕ → ℝ≥0∞ := fun r => ⨆ k : ℕ,
      ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s (m + P.eval (r:ℤ))‖ₑ
    calc (⨆ k : ℕ, ‖genWindowGauss P k q D φ g s m‖ₑ) ^ p
        ≤ (ENNReal.ofReal (((q:ℝ)))⁻¹ * ∑ r ∈ Finset.range q, Z r) ^ p :=
          ENNReal.rpow_le_rpow (hstep m) hp0
      _ = (ENNReal.ofReal (((q:ℝ)))⁻¹) ^ p * (∑ r ∈ Finset.range q, Z r) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0
      _ ≤ (ENNReal.ofReal (((q:ℝ)))⁻¹) ^ p *
            (((q : ℝ≥0∞)) ^ (p - 1) * ∑ r ∈ Finset.range q, (Z r) ^ p) := by
          refine mul_le_mul_right ?_ _
          simpa using ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.range q) Z hp1
      _ = ENNReal.ofReal (((q:ℝ)))⁻¹ * ∑ r ∈ Finset.range q, (Z r) ^ p := by
          rw [show ((q : ℝ≥0∞)) = ENNReal.ofReal ((q:ℝ)) by
                rw [ENNReal.ofReal_natCast]]
          rw [← mul_assoc, ofReal_inv_rpow_mul (q:ℝ) p hqR hp1]
  calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindowGauss P k q D φ g s m‖ₑ) ^ p ∂Measure.count
      ≤ ∫⁻ m : ℤ, ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ Finset.range q,
            (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              (m + P.eval (r:ℤ))‖ₑ) ^ p ∂Measure.count :=
        lintegral_mono (fun m => hstep2 m)
    _ = ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ Finset.range q,
            ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              (m + P.eval (r:ℤ))‖ₑ) ^ p ∂Measure.count := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_finset_sum]
        intro r _
        exact measurable_of_countable _
    _ = ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ Finset.range q,
            ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              m‖ₑ) ^ p ∂Measure.count := by
        congr 1
        refine Finset.sum_congr rfl (fun r _ => ?_)
        exact lintegral_count_add_right
          (fun m : ℤ => (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              m‖ₑ) ^ p) (P.eval (r:ℤ))
    _ ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ Finset.range q,
            (ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
              * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count) := by
        refine mul_le_mul_right ?_ _
        exact Finset.sum_le_sum (fun r _ => hshift (P.eval (r:ℤ)) q hq D hD hDq g s hs)
    _ = ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hqinv : ENNReal.ofReal (((q:ℝ)))⁻¹ = ((q : ℝ≥0∞))⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos hqR, ENNReal.ofReal_natCast]
        rw [hqinv, ← mul_assoc]
        rw [ENNReal.inv_mul_cancel (by simp [hq.ne']) (by simp)]
        rw [one_mul]


/-! ## Bourgain's Lemma 7.29: (7.30) from (7.21) -/

/-- **Bourgain's Lemma 7.29 (7.30)**: the *dressed* (Gauss-weighted) §7.2 model obeys the same `ℓᵖ`
maximal inequality as the undressed model of Lemma 7.20 / (7.21), for every `p > 1`, uniformly in
the denominator `q` and the truncation parameter `D`.  This is the "dressing" step of §7.4: the
arithmetic (Gauss-sum) weights cost nothing, because the weight `W_q(a) = q⁻¹Σ_{r<q}e(aP(r)/q)`
collapses against the residue phase onto a constant shift of `P` and a shifted output index
(`genWindowGauss_eq`). -/
theorem genWindowGauss_maximal_lp (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
      (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindowGauss P k q D φ g s m‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C, hC, hshift⟩ := genWindow_maximal_lp_shift_const P hP hd hp hφ hφs
  exact ⟨C, hC, genWindowGauss_maximal_lp_of_shift P hP hd hp hφ hφs hC hshift⟩


/-! ## Truncated weights: the §7.4 increments

Bourgain's §7.4 (7.60)–(7.64) does not use the *complete* Gauss weight but a **truncated** one
`W^{(T)}_q(a) = q⁻¹ Σ_{r∈T} e(a P(r)/q)` (his `Ω_{s,j}` is a partial sum over the levels
`s' ≤ j`), and needs the `ℓᵖ` maximal bound for the *increments* `Ω_{s,j} − Ω_{s,j−1}`.  The
dressing identity is insensitive to replacing `Finset.range q` by an arbitrary index set `T`
(`genWindowGaussSet_eq`), and the `ℓᵖ` bound survives whenever `#T ≤ q`: the factor `(#T/q)^p`
produced by the convexity inequality over the `#T` shifts, together with the extra `#T` from the
sum of the `#T` copies of the constant, is `≤ 1`.  Hence every truncated Gauss weight — and every
increment — obeys the same `ℓᵖ` bound as the complete one. -/

/-- The dressed model with a **truncated** weight expansion. -/
noncomputable def genWindowGaussSet (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (T : Finset ℕ) (m : ℤ) : ℂ :=
  ∑ a ∈ Finset.range q,
    ((q : ℂ)⁻¹ * ∑ r ∈ T, Complex.exp (2 * Real.pi * Complex.I *
        ((((a : ℝ) / (q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)))
      * ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)), dressSummand P k q D φ g s m a β

/-- The complete dressed model is the case `T = Finset.range q`. -/
lemma genWindowGauss_eq_set_range (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) :
    genWindowGauss P k q D φ g s m
      = genWindowGaussSet P k q D φ g s (Finset.range q) m := by
  rw [genWindowGauss_eq_sum_dressSummand]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [genWindowGaussSet, polyWeight, Int.cast_natCast]

/-- The swap of the two finite sums of the dressing identity, for arbitrary index sets. -/
lemma dress_sum_swap' (s T : Finset ℕ) (c : ℂ) (E : ℕ → ℕ → ℂ) (I : ℕ → ℂ) :
    (∑ a ∈ s, (c * ∑ r ∈ T, E a r) * I a) = c * ∑ r ∈ T, ∑ a ∈ s, E a r * I a := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun a _ => ?_))
  ring

/-- **The dressing identity with a truncated weight expansion** (Bourgain (7.31)). -/
theorem genWindowGaussSet_eq (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (T : Finset ℕ) (m : ℤ) :
    genWindowGaussSet P k q D φ g s T m
      = (q : ℂ)⁻¹ * ∑ r ∈ T,
          genWindow (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s (m + P.eval (r : ℤ)) := by
  have hgen : ∀ r : ℕ,
      genWindow (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s (m + P.eval (r : ℤ))
        = ∑ a ∈ Finset.range q, ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
            dressSummand (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s
              (m + P.eval (r : ℤ)) a β :=
    fun r => genWindow_eq_sum_dressSummand (P + Polynomial.C (P.eval (r : ℤ))) k q D φ g s
      (m + P.eval (r : ℤ))
  simp only [genWindowGaussSet]
  rw [Finset.sum_congr rfl (fun r _ => hgen r)]
  rw [dress_sum_swap' (Finset.range q) T ((q : ℂ)⁻¹)
    (fun a r => Complex.exp (2 * Real.pi * Complex.I *
        ((((a : ℝ) / (q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)))
    (fun a => ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
        dressSummand P k q D φ g s m a β)]
  congr 1
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun β _ => dressSummand_gauss P k q D φ g s m a (r : ℤ) β)

/-- **The truncated dressed model obeys the `ℓᵖ` maximal bound, uniformly in the truncation.** -/
theorem genWindowGaussSet_maximal_lp_of_shift (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    {C : ℝ} (hC : 0 < C)
    (hshift : ∀ (c : ℤ) (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
        (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindow (P + Polynomial.C c) k q D φ g s m‖ₑ) ^ p
          ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count) :
    ∀ (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
      (T : Finset ℕ), T.card ≤ q →
      ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
  intro q hq D hD hDq T hT g s hs
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · subst hT0
    have hz : ∀ (k : ℕ) (m : ℤ), genWindowGaussSet P k q D φ g s (∅ : Finset ℕ) m = 0 :=
      fun k m => by simp [genWindowGaussSet]
    have hzero : ∫⁻ m : ℤ,
        (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s (∅ : Finset ℕ) m‖ₑ) ^ p
          ∂Measure.count = 0 := by
      have hfun : (fun m : ℤ =>
          (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s (∅ : Finset ℕ) m‖ₑ) ^ p) = fun _ => 0 := by
        funext m
        have h1 : (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s (∅ : Finset ℕ) m‖ₑ) = 0 := by
          simp [hz, enorm_zero]
        rw [h1, ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hp)]
      rw [hfun, lintegral_zero]
    rw [hzero]; exact zero_le
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hp1 : (1:ℝ) ≤ p := le_of_lt hp
  have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
  have hcard : (T.card : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hT)
  have hqpow : (ENNReal.ofReal ((q:ℝ))⁻¹) ^ p * ((q : ℝ≥0∞)) ^ (p - 1)
      = ENNReal.ofReal ((q:ℝ))⁻¹ := by
    rw [show ((q : ℝ≥0∞)) = ENNReal.ofReal ((q:ℝ)) by rw [ENNReal.ofReal_natCast]]
    exact ofReal_inv_rpow_mul (q:ℝ) p hqR hp1
  have hle : ENNReal.ofReal ((q:ℝ))⁻¹ * (T.card : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.ofReal_inv_of_pos hqR, ENNReal.ofReal_natCast q]
    have h : (q : ℝ≥0∞)⁻¹ * (T.card : ℝ≥0∞) ≤ (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞) :=
      mul_le_mul_right hcard _
    rw [ENNReal.inv_mul_cancel (by simp [hq.ne']) (by simp)] at h
    exact h
  have hstep : ∀ m : ℤ,
      (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ)
        ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
            ∑ r ∈ T,
              (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
                (m + P.eval (r:ℤ))‖ₑ) := by
    intro m
    have hpt : ∀ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ
        ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
            ∑ r ∈ T,
              ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
                (m + P.eval (r:ℤ))‖ₑ := by
      intro k
      rw [genWindowGaussSet_eq, enorm_mul]
      rw [show ‖((q:ℂ))⁻¹‖ₑ = ENNReal.ofReal (((q:ℝ)))⁻¹ by
            rw [← ofReal_norm, norm_inv, Complex.norm_natCast]]
      exact mul_le_mul_right (enorm_sum_le _ _) _
    refine iSup_le (fun k => ?_)
    exact le_trans (hpt k) (mul_le_mul_right (Finset.sum_le_sum (s := T)
      (fun r _ => le_iSup (fun k => ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
        (m + P.eval (r:ℤ))‖ₑ) k)) _)
  have hstep2 : ∀ m : ℤ,
      (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ) ^ p
        ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
            ∑ r ∈ T,
              (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
                (m + P.eval (r:ℤ))‖ₑ) ^ p := by
    intro m
    set Z : ℕ → ℝ≥0∞ := fun r => ⨆ k : ℕ,
      ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s (m + P.eval (r:ℤ))‖ₑ
    calc (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ) ^ p
        ≤ (ENNReal.ofReal (((q:ℝ)))⁻¹ * ∑ r ∈ T, Z r) ^ p :=
          ENNReal.rpow_le_rpow (hstep m) hp0
      _ = (ENNReal.ofReal (((q:ℝ)))⁻¹) ^ p * (∑ r ∈ T, Z r) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0
      _ ≤ (ENNReal.ofReal (((q:ℝ)))⁻¹) ^ p *
            (((T.card : ℝ≥0∞)) ^ (p - 1) * ∑ r ∈ T, (Z r) ^ p) :=
          mul_le_mul_right (by
            simpa using ENNReal.rpow_sum_le_const_mul_sum_rpow T Z hp1) _
      _ ≤ (ENNReal.ofReal (((q:ℝ)))⁻¹) ^ p *
            ((((q : ℝ≥0∞)) ^ (p - 1)) * ∑ r ∈ T, (Z r) ^ p) :=
          mul_le_mul_right (mul_le_mul_left (ENNReal.rpow_le_rpow hcard (by linarith)) _) _
      _ = ((ENNReal.ofReal (((q:ℝ)))⁻¹) ^ p * ((q : ℝ≥0∞)) ^ (p - 1)) *
            ∑ r ∈ T, (Z r) ^ p := by ring
      _ = ENNReal.ofReal (((q:ℝ)))⁻¹ * ∑ r ∈ T, (Z r) ^ p := by rw [hqpow]
  calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ) ^ p ∂Measure.count
      ≤ ∫⁻ m : ℤ, ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ T,
            (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              (m + P.eval (r:ℤ))‖ₑ) ^ p ∂Measure.count :=
        lintegral_mono (fun m => hstep2 m)
    _ = ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ T,
            ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              (m + P.eval (r:ℤ))‖ₑ) ^ p ∂Measure.count := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_finset_sum]
        intro r _
        exact measurable_of_countable _
    _ = ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ T,
            ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              m‖ₑ) ^ p ∂Measure.count := by
        congr 1
        exact Finset.sum_congr rfl (fun r _ => lintegral_count_add_right
          (fun m : ℤ => (⨆ k : ℕ, ‖genWindow (P + Polynomial.C (P.eval (r:ℤ))) k q D φ g s
              m‖ₑ) ^ p) (P.eval (r:ℤ)))
    _ ≤ ENNReal.ofReal (((q:ℝ)))⁻¹ *
          ∑ r ∈ T,
            (ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
              * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count) :=
        mul_le_mul_right (Finset.sum_le_sum (s := T)
          (fun r _ => hshift (P.eval (r:ℤ)) q hq D hD hDq g s hs)) _
    _ = (ENNReal.ofReal (((q:ℝ)))⁻¹ * (T.card : ℝ≥0∞)) *
          (ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
            * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 1 * (ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
            * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count) := mul_le_mul_left hle _
    _ = ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := one_mul _

/-- **Bourgain (7.60)–(7.64), dressed-model form.**  Every *truncation* of the Gauss-weight
expansion — in particular every increment `Ω_{s,j} − Ω_{s,j−1}` of the §7.4 telescoping — obeys the
`ℓᵖ` maximal bound of Lemma 7.20, with the same constant as the complete model, as long as the
truncation has at most `q` terms. -/
theorem genWindowGaussSet_maximal_lp (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
      (T : Finset ℕ), T.card ≤ q →
      ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖genWindowGaussSet P k q D φ g s T m‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C, hC, hshift⟩ := genWindow_maximal_lp_shift_const P hP hd hp hφ hφs
  exact ⟨C, hC, genWindowGaussSet_maximal_lp_of_shift P hP hd hp hφ hφs hC hshift⟩


/-- **The block-restricted form matching §7.4.**  In the telescoping (7.63) the sup is taken over
the scales `k` of a *block* `𝒦_s` (`k ∈ 𝒦_s`), not over all `k ∈ ℕ`; the restriction is free
(monotonicity of `⨆`).  Together with `genWindowGaussSet_maximal_lp` this says: for **nested**
truncations `T' ⊆ T` the increment `Ω_T − Ω_{T'} = Ω_{T \ T'}` (the weights subtract linearly) obeys
the same bound with the constant `C` of the complete model, whenever `#T ≤ q` — i.e. Bourgain's
(7.64) for `Ω_{s,j} − Ω_{s,j−1}`. -/
theorem genWindowGaussSet_block_maximal_lp (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
      (T : Finset ℕ), T.card ≤ q →
      ∀ (K : Finset ℕ) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k ∈ K, ‖genWindowGaussSet P k q D φ g s T m‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal C * (∫⁻ y : ℝ, ‖FourierTransform.fourierInv φ y‖ₑ ∂volume)
          * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C, hC, hmain⟩ := genWindowGaussSet_maximal_lp P hP hd hp hφ hφs
  refine ⟨C, hC, fun q hq D hD hDq T hT K g s hs => ?_⟩
  refine le_trans (lintegral_mono (fun m => ENNReal.rpow_le_rpow ?_ (le_of_lt (lt_trans zero_lt_one hp)))) (hmain q hq D hD hDq T hT g s hs)
  exact iSup₂_le (fun k _ => le_iSup (fun k => ‖genWindowGaussSet P k q D φ g s T m‖ₑ) k)

end

end Work.BourgainPlan.Maximal

