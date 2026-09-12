import Submission.Notions
import Submission.LogProductMeasure
import Submission.PerRootBound
import Submission.RootProductLog
import Submission.SerreConstantNeg

/-!
# Arithmeticity assembly (C4): `ArithmeticOn (serreMeasure gSerre aSerre bSerre)`

Proves `Submission.Converse.serre_arithmetic` and
`Submission.SerreArithmetic.serre_arithmetic` (same statement).  Route:

* (C4b, x-free case) For `Q ≠ 0` with `Q.coeff 0 ≠ 0` (no zero root),
  1. bridge the real evaluation in `ArithmeticOn` to the ℂ form used by C1:
     `log|aeval x Q| = log‖aeval (x:ℂ) Q‖` for real x (isScalarTower ℤ→ℝ→ℂ
     and `‖(r:ℂ)‖ = |r|`, `Submission.PotentialDefs.norm_complex_ofReal`);
  2. `Submission.LogProductMeasure.integral_log_q_eq` (C1):
     `∫log|Q|dμ = log‖lc‖ + Σ_{z∈roots} ∫ log‖(x:ℂ)−z‖ dμ`;
  3. per-root bound (C2, all roots ≠ 0 since `Q.coeff 0 ≠ 0`):
     each `∫log‖(x:ℂ)−z‖dμ ≥ γ·log‖z‖ − serreConstant`, so
     `∫log|Q|dμ ≥ log‖lc‖ + γ·(Σ log‖z‖) − n·serreConstant` with
     `n = natDegree Q` (count roots with multiplicity: natDegree equals the
     number of aroots over ℂ);
  4. `Submission.RootProductLog.root_product_log` (C3):
     `Σ log‖z‖ = log‖Q(0)‖ − log‖lc‖`, so
     `∫log|Q|dμ ≥ (1−γ)·log‖lc‖ + γ·log‖Q(0)‖ − n·serreConstant`;
  5. `‖(c:ℤ : ℂ)‖ = |c| ≥ 1` for nonzero integers c (both `Q.leadingCoeff`
     and `Q.coeff 0` are nonzero), so both log terms ≥ 0, and
     `−n·serreConstant ≥ 0` because `serreConstant < 0` (`A3-num`); conclude
     ≥ 0.  (For constant Q the root multiset is empty: Σ = 0 and n = 0.)

* (C4a, general case) Decompose `Q = X^k·Q′` with `Q′.coeff 0 ≠ 0`
  (`k` = multiplicity of the root 0, found by repeatedly dividing by `X`
  while the constant coefficient is 0 — terminates since `Q ≠ 0`).
  The roots of `Q` are the roots of `Q′` plus `k` copies of 0, so by C1
  applied to `Q`, `Q′` and `X^k` (or directly via `aroots_mul`):
      ∫log|Q|dμ = ∫log|Q′|dμ + k·∫log|X|dμ
  (constant terms cancel: `lc(Q′) = lc(Q)`, and `∫log‖(x:ℂ)−0‖dμ =
  ∫log|x|dμ`), with `k·∫log|x|dμ ≥ 0` by A4-num
  (`serre_log_moment_pos`).  The x-free piece is ≥ 0 by (C4b).

Notes: `μ` is a probability measure supported on `[aSerre,bSerre] ⊂ (0,∞)`
(`SupportConcentration`), which makes every integrand bounded except for the
(integrable) log-singularity handled in the imported lemmas.  The multiset
`rootMultiset Q` is `(Q.map ℤ→ℂ).aroots ℂ`; `Polynomial.aroots_mul` splits
multisets of products; natDegree counts roots with multiplicity over ℂ
(`Polynomial.natDegree_eq_card_roots`-type facts).
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open AlgebraicIntegers
open scoped Real

namespace Submission.ArithmeticAssembly

open Submission.Notions
open Submission.Serre
open Submission.SerreExample
open Submission.PotentialDefs

open Submission.LogProductMeasure (rootMultiset)

/-- The real evaluation of an integer polynomial at `x` casts to the complex
evaluation at `(x : ℂ)`. -/
lemma aeval_complex_of_aeval (Q : Polynomial ℤ) (x : ℝ) :
    ((Polynomial.aeval x Q : ℝ) : ℂ) = Polynomial.aeval (x : ℂ) Q := by
  simpa [Polynomial.map_id]
    using (Polynomial.map_aeval_eq_aeval_map (R := ℤ) (S := ℝ) (T := ℤ) (U := ℂ)
      (φ := RingHom.id ℤ) (ψ := Complex.ofRealHom) (by ext n <;> simp) Q x)

/-- Bridge: `log|aeval x Q|` (real) equals `log‖aeval (x : ℂ) Q‖` (complex norm). -/
lemma real_log_aeval_eq_complex (Q : Polynomial ℤ) (x : ℝ) :
    Real.log |Polynomial.aeval x Q| = Real.log ‖Polynomial.aeval (x : ℂ) Q‖ := by
  have h := aeval_complex_of_aeval Q x
  rw [← h]
  rw [norm_complex_ofReal (Polynomial.aeval x Q)]

/-- A real integer cast into ℂ has norm `≥ 1` when the integer is nonzero. -/
lemma norm_int_complex_ge_one (c : ℤ) (hc : c ≠ 0) : (1 : ℝ) ≤ ‖(c : ℂ)‖ := by
  have h1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast (Int.one_le_abs hc)
  have hc2 : (c : ℂ) = ((c : ℝ) : ℂ) := by rfl
  rw [hc2, norm_complex_ofReal (c : ℝ)]
  exact h1

/-- The log of a nonzero integer cast to ℝ/ℂ is nonnegative. -/
lemma log_norm_int_nonneg (c : ℤ) (hc : c ≠ 0) : 0 ≤ Real.log ‖(c : ℂ)‖ := by
  exact Real.log_nonneg (norm_int_complex_ge_one c hc)

/-- Integrability of a finite sum of log-distance terms against Serre's measure. -/
lemma log_sum_integrable (m : Multiset ℂ) :
    Integrable (fun x : ℝ => (m.map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum)
      (serreMeasure gSerre aSerre bSerre) := by
  induction m using Multiset.induction_on with
  | empty => simpa using (MeasureTheory.integrable_zero ℝ (serreMeasure gSerre aSerre bSerre))
  | cons a t ih =>
      have hfun : (fun x : ℝ => ((a ::ₘ t).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) =
          (fun x : ℝ => Real.log ‖(x : ℂ) - a‖) +
            (fun x : ℝ => (t.map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) := by
        funext x
        simp [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun]
      exact (Submission.LogProductMeasure.log_dist_integrable a).add ih

/-- Integral of a finite sum of log-distance terms equals the sum of the
individual integrals (against Serre's measure). -/
lemma integral_sum_log_dist (m : Multiset ℂ) :
    (∫ x : ℝ, (m.map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum
        ∂serreMeasure gSerre aSerre bSerre) =
      (m.map (fun z : ℂ =>
        ∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have hfun : (fun x : ℝ => ((a ::ₘ t).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) =
          (fun x : ℝ => Real.log ‖(x : ℂ) - a‖) +
            (fun x : ℝ => (t.map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) := by
        funext x
        simp [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun]
      change (∫ x : ℝ, Real.log ‖(x : ℂ) - a‖ + (t.map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum
          ∂serreMeasure gSerre aSerre bSerre) = _
      rw [MeasureTheory.integral_add (Submission.LogProductMeasure.log_dist_integrable a)
        (log_sum_integrable t)]
      rw [ih]
      simp

/-- Pointwise comparison of multiset sums (multiset version of `sum_le_sum`). -/
lemma multiset_sum_le {m : Multiset ℂ} {f g : ℂ → ℝ}
    (h : ∀ z ∈ m, f z ≤ g z) : (m.map f).sum ≤ (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have h1 : f a ≤ g a := h a (by simp)
      have ih' : (t.map f).sum ≤ (t.map g).sum := ih (fun z hz => h z (by simp [hz]))
      simp [Multiset.sum_cons]
      exact add_le_add h1 ih'

/-- `Σ_z (γ·log‖z‖ − serreConstant) = γ·Σ_z log‖z‖ − card·serreConstant`. -/
lemma sum_map_mul_sub_const (m : Multiset ℂ) (γ : ℝ) :
    (m.map (fun z : ℂ => γ * Real.log ‖z‖ - serreConstant)).sum =
      γ * (m.map (fun z : ℂ => Real.log ‖z‖)).sum - (m.card : ℝ) * serreConstant := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have hcard : ((a ::ₘ t).card : ℝ) = (t.card : ℝ) + 1 := by simp
      simp [Multiset.sum_cons, ih, hcard]
      ring

/-- (C2-assembly) Summing the per-root bounds over all roots (all nonzero). -/
lemma sum_root_integral_bound (Q : Polynomial ℤ) (hz : ∀ z ∈ rootMultiset Q, z ≠ 0) :
    gSerre * ((rootMultiset Q).map (fun z : ℂ => Real.log ‖z‖)).sum -
        ((rootMultiset Q).card : ℝ) * serreConstant ≤
      ((rootMultiset Q).map (fun z : ℂ =>
        ∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre)).sum := by
  have hterm : ∀ z ∈ rootMultiset Q,
      gSerre * Real.log ‖z‖ - serreConstant ≤
        (∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre) := by
    intro z hzmem
    exact Submission.PerRootBound.per_root_bound (hz z hzmem)
  have hle : ((rootMultiset Q).map (fun z : ℂ => gSerre * Real.log ‖z‖ - serreConstant)).sum ≤
      ((rootMultiset Q).map (fun z : ℂ =>
        ∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre)).sum :=
    multiset_sum_le hterm
  have harith : ((rootMultiset Q).map (fun z : ℂ => gSerre * Real.log ‖z‖ - serreConstant)).sum =
      gSerre * ((rootMultiset Q).map (fun z : ℂ => Real.log ‖z‖)).sum -
        ((rootMultiset Q).card : ℝ) * serreConstant := sum_map_mul_sub_const (rootMultiset Q) gSerre
  simpa [harith] using hle

/-- (C4b) Arithmeticity bound for polynomials with nonzero constant term. -/
theorem arithmetic_xfree (Q : Polynomial ℤ) (hQ : Q ≠ 0) (hQ0 : Q.coeff 0 ≠ 0) :
    0 ≤ (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂serreMeasure gSerre aSerre bSerre) := by
  -- all roots of `Q` are nonzero (constant term ≠ 0)
  have hz : ∀ z ∈ rootMultiset Q, z ≠ 0 :=
    Submission.RootProductLog.rootMultiset_ne_zero Q hQ hQ0
  let cL : ℝ := Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖
  let c0L : ℝ := Real.log ‖(((Q.coeff 0 : ℤ) : ℂ))‖
  let n : ℕ := (rootMultiset Q).card
  -- C1 + exchange:  ∫ log|Q| = log‖lc‖ + Σ_z ∫ log‖(x:ℂ) − z‖
  have hid : (∫ x : ℝ, Real.log |Polynomial.aeval x Q|
        ∂serreMeasure gSerre aSerre bSerre) =
      cL + ((rootMultiset Q).map (fun z : ℂ =>
        ∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre)).sum := by
    calc
      (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂serreMeasure gSerre aSerre bSerre)
          = (∫ x : ℝ, Real.log ‖Polynomial.aeval (x : ℂ) Q‖
              ∂serreMeasure gSerre aSerre bSerre) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact real_log_aeval_eq_complex Q x
      _ = cL + (∫ x : ℝ, ((rootMultiset Q).map
              (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum
              ∂serreMeasure gSerre aSerre bSerre) := by
              exact Submission.LogProductMeasure.integral_log_q_eq Q hQ
      _ = cL + ((rootMultiset Q).map (fun z : ℂ =>
            ∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre)).sum := by
              rw [integral_sum_log_dist]
  -- per-root bounds summed over the (nonzero) roots
  have hsum := sum_root_integral_bound Q hz
  -- C3: Σ_z log‖z‖ = log‖Q(0)‖ − log‖lc‖
  have hc3 := Submission.RootProductLog.root_product_log hQ hQ0
  have hb : cL + (gSerre * (c0L - cL) - (n : ℝ) * serreConstant) ≤
      (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂serreMeasure gSerre aSerre bSerre) := by
    have hb0 : cL + (gSerre * ((rootMultiset Q).map (fun z : ℂ => Real.log ‖z‖)).sum -
        (n : ℝ) * serreConstant) ≤ (∫ x : ℝ, Real.log |Polynomial.aeval x Q|
          ∂serreMeasure gSerre aSerre bSerre) := by
      rw [hid]
      linarith
    rw [hc3] at hb0
    exact hb0
  -- nonnegativity of the lower bound expression
  have hcL : 0 ≤ cL := by
    exact log_norm_int_nonneg (Q.leadingCoeff) (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hc0L : 0 ≤ c0L := log_norm_int_nonneg (Q.coeff 0) hQ0
  have hmain : 0 ≤ (1 - gSerre) * cL + gSerre * c0L := by
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr gSerre_le_one) hcL)
      (mul_nonneg (le_of_lt gSerre_pos) hc0L)
  have hneg : 0 ≤ -((n : ℝ) * serreConstant) := by
    have hs : serreConstant ≤ 0 := le_of_lt Submission.SerreConstantNeg.serreConstant_neg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hs]
  have hA : cL + (gSerre * (c0L - cL) - (n : ℝ) * serreConstant) =
      ((1 - gSerre) * cL + gSerre * c0L) + (-((n : ℝ) * serreConstant)) := by
    ring
  have hnonneg : 0 ≤ cL + (gSerre * (c0L - cL) - (n : ℝ) * serreConstant) := by
    rw [hA]
    exact add_nonneg hmain hneg
  linarith

/-- Any nonzero polynomial is `X^k · Q'` for a `Q'` with nonzero constant term. -/
lemma exists_eq_X_pow_mul (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    ∃ k : ℕ, ∃ Q' : Polynomial ℤ, Q = Polynomial.X ^ k * Q' ∧ Q'.coeff 0 ≠ 0 := by
  have hex : ∃ i : ℕ, Q.coeff i ≠ 0 := by
    by_contra h
    apply hQ
    apply Polynomial.ext
    intro i
    exact by_contra (fun hci => h ⟨i, hci⟩)
  let k := Nat.find hex
  have hk0 : Q.coeff k ≠ 0 := Nat.find_spec hex
  have hkmin : ∀ d : ℕ, d < k → Q.coeff d = 0 := by
    intro d hd
    by_contra hd0
    exact (Nat.find_min hex hd) hd0
  have hdiv : Polynomial.X ^ k ∣ Q := (Polynomial.X_pow_dvd_iff).mpr hkmin
  rcases hdiv with ⟨Q', hQeq⟩
  refine ⟨k, Q', hQeq, ?_⟩
  have hck : (Polynomial.X ^ k * Q').coeff k ≠ 0 := by
    rw [← hQeq]
    exact hk0
  have hcoeff : (Polynomial.X ^ k * Q').coeff k = Q'.coeff 0 := by
    rw [Polynomial.coeff_X_pow_mul' (p := Q') k k]
    simp
  rwa [hcoeff] at hck

/-- Real log of the absolute value of `X^k·Q'` at a point where neither the
point nor the value of `Q'` vanishes. -/
lemma log_abs_X_pow_mul_aeval (Q' : Polynomial ℤ) (k : ℕ) (x : ℝ) (hx0 : x ≠ 0)
    (hxq : Polynomial.aeval x Q' ≠ 0) :
    Real.log |Polynomial.aeval x (Polynomial.X ^ k * Q')| =
      (k : ℝ) * Real.log |x| + Real.log |Polynomial.aeval x Q'| := by
  have haeval : Polynomial.aeval x (Polynomial.X ^ k * Q') =
      x ^ k * Polynomial.aeval x Q' := by
    simp
  rw [haeval]
  have hx' : |x| ^ k ≠ 0 := pow_ne_zero k (abs_ne_zero.mpr hx0)
  have hr' : |Polynomial.aeval x Q'| ≠ 0 := abs_ne_zero.mpr hxq
  calc
    Real.log |x ^ k * Polynomial.aeval x Q'|
        = Real.log (|x ^ k| * |Polynomial.aeval x Q'|) := by rw [abs_mul]
    _ = Real.log (|x| ^ k * |Polynomial.aeval x Q'|) := by rw [abs_pow]
    _ = Real.log (|x| ^ k) + Real.log |Polynomial.aeval x Q'| := by
          rw [Real.log_mul hx' hr']
    _ = (k : ℝ) * Real.log |x| + Real.log |Polynomial.aeval x Q'| := by
          rw [Real.log_pow]

/-- (C4) Full arithmeticity of Serre's measure. -/
theorem arithmetic (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    0 ≤ (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂serreMeasure gSerre aSerre bSerre) := by
  rcases exists_eq_X_pow_mul Q hQ with ⟨k, Q', hQeq, hQ'0⟩
  have hQ' : Q' ≠ 0 := by
    intro hQ'0
    apply hQ
    rw [hQeq, hQ'0, mul_zero]
  -- pointwise log-product identity on the complement of `realRootSet Q' ∪ {0}`
  have hpoint : ∀ x : ℝ, x ≠ 0 → Polynomial.aeval x Q' ≠ 0 →
      Real.log |Polynomial.aeval x Q| =
        (k : ℝ) * Real.log |x| + Real.log |Polynomial.aeval x Q'| := by
    intro x hx0 hxq
    rw [hQeq]
    exact log_abs_X_pow_mul_aeval Q' k x hx0 hxq
  have hae : (fun x : ℝ => Real.log |Polynomial.aeval x Q|) =ᵐ[serreMeasure gSerre aSerre bSerre]
      (fun x : ℝ => (k : ℝ) * Real.log |x| + Real.log |Polynomial.aeval x Q'|) := by
    refine (MeasureTheory.ae_iff (p := fun x : ℝ =>
      Real.log |Polynomial.aeval x Q| =
        (k : ℝ) * Real.log |x| + Real.log |Polynomial.aeval x Q'|)).mpr ?_
    refine measure_mono_null ?_
      (measure_union_null
        (Submission.LogProductMeasure.measure_realRootSet_zero Q' hQ')
        (Submission.LogProductMeasure.serre_atom_free (0 : ℝ)))
    intro x hx
    by_contra hxS
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hxS
      right
      simpa [hx0]
    have hxq : Polynomial.aeval x Q' ≠ 0 := by
      intro hq0
      apply hxS
      left
      change Polynomial.aeval (x : ℂ) Q' = 0
      rw [← aeval_complex_of_aeval Q' x, hq0]
      simp
    exact hx (hpoint x hx0 hxq)
  -- integrability of the two summands
  have hint_logx : Integrable (fun x : ℝ => Real.log |x|)
      (serreMeasure gSerre aSerre bSerre) := by
    have h0 : (fun x : ℝ => Real.log |x|) =
        (fun x : ℝ => Real.log ‖(x : ℂ) - (0 : ℂ)‖) := by
      funext x
      rw [sub_zero, ← norm_complex_ofReal x]
    rw [h0]
    exact Submission.LogProductMeasure.log_dist_integrable 0
  have hint_cf : Integrable (fun x : ℝ => (k : ℝ) * Real.log |x|)
      (serreMeasure gSerre aSerre bSerre) := hint_logx.const_mul (k : ℝ)
  have hint_logQ' : Integrable (fun x : ℝ => Real.log |Polynomial.aeval x Q'|)
      (serreMeasure gSerre aSerre bSerre) := by
    have hpe : (fun x : ℝ => Real.log |Polynomial.aeval x Q'|) =
        (fun x : ℝ => Real.log ‖Polynomial.aeval (x : ℂ) Q'‖) := by
      funext x
      exact real_log_aeval_eq_complex Q' x
    rw [hpe]
    have hS : Integrable (fun x : ℝ => ((rootMultiset Q').map
        (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum)
        (serreMeasure gSerre aSerre bSerre) :=
      Submission.LogProductMeasure.sum_log_dist_integrable Q'
    let c : ℝ := Real.log ‖(((Q'.leadingCoeff : ℤ) : ℂ))‖
    have hcS : Integrable (fun x : ℝ => c + ((rootMultiset Q').map
        (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum)
        (serreMeasure gSerre aSerre bSerre) := (integrable_const c).add hS
    have hae' : (fun x : ℝ => c + ((rootMultiset Q').map
        (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) =ᵐ[serreMeasure gSerre aSerre bSerre]
        (fun x : ℝ => Real.log ‖Polynomial.aeval (x : ℂ) Q'‖) := by
      simpa [c] using (Submission.LogProductMeasure.ae_log_q_eq_sum Q' hQ').symm
    exact hcS.congr hae'
  -- integral splitting
  have hid : (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂serreMeasure gSerre aSerre bSerre) =
      (k : ℝ) * (∫ x : ℝ, Real.log |x| ∂serreMeasure gSerre aSerre bSerre) +
        (∫ x : ℝ, Real.log |Polynomial.aeval x Q'| ∂serreMeasure gSerre aSerre bSerre) := by
    calc
      (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂serreMeasure gSerre aSerre bSerre)
          = (∫ x : ℝ, ((k : ℝ) * Real.log |x| + Real.log |Polynomial.aeval x Q'|)
              ∂serreMeasure gSerre aSerre bSerre) := by
              exact MeasureTheory.integral_congr_ae hae
      _ = (k : ℝ) * (∫ x : ℝ, Real.log |x| ∂serreMeasure gSerre aSerre bSerre) +
          (∫ x : ℝ, Real.log |Polynomial.aeval x Q'| ∂serreMeasure gSerre aSerre bSerre) := by
              rw [MeasureTheory.integral_add hint_cf hint_logQ']
              rw [MeasureTheory.integral_const_mul]
  -- both pieces are nonnegative
  have h1 : 0 ≤ (∫ x : ℝ, Real.log |x| ∂serreMeasure gSerre aSerre bSerre) := by
    have hpe : (fun x : ℝ => Real.log |x|) = (fun x : ℝ => Real.log ‖(x : ℂ)‖) := by
      funext x
      rw [← norm_complex_ofReal x]
    rw [hpe]
    exact Submission.PerRootBound.zero_root_bound
  have h2 : 0 ≤ (∫ x : ℝ, Real.log |Polynomial.aeval x Q'|
      ∂serreMeasure gSerre aSerre bSerre) := arithmetic_xfree Q' hQ' hQ'0
  have hk : 0 ≤ (k : ℝ) * (∫ x : ℝ, Real.log |x| ∂serreMeasure gSerre aSerre bSerre) :=
    mul_nonneg (Nat.cast_nonneg k) h1
  nlinarith

/-- Arithmeticity in the `ArithmeticOn` form (the goal of `SerreArithmetic`). -/
theorem serre_arithmetic :
    ArithmeticOn (serreMeasure gSerre aSerre bSerre) := by
  intro Q hQ
  exact arithmetic Q hQ

end Submission.ArithmeticAssembly
