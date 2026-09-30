import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.mahlerMeasure_minpoly_le_logHeight1
import Submission.Work.BW.isPrimitiveRoot_order_lt
import Submission.Work.BW.blanksby_montgomery

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker-Wüstholz drive). Route design: BW = Baker-Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# lehmer_bound - BW L5 (p. 28-29), 3-6k lines, medium risk

**Claim.** Take `β ≠ 0` and `ℓ ≠ 0` with `exp ℓ = φβ`. Then `1 < c'·max(h(β), |ℓ|)` with
`c' = 60 d log(6d)`. Since `h'` is BW's modified height, this is equivalent to `h'(β) < c' h̄(β)`.

**Proof (BW).** Split into three cases.
* **`β` not an algebraic integer.** The leading coefficient is `≥ 2`, so `h(β) ≥ log 2`.
* **`β` a root of unity of order `k`.** Every logarithm of `φβ` has `|ℓ| ≥ 2π/k`, including
  `ℓ ∈ 2πiℤ` when `β = 1`, and `φ(k) ≤ d`.
  * The elementary bound `φ(k) ≥ k/(log₂k + 1)` suffices: `∏_{p|k}(1-1/p) ≥ 1/(ω+1)` and
    `ω ≤ log₂ k`.
* **`β` an algebraic integer, not a root of unity, of degree `δ ≤ d`.**
  * Then `h(β) = (d/δ) log M(β) ≥ log M(β)`.
  * Blanksby-Montgomery gives `M > 1 + 1/(52δ log 6δ)`.

**Only this much is needed downstream.** `kummer_reduction` takes the constant `c'` as a
hypothesis, and `bw_independent` then needs `log(c'^n n!) < n·X(n,d)`. That holds with large
room for **any** `c' ≤ 10⁸·d·log(6d)`. So instead of Blanksby-Montgomery (Fourier analysis),
use an elementary Dobrowolski-type bound: Dobrowolski 1979, or the Cantor-Straus
confluent-Vandermonde proof, or Voutier's explicit version. A bound of the form
`log M(β) ≥ 1/(K δ log 6δ)` with `K ≤ 10⁸` suffices. If you change the constant, restate this
lemma with it.

**Assets.**
* Mathlib `MahlerMeasure` (in `NumberTheory/MahlerMeasure.lean`):
  `pow_eq_one_of_mahlerMeasure_eq_one` (Kronecker).
* `NumberField.Embeddings` also has Kronecker.
* A bridge `logHeight₁ β = (d/δ) log M(minpoly)` is needed and is not in Mathlib.

**Do not** use a `1/δ²`-quality bound: it fails for `d ≳ 10¹⁰` (see DESIGN §5).
-/

/-
This file proves `Work.BW.lehmer_bound` from three auxiliary statements proved in sibling nodes:
* `Work.BW.blanksby_montgomery` (Blanksby-Montgomery, Acta Arith. 18 (1971), Theorem 1);
* `Work.BW.mahlerMeasure_minpoly_le_logHeight1` (the Mahler-measure/height bridge);
* `Work.BW.isPrimitiveRoot_order_lt` (the order of a root of unity vs. the degree).
All three are imported (and proved).  The file itself reduces `Work.BW.lehmer_bound` to them by a
three-way case split on `β` (root of unity / algebraic integer / not an algebraic integer).
-/

namespace Work.BW

open NumberField

/-! ## Auxiliary lemmas: the archimedean part of the height -/

/-- The archimedean part of the relative height is the sum over the complex embeddings:
`∑_{v | ∞} mult_v · log⁺(v x) = ∑_{φ : K →+* ℂ} log⁺ ‖φ x‖`. -/
theorem sum_posLog_embeddings_eq {K : Type*} [Field K] [NumberField K] (x : K) :
    ∑ φ : K →+* ℂ, Real.posLog ‖φ x‖ =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v x) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      Real.posLog ‖φ x‖ = Real.posLog (w x) := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    rw [← hφ.2]
    rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_const, InfinitePlace.card_filter_mk_eq w, nsmul_eq_mul]

/-- The sum of `log⁺ ‖φ x‖` over the complex embeddings is at most the relative height. -/
theorem sum_posLog_embeddings_le_logHeight1 {K : Type*} [Field K] [NumberField K] (x : K) :
    ∑ φ : K →+* ℂ, Real.posLog ‖φ x‖ ≤ Height.logHeight₁ x := by
  rw [sum_posLog_embeddings_eq x, NumberField.logHeight₁_eq]
  exact le_add_of_nonneg_right (finsum_nonneg fun v => Real.posLog_nonneg)

/-- The number of complex embeddings of a number field is its degree. -/
theorem card_embeddings (K : Type*) [Field K] [NumberField K] :
    Fintype.card (K →+* ℂ) = Module.finrank ℚ K :=
  NumberField.Embeddings.card K ℂ

/-- A rational integer `m` of modulus at least `2`, viewed in a number field of degree `d`,
has relative height at least `log 2`. -/
theorem log_two_le_logHeight1_intCast {K : Type*} [Field K] [NumberField K] (m : ℤ)
    (hm : 2 ≤ |m|) : Real.log 2 ≤ Height.logHeight₁ (m : K) := by
  classical
  have h1 := sum_posLog_embeddings_le_logHeight1 (K := K) (m : K)
  have h2 : ∀ φ : K →+* ℂ, Real.posLog ‖φ (m : K)‖ = Real.posLog |(m : ℝ)| := by
    intro φ
    rw [map_intCast, Complex.norm_intCast]
  rw [Finset.sum_congr rfl fun φ _ => h2 φ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_embeddings] at h1
  have hm' : (2 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm
  have hpos : Real.posLog |(m : ℝ)| = Real.log |(m : ℝ)| :=
    Real.posLog_eq_log (by simpa using (le_trans (by norm_num : (1:ℝ) ≤ 2) hm'))
  rw [hpos] at h1
  have hlog2 : Real.log 2 ≤ Real.log |(m : ℝ)| := Real.log_le_log (by norm_num) hm'
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  nlinarith [h1, hlog2, hd, Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]

/-- `1 ≤ [K : ℚ]` as a real number. -/
theorem one_le_finrank {K : Type*} [Field K] [NumberField K] :
    (1:ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
  exact_mod_cast (show 1 ≤ Module.finrank ℚ K from Module.finrank_pos (R := ℚ) (M := K))

/-- `log x ≥ 1 - 1/x` for `x > 0`. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

/-! ## The minimal polynomial of an algebraic integer has degree at most `[K : ℚ]` -/

theorem natDegree_minpoly_int_le_finrank {K : Type*} [Field K] [NumberField K] (β : K)
    (hint : IsIntegral ℤ β) :
    (minpoly ℤ β).natDegree ≤ Module.finrank ℚ K := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (S := K) ℚ hint
  rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int (minpoly ℤ β), ← h]
  exact minpoly.natDegree_le β

/-! ## The case `β` not an algebraic integer -/

/-- If `β` is not an algebraic integer then its relative height is at least `log 2`. -/
theorem log_two_le_logHeight1_of_not_isIntegral {K : Type*} [Field K] [NumberField K] (β : K)
    (hint : ¬ IsIntegral ℤ β) : Real.log 2 ≤ Height.logHeight₁ β := by
  obtain ⟨n, hn0, hnle, hnint⟩ := NumberField.exists_nat_le_mulHeight₁ β
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hint (by simpa using hnint)
  have hn2 : 2 ≤ n := by omega
  have h : Height.logHeight₁ β = Real.log (Height.mulHeight₁ β) := rfl
  rw [h]
  exact Real.log_le_log (by norm_num)
    (le_trans (by exact_mod_cast hn2 : (2:ℝ) ≤ (n:ℝ)) hnle)

/-! ## The case `β` is a root of unity -/

/-- If `β` is a primitive `n`-th root of unity then every logarithm of `φ β` has modulus
at least `2π/n`. -/
theorem two_pi_div_le_norm_of_isPrimitiveRoot {K : Type*} [Field K] (φ : K →+* ℂ) (β : K)
    (ℓ : ℂ) (hℓ : Complex.exp ℓ = φ β) (hℓ0 : ℓ ≠ 0) (n : ℕ) (hn : 0 < n)
    (hprim : IsPrimitiveRoot β n) : (2 * Real.pi : ℝ) / n ≤ ‖ℓ‖ := by
  have hpoweq : (φ β) ^ n = 1 := by
    rw [← map_pow, hprim.pow_eq_one, map_one]
  have hexp : Complex.exp (ℓ * (n : ℂ)) = 1 := by
    rw [mul_comm ℓ (n : ℂ), Complex.exp_nat_mul, hℓ, hpoweq]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at hm
    rcases mul_eq_zero.mp hm with h | h
    · exact hℓ0 h
    · exact hnne h
  have hnrm : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  have hnorm : ‖ℓ‖ * (n : ℝ) = |(m : ℝ)| * (2 * Real.pi) := by
    have h1 : ‖ℓ * (n : ℂ)‖ = ‖(m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ := by rw [hm]
    rw [norm_mul, Complex.norm_natCast, norm_mul, Complex.norm_intCast] at h1
    rw [hnrm] at h1
    exact h1
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have hpos : (0:ℝ) < |(m : ℝ)| := by rw [abs_pos]; exact_mod_cast hm0
    exact_mod_cast hpos
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  nlinarith [Real.pi_pos]

/-! ## Algebraic integers that are not roots of unity (Blanksby–Montgomery) -/

/-- For `β ≠ 0` an algebraic integer that is not a root of unity,
`1 < 60 d log(6d) · logHeight₁ β`, `d = [K : ℚ]`. -/
theorem one_lt_sixty_mul_logHeight1_of_not_rootOfUnity {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (β : K) (hβ : β ≠ 0) (hint : IsIntegral ℤ β)
    (hnot : ∀ k : ℕ, 0 < k → β ^ k ≠ 1) :
    1 < 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ)) *
      Height.logHeight₁ β := by
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hddef
  set n : ℝ := ((minpoly ℤ β).natDegree : ℝ) with hndef
  rcases Nat.lt_or_ge (minpoly ℤ β).natDegree 2 with hnlt | hnge
  · -- degree `1`: `β` is a rational integer of modulus at least `2`
    have hdeg1 : (minpoly ℤ β).natDegree = 1 := by
      have h1 : (minpoly ℤ β).natDegree ≤ 1 := by omega
      have h2 : 1 ≤ (minpoly ℤ β).natDegree := by
        have h := minpoly.natDegree_pos hint
        omega
      exact le_antisymm h1 h2
    have hmonic : (minpoly ℤ β).Monic := minpoly.monic hint
    have hX : minpoly ℤ β = Polynomial.X + Polynomial.C ((minpoly ℤ β).coeff 0) :=
      hmonic.eq_X_add_C hdeg1
    have haev := minpoly.aeval ℤ β
    rw [hX] at haev
    simp only [map_add] at haev
    have hβeq : β = ((-(minpoly ℤ β).coeff 0 : ℤ) : K) := by
      simpa using eq_neg_of_add_eq_zero_left haev
    have hm0 : (-(minpoly ℤ β).coeff 0 : ℤ) ≠ 0 := by
      intro h
      exact hβ (by rw [hβeq, h, Int.cast_zero])
    have hm1 : (-(minpoly ℤ β).coeff 0 : ℤ) ≠ 1 := by
      intro h
      exact hnot 1 one_pos (by rw [hβeq, h]; norm_num)
    have hmneg1 : (-(minpoly ℤ β).coeff 0 : ℤ) ≠ -1 := by
      intro h
      exact hnot 2 (by norm_num) (by rw [hβeq, h]; norm_num)
    have hm2 : 2 ≤ |(-(minpoly ℤ β).coeff 0 : ℤ)| := by
      rcases lt_trichotomy (-(minpoly ℤ β).coeff 0 : ℤ) 0 with h | h | h
      · rw [abs_of_neg h]; omega
      · omega
      · rw [abs_of_pos h]; omega
    have h2 := log_two_le_logHeight1_intCast (K := K) (-(minpoly ℤ β).coeff 0) hm2
    rw [hβeq]
    have hd1 : (1:ℝ) ≤ d := by
      rw [hddef]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
      have h := one_sub_inv_le_log (show (0:ℝ) < 2 by norm_num)
      norm_num at h
      linarith
    have hlog6 : (5/6 : ℝ) ≤ Real.log 6 := by
      have h := one_sub_inv_le_log (show (0:ℝ) < 6 by norm_num)
      norm_num at h
      linarith
    have hlog6d : Real.log 6 ≤ Real.log (6 * d) := Real.log_le_log (by norm_num) (by nlinarith)
    have hlog6d' : (5/6 : ℝ) ≤ Real.log (6 * d) := le_trans hlog6 hlog6d
    have hH : (1/2 : ℝ) ≤ Height.logHeight₁ ((-(minpoly ℤ β).coeff 0 : ℤ) : K) := le_trans hlog2 h2
    have hprod : 60 * (1:ℝ) * (5/6) * (1/2)
        ≤ 60 * d * Real.log (6 * d) * Height.logHeight₁ ((-(minpoly ℤ β).coeff 0 : ℤ) : K) := by
      gcongr
    linarith [hprod]
  · -- degree at least `2`: Blanksby–Montgomery
    have hn2 : 2 ≤ (minpoly ℤ β).natDegree := hnge
    have hn2' : (2:ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn2
    have hnpos : 0 < n := by linarith
    have hnle : n ≤ d := by
      rw [hddef, hndef]
      exact_mod_cast natDegree_minpoly_int_le_finrank β hint
    have hd1 : (1:ℝ) ≤ d := by
      rw [hddef]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    have hlog6dpos : 0 < Real.log (6 * d) := Real.log_pos (by nlinarith)
    have hlog6npos : 0 < Real.log (6 * n) := Real.log_pos (by nlinarith)
    have hlogle : Real.log (6 * n) ≤ Real.log (6 * d) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    set x : ℝ := 1 / (52 * n * Real.log (6 * n)) with hxdef
    have hxpos : 0 < x := by rw [hxdef]; positivity
    -- the root condition for `φ β`
    have hroot : (Polynomial.map (Int.castRingHom ℂ) (minpoly ℤ β)).IsRoot (φ β) := by
      have hae : (Polynomial.aeval β) (minpoly ℤ β) = 0 := minpoly.aeval ℤ β
      have hroot1 : (Polynomial.map (algebraMap ℤ K) (minpoly ℤ β)).IsRoot β := by
        rw [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map]
        rw [← Polynomial.aeval_def]
        exact hae
      have hroot2 : (Polynomial.map φ (Polynomial.map (algebraMap ℤ K) (minpoly ℤ β))).IsRoot (φ β) :=
        hroot1.map (f := φ)
      rwa [Polynomial.map_map, show φ.comp (algebraMap ℤ K) = Int.castRingHom ℂ from
        RingHom.ext fun z => by simp] at hroot2
    -- Blanksby–Montgomery: `M > 1 + 1/(52 n log 6n)`
    have hBM : 1 + x < ((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure := by
      by_contra hcon
      rw [not_lt] at hcon
      have hcond : (Polynomial.map (Int.castRingHom ℂ) (minpoly ℤ β)).mahlerMeasure ≤
          1 + 1 / (52 * ((minpoly ℤ β).natDegree : ℝ) *
            Real.log (6 * ((minpoly ℤ β).natDegree : ℝ))) := by
        simpa [hxdef, hndef] using hcon
      obtain ⟨k, hk, hαk⟩ := blanksby_montgomery (minpoly ℤ β) (minpoly.monic hint)
        (minpoly.irreducible hint) hn2 hcond hroot
      exact hnot k hk (φ.injective (by rw [map_pow, hαk, map_one]))
    -- the height bridge
    have hbridge := mahlerMeasure_minpoly_le_logHeight1 β hint
    have hlogh : x * (1 - x) ≤ Height.logHeight₁ β := by
      have hlt : Real.log (1 + x) <
          Real.log ((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure :=
        Real.log_lt_log (by linarith) hBM
      have hlogx : x * (1 - x) ≤ Real.log (1 + x) := by
        have hx1' : 0 < 1 + x := by linarith
        have hlog : x / (1 + x) ≤ Real.log (1 + x) := by
          have h := Real.log_le_sub_one_of_pos (show 0 < (1 + x)⁻¹ by positivity)
          rw [Real.log_inv] at h
          have h2 : x / (1 + x) = 1 - (1 + x)⁻¹ := by
            field_simp
            ring
          linarith
        have h2 : x * (1 - x) ≤ x / (1 + x) := by
          rw [le_div_iff₀ hx1']
          nlinarith [sq_nonneg x, mul_nonneg hxpos.le hxpos.le,
            mul_nonneg (mul_nonneg hxpos.le hxpos.le) hxpos.le]
        linarith
      linarith
    -- numerical comparison
    have hlog12 : (11/12 : ℝ) ≤ Real.log 12 := by
      have h := one_sub_inv_le_log (show (0:ℝ) < 12 by norm_num)
      norm_num at h
      linarith
    have hx95 : x ≤ 1 / 95 := by
      rw [hxdef]
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 95)
      have hlog : (11/12 : ℝ) ≤ Real.log (6 * n) :=
        le_trans hlog12 (Real.log_le_log (by norm_num) (by nlinarith))
      have hml : (2:ℝ) * (11/12) ≤ n * Real.log (6 * n) :=
        mul_le_mul hn2' hlog (by norm_num) (by linarith)
      nlinarith
    have hA1 : 1 ≤ (d / n) * (Real.log (6 * d) / Real.log (6 * n)) := by
      have h1 : 1 ≤ d / n := (one_le_div hnpos).mpr hnle
      have h2 : 1 ≤ Real.log (6 * d) / Real.log (6 * n) := (one_le_div hlog6npos).mpr hlogle
      have h3 := mul_le_mul h1 h2 zero_le_one (by positivity : (0:ℝ) ≤ d / n)
      linarith
    have hAx : 60 * d * Real.log (6 * d) * (x * (1 - x))
        = (60/52) * ((d / n) * (Real.log (6 * d) / Real.log (6 * n))) * (1 - x) := by
      rw [hxdef]
      field_simp
    have hkey : 1 < 60 * d * Real.log (6 * d) * (x * (1 - x)) := by
      rw [hAx]
      nlinarith [hA1, hx95, hxpos]
    have hfin : 60 * d * Real.log (6 * d) * (x * (1 - x))
        ≤ 60 * d * Real.log (6 * d) * Height.logHeight₁ β :=
      mul_le_mul_of_nonneg_left hlogh (by positivity)
    exact lt_of_lt_of_le hkey hfin

/-! ## Roots of unity -/

/-- If `β ≠ 0` is a root of unity then `1 < 60 d log(6d) · max (h β) ‖ℓ‖` for every logarithm
`ℓ ≠ 0` of `φ β`. -/
theorem one_lt_sixty_mul_of_rootOfUnity {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (β : K) (ℓ : ℂ) (hℓ : Complex.exp ℓ = φ β) (hℓ0 : ℓ ≠ 0)
    (hru : ∃ k : ℕ, 0 < k ∧ β ^ k = 1) :
    1 < 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ)) *
      max (Height.logHeight₁ β) ‖ℓ‖ := by
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hddef
  obtain ⟨k, hk, hβk⟩ := hru
  have hk0 : 0 < orderOf β := by
    have hdvd : orderOf β ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hβk
    rcases Nat.eq_zero_or_pos (orderOf β) with h | h
    · rw [h] at hdvd
      have : k = 0 := Nat.eq_zero_of_zero_dvd hdvd
      omega
    · exact h
  have hprim : IsPrimitiveRoot β (orderOf β) := IsPrimitiveRoot.orderOf β
  have hℓb := two_pi_div_le_norm_of_isPrimitiveRoot φ β ℓ hℓ hℓ0 (orderOf β) hk0 hprim
  have hkb := isPrimitiveRoot_order_lt β (orderOf β) hk0 hprim
  have hkb' : ((orderOf β : ℕ) : ℝ) < 120 * Real.pi * d * Real.log (6 * d) := by
    rw [hddef] at *
    exact hkb
  have hdpos : 0 < d := by
    rw [hddef]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hlogpos : 0 < Real.log (6 * d) := by
    apply Real.log_pos
    rw [hddef]
    have := one_le_finrank (K := K)
    linarith
  have hcpos : 0 < 60 * d * Real.log (6 * d) := by positivity
  have hk0' : (0:ℝ) < (orderOf β : ℕ) := by exact_mod_cast hk0
  have h2 : 1 / (60 * d * Real.log (6 * d)) < 2 * Real.pi / (orderOf β : ℕ) := by
    rw [div_lt_div_iff₀ hcpos hk0']
    nlinarith [hkb', Real.pi_pos]
  have h1 : (1:ℝ) = 60 * d * Real.log (6 * d) * (1 / (60 * d * Real.log (6 * d))) := by
    rw [mul_one_div, div_self (ne_of_gt hcpos)]
  calc 1 = 60 * d * Real.log (6 * d) * (1 / (60 * d * Real.log (6 * d))) := h1
    _ < 60 * d * Real.log (6 * d) * (2 * Real.pi / (orderOf β : ℕ)) :=
        mul_lt_mul_of_pos_left h2 hcpos
    _ ≤ 60 * d * Real.log (6 * d) * ‖ℓ‖ := mul_le_mul_of_nonneg_left hℓb hcpos.le
    _ ≤ 60 * d * Real.log (6 * d) * max (Height.logHeight₁ β) ‖ℓ‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hcpos.le

/-- BW L5 in the form used: if `ℓ ≠ 0` is a logarithm of `φ β` then
`1 < c' · max(h(β), |ℓ|)` with `c' = 60 d log(6d)` (Blanksby–Montgomery; roots of unity by
`|ℓ| ≥ 2π/k`). Equivalent to `h'(β) < c' h̄(β)`. -/
theorem lehmer_bound {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (β : K)
    (hβ : β ≠ 0) (ℓ : ℂ) (hℓ : Complex.exp ℓ = φ β) (hℓ0 : ℓ ≠ 0) :
    1 < 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * Module.finrank ℚ K) *
      max (Height.logHeight₁ β) ‖ℓ‖ := by
  have cnonneg : (0:ℝ) ≤ 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ)) := by
    refine mul_nonneg (by positivity) ?_
    apply Real.log_nonneg
    linarith [one_le_finrank (K := K)]
  by_cases hru : ∃ k : ℕ, 0 < k ∧ β ^ k = 1
  · exact one_lt_sixty_mul_of_rootOfUnity φ β ℓ hℓ hℓ0 hru
  · simp only [not_exists, not_and] at hru
    by_cases hint : IsIntegral ℤ β
    · have h := one_lt_sixty_mul_logHeight1_of_not_rootOfUnity φ β hβ hint hru
      have hmax : Height.logHeight₁ β ≤ max (Height.logHeight₁ β) ‖ℓ‖ := le_max_left _ _
      have := mul_le_mul_of_nonneg_left hmax cnonneg
      linarith
    · have h2 := log_two_le_logHeight1_of_not_isIntegral β hint
      have hd1 : (1:ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
      have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
        have h := one_sub_inv_le_log (show (0:ℝ) < 2 by norm_num)
        norm_num at h
        linarith
      have hlog6 : (5/6 : ℝ) ≤ Real.log 6 := by
        have h := one_sub_inv_le_log (show (0:ℝ) < 6 by norm_num)
        norm_num at h
        linarith
      have hlog6d : Real.log 6 ≤ Real.log (6 * (Module.finrank ℚ K : ℝ)) :=
        Real.log_le_log (by norm_num) (by nlinarith)
      have hmax : Real.log 2 ≤ max (Height.logHeight₁ β) ‖ℓ‖ := le_trans h2 (le_max_left _ _)
      have hkey : 1 < 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ))
          * Real.log 2 := by
        nlinarith [hd1, hlog6, hlog6d, hlog2]
      have := mul_le_mul_of_nonneg_left hmax cnonneg
      linarith

end Work.BW
