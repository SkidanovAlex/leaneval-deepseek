import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 0. Elementary complex-norm and divisor helpers -/

/-- `‖(r : ℂ)‖ = |r|` for a real `r`. -/
private lemma norm_ofReal_c (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (|r| ^ 2) := by
        congr 1
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
        ring
    _ = |r| := Real.sqrt_sq (abs_nonneg r)

/-- `‖(z : ℂ)‖ = |z|` for an integer `z`. -/
private lemma norm_intCast_c (z : ℤ) : ‖((z : ℤ) : ℂ)‖ = |(z : ℝ)| := by
  have hz : ((z : ℤ) : ℂ) = ((z : ℝ) : ℂ) := by push_cast; ring
  rw [hz, norm_ofReal_c]

/-- `|μ(n)| ≤ 1` for the Möbius function, as a real number. -/
private lemma abs_moebius_cast_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  have h2 : (((|ArithmeticFunction.moebius n| : ℤ)) : ℝ) =
      |(((ArithmeticFunction.moebius n : ℤ)) : ℝ)| := Int.cast_abs
  rw [← h2]
  exact_mod_cast h

/-- `τ(|z|²) = #(divisors of |z|²)`, as a real number. -/
private def tauN (z : GaussianInt) : ℝ := (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)

private lemma tauN_nonneg (z : GaussianInt) : 0 ≤ tauN z := Nat.cast_nonneg _

/-- `|γ(n; C)| = |Σ_{d | n, d ≤ C} μ(d)| ≤ τ(n)`. -/
private lemma abs_gammaTrunc_le (Cc : ℝ) (n : ℕ) :
    |Work.FIPlan.gammaTrunc Cc n| ≤ ((n.divisors.card : ℕ) : ℝ) := by
  rw [Work.FIPlan.gammaTrunc]
  calc |∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)|
      ≤ ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc), (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => abs_moebius_cast_le_one d)
    _ = ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((n.divisors.card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- `‖radBeta z‖ ≤ τ(|z|²)`. -/
private lemma norm_radBeta_le (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z : GaussianInt)
    (hp : ∀ u, 0 ≤ p u ∧ p u ≤ 1) :
    ‖Work.FIArea7.radBeta Pa p Pa.C z‖ ≤ tauN z := by
  rw [Work.FIArea7.radBeta]
  by_cases hc : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
  · rw [if_pos hc]
    have hp1 : ‖((((p (Work.FIPlan.gnorm z) : ℝ)) : ℂ))‖ ≤ 1 := by
      rw [norm_ofReal_c, abs_of_nonneg (hp _).1]; exact (hp _).2
    have hmu1 : ‖((((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℤ)) : ℂ))‖ ≤ 1 := by
      rw [norm_intCast_c]; exact abs_moebius_cast_le_one _
    have hg1 : ‖((((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ)) : ℂ))‖
        ≤ tauN z := by
      rw [norm_ofReal_c]
      exact abs_gammaTrunc_le Pa.C _
    rw [norm_mul, norm_mul]
    calc ‖((((p (Work.FIPlan.gnorm z) : ℝ)) : ℂ))‖
            * ‖((((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℤ)) : ℂ))‖
            * ‖((((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ)) : ℂ))‖
        ≤ 1 * 1 * tauN z :=
          mul_le_mul (mul_le_mul hp1 hmu1 (norm_nonneg _) (by norm_num)) hg1
            (norm_nonneg _) (by norm_num)
      _ = tauN z := by ring
  · rw [if_neg hc]
    simpa using tauN_nonneg z

/-- `‖betaTilde z‖ ≤ τ(|z|²)`. -/
private lemma norm_betaTilde_le (Pa : Work.FITop.Params) (q p : ℝ → ℝ) (φ : ℝ)
    (z0 z : GaussianInt) (hmoll : Work.FIArea7.IsMollPair Pa q p) :
    ‖Work.FIArea7.betaTilde Pa q p φ z0 z‖ ≤ tauN z := by
  obtain ⟨-, -, hq01, -, -, hp01, -, -⟩ := hmoll
  rw [Work.FIArea7.betaTilde, Work.FIArea7.radBetaCls]
  have hq1 : ‖((((q (Complex.arg z.toComplex - φ) : ℝ)) : ℂ))‖ ≤ 1 := by
    rw [norm_ofReal_c, abs_of_nonneg (hq01 _).1]
    exact (hq01 _).2
  have hcls : ‖(if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)‖ ≤ 1 := by
    by_cases h : Work.FITop4.SameClass8 z z0 <;> simp [h]
  rw [norm_mul, norm_mul]
  calc ‖((((q (Complex.arg z.toComplex - φ) : ℝ)) : ℂ))‖
        * (‖(if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)‖
            * ‖Work.FIArea7.radBeta Pa p Pa.C z‖)
      ≤ 1 * (1 * tauN z) :=
        mul_le_mul hq1
          (mul_le_mul hcls (norm_radBeta_le Pa p z hp01) (norm_nonneg _) (by norm_num))
          (by positivity) (by norm_num)
    _ = tauN z := by ring

/-- **The pointwise Rankin bound of the (5.9)-complement.** -/
private lemma complement_term_le (Pa : Work.FITop.Params) (q p : ℝ → ℝ) (φ : ℝ)
    (z0 z : GaussianInt) (hmoll : Work.FIArea7.IsMollPair Pa q p) (hτ : 0 < Pa.τ) :
    ‖Work.FIArea7.betaTilde Pa q p φ z0 z
        * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2
      ≤ (tauN z) ^ 27 * Pa.τ ^ (-(25 : ℝ)) := by
  have hnorm := norm_betaTilde_le Pa q p φ z0 z hmoll
  by_cases hcase : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ
  · rw [if_pos hcase, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (pow_nonneg (tauN_nonneg z) 27) (Real.rpow_nonneg hτ.le _)
  · rw [if_neg hcase, mul_one]
    have hlt : Pa.τ < (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := not_le.mp hcase
    have h2 : ‖Work.FIArea7.betaTilde Pa q p φ z0 z‖ ^ 2
        ≤ (tauN z) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hid : (tauN z) ^ 27 * Pa.τ ^ (-(25 : ℝ))
        = (tauN z) ^ 2 * ((tauN z) ^ 25 * Pa.τ ^ (-(25 : ℝ))) := by
      rw [show (27 : ℕ) = 2 + 25 from rfl, pow_add]
      ring
    rw [hid]
    have hτ25 : Pa.τ ≤ tauN z := hlt.le
    have h25 : (1 : ℝ) ≤ (tauN z) ^ 25 * Pa.τ ^ (-(25 : ℝ)) := by
      have h5 : Pa.τ ^ (25 : ℕ) ≤ (tauN z) ^ (25 : ℕ) := pow_le_pow_left₀ hτ.le hτ25 25
      have hrpow : Pa.τ ^ (-(25 : ℝ)) = (Pa.τ ^ (25 : ℕ))⁻¹ := by
        rw [Real.rpow_neg hτ.le]
        norm_num
      rw [hrpow, ← div_eq_mul_inv, one_le_div (pow_pos hτ 25)]
      exact h5
    calc ‖Work.FIArea7.betaTilde Pa q p φ z0 z‖ ^ 2 ≤ (tauN z) ^ 2 := h2
      _ = (tauN z) ^ 2 * 1 := by ring
      _ ≤ (tauN z) ^ 2 * ((tauN z) ^ 25 * Pa.τ ^ (-(25 : ℝ))) :=
          mul_le_mul_of_nonneg_left h25 (sq_nonneg _)

/-! ## 1. The box `gBox R`: coordinates and the norm bound -/

/-- `|z|²` in coordinates. -/
private lemma gnorm_eq_coords (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simp only [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]

/-- `(a² + b²).natAbs = a.natAbs² + b.natAbs²` for integers `a, b`. -/
private lemma int_natAbs_sq_sum (a b : ℤ) :
    (a ^ 2 + b ^ 2).natAbs = a.natAbs ^ 2 + b.natAbs ^ 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ a ^ 2 + b ^ 2)]
  rw [show (((a.natAbs : ℤ)) ^ 2) = a ^ 2 by rw [← sq_abs a, Int.abs_eq_natAbs],
    show (((b.natAbs : ℤ)) ^ 2) = b ^ 2 by rw [← sq_abs b, Int.abs_eq_natAbs]]

/-- Membership in `gBox R` bounds both coordinates by `R.natAbs`. -/
private lemma mem_gBox_coords {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    z.re.natAbs ≤ R.natAbs ∧ z.im.natAbs ≤ R.natAbs := by
  rw [Work.FIPlan.gBox] at hz
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at h1 h2
  have hR0 : 0 ≤ R := by linarith [h1.1, h2.1]
  have hre : p.1 = z.re := by rw [← hpz]
  have him : p.2 = z.im := by rw [← hpz]
  constructor
  · have habs : ((z.re.natAbs : ℤ)) ≤ R := by
      have h := abs_le.mpr ⟨h1.1, h1.2⟩
      rw [hre, Int.abs_eq_natAbs] at h
      exact h
    rw [← Int.natAbs_of_nonneg hR0] at habs
    exact Nat.cast_le.mp habs
  · have habs : ((z.im.natAbs : ℤ)) ≤ R := by
      have h := abs_le.mpr ⟨h2.1, h2.2⟩
      rw [him, Int.abs_eq_natAbs] at h
      exact h
    rw [← Int.natAbs_of_nonneg hR0] at habs
    exact Nat.cast_le.mp habs

/-- On `gBox R` the norm is at most `2 R²`. -/
private lemma gnorm_le_of_mem_gBox {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    Work.FIPlan.gnorm z ≤ 2 * R.natAbs ^ 2 := by
  obtain ⟨h1, h2⟩ := mem_gBox_coords hz
  rw [gnorm_eq_coords]
  calc z.re.natAbs ^ 2 + z.im.natAbs ^ 2 ≤ R.natAbs ^ 2 + R.natAbs ^ 2 :=
        Nat.add_le_add (Nat.pow_le_pow_left h1 2) (Nat.pow_le_pow_left h2 2)
    _ = 2 * R.natAbs ^ 2 := by ring

/-! ## 2. The fibre bound `#{z ∈ gBox R : |z|² = n} ≤ 4τ(n)` -/

/-- The number of box points of a given norm `n ≥ 1` is at most the number of representations of
`n` as an ordered sum of two squares, which is `≤ 4τ(n)` (Jacobi's two-squares formula,
`Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos`). -/
private lemma fiber_le (R : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ((((Work.FIPlan.gBox R).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
      ≤ 4 * (((n.divisors.card : ℕ) : ℝ)) := by
  set S : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z => Work.FIPlan.gnorm z = n) with hS
  set T : Finset (ℤ × ℤ) :=
    Finset.filter (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))
      (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)) with hT
  have hinj : Set.InjOn (fun z : GaussianInt => (z.re, z.im)) ↑S := by
    intro x _ y _ h
    exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hcard : (S.card : ℤ) = ((S.image (fun z : GaussianInt => (z.re, z.im))).card : ℤ) := by
    rw [Finset.card_image_of_injOn hinj]
  have hsub : S.image (fun z : GaussianInt => (z.re, z.im)) ⊆ T := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := Finset.mem_image.mp hp
    rw [hS, Finset.mem_filter] at hz
    obtain ⟨hzbox, hznorm⟩ := hz
    rw [hT]
    have hsum : z.re.natAbs ^ 2 + z.im.natAbs ^ 2 = n := by
      rw [← gnorm_eq_coords z, hznorm]
    have hre : z.re.natAbs ≤ n := by
      rcases Nat.eq_zero_or_pos z.re.natAbs with h | h
      · omega
      · nlinarith [hsum]
    have him : z.im.natAbs ≤ n := by
      rcases Nat.eq_zero_or_pos z.im.natAbs with h | h
      · omega
      · nlinarith [hsum]
    have hp1 : p.1 = z.re := by rw [← hpz]
    have hp2 : p.2 = z.im := by rw [← hpz]
    have habs1 : |p.1| ≤ (n : ℤ) := by
      rw [hp1, Int.abs_eq_natAbs]; exact_mod_cast hre
    have habs2 : |p.2| ≤ (n : ℤ) := by
      rw [hp2, Int.abs_eq_natAbs]; exact_mod_cast him
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact (abs_le.mp habs1).1
    · exact (abs_le.mp habs1).2
    · exact (abs_le.mp habs2).1
    · exact (abs_le.mp habs2).2
    · rw [hp1, hp2]
      have h1 : (z.re ^ 2 + z.im ^ 2).natAbs = n := by rw [int_natAbs_sq_sum, hsum]
      have h2 : ((z.re ^ 2 + z.im ^ 2).natAbs : ℤ) = z.re ^ 2 + z.im ^ 2 :=
        Int.natAbs_of_nonneg (by positivity)
      rw [← h2, h1]
  have hcard2 : ((S.image (fun z : GaussianInt => (z.re, z.im))).card : ℤ) ≤ ((T.card : ℕ) : ℤ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hJac := Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos n hn
  have hfin : (S.card : ℤ) ≤ 4 * ((n.divisors.card : ℕ) : ℤ) := by
    rw [hcard]
    exact le_trans hcard2 hJac
  have : (S.card : ℝ) ≤ 4 * (((n.divisors.card : ℕ) : ℝ)) := by exact_mod_cast hfin
  simpa [hS] using this

/-! ## 3. Regrouping a box sum by the value of the norm -/

private lemma sum_comp_gnorm (s : Finset GaussianInt) (Y : ℕ) (F : ℕ → ℝ)
    (hY : ∀ z ∈ s, Work.FIPlan.gnorm z ≤ Y) (hF0 : F 0 = 0) :
    ∑ z ∈ s, F (Work.FIPlan.gnorm z)
      = ∑ n ∈ Finset.Icc 1 Y, (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
          * F n := by
  have hterm : ∀ z ∈ s, F (Work.FIPlan.gnorm z)
      = ∑ n ∈ Finset.Icc 1 Y, (if Work.FIPlan.gnorm z = n then F n else 0) := by
    intro z hz
    rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm z) with h0 | hpos
    · have hz0 : ∀ n ∈ Finset.Icc 1 Y,
          (if Work.FIPlan.gnorm z = n then F n else 0) = 0 := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [if_neg]
        omega
      rw [Finset.sum_eq_zero hz0, h0, hF0]
    · rw [Finset.sum_ite_eq_of_mem (Finset.Icc 1 Y) (Work.FIPlan.gnorm z) F
        (Finset.mem_Icc.mpr ⟨hpos, hY z hz⟩)]
  calc ∑ z ∈ s, F (Work.FIPlan.gnorm z)
      = ∑ z ∈ s, ∑ n ∈ Finset.Icc 1 Y,
          (if Work.FIPlan.gnorm z = n then F n else 0) := Finset.sum_congr rfl hterm
    _ = ∑ n ∈ Finset.Icc 1 Y, ∑ z ∈ s,
          (if Work.FIPlan.gnorm z = n then F n else 0) := Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 Y,
          ∑ z ∈ s.filter (fun z => Work.FIPlan.gnorm z = n), F n := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc 1 Y,
          (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ) * F n := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 4. The moment of `τ(|z|²)^K` over the box -/

private lemma sum_tau_gnorm_pow_le (R : ℤ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ z ∈ Work.FIPlan.gBox R, (tauN z) ^ K
      ≤ 4 * ∑ n ∈ Finset.Icc 1 (2 * R.natAbs ^ 2),
          ((((n.divisors.card : ℕ) : ℝ)) ^ (K + 1)) := by
  have hF0 : (fun n : ℕ => ((((n.divisors.card : ℕ) : ℝ)) ^ K)) 0 = 0 := by
    show ((((0 : ℕ).divisors.card : ℕ) : ℝ)) ^ K = 0
    rw [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    exact zero_pow (by omega)
  have hcomp := sum_comp_gnorm (Work.FIPlan.gBox R) (2 * R.natAbs ^ 2)
    (fun n : ℕ => ((((n.divisors.card : ℕ) : ℝ)) ^ K))
    (fun z hz => gnorm_le_of_mem_gBox hz) hF0
  calc ∑ z ∈ Work.FIPlan.gBox R, (tauN z) ^ K
      = ∑ n ∈ Finset.Icc 1 (2 * R.natAbs ^ 2),
          ((((Work.FIPlan.gBox R).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
            * ((((n.divisors.card : ℕ) : ℝ)) ^ K) := by
          simpa only [tauN] using hcomp
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * R.natAbs ^ 2),
          (4 * (((n.divisors.card : ℕ) : ℝ))) * ((((n.divisors.card : ℕ) : ℝ)) ^ K) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        exact mul_le_mul_of_nonneg_right (fiber_le R n hn1) (by positivity)
    _ = 4 * ∑ n ∈ Finset.Icc 1 (2 * R.natAbs ^ 2),
          ((((n.divisors.card : ℕ) : ℝ)) ^ (K + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [pow_succ]
        ring

/-! ## 5. The box radius `radN` and the numeric core -/

private lemma radN_natAbs_sq_le (Pa : Work.FITop.Params) (hN : 1 ≤ Pa.N) :
    (Work.FITop.radN Pa).natAbs ^ 2 ≤ 9 * Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := hN
  have hN0 : (0 : ℝ) ≤ Pa.N := le_of_lt (lt_of_lt_of_le zero_lt_one hN1)
  have hceil : (⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ : ℝ) < Real.sqrt (4 * (Pa.N : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hle : (⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ : ℝ) ^ 2 ≤ 9 * (Pa.N : ℝ) := by
    have h2 : Real.sqrt (4 * (Pa.N : ℝ)) + 1 = 2 * Real.sqrt (Pa.N : ℝ) + 1 := by
      have h4 : Real.sqrt (4 * (Pa.N : ℝ)) = 2 * Real.sqrt (Pa.N : ℝ) := by
        rw [show (4 : ℝ) * (Pa.N : ℝ) = 2 ^ 2 * (Pa.N : ℝ) by norm_num,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [h4]
    have h3 : (2 * Real.sqrt (Pa.N : ℝ) + 1) ^ 2 ≤ 9 * (Pa.N : ℝ) := by
      have hsq : Real.sqrt (Pa.N : ℝ) ^ 2 = (Pa.N : ℝ) := Real.sq_sqrt hN0
      nlinarith [Real.sqrt_nonneg (Pa.N : ℝ), hN1, hsq]
    calc (⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ : ℝ) ^ 2
        ≤ (Real.sqrt (4 * (Pa.N : ℝ)) + 1) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hceil.le 2
      _ = (2 * Real.sqrt (Pa.N : ℝ) + 1) ^ 2 := by rw [h2]
      _ ≤ 9 * (Pa.N : ℝ) := h3
  have hcast : (Work.FITop.radN Pa).natAbs = ⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ := by
    rw [Work.FITop.radN]
    simp
  rw [hcast]
  exact_mod_cast hle

/-- `72·2^{2^28} ≤ M^{757778943}` for `M ≥ 17`. -/
private lemma const_bound (M : ℝ) (hM : 17 ≤ M) :
    72 * (2 : ℝ) ^ (((2 ^ 28 : ℕ) : ℝ)) ≤ M ^ (757778943 : ℝ) := by
  have hbase : (16 : ℝ) ≤ M := by linarith
  have h1 : (16 : ℝ) ^ (757778943 : ℝ) ≤ M ^ (757778943 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hbase (by norm_num)
  have h2 : (16 : ℝ) ^ (757778943 : ℝ) = (2 : ℝ) ^ (3031115772 : ℝ) := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 4 (757778943 : ℝ)]
    norm_num
  have h3 : 72 * (2 : ℝ) ^ (((2 ^ 28 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (3031115772 : ℝ) := by
    have h72 : (72 : ℝ) ≤ (2 : ℝ) ^ (7 : ℝ) := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have h7 : (2 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (((2 ^ 28 : ℕ) : ℝ))
        = (2 : ℝ) ^ (7 + (((2 ^ 28 : ℕ) : ℝ))) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) 7 (((2 ^ 28 : ℕ) : ℝ))).symm
    have hexp : 7 + (((2 ^ 28 : ℕ) : ℝ)) ≤ (3031115772 : ℝ) := by norm_num
    calc 72 * (2 : ℝ) ^ (((2 ^ 28 : ℕ) : ℝ))
        ≤ (2 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (((2 ^ 28 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right h72 (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (7 + (((2 ^ 28 : ℕ) : ℝ))) := h7
      _ ≤ (2 : ℝ) ^ (3031115772 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  rw [h2] at h1
  exact le_trans h3 h1

/-- **The numeric core of the Rankin mass bound.** -/
private lemma rankin_numeric_core (C N Y L M : ℝ) (hC : 0 < C) (hN : 1 ≤ N) (hY1 : 1 ≤ Y)
    (hY : Y ≤ 18 * N) (hCleq : C ≤ M) (hlogY : Real.log Y + 2 ≤ 2 * M)
    (hM17 : 17 ≤ M) (hML : M ≤ L) :
    4 * C * Y * (Real.log Y + 2) ^ (((2 ^ 28 : ℕ) : ℝ)) * L ^ (-(25 * 201048576 : ℝ))
      ≤ N * M ^ (-(4 * 10 ^ 9 : ℝ)) := by
  have hM0 : 0 < M := by linarith
  have hL0 : 0 < L := lt_of_lt_of_le hM0 hML
  have hlogY0 : 0 ≤ Real.log Y + 2 := by
    have h := Real.log_nonneg hY1
    linarith
  have hconst := const_bound M hM17
  set e : ℝ := ((2 ^ 28 : ℕ) : ℝ) with he
  have hpow : (Real.log Y + 2) ^ e ≤ (2 * M) ^ e :=
    Real.rpow_le_rpow hlogY0 hlogY (by positivity)
  have hmul : (2 * M) ^ e = (2 : ℝ) ^ e * M ^ e := Real.mul_rpow (by norm_num) hM0.le
  have hCY : 4 * C * Y ≤ 4 * M * (18 * N) := by
    have h4C : 4 * C ≤ 4 * M := by linarith
    calc 4 * C * Y ≤ 4 * M * Y := mul_le_mul_of_nonneg_right h4C (by linarith)
      _ ≤ 4 * M * (18 * N) := mul_le_mul_of_nonneg_left hY (by linarith)
  have hLr : L ^ (-(25 * 201048576 : ℝ)) ≤ M ^ (-(25 * 201048576 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hM0 hML (by norm_num)
  have hM1 : M * M ^ e = M ^ (e + 1) := by
    have h := Real.rpow_add hM0 e 1
    rw [Real.rpow_one] at h
    rw [mul_comm, ← h]
  have hMc : M ^ (e + 1) * M ^ (-(25 * 201048576 : ℝ)) = M ^ (-4757778943 : ℝ) := by
    rw [← Real.rpow_add hM0]
    norm_num
  have hMd : M ^ (-4757778943 : ℝ) = M ^ (-(4 * 10 ^ 9 : ℝ)) * M ^ (-757778943 : ℝ) := by
    rw [← Real.rpow_add hM0]
    norm_num
  have hkey : 72 * (2 : ℝ) ^ e * M ^ (-757778943 : ℝ) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hM0.le (-757778943 : ℝ))
    have hsum : M ^ (757778943 : ℝ) * M ^ (-757778943 : ℝ) = 1 := by
      rw [← Real.rpow_add hM0, add_neg_cancel, Real.rpow_zero]
    linarith [hm, hsum.le, hsum.ge]
  have stepA : 4 * C * Y * (Real.log Y + 2) ^ e * L ^ (-(25 * 201048576 : ℝ))
      ≤ 4 * M * (18 * N) * ((2 : ℝ) ^ e * M ^ e) * L ^ (-(25 * 201048576 : ℝ)) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
    have hp : (Real.log Y + 2) ^ e ≤ (2 : ℝ) ^ e * M ^ e := hpow.trans hmul.le
    exact mul_le_mul hCY hp (Real.rpow_nonneg hlogY0 _) (by positivity)
  have stepB : 4 * M * (18 * N) * ((2 : ℝ) ^ e * M ^ e) * L ^ (-(25 * 201048576 : ℝ))
      = 72 * (2 : ℝ) ^ e * N * (M * M ^ e) * L ^ (-(25 * 201048576 : ℝ)) := by ring
  have h4 : M ^ (e + 1) * L ^ (-(25 * 201048576 : ℝ))
      ≤ M ^ (e + 1) * M ^ (-(25 * 201048576 : ℝ)) :=
    mul_le_mul_of_nonneg_left hLr (by positivity)
  have stepC : 72 * (2 : ℝ) ^ e * N * M ^ (e + 1) * L ^ (-(25 * 201048576 : ℝ))
      ≤ 72 * (2 : ℝ) ^ e * N * (M ^ (e + 1) * M ^ (-(25 * 201048576 : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ 72 * (2:ℝ)^e * N by positivity)
    calc 72 * (2 : ℝ) ^ e * N * M ^ (e + 1) * L ^ (-(25 * 201048576 : ℝ))
        = 72 * (2 : ℝ) ^ e * N * (M ^ (e + 1) * L ^ (-(25 * 201048576 : ℝ))) := by ring
      _ ≤ 72 * (2 : ℝ) ^ e * N * (M ^ (e + 1) * M ^ (-(25 * 201048576 : ℝ))) := h
  calc 4 * C * Y * (Real.log Y + 2) ^ e * L ^ (-(25 * 201048576 : ℝ))
      ≤ 4 * M * (18 * N) * ((2 : ℝ) ^ e * M ^ e) * L ^ (-(25 * 201048576 : ℝ)) := stepA
    _ = 72 * (2 : ℝ) ^ e * N * (M * M ^ e) * L ^ (-(25 * 201048576 : ℝ)) := stepB
    _ = 72 * (2 : ℝ) ^ e * N * M ^ (e + 1) * L ^ (-(25 * 201048576 : ℝ)) := by rw [hM1]
    _ ≤ 72 * (2 : ℝ) ^ e * N * (M ^ (e + 1) * M ^ (-(25 * 201048576 : ℝ))) := stepC
    _ = 72 * (2 : ℝ) ^ e * N * M ^ (-4757778943 : ℝ) := by rw [hMc]
    _ = 72 * (2 : ℝ) ^ e * N
          * (M ^ (-(4 * 10 ^ 9 : ℝ)) * M ^ (-757778943 : ℝ)) := by rw [hMd]
    _ = (72 * (2 : ℝ) ^ e * M ^ (-757778943 : ℝ)) * (N * M ^ (-(4 * 10 ^ 9 : ℝ))) := by
        ring
    _ ≤ 1 * (N * M ^ (-(4 * 10 ^ 9 : ℝ))) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = N * M ^ (-(4 * 10 ^ 9 : ℝ)) := by ring

/-! ## 6. The main theorem -/

/-- **A3: the mass of the (5.9)-complement, by Rankin's trick** (*FI* (10.4)–(10.7) replaced by a
mass bound, since the round-6 contract keeps `τ(|z|²) ≤ Pa.τ` inside `β`; see
`AREA7_ROUTE_LEAD.md` §0.1).

With `Pa.τ = tauOf Pa.x Asave = (log x)^{201048576}`, the complement
`δτ = betaTilde·1[τ(n) > Pa.τ]` has `L²`-mass at most `N·(log N)^{-4·10^9}`.

Proof: (1) `‖betaTilde‖ ≤ τ(n)`; (2) Rankin, `1[τ > Pa.τ] ≤ (τ/Pa.τ)^{25}`, and `r₂(n) ≤ 4τ(n)`;
(3) this gives `≤ 8N(1+log 2N)^{2^28}·(log x)^{-25·201048576}`, which is `≤ N(log N)^{-4·10^9}` for
large `x` (using `log N ≤ log x ≤ 4 log N`).  `2^28` stays symbolic: no numeral is evaluated
beyond `25·201048576 − 2^28 ≥ 4·10^9 + 1`.  Use `sum_tau_pow_le` (A3a) for the moment bound. -/
theorem deltaTau_mass_le : ∃ x0 : ℝ, ∀ (Pa : Work.FITop.Params) (q p : ℝ → ℝ) (φ : ℝ) (z0 : GaussianInt),
    x0 ≤ (Pa.x : ℝ) → Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
    Work.FIArea7.IsMollPair Pa q p →
    ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ‖Work.FIArea7.betaTilde Pa q p φ z0 z
          * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2
      ≤ Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FIArea2.sum_tau_pow_le 28
  refine ⟨Real.exp (200 * (C + 5)), ?_⟩
  intro Pa q p φ z0 hx hPatau hmoll
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h2 : (1 : ℝ) ≤ Real.exp (200 * (C + 5)) := Real.one_le_exp (by linarith)
    linarith
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hlogx : 200 * (C + 5) ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  set L : ℝ := Real.log (Pa.x : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hL1 : (1 : ℝ) ≤ L := by rw [hL]; linarith
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : 0 < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  -- `N < x`
  have hNlt : Pa.N < (Pa.x : ℝ) := by
    have h1 : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith [Pa.hB])
    have h3 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Pa.x : ℝ) := by
      have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Pa.x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      simpa [Real.rpow_one] using h2
    calc Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B) := Pa.hNhi
      _ ≤ (Pa.x : ℝ) * 1 :=
          mul_le_mul h3 h1 (Real.rpow_nonneg (by positivity) _) (by linarith)
      _ = (Pa.x : ℝ) := by ring
  set M : ℝ := Real.log Pa.N with hM
  have hML : M ≤ L := by
    rw [hM, hL]
    exact Real.log_le_log hNpos hNlt.le
  have hMbig : 50 * (C + 5) ≤ M := by
    have hlo : (1 / 4 : ℝ) * Real.log (Pa.x : ℝ) ≤ Real.log Pa.N := by
      have h1 : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) = ((1 : ℝ) / 4 + Pa.η) * L := by
        rw [Real.log_rpow hxpos, hL]
      have h2 : ((1 : ℝ) / 4 + Pa.η) * L ≤ Real.log Pa.N := by
        rw [← h1]
        exact Real.log_le_log (Real.rpow_pos_of_pos hxpos _) (le_of_lt Pa.hNlo)
      have h3 : (1 / 4 : ℝ) * L ≤ ((1 : ℝ) / 4 + Pa.η) * L := by
        nlinarith [hL0, Pa.hη]
      linarith
    have h4 : 50 * (C + 5) ≤ (1 / 4 : ℝ) * Real.log (Pa.x : ℝ) := by
      rw [hL] at hlogx
      linarith
    rw [hM]
    linarith
  have hM17 : 17 ≤ M := by linarith
  have hCleq : C ≤ M := by linarith
  -- the `τ` facts
  have hPatau_val : Pa.τ = L ^ (201048576 : ℝ) := by
    have h1 : Pa.τ = (Real.log (Pa.x : ℝ)) ^ (201048576 : ℝ) := by
      rw [hPatau]
      unfold Work.FITop4.tauOf Work.FITop4.Asave
      norm_num
    rwa [← hL] at h1
  have hτpos : 0 < Pa.τ := by rw [hPatau_val]; exact Real.rpow_pos_of_pos hL0 _
  have hτpow : Pa.τ ^ (-(25 : ℝ)) = L ^ (-(25 * 201048576 : ℝ)) := by
    rw [hPatau_val, ← Real.rpow_mul hL0.le]
    congr 1
    norm_num
  -- the radius bookkeeping
  have hRad : (Work.FITop.radN Pa).natAbs = ⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ := by
    rw [Work.FITop.radN]; simp
  have hR2 : 2 ≤ (Work.FITop.radN Pa).natAbs := by
    rw [hRad]
    have h1 : (2 : ℝ) ≤ Real.sqrt (4 * (Pa.N : ℝ)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      linarith
    have h2 : (2 : ℝ) ≤ ((⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ : ℕ) : ℝ) :=
      le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have hY1 : (1 : ℝ) ≤ ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) := by
    have h4 : 4 ≤ (Work.FITop.radN Pa).natAbs ^ 2 := by nlinarith
    have : (8 : ℕ) ≤ 2 * (Work.FITop.radN Pa).natAbs ^ 2 := by omega
    exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 8) this)
  have hY18 : ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) ≤ 18 * Pa.N := by
    have h := radN_natAbs_sq_le Pa Pa.hN1
    have h' : (((Work.FITop.radN Pa).natAbs : ℕ) : ℝ) ^ 2 ≤ 9 * Pa.N := by exact_mod_cast h
    push_cast
    linarith
  have hlogY : Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)) + 2 ≤ 2 * M := by
    have h1 : Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ))
        ≤ Real.log (18 * Pa.N) := Real.log_le_log (by positivity) hY18
    have h2 : Real.log (18 * Pa.N) = Real.log 18 + M := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hNpos), hM]
    have h3 : Real.log 18 + 2 ≤ M := by
      have h4 : Real.log 18 ≤ 17 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 18 by norm_num)
        linarith
      linarith [hM17]
    linarith
  -- the box sum and the moment bound
  have hbox : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ‖Work.FIArea7.betaTilde Pa q p φ z0 z
          * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2)
      ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (tauN z) ^ 27) * Pa.τ ^ (-(25 : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun z _ => complement_term_le Pa q p φ z0 z hmoll hτpos)
  have hmom := sum_tau_gnorm_pow_le (Work.FITop.radN Pa) 27 (by norm_num)
  have hstep2 : 4 * (∑ n ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
        ((((n.divisors.card : ℕ) : ℝ)) ^ 28))
      ≤ 4 * (C * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
          * (Real.log ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2) ^ (2 ^ 28)) :=
    mul_le_mul_of_nonneg_left (hC _) (by norm_num)
  have hrpow : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (tauN z) ^ 27) * Pa.τ ^ (-(25 : ℝ))
      ≤ 4 * C * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
          * (Real.log ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2) ^ (((2 ^ 28 : ℕ) : ℝ))
          * L ^ (-(25 * 201048576 : ℝ)) := by
    calc (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (tauN z) ^ 27) * Pa.τ ^ (-(25 : ℝ))
        ≤ (4 * ∑ n ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
              ((((n.divisors.card : ℕ) : ℝ)) ^ 28)) * Pa.τ ^ (-(25 : ℝ)) :=
            mul_le_mul_of_nonneg_right hmom (Real.rpow_nonneg hτpos.le _)
      _ ≤ (4 * (C * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
              * (Real.log ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2) ^ (2 ^ 28)))
              * Pa.τ ^ (-(25 : ℝ)) :=
            mul_le_mul_of_nonneg_right hstep2 (Real.rpow_nonneg hτpos.le _)
      _ = 4 * C * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
              * (Real.log ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)
                ^ (((2 ^ 28 : ℕ) : ℝ))
              * L ^ (-(25 * 201048576 : ℝ)) := by
            rw [hτpow, ← Real.rpow_natCast
              (Real.log ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2) (2 ^ 28)]
            ring
  calc ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ‖Work.FIArea7.betaTilde Pa q p φ z0 z
          * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2
      ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (tauN z) ^ 27)
          * Pa.τ ^ (-(25 : ℝ)) := hbox
    _ ≤ Pa.N * M ^ (-(4 * 10 ^ 9 : ℝ)) :=
        le_trans hrpow
          (rankin_numeric_core C Pa.N ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) L M
            hCpos hN1 hY1 hY18 hCleq hlogY hM17 hML)
    _ = Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ)) := by rw [hM]

end

end Work.FIArea7
