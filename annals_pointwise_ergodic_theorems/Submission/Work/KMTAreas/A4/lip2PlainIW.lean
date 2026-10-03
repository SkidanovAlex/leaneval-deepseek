/-
# The inverse Weyl estimate for plain polynomial exponential sums (`plainIW`)

This file proves the *inverse form of Weyl's exponential sum estimate* for plain sums

  `∑_{n ∈ [a,b]} c · e (F n)`,

where `F : ℝ[X]` is a real polynomial of degree `d ≥ 1`, `c` is a complex number of modulus `1`
and `e (x) = exp (2 π i x)`:

if the sum has modulus at least `η · #([a,b])` then the leading coefficient of `F` has a rational
approximation with denominator at most `C η^{-K}` and error at most `C η^{-K} / #([a,b])^d`.

The proof is a strong induction on `d`:

* `d = 1`: the geometric-sum (Dirichlet kernel) bound;
* the step `d → d-1`: one van der Corput step (`Work.KMTAreas.A4.vdc_good`) reduces the level-`d`
  sum to a family of level-`(d-1)` sums over the overlap windows `J_h`, indexed by a set `H` of
  non-zero shifts with `∑_{h ∈ H} |J_h| ≥ η² L²/8`; the induction hypothesis at level `d-1` gives,
  for each `h ∈ H`, a denominator `q_h` with `‖q_h · (leading coefficient of F - F(X+h))‖` small,
  i.e. `‖q_h h d lc(F)‖ ≤ δ`; the pigeonhole principle extracts a single `q` and a subset
  `T ⊆ H` of density `∼ 1/Q`; the arithmetic amplification (Green--Tao Lemma 3.1 (ii)) applied to
  the `q`-multiples of `T` finally converts "many multiples of `β = d · lc F` are close to
  integers" into a rational approximation of `β` with the sharp `L^{-d}` error.

The arithmetic amplification enters as the hypothesis `hAmp` (it is proved in
`Work.KMTAreas.A4.lip2Amplify`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.eeDef
import Submission.Work.KMTAreas.A4.vdcPlainMathlib
import Submission.Work.KMTAreas.A4.coeff_comp_add_C_sub
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

set_option autoImplicit false
set_option maxHeartbeats 60000000

open scoped BigOperators
open Polynomial
open Pointwise

namespace Work.KMTAreas.A4

/-! ## The complex exponential `e x = exp (2 π i x)` -/

-- `ee` (`e (x) = exp (2 π i x)`) is defined in `Submission.Work.KMTAreas.A4.eeDef`.

theorem ee_ne_zero (x : ℝ) : ee x ≠ 0 := Complex.exp_ne_zero _

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_norm (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  have h : ee (-x) * ee x = 1 := by rw [← ee_add]; simp [ee]
  refine mul_right_cancel₀ (ee_ne_zero x) ?_
  rw [h]
  exact (inv_mul_cancel₀ (ee_ne_zero x)).symm

theorem star_ee (x : ℝ) : star (ee x) = ee (-x) := by
  rw [Complex.star_def, ← Complex.inv_eq_conj (ee_norm x), ee_neg]


theorem ee_eq_cexp (θ : ℝ) : ee θ = Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
  rw [ee]
  congr 1
  push_cast
  ring

theorem ee_sub (x y : ℝ) : ee (x - y) = ee x * star (ee y) := by
  rw [star_ee, ← ee_add]
  ring_nf

theorem ee_zpow (θ : ℝ) (n : ℤ) : ee (θ * (n : ℝ)) = ee θ ^ n := by
  rw [ee, ee]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ((θ * (n : ℝ) : ℝ) : ℂ))
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul]

/-! ## The real version of the leading-coefficient computation -/

theorem coeff_comp_add_C_sub_R (F : Polynomial ℝ) (d : ℕ) (hd : F.natDegree = d) (hd1 : 1 ≤ d)
    (h : ℝ) (hh : h ≠ 0) :
    (F - F.comp (Polynomial.X + Polynomial.C h)).natDegree = d - 1 ∧
      (F - F.comp (Polynomial.X + Polynomial.C h)).coeff (d - 1) =
        -(h * (d : ℝ) * F.coeff d) := by
  have hcoeff : (F.comp (Polynomial.X + Polynomial.C h)).coeff (d - 1) =
      F.coeff (d - 1) + (d : ℝ) * F.coeff d * h := coeff_comp_X_add_C_pred F hd hd1 h
  have hF0 : F ≠ 0 := by
    rintro rfl
    simp at hd
    omega
  have hlad : F.coeff d ≠ 0 := by
    rw [← hd]
    exact leadingCoeff_ne_zero.mpr hF0
  have hDcoeff : (F - F.comp (Polynomial.X + Polynomial.C h)).coeff (d - 1)
      = -((d : ℝ) * F.coeff d * h) := by
    rw [coeff_sub, hcoeff]
    ring
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hDne : (F - F.comp (Polynomial.X + Polynomial.C h)).coeff (d - 1) ≠ 0 := by
    rw [hDcoeff]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hd0 hlad) hh)
  have hUpper : (F - F.comp (Polynomial.X + Polynomial.C h)).natDegree ≤ d - 1 := by
    rw [← hd]
    exact natDegree_sub_comp_X_add_C_le F h
  have hLower : d - 1 ≤ (F - F.comp (Polynomial.X + Polynomial.C h)).natDegree :=
    le_natDegree_of_ne_zero hDne
  refine ⟨le_antisymm hUpper hLower, ?_⟩
  rw [hDcoeff]
  ring

/-! ## The target predicate and the trivial case -/

/-- `IW d C K` is the inverse Weyl estimate at degree `d` with constants `C` and the *natural*
exponent `K`. -/
def IW (d : ℕ) (C : ℝ) (K : ℕ) : Prop :=
  ∀ (F : Polynomial ℝ) (c : ℂ) (a b : ℤ) (η : ℝ),
    F.natDegree = d → ‖c‖ = 1 → a ≤ b → 0 < η → η ≤ 1 →
    η * (((b - a : ℤ) : ℝ) + 1) ≤
      ‖∑ n ∈ Finset.Icc a b, c * ee (F.eval (n : ℝ))‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * (η⁻¹) ^ K ∧
      ∃ m : ℤ, |(q : ℝ) * F.leadingCoeff - (m : ℝ)|
        ≤ C * (η⁻¹) ^ K / (((b - a : ℤ) : ℝ) + 1) ^ d

/-- The "trivial" case: if the interval is so short that `L^d ≤ 2 C η^{-K}`, the conclusion
follows from the nearest integer (`q = 1`, `m = round (lc F)`). -/
theorem IW_trivial {d : ℕ} {C : ℝ} {K : ℕ} (hC : 1 ≤ C) (F : Polynomial ℝ) (a b : ℤ) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hab : a ≤ b)
    (hL : (((b - a : ℤ) : ℝ) + 1) ^ d ≤ 2 * C * (η⁻¹) ^ K) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * (η⁻¹) ^ K ∧
      ∃ m : ℤ, |(q : ℝ) * F.leadingCoeff - (m : ℝ)|
        ≤ C * (η⁻¹) ^ K / (((b - a : ℤ) : ℝ) + 1) ^ d := by
  have hηinv1 : (1 : ℝ) ≤ η⁻¹ := by
    rw [one_le_inv₀ hη0]
    exact hη1
  have hpK : (1 : ℝ) ≤ (η⁻¹) ^ K := one_le_pow₀ hηinv1
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hCinv : (0 : ℝ) < C * (η⁻¹) ^ K := mul_pos hCpos (pow_pos (inv_pos.mpr hη0) K)
  -- the length is positive
  have hLpos : (0 : ℝ) < (((b - a : ℤ) : ℝ) + 1) := by
    have : (0 : ℤ) ≤ b - a := by omega
    have h2 : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  have hpowpos : (0 : ℝ) < (((b - a : ℤ) : ℝ) + 1) ^ d := pow_pos hLpos d
  refine ⟨1, le_rfl, ?_, round F.leadingCoeff, ?_⟩
  · have h1C : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1C]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (η⁻¹) ^ K := mul_le_mul hC hpK zero_le_one (le_of_lt hCpos)
  · have hround : |F.leadingCoeff - (round F.leadingCoeff : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hkey : (1 : ℝ) / 2 ≤ C * (η⁻¹) ^ K / (((b - a : ℤ) : ℝ) + 1) ^ d := by
      rw [le_div_iff₀ hpowpos]
      linarith [hL]
    have : |((1 : ℕ) : ℝ) * F.leadingCoeff - (round F.leadingCoeff : ℝ)|
        = |F.leadingCoeff - (round F.leadingCoeff : ℝ)| := by norm_num
    rw [this]
    linarith

/-! ## The base case `d = 1` -/

/-- Evaluation of a degree-one real polynomial. -/
private lemma eval_eq_of_natDegree_one_R (F : Polynomial ℝ) (hF : F.natDegree = 1) (x : ℝ) :
    F.eval x = F.coeff 1 * x + F.coeff 0 := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hF.le]
  simp [Polynomial.eval_add, Polynomial.eval_mul]

theorem IW_one : IW 1 4 1 := by
  intro F c a b η hd hc hab hη0 hη1 hmain
  classical
  set θ : ℝ := F.coeff 1 with hθ
  set N : ℕ := (b + 1 - a).toNat with hN
  have hN1 : 1 ≤ N := by rw [hN]; omega
  have hNL : (N : ℝ) = (((b - a : ℤ) : ℝ) + 1) := by
    rw [hN]
    have hNz : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg (by omega)
    have h1 : (((b + 1 - a).toNat : ℝ)) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast hNz
    have h2 : ((b + 1 - a : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by push_cast; ring
    exact h1.trans h2
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hlin : ∀ n : ℝ, F.eval n = F.coeff 1 * n + F.coeff 0 := fun n =>
    eval_eq_of_natDegree_one_R F hd n
  -- the summand is a constant times a power of `ee θ`
  have hterm : ∀ n : ℤ, c * ee (F.eval (n : ℝ))
      = (c * ee (F.coeff 0)) * (ee θ) ^ n := by
    intro n
    have h1 : F.eval ((n : ℤ) : ℝ) = θ * ((n : ℝ)) + F.coeff 0 := by
      rw [hlin, hθ]
    rw [h1, ee_add, ee_zpow, hθ]
    ring
  have hsum1 : (∑ n ∈ Finset.Icc a b, c * ee (F.eval (n : ℝ)))
      = (c * ee (F.coeff 0)) * ∑ n ∈ Finset.Icc a b, (ee θ) ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n
  have hz : ee θ ≠ 0 := ee_ne_zero θ
  have hsum2 : (∑ n ∈ Finset.Icc a b, (ee θ) ^ n)
      = (ee θ) ^ a * ∑ k ∈ Finset.range N, (ee θ) ^ (k : ℤ) := by
    rw [hN, Int.Icc_eq_finset_map, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hemb : (Nat.castEmbedding.trans (addLeftEmbedding a)) k = a + (k : ℤ) := rfl
    rw [hemb, zpow_add₀ hz]
  have hsum3 : (∑ k ∈ Finset.range N, (ee θ) ^ (k : ℤ))
      = ∑ k ∈ Finset.range N, Submission.VanDerCorput.linPhase θ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [zpow_natCast, ee_eq_cexp, ← Submission.VanDerCorput.linPhase_eq_pow]
  have hnormc : ‖c * ee (F.coeff 0)‖ = 1 := by
    rw [norm_mul, hc, ee_norm, mul_one]
  have hnorma : ‖(ee θ) ^ a‖ = 1 := by
    rw [norm_zpow, ee_norm, one_zpow]
  have hnorm : ‖∑ n ∈ Finset.Icc a b, c * ee (F.eval (n : ℝ))‖
      = ‖∑ k ∈ Finset.range N, Submission.VanDerCorput.linPhase θ k‖ := by
    rw [hsum1, norm_mul, hnormc, one_mul, hsum2, norm_mul, hnorma, one_mul, hsum3]
  -- the geometric bound
  have hbig : η * (N : ℝ) ≤ ‖∑ k ∈ Finset.range N, Submission.VanDerCorput.linPhase θ k‖ := by
    rw [hNL, ← hnorm]
    exact hmain
  have hd0 : 0 ≤ Submission.VanDerCorput.intDist θ := Submission.VanDerCorput.intDist_nonneg θ
  have hlt : Submission.VanDerCorput.intDist θ < 4 * (η⁻¹) ^ 1 / (N : ℝ) := by
    rcases eq_or_lt_of_le hd0 with hz | hpos
    · rw [← hz]
      have : (0 : ℝ) < 4 * (η⁻¹) ^ 1 / (N : ℝ) := by
        have : (0 : ℝ) < (η⁻¹) ^ 1 := by
          simpa using pow_pos (inv_pos.mpr hη0) 1
        positivity
      exact this
    · have hγ : η * (N : ℝ) ≤ (1 / 2) / Submission.VanDerCorput.intDist θ :=
        hbig.trans (Submission.UnitCircle.geom_sum_bound_of_intDist_pos (α := θ) hpos)
      have hηN : 0 < η * (N : ℝ) := mul_pos hη0 hNpos
      have hstrict : Submission.VanDerCorput.intDist θ < 4 * (η⁻¹) ^ 1 / (N : ℝ) := by
        have h2 : Submission.VanDerCorput.intDist θ ≤ (1 / 2) / (η * (N : ℝ)) := by
          rw [le_div_iff₀ hηN]
          rw [le_div_iff₀ hpos] at hγ
          linarith
        have h4 : (1 / 2 : ℝ) / (η * (N : ℝ)) < 4 * (η⁻¹) ^ 1 / (N : ℝ) := by
          rw [pow_one, div_lt_div_iff₀ (by positivity : (0:ℝ) < η * (N:ℝ)) hNpos]
          have hηinv2 : η⁻¹ * η = 1 := inv_mul_cancel₀ (ne_of_gt hη0)
          nlinarith [hηinv2, hNpos, hη0]
        linarith
      exact hstrict
  have hδ0 : 0 ≤ 4 * (η⁻¹) ^ 1 / (N : ℝ) := by
    have : (0 : ℝ) < (η⁻¹) ^ 1 := by simpa using pow_pos (inv_pos.mpr hη0) 1
    positivity
  obtain ⟨m, hm⟩ :=
    (Submission.IntDistRegion.intDist_lt_iff_exists_int (x := θ)
      (δ := 4 * (η⁻¹) ^ 1 / (N : ℝ)) hδ0).mp hlt
  have hlead : F.leadingCoeff = θ := by
    rw [hθ, ← hd, coeff_natDegree, leadingCoeff]
  refine ⟨1, le_rfl, ?_, m, ?_⟩
  · have hηinv1 : (1 : ℝ) ≤ η⁻¹ := by rw [one_le_inv₀ hη0]; exact hη1
    have h4 : (1 : ℝ) ≤ 4 * (η⁻¹) ^ 1 := by
      rw [pow_one]
      nlinarith
    simpa using h4
  · have hm' : |θ - (m : ℝ)| ≤ 4 * (η⁻¹) ^ 1 / (N : ℝ) := hm.le
    have hq : ((1 : ℕ) : ℝ) * F.leadingCoeff = θ := by rw [hlead]; norm_num
    have hL2 : ((((b - a : ℤ) : ℝ) + 1) ^ (1 : ℕ)) = (N : ℝ) := by rw [hNL, pow_one]
    rw [hq, hL2] at *
    exact hm'

/-! ## Pigeonhole: a frequently taken value -/

/-- **Pigeonhole.**  If `f : ℤ → ℕ` takes values in `[1,Q]` on the finite set `H`, then some
value `q ∈ [1,Q]` is taken on a subset `T ⊆ H` containing at least an `1/Q`-fraction of `H`. -/
theorem exists_common_value {H : Finset ℤ} {Q : ℕ} (hQ : 1 ≤ Q) (f : ℤ → ℕ)
    (hf : ∀ h ∈ H, 1 ≤ f h ∧ f h ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ ∃ T, T ⊆ H ∧ (H.card : ℝ) ≤ (Q : ℝ) * (T.card : ℝ) ∧
      ∀ h ∈ T, f h = q := by
  classical
  have hsum : ∑ q ∈ Finset.Icc 1 Q, (((H.filter fun h => f h = q).card : ℕ) : ℝ)
      = (H.card : ℝ) := by
    have h1 : ∀ q ∈ Finset.Icc 1 Q, (((H.filter fun h => f h = q).card : ℕ) : ℝ)
        = ∑ h ∈ H, (if f h = q then (1 : ℝ) else 0) := by
      intro q _
      rw [Finset.card_filter]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ h ∈ H, ∑ q ∈ Finset.Icc 1 Q, (if f h = q then (1 : ℝ) else 0) = 1 := by
      intro h hh
      rw [Finset.sum_eq_single (f h)]
      · simp
      · intro b _ hb
        rw [if_neg (fun h' => hb h'.symm)]
      · intro hnot
        exact absurd (Finset.mem_Icc.mpr (hf h hh)) hnot
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hQcard : ((Finset.Icc 1 Q).card : ℝ) = (Q : ℝ) := by
    have h : (Finset.Icc 1 Q).card = Q := by rw [Nat.card_Icc]; omega
    exact_mod_cast h
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ q ∈ Finset.Icc 1 Q,
      ((Q : ℝ) * (((H.filter fun h => f h = q).card : ℕ) : ℝ) < (H.card : ℝ)) := by
    intro q hq
    by_contra hge
    push_neg at hge
    obtain ⟨h, hh, hne⟩ := hcon q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (H.filter fun h => f h = q) (Finset.filter_subset _ _) hge
    exact hne (Finset.mem_filter.mp hh).2
  have hne : (Finset.Icc 1 Q).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩
  have h3 : ∑ q ∈ Finset.Icc 1 Q,
        ((Q : ℝ) * (((H.filter fun h => f h = q).card : ℕ) : ℝ))
      < ∑ q ∈ Finset.Icc 1 Q, (H.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne fun q hq => hlt q hq
  have h3' : (Q : ℝ) * (H.card : ℝ) < (Q : ℝ) * (H.card : ℝ) := by
    calc (Q : ℝ) * (H.card : ℝ)
        = ∑ q ∈ Finset.Icc 1 Q, ((Q : ℝ) * (((H.filter fun h => f h = q).card : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum, hsum]
      _ < ∑ q ∈ Finset.Icc 1 Q, (H.card : ℝ) := h3
      _ = ((Finset.Icc 1 Q).card : ℝ) * (H.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Q : ℝ) * (H.card : ℝ) := by rw [hQcard]
  exact lt_irrefl _ h3'




/-- The phase summand identity: the correlation of the phases of `F` at shift `h` is the phase of
the differenced polynomial `F - F(X + h)`. -/
theorem ee_corr (F : Polynomial ℝ) (c : ℂ) (hc : ‖c‖ = 1) (h n : ℤ) :
    (c * ee (F.eval (n : ℝ))) * star (c * ee (F.eval ((n + h : ℤ) : ℝ)))
      = ee ((F - F.comp (Polynomial.X + Polynomial.C (h : ℝ))).eval (n : ℝ)) := by
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp at hc
  have hcs : c * star c = 1 := by
    rw [Complex.star_def, ← Complex.inv_eq_conj hc, mul_inv_cancel₀ hcne]
  have hcast : (((n + h : ℤ)) : ℝ) = (n : ℝ) + (h : ℝ) := by push_cast; ring
  have hev : (F - F.comp (Polynomial.X + Polynomial.C (h : ℝ))).eval (n : ℝ)
      = F.eval (n : ℝ) - F.eval ((n : ℝ) + (h : ℝ)) := by
    rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
  have hstar : star (c * ee (F.eval ((n + h : ℤ) : ℝ)))
      = star c * ee (-(F.eval ((n : ℝ) + (h : ℝ)))) := by
    rw [star_mul, star_ee, hcast]
    ring
  have hAB : ee (F.eval (n : ℝ)) * ee (-(F.eval ((n : ℝ) + (h : ℝ))))
      = ee (F.eval (n : ℝ) - F.eval ((n : ℝ) + (h : ℝ))) := by
    rw [← ee_add]
    ring_nf
  rw [hstar, hev]
  calc c * ee (F.eval (n : ℝ)) * (star c * ee (-(F.eval ((n : ℝ) + (h : ℝ)))))
      = (c * star c) * (ee (F.eval (n : ℝ)) * ee (-(F.eval ((n : ℝ) + (h : ℝ))))) := by
        ring
    _ = (c * star c) * ee (F.eval (n : ℝ) - F.eval ((n : ℝ) + (h : ℝ))) := by rw [hAB]
    _ = ee (F.eval (n : ℝ) - F.eval ((n : ℝ) + (h : ℝ))) := by rw [hcs]; ring

/-- For `p ≤ q` the `IW`-length `(q - p) + 1` of the interval `[p,q]` is its cardinality. -/
theorem Icc_card_cast {p q : ℤ} (hpq : p ≤ q) :
    (((q - p : ℤ)) : ℝ) + 1 = ((Finset.Icc p q).card : ℝ) := by
  rw [Int.card_Icc]
  have h2 : ((q + 1 - p).toNat : ℤ) = q + 1 - p := Int.toNat_of_nonneg (by omega)
  have h3 : ((q + 1 - p).toNat : ℝ) = ((q + 1 - p : ℤ) : ℝ) := by exact_mod_cast h2
  rw [h3]
  push_cast
  ring

/-- The induction step of the plain inverse Weyl estimate. -/
theorem IW_step (d : ℕ) (hd : 2 ≤ d) {C' : ℝ} {K' : ℕ} (hC' : 0 < C')
    (hIW : IW (d - 1) C' K')
    (hAmp : ∀ (β δ₁ δ₂ : ℝ) (N : ℕ) (T : Finset ℤ), 1 ≤ N → 0 < δ₁ → 0 < δ₂ → δ₂ ≤ 1 →
      50 * δ₁ ≤ δ₂ ^ 2 → 1 ≤ δ₂ * ((N : ℝ) + 1) →
      (∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) →
      δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ) →
      (∀ n ∈ T, ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ₁) →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 2 ^ 20 / δ₂ ∧ ∃ a : ℤ,
        |β - (a : ℝ) / (q : ℝ)| ≤ 2 ^ 20 * δ₁ / (δ₂ ^ 3 * (2 * (N : ℝ) + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, IW d C K := by
  classical
  have hd1 : 1 ≤ d := by omega
  set K2 : ℝ := (2 : ℝ) ^ (d - 1) + (2 : ℝ) ^ (d - 2) * (32 * (C' + 1) * 4 ^ K')
      + 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (2 : ℝ) ^ (9 * d + 40) * (d : ℝ) ^ 3
      + 24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') + 1 with hK2def
  set C : ℝ := 1 + (K2 + 1) ^ d / 2 + (2 : ℝ) ^ 20 * (24 * (C' + 1) ^ 2 * 4 ^ (2 * K'))
      + (2 : ℝ) ^ (9 * d + 70) * 24 ^ 4 * C' * (C' + 1) ^ 8 * 4 ^ (9 * K') * (d : ℝ) ^ 3
      + (2 : ℝ) ^ 20 * 24 * (d : ℝ) * ((C' + 1) ^ 2 * 4 ^ (2 * K')) with hCdef
  set M0 : ℕ := max (10 * K' + 2 * d + 2) (max (2 * K' + 2) (2 * (d - 1))) with hM0def
  set K : ℕ := max (d * M0) (max (2 * K' + 2) (18 * K' + 2 * d + 6)) with hKdef
  have hK2t1 : (0:ℝ) ≤ (2 : ℝ) ^ (d - 2) * (32 * (C' + 1) * 4 ^ K') := by positivity
  have hK2t2 : (0:ℝ) ≤ 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (2 : ℝ) ^ (9 * d + 40) * (d : ℝ) ^ 3 := by
    positivity
  have hK2t3 : (0:ℝ) ≤ (2 : ℝ) ^ (d - 1) := by positivity
  have hK2t4 : (0:ℝ) ≤ 24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') := by positivity
  have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; linarith [hK2t1, hK2t2, hK2t3, hK2t4]
  have hK2a : (2 : ℝ) ^ (d - 1) ≤ K2 := by
    rw [hK2def]
    linarith [hK2t1, hK2t2, hK2t4]
  have hK2b : 24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') ≤ K2 := by
    rw [hK2def]
    linarith [hK2t1, hK2t2, hK2t3]
  have h64 : (64:ℝ) ^ (d - 1) ≤ (2:ℝ) ^ (9 * d + 40) := by
    calc (64:ℝ) ^ (d - 1) ≤ (64:ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((2:ℝ)^6) ^ d := by norm_num
      _ = (2:ℝ) ^ (6 * d) := by rw [← pow_mul]
      _ ≤ (2:ℝ) ^ (9 * d + 40) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hK2c : 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (64:ℝ) ^ (d - 1) * (d : ℝ) ^ 2 ≤ K2 := by
    have hlt : 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (64:ℝ) ^ (d - 1) * (d : ℝ) ^ 2
        ≤ 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (2:ℝ) ^ (9 * d + 40) * (d : ℝ) ^ 3 := by
      have h1 : (64:ℝ) ^ (d - 1) * (d:ℝ) ^ 2 ≤ (2:ℝ) ^ (9 * d + 40) * (d:ℝ) ^ 3 := by
        have h2 : (0:ℝ) ≤ (2:ℝ) ^ (9 * d + 40) * (d:ℝ) ^ 2 := by positivity
        calc (64:ℝ) ^ (d - 1) * (d:ℝ) ^ 2 ≤ (2:ℝ) ^ (9 * d + 40) * (d:ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right h64 (by positivity)
          _ ≤ (2:ℝ) ^ (9 * d + 40) * (d:ℝ) ^ 2 * (d:ℝ) := by
              have hh := mul_le_mul_of_nonneg_left hdR1 (show (0:ℝ) ≤ (2:ℝ)^(9*d+40) * (d:ℝ)^2 by positivity)
              simpa using hh
          _ = (2:ℝ) ^ (9 * d + 40) * (d:ℝ) ^ 3 := by ring
      have h3 : 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * ((64:ℝ)^(d-1) * (d:ℝ)^2)
          ≤ 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * ((2:ℝ)^(9*d+40) * (d:ℝ)^3) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      calc 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (64:ℝ) ^ (d - 1) * (d : ℝ) ^ 2
          = 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * ((64:ℝ)^(d-1) * (d:ℝ)^2) := by ring
        _ ≤ 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * ((2:ℝ)^(9*d+40) * (d:ℝ)^3) := h3
        _ = 28800 * C' * (C' + 1) ^ 4 * 4 ^ (5 * K') * (2:ℝ) ^ (9 * d + 40) * (d : ℝ) ^ 3 := by ring
    rw [hK2def]
    linarith [hlt, hK2t1, hK2t3, hK2t4]
  have hK2one : 1 ≤ K2 := by
    have := hK2a; have h2 : (1:ℝ) ≤ (2:ℝ)^(d-1) := one_le_pow₀ (by norm_num)
    linarith
  have hK2pos : 0 < K2 := lt_of_lt_of_le zero_lt_one hK2one
  have hY' : (0:ℝ) ≤ (K2 + 1) ^ d / 2 :=
    div_nonneg (pow_nonneg (by linarith [hK2nn]) d) (by norm_num)
  have hAn : (0:ℝ) ≤ (2:ℝ)^20 * (24 * (C'+1)^2 * 4^(2*K')) := by positivity
  have hBn : (0:ℝ) ≤ (2:ℝ)^(9*d+70) * 24^4 * C' * (C'+1)^8 * 4^(9*K') * (d:ℝ)^3 := by positivity
  have hDn : (0:ℝ) ≤ (2:ℝ)^20 * 24 * (d:ℝ) * ((C'+1)^2 * 4^(2*K')) := by positivity
  have hC1 : 1 ≤ C := by
    have hsplit : C = 1 + ((K2 + 1) ^ d / 2 + (2:ℝ)^20 * (24 * (C'+1)^2 * 4^(2*K'))
        + (2:ℝ)^(9*d+70) * 24^4 * C' * (C'+1)^8 * 4^(9*K') * (d:ℝ)^3
        + (2:ℝ)^20 * 24 * (d:ℝ) * ((C'+1)^2 * 4^(2*K'))) := by
      rw [hCdef]; ring
    rw [hsplit]
    linarith [hY', hAn, hBn, hDn]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCdq : (2:ℝ) ^ 20 * 24 * (d : ℝ) * ((C' + 1) ^ 2 * 4 ^ (2 * K')) ≤ C := by
    have hsplit : C = (2:ℝ)^20 * 24 * (d:ℝ) * ((C'+1)^2 * 4^(2*K'))
        + (1 + (K2 + 1)^d/2 + (2:ℝ)^20 * (24 * (C'+1)^2 * 4^(2*K'))
          + (2:ℝ)^(9*d+70) * 24^4 * C' * (C'+1)^8 * 4^(9*K') * (d:ℝ)^3) := by
      rw [hCdef]; ring
    rw [hsplit]
    linarith [hY', hAn, hBn]
  have hCerr : (2:ℝ) ^ 39 * 24 ^ 4 * C' * (C' + 1) ^ 8 * 4 ^ (9 * K') * (64:ℝ) ^ (d - 1) * (d : ℝ) ^ 4 ≤ C := by
    have h64b : (64:ℝ) ^ (d - 1) * (d:ℝ) ≤ (2:ℝ) ^ (9 * d + 31) := by
      have h1 : (64:ℝ) ^ (d - 1) ≤ (2:ℝ) ^ (6 * d) := by
        calc (64:ℝ) ^ (d - 1) ≤ (64:ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = ((2:ℝ)^6) ^ d := by norm_num
          _ = (2:ℝ) ^ (6 * d) := by rw [← pow_mul]
      have h4 : (d:ℝ) ≤ (2:ℝ) ^ d := by
        have h5 : d < 2 ^ d := Nat.lt_two_pow_self
        exact_mod_cast h5.le
      have h3 : (d:ℝ) ≤ (2:ℝ) ^ (3*d+31) := le_trans h4 (pow_le_pow_right₀ (by norm_num) (by omega))
      calc (64:ℝ) ^ (d - 1) * (d:ℝ) ≤ (2:ℝ) ^ (6*d) * (2:ℝ) ^ (3*d+31) :=
            mul_le_mul h1 h3 (by positivity) (by positivity)
        _ = (2:ℝ) ^ (6*d + (3*d+31)) := by rw [← pow_add]
        _ = (2:ℝ) ^ (9 * d + 31) := by
            congr 1
            omega
    have hlt : (2:ℝ)^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * (64:ℝ)^(d-1) * (d:ℝ)^4
        ≤ (2:ℝ)^(9*d+70) * 24^4 * C' * (C'+1)^8 * 4^(9*K') * (d:ℝ)^3 := by
      have h1 : (64:ℝ) ^ (d - 1) * (d:ℝ) ^ 4 ≤ (2:ℝ) ^ (9 * d + 31) * (d:ℝ) ^ 3 := by
        calc (64:ℝ) ^ (d - 1) * (d:ℝ) ^ 4 = ((64:ℝ)^(d-1) * (d:ℝ)) * (d:ℝ)^3 := by ring
          _ ≤ (2:ℝ) ^ (9 * d + 31) * (d:ℝ)^3 := mul_le_mul_of_nonneg_right h64b (by positivity)
      have h3 : (2:ℝ)^39 * (2:ℝ) ^ (9 * d + 31) ≤ (2:ℝ) ^ (9*d+70) := by
        rw [← pow_add]
        apply pow_le_pow_right₀ (by norm_num)
        omega
      have h4 : (0:ℝ) ≤ 24^4 * C' * (C'+1)^8 * 4^(9*K') := by positivity
      calc (2:ℝ)^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * (64:ℝ)^(d-1) * (d:ℝ)^4
          = (24^4 * C' * (C'+1)^8 * 4^(9*K')) * ((2:ℝ)^39 * ((64:ℝ)^(d-1) * (d:ℝ)^4)) := by ring
        _ ≤ (24^4 * C' * (C'+1)^8 * 4^(9*K')) * ((2:ℝ)^(9*d+70) * (d:ℝ)^3) := by
            apply mul_le_mul_of_nonneg_left _ h4
            calc (2:ℝ)^39 * ((64:ℝ)^(d-1) * (d:ℝ)^4) ≤ (2:ℝ)^39 * ((2:ℝ)^(9*d+31) * (d:ℝ)^3) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = ((2:ℝ)^39 * (2:ℝ)^(9*d+31)) * (d:ℝ)^3 := by ring
              _ ≤ (2:ℝ)^(9*d+70) * (d:ℝ)^3 := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (2:ℝ)^(9*d+70)*24^4*C'*(C'+1)^8*4^(9*K')*(d:ℝ)^3 := by ring
    have hsplit : C = (2:ℝ)^(9*d+70)*24^4*C'*(C'+1)^8*4^(9*K')*(d:ℝ)^3
        + (1 + (K2+1)^d/2 + (2:ℝ)^20*(24*(C'+1)^2*4^(2*K'))
          + (2:ℝ)^20*24*(d:ℝ)*((C'+1)^2*4^(2*K'))) := by
      rw [hCdef]; ring
    rw [hsplit]
    linarith [hY', hAn, hDn, hlt]
  have hCK2 : (K2 + 1) ^ d ≤ 2 * C := by
    have hsplit : C = (K2 + 1)^d/2 + (1 + (2:ℝ)^20*(24*(C'+1)^2*4^(2*K'))
        + (2:ℝ)^(9*d+70)*24^4*C'*(C'+1)^8*4^(9*K')*(d:ℝ)^3
        + (2:ℝ)^20*24*(d:ℝ)*((C'+1)^2*4^(2*K'))) := by
      rw [hCdef]; ring
    have h1 : (K2 + 1)^d/2 ≤ C := by
      rw [hsplit]
      linarith [hAn, hBn, hDn]
    have h2 : (K2 + 1)^d = 2 * ((K2 + 1)^d / 2) := by ring
    linarith [h1, h2]
  have hM0a : 10 * K' + 2 * d + 2 ≤ M0 := by rw [hM0def]; exact le_max_left _ _
  have hM0b : 2 * K' + 2 ≤ M0 := by
    rw [hM0def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM0c : 2 * (d - 1) ≤ M0 := by
    rw [hM0def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hM0d : 2 * K' + 2 ≤ M0 := hM0b
  have hKa : d * M0 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKb : 2 * K' + 2 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKc : 18 * K' + 2 * d + 6 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKb3 : 4 * K' + 2 ≤ K := by
    have h1 : 4 * K' + 2 ≤ 18 * K' + 2 * d + 6 := by omega
    exact le_trans h1 hKc
  refine ⟨C, hCpos, K, ?_⟩
  intro F c a b η hFd hc hab hη0 hη1 hmain
  set L : ℝ := ((b - a : ℤ) : ℝ) + 1 with hL
  set NL : ℕ := (b + 1 - a).toNat with hNLdef
  have hNL : (NL : ℝ) = L := by
    rw [hNLdef, hL]
    have hNz : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg (by omega)
    have h1 : (((b + 1 - a).toNat : ℝ)) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast hNz
    have h2 : ((b + 1 - a : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by push_cast; ring
    rw [h1, h2]
  have hNL1 : 1 ≤ NL := by rw [hNLdef]; omega
  have hL1 : 1 ≤ L := by rw [← hNL]; exact_mod_cast hNL1
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have ht1 : 1 ≤ η⁻¹ := by rw [one_le_inv₀ hη0]; exact hη1
  have htpos : 0 < η⁻¹ := inv_pos.mpr hη0
  by_cases hcase : L ^ d ≤ 2 * C * (η⁻¹) ^ K
  · exact IW_trivial hC1 F a b η hη0 hη1 hab hcase
  · push_neg at hcase
    -- hcase : 2 * C * (η⁻¹) ^ K < L ^ d
    have hLbig : (K2 + 1) * (η⁻¹) ^ M0 ≤ L := by
      by_contra hcon
      push_neg at hcon
      have h1 : L ^ d < ((K2 + 1) * (η⁻¹) ^ M0) ^ d :=
        pow_lt_pow_left₀ hcon (by positivity) (by omega)
      have h2 : ((K2 + 1) * (η⁻¹) ^ M0) ^ d ≤ 2 * C * (η⁻¹) ^ K := by
        rw [mul_pow, ← pow_mul]
        have h4 : (η⁻¹) ^ (M0 * d) ≤ (η⁻¹) ^ K :=
          pow_le_pow_right₀ ht1 (by rw [Nat.mul_comm]; exact hKa)
        exact mul_le_mul hCK2 h4 (by positivity) (by positivity)
      linarith [hcase, h1, h2]
    have hLbd : K2 * (η⁻¹) ^ M0 ≤ L ^ (d - 1) := by
      have h1 : ((K2 + 1) * (η⁻¹) ^ M0) ^ (d - 1) ≤ L ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) hLbig (d - 1)
      have h2 : (K2 + 1) ^ (d - 1) * (η⁻¹) ^ (M0 * (d - 1)) ≤ ((K2 + 1) * (η⁻¹) ^ M0) ^ (d - 1) := by
        rw [mul_pow, ← pow_mul]
      have h3 : K2 ≤ (K2 + 1) ^ (d - 1) := by
        have h4 : (K2 + 1) ^ 1 ≤ (K2 + 1) ^ (d - 1) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        rw [pow_one] at h4
        linarith
      have h5 : (η⁻¹) ^ M0 ≤ (η⁻¹) ^ (M0 * (d - 1)) := by
        apply pow_le_pow_right₀ ht1
        have h6 : 1 ≤ d - 1 := by omega
        calc M0 = M0 * 1 := (Nat.mul_one M0).symm
          _ ≤ M0 * (d - 1) := Nat.mul_le_mul_left _ h6
      calc K2 * (η⁻¹) ^ M0 ≤ (K2 + 1) ^ (d - 1) * (η⁻¹) ^ (M0 * (d - 1)) :=
            mul_le_mul h3 h5 (by positivity) (by positivity)
        _ ≤ ((K2 + 1) * (η⁻¹) ^ M0) ^ (d - 1) := h2
        _ ≤ L ^ (d - 1) := h1
    by_cases hsmall2 : η ^ 2 * L < 2
    · exfalso
      have hLlt : L < 2 * (η⁻¹) ^ 2 := by
        have h2 : L < 2 / η ^ 2 := by
          rw [lt_div_iff₀ (by positivity : (0:ℝ) < η ^ 2)]
          linarith [hsmall2]
        have h3 : (2 : ℝ) / η ^ 2 = 2 * (η⁻¹) ^ 2 := by
          rw [inv_pow]; ring
        linarith [h2, h3.le]
      have hp : L ^ (d - 1) < (2 * (η⁻¹) ^ 2) ^ (d - 1) :=
        pow_lt_pow_left₀ hLlt (by positivity) (by omega)
      have hpe : (2 * (η⁻¹) ^ 2) ^ (d - 1) = 2 ^ (d - 1) * (η⁻¹) ^ (2 * (d - 1)) := by
        rw [mul_pow, ← pow_mul]
      have hM0le : (η⁻¹) ^ (2 * (d - 1)) ≤ (η⁻¹) ^ M0 := pow_le_pow_right₀ ht1 hM0c
      have hlt2 : K2 * (η⁻¹) ^ M0 < (2 : ℝ) ^ (d - 1) * (η⁻¹) ^ M0 := by
        calc K2 * (η⁻¹) ^ M0 ≤ L ^ (d - 1) := hLbd
          _ < (2 * (η⁻¹) ^ 2) ^ (d - 1) := hp
          _ = 2 ^ (d - 1) * (η⁻¹) ^ (2 * (d - 1)) := hpe
          _ ≤ 2 ^ (d - 1) * (η⁻¹) ^ M0 := mul_le_mul_of_nonneg_left hM0le (by positivity)
      have hK2lt : K2 < (2 : ℝ) ^ (d - 1) := by
        have hpos : 0 < (η⁻¹) ^ M0 := by positivity
        nlinarith [hlt2, hpos]
      linarith [hK2lt, hK2a]
    · push_neg at hsmall2
      have hL2 : 2 ≤ L := by
        have h1 : η ^ 2 * L ≤ 1 * L := by
          apply mul_le_mul_of_nonneg_right _ hLpos.le
          nlinarith [hη0.le, hη1]
        linarith [hsmall2, h1]
      obtain ⟨H, hHne, hHcard1, hHcard2, hHsum⟩ :=
        vdcPlainMathlib a b (fun n => c * ee (F.eval (n : ℝ))) η hab hη0
          (by rw [← hL]; exact hsmall2)
          (fun n => by simp [norm_mul, hc, ee_norm]) hmain
      have hHrange : ∀ h ∈ H, -(b - a) ≤ h ∧ h ≤ b - a := by
        intro h hh
        have hpos1 : (0:ℝ) < η ^ 2 / 64 * L := by positivity
        constructor
        · by_contra hcon
          push_neg at hcon
          have h1 : max a (a - h) = a - h := max_eq_right (by omega)
          have h2 : min b (b - h) = b := min_eq_left (by omega)
          have hcard0 : (Finset.Icc (max a (a - h)) (min b (b - h))).card = 0 := by
            rw [Int.card_Icc]
            have hle : (min b (b - h)) + 1 - (max a (a - h)) ≤ 0 := by rw [h1, h2]; omega
            exact Int.toNat_eq_zero.mpr hle
          have h4 := hHcard1 h hh
          rw [hcard0] at h4
          simp only [Nat.cast_zero] at h4
          linarith
        · by_contra hcon
          push_neg at hcon
          have h1 : max a (a - h) = a := max_eq_left (by omega)
          have h2 : min b (b - h) = b - h := min_eq_right (by omega)
          have hcard0 : (Finset.Icc (max a (a - h)) (min b (b - h))).card = 0 := by
            rw [Int.card_Icc]
            have hle : (min b (b - h)) + 1 - (max a (a - h)) ≤ 0 := by rw [h1, h2]; omega
            exact Int.toNat_eq_zero.mpr hle
          have h4 := hHcard1 h hh
          rw [hcard0] at h4
          simp only [Nat.cast_zero] at h4
          linarith
      have hHcard : η ^ 2 * L / 8 ≤ (H.card : ℝ) := by
        have hJle : ∀ h ∈ H,
            ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ≤ L := by
          intro h _
          have hsub : Finset.Icc (max a (a - h)) (min b (b - h)) ⊆ Finset.Icc a b := by
            intro x hx
            rw [Finset.mem_Icc] at hx ⊢
            exact ⟨le_trans (le_max_left _ _) hx.1, le_trans hx.2 (min_le_left _ _)⟩
          have h2 : ((Finset.Icc a b).card : ℝ) = L := by
            have hc1 : (Finset.Icc (a:ℤ) b).card = NL := by
              rw [Int.card_Icc, hNLdef]
            rw [hc1, hNL]
          calc ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)
              ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
            _ = L := h2
        have hs : ∑ h ∈ H, ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)
            ≤ (H.card : ℝ) * L := by
          calc ∑ h ∈ H, ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)
              ≤ ∑ h ∈ H, L := Finset.sum_le_sum hJle
            _ = (H.card : ℝ) * L := by rw [Finset.sum_const, nsmul_eq_mul]
        have h3 : η ^ 2 / 8 * L ^ 2 ≤ (H.card : ℝ) * L := le_trans hHcard2 hs
        have h4 : η ^ 2 * L / 8 ≤ (H.card : ℝ) := by
          have h5 : (η ^ 2 / 8 * L ^ 2) = η ^ 2 * L / 8 * L := by ring
          rw [h5] at h3
          exact le_of_mul_le_mul_right h3 hLpos
        exact h4
      -- ## opaque atoms for the numerical quantities
      set T0 : ℝ := η⁻¹ with hT0def
      set P1 : ℝ := (4 * T0 ^ 2) ^ K' with hP1def
      set P2 : ℝ := (64 * T0 ^ 2) ^ (d - 1) with hP2def
      set B : ℝ := (C' + 1) * P1 with hBdef
      set Edelta : ℝ := C' * P1 * P2 / L ^ (d - 1) with hEdef
      have hT0pos : 0 < T0 := by rw [hT0def]; exact htpos
      have hT01 : 1 ≤ T0 := by rw [hT0def]; exact ht1
      have hηT0 : η * T0 = 1 := by rw [hT0def]; exact mul_inv_cancel₀ (ne_of_gt hη0)
      have hη2 : η ^ 2 = (T0 ^ 2)⁻¹ := by rw [hT0def, inv_pow]; simp
      have hinvη2 : (1 : ℝ) / η ^ 2 = T0 ^ 2 := by rw [hη2]; simp
      have hP1pos : 0 < P1 := by rw [hP1def]; positivity
      have hP11 : 1 ≤ P1 := by
        rw [hP1def]; apply one_le_pow₀; nlinarith only [hT01]
      have hP2pos : 0 < P2 := by rw [hP2def]; positivity
      have hBpos : 0 < B := by rw [hBdef]; positivity
      have hEpos : 0 < Edelta := by rw [hEdef]; positivity
      -- ## the per-shift induction hypothesis
      have hlast2 : 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4
            * T0^(18*K'+2*d+6) / L^d ≤ C * T0^K / L^d := by
        have h6 : T0^(18*K'+2*d+6) ≤ T0^K := pow_le_pow_right₀ hT01 hKc
        have h7 : 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4 ≤ C := hCerr
        have hAB2 : 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4 * T0^(18*K'+2*d+6)
            ≤ C * T0^K := by
          calc 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4 * T0^(18*K'+2*d+6)
              ≤ C * T0^(18*K'+2*d+6) := mul_le_mul_of_nonneg_right h7 (by positivity)
            _ ≤ C * T0^K := mul_le_mul_of_nonneg_left h6 hCpos.le
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hAB2 (inv_nonneg.mpr (pow_nonneg hLpos.le d))
      have hstep : ∀ h : ℤ, h ∈ H → ∃ p : ℕ × ℤ,
          (1 ≤ p.1) ∧ ((p.1 : ℝ) ≤ C' * P1) ∧
          |((p.1 : ℝ)) * ((h : ℝ) * (d : ℝ) * F.leadingCoeff) - ((p.2 : ℤ) : ℝ)| ≤ Edelta := by
        intro h hh
        have hne : h ≠ 0 := hHne h hh
        have hneR : (h : ℝ) ≠ 0 := by exact_mod_cast hne
        set Fh : Polynomial ℝ := F - F.comp (Polynomial.X + Polynomial.C (h : ℝ)) with hFh
        obtain ⟨hdeg, hcoe⟩ := coeff_comp_add_C_sub_R F d hFd hd1 (h : ℝ) hneR
        have hFdc : F.coeff d = F.leadingCoeff := by rw [Polynomial.leadingCoeff, hFd]
        have hleadFh : Fh.leadingCoeff = -((h : ℝ) * (d : ℝ) * F.leadingCoeff) := by
          rw [Polynomial.leadingCoeff, hdeg, hcoe, hFdc]
        have hJhcard : η ^ 2 / 4 * ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)
            ≤ ‖∑ n ∈ Finset.Icc (max a (a - h)) (min b (b - h)), ee (Fh.eval (n : ℝ))‖ := by
          have hS := hHsum h hh
          have hsub : ∀ n : ℤ, (c * ee (F.eval (n : ℝ))) * star (c * ee (F.eval ((n + h : ℤ) : ℝ)))
              = ee (Fh.eval (n : ℝ)) := by
            intro n; rw [hFh]; exact ee_corr F c hc h n
          rw [Finset.sum_congr rfl (fun n _ => hsub n)] at hS
          exact hS
        have hJne : (Finset.Icc (max a (a - h)) (min b (b - h))).Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          have h1 := hHcard1 h hh
          rw [hempty] at h1
          simp only [Finset.card_empty, Nat.cast_zero] at h1
          have h2 : (0:ℝ) < η ^ 2 / 64 * L := by positivity
          linarith
        have hle : max a (a - h) ≤ min b (b - h) := by
          obtain ⟨x, hx⟩ := hJne
          exact le_trans (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2
        have hJhlen : (((min b (b - h) - max a (a - h) : ℤ)) : ℝ) + 1
            = ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) := Icc_card_cast hle
        obtain ⟨qh, hqh1, hqhQ, mh, hmh⟩ :=
          hIW Fh 1 (max a (a - h)) (min b (b - h)) (η ^ 2 / 4) hdeg (by norm_num) hle
            (by positivity) (by nlinarith only [hη1, hη0.le]) (by rw [hJhlen]; simpa using hJhcard)
        have hηh : (η ^ 2 / 4)⁻¹ = 4 * T0 ^ 2 := by
          rw [hT0def, inv_div, inv_pow]
          ring
        rw [hηh, ← hP1def, hJhlen] at hmh
        rw [hηh, ← hP1def] at hqhQ
        refine ⟨(qh, -mh), hqh1, hqhQ, ?_⟩
        have hineq : L / (64 * T0 ^ 2)
            ≤ ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) := by
          have h1 := hHcard1 h hh
          have h2 : η ^ 2 / 64 * L = L / (64 * T0 ^ 2) := by
            rw [hη2]
            ring
          linarith [h1, h2.le, h2.ge]
        have hpos1 : (0:ℝ) < L / (64 * T0 ^ 2) := by positivity
        have hkey2 : (1 : ℝ) / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ^ (d - 1)
            ≤ P2 / L ^ (d - 1) := by
          have h3 : (1 : ℝ) / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)
              ≤ 64 * T0 ^ 2 / L := by
            rw [one_div, ← inv_div]
            exact inv_anti₀ hpos1 hineq
          have h4 : (1 / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)) ^ (d - 1)
              ≤ (64 * T0 ^ 2 / L) ^ (d - 1) :=
            pow_le_pow_left₀ (by positivity) h3 (d - 1)
          have hone : (1 : ℝ) / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ^ (d - 1)
              = (1 / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ)) ^ (d - 1) := by
            rw [div_pow, one_pow]
          rw [hone, hP2def, ← div_pow]
          exact h4
        have hmh' : |(qh : ℝ) * (-((h : ℝ) * (d : ℝ) * F.leadingCoeff)) - (mh : ℝ)| ≤ Edelta := by
          rw [← hleadFh]
          refine le_trans hmh ?_
          rw [hEdef]
          have h5 : C' * P1
              / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ^ (d - 1)
              = C' * P1 * (1 / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ^ (d - 1)) := by
            ring
          rw [h5]
          have h6 : (0:ℝ) ≤ C' * P1 := by positivity
          calc C' * P1 * (1 / ((Finset.Icc (max a (a - h)) (min b (b - h))).card : ℝ) ^ (d - 1))
              ≤ C' * P1 * (P2 / L ^ (d - 1)) := mul_le_mul_of_nonneg_left hkey2 h6
            _ = C' * P1 * P2 / L ^ (d - 1) := by ring
        have hfin : |(qh : ℝ) * ((h : ℝ) * (d : ℝ) * F.leadingCoeff) - ((-mh : ℤ) : ℝ)| ≤ Edelta := by
          have h4 : |(qh : ℝ) * ((h : ℝ) * (d : ℝ) * F.leadingCoeff) - ((-mh : ℤ) : ℝ)|
              = |(qh : ℝ) * (-((h : ℝ) * (d : ℝ) * F.leadingCoeff)) - (mh : ℝ)| := by
            have h1' : ((-mh : ℤ) : ℝ) = -(mh : ℝ) := by push_cast; ring
            rw [h1']
            have h2' : (qh : ℝ) * ((h : ℝ) * (d : ℝ) * F.leadingCoeff) - (-(mh : ℝ))
                = -((qh : ℝ) * (-((h : ℝ) * (d : ℝ) * F.leadingCoeff)) - (mh : ℝ)) := by ring
            rw [h2', abs_neg]
          rw [h4]
          exact hmh'
        exact hfin
      let pf : ℤ → ℕ × ℤ := fun h => if hh : h ∈ H then Classical.choose (hstep h hh) else (1, 0)
      have hpf : ∀ h ∈ H, (1 ≤ (pf h).1) ∧ (((pf h).1 : ℝ) ≤ C' * P1) ∧
          |(((pf h).1 : ℝ)) * ((h : ℝ) * (d : ℝ) * F.leadingCoeff) - (((pf h).2 : ℤ) : ℝ)| ≤ Edelta := by
        intro h hh
        have h1 : pf h = Classical.choose (hstep h hh) := by simp only [pf, dif_pos hh]
        rw [h1]
        exact Classical.choose_spec (hstep h hh)
      -- ## pigeonhole
      set Q1 : ℕ := ⌈C' * P1⌉₊ with hQ1def
      have hQ1pos : 1 ≤ Q1 := by
        rw [hQ1def]
        have h : 0 < ⌈C' * P1⌉₊ := Nat.ceil_pos.mpr (by positivity)
        omega
      have hQ1b : ((Q1 : ℕ) : ℝ) ≤ B := by
        rw [hQ1def, hBdef]
        have h1 : (((⌈C' * P1⌉₊ : ℕ) : ℝ)) < C' * P1 + 1 :=
          Nat.ceil_lt_add_one (le_of_lt (by positivity))
        nlinarith [h1, hP11, hC']
      obtain ⟨q, hq1, hqQ, T, hTH, hTcard, hTq⟩ :=
        exists_common_value (H := H) (Q := Q1) hQ1pos (fun h => (pf h).1) (fun h hh => by
          have hp := hpf h hh
          exact ⟨hp.1, by
            have h2 : ((pf h).1 : ℝ) ≤ C' * P1 := hp.2.1
            have h3 : C' * P1 ≤ (Q1 : ℝ) := by rw [hQ1def]; exact Nat.le_ceil _
            exact_mod_cast le_trans h2 h3⟩)
      have hqB : (q : ℝ) ≤ B := le_trans (by exact_mod_cast hqQ) hQ1b
      have hTnon : T.Nonempty := by
        have h1 : (0:ℝ) < (T.card : ℝ) := by
          have h2 : (0:ℝ) < (H.card : ℝ) / (Q1 : ℝ) := by
            have h3 : (0:ℝ) < (H.card : ℝ) := by
              have h4 : (0:ℝ) < η ^ 2 * L / 8 := by positivity
              linarith [hHcard]
            positivity
          have h5 : (H.card : ℝ) / (Q1 : ℝ) ≤ (T.card : ℝ) := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (Q1:ℝ))]
            linarith [hTcard]
          linarith
        exact Finset.card_pos.mp (by exact_mod_cast h1)
      -- ## the amplified set
      set T2 : Finset ℤ := T.image (fun h => (d : ℤ) * (q : ℤ) * h) with hT2
      set N2 : ℕ := d * q * NL with hN2
      have hT2card : T2.card = T.card := by
        rw [hT2]
        apply Finset.card_image_of_injective
        intro x y hxy
        have hdq : ((d : ℤ) * (q : ℤ)) ≠ 0 := by
          have h1 : (1:ℤ) ≤ (q:ℤ) := by exact_mod_cast hq1
          have h2 : (2:ℤ) ≤ (d:ℤ) := by exact_mod_cast hd
          nlinarith
        exact mul_left_cancel₀ hdq hxy
      have hT2sub : ∀ n ∈ T2, -(N2 : ℤ) ≤ n ∧ n ≤ (N2 : ℤ) := by
        intro n hn
        rw [hT2] at hn
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
        have hrange := hHrange h (hTH hh)
        have h8 : |h| ≤ b - a := abs_le.mpr hrange
        have h9 : (NL : ℤ) = b + 1 - a := by
          rw [hNLdef]; exact Int.toNat_of_nonneg (by omega)
        have h10 : |h| ≤ (NL : ℤ) := by omega
        have hd0 : (0 : ℤ) ≤ (d : ℤ) := by omega
        have hq0 : (0 : ℤ) ≤ (q : ℤ) := by omega
        have h6 : |(d : ℤ) * (q : ℤ) * h| ≤ (N2 : ℤ) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg hq0]
          have h11 : (d : ℤ) * (q : ℤ) * |h| ≤ (d : ℤ) * (q : ℤ) * (NL : ℤ) :=
            mul_le_mul_of_nonneg_left h10 (mul_nonneg hd0 hq0)
          have h12 : (d : ℤ) * (q : ℤ) * (NL : ℤ) = (N2 : ℤ) := by
            rw [hN2]; push_cast; ring
          linarith [h11, h12.le, h12.ge]
        exact abs_le.mp h6
      set Dd : ℝ := (T2.card : ℝ) / (2 * (N2 : ℝ) + 1) with hDd
      have hDdpos : 0 < Dd := by
        rw [hDd]
        have h1 : (0 : ℝ) < (T2.card : ℝ) := by
          rw [hT2card]
          exact_mod_cast Finset.card_pos.mpr hTnon
        positivity
      have hDdcard : Dd * (2 * (N2 : ℝ) + 1) = (T2.card : ℝ) := by
        rw [hDd]; field_simp
      have hDdle : Dd ≤ 1 := by
        have h1 : (T2.card : ℝ) ≤ 2 * (N2 : ℝ) + 1 := by
          have h2 : T2 ⊆ Finset.Icc (-(N2 : ℤ)) (N2 : ℤ) := fun x hx => Finset.mem_Icc.mpr (hT2sub x hx)
          have h3 := Finset.card_le_card h2
          have h4 : ((Finset.Icc (-(N2 : ℤ)) (N2 : ℤ)).card : ℝ) = 2 * (N2 : ℝ) + 1 := by
            rw [Int.card_Icc]
            have h5 : ((N2 : ℤ) + 1 - (-(N2 : ℤ))).toNat = 2 * N2 + 1 := by
              rw [show (N2 : ℤ) + 1 - (-(N2 : ℤ)) = ((2 * N2 + 1 : ℕ) : ℤ) by push_cast; ring]
              exact Int.toNat_natCast _
            rw [h5]
            push_cast
            ring
          calc (T2.card : ℝ) ≤ ((Finset.Icc (-(N2 : ℤ)) (N2 : ℤ)).card : ℝ) := by exact_mod_cast h3
            _ = 2 * (N2 : ℝ) + 1 := h4
        rw [hDd, div_le_one (by positivity)]
        exact h1
      have hDdlow : η ^ 2 / (24 * B ^ 2 * (d : ℝ)) ≤ Dd := by
        have h6 : ((T2.card : ℕ) : ℝ) = (T.card : ℝ) := by rw [hT2card]
        have h1 : η ^ 2 * L / 8 ≤ B * (T2.card : ℝ) := by
          calc η ^ 2 * L / 8 ≤ (H.card : ℝ) := hHcard
            _ ≤ (Q1 : ℝ) * (T.card : ℝ) := hTcard
            _ ≤ B * (T.card : ℝ) := mul_le_mul_of_nonneg_right hQ1b (by positivity)
            _ = B * (T2.card : ℝ) := by rw [h6]
        have h7 : (1 : ℝ) ≤ (d : ℝ) * (q : ℝ) * L := by
          have h8 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
          have h9 : (1 : ℝ) ≤ (d : ℝ) := hdR1
          have h10 : (1 : ℝ) ≤ L := hL1
          have h11 : (1:ℝ) * 1 ≤ (d:ℝ) * (q:ℝ) := mul_le_mul h9 h8 (by norm_num) (by linarith)
          have h12 : ((1:ℝ) * 1) * 1 ≤ ((d:ℝ) * (q:ℝ)) * L :=
            mul_le_mul h11 h10 (by norm_num) (by positivity)
          simpa using h12
        have h2 : 2 * (N2 : ℝ) + 1 ≤ 3 * ((d : ℝ) * (q : ℝ) * L) := by
          have hN2int : (N2 : ℝ) = (d : ℝ) * (q : ℝ) * (NL : ℝ) := by rw [hN2]; push_cast; ring
          rw [hN2int, hNL]
          linarith [h7]
        rw [hDd, le_div_iff₀ (by positivity : (0:ℝ) < 2 * (N2 : ℝ) + 1)]
        have hX : 0 ≤ η ^ 2 / (24 * B ^ 2 * (d : ℝ)) := by positivity
        have hstep2 : η ^ 2 / (24 * B ^ 2 * (d : ℝ)) * (3 * ((d : ℝ) * (q : ℝ) * L))
            = η ^ 2 * L / 8 / B * ((q : ℝ) / B) := by
          field_simp
          ring
        have hqB' : (q : ℝ) / B ≤ 1 := by
          rw [div_le_one hBpos]; exact hqB
        have h4 : η ^ 2 * L / 8 / B * ((q : ℝ) / B) ≤ η ^ 2 * L / 8 / B := by
          calc η ^ 2 * L / 8 / B * ((q : ℝ) / B)
              ≤ η ^ 2 * L / 8 / B * 1 := mul_le_mul_of_nonneg_left hqB' (by positivity)
            _ = η ^ 2 * L / 8 / B := by ring
        have h5 : η ^ 2 * L / 8 / B ≤ (T2.card : ℝ) := by
          rw [div_le_iff₀ hBpos]
          linarith [h1]
        calc η ^ 2 / (24 * B ^ 2 * (d : ℝ)) * (2 * (N2 : ℝ) + 1)
            ≤ η ^ 2 / (24 * B ^ 2 * (d : ℝ)) * (3 * ((d : ℝ) * (q : ℝ) * L)) :=
              mul_le_mul_of_nonneg_left h2 hX
          _ = η ^ 2 * L / 8 / B * ((q : ℝ) / B) := hstep2
          _ ≤ η ^ 2 * L / 8 / B := h4
          _ ≤ (T2.card : ℝ) := h5
      have hP1le : P1 ≤ 4^(K') * T0^(2*K') := by
        rw [hP1def, mul_pow, ← pow_mul]
      have hP2le : P2 ≤ 64^(d-1) * T0^(2*(d-1)) := by
        rw [hP2def, mul_pow, ← pow_mul]
      have hXpos : (0:ℝ) < η^2/(24*B^2*(d:ℝ)) := by positivity
      have hη8 : (1:ℝ)/η^8 = T0^8 := by
        rw [div_eq_iff (by positivity : (η:ℝ)^8 ≠ 0), mul_comm, ← mul_pow, hηT0, one_pow]
      have hinvX : (1:ℝ)/(η^2/(24*B^2*(d:ℝ)))^4 = 24^4*B^8*(d:ℝ)^4*T0^8 := by
        have h2 : (η^2)^4 * T0^8 = 1 := by
          have h2a : T0^8 = (T0^2)^4 := by rw [← pow_mul]
          rw [h2a, ← mul_pow, show η^2 * T0^2 = (η*T0)^2 by ring, hηT0]
          norm_num
        rw [div_pow, one_div_div, div_eq_iff (by positivity : ((η^2)^4 : ℝ) ≠ 0)]
        rw [show 24^4*B^8*(d:ℝ)^4*T0^8*((η^2)^4) = 24^4*B^8*(d:ℝ)^4*(T0^8*((η^2)^4)) by ring]
        rw [show T0^8*((η^2)^4) = 1 by rw [mul_comm]; exact h2]
        rw [mul_one, mul_pow, mul_pow]
        ring
      have hmaster : 28800 * C' * (C'+1)^4 * P1^5 * P2 * (d:ℝ)^2 * T0^4 ≤ L^(d-1) := by
        have h0 : 28800 * C' * (C'+1)^4 * 4^(5*K') * 64^(d-1) * (d:ℝ)^2 * T0^(10*K'+2*d+2) ≤ L^(d-1) := by
          have h1 : 28800 * C' * (C'+1)^4 * 4^(5*K') * 64^(d-1) * (d:ℝ)^2 ≤ K2 := hK2c
          have h2 : T0^(10*K'+2*d+2) ≤ T0^M0 := pow_le_pow_right₀ hT01 hM0a
          exact le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) hLbd
        have h3 : P1^5 * P2 * T0^4 ≤ 4^(5*K') * 64^(d-1) * T0^(10*K'+2*d+2) := by
          have h4 : P1^5 ≤ 4^(5*K') * T0^(10*K') := by
            calc P1^5 ≤ (4^(K') * T0^(2*K'))^5 := pow_le_pow_left₀ (by positivity) hP1le 5
              _ = 4^(5*K') * T0^(10*K') := by
                  rw [mul_pow, ← pow_mul, ← pow_mul]
                  congr 1 <;> congr 1 <;> omega
          have h5 : T0^(10*K') * (64^(d-1) * T0^(2*(d-1))) * T0^4
              ≤ 64^(d-1) * T0^(10*K' + 2*d + 2) := by
            have h6 : T0^(10*K') * (64^(d-1) * T0^(2*(d-1))) * T0^4
                = 64^(d-1) * T0^(10*K' + (2*(d-1) + 4)) := by
              rw [show T0^(10*K') * (64^(d-1) * T0^(2*(d-1))) * T0^4
                  = 64^(d-1) * (T0^(10*K') * T0^(2*(d-1)) * T0^4) by ring]
              rw [← pow_add, ← pow_add]
              congr 1
            rw [h6]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply pow_le_pow_right₀ hT01
            omega
          calc P1^5 * P2 * T0^4
              ≤ (4^(5*K') * T0^(10*K')) * (64^(d-1) * T0^(2*(d-1))) * T0^4 := by
                apply mul_le_mul (mul_le_mul h4 hP2le (by positivity) (by positivity))
                  (le_refl _) (by positivity) (by positivity)
            _ = 4^(5*K') * (T0^(10*K') * (64^(d-1) * T0^(2*(d-1))) * T0^4) := by ring
            _ ≤ 4^(5*K') * (64^(d-1) * T0^(10*K' + 2*d + 2)) :=
                mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = 4^(5*K') * 64^(d-1) * T0^(10*K'+2*d+2) := by ring
        calc 28800 * C' * (C'+1)^4 * P1^5 * P2 * (d:ℝ)^2 * T0^4
            = (28800 * C' * (C'+1)^4 * (d:ℝ)^2) * (P1^5 * P2 * T0^4) := by ring
          _ ≤ (28800 * C' * (C'+1)^4 * (d:ℝ)^2) * (4^(5*K') * 64^(d-1) * T0^(10*K'+2*d+2)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = 28800 * C' * (C'+1)^4 * 4^(5*K') * 64^(d-1) * (d:ℝ)^2 * T0^(10*K'+2*d+2) := by ring
          _ ≤ L^(d-1) := h0
      have hDdsmall : 50 * Edelta ≤ Dd ^ 2 := by
        have h1 : (η^2/(24*B^2*(d:ℝ)))^2 ≤ Dd^2 := pow_le_pow_left₀ hXpos.le hDdlow 2
        have h2 : 50 * Edelta ≤ (η^2/(24*B^2*(d:ℝ)))^2 := by
          have hX2 : (0:ℝ) < (η^2/(24*B^2*(d:ℝ)))^2 := by positivity
          rw [hEdef, mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < L^(d-1))]
          have hkey : 50 * (C'*P1*P2) * (24*B^2*(d:ℝ))^2 ≤ η^4 * L^(d-1) := by
            have h3 : 50 * (C'*P1*P2) * (24*B^2*(d:ℝ))^2
                = η^4 * (28800 * C' * (C'+1)^4 * P1^5 * P2 * (d:ℝ)^2 * T0^4) := by
              have hη4 : η^4 * T0^4 = 1 := by rw [← mul_pow, hηT0, one_pow]
              rw [hBdef]
              rw [show η^4 * (28800 * C' * (C'+1)^4 * P1^5 * P2 * (d:ℝ)^2 * T0^4)
                  = (η^4 * T0^4) * (28800 * C' * (C'+1)^4 * P1^5 * P2 * (d:ℝ)^2) by ring]
              rw [hη4, one_mul]
              ring
            rw [h3]
            have h4 : η^4 * T0^4 = 1 := by rw [← mul_pow, hηT0, one_pow]
            have h5 := mul_le_mul_of_nonneg_left hmaster (by positivity : (0:ℝ) ≤ η^4)
            nlinarith only [h5, h4]
          have hX2' : (η^2/(24*B^2*(d:ℝ)))^2 = (η^2)^2/((24*B^2*(d:ℝ))^2) := by rw [div_pow]
          rw [hX2', div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (24*B^2*(d:ℝ))^2)]
          have hη4 : (η^2)^2 = η^4 := by rw [← pow_mul]
          rw [hη4]
          exact hkey
        linarith only [h1, h2]
      have hDddens : 1 ≤ Dd * ((N2 : ℝ) + 1) := by
        have hB2v : B^2 = (C'+1)^2 * 4^(2*K') * T0^(4*K') := by
          rw [hBdef, hP1def, mul_pow, ← pow_mul]
          ring
        have hLbig' : 24 * (C'+1)^2 * 4^(2*K') * T0^(4*K'+2) ≤ L := by
          have h1 : 24 * (C'+1)^2 * 4^(2*K') ≤ K2 + 1 := by
            have h1a : 24 * (C'+1)^2 * 4^(2*K') ≤ 24 * (d:ℝ) * (C'+1)^2 * 4^(2*K') := by
              have h1b : (1:ℝ) ≤ (d:ℝ) := hdR1
              nlinarith only [h1b, show (0:ℝ) ≤ 24 * (C'+1)^2 * 4^(2*K') by positivity]
            linarith only [h1a, hK2b]
          have h2 : T0^(4*K'+2) ≤ T0^M0 := pow_le_pow_right₀ hT01 (by omega)
          calc 24 * (C'+1)^2 * 4^(2*K') * T0^(4*K'+2)
              ≤ (K2+1) * T0^(4*K'+2) := mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ (K2+1) * T0^M0 := mul_le_mul_of_nonneg_left h2 (by positivity)
            _ ≤ L := hLbig
        have h9 : (1:ℝ) ≤ (N2:ℝ) * (η^2/(24*B^2*(d:ℝ))) := by
          have hN2eq : (N2:ℝ) = (d:ℝ)*(q:ℝ)*L := by
            have hN2int : (N2 : ℝ) = (d : ℝ) * (q : ℝ) * (NL : ℝ) := by rw [hN2]; push_cast; ring
            rw [hN2int, hNL]
          have hB2pos : (0:ℝ) < 24*B^2*(d:ℝ)*T0^2 := by
            have h1 : (0:ℝ) < B^2 := by rw [hBdef]; positivity
            have h2 : (0:ℝ) < T0^2 := by positivity
            have h3 : (0:ℝ) < (d:ℝ) := by linarith only [hdR1]
            positivity
          have hX' : η^2/(24*B^2*(d:ℝ)) = 1/(24*B^2*(d:ℝ)*T0^2) := by
            rw [hη2, inv_pow]
            ring
          rw [hX', hN2eq, mul_one_div, le_div_iff₀ hB2pos]
          rw [hB2v]
          have h10 : 24 * (C'+1)^2 * 4^(2*K') * T0^(4*K'+2) ≤ L := hLbig'
          have h11 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
          have h12 : (1:ℝ) ≤ (d:ℝ) := hdR1
          have h13 : T0^(4*K') * T0^2 = T0^(4*K'+2) := by rw [← pow_add]
          have hkey : 1 * (24 * ((C'+1)^2 * 4^(2*K') * T0^(4*K')) * (d:ℝ) * T0^2)
              = (24 * (C'+1)^2 * 4^(2*K') * T0^(4*K'+2)) * (d:ℝ) := by rw [← h13]; ring
          rw [hkey]
          have h16 : 24 * (C'+1)^2 * 4^(2*K') * T0^(4*K'+2) * (d:ℝ) * (q:ℝ)
              ≤ L * (d:ℝ) * (q:ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h10 (by positivity)) (by positivity)
          have h17 : (0:ℝ) ≤ 24 * (C'+1)^2 * 4^(2*K') * T0^(4*K'+2) * (d:ℝ) := by positivity
          nlinarith only [h16, h11, h12, h17]
        have h14 : Dd * (N2:ℝ) ≤ Dd * ((N2:ℝ)+1) := by
          apply mul_le_mul_of_nonneg_left _ hDdpos.le
          linarith
        calc (1:ℝ) ≤ (N2:ℝ) * (η^2/(24*B^2*(d:ℝ))) := h9
          _ = (η^2/(24*B^2*(d:ℝ))) * (N2:ℝ) := by ring
          _ ≤ Dd * (N2:ℝ) := mul_le_mul_of_nonneg_right hDdlow (by positivity)
          _ ≤ Dd * ((N2:ℝ)+1) := h14
      have hDdgood : ∀ n ∈ T2, ∃ m : ℤ, |F.leadingCoeff * (n : ℝ) - (m : ℝ)| ≤ Edelta := by
        intro n hn
        obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp (by rwa [hT2] at hn)
        have hp := hpf a0 (hTH ha0)
        have hqt := hTq a0 ha0
        refine ⟨(pf a0).2, ?_⟩
        have h1 : ((pf a0).1 : ℝ) = (q : ℝ) := by rw [hqt]
        have h2 : F.leadingCoeff * (((d : ℤ) * (q : ℤ) * a0 : ℤ) : ℝ)
            = ((pf a0).1 : ℝ) * ((a0 : ℝ) * (d : ℝ) * F.leadingCoeff) := by
          rw [h1]; push_cast; ring
        rw [h2]
        exact hp.2.2
      have hN2one : 1 ≤ N2 := by
        rw [hN2]
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      obtain ⟨q', hq'1, hq'le, a', ha'⟩ :=
        hAmp F.leadingCoeff Edelta Dd N2 T2 hN2one hEpos hDdpos hDdle hDdsmall hDddens hT2sub
          (le_of_eq hDdcard) hDdgood
      refine ⟨q', hq'1, ?_, round ((q' : ℝ) * F.leadingCoeff), ?_⟩
      · have h1 : (q' : ℝ) ≤ (2:ℝ)^20 / Dd := hq'le
        have h1D : 1 / Dd ≤ 24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') * T0 ^ (4 * K' + 2) := by
          have h2 := one_div_le_one_div_of_le hXpos hDdlow
          have h2b : 1 / (η^2/(24*B^2*(d:ℝ))) = 24 * B^2 * (d:ℝ) / η^2 := by rw [one_div_div]
          rw [h2b] at h2
          have h3 : 24 * B ^ 2 * (d : ℝ) / η ^ 2
              = 24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') * T0 ^ (4 * K' + 2) := by
            have h1 : ((C'+1)*P1)^2 = (C'+1)^2 * 4^(2*K') * T0^(4*K') := by
              rw [hP1def, mul_pow]
              rw [show ((4*T0^2)^K')^2 = 4^(2*K') * T0^(4*K') by
                rw [← pow_mul, mul_pow, ← pow_mul]
                congr 1 <;> congr 1 <;> ring]
              ring
            rw [div_eq_mul_inv, ← one_div, hinvη2, hBdef, h1]
            rw [show 24 * ((C'+1)^2 * 4^(2*K') * T0^(4*K')) * (d:ℝ) * T0^2
                = 24 * (d:ℝ) * (C'+1)^2 * 4^(2*K') * (T0^(4*K') * T0^2) by ring]
            rw [show T0^(4*K') * T0^2 = T0^(4*K'+2) by rw [← pow_add]]
          rw [h3] at h2
          exact h2
        have h2 : (2:ℝ)^20 / Dd ≤ (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) * T0 ^ (4 * K' + 2) := by
          have h3 : (2:ℝ)^20 / Dd = (2:ℝ)^20 * (1 / Dd) := by ring
          rw [h3]
          have h4 : (2:ℝ)^20 * (1 / Dd)
              ≤ (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') * T0 ^ (4 * K' + 2)) :=
            mul_le_mul_of_nonneg_left h1D (by positivity : (0:ℝ) ≤ (2:ℝ)^20)
          rw [show (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K') * T0 ^ (4 * K' + 2))
              = (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) * T0 ^ (4 * K' + 2) by ring] at h4
          exact h4
        have h3 : (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) * T0 ^ (4 * K' + 2)
            ≤ C * T0 ^ K := by
          have h4 : T0 ^ (4 * K' + 2) ≤ T0 ^ K := pow_le_pow_right₀ hT01 hKb3
          calc (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) * T0 ^ (4 * K' + 2)
              ≤ (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) * T0 ^ K :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
            _ ≤ C * T0 ^ K := by
                have hcd : (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) ≤ C := by
                  have hh := hCdq
                  rw [show (2:ℝ)^20 * 24 * (d : ℝ) * ((C' + 1) ^ 2 * 4 ^ (2 * K'))
                      = (2:ℝ)^20 * (24 * (d : ℝ) * (C' + 1) ^ 2 * 4 ^ (2 * K')) by ring] at hh
                  exact hh
                exact mul_le_mul_of_nonneg_right hcd (by positivity)
        linarith only [h1, h2, h3]
      · have hq'pos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'1
        have h3 : |(q':ℝ) * F.leadingCoeff - ((round ((q':ℝ)*F.leadingCoeff)) : ℝ)|
            ≤ (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*(N2:ℝ)+1))) := by
          have h5 : (q':ℝ) * ((a':ℝ)/(q':ℝ)) = (a':ℝ) := by field_simp
          calc |(q':ℝ)*F.leadingCoeff - ((round ((q':ℝ)*F.leadingCoeff)) : ℝ)|
              ≤ |(q':ℝ)*F.leadingCoeff - (a':ℝ)| := round_le _ a'
            _ = (q':ℝ) * |F.leadingCoeff - (a':ℝ)/(q':ℝ)| := by
                have h6 : (q':ℝ)*F.leadingCoeff - (a':ℝ)
                    = (q':ℝ)*(F.leadingCoeff - (a':ℝ)/(q':ℝ)) := by
                  rw [mul_sub, h5]
                rw [h6, abs_mul, abs_of_pos hq'pos]
            _ ≤ (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*(N2:ℝ)+1))) :=
                mul_le_mul_of_nonneg_left ha' hq'pos.le
        have hN2ge : 2 * L ≤ 2 * (N2 : ℝ) + 1 := by
          have hN2eq : (N2:ℝ) = (d:ℝ)*(q:ℝ)*L := by
            have hN2int : (N2 : ℝ) = (d : ℝ) * (q : ℝ) * (NL : ℝ) := by rw [hN2]; push_cast; ring
            rw [hN2int, hNL]
          have h1 : (1:ℝ) ≤ (d:ℝ)*(q:ℝ) := by
            have h8 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
            have h9 : (1:ℝ) ≤ (d:ℝ) := hdR1
            nlinarith
          rw [hN2eq]; nlinarith only [h1, hLpos]
        have hstep : (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*(N2:ℝ)+1)))
            ≤ 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4
              * T0^(18*K'+2*d+6) / L^d := by
          have h1 : (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*(N2:ℝ)+1)))
              ≤ (2:ℝ)^39 * Edelta / (L * (η^2/(24*B^2*(d:ℝ)))^4) := by
            have haux : (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*L)))
                ≤ (2:ℝ)^39 * Edelta / (L * Dd^4) := by
              have h6 : (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*L)))
                  ≤ ((2:ℝ)^20/Dd) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*L))) :=
                mul_le_mul_of_nonneg_right hq'le (by positivity)
              have h7 : ((2:ℝ)^20/Dd) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*L)))
                  = (2:ℝ)^39 * Edelta / (L * Dd^4) := by
                field_simp
                try ring
              linarith only [h6, h7.le, h7.ge]
            have h8 : (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*(N2:ℝ)+1)))
                ≤ (q':ℝ) * ((2:ℝ)^20 * Edelta / (Dd^3 * (2*L))) := by
              apply mul_le_mul_of_nonneg_left _ hq'pos.le
              rw [div_eq_mul_inv, div_eq_mul_inv]
              apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (2:ℝ)^20 * Edelta)
              rw [← one_div, ← one_div]
              apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < Dd^3 * (2*L))
              exact mul_le_mul_of_nonneg_left hN2ge (by positivity : (0:ℝ) ≤ Dd^3)
            have h9 : (2:ℝ)^39 * Edelta / (L * Dd^4) ≤ (2:ℝ)^39 * Edelta / (L * (η^2/(24*B^2*(d:ℝ)))^4) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (2:ℝ)^39 * Edelta)
              rw [← one_div, ← one_div]
              apply one_div_le_one_div_of_le (show (0:ℝ) < L * (η^2/(24*B^2*(d:ℝ)))^4 by
                exact mul_pos hLpos (pow_pos hXpos 4))
              have h4 : (η^2/(24*B^2*(d:ℝ)))^4 ≤ Dd^4 := pow_le_pow_left₀ hXpos.le hDdlow 4
              nlinarith only [h4, hLpos.le]
            linarith only [h8, haux, h9]
          have hmid : (2:ℝ)^39 * Edelta / (L * (η^2/(24*B^2*(d:ℝ)))^4)
              = 2^39 * 24^4 * C' * (C'+1)^8 * P1^9 * P2 * (d:ℝ)^4 * T0^8 / L^d := by
            have hE2 : Edelta * B^8 * T0^8 = C' * (C'+1)^8 * P1^9 * P2 * T0^8 / L^(d-1) := by
              rw [hEdef, hBdef]
              rw [show ((C'+1)*P1)^8 = (C'+1)^8*P1^8 by rw [mul_pow]]
              ring
            rw [show (2:ℝ)^39 * Edelta / (L * (η^2/(24*B^2*(d:ℝ)))^4)
                = 2^39 * (Edelta * (1/(η^2/(24*B^2*(d:ℝ)))^4)) / L by ring]
            rw [hinvX]
            rw [show 2^39 * (Edelta * (24^4*B^8*(d:ℝ)^4*T0^8)) / L
                = 2^39 * 24^4 * (d:ℝ)^4 * (Edelta*B^8*T0^8) / L by ring]
            rw [hE2]
            rw [show 2^39 * 24^4 * (d:ℝ)^4 * (C'*(C'+1)^8*P1^9*P2*T0^8/L^(d-1)) / L
                = 2^39 * 24^4 * C' * (C'+1)^8 * P1^9 * P2 * (d:ℝ)^4 * T0^8 / (L*L^(d-1)) by ring]
            rw [show L * L^(d-1) = L^d by rw [mul_comm, ← pow_succ]; congr 1; omega]
          have hfin : 2^39 * 24^4 * C' * (C'+1)^8 * P1^9 * P2 * (d:ℝ)^4 * T0^8 / L^d
              ≤ 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4
                * T0^(18*K'+2*d+6) / L^d := by
            have hAB : 2^39 * 24^4 * C' * (C'+1)^8 * P1^9 * P2 * (d:ℝ)^4 * T0^8
                ≤ 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4
                  * T0^(18*K'+2*d+6) := by
              have h4 : P1^9 ≤ 4^(9*K') * T0^(18*K') := by
                calc P1^9 ≤ (4^(K') * T0^(2*K'))^9 := pow_le_pow_left₀ (by positivity) hP1le 9
                  _ = 4^(9*K') * T0^(18*K') := by
                      rw [mul_pow, ← pow_mul, ← pow_mul]
                      congr 1 <;> congr 1 <;> omega
              have h5 : P2 ≤ 64^(d-1) * T0^(2*(d-1)) := hP2le
              have h6 : T0^(18*K') * T0^(2*(d-1)) * T0^8 ≤ T0^(18*K'+2*d+6) := by
                rw [← pow_add, ← pow_add]
                apply pow_le_pow_right₀ hT01
                omega
              have hstep1 : P1^9 * P2 ≤ (4^(9*K') * T0^(18*K')) * (64^(d-1) * T0^(2*(d-1))) :=
                mul_le_mul h4 h5 (by positivity) (by positivity)
              calc 2^39 * 24^4 * C' * (C'+1)^8 * P1^9 * P2 * (d:ℝ)^4 * T0^8
                  = (2^39 * 24^4 * C' * (C'+1)^8 * (d:ℝ)^4 * T0^8) * (P1^9 * P2) := by ring
                _ ≤ (2^39 * 24^4 * C' * (C'+1)^8 * (d:ℝ)^4 * T0^8)
                      * ((4^(9*K') * T0^(18*K')) * (64^(d-1) * T0^(2*(d-1)))) :=
                    mul_le_mul_of_nonneg_left hstep1 (by positivity)
                _ = 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4
                      * (T0^(18*K') * T0^(2*(d-1)) * T0^8) := by ring
                _ ≤ 2^39 * 24^4 * C' * (C'+1)^8 * 4^(9*K') * 64^(d-1) * (d:ℝ)^4
                      * T0^(18*K'+2*d+6) := by
                    apply mul_le_mul_of_nonneg_left h6 (by positivity)
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hAB (inv_nonneg.mpr (pow_nonneg hLpos.le d))
          linarith only [h1, hmid, hfin, hlast2]
        linarith only [h3, hstep, hlast2]


/-- **The inverse Weyl estimate for plain polynomial sums**, obtained by strong induction on the
degree, given the arithmetic amplification `hAmp` (Green--Tao Lemma 3.1 (ii)). -/
theorem lip2PlainIW_of_amp
    (hAmp : ∀ (β δ₁ δ₂ : ℝ) (N : ℕ) (T : Finset ℤ), 1 ≤ N → 0 < δ₁ → 0 < δ₂ → δ₂ ≤ 1 →
      50 * δ₁ ≤ δ₂ ^ 2 → 1 ≤ δ₂ * ((N : ℝ) + 1) →
      (∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) →
      δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ) →
      (∀ n ∈ T, ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ₁) →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 2 ^ 20 / δ₂ ∧ ∃ a : ℤ,
        |β - (a : ℝ) / (q : ℝ)| ≤ 2 ^ 20 * δ₁ / (δ₂ ^ 3 * (2 * (N : ℝ) + 1))) :
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, IW d C K := by
  intro d hd
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases eq_or_lt_of_le hd with h1 | h1
    · subst h1
      exact ⟨4, by norm_num, 1, IW_one⟩
    · obtain ⟨C', hC'pos, K', hIW'⟩ := ih (d - 1) (by omega) (by omega)
      exact IW_step d h1 hC'pos hIW' hAmp

end Work.KMTAreas.A4
