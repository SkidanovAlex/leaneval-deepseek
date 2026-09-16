import Mathlib
import Submission.BVBasic
import Submission.BVLevel
import Submission.LevelOfDistribution
import Submission.Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_chi_range
import Submission.Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive
import Submission.Commons.NumberTheory.BombieriVinogradov.abel_tail_sum_le
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real
import Submission.Commons.Analysis.Asymptotics.eventually_log_ge

open scoped BigOperators Topology
open Finset Filter
open Submission.BV
open Classical

/-!
# Assembling the Bombieri--Vinogradov input `CleanBV`

This module carries out the final assembly of the classical Bombieri--Vinogradov
theorem in the form `CleanBV` consumed by `Submission/BVLevel.lean`:

* the primitive-character reduction (Vaughan §1, the commons lemma
  `sum_charSup_le_log_mul_primitive`), which bounds the sum over all characters
  modulo `q` by the sum over the primitive ones plus an error term;
* the Siegel--Walfisz step for `q ≤ (log X)^{A+10}`, obtained from the commons
  lemma `siegel_walfisz_chi_range` (uniform in the modulus up to a power of
  `log x`) together with the prime number theorem for the principal character;
* the Basic Mean Value Theorem (Vaughan's Theorem 1.2) for the range
  `(log X)^{A+10} < q ≤ Q`, combined with summation by parts
  (`abel_tail_sum_le`).

The only input that is *not* proved here is the Basic Mean Value Theorem itself,
which enters as the explicit hypothesis `hBMVT` on the `q/φ(q)`-weighted primitive
character sum; `basic_mean_value_theorem` in the shared library supplies exactly
that statement.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

set_option maxHeartbeats 4000000

/-! ## §1. Character-sup forms. -/

/-- The sup of the primitive character sums, in the `range` form used for the
Siegel--Walfisz input. -/
def chiSupRange (q : ℕ) (χ : DirichletCharacter ℂ q) (X : ℕ) : ℝ :=
  sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
        - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X)

/-- The sup of the primitive character sums, in the `Icc` form appearing in the
Basic Mean Value Theorem. -/
def chiSupIcc (q : ℕ) (χ : DirichletCharacter ℂ q) (X : ℕ) : ℝ :=
  sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖) '' Set.Icc 1 X)

/-- `charSup` agrees with its explicit `range` form. -/
theorem charSup_eq_chiSupRange (X : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    charSup X χ = chiSupRange q χ X := by
  simp only [chiSupRange, charSup, psiChar, deltaChar]

/-- `Λ 0 = 0`. -/
theorem vonMangoldt_zero : ArithmeticFunction.vonMangoldt 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
  rintro ⟨p, k, hp, _hk, hpk⟩
  have : 0 < p ^ k := pow_pos hp.pos k
  omega

/-- The `range`-sum of the character-twisted von Mangoldt weights equals the
`Icc`-sum (the `n = 0` term vanishes). -/
theorem sum_range_eq_sum_Icc (q y : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.range (y + 1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
        * χ ((n : ℕ) : ZMod q)) =
      (∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
        * χ ((n : ℕ) : ZMod q)) := by
  have h1 : Finset.range (y + 1) = insert 0 (Finset.Icc 1 y) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h2 : (0 : ℕ) ∉ Finset.Icc 1 y := by simp only [Finset.mem_Icc]; omega
  rw [h1, Finset.sum_insert h2, vonMangoldt_zero]
  simp

/-- The two sup forms agree for a non-principal character. -/
theorem chiSupRange_eq_chiSupIcc (q X : ℕ) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    chiSupRange q χ X = chiSupIcc q χ X := by
  have key : ∀ y : ℕ,
      ‖(∑ n ∈ Finset.range (y + 1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
          * χ ((n : ℕ) : ZMod q)) - (if χ = 1 then (y : ℂ) else 0)‖
        = ‖(∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
          * χ ((n : ℕ) : ZMod q))‖ := by
    intro y
    rw [sum_range_eq_sum_Icc, if_neg hχ, sub_zero]
  unfold chiSupRange chiSupIcc
  rw [show (fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
          - (if χ = 1 then (y : ℂ) else 0)‖)
      = (fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖)
      from funext key]

/-- A primitive character modulo `q ≥ 2` is not the principal character. -/
theorem isPrimitive_ne_one {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  rw [h, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
  omega

/-- The primitive-character sum `Σ_{q ≤ R} φ(q)⁻¹ Σ*_χ sup_y ‖ψ(y,χ) − δ(χ) y‖`. -/
def primSum (X R : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
    ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)), charSup X χ

/-- One summand of the Basic Mean Value Theorem. -/
def bmvtTerm (X q : ℕ) : ℝ :=
  ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
      chiSupIcc q χ X

/-- The `q/φ(q)`-weighted primitive-character sum of the Basic Mean Value
Theorem, in `Icc` form. -/
def bmvtSum (X Q : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 Q, bmvtTerm X q

/-! ## §4. The Basic Mean Value Theorem on the large-moduli range. -/

/-- The Basic Mean Value Theorem (Vaughan, Theorem 1.2), packaged as a
hypothesis on `bmvtSum`. -/
def BMVTHypothesis : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 2 ≤ X → 1 ≤ Q →
    bmvtSum X Q ≤ C * ((X : ℝ) + (X : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ)
        + (X : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2)
      * (Real.log ((X : ℝ) * (Q : ℝ) + 2)) ^ 5

/-- `abelX K X = ⌊K ^ 10 * X⌋ + 1`, the rescaling used to absorb the constant of
the Basic Mean Value Theorem into the parameter of the summation-by-parts bound. -/
def abelX (K : ℝ) (X : ℕ) : ℕ := ⌊K ^ 10 * (X : ℝ)⌋₊ + 1

/-- A constant is eventually below any positive power of `log X`. -/
theorem eventually_const_le_log_rpow (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) :
    ∀ᶠ X : ℕ in atTop, c ≤ (Real.log (X : ℝ)) ^ d := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h
    filter_upwards [Filter.eventually_ge_atTop 2] with X hX
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))) d
  · filter_upwards [Commons.Analysis.Asymptotics.eventually_log_ge (c ^ (1 / d))] with X hX
    have h2 : (1 / d) * d = 1 := by field_simp
    have hc_eq : c = (c ^ (1 / d)) ^ d := by
      calc c = c ^ (1 : ℝ) := (Real.rpow_one c).symm
        _ = c ^ ((1 / d) * d) := by rw [h2]
        _ = (c ^ (1 / d)) ^ d := Real.rpow_mul h.le (1 / d) d
    rw [hc_eq]
    exact Real.rpow_le_rpow (Real.rpow_nonneg h.le _) hX hd.le

/-- `C * (log X)^m = O(X^δ)` for every `C ≥ 0` and `δ > 0`. -/
theorem eventually_const_mul_log_pow_le_rpow {C δ m : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, C * (Real.log (X : ℝ)) ^ m ≤ (X : ℝ) ^ δ := by
  rcases eq_or_lt_of_le hC with h | h
  · subst h
    filter_upwards [Filter.eventually_ge_atTop 2] with X _
    rw [zero_mul]
    exact Real.rpow_nonneg (Nat.cast_nonneg X) δ
  · set M : ℝ := max m 1 with hM
    have hM1 : (1 : ℝ) ≤ M := le_max_right m 1
    have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
    set ε : ℝ := δ / (2 * M) with hεdef
    have hε : 0 < ε := by rw [hεdef]; positivity
    have hεM : ε * M < δ := by rw [hεdef]; field_simp; linarith
    have hεMn : (0 : ℝ) < δ - ε * M := by linarith
    have hEpos : (0 : ℝ) < ε ^ M := by positivity
    filter_upwards [Filter.eventually_ge_atTop 3,
      Filter.eventually_ge_atTop (⌈(((C + 1) / ε ^ M) ^ (1 / (δ - ε * M)))⌉₊ + 1)] with X hX2 hX3
    have hX2' : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by linarith
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := hXpos.le
    have hlog1 : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
    have hlogge1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
      rw [Real.le_log_iff_exp_le hXpos]
      linarith [Real.exp_one_lt_three]
    have hlogM : (Real.log (X : ℝ)) ^ m ≤ (Real.log (X : ℝ)) ^ M :=
      Real.rpow_le_rpow_of_exponent_le hlogge1 (le_max_left m 1)
    have hlogX : Real.log (X : ℝ) ≤ (X : ℝ) ^ ε / ε :=
      Real.log_le_rpow_div hXnn hε
    have hlogM2 : (Real.log (X : ℝ)) ^ M ≤ ((X : ℝ) ^ ε / ε) ^ M :=
      Real.rpow_le_rpow hlog1 hlogX hMpos.le
    have hdiv : ((X : ℝ) ^ ε / ε) ^ M = (X : ℝ) ^ (ε * M) / ε ^ M := by
      rw [Real.div_rpow (Real.rpow_nonneg hXnn ε) hε.le,
        ← Real.rpow_mul hXnn]
    have hCX : C * (Real.log (X : ℝ)) ^ m ≤ (C + 1) * ((X : ℝ) ^ (ε * M) / ε ^ M) := by
      have ha : C * (Real.log (X : ℝ)) ^ m ≤ (C + 1) * (Real.log (X : ℝ)) ^ M := by
        have hs1 : C * (Real.log (X : ℝ)) ^ m ≤ (C + 1) * (Real.log (X : ℝ)) ^ m :=
          mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (Real.rpow_nonneg hlog1 m)
        have hs2 : (C + 1) * (Real.log (X : ℝ)) ^ m ≤ (C + 1) * (Real.log (X : ℝ)) ^ M :=
          mul_le_mul_of_nonneg_left hlogM (by linarith : (0 : ℝ) ≤ C + 1)
        exact le_trans hs1 hs2
      have hb : (C + 1) * (Real.log (X : ℝ)) ^ M
          ≤ (C + 1) * ((X : ℝ) ^ (ε * M) / ε ^ M) := by
        rw [hdiv] at hlogM2
        exact mul_le_mul_of_nonneg_left hlogM2 (by linarith : (0 : ℝ) ≤ C + 1)
      exact le_trans ha hb
    have hkey : (C + 1) / ε ^ M ≤ (X : ℝ) ^ (δ - ε * M) := by
      have hbase : (0 : ℝ) ≤ (C + 1) / ε ^ M := by positivity
      have hbig : (((C + 1) / ε ^ M) ^ (1 / (δ - ε * M))) ≤ (X : ℝ) := by
        have h1 : (((C + 1) / ε ^ M) ^ (1 / (δ - ε * M))) ≤ (⌈(((C + 1) / ε ^ M)
            ^ (1 / (δ - ε * M)))⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈(((C + 1) / ε ^ M) ^ (1 / (δ - ε * M)))⌉₊ : ℝ) + 1 ≤ (X : ℝ) := by
          exact_mod_cast hX3
        linarith
      calc (C + 1) / ε ^ M
          = (((C + 1) / ε ^ M) ^ (1 / (δ - ε * M))) ^ (δ - ε * M) := by
            rw [← Real.rpow_mul hbase, one_div,
              inv_mul_cancel₀ (ne_of_gt hεMn), Real.rpow_one]
        _ ≤ (X : ℝ) ^ (δ - ε * M) := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hbig hεMn.le
    calc C * (Real.log (X : ℝ)) ^ m ≤ (C + 1) * ((X : ℝ) ^ (ε * M) / ε ^ M) := hCX
      _ = ((C + 1) / ε ^ M) * (X : ℝ) ^ (ε * M) := by ring
      _ ≤ (X : ℝ) ^ (δ - ε * M) * (X : ℝ) ^ (ε * M) :=
          mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hXnn _)
      _ = (X : ℝ) ^ ((δ - ε * M) + ε * M) := by
          rw [Real.rpow_add hXpos]
      _ = (X : ℝ) ^ δ := by ring_nf

/-- A non-negative constant is eventually below `X^δ` for every `δ > 0`. -/
theorem eventually_const_le_rpow {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, C ≤ (X : ℝ) ^ δ := by
  have h := eventually_const_mul_log_pow_le_rpow (C := C) (δ := δ) (m := 0) hC hδ
  filter_upwards [h] with X hX
  simpa using hX

/-- `Σ_{q ≤ Q} c q ≤ Σ_{q ≤ R} c q + Σ_{R < q ≤ Q} c q` for non-negative `c`. -/
theorem sum_Icc_le_sum_Icc_add_Ioc {c : ℕ → ℝ} (hc : ∀ q, 0 ≤ c q) (R Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, c q) ≤ (∑ q ∈ Finset.Icc 1 R, c q) + ∑ q ∈ Finset.Ioc R Q, c q := by
  rcases le_or_gt R Q with h | h
  · have hunion : Finset.Icc 1 Q = Finset.Icc 1 R ∪ Finset.Ioc R Q := by
      ext q; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdisj : Disjoint (Finset.Icc 1 R) (Finset.Ioc R Q) := by
      rw [Finset.disjoint_left]; intro q hq1 hq2
      simp only [Finset.mem_Icc] at hq1; simp only [Finset.mem_Ioc] at hq2; omega
    rw [hunion, Finset.sum_union hdisj]
  · have hsub : Finset.Icc 1 Q ⊆ Finset.Icc 1 R := by
      intro q hq; simp only [Finset.mem_Icc] at hq ⊢; omega
    have hempty : Finset.Ioc R Q = ∅ := Finset.Ioc_eq_empty (by omega)
    have hle : (∑ q ∈ Finset.Icc 1 Q, c q) ≤ ∑ q ∈ Finset.Icc 1 R, c q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hc q)
    have hgoal : (∑ q ∈ Finset.Icc 1 Q, c q)
        ≤ (∑ q ∈ Finset.Icc 1 R, c q) + ∑ q ∈ Finset.Ioc R Q, c q := by
      rw [hempty, Finset.sum_empty, add_zero]
      exact hle
    exact hgoal

/-! ## §2. The primitive-character reduction. -/

/-- **Primitive-character reduction** in terms of `charSup`: the sum over all
characters modulo `q` is bounded by the sum over the primitive ones plus an
explicit error term. -/
theorem primitive_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, charSup X χ)
      ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * primSum X Q
        + C * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2) := by
  obtain ⟨C, hC, h⟩ :=
    Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive
  refine ⟨C, hC, fun X Q hQ => ?_⟩
  have h1 := h X Q hQ
  simpa only [primSum, chiSupRange, charSup, psiChar, deltaChar] using h1

end

end Commons.NumberTheory.MaynardSieve
