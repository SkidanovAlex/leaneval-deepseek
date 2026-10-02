/-
# ZeroFreeTables/XY — eight-term positivity of the `Nebenfall` `K`-combination

The pointwise positivity behind Xylouris's (4.4) at `k = 1` (equivalently HB's `F`-method
`K`-inequality of §9 for a real character `χ₁`, `χ₁² = 1`): the eight `K`-terms

`(3/2)K(β,χ₀) + (3/2)K(β+iγ,χ₁) + K(β+i(γ₁-γ),χ₀) + 2K(β+iγ₁,χ₁) + K(β+i(γ₁+γ),χ₀)
   + (1/4)K(β+i(2γ₁-γ),χ₁) + (1/2)K(β+2iγ₁,χ₀) + (1/4)K(β+i(2γ₁+γ),χ₁)`

(where `K(s,χ) = Σ'_n Λ(n)·ℜ(χ(n)/n^s)·f(log n / L)`, `χ₀` the principal character) are
non-negative whenever `f ≥ 0` is supported below `x₀` and `χ₁ ^ 2 = 1`.

The mechanism is the classical pointwise one.  For `n` a unit of `ZMod q` write
`A = χ₁(n)·n^{-iγ}`, `B = χ₁(n)·n^{-iγ₁}`; both are points of the complex unit circle
(`χ₁² = 1` makes `χ₁(n) = ±1`).  Since `ℜ(χ(n)/n^{β+it}) = n^{-β}ℜ(χ(n)n^{-it})`, the
`n`-th summand of the eight terms equals `Λ(n)f(log n/L)n^{-β}` times

`3/2 + (3/2)ℜA + ℜ(B·conj A) + 2ℜB + ℜ(BA) + (1/4)ℜ(B²·conj A) + (1/2)ℜ(B²) + (1/4)ℜ(B²A)
   = (1 + ℜA)(1 + ℜB)²  ≥ 0`

(the algebraic identity `eight_unit`, verified by reducing to real coordinates and using
`|B| = 1`).  Off the units every character value vanishes.  The `tsum`s are finite because
`f` is supported below `x₀`, so the pointwise inequality integrates to the stated one.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.ZeroFreeTables.TrigPolyPos
import Submission.Work.ZeroFreeTables.XY.KsumFiveNonneg

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option linter.unusedVariables false

noncomputable section

namespace Work.ZeroFreeTables.XY

/-- Coefficients of the eight-term `Nebenfall` positivity. -/
def KsumEightC : ℕ → ℝ
  | 0 => 3/2
  | 1 => 3/2
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 1/4
  | 6 => 1/2
  | 7 => 1/4
  | _ => 0

/-- Heights of the eight `K`-summands. -/
def KsumEightT (γ γ₁ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => γ
  | 2 => γ₁ - γ
  | 3 => γ₁
  | 4 => γ₁ + γ
  | 5 => 2 * γ₁ - γ
  | 6 => 2 * γ₁
  | 7 => 2 * γ₁ + γ
  | _ => 0

/-- Characters of the eight `K`-summands: `χ₁` at the odd indices, the principal character
at the even ones (using `χ₁ ^ 2 = 1`). -/
def KsumEightChi {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) : ℕ → DirichletCharacter ℂ q
  | 1 => χ₁
  | 3 => χ₁
  | 5 => χ₁
  | 7 => χ₁
  | _ => 1

/-- The eight pointwise patterns `1, A, B·conj A, B, BA, B²·conj A, B², B²A`
in terms of `A = χ₁(n)n^{-iγ}`, `B = χ₁(n)n^{-iγ₁}`. -/
def KsumEightTerm (A B : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => A
  | 2 => B * starRingEnd ℂ A
  | 3 => B
  | 4 => B * A
  | 5 => B^2 * starRingEnd ℂ A
  | 6 => B^2
  | 7 => B^2 * A
  | _ => 0

/-- **Pointwise algebra of the eight-term positivity.**  For `B` on the complex unit circle
and arbitrary `A`,

`(1+ℜA)(1+ℜB)² = 3/2 + (3/2)ℜA + ℜ(B conj A) + 2ℜB + ℜ(BA) + 1/4·ℜ(B² conj A)
   + 1/2·ℜ(B²) + 1/4·ℜ(B²A)`.

Only the unit-circle property of `B` is used (the imaginary part of `A` cancels). -/
theorem eight_unit (A B : ℂ) (hB : ‖B‖ = 1) :
    3/2 + 3/2 * A.re + (B * starRingEnd ℂ A).re + 2 * B.re + (B * A).re
      + 1/4 * (B^2 * starRingEnd ℂ A).re + 1/2 * (B^2).re + 1/4 * (B^2 * A).re
    = (1 + A.re) * (1 + B.re)^2 := by
  have hB' : B.re ^ 2 + B.im ^ 2 = 1 := by
    have h := Complex.normSq_apply B
    rw [Complex.normSq_eq_norm_sq, hB, one_pow] at h
    nlinarith
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring_nf
  have h1 : A.re * (B.re ^ 2 + B.im ^ 2 - 1) = 0 := by rw [hB']; ring
  linarith [hB', h1]

/-- **Pointwise (single `n`) form of the eight-term positivity.**  For `n ≥ 1`, a real
character `χ₁` (`χ₁ ^ 2 = 1`), `f ≥ 0` and any `β, γ, γ₁`, the eight summands at `n` sum to
`Λ(n)·f(log n / L)·n^{-β}·(1 + ℜA)(1 + ℜB)² ≥ 0` with `A = χ₁(n)n^{-iγ}`, `B = χ₁(n)n^{-iγ₁}`:
every character value vanishes when `n` is not a unit of `ZMod q`. -/
theorem KsumEight_pointwise {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {L β γ γ₁ : ℝ} (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ∑ k ∈ Finset.range 8, KsumEightC k *
      ((ArithmeticFunction.vonMangoldt n : ℝ) *
        ((KsumEightChi χ₁ k (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
        * f (Real.log n / L)) := by
  classical
  by_cases hunit : IsUnit (n : ZMod q)
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
    set w : ℂ := χ₁ (n : ZMod q) with hw
    set z : ℂ := (n : ℂ) ^ (-((γ : ℂ) * Complex.I)) with hz
    set u : ℂ := (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) with hu
    have hznorm : ‖z‖ = 1 := by
      rw [hz]
      have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hunorm : ‖u‖ = 1 := by
      rw [hu]
      have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hwnorm : ‖w‖ = 1 := by
      rw [hw]
      have h1 : χ₁ (n : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
        rw [← IsUnit.unit_spec hunit, ← MulChar.pow_apply_coe χ₁ _ hunit.unit,
          MulChar.pow_card_eq_one, MulChar.one_apply_coe]
      exact Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
    have hw2 : w ^ 2 = 1 := by
      rw [hw, pow_two, ← MulChar.mul_apply, ← pow_two, hχ₁]
      exact MulChar.one_apply hunit
    have hwreal : starRingEnd ℂ w = w := by
      have hfac : (w - 1) * (w + 1) = 0 := by linear_combination hw2
      rcases mul_eq_zero.mp hfac with h | h
      · rw [sub_eq_zero.mp h]; simp
      · rw [add_eq_zero_iff_eq_neg.mp h]; simp
    have hwconjmul : w * starRingEnd ℂ w = 1 := by
      rw [hwreal, ← pow_two, hw2]
    set A : ℂ := w * z with hA
    set B : ℂ := w * u with hB
    have hAnorm : ‖A‖ = 1 := by rw [hA, Complex.norm_mul, hwnorm, hznorm, one_mul]
    have hBnorm : ‖B‖ = 1 := by rw [hB, Complex.norm_mul, hwnorm, hunorm, one_mul]
    have hzinv : z⁻¹ = starRingEnd ℂ z := Complex.inv_eq_conj hznorm
    have hγinv : (n : ℂ) ^ ((γ : ℂ) * Complex.I) = z⁻¹ := by
      rw [hz, ← Complex.cpow_neg]
      congr 1
      ring
    have hp2 : (n : ℂ) ^ (-(((γ₁ - γ : ℝ) : ℂ) * Complex.I)) = u * z⁻¹ := by
      have harg : -(((γ₁ - γ : ℝ) : ℂ) * Complex.I)
          = (-((γ₁ : ℂ) * Complex.I)) + ((γ : ℂ) * Complex.I) := by push_cast; ring
      rw [harg, Complex.cpow_add _ _ hnc, ← hu, hγinv]
    have hp4 : (n : ℂ) ^ (-(((γ₁ + γ : ℝ) : ℂ) * Complex.I)) = u * z := by
      have harg : -(((γ₁ + γ : ℝ) : ℂ) * Complex.I)
          = (-((γ₁ : ℂ) * Complex.I)) + (-((γ : ℂ) * Complex.I)) := by push_cast; ring
      rw [harg, Complex.cpow_add _ _ hnc, ← hu, ← hz]
    have hp5 : (n : ℂ) ^ (-(((2 * γ₁ - γ : ℝ) : ℂ) * Complex.I)) = u ^ 2 * z⁻¹ := by
      have harg : -(((2 * γ₁ - γ : ℝ) : ℂ) * Complex.I)
          = (-((γ₁ : ℂ) * Complex.I)) + (-((γ₁ : ℂ) * Complex.I)) + ((γ : ℂ) * Complex.I) := by
        push_cast; ring
      rw [harg, Complex.cpow_add _ _ hnc, Complex.cpow_add _ _ hnc, ← hu, hγinv]
      ring
    have hp6 : (n : ℂ) ^ (-(((2 * γ₁ : ℝ) : ℂ) * Complex.I)) = u ^ 2 := by
      have harg : -(((2 * γ₁ : ℝ) : ℂ) * Complex.I)
          = (-((γ₁ : ℂ) * Complex.I)) + (-((γ₁ : ℂ) * Complex.I)) := by push_cast; ring
      rw [harg, Complex.cpow_add _ _ hnc, ← hu]
      ring
    have hp7 : (n : ℂ) ^ (-(((2 * γ₁ + γ : ℝ) : ℂ) * Complex.I)) = u ^ 2 * z := by
      have harg : -(((2 * γ₁ + γ : ℝ) : ℂ) * Complex.I)
          = (-((γ₁ : ℂ) * Complex.I)) + (-((γ₁ : ℂ) * Complex.I)) + (-((γ : ℂ) * Complex.I)) := by
        push_cast; ring
      rw [harg, Complex.cpow_add _ _ hnc, Complex.cpow_add _ _ hnc, ← hu, ← hz]
      ring
    have hAconj : starRingEnd ℂ A = w * starRingEnd ℂ z := by rw [hA, map_mul, hwreal]
    have hk2c : u * starRingEnd ℂ z = B * starRingEnd ℂ A := by
      rw [hAconj, hB]
      calc u * starRingEnd ℂ z = (w * starRingEnd ℂ w) * (u * starRingEnd ℂ z) := by
            rw [hwconjmul, one_mul]
        _ = w * u * (w * starRingEnd ℂ z) := by rw [hwreal]; ring
    have hk4c : u * z = B * A := by
      rw [hA, hB]
      calc u * z = (w ^ 2) * (u * z) := by rw [hw2, one_mul]
        _ = w * u * (w * z) := by ring
    have hk5c : w * u ^ 2 * starRingEnd ℂ z = B ^ 2 * starRingEnd ℂ A := by
      rw [hAconj, hB]
      calc w * u ^ 2 * starRingEnd ℂ z = (w ^ 2) * (w * u ^ 2 * starRingEnd ℂ z) := by
            rw [hw2, one_mul]
        _ = (w * u) ^ 2 * (w * starRingEnd ℂ z) := by ring
    have hk6c : u ^ 2 = B ^ 2 := by
      rw [hB]
      calc u ^ 2 = (w ^ 2) * u ^ 2 := by rw [hw2, one_mul]
        _ = (w * u) ^ 2 := by ring
    have hk7c : w * u ^ 2 * z = B ^ 2 * A := by
      rw [hA, hB]
      calc w * u ^ 2 * z = (w ^ 2) * (w * u ^ 2 * z) := by rw [hw2, one_mul]
        _ = (w * u) ^ 2 * (w * z) := by ring
    have hv : ∀ k ∈ Finset.range 8,
        (KsumEightChi χ₁ k (n : ZMod q) *
          (n : ℂ) ^ (-(((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I))).re
          = (KsumEightTerm A B k).re := by
      intro k hk
      simp only [Finset.mem_range] at hk
      interval_cases k
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [MulChar.one_apply hunit]
        simp
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [← hw, ← hz, ← hA]
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [MulChar.one_apply hunit, one_mul, hp2, hzinv, hk2c]
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [← hw, ← hu, ← hB]
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [MulChar.one_apply hunit, one_mul, hp4, hk4c]
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [← hw, hp5, hzinv, ← mul_assoc, hk5c]
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [MulChar.one_apply hunit, one_mul, hp6, hk6c]
      · simp only [KsumEightChi, KsumEightT, KsumEightTerm]
        rw [← hw, hp7, ← mul_assoc, hk7c]
    have hsum2 : ∑ k ∈ Finset.range 8, KsumEightC k *
          (KsumEightChi χ₁ k (n : ZMod q) *
            (n : ℂ) ^ (-(((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I))).re
        = 3/2 + 3/2 * A.re + (B * starRingEnd ℂ A).re + 2 * B.re + (B * A).re
          + 1/4 * (B^2 * starRingEnd ℂ A).re + 1/2 * (B^2).re + 1/4 * (B^2 * A).re := by
      rw [Finset.sum_congr rfl (fun k hk => by rw [hv k hk])]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, KsumEightC, KsumEightTerm,
        Complex.one_re]
      ring
    have hstep : ∀ k ∈ Finset.range 8,
        KsumEightC k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((KsumEightChi χ₁ k (n : ZMod q) /
              (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
          * f (Real.log n / L))
        = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
          * (KsumEightC k * (KsumEightChi χ₁ k (n : ZMod q) *
              (n : ℂ) ^ (-(((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I))).re) := by
      intro k _
      rw [re_div_cpow_eq (KsumEightChi χ₁ k) hn β (((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)]
      ring
    have hsum1 : (∑ k ∈ Finset.range 8, KsumEightC k *
          ((ArithmeticFunction.vonMangoldt n : ℝ) *
            ((KsumEightChi χ₁ k (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
            * f (Real.log n / L)))
        = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
          * (∑ k ∈ Finset.range 8, KsumEightC k * (KsumEightChi χ₁ k (n : ZMod q) *
              (n : ℂ) ^ (-(((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I))).re) := by
      rw [Finset.sum_congr rfl hstep, Finset.mul_sum]
    have hident := eight_unit A B hBnorm
    rw [hsum1, hsum2, hident]
    have hAre : -1 ≤ A.re := by
      have h := Complex.abs_re_le_norm A
      rw [hAnorm, abs_le] at h
      exact h.1
    exact mul_nonneg (mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hf _))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (mul_nonneg (by linarith) (sq_nonneg _))
  · have hzero : ∀ k : ℕ, KsumEightChi χ₁ k (n : ZMod q) = 0 :=
      fun k => MulChar.map_nonunit (KsumEightChi χ₁ k) hunit
    rw [Finset.sum_eq_zero]
    intro k _
    rw [hzero k]
    simp

theorem KsumEightNonneg {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ γ₁ : ℝ} (hL : 0 < L) (hx₀ : 0 ≤ x₀)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) :
    0 ≤ (3 / 2) * Work.ZeroFreeTables.XY.Kxy f L β 0 (1 : DirichletCharacter ℂ q)
      + (3 / 2) * Work.ZeroFreeTables.XY.Kxy f L β γ χ₁
      + Work.ZeroFreeTables.XY.Kxy f L β (γ₁ - γ) (1 : DirichletCharacter ℂ q)
      + 2 * Work.ZeroFreeTables.XY.Kxy f L β γ₁ χ₁
      + Work.ZeroFreeTables.XY.Kxy f L β (γ₁ + γ) (1 : DirichletCharacter ℂ q)
      + (1 / 4) * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ₁ - γ) χ₁
      + (1 / 2) * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ₁) (1 : DirichletCharacter ℂ q)
      + (1 / 4) * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ₁ + γ) χ₁ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    refine ⟨Nat.ceil (Real.exp (x₀ * L)) + 1, fun n hn => ?_⟩
    have h1 : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have : (Nat.ceil (Real.exp (x₀ * L)) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hn)
      exact le_trans (Nat.le_ceil _) this
    have h2 : x₀ * L ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hL]
    exact h2
  have hvan : ∀ k n : ℕ, N ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((KsumEightChi χ₁ k (n : ZMod q) /
          (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
      * f (Real.log n / L) = 0 := by
    intro k n hn
    rw [hsupp _ (hN n hn)]
    ring
  have hterm : ∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range (7 + 1), KsumEightC k *
      ((ArithmeticFunction.vonMangoldt n : ℝ) *
        ((KsumEightChi χ₁ k (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
        * f (Real.log n / L)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
      rw [Finset.sum_eq_zero (fun k _ => by rw [hΛ0]; simp)]
    · exact KsumEight_pointwise hf χ₁ hχ₁ h
  have key := Work.ZeroFreeTables.tsum_finset_sum_nonneg (N := N) (c := KsumEightC) (d := 7)
    (g := fun k n => (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((KsumEightChi χ₁ k (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
        * f (Real.log n / L)) hvan hterm
  have hg : ∀ k : ℕ, (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((KsumEightChi χ₁ k (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
        * f (Real.log n / L)) = Kxy f L β (KsumEightT γ γ₁ k) (KsumEightChi χ₁ k) :=
    fun k => rfl
  have hsum_eq : (∑ k ∈ Finset.range 8, KsumEightC k *
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((KsumEightChi χ₁ k (n : ZMod q) /
              (n : ℂ) ^ ((β : ℂ) + ((KsumEightT γ γ₁ k : ℝ) : ℂ) * Complex.I)).re)
          * f (Real.log n / L)))
      = (3 / 2) * Work.ZeroFreeTables.XY.Kxy f L β 0 (1 : DirichletCharacter ℂ q)
        + (3 / 2) * Work.ZeroFreeTables.XY.Kxy f L β γ χ₁
        + Work.ZeroFreeTables.XY.Kxy f L β (γ₁ - γ) (1 : DirichletCharacter ℂ q)
        + 2 * Work.ZeroFreeTables.XY.Kxy f L β γ₁ χ₁
        + Work.ZeroFreeTables.XY.Kxy f L β (γ₁ + γ) (1 : DirichletCharacter ℂ q)
        + (1 / 4) * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ₁ - γ) χ₁
        + (1 / 2) * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ₁) (1 : DirichletCharacter ℂ q)
        + (1 / 4) * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ₁ + γ) χ₁ := by
    simp only [hg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, KsumEightC, KsumEightT,
      KsumEightChi]
    ring
  rw [hsum_eq] at key
  exact key

end Work.ZeroFreeTables.XY
