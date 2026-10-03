import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped LSeries.notation

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Uniform bound for the logarithmic derivative of a Dirichlet L-function

We prove that there is an absolute constant `C > 0` such that, uniformly in the modulus
`N`, the character `χ` and the point `s` with `Re s > 1`,

    ‖ (L(·,χ))′/L(·,χ) (s) ‖ ≤ 1/(Re s − 1) + C.

The proof uses the von Mangoldt expansion on `Re s > 1`

    (logDeriv L(·,χ))(s) = − ∑_n Λ(n)χ(n) n^{−s}

(together with `‖χ(n)‖ ≤ 1` and `Λ(n) ≥ 0`) to dominate the norm by the real sum
`∑_n Λ(n) n^{−σ}` with `σ = Re s`.  That sum is the value on the real axis of the
negative logarithmic derivative of `ζ` (the L-series of `Λ`), `−ζ′/ζ(σ)`, which is
bounded by `1/(σ−1) + C` for `1 < σ ≤ 2` by the published
`zeta_logDeriv_re_axis_bound`, and by its value at `σ = 2` for `σ ≥ 2` by monotonicity.
-/

/-- The real majorant `Λ(n)·n^{-σ}` of the twisted von Mangoldt L-series is summable
for `σ > 1`. -/
private lemma summable_vonMangoldt_mul_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

/-- Pointwise evaluation of the norm of the `n`-th term of the L-series of `Λ`. -/
private lemma norm_LSeries_term_vonMangoldt (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) s.re, div_eq_mul_inv]

/-- The L-series of `Λ` at a real point `σ > 1` has real part equal to the real sum
`∑_n Λ(n) n^{-σ} = −Re(ζ′/ζ(σ))`. -/
private lemma vonMangoldt_tsum_eq_zeta_re (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) =
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hsumm : LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hζid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (σ : ℂ)) (by simpa using hσ)
  rw [← hζid, LSeries, Complex.re_tsum hsumm]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ, ← Complex.ofReal_div,
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

/-- **Norm bound for the twist of the von Mangoldt L-series.**  For `Re s > 1`,

    ‖ ∑_n Λ(n)χ(n) n^{-s} ‖ ≤ ∑_n Λ(n) n^{-Re s}. -/
private lemma norm_LSeries_twist_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s‖
      ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  have hfsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) s := by
    have hg : LSeriesSummable
        ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
          fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    refine (LSeriesSummable_congr s (f := fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      (g := (fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
        fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ?_).mpr hg
    intro n _
    simp only [Pi.mul_apply]
    ring
  have hΛsumm : LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  calc ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hfsumm.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ := by
        refine Summable.tsum_le_tsum (fun n => LSeries.norm_term_le s ?_)
          hfsumm.norm hΛsumm.norm
        rw [norm_mul, Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        simpa using mul_le_mul_of_nonneg_left (χ.norm_le_one (n : ZMod N))
          ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) :=
        tsum_congr (fun n => norm_LSeries_term_vonMangoldt s n)

theorem logDeriv_LFunction_norm_le_of_one_lt_re :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 < s.re → ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨Cz, hCzpos, hz⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  refine ⟨Cz + 1, by linarith, ?_⟩
  intro N _inst χ s hs
  have hld := LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs
  have hbound := norm_LSeries_twist_le (N := N) χ hs
  have hAub : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re)) ≤
      1 / (s.re - 1) + (Cz + 1) := by
    by_cases hle : s.re ≤ 2
    · rw [vonMangoldt_tsum_eq_zeta_re s.re hs]
      have h2 := hz s.re hs hle
      linarith
    · have hgt : 2 < s.re := lt_of_not_ge hle
      have hmono : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re)) ≤
          ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ)) := by
        refine Summable.tsum_le_tsum (fun n => ?_)
          (summable_vonMangoldt_mul_rpow_neg s.re hs)
          (summable_vonMangoldt_mul_rpow_neg 2 (by norm_num))
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · have hn1 : (1 : ℝ) ≤ (n : ℝ) :=
            by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          have hexp : -(s.re) ≤ -(2 : ℝ) := by linarith
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hn1 hexp)
            ArithmeticFunction.vonMangoldt_nonneg
      have h2 : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) =
          (-deriv riemannZeta ((2 : ℝ) : ℂ) / riemannZeta ((2 : ℝ) : ℂ)).re :=
        vonMangoldt_tsum_eq_zeta_re 2 (by norm_num)
      have h3 : (-deriv riemannZeta ((2 : ℝ) : ℂ) / riemannZeta ((2 : ℝ) : ℂ)).re ≤
          1 + Cz := by
        have hz2 := hz 2 (by norm_num) le_rfl
        norm_num at hz2
        exact hz2
      have h4 : (0 : ℝ) ≤ 1 / (s.re - 1) := by positivity
      linarith
  calc ‖logDeriv (DirichletCharacter.LFunction χ) s‖
      = ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s‖ := by rw [hld, norm_neg]
    _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := hbound
    _ ≤ 1 / (s.re - 1) + (Cz + 1) := hAub

end Commons.NumberTheory.DirichletCharacter
