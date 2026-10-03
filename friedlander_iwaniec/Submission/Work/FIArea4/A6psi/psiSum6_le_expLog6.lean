/-
# Area 4 (round 6): the separation step `S15psiSum6 <= (log N)^2 * M`

The round-6 analogue of `Work.FIArea4.S15psi_relaxed.S15psiSum_le_expLog_sharp`: the psi-cut sum
`S15psiSum6` (built from FI's ratio symbol and the round-6 logarithm `logFac6`) is dominated by
`(log N + 1)^2` times a uniform bound `M` for the *separated* exponential sums `S15expLog6`.

The proof is the paper's FI (12.13)-(12.14) separation of variables, verbatim as in the frozen
chain: the only analytic input is `S15red.sep_uniform`, which is symbol-agnostic (it uses only the
smoothness and the support of `psi`).  The round-6 sum differs from the frozen one only in the
*coefficient* `S15coef6`, which plays no role in the separation:

* the index set is cut down to the support `A6supp` of `beta` (every pair then lies in the polar
  box, and `S15coef6` vanishes off that support);
* on the support the separating variables satisfy `1/(4N) <= |x| <= 2N` and `0 < y`
  (`A6supp_bounds`), so the `nearCut` of `sep_uniform` equals `1`;
* hence `S15psiSum6` is `sep_uniform` applied to `iota = A6supp ...`, `x = S15x`, `y = S15y` and
  `c = S15coef6 beta * logFac6`, with `log (2 + b/a) + 1 <= 4 (log N + 1)`.
-/
import Mathlib
import Submission.Work.FIArea4.A6psi.Defs
import Submission.Work.FIArea4.S15red.sep_uniform
import Submission.Work.FIArea4.A6supp6

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 4000000

/-- The round-6 coefficient vanishes as soon as one of the two Gaussian integers is outside the
support of `beta`. -/
lemma S15coef6_eq_zero_of_supp {β : GaussianInt → ℂ} {i : Work.FIArea4.S15Id}
    (h : β i.1.1 = 0 ∨ β i.1.2 = 0) : S15coef6 β i = 0 := by
  rcases h with h | h
  · rw [S15coef6, h]; ring
  · rw [S15coef6, h, star_zero]; ring

/-- `S15expLog6` as a sum over the subtype of the support of `beta` (the normal form of the
exponential sums of `sep_uniform`). -/
lemma S15expLog6_eq_subtype_sum (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (u t : ℝ) :
    S15expLog6 Pa X j β u t
      = ∑ i : ↥(Work.FIArea4.A6supp Pa X j β),
          S15coef6 β i.1 * ((Work.FITop4.logFac6 i.1.1.1 i.1.1.2 : ℝ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (u * Work.FIArea4.S15x i.1.1.1 i.1.1.2)) *
            ((Work.FIArea4.S15y X j i.1.2 i.1.1.1 i.1.1.2 : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
  have hsupp : S15expLog6 Pa X j β u t
      = ∑ i ∈ Work.FIArea4.A6supp Pa X j β,
          S15coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ)
            * Work.FIArea4.S15phase X j u t i := by
    rw [show S15expLog6 Pa X j β u t = ∑ i ∈ Work.FIArea4.S15ixSet Pa X j,
        S15coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ)
          * Work.FIArea4.S15phase X j u t i from rfl]
    exact Work.FIArea4.A6sum_S15ixSet_eq_sum_supp
      (f := fun z1 z2 d => S15coef6 β ((z1, z2), d)
        * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) * Work.FIArea4.S15phase X j u t ((z1, z2), d))
      Pa X j β (fun z1 z2 d h => by rw [S15coef6_eq_zero_of_supp (i := ((z1, z2), d)) h]; ring)
  rw [hsupp, Work.FIArea4.A6sum_eq_sum_univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.FIArea4.S15phase]
  ring

/-- `S15psiSum6` as a sum over the subtype of the support of `beta`, with the `nearCut` factor of
`sep_uniform`. -/
lemma S15psiSum6_eq_subtype_sum (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ)
    (β : GaussianInt → ℂ) {a b : ℝ}
    (hnc : ∀ i : ↥(Work.FIArea4.A6supp Pa X j β),
      Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.S15x i.1.1.1 i.1.1.2) = 1) :
    S15psiSum6 Pa X j ψ β
      = ∑ i : ↥(Work.FIArea4.A6supp Pa X j β),
          S15coef6 β i.1 * ((Work.FITop4.logFac6 i.1.1.1 i.1.1.2 : ℝ) : ℂ) *
            ((ψ (|Work.FIArea4.S15x i.1.1.1 i.1.1.2| * Work.FIArea4.S15y X j i.1.2 i.1.1.1 i.1.1.2)
                * Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.S15x i.1.1.1 i.1.1.2) : ℝ) : ℂ) := by
  have hsupp : S15psiSum6 Pa X j ψ β
      = ∑ i ∈ Work.FIArea4.A6supp Pa X j β,
          S15coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ) *
            ((ψ (|Work.FIArea4.S15x i.1.1 i.1.2|
              * Work.FIArea4.S15y X j i.2 i.1.1 i.1.2) : ℝ) : ℂ) := by
    rw [show S15psiSum6 Pa X j ψ β = ∑ i ∈ Work.FIArea4.S15ixSet Pa X j,
        S15coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ) *
          ((ψ (|Work.FIArea4.S15x i.1.1 i.1.2|
            * Work.FIArea4.S15y X j i.2 i.1.1 i.1.2) : ℝ) : ℂ) from rfl]
    exact Work.FIArea4.A6sum_S15ixSet_eq_sum_supp
      (f := fun z1 z2 d => S15coef6 β ((z1, z2), d)
        * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
        * ((ψ (|Work.FIArea4.S15x z1 z2| * Work.FIArea4.S15y X j d z1 z2) : ℝ) : ℂ))
      Pa X j β (fun z1 z2 d h => by rw [S15coef6_eq_zero_of_supp (i := ((z1, z2), d)) h]; ring)
  rw [hsupp, Work.FIArea4.A6sum_eq_sum_univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hnc i, mul_one]

/-- **The separation of variables for the round-6 §15 `psi`-cut sum (FI (12.13)-(12.14)).**  If `M`
bounds the separated exponential sums `S15expLog6` of the relaxed index set, then the `psi`-cut sum
`S15psiSum6` is bounded by `(log N + 1)^2` times `M`, uniformly in the box coefficient `beta`.

This is the round-6 analogue of `Work.FIArea4.S15psi_relaxed.S15psiSum_le_expLog_sharp`: the
coefficient `S15coef6` (which carries FI's ratio symbol) enters only through the hypothesis `hM`,
and the separation inequality `S15red.sep_uniform` is used at the support of `beta`, where
`1/(4N) <= |x| <= 2N`, `y > 0`, and the `nearCut` is `1`. -/
theorem psiSum6_le_expLog6 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψsup : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
      (M : ℝ),
      Work.FIArea4.IsPrimBoxCoeff Pa φ β → 1 ≤ X →
      (∀ u t : ℝ, ‖Work.FIArea4.A6psi.S15expLog6 Pa X j β u t‖ ≤ M) →
      ‖Work.FIArea4.A6psi.S15psiSum6 Pa X j ψ β‖ ≤ C * (Real.log Pa.N + 1) ^ 2 * M := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FIArea4.S15red.sep_uniform hψ hψsup
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro Pa X j φ β M hβ hX hM
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  set a : ℝ := 1 / (4 * Pa.N) with ha
  set b : ℝ := 2 * Pa.N with hb
  have hapos : 0 < a := by rw [ha]; positivity
  have hab : a ≤ b := by
    rw [ha, hb, div_le_iff₀ (by positivity)]
    nlinarith [hN1]
  have hy : ∀ i : ↥(Work.FIArea4.A6supp Pa X j β),
      0 < Work.FIArea4.S15y X j i.1.2 i.1.1.1 i.1.1.2 :=
    fun i => (Work.FIArea4.A6supp_bounds Pa X j hβ hX i.2).2.2
  have hexp : ∀ u t : ℝ,
      ‖∑ i : ↥(Work.FIArea4.A6supp Pa X j β),
          S15coef6 β i.1 * ((Work.FITop4.logFac6 i.1.1.1 i.1.1.2 : ℝ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (u * Work.FIArea4.S15x i.1.1.1 i.1.1.2)) *
            ((Work.FIArea4.S15y X j i.1.2 i.1.1.1 i.1.1.2 : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖
        ≤ M :=
    fun u t => by rw [← S15expLog6_eq_subtype_sum]; exact hM u t
  have key := hC₀ a b hapos hab ↥(Work.FIArea4.A6supp Pa X j β)
      (fun i => Work.FIArea4.S15x i.1.1.1 i.1.1.2)
      (fun i => Work.FIArea4.S15y X j i.1.2 i.1.1.1 i.1.1.2)
      (fun i => S15coef6 β i.1 * ((Work.FITop4.logFac6 i.1.1.1 i.1.1.2 : ℝ) : ℂ)) M hy hexp
  have hnc : ∀ i : ↥(Work.FIArea4.A6supp Pa X j β),
      Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.S15x i.1.1.1 i.1.1.2) = 1 := by
    intro i
    obtain ⟨h1, h2, _⟩ := Work.FIArea4.A6supp_bounds Pa X j hβ hX i.2
    exact Work.FIArea4.Vflip.nearCut_eq_one hapos h1 h2
  rw [S15psiSum6_eq_subtype_sum Pa X j ψ β hnc]
  have hlog : Real.log (2 + b / a) + 1 ≤ 4 * (Real.log Pa.N + 1) := by
    have hba : b / a = 8 * Pa.N ^ 2 := by
      rw [ha, hb]; field_simp; ring
    rw [hba]
    have hlogN : 0 ≤ Real.log Pa.N := Real.log_nonneg hN1
    have hstep : Real.log (2 + 8 * Pa.N ^ 2) ≤ Real.log 10 + 2 * Real.log Pa.N := by
      calc Real.log (2 + 8 * Pa.N ^ 2) ≤ Real.log (10 * Pa.N ^ 2) := by
            apply Real.log_le_log (by positivity)
            nlinarith
        _ = Real.log 10 + Real.log (Pa.N ^ 2) := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log 10 + 2 * Real.log Pa.N := by
            rw [Real.log_pow]; push_cast; ring
    have h10 : Real.log 10 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)]
      have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 5
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
      linarith
    linarith
  have hargnn : 0 ≤ Real.log (2 + b / a) + 1 := by
    have hbpos : 0 < b / a := div_pos (by rw [hb]; linarith) hapos
    have : 0 ≤ Real.log (2 + b / a) := Real.log_nonneg (by linarith)
    linarith
  have hsq : (Real.log (2 + b / a) + 1) ^ 2 ≤ 16 * (Real.log Pa.N + 1) ^ 2 := by
    have h1 : (Real.log (2 + b / a) + 1) ^ 2 ≤ (4 * (Real.log Pa.N + 1)) ^ 2 :=
      pow_le_pow_left₀ hargnn hlog 2
    nlinarith [h1, Real.log_nonneg hN1]
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 0)
  calc ‖∑ i : ↥(Work.FIArea4.A6supp Pa X j β),
        S15coef6 β i.1 * ((Work.FITop4.logFac6 i.1.1.1 i.1.1.2 : ℝ) : ℂ) *
          ((ψ (|Work.FIArea4.S15x i.1.1.1 i.1.1.2|
              * Work.FIArea4.S15y X j i.1.2 i.1.1.1 i.1.1.2)
            * Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.S15x i.1.1.1 i.1.1.2) : ℝ) : ℂ)‖
      ≤ C₀ * (Real.log (2 + b / a) + 1) ^ 2 * M := key
    _ ≤ C₀ * (16 * (Real.log Pa.N + 1) ^ 2) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC₀pos.le) hMnn
    _ = 16 * C₀ * (Real.log Pa.N + 1) ^ 2 * M := by ring

end

end Work.FIArea4.A6psi
