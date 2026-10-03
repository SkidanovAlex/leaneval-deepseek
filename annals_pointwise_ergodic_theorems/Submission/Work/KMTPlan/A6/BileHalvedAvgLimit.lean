import Mathlib
import Submission.Work.KMTPlan.A6.BileLiftDefs
import Submission.Work.Analysis.Concentration.Bilinear
import Submission.Work.KMTPlan.A6Aux.ResidueBlockSum
import Submission.Work.KMTPlan.A6Aux.NatDivDivTendsto
import Submission.Work.KMTPlan.A6Aux.LpNormZModOneTendsto

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The halved average at scale `N` converges to `½ · A(u,v)` in `L¹(ℤ/Qℤ)`

This file proves `Work.KMTPlan.A6.BileHalvedAvgLimit`: the halved window average

`bileHalvedAvg P N u v z = N⁻¹ ∑_{N/2 < n ≤ N} u(z-n) v(z-P(n))`

converges, as `N → ∞`, to `½` times the arithmetic bilinear average
`polyBilinearAverageZMod X P Q u v z = Q⁻¹ ∑_{y ∈ ℤ/Qℤ} u(z-y) v(z-P(y))` in the normalized
`L¹(ℤ/Qℤ)` norm.

The mathematical content is the equidistribution of the interval `(N/2, N]` over the residue
classes modulo `Q`: each class occurs `⌈N/2⌉/Q + O(1)` times and `⌈N/2⌉/N → 1/2` (so the
normalised count converges to `1/(2Q)`).  The proof is pointwise in `z`: the interval sum is
split into `⌊L/Q⌋` complete blocks of `Q` consecutive integers (each of which sums to the full
sum `∑_y f y`, by `ResidueBlockSum`) plus a remainder of `L % Q` terms, which is `O(Q‖f‖)` and
hence killed by the `N⁻¹` normalisation.  The arithmetic input is `NatDivDivTendsto`; the
passage from pointwise convergence to the convergence of the `L¹` norm is
`LpNormZModOneTendsto`.
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6

open Filter Finset
open Work.Analysis.Concentration

noncomputable section

/-! ## Reindexing an interval sum over `range` -/

/-- `∑_{n ∈ Icc b c} g n = ∑_{j < c+1-b} g (b+j)`. -/
private lemma sum_Icc_eq_sum_range_nat {M : Type*} [AddCommMonoid M] (g : ℕ → M) (b c : ℕ) :
    ∑ n ∈ Finset.Icc b c, g n = ∑ j ∈ Finset.range (c + 1 - b), g (b + j) := by
  rw [show Finset.Icc b c = Finset.Ico b (c + 1) from by
        ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]

/-! ## The decomposition of an interval sum over `ℤ/Qℤ` into complete blocks plus a remainder -/

/-- Splitting `Icc (a+1) (a+L)` into `L/Q` complete blocks of `Q` consecutive integers
(each of which sums to the full sum, by `ResidueBlockSum`) plus a remainder of `L % Q` terms. -/
private lemma icc_decomp {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) (a L : ℕ)
    (hb : ∀ k t : ℕ, ∑ j ∈ Finset.range (k * Q), f (((t + j : ℕ)) : ZMod Q)
      = (k : ℂ) * ∑ y : ZMod Q, f y) :
    ∑ n ∈ Finset.Icc (a + 1) (a + L), f (n : ZMod Q)
      = ((L / Q : ℕ) : ℂ) * (∑ y : ZMod Q, f y)
        + ∑ j ∈ Finset.range (L % Q), f (((a + 1 + (L / Q * Q + j) : ℕ)) : ZMod Q) := by
  rw [sum_Icc_eq_sum_range_nat (fun n => f (n : ZMod Q)) (a + 1) (a + L)]
  rw [show a + L + 1 - (a + 1) = L by omega]
  conv_lhs => rw [show L = L / Q * Q + L % Q from (Nat.div_add_mod' L Q).symm]
  rw [Finset.sum_range_add (fun x => f (((a + 1 + x : ℕ)) : ZMod Q)) (L / Q * Q) (L % Q)]
  congr 1
  exact hb (L / Q) (a + 1)

/-! ## The limit of the interval average -/

/-- **The averaging limit.**  For any `f` on `ℤ/Qℤ`, the averages over the halved window
`(N/2, N]` converge to `(2Q)⁻¹ ∑_y f y`, with the normalising factor `N⁻¹`. -/
private lemma intervalAvg_tendsto {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) :
    Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (N / 2 + 1) N, f (n : ZMod Q))
      Filter.atTop (nhds ((2 : ℂ)⁻¹ * (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y)) := by
  have hQ : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)
  have hblock : ∀ k t : ℕ, ∑ j ∈ Finset.range (k * Q), f (((t + j : ℕ)) : ZMod Q)
      = (k : ℂ) * ∑ y : ZMod Q, f y := fun k t => Work.KMTPlan.A6Aux.ResidueBlockSum k t f
  have hdecomp : ∀ N : ℕ, ∑ n ∈ Finset.Icc (N / 2 + 1) N, f (n : ZMod Q)
      = (((N - N / 2) / Q : ℕ) : ℂ) * (∑ y : ZMod Q, f y)
        + ∑ j ∈ Finset.range ((N - N / 2) % Q),
            f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q) := by
    intro N
    have h1 : N / 2 + (N - N / 2) = N := by omega
    have h2 := icc_decomp (Q := Q) f (N / 2) (N - N / 2) hblock
    rw [h1] at h2
    exact h2
  have hrem : ∀ N : ℕ,
      ‖∑ j ∈ Finset.range ((N - N / 2) % Q),
            f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q)‖
          ≤ (Q : ℝ) * ‖f‖ := by
    intro N
    have hr : (((N - N / 2) % Q : ℕ) : ℝ) ≤ (Q : ℝ) := by
      have hlt := Nat.mod_lt (N - N / 2) (Nat.pos_of_ne_zero (NeZero.ne Q))
      exact_mod_cast le_of_lt hlt
    calc ‖∑ j ∈ Finset.range ((N - N / 2) % Q),
            f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q)‖
        ≤ ∑ j ∈ Finset.range ((N - N / 2) % Q),
            ‖f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range ((N - N / 2) % Q), ‖f‖ :=
          Finset.sum_le_sum (fun j _ => norm_le_pi_norm f _)
      _ = (((N - N / 2) % Q : ℕ) : ℝ) * ‖f‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * ‖f‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg f)
  have h1 : Filter.Tendsto
      (fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℂ) * (N : ℂ)⁻¹ * (∑ y : ZMod Q, f y))
      Filter.atTop (nhds ((2 : ℂ)⁻¹ * (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y)) :=
    (Work.KMTPlan.A6Aux.NatDivDivTendsto Q hQ).mul_const _
  have h2 : Filter.Tendsto
      (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ Finset.range ((N - N / 2) % Q),
            f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun N : ℕ => (N : ℝ)⁻¹ * ((Q : ℝ) * ‖f‖))
      (fun N => ?_) ?_
    · calc ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range ((N - N / 2) % Q),
              f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q)‖
          ≤ ‖(N : ℂ)⁻¹‖ * ‖∑ j ∈ Finset.range ((N - N / 2) % Q),
              f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q)‖ := norm_mul_le _ _
        _ ≤ (N : ℝ)⁻¹ * ((Q : ℝ) * ‖f‖) := by
            refine mul_le_mul ?_ (hrem N) (norm_nonneg _) ?_
            · rw [norm_inv, Complex.norm_natCast]
            · positivity
    · have h0 := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const
          ((Q : ℝ) * ‖f‖)
      rw [zero_mul] at h0
      exact h0
  have hsum := h1.add h2
  have hfun : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (N / 2 + 1) N, f (n : ZMod Q))
      = fun N : ℕ => (((N - N / 2) / Q : ℕ) : ℂ) * (N : ℂ)⁻¹ * (∑ y : ZMod Q, f y)
          + (N : ℂ)⁻¹ * ∑ j ∈ Finset.range ((N - N / 2) % Q),
              f (((N / 2 + 1 + ((N - N / 2) / Q * Q + j) : ℕ)) : ZMod Q) := by
    funext N
    rw [hdecomp N]
    ring
  rw [hfun]
  simpa using hsum

/-! ## Pointwise convergence of the halved bilinear average -/

private lemma bileHalvedAvg_tendsto (P : Polynomial ℤ) {Q : ℕ} [NeZero Q] (u v : ZMod Q → ℂ)
    (z : ZMod Q) :
    Filter.Tendsto (fun N : ℕ => bileHalvedAvg P N u v z) Filter.atTop
      (nhds ((1 / 2 : ℂ) * polyBilinearAverageZMod Polynomial.X P Q u v z)) := by
  have hdecomp : ∀ N : ℕ, bileHalvedAvg P N u v z
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (N / 2 + 1) N,
          (fun y : ZMod Q => u (z - y) * v (z - polyEvalZMod P Q y)) (n : ZMod Q) := by
    intro N
    rw [bileHalvedAvg]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have h1 : ((n : ℤ) : ZMod Q) = (n : ZMod Q) := by simp
    have h2 : ((Polynomial.eval (n : ℤ) P : ℤ) : ZMod Q) = polyEvalZMod P Q (n : ZMod Q) :=
      (polyEvalZMod_natCast P Q n).symm
    rw [h1, h2]
  rw [show (fun N : ℕ => bileHalvedAvg P N u v z)
      = fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (N / 2 + 1) N,
          (fun y : ZMod Q => u (z - y) * v (z - polyEvalZMod P Q y)) (n : ZMod Q) from
        funext hdecomp]
  have h := intervalAvg_tendsto (Q := Q)
    (fun y : ZMod Q => u (z - y) * v (z - polyEvalZMod P Q y))
  have hgoal : (2 : ℂ)⁻¹ * (Q : ℂ)⁻¹
        * ∑ y : ZMod Q, u (z - y) * v (z - polyEvalZMod P Q y)
      = (1 / 2 : ℂ) * polyBilinearAverageZMod Polynomial.X P Q u v z := by
    rw [polyBilinearAverageZMod]
    simp only [polyEvalZMod_X]
    ring
  rw [hgoal] at h
  exact h

/-! ## The limit of the `L¹` norm, and the final statement -/

theorem BileHalvedAvgLimit (P : Polynomial ℤ) {Q : ℕ} [NeZero Q] (u v : ZMod Q → ℂ) :
    Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (Work.KMTPlan.A6.bileHalvedAvg P N u v)))
      Filter.atTop
      (nhds (ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (fun z : ZMod Q => (1 / 2 : ℂ) *
          Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q u v z)))) := by
  refine ENNReal.tendsto_ofReal ?_
  exact Work.KMTPlan.A6Aux.LpNormZModOneTendsto
    (fun z => bileHalvedAvg_tendsto P u v z)

end

end Work.KMTPlan.A6
