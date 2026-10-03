import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A4c.MoebiusCore
import Submission.Work.FIArea4.A6Ener3_le
import Submission.Work.FIArea4.A6Cl.toPrimBoxCoeff
import Submission.Work.FIArea4.A4c.divBound_four_tau
import Submission.Work.FIArea4.A4c.exists_pow_log_le_rpow
import Submission.Work.FIArea4.A4c.N_mul_S15Br6_le
import Submission.Work.FIArea4.A4c.theta_tau_step7

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The last multiplication of step 7: from the `θτ`-facts produced by `theta_tau_step7`,
the factor `τ·L^E·(θ²N + N^{5/6} + 1)` is at most `3N`.  Indeed `τ = θ⁻¹` and `θ²τ = θ`, so the
factor equals `θ N L^E + N^{5/6}(θ⁻¹L^E) + θ⁻¹L^E ≤ N + N^{5/6}·N^{1/6} + N = 3N`. -/
lemma tau_L_theta_le (Pa : Work.FITop.Params) (L : ℝ) (E : ℕ)
    (hθτ : Pa.θ * Pa.τ = 1)
    (hθL : Pa.θ * L ^ E ≤ 1)
    (hθinvL6 : (Pa.θ)⁻¹ * L ^ E ≤ Pa.N ^ ((1 : ℝ) / 6))
    (hθinvL : (Pa.θ)⁻¹ * L ^ E ≤ Pa.N) :
    Pa.τ * L ^ E * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) ≤ 3 * Pa.N := by
  have hN0 : 0 ≤ Pa.N := by linarith only [Pa.hN1]
  have hNpos : 0 < Pa.N := by linarith only [Pa.hN1]
  have hθne : Pa.θ ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hθτ
    exact one_ne_zero hθτ.symm
  have hθsq : (Pa.θ)⁻¹ * Pa.θ ^ 2 = Pa.θ := by
    rw [pow_two]
    field_simp
  have hexp : Pa.τ * L ^ E * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
      = Pa.N * (Pa.θ * L ^ E) + Pa.N ^ ((5 : ℝ) / 6) * ((Pa.θ)⁻¹ * L ^ E)
          + (Pa.θ)⁻¹ * L ^ E := by
    rw [eq_inv_of_mul_eq_one_right hθτ]
    rw [show (Pa.θ)⁻¹ * L ^ E * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
        = ((Pa.θ)⁻¹ * Pa.θ ^ 2) * (L ^ E * Pa.N)
            + (Pa.θ)⁻¹ * L ^ E * Pa.N ^ ((5 : ℝ) / 6) + (Pa.θ)⁻¹ * L ^ E from by ring]
    rw [hθsq]
    ring
  rw [hexp]
  have h1 : Pa.N * (Pa.θ * L ^ E) ≤ Pa.N * 1 := mul_le_mul_of_nonneg_left hθL hN0
  have h2 : Pa.N ^ ((5 : ℝ) / 6) * ((Pa.θ)⁻¹ * L ^ E)
      ≤ Pa.N ^ ((5 : ℝ) / 6) * Pa.N ^ ((1 : ℝ) / 6) :=
    mul_le_mul_of_nonneg_left hθinvL6 (Real.rpow_nonneg hN0 _)
  have h3 : Pa.N ^ ((5 : ℝ) / 6) * Pa.N ^ ((1 : ℝ) / 6) = Pa.N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  rw [mul_one] at h1
  rw [h3] at h2
  linarith only [h1, h2, hθinvL]

/-- **The piece sum** (design `AREA4_ENGINES_LEAD.md` §3.3, node N5).

Inputs (both as explicit hypotheses, so that this node is independent of the nodes proving them):
`hRed : A6RedTProp` (the §15 reduction with the divisor factor `T` carried through) and
`hcard : CardDvdLe` (the divisor count `#(divisors of z) ≤ 4τ(|z|²)` for `Squarefree (gnorm z)`).

Proof route (all arithmetic must be done with `Real.rpow`, `set … ; clear_value` and
`linarith only`, never letting a tactic see `(log N+1)^(2^20)`):

1. `obtain ⟨C_R, x_R, hC_R, hRed⟩ := hRed ψ hψ h0 h1 hs`.
2. For `Pa` with both pins and `β` with `hβ : IsBetaCoeff6`, put `T := 4 * Pa.τ` and prove
   `Work.FIArea4.A4c.DivBound Pa β T`: for `z` with `β z ≠ 0`, `hβ.support` gives
   `N < |z|²` (so `z ≠ 0`), `hβ.squarefree_gnorm` gives `Squarefree (gnorm z)`, and the support
   clause of `IsBetaCoeff6` (`rw [the defining `if`] at hz; split_ifs at hz`) gives
   `((gnorm z).divisors.card : ℝ) ≤ Pa.τ`; then `hcard z hz0 hsq (… .filter (· ∣ z))` gives the
   bound, using `mul_le_mul_of_nonneg_left` and `4 * τ(gnorm z) ≤ 4 * Pa.τ`.
3. `Work.FIArea4.A6Cl.toPrimBoxCoeff hβ : IsPrimBoxCoeff Pa φ β`.
4. Each piece: `hRed Pa hx' X φ j β T hprim hdiv hX hX9` with
   `‖Tcut (radN Pa) (A6cut ψ X j) β‖ ≤ C_R (log N+1)^8 S15Br6 Pa X (T · A6Ener3 Pa β)`.
5. `A6Ener3_le` gives `∃ C_E, A6Ener3 Pa β ≤ C_E (θ²N + N^{5/6} + 1)(log N+1)^{2^20-30}`; with
   `T = 4Pa.τ` each piece is `≤ 4 C_R C_E Pa.τ (log N+1)^{2^20-22} S15Br6 (θ²N+N^{5/6}+1)`.
6. `∑_{j<J}` with `J ≤ 12(log N+1)²`
   (`Finset.sum_le_sum`, `Finset.sum_const`, `nsmul_eq_mul`) gives
   `≤ 48 C_R C_E Pa.τ (log N+1)^{2^20-20} S15Br6 (θ²N + N^{5/6} + 1)`.
7. With the pins (`thetaOf x A = (log x)^{-(2A+2^20)}`, `tauOf x A = (log x)^{2A+2^20}`,
   `Asave = 10^8`), `Pa.τ * Pa.θ = 1`, so the last display is
   `48 C_R C_E (log N+1)^{2^20-20} S15Br6 (θN + θ^{-1}N^{5/6} + θ^{-1})`.  `Pa.N < √(Pa.x)` gives
   `log N + 1 ≤ 2 log x`, hence `θ(log N+1)^{2^20-20} ≤ 2^{2^20}(log x)^{-(2·10^8+20)} ≤ 1` and
   `θ^{-1}(log N+1)^{2^20-20} ≤ N^{1/6}` for `log x ≥ 2`; also `Pa.hNlo` (`x^{1/4+η} < N`) gives
   `θ^{-1} ≤ N^{1/6}` and `θ^{-1} ≤ N` for `x ≥ x0`.  So the whole display is
   `≤ 48 C_R C_E · 3 · N · S15Br6`.
8. `N · S15Br6 ≤ 3 X^{-1/3} N²`: `X^{-1/2}N·N ≤ X^{-1/3}N²` (`X ≥ 1`);
   `N^{1/3}X^{-1/3}N^{2/3}·N = X^{-1/3}N²`; and
   `N^{23/24+1/1000}N ≤ X^{-1/3}N²` because `X^{1/3} ≤ N^{1/27}` (`X ≤ N^{1/9`) and
   `1/27 < 1/24 - 1/1000` (`X^{-1/3} ≥ N^{-1/27}`, so `N^{1+23/24+1/1000} ≤ N^{26/27}·X^{-1/3}N`).
   Hence `K = 288 C_R C_E` works; the two thresholds on `x` (step 7) and `(log N) ≥ (3c)^3`
   (there is no such term, but `N·S15Br6`'s middle term is exact) give `x0` — take the max of the
   thresholds; `h1 : 1 ≤ X` and `(log N)^2 ≤ X` are NOT needed.
   Every `(log N+1)^{2^20-…}` must be made opaque with `set … ; clear_value` before any
   arithmetic tactic sees it (project build rule). -/
theorem pieceSum_le (hRed : Work.FIArea4.A4c.A6RedTProp)
    (hcard : Work.FIArea4.A4c.CardDvdLe)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ∀ y : ℝ, 0 ≤ ψ y)
    (h1 : ∀ y : ℝ, ψ y ≤ 1) (hs : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) :
    ∃ K x0 : ℝ, 0 < K ∧ ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      Pa.θ = Work.FITop4.thetaOf Pa.x Work.FITop4.Asave →
      Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
    ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ) (J : ℕ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
      (J : ℝ) ≤ 12 * (Real.log Pa.N + 1) ^ 2 →
      ∑ j ∈ Finset.range J,
        ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (Work.FIArea4.A6cut ψ X j) β‖
        ≤ K * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
  obtain ⟨C_R, x_R, hC_R, hred⟩ := hRed ψ hψ h0 h1 hs
  obtain ⟨C_E, hC_E, hEner⟩ := A6Ener3_le
  obtain ⟨x_log, hx_log⟩ := exists_pow_log_le_rpow 300000000 (by norm_num) (1 / 24) (by norm_num)
  refine ⟨432 * C_R * C_E, max (max x_R (Real.exp (Real.exp 2))) x_log, ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) hC_R) hC_E
  · intro Pa hx0 hθ hτ X φ z0 β J hβ hX hX9 hJ
    have hx_R : x_R ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
    have hxexp : Real.exp (Real.exp 2) ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
    have hx_log' : x_log ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx0
    have hlog2 : (2 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
      have h2e : (2 : ℝ) ≤ Real.exp 2 := by
        have hexp := Real.add_one_le_exp (2 : ℝ); linarith only [hexp]
      calc (2 : ℝ) ≤ Real.exp 2 := h2e
        _ = Real.log (Real.exp (Real.exp 2)) := (Real.log_exp _).symm
        _ ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (Real.exp_pos _) hxexp
    have hxpow : (Real.log (Pa.x : ℝ)) ^ (300000000 : ℕ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 24) :=
      hx_log (Pa.x : ℝ) hx_log'
    obtain ⟨hθτ1, hθL, hθinvL6, hθinvL⟩ := theta_tau_step7 Pa hθ hτ hlog2 hxpow
    have hprim : Work.FIArea4.IsPrimBoxCoeff Pa φ β := Work.FIArea4.A6Cl.toPrimBoxCoeff hβ
    have hdiv : DivBound Pa β (4 * Pa.τ) := divBound_four_tau hcard Pa φ z0 β hβ
    set L : ℝ := Real.log Pa.N + 1 with hLdef
    clear_value L
    have hL1 : 1 ≤ L := by
      rw [hLdef]; exact le_add_of_nonneg_left (Real.log_nonneg Pa.hN1)
    have hL0 : 0 ≤ L := le_trans zero_le_one hL1
    have hN0 : 0 ≤ Pa.N := by linarith only [Pa.hN1]
    have hS15 : 0 ≤ Work.FIArea4.S15Br6 Pa X := S15Br6_nonneg Pa X
    have hτpos : 0 < Pa.τ := by
      rw [hτ]
      unfold Work.FITop4.tauOf
      exact Real.rpow_pos_of_pos (by linarith only [hlog2] : (0 : ℝ) < Real.log (Pa.x : ℝ)) _
    have hA0 : 0 ≤ Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1 := by
      have h1 : 0 ≤ Pa.θ ^ 2 := sq_nonneg Pa.θ
      have h2 : 0 ≤ Pa.θ ^ 2 * Pa.N := mul_nonneg h1 hN0
      have h3 : 0 ≤ Pa.N ^ ((5 : ℝ) / 6) := Real.rpow_nonneg hN0 _
      linarith only [h1, h2, h3]
    -- the per-piece bound
    have hpiece : ∀ j : ℕ,
        ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β‖
        ≤ 4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30)) * Work.FIArea4.S15Br6 Pa X
            * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) := by
      intro j
      have hR := hred Pa hx_R X φ j β (4 * Pa.τ) hprim hdiv hX hX9
      rw [← hLdef] at hR
      have hE := hEner Pa φ z0 β hβ
      rw [← hLdef] at hE
      have hT0 : 0 ≤ 4 * Pa.τ := by linarith only [le_of_lt hτpos]
      have hA : 0 ≤ C_R * L ^ 8 * Work.FIArea4.S15Br6 Pa X :=
        mul_nonneg (mul_nonneg (le_of_lt hC_R) (pow_nonneg hL0 8)) hS15
      have hE1 : (4 * Pa.τ) * Work.FIArea4.A6Ener3 Pa β
          ≤ (4 * Pa.τ) * (C_E * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
              * L ^ (((2 : ℕ) ^ 20) - 30)) :=
        mul_le_mul_of_nonneg_left hE hT0
      have h2 : C_R * L ^ 8 * Work.FIArea4.S15Br6 Pa X
            * ((4 * Pa.τ) * (C_E * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
                * L ^ (((2 : ℕ) ^ 20) - 30)))
          = 4 * C_R * C_E * Pa.τ * (L ^ 8 * L ^ (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X
              * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) := by ring
      refine le_trans hR ?_
      refine le_trans (mul_le_mul_of_nonneg_left hE1 hA) ?_
      rw [h2, ← pow_add]
    -- the sum
    have hB0 : 0 ≤ 4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
        * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) := by
      have h1 : 0 ≤ L ^ (8 + (((2 : ℕ) ^ 20) - 30)) := pow_nonneg hL0 _
      have h2 : 0 ≤ 4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
          * Work.FIArea4.S15Br6 Pa X :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
          (le_of_lt hC_R)) (le_of_lt hC_E)) (le_of_lt hτpos)) h1) hS15
      exact mul_nonneg h2 hA0
    have hLp : L ^ 2 * L ^ (8 + (((2 : ℕ) ^ 20) - 30)) = L ^ (10 + (((2 : ℕ) ^ 20) - 30)) := by
      rw [← pow_add]
      congr 1
    have hsum : ∑ j ∈ Finset.range J,
        ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β‖
        ≤ 48 * C_R * C_E * Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
            * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) := by
      have hs1 : ∑ j ∈ Finset.range J,
            ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β‖
          ≤ ∑ _j ∈ Finset.range J,
            (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)) :=
        Finset.sum_le_sum (fun j _ => hpiece j)
      have hs2 : (∑ _j ∈ Finset.range J,
            (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)))
          = (J : ℝ) * (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hJ' : (J : ℝ) ≤ 12 * L ^ 2 := hJ
      have hs3 : (J : ℝ) * (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1))
          ≤ (12 * L ^ 2) * (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)) :=
        mul_le_mul_of_nonneg_right hJ' hB0
      have hs4 : (12 * L ^ 2) * (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1))
          = 48 * C_R * C_E * Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) := by
        rw [show (12 * L ^ 2) * (4 * C_R * C_E * Pa.τ * L ^ (8 + (((2 : ℕ) ^ 20) - 30))
              * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1))
            = 48 * C_R * C_E * Pa.τ * (L ^ 2 * L ^ (8 + (((2 : ℕ) ^ 20) - 30)))
              * Work.FIArea4.S15Br6 Pa X
              * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) from by ring]
        rw [hLp]
      exact le_trans hs1 (le_trans hs2.le (le_trans hs3 (le_of_eq hs4)))
    -- step 7-8
    have hstep3 : 48 * C_R * C_E * Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
          * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
        ≤ 48 * C_R * C_E * (3 * Pa.N) * Work.FIArea4.S15Br6 Pa X := by
      have h1 : Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
          * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) ≤ 3 * Pa.N :=
        tau_L_theta_le Pa L (10 + (((2 : ℕ) ^ 20) - 30)) hθτ1 hθL hθinvL6 hθinvL
      have h2 : 0 ≤ 48 * C_R * C_E * Work.FIArea4.S15Br6 Pa X :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) (le_of_lt hC_R))
          (le_of_lt hC_E)) hS15
      have hEq : 48 * C_R * C_E * Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
            * Work.FIArea4.S15Br6 Pa X * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
          = (48 * C_R * C_E * Work.FIArea4.S15Br6 Pa X)
            * (Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
              * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)) := by ring
      rw [hEq]
      calc (48 * C_R * C_E * Work.FIArea4.S15Br6 Pa X)
              * (Pa.τ * L ^ (10 + (((2 : ℕ) ^ 20) - 30))
                * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1))
          ≤ (48 * C_R * C_E * Work.FIArea4.S15Br6 Pa X) * (3 * Pa.N) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = 48 * C_R * C_E * (3 * Pa.N) * Work.FIArea4.S15Br6 Pa X := by ring
    have hstep4 : 48 * C_R * C_E * (3 * Pa.N) * Work.FIArea4.S15Br6 Pa X
        ≤ 432 * C_R * C_E * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
      have h1 : Pa.N * Work.FIArea4.S15Br6 Pa X
          ≤ 3 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 :=
        N_mul_S15Br6_le Pa X hX hX9
      have h2 : 0 ≤ 144 * C_R * C_E :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 144) (le_of_lt hC_R)) (le_of_lt hC_E)
      have hEq : 48 * C_R * C_E * (3 * Pa.N) * Work.FIArea4.S15Br6 Pa X
          = (144 * C_R * C_E) * (Pa.N * Work.FIArea4.S15Br6 Pa X) := by ring
      rw [hEq]
      calc (144 * C_R * C_E) * (Pa.N * Work.FIArea4.S15Br6 Pa X)
          ≤ (144 * C_R * C_E) * (3 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = 432 * C_R * C_E * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by ring
    exact le_trans hsum (le_trans hstep3 hstep4)

end

end Work.FIArea4.A4c
