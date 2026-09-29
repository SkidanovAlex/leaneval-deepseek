import Mathlib
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.Core.Ablock_res
import Submission.Work.TMC16Core.Core.pd_le_of_decay_win
import Submission.Work.TMC16Core.Core.Ablock_res_win_degen

/-!
# `Work.TMC16Core.Core.Ablock_res_win` — the resonant `A`-block with a *windowed* bound

This is AJ's Lemma 9.11 (`Work.Core.Ablock_res`) with the continuant hypothesis `hbd`
restricted to the scales `m ≥ (2n-1)/40`, which is the form in which AJ's §9 argument
actually supplies it (cf. `Basic.green_bound_notA_win`, `Basic.lemma_9_2_win`).  The
restriction matters: at scale `m = 1` a bound `‖pd‖ ≤ e^{(L+ε₁)}` would force a slack
`log 4`, which the `A`-deficit `3L/16` cannot afford for small coupling.

The two scales at which `hbd` is consumed in the Poisson/Cramér step are the lengths of the
complementary windows `(0-x).toNat` and `(x₂-0).toNat` for `x ∈ A2blk (2n-1)`, `x₂ = x+K-1`;
both lie in `[3K/16 - 1, 13K/16]` with `K = 2n-1`, hence in particular `≥ K/40` — that is the
whole content of the two arithmetic lemmas below.

* non-degenerate case `L + ε₁ ≥ 0`: `pd_le_of_decay_win` (Poisson + Cramér) plus the
  numerical hypothesis `hnum`;
* degenerate case `L + ε₁ < 0`: `Ablock_res_win_degen` (reconstruction `sol_recon` forces
  `B ≥ 1/2`, and then the trivial bound at scale `2n-1` suffices).
-/

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-! ## Arithmetic: the two scales at which `hbd` is consumed are `≥ K/40` -/

private lemma div40_le_b316 (K : ℕ) : ((K / 40 : ℕ) : ℤ) ≤ b316 K := by
  have h1 : ((K / 40 : ℕ) : ℝ) ≤ (K : ℝ) / 40 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 40)]
    exact_mod_cast Nat.div_mul_le_self K 40
  have h2 : (K : ℝ) / 40 ≤ (3 : ℝ) * (K : ℝ) / 16 := by
    have := Nat.cast_nonneg K (α := ℝ); nlinarith
  have h3 : (3 : ℝ) * (K : ℝ) / 16 ≤ ((b316 K : ℤ) : ℝ) := Int.le_ceil _
  have h4 : (((K / 40 : ℕ) : ℤ) : ℝ) ≤ ((b316 K : ℤ) : ℝ) := by
    push_cast
    exact le_trans h1 (le_trans h2 h3)
  exact Int.cast_le.mp h4

private lemma div40_le_left_end (K : ℕ) (hK : 1 ≤ K) :
    ((K / 40 : ℕ) : ℤ) ≤ (K : ℤ) - 1 - b1316 K := by
  rcases le_or_gt K 12 with h12 | h12
  · have h0 : K / 40 = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0]
    simp only [Nat.cast_zero]
    have hb : b1316 K < (K : ℤ) := by
      rw [b1316]
      exact Int.floor_lt.mpr (by
        have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
        push_cast
        linarith)
    omega
  · have h13 : 13 ≤ K := by omega
    have h1 : ((K / 40 : ℕ) : ℝ) ≤ (K : ℝ) / 40 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 40)]
      exact_mod_cast Nat.div_mul_le_self K 40
    have h2 : (K : ℝ) / 40 ≤ (3 : ℝ) * (K : ℝ) / 16 - 1 := by
      have h13' : (13:ℝ) ≤ (K:ℝ) := by exact_mod_cast h13
      nlinarith
    have h3 : (3 : ℝ) * (K : ℝ) / 16 - 1 ≤ (((K : ℤ) - 1 - b1316 K : ℤ) : ℝ) := by
      have hf : ((b1316 K : ℤ) : ℝ) ≤ (13 : ℝ) * (K : ℝ) / 16 := Int.floor_le _
      push_cast
      linarith
    have h4 : (((K / 40 : ℕ) : ℤ) : ℝ) ≤ (((K : ℤ) - 1 - b1316 K : ℤ) : ℝ) :=
      le_trans h1 (le_trans h2 h3)
    exact Int.cast_le.mp h4

/-- STUB - will come from the delegated module. -/
theorem Ablock_res_win {α lam L ε ε₁ B : ℝ} {E : ℂ} {θ : ℝ} {n : ℕ} {u : ℤ → ℂ}
    (hL : 0 < L) (hεε₁ : ε₁ < ε) (hn : 2 ≤ n) (hB : 0 < B)
    (hbd : ∀ m : ℕ, (2 * n - 1) / 40 ≤ m → m ≤ 2 * n - 1 → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (m + 1)‖ ≤ Real.exp ((m : ℝ) * (L + ε₁)))
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) (hu0 : u 0 = 1)
    (hdecay : ∀ x ∈ Work.TMC16Core.Core.A2blk (2 * n - 1),
      ‖u (x - 1)‖ ≤ B ∧ ‖u (x + ((2 * n - 1 : ℕ) : ℤ))‖ ≤ B)
    (hnum : 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
      ≤ Real.exp (((2 * n : ℕ) : ℝ) * ((23 / 32 : ℝ) * L + ε))) :
    ∀ x ∈ Work.TMC16Core.Core.A2blk (2 * n - 1),
      ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (2 * n)‖ ≤
        Real.exp (((2 * n : ℕ) : ℝ) * ((23 / 32 : ℝ) * L + ε)) := by
  intro x hx
  by_cases hD : 0 ≤ L + ε₁
  · obtain ⟨hxlo, hxhi⟩ := Work.Core.mem_A2blk.mp hx
    have hK1 : 1 ≤ 2 * n - 1 := by omega
    have hxR : ((x : ℤ) : ℝ) ≤ -((b316 (2 * n - 1) : ℤ) : ℝ) := by exact_mod_cast hxhi
    have hxloR : -((b1316 (2 * n - 1) : ℤ) : ℝ) ≤ ((x : ℤ) : ℝ) := by exact_mod_cast hxlo
    have hb316R := Work.Core.b316_ge_cast (2 * n - 1)
    have hb1316R := Work.Core.b1316_le_cast (2 * n - 1)
    have hx0 : x ≤ 0 := by
      have h' : (0 : ℝ) < ((b316 (2 * n - 1) : ℤ) : ℝ) := by
        have h1 : (0 : ℝ) < (3 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16 := by
          have : (0 : ℝ) < ((2 * n - 1 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 0 < 2 * n - 1)
          linarith
        have h2 := Work.Core.b316_ge_cast (2 * n - 1)
        linarith
      have h'' : (0 : ℤ) < b316 (2 * n - 1) := by exact_mod_cast h'
      omega
    have hposK : 0 ≤ x + ((2 * n - 1 : ℕ) : ℤ) - 1 := by
      have hb := Work.Core.b1316_le_pred (K := 2 * n - 1) hK1
      omega
    by_cases hP : pd α lam (θ + (x : ℝ) * α) E (2 * n) = 0
    · rw [hP, norm_zero]; exact (Real.exp_pos _).le
    · have hdec1 : ‖u (x - 1)‖ ≤ B := (hdecay x hx).1
      have hdec2 : ‖u (x + ((2 * n - 1 : ℕ) : ℤ))‖ ≤ B := (hdecay x hx).2
      have hdec2' : ‖u ((x + ((2 * n - 1 : ℕ) : ℤ) - 1) + 1)‖ ≤ B := by
        rw [show x + ((2 * n - 1 : ℕ) : ℤ) - 1 + 1 = x + ((2 * n - 1 : ℕ) : ℤ) by ring]
        exact hdec2
      have hm1 : ((x + ((2 * n - 1 : ℕ) : ℤ) - 1) - 0).toNat ≤ 2 * n - 1 := by
        rw [Int.toNat_le]; omega
      have hm2 : (0 - x).toNat ≤ 2 * n - 1 := by
        rw [Int.toNat_le]
        have hb := Work.Core.b1316_le_pred (K := 2 * n - 1) hK1
        omega
      have hn1 : (2 * n - 1) / 40 ≤ ((x + ((2 * n - 1 : ℕ) : ℤ) - 1) - 0).toNat := by
        have hA : (((2 * n - 1) / 40 : ℕ) : ℤ) ≤ ((2 * n - 1 : ℕ) : ℤ) - 1 - b1316 (2 * n - 1) :=
          div40_le_left_end (2 * n - 1) hK1
        have hA0 : (0 : ℤ) ≤ ((2 * n - 1 : ℕ) : ℤ) - 1 - b1316 (2 * n - 1) :=
          le_trans (Nat.cast_nonneg _) hA
        have hC : ((2 * n - 1 : ℕ) : ℤ) - 1 - b1316 (2 * n - 1) ≤
            (x + ((2 * n - 1 : ℕ) : ℤ) - 1) - 0 := by omega
        have hz : (((2 * n - 1) / 40 : ℕ) : ℤ) ≤
            ((((x + ((2 * n - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℕ) : ℤ) :=
          calc (((2 * n - 1) / 40 : ℕ) : ℤ)
              ≤ ((2 * n - 1 : ℕ) : ℤ) - 1 - b1316 (2 * n - 1) := hA
            _ = ((((2 * n - 1 : ℕ) : ℤ) - 1 - b1316 (2 * n - 1)).toNat : ℤ) := by
                rw [Int.toNat_of_nonneg hA0]
            _ ≤ ((((x + ((2 * n - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℕ) : ℤ) := by
                exact_mod_cast Int.toNat_le_toNat hC
        exact_mod_cast hz
      have hn2 : (2 * n - 1) / 40 ≤ (0 - x).toNat := by
        have hA : (((2 * n - 1) / 40 : ℕ) : ℤ) ≤ b316 (2 * n - 1) := div40_le_b316 (2 * n - 1)
        have hA0 : (0 : ℤ) ≤ b316 (2 * n - 1) := le_trans (Nat.cast_nonneg _) hA
        have hC : b316 (2 * n - 1) ≤ 0 - x := by omega
        have hz : (((2 * n - 1) / 40 : ℕ) : ℤ) ≤ (((0 - x).toNat : ℕ) : ℤ) :=
          calc (((2 * n - 1) / 40 : ℕ) : ℤ) ≤ b316 (2 * n - 1) := hA
            _ = ((b316 (2 * n - 1)).toNat : ℤ) := by rw [Int.toNat_of_nonneg hA0]
            _ ≤ (((0 - x).toNat : ℕ) : ℤ) := by exact_mod_cast Int.toNat_le_toNat hC
        exact_mod_cast hz
      have hmain := pd_le_of_decay_win (K := 2 * n - 1) (x := x)
        (x₂ := x + ((2 * n - 1 : ℕ) : ℤ) - 1) (n₀ := (2 * n - 1) / 40) hB rfl
        (fun m hm1' hm2' ζ => hbd m hm1' hm2' ζ) hm1 hm2 hn1 hn2 hsol hu0 hdec1 hdec2'
        hx0 hposK (by rw [show 2 * n - 1 + 1 = 2 * n by omega]; exact hP)
      rw [show 2 * n - 1 + 1 = 2 * n by omega] at hmain
      have hz1 : (0 : ℤ) ≤ x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0 := by omega
      have hz2 : (0 : ℤ) ≤ 0 - x := by omega
      have hcast1 : (((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ))
          = ((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0 : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hz1]
      have hcast2 : ((((0 - x).toNat : ℕ) : ℝ)) = ((0 - x : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hz2]
      have harg1 : (((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ))
          ≤ (13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16 := by
        rw [hcast1]
        push_cast
        linarith
      have harg2 : (((0 - x).toNat : ℝ)) ≤ (13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16 := by
        rw [hcast2]
        push_cast
        linarith
      have ht : ((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)
          = (L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)) := by ring
      have hA1 : Real.exp ((((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ) * (L + ε₁)))
          ≤ Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)) :=
        Real.exp_le_exp.mpr (le_trans (mul_le_mul_of_nonneg_right harg1 hD) le_rfl)
      have hA2 : Real.exp (((((0 - x).toNat : ℝ)) * (L + ε₁)))
          ≤ Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)) :=
        Real.exp_le_exp.mpr (le_trans (mul_le_mul_of_nonneg_right harg2 hD) le_rfl)
      have hsum2 : B * (Real.exp ((((x + ((2 * n - 1 : ℕ) : ℤ) - 1 - 0).toNat : ℝ) * (L + ε₁)))
              + Real.exp (((((0 - x).toNat : ℝ)) * (L + ε₁))))
          ≤ B * (Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁))
              + Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hB)
        linarith
      have hEq : B * (Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁))
              + Real.exp (((13 : ℝ) * ((2 * n - 1 : ℕ) : ℝ) / 16) * (L + ε₁)))
          = 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))) := by
        rw [ht]; ring
      exact le_trans hmain (le_trans hsum2 (hEq.le.trans hnum))
  · exact Ablock_res_win_degen hL hεε₁ hn hB hbd hsol hu0 hdecay hnum (lt_of_not_ge hD) x hx

end Work.TMC16Core.Core
