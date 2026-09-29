import Mathlib
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.Core.Ablock_res

/-!
# `Work.TMC16Core.Core.Ablock_res_win_degen` — the resonant `A`-block, degenerate regime

This is the *degenerate* (`L + ε₁ < 0`) half of the "restricted `hbd`" variant of
`Work.Core.Ablock_res` (AJ Lemma 9.11).  The difference from `Work.Core.Ablock_res` is that
the continuant bound `hbd` is only assumed for indices `m ≥ (2n-1)/40`, which is all AJ ever
use; in the degenerate regime the remaining ingredients are

* `degen_site_bounds`: the two sites `y = -⌈3K/16⌉ - 1`, `y+1` lie in `A2blk K`, and `n₀ = -y`
  satisfies `1 ≤ n₀ ≤ K` together with the two restricted-range conditions
  `K/40 ≤ n₀`, `K/40 ≤ n₀ - 1` (`K = 2n-1`);
* `degen_half_le_B`: reconstructing `u 0` from the two consecutive decaying sites `y`, `y-1`
  (`Work.Core.sol_recon`) forces `1 ≤ 2B`, because in this regime all continuants *shrink*;
* and then the *trivial* bound `‖P_K(θ+xα)‖ ≤ e^{K(L+ε₁)}` at `m = K` suffices, the numerical
  hypothesis `hnum` absorbing the remaining slack.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- Arithmetic of the degenerate site: for `K ≥ 3`, the sites `y = -⌈3K/16⌉ - 1` and `y+1`
lie in the `A`-block, and `n₀ = -y` satisfies all the range conditions needed to apply the
restricted continuant bound. -/
lemma degen_site_bounds {K : ℕ} (hK : 3 ≤ K) {y : ℤ} (hy : y = -(b316 K) - 1) {n₀ : ℕ}
    (hn₀ : n₀ = (-y).toNat) :
    y ∈ A2blk K ∧ y + 1 ∈ A2blk K ∧ ((n₀ : ℕ) : ℤ) = -y ∧ y + (n₀ : ℤ) = 0 ∧
      1 ≤ n₀ ∧ n₀ ≤ K ∧ K / 40 ≤ n₀ ∧ K / 40 ≤ n₀ - 1 := by
  have hK1 : 1 ≤ K := by omega
  have hK2 : 2 ≤ K := by omega
  have hbpos : 0 < b316 K := Work.Core.b316_pos hK1
  have hle₁ : b316 K + 1 ≤ b1316 K := Work.Core.b316_succ_le_b1316 hK
  have hle₂ : b316 K ≤ b1316 K := Work.Core.b316_le_b1316 hK
  have hpred : b316 K ≤ (K : ℤ) - 1 := Work.Core.b316_le_pred hK2
  have hint := Work.Core.int_bounds K
  have hnegy : -y = b316 K + 1 := by rw [hy]; ring
  have hcast : ((n₀ : ℕ) : ℤ) = -y := by
    rw [hn₀, hnegy]
    exact Int.toNat_of_nonneg (by omega)
  have hn₀nat : n₀ = (b316 K + 1).toNat := by rw [hn₀, hnegy]
  -- the `ℕ`-division condition, at the level of `b316`
  have hbdiv : K / 40 ≤ (b316 K).toNat := by
    have hbz : (0 : ℤ) ≤ b316 K := le_of_lt hbpos
    have hKb : (K : ℤ) ≤ 40 * ((b316 K).toNat : ℕ) := by
      rw [Int.toNat_of_nonneg hbz]
      omega
    exact Nat.div_le_of_le_mul (by exact_mod_cast hKb)
  have hn₀sub : ((n₀ - 1 : ℕ) : ℤ) = b316 K := by
    have h1 : (1 : ℕ) ≤ n₀ := by
      have : (1 : ℤ) ≤ ((n₀ : ℕ) : ℤ) := by rw [hcast]; omega
      exact_mod_cast this
    rw [Nat.cast_sub h1, hcast, hnegy]
    ring
  have hsubcast : (n₀ - 1 : ℕ) = (b316 K).toNat := by
    have h0 : (0 : ℤ) ≤ b316 K := le_of_lt hbpos
    have : (((n₀ - 1 : ℕ)) : ℤ) = (((b316 K).toNat : ℕ) : ℤ) := by
      rw [hn₀sub, Int.toNat_of_nonneg h0]
    exact_mod_cast this
  refine ⟨?_, ?_, hcast, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Work.Core.mem_A2blk]
    constructor <;> omega
  · rw [Work.Core.mem_A2blk]
    constructor <;> omega
  · rw [hcast]; ring
  · have : (1 : ℤ) ≤ ((n₀ : ℕ) : ℤ) := by rw [hcast]; omega
    exact_mod_cast this
  · have : ((n₀ : ℕ) : ℤ) ≤ (K : ℤ) := by rw [hcast]; omega
    exact_mod_cast this
  · have : K / 40 ≤ n₀ - 1 := by
      rw [hsubcast]; exact hbdiv
    omega
  · rw [hsubcast]; exact hbdiv

/-- **Reconstruction forces `B ≥ 1/2` in the degenerate regime.**  If `u` is a formal
solution with `u 0 = 1` which is bounded by `B` at two consecutive sites `y`, `y-1` at mutual
distance `n₀ = -y`, and the continuants of lengths `n₀+1` and `n₀` are bounded by
`e^{n₀(L+ε₁)}`, `e^{(n₀-1)(L+ε₁)}` with `L + ε₁ < 0`, then `1 ≤ 2B`. -/
lemma degen_half_le_B {α lam L ε₁ B : ℝ} {E : ℂ} {θ : ℝ} {u : ℤ → ℂ} {y : ℤ} {n₀ : ℕ}
    (hD : L + ε₁ < 0) (hB : 0 < B)
    (hbd₀ : ∀ ζ : ℝ, ‖pd α lam ζ E (n₀ + 1)‖ ≤ Real.exp ((n₀ : ℝ) * (L + ε₁)))
    (hbd₁ : ∀ ζ : ℝ, ‖pd α lam ζ E n₀‖ ≤ Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)))
    (hsol : IsFormalSol α lam θ E u) (hu0 : u 0 = 1)
    (hdecy : ‖u y‖ ≤ B) (hdecy1 : ‖u (y - 1)‖ ≤ B)
    (hyadd : y + (n₀ : ℤ) = 0) :
    (1 : ℝ) ≤ 2 * B := by
  have h2 : Real.exp ((n₀ : ℝ) * (L + ε₁)) ≤ 1 := by
    have hnn : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
    have hle : (n₀ : ℝ) * (L + ε₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn (le_of_lt hD)
    calc Real.exp ((n₀ : ℝ) * (L + ε₁)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
      _ = 1 := Real.exp_zero
  have h3 : Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) ≤ 1 := by
    have hnn : (0 : ℝ) ≤ ((n₀ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((n₀ - 1 : ℕ) : ℝ) * (L + ε₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn (le_of_lt hD)
    calc Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
      _ = 1 := Real.exp_zero
  have hrec := Work.Core.sol_recon (α := α) (lam := lam) (θ := θ) (E := E) (u := u) hsol y n₀
  rw [hyadd] at hrec
  have h1 : (1 : ℝ) ≤
      (Real.exp ((n₀ : ℝ) * (L + ε₁))
        + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁))) * B := by
    calc (1 : ℝ) = ‖u 0‖ := by rw [hu0, norm_one]
      _ = ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1) * u y
            - pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀ * u (y - 1)‖ := by rw [hrec]
      _ ≤ ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1) * u y‖
            + ‖pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀ * u (y - 1)‖ :=
          norm_sub_le _ _
      _ = ‖pd α lam (θ + (y : ℝ) * α) E (n₀ + 1)‖ * ‖u y‖
            + ‖pd α lam (θ + ((y + 1 : ℤ) : ℝ) * α) E n₀‖ * ‖u (y - 1)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Real.exp ((n₀ : ℝ) * (L + ε₁)) * B
            + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) * B :=
          add_le_add (mul_le_mul (hbd₀ _) hdecy (norm_nonneg _) (Real.exp_pos _).le)
            (mul_le_mul (hbd₁ _) hdecy1 (norm_nonneg _) (Real.exp_pos _).le)
      _ = (Real.exp ((n₀ : ℝ) * (L + ε₁))
            + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁))) * B := by ring
  have h4 : (Real.exp ((n₀ : ℝ) * (L + ε₁))
        + Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁))) * B ≤ 2 * B := by
    nlinarith [h2, h3, hB]
  linarith

theorem Ablock_res_win_degen {α lam L ε ε₁ B : ℝ} {E : ℂ} {θ : ℝ} {n : ℕ} {u : ℤ → ℂ}
    (hL : 0 < L) (hεε₁ : ε₁ < ε) (hn : 2 ≤ n) (hB : 0 < B)
    (hbd : ∀ m : ℕ, (2 * n - 1) / 40 ≤ m → m ≤ 2 * n - 1 → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (m + 1)‖ ≤ Real.exp ((m : ℝ) * (L + ε₁)))
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) (hu0 : u 0 = 1)
    (hdecay : ∀ x ∈ Work.TMC16Core.Core.A2blk (2 * n - 1),
      ‖u (x - 1)‖ ≤ B ∧ ‖u (x + ((2 * n - 1 : ℕ) : ℤ))‖ ≤ B)
    (hnum : 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
      ≤ Real.exp (((2 * n : ℕ) : ℝ) * ((23 / 32 : ℝ) * L + ε)))
    (hD : L + ε₁ < 0) :
    ∀ x ∈ Work.TMC16Core.Core.A2blk (2 * n - 1),
      ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (2 * n)‖ ≤
        Real.exp (((2 * n : ℕ) : ℝ) * ((23 / 32 : ℝ) * L + ε)) := by
  intro x hx
  have hK3 : 3 ≤ 2 * n - 1 := by omega
  set y : ℤ := -(b316 (2 * n - 1)) - 1 with hydef
  set n₀ : ℕ := (-y).toNat with hn₀def
  obtain ⟨hyA, hyA1, hcast, hyadd, hn₀1, hn₀K, hn₀lo, hn₀lo1⟩ :=
    degen_site_bounds (K := 2 * n - 1) hK3 hydef hn₀def
  have hbd₀ : ∀ ζ : ℝ, ‖pd α lam ζ E (n₀ + 1)‖ ≤ Real.exp ((n₀ : ℝ) * (L + ε₁)) :=
    fun ζ => hbd n₀ hn₀lo hn₀K ζ
  have hbd₁ : ∀ ζ : ℝ, ‖pd α lam ζ E n₀‖ ≤ Real.exp (((n₀ - 1 : ℕ) : ℝ) * (L + ε₁)) := by
    intro ζ
    have h := hbd (n₀ - 1) hn₀lo1 (by omega) ζ
    rwa [show n₀ - 1 + 1 = n₀ by omega] at h
  have hdecy : ‖u y‖ ≤ B := by
    have h := (hdecay (y + 1) hyA1).1
    rwa [show y + 1 - 1 = y by ring] at h
  have hdecy1 : ‖u (y - 1)‖ ≤ B := (hdecay y hyA).1
  have hBn : (1 : ℝ) ≤ 2 * B :=
    degen_half_le_B hD hB hbd₀ hbd₁ hsol hu0 hdecy hdecy1 hyadd
  have hKnn : (0 : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hbK : ‖pd α lam (θ + (x : ℝ) * α) E (2 * n)‖
      ≤ Real.exp (((2 * n - 1 : ℕ) : ℝ) * (L + ε₁)) := by
    have h := hbd (2 * n - 1) (Nat.div_le_self (2 * n - 1) 40) le_rfl (θ + (x : ℝ) * α)
    simpa only [show 2 * n - 1 + 1 = 2 * n by omega] using h
  have hexp1 : Real.exp (((2 * n - 1 : ℕ) : ℝ) * (L + ε₁))
      ≤ Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hKD : ((2 * n - 1 : ℕ) : ℝ) * (L + ε₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hKnn (le_of_lt hD)
    have heq : (L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))
        = ((13 : ℝ) / 16) * (((2 * n - 1 : ℕ) : ℝ) * (L + ε₁)) := by ring
    rw [heq]; nlinarith [hKD]
  have hexp2 : Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
      ≤ 2 * B * Real.exp ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ))) := by
    have hpos := Real.exp_pos ((L + ε₁) * ((13 / 16 : ℝ) * ((2 * n - 1 : ℕ) : ℝ)))
    nlinarith [hBn, hpos]
  exact le_trans (le_trans hbK hexp1) (le_trans hexp2 hnum)

end Work.TMC16Core.Core
