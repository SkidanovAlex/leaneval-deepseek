import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.Branch
import Submission.Work.TMC16Core.Core.pd_le_of_decay_win
import Submission.Work.TMC16Core.Assembly.res_dist_le
import Submission.Work.TMC16Core.Assembly.res_arith_good
import Submission.Work.TMC16Core.Assembly.res_arith_bad
import Submission.Work.TMC16Core.Assembly.res_thresh_good
import Submission.Work.TMC16Core.Assembly.res_thresh_bad

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

/-!
# `Work.TMC16Core.Assembly.res_zero` — AJ Lemma 9.12

For a formal solution `u` of `H u = E u` with `u 0 = 1`, polynomial growth `C(1+|k|)`,
exponential decay `‖u k‖ ≤ e^{-(L/2) d}` at the non-resonant sites `d = dist(k, qₙ ℤ) ≥ qₙ/5`
and the continuant bound `‖pd ζ E (m+1)‖ ≤ e^{m(L+εf)}` for `(2qₙ-1)/40 ≤ m ≤ 2qₙ-1`, the
continuant of the resonant window `I1r qₙ` at scale `K = 2qₙ - 1` is bounded by
`e^{2qₙ(23L/32 + 2εf)}`.

The proof is Poisson + Cramér (`Core.pd_le_of_decay_win`): for `x ∈ I1r qₙ`, writing
`τ := x + qₙ - 1` (so `|τ| ≤ 5qₙ/8`), the two Poisson endpoints `x - 1 = τ - qₙ` and
`x + K = τ + qₙ` are at the same distance `d(τ) = min(|τ|, qₙ - |τ|)` from `qₙℤ` (only the
lower bound `d(τ) ≤ dist(·, qₙℤ)` is used, `res_dist_le`).  The numerator lengths are
`qₙ - 1 ± τ`, both `≤ qₙ - 1 + |τ|`.  Two regimes:

* `qₙ ≤ 5 d(τ)`: the decay hypothesis applies at both ends and gives `B = e^{-(L/2)d(τ)}`;
  the worst exponent in units of `qₙ` is `23/16` (`res_arith_good`);
* `5 d(τ) < qₙ`: the decay hypothesis is unavailable, and the polynomial bound gives
  `B = C(1+2qₙ)`; here `|τ| = d(τ) < qₙ/5`, and the worst exponent is again below `23/16`
  (`res_arith_bad`).

The `O(log(C qₙ))` losses are absorbed by the second slack `εf` (`res_thresh_good`,
`res_thresh_bad`), which is why `Q₀` depends on `L`, `εf` and `C` only.
-/

theorem res_zero {L εf C : ℝ} (hL : 0 < L) (hεf : 0 < εf) (hC : 0 ≤ C) :
    ∃ Q₀ : ℕ, ∀ qn : ℕ, Q₀ ≤ qn → ∀ {α lam θ : ℝ} {E : ℂ} {u : ℤ → ℂ},
      Work.TMC16Core.IsFormalSol α lam θ E u → u 0 = 1 →
      (∀ k : ℤ, ‖u k‖ ≤ C * (1 + |(k : ℝ)|)) →
      (∀ k : ℤ, |k| ≤ 2 * (qn : ℤ) → ∀ d : ℕ, qn ≤ 5 * d →
          (∀ ℓ : ℤ, (d : ℤ) ≤ |k - ℓ * (qn : ℤ)|) →
          ‖u k‖ ≤ Real.exp (-(L / 2) * (d : ℝ))) →
      (∀ N : ℕ, (2 * qn - 1) / 40 ≤ N → N ≤ 2 * qn - 1 → ∀ ζ : ℝ,
          ‖Work.TMC16Core.pd α lam ζ E (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + εf))) →
      ∀ x ∈ Work.TMC16Core.Assembly.I1r qn,
        ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (2 * qn)‖ ≤
          Real.exp ((2 * qn : ℝ) * (23 * L / 32 + 2 * εf)) := by
  obtain ⟨Qg, hQg⟩ := res_thresh_good (L := L) (εf := εf) hL hεf
  obtain ⟨Qb, hQb⟩ := res_thresh_bad (L := L) (εf := εf) (C := C) hL hεf hC
  refine ⟨max 4 (max Qg Qb), ?_⟩
  intro qn hqn α lam θ E u hsol hu0 hpoly hdec hbd x hx
  have hqn4 : 4 ≤ qn := le_trans (le_max_left _ _) hqn
  have hQg' : Qg ≤ qn := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hqn)
  have hQb' : Qb ≤ qn := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hqn)
  have hlogg := hQg qn hQg'
  have hlogb := hQb qn hQb'
  have hC1 : (1 : ℝ) ≤ C := by
    have h := hpoly 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    rwa [hu0, norm_one] at h
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  -- ## window data
  set H : ℕ := 5 * qn / 8 with hHdef
  set τ : ℤ := x + (qn : ℤ) - 1 with hτdef
  obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx
  have hHle : H ≤ qn := by omega
  have hH1 : H + 1 ≤ qn := by omega
  have hnum : (2 * qn - 1) / 40 + H + 1 ≤ qn := by omega
  have hτlo : -((H : ℤ)) ≤ τ := by omega
  have hτhi : τ ≤ (H : ℤ) - 1 := by omega
  have hτabs : τ.natAbs ≤ H := by omega
  have hτabsq : τ.natAbs ≤ qn := le_trans hτabs hHle
  set d : ℕ := min τ.natAbs (qn - τ.natAbs) with hddef
  have hdR : (d : ℝ) = min (τ.natAbs : ℝ) ((qn : ℝ) - (τ.natAbs : ℝ)) := by
    rw [hddef, Nat.cast_min, Nat.cast_sub hτabsq]
  have hjR : (τ.natAbs : ℝ) ≤ 5 * (qn : ℝ) / 8 := by
    have h1 : ((τ.natAbs : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hτabs
    have h2 : (H : ℝ) ≤ 5 * (qn : ℝ) / 8 := by
      have h4 : (H : ℝ) = ((5 * qn / 8 : ℕ) : ℝ) := by rw [hHdef]
      rw [h4, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      have h5 : 8 * (5 * qn / 8) ≤ 5 * qn := by
        rw [mul_comm 8]; exact Nat.div_mul_le_self (5 * qn) 8
      have h6 : (8 : ℝ) * (((5 * qn / 8 : ℕ)) : ℝ) ≤ 5 * (qn : ℝ) := by exact_mod_cast h5
      linarith
    linarith
  -- ## the two Poisson endpoints
  have hK1 : 1 ≤ 2 * qn := by omega
  have hxm1 : x - 1 = τ - (qn : ℤ) := by omega
  have hxK : x + ((2 * qn - 1 : ℕ) : ℤ) = τ + (qn : ℤ) := by
    have h2 : ((2 * qn - 1 : ℕ) : ℤ) = 2 * (qn : ℤ) - 1 := by
      rw [Nat.cast_sub hK1]; push_cast; ring
    rw [h2]; omega
  have hx2 : x + ((2 * qn - 1 : ℕ) : ℤ) - 1 = τ + (qn : ℤ) - 1 := by
    rw [hxK]
  have hk1 : |x - 1| ≤ 2 * (qn : ℤ) := by
    rw [hxm1, abs_le]
    constructor <;> omega
  have hk2 : |x + ((2 * qn - 1 : ℕ) : ℤ)| ≤ 2 * (qn : ℤ) := by
    rw [hxK, abs_le]
    constructor <;> omega
  have hdistm1 : ∀ ℓ : ℤ, (d : ℤ) ≤ |(x - 1) - ℓ * (qn : ℤ)| := by
    intro ℓ
    have h := res_dist_le (qn := qn) (j := τ) hτabsq (ℓ + 1)
    rw [show τ - (ℓ + 1) * (qn : ℤ) = (x - 1) - ℓ * (qn : ℤ) by rw [hxm1]; ring] at h
    simpa [hddef] using h
  have hdistK : ∀ ℓ : ℤ, (d : ℤ) ≤ |(x + ((2 * qn - 1 : ℕ) : ℤ)) - ℓ * (qn : ℤ)| := by
    intro ℓ
    have h := res_dist_le (qn := qn) (j := τ) hτabsq (ℓ - 1)
    rw [show τ - (ℓ - 1) * (qn : ℤ) =
        (x + ((2 * qn - 1 : ℕ) : ℤ)) - ℓ * (qn : ℤ) by rw [hxK]; ring] at h
    simpa [hddef] using h
  -- ## Poisson/Cramer prerequisites
  have hxj0 : x ≤ 0 := by omega
  have hx2pos : 0 ≤ x + ((2 * qn - 1 : ℕ) : ℤ) - 1 := by rw [hx2]; omega
  have hm1 : ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat ≤ 2 * qn - 1 := by
    rw [hx2, sub_zero, Int.toNat_le]; omega
  have hm2 : (0 - x).toNat ≤ 2 * qn - 1 := by
    rw [Int.toNat_le]; omega
  have hnn1 : (0 : ℤ) ≤ τ + (qn : ℤ) - 1 := by omega
  have hnn2 : (0 : ℤ) ≤ (qn : ℤ) - 1 - τ := by omega
  have hn1 : (2 * qn - 1) / 40 ≤ ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat := by
    rw [hx2, sub_zero]
    have hc : (((2 * qn - 1) / 40 : ℕ) : ℤ) ≤ (qn : ℤ) - 1 - (H : ℤ) := by omega
    have h2 : (((2 * qn - 1) / 40 : ℕ) : ℤ) ≤ τ + (qn : ℤ) - 1 := by omega
    have h3 : (((2 * qn - 1) / 40 : ℕ) : ℤ) ≤ (((τ + (qn : ℤ) - 1).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnn1]; exact h2
    exact Int.ofNat_le.mp h3
  have hn2 : (2 * qn - 1) / 40 ≤ (0 - x).toNat := by
    have h0x : 0 - x = (qn : ℤ) - 1 - τ := by omega
    rw [h0x]
    have hc : (((2 * qn - 1) / 40 : ℕ) : ℤ) ≤ (qn : ℤ) - 1 - (H : ℤ) := by omega
    have h2 : (((2 * qn - 1) / 40 : ℕ) : ℤ) ≤ (qn : ℤ) - 1 - τ := by omega
    have h3 : (((2 * qn - 1) / 40 : ℕ) : ℤ) ≤ ((((qn : ℤ) - 1 - τ).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnn2]; exact h2
    exact Int.ofNat_le.mp h3
  -- ## the two numerator lengths, as reals
  have hcasta : ((((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℕ) : ℝ)
      = (τ : ℝ) + (qn : ℝ) - 1 := by
    rw [hx2, sub_zero]
    have h3 : ((((τ + (qn : ℤ) - 1).toNat : ℕ)) : ℝ) = ((τ + (qn : ℤ) - 1 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn1
    rw [h3]; push_cast; ring
  have hcastb : (((0 - x).toNat : ℕ) : ℝ) = (qn : ℝ) - 1 - (τ : ℝ) := by
    have h0x : 0 - x = (qn : ℤ) - 1 - τ := by omega
    rw [h0x]
    have h3 : (((((qn : ℤ) - 1 - τ).toNat : ℕ)) : ℝ) = (((qn : ℤ) - 1 - τ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn2
    rw [h3]; push_cast; ring
  have ha : ((((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℕ) : ℝ)
      ≤ (qn : ℝ) - 1 + (τ.natAbs : ℝ) := by
    rw [hcasta]
    have hle : (τ : ℝ) ≤ (τ.natAbs : ℝ) := by simpa using le_abs_self (τ : ℝ)
    linarith
  have hb : (((0 - x).toNat : ℕ) : ℝ) ≤ (qn : ℝ) - 1 + (τ.natAbs : ℝ) := by
    rw [hcastb]
    have hle : -(τ : ℝ) ≤ (τ.natAbs : ℝ) := by simpa using neg_le_abs (τ : ℝ)
    linarith
  -- ## main case split
  by_cases hP : pd α lam (θ + (x : ℝ) * α) E (2 * qn) = 0
  · rw [hP, norm_zero]; exact (Real.exp_pos _).le
  · have hP' : pd α lam (θ + (x : ℝ) * α) E (2 * qn - 1 + 1) ≠ 0 := by
      rwa [show 2 * qn - 1 + 1 = 2 * qn by omega]
    have hsum : Real.exp ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1 - 0).toNat * (L + εf))
          + Real.exp ((0 - x).toNat * (L + εf))
        ≤ 2 * Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf)) := by
      have hL' : 0 ≤ L + εf := by linarith
      have e1 : Real.exp ((((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℝ) * (L + εf))
          ≤ Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hL')
      have e2 : Real.exp (((0 - x).toNat : ℝ) * (L + εf))
          ≤ Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hL')
      linarith
    by_cases hgood : qn ≤ 5 * d
    · -- good case: the decay hypothesis is available
      have hdec1 : ‖u (x - 1)‖ ≤ Real.exp (-(L / 2) * (d : ℝ)) :=
        hdec (x - 1) hk1 d hgood hdistm1
      have hdec2 : ‖u ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) + 1)‖ ≤
          Real.exp (-(L / 2) * (d : ℝ)) := by
        have heq : (x + ((2 * qn - 1 : ℕ) : ℤ) - 1) + 1 =
            x + ((2 * qn - 1 : ℕ) : ℤ) := by ring
        rw [heq]
        exact hdec (x + ((2 * qn - 1 : ℕ) : ℤ)) hk2 d hgood hdistK
      have hmain := Work.TMC16Core.Core.pd_le_of_decay_win (α := α) (lam := lam) (L := L)
        (ε₁ := εf) (B := Real.exp (-(L / 2) * (d : ℝ))) (E := E) (θ := θ) (u := u)
        (K := 2 * qn - 1) (x := x) (x₂ := x + ((2 * qn - 1 : ℕ) : ℤ) - 1)
        (n₀ := (2 * qn - 1) / 40) (Real.exp_pos _) rfl
        (fun m hm1' hm2' ζ => hbd m hm1' hm2' ζ) hm1 hm2 hn1 hn2 hsol hu0 hdec1 hdec2
        hxj0 hx2pos hP'
      rw [show 2 * qn - 1 + 1 = 2 * qn by omega] at hmain
      calc ‖pd α lam (θ + (x : ℝ) * α) E (2 * qn)‖
          ≤ Real.exp (-(L / 2) * (d : ℝ)) *
              (Real.exp ((((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℝ) * (L + εf))
                + Real.exp (((0 - x).toNat : ℝ) * (L + εf))) := hmain
        _ ≤ Real.exp (-(L / 2) * (d : ℝ)) *
              (2 * Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf))) :=
            mul_le_mul_of_nonneg_left hsum (le_of_lt (Real.exp_pos _))
        _ = 2 * Real.exp (-(L / 2) * (d : ℝ)) *
              Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf)) := by ring
        _ ≤ Real.exp ((2 * (qn : ℝ)) * (23 * L / 32 + 2 * εf)) :=
            res_arith_good hL hεf hjR hdR hlogg
    · -- bad case: use the polynomial bound
      have hbad : 5 * d < qn := not_le.mp hgood
      have hbadR : 5 * (d : ℝ) < (qn : ℝ) := by exact_mod_cast hbad
      have hdec1 : ‖u (x - 1)‖ ≤ C * (1 + 2 * (qn : ℝ)) := by
        have h2 : |(((x - 1 : ℤ)) : ℝ)| ≤ 2 * (qn : ℝ) := by
          rw [← Int.cast_abs]
          exact_mod_cast hk1
        calc ‖u (x - 1)‖ ≤ C * (1 + |(((x - 1 : ℤ)) : ℝ)|) := hpoly (x - 1)
          _ ≤ C * (1 + 2 * (qn : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hC
      have hdec2 : ‖u ((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) + 1)‖ ≤ C * (1 + 2 * (qn : ℝ)) := by
        have heq : (x + ((2 * qn - 1 : ℕ) : ℤ) - 1) + 1 =
            x + ((2 * qn - 1 : ℕ) : ℤ) := by ring
        rw [heq]
        have h2 : |(((x + ((2 * qn - 1 : ℕ) : ℤ) : ℤ)) : ℝ)| ≤ 2 * (qn : ℝ) := by
          rw [← Int.cast_abs]
          exact_mod_cast hk2
        calc ‖u (x + ((2 * qn - 1 : ℕ) : ℤ))‖
            ≤ C * (1 + |(((x + ((2 * qn - 1 : ℕ) : ℤ) : ℤ)) : ℝ)|) := hpoly _
          _ ≤ C * (1 + 2 * (qn : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hC
      have hB : 0 < C * (1 + 2 * (qn : ℝ)) := by
        have h2 : (0 : ℝ) < 1 + 2 * (qn : ℝ) := by positivity
        exact mul_pos hCpos h2
      have hmain := Work.TMC16Core.Core.pd_le_of_decay_win (α := α) (lam := lam) (L := L)
        (ε₁ := εf) (B := C * (1 + 2 * (qn : ℝ))) (E := E) (θ := θ) (u := u)
        (K := 2 * qn - 1) (x := x) (x₂ := x + ((2 * qn - 1 : ℕ) : ℤ) - 1)
        (n₀ := (2 * qn - 1) / 40) hB rfl
        (fun m hm1' hm2' ζ => hbd m hm1' hm2' ζ) hm1 hm2 hn1 hn2 hsol hu0 hdec1 hdec2
        hxj0 hx2pos hP'
      rw [show 2 * qn - 1 + 1 = 2 * qn by omega] at hmain
      calc ‖pd α lam (θ + (x : ℝ) * α) E (2 * qn)‖
          ≤ (C * (1 + 2 * (qn : ℝ))) *
              (Real.exp ((((x + ((2 * qn - 1 : ℕ) : ℤ) - 1) - 0).toNat : ℝ) * (L + εf))
                + Real.exp (((0 - x).toNat : ℝ) * (L + εf))) := hmain
        _ ≤ (C * (1 + 2 * (qn : ℝ))) *
              (2 * Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf))) :=
            mul_le_mul_of_nonneg_left hsum (le_of_lt hB)
        _ = 2 * (C * (1 + 2 * (qn : ℝ))) *
              Real.exp (((qn : ℝ) - 1 + (τ.natAbs : ℝ)) * (L + εf)) := by ring
        _ ≤ Real.exp ((2 * (qn : ℝ)) * (23 * L / 32 + 2 * εf)) :=
            res_arith_bad hL hεf hC hjR hdR hbadR hlogb


end Work.TMC16Core.Assembly
