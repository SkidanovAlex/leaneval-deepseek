import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.gamInt_abs_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- BW §13: the argument `γ_m(λ) = ∑_i (b_k L_{i,ιm} − b_{ιm} L_{i,k}) λ_i` of the `Δ`-factor is bounded by `Λ = (r-1)·2e·e^{h}·D`. Sum the per-term bound `gamInt_abs_le` over `Fin (r-1)`; `e^{h'(L)}2^v ≤ e·e^{h}` because `h = ⌊h'(L) + v log 2⌋`. -/
theorem sum_gamInt_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ∑ m : Fin (r - 1), |(gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ)) : ℝ)|
      ≤ gamBound K b v σ := by
  have hr2 : 2 ≤ r := H.hr
  obtain ⟨-, -, -, -, hσpos, -, -, -⟩ := H.hBH
  -- `D = pD r d σ ≥ 0`: every factor is nonnegative (`d = [K:ℚ] ≥ 1`, `σ_j > 0`, `r ≥ 2`).
  have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by
    have h := Module.finrank_pos (R := ℚ) (M := K)
    have h1 : 0 < dK K := by simpa [dK] using h
    exact_mod_cast h1
  have hDnn : 0 ≤ pD r (dK K) σ := by
    rw [pD]
    have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    have hlog : 0 ≤ Real.log (2 * (r:ℝ) * (dK K:ℝ)) := by
      apply Real.log_nonneg
      nlinarith
    have hprod : 0 ≤ ∏ j, σ j := Finset.prod_nonneg fun j _ => le_of_lt (hσpos j)
    have h2 : (0:ℝ) ≤ (r:ℝ)^r := pow_nonneg (by linarith) r
    have h3 : (0:ℝ) ≤ (32 * (dK K:ℝ))^(r+1) := pow_nonneg (by linarith) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) h3) hlog) hprod
  -- Per-term bound from `gamInt_abs_le`.
  have hterm : ∀ m : Fin (r - 1),
      |(gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ)) : ℝ)|
        ≤ 2 * Real.exp (hL b (dK K)) * (2:ℝ)^v * pD r (dK K) σ :=
    fun m => gamInt_abs_le φ α b k v c L α' σ H.hBH ι m lm.2.2
  -- Sum the `r - 1` identical bounds.
  have hsum : ∑ m : Fin (r - 1), |(gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ)) : ℝ)|
      ≤ ((r:ℝ) - 1) * (2 * Real.exp (hL b (dK K)) * (2:ℝ)^v * pD r (dK K) σ) := by
    calc ∑ m : Fin (r - 1), |(gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ)) : ℝ)|
        ≤ ∑ _m : Fin (r - 1), (2 * Real.exp (hL b (dK K)) * (2:ℝ)^v * pD r (dK K) σ) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = ((r:ℝ) - 1) * (2 * Real.exp (hL b (dK K)) * (2:ℝ)^v * pD r (dK K) σ) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
            Nat.cast_sub (by omega : 1 ≤ r)]
          norm_num
  -- `h'(L) + v log 2 < h + 1` with `h = ⌊h'(L) + v log 2⌋`.
  have hfloor : hL b (dK K) + (v:ℝ) * Real.log 2 < (acH K b v : ℝ) + 1 := by
    rw [show acH K b v = ph (hL b (dK K)) v from rfl, ph]
    exact Nat.lt_floor_add_one _
  have hExpStep : Real.exp (hL b (dK K)) * (2:ℝ)^v ≤ Real.exp 1 * Real.exp (acH K b v : ℝ) := by
    have h2v : (2:ℝ)^v = Real.exp ((v:ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    calc Real.exp (hL b (dK K)) * (2:ℝ)^v
        = Real.exp (hL b (dK K) + (v:ℝ) * Real.log 2) := by
          rw [h2v, ← Real.exp_add]
      _ ≤ Real.exp ((acH K b v : ℝ) + 1) := Real.exp_le_exp.mpr (le_of_lt hfloor)
      _ = Real.exp 1 * Real.exp (acH K b v : ℝ) := by rw [Real.exp_add, mul_comm]
  have hXY : 2 * Real.exp (hL b (dK K)) * (2:ℝ)^v
      ≤ 2 * Real.exp 1 * Real.exp (acH K b v : ℝ) := by
    calc 2 * Real.exp (hL b (dK K)) * (2:ℝ)^v
        = 2 * (Real.exp (hL b (dK K)) * (2:ℝ)^v) := mul_assoc 2 _ _
      _ ≤ 2 * (Real.exp 1 * Real.exp (acH K b v : ℝ)) :=
          mul_le_mul_of_nonneg_left hExpStep (by norm_num)
      _ = 2 * Real.exp 1 * Real.exp (acH K b v : ℝ) := (mul_assoc 2 _ _).symm
  have hmain : 2 * Real.exp (hL b (dK K)) * (2:ℝ)^v * pD r (dK K) σ
      ≤ 2 * Real.exp 1 * Real.exp (acH K b v : ℝ) * pD r (dK K) σ :=
    mul_le_mul_of_nonneg_right hXY hDnn
  have ha : 0 ≤ (r:ℝ) - 1 := by
    have h2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr2
    linarith
  calc ∑ m : Fin (r - 1), |(gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ)) : ℝ)|
      ≤ ((r:ℝ) - 1) * (2 * Real.exp (hL b (dK K)) * (2:ℝ)^v * pD r (dK K) σ) := hsum
    _ ≤ ((r:ℝ) - 1) * (2 * Real.exp 1 * Real.exp (acH K b v : ℝ) * pD r (dK K) σ) :=
        mul_le_mul_of_nonneg_left hmain ha
    _ = gamBound K b v σ := by
        simp only [gamBound, acD]
        ring

end Work.BW
