import Mathlib
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.aDiag_conj_expansion
import Submission.Work.EKLC6Core.aDiag_conj_exp_le

/-!
# `Work.EKLC6Core.injCap_aDiag_geometric` — the capped injectivity radius decays at most geometrically along the diagonal flow

`injCap x = min (injS x) (1/2)` is the capped injectivity radius of the orbit map `v ↦ v • x`
on `X₃ = SL₃(ℝ)/SL₃(ℤ)` (`Work.EKLC6Core.InjRadius`): the largest `ρ ≤ 1/2` such that
`v ↦ v • x` is injective on the displacement neighbourhood
`V ρ = {v | |v i j - 1 i j| < ρ ∀ i j}`.  It tends to `0` in the cusp, so no *uniform* positive
lower bound for `injCap` along the orbit exists; the theorem proved here is the *quantitative*
statement that the decay is at most exponential, with a rate controlled by the exponent vector
`t`:

`injCap (aDiag t ^ n • x) ≥ c₂ · injCap x · λⁿ`,  `c₂ > 0`, `0 < λ < 1`.

## The argument

Everything is read off the conjugation formula `boxi_conj_pow_apply_inv`:
for `D = aDiag t ^ n` and `v : SL₃(ℝ)`,

`(D⁻¹ v D) i j = e^{n (t j - t i)} · v i j`.

**Step 1** (`injAt_aDiag_pow_transfer_aux`): if `v ∈ V ρ` and `e^{n (t j - t i)} ≤ κ` for all
`i j`, then `D⁻¹ v D ∈ V (ρκ)`: the diagonal entries are unchanged, and off the diagonal the
entry of `v` is multiplied by at most `κ`.  Hence, if `v₁ • x = v₂ • x` with `v₁, v₂ ∈ V (r/(1000κ))`,
conjugating the equality by `D⁻¹` gives `(D⁻¹vᵢD) • x = x` with `D⁻¹vᵢD ∈ V r`; injectivity
of `V r` at `x` (`InjAt x r`) then forces `D⁻¹v₁D = D⁻¹v₂D`, i.e. `v₁ = v₂`.  So

`InjAt x r  ⟹  InjAt (D • x) (r / (1000 κ))`.

**Step 2**: `κ := e^{n·M}` with `M := max 1 (2 ∑ |t k|) ≥ |t j - t i|` for all `i, j`
(`aDiag_conj_exp_le`), so `InjAt x (injCap x / 2)` gives
`InjAt (D • x) (injCap x / (2000 κ))`.  Since `InjAt` on a radius `≤ 1` forces the same radius
into the set whose supremum defines `injS` (`injSet_bddAbove`), and `injCap x / (2000κ) ≤ 1/2`,

`injCap (D • x) ≥ injCap x / (2000 κ) = (injCap x / 2000) · e^{-n M}`,

which is the claimed bound with `c₂ = 1/2000` and `λ = e^{-M} < 1`.
-/

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-- The iterate of the translation action is the power of the group element:
`(fun y ↦ aDiag t • y)^[n] x = aDiag t ^ n • x`. -/
theorem aDiag_iterate_smul (t : Fin 3 → ℝ) (x : X3) (n : ℕ) :
    (fun y : X3 => aDiag t • y)^[n] x = aDiag t ^ n • x := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, pow_succ']

/-- **Injectivity transfers along the diagonal flow.**  If `κ` dominates the conjugation factors
`e^{n (t j - t i)}` and is at least `1`, then injectivity of the orbit map on `V r` at `x`
transfers to injectivity of the orbit map on `V (r / (1000 κ))` at `aDiag t ^ n • x`.

Indeed `D⁻¹ v D ∈ V r` for every `v ∈ V (r/(1000κ))` (`D = aDiag t ^ n`), so conjugating the
equality `v₁ • (D • x) = v₂ • (D • x)` by `D⁻¹` puts `InjAt x r` in a position to apply. -/
theorem injAt_aDiag_pow_transfer_aux (t : Fin 3 → ℝ) (x : X3) (n : ℕ) {r κ : ℝ}
    (hr : 0 < r) (_hr1 : r ≤ 1) (hκ1 : 1 ≤ κ)
    (hκ : ∀ i j : Fin 3, Real.exp ((n : ℝ) * (t j - t i)) ≤ κ)
    (h : InjAt x r) :
    InjAt (aDiag t ^ n • x) (r / (1000 * κ)) := by
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ1
  have h10 : (0 : ℝ) < 1000 * κ := by linarith
  have hρle : r / (1000 * κ) ≤ r := by
    rw [div_le_iff₀ h10]
    nlinarith [hr, hκ1, hκpos]
  -- off-diagonal entries are amplified by at most `κ`, diagonal entries not at all
  have key : ∀ {v : SL3}, v ∈ V (r / (1000 * κ)) →
      (aDiag t ^ n)⁻¹ * v * aDiag t ^ n ∈ V r := by
    intro v hv i j
    rw [boxi_conj_pow_apply_inv]
    have hvij : |(((v : Matrix (Fin 3) (Fin 3) ℝ) i j) - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
        < r / (1000 * κ) := hv i j
    rcases eq_or_ne i j with rfl | hij
    · rw [show ((1 : Matrix (Fin 3) (Fin 3) ℝ) i i) = 1 from Matrix.one_apply_eq i] at hvij ⊢
      rw [show (n : ℝ) * (t i - t i) = 0 by ring, Real.exp_zero, one_mul]
      linarith [hvij, hρle]
    · rw [show ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) = 0 from Matrix.one_apply_ne hij,
        sub_zero] at hvij
      rw [show ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) = 0 from Matrix.one_apply_ne hij, sub_zero]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : Real.exp ((n : ℝ) * (t j - t i)) * |((v : Matrix (Fin 3) (Fin 3) ℝ) i j)|
          ≤ κ * |((v : Matrix (Fin 3) (Fin 3) ℝ) i j)| :=
        mul_le_mul_of_nonneg_right (hκ i j) (abs_nonneg _)
      have h2 : 1000 * κ * |((v : Matrix (Fin 3) (Fin 3) ℝ) i j)| < r := by
        have h3 := mul_lt_mul_of_pos_left hvij h10
        rwa [mul_div_cancel₀ r h10.ne'] at h3
      nlinarith [h1, h2, hr, h10, hκpos, abs_nonneg ((v : Matrix (Fin 3) (Fin 3) ℝ) i j)]
  intro v₁ v₂ h₁ h₂ heq
  have h₁' : (aDiag t ^ n)⁻¹ * v₁ * aDiag t ^ n ∈ V r := key h₁
  have h₂' : (aDiag t ^ n)⁻¹ * v₂ * aDiag t ^ n ∈ V r := key h₂
  have heq' : ((aDiag t ^ n)⁻¹ * v₁ * aDiag t ^ n) • x
      = ((aDiag t ^ n)⁻¹ * v₂ * aDiag t ^ n) • x := by
    simp only [mul_smul]
    rw [heq]
  have hvv := h _ _ h₁' h₂' heq'
  calc v₁ = aDiag t ^ n * ((aDiag t ^ n)⁻¹ * v₁ * aDiag t ^ n) * (aDiag t ^ n)⁻¹ := by group
    _ = aDiag t ^ n * ((aDiag t ^ n)⁻¹ * v₂ * aDiag t ^ n) * (aDiag t ^ n)⁻¹ := by rw [hvv]
    _ = v₂ := by group

/-- **The capped injectivity radius along the diagonal orbit.**  For every `x` and `n`,
`injCap (aDiag t ^ n • x) ≥ (injCap x / 2000) · e^{-n·max 1 (2 ∑ |t k|)}`. -/
theorem injCap_aDiag_pow_ge (t : Fin 3 → ℝ) (x : X3) (n : ℕ) :
    injCap x / 2000 * Real.exp (-(max 1 (2 * ∑ k, |t k|))) ^ n ≤
      injCap (aDiag t ^ n • x) := by
  set M : ℝ := max 1 (2 * ∑ k, |t k|) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set κ : ℝ := Real.exp ((n : ℝ) * M) with hκdef
  have hκ1 : 1 ≤ κ := by
    rw [hκdef, Real.one_le_exp_iff]
    exact mul_nonneg (Nat.cast_nonneg n) hMpos.le
  have hInj : InjAt x (injCap x / 2) :=
    injAt_of_lt_injCap (by linarith [injCap_pos x]) (by linarith [injCap_pos x])
  have htrans : InjAt (aDiag t ^ n • x) (injCap x / 2 / (1000 * κ)) :=
    injAt_aDiag_pow_transfer_aux t x n (by linarith [injCap_pos x]) (by linarith [injCap_le_half x])
      hκ1 (fun i j => by rw [hκdef, hMdef]; exact aDiag_conj_exp_le t n i j) hInj
  have hρ : (0 : ℝ) < injCap x / 2 / (1000 * κ) := by
    apply div_pos (by linarith [injCap_pos x])
    linarith
  have hρ1 : injCap x / 2 / (1000 * κ) ≤ 1 := by
    apply div_le_one_of_le₀
    · linarith [injCap_le_half x]
    · linarith
  -- the radius is in the set defining `injS`, whence it is at most `injCap`
  have hle : injCap x / 2 / (1000 * κ) ≤ injS (aDiag t ^ n • x) :=
    le_csSup (injSet_bddAbove _) ⟨hρ, hρ1, htrans⟩
  have h2 : injCap x / 2 / (1000 * κ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [injCap_le_half x, injCap_pos x, hκ1]
  have hmain : injCap x / 2 / (1000 * κ) ≤ injCap (aDiag t ^ n • x) := by
    rw [injCap]
    exact le_min hle h2
  have hexp : Real.exp (-M) ^ n = (Real.exp ((n : ℝ) * M))⁻¹ := by
    rw [← Real.exp_nat_mul (-M) n, ← Real.exp_neg]
    congr 1
    ring
  have hrew : injCap x / 2000 * Real.exp (-M) ^ n = injCap x / 2 / (1000 * κ) := by
    rw [hexp, hκdef]
    ring
  rw [show -(max 1 (2 * ∑ k, |t k|)) = -M from by rw [hMdef]]
  rw [hrew]
  exact hmain

/-- **The capped injectivity radius decays at most geometrically along the diagonal flow.**

There are constants `c₂ > 0` and `λ ∈ (0,1)`, depending only on the exponent vector `t`, with
`c₂ · injCap x · λⁿ ≤ injCap (aDiag t ^ n • x)` for every `x ∈ X₃` and every `n`; concretely one
may take `c₂ = 1/2000` and `λ = e^{-max 1 (2 ∑ |t k|)}`. -/
theorem injCap_aDiag_geometric (t : Fin 3 → ℝ) :
    ∃ c₂ lam0 : ℝ, 0 < c₂ ∧ 0 < lam0 ∧ lam0 < 1 ∧
      ∀ x : Work.EKLContract.X3, ∀ n : ℕ,
        c₂ * Work.EKLC6Core.injCap x * lam0 ^ n ≤
          Work.EKLC6Core.injCap ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n] x) := by
  refine ⟨1 / 2000, Real.exp (-(max 1 (2 * ∑ k, |t k|))), by norm_num, Real.exp_pos _, ?_, ?_⟩
  · have hM : (0 : ℝ) < max 1 (2 * ∑ k, |t k|) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlt : Real.exp (-(max 1 (2 * ∑ k, |t k|))) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by linarith)
    simpa using hlt
  · intro x n
    rw [aDiag_iterate_smul]
    have key := injCap_aDiag_pow_ge t x n
    have h1 : (1 : ℝ) / 2000 * injCap x * Real.exp (-(max 1 (2 * ∑ k, |t k|))) ^ n
        = injCap x / 2000 * Real.exp (-(max 1 (2 * ∑ k, |t k|))) ^ n := by ring
    rw [h1]
    exact key

end

end Work.EKLC6Core
