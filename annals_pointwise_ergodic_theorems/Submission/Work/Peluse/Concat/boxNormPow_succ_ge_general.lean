/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.PET.two_mul_boxNormPow_succ_ge

/-!
# Level raising for the box-norm power, for an arbitrary complex function

`Work.Peluse.PET.two_mul_boxNormPow_succ_ge` proves the Gowers--Cauchy--Schwarz step

`(boxNormPow t (Q ∘ castSucc) S f)^2 ≤ 2 * boxNormPow (t+1) Q S f`

for a complex function `f` that is additionally assumed to be *real nonnegative*
(`hreal : ∀ x, f x = ((‖f x‖ : ℝ) : ℂ)`).  That hypothesis is in fact never used in the proof, and
this file records the general statement: the same inequality holds for **every** complex function
vanishing off the symmetric interval `symIcc N` (hence finitely supported there), with `N > 0` and
with `Q i` nonempty and `Q (Fin.last t)` a set of elements of absolute value at most `N`.

The proof is literally the proof of `two_mul_boxNormPow_succ_ge` with the unused hypothesis
removed; it is reproduced here only because a hypothesis cannot be dropped from an existing
theorem without reproving it.

## Main results

* `Work.Peluse.Concat.two_mul_boxNormPow_succ_ge_complex`: the inequality above;
* `Work.Peluse.Concat.boxNormPow_succ_ge_general`: its constant-form corollary,
  `∃ C > 0` with `C * (boxNormPow t (Q ∘ castSucc) S f)^2 ≤ boxNormPow (t+1) Q S f` for all `Q`,
  `N`, `f` under Peluse's standing hypotheses (`Q i` nonempty with `|a| ≤ N`, `SupportIn f N`,
  `‖f‖_∞ ≤ 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

open Work.Peluse
open Work.Peluse.PET
open Work.Peluse.PET.TwoMul

theorem two_mul_boxNormPow_succ_ge_complex {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) {N : ℕ} (hN : 0 < N)
    (h : ℤ → ℂ) (hQ : ∀ i, (Q i).Nonempty)
    (hbd : ∀ a ∈ Q (Fin.last n), |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0) :
    (Work.Peluse.boxNormPow n (fun i : Fin n => Q i.castSucc) (Work.Peluse.symIcc N) h) ^ 2
      ≤ 2 * Work.Peluse.boxNormPow (n + 1) Q (Work.Peluse.symIcc N) h := by
  classical
  have hQncard : (0 : ℝ) < ((Q (Fin.last n)).card : ℝ) := by
    have : 0 < (Q (Fin.last n)).card := Finset.card_pos.mpr (hQ (Fin.last n))
    exact_mod_cast this
  have hScard : (0 : ℝ) < ((Work.Peluse.symIcc N).card : ℝ) := by
    have : 0 < (Work.Peluse.symIcc N).card := Finset.card_pos.mpr ⟨0, by
      rw [Work.Peluse.symIcc, Finset.mem_Icc]; omega⟩
    exact_mod_cast this
  have hfs : Work.Peluse.FinSuppZ h := ⟨N, fun x hx => by
    apply hsupp
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    intro hcon
    have h1 : |x| ≤ (N : ℤ) := abs_le.mpr ⟨hcon.1, hcon.2⟩
    rw [Int.abs_eq_natAbs] at h1
    have h2 : x.natAbs ≤ N := by exact_mod_cast h1
    omega⟩
  set W : ℝ := ∑ p : PetTuple n Q, ∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2 with hWdef
  set V : ℂ := ∑ p : PetTuple n Q,
    ∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x with hVdef
  have hWnn : 0 ≤ W := by
    rw [hWdef]
    exact Finset.sum_nonneg fun p _ => tsum_nonneg fun x => by positivity
  -- (I) the top-dimensional cube sum
  have hI : Work.Peluse.boxSumPow (n + 1) Q (Work.Peluse.symIcc N) h
      = ((nu (Work.Peluse.symIcc N) Q * W : ℝ) : ℂ) := by
    rw [Work.Peluse.boxSumPow, prodCubeSum_last_split Q (Work.Peluse.symIcc N) h hfs]
    rw [show (∑ p : PetTuple n Q,
          ∑' x : ℤ, ‖∑ a : {x : ℤ // x ∈ Q (Fin.last n)},
            ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
              (h (x + a.1 + Work.Peluse.cornerShift (fun i => (p.1 i).1) (fun i => (p.2 i).1) τ))‖ ^ 2)
        = (∑ p : PetTuple n Q, ∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2) from
      Finset.sum_congr rfl fun p _ => tsum_congr fun x => by simp only [cubeShiftSum, cubeProd]]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    rw [show ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹)
        * (∏ i : Fin (n + 1), (((Q i).card : ℝ))⁻¹) = nu (Work.Peluse.symIcc N) Q from by
      unfold nu; rw [pow_two]; ring]
  -- (II) the lower-dimensional cube sum
  have hII : Work.Peluse.boxSumPow n (fun i : Fin n => Q i.castSucc) (Work.Peluse.symIcc N) h
      = ((nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) : ℝ) : ℂ) * V := by
    rw [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum]
    have hconst : ((Work.Peluse.symIcc N).card : ℂ)⁻¹
        * (∏ i : Fin n, (((Q i.castSucc).card : ℂ))⁻¹)
        * (∏ i : Fin n, (((Q i.castSucc).card : ℂ))⁻¹)
        = ((nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) : ℝ) : ℂ) := by
      unfold nu
      rw [pow_two]
      push_cast
      ring
    rw [hconst]
    congr 1
    rw [hVdef, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact tsum_congr fun x => by simp only [cubeProd]
  have hbn : Work.Peluse.boxNormPow n (fun i : Fin n => Q i.castSucc) (Work.Peluse.symIcc N) h
      = nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) * ‖V‖ := by
    rw [Work.Peluse.boxNormPow, hII, norm_mul,
      norm_ofReal_of_nonneg (nu_nonneg _ _)]
  have hbn1 : Work.Peluse.boxNormPow (n + 1) Q (Work.Peluse.symIcc N) h
      = nu (Work.Peluse.symIcc N) Q * W := by
    rw [Work.Peluse.boxNormPow, hI,
      norm_ofReal_of_nonneg (mul_nonneg (nu_nonneg _ _) hWnn)]
  -- per-p bound
  have hper : ∀ p : PetTuple n Q,
      ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ ^ 2
        ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
          * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2)
          / ((Q (Fin.last n)).card : ℝ) ^ 2 := by
    intro p
    have hD2 : ∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x
        = ((Q (Fin.last n)).card : ℂ)
          * ∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x := by
      have h1 : (∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x)
          = ∑' x : ℤ, ∑ a ∈ Q (Fin.last n),
              cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 (x + a) := by
        refine tsum_congr fun x => ?_
        rw [cubeShiftSum]
        exact Finset.sum_attach (Q (Fin.last n))
          (fun a => cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 (x + a))
      exact h1.trans (tsum_sum_shift (Q (Fin.last n)) (summable_cubeProd hsupp p.1 p.2))
    have hD3 : ‖∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x‖ ^ 2
        ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
          * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2) := by
      simpa only [cubeShiftSum, cubeProd] using
        tsum_cubeShiftSum_norm_sq_le Q hN h hbd hsupp p.1 p.2
    have hnorm : ‖∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x‖
        = ((Q (Fin.last n)).card : ℝ)
          * ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ := by
      rw [hD2, norm_mul, norm_natCast_complex]
    have hsq : ((Q (Fin.last n)).card : ℝ) ^ 2
        * ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ ^ 2
        ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
          * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2) := by
      calc ((Q (Fin.last n)).card : ℝ) ^ 2
            * ‖∑' x : ℤ, cubeProd (fun i : Fin n => Q i.castSucc) h p.1 p.2 x‖ ^ 2
          = ‖∑' x : ℤ, cubeShiftSum Q h p.1 p.2 x‖ ^ 2 := by rw [hnorm, mul_pow]
        _ ≤ _ := hD3
    rw [le_div_iff₀ (pow_pos hQncard 2)]
    nlinarith [hsq]
  -- the ‖V‖ bound
  have hVbound : ‖V‖ ^ 2 ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ)
      * pairNum (fun i : Fin n => Q i.castSucc) / ((Q (Fin.last n)).card : ℝ) ^ 2 * W := by
    have hsum_le : ‖V‖ ^ 2 ≤ (Fintype.card (PetTuple n Q) : ℝ)
        * ∑ p : PetTuple n Q, (2 * ((Work.Peluse.symIcc N).card : ℝ)
            * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2)
            / ((Q (Fin.last n)).card : ℝ) ^ 2) := by
      rw [hVdef]
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2) ?_
      refine le_trans sq_sum_le_card_mul_sum_sq ?_
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hper p)
        (Nat.cast_nonneg _)
    have hfac : (∑ p : PetTuple n Q, (2 * ((Work.Peluse.symIcc N).card : ℝ)
            * (∑' x : ℤ, ‖cubeShiftSum Q h p.1 p.2 x‖ ^ 2)
            / ((Q (Fin.last n)).card : ℝ) ^ 2))
        = 2 * ((Work.Peluse.symIcc N).card : ℝ) / ((Q (Fin.last n)).card : ℝ) ^ 2 * W := by
      rw [hWdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hfac, card_tuple_eq_pairNum] at hsum_le
    calc ‖V‖ ^ 2 ≤ pairNum (fun i : Fin n => Q i.castSucc)
          * (2 * ((Work.Peluse.symIcc N).card : ℝ) / ((Q (Fin.last n)).card : ℝ) ^ 2 * W) := hsum_le
      _ = 2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
          / ((Q (Fin.last n)).card : ℝ) ^ 2 * W := by ring
  -- coefficient identities
  have hcoef1 : nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
      * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc) = 1 := by
    have hS0 : ((Work.Peluse.symIcc N).card : ℝ) ≠ 0 := ne_of_gt hScard
    have hprod : (∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹)
        * (∏ i : Fin n, ((Q i.castSucc).card : ℝ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [inv_mul_cancel₀]
      exact_mod_cast Finset.card_ne_zero.mpr (hQ i.castSucc)
    calc nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
          * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
        = (((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((Work.Peluse.symIcc N).card : ℝ))
          * ((∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹)
              * (∏ i : Fin n, ((Q i.castSucc).card : ℝ))) ^ 2 := by
            unfold nu pairNum
            rw [Finset.prod_pow]
            ring
      _ = 1 := by rw [inv_mul_cancel₀ hS0, hprod]; ring
  have hcoef2 : nu (Work.Peluse.symIcc N) Q * ((Q (Fin.last n)).card : ℝ) ^ 2
      = nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) := by
    have hp : ((Q (Fin.last n)).card : ℝ) ≠ 0 := ne_of_gt hQncard
    have h1 : (((Q (Fin.last n)).card : ℝ))⁻¹ * ((Q (Fin.last n)).card : ℝ) = 1 :=
      inv_mul_cancel₀ hp
    calc nu (Work.Peluse.symIcc N) Q * ((Q (Fin.last n)).card : ℝ) ^ 2
        = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
          * ((∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹)
              * ((((Q (Fin.last n)).card : ℝ))⁻¹ * ((Q (Fin.last n)).card : ℝ))) ^ 2 := by
          unfold nu
          rw [Fin.prod_univ_castSucc]
          ring
      _ = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
          * (∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹) ^ 2 := by
          rw [h1]; ring
      _ = nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) := by
          unfold nu; ring
  have hcoef : (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2
      * (2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
          / ((Q (Fin.last n)).card : ℝ) ^ 2) = 2 * nu (Work.Peluse.symIcc N) Q := by
    have hp2 : ((Q (Fin.last n)).card : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hQncard)
    have hA : (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2
        * (2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
            / ((Q (Fin.last n)).card : ℝ) ^ 2)
        = 2 * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
            * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc))
          * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
            / ((Q (Fin.last n)).card : ℝ) ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hA, hcoef1]
    have hb : 2 * 1 * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
        / ((Q (Fin.last n)).card : ℝ) ^ 2)
        = 2 * (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)
        / ((Q (Fin.last n)).card : ℝ) ^ 2) := by ring
    rw [hb]
    congr 1
    rw [div_eq_iff hp2]
    exact hcoef2.symm
  rw [hbn, hbn1]
  calc (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc) * ‖V‖) ^ 2
      = (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2 * ‖V‖ ^ 2 := by ring
    _ ≤ (nu (Work.Peluse.symIcc N) (fun i : Fin n => Q i.castSucc)) ^ 2
        * (2 * ((Work.Peluse.symIcc N).card : ℝ) * pairNum (fun i : Fin n => Q i.castSucc)
            / ((Q (Fin.last n)).card : ℝ) ^ 2 * W) :=
        mul_le_mul_of_nonneg_left hVbound (sq_nonneg _)
    _ = 2 * nu (Work.Peluse.symIcc N) Q * W := by rw [← mul_assoc, hcoef]
    _ = 2 * (nu (Work.Peluse.symIcc N) Q * W) := by ring


/-- **The general form of Peluse's Gowers--Cauchy--Schwarz step.**
For a complex function `f` supported in the symmetric interval `symIcc N` and shift sets
`Q : Fin (n+1) → Finset ℤ` with `Q i` nonempty and `|a| ≤ N` for `a ∈ Q (Fin.last n)`,
`(‖f‖^{2^n}_{□^n_{Q₁,…,Q_n}([-N,N])})^2 ≤ 2 ‖f‖^{2^{n+1}}_{□^{n+1}_{Q₁,…,Q_{n+1}}([-N,N])}`,
i.e. the box-norm power at level `n+1` dominates (up to the factor `2`) the square of the box-norm
power at level `n`.  Unlike `Work.Peluse.PET.two_mul_boxNormPow_succ_ge`, no reality hypothesis is
imposed on `f`. -/
theorem boxNormPow_succ_ge_general (t : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : Fin (t + 1) → Finset ℤ) {N : ℕ} (f : ℤ → ℂ),
    (∀ i, (Q i).Nonempty) → 0 < N → (∀ i a, a ∈ Q i → |a| ≤ (N : ℤ)) →
    Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    C * (Work.Peluse.boxNormPow t (fun i : Fin t => Q i.castSucc) (Work.Peluse.symIcc N) f) ^ 2
      ≤ Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) f := by
  classical
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro Q N f hQ hN hbd hsuppIn hbd'
  -- `SupportIn` in the form `∀ x ∉ symIcc N, f x = 0`
  have hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := by
    intro x hx
    apply hsuppIn
    have hx' : ¬ |x| ≤ (N : ℤ) := fun hle =>
      hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hle)
    have h2 : (N : ℤ) < |x| := lt_of_not_ge hx'
    have h3 : (N : ℤ) < (x.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact h2
    exact_mod_cast h3
  have hmain := two_mul_boxNormPow_succ_ge_complex Q hN f hQ
    (fun a ha => hbd (Fin.last t) a ha) hsupp
  have h2 : (1 / 2 : ℝ)
      * (Work.Peluse.boxNormPow t (fun i : Fin t => Q i.castSucc) (Work.Peluse.symIcc N) f) ^ 2
      ≤ (1 / 2 : ℝ) * (2 * Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) f) :=
    mul_le_mul_of_nonneg_left hmain (by norm_num)
  linarith

end

end Work.Peluse.Concat
