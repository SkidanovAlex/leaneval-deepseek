import Mathlib
import Submission.Work.Peluse.PET.two_mul_boxNormPow_succ_ge

/-!
# The iterated Cauchy--Schwarz lower bound for the Gowers box norm

This file proves

`((∑_{x ∈ [-N,N]} ‖h x‖)/|[-N,N]|)^{2^t} ≤ 2^{2^t - 1} ‖h‖^{2^t}_{□^t_{Q₁,…,Q_t}([-N,N])}`

for a nonnegative real function `h` supported in `[-N,N]` (`t` arbitrary, `Q_i ⊆ [-N,N]`
nonempty): the `L¹`-average of `h` is controlled, to the power `2^t`, by the `2^t`-th power of the
Gowers box norm of `h`.

The `L¹`-bound is the trivial direction of the Gowers-norm monotonicity
`‖h‖_{□^{t+1}} ≥ ‖h‖_{□^t}`: at level `0` the box-norm power *is* the `L¹`-average
(`boxNormPow_zero`), and each further level squares it at the price of a factor `2`
(`Work.Peluse.PET.two_mul_boxNormPow_succ_ge`, the Gowers--Cauchy--Schwarz step of Peluse's
Lemma 2.3 specialised to a single function).  Iterating that step `t` times produces the
constant `2^{2^t - 1}`.

The version with the intermediate right-hand side `2^{2^t}/2 · ‖h‖^{2^t}_{□^t}` is
`cs_iterate_ge_aux`; the division-by-two form is what makes the induction step free of natural
number subtraction.  The general `t`-fold statement is the form consumed by
`Work.Peluse.Track.boxNormPow_v2_degenerate`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.Peluse.Track

noncomputable section

/-- `boxSumPow` at level zero is the normalised `tsum` of `f`: there are no directions, so the
cube term is `f x` itself, and the sums over the (empty) shift tuples collapse. -/
private lemma boxSumPow_zero (Q : Fin 0 → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow 0 Q S f = ((S.card : ℂ))⁻¹ * ∑' x : ℤ, f x := by
  unfold Work.Peluse.boxSumPow Work.Peluse.prodCubeSum
  simp only [Fin.prod_univ_zero, mul_one]
  congr 1
  rw [Fintype.sum_unique, Fintype.sum_unique]
  refine tsum_congr (fun x => ?_)
  rw [Fintype.prod_unique]
  simp [Work.Peluse.weight, Work.Peluse.cornerShift]

/-- At level zero the box-norm power is the `L¹` average of `f` over `S`, for `f` vanishing off `S`
and real nonnegative. -/
private lemma boxNormPow_zero (Q : Fin 0 → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) (hreal : ∀ x : ℤ, f x = ((‖f x‖ : ℝ) : ℂ)) :
    Work.Peluse.boxNormPow 0 Q S f = (∑ x ∈ S, ‖f x‖) / ((S.card : ℕ) : ℝ) := by
  have hsum : (∑' x : ℤ, f x) = (((∑ x ∈ S, ‖f x‖) : ℝ) : ℂ) := by
    rw [tsum_eq_sum (fun x hx => hsupp x hx)]
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => hreal x
  rw [Work.Peluse.boxNormPow, boxSumPow_zero, norm_mul, hsum,
    Complex.norm_of_nonneg (Finset.sum_nonneg fun x _ => norm_nonneg _)]
  rw [norm_inv, Complex.norm_natCast, inv_mul_eq_div]

/-- `2 ^ m / 2 = 2 ^ (m - 1)` for `m ≥ 1`. -/
private lemma half_pow_two (m : ℕ) (hm : 1 ≤ m) : (2 : ℝ) ^ m / 2 = 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The iterated Cauchy--Schwarz bound in the form adapted to the induction, with the
right-hand side `2^{2^t}/2 · ‖h‖^{2^t}_{□^t}`. -/
theorem cs_iterate_ge_aux : ∀ (t : ℕ) (Q : Fin t → Finset ℤ) (N : ℕ) (hN : 0 < N) (h : ℤ → ℂ),
    (∀ i, (Q i).Nonempty) → (∀ i a, a ∈ Q i → |a| ≤ (N : ℤ)) →
    (∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0) →
    (∀ x : ℤ, h x = ((‖h x‖ : ℝ) : ℂ)) →
    ((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖) / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ t)
      ≤ (2 ^ (2 ^ t) / 2) * Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) h := by
  intro t
  induction t with
  | zero =>
      intro Q N _hN h hQ hbd hsupp hreal
      simp only [Nat.pow_zero, pow_one]
      rw [boxNormPow_zero Q (Work.Peluse.symIcc N) h hsupp hreal]
      rw [show (2 : ℝ) / 2 = 1 by norm_num, one_mul]
  | succ n ih =>
      intro Q N hN h hQ hbd hsupp hreal
      have hIH := ih (fun i : Fin n => Q i.castSucc) N hN h
          (fun i => hQ i.castSucc) (fun i a ha => hbd i.castSucc a ha) hsupp hreal
      have hstep := Work.Peluse.PET.two_mul_boxNormPow_succ_ge Q hN h hQ
          (fun a ha => hbd (Fin.last n) a ha) hsupp hreal
      have hA0 : (0 : ℝ) ≤ (∑ x ∈ Work.Peluse.symIcc N, ‖h x‖)
          / (((Work.Peluse.symIcc N).card : ℕ) : ℝ) :=
        div_nonneg (Finset.sum_nonneg fun x _ => norm_nonneg _) (Nat.cast_nonneg _)
      calc ((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖)
              / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ (n + 1))
          = (((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖)
              / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ n)) ^ 2 := by
              rw [← pow_mul, pow_succ]
        _ ≤ ((2 ^ (2 ^ n) / 2) * Work.Peluse.boxNormPow n (fun i : Fin n => Q i.castSucc)
              (Work.Peluse.symIcc N) h) ^ 2 :=
              pow_le_pow_left₀ (pow_nonneg hA0 _) hIH 2
        _ = (2 ^ (2 ^ n)) ^ 2 / 4 * (Work.Peluse.boxNormPow n (fun i : Fin n => Q i.castSucc)
              (Work.Peluse.symIcc N) h) ^ 2 := by ring
        _ ≤ (2 ^ (2 ^ n)) ^ 2 / 4 * (2 * Work.Peluse.boxNormPow (n + 1) Q
              (Work.Peluse.symIcc N) h) := by
              apply mul_le_mul_of_nonneg_left hstep
              positivity
        _ = 2 ^ (2 ^ (n + 1)) / 2 * Work.Peluse.boxNormPow (n + 1) Q
              (Work.Peluse.symIcc N) h := by
              have hp : ((2 : ℝ) ^ (2 ^ n)) ^ 2 = 2 ^ (2 ^ (n + 1)) := by
                rw [← pow_mul, pow_succ]
              rw [hp]; ring

theorem cs_iterate_ge {t : ℕ} (Q : Fin t → Finset ℤ) {N : ℕ} (hN : 0 < N)
    (h : ℤ → ℂ) (hQ : ∀ i, (Q i).Nonempty) (hbd : ∀ i a, a ∈ Q i → |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (hreal : ∀ x : ℤ, h x = ((‖h x‖ : ℝ) : ℂ)) :
    ((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖) / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ t)
      ≤ 2 ^ (2 ^ t - 1) * Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) h := by
  have haux := cs_iterate_ge_aux t Q N hN h hQ hbd hsupp hreal
  rwa [half_pow_two (2 ^ t) Nat.one_le_two_pow] at haux

end

end Work.Peluse.Track
