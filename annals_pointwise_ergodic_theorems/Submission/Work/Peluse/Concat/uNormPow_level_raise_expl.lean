import Mathlib
import Submission.Work.Peluse.Concat.boxNormPow_succ_ge_general

/-!
# The level raising for the uniformity-norm power, with the explicit constant

`Work.Peluse.Concat.boxNormPow_succ_ge_general` (in the imported module) proves Peluse's
Gowers--Cauchy--Schwarz step in the constant form

`(1/2) * (‖f‖^{2^t}_{□^t_{Q,…,Q}([-N,N])})^2 ≤ ‖f‖^{2^{t+1}}_{□^{t+1}_{Q,…,Q}([-N,N])}`

for a complex function `f` supported in `symIcc N`, a nonempty shift set `Q` with `|a| ≤ N` for
`a ∈ Q`, and `N > 0`.  Iterating that step `b - a` times gives the level raising

`(1/2)^{2^{b-a}-1} * (uNormPow a Q (symIcc N) f)^{2^{b-a}} ≤ uNormPow b Q (symIcc N) f`

of this file, with the **explicit** constant `(1/2)^{2^{b-a}-1}` in place of the existential
constant `c > 0` of `Work.Peluse.UControl.uNormPow_level_raise`.

The proof is the elementary induction on the number of steps `k = b - a`, carried out in the
rearranged (all-positive) form

`(uNormPow a Q (symIcc N) f)^{2^k} ≤ 2^{2^k - 1} * uNormPow (a + k) Q (symIcc N) f`,

which multiplies without division; at the end one multiplies by `(1/2)^{2^k-1}` and uses
`(1/2)^m * 2^m = 1`.

## Main result

* `Work.Peluse.Concat.uNormPow_level_raise_expl`: the statement above.
-/

set_option linter.unusedVariables false

namespace Work.Peluse.Concat

open Work.Peluse

noncomputable section

/-- One Gowers--Cauchy--Schwarz step, with the explicit constant `1/2`, in the uniformity-norm
normalisation `uNormPow t Q S f = boxNormPow t (fun _ => Q) S f`. -/
private lemma uNormPow_succ_ge_half {t : ℕ} {Q : Finset ℤ} {N : ℕ} (hN : 0 < N) {f : ℤ → ℂ}
    (hQ : Q.Nonempty) (hbd : ∀ x ∈ Q, |x| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0) :
    (1 / 2 : ℝ) * (Work.Peluse.uNormPow t Q (Work.Peluse.symIcc N) f) ^ 2
      ≤ Work.Peluse.uNormPow (t + 1) Q (Work.Peluse.symIcc N) f := by
  have hmain := two_mul_boxNormPow_succ_ge_complex (fun _ : Fin (t + 1) => Q) hN f
    (fun _ => hQ) (fun a _ => hbd a (by assumption)) hsupp
  have h2 : (Work.Peluse.boxNormPow t (fun _ : Fin t => Q) (Work.Peluse.symIcc N) f) ^ 2
      ≤ 2 * Work.Peluse.boxNormPow (t + 1) (fun _ : Fin (t + 1) => Q)
          (Work.Peluse.symIcc N) f := hmain
  have hgoal : (1 / 2 : ℝ)
      * (Work.Peluse.boxNormPow t (fun _ : Fin t => Q) (Work.Peluse.symIcc N) f) ^ 2
      ≤ Work.Peluse.boxNormPow (t + 1) (fun _ : Fin (t + 1) => Q)
          (Work.Peluse.symIcc N) f := by
    linarith
  simpa only [Work.Peluse.uNormPow] using hgoal

/-- `SupportIn f N` in the form `f` vanishes off the symmetric interval, as consumed by
`two_mul_boxNormPow_succ_ge_complex`. -/
private lemma eq_zero_of_notMem_symIcc {f : ℤ → ℂ} {N : ℕ} (h : Work.Peluse.SupportIn f N) :
    ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := by
  intro x hx
  apply h
  have hx' : ¬ |x| ≤ (N : ℤ) := fun hle => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hle)
  have h2 : (N : ℤ) < |x| := lt_of_not_ge hx'
  have h3 : (N : ℤ) < (x.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact h2
  exact_mod_cast h3

/-- The arithmetic of the induction step: `2·(2^k - 1) = 2^{k+1} - 2`. -/
private lemma two_mul_two_pow_sub_one (k : ℕ) : 2 * (2 ^ k - 1) = 2 ^ (k + 1) - 2 := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  omega

/-- `2^{m-1} * 2 = 2^m` for `1 ≤ m`. -/
private lemma two_pow_pred_mul_two (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (m - 1) * 2 = (2 : ℝ) ^ m := by
  rw [← pow_succ, Nat.sub_add_cancel hm]

/-- **The level raising in rearranged form.**  For every number of steps `k`,

`(uNormPow a Q (symIcc N) f)^{2^k} ≤ 2^{2^k - 1} * uNormPow (a + k) Q (symIcc N) f`.

This is equivalent to the target statement (multiply by `(1/2)^{2^k-1}`), but has no division, so
the induction multiplies cleanly. -/
private lemma uNormPow_level_raise_aux (a : ℕ) :
    ∀ k : ℕ, ∀ (Q : Finset ℤ) {N : ℕ}, 0 < N → ∀ {f : ℤ → ℂ},
      Q.Nonempty → (∀ x ∈ Q, |x| ≤ (N : ℤ)) → Work.Peluse.SupportIn f N →
      (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f) ^ (2 ^ k)
        ≤ (2 : ℝ) ^ (2 ^ k - 1) * Work.Peluse.uNormPow (a + k) Q (Work.Peluse.symIcc N) f := by
  intro k
  induction k with
  | zero =>
      intro Q N hN f hQ hbd hsupp
      simp
  | succ k ih =>
      intro Q N hN f hQ hbd hsupp
      have hstep := uNormPow_succ_ge_half (t := a + k) hN hQ hbd
        (eq_zero_of_notMem_symIcc hsupp)
      have hprev := ih Q hN (f := f) hQ hbd hsupp
      have hU : (0 : ℝ) ≤ Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f := by
        rw [Work.Peluse.uNormPow, Work.Peluse.boxNormPow]; exact norm_nonneg _
      have hsq : (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f ^ (2 ^ k)) ^ 2
          ≤ ((2 : ℝ) ^ (2 ^ k - 1)
              * Work.Peluse.uNormPow (a + k) Q (Work.Peluse.symIcc N) f) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg hU _) hprev 2
      have h1 : (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f) ^ (2 ^ (k + 1))
          = (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f ^ (2 ^ k)) ^ 2 := by
        rw [show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]
      have h2 : ((2 : ℝ) ^ (2 ^ k - 1)) ^ 2 = (2 : ℝ) ^ (2 ^ (k + 1) - 2) := by
        rw [← pow_mul, show (2 ^ k - 1) * 2 = 2 ^ (k + 1) - 2 from by
          rw [Nat.mul_comm]; exact two_mul_two_pow_sub_one k]
      have h3 : (2 : ℝ) ^ (2 ^ (k + 1) - 2)
            * (Work.Peluse.uNormPow (a + k) Q (Work.Peluse.symIcc N) f) ^ 2
          ≤ (2 : ℝ) ^ (2 ^ (k + 1) - 2)
            * (2 * Work.Peluse.uNormPow (a + k + 1) Q (Work.Peluse.symIcc N) f) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hstep]
      have hpow2 : (2 : ℝ) ^ (2 ^ (k + 1) - 2) * 2 = (2 : ℝ) ^ (2 ^ (k + 1) - 1) := by
        have hm : 1 ≤ 2 ^ (k + 1) - 1 := by
          have h := Nat.one_le_two_pow (n := k + 1); omega
        have h := two_pow_pred_mul_two (2 ^ (k + 1) - 1) hm
        rw [show (2 ^ (k + 1) - 1) - 1 = 2 ^ (k + 1) - 2 by omega] at h
        exact h
      calc (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f) ^ (2 ^ (k + 1))
          = (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f ^ (2 ^ k)) ^ 2 := h1
        _ ≤ ((2 : ℝ) ^ (2 ^ k - 1)
              * Work.Peluse.uNormPow (a + k) Q (Work.Peluse.symIcc N) f) ^ 2 := hsq
        _ = (2 : ℝ) ^ (2 ^ (k + 1) - 2)
              * (Work.Peluse.uNormPow (a + k) Q (Work.Peluse.symIcc N) f) ^ 2 := by
              rw [mul_pow, h2]
        _ ≤ (2 : ℝ) ^ (2 ^ (k + 1) - 2)
            * (2 * Work.Peluse.uNormPow (a + k + 1) Q (Work.Peluse.symIcc N) f) := h3
        _ = (2 : ℝ) ^ (2 ^ (k + 1) - 1)
              * Work.Peluse.uNormPow (a + (k + 1)) Q (Work.Peluse.symIcc N) f := by
              rw [← mul_assoc, hpow2, Nat.add_assoc]

/-- **Level raising for the uniformity-norm power, with the explicit constant.**

For `1 ≤ a ≤ b`, a nonempty shift set `Q` contained in `[-N,N]` (`N > 0`), and a function `f`
supported in `[-N,N]` and bounded by `1`,

`(1/2)^{2^{b-a}-1} · (‖f‖^{2^a}_{U^a_Q([-N,N])})^{2^{b-a}} ≤ ‖f‖^{2^b}_{U^b_Q([-N,N])}`.

This is the `b - a`-fold iteration of Peluse's Gowers--Cauchy--Schwarz step
`two_mul_boxNormPow_succ_ge_complex`, with the constant tracked explicitly (the existential form is
`Work.Peluse.UControl.uNormPow_level_raise`). -/
theorem uNormPow_level_raise_expl (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∀ (Q : Finset ℤ) {N : ℕ} (hN : 0 < N) {f : ℤ → ℂ},
      Q.Nonempty → (∀ x ∈ Q, |x| ≤ (N : ℤ)) →
      Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      ((1 / 2 : ℝ) ^ (2 ^ (b - a) - 1))
        * (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f) ^ (2 ^ (b - a))
        ≤ Work.Peluse.uNormPow b Q (Work.Peluse.symIcc N) f := by
  intro Q N hN f hQ hbd hsupp _
  have h := uNormPow_level_raise_aux a (b - a) Q hN (f := f) hQ hbd hsupp
  rw [Nat.add_sub_cancel' hab] at h
  have h1 := mul_le_mul_of_nonneg_left h
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 ^ (b - a) - 1))
  have hone : (1 / 2 : ℝ) ^ (2 ^ (b - a) - 1) * (2 : ℝ) ^ (2 ^ (b - a) - 1) = 1 := by
    rw [← mul_pow]; norm_num
  calc (1 / 2 : ℝ) ^ (2 ^ (b - a) - 1)
        * (Work.Peluse.uNormPow a Q (Work.Peluse.symIcc N) f) ^ (2 ^ (b - a))
      ≤ (1 / 2 : ℝ) ^ (2 ^ (b - a) - 1)
          * ((2 : ℝ) ^ (2 ^ (b - a) - 1)
              * Work.Peluse.uNormPow b Q (Work.Peluse.symIcc N) f) := h1
    _ = ((1 / 2 : ℝ) ^ (2 ^ (b - a) - 1) * (2 : ℝ) ^ (2 ^ (b - a) - 1))
          * Work.Peluse.uNormPow b Q (Work.Peluse.symIcc N) f := by ring
    _ = Work.Peluse.uNormPow b Q (Work.Peluse.symIcc N) f := by rw [hone, one_mul]

end

end Work.Peluse.Concat
