import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.abel_exp_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VU

open Finset
open scoped BigOperators
open Work.BMF

attribute [local instance] Classical.propDecidable

/-! ### Auxiliary lemmas -/

private lemma eC_add_v2 (x y : ℝ) : eC (x + y) = eC x * eC y := by
  rw [eC, eC, eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eC_intCast_v2 (m : ℤ) : eC (m : ℝ) = 1 := by
  have h : eC (m : ℝ) = Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [eC]
    congr 1
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private lemma eC_add_int_v2 (x : ℝ) (m : ℤ) : eC (x + (m : ℝ)) = eC x := by
  rw [eC_add_v2, eC_intCast_v2, mul_one]

private lemma phase_int_shift_v2 (m : ℕ) (α : Fin m → ℝ) (z : Fin m → ℤ) (h : ℕ) :
    phase m α h = phase m (fun j : Fin m => α j - (z j : ℝ)) h
      + ((∑ j : Fin m, z j * ((h : ℤ) ^ ((j:ℕ)+1)) : ℤ) : ℝ) := by
  have h1 : phase m α h - phase m (fun j : Fin m => α j - (z j : ℝ)) h
      = ((∑ j : Fin m, z j * ((h : ℤ) ^ ((j:ℕ)+1)) : ℤ) : ℝ) := by
    rw [phase, phase, ← Finset.sum_sub_distrib]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    ring
  linarith [h1]

private lemma polySum_sub_intCast_v2 (m : ℕ) (α : Fin m → ℝ) (z : Fin m → ℤ) (x : ℝ) :
    polySum m (fun j : Fin m => α j - (z j : ℝ)) x = polySum m α x := by
  rw [polySum, polySum]
  apply Finset.sum_congr rfl
  intro h _
  rw [← eC_add_int_v2 (phase m (fun j : Fin m => α j - (z j : ℝ)) h)
        (∑ j : Fin m, z j * ((h : ℤ) ^ ((j:ℕ)+1)))]
  congr 1
  exact (phase_int_shift_v2 m α z h).symm

private lemma hasDerivAt_poly_phase_v2 (m : ℕ) (c : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ j : Fin m, c j * t ^ ((j:ℕ)+1))
      (∑ j : Fin m, c j * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ))) t := by
  have h : ∀ j : Fin m, HasDerivAt (fun t : ℝ => c j * t ^ ((j:ℕ)+1))
      (c j * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ))) t := by
    intro j
    have h1 : HasDerivAt (fun t : ℝ => t ^ ((j:ℕ)+1))
        ((((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ))) t := by
      have h2 := hasDerivAt_pow ((j:ℕ)+1) t
      simpa only [Nat.add_sub_cancel] using h2
    simpa only [mul_assoc] using h1.const_mul (c j)
  exact HasDerivAt.fun_sum (fun j _ => h j)

private lemma deriv_poly_phase_v2 (m : ℕ) (c : Fin m → ℝ) (t : ℝ) :
    deriv (fun t : ℝ => ∑ j : Fin m, c j * t ^ ((j:ℕ)+1)) t
      = ∑ j : Fin m, c j * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ)) :=
  (hasDerivAt_poly_phase_v2 m c t).deriv

private lemma norm_deriv_poly_phase_le_v2 (k : ℕ) (hk : 2 ≤ k) {H : ℝ} (hH : 0 < H)
    {c : Fin (k-1) → ℝ} (hc : ∀ j : Fin (k-1), |c j| ≤ H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)))
    {L : ℕ} (hL : (L:ℝ) ≤ H) :
    ∀ t ∈ Set.Icc (1:ℝ) (L:ℝ),
      ‖deriv (fun t : ℝ => ∑ j : Fin (k-1), c j * t ^ ((j:ℕ)+1)) t‖ ≤ (k:ℝ)^2 * H⁻¹ := by
  have hHinv : 0 ≤ H⁻¹ := inv_nonneg.mpr (le_of_lt hH)
  have hsum : ∑ j : Fin (k-1), (((j:ℕ)+1 : ℕ) : ℝ) ≤ (k:ℝ)^2 := by
    have h1 : ∀ j : Fin (k-1), (((j:ℕ)+1 : ℕ) : ℝ) ≤ (k:ℝ) := by
      intro j
      have hj : (j:ℕ) + 1 ≤ k := by have := j.isLt; omega
      exact_mod_cast hj
    calc ∑ j : Fin (k-1), (((j:ℕ)+1 : ℕ) : ℝ)
        ≤ ∑ _j : Fin (k-1), (k:ℝ) := Finset.sum_le_sum (fun j _ => h1 j)
      _ = ((k-1 : ℕ) : ℝ) * k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]
      _ ≤ (k:ℝ)^2 := by
          have h2 : ((k-1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.sub_le k 1
          nlinarith [show (0:ℝ) ≤ (k:ℝ) by exact_mod_cast Nat.zero_le k]
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have htH : t ≤ H := le_trans ht.2 hL
  rw [deriv_poly_phase_v2]
  calc ‖∑ j : Fin (k-1), c j * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ))‖
      ≤ ∑ j : Fin (k-1), ‖c j * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ))‖ := norm_sum_le _ _
    _ = ∑ j : Fin (k-1), |c j| * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hA : 0 ≤ (((j:ℕ)+1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have ht : 0 ≤ t ^ ((j:ℕ)) := pow_nonneg ht0 _
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg, hA, ht]
    _ ≤ ∑ j : Fin (k-1), (((j:ℕ)+1 : ℕ) : ℝ) * H⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        have h2 : t ^ ((j:ℕ)) ≤ H ^ ((j:ℕ)) := pow_le_pow_left₀ ht0 htH _
        have h3 : 0 ≤ (((j:ℕ)+1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hpow : H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) * H ^ ((j:ℕ)) = H⁻¹ := by
          rw [← Real.rpow_natCast H ((j:ℕ)), ← Real.rpow_add hH]
          have : -(((j:ℕ)+1 : ℕ) : ℝ) + ((j:ℕ) : ℝ) = -1 := by push_cast; ring
          rw [this, Real.rpow_neg_one]
        calc |c j| * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ))
            ≤ H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) * (((j:ℕ)+1 : ℕ) : ℝ) * t ^ ((j:ℕ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc j) h3)
                (pow_nonneg ht0 _)
          _ ≤ H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) * (((j:ℕ)+1 : ℕ) : ℝ) * H ^ ((j:ℕ)) :=
              mul_le_mul_of_nonneg_left h2
                (mul_nonneg (Real.rpow_nonneg (le_of_lt hH) _) h3)
          _ = (((j:ℕ)+1 : ℕ) : ℝ) * H⁻¹ := by rw [← hpow]; ring
    _ = (∑ j : Fin (k-1), (((j:ℕ)+1 : ℕ) : ℝ)) * H⁻¹ := by rw [Finset.sum_mul]
    _ ≤ (k:ℝ)^2 * H⁻¹ := mul_le_mul_of_nonneg_right hsum hHinv

/-- **Abel comparison of two polynomial phases.** Let `k ≥ 2`, `H > 0`, `y ≤ ⌊H⌋₊`, and let
`a, α : Fin (k-1) → ℝ` satisfy `dist(α j, a j) ≤ H^{-(j+1)}` in the wrapped sense (the `∃ z : ℤ`).
Then `‖polySum (k-1) a y‖ ≤ ‖polySum (k-1) α y‖ + 2π k² H⁻¹ Σ_{h < ⌊y⌋₊} ‖polySum (k-1) α h‖`.

Route: choose `α' = α - z` (`z : Fin (k-1) → ℤ`) with `|a j - α' j| ≤ H^{-(j+1)}`; the sums are
unchanged because `α ↦ α - z` changes `phase` by an integer (`eC` has period `1`, i.e.
`eC (x + m) = eC x` for `m : ℤ`); then apply `Submission.Work.BMF.abel_exp_sum` with
`a h := eC (phase (k-1) α' h)` and `β t := phase (k-1) a t - phase (k-1) α' t`, whose derivative
is bounded by `Σ_{j} (j+1) H^{-(j+1)} H^j = k(k-1)/2 · H^{-1} ≤ k² H^{-1}` for `t ≤ H`.
Note `polySum (k-1) α y = Σ_{h ∈ Icc 1 ⌊y⌋₊} eC (phase (k-1) α h)`, so the partial sums of
`abel_exp_sum`'s input sequence are `polySum (k-1) α h` for `h ∈ range ⌊y⌋₊`; the `HasDerivAt` /
derivative-bound hypotheses of `abel_exp_sum` are for `y ∈ Set.Icc 1 L` with `L := ⌊y⌋₊ ≤ H`.
All auxiliary lemmas you introduce must be marked `private` (or given a name unique to this file)
so that they cannot clash with sibling files. -/
theorem polysum_abel_compare_v2 (k : ℕ) (hk : 2 ≤ k) {H : ℝ} (hH : 0 < H)
    {a α : Fin (k-1) → ℝ} {y : ℝ} (hy : y ≤ ⌊H⌋₊)
    (hclose : ∀ j : Fin (k-1), ∃ z : ℤ, |α j - a j - z| ≤ H ^ (-(((j:ℕ)+1 : ℕ) : ℝ))) :
    ‖polySum (k-1) a y‖ ≤ ‖polySum (k-1) α y‖ +
      2 * Real.pi * (k:ℝ)^2 * H⁻¹ * ∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖ := by
  choose z hz using hclose
  have hae : ∀ j : Fin (k-1), |a j - (α j - (z j : ℝ))| ≤ H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) := by
    intro j
    have h := hz j
    rw [show a j - (α j - (z j : ℝ)) = -(α j - a j - (z j : ℝ)) by ring, abs_neg]
    exact h
  have hLH : ((⌊y⌋₊ : ℕ) : ℝ) ≤ H := by
    have h1 : ⌊y⌋₊ ≤ ⌊H⌋₊ := by
      have h3 : ⌊y⌋₊ ≤ ⌊((⌊H⌋₊ : ℕ) : ℝ)⌋₊ := Nat.floor_mono hy
      rwa [Nat.floor_natCast] at h3
    have h2 : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊H⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    exact h2.trans (Nat.floor_le (le_of_lt hH))
  let β : ℝ → ℝ := fun t => ∑ j : Fin (k-1), (a j - (α j - (z j : ℝ))) * t ^ ((j:ℕ)+1)
  have hβderiv : ∀ t ∈ Set.Icc (1:ℝ) ((⌊y⌋₊ : ℕ) : ℝ), HasDerivAt β (deriv β t) t := by
    intro t _
    exact (hasDerivAt_poly_phase_v2 (k-1) (fun j : Fin (k-1) => a j - (α j - (z j : ℝ))) t
      ).differentiableAt.hasDerivAt
  have hβbnd : ∀ t ∈ Set.Icc (1:ℝ) ((⌊y⌋₊ : ℕ) : ℝ), ‖deriv β t‖ ≤ (k:ℝ)^2 * H⁻¹ := by
    intro t ht
    exact norm_deriv_poly_phase_le_v2 k hk hH hae hLH t ht
  have hβapply : ∀ h : ℕ, β (h:ℝ)
      = phase (k-1) a h - phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h := by
    intro h
    show (∑ j : Fin (k-1), (a j - (α j - (z j : ℝ))) * (h:ℝ) ^ ((j:ℕ)+1))
        = phase (k-1) a h - phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h
    rw [phase, phase, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hkey : ∀ h : ℕ,
      eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h) * eC (β (h:ℝ))
        = eC (phase (k-1) a h) := by
    intro h
    rw [← eC_add_v2, hβapply h]
    congr 1
    ring
  have hsum_eq : polySum (k-1) a y
      = ∑ h ∈ Finset.Icc 1 ⌊y⌋₊,
          eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h) * eC (β (h:ℝ)) := by
    rw [polySum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← hkey h]
  have hLHS : ‖∑ h ∈ Finset.Icc 1 ⌊y⌋₊,
        eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h)‖
      = ‖polySum (k-1) α y‖ := by
    rw [← polySum_sub_intCast_v2 (k-1) α z y, polySum]
  have hR : ∀ h : ℕ, ‖∑ h' ∈ Finset.Icc 1 h,
        eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h')‖
      = ‖polySum (k-1) α (h:ℝ)‖ := by
    intro h
    rw [← polySum_sub_intCast_v2 (k-1) α z (h:ℝ), polySum, Nat.floor_natCast]
  have habel := abel_exp_sum ⌊y⌋₊
    (fun h => eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h)) β ((k:ℝ)^2 * H⁻¹)
    hβderiv hβbnd
  have hsumR : ∑ h ∈ Finset.range ⌊y⌋₊,
        ‖∑ h' ∈ Finset.Icc 1 h,
          eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h')‖
      = ∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖ :=
    Finset.sum_congr rfl (fun h _ => hR h)
  calc ‖polySum (k-1) a y‖
      = ‖∑ h ∈ Finset.Icc 1 ⌊y⌋₊,
          eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h) * eC (β (h:ℝ))‖ := by
        rw [hsum_eq]
    _ ≤ ‖∑ h ∈ Finset.Icc 1 ⌊y⌋₊,
          eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h)‖ +
          2 * Real.pi * ((k:ℝ)^2 * H⁻¹) * ∑ h ∈ Finset.range ⌊y⌋₊,
            ‖∑ h' ∈ Finset.Icc 1 h,
              eC (phase (k-1) (fun j : Fin (k-1) => α j - (z j : ℝ)) h')‖ := habel
    _ = ‖polySum (k-1) α y‖ +
          2 * Real.pi * ((k:ℝ)^2 * H⁻¹) * ∑ h ∈ Finset.range ⌊y⌋₊,
            ‖polySum (k-1) α (h:ℝ)‖ := by rw [hLHS, hsumR]
    _ = ‖polySum (k-1) α y‖ +
          2 * Real.pi * (k:ℝ)^2 * H⁻¹ * ∑ h ∈ Finset.range ⌊y⌋₊,
            ‖polySum (k-1) α (h:ℝ)‖ := by ring

end Work.BMF.VU
