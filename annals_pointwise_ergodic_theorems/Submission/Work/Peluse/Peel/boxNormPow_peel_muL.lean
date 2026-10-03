/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.boxNormPow_shift
import Submission.Work.Peluse.Track.sum_muL_mul_eq_real
import Submission.Work.Peluse.MuL.muL_eq_zero
import Submission.Work.Peluse.Concat.boxNormPow_succ_peel_gen

/-!
# Peeling the first coordinate of Peluse's box norm against the van der Corput weight

Let `Q : Fin m → Finset ℤ` be a family of shift sets whose first member is the arithmetic
progression `c[H] = {c, 2c, …, Hc}` (`c ≠ 0`), and let `F` be supported in `[-N,N]`.  Then
Peluse's box-norm power of order `m` (Definition 2.1 of S. Peluse, Forum of Math. Pi **8** (2020),
e16) is the `μ_H`-weighted average, over the shifts `c·a` with `a ∈ [-H,H]`, of the box-norm
power of order `m-1` of the *normalised difference* `u ↦ F (u + c·a) · conj (F u)`:

`‖F‖^{2^m}_{□^m_{Q₀,…,Q_{m-1}}(S)}
   = ∑_{a ∈ [-H,H]} μ_H(a) · ‖F(· + c·a)·conj(F)‖^{2^{m-1}}_{□^{m-1}_{Q₁,…,Q_{m-1}}(S)}.`

This is the form of the peel (Gowers/Cauchy–Schwarz) step used to pass from the box norm of order
`m` built from a *single* arithmetic-progression direction family to the difference functions of
the van der Corput inequality of Peluse §2, whose weight is `μ_H`.

## Proof

1. **Peel the first coordinate** (`Work.Peluse.Concat.boxNormPow_succ_peel_gen`, a real-valued
   form of `Work.Peluse.Peel.boxSumPow_peel`): with `m = t + 1` and `t ≥ 1`,

   `‖F‖^{2^{t+1}}_{□^{t+1}_Q(S)} = |Q₀|⁻² ∑_{h,h' ∈ Q₀} ‖Δ'_{h,h'} F‖^{2^t}_{□^t_{Q₁,…}(S)}`.

2. **Reindex `Q₀ = c[H]`** as `∑_{y ∈ [H]}` using the injectivity of `y ↦ c·y` (`c ≠ 0`); as
   `|Q₀| = H`, the prefactor becomes `H⁻²`.

3. **Translate each difference**: `Δ'_{c y₁, c y₂} F` is the translate by `c y₂` of the normalised
   difference `u ↦ F (u + c(y₁ - y₂))·conj (F u)`, and the box-norm power is translation invariant
   (`Work.Peluse.BoxNorm.boxNormPow_shift`).

4. **Van der Corput weight** (`Work.Peluse.Track.sum_muL_mul_eq_real`): for any `φ : ℤ → ℝ`,

   `∑_{a ∈ [-H,H]} μ_H(a) φ(a) = H⁻² ∑_{y₁,y₂ ∈ [H]} φ(y₁ - y₂)`,

   which cancels the prefactor `H⁻²` of step 2.

The statement `Work.Peluse.Peel.boxNormPow_peel_muL` is the case `Q₀ = c[H]` of this computation,
written with the original index conventions.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Peel

noncomputable section

/-! ## Elementary reindexings of sums over `arithIcc` -/

/-- For `c ≠ 0` the arithmetic-progression set `c[L] = {c, 2c, …, Lc}` has `L` elements. -/
private lemma peel_card_arithIcc {c : ℤ} (hc : c ≠ 0) (L : ℕ) :
    (Work.Peluse.arithIcc c L).card = L := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

/-- Sums over `c[L]` are sums over `[L]` of the parametrised terms. -/
private lemma peel_sum_arithIcc {L : ℕ} {c : ℤ} (hc : c ≠ 0) {M : Type*} [AddCommMonoid M]
    (g : ℤ → M) :
    ∑ a ∈ Work.Peluse.arithIcc c L, g a = ∑ y ∈ Finset.Icc 1 L, g (c * (y : ℤ)) := by
  rw [Work.Peluse.arithIcc, Finset.sum_image]
  intro a _ b _ hab
  have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
  exact_mod_cast h

/-- The same reindexing for a double sum over `c[L] × c[L]`. -/
private lemma peel_sum_arithIcc_double {L : ℕ} {c : ℤ} (hc : c ≠ 0)
    {M : Type*} [AddCommMonoid M] (g : ℤ → ℤ → M) :
    ∑ a ∈ Work.Peluse.arithIcc c L, ∑ b ∈ Work.Peluse.arithIcc c L, g a b
      = ∑ y₁ ∈ Finset.Icc 1 L, ∑ y₂ ∈ Finset.Icc 1 L,
          g (c * (y₁ : ℤ)) (c * (y₂ : ℤ)) := by
  rw [peel_sum_arithIcc hc (fun a => ∑ b ∈ Work.Peluse.arithIcc c L, g a b)]
  exact Finset.sum_congr rfl (fun y₁ _ => peel_sum_arithIcc hc (fun b => g (c * (y₁ : ℤ)) b))

/-! ## Finite support of the normalised differences -/

/-- The normalised difference `u ↦ F (u + a) · conj (F u)` of a function supported in `[-N,N]` is
supported in `[-(N + |a|), N + |a|]`. -/
private lemma peel_supportIn_mul_star_shift {N : ℕ} {F : ℤ → ℂ} (hF : Work.Peluse.SupportIn F N)
    (a : ℤ) : Work.Peluse.SupportIn (fun u : ℤ => F (u + a) * star (F u)) (N + a.natAbs) := by
  intro u hu
  have h1 : F (u + a) = 0 := by
    apply hF
    have hle : u.natAbs ≤ (u + a).natAbs + a.natAbs := by
      have h := Int.natAbs_add_le (u + a) (-a)
      simpa [Int.natAbs_neg, add_assoc] using h
    omega
  simp [h1]

/-! ## The peel in the `t + 1` normalisation -/

/-- **The van der Corput peel of the box-norm power.**  For `t ≥ 1`, a direction family whose first
member is the progression `c[H]` (`c ≠ 0`) and a function supported in `[-N,N]`, the box-norm power
of order `t + 1` is the `μ_H`-weighted average of the box-norm powers of order `t` of the
normalised differences `u ↦ F (u + c·a)·conj (F u)`. -/
private theorem peel_aux {t : ℕ} (ht : 1 ≤ t) {N : ℕ} (F : ℤ → ℂ)
    (hF : Work.Peluse.SupportIn F N) (Q : Fin (t + 1) → Finset ℤ) {c : ℤ} (hc : c ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hQ0 : Q 0 = Work.Peluse.arithIcc c H) :
    Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) F
      = ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
          Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
            (fun u : ℤ => F (u + c * a) * star (F u)) := by
  classical
  have hcard : ((Q 0).card : ℝ) = (H : ℝ) := by
    rw [hQ0, peel_card_arithIcc hc H]
  -- the peel of the first coordinate
  have hpeel := Work.Peluse.Concat.boxNormPow_succ_peel_gen (t := t) ht Q
    (Work.Peluse.symIcc N) (Work.Peluse.FinSuppZ.of_supportIn hF)
  -- translation invariance moves the second shift onto the argument
  have hshift : ∀ y₁ y₂ : ℕ,
      Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
        (fun u : ℤ => F (u + c * (y₁ : ℤ)) * star (F (u + c * (y₂ : ℤ))))
      = Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
        (fun u : ℤ => F (u + c * ((y₁ : ℤ) - (y₂ : ℤ))) * star (F u)) := by
    intro y₁ y₂
    have hfs : Work.Peluse.FinSuppZ
        (fun u : ℤ => F (u + c * ((y₁ : ℤ) - (y₂ : ℤ))) * star (F u)) :=
      Work.Peluse.FinSuppZ.of_supportIn
        (peel_supportIn_mul_star_shift hF (c * ((y₁ : ℤ) - (y₂ : ℤ))))
    rw [show (fun u : ℤ => F (u + c * (y₁ : ℤ)) * star (F (u + c * (y₂ : ℤ))))
        = Work.Peluse.shift (c * (y₂ : ℤ))
            (fun u : ℤ => F (u + c * ((y₁ : ℤ) - (y₂ : ℤ))) * star (F u)) from by
      funext u
      simp only [Work.Peluse.shift]
      have harg : u + c * (y₂ : ℤ) + c * ((y₁ : ℤ) - (y₂ : ℤ)) = u + c * (y₁ : ℤ) := by
        ring
      rw [harg]]
    exact Work.Peluse.BoxNorm.boxNormPow_shift t (fun j : Fin t => Q j.succ)
      (Work.Peluse.symIcc N) _ (c * (y₂ : ℤ)) hfs
  -- reindex the two shift sums and normalise
  have hmain : Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) F
      = ((H : ℝ) ^ 2)⁻¹ *
        ∑ y₁ ∈ Finset.Icc 1 H, ∑ y₂ ∈ Finset.Icc 1 H,
          Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
            (fun u : ℤ => F (u + c * ((y₁ : ℤ) - (y₂ : ℤ))) * star (F u)) := by
    rw [hpeel, hcard, inv_pow]
    rw [hQ0]
    rw [peel_sum_arithIcc_double hc
      (fun h h' : ℤ => Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ)
        (Work.Peluse.symIcc N) (fun u : ℤ => F (u + h) * star (F (u + h'))))]
    rw [Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ => hshift y₁ y₂))]
  -- the van der Corput weight identity cancels the normalising factor
  rw [hmain]
  have hvd := Work.Peluse.Track.sum_muL_mul_eq_real (H := H) (by omega)
    (fun a : ℤ => Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ)
      (Work.Peluse.symIcc N) (fun u : ℤ => F (u + c * a) * star (F u)))
  rw [hvd, Finset.product_eq_sprod, Finset.sum_product]

/-! ## The target statement -/

theorem boxNormPow_peel_muL {m : ℕ} (hm : 2 ≤ m) {N : ℕ} (F : ℤ → ℂ)
    (hF : Work.Peluse.SupportIn F N) (Q : Fin m → Finset ℤ) {c : ℤ} (hc : c ≠ 0) {H : ℕ}
    (hH : 1 ≤ H) (hQ0 : Q ⟨0, by omega⟩ = Work.Peluse.arithIcc c H) :
    Work.Peluse.boxNormPow m Q (Work.Peluse.symIcc N) F
      = ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
          Work.Peluse.boxNormPow (m - 1)
            (fun j : Fin (m - 1) => Q ⟨j.1 + 1, by omega⟩)
            (Work.Peluse.symIcc N) (fun u : ℤ => F (u + c * a) * star (F u)) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have ht : 1 ≤ t := by omega
  exact peel_aux ht F hF Q hc hH hQ0

end

end Work.Peluse.Peel
