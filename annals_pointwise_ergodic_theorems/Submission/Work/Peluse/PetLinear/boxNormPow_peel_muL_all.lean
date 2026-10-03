import Mathlib
import Submission.Work.Peluse.Peel.boxNormPow_peel_muL
import Submission.Work.Peluse.PET.muL_abs_bound

/-!
# Peeling the first coordinate of the box norm against `μ_H`, *including the degenerate case*

`Work.Peluse.Peel.boxNormPow_peel_muL` peels the first direction of Peluse's box-norm power when
that direction is a genuine arithmetic progression `c[H] = {c, 2c, …, Hc}` with `c ≠ 0`.  The
peeler used by the induction of Peluse's Lemma 4.10, however, has to be applied to the directions
`(c_m - c_i)[H]`, and these *vanish* when `c_i = c_m` — the first direction of the family is the
singleton `{0}`.

This module supplies the missing case, so that the peel is available for **every** `c : ℤ`:

`Work.Peluse.PetLinear.boxNormPow_peel_muL_all`.

## The degenerate case `c = 0`

Here `c[H] = {0}` is a singleton, so the level-lowering recursion
`Work.Peluse.Concat.boxNormPow_succ_peel_gen`,
`‖F‖^{2^{t+1}}_{□^{t+1}_Q(S)} = |Q₀|⁻² ∑_{h,h' ∈ Q₀} ‖Δ'_{h,h'}F‖^{2^t}_{□^t_{Q₁,…}(S)}`,
reads (with `|Q₀| = 1` and `Δ'_{0,0}F = F·conj F`)

`‖F‖^{2^{t+1}}_{□^{t+1}_Q(S)} = ‖F·conj F‖^{2^t}_{□^t_{Q₁,…}(S)}`,

while the right-hand side of the peel is the `μ_H`-weighted average of the *same* function (the
shift `0 · a` is trivial):

`∑_{a ∈ [-H,H]} μ_H(a) ‖F(· + 0·a)·conj F‖^{2^t} = (∑_{a ∈ [-H,H]} μ_H(a)) ‖F·conj F‖^{2^t}`.

Since `μ_H` is a probability weight on `[-H,H]` (`Work.Peluse.PET.sum_muL_Icc`, which the import
`Work.Peluse.PET.muL_abs_bound` provides), the two sides agree.

The non-degenerate case `c ≠ 0` is `Work.Peluse.Peel.boxNormPow_peel_muL` itself; the target below
is the case split between them.
-/

open scoped BigOperators

namespace Work.Peluse.PetLinear

/-- The degenerate arithmetic progression `0[H] = {0, 0, …, 0}` is the singleton `{0}` (for
`H ≥ 1`). -/
theorem arithIcc_zero_eq_singleton {H : ℕ} (hH : 1 ≤ H) : Work.Peluse.arithIcc (0 : ℤ) H = {0} := by
  unfold Work.Peluse.arithIcc
  rw [show (fun n : ℕ => (0 : ℤ) * (n : ℤ)) = (fun _ : ℕ => (0 : ℤ)) from by funext n; simp]
  exact Finset.image_const ⟨1, by simp [hH]⟩ 0

/-- **The peel in the degenerate direction `c = 0`.**  For `t ≥ 1`, a direction family whose first
member is the singleton `{0}` and a function supported in `[-N,N]`, the box-norm power of order
`t + 1` is the `μ_H`-weighted average (the shift `0 · a` being trivial) of the box-norm power of
order `t` of `u ↦ F u · conj (F u)`. -/
private theorem peel_aux_zero {t : ℕ} (ht : 1 ≤ t) {N : ℕ} (F : ℤ → ℂ)
    (hF : Work.Peluse.SupportIn F N) (Q : Fin (t + 1) → Finset ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hQ0 : Q 0 = Work.Peluse.arithIcc (0 : ℤ) H) :
    Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) F
      = ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
          Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
            (fun u : ℤ => F (u + 0 * a) * star (F u)) := by
  classical
  have hsing : Q 0 = {0} := by rw [hQ0]; exact arithIcc_zero_eq_singleton hH
  -- the level-lowering recursion, with the first direction family collapsed to `{0}`
  have hpeel := Work.Peluse.Concat.boxNormPow_succ_peel_gen (t := t) ht Q
      (Work.Peluse.symIcc N) (Work.Peluse.FinSuppZ.of_supportIn hF)
  rw [hsing] at hpeel
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, inv_one, one_pow,
    one_mul] at hpeel
  -- `hpeel` now reads `‖F‖ = ‖F·conj F‖`; the right-hand side is the same function
  rw [hpeel, show (fun u : ℤ => F (u + 0) * star (F (u + 0))) = (fun u : ℤ => F u * star (F u))
    from by funext u; simp]
  rw [show (∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
        Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
          (fun u : ℤ => F (u + 0 * a) * star (F u)))
      = ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
        Work.Peluse.boxNormPow t (fun j : Fin t => Q j.succ) (Work.Peluse.symIcc N)
          (fun u : ℤ => F u * star (F u)) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show (fun u : ℤ => F (u + 0 * a) * star (F u)) = (fun u : ℤ => F u * star (F u))
      from by funext u; simp]]
  -- the `μ_H`-weights sum to one
  rw [← Finset.sum_mul, Work.Peluse.PET.sum_muL_Icc H hH, one_mul]

theorem boxNormPow_peel_muL_all {m : ℕ} (hm : 2 ≤ m) {N : ℕ} (F : ℤ → ℂ)
    (hF : Work.Peluse.SupportIn F N) (Q : Fin m → Finset ℤ) (c : ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hQ0 : Q ⟨0, by omega⟩ = Work.Peluse.arithIcc c H) :
    Work.Peluse.boxNormPow m Q (Work.Peluse.symIcc N) F
      = ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
          Work.Peluse.boxNormPow (m - 1)
            (fun j : Fin (m - 1) => Q ⟨j.1 + 1, by omega⟩)
            (Work.Peluse.symIcc N) (fun u : ℤ => F (u + c * a) * star (F u)) := by
  by_cases hc : c = 0
  · -- the degenerate direction: `c[H] = {0}`
    subst hc
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    have ht : 1 ≤ t := by omega
    exact peel_aux_zero (t := t) ht F hF Q hH hQ0
  · -- the genuine arithmetic progression
    exact Work.Peluse.Peel.boxNormPow_peel_muL hm F hF Q hc hH hQ0

end Work.Peluse.PetLinear
