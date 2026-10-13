import Mathlib
import Submission.Work.DSM5b.HCF.Basic

/-!
# The "surjection complex" over an arbitrary finset

`Work.DSM5b.SurjIdx`/`Work.DSM5b.SurjTerm`/`Work.DSM5b.surjD` are the terms and differential of
the surjection complex attached to a finset `S₀ : Finset (Fin n)`.  For the honest tuple complex of
the coefficient system supported on the subsets of size exactly `k` (the "graded piece"
`Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` of the size filtration) the relevant finsets are arbitrary
subsets `S₀ : Finset ι` of an *arbitrary* index type `ι`.

This file provides the same objects for an arbitrary `S₀ : Finset ι`:

* `GSurjIdx S₀ q` — the tuples `τ : Fin (q+1) → ι` with `tupRng τ = S₀`;
* `GSurjTerm S₀ N q` — functions on those tuples with values in `N`;
* `gsurjD S₀ N q` — the differential, dropping the deletions which lose surjectivity onto `S₀`.

Nothing here uses an ordering on `ι`, so the statements are immediately applicable to the index
type of `Work.DSM5b.HCF.htcD_exact_above`.
-/

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]

/-- The tuples of length `q+1` in `ι` whose range is exactly `S₀`. -/
abbrev GSurjIdx (S₀ : Finset ι) (q : ℕ) : Type u := {τ : Fin (q + 1) → ι // tupRng τ = S₀}

/-- The `q`-th term of the surjection complex attached to `S₀`: functions on the tuples whose
range is exactly `S₀`. -/
abbrev GSurjTerm (S₀ : Finset ι) (N : Type u) (q : ℕ) : Type u := GSurjIdx S₀ q → N

/-- The differential of the surjection complex attached to `S₀`: the alternating sum of the
deletions which keep the range equal to `S₀` (a deletion which loses surjectivity contributes
`0`).  This is the honest tuple differential of the coefficient system supported on the single
subset `S₀`. -/
noncomputable def gsurjD (S₀ : Finset ι) (N : Type u) [AddCommGroup N] [Module R N]
    (q : ℕ) : GSurjTerm S₀ N q →ₗ[R] GSurjTerm S₀ N (q + 1) where
  toFun z := fun τ => ∑ i : Fin (q + 2), if h : tupRng (tupDel i τ.1) = S₀ then
      ((-1 : R) ^ (i : ℕ)) • z ⟨tupDel i τ.1, h⟩ else 0
  map_add' z z' := by
    funext τ
    rw [Pi.add_apply]
    trans ∑ i : Fin (q + 2), ((if h : tupRng (tupDel i τ.1) = S₀ then
          ((-1 : R) ^ (i : ℕ)) • z ⟨tupDel i τ.1, h⟩ else 0) +
        (if h : tupRng (tupDel i τ.1) = S₀ then
          ((-1 : R) ^ (i : ℕ)) • z' ⟨tupDel i τ.1, h⟩ else 0))
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : tupRng (tupDel i τ.1) = S₀
      · rw [dif_pos h, dif_pos h, dif_pos h]
        simp only [Pi.add_apply, smul_add]
      · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]
    · rw [Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    rw [Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : tupRng (tupDel i τ.1) = S₀
    · rw [dif_pos h, dif_pos h]
      simp only [RingHom.id_apply]
      exact smul_comm _ _ _
    · rw [dif_neg h, dif_neg h]
      simp only [RingHom.id_apply, smul_zero]

@[simp] lemma gsurjD_apply (S₀ : Finset ι) (N : Type u) [AddCommGroup N] [Module R N]
    (q : ℕ) (z : GSurjTerm S₀ N q) (τ : GSurjIdx S₀ (q + 1)) :
    gsurjD (R := R) S₀ N q z τ = ∑ i : Fin (q + 2),
      (if h : tupRng (tupDel i τ.1) = S₀ then
        ((-1 : R) ^ (i : ℕ)) • z ⟨tupDel i τ.1, h⟩ else 0) := rfl

end Work.DSM5b.HCF
