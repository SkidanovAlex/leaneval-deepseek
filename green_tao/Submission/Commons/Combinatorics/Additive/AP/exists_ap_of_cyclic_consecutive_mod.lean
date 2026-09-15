import Mathlib
import Submission.Commons.Combinatorics.Additive.AP.exists_ap_of_cyclic_consecutive

namespace Commons.Combinatorics.Additive.AP

/-- If `a 0, a 1, …, a (n+1)` are `n+2` elements of `A` all lying in `[0, N)`, and consecutive
differences are all congruent modulo `M` (with `M ≥ 2 * N + 1`) to a nonzero residue, then
`A` contains a genuine `(n+2)`-term arithmetic progression.

Indeed every consecutive integer difference has absolute value `< N`, so any two of them differ
by an integer of absolute value `< 2 * N < M`; being congruent mod `M` they must be *equal*.
Thus the sequence is an affine (integer) progression with nonzero step, and the statement reduces
to the `M = 2 * N + 1` case. -/
theorem exists_ap_of_cyclic_consecutive_mod {n N M : ℕ} (hM : 2 * N + 1 ≤ M)
    {A : Finset ℕ} (a : Fin (n + 2) → ℕ)
    (haA : ∀ j : Fin (n + 2), a j ∈ A) (haN : ∀ j : Fin (n + 2), a j < N)
    (t : ZMod M) (ht : t ≠ 0)
    (hstep : ∀ j : Fin (n + 1),
      ((a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ) : ZMod M) = t) :
    ∃ c b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < n + 2 → c + b * j ∈ A := by
  classical
  -- The consecutive integer differences.
  let e : Fin (n + 1) → ℤ := fun j => (a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ)
  have he_t : ∀ j : Fin (n + 1), (e j : ZMod M) = t := by
    intro j
    simpa [e] using hstep j
  -- Each difference lies in `(-N, N)`.
  have heN : ∀ j : Fin (n + 1), |e j| < (N : ℤ) := by
    intro j
    have hp : (0 : ℤ) ≤ (a j.succ : ℤ) := by exact_mod_cast (Nat.zero_le (a j.succ))
    have hpN : (a j.succ : ℤ) < (N : ℤ) := by exact_mod_cast (haN j.succ)
    have hq : (0 : ℤ) ≤ (a (j.castSucc : Fin (n + 2)) : ℤ) := by
      exact_mod_cast (Nat.zero_le (a (j.castSucc : Fin (n + 2))))
    have hqN : (a (j.castSucc : Fin (n + 2)) : ℤ) < (N : ℤ) := by
      exact_mod_cast (haN (j.castSucc : Fin (n + 2)))
    rw [abs_lt]
    constructor <;> linarith
  have h2N : (2 * (N : ℤ)) < (M : ℤ) := by
    have h : ((2 * N + 1 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    push_cast at h
    linarith
  -- All consecutive differences are equal.
  have he_eq : ∀ j k : Fin (n + 1), e j = e k := by
    intro j k
    have hsub : (e j : ZMod M) - (e k : ZMod M) = 0 := by
      rw [he_t j, he_t k, sub_self]
    have hz : ((e j - e k : ℤ) : ZMod M) = 0 := by simpa using hsub
    have hdvd : (M : ℤ) ∣ e j - e k :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (e j - e k) M).mp hz
    have habs : |e j - e k| < (M : ℤ) := by
      have h1 : |e j - e k| ≤ |e j| + |e k| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (e j) (-(e k))
      have h2 : |e j| + |e k| < 2 * (N : ℤ) := by linarith [heN j, heN k]
      linarith
    exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs)
  let e0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let s : ℤ := e e0
  have he_s : ∀ j : Fin (n + 1), e j = s := by
    intro j
    simpa [s] using he_eq j e0
  -- The (common) difference is nonzero.
  have hsn : s ≠ 0 := by
    intro hs0
    apply ht
    calc t = (e e0 : ZMod M) := (he_t e0).symm
      _ = (s : ZMod M) := rfl
      _ = 0 := by rw [hs0]; simp
  have hsN : |s| < (N : ℤ) := by
    have h := heN e0
    simpa [s] using h
  -- Reduce to the `M = 2 * N + 1` case with residue `s`.
  let t' : ZMod (2 * N + 1) := (s : ZMod (2 * N + 1))
  have ht' : t' ≠ 0 := by
    intro h0
    have hz : ((s : ℤ) : ZMod (2 * N + 1)) = 0 := by simpa [t'] using h0
    have hdvd : ((2 * N + 1 : ℕ) : ℤ) ∣ s :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd s (2 * N + 1)).mp hz
    have hlt : |s| < ((2 * N + 1 : ℕ) : ℤ) := by
      have hcast : ((2 * N + 1 : ℕ) : ℤ) = 2 * (N : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      linarith
    exact hsn (Int.eq_zero_of_abs_lt_dvd hdvd hlt)
  have hstep' : ∀ j : Fin (n + 1),
      ((a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ) : ZMod (2 * N + 1)) = t' := by
    intro j
    have h : e j = s := he_s j
    have h' : ((e j : ℤ) : ZMod (2 * N + 1)) = ((s : ℤ) : ZMod (2 * N + 1)) := by
      rw [h]
    simpa [e, Int.cast_sub, t'] using h'
  exact exists_ap_of_cyclic_consecutive a haA haN t' ht' hstep'

end Commons.Combinatorics.Additive.AP
