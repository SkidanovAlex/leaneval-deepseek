import Mathlib
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le
import Submission.Commons.NumberTheory.Sieve.card_omega_one_gen

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Sieve

open Finset
open scoped BigOperators

/-- Local count at a prime for a system with exactly one active index (Green–Tao Lemma 9.2, first
case), general form: if `σ.X ∪ σ.X'` has exactly one element `i`, then the number of
`x ∈ (ZMod p)^t` with `θ_i(x) = 0` is `p^(t-1)`.  Here `W` need NOT be smaller than `p`; only
`p ∤ W` is used (i.e. `W ≠ 0` in `ZMod p`).

`locCount W A b M p` counts the `x ∈ (ZMod p)^t` with `p ∣ M i → thetaMod W A b p i x = 0`, where
`thetaMod W A b p i x = W·(∑_j A_{ij} x_j + b_i) + 1` in `ZMod p`.

Use `Commons.NumberTheory.Sieve.card_omega_one_gen` (prime `p`, `W ≠ 0` in `ZMod p`, `L ≠ 0`,
`b : ZMod p`): `#{x : W * ((∑ j, L j * x j) + b) + 1 = 0} = p ^ (t - 1)`.  Here `L` is
`fun j => ((A i j : ℤ) : ZMod p)`, nonzero because some `A i j ≠ 0` (`hne i`) and
`(A i j).natAbs ≤ Amax < p`; `W ≠ 0` in `ZMod p` from `¬ p ∣ W`
(`ZMod.natCast_zmod_eq_zero_iff_dvd`, with `0 < W` ruling out `W = 0`).  Finally identify the two
filtered sets: `p ∣ (if i ∈ σ.X ∪ σ.X' then p else 1)` holds exactly for `i ∈ σ.X ∪ σ.X'` (a prime
does not divide `1`), so for a singleton index set the solution set is the one counted by
`card_omega_one_gen`. -/
theorem locCount_one_active {p m t : ℕ} [NeZero p] (hp : p.Prime) (W Amax : ℕ)
    (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (σ : PrimeData m)
    (ht : 1 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hW0 : 0 < W) (hWp : ¬ p ∣ W) (hAmaxp : Amax < p) (hcard : (σ.X ∪ σ.X').card = 1) :
    locCount W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p = p ^ (t - 1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  -- `σ.X ∪ σ.X'` is a singleton `{i₀}`.
  obtain ⟨i₀, hS⟩ := Finset.card_eq_one.mp hcard
  have hmem : i₀ ∈ σ.X ∪ σ.X' := by
    rw [hS]; exact Finset.mem_singleton_self i₀
  have hiff : ∀ i, i ∈ σ.X ∪ σ.X' ↔ i = i₀ := by
    intro i; rw [hS]; simp
  -- `W` is nonzero modulo `p`, since `p ∤ W` and `p ≠ 0`.
  have hW : ((W : ℕ) : ZMod p) ≠ 0 := by
    intro h
    exact hWp ((ZMod.natCast_eq_zero_iff W p).mp h)
  -- The coefficient vector `L j = ((A i₀ j : ℤ) : ZMod p)` is nonzero.
  have hL : (fun j => ((A i₀ j : ℤ) : ZMod p)) ≠ 0 := by
    intro hL0
    obtain ⟨j₀, hj₀⟩ := hne i₀
    have h0 : ((A i₀ j₀ : ℤ) : ZMod p) = 0 := by
      have := congrFun hL0 j₀
      simpa using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hpos : 0 < (A i₀ j₀).natAbs := Int.natAbs_pos.mpr hj₀
    have hdvd : p ∣ (A i₀ j₀).natAbs := by
      simpa using (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := A i₀ j₀)).mpr h0
    have h1 : p ≤ (A i₀ j₀).natAbs := Nat.le_of_dvd hpos hdvd
    have h2 : (A i₀ j₀).natAbs < p := lt_of_le_of_lt (hA i₀ j₀) hAmaxp
    omega
  -- The system is equivalent to the single equation `θ_{i₀}(x) = 0`.
  have hpred : ∀ x : Fin t → ZMod p,
      (∀ i, p ∣ (if i ∈ σ.X ∪ σ.X' then p else 1) → thetaMod W A b p i x = 0)
        ↔ thetaMod W A b p i₀ x = 0 := by
    intro x
    constructor
    · intro hx
      exact hx i₀ (by rw [if_pos hmem])
    · intro hx i hi
      by_cases hii : i ∈ σ.X ∪ σ.X'
      · have hi' : i = i₀ := (hiff i).mp hii
        rw [hi'] at hi ⊢
        exact hx
      · exfalso
        rw [if_neg hii] at hi
        have hle : p ≤ 1 := Nat.le_of_dvd Nat.one_pos hi
        have := hp.two_le
        omega
  rw [locCount, Finset.filter_congr (fun x _ => hpred x)]
  exact card_omega_one_gen ht hW (fun j => ((A i₀ j : ℤ) : ZMod p)) hL ((b i₀ : ℤ) : ZMod p)

end Commons.NumberTheory.Sieve
