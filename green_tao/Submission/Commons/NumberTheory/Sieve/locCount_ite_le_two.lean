import Mathlib
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le
import Submission.Commons.NumberTheory.Sieve.card_omega_ge_two_le
import Submission.Commons.NumberTheory.Sieve.not_proportional_zmod_of_small

namespace Commons.NumberTheory.Sieve

open Finset
open scoped BigOperators

/-- Local count bound with at least two active, non-proportional indices (Green–Tao Lemma 9.2,
second case): if `σ.X ∪ σ.X'` has at least two elements, `p ∤ W` and `2·Amax² < p`, then the number
of `x ∈ (ZMod p)^t` with `θ_i(x) = 0` for `i ∈ σ.X ∪ σ.X'` is at most `p^(t-2)`.

`locCount W A b M p` counts the `x` with `p ∣ M i → thetaMod W A b p i x = 0`.

This is the exact analogue of the existing commons lemma
`Commons.NumberTheory.Sieve.locCount_ite_le` (which proves `≤ p^(t-1)` for a single active index),
but using `Commons.NumberTheory.Sieve.card_omega_ge_two_le`:
`card_omega_ge_two_le (ht : 2 ≤ t) (L : Fin m → Fin t → ZMod p) (c : Fin m → ZMod p) (X) (hX : 2 ≤ X.card)
(hne0 : ∀ i ∈ X, L i ≠ 0) (hprop : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → ∀ lam : ZMod p, L j ≠ lam • L i)`
gives `#{x : ∀ i ∈ X, W * ((∑ j, L i j * x j) + c i) + 1 = 0} ≤ if W = 0 then 0 else p^(t - 2)`.
Take `L i := fun j => ((A i j : ℤ) : ZMod p)`, `c i := ((b i : ℤ) : ZMod p)`, `X := σ.X ∪ σ.X'`, and
the `W` of `card_omega_ge_two_le` to be `((W : ℤ) : ZMod p)`, which is nonzero since `¬ p ∣ W` and
`0 < W`, so the `if` selects `p ^ (t - 2)`.  The `hne0` hypothesis follows from `hne i` and
`(A i j).natAbs ≤ Amax < p` (using `2 * Amax ^ 2 < p`, hence `Amax < p`).  The `hprop` hypothesis is
`Commons.NumberTheory.Sieve.not_proportional_zmod_of_small` applied to the two rows, using
`2 * Amax ^ 2 < p`.  Finally identify the filtered sets: the condition
`p ∣ (if i ∈ σ.X ∪ σ.X' then p else 1)` holds exactly for `i ∈ σ.X ∪ σ.X'` (a prime does not divide
`1`), so `locCount`'s filter is the filter of `card_omega_ge_two_le`. -/
theorem locCount_ite_le_two {p : ℕ} [Fact p.Prime] {m t : ℕ} (W Amax : ℕ)
    (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (σ : PrimeData m) (W0 : ℕ)
    (ht : 2 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hW0 : 0 < W0) (hWp : ¬ p ∣ W0) (h2 : 2 * Amax ^ 2 < p)
    (hcard : 2 ≤ (σ.X ∪ σ.X').card) :
    @locCount m t W0 A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
        (NeZero.of_pos (Fact.out : p.Prime).pos) ≤ p ^ (t - 2) := by
  classical
  -- `p` is a prime, in particular `p ≠ 0` and `p ∤ 1`.
  have hpprime : p.Prime := Fact.out
  -- The set of active indices.
  set S : Finset (Fin m) := σ.X ∪ σ.X' with hSdef
  -- The active condition `p ∣ (if i ∈ S then p else 1)` is equivalent to `i ∈ S`.
  have hmem : ∀ i, p ∣ (if i ∈ S then p else 1) ↔ i ∈ S := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact ⟨fun _ => hi, fun _ => dvd_refl p⟩
    · rw [if_neg hi]
      exact ⟨fun h => absurd h hpprime.not_dvd_one, fun h => absurd h hi⟩
  -- `Amax < p`: from `2 * Amax^2 < p`.
  have hAmax_lt_p : Amax < p := by
    by_cases h0 : Amax = 0
    · subst h0
      exact hpprime.pos
    · have h1 : 1 ≤ Amax := Nat.one_le_iff_ne_zero.mpr h0
      nlinarith [sq_nonneg (Amax : ℤ), h2]
  -- `W0` is nonzero modulo `p`.
  have hW : ((W0 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ZMod p) p W0] at h
    exact hWp h
  -- The coefficient vectors `L i j = ((A i j : ℤ) : ZMod p)` are nonzero on `S`.
  have hne0 : ∀ i ∈ S, (fun j => ((A i j : ℤ) : ZMod p)) ≠ 0 := by
    intro i _
    intro hL0
    obtain ⟨j₀, hj₀⟩ := hne i
    have h0 : ((A i j₀ : ℤ) : ZMod p) = 0 := by
      have := congrFun hL0 j₀
      simpa using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hpos : 0 < (A i j₀).natAbs := Int.natAbs_pos.mpr hj₀
    have hdvd : p ∣ (A i j₀).natAbs := by
      simpa using (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := A i j₀)).mpr h0
    have h1 : p ≤ (A i j₀).natAbs := Nat.le_of_dvd hpos hdvd
    have h2' : (A i j₀).natAbs < p := lt_of_le_of_lt (hA i j₀) hAmax_lt_p
    omega
  -- Distinct rows of `S` stay non-proportional modulo `p`.
  have hprop' : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ∀ lam : ZMod p,
      (fun j => ((A i' j : ℤ) : ZMod p)) ≠ lam • (fun j => ((A i j : ℤ) : ZMod p)) := by
    intro i _ i' _ hii' lam
    exact not_proportional_zmod_of_small (A := A i) (A' := A i')
      (fun j => hA i j) (fun j => hA i' j) h2 (hprop i i' hii') lam
  -- The `locCount` filter is the filter of `card_omega_ge_two_le`.
  have hset : ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => ∀ i, p ∣ (if i ∈ S then p else 1) → thetaMod W0 A b p i x = 0))
      = ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => ∀ i ∈ S,
          ((W0 : ℕ) : ZMod p) * ((∑ j, ((A i j : ℤ) : ZMod p) * x j) + ((b i : ℤ) : ZMod p))
            + 1 = 0)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hx i hi
      have := hx i ((hmem i).mpr hi)
      simpa only [thetaMod] using this
    · intro hx i hi
      have := hx i ((hmem i).mp hi)
      simpa only [thetaMod] using this
  rw [locCount]
  rw [hset]
  have hbound := card_omega_ge_two_le (p := p) (W := ((W0 : ℕ) : ZMod p)) ht
    (fun i j => ((A i j : ℤ) : ZMod p)) (fun i => ((b i : ℤ) : ZMod p)) S hcard hne0 hprop'
  rw [if_neg hW] at hbound
  exact hbound

end Commons.NumberTheory.Sieve
