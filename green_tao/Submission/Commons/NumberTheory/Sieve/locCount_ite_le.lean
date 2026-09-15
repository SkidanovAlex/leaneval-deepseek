import Mathlib
import Submission.Commons.NumberTheory.Sieve.card_system_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Sieve.card_omega_one_gen
import Submission.Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct

namespace Commons.NumberTheory.Sieve

open Finset
open scoped BigOperators

/-- **The local density of a nonempty system is at most `1/p`.**  For a prime `p` larger than the
coefficient bound `Amax` and than `W`, and for a nonzero local datum `σ : PrimeData m` (i.e. the
system `θ_i(x) = 0`, `i ∈ σ.X ∪ σ.X'`, is nonempty), the number of solutions in `(ZMod p)^t` of the
system `p ∣ (if i ∈ σ.X ∪ σ.X' then p else 1) → θ_i(x) = 0` is at most `p ^ (t-1)`, i.e. the
density is at most `1/p`.

This is the input of the summability condition `hv3` of
`Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct_weighted` for the local weights
`v_p σ = (locCount …)/p^t` of Green–Tao §10 (eq. (10.2)–(10.7)).

Proof sketch: since `σ ≠ 0`, the set `S := σ.X ∪ σ.X'` is nonempty; pick `i₀ ∈ S`.  The solution
set of the system is contained in the solution set of the single condition `θ_{i₀}(x) = 0`, which
has exactly `p ^ (t-1)` elements by `Commons.NumberTheory.Sieve.card_omega_one_gen`: the form is
`W·(∑_j L_j x_j + b) + 1` with `L_j = ((A i₀ j : ℤ) : ZMod p)` and `b = ((b i₀ : ℤ) : ZMod p)`;
`W ≠ 0` in `ZMod p` because `0 < W < p`, and `L ≠ 0` because some `A i₀ j₀ ≠ 0` with
`|A i₀ j₀| ≤ Amax < p` (`ZMod.natCast_zmod_eq_zero_iff_dvd` or
`CharP.cast_eq_zero_iff`).  Use `Finset.card_le_card` for the inclusion of the filtered sets.
The fact that `σ ≠ 0` implies `σ.X ∪ σ.X' ≠ ∅` is `PrimeData.ne_zero_iff` (private in
`hasSum_dirichlet_eulerProduct.lean`; reprove it by cases on `σ`). -/
theorem locCount_ite_le {p m t : ℕ} [Fact p.Prime] (W Amax : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) (σ : PrimeData m) (hσ : σ ≠ 0) (ht : 1 ≤ t)
    (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hW0 : 0 < W) (hWp : W < p) (hAmaxp : Amax < p) :
    @locCount m t W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
        (NeZero.of_pos (Fact.out : p.Prime).pos) ≤ p ^ (t - 1) := by
  classical
  -- `σ ≠ 0` means the index set `σ.X ∪ σ.X'` is nonempty.
  have hS : σ.X ∪ σ.X' ≠ ∅ := by
    intro h
    obtain ⟨h1, h2⟩ := Finset.union_eq_empty.mp h
    obtain ⟨X, X'⟩ := σ
    change X = ∅ at h1
    change X' = ∅ at h2
    apply hσ
    rw [h1, h2]
    rfl
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  -- The linear coefficient vector `L j = ((A i₀ j : ℤ) : ZMod p)` is nonzero.
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
  -- The constant term `((W : ℕ) : ZMod p)` is nonzero.
  have hW : ((W : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ZMod p) p W] at h
    exact not_le.mpr hWp (Nat.le_of_dvd hW0 h)
  -- The solution set of the system is contained in the solution set of the single equation
  -- `θ_{i₀}(x) = 0`.
  have hsub : (Finset.univ.filter
        (fun x : Fin t → ZMod p => ∀ i, p ∣ (if i ∈ σ.X ∪ σ.X' then p else 1) →
          thetaMod W A b p i x = 0))
      ⊆ (Finset.univ.filter (fun x : Fin t → ZMod p => thetaMod W A b p i₀ x = 0)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx i₀ (by rw [if_pos hi₀])
  have hcard := Finset.card_le_card hsub
  -- The single-equation solution set has exactly `p ^ (t - 1)` elements.
  have hEq : (Finset.univ.filter
      (fun x : Fin t → ZMod p => thetaMod W A b p i₀ x = 0)).card = p ^ (t - 1) := by
    rw [Finset.filter_congr (fun x (_ : x ∈ Finset.univ) => by
      simp only [thetaMod]; rfl)]
    exact card_omega_one_gen ht hW _ hL _
  rw [locCount]
  exact le_trans hcard (le_of_eq hEq)

end Commons.NumberTheory.Sieve
