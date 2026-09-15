import Mathlib
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le

namespace Commons.NumberTheory.Sieve

/-- Local count at a prime dividing `W` (Green–Tao Lemma 9.2, the `p ≤ w` case): if `p ∣ W` then
`θ_i(x) = W·(…) + 1 ≡ 1 (mod p)` for every `i`, so the system `θ_i(x) ≡ 0 (mod p)` over the
nonempty index set `σ.X ∪ σ.X'` has no solution and the local count vanishes.

`locCount W A b M p` counts the `x ∈ (ZMod p)^t` with `p ∣ M i → thetaMod W A b p i x = 0`, where
`thetaMod W A b p i x = W·(∑_j A_{ij} x_j + b_i) + 1` in `ZMod p`.

Proof sketch: `locCount` is the cardinality of a filtered set, and the filter is empty: for
`i ∈ σ.X ∪ σ.X'` (nonempty because `σ ≠ 0`), `thetaMod W A b p i x = 0 * (…) + 1 = 1` because
`(W : ZMod p) = 0` (`p ∣ W`), and `(1 : ZMod p) ≠ 0` since `1 < p`.  Then
`Finset.card_eq_zero` / `Finset.eq_empty_iff_forall_notMem`. -/
theorem locCount_ite_eq_zero_of_dvd {p m t : ℕ} [NeZero p] (hp : p.Prime) (W Amax : ℕ)
    (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (σ : PrimeData m) (hσ : σ ≠ 0)
    (ht : 1 ≤ t) (hpW : p ∣ W) :
    locCount W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p = 0 := by
  classical
  rw [locCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨-, hx⟩ := hx
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
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  -- `(W : ZMod p) = 0` because `p ∣ W`.
  have hW : (W : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p W]
    exact hpW
  -- hence `θ_i(x) = 1` for every `x`.
  have htheta : thetaMod W A b p i x = 1 := by
    simp only [thetaMod]
    rw [hW]
    ring
  -- but the filter demands `θ_i(x) = 0`.
  have h0 : thetaMod W A b p i x = 0 := hx i (by rw [if_pos hi])
  -- and `(1 : ZMod p) ≠ 0` because `p` is prime.
  have hone : (1 : ZMod p) ≠ 0 := by
    intro h1
    have hdvd : p ∣ 1 := by
      have hcast := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp (by simpa using h1)
      simpa using hcast
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ≤ p := hp.two_le
    omega
  rw [htheta] at h0
  exact hone h0

end Commons.NumberTheory.Sieve
