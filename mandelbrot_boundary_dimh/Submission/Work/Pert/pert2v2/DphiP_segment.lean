import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Setup
import Submission.Work.Pert.coordP_level_eq
import Submission.Work.Interfaces.Parabolic

/-! Guidance from the project lead (the requester):

LEAD (pert2_v2 S16 support). If z and z + k (k ∈ ℕ) are both in the maximal domain DphiP, then so is every z + i, 0 ≤ i ≤ k. Definitions: Pert/MaxDom.lean, GoodP w := ∃ n, w − n ∈ Φ '' Q ∧ ∀ j < n, f^[j] (seedP τ Φ Q (w − n)) ∈ Df.
Route. Let s := z − n_z and s′ := z + k − n′ be the two seeds (both in Φ '' Q), with ζ, ζ′ their Φ-preimages in Q.
  - Case z + i ≥ s′ in the integer order, i.e. i ≥ k − n′: use the seed s′ with level n′ − (k − i) ≤ n′. Its walk is a prefix of the legal walk of z + k.
  - Case z + i < s′: then s′ − s = (k − n′) + n_z > i ≥ 0 is a natural number p with Φ ζ′ = Φ ζ + p. By hOrb, F^[j] ζ ∈ Q for j ≤ p and F^[p] ζ = ζ′. Hence f^[j] (τ ζ) = τ (F^[j] ζ) ∈ Df for j ≤ p (hτF iterated, hτDf). The orbit of the seed s up to n_z + i ≤ p is legal: for j ≤ n_z by GoodP(z), and beyond n_z it is inside the gate walk. So z + i ∈ DphiP with seed s.
Reuse Pert/coordP_level_eq.lean (the same hOrb / hτF bookkeeping) and Setup.abel_iter.
-/

namespace Work.Pert.pert2v2

open MandelDim

theorem DphiP_segment {f F τ Φ : ℂ → ℂ} {Df Q : Set ℂ}
    (hinj : Set.InjOn Φ Q)
    (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hτDf : ∀ z ∈ Q, τ z ∈ Df)
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    {z : ℂ} {k : ℕ} (hz : z ∈ Work.Pert.DphiP f Df τ Φ Q)
    (hzk : z + (k : ℂ) ∈ Work.Pert.DphiP f Df τ Φ Q) :
    ∀ i : ℕ, i ≤ k → z + (i : ℂ) ∈ Work.Pert.DphiP f Df τ Φ Q := by
  intro i hi
  -- the two given levels: `nz` for `z` with seed `ζ`, `nk` for `z + k` with seed `ζ'`
  obtain ⟨nz, hseedz, hwalkz⟩ := hz
  obtain ⟨nk, hseedk, hwalkk⟩ := hzk
  have himgz : ∃ ζ ∈ Q, Φ ζ = z - (nz : ℂ) := hseedz
  have himgk : ∃ ζ ∈ Q, Φ ζ = z + (k : ℂ) - (nk : ℂ) := hseedk
  obtain ⟨ζ, hζQ, hζΦ⟩ := himgz
  obtain ⟨ζ', hζ'Q, hζ'Φ⟩ := himgk
  by_cases hcase : k ≤ nk + i
  · -- Case `i ≥ k - nk`: the point `z + i` is at level `i + nk - k ≤ nk` with the seed
    -- `z + k - nk` of `z + k`; the walk of `z + k` gives the legality.
    have hle : k ≤ i + nk := by omega
    have hcast : (((i + nk - k : ℕ)) : ℂ) = (i : ℂ) + (nk : ℂ) - (k : ℂ) := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    have harg : z + (i : ℂ) - ((i + nk - k : ℕ) : ℂ) = z + (k : ℂ) - (nk : ℂ) := by
      rw [hcast]; ring
    refine ⟨i + nk - k, ?_, ?_⟩
    · rw [harg]; exact hseedk
    · intro j hj
      rw [harg]
      exact hwalkk j (by omega)
  · -- Case `nk + i < k`: use the seed `ζ` of `z` and the level `nz + i`.  The two seeds differ by
    -- the natural number `p = (k - nk) + nz`, so `hOrb` gives the legal walk of length `p ≥ nz + i`
    -- and `hτF` converts the `F`-walk of `ζ` into the `f`-walk of `τ ζ`.
    have hnk_le : nk ≤ k := by omega
    have hcast : (((k - nk) + nz : ℕ) : ℂ) = (k : ℂ) - (nk : ℂ) + (nz : ℂ) := by
      rw [Nat.cast_add, Nat.cast_sub hnk_le]
    have hΦpp : Φ ζ' = Φ ζ + (((k - nk) + nz : ℕ) : ℂ) := by
      rw [hζ'Φ, hζΦ, hcast]; ring
    obtain ⟨hstay, -⟩ := hOrb ζ hζQ ζ' hζ'Q ((k - nk) + nz) hΦpp
    have harg : z + (i : ℂ) - ((nz + i : ℕ) : ℂ) = z - (nz : ℂ) := by
      push_cast; ring
    refine ⟨nz + i, ?_, ?_⟩
    · rw [harg]
      exact ⟨ζ, hζQ, hζΦ⟩
    · intro j hj
      have hjle : j ≤ (k - nk) + nz := by omega
      have hjQ : F^[j] ζ ∈ Q := hstay j hjle
      have hiter : τ (F^[j] ζ) = f^[j] (τ ζ) :=
        Work.Pert.tau_walk_iterate (fun l hl => hstay l (le_trans hl hjle)) hτF
      have hseed : seedP τ Φ Q (z + (i : ℂ) - ((nz + i : ℕ) : ℂ)) = τ ζ := by
        rw [seedP, harg, Work.Pert.invOn_eq hinj ⟨ζ, hζQ, hζΦ⟩ hζQ hζΦ]
      rw [hseed, ← hiter]
      exact hτDf (F^[j] ζ) hjQ

end Work.Pert.pert2v2
