import ChallengeDeps
import Mathlib.Data.PNat.Basic

/-!
# Infinite sets of solutions vs. infinitely many denominators
-/

open scoped Nat
open Set

namespace Submission.DS

/-- The set of solution pairs for per-denominator solution-numerator sets `sol`. -/
def pairSet (sol : ℕ+ → Set ℕ) : Set (ℕ × ℕ+) := {p | p.1 ∈ sol p.2}

/-- Denominators admitting at least one solution. -/
def denomSet (sol : ℕ+ → Set ℕ) : Set ℕ+ := {q | (sol q).Nonempty}

lemma denomSet_eq_snd_image (sol : ℕ+ → Set ℕ) :
    denomSet sol = Prod.snd '' pairSet sol := by
  ext q
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a, q), ha, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp⟩

lemma denom_finite_of_pair_finite {sol : ℕ+ → Set ℕ} (h : (pairSet sol).Finite) :
    (denomSet sol).Finite := by
  rw [denomSet_eq_snd_image]
  exact h.image (fun p : ℕ × ℕ+ => p.2)

lemma pair_finite_of_denom_finite {sol : ℕ+ → Set ℕ} (hfin : ∀ q, (sol q).Finite)
    (h : (denomSet sol).Finite) : (pairSet sol).Finite := by
  have hEq : pairSet sol = ⋃ q ∈ denomSet sol, (fun a : ℕ => (a, q)) '' sol q := by
    ext p
    constructor
    · intro hp
      exact mem_iUnion₂.mpr ⟨p.2, ⟨p.1, hp⟩, ⟨p.1, hp, rfl⟩⟩
    · intro hp
      rcases mem_iUnion₂.mp hp with ⟨q, _hq, a, ha, hpair⟩
      cases hpair
      simpa [pairSet] using ha
  rw [hEq]
  exact h.biUnion (fun q _ => (hfin q).image (fun a : ℕ => (a, q)))

/-- Infinite solution pairs iff infinitely many denominators admit a solution. -/
lemma infinite_pairs_iff_infinite_denoms (sol : ℕ+ → Set ℕ) (hfin : ∀ q, (sol q).Finite) :
    (pairSet sol).Infinite ↔ (denomSet sol).Infinite := by
  constructor
  · intro h hd
    exact h (pair_finite_of_denom_finite hfin hd)
  · intro h hp
    exact h (denom_finite_of_pair_finite hp)

end Submission.DS
