import Mathlib

namespace Work.Parab.invOrbit

/-- Along a backward chain of the abstract inverse-branch relation: if `w - k` is a
point of the domain `Dφ` whose `φ`-image is `z k`, then every earlier point
`w - j` (`j ≤ k`) lies in `Dφ` and has `φ`-image `z j`.

This is a downward induction: the successor relation `hsucc` transports membership in
`Dφ` one step back, and `habel` transports the value of `φ`. -/
theorem backward_chain {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {φ : ℂ → ℂ} {Dφ : Set ℂ} {z : ℕ → ℂ} {k : ℕ}
    (hsucc : ∀ w ∈ Dφ, (w + 1 ∈ Dφ ↔ φ w ∈ D₀))
    (habel : ∀ w ∈ Dφ, w + 1 ∈ Dφ → φ (w + 1) = f₀ (φ w))
    (hzD : ∀ j : ℕ, 1 ≤ j → z j ∈ D₀) (hz : ∀ j : ℕ, f₀ (z (j + 1)) = z j)
    {w : ℂ} (hw : w - (k : ℂ) ∈ Dφ) (hwφ : φ (w - (k : ℂ)) = z k) :
    ∀ j : ℕ, j ≤ k → w - (j : ℂ) ∈ Dφ ∧ φ (w - (j : ℂ)) = z j := by
  intro j hj
  refine Nat.decreasingInduction'
    (n := k) (P := fun j => w - (j : ℂ) ∈ Dφ ∧ φ (w - (j : ℂ)) = z j) ?_ hj ⟨hw, hwφ⟩
  -- step: from the claim at `k' + 1` deduce it at `k'`
  intro k' _ _
  rintro ⟨ha, hφa⟩
  -- `w - (k'+1) + 1 = w - k'`
  have hcast : ((k' + 1 : ℕ) : ℂ) = (k' : ℂ) + 1 := by push_cast; ring
  have ha' : w - ((k' + 1 : ℕ) : ℂ) + 1 = w - (k' : ℂ) := by rw [hcast]; ring
  -- membership one step back, via the successor relation and `z (k'+1) ∈ D₀`
  have hmem : (w - ((k' + 1 : ℕ) : ℂ)) + 1 ∈ Dφ := by
    rw [hsucc (w - ((k' + 1 : ℕ) : ℂ)) ha]
    rw [hφa]
    exact hzD (k' + 1) (by omega)
  constructor
  · rw [← ha']; exact hmem
  · have h := habel (w - ((k' + 1 : ℕ) : ℂ)) ha hmem
    rw [ha'] at h
    rw [hφa] at h
    rw [hz k'] at h
    exact h

end Work.Parab.invOrbit
