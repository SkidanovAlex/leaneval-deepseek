import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_card_subspaces
import Submission.Work.LT.gb_gaussian_prod_le
import Submission.Work.LT.gb_gaussian_prod_pos
import Submission.Work.LT.gb_submodule_le_equiv

namespace Work.LT

/-! ### The Gaussian-binomial count, cross-multiplied

For a finite `𝔽₂`-vector space `V` of dimension `k`, the number of `j`-dimensional subspaces times
the number `∏_{i<j} (2^j - 2^i)` of ordered bases of a `j`-dimensional space equals the number
`∏_{i<j} (2^k - 2^i)` of ordered `j`-tuples of linearly independent vectors of `V`
(this is the Gaussian binomial identity `#{W} = ∏ (2^k - 2^i)/(2^j - 2^i)`).
Proved as `gb_card_subspaces`. -/

/-- **Counting bound for `j`-dimensional subspaces of a finite `𝔽₂`-space.**
A `k`-dimensional `𝔽₂`-space has at most `2^{j(k-j)+j+2}` subspaces of dimension `j`.

The proof is the elementary double count: mapping an ordered `j`-tuple of linearly independent
vectors to its span gives `#{W} · ∏_{i<j}(2^j-2^i) = ∏_{i<j}(2^k-2^i)`, and the crude termwise
bound `(2^k - 2^i) ≤ 2^{k-j+1}(2^j - 2^i)` (valid for `i < j ≤ k`) turns the right hand side into
`2^{j(k-j)+j} · ∏_{i<j}(2^j - 2^i)`; dividing by the positive factor `∏_{i<j}(2^j-2^i)` gives the
claim.  The extra `2^j` is exactly the slack available in this estimate. -/
theorem card_subspaces_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (j : ℕ) :
    (Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} : ℝ) ≤
      (2 : ℝ) ^ (j * (Module.finrank (ZMod 2) V - j) + j + 2) := by
  by_cases hj : j ≤ Module.finrank (ZMod 2) V
  · -- the two products appearing in the count
    set c : ℕ := ∏ i : Fin j, ((2 : ℕ) ^ j - 2 ^ (i : ℕ)) with hc_def
    have hkey : Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} * c =
        ∏ i : Fin j, ((2 : ℕ) ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := by
      rw [hc_def]
      exact gb_card_subspaces j hj
    have hle : (∏ i : Fin j, ((2 : ℕ) ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ))) ≤
        2 ^ (j * (Module.finrank (ZMod 2) V - j) + j + 2) * c := by
      rw [hc_def]
      exact gb_gaussian_prod_le hj
    have hcpos : 0 < c := by
      rw [hc_def]
      exact gb_gaussian_prod_pos j
    have hAB : Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} ≤
        2 ^ (j * (Module.finrank (ZMod 2) V - j) + j + 2) := by
      apply Nat.le_of_mul_le_mul_right _ hcpos
      calc Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} * c
          = ∏ i : Fin j, ((2 : ℕ) ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := hkey
        _ ≤ 2 ^ (j * (Module.finrank (ZMod 2) V - j) + j + 2) * c := hle
    calc (Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} : ℝ)
        ≤ ((2 ^ (j * (Module.finrank (ZMod 2) V - j) + j + 2) : ℕ) : ℝ) := by
          exact_mod_cast hAB
      _ = (2 : ℝ) ^ (j * (Module.finrank (ZMod 2) V - j) + j + 2) := by push_cast; ring
  · -- no `j`-dimensional subspace exists
    have hlt : Module.finrank (ZMod 2) V < j := not_le.mp hj
    have hE : IsEmpty {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} :=
      ⟨fun W => (ne_of_lt (lt_of_le_of_lt (Submodule.finrank_le W.val) hlt)) W.2⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hE)]
    simp

/-- Over `𝔽₂`, an `m`-dimensional space has at most `2^{j(m-j)+j+2}` subspaces of dimension `j` (the Gaussian binomial coefficient is at most a constant times `2^{j(m-j)}`; the extra `2^j` is harmless slack).  Formulated for subspaces of a given subspace `U` of `Fin m → ZMod 2`. -/
theorem gb_card_submodule (m : ℕ) (U : Submodule (ZMod 2) (Fin m → ZMod 2)) (j : ℕ) :
    (Nat.card {W : Submodule (ZMod 2) (Fin m → ZMod 2) // W ≤ U ∧ GB.frk W = j} : ℝ) ≤
      (2 : ℝ) ^ (j * (GB.frk U - j) + j + 2) := by
  -- transport to `U` viewed as the ambient space
  have hcard : Nat.card {W : Submodule (ZMod 2) (Fin m → ZMod 2) // W ≤ U ∧ GB.frk W = j} =
      Nat.card {W' : Submodule (ZMod 2) U // Module.finrank (ZMod 2) W' = j} := by
    simp only [GB.frk]
    exact gb_submodule_le_equiv U j
  rw [hcard]
  exact card_subspaces_le (V := U) j

end Work.LT
