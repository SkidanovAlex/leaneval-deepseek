import Mathlib
import Submission.Commons.Combinatorics.QBinomial.sum_Icc_card_superspace_codim_eq_indicator
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_compl

namespace Commons.LinearAlgebra.Submodule

open Module

/-- The number of superspaces of `W'` in `𝔽₂ⁿ` of dimension exactly `n - j` equals the
Gaussian binomial `gb d j`, where `d = n - finrank W'` is the codimension of `W'`.

This is `Commons.Combinatorics.QBinomial.card_superspace_codim_eq_gb` with the weaker
hypothesis `j ≤ n` in place of `j ≤ n - finrank W'`.  When `j > n - finrank W'` there is
no such superspace (a superspace has dimension at least `finrank W' > n - j`), so both
sides vanish: the left-hand side is `Nat.card` of an empty type and the right-hand side
is `gb d j = 0` because `d < j`. -/
theorem card_superspace_codim_eq_gb_of_le (n : ℕ) (W' : Submodule (ZMod 2) (Fin n → ZMod 2))
    (j : ℕ) (hj : j ≤ n) :
    Nat.card {W₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
        W' ≤ W₁ ∧ Module.finrank (ZMod 2) W₁ = n - j}
      = Commons.Combinatorics.QBinomial.gb (n - Module.finrank (ZMod 2) W') j := by
  by_cases h : j ≤ n - Module.finrank (ZMod 2) W'
  · exact Commons.Combinatorics.QBinomial.card_superspace_codim_eq_gb n W' j h
  · -- No superspace of `W'` can have dimension `n - j < finrank W'`.
    have hE : IsEmpty {W₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
        W' ≤ W₁ ∧ Module.finrank (ZMod 2) W₁ = n - j} := by
      have hmle : Module.finrank (ZMod 2) W' ≤ n := by
        have htop := Submodule.finrank_mono (R := ZMod 2) (s := W') (t := ⊤) le_top
        rw [finrank_top, Module.finrank_pi, Fintype.card_fin] at htop
        exact htop
      rw [not_le] at h
      refine ⟨fun x => ?_⟩
      obtain ⟨W₁, hle, hfr⟩ := x
      have h1 : Module.finrank (ZMod 2) W' ≤ Module.finrank (ZMod 2) W₁ :=
        Submodule.finrank_mono hle
      have h2 : Module.finrank (ZMod 2) W' ≤ n - j := hfr ▸ h1
      omega
    rw [Nat.card_eq_zero.mpr (Or.inl hE),
      Commons.Combinatorics.QBinomial.gb_eq_zero_of_lt (n - Module.finrank (ZMod 2) W') j (not_le.mp h)]

end Commons.LinearAlgebra.Submodule
