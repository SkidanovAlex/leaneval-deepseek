import Mathlib
import Submission.Commons.Combinatorics.QBinomial.sum_Icc_mul_gb_eq_one
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

namespace Commons.Combinatorics.QBinomial

theorem sum_Icc_card_submodule_finrank_eq_indicator (n : ℕ) (a : ℕ → ℤ)
    (ha : ∀ t : ℕ, 1 ≤ t →
      ∑ i ∈ Finset.Icc 1 t, a i * (Commons.Combinatorics.QBinomial.gb t i : ℤ) = 1) :
    ∀ V' : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∑ i ∈ Finset.Icc 1 (Module.finrank (ZMod 2) V'),
        a i * (Nat.card {W : Submodule (ZMod 2) V' // Module.finrank (ZMod 2) W = i} : ℤ))
        = if V' = ⊥ then 0 else 1 := by
  intro V'
  by_cases h : V' = ⊥
  · rw [if_pos h, h]
    simp
  · rw [if_neg h]
    have hd1 : 1 ≤ Module.finrank (ZMod 2) V' := Submodule.one_le_finrank_iff.mpr h
    have hterm : ∀ i : ℕ,
        Nat.card {W : Submodule (ZMod 2) V' // Module.finrank (ZMod 2) W = i} =
          gb (Module.finrank (ZMod 2) V') i := by
      intro i
      unfold gb
      exact (Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
        (K := ZMod 2) (V := (Fin (Module.finrank (ZMod 2) V') → ZMod 2)) (V' := V')
        (ℓ := i) (by rw [Module.finrank_pi, Fintype.card_fin])).symm
    have hcongr : (∑ i ∈ Finset.Icc 1 (Module.finrank (ZMod 2) V'),
        a i * (Nat.card {W : Submodule (ZMod 2) V' // Module.finrank (ZMod 2) W = i} : ℤ))
        = ∑ i ∈ Finset.Icc 1 (Module.finrank (ZMod 2) V'),
            a i * (gb (Module.finrank (ZMod 2) V') i : ℤ) :=
      Finset.sum_congr rfl (fun i _ => by rw [hterm i])
    rw [hcongr]
    exact ha (Module.finrank (ZMod 2) V') hd1

end Commons.Combinatorics.QBinomial
