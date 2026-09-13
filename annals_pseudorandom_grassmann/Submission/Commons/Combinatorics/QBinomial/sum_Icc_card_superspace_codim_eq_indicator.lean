import Mathlib
import Submission.Commons.Combinatorics.QBinomial.sum_Icc_mul_gb_eq_one
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_compl
import Submission.Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient

namespace Commons.Combinatorics.QBinomial

open Module

noncomputable section

private lemma finrank_pi_zmod2 (n : ℕ) :
    Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
  rw [Module.finrank_pi, Fintype.card_fin]

/-- The number of superspaces of `W'` in `𝔽₂ⁿ` having codimension exactly `i` equals the
Gaussian binomial `gb d i`, where `d = n - finrank W'` is the codimension of `W'`. -/
lemma card_superspace_codim_eq_gb (n : ℕ) (W' : Submodule (ZMod 2) (Fin n → ZMod 2))
    (i : ℕ) (hi : i ≤ n - Module.finrank (ZMod 2) W') :
    Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
      W' ≤ U ∧ Module.finrank (ZMod 2) U = n - i} =
      gb (n - Module.finrank (ZMod 2) W') i := by
  have hmle : Module.finrank (ZMod 2) W' ≤ n :=
    (Submodule.finrank_mono (R := ZMod 2) (s := W') (t := ⊤) le_top).trans
      (le_of_eq (by rw [finrank_top, finrank_pi_zmod2]))
  have hA : Module.finrank (ZMod 2) W' ≤ n - i := by omega
  rw [Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient
    (K := ZMod 2) (V := Fin n → ZMod 2) W' (ℓ := n - i) hA]
  have hsub : (n - i) - Module.finrank (ZMod 2) W'
      = (n - Module.finrank (ZMod 2) W') - i := by
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]
  rw [hsub, gb]
  have hfinQ : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ W')
      = n - Module.finrank (ZMod 2) W' := by
    have h := Submodule.finrank_quotient_add_finrank (R := ZMod 2) (M := Fin n → ZMod 2) W'
    rw [finrank_pi_zmod2 n] at h
    omega
  rw [Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
    (K := ZMod 2) (V := (Fin n → ZMod 2) ⧸ W')
    (V' := Fin (n - Module.finrank (ZMod 2) W') → ZMod 2)
    (ℓ := (n - Module.finrank (ZMod 2) W') - i)
    (by rw [hfinQ, finrank_pi_zmod2])]
  have hdual : Nat.card {T : Submodule (ZMod 2) (Fin (n - Module.finrank (ZMod 2) W') → ZMod 2) //
      Module.finrank (ZMod 2) T = (n - Module.finrank (ZMod 2) W') - i}
      = Nat.card {T : Submodule (ZMod 2) (Fin (n - Module.finrank (ZMod 2) W') → ZMod 2) //
      Module.finrank (ZMod 2) T = i} := by
    have h := (Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_compl (K := ZMod 2)
      (V := Fin (n - Module.finrank (ZMod 2) W') → ZMod 2) i
      (by rw [finrank_pi_zmod2]; exact hi)).symm
    rwa [finrank_pi_zmod2] at h
  exact hdual

theorem sum_Icc_card_superspace_codim_eq_indicator (n : ℕ) (a : ℕ → ℤ)
    (ha : ∀ t : ℕ, 1 ≤ t →
      ∑ i ∈ Finset.Icc 1 t, a i * (Commons.Combinatorics.QBinomial.gb t i : ℤ) = 1) :
    ∀ W' : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∑ i ∈ Finset.Icc 1 (n - Module.finrank (ZMod 2) W'),
        a i * (Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
          W' ≤ U ∧ Module.finrank (ZMod 2) U = n - i} : ℤ))
        = if W' = ⊤ then 0 else 1 := by
  intro W'
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [card_superspace_codim_eq_gb n W' i (Finset.mem_Icc.mp hi).2])]
  by_cases htop : W' = ⊤
  · rw [if_pos htop, htop, finrank_top, finrank_pi_zmod2]
    have hempty : Finset.Icc 1 (n - n) = ∅ := by
      rw [Nat.sub_self]
      exact Finset.Icc_eq_empty_of_lt (by omega)
    rw [hempty, Finset.sum_empty]
  · rw [if_neg htop]
    have hmle : Module.finrank (ZMod 2) W' ≤ n :=
      (Submodule.finrank_mono (R := ZMod 2) (s := W') (t := ⊤) le_top).trans
        (le_of_eq (by rw [finrank_top, finrank_pi_zmod2]))
    have hne : Module.finrank (ZMod 2) W' ≠ n := by
      intro h
      refine htop (Submodule.eq_top_of_finrank_eq ?_)
      rw [h, finrank_pi_zmod2]
    exact ha (n - Module.finrank (ZMod 2) W') (by omega)

end

end Commons.Combinatorics.QBinomial
