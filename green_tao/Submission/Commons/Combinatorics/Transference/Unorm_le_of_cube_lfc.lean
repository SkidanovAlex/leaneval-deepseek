import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.mua
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

namespace Commons.Combinatorics.Transference

theorem Unorm_le_of_cube_lfc {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ}
    {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A.Nonempty →
      |((Fintype.card (ZMod p) : ℝ) ^ (d + 1))⁻¹ *
        (∑ z : ZMod p, ∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (z + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε) :
    Unorm d (fun x => ν x - 1) ≤ 2 * ε ^ (((2 ^ d : ℕ) : ℝ)⁻¹) := by
  classical
  set g : ZMod p → ℝ := fun x => ν x - 1 with hg
  set M : ℝ := (Fintype.card (ZMod p) : ℝ) ^ (d + 1) with hM
  have hcardN : (Fintype.card (ZMod p × (Fin d → ZMod p)) : ℝ) = M := by
    rw [hM]
    have hnat : Fintype.card (ZMod p × (Fin d → ZMod p))
        = Fintype.card (ZMod p) ^ (d + 1) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_succ']
    exact_mod_cast hnat
  set f : (Fin d → Bool) → (ZMod p × (Fin d → ZMod p)) → ℝ :=
    fun ω x => ν (x.1 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * x.2 j) with hf
  have h : ∀ A : Finset (Fin d → Bool), A.Nonempty →
      |M⁻¹ * (∑ x : ZMod p × (Fin d → ZMod p), ∏ ω ∈ A, f ω x) - 1| ≤ ε := by
    intro A hA
    rw [Fintype.sum_prod_type]
    simp only [hf]
    rw [hM]
    exact hLFC A hA
  have hmua := mua_core (ι := Fin d → Bool) (X := ZMod p × (Fin d → ZMod p)) f M ε
    hcardN.symm h
  have hcard2 : Fintype.card (Fin d → Bool) = 2 ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [hcard2] at hmua
  have hcube : (∑ x : ZMod p × (Fin d → ZMod p),
      ∏ ω : Fin d → Bool, (f ω x - 1)) = cubeSum d g := by
    rw [Fintype.sum_prod_type]
    unfold cubeSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro hh _
    apply Finset.sum_congr rfl; intro z _
    apply Finset.prod_congr rfl; intro ω _
    simp only [hf, hg]
    have hshift : (∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * hh j)
        = ∑ i : Fin d, if ω i then hh i else 0 := by
      apply Finset.sum_congr rfl; intro j _
      cases hω : ω j <;> simp
    rw [hshift]
  have h2 : Unorm d g ^ (2 ^ d) ≤ (2 : ℝ) ^ (2 ^ d) * ε := by
    rw [Unorm_pow d hd g, ← hM]
    calc cubeSum d g / M
        = M⁻¹ * (∑ x : ZMod p × (Fin d → ZMod p),
            ∏ ω : Fin d → Bool, (f ω x - 1)) := by rw [hcube, div_eq_inv_mul]
      _ ≤ (2 : ℝ) ^ (2 ^ d) * ε := le_trans (le_abs_self _) hmua
  have hn : (2 ^ d : ℕ) ≠ 0 := pow_ne_zero d (by norm_num)
  have hA0 : 0 ≤ Unorm d g := Unorm_nonneg d hd g
  have hεr : 0 ≤ ε ^ (((2 ^ d : ℕ) : ℝ)⁻¹) := Real.rpow_nonneg hε _
  have hB0 : 0 ≤ 2 * ε ^ (((2 ^ d : ℕ) : ℝ)⁻¹) := by linarith
  have hBpow : (2 * ε ^ (((2 ^ d : ℕ) : ℝ)⁻¹)) ^ (2 ^ d)
      = (2 : ℝ) ^ (2 ^ d) * ε := by
    rw [mul_pow, Real.rpow_inv_natCast_pow hε hn]
  rw [← hBpow] at h2
  exact (pow_le_pow_iff_left₀ hA0 hB0 hn).mp h2

end Commons.Combinatorics.Transference
