import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.schmidt_bound

/-!
# The rank-two ball-count bound `#(L ∩ B_X) ≤ K X² / λ₁(L)²`

For a rank-two sublattice `L ⊆ ℤ^ι` and a radius `X ≥ 1` at least as large as the first successive
minimum `λ₁(L)`, the number of lattice points of `L` of Euclidean norm at most `X` is at most
`K · X² / λ₁(L)²`, with a constant `K` depending only on the ambient type `ι`.

The proof applies Schmidt's bound `Work.HP.Sig2.schmidt_bound`
(`#(L ∩ B_T) ≤ K ∏_{i<rk L}(T/λ_{i+1}+1)`) at `T = X`: for `rk L = 2` the product is
`(X/λ₁+1)(X/λ₂+1)`, which expands to `X²/(λ₁λ₂) + X/λ₁ + X/λ₂ + 1` and is bounded by
`4 X²/λ₁²` using `λ₁ ≤ λ₂` and `λ₁ ≤ X`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

theorem ballCount_two_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (X : ℝ), Work.HP.rk L = 2 → 1 ≤ X →
      Work.HP.lam L 1 ≤ X → (Work.HP.ballCount L X : ℝ) ≤ K * X ^ 2 / Work.HP.lam L 1 ^ 2 := by
  obtain ⟨Kc, hKc, hKc'⟩ := Work.HP.Sig2.schmidt_bound (ι := ι)
  refine ⟨4 * Kc, by positivity, ?_⟩
  intro L X hrk hX hlX
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have h1 : 0 < Work.HP.lam L 1 := Work.HP.lam_pos L le_rfl (by omega)
  have hmono : Work.HP.lam L 1 ≤ Work.HP.lam L 2 := Work.HP.lam_mono L (by norm_num) (by omega)
  have hss := hKc' L X hX
  -- Schmidt's product for rank two is `(X/λ₁+1)(X/λ₂+1)`.
  have hprod : (∏ i ∈ Finset.range (Work.HP.rk L), (X / Work.HP.lam L (i + 1) + 1))
      = (X / Work.HP.lam L 1 + 1) * (X / Work.HP.lam L 2 + 1) := by
    rw [hrk, Finset.prod_range_succ, Finset.prod_range_succ]
    simp
  rw [hprod] at hss
  -- Each of the four terms is at most `X²/λ₁²`.
  have hD1 : 1 ≤ X / Work.HP.lam L 1 := (one_le_div h1).mpr hlX
  have hD2 : X / Work.HP.lam L 1 ≤ X ^ 2 / Work.HP.lam L 1 ^ 2 := by
    rw [div_le_div_iff₀ h1 (by positivity)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hX0 h1.le) (sub_nonpos.mpr hlX)]
  have hXb : X / Work.HP.lam L 2 ≤ X / Work.HP.lam L 1 :=
    div_le_div_of_nonneg_left hX0 h1 hmono
  have hA : X ^ 2 / (Work.HP.lam L 1 * Work.HP.lam L 2) ≤ X ^ 2 / Work.HP.lam L 1 ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg X) (by positivity) (by nlinarith [h1, hmono])
  have hexp : (X / Work.HP.lam L 1 + 1) * (X / Work.HP.lam L 2 + 1)
      = X ^ 2 / (Work.HP.lam L 1 * Work.HP.lam L 2) + X / Work.HP.lam L 1
        + X / Work.HP.lam L 2 + 1 := by
    field_simp; ring
  have hkey : (X / Work.HP.lam L 1 + 1) * (X / Work.HP.lam L 2 + 1)
      ≤ 4 * (X ^ 2 / Work.HP.lam L 1 ^ 2) := by
    rw [hexp]; linarith [hA, hD1, hD2, hXb]
  calc (Work.HP.ballCount L X : ℝ)
      ≤ Kc * ((X / Work.HP.lam L 1 + 1) * (X / Work.HP.lam L 2 + 1)) := hss
    _ ≤ Kc * (4 * (X ^ 2 / Work.HP.lam L 1 ^ 2)) := mul_le_mul_of_nonneg_left hkey hKc.le
    _ = 4 * Kc * X ^ 2 / Work.HP.lam L 1 ^ 2 := by field_simp

end Work.HP.FM3
