import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract
import Submission.Commons.Combinatorics.Transference.dual_first

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Lemma 7.3, normalised form.**  Pairing a function `F` with its dual function
`𝒟F(x) = |G|^{-d} ∑_h ∏_{ω ≠ 0} F(x + ω·h)` gives `|G|` times the `2^d`-th power of the Gowers
`U^d` norm: `∑_x F x · 𝒟F(x) = |G| · ‖F‖_{U^d}^{2^d}`. -/
theorem dual_inner_unorm {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (F : ZMod p → ℝ) :
    ∑ x : ZMod p, F x * davg d F x
      = (Fintype.card (ZMod p) : ℝ) * (Unorm d F) ^ (2 ^ d) := by
  have hcard : ((Fintype.card (ZMod p) : ℝ)) ≠ 0 := by
    have hpos : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast (ne_of_gt hpos)
  have hNd : (Fintype.card (Fin d → ZMod p) : ℝ) = (Fintype.card (ZMod p) : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hL : ∑ x : ZMod p, F x * davg d F x
      = ((Fintype.card (ZMod p) : ℝ) ^ d)⁻¹ * cubeSum d F := by
    have h1 : ∀ x : ZMod p, F x * davg d F x
        = ((Fintype.card (ZMod p) : ℝ) ^ d)⁻¹ *
          (F x * (∑ h : Fin d → ZMod p, ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
            F (x + ∑ i, (if ω i then h i else 0)))) := by
      intro x
      rw [davg, hNd]
      ring
    rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum]
    congr 1
    rw [dual_first d F, cubeSum]
  have hR : (Fintype.card (ZMod p) : ℝ) * (Unorm d F) ^ (2 ^ d)
      = ((Fintype.card (ZMod p) : ℝ) ^ d)⁻¹ * cubeSum d F := by
    rw [Unorm_pow d hd F]
    field_simp
    ring
  rw [hL, hR]

end Commons.Combinatorics.Transference
