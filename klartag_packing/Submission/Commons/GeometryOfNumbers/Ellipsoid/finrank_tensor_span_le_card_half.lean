import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.GeometryOfNumbers.Ellipsoid

theorem finrank_tensor_span_le_card_half {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hne : ∀ x ∈ S, x ≠ 0) (hneg : ∀ x ∈ S, -x ∈ S) :
    2 * Module.finrank ℝ (Submodule.span ℝ
        ((fun x : EuclideanSpace ℝ (Fin d) => Matrix.vecMulVec x x) '' (S : Set _))) ≤ S.card := by
  classical
  set f : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ :=
    fun x => Matrix.vecMulVec x x with hf
  -- invariance of the rank-one tensor under negation
  have hf_neg : ∀ x : EuclideanSpace ℝ (Fin d), f (-x) = f x := by
    intro x
    rw [hf]
    ext i j
    simp [Matrix.vecMulVec]
  -- Step 1: finrank of the span is at most the number of distinct tensors
  have hfin : Module.finrank ℝ (Submodule.span ℝ (f '' (S : Set _))) ≤ (S.image f).card := by
    rw [← Finset.coe_image]
    exact finrank_span_finset_le_card _
  -- Step 2: each tensor arises from at least two elements of S (x and -x)
  have hcard : 2 * (S.image f).card ≤ S.card := by
    have hsum := Finset.card_eq_sum_card_image f S
    -- (hsum : S.card = ∑ y ∈ S.image f, #{a ∈ S | f a = y})
    have hfib : ∀ y ∈ S.image f, 2 ≤ (S.filter (fun x => f x = y)).card := by
      intro y hy
      obtain ⟨x₀, hx₀S, hfx₀⟩ := Finset.mem_image.mp hy
      have hx₀ne : x₀ ≠ 0 := hne x₀ hx₀S
      have hnegn : -x₀ ∈ S := hneg x₀ hx₀S
      have hfx₀' : f (-x₀) = y := by rw [hf_neg x₀, hfx₀]
      have hdist : x₀ ≠ -x₀ := by
        intro h
        have h0' : x₀ + x₀ = 0 := eq_neg_iff_add_eq_zero.mp h
        have h0 : (2 : ℝ) • x₀ = 0 := by rw [two_smul, h0']
        rcases smul_eq_zero.mp h0 with h2 | hx
        · norm_num at h2
        · exact hx₀ne hx
      have hmx : x₀ ∈ S.filter (fun x => f x = y) := Finset.mem_filter.mpr ⟨hx₀S, hfx₀⟩
      have hmy : -x₀ ∈ S.filter (fun x => f x = y) := Finset.mem_filter.mpr ⟨hnegn, hfx₀'⟩
      have : 1 < (S.filter (fun x => f x = y)).card := by
        rw [Finset.one_lt_card]
        exact ⟨x₀, hmx, -x₀, hmy, hdist⟩
      omega
    calc 2 * (S.image f).card = (S.image f).card * 2 := by rw [Nat.mul_comm]
      _ = ∑ y ∈ S.image f, (2 : ℕ) := (Finset.sum_const_nat (fun y _ => rfl)).symm
      _ ≤ ∑ y ∈ S.image f, (S.filter (fun x => f x = y)).card := Finset.sum_le_sum hfib
      _ = S.card := hsum.symm
  calc 2 * Module.finrank ℝ (Submodule.span ℝ (f '' (S : Set _)))
      ≤ 2 * (S.image f).card := Nat.mul_le_mul_left 2 hfin
    _ ≤ S.card := hcard

end Commons.GeometryOfNumbers.Ellipsoid