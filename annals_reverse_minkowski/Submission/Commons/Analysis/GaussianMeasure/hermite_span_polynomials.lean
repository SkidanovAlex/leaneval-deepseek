import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Hermite.Basic

namespace Commons.Analysis.GaussianMeasure

open Polynomial

noncomputable section

/-- The sequence of probabilists' Hermite polynomials over `ℝ` (the image of the
integer `Polynomial.hermite` under the canonical map `ℤ → ℝ`). -/
private def hermiteSeq : Polynomial.Sequence ℝ where
  elems' := fun k => (Polynomial.hermite k).map (Int.castRingHom ℝ)
  degree_eq' := fun k => by
    rw [Polynomial.degree_map_eq_of_injective (Int.cast_injective (α := ℝ)),
        Polynomial.degree_hermite]

/-- The sequence of monomials `X ^ k` over `ℝ`. -/
private def monomialSeq : Polynomial.Sequence ℝ where
  elems' := fun k => (Polynomial.X : Polynomial ℝ) ^ k
  degree_eq' := fun k => Polynomial.degree_X_pow k

/-- `Fin (n+1)` is the same as `{0, …, n}` when read through the coercion to `ℕ`. -/
private lemma fin_range_val_coe (n : ℕ) :
    Set.range (fun k : Fin (n + 1) => (k : ℕ)) = Set.Iic n := by
  ext j
  simp only [Set.mem_range, Set.mem_Iic]
  constructor
  · rintro ⟨k, rfl⟩
    exact Nat.lt_succ_iff.mp k.isLt
  · intro hj
    exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩

/-- The range of a sequence indexed by `Fin (n+1)` is the image of `Set.Iic n`. -/
private lemma seq_image_Iic_eq_range (S : Polynomial.Sequence ℝ) (n : ℕ) :
    ((S : ℕ → Polynomial ℝ) '' Set.Iic n)
      = Set.range (fun k : Fin (n + 1) => (S : ℕ → Polynomial ℝ) (k : ℕ)) := by
  rw [← fin_range_val_coe n, ← Set.range_comp]
  rfl

private lemma hermiteSeq_image (n : ℕ) :
    Set.range (fun k : Fin (n + 1) =>
        (Polynomial.hermite (k : ℕ)).map (Int.castRingHom ℝ))
      = ((hermiteSeq : Polynomial.Sequence ℝ) : ℕ → Polynomial ℝ) '' Set.Iic n := by
  rw [seq_image_Iic_eq_range]
  rfl

private lemma monomialSeq_image (n : ℕ) :
    Set.range (fun k : Fin (n + 1) => (Polynomial.X : Polynomial ℝ) ^ (k : ℕ))
      = ((monomialSeq : Polynomial.Sequence ℝ) : ℕ → Polynomial ℝ) '' Set.Iic n := by
  rw [seq_image_Iic_eq_range]
  rfl

theorem hermite_span_polynomials (n : ℕ) :
    Submodule.span ℝ (Set.range (fun k : Fin (n + 1) =>
        (Polynomial.hermite (k : ℕ)).map (Int.castRingHom ℝ)))
      = Submodule.span ℝ (Set.range (fun k : Fin (n + 1) =>
        (Polynomial.X : Polynomial ℝ) ^ (k : ℕ))) := by
  have hh : Submodule.span ℝ (Set.range (fun k : Fin (n + 1) =>
        (Polynomial.hermite (k : ℕ)).map (Int.castRingHom ℝ))) = Polynomial.degreeLE ℝ n := by
    rw [hermiteSeq_image n]
    exact Polynomial.Sequence.span_degreeLE hermiteSeq (fun i _ => by
      rw [isUnit_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr (hermiteSeq.ne_zero i))
  have hm : Submodule.span ℝ (Set.range (fun k : Fin (n + 1) =>
        (Polynomial.X : Polynomial ℝ) ^ (k : ℕ))) = Polynomial.degreeLE ℝ n := by
    rw [monomialSeq_image n]
    exact Polynomial.Sequence.span_degreeLE monomialSeq (fun i _ => by
      rw [isUnit_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr (monomialSeq.ne_zero i))
  rw [hh, hm]

end

end Commons.Analysis.GaussianMeasure