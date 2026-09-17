import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.TotallySplit

namespace Commons.Lattice.Counting

open Matrix

/-- The number of `m × d` matrices over `ZMod q` is `q ^ (m * d)`. -/
lemma card_matrix_zmod (q m d : ℕ) [Fact q.Prime] :
    Nat.card (Matrix (Fin m) (Fin d) (ZMod q)) = q ^ (m * d) := by
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod q) (V := Matrix (Fin m) (Fin d) (ZMod q)),
    ZMod.card q,
    Module.finrank_matrix (ZMod q) (ZMod q) (Fin m) (Fin d)]
  simp [Module.finrank_self]

theorem card_matrix_mulVec_eq_zero {q m d : ℕ} [Fact q.Prime] (x : Fin d → ZMod q) :
    Nat.card {A : Matrix (Fin m) (Fin d) (ZMod q) // A.mulVec x = 0}
      = if x = 0 then q ^ (m * d) else q ^ (m * d - m) := by
  by_cases hx : x = 0
  · rw [if_pos hx]
    have hall : ∀ A : Matrix (Fin m) (Fin d) (ZMod q), A.mulVec x = 0 := by
      intro A; rw [hx, Matrix.mulVec_zero]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), card_matrix_zmod]
  · rw [if_neg hx]
    let φ : Matrix (Fin m) (Fin d) (ZMod q) →ₗ[ZMod q] (Fin m → ZMod q) :=
      LinearMap.flip (Matrix.mulVecBilin (ZMod q) (ZMod q)) x
    have hφ : ∀ A, φ A = A.mulVec x := by
      intro A
      simp only [φ]
      rw [LinearMap.flip_apply, Matrix.mulVecBilin_apply]
    haveI : Fintype (LinearMap.ker φ) := Fintype.ofFinite _
    have hcard : Nat.card {A : Matrix (Fin m) (Fin d) (ZMod q) // A.mulVec x = 0}
        = Fintype.card (LinearMap.ker φ) := by
      rw [Nat.card_eq_fintype_card]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun A => by
        show (A.mulVec x = 0) ↔ (A ∈ LinearMap.ker φ)
        rw [LinearMap.mem_ker, hφ A])
    rw [hcard,
      Module.card_eq_pow_finrank (K := ZMod q) (V := LinearMap.ker φ),
      ZMod.card q]
    have hsurj : Function.Surjective φ := by
      intro y
      obtain ⟨i0, hi0⟩ : ∃ i : Fin d, x i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (funext h)
      refine ⟨Matrix.of (fun i j => if j = i0 then y i * (x i0)⁻¹ else 0), ?_⟩
      rw [hφ]
      ext i
      rw [Matrix.mulVec_apply_eq_sum]
      show (∑ j : Fin d, (if j = i0 then y i * (x i0)⁻¹ else 0) * x j) = y i
      rw [Finset.sum_eq_single i0]
      · rw [if_pos rfl, mul_assoc, inv_mul_cancel₀ hi0, mul_one]
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i0) h
    have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hV : Module.finrank (ZMod q) (Matrix (Fin m) (Fin d) (ZMod q)) = m * d := by
      rw [Module.finrank_matrix (ZMod q) (ZMod q) (Fin m) (Fin d)]
      simp [Module.finrank_self]
    have hrange_fin : Module.finrank (ZMod q) (LinearMap.range φ) = m := by
      rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange_fin, hV] at hrn
    have hfin : Module.finrank (ZMod q) (LinearMap.ker φ) = m * d - m := by omega
    rw [hfin]

end Commons.Lattice.Counting