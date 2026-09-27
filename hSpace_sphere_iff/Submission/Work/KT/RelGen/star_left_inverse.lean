import Mathlib
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.recipB_eq_graphB_mul

/-!
# `Work.KT.RelGen.star_left_inverse`

For a unit `u` of the matrix ring `M_N(C(X × S¹, ℂ))`, the "left inverse" of the graph column
`B = graphB u` built from `u` agrees with the one built from the reciprocal graph column
`recipB u⁻¹`.

Writing `M` for `u` and `Mi` for `u⁻¹` (so that `M * Mi = Mi * M = 1`) and
`B = [[1],[M]]`, the reciprocal column is `Cc = recipB Mi = [[Mi],[1]] = B * Mi`.  Hence

`Ccᴴ Cc = (B Mi)ᴴ (B Mi) = Miᴴ (Bᴴ B) Mi`,

and since `Mi` and `Miᴴ` are units the totalized inverse splits:

`Ring.inverse (Ccᴴ Cc) = Ring.inverse Mi * Ring.inverse (Bᴴ B) * Ring.inverse (Miᴴ)`.

Multiplying on the right by `Ccᴴ = Miᴴ Bᴴ`, the factor `Ring.inverse (Miᴴ) * Miᴴ = 1` cancels and
we are left with `Ring.inverse Mi * Ring.inverse (Bᴴ B) * Bᴴ`; finally `Ring.inverse Mi = M`
because `Mi * M = 1`.
-/

namespace Work.KT.RelGen

open Matrix

theorem star_left_inverse (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (N : ℕ) (u : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ) :
    (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) *
        Ring.inverse ((Work.KT.Fund.graphB C(X × Sph ℂ, ℂ)
              (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))).conjTranspose *
          Work.KT.Fund.graphB C(X × Sph ℂ, ℂ)
            (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))) *
        (Work.KT.Fund.graphB C(X × Sph ℂ, ℂ)
          (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))).conjTranspose
      = Ring.inverse ((Work.KT.Fund.recipB C(X × Sph ℂ, ℂ)
            (↑u⁻¹ : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))).conjTranspose *
          Work.KT.Fund.recipB C(X × Sph ℂ, ℂ)
            (↑u⁻¹ : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))) *
        (Work.KT.Fund.recipB C(X × Sph ℂ, ℂ)
          (↑u⁻¹ : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))).conjTranspose := by
  -- Abbreviate the two matrix factors.
  set M : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ) := ↑u with hM
  set Mi : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ) :=
    (↑u⁻¹ : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) with hMi
  set B : Matrix (Fin N ⊕ Fin N) (Fin N) C(X × Sph ℂ, ℂ) :=
    Work.KT.Fund.graphB C(X × Sph ℂ, ℂ) M with hB
  set Cc : Matrix (Fin N ⊕ Fin N) (Fin N) C(X × Sph ℂ, ℂ) :=
    Work.KT.Fund.recipB C(X × Sph ℂ, ℂ) Mi with hCc
  -- `M` and `Mi` are mutually inverse.
  have hMN : M * Mi = 1 := by rw [hM, hMi]; exact Units.mul_inv u
  have hNM : Mi * M = 1 := by rw [hMi, hM]; exact Units.inv_mul u
  -- `Mi` and its conjugate transpose are units.
  have hMiunit : IsUnit Mi := ⟨u⁻¹, hMi.symm⟩
  have hMitunit : IsUnit Mi.conjTranspose := (Matrix.isUnit_conjTranspose Mi).2 hMiunit
  -- `Ring.inverse Mi = M`.
  have hMi_inv : Ring.inverse Mi = M := by
    let w : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ := Units.mk Mi M hNM hMN
    have hw : (w : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) = Mi := rfl
    calc Ring.inverse Mi = Ring.inverse (w : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) := by
          rw [hw]
      _ = ((w⁻¹ : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ) :
            Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) := Ring.inverse_unit w
      _ = M := rfl
  -- The reciprocal column is the graph column right-multiplied by `Mi`.
  have hCc_eq : Cc = B * Mi := by
    rw [hCc, hB]
    exact Work.KT.Fund.recipB_eq_graphB_mul _ Mi M hMN
  -- Splitting the totalized inverse of the Gram matrix.
  have h1 : Ring.inverse ((B * Mi).conjTranspose * (B * Mi))
      = (Ring.inverse Mi * Ring.inverse (B.conjTranspose * B)) *
          Ring.inverse (Mi.conjTranspose) := by
    rw [Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc (Mi.conjTranspose) B.conjTranspose (B * Mi),
      ← Matrix.mul_assoc B.conjTranspose B Mi]
    rw [Ring.inverse_mul (Or.inl hMitunit), Ring.inverse_mul (Or.inr hMiunit)]
  -- Cancel the unit factor `Ring.inverse (Miᴴ)` against `Miᴴ`.
  rw [hCc_eq, h1, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Ring.inverse (Mi.conjTranspose)) (Mi.conjTranspose) B.conjTranspose,
    Ring.inverse_mul_cancel (Mi.conjTranspose) hMitunit, Matrix.one_mul]
  rw [hMi_inv]

end Work.KT.RelGen
