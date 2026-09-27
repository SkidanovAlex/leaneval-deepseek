import Mathlib
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self

/-!
# `graphProj` and `recipProj` are continuous in the matrix argument

For a compact space `Y` and a natural number `n`, the maps
`M ↦ graphProj C(Y, ℂ) M` and `M ↦ recipProj C(Y, ℂ) M` from `n × n` matrices over `C(Y, ℂ)`
are continuous.

Both are instances of a single mechanism: `orthProj R B = B (Bᴴ B)⁻¹ Bᴴ` is a composition of
the continuous operations `B ↦ Bᴴ`, matrix multiplication, and the totalized inverse
`Ring.inverse`, the last applied only at points where `Bᴴ B` is a unit.  Continuity of the
inverse on the unit group is the classical fact that `Ring.inverse` is continuous at units of a
normed ring (`NormedRing.inverse_continuousAt`), transported to matrices through
`Matrix.nonsing_inv_eq_ringInverse` and `continuousAt_matrix_inv` (continuity of the matrix
inverse at a point whose determinant is invertible).  The Gram matrices here are

* `(graphB M)ᴴ (graphB M) = 1 + Mᴴ M`,
* `(recipB M)ᴴ (recipB M) = 1 + Mᴴ M`,

which are positive definite, hence units, by
`Work.KT.Fund.graphB_recipB_conjTranspose_mul_self` and
`Work.KT.Fund.isUnit_one_add_conjTranspose_mul`; compactness of `Y` is used only through the
`NormedRing` structure on `C(Y, ℂ)`.
-/

namespace Work.KT.Fund

open Matrix

/-- `graphB` is continuous in the matrix argument. -/
private lemma continuous_graphB (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Continuous (fun M : Matrix (Fin n) (Fin n) C(Y, ℂ) => graphB C(Y, ℂ) M) := by
  apply continuous_matrix
  intro i j
  cases i with
  | inl a => exact continuous_const
  | inr a => exact continuous_apply_apply a j

/-- `recipB` is continuous in the matrix argument. -/
private lemma continuous_recipB (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Continuous (fun M : Matrix (Fin n) (Fin n) C(Y, ℂ) => recipB C(Y, ℂ) M) := by
  apply continuous_matrix
  intro i j
  cases i with
  | inl a => exact continuous_apply_apply a j
  | inr a => exact continuous_const

/-- The orthogonal projection `B (Bᴴ B)⁻¹ Bᴴ` depends continuously on `B`, provided every Gram
matrix `Bᴴ B` is invertible.  This is the single mechanism behind the continuity of `graphProj`
and `recipProj`. -/
lemma continuous_orthProj {Y : Type} [TopologicalSpace Y] [CompactSpace Y]
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (B : X → Matrix (Fin n ⊕ Fin n) (Fin n) C(Y, ℂ))
    (hB : Continuous B) (hUnit : ∀ x, IsUnit ((B x)ᴴ * B x)) :
    Continuous (fun x => orthProj C(Y, ℂ) (B x)) := by
  have hgram : Continuous (fun x => (B x)ᴴ * B x) := hB.matrix_conjTranspose.matrix_mul hB
  have hinv : Continuous (fun x => Ring.inverse ((B x)ᴴ * B x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hunit : IsUnit ((B x)ᴴ * B x) := hUnit x
    have hdet : IsUnit (((B x)ᴴ * B x).det) := (Matrix.isUnit_iff_isUnit_det _).mp hunit
    have hdet' : ContinuousAt Ring.inverse (((B x)ᴴ * B x).det) := by
      have h := NormedRing.inverse_continuousAt hdet.unit
      rwa [IsUnit.unit_spec hdet] at h
    have hcont : ContinuousAt (fun z : Matrix (Fin n) (Fin n) C(Y, ℂ) => Ring.inverse z)
        ((B x)ᴴ * B x) := by
      have h : ContinuousAt (fun z : Matrix (Fin n) (Fin n) C(Y, ℂ) => z⁻¹)
          ((B x)ᴴ * B x) := continuousAt_matrix_inv _ hdet'
      rwa [show (fun z : Matrix (Fin n) (Fin n) C(Y, ℂ) => z⁻¹)
            = (fun z => Ring.inverse z) from
          funext fun z => Matrix.nonsing_inv_eq_ringInverse z] at h
    exact ContinuousAt.comp (f := fun x => (B x)ᴴ * B x) hcont hgram.continuousAt
  unfold orthProj
  exact (hB.matrix_mul hinv).matrix_mul hB.matrix_conjTranspose

theorem continuous_graphProj_recipProj (Y : Type) [TopologicalSpace Y] [CompactSpace Y]
    (n : ℕ) :
    Continuous (fun M : Matrix (Fin n) (Fin n) C(Y, ℂ) => graphProj C(Y, ℂ) M) ∧
    Continuous (fun M : Matrix (Fin n) (Fin n) C(Y, ℂ) => recipProj C(Y, ℂ) M) := by
  constructor
  · have hB : Continuous (fun M : Matrix (Fin n) (Fin n) C(Y, ℂ) => graphB C(Y, ℂ) M) :=
      continuous_graphB Y n
    have hunit : ∀ M : Matrix (Fin n) (Fin n) C(Y, ℂ),
        IsUnit ((graphB C(Y, ℂ) M)ᴴ * graphB C(Y, ℂ) M) := by
      intro M
      rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) M M).1]
      exact isUnit_one_add_conjTranspose_mul M
    simpa only [graphProj] using continuous_orthProj (Y := Y) (fun M => graphB C(Y, ℂ) M) hB hunit
  · have hB : Continuous (fun M : Matrix (Fin n) (Fin n) C(Y, ℂ) => recipB C(Y, ℂ) M) :=
      continuous_recipB Y n
    have hunit : ∀ M : Matrix (Fin n) (Fin n) C(Y, ℂ),
        IsUnit ((recipB C(Y, ℂ) M)ᴴ * recipB C(Y, ℂ) M) := by
      intro M
      rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) M M).2]
      exact isUnit_one_add_conjTranspose_mul M
    simpa only [recipProj] using continuous_orthProj (Y := Y) (fun M => recipB C(Y, ℂ) M) hB hunit

end Work.KT.Fund
