import Mathlib
import Submission.Work.SSS.coherentLiftR

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

/-- **Gluing a matching family of pieces over a horn, tensored with a fixed simplicial set.**
Let `P j : F ⊗ Δ[n] ⟶ Y` (`j ≠ i`) be a family of morphisms which agree on the pairwise
intersections of the faces of the horn `Λ[n+1,i]` (the condition
`Work.SSS.HornTensorCompatible`), then there is a single morphism `F ⊗ Λ[n+1,i] ⟶ Y` restricting
to `P j` on the `j`-th face.

Proof: use the tensor-hom adjunction of the cartesian closed structure on `SSet`; the adjoints
`MonoidalClosed.curry (P j) : Δ[n] ⟶ F ⟶[SSet] Y` are compatible in the sense of
`SSet.horn.IsCompatible` (`MonoidalClosed.curry_natural_left` turns the compatibility of the
pieces into the compatibility of the adjoints; note `Work.SSS.HornTensorCompatible` is defined by
the same case distinction on `n` as `SSet.horn.IsCompatible`, with the vacuous case `n = 0`), so
`SSet.horn.IsCompatible.desc` glues them to a morphism `Λ[n+1,i] ⟶ F ⟶[SSet] Y`, and
`MonoidalClosed.uncurry` of that is the required map (its restrictions are computed with
`SSet.horn.IsCompatible.ι_desc`, `MonoidalClosed.uncurry_natural_left` and
`MonoidalClosed.uncurry_curry`). -/
theorem exists_hornGlue_tensor {F Y : SSet.{0}} {n : ℕ} {i : Fin (n + 2)}
    (P : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (F ⊗ Work.SSS.stdSimp n) ⟶ Y)
    (hP : Work.SSS.HornTensorCompatible P) :
    ∃ u : F ⊗ (SSet.horn (n + 1) i).toSSet ⟶ Y,
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), (F ◁ SSet.horn.ι i j hj) ≫ u = P j hj := by
  classical
  -- the adjoints of the pieces
  let Q : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Work.SSS.stdSimp n ⟶ (CategoryTheory.ihom F).obj Y :=
    fun j hj => MonoidalClosed.curry (P j hj)
  -- they are compatible in the sense of `SSet.horn.IsCompatible`
  have hQ : SSet.horn.IsCompatible Q := by
    obtain _ | m := n
    · -- `n = 0`: the horn `Λ[1,i]` has a single face, nothing to check
      simp
    · rw [SSet.horn.isCompatible_iff]
      intro j k hj hk hjk
      -- currying the compatibility of the pieces
      have h := hP j k hj hk hjk
      have h2 : MonoidalClosed.curry
            (F ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ P j hj)
          = MonoidalClosed.curry
            (F ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ P k hk) := by
        rw [h]
      rwa [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_left] at h2
  -- glue the adjoints and uncurry
  refine ⟨MonoidalClosed.uncurry hQ.desc, fun j hj => ?_⟩
  rw [← MonoidalClosed.uncurry_natural_left (A := F) (f := SSet.horn.ι i j hj) (g := hQ.desc)]
  rw [SSet.horn.IsCompatible.ι_desc]
  show MonoidalClosed.uncurry (Q j hj) = P j hj
  rw [show Q j hj = MonoidalClosed.curry (P j hj) from rfl, MonoidalClosed.uncurry_curry]

end Work.SSS
