import Mathlib
import Submission.Work.SSS.coherentLiftR
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.sSingP_fibreIncl_comp

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

/-- **The level `0` data of the right-handed coherent lift family.**  For a continuous map `p` and
a vertex `σ : Δ[0] ⟶ Sing B`, the morphism
`fst : sSing (p⁻¹b') ⊗ Δ[0] ⟶ sSing (p⁻¹b')` followed by `Sing (fibreIncl p b')` is a lift of
`snd ≫ σ` along `Sing p` (because `σ` is the constant simplex at its `0`-th vertex
`Work.SSS.sigmaVert σ`, `Work.SSS.sigma_eq_const`, and the fibre inclusion is mapped to that same
vertex, `Work.SSS.sSingP_fibreIncl_comp`) and restricts to the fibre inclusion on the `v₀`-slice
(`Work.SSS.vertInclR_fst`).  Recall that `Work.SSS.RLevel p n` only requires these properties for
the *based* pairs `(b', σ)`, i.e. when `sigmaVert σ = b'`. -/
theorem exists_rlevel_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Nonempty (Work.SSS.RLevel p 0) := by
  -- The level `0` piece over `(b', σ)` is `fst ≫ Sing (fibreIncl p b')`: it forgets the vertex
  -- coordinate of `sSing (p⁻¹b') ⊗ Δ[0]` and includes the fibre over `b'`.  This is independent
  -- of `σ`, which is why no case distinction on `sigmaVert σ = b'` is needed for the data.
  refine ⟨{ Φ := ?_, lift := ?_, vert := ?_ }⟩
  · intro b' σ
    exact SemiCartesianMonoidalCategory.fst (sSing (Work.StemsB.fibre p b')) (stdSimp 0) ≫
      sSingP (Work.StemsB.fibreIncl p b')
  · -- `fst ≫ Sing (fibreIncl p b') ≫ Sing p = fst ≫ const b' = const b'`, while for a based pair
    -- `σ` is the constant vertex at `b'`, so `snd ≫ σ = snd ≫ const b' = const b'`.
    intro b' σ h
    rw [Category.assoc, sSingP_fibreIncl_comp p b', SSet.comp_const, sigma_eq_const σ, h,
      SSet.comp_const]
  · intro b' σ _
    rw [← Category.assoc, vertInclR_fst, Category.id_comp]

end Work.SSS
