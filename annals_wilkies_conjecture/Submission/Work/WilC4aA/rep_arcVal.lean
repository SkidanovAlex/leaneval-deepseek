import Mathlib
import Submission.Work.WilC4aA.Defs

namespace Work.WilC4aA

/-- For a point `z` of a good piece `P`, the `y`-value it represents (`z 1`, resp. `z 1⁻¹` for an
inverted piece, i.e. `arcVal P γ s` when `z = γ s`) is indeed represented by `z`: `P.Rep z y`. -/
theorem rep_arcVal {P : WilkiesDesign.CG.C4a.LiftPiece} (hP : P.Good)
    {γ : ℝ → Fin (P.m + 2) → ℝ}
    (hγmem : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ s ∈ P.set) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), P.Rep (γ s) (Work.WilC4aA.arcVal P γ s) := by
  filter_upwards [hγmem] with s hs
  cases hb : P.inv
  · -- non-inverted piece: `Rep` is the identity condition
    simp only [WilkiesDesign.CG.C4a.LiftPiece.Rep, Work.WilC4aA.arcVal_apply, hb]
    rfl
  · -- inverted piece: the inverted coordinate does not vanish on the piece
    simp only [WilkiesDesign.CG.C4a.LiftPiece.Rep, Work.WilC4aA.arcVal_apply, hb, ite_true]
    exact mul_inv_cancel₀ (hP.2.2.2.2 hb (γ s) hs)

end Work.WilC4aA
