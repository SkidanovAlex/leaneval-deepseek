import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.DzAmgm.Scratch
import Submission.Work.FTS.EllipticEst.DzAmgm.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STSigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.NormPiecesAux

/-- `D_z^i` commutes with `z²∂_z² = D_z² − D_z` **on the open quadrant**, i.e.
`D_z^i (z² ∂_z² Ψ) = z² ∂_z² (D_z^i Ψ)` there (`zsqPz2 g := z^2 * pzIter 2 g` is the
abbreviation `Work.FTS.EllipticEst.DzAmgm.zsqPz2`; the statement above writes it out).

Route.  Induction on `i`.  The base is `rfl`.  For the step use
`DzAmgm.zsqPz2_Dz : Set.EqOn (uncurry (zsqPz2 (Dz g))) (uncurry (Dz (zsqPz2 g))) Q0` with
`g := DzIter i Ψ` (`SmoothOpen (DzIter i Ψ)` from `hΨ.DzIter i`), so that on `Q0`
`z²∂_z²(DzIter (i+1) Ψ) = D_z (z²∂_z²(DzIter i Ψ))`; the induction hypothesis gives the pointwise
equality with `D_z (DzIter i (z²∂_z² Ψ))` on `Q0`, and the two are identified by
`Work.FTS.H2.Dz_congr_of_isOpen` (`Set.EqOn`-congruence of `D_z` on an open set, which is
`Work.Spaces.pz_congr_of_isOpen`).  Everything is definitional after unfolding
`DzIter_succ`. -/
theorem zsqPz2_DzIter_eqOn (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter i Ψ) z θ := by
  intro z θ hz hθ hπ
  -- The goal is the symmetric form of the commuting identity `Qop_DzIter_eq` for
  -- `Qop = z²∂_z²` — which is the definitional unfolding of `zsqPz2` — read off at the
  -- point `(z,θ)` of the open quadrant `Q0 = (0,∞) × (0,π/2)`.
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
  have h := Work.FTS.EllipticEst.DzAmgm.Qop_DzIter_eq (g := Ψ) hΨ i hp
  exact h.symm

end Work.FTS.ClassC.NormPiecesAux
