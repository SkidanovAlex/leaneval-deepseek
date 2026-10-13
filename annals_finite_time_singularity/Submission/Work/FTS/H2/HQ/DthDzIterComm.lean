import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2.HQ

/-! ## The commutation identity on the open strip

`Work.FTS.LocData.SmoothQuad f` is, by definition, smoothness of `Function.uncurry f` in the
*genuine* smooth order `Work.Stability.smoothOrder` on the open strip
`Work.Spaces.quadU = (-1,∞) × (0,π/2)`.  Both curvilinear derivatives are local, so the
induction of `Work.Spaces.Dth_DzIter_comm_eqOn` goes through verbatim with `nbhU` replaced by
`quadU`: at each step Clairaut (`Work.Spaces.Dz_Dth_comm`, which only asks for `C²` at the
point) moves the outer `D_z` past the `D_θ`, and the two `z`-slices are then compared by the
induction hypothesis through `Work.Spaces.pz_congr_of_isOpen`. -/

/-- **`D_θ` commutes with every iterate of `D_z` on the open strip `quadU = (-1,∞) × (0,π/2)`.**

For `g` of class `C^∞` (`Work.Stability.smoothOrder`) on `quadU` and every `b : ℕ`, the
functions `D_θ (D_z^b g)` and `D_z^b (D_θ g)` agree on `quadU`.  The induction hypothesis is
used through the congruence lemma `Work.Spaces.pz_congr_of_isOpen`, which is available because
`quadU` is open. -/
theorem Dth_DzIter_comm_quadU {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) Work.Spaces.quadU := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      -- `D_z^b g` is `C^∞` (hence `C²`) on the open strip, so Clairaut applies at `y`.
      have hG : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter b g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg b
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) y :=
        (hG.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hy)).of_le
          (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DzIter b g) hcd
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [← hcomm]
      -- The two `z`-slices agree on the open set `quadU` by the induction hypothesis,
      -- so their derivatives at `y` agree.
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]

/-- **`D_θ` commutes past every iterate of `D_z` in the interior class `SmoothQuad`.**

`Work.Spaces.Dth_DzIter_comm_eqOn` (proved) is the same statement for
`Work.Spaces.SmoothNbhd` functions (analyticity on a neighbourhood of the closed quadrant),
which is false for the cut-off `χ`, for `F_*` and for the stream functions.  Here `f` is
`SmoothQuad` (genuine `C^∞` on the open strip `(-1,∞) × (0,π/2)`) and the identity

  `D_θ (D_z^j f) = D_z^j (D_θ f) =: mixed j 1 f`

is claimed at the points `z ∈ Iz`, `0 < θ < π/2` of the domain.

Route: copy the proof of `Work.Spaces.Dth_DzIter_comm_eqOn` (`Submission/Work/Spaces/mixed_comm.lean`)
together with its ingredient `Work.Spaces.Dz_Dth_comm_eqOn`, replacing `nbhU` by
`Work.Spaces.quadU` and the class `SmoothNbhd` by `SmoothQuad`, and using
`Work.Spaces.Dz_Dth_comm` (Clairaut for the two curvilinear derivatives, `C²` at the point),
with `ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b f)) (z,θ)` obtained from
`Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf b` and
`Work.Spaces.isOpen_quadU.mem_nhds`, together with the congr lemmas
`Work.Spaces.pz_congr_of_isOpen`/`Work.Spaces.pth_congr_of_isOpen` (proved for an arbitrary
open set) in the induction step.  Note the definitional identities
`Work.Spaces.mixed j 1 f = Work.Spaces.DzIter j (Work.Spaces.Dth f)`.
`Submission/Work/FTS/H2/LinfQ.lean` contains a draft of this proof
(`DzDthIterCommOn_quad`, `DzIter_DthIter_comm_quad`, `Dth_mixed_quad`); note that that file
does not compile, so do not import it — write your own. -/
theorem DthDzIterComm (j : ℕ) (f : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.Dth (Work.Spaces.DzIter j f) z θ = Work.Spaces.mixed j 1 f z θ := by
  -- `SmoothQuad f` *is* the hypothesis of the open-strip lemma, since
  -- `Work.Spaces.quadU = (-1,∞) × (0,π/2)` is exactly the strip in `SmoothQuad`, and
  -- `Work.Spaces.Iz = [0,∞) ⊆ (-1,∞)`.
  intro z hz θ hθ
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    linarith
  have hy : (z, θ) ∈ Work.Spaces.quadU := ⟨hz', hθ⟩
  have h := Dth_DzIter_comm_quadU (g := f) hf j hy
  simpa [Function.uncurry, Work.Spaces.mixed, Work.Spaces.DthIter] using h

end Work.FTS.H2.HQ
