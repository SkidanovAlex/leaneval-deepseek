import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

set_option autoImplicit false

/-- The differential operator `D_z g = z · ∂_z g` maps functions smooth on an open set
`V` to functions smooth on `V`.  Indeed, after currying,
`Function.uncurry (Dz g) p = p.1 * Function.uncurry (pz g) p` is the product of the
smooth projection `p ↦ p.1` with the curried `z`-partial, which is smooth by
`contDiffOn_uncurry_pz`. -/
theorem contDiffOn_uncurry_Dz {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry g) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Dz g)) V := by
  have hpz : ContDiffOn ℝ ⊤ (Function.uncurry (pz g)) V := contDiffOn_uncurry_pz hV h
  have hz : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
  have hmul : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * Function.uncurry (pz g) p) V :=
    hz.mul hpz
  refine hmul.congr ?_
  intro p hp
  rfl

/-- Iterating `D_z` preserves smoothness on an open set: the map
`(z,θ) ↦ D_z^j f (z,θ)` is `C^∞` on `V` whenever `f` is. -/
theorem DzIterSmoothOn {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (j : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j f)) V := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      have hstep : ContDiffOn ℝ ⊤ (Function.uncurry (Dz (DzIter j f))) V :=
        contDiffOn_uncurry_Dz hV ih
      simpa using hstep

end Work.Spaces
