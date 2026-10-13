import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Q.WtoH_Radial_Q
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.WtoH_OpenAux
import Submission.Work.Elliptic.radial_arith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

-- NOTE (porting trap).  The statement below is written with the notation `π`, and the `Real`
-- scope must be open for it to mean `Real.pi`: without the `open scoped Real` line the
-- identifier `π` is *not* the constant `Real.pi` — under `autoImplicit = false` (the setting of
-- this lakefile) it is an unknown identifier, and under the default options it would be
-- auto-bound as a free variable, either way not the intended `θ ∈ (0, π/2)`.  Every sibling file
-- opens the scope; the same line is added here.  The statement itself is unchanged.
open scoped Real

namespace Work.FTS.NonlinRows

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/- Port of `Work.FTS.H2.Q.WtoH_Radial_Q` from the class `SmoothQuad` (C^∞ through z = 0) to the
*open*-quadrant class `Work.FTS.EllipticEst.SmoothOpen` (C^∞ on (0,∞) × (0,π/2) only), which is
the class in which the primed interfaces `N4Norm'`/`StarPkgo` are stated.  Needed by the primed
rows 10, 11, 15, 19 (`Submission/Work/FTS/NonlinRows/`), whose pieces have the shape
`2 ℛ(Φ̃_*)·F_*`: with `f := ℛ(Φ̃_*)·z/(1+z)²` one has `(z+1)³/z²·f = ((z+1)/z)·ℛ(Φ̃_*)` — the
weighted coefficient carried by `StarPkg.R` / to be restored in `StarPkgo`. -/
theorem WtoH_Radial_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ|
        ≤ 200000 * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  -- This is the proof of `Work.FTS.H2.Q.WtoH_Radial_Q`, with its two class-dependent inputs
  -- replaced by the open-quadrant counterparts of `WtoH_OpenAux.lean`
  -- (`contDiffAt_divZ2_zslice_O`, `pzIter_divZ2_expansion_aux_O`).  The class-agnostic pieces
  -- (`tri_bound_sm`, `radial_arith`, `g_divZ2_eq`, `WlInf_z_bound`) are reused unchanged: the
  -- conclusion is a pointwise bound at `θ ∈ (0,π/2)`, where the `C^∞`-on-the-open-quadrant
  -- hypothesis provides all the smoothness that the argument uses.
  intro m hm z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  let G : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ
  have hmemG : Work.Spaces.WlInfMem α 4 G := hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 G := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 G hmemG)
      (Work.Spaces.wlThSum_nonneg α 4 G hmemG)
  have hG : G = fun z θ => (z + 1) ^ 3 * Work.Elliptic.divZ2 f z θ :=
    Work.Elliptic.g_divZ2_eq f
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice_O hsm hθ z hz
  have htri : ∀ j ≤ m,
      |(1 + z) ^ (j + 3) * Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ|
        ≤ 6000 * Work.Spaces.WlInf α 4 G := by
    have h := Work.FTS.H2.Q.tri_bound_sm (G := G) (κ := Work.Elliptic.divZ2 f) hG hm hz hκ
      (fun j hj => Work.Spaces.WlInf_z_bound α 4 G hmemG j (by omega) z θ (le_of_lt hz) hθI)
    intro j hj
    have h' := h j hj
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact h'
  have hA := pzIter_divZ2_expansion_aux_O hsm hm hz hθ
  rw [hA]
  exact Work.Elliptic.radial_arith (Λ := Work.Spaces.WlInf α 4 G) hm hz hΛ
    (fun j => Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ) htri

end Work.FTS.NonlinRows
