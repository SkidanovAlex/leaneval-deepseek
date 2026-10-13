/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_z^j D_θ^i (D_z ∂_θ V) = D_z^{j+1} D_θ^i (∂_θ V)` on the open quadrant

The curvilinear operators `D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f` commute at every point
where the function is `C²` (`Work.Spaces.Dz_Dth_comm`, Clairaut in the two slices), hence so do
`D_z` and each iterate `D_θ^i`.  Consequently the two mixed operators

* `mixed j i (D_z (∂_θ V))  =  D_z^j D_θ^i (D_z ∂_θ V)`, and
* `mixed (j+1) i (∂_θ V)    =  D_z^{j+1} D_θ^i (∂_θ V)`

agree at every point of the open quadrant `Q0` for a source `V` which is `C^∞` there (in the
genuine smooth order `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)`, *not* the analytic
order `⊤` used by the older `SmoothNbhd` class): this is `OpIdentMixed` below.

The proof has two ingredients, both isolated as lemmas of this file:

* `DzIter_congr_of_isOpen` — congruence of `D_z^j` on an open set (the operators are local, and
  only the slices of the two functions are compared);
* `Dz_DthIter_comm_of_isOpen` — the commutation `D_z (D_θ^i g) = D_θ^i (D_z g)` on an open set
  on which `g` is `C^∞` in the genuine smooth order.

The latter is the smooth-order counterpart of `Work.Spaces.DzDthIterCommOn`, whose hypothesis
`ContDiffOn ℝ ⊤` is analyticity and hence unavailable for the cut-off sources of the route; the
proof is the same induction, but the pointwise regularity of `D_θ^i g` (needed for Clairaut) is
supplied by `Work.FTS.LocData.contDiffOn_DthIter`, which is stated at the genuine smooth order.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-! ## Congruence of the iterated `D_z` on an open set -/

/-- The iterated operator `D_z^j` is local: two functions which agree on an open set `V` have
equal `D_z^j` at every point of `V`. -/
lemma DzIter_congr_of_isOpen {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      intro y hy
      have hp := Work.Spaces.pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g') y.1 y.2
      rw [hp]

/-! ## `D_z` commutes with the iterates of `D_θ`, at the genuine smooth order -/

/-- On an open set `V` on which `g` is `C^∞` in the genuine smooth order
`Work.Stability.smoothOrder`, the operator `D_z` commutes with every iterate of `D_θ`:
`D_z (D_θ^i g) = D_θ^i (D_z g)` on `V`.  (The smooth-order counterpart of
`Work.Spaces.DzDthIterCommOn`.) -/
lemma Dz_DthIter_comm_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      -- `D_θ^i g` is `C^∞`, hence `C²`, at the point `y`: Clairaut applies.
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (hV.mem_nhds hy)).of_le (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      -- The two functions now agree on the open set `V` by the induction hypothesis, so their
      -- `θ`-derivatives agree at `y`.
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-! ## The identity -/

theorem OpIdentMixed {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (i j : ℕ) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Spaces.pth V)) z θ
      = Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ := by
  -- `∂_θ V` is `C^∞` on the open quadrant `Q0`.
  have hgp : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth V)) Work.FTS.EllipticEst.Q0 := hV.pth
  -- `D_z` commutes with `D_θ^i`, so the two functions agree on `Q0`.
  have hcomm := Dz_DthIter_comm_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hgp i
  -- `D_z^j` is local, so it preserves that agreement at `(z,θ)`.
  have hkey := DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm.symm j
  change Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V))) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth V)) z θ
  rw [show Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth V))
      = Work.Spaces.DzIter j
          (Work.Spaces.Dz (Work.Spaces.DthIter i (Work.Spaces.pth V))) from
    Work.Spaces.DzIter_add_right j 1 _]
  exact hkey hz

end Work.FTS.EllipticEst.RPFresh
