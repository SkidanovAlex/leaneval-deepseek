import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin
import Submission.Work.FTS.CoercivityFix.Transfer.HkIntegrand_Dz_le_succ_Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

/-! ## Helper identities for the `D_z`-index shift

The identity `mixed p q (D_z X) = mixed (p+1) q X` splits into two independent pieces:

* the *commutation* `D_θ^q (D_z X) = D_z (D_θ^q X)` on the open quadrant, which is Clairaut's
  theorem at the finite order `q + 1 ≤ 3` (this is
  `Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin`, since `D_z = D_z^1`);
* the purely *definitional* identity `D_z^p (D_z f) = D_z^{p+1} f`
  (`Work.Spaces.DzIter_add_right` at `(p,1)`), together with the locality of the `D_z`-iterates
  on an open set (an induction on `p` whose step is `Work.Spaces.pz_congr_of_isOpen`). -/

/-- The iterates of `D_z` are local: two functions that agree on an open set `V` have the same
`D_z^p` at every point of `V`.  (Induction on `p`, the step being `pz_congr_of_isOpen`.) -/
private theorem DzIter_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) (p : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter p f))
      (Function.uncurry (Work.Spaces.DzIter p f')) V := by
  induction p with
  | zero => exact h
  | succ n ih =>
      intro y hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter n f) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter n f') y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

theorem mixed_Dz_shift {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {p q : ℕ} (hpq : p + q ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed p q (Work.Spaces.Dz X) z θ = Work.Spaces.mixed (p + 1) q X z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨hz, hθ0, hθ1⟩
  -- Clairaut at the finite order `q + 1 ≤ 3`: `D_θ^q` crosses the single `D_z`.
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter q (Work.Spaces.DzIter 1 X)))
      (Function.uncurry (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q X)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin Work.FTS.EllipticEst.isOpen_Q0 3 hX q 1
      (by omega)
  -- Transport this identity through the `p` outer `D_z`-iterates (locality on the open
  -- quadrant), then absorb `D_z^p ∘ D_z` into `D_z^{p+1}`.
  have hstep : Work.Spaces.DzIter p (Work.Spaces.DthIter q (Work.Spaces.DzIter 1 X)) z θ
      = Work.Spaces.DzIter p (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q X)) z θ :=
    DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm p hQ
  show Work.Spaces.DzIter p (Work.Spaces.DthIter q (Work.Spaces.DzIter 1 X)) z θ
      = Work.Spaces.DzIter (p + 1) (Work.Spaces.DthIter q X) z θ
  rw [hstep]
  exact congrFun (congrFun
    (Work.Spaces.DzIter_add_right p 1 (Work.Spaces.DthIter q X)).symm z) θ

end Work.FTS_RegExport.RXT.Sys.GdotAux
