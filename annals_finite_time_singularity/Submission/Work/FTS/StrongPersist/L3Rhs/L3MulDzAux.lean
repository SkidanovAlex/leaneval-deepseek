/-
# `L3MulDzAux` — the `D_z`-commutation identities for the product rule `h · D_z f`

The target `Work.FTS.StrongPersist.L3Rhs.L3MulDz` bounds the `ℋ³`-norm of the product
`h · D_z f` (with `D_z = z ∂_z`) by `C/(γ-1)·|h|²_{𝒲^{4,∞}}·|f|²_{ℋ⁴}`.  The product is
estimated through the Leibniz rule for `D_z`, `D_θ` in the open quadrant
(`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, `…leibniz_open_mixed`), applied to the two
factors `h` and `D_z f`; every derivative that lands on the second factor must then be
recognised as (a slot of) a derivative of `f`.

That recognition is the content of this module.  Because `D_z = z ∂_z` and `D_θ = sin(2θ)∂_θ`
only involve the derivative in their own variable, they *commute* (Clairaut), and hence

  `D_z^m (D_θ^i (D_z f)) = D_z^{m+1} (D_θ^i f)`  (`mixed m i (D_z f) = mixed (m+1) i f`),

at every point of the open quadrant, for `f` of class `Work.FTS.EllipticEst.SmoothOpen`
(`C^∞` on `Q0 = (0,∞) × (0,π/2)` in the genuine order `Work.Stability.smoothOrder`).
The sibling `Work.Spaces.DzDthIterCommOn` states the same commutation for the *analytic* order
`⊤` (`= ω`, which `SmoothOpen` does not provide), and
`Work.FTS.StrongLWP.Sobolev.Dz_DthIter_comm_quadU` for the genuinely smooth order on the
larger rectangle `quadU = (-1,∞) × (0,π/2)`; both are private or off-`Q0`, so the short
induction is redone here on `Q0` in the honest order.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.Spaces (Dz Dth DthIter DzIter mixed pz pth pzIter pthIter)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Multiplication of the open-quadrant smooth class -/

/-- `Work.FTS.EllipticEst.SmoothOpen` is closed under pointwise multiplication. -/
theorem smoothOpen_mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ => F z θ * G z θ)
      = Function.uncurry F * Function.uncurry G := rfl
  rw [h1]
  exact hF.mul hG

/-! ## `D_z` commutes with the iterates of `D_θ` on the open quadrant, in the honest order -/

/-- **`D_z (D_θ^i g) = D_θ^i (D_z g)` on the open quadrant**, for `g` of class `SmoothOpen`.
This is the genuine-order (`Work.Stability.smoothOrder`) instance of
`Work.Spaces.DzDthIterCommOn` (which asks for analyticity) on `Q0 = (0,∞) × (0,π/2)`. -/
theorem Dz_DthIter_comm_Q0 {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      Work.FTS.EllipticEst.Q0) (a : ℕ) :
    Set.EqOn (Function.uncurry (Dz (DthIter a g)))
      (Function.uncurry (DthIter a (Dz g))) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have h2le : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  induction a with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hsmD : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (DthIter i g)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (DthIter i g)) y :=
        (ContDiffOn.of_le hsmD h2le).contDiffAt (hV.mem_nhds hy)
      have hcomm : Dz (Dth (DthIter i g)) y.1 y.2
          = Dth (Dz (DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := DthIter i g) hcd
      show Dz (Dth (DthIter i g)) y.1 y.2 = Dth (DthIter i (Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * pth (Dz (DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2) * pth (DthIter i (Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- `D_θ^i (D_z f) = D_z (D_θ^i f)` on the open quadrant, for `f` of class `SmoothOpen`
(the two sides of `Dz_DthIter_comm_Q0`, in the form used below). -/
theorem DthIter_Dz_eq_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) :
    Set.EqOn (Function.uncurry (DthIter i (Dz f))) (Function.uncurry (Dz (DthIter i f)))
      Work.FTS.EllipticEst.Q0 :=
  (Dz_DthIter_comm_Q0 hf i).symm

/-! ## The resulting slot identity -/

/-- The pure radial instance: `D_z^b (D_z f) = D_z^{b+1} f` (a function identity). -/
theorem dzIter_Dz_eq (b : ℕ) (f : ℝ → ℝ → ℝ) : DzIter b (Dz f) = DzIter (b + 1) f := by
  induction b with
  | zero => rfl
  | succ n ih =>
      show Dz (DzIter n (Dz f)) = DzIter (n + 1 + 1) f
      rw [ih]
      exact (Work.Spaces.DzIter_succ (n + 1) f).symm

/-- **`mixed m i (D_z f) = mixed (m+1) i f` on the open quadrant.**  A `D_θ`-derivative that
lands on the factor `D_z f` of a Leibniz expansion is (the next slot of) a derivative of `f`:
`D_z^m D_θ^i (D_z f) = D_z^{m+1} D_θ^i f`. -/
theorem mixed_Dz_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (m i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    mixed m i (Dz f) z θ = mixed (m + 1) i f z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  have hEq := (Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
    (DthIter_Dz_eq_Q0 hf i) m) hy
  have hEq' : DzIter m (DthIter i (Dz f)) z θ = DzIter m (Dz (DthIter i f)) z θ := hEq
  simp only [mixed]
  rw [hEq', dzIter_Dz_eq m (DthIter i f)]

end Work.FTS.StrongPersist.L3Rhs
