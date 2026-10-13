import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.Blocks.HalfInfra
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Sup

open scoped Real Topology
open Set Filter

/-! ## Finite-order commutation of `D_θ`- and `D_z`-iterates

`D_θ f = sin(2θ) ∂_θ f` and `D_z f = z ∂_z f` commute at every point where the profile is
`C²` (`Work.Spaces.Dz_Dth_comm`): the coefficient of `D_θ` depends only on `θ` and that of
`D_z` only on `z`, so the identity is Clairaut's theorem.  On an open set on which the
profile is *genuinely* smooth, iterating gives `D_θ^i (D_z^b f) = D_z^b (D_θ^i f)`
(`Work.Blocks.Half.DthIter_DzIter_comm_eqOn`, `Work.Spaces.DthIter_DzIter_comm_eqOn`, …).

Here we record the **finite-order** version: it suffices that the profile is `C^n` on the
open set `V`, with `i + b ≤ n`.  Each of the two operators costs exactly one order of
differentiability (`contDiffOn_Dth_fin`, `contDiffOn_Dz_fin`), so after moving `i` angular
derivatives across `b` radial ones every Clairaut step still has two orders to spare. -/

/-- `D_θ` is local: two functions that agree on an open set have the same `D_θ` at every
point of that set.  (Only the `θ`-slice near the point matters.) -/
theorem Dth_congr_of_isOpen_fin {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro y hy
  show Real.sin (2 * y.2) * Work.Spaces.pth g y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth g' y.1 y.2
  rw [Work.Spaces.pth_congr_of_isOpen hV h hy]

/-- **A single `D_θ` crosses any number of `D_z`-iterates**, for a profile of class `C^{b+1}`
(or better) on the open set `V`. -/
theorem Dth_DzIter_comm_fin_aux {Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (m : ℕ) (hY : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (Function.uncurry Y) V) :
    ∀ b : ℕ, b + 1 ≤ m →
      Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b Y)))
        (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth Y))) V := by
  intro b
  induction b with
  | zero => intro _ y hy; rfl
  | succ b ih =>
      intro hb y hy
      -- `D_z^b Y` has `m - b ≥ 2` orders, so Clairaut applies at `y`.
      have hDb : ContDiffOn ℝ (((m - b : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DzIter b Y)) V :=
        Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin hV hY b (by omega)
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b Y)) (y.1, y.2) :=
        (hDb.contDiffAt (hV.mem_nhds hy)).of_le (by
          have h2 : (2 : ℕ) ≤ m - b := by omega
          exact_mod_cast h2)
      -- Clairaut at `y`, then the induction hypothesis transported through `D_z`.
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b Y)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b Y)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DzIter b Y) hcd
      have hpz : Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b Y)) y.1 y.2
          = Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth Y)) y.1 y.2 :=
        Work.Spaces.pz_congr_of_isOpen hV (ih (by omega)) hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b Y)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth Y)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b Y)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth Y)) y.1 y.2
      rw [hpz]

/-- **Finite-order commutation of the curvilinear derivatives on an open set.**  If the
uncurried profile `X` is `C^n` on the open set `V` and `i + b ≤ n`, then
`D_θ^i (D_z^b X) = D_z^b (D_θ^i X)` on `V`. -/
theorem DthIter_DzIter_comm_fin {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ n (Function.uncurry X) V) (i b : ℕ) (hib : i + b ≤ n) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i X))) V := by
  induction i generalizing b with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hib' : i + b ≤ n := by omega
      -- `D_θ^i X` is `C^{n-i}` on `V`, with `n - i ≥ b + 1`.
      have hDi : ContDiffOn ℝ (((n - i : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DthIter i X)) V :=
        Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin hV h i (by omega)
      -- transport the induction hypothesis through the outer `D_θ` …
      have hcongr : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) y.1 y.2 :=
        Dth_congr_of_isOpen_fin hV (ih b hib') hy
      -- … and cross the `b` radial derivatives.
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i X)) y.1 y.2 :=
        (Dth_DzIter_comm_fin_aux (Y := Work.Spaces.DthIter i X) hV (n - i) hDi b (by omega)) hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i X)) y.1 y.2
      rw [hcongr, hstep]

end Work.FTS.RegPkgGal.Sup
