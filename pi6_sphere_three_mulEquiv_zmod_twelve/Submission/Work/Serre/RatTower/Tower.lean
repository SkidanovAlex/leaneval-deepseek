import Mathlib
import Submission.Work.Serre.RatTower.Base
import Submission.Work.Serre.RatTower.attachStepQ
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.Kill
import Submission.Work.Serre.CWModel.sphereExtend

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre.RatTower

noncomputable section

/-- The null-homotopy of the attaching data of `Work.Serre.CWModel.killStep` (verbatim from its
definition, so that the `hG`-field of the resulting `attachG` can be reconstructed). -/
theorem rt_killStep_hnull {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : CWModel.StG B b₀ n)
    (k : {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // piMapN s.g (n + 2) s.y₀ α = 1}) :
    (s.g.comp (Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1)).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.cellSphere (n + 1)) (s.g s.y₀)) := by
  have hker : piMapN s.g (n + 2) s.y₀ k.1 = 1 := k.2
  have hn : 1 ≤ n + 2 := by omega
  have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap s.g (n + 2) (Quotient.out k.1))
      (GenLoop.const (N := Fin (n + 2)) (X := B) (x := s.g s.y₀)) := by
    have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap s.g (n + 2) (Quotient.out k.1)) :
          HomotopyGroup (Fin (n + 2)) B (s.g s.y₀))
        = Quotient.mk (GenLoop.Homotopic.setoid (Fin (n + 2)) (s.g s.y₀))
            (GenLoop.const (N := Fin (n + 2)) (X := B) (x := s.g s.y₀)) := by
      rw [← piMapN_apply_mk, Quotient.out_eq k.1, hker]
      exact HomotopyGroup.one_def (N := Fin (n + 2)) (X := B) (x := s.g s.y₀)
    exact Quotient.exact h1
  have h2 := Work.Serre.CWModel.cubeLift_homotopic hn hcube
  rw [Work.Serre.cubeLift_genLoopMap, Work.Serre.CWModel.cubeLift_const] at h2
  exact h2

/-- **The tower induction.**  For a Serre fibration `p : E → B` over a `(b-1)`-connected base
(`b ≥ 2`) whose fibres are rationally acyclic below `f` and rationally connected, the comparison
map of the pullback of `p` along the `k`-th stage of the model tower is an isomorphism on rational
homology below `b + f` and surjective in degree `b + f`. -/
theorem rt_goodQ_towerA (hcell : RatCellStepSharp) {B : Type} [TopologicalSpace B]
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (b₀ : B) (b f : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib : ∀ b' : B, ∀ j : ℕ, 0 < j → j < f →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p b')) j))
    (h0 : ∀ b' : B, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b')) 0 ≅ ModuleCat.of ℚ ℚ))
    (k : ℕ) :
    GoodQ p b f (CWModel.towerA B b₀ b hb hconn k).Y (CWModel.towerA B b₀ b hb hconn k).g
      (CWModel.towerA B b₀ b hb hconn k).y₀ := by
  induction k with
  | zero => exact rt_baseGood p b₀ b f
  | succ k ih =>
      set s := CWModel.towerA B b₀ b hb hconn k with hs
      have h1 : GoodQ p b f (CWModel.genStep s).Y (CWModel.genStep s).g (CWModel.genStep s).y₀ := by
        refine attachStepQ p hp b f hb hfib h0 hcell s.y₀ s.g (b - 2 + k) (by omega)
          _ _ _ ?_ ih
        intro j z
        have hspec := Classical.choose_spec (Work.Serre.cubeDiskHomeo (b - 2 + k + 2))
        refine (Quotient.out j).2 _ ((hspec _).mpr ?_)
        show ((Classical.choose (Work.Serre.cubeDiskHomeo (b - 2 + k + 2)))
            ((Classical.choose (Work.Serre.cubeDiskHomeo (b - 2 + k + 2))).symm
              (Work.RatHurewicz.cellSphereToDisk (b - 2 + k) z)) :
              EuclideanSpace ℝ (Fin (b - 2 + k + 2))) ∈ Metric.sphere 0 1
        rw [Homeomorph.apply_symm_apply]
        exact z.2
      refine attachStepQ p hp b f hb hfib h0 hcell (CWModel.genStep s).y₀ (CWModel.genStep s).g
        (b - 2 + k + 1) (by omega) _ _ _ ?_ h1
      intro kk z
      have hnn := rt_killStep_hnull (CWModel.genStep s) kk
      exact congrArg (fun ψ : C(Work.RatHurewicz.cellSphere (b - 2 + k + 1), B) => ψ z)
        (Classical.choose_spec (Work.Serre.CWModel.sphereExtend
          ((CWModel.genStep s).g.comp (Work.RatHurewicz.killFamily (b - 2 + k + 1)
            (CWModel.genStep s).Y (CWModel.genStep s).y₀ kk.1))
          hnn.some.toContinuousMap ((CWModel.genStep s).g (CWModel.genStep s).y₀)
          hnn.some.map_zero_left hnn.some.map_one_left))

end

end Work.Serre.RatTower
