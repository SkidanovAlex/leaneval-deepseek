import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.SPC.Setup
import Submission.Work.Serre.SPC.attachGood
import Submission.Work.Serre.SPC.cellStepStrong
import Submission.Work.Serre.SPC.fibreTransport
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.Kill
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Serre.cellStepDefs
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.Serre.E2dFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The tower comparison

The cellular induction of the proof of the Serre exact sequence in the stable range: for a Serre
fibration `p : E → B` with `B` `(b-1)`-connected and fibre homologically `f`-connected, the
comparison map of the pullback of `p` along the structure map of every stage of the model tower
`Work.Serre.CWModel.towerA` is an isomorphism in degrees `< b + f` and surjective in degree
`b + f`.

The induction runs over `Work.Serre.SPC.attachGood`, which compares the two triple exact sequences
`(P, q⁻¹{γ₀'}, q⁻¹Γ)` and `(Γ', {γ₀'}, Γ)` of one cell attachment and applies the five lemma
(`Work.Serre.SPC.tauTwoRange`) to the middle terms.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Serre.SPC

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The induction of the tower comparison.**  For every stage `k` of the model tower the
comparison map of the pullback of `p` along the structure map is an isomorphism in degrees
`< b + f` and an epimorphism in degree `b + f`. -/
theorem towerGood (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    (e₀ : E) (he₀ : p e₀ = b₀) (f : ℕ) (hcell : Work.Serre.SPC.CellStepHyp)
    (htr : Work.Serre.SPC.FibreTransport)
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (b : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) (k : ℕ) :
    GoodMap p b f (Work.Serre.CWModel.towerA B b₀ b hb hconn k).g
      (Work.Serre.CWModel.towerA B b₀ b hb hconn k).y₀ := by
  induction k with
  | zero =>
    exact goodMap_of_good p b f (Work.Serre.CWModel.baseState B b₀ b hb hconn)
      (baseGood p b₀ b f hb hconn)
  | succ k ih =>
    let n : ℕ := b - 2 + k
    let st : Work.Serre.CWModel.StA B b₀ n := Work.Serre.CWModel.towerA B b₀ b hb hconn k
    haveI hc1 : PathConnectedSpace st.Y := st.conn
    have hgen : GoodMap p b f (Work.Serre.CWModel.genStep st).g
        (Work.Serre.CWModel.genStep st).y₀ :=
      attachGood p hp b₀ e₀ he₀ f hcell htr hfib hfib0 b hb st.g st.y₀ st.gbase
        n (HomotopyGroup (Fin (n + 2)) B (st.g st.y₀))
        (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) st.y₀)
        (Work.Serre.CWModel.genStep st).g (fun x => rfl) (by omega)
        ih
    haveI hc2 : PathConnectedSpace (Work.Serre.CWModel.genStep st).Y :=
      (Work.Serre.CWModel.genStep st).conn
    have hkill : GoodMap p b f (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep st)).g
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep st)).y₀ :=
      attachGood p hp b₀ e₀ he₀ f hcell htr hfib hfib0 b hb
        (Work.Serre.CWModel.genStep st).g (Work.Serre.CWModel.genStep st).y₀
        (Work.Serre.CWModel.genStep st).gbase (n + 1)
        {α : HomotopyGroup (Fin (n + 2)) (Work.Serre.CWModel.genStep st).Y
            (Work.Serre.CWModel.genStep st).y₀ //
          Work.Serre.piMapN (Work.Serre.CWModel.genStep st).g (n + 2)
            (Work.Serre.CWModel.genStep st).y₀ α = 1}
        (fun k => Work.RatHurewicz.killFamily (n + 1) (Work.Serre.CWModel.genStep st).Y
          (Work.Serre.CWModel.genStep st).y₀ k.1)
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep st)).g
        (fun x => rfl) (by omega) hgen
    show GoodMap p b f (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep st)).g
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep st)).y₀
    exact hkill

end

noncomputable section

theorem towerComparison {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    (e₀ : E) (he₀ : p e₀ = b₀) (b f : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hcell : Work.Serre.SPC.CellStepHyp) (htr : Work.Serre.SPC.FibreTransport) (k : ℕ) :
    (∀ i : ℕ, i < b + f → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.StemsB.pullbackFst
        (Work.Serre.CWModel.towerA B b₀ b hb hconn k).g p)
        (Work.Serre.CWModel.towerA B b₀ b hb hconn k).y₀) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.StemsB.pullbackFst
        (Work.Serre.CWModel.towerA B b₀ b hb hconn k).g p)
        (Work.Serre.CWModel.towerA B b₀ b hb hconn k).y₀) (b + f)).hom := by
  have h := towerGood p hp b₀ e₀ he₀ f hcell htr hfib hfib0 b hb hconn k
  exact ⟨h.1, (ModuleCat.epi_iff_surjective _).mp h.2⟩

end

end Work.Serre.SPC
