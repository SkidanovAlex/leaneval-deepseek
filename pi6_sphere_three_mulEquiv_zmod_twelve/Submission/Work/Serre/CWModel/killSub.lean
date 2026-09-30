import Mathlib
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.RatHurewicz.AttachCells

/-!
# Every class dies in the space obtained by attaching the killing cells

`Work.RatHurewicz.killFamily_subsingleton` shows that attaching one `(n+2)`-cell to `Y` along a
sphere map representing *every* element of `π_{n+1}(Y,y₀)` (the family
`Work.RatHurewicz.killFamily n Y y₀`) makes that group trivial.

This module isolates the *general* form of the underlying computation: for an **arbitrary** index
type `ι` and an **arbitrary** family `f : ι → C(S^{n+1},Y)`, a class `α : π_{n+1}(Y,y₀)` whose
representative `killFamily n Y y₀ α` is one of the attaching maps dies in the attached space:

  `πmap (attachIncl n Y ι f) n y₀ α = 1`   whenever `f i = killFamily n Y y₀ α`.

The target `Work.Serre.CWModel.killSub` is the case `f = fun j => killFamily n Y y₀ (s j)`,
`α = s i` of that statement.  The proof is the one of
`Work.RatHurewicz.πmap_attachIncl_killFamily_eq_one`: the attaching map of the cell of `α` is
(`Work.Stems.cubeLift` of) a representative cube of `α`, so `πmap (attachIncl) α` is represented
by a based cube whose descent to `S^{n+1}` is `attachIncl ∘ f i`; that composite is null-homotopic
through the characteristic map of the cell (`attachIncl_comp_nullhomotopic`), and a based cube
which is *freely* null-homotopic is trivial (`genLoop_eq_one_of_free_homotopic_const`).
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.StemsB

namespace Work.Serre.CWModel

noncomputable section

/-- **A class dies in the space obtained by attaching its own cell (general index type).**

If `f : ι → C(S^{n+1},Y)` is any family of attaching maps one of which is the sphere map
`Work.RatHurewicz.killFamily n Y y₀ α` representing `α ∈ π_{n+1}(Y,y₀)`, then `α` is killed by the
inclusion `attachIncl n Y ι f` of `Y` into the space obtained by attaching the cells. -/
theorem πmap_attachIncl_eq_one_of_killFamily {n : ℕ} (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    {ι : Type} (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (α : HomotopyGroup (Fin (n + 1)) Y y₀)
    (hf : f i = Work.RatHurewicz.killFamily n Y y₀ α) :
    πmap (Work.RatHurewicz.attachIncl n Y ι f) n y₀ α = 1 := by
  let X := Work.RatHurewicz.attachCells n Y ι f
  let y₀' : X := Work.RatHurewicz.attachIncl n Y ι f y₀
  have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨c, hc⟩ := Work.RatHurewicz.attachIncl_comp_nullhomotopic n Y ι f i
  have hzero : (0 : I^(Fin (n + 1))) ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  have hz₀val : Work.Stems.cubeLift (n + 1) hn (Quotient.out α)
      (Work.Stems.collapseMap (n + 1) hn 0) = y₀ := by
    have h := DFunLike.congr_fun (Work.Stems.cubeLift_comp (n + 1) hn (Quotient.out α))
      (0 : I^(Fin (n + 1)))
    exact h.trans ((Quotient.out α).2 0 hzero)
  have hnat : Work.Stems.cubeLift (n + 1) hn
        (genLoopMap (Work.RatHurewicz.attachIncl n Y ι f) (n + 1) (Quotient.out α))
      = (Work.RatHurewicz.attachIncl n Y ι f).comp (f i) := by
    rw [Work.RatHurewicz.cubeLift_genLoopMap]
    exact congrArg (ContinuousMap.comp (Work.RatHurewicz.attachIncl n Y ι f)) hf.symm
  obtain ⟨H⟩ := hc
  have hz₀Q : ((Work.RatHurewicz.attachIncl n Y ι f).comp (f i))
      (Work.Stems.collapseMap (n + 1) hn 0) = y₀' := by
    show Work.RatHurewicz.attachIncl n Y ι f
      ((f i) (Work.Stems.collapseMap (n + 1) hn 0)) = Work.RatHurewicz.attachIncl n Y ι f y₀
    have hfα : (f i) (Work.Stems.collapseMap (n + 1) hn 0) = y₀ := by
      rw [hf]; exact hz₀val
    rw [hfα]
  have htraj : Continuous fun t : I => H (t, Work.Stems.collapseMap (n + 1) hn 0) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have hslide : (ContinuousMap.const (Work.Stems.sphere (n + 1)) c).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) y₀') := by
    refine Work.RatHurewicz.homotopic_const_of_path (S := Work.Stems.sphere (n + 1))
      (Path.symm ?_)
    exact ⟨⟨fun t => H (t, Work.Stems.collapseMap (n + 1) hn 0), htraj⟩,
      (H.map_zero_left _).trans hz₀Q, H.map_one_left _⟩
  have hfree : (Work.Stems.cubeLift (n + 1) hn
        (genLoopMap (Work.RatHurewicz.attachIncl n Y ι f) (n + 1) (Quotient.out α))).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) y₀') := by
    rw [hnat]
    exact (show ((Work.RatHurewicz.attachIncl n Y ι f).comp (f i)).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) c) from ⟨H⟩).trans hslide
  rw [← Quotient.out_eq α, πmap_apply_mk]
  exact Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const n y₀' _ hfree

/-- **Every class `s i` dies in the space obtained by attaching the cells of the classes `s j`.**

This is the form in which the killing step of the Postnikov construction is used: for an arbitrary
family `s : ι → π_{n+1}(Y,y₀)`, attaching an `(n+2)`-cell along a representative of `s j` for every
`j` kills every class `s i` (not only the whole of `π_{n+1}`, which is
`Work.RatHurewicz.killFamily_subsingleton` for the family of *all* classes). -/
theorem killSub {n : ℕ} (Y : Type) [TopologicalSpace Y] (y₀ : Y) (ι : Type)
    (s : ι → HomotopyGroup (Fin (n + 1)) Y y₀) (i : ι) :
    Work.StemsB.πmap (Work.RatHurewicz.attachIncl n Y ι
        (fun j => Work.RatHurewicz.killFamily n Y y₀ (s j))) n y₀ (s i) = 1 :=
  πmap_attachIncl_eq_one_of_killFamily Y y₀ (fun j => Work.RatHurewicz.killFamily n Y y₀ (s j))
    i (s i) rfl

end

end Work.Serre.CWModel
