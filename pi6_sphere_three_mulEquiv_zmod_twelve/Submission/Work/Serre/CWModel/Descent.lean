import Mathlib
import Submission.Work.Stems.Hurewicz
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.ThomBordism.Grassmann.Clamp.LpcCriterion

/-!
# Descending a homotopy of cubes to a homotopy of spheres

`Work.Stems.cubeLift` turns a based cube `I^n → X` (constant on `∂I^n`) into a sphere map
`S^n → X`, by descending along the collapse `Work.Stems.collapseMap : I^n → S^n`.  This file proves
that the construction is compatible with homotopies: a homotopy of cubes *relative to the boundary*
descends to a homotopy of the corresponding sphere maps.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre.CWModel

noncomputable section

/-- The product of the identity of the interval with the collapse `I^n → S^n`. -/
def prodCollapse (n : ℕ) (hn : 1 ≤ n) :
    C(unitInterval × Work.Stems.CubeI n, unitInterval × Work.Stems.sphere n) :=
  ContinuousMap.prodMap (ContinuousMap.id unitInterval) (Work.Stems.collapseMap n hn)

/-- The product collapse is a quotient map (a continuous surjection from a compact space onto a
Hausdorff space). -/
theorem isQuotientMap_prodCollapse (n : ℕ) (hn : 1 ≤ n) :
    Topology.IsQuotientMap (prodCollapse n hn) := by
  refine Work.ThomBordism.Grassmann.Clamp.isQuotientMap_of_compact_t2 (prodCollapse n hn).continuous ?_
  rintro ⟨t, z⟩
  obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
  exact ⟨(t, y), rfl⟩

/-- **A homotopy of based cubes descends to a homotopy of the corresponding sphere maps.** -/
theorem cubeLift_homotopic {n : ℕ} (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x : X}
    {c c' : Ω^ (Fin n) X x} (h : GenLoop.Homotopic c c') :
    (Work.Stems.cubeLift n hn c).Homotopic (Work.Stems.cubeLift n hn c') := by
  classical
  obtain ⟨F⟩ := h
  let κ : C(unitInterval × Work.Stems.CubeI n, X) := ⟨fun w => F w, F.continuous⟩
  have hκ : ∀ w, κ w = F w := fun _ => rfl
  have hq := isQuotientMap_prodCollapse n hn
  have hfac : Function.FactorsThrough (⇑κ) (⇑(prodCollapse n hn)) := by
    rintro ⟨t, y⟩ ⟨t', y'⟩ hxy
    have ht : t = t' := congrArg Prod.fst hxy
    have hy : (Work.Stems.collapseMap n hn) y = (Work.Stems.collapseMap n hn) y' :=
      congrArg Prod.snd hxy
    subst ht
    rcases Work.Stems.collapseMap_fiber n hn hy with h1 | ⟨h1, h2⟩
    · subst h1; rfl
    · calc κ (t, y) = F (t, y) := hκ (t, y)
        _ = c.1 y := F.eq_fst t h1
        _ = x := c.2 y h1
        _ = c.1 y' := (c.2 y' h2).symm
        _ = F (t, y') := (F.eq_fst t h2).symm
        _ = κ (t, y') := (hκ (t, y')).symm
  set H : C(unitInterval × Work.Stems.sphere n, X) := hq.lift κ hfac with hHdef
  have hH : ∀ (t : unitInterval) (y : Work.Stems.CubeI n),
      ⇑H (t, (Work.Stems.collapseMap n hn) y) = F (t, y) := by
    intro t y
    have hc := congrFun (congrArg DFunLike.coe (Topology.IsQuotientMap.lift_comp hq κ hfac))
      (t, y)
    simp only [ContinuousMap.comp_apply, prodCollapse, ContinuousMap.prodMap_apply,
      ContinuousMap.id_apply] at hc
    calc ⇑H (t, (Work.Stems.collapseMap n hn) y) = κ (t, y) := hc
      _ = F (t, y) := hκ (t, y)
  refine ⟨{ toContinuousMap := H
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro z
    obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
    calc ⇑H (0, (Work.Stems.collapseMap n hn) y) = F (0, y) := hH 0 y
      _ = c.1 y := F.map_zero_left y
      _ = (Work.Stems.cubeLift n hn c) ((Work.Stems.collapseMap n hn) y) :=
          (congrFun (congrArg (fun f : C(Work.Stems.CubeI n, X) => ⇑f)
            (Work.Stems.cubeLift_comp n hn c)) y).symm
  · intro z
    obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
    calc ⇑H (1, (Work.Stems.collapseMap n hn) y) = F (1, y) := hH 1 y
      _ = c'.1 y := F.map_one_left y
      _ = (Work.Stems.cubeLift n hn c') ((Work.Stems.collapseMap n hn) y) :=
          (congrFun (congrArg (fun f : C(Work.Stems.CubeI n, X) => ⇑f)
            (Work.Stems.cubeLift_comp n hn c')) y).symm

/-- The descent of the constant cube is the constant sphere map. -/
@[simp] theorem cubeLift_const {n : ℕ} (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x : X) :
    Work.Stems.cubeLift n hn (GenLoop.const (N := Fin n) (X := X) (x := x))
      = ContinuousMap.const (Work.Stems.sphere n) x := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
  exact congrFun (congrArg (fun f : C(Work.Stems.CubeI n, X) => ⇑f)
    (Work.Stems.cubeLift_comp n hn (GenLoop.const (N := Fin n) (X := X) (x := x)))) y

end

end Work.Serre.CWModel
