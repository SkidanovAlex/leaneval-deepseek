import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.attachCells_kill
import Submission.Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const

set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open scoped Topology unitInterval

/-!
# Attaching a cell along *every* map kills `π_{n+1}` (cube-based)

Let `Y' := attachCells n Y ι f` be `Y` with `(n+2)`-cells attached along the maps `f i : S^{n+1} → Y`
and let `attachIncl : C(Y, Y')` be the inclusion.  Take the index set to be **all** continuous maps,
`ι := C(cellSphere n, Y)` and `f := id`.  This statement says that then the induced map

`HomotopyGroup (Fin (n+1)) Y y₀ → HomotopyGroup (Fin (n+1)) Y' (attachIncl y₀)`

is *zero*: every `(n+1)`-cube class dies.

Every homotopy class in `π_{n+1}(Y)` has some representative map `g : S^{n+1} → Y`, and a cell is
attached along that very `g`; `Work.RatHurewicz.attachCells_kill` (proved) gives a **free**
null-homotopy of `attachIncl ∘ g` (to the centre of the cell, not to `attachIncl y₀`).  Two pieces of
work are needed (the second is what makes this cube-based statement non-trivial): (1) the cube ↔
sphere dictionary, i.e. a based `(n+1)`-cube `p` (constant on the boundary) and the sphere map `g` it
induces through the collapse `I^{n+1} → I^{n+1}/∂ ≅ S^{n+1}` have the same class; (2) the free → based
upgrade: the centre of the cell is joined to `attachIncl y₀` by a path, so a free null-homotopy of a
*based* sphere map can be turned into a *based* null-homotopy (e.g. by coning the free homotopy with
the path, or by `Work.Stems.genLoop_eq_one_of_free_homotopic_const`-style reasoning).  `Work.Serre.piMapN`
is the induced map on cube-based homotopy groups, so the goal is exactly "the class of every cube
maps to `1`".

This is the second half of the killing step of the tower in `Submission/Work/Serre/SERRES1_NOTES.md`
§5/§7; combined with the *compression* crux (`Serre/serreAttachCompress`, delegated) it yields
`π_i(Y) ≅ π_i(Y')` for `i ≤ n` and `π_{n+1}(Y') = 0` via the long exact sequence of the pair
(`Work.RatHurewicz.pair_les`).

## The argument implemented here

The two requested pieces are both short, and the cell centre is never needed:

* **(sphere dictionary, free version).**  `g := cubeLift (n+1) p : S^{n+1} → Y` is a representative
  of the class of the cube `p` (`Work.Stems.cubeLift_comp`).  Since `g` *is* one of the attaching
  maps, the characteristic map `cellMap i` of its cell restricts to `attachIncl ∘ g` on the boundary
  of the disc (`Work.RatHurewicz.attachIncl_attachRel`).  Composing with the straight lines
  `t ↦ (1-t)•z + t•z₀` of the (convex) disc, where `z₀ = collapseMap 0` is the sphere point that
  `g` sends to `y₀`, gives a **free** null-homotopy of `attachIncl ∘ g` *to the correct constant*
  `attachIncl y₀` — see `attachIncl_comp_homotopic_const`.  (`Work.RatHurewicz.attachCells_kill`
  gives instead the free homotopy to the centre; the straight-line homotopy is used here because it
  lands on `attachIncl y₀` with no path-transport.)

* **(free → based).**  A *free* null-homotopy of the sphere map `cubeLift (n+1) (genLoopMap …)` at the
  correct base value is upgraded to a homotopy relative to `∂I^{n+1}` by
  `Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const` (Hutchings 2.2(a), already in the
  workspace), which is stated for precisely this situation; it descends the free homotopy to the cone
  over the sphere and straightens the base point out along its trajectory.
-/

noncomputable section

/-- The index set of the attaching maps: **all** continuous maps `S^{n+1} → Y`. -/
abbrev KillIdx (n : ℕ) (Y : Type) [TopologicalSpace Y] : Type :=
  C(Work.RatHurewicz.cellSphere n, Y)

/-- `Y` with an `(n+2)`-cell attached along *every* map `S^{n+1} → Y`. -/
abbrev KillCells (n : ℕ) (Y : Type) [TopologicalSpace Y] : Type :=
  Work.RatHurewicz.attachCells n Y (KillIdx n Y) (fun g => g)

/-- The inclusion of `Y` into `KillCells n Y`. -/
abbrev killIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] : C(Y, KillCells n Y) :=
  Work.RatHurewicz.attachIncl n Y (KillIdx n Y) (fun g => g)

/-- The characteristic map of the cell attached along `g : S^{n+1} → Y`. -/
abbrev killCell (n : ℕ) (Y : Type) [TopologicalSpace Y] (g : KillIdx n Y) :
    C(Work.RatHurewicz.cellDisk n, KillCells n Y) :=
  Work.RatHurewicz.cellMap n Y (KillIdx n Y) (fun g => g) g

/-- The gluing relation in the "kill everything" attachment, in the clean form used below: the
boundary of the cell attached along `g` is glued to `Y` along `g` itself. -/
theorem killIncl_apply (n : ℕ) (Y : Type) [TopologicalSpace Y] (g : KillIdx n Y)
    (z : Work.RatHurewicz.cellSphere n) :
    killIncl n Y (g z)
      = killCell n Y g (Work.RatHurewicz.cellSphereToDisk n z) :=
  Work.RatHurewicz.attachIncl_attachRel n Y (KillIdx n Y) (fun g => g) g z

/-- The straight lines of the disc, `(t, z) ↦ (1 - t) • z + t • b`: a continuous map from the
cylinder on the sphere into the disc, contracting the sphere to the point `b`. -/
def sphereStraightLine (n : ℕ) (b : Work.RatHurewicz.cellSphere n) :
    C(unitInterval × Work.RatHurewicz.cellSphere n, Work.RatHurewicz.cellDisk n) where
  toFun w :=
    ⟨(1 - (w.1 : ℝ)) • (w.2 : EuclideanSpace ℝ (Fin (n + 2)))
        + (w.1 : ℝ) • (b : EuclideanSpace ℝ (Fin (n + 2))),
      Metric.mem_closedBall.mpr (by
        rw [dist_eq_norm, sub_zero]
        have hb : ‖(b : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
          have h := Metric.mem_sphere.mp b.2
          rwa [dist_eq_norm, sub_zero] at h
        have hz : ‖(w.2 : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
          have h := Metric.mem_sphere.mp w.2.2
          rwa [dist_eq_norm, sub_zero] at h
        have ht0 : (0 : ℝ) ≤ (w.1 : ℝ) := w.1.2.1
        have ht1 : (w.1 : ℝ) ≤ 1 := w.1.2.2
        have h1 : ‖(1 - (w.1 : ℝ))‖ = 1 - (w.1 : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have h2 : ‖(w.1 : ℝ)‖ = (w.1 : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg ht0]
        calc ‖(1 - (w.1 : ℝ)) • (w.2 : EuclideanSpace ℝ (Fin (n + 2)))
                + (w.1 : ℝ) • (b : EuclideanSpace ℝ (Fin (n + 2)))‖
            ≤ ‖(1 - (w.1 : ℝ)) • (w.2 : EuclideanSpace ℝ (Fin (n + 2)))‖
                + ‖(w.1 : ℝ) • (b : EuclideanSpace ℝ (Fin (n + 2)))‖ := norm_add_le _ _
          _ = 1 := by
              rw [norm_smul, norm_smul, h1, h2, hz, hb, mul_one, mul_one]
              ring)⟩
  continuous_toFun := by fun_prop

@[simp]
theorem sphereStraightLine_zero (n : ℕ) (b : Work.RatHurewicz.cellSphere n)
    (z : Work.RatHurewicz.cellSphere n) :
    sphereStraightLine n b (0, z) = Work.RatHurewicz.cellSphereToDisk n z := by
  apply Subtype.ext
  simp [sphereStraightLine, Work.RatHurewicz.cellSphereToDisk]

@[simp]
theorem sphereStraightLine_one (n : ℕ) (b : Work.RatHurewicz.cellSphere n)
    (z : Work.RatHurewicz.cellSphere n) :
    sphereStraightLine n b (1, z) = Work.RatHurewicz.cellSphereToDisk n b := by
  apply Subtype.ext
  simp [sphereStraightLine, Work.RatHurewicz.cellSphereToDisk]

/-- **The attaching map of a cell dies, freely, at the correct base value.**  `attachIncl ∘ f i`
is freely homotopic to the constant map at `cellMap i b`, where `b` is *any* point of the sphere:
the characteristic map of the cell restricted to the straight lines of the (convex) disc supplies
the homotopy.  Taking `b` to be the sphere point which `f i` sends to the chosen base point of `Y`
renders the constant map the one at `attachIncl` of that base point. -/
theorem attachIncl_comp_homotopic_const (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (b : Work.RatHurewicz.cellSphere n) :
    ((Work.RatHurewicz.attachIncl n Y ι f).comp (f i)).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.cellSphere n)
        (Work.RatHurewicz.cellMap n Y ι f i (Work.RatHurewicz.cellSphereToDisk n b))) :=
  ⟨⟨(Work.RatHurewicz.cellMap n Y ι f i).comp (sphereStraightLine n b), fun z => by
      show (Work.RatHurewicz.cellMap n Y ι f i) (sphereStraightLine n b (0, z))
          = (Work.RatHurewicz.attachIncl n Y ι f) (f i z)
      rw [sphereStraightLine_zero, Work.RatHurewicz.attachIncl_attachRel], fun z => by
      show (Work.RatHurewicz.cellMap n Y ι f i) (sphereStraightLine n b (1, z))
          = (Work.RatHurewicz.cellMap n Y ι f i) (Work.RatHurewicz.cellSphereToDisk n b)
      rw [sphereStraightLine_one]⟩⟩

/-- **The cube ↔ sphere dictionary.**  The descent of a based cube to the sphere commutes with
postcomposition: `cubeLift (genLoopMap h p) = h ∘ cubeLift p`.  Both sides agree after composing
with the surjective quotient map `collapseMap : I^k → S^k`. -/
theorem cubeLift_genLoopMap {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (h : C(X, Z))
    (k : ℕ) (hk : 1 ≤ k) {x₀ : X} (p : GenLoop (Fin k) X x₀) :
    Work.Stems.cubeLift k hk (Work.StemsB.genLoopMap h k p)
      = h.comp (Work.Stems.cubeLift k hk p) := by
  have hsurj := (Work.Stems.collapseMap_isQuotientMap k hk).surjective
  ext z
  obtain ⟨y, rfl⟩ := hsurj z
  show Work.Stems.cubeLift k hk (Work.StemsB.genLoopMap h k p) (Work.Stems.collapseMap k hk y)
      = h ((Work.Stems.cubeLift k hk p) (Work.Stems.collapseMap k hk y))
  have e1 : Work.Stems.cubeLift k hk (Work.StemsB.genLoopMap h k p) (Work.Stems.collapseMap k hk y)
      = (Work.StemsB.genLoopMap h k p).1 y := by
    simpa using congrFun (congrArg (fun f : C(Work.Stems.CubeI k, Z) => ⇑f)
      (Work.Stems.cubeLift_comp k hk (Work.StemsB.genLoopMap h k p))) y
  have e2 : Work.Stems.cubeLift k hk p (Work.Stems.collapseMap k hk y) = p.1 y := by
    simpa using congrFun (congrArg (fun f : C(Work.Stems.CubeI k, X) => ⇑f)
      (Work.Stems.cubeLift_comp k hk p)) y
  rw [e1, e2]
  exact ContinuousMap.comp_apply h p.1 y

/-- The sphere base point of the descent of a based cube maps to the base value: the collapse
`I^k → S^k` sends the (boundary) point `0` to the sphere base point picked by `collapseMap`. -/
theorem cubeLift_boundary_point (k : ℕ) (hk : 1 ≤ k) {X : Type} [TopologicalSpace X] {x₀ : X}
    (p : GenLoop (Fin k) X x₀) :
    Work.Stems.cubeLift k hk p (Work.Stems.collapseMap k hk 0) = x₀ := by
  have e : Work.Stems.cubeLift k hk p (Work.Stems.collapseMap k hk 0) = p.1 0 := by
    simpa using congrFun (congrArg (fun f : C(Work.Stems.CubeI k, X) => ⇑f)
      (Work.Stems.cubeLift_comp k hk p)) (0 : Work.Stems.CubeI k)
  rw [e]
  exact p.2 0 ⟨⟨0, hk⟩, Or.inl rfl⟩

/-- **The key free null-homotopy.**  For `p` a based `(n+1)`-cube in `Y`, the sphere map that
represents its class and along which a cell of `KillCells n Y` is attached has
`killIncl ∘ (cubeLift p)` freely null-homotopic — indeed to the constant map at
`killIncl y₀`, the base point of the cube. -/
theorem killFreeNull (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (p : GenLoop (Fin (n + 1)) Y y₀) :
    (Work.Stems.cubeLift (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Work.StemsB.genLoopMap (killIncl n Y) (n + 1) p)).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) (killIncl n Y y₀)) := by
  have hk : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  -- the sphere map attached along, and the sphere base point of the cube
  have hpt : Work.Stems.cubeLift (n + 1) hk p (Work.Stems.collapseMap (n + 1) hk 0) = y₀ :=
    cubeLift_boundary_point (n + 1) hk p
  -- the free null-homotopy of `killIncl ∘ g`, to the constant at the boundary point of the cell
  have hfree := attachIncl_comp_homotopic_const n Y (KillIdx n Y) (fun g => g)
    (Work.Stems.cubeLift (n + 1) hk p) (Work.Stems.collapseMap (n + 1) hk 0)
  -- ... and that constant is `killIncl y₀`
  have hconst : killCell n Y (Work.Stems.cubeLift (n + 1) hk p)
      (Work.RatHurewicz.cellSphereToDisk n (Work.Stems.collapseMap (n + 1) hk 0))
      = killIncl n Y y₀ := by
    rw [← killIncl_apply n Y (Work.Stems.cubeLift (n + 1) hk p)
      (Work.Stems.collapseMap (n + 1) hk 0), hpt]
  have h2 : ((Work.RatHurewicz.attachIncl n Y (KillIdx n Y) (fun g => g)).comp
      (Work.Stems.cubeLift (n + 1) hk p)).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.cellSphere n) (killIncl n Y y₀)) := by
    simpa only [hconst] using hfree
  have hA : Work.Stems.cubeLift (n + 1) hk (Work.StemsB.genLoopMap (killIncl n Y) (n + 1) p)
      = (killIncl n Y).comp (Work.Stems.cubeLift (n + 1) hk p) :=
    cubeLift_genLoopMap (killIncl n Y) (n + 1) hk p
  simpa only [← hA] using h2

theorem serreAttachKillPi :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y),
      ∀ a : HomotopyGroup (Fin (n + 1)) Y y₀,
        piMapN (Work.RatHurewicz.attachIncl n Y (C(Work.RatHurewicz.cellSphere n, Y))
            (fun g => g)) (n + 1) y₀ a = 1 := by
  intro n Y _ y₀ a
  induction a using Quotient.inductionOn with
  | h p =>
    rw [piMapN_apply_mk]
    exact Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const n (killIncl n Y y₀)
      (Work.StemsB.genLoopMap (killIncl n Y) (n + 1) p) (killFreeNull n Y y₀ p)

end

end Work.Serre
