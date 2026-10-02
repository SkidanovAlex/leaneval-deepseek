import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachKill
import Submission.Work.RatHurewicz.attachCells_kill
import Submission.Work.RatHurewicz.attachCells_relPi_subsingleton
import Submission.Work.RatHurewicz.attachCells_piMap_bijective
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.excisionTransfer
import Submission.Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open scoped Topology Topology.Homotopy unitInterval

open Work.StemsB

noncomputable section

/-! ## Auxiliary lemmas for the killing step -/

/-- **Naturality of `Work.Stems.cubeLift`**: descending a composed cube is composing the descent.
This is the form in which the link between a class `α` and the sphere map `killFamily n Y y₀ α` is
used below. -/
theorem cubeLift_genLoopMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (f : C(X, Y)) {x : X} (p : Ω^ (Fin n) X x) :
    Work.Stems.cubeLift n hn (genLoopMap f n p) = f.comp (Work.Stems.cubeLift n hn p) := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨w, hw⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
  have hlift : Work.Stems.cubeLift n hn p (Work.Stems.collapseMap n hn w) = p w :=
    DFunLike.congr_fun (Work.Stems.cubeLift_comp n hn p) w
  have hlift2 : Work.Stems.cubeLift n hn (genLoopMap f n p) (Work.Stems.collapseMap n hn w)
      = (genLoopMap f n p) w :=
    DFunLike.congr_fun (Work.Stems.cubeLift_comp n hn (genLoopMap f n p)) w
  calc Work.Stems.cubeLift n hn (genLoopMap f n p) z
      = Work.Stems.cubeLift n hn (genLoopMap f n p) (Work.Stems.collapseMap n hn w) := by rw [hw]
    _ = (genLoopMap f n p) w := hlift2
    _ = f (p w) := rfl
    _ = f (Work.Stems.cubeLift n hn p (Work.Stems.collapseMap n hn w)) := by rw [hlift]
    _ = (f.comp (Work.Stems.cubeLift n hn p)) z := by rw [hw]; rfl

/-- Two constant maps with path-connected values are homotopic: move the value along the path. -/
theorem homotopic_const_of_path {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    {y y' : X} (γ : Path y y') :
    (ContinuousMap.const S y).Homotopic (ContinuousMap.const S y') :=
  ⟨{ toFun := fun w => γ w.1
     continuous_toFun := γ.continuous.comp continuous_fst
     map_zero_left := fun _ => γ.source
     map_one_left := fun _ => γ.target }⟩

/-- `Work.RatHurewicz.rangeHomeo` is a section of `attachIncl` on its range. -/
theorem rangeHomeo_symm_apply_attachIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (a : ↥(Set.range (attachIncl n Y ι f))) :
    attachIncl n Y ι f ((rangeHomeo n Y ι f).symm a) = (a : attachCells n Y ι f) :=
  congrArg Subtype.val (Homeomorph.apply_symm_apply (rangeHomeo n Y ι f) a)

/-- `Work.RatHurewicz.rangeHomeo` is the identity at the base point. -/
theorem rangeHomeo_symm_basepoint (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) :
    (rangeHomeo n Y ι f).symm ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ = y₀ := by
  have h : (rangeHomeo n Y ι f) y₀ = ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ := rfl
  rw [← h]
  exact (rangeHomeo n Y ι f).symm_apply_apply y₀

/-- **Attaching `(n+2)`-cells to `Y` is onto on `π_{n+1}`**: the inclusion `attachIncl` induces a
surjection `π_{n+1}(Y,y₀) → π_{n+1}(Y',attachIncl y₀)`.

This holds for *all* `n` (including the low cases `n = 0, 1`, where the pair sequence is not
available in the form needed): a based `(n+1)`-cube of the attached space is a map of pairs
`(I^{n+1}, ∂I^{n+1}) → (Y', range attachIncl)`, and the compression property of the attachment in
dimensions `≤ n+1` (`Work.RatHurewicz.compressRel_attachCells_range`, the geometric content of the
vanishing of the relative groups) homotopes it, relative to the boundary, into the range, where it
can be lifted back to `Y` through the homeomorphism `Work.RatHurewicz.rangeHomeo` of the range
with `Y`. -/
theorem surjective_πmap_attachIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) :
    Function.Surjective (πmap (attachIncl n Y ι f) n y₀) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have hbdr : ∀ x, x ∈ Cube.boundary (Fin (n + 1)) →
        p x ∈ Set.range (attachIncl n Y ι f) := by
      intro x hx
      exact ⟨y₀, (p.2 x hx).symm⟩
    obtain ⟨G, hG0, hGb, hG1⟩ :=
      compressRel_attachCells_range n Y ι f (n + 1) le_rfl p.1 hbdr
    have hc : Continuous fun x : ICube (n + 1) =>
        (⟨G (x, 1), hG1 x⟩ : ↥(Set.range (attachIncl n Y ι f))) :=
      Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const))
        (fun x => hG1 x)
    have hbd : ∀ y ∈ Cube.boundary (Fin (n + 1)),
        (rangeHomeo n Y ι f).symm ⟨G (y, 1), hG1 y⟩ = y₀ := by
      intro y hy
      have hGy : G (y, 1) = attachIncl n Y ι f y₀ := by
        rw [hGb y hy 1, p.2 y hy]
      have hsub : (⟨G (y, 1), hG1 y⟩ : ↥(Set.range (attachIncl n Y ι f))) =
          ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ := by
        refine Subtype.ext ?_
        exact hGy
      rw [hsub]
      exact rangeHomeo_symm_basepoint n Y ι f y₀
    let g : Ω^ (Fin (n + 1)) Y y₀ :=
      ⟨⟨fun x => (rangeHomeo n Y ι f).symm ⟨G (x, 1), hG1 x⟩,
          (rangeHomeo n Y ι f).symm.continuous.comp hc⟩, hbd⟩
    refine ⟨⟦g⟧, ?_⟩
    rw [πmap_apply_mk]
    have hhom : GenLoop.Homotopic p (genLoopMap (attachIncl n Y ι f) (n + 1) g) := by
      refine ⟨⟨⟨fun w : I × ICube (n + 1) => G (w.2, w.1),
        G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩, ?_, ?_⟩, ?_⟩
      · intro x
        exact hG0 x
      · intro x
        show G (x, 1) = attachIncl n Y ι f (g x)
        exact (rangeHomeo_symm_apply_attachIncl n Y ι f ⟨G (x, 1), hG1 x⟩).symm
      · intro t x hx
        exact hGb x hx t
    exact (Quotient.sound hhom).symm

/-- **Every class in `π_{n+1}(Y,y₀)` dies in `π_{n+1}(Y',attachIncl y₀)`** when the `(n+2)`-cells
are attached along the representatives `killFamily n Y y₀`.

`πmap attachIncl α` is represented by the based cube `genLoopMap attachIncl (Quotient.out α)`,
whose descent `cubeLift` to the sphere is the attaching map of the cell of `α`
(`cubeLift_genLoopMap`); that attaching map becomes null-homotopic in `Y'` through the
characteristic map of the cell (`attachIncl_comp_nullhomotopic`).  The homotopy supplied there is
*unbased*: it ends at the constant map at the centre of the cell, while the base point travels
along the path traced by the centre of the sphere.  Sliding the constant map at the centre back to
the base point along that path (which lives in `Y'` and is continuous) produces a free homotopy to
the constant map at the base point, and a based cube that is freely null-homotopic is trivial in
the homotopy group (`Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const`). -/
theorem πmap_attachIncl_killFamily_eq_one (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (α : HomotopyGroup (Fin (n + 1)) Y y₀) :
    πmap (attachIncl n Y (HomotopyGroup (Fin (n + 1)) Y y₀) (killFamily n Y y₀)) n y₀ α = 1 := by
  let ι := HomotopyGroup (Fin (n + 1)) Y y₀
  let f : ι → C(cellSphere n, Y) := killFamily n Y y₀
  let X := attachCells n Y ι f
  let y₀' : X := attachIncl n Y ι f y₀
  have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨c, hc⟩ := attachIncl_comp_nullhomotopic n Y ι f α
  have hzero : (0 : ICube (n + 1)) ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  have hz₀val : Work.Stems.cubeLift (n + 1) hn (Quotient.out α)
      (Work.Stems.collapseMap (n + 1) hn 0) = y₀ := by
    have h := DFunLike.congr_fun (Work.Stems.cubeLift_comp (n + 1) hn (Quotient.out α))
      (0 : ICube (n + 1))
    exact h.trans ((Quotient.out α).2 0 hzero)
  have hnat : Work.Stems.cubeLift (n + 1) hn
        (genLoopMap (attachIncl n Y ι f) (n + 1) (Quotient.out α))
      = (attachIncl n Y ι f).comp (f α) := by
    rw [cubeLift_genLoopMap]
    rfl
  obtain ⟨H⟩ := hc
  have hz₀Q : ((attachIncl n Y ι f).comp (f α)) (Work.Stems.collapseMap (n + 1) hn 0) = y₀' := by
    show attachIncl n Y ι f ((f α) (Work.Stems.collapseMap (n + 1) hn 0)) = attachIncl n Y ι f y₀
    have hfα : (f α) (Work.Stems.collapseMap (n + 1) hn 0) = y₀ := hz₀val
    rw [hfα]
  have htraj : Continuous fun t : I => H (t, Work.Stems.collapseMap (n + 1) hn 0) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have hslide : (ContinuousMap.const (Work.Stems.sphere (n + 1)) c).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) y₀') := by
    refine homotopic_const_of_path (S := Work.Stems.sphere (n + 1)) (Path.symm ?_)
    exact ⟨⟨fun t => H (t, Work.Stems.collapseMap (n + 1) hn 0), htraj⟩,
      (H.map_zero_left _).trans hz₀Q, H.map_one_left _⟩
  have hfree : (Work.Stems.cubeLift (n + 1) hn
        (genLoopMap (attachIncl n Y ι f) (n + 1) (Quotient.out α))).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) y₀') := by
    rw [hnat]
    exact (show ((attachIncl n Y ι f).comp (f α)).Homotopic
      (ContinuousMap.const (Work.Stems.sphere (n + 1)) c) from ⟨H⟩).trans hslide
  rw [← Quotient.out_eq α, πmap_apply_mk]
  exact genLoop_eq_one_of_free_homotopic_const n y₀' _ hfree

end

/-- **Attaching one `(n+2)`-cell per element of `π_{n+1}(Y,y₀)` kills `π_{n+1}`.**

The attaching family `Work.RatHurewicz.killFamily n Y y₀` sends every class
`α : π_{n+1}(Y,y₀)` to a sphere map representing it, and the characteristic map of the corresponding
cell then exhibits `attachIncl ∘ killFamily α` as null-homotopic
(`Work.RatHurewicz.attachIncl_comp_nullhomotopic`, whose homotopy is
`(t,z) ↦ cellMap i ((1 - t) • z)`).  Hence the map induced by the inclusion on `π_{n+1}` is the
zero map; and it is *onto* because the relative group `RelHomotopyGroup (attachIncl …) y₀ n`
vanishes (`Work.RatHurewicz.attachCells_relPi_subsingleton` at the index `n`, which is available).
Zero and onto imply that the target group is trivial.

This is the "killing" half of the one-step analysis of the Serre blueprint's C0/K1 models
(`Submission/Work/Drive/SERRE_BLUEPRINT.md` §2 C0, ADDENDUM 1 (E), ADDENDUM 2 K1).

Two points of care for the prover, neither affecting the statement:

* the homotopy `attachIncl_comp_nullhomotopic` is *unbased*: it ends at the constant map at the
  centre `cellMap i 0` of the cell, while the base point travels along the path
  `t ↦ cellMap i ((1 - t) • z₀)`.  For `n + 1 ≥ 2` (i.e. `n ≥ 1`) the action of `π_1` on `π_{n+1}`
  is trivial, so an unbased null-homotopy of a based map out of `S^{n+1}` *is* a based
  null-homotopy; for `n = 0` one argues directly with the path component of `y₀`;
* the link between the class `α` and the sphere map `killFamily n Y y₀ α` is the collapse device
  `Work.Stems.cubeLift` together with `Work.Stems.cubeLift_comp` (the descent of a based cube along
  `Work.Stems.collapseMap`), and the base-point transport
  `Work.Stems.subsingleton_homotopyGroup_change_basepoint` (or the corresponding equality of
  classes along a path). -/
theorem killFamily_subsingleton (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Subsingleton (HomotopyGroup (Fin (n + 1))
      (attachCells n Y (HomotopyGroup (Fin (n + 1)) Y y₀) (killFamily n Y y₀))
      (attachIncl n Y (HomotopyGroup (Fin (n + 1)) Y y₀) (killFamily n Y y₀) y₀)) := by
  let ι := HomotopyGroup (Fin (n + 1)) Y y₀
  let f : ι → C(cellSphere n, Y) := killFamily n Y y₀
  let X := attachCells n Y ι f
  let y₀' : X := attachIncl n Y ι f y₀
  refine ⟨fun a b => ?_⟩
  have hsurj : Function.Surjective (πmap (attachIncl n Y ι f) n y₀) :=
    surjective_πmap_attachIncl n Y ι f y₀
  obtain ⟨α, hα⟩ := hsurj a
  obtain ⟨β, hβ⟩ := hsurj b
  rw [← hα, ← hβ, πmap_attachIncl_killFamily_eq_one n Y y₀ α,
    πmap_attachIncl_killFamily_eq_one n Y y₀ β]

end Work.RatHurewicz
