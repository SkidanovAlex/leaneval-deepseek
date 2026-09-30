/-
# The finite junction-collar cover: every point of the collar layer lies in a junction chart

The junction charts of `M̂` (`Submission/Work/RTOwed/FillBigDefs.lean`) are indexed by the pinning
datum `Work.RTOwed.JPin` (a perimeter pinning `(cU,k)`, a `w`-section box `W` with its injectivity
condition `hsec`, and a horizontal box `(kx,δ)` of the collar branch).  This file proves the cover
theorem

  `Work.RTOwed.jCollar_cover_fin`:

for **every** assembly `a` and every gluing datum `D`, there is a *finite* family of junction
pinning data — a natural number `N` and a map `par : Fin N → Σ v, JPin a v` — such that every point
`q = (p,y)` of the collar layer `‖p‖∞ ≥ 1/2` of every filling piece `v` has its image `a.incW v q`
in the image of the coordinate inclusion `jCoordM` of one of the boxes.

## The construction

The finiteness is the whole point, and it is obtained from three independent finite covers, one for
each entry of the pinning data:

* **the `w`-section.**  The lift `w` of the torus coordinate is *chosen canonically*: the
  representative of `D v |>.tor y` in the fundamental domain `[0,1]²` (`AddCircle.equivIco`).
  The `w`-coordinates of the canonical lifts form a compact set, so finitely many section boxes
  `jWSet v c` cover them (`Work.RTOwed.jW_cover`); the box radius `1/4` makes each `jWSet v c`
  satisfy the section condition `hsec` (`jWSet_hsec`).
* **the horizontal box** `(kx, δ = 1/2)`.  With the canonical lift the collar coordinate
  `x = cuspX v (u p) w` ranges over the compact image of `[0,1]³`, so finitely many `kx` cover it
  (`Work.RTOwed.jKx_cover`).
* **the perimeter pinning** `(cU,k)`.  The perimeter coordinate of the polar point is the layer
  parameter `u p ∈ [0,1)` (`polarChart_uqOf_ThetaPolar`), and the eight pairs of `jPin` pin its lift
  (`Work.RTOwed.jPin_cover`).

The polar point attached to the data is `z = ThetaPolar v p w`: its radial coordinate lies in
`(1/2, rBig)` (`Work.RTOwed.jRadial_window`), its `w`-coordinates lie in the chosen section box, its
perimeter coordinate is pinned by `(cU,k)`, and `xOf (polarToUHS v z) = cuspX v (u p) w` lies in the
horizontal box of radius `1/2`.  Hence `z ∈ jBox` and the coordinate inclusion of the junction chart
evaluates at `z` to `a.incW v (p,y)`: this is `Work.RTOwed.jCoordM_inner` at the junction
`‖p‖∞ = 1/2` and `Work.RTOwed.jCoordM_collar` on the open collar.
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.RTOwed.jCollarAux
import Submission.Work.Cusp.radial_bounds
import Submission.Work.Cusp.radial_half
import Submission.Work.Cusp.u_mem
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter_half
import Submission.Work.Cusp.cuspInvInner_ThetaPolar
import Submission.Work.RTOwed.jRadial_window
import Submission.Work.RTOwed.jW_cover
import Submission.Work.RTOwed.jKx_cover
import Submission.Work.RTOwed.jPin_cover
import Submission.Work.RTOwed.jCoordM_inner
import Submission.Work.RTOwed.jCoordM_collar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.Cusp

theorem jCollar_cover_fin (a : Work.Space.Assembly) (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v) :
    ∃ (N : ℕ) (par : Fin N → Σ v : Work.Space.Cusp, Work.RTOwed.JPin a v),
      ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
        q ∈ Work.Cusp.collarLayer (a.Torus v) →
        ∃ i, (par i).1 = v ∧
          a.incW v q ∈ Work.RTOwed.jCoordM a v (D v) (par i).2.cU (par i).2.k (par i).2.W
            (par i).2.kx (par i).2.δ '' (Set.univ : Set {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v (par i).2.cU (par i).2.k (par i).2.W (par i).2.kx (par i).2.δ}) := by
  classical
  -- (1) the two finite cover families, one for each cusp
  have hW : ∀ v : Work.Space.Cusp, ∃ C : Finset Work.Cusp.E2, ∀ w : Work.Cusp.E2,
      (∀ j, 0 ≤ w j ∧ w j ≤ 1) → ∃ c ∈ C, Work.Cusp.wOf v w ∈ Work.RTOwed.jWSet v c :=
    fun v => jW_cover v
  choose Cw hCw using hW
  have hKx : ∀ v : Work.Space.Cusp, ∃ K : Finset Work.Cusp.E3, ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ∀ y : Work.Cusp.E2, (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      ∃ kx ∈ K, ∀ j, |Work.Cusp.cuspX v u y j - kx j| < 1 / 2 := fun v => jKx_cover v
  choose Kx hKx' using hKx
  -- (2) the index type of the finite family
  let ι := Σ v : Work.Space.Cusp,
      {c : Work.Cusp.E2 // c ∈ Cw v} × {kx : Work.Cusp.E3 // kx ∈ Kx v} × Fin 8
  haveI : Fintype ι := by dsimp only [ι]; infer_instance
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let pinOf : ι → Σ v : Work.Space.Cusp, Work.RTOwed.JPin a v := fun i =>
    ⟨i.1,
      { cU := (Work.RTOwed.jPin i.2.2.2).1
        k := (Work.RTOwed.jPin i.2.2.2).2
        W := Work.RTOwed.jWSet i.1 i.2.1.1
        kx := i.2.2.1.1
        δ := 1 / 2
        hδ := le_refl (1 / 2)
        hW := Work.RTOwed.jWSet_isOpen i.1 i.2.1.1
        hsec := Work.RTOwed.jWSet_hsec i.1 i.2.1.1 }⟩
  let par : Fin (Fintype.card ι) → Σ v : Work.Space.Cusp, Work.RTOwed.JPin a v :=
    fun i => pinOf (e.symm i)
  refine ⟨Fintype.card ι, par, ?_⟩
  intro v q hq
  obtain ⟨p, y⟩ := q
  have hpSq : (p : Work.Cusp.E2) ∈ Work.Cusp.Sq := p.2
  have hp1 : Work.Cusp.nrm (p : Work.Cusp.E2) ≤ 1 := by
    rcases hpSq with ⟨h0, h1⟩; exact max_le h0 h1
  have h1 : 1 / 2 ≤ Work.Cusp.nrm (p : Work.Cusp.E2) := hq
  -- (3) the canonical lift of the torus coordinate into the unit square
  have hico : ∀ x : AddCircle (1 : ℝ), 0 ≤ (AddCircle.equivIco (1 : ℝ) 0 x : ℝ) ∧
      (AddCircle.equivIco (1 : ℝ) 0 x : ℝ) ≤ 1 := by
    intro x
    have h := (AddCircle.equivIco (1 : ℝ) 0 x).2
    exact ⟨h.1, by linarith [h.2]⟩
  obtain ⟨w0, hw0, hw0mem⟩ : ∃ w0 : Work.Cusp.E2,
      (∀ i, ((w0 i : ℝ) : AddCircle (1 : ℝ)) = (D v).tor y i) ∧
        (∀ j, 0 ≤ w0 j ∧ w0 j ≤ 1) := by
    refine ⟨!₂[(AddCircle.equivIco (1 : ℝ) 0 ((D v).tor y 0) : ℝ),
      (AddCircle.equivIco (1 : ℝ) 0 ((D v).tor y 1) : ℝ)], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [AddCircle.coe_equivIco]
    · intro j
      fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        exact hico _
  -- (4) the chart data attached to this point
  obtain ⟨c, hcC, hcW⟩ := hCw v w0 hw0mem
  have hpne : (p : Work.Cusp.E2) ≠ 0 := by
    intro h0
    have hz : Work.Cusp.nrm (p : Work.Cusp.E2) = 0 := by rw [h0]; simp [Work.Cusp.nrm]
    linarith
  have hu : 0 ≤ Work.Cusp.u (p : Work.Cusp.E2) ∧ Work.Cusp.u (p : Work.Cusp.E2) < 1 :=
    Work.Cusp.u_mem hpSq hpne
  obtain ⟨kx, hkxK, hkx⟩ := hKx' v (Work.Cusp.u (p : Work.Cusp.E2)) hu.1 (le_of_lt hu.2) w0 hw0mem
  obtain ⟨i8, hi8a, hi8b⟩ := jPin_cover (Work.Cusp.u (p : Work.Cusp.E2)) hu.1 hu.2
  -- (5) the polar point of the junction chart, in its box
  have hrad := jRadial_window v (p : Work.Cusp.E2) w0 hpSq h1
  have hpt : Work.Cusp.polarToUHS v (Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w0) =
      Work.Cusp.ThetaOuter v (p : Work.Cusp.E2) w0 :=
    Work.Cusp.polarToUHS_ThetaPolar v (p : Work.Cusp.E2) w0 h1 hp1
  obtain ⟨z, hzbox⟩ : ∃ z : {q : Work.Cusp.E4 //
      q ∈ Work.RTOwed.jBox v (Work.RTOwed.jPin i8).1 (Work.RTOwed.jPin i8).2
        (Work.RTOwed.jWSet v c) kx (1 / 2)},
      z.1 = Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w0 :=
    ⟨⟨Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w0, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Work.RTOwed.thetaPolar_zero v (p : Work.Cusp.E2) w0]
          linarith [hrad.1]
        · rw [Work.RTOwed.thetaPolar_zero v (p : Work.Cusp.E2) w0]; exact hrad.2
        · rw [Work.RTOwed.thetaPolar_two_three v (p : Work.Cusp.E2) w0]; exact hcW
        · rw [Work.RTOwed.uqOf_thetaPolar v (p : Work.Cusp.E2) w0]; exact hi8a
        · rw [Work.RTOwed.uqOf_thetaPolar v (p : Work.Cusp.E2) w0]; exact hi8b
        · intro i
          rw [hpt, Work.RTOwed.xOf_thetaOuter v (p : Work.Cusp.E2) w0]
          exact hkx i⟩, rfl⟩
  -- (6) the coordinate inclusion of the junction chart takes `z` to `a.incW v (p,y)`
  have hval : Work.RTOwed.jCoordM a v (D v) (Work.RTOwed.jPin i8).1 (Work.RTOwed.jPin i8).2
      (Work.RTOwed.jWSet v c) kx (1 / 2) z = a.incW v (p, y) := by
    rcases lt_or_ge (1 / 2 : ℝ) (Work.Cusp.nrm (p : Work.Cusp.E2)) with hlt | hle
    · refine jCoordM_collar a v (D v) p y w0 hw0 hpSq h1 (Work.RTOwed.jPin i8).1
        (Work.RTOwed.jPin i8).2 (Work.RTOwed.jWSet v c) kx (1 / 2) z hzbox ?_
      rw [hzbox, Work.RTOwed.thetaPolar_zero v (p : Work.Cusp.E2) w0]
      exact Work.Cusp.radial_gt_rJ v (p : Work.Cusp.E2) w0 hlt
    · have heq : Work.Cusp.nrm (p : Work.Cusp.E2) = 1 / 2 := le_antisymm hle h1
      refine jCoordM_inner a v (D v) p y w0 hw0 (Work.RTOwed.jPin i8).1 (Work.RTOwed.jPin i8).2
        (Work.RTOwed.jWSet v c) kx (1 / 2) z hzbox ?_
      rw [hzbox, Work.RTOwed.thetaPolar_zero v (p : Work.Cusp.E2) w0,
        Work.Cusp.radial_half v (p : Work.Cusp.E2) w0 heq]
  -- (7) the index of the constructed point
  refine ⟨e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩, ?_, ?_⟩
  · show (par (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)).1 = v
    rw [show par (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)
        = pinOf ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩ from by
      show pinOf (e.symm (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)) = _
      rw [Equiv.symm_apply_apply]]
  · have hparEq : par (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)
        = ⟨v, { cU := (Work.RTOwed.jPin i8).1, k := (Work.RTOwed.jPin i8).2,
                W := Work.RTOwed.jWSet v c, kx := kx, δ := 1 / 2, hδ := le_refl (1 / 2),
                hW := Work.RTOwed.jWSet_isOpen v c, hsec := Work.RTOwed.jWSet_hsec v c }⟩ := by
      rw [show par (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)
          = pinOf ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩ from by
        show pinOf (e.symm (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)) = _
        rw [Equiv.symm_apply_apply]]
    rw [hparEq]
    refine ⟨z, mem_univ z, ?_⟩
    exact hval


end Work.RTOwed
