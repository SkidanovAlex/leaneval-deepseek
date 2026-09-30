/-
# The junction charts cover the inner part of the collar layer

This file proves `Work.RTOwed.atlas_junction_cover_collar`: there is a *finite* family of junction
charts whose **sources** cover the collar layer `1/2 ≤ ‖p‖∞` of every filling piece, restricted to
its inner radial shell `‖p‖∞ ≤ 51/100`.

It is the *source* form of `Work.RTOwed.jCollar_cover_fin` (the analytic collar cover), in the same
way that `Work.RTOwed.atlas_junction_cover_polar` is the source form of
`Work.RTOwed.jPolar_cover_fin`.  The proof follows `jCollar_cover_fin` line by line; the only
difference is the *radial* bound on the witness point.

## Why the bound `‖p‖∞ ≤ 51/100`

The source of the junction chart `jChart a D v P` of the pin `P` is the image under `jCoordM` of the
box of `P` **cut at the radial coordinate** `rCut = 61/20` (`Work.RTOwed.jBoxR`), not of the whole
box: above `rCut` the collar branch of `jCoordM` can fall under the ceiling `β`, i.e. its value can
be a point of the chimney of the hyperbolic piece rather than of the filling piece
(`Work.RTOwed.rCoordM_mem_range_incW` explains the choice of the cut).

The witness of the collar cover at a point `(p,y)` of layer parameter `t = ‖p‖∞ ≥ 1/2` is the polar
coordinate `z = Θ_v(p,w)` of the point, whose radial coordinate is
`radial v p y = R₀ − log (collarS v p y)` with

  `log (collarS v p y) = (2t−1) log (β(cuspX v (u p) y)) + (1−t)`,

since `log s_J = 1/2`.  With `log β ≥ log β_min = log(3/2)/2 > 1/5` (this is the numerical input
`e^{2/5} < 3/2`, proved below by the Taylor estimate `Real.exp_bound'`) and `2t−1 ≥ 0` one gets

  `log (collarS) ≥ (2t−1)/5 + (1−t) = (4−3t)/5`,

which for `t ≤ 51/100 < 7/12` exceeds `9/20 = R₀ − rCut`.  Hence `radial < rCut` on the shell
`1/2 ≤ ‖p‖∞ ≤ 51/100`, which is exactly the hypothesis of the statement.  (For larger `t` the
radial coordinate grows and the witness leaves `jBoxR`; the collar cover over the *whole* collar
layer is `jCollar_cover_fin`, which uses the uncut box.)
-/
import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.jCollar_cover_fin

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

/-! ### The numerical input `e^{2/5} < 3/2`

This is the only new numerical fact.  The Taylor estimate `Real.exp_bound'` at `x = 2/5` and `n = 3`
gives `e^{2/5} ≤ 1 + 2/5 + (2/5)²/2 + (2/5)³·4/18 = 37/25 + 32/2250 < 3/2`. -/
theorem exp_two_fifths_lt_three_halves : Real.exp ((2:ℝ)/5) < 3/2 := by
  have h := Real.exp_bound' (x := (2:ℝ)/5) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 3, ((2:ℝ)/5)^m / ((m.factorial : ℕ) : ℝ)) = 37/25 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at h
  have h' : Real.exp ((2:ℝ)/5) ≤ 37/25 + ((2:ℝ)/5)^3 * ((3:ℝ) + 1) /
      (((Nat.factorial 3 : ℕ) : ℝ) * 3) := h
  have h'' : (37:ℝ)/25 + ((2:ℝ)/5)^3 * ((3:ℝ) + 1) /
      (((Nat.factorial 3 : ℕ) : ℝ) * 3) < 3/2 := by norm_num
  linarith

/-- **`log β_min ≥ 1/5`**: `β_min = √(3/2)` and `log √(3/2) = log(3/2)/2 ≥ 1/5`, since
`2/5 < log (3/2) ⟺ e^{2/5} < 3/2`. -/
theorem log_betaMin_ge_fifth : (1:ℝ)/5 ≤ Real.log Work.Cusp.betaMin := by
  have hsqrt : Real.log Work.Cusp.betaMin = Real.log (3/2) / 2 := by
    rw [Work.Cusp.betaMin, Real.log_sqrt (by norm_num)]
  have h32 : (2:ℝ)/5 < Real.log (3/2) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr exp_two_fifths_lt_three_halves
  rw [hsqrt]; linarith

/-! ### The radial bound on the inner collar shell -/

/-- **The radial coordinate of the collar shell `1/2 ≤ ‖p‖∞ ≤ 51/100` is below the cut `rCut`.**

`radial v p y = R₀ − log (collarS v p y)` with
`log (collarS v p y) = (2t−1) log β + (1−t)`, `t = ‖p‖∞`, `β = β (cuspX v (u p) y) ≥ β_min`; hence
`log (collarS) ≥ (2t−1)/5 + (1−t) = (4−3t)/5 > 9/20 = R₀ − rCut` for `t ≤ 51/100 < 7/12`. -/
theorem radial_lt_rCut (v : Work.Space.Cusp) (p y : Work.Cusp.E2)
    (h1 : 1/2 ≤ Work.Cusp.nrm p) (h2 : Work.Cusp.nrm p ≤ 51/100) :
    Work.Cusp.radial v p y < Work.RTOwed.rCut := by
  have ht : Work.Cusp.nrm p < 7/12 := by norm_num at h2 ⊢; linarith
  have hlogbge : (1:ℝ)/5 ≤ Real.log (Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u p) y)) :=
    le_trans log_betaMin_ge_fifth (Real.log_le_log (by rw [Work.Cusp.betaMin]; positivity)
      (Work.Cusp.beta_min_le _))
  have hlogS : Real.log (Work.Cusp.collarS v p y) =
      (2 * Work.Cusp.nrm p - 1) * Real.log (Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u p) y))
        + (1 - Work.Cusp.nrm p) := by
    rw [Work.Cusp.collarS, Work.Cusp.collarHeight, Real.log_exp, Work.Cusp.log_sJ]
    ring
  have h2t : 0 ≤ 2 * Work.Cusp.nrm p - 1 := by linarith
  have hkey : (9:ℝ)/20 <
      (2 * Work.Cusp.nrm p - 1) * Real.log (Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u p) y))
        + (1 - Work.Cusp.nrm p) := by
    have hle := mul_le_mul_of_nonneg_left hlogbge h2t
    linarith
  rw [Work.Cusp.radial_collar v p y h1, hlogS]
  unfold Work.Cusp.R0 Work.RTOwed.rCut
  linarith

/-- **The coordinate inclusion of a radial box point lies in the source of the junction chart.**
If `q` is a point of the box of the pin `P` whose radial coordinate `q 0` is below the cut `rCut`
(i.e. `q` lies in `jBoxR a v P`), then `jCoordM` of `q` lies in the source of `jChart a D v P`. -/
theorem jChart_source_of_coordM_jBoxR (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v)
    (q : {q : E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ})
    (hq : (q : E4) ∈ jBoxR a v P) :
    jCoordM a v (D v) P.cU P.k P.W P.kx P.δ q ∈ (jChart a D v P).source := by
  rw [jChart_source]
  exact ⟨q, hq, rfl⟩

/-! ### The cover -/

/-- **The inner collar shell of every cusp is covered by the sources of finitely many junction
charts.** -/
theorem atlas_junction_cover_collar (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v) :
    ∃ (N : ℕ) (par : Fin N → Σ v : Work.Space.Cusp, Work.RTOwed.JPin a v),
      ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
        q ∈ Work.Cusp.collarLayer (a.Torus v) → Work.Cusp.nrm (q.1 : Work.Cusp.E2) ≤ 51/100 →
        ∃ i, (par i).1 = v ∧ a.incW v q ∈
          (Work.RTOwed.jChart a D (par i).1 (par i).2).source := by
  classical
  -- (1) the two finite cover families, one for each cusp
  have hW : ∀ v : Work.Space.Cusp, ∃ C : Finset Work.Cusp.E2, ∀ w : Work.Cusp.E2,
      (∀ j, 0 ≤ w j ∧ w j ≤ 1) → ∃ c ∈ C, Work.Cusp.wOf v w ∈ Work.RTOwed.jWSet v c :=
    fun v => Work.RTOwed.jW_cover v
  choose Cw hCw using hW
  have hKx : ∀ v : Work.Space.Cusp, ∃ K : Finset Work.Cusp.E3, ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ∀ y : Work.Cusp.E2, (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      ∃ kx ∈ K, ∀ j, |Work.Cusp.cuspX v u y j - kx j| < 1 / 2 :=
    fun v => Work.RTOwed.jKx_cover v
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
  intro v q hq hbnd
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
  -- (5b) the new radial bound: the witness lies in the *cut* box `jBoxR`
  have hz0lt : z.1 0 < Work.RTOwed.rCut := by
    rw [hzbox, Work.RTOwed.thetaPolar_zero v (p : Work.Cusp.E2) w0]
    exact radial_lt_rCut v (p : Work.Cusp.E2) w0 h1 hbnd
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
  · let P : Work.RTOwed.JPin a v :=
      { cU := (Work.RTOwed.jPin i8).1, k := (Work.RTOwed.jPin i8).2,
        W := Work.RTOwed.jWSet v c, kx := kx, δ := 1 / 2, hδ := le_refl (1 / 2),
        hW := Work.RTOwed.jWSet_isOpen v c, hsec := Work.RTOwed.jWSet_hsec v c }
    have hparEq : par (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩) = ⟨v, P⟩ := by
      rw [show par (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)
          = pinOf ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩ from by
        show pinOf (e.symm (e ⟨v, (⟨c, hcC⟩, ⟨kx, hkxK⟩, i8)⟩)) = _
        rw [Equiv.symm_apply_apply]]
    rw [hparEq]
    simp only []
    show a.incW v (p, y) ∈ (jChart a D v P).source
    rw [Work.RTOwed.jChart_source]
    refine ⟨z, ⟨z.2, hz0lt⟩, ?_⟩
    exact hval

end Work.RTOwed
