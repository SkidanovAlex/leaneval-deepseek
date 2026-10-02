import Mathlib
import Submission.Work.StemsB.ConnectingMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exactness of the long exact homotopy sequence

Three exactness statements for the connecting map `dMap` of `Submission.Work.StemsB.ConnectingMap`:
at `π_{k+2}(E)`, at `π_{k+2}(B)` and at `π_{k+1}(F)`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.StemsB

noncomputable section

open Classical

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (e₀ : E)

/-! ## Preliminaries -/

/-- The map induced by a constant continuous map is trivial. -/
theorem πmap_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) (n : ℕ)
    (x : X) (a : HomotopyGroup (Fin (n+1)) X x) :
    πmap (ContinuousMap.const X y) n x a = 1 := by
  refine Quotient.inductionOn a (fun γ => ?_)
  rw [πmap_apply_mk, HomotopyGroup.one_def (N := Fin (n+1))]
  apply Quotient.sound
  have h : genLoopMap (ContinuousMap.const X y) (n+1) γ = GenLoop.const := by
    apply GenLoop.ext; intro t; rfl
  rw [h]

/-- The composite `p ∘ fibreIncl` is the constant map at the base point. -/
theorem p_comp_fibreIncl :
    p.comp (fibreIncl p (p e₀)) = ContinuousMap.const (fibre p (p e₀)) (p e₀) := by
  ext x
  exact x.2

/-! ## Exactness at `π_{k+2}(E)` -/

theorem les_exact_E (hrel : ∀ k, HasHLPRel p k) (k : ℕ) :
    Function.MulExact (πmap (fibreIncl p (p e₀)) (k+1) (fibrePoint p e₀))
      (πmap p (k+1) e₀) := by
  intro y
  constructor
  · refine Quotient.inductionOn y ?_
    intro g hy
    have hhom : GenLoop.Homotopic (genLoopMap p (k+2) g) GenLoop.const := by
      have h := hy
      change (⟦genLoopMap p (k+2) g⟧ : HomotopyGroup (Fin (k+2)) B (p e₀))
        = (1 : HomotopyGroup (Fin (k+2)) B (p e₀)) at h
      rw [HomotopyGroup.one_def (N := Fin (k+2))] at h
      exact Quotient.exact h
    obtain ⟨Φ⟩ := hhom
    let H : C((Fin (k+2) → I) × I, B) :=
      ⟨fun q => Φ (q.2, q.1), Φ.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
    have hb : p.comp g.1 = H.comp (zeroIncl (k+2)) := by
      ext v
      show p (g.1 v) = Φ (0, v)
      exact (Φ.map_zero_left v).symm
    have hl : p.comp (ContinuousMap.const (CubeBdry (k+2) × I) e₀) = H.comp (bdryIncl (k+2)) := by
      ext q
      show p e₀ = Φ (q.2, q.1.1)
      exact ((Φ.eq_fst q.2 q.1.2).trans (congrArg p (g.2 q.1.1 q.1.2))).symm
    have hl0 : ∀ (x : CubeBdry (k+2)),
        (ContinuousMap.const (CubeBdry (k+2) × I) e₀) (x, 0) = g.1 x.1 :=
      fun x => (g.2 x.1 x.2).symm
    obtain ⟨Ψ, hΨp, hΨ0, hΨbd⟩ :=
      hrel (k+2) H g.1 hb (ContinuousMap.const (CubeBdry (k+2) × I) e₀) hl hl0
    have hΨp' : ∀ q, p (Ψ q) = H q := fun q => ContinuousMap.congr_fun hΨp q
    have hmem : ∀ v : Fin (k+2) → I, p (Ψ (v, 1)) = p e₀ := by
      intro v
      rw [hΨp']
      show Φ (1, v) = p e₀
      exact Φ.map_one_left v
    have hbdd : ∀ v ∈ Cube.boundary (Fin (k+2)),
        (⟨Ψ (v, 1), hmem v⟩ : fibre p (p e₀)) = fibrePoint p e₀ := by
      intro v hv
      apply Subtype.ext
      show Ψ (v, 1) = e₀
      exact hΨbd ⟨v, hv⟩ 1
    let hgl : GenLoop (Fin (k+2)) (fibre p (p e₀)) (fibrePoint p e₀) :=
      ⟨⟨fun v => ⟨Ψ (v, 1), hmem v⟩,
        Continuous.subtype_mk (Ψ.continuous.comp (continuous_id.prodMk continuous_const)) _⟩,
        hbdd⟩
    refine ⟨⟦hgl⟧, ?_⟩
    rw [πmap_apply_mk]
    apply Quotient.sound
    refine ⟨ContinuousMap.HomotopyWith.mk
      (ContinuousMap.Homotopy.mk ⟨fun q => Ψ (q.2, σ q.1), ?_⟩ ?_ ?_) ?_⟩
    · exact Ψ.continuous.comp (continuous_snd.prodMk
        (unitInterval.continuous_symm.comp continuous_fst))
    · intro v
      show Ψ (v, σ 0) = Ψ (v, 1)
      rw [unitInterval.symm_zero]
    · intro v
      show Ψ (v, σ 1) = g.1 v
      rw [unitInterval.symm_one, hΨ0]
    · intro s v hv
      show Ψ (v, σ s) = Ψ (v, 1)
      rw [hΨbd ⟨v, hv⟩ (σ s), hΨbd ⟨v, hv⟩ 1]
      rfl
  · rintro ⟨z, rfl⟩
    refine Quotient.inductionOn z (fun h => ?_)
    change (⟦genLoopMap p (k+2) (genLoopMap (fibreIncl p (p e₀)) (k+2) h)⟧
      : HomotopyGroup (Fin (k+2)) B (p e₀)) = (1 : HomotopyGroup (Fin (k+2)) B (p e₀))
    have hc : genLoopMap p (k+2) (genLoopMap (fibreIncl p (p e₀)) (k+2) h) = GenLoop.const := by
      apply GenLoop.ext
      intro v
      show p ((h v).1) = p e₀
      exact (h v).2
    rw [HomotopyGroup.one_def (N := Fin (k+2))]
    apply Quotient.sound
    exact Eq.mpr (congrArg (fun x => GenLoop.Homotopic x GenLoop.const) hc)
      (GenLoop.Homotopic.refl GenLoop.const)


/-! ## Exactness at `π_{k+1}(F)` -/

theorem les_exact_F (hrel : ∀ k, HasHLPRel p k) (k : ℕ) :
    Function.MulExact (dMap p e₀ hrel k) (πmap (fibreIncl p (p e₀)) k (fibrePoint p e₀)) := by
  intro y
  constructor
  · -- a class in the kernel of `fibreIncl_*` is in the image of the connecting map
    refine Quotient.inductionOn y (fun h hy => ?_)
    have hhom : GenLoop.Homotopic (genLoopMap (fibreIncl p (p e₀)) (k+1) h) GenLoop.const := by
      have hh := hy
      change (⟦genLoopMap (fibreIncl p (p e₀)) (k+1) h⟧
        : HomotopyGroup (Fin (k+1)) E ((fibreIncl p (p e₀)) (fibrePoint p e₀)))
        = (1 : HomotopyGroup (Fin (k+1)) E ((fibreIncl p (p e₀)) (fibrePoint p e₀))) at hh
      rw [HomotopyGroup.one_def (N := Fin (k+1))] at hh
      exact Quotient.exact hh
    obtain ⟨Ψ⟩ := hhom
    have hΨ0 : ∀ v : Fin (k+1) → I, Ψ (0, v) = (fibreIncl p (p e₀)) (h v) :=
      fun v => Ψ.map_zero_left v
    have hΨ1 : ∀ v : Fin (k+1) → I, Ψ (1, v) = fibreIncl p (p e₀) (fibrePoint p e₀) :=
      fun v => Ψ.map_one_left v
    have hΨbd : ∀ (s : I) (v : Fin (k+1) → I), v ∈ Cube.boundary (Fin (k+1)) →
        Ψ (s, v) = (fibreIncl p (p e₀)) (h v) := fun s v hv => Ψ.eq_fst s hv
    -- the map on the base induced by `Ψ`
    let W : C((Fin (k+1) → I) × I, B) :=
      ⟨fun q => p (Ψ (q.2, q.1)), p.continuous.comp (Ψ.continuous.comp
        (continuous_snd.prodMk continuous_fst))⟩
    have hW : ∀ (v : Fin (k+1) → I) (s : I), W (v, s) = p (Ψ (s, v)) := fun v s => rfl
    -- the based cube
    have hfW : ∀ u ∈ Cube.boundary (Fin (k+2)), W (Fin.tail u, σ (u 0)) = p e₀ := by
      intro u hu
      by_cases hv : Fin.tail u ∈ Cube.boundary (Fin (k+1))
      · rw [hW, hΨbd (σ (u 0)) (Fin.tail u) hv]
        exact (h (Fin.tail u)).2
      · have h0 : u 0 = 0 ∨ u 0 = 1 := by
          obtain ⟨i, hi⟩ := hu
          cases i using Fin.cases with
          | zero => exact hi
          | succ j => exact absurd ⟨j, by simpa [Fin.tail] using hi⟩ hv
        rcases h0 with h0 | h0
        · rw [h0, unitInterval.symm_zero, hW, hΨ1 (Fin.tail u)]
          rfl
        · rw [h0, unitInterval.symm_one, hW, hΨ0 (Fin.tail u)]
          exact (h (Fin.tail u)).2
    let fW : GenLoop (Fin (k+2)) B (p e₀) :=
      ⟨⟨fun u => W (Fin.tail u, σ (u 0)), W.continuous.comp
        (((continuous_finTail (k+1)).comp continuous_id).prodMk
          (unitInterval.continuous_symm.comp (continuous_apply 0)))⟩, hfW⟩
    -- the lift of its cube
    let G2 : C((Fin (k+1) → I) × I, E) :=
      ⟨fun q => Ψ (σ q.2, q.1), Ψ.continuous.comp
        ((unitInterval.continuous_symm.comp continuous_snd).prodMk continuous_fst)⟩
    have hG2 : ∀ (v : Fin (k+1) → I) (t : I), G2 (v, t) = Ψ (σ t, v) := fun v t => rfl
    have hG2_lift : p.comp G2 = cubeReindex fW := by
      ext q
      show p (G2 q) = cubeReindex fW q
      rw [hG2 q.1 q.2]
      show p (Ψ (σ q.2, q.1)) = W (q.1, σ q.2)
      rw [hW]
    have hG2_0 : ∀ v : Fin (k+1) → I, G2 (v, 0) = e₀ := by
      intro v
      rw [hG2, unitInterval.symm_zero, hΨ1 v]
      rfl
    have hG2_bd : ∀ (v : CubeBdry (k+1)) (t : I), G2 (v.1, t) = e₀ := by
      intro v t
      rw [hG2, hΨbd (σ t) v.1 v.2, show h v.1 = fibrePoint p e₀ from h.2 v.1 v.2]
      rfl
    have htop : GenLoop.Homotopic (dGenLoop p e₀ hrel fW) h := by
      have h1 := liftUniqueness p e₀ hrel (k+1) (cubeReindex fW) (cubeReindex_zero fW)
        (cubeReindex_one fW) (dLift p e₀ hrel fW) G2 (dLift_spec p e₀ hrel fW).1
        hG2_lift (dLift_spec p e₀ hrel fW).2.1 hG2_0
        (dLift_spec p e₀ hrel fW).2.2 hG2_bd
      have h2 : topFaceG (k+1) (cubeReindex fW) (cubeReindex_one fW) G2 hG2_lift hG2_bd
          = h := by
        apply GenLoop.ext
        intro v
        apply Subtype.ext
        show G2 (v, 1) = (h v).1
        rw [hG2, unitInterval.symm_one, hΨ0 v]
        rfl
      rw [h2] at h1
      exact h1
    exact ⟨⟦fW⟧, (dFun_mk p e₀ hrel fW).trans (Quotient.sound htop)⟩
  · -- the connecting map kills the image of `π_{k+2}(E)`
    rintro ⟨z, rfl⟩
    refine Quotient.inductionOn z (fun f => ?_)
    change (πmap (fibreIncl p (p e₀)) k (fibrePoint p e₀))
      (dFun p e₀ hrel k ⟦f⟧) = (1 : HomotopyGroup (Fin (k+1)) E ((fibreIncl p (p e₀)) (fibrePoint p e₀)))
    rw [dFun_mk]
    change (⟦genLoopMap (fibreIncl p (p e₀)) (k+1) (dGenLoop p e₀ hrel f)⟧
      : HomotopyGroup (Fin (k+1)) E ((fibreIncl p (p e₀)) (fibrePoint p e₀)))
      = (1 : HomotopyGroup (Fin (k+1)) E ((fibreIncl p (p e₀)) (fibrePoint p e₀)))
    rw [HomotopyGroup.one_def (N := Fin (k+1))]
    apply Quotient.sound
    -- `dLift f` is a based null-homotopy in `E` of the loop `dGenLoop f`
    let G : C((Fin (k+1) → I) × I, E) := dLift p e₀ hrel f
    have hG0 : ∀ v : Fin (k+1) → I, G (v, 0) = e₀ := (dLift_spec p e₀ hrel f).2.1
    have hGbd : ∀ (v : CubeBdry (k+1)) (t : I), G (v.1, t) = e₀ := (dLift_spec p e₀ hrel f).2.2
    refine ⟨ContinuousMap.HomotopyWith.mk
      (ContinuousMap.Homotopy.mk ⟨fun q => G (q.2, σ q.1), ?_⟩ ?_ ?_) ?_⟩
    · exact G.continuous.comp (continuous_snd.prodMk
        (unitInterval.continuous_symm.comp continuous_fst))
    · intro v
      show G (v, σ 0) = ((dGenLoop p e₀ hrel f) v).1
      rw [unitInterval.symm_zero, dGenLoop_apply_coe]
    · intro v
      show G (v, σ 1) = e₀
      rw [unitInterval.symm_one, hG0 v]
    · intro s v hv
      show G (v, σ s) = ((dGenLoop p e₀ hrel f) v).1
      rw [hGbd ⟨v, hv⟩ (σ s), dGenLoop_apply_coe, hGbd ⟨v, hv⟩ 1]


/-- `Fin.cons` in terms of `Function.update`. -/
theorem cons_tail_update {n : ℕ} (c : I) (u : Fin (n+1) → I) :
    Fin.cons c (Fin.tail u) = Function.update u 0 c := by
  funext j
  cases j using Fin.cases with
  | zero => rw [Function.update_apply, if_pos rfl, Fin.cons_zero]
  | succ i => rw [Function.update_apply, if_neg (Fin.succ_ne_zero i), Fin.cons_succ]; rfl

/-! ## Exactness at `π_{k+2}(B)` -/

theorem les_exact_B (hrel : ∀ k, HasHLPRel p k) (k : ℕ) :
    Function.MulExact (πmap p (k+1) e₀) (dMap p e₀ hrel k) := by
  intro y
  constructor
  · -- if the connecting map kills `y`, it comes from a based loop of `E`
    refine Quotient.inductionOn y (fun f hy => ?_)
    have hy' : GenLoop.Homotopic (dGenLoop p e₀ hrel f) (GenLoop.const :
        GenLoop (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀)) := by
      have hh := hy
      change (dFun p e₀ hrel k ⟦f⟧)
        = (1 : HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀)) at hh
      rw [dFun_mk, HomotopyGroup.one_def (N := Fin (k+1))] at hh
      exact Quotient.exact hh
    obtain ⟨Ξ⟩ := hy'
    have hΞ0 : ∀ v : Fin (k+1) → I, Ξ (0, v) = (dGenLoop p e₀ hrel f).1 v :=
      fun v => Ξ.map_zero_left v
    have hΞ1 : ∀ v : Fin (k+1) → I, Ξ (1, v) = fibrePoint p e₀ :=
      fun v => Ξ.map_one_left v
    have hΞbd : ∀ (s : I) (v : Fin (k+1) → I), v ∈ Cube.boundary (Fin (k+1)) →
        Ξ (s, v) = (dGenLoop p e₀ hrel f).1 v := fun s v hv => Ξ.eq_fst s hv
    have hΞe : ∀ (s : I) (v : Fin (k+1) → I), v ∈ Cube.boundary (Fin (k+1)) →
        (Ξ (s, v)).1 = e₀ := by
      intro s v hv
      exact (Subtype.ext_iff.mp (hΞbd s v hv)).trans
        ((dGenLoop_apply_coe p e₀ hrel f v).trans ((dLift_spec p e₀ hrel f).2.2 ⟨v, hv⟩ 1))
    -- the based loop of `E` obtained by gluing the canonical lift with the null-homotopy
    have hg_cont : Continuous fun u : Fin (k+2) → I =>
        if (u 0 : ℝ) ≤ 1/2
          then (dLift p e₀ hrel f) (Fin.tail u, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))
          else (Ξ (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), Fin.tail u)).1 := by
      have hcoord : Continuous fun u : Fin (k+2) → I => (u 0 : ℝ) :=
        continuous_subtype_val.comp (continuous_apply 0)
      have htail : Continuous fun u : Fin (k+2) → I => Fin.tail u := continuous_finTail (k+1)
      have hp1 : Continuous fun u : Fin (k+2) → I =>
          (dLift p e₀ hrel f) (Fin.tail u, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))) :=
        (dLift p e₀ hrel f).continuous.comp (htail.prodMk
          (continuous_projIcc.comp (continuous_const.mul hcoord)))
      have hp2 : Continuous fun u : Fin (k+2) → I =>
          (Ξ (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), Fin.tail u)).1 :=
        (continuous_subtype_val.comp Ξ.continuous).comp
          ((continuous_projIcc.comp ((continuous_const.mul hcoord).sub continuous_const)).prodMk htail)
      apply Continuous.if
      · intro u hu
        have hclosed : IsClosed {u : Fin (k+2) → I | (u 0 : ℝ) ≤ 1/2} :=
          isClosed_Iic.preimage hcoord
        have hule : (u 0 : ℝ) ≤ 1/2 := by
          have h1 : u ∈ closure {u : Fin (k+2) → I | (u 0 : ℝ) ≤ 1/2} := hu.1
          rwa [hclosed.closure_eq] at h1
        have hue : (u 0 : ℝ) = 1/2 := by
          refine le_antisymm hule ?_
          by_contra hlt
          have hlt' : (u 0 : ℝ) < 1/2 := lt_of_not_ge hlt
          have : u ∈ interior {u : Fin (k+2) → I | (u 0 : ℝ) ≤ 1/2} := by
            apply mem_interior_iff_mem_nhds.mpr
            have hop : IsOpen {u : Fin (k+2) → I | (u 0 : ℝ) < 1/2} :=
              isOpen_lt hcoord continuous_const
            exact Filter.mem_of_superset (hop.mem_nhds hlt')
              (fun y hy => le_of_lt (show (y 0 : ℝ) < 1/2 from hy))
          exact hu.2 this
        have h2 : (2:ℝ) * (1/2) = 1 := by norm_num
        have h3 : (2:ℝ) * ((0:I):ℝ) = 0 := by simp
        have h4 : (2:ℝ) * ((1:I):ℝ) - 1 = 1 := by norm_num
        rw [show Set.projIcc (0:ℝ) 1 zero_le_one (2 * (u 0 : ℝ)) = 1 by
              rw [hue, h2]; exact projIcc_one',
            show Set.projIcc (0:ℝ) 1 zero_le_one (2 * (u 0 : ℝ) - 1) = 0 by
              rw [hue, h2, show (1:ℝ) - 1 = 0 by norm_num]; exact projIcc_zero',
            hΞ0 (Fin.tail u)]
        rfl
      · exact hp1
      · exact hp2
    let gcube : C(Fin (k+2) → I, E) :=
      ⟨fun u => if (u 0 : ℝ) ≤ 1/2
          then (dLift p e₀ hrel f) (Fin.tail u, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))
          else (Ξ (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), Fin.tail u)).1, hg_cont⟩
    have hgcube : ∀ u : Fin (k+2) → I, gcube u = if (u 0 : ℝ) ≤ 1/2
        then (dLift p e₀ hrel f) (Fin.tail u, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))
        else (Ξ (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), Fin.tail u)).1 := fun u => rfl
    have hg_bd : ∀ u ∈ Cube.boundary (Fin (k+2)), gcube u = e₀ := by
      intro u hu
      by_cases hv : Fin.tail u ∈ Cube.boundary (Fin (k+1))
      · rw [hgcube]
        by_cases h : (u 0 : ℝ) ≤ 1/2
        · rw [if_pos h]
          exact (dLift_spec p e₀ hrel f).2.2 ⟨Fin.tail u, hv⟩ _
        · rw [if_neg h]
          exact hΞe _ (Fin.tail u) hv
      · have h0 : u 0 = 0 ∨ u 0 = 1 := by
          obtain ⟨i, hi⟩ := hu
          cases i using Fin.cases with
          | zero => exact hi
          | succ j => exact absurd ⟨j, by simpa [Fin.tail] using hi⟩ hv
        rcases h0 with h0 | h0
        · rw [hgcube, h0]
          rw [if_pos (by norm_num : (((0:I):ℝ) ≤ 1/2))]
          rw [show (2:ℝ) * ((0:I):ℝ) = 0 by simp, projIcc_zero']
          exact (dLift_spec p e₀ hrel f).2.1 _
        · rw [hgcube, h0]
          rw [if_neg (by norm_num : ¬ (((1:I):ℝ) ≤ 1/2))]
          rw [show (2:ℝ) * ((1:I):ℝ) - 1 = 1 by norm_num, projIcc_one']
          exact Subtype.ext_iff.mp (hΞ1 (Fin.tail u))
    let g : GenLoop (Fin (k+2)) E e₀ := ⟨gcube, hg_bd⟩
    -- `p ∘ g` is the "collapsed" cube `transAt 0 f const`
    have hcompat : p.comp g.1
        = (GenLoop.transAt (0 : Fin (k+2)) f (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))).1 := by
      ext u
      show p (gcube u)
        = (GenLoop.transAt (0 : Fin (k+2)) f (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))) u
      rw [hgcube u]
      rw [show (GenLoop.transAt (0 : Fin (k+2)) f (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))) u
          = (if (u 0 : ℝ) ≤ 1/2
              then f (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))
              else (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))
                (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)))) from
        GenLoop.transAt_apply _ _ _ u]
      by_cases h : (u 0 : ℝ) ≤ 1/2
      · rw [if_pos h, if_pos h]
        rw [show p ((dLift p e₀ hrel f) (Fin.tail u, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))
              = f (Fin.cons (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))) (Fin.tail u)) from
            ContinuousMap.congr_fun (dLift_spec p e₀ hrel f).1 _]
        rw [cons_tail_update]
      · rw [if_neg h, if_neg h]
        exact (Ξ (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), Fin.tail u)).2
    refine ⟨⟦g⟧, ?_⟩
    change (⟦genLoopMap p (k+2) g⟧ : HomotopyGroup (Fin (k+2)) B (p e₀)) = ⟦f⟧
    have hpq : genLoopMap p (k+2) g
        = (GenLoop.transAt (0 : Fin (k+2)) f (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))) := by
      apply GenLoop.ext
      intro u
      exact ContinuousMap.congr_fun hcompat u
    rw [hpq]
    have htrans : (⟦GenLoop.transAt (0 : Fin (k+2)) f
          (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))⟧
        : HomotopyGroup (Fin (k+2)) B (p e₀)) = ⟦f⟧ := by
      rw [← HomotopyGroup.mul_spec (i := (0 : Fin (k+2)))
        (p := (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))) (q := f)]
      rw [show (⟦(GenLoop.const : GenLoop (Fin (k+2)) B (p e₀))⟧
          : HomotopyGroup (Fin (k+2)) B (p e₀)) = (1 : HomotopyGroup (Fin (k+2)) B (p e₀)) from
        (HomotopyGroup.one_def (N := Fin (k+2))).symm]
      exact one_mul (M := HomotopyGroup (Fin (k+2)) B (p e₀)) ⟦f⟧
    exact htrans
  · -- the connecting map kills the image of `π_{k+2}(E)`
    rintro ⟨z, rfl⟩
    refine Quotient.inductionOn z (fun g => ?_)
    change (dFun p e₀ hrel k) (πmap p (k+1) e₀ ⟦g⟧)
      = (1 : HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀))
    change (dFun p e₀ hrel k) (⟦genLoopMap p (k+2) g⟧ : HomotopyGroup (Fin (k+2)) B (p e₀))
      = (1 : HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀))
    rw [dFun_mk, HomotopyGroup.one_def (N := Fin (k+1))]
    let G2 : C((Fin (k+1) → I) × I, E) :=
      ⟨fun q => g (Fin.cons q.2 q.1), g.1.continuous.comp (consCM (k+1)).continuous⟩
    have hG2_lift : p.comp G2 = cubeReindex (genLoopMap p (k+2) g) := by
      ext q
      show p (g (Fin.cons q.2 q.1)) = cubeReindex (genLoopMap p (k+2) g) q
      rw [cubeReindex_apply]
      rfl
    have hG2_0 : ∀ v : Fin (k+1) → I, G2 (v, 0) = e₀ :=
      fun v => g.2 (Fin.cons 0 v) (cons_zero_mem_boundary v)
    have hG2_bd : ∀ (v : CubeBdry (k+1)) (t : I), G2 (v.1, t) = e₀ :=
      fun v t => g.2 (Fin.cons t v.1) (cons_mem_boundary v.2)
    have h1 := liftUniqueness p e₀ hrel (k+1) (cubeReindex (genLoopMap p (k+2) g))
      (cubeReindex_zero _) (cubeReindex_one _) (dLift p e₀ hrel (genLoopMap p (k+2) g)) G2
      (dLift_spec p e₀ hrel (genLoopMap p (k+2) g)).1 hG2_lift
      (dLift_spec p e₀ hrel (genLoopMap p (k+2) g)).2.1 hG2_0
      (dLift_spec p e₀ hrel (genLoopMap p (k+2) g)).2.2 hG2_bd
    have h2 : topFaceG (k+1) (cubeReindex (genLoopMap p (k+2) g)) (cubeReindex_one _)
        G2 hG2_lift hG2_bd
        = (GenLoop.const : GenLoop (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀)) := by
      apply GenLoop.ext
      intro v
      apply Subtype.ext
      show g (Fin.cons 1 v) = (fibrePoint p e₀).1
      exact (g.2 (Fin.cons 1 v) (cons_one_mem_boundary v)).trans rfl
    rw [h2] at h1
    exact Quotient.sound h1

end

end Work.StemsB
