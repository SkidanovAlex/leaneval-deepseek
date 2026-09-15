import ChallengeDeps
import Submission.Commons.Analysis.Complex.zero_set_analyticOnNhd_closedBall_finite

open MeasureTheory Metric Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The real zero set of a non-zero holomorphic function on a polydisk is null

`Submission.Commons.Analysis.Complex.zero_set_analyticOnNhd_closedBall_finite` gives the
one-dimensional statement.  Here we deduce the `d`-dimensional one by induction, slicing the
first coordinate and applying Fubini.  This is needed in order to convert the Cartan
(two constants) lower bound `log ‖G z‖ ≥ level` — which in Lean is vacuous at the zeros of `G`
because `Real.log 0 = 0` — into the exponential bound `‖G z‖ ≥ exp level`.
-/

namespace Submission.FUP

variable {m : ℕ}

/-! ### The affine slice maps -/

/-- The complex-linear map `w ↦ Fin.cons 0 w`. -/
noncomputable def sliceLM (m : ℕ) : (Fin m → ℂ) →L[ℂ] (Fin (m+1) → ℂ) :=
  ContinuousLinearMap.pi (fun j : Fin (m+1) =>
    Fin.cases (0 : (Fin m → ℂ) →L[ℂ] ℂ) (fun i : Fin m => ContinuousLinearMap.proj i) j)

lemma sliceLM_apply (m : ℕ) (w : Fin m → ℂ) : sliceLM m w = Fin.cons (0:ℂ) w := by
  ext j
  induction j using Fin.cases with
  | zero => simp [sliceLM]
  | succ i => simp [sliceLM]

lemma insertNth_eq_cons (m : ℕ) (t : ℂ) (w : Fin m → ℂ) :
    Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 t w = Fin.cons t w := by
  ext j
  induction j using Fin.cases with
  | zero => rw [Fin.cons_zero, Fin.insertNth_apply_same]
  | succ i => rw [Fin.cons_succ, ← Fin.succAbove_zero_apply i, Fin.insertNth_apply_succAbove]

lemma cons_eq_add (m : ℕ) (t : ℂ) (w : Fin m → ℂ) :
    Fin.cons t w = sliceLM m w + Fin.cons t (0 : Fin m → ℂ) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [sliceLM_apply]
  | succ i => simp [sliceLM_apply]

/-- The complex-linear map `u ↦ Fin.cons u 0`. -/
noncomputable def consLM (m : ℕ) : ℂ →L[ℂ] (Fin (m+1) → ℂ) :=
  ContinuousLinearMap.pi (fun j : Fin (m+1) =>
    Fin.cases (ContinuousLinearMap.id ℂ ℂ) (fun _ : Fin m => 0) j)

lemma consLM_apply (m : ℕ) (u : ℂ) : consLM m u = Fin.cons u (0 : Fin m → ℂ) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [consLM]
  | succ i => simp [consLM]

/-- `Fin.insertNth 0` is an affine map. -/
lemma insertNth_eq_consLM_add (m : ℕ) (u : ℂ) (v : Fin m → ℂ) :
    Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u v = consLM m u + Fin.cons (0:ℂ) v := by
  rw [insertNth_eq_cons, consLM_apply]
  ext j
  induction j using Fin.cases with
  | zero => simp
  | succ i => simp

/-- The slice map `v ↦ Fin.insertNth 0 u v` is entire. -/
lemma analyticOnNhd_insertNth (m : ℕ) (u : ℂ) (s : Set (Fin m → ℂ)) :
    AnalyticOnNhd ℂ (fun v : Fin m → ℂ => Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u v) s := by
  have hfun : (fun v : Fin m → ℂ => Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u v)
      = fun v => sliceLM m v + Fin.cons u (0 : Fin m → ℂ) := by
    funext v; rw [insertNth_eq_cons, cons_eq_add]
  intro v _
  rw [hfun]
  have h := ((sliceLM m).analyticAt v).add (analyticAt_const (v := Fin.cons u (0 : Fin m → ℂ)))
  have h' : (fun v => sliceLM m v + Fin.cons u (0 : Fin m → ℂ))
      = (⇑(sliceLM m) + fun _ => Fin.cons u (0 : Fin m → ℂ)) := by funext v; rfl
  rw [h']
  exact h

/-- The map `u ↦ Fin.insertNth 0 u v` is entire. -/
lemma analyticOnNhd_consLM (m : ℕ) (v : Fin m → ℂ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun u : ℂ => Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u v) s := by
  have hfun : (fun u : ℂ => Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u v)
      = fun u => consLM m u + Fin.cons (0:ℂ) v := by
    funext u; rw [insertNth_eq_consLM_add]
  intro u _
  rw [hfun]
  have h := ((consLM m).analyticAt u).add (analyticAt_const (v := Fin.cons (0:ℂ) v))
  have h' : (fun u => consLM m u + Fin.cons (0:ℂ) v)
      = (⇑(consLM m) + fun _ => Fin.cons (0:ℂ) v) := by funext u; rfl
  rw [h']
  exact h

/-- Inserting a real value commutes with the coercion `ℝ → ℂ` in each coordinate. -/
lemma insertNth_coe (m : ℕ) (t : ℝ) (w : Fin m → ℝ) :
    (fun j : Fin (m+1) => ((Fin.insertNth (α := fun _ : Fin (m+1) => ℝ) 0 t w j : ℝ) : ℂ))
      = Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t : ℂ) (fun j => (w j : ℂ)) := by
  ext j
  induction j using Fin.cases with
  | zero => rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  | succ i => rw [← Fin.succAbove_zero_apply i, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove]

/-- Inserting the coordinates of a point of the polydisk stays in the polydisk. -/
lemma norm_insertNth_le (m : ℕ) {u : ℂ} (hu : ‖u‖ ≤ 1) {v : Fin m → ℂ}
    (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u v‖ ≤ 1 := by
  rw [insertNth_eq_cons, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  induction j using Fin.cases with
  | zero => simpa using hu
  | succ i => simpa using hv i

/-- The inverse of the `Fin (m+1) → ℝ ≃ ℝ × (Fin m → ℝ)` decomposition is `Fin.insertNth`. -/
lemma piFinSuccAbove_symm_insertNth (m : ℕ) (t : ℝ) (x' : Fin m → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm (t, x')
      = Fin.insertNth (α := fun _ : Fin (m+1) => ℝ) 0 t x' := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext j
  rw [Fin.insertNthEquiv_apply]

/-- Membership of a "sliced" point in the box. -/
lemma insertNth_mem_box (m : ℕ) (t : ℝ) (x' : Fin m → ℝ) :
    (∀ j : Fin (m+1), |Fin.insertNth (α := fun _ : Fin (m+1) => ℝ) 0 t x' j| ≤ 1)
      ↔ |t| ≤ 1 ∧ ∀ i, |x' i| ≤ 1 := by
  constructor
  · intro h
    refine ⟨?_, fun i => ?_⟩
    · have h0 := h 0; rwa [Fin.insertNth_apply_same] at h0
    · have hi := h i.succ
      rwa [← Fin.succAbove_zero_apply i, Fin.insertNth_apply_succAbove] at hi
  · rintro ⟨h1, h2⟩ j
    induction j using Fin.cases with
    | zero => rwa [Fin.insertNth_apply_same]
    | succ i => rw [← Fin.succAbove_zero_apply i, Fin.insertNth_apply_succAbove]; exact h2 i

/-! ### The clipped complexification -/

/-- The coordinatewise projection onto the box `[-1,1]^d`. -/
noncomputable def clipBox (d : ℕ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => max (-1) (min 1 (x i))

lemma continuous_clipBox (d : ℕ) : Continuous (clipBox d) := by
  unfold clipBox; fun_prop

lemma clipBox_abs_le (d : ℕ) (x : Fin d → ℝ) (i : Fin d) : |clipBox d x i| ≤ 1 := by
  simp only [clipBox]
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clipBox_eq_self {d : ℕ} {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ 1) : clipBox d x = x := by
  funext i
  have h := abs_le.mp (hx i)
  simp only [clipBox]
  rw [min_eq_right h.2, max_eq_right h.1]

/-- The "clipped" complexification: continuous on *all* of `Fin d → ℝ`, and agreeing with
`x ↦ G (x : Fin d → ℂ)` on the box. -/
noncomputable def clipG {d : ℕ} (G : (Fin d → ℂ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  G (fun i => ((clipBox d x i : ℝ) : ℂ))

lemma clipG_of_mem {d : ℕ} (G : (Fin d → ℂ) → ℂ) {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    clipG G x = G (fun i => (x i : ℂ)) := by
  simp only [clipG, clipBox_eq_self hx]

lemma continuous_clipG {d : ℕ} {G : (Fin d → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1)) : Continuous (clipG G) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hcoe : Continuous (fun y : Fin d → ℝ => (fun i => (y i : ℂ))) :=
    continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))
  have hcomp : ContinuousAt (fun y : Fin d → ℝ => (fun i => ((clipBox d y i : ℝ) : ℂ))) x :=
    hcoe.continuousAt.comp (continuous_clipBox d).continuousAt
  have h3 : (fun i => ((clipBox d x i : ℝ) : ℂ)) ∈ Metric.closedBall (0 : Fin d → ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simpa using clipBox_abs_le d x i
  have h4 : clipG G = fun y : Fin d → ℝ => G (fun i => ((clipBox d y i : ℝ) : ℂ)) := rfl
  rw [h4]
  exact ((hG _ h3).continuousAt).comp hcomp

end Submission.FUP

namespace Submission.FUP

/-- **The real zero set of a non-zero holomorphic function on the unit polydisk is null.** -/
theorem volume_zero_set_pi : ∀ d : ℕ, ∀ (G : (Fin d → ℂ) → ℂ),
    AnalyticOnNhd ℂ G (Metric.closedBall 0 1) →
    (∃ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧ G z ≠ 0) →
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      {x : Fin d → ℝ | (∀ i, |x i| ≤ 1) ∧ G (fun i => (x i : ℂ)) = 0} = 0
  | 0, G, _hG, hne => by
      obtain ⟨z, _, hz0⟩ := hne
      have hempty : {x : Fin 0 → ℝ | (∀ i, |x i| ≤ 1) ∧ G (fun i => (x i : ℂ)) = 0} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨-, hx2⟩
        have hEq : (fun i : Fin 0 => (x i : ℂ)) = z := Subsingleton.elim _ _
        rw [hEq] at hx2
        exact hz0 hx2
      rw [hempty, measure_empty]
  | m+1, G, hG, hne => by
      classical
      obtain ⟨z, hz1, hz2⟩ := hne
      set Z : Set (Fin (m+1) → ℝ) :=
        {x | (∀ i, |x i| ≤ 1) ∧ G (fun i => (x i : ℂ)) = 0} with hZdef
      have hZeq : Z = {x : Fin (m+1) → ℝ | ∀ i, |x i| ≤ 1} ∩ (clipG G) ⁻¹' {0} := by
        ext x
        rw [hZdef]
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [clipG_of_mem G h1]; exact h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [clipG_of_mem G h1] at h2; exact h2⟩
      have hZmeas : MeasurableSet Z := by
        rw [hZeq]
        refine MeasurableSet.inter ?_ ?_
        · rw [show {x : Fin (m+1) → ℝ | ∀ i, |x i| ≤ 1}
              = ⋂ i, (fun x : Fin (m+1) → ℝ => x i) ⁻¹' (Set.Icc (-1:ℝ) 1) from by
            ext x; simp [abs_le]]
          exact MeasurableSet.iInter fun i =>
            measurableSet_Icc.preimage (continuous_apply i).measurable
        · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℂ))
            (continuous_clipG hG).measurable
      set w0 : Fin m → ℂ := fun j => z (Fin.succ j) with hw0def
      have hw0 : ∀ i : Fin m, ‖w0 i‖ ≤ 1 := fun i => hz1 (Fin.succ i)
      have hw0ins : Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (z 0) w0 = z := by
        ext j
        induction j using Fin.cases with
        | zero => rw [Fin.insertNth_apply_same]
        | succ i => rw [← Fin.succAbove_zero_apply i, Fin.insertNth_apply_succAbove]; rfl
      have hw0ne : G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (z 0) w0) ≠ 0 := by
        rw [hw0ins]; exact hz2
      set Es : Set ℝ := {t | |t| ≤ 1 ∧
        G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) w0) = 0} with hEsdef
      have hEsfin : Es.Finite := by
        have hphi : AnalyticOnNhd ℂ (fun u : ℂ =>
            G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u w0)) (Metric.closedBall 0 1) := by
          refine hG.comp (analyticOnNhd_consLM m w0 _) ?_
          intro u hu
          rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
          exact norm_insertNth_le m hu hw0
        have hne' : ∃ u ∈ Metric.closedBall (0 : ℂ) 1,
            G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 u w0) ≠ 0 :=
          ⟨z 0, by rw [Metric.mem_closedBall, dist_zero_right]; exact hz1 0, hw0ne⟩
        have h := Commons.Analysis.Complex.zero_set_analyticOnNhd_closedBall_finite (R := 1)
          (by norm_num) hphi hne'
        rw [hEsdef]
        exact h.subset fun x hx => ⟨hx.1, hx.2⟩
      have hEsmeas : MeasurableSet Es := hEsfin.measurableSet
      have hEszero : (MeasureTheory.volume : MeasureTheory.Measure ℝ) Es = 0 :=
        hEsfin.measure_zero _
      let e : (Fin (m+1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
      have hemp : MeasurePreserving e (MeasureTheory.volume : MeasureTheory.Measure (Fin (m+1) → ℝ))
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
        have h := measurePreserving_piFinSuccAbove
          (fun _ : Fin (m+1) => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0
        simpa only [MeasureTheory.volume_pi] using h
      have himg : e '' Z = e.symm ⁻¹' Z := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
          exact hx
        · intro hy
          exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      have hZmeas' : MeasurableSet (e '' Z) := himg ▸ (e.symm.measurable hZmeas)
      have hfub : (MeasureTheory.volume : MeasureTheory.Measure (Fin (m+1) → ℝ)) Z
          = ∫⁻ t, (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
              {x' : Fin m → ℝ | (t, x') ∈ e '' Z} := by
        have h1 : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
              (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) (e '' Z)
            = (MeasureTheory.volume : MeasureTheory.Measure (Fin (m+1) → ℝ)) Z := by
          rw [← hemp.map_eq, Measure.map_apply e.measurable hZmeas']
          congr 1
          ext x
          constructor
          · rintro ⟨y, hy, hxy⟩
            rwa [e.injective hxy] at hy
          · intro hx; exact ⟨x, hx, rfl⟩
        rw [← h1]
        exact Measure.prod_apply hZmeas'
      have hslice : ∀ t : ℝ, {x' : Fin m → ℝ | (t, x') ∈ e '' Z}
          = {x' : Fin m → ℝ | |t| ≤ 1 ∧ (∀ i, |x' i| ≤ 1) ∧
              G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) (fun i => (x' i : ℂ))) = 0} := by
        intro t
        ext x'
        have h1 : ((t, x') ∈ e '' Z) ↔ e.symm (t, x') ∈ Z := by
          constructor
          · rintro ⟨y, hy, hxy⟩
            rwa [← hxy, MeasurableEquiv.symm_apply_apply]
          · intro hy; exact ⟨e.symm (t, x'), hy, e.apply_symm_apply (t, x')⟩
        rw [Set.mem_ofPred_eq]
        rw [h1, hZdef, Set.mem_ofPred_eq]
        rw [piFinSuccAbove_symm_insertNth, insertNth_mem_box, insertNth_coe]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      have hbound : ∀ t : ℝ, (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
            {x' : Fin m → ℝ | (t, x') ∈ e '' Z}
          ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
              {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1} * Es.indicator (fun _ => (1 : ℝ≥0∞)) t := by
        intro t
        rw [hslice t]
        by_cases ht : t ∈ Es
        · rw [Set.indicator_of_mem ht, mul_one]
          exact measure_mono fun _ hx' => hx'.2.1
        · rw [Set.indicator_of_notMem ht, mul_zero]
          by_cases ht1 : |t| ≤ 1
          · have hGs : AnalyticOnNhd ℂ (fun w : Fin m → ℂ =>
                G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) w)) (Metric.closedBall 0 1) := by
              refine hG.comp (analyticOnNhd_insertNth m (t:ℂ) _) ?_
              intro w hw
              rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
              exact norm_insertNth_le m (by simpa using ht1)
                (fun i => (pi_norm_le_iff_of_nonneg (by norm_num)).mp hw i)
            have hne' : ∃ w : Fin m → ℂ, (∀ i, ‖w i‖ ≤ 1) ∧
                G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) w) ≠ 0 := by
              refine ⟨w0, hw0, ?_⟩
              intro h
              exact ht ⟨ht1, h⟩
            have hIH := volume_zero_set_pi m (fun w : Fin m → ℂ =>
                G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) w)) hGs hne'
            have hset : {x' : Fin m → ℝ | |t| ≤ 1 ∧ (∀ i, |x' i| ≤ 1) ∧
                  G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) (fun i => (x' i : ℂ))) = 0}
                = {x' : Fin m → ℝ | (∀ i, |x' i| ≤ 1) ∧
                  G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) (fun i => (x' i : ℂ))) = 0} := by
              ext x'
              simp only [Set.mem_ofPred_eq]
              exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨ht1, h.1, h.2⟩⟩
            rw [hset, hIH]
          · have hset : {x' : Fin m → ℝ | |t| ≤ 1 ∧ (∀ i, |x' i| ≤ 1) ∧
                  G (Fin.insertNth (α := fun _ : Fin (m+1) => ℂ) 0 (t:ℂ) (fun i => (x' i : ℂ))) = 0}
                = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro x' ⟨h, -, -⟩
              exact ht1 h
            rw [hset, measure_empty]
      have hle : (MeasureTheory.volume : MeasureTheory.Measure (Fin (m+1) → ℝ)) Z ≤ 0 := by
       calc (MeasureTheory.volume : MeasureTheory.Measure (Fin (m+1) → ℝ)) Z
          = ∫⁻ t, (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
              {x' : Fin m → ℝ | (t, x') ∈ e '' Z} := hfub
        _ ≤ ∫⁻ t, (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
              {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1} * Es.indicator (fun _ => (1 : ℝ≥0∞)) t :=
              lintegral_mono fun t => hbound t
        _ = (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
              {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1} * (MeasureTheory.volume : MeasureTheory.Measure ℝ) Es := by
              rw [show (fun t : ℝ => (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
                    {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1} * Es.indicator (fun _ => (1 : ℝ≥0∞)) t)
                  = Es.indicator (fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
                    {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1}) from by
                funext t
                by_cases ht : t ∈ Es
                · rw [Set.indicator_of_mem ht (f := fun _ => (1 : ℝ≥0∞)),
                    Set.indicator_of_mem ht (f := fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
                      {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1})]
                  simp
                · rw [Set.indicator_of_notMem ht (f := fun _ => (1 : ℝ≥0∞)),
                    Set.indicator_of_notMem ht (f := fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
                      {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1})]
                  simp]
              rw [lintegral_indicator hEsmeas fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
                    {x' : Fin m → ℝ | ∀ i, |x' i| ≤ 1}, setLIntegral_const]
        _ = 0 := by rw [hEszero, mul_zero]
      exact le_antisymm hle (by simp)

end Submission.FUP
