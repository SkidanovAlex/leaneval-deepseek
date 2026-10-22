/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Work.CWTOP.Basic

/-!
# CWTOP: the glued pieces of the `(n+1)`-skeleton

Bookkeeping around the definitions of `Submission.Work.CWTOP.Basic`:

* the centres of the `(n+1)`-cells are disjoint from the `n`-skeleton;
* the piece maps `stepGlue`, `stepRadialPiece`, `stepHomPiece` are continuous;
* `stepRadialPiece` and `stepHomPiece` are constant on the fibres of `stepGlue`, so that they
  descend to the collar space (see `Submission.Work.CWTOP.Radial`).

We also record the homeomorphism between an open cell and the model ball.
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-! ## §1 The `n`-skeleton and the centres -/

lemma centres_disjoint_skel {n k : ℕ} (h : k < n) : Disjoint (centres C n) (skel C k) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_centres] at hx
  obtain ⟨j, rfl⟩ := hx
  exact cellCentre_notMem_skeleton n j h hx'

lemma centres_disjoint_skel' {n k : ℕ} (h : k < n) : Disjoint (skel C k) (centres C n) :=
  (centres_disjoint_skel (C := C) h).symm

lemma skel_subset_stepU (n : ℕ) : skel C n ⊆ stepU C n :=
  fun x hx => ⟨skel_subset_skel_succ hx, fun hc =>
    Set.disjoint_left.mp (centres_disjoint_skel' (C := C) (Nat.lt_succ_self n)) hx hc⟩

/-! ## §2 Coordinates -/

lemma cellCoord_map_of_mem_ball {n : ℕ} (j : RelCWComplex.cell C n) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball 0 1) : cellCoord C n j (RelCWComplex.map n j y) = y := by
  rw [cellCoord]
  exact PartialEquiv.left_inv _ (by rwa [RelCWComplex.source_eq])

/-- The coordinate map on an open cell is continuous. -/
lemma continuous_cellCoord (n : ℕ) (j : RelCWComplex.cell C n) :
    Continuous fun x : RelCWComplex.openCell n j => cellCoord C n j (x : X) := by
  have h : ContinuousOn (fun x : X => cellCoord C n j x) (RelCWComplex.openCell n j) :=
    (RelCWComplex.continuousOn_symm n j).mono (openCell_subset_target n j)
  exact continuousOn_iff_continuous_restrict.mp h

/-- The characteristic map, viewed as a map from the model ball to the open cell, is continuous. -/
lemma continuous_map_openCell (n : ℕ) (j : RelCWComplex.cell C n) :
    Continuous fun y : Metric.ball (0 : Fin n → ℝ) 1 =>
      (⟨RelCWComplex.map n j y, ⟨y, y.2, rfl⟩⟩ : RelCWComplex.openCell n j) := by
  have h : ContinuousOn (fun y : Fin n → ℝ => RelCWComplex.map n j y)
      (Metric.ball (0 : Fin n → ℝ) 1) :=
    (RelCWComplex.continuousOn n j).mono Metric.ball_subset_closedBall
  have h' : Continuous fun y : Metric.ball (0 : Fin n → ℝ) 1 => RelCWComplex.map n j y :=
    continuousOn_iff_continuous_restrict.mp h
  exact Continuous.subtype_mk h' _

/-- The characteristic map identifies the model ball with the open cell. -/
noncomputable def ballHomeomorphOpenCell (n : ℕ) (j : RelCWComplex.cell C n) :
    Metric.ball (0 : Fin n → ℝ) 1 ≃ₜ RelCWComplex.openCell n j where
  toFun y := ⟨RelCWComplex.map n j y, ⟨y, y.2, rfl⟩⟩
  invFun x := ⟨cellCoord C n j (x : X), cellCoord_mem_ball x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact cellCoord_map_of_mem_ball j x.2
  right_inv y := by
    apply Subtype.ext
    exact map_cellCoord y.2
  continuous_toFun := continuous_map_openCell n j
  continuous_invFun := Continuous.subtype_mk (continuous_cellCoord n j) _

/-! ## §3 Values of the piece maps -/

lemma stepGlue_inl_val (n : ℕ) (x : {x : X // x ∈ skel C n}) :
    ((stepGlue C n (Sum.inl x) : {x : X // x ∈ stepCollar C n}) : X) = (x : X) := rfl

lemma stepGlue_inr_val (n : ℕ) (j : RelCWComplex.cell C (n + 1))
    (y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}) :
    ((stepGlue C n (Sum.inr ⟨j, y⟩) : {x : X // x ∈ stepCollar C n}) : X)
      = RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) := rfl

lemma stepRadialPiece_inl (n : ℕ) (x : {x : X // x ∈ skel C n}) :
    stepRadialPiece C n (Sum.inl x) = x := rfl

lemma stepRadialPiece_inr_val (n : ℕ) (j : RelCWComplex.cell C (n + 1))
    (y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}) :
    ((stepRadialPiece C n (Sum.inr ⟨j, y⟩) : {x : X // x ∈ skel C n}) : X)
      = RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ)) := rfl

lemma stepHomDistrib_inl (n : ℕ) (t : unitInterval) (x : {x : X // x ∈ skel C n}) :
    stepHomDistrib C n (t, Sum.inl x) = Sum.inl (t, x) := by
  simp only [stepHomDistrib, Homeomorph.trans_apply]
  simp [Homeomorph.prodSumDistrib, Homeomorph.sumProdDistrib, Homeomorph.sumCongr,
    Homeomorph.prodComm, Homeomorph.refl_apply]

lemma stepHomDistrib_inr (n : ℕ) (t : unitInterval) (j : RelCWComplex.cell C (n + 1))
    (y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}) :
    stepHomDistrib C n (t, Sum.inr ⟨j, y⟩) = Sum.inr ⟨j, (y, t)⟩ := by
  simp only [stepHomDistrib, Homeomorph.trans_apply]
  simp [Homeomorph.prodSumDistrib, Homeomorph.sumProdDistrib, Homeomorph.sumCongr,
    Homeomorph.prodComm, Homeomorph.sigmaProdDistrib]

lemma stepHomPiece_inl_val (n : ℕ) (t : unitInterval) (x : {x : X // x ∈ skel C n}) :
    ((stepHomPiece C n (t, Sum.inl x) : {x : X // x ∈ stepCollar C n}) : X) = (x : X) := by
  rw [stepHomPiece, Function.comp_apply, stepHomDistrib_inl]
  rfl

lemma stepHomPiece_inr_val (n : ℕ) (t : unitInterval) (j : RelCWComplex.cell C (n + 1))
    (y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n}) :
    ((stepHomPiece C n (t, Sum.inr ⟨j, y⟩) : {x : X // x ∈ stepCollar C n}) : X)
      = RelCWComplex.map (n + 1) j (radialInterpSafe (y : Fin (n + 1) → ℝ) (t : ℝ)) := by
  rw [stepHomPiece, Function.comp_apply, stepHomDistrib_inr]
  rfl

/-! ## §4 Continuity of the piece maps -/

lemma norm_eq_one_of_map_mem_skel {n : ℕ} (j : RelCWComplex.cell C (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1)
    (h : RelCWComplex.map (n + 1) j y ∈ skel C n) : ‖y‖ = 1 := by
  by_contra hne
  have hle : ‖y‖ ≤ 1 := by
    have h1 := Metric.mem_closedBall.mp hy
    rwa [dist_eq_norm, sub_zero] at h1
  have hlt : ‖y‖ < 1 := lt_of_le_of_ne hle hne
  have hball : y ∈ Metric.ball 0 1 := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hmem : RelCWComplex.map (n + 1) j y ∈ RelCWComplex.openCell (n + 1) j := ⟨y, hball, rfl⟩
  have hd := RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1)
    (j := j) (by exact_mod_cast Nat.lt_succ_self n)
  exact Set.disjoint_left.mp hd h hmem

lemma mem_closedBall_of_mem_modelCollar {n : ℕ} {y : Fin (n + 1) → ℝ}
    (hy : y ∈ modelCollar n) : y ∈ Metric.closedBall 0 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hy.2

lemma radialUnitSafe_eq_self_of_map_mem_skel {n : ℕ} (j : RelCWComplex.cell C (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1)
    (h : RelCWComplex.map (n + 1) j y ∈ skel C n) : radialUnitSafe y = y :=
  radialUnitSafe_eq_self_of_norm_eq_one (norm_eq_one_of_map_mem_skel j hy h)

lemma radialInterpSafe_eq_self_of_map_mem_skel {n : ℕ} (j : RelCWComplex.cell C (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : y ∈ Metric.closedBall 0 1)
    (h : RelCWComplex.map (n + 1) j y ∈ skel C n) (t : ℝ) : radialInterpSafe y t = y :=
  radialInterpSafe_eq_self_of_norm_eq_one (norm_eq_one_of_map_mem_skel j hy h) t

lemma continuous_stepGlue (n : ℕ) : Continuous (stepGlue C n) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · refine Continuous.subtype_mk (f := fun x : {x : X // x ∈ skel C n} => (x : X))
      continuous_subtype_val fun x => Or.inl x.2
  · rw [continuous_sigma_iff]
    intro j
    refine Continuous.subtype_mk (f := fun y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} =>
      RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ))
      (continuousOn_iff_continuous_restrict.mp
        ((RelCWComplex.continuousOn (n + 1) j).mono (fun y hy =>
          mem_closedBall_of_mem_modelCollar hy))) _

lemma continuous_stepRadialPiece (n : ℕ) : Continuous (stepRadialPiece C n) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · exact continuous_subtype_val.subtype_mk _
  · rw [continuous_sigma_iff]
    intro j
    have hc : Continuous fun y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} =>
        radialUnitSafe (y : Fin (n + 1) → ℝ) := by
      have hnorm : Continuous fun y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} =>
          (max ‖(y : Fin (n + 1) → ℝ)‖ (1 / 2))⁻¹ :=
        ((continuous_norm.comp continuous_subtype_val).max continuous_const).inv₀
          (fun y => norm_max_norm_half_ne_zero _)
      exact (hnorm.smul continuous_subtype_val).congr fun y => rfl
    have hmem : ∀ y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n},
        radialUnitSafe (y : Fin (n + 1) → ℝ) ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
      fun y => Metric.mem_closedBall.mpr (by
        rw [dist_eq_norm, sub_zero]
        exact norm_radialUnitSafe_le_one y.2.2)
    refine Continuous.subtype_mk (f := fun y : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} =>
      RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ)))
      ((continuousOn_iff_continuous_restrict.mp
        ((RelCWComplex.continuousOn (n + 1) j).mono (fun y hy => hy))).comp
          (hc.subtype_mk hmem)) _

lemma continuous_stepHomPieceSum (n : ℕ) : Continuous (stepHomPieceSum C n) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · refine Continuous.subtype_mk (f := fun p : unitInterval × {x : X // x ∈ skel C n} =>
      (p.2 : X)) (continuous_subtype_val.comp continuous_snd) fun p => Or.inl p.2.2
  · rw [continuous_sigma_iff]
    intro j
    have hc : Continuous fun q : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval =>
        radialInterpSafe (q.1 : Fin (n + 1) → ℝ) (q.2 : ℝ) := by
      have hnorm : Continuous fun q :
          {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval =>
          (max ‖(q.1 : Fin (n + 1) → ℝ)‖ (1 / 2))⁻¹ :=
        ((continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).max
          continuous_const).inv₀ (fun q => norm_max_norm_half_ne_zero _)
      have h2 : Continuous fun q : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval =>
          radialUnitSafe (q.1 : Fin (n + 1) → ℝ) :=
        (hnorm.smul (continuous_subtype_val.comp continuous_fst)).congr fun q => rfl
      have h1 : Continuous fun q : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval =>
          (1 - (q.2 : ℝ)) • (q.1 : Fin (n + 1) → ℝ) :=
        (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
          (continuous_subtype_val.comp continuous_fst)
      have h3 : Continuous fun q : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval =>
          (q.2 : ℝ) • radialUnitSafe (q.1 : Fin (n + 1) → ℝ) :=
        (continuous_subtype_val.comp continuous_snd).smul h2
      exact (h1.add h3).congr fun q => rfl
    have hmem : ∀ q : {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval,
        radialInterpSafe (q.1 : Fin (n + 1) → ℝ) (q.2 : ℝ)
          ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
      fun q => Metric.mem_closedBall.mpr (by
        rw [dist_eq_norm, sub_zero]
        exact norm_radialInterpSafe_le q.1.2.2 q.2.2.1 q.2.2.2)
    refine Continuous.subtype_mk (f := fun q :
        {y : Fin (n + 1) → ℝ // y ∈ modelCollar n} × unitInterval =>
      RelCWComplex.map (n + 1) j (radialInterpSafe (q.1 : Fin (n + 1) → ℝ) (q.2 : ℝ)))
      ((continuousOn_iff_continuous_restrict.mp
        ((RelCWComplex.continuousOn (n + 1) j).mono (fun y hy => hy))).comp
          (hc.subtype_mk hmem)) _

lemma continuous_stepHomPiece (n : ℕ) : Continuous (stepHomPiece C n) :=
  (continuous_stepHomPieceSum n).comp (stepHomDistrib C n).continuous

/-! ## §5 The maps descend to the collar space -/

lemma eq_of_map_eq_of_norm_ne_one {n : ℕ} (j j' : RelCWComplex.cell C (n + 1))
    {y y' : Fin (n + 1) → ℝ} (hy : y ∈ Metric.ball 0 1) (hy' : y' ∈ Metric.ball 0 1)
    (h : RelCWComplex.map (n + 1) j y = RelCWComplex.map (n + 1) j' y') (hlt : ‖y‖ < 1) :
    j = j' ∧ y = y' := by
  have hcell : RelCWComplex.map (n + 1) j y ∈ RelCWComplex.openCell (n + 1) j' :=
    ⟨y', hy', h.symm⟩
  have hmem : RelCWComplex.map (n + 1) j y ∈ RelCWComplex.openCell (n + 1) j := ⟨y, hy, rfl⟩
  have hj : j = j' := by
    by_contra hne
    refine Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (C := C) (n := n + 1)
      (m := n + 1) (i := j) (j := j') ?_) hmem hcell
    exact fun hEq => hne (eq_of_heq (Sigma.mk.inj_iff.mp hEq).2)
  subst hj
  exact ⟨rfl, by rw [← cellCoord_map_of_mem_ball j hy, ← cellCoord_map_of_mem_ball j hy', h]⟩

lemma stepRadialPiece_factors (n : ℕ) :
    Function.FactorsThrough (stepRadialPiece C n) (stepGlue C n) := by
  intro a b hab
  have hval := congrArg (fun z : {x : X // x ∈ stepCollar C n} => (z : X)) hab
  rcases a with x | ⟨j, y⟩
  · rcases b with x' | ⟨j', y'⟩
    · exact Subtype.ext hval
    · have hx_eq : (x : X) = RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) := hval
      have hyS : RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) ∈ skel C n := hx_eq ▸ x.2
      have hu : radialUnitSafe (y' : Fin (n + 1) → ℝ) = (y' : Fin (n + 1) → ℝ) :=
        radialUnitSafe_eq_self_of_map_mem_skel j' (mem_closedBall_of_mem_modelCollar y'.2) hyS
      refine Subtype.ext ?_
      show (x : X) = RelCWComplex.map (n + 1) j' (radialUnitSafe (y' : Fin (n + 1) → ℝ))
      rw [hu]; exact hx_eq
  · rcases b with x' | ⟨j', y'⟩
    · have hx_eq : (x' : X) = RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) := hval.symm
      have hyS : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) ∈ skel C n := hx_eq ▸ x'.2
      have hu : radialUnitSafe (y : Fin (n + 1) → ℝ) = (y : Fin (n + 1) → ℝ) :=
        radialUnitSafe_eq_self_of_map_mem_skel j (mem_closedBall_of_mem_modelCollar y.2) hyS
      refine Subtype.ext ?_
      show RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ)) = (x' : X)
      rw [hu]; exact hx_eq.symm
    · have hycl : (y : Fin (n + 1) → ℝ) ∈ Metric.closedBall 0 1 :=
        mem_closedBall_of_mem_modelCollar y.2
      have hy'cl : (y' : Fin (n + 1) → ℝ) ∈ Metric.closedBall 0 1 :=
        mem_closedBall_of_mem_modelCollar y'.2
      by_cases hy : ‖(y : Fin (n + 1) → ℝ)‖ = 1
      · have heq : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ)
            = RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) := hval
        have hy' : ‖(y' : Fin (n + 1) → ℝ)‖ = 1 := by
          refine norm_eq_one_of_map_mem_skel j' hy'cl ?_
          rw [← heq]
          exact RelCWComplex.cellFrontier_subset_skeleton (n := n) (j := j)
            ⟨(y : Fin (n + 1) → ℝ), by
              rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hy, rfl⟩
        refine Subtype.ext ?_
        show RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ))
            = RelCWComplex.map (n + 1) j' (radialUnitSafe (y' : Fin (n + 1) → ℝ))
        rw [radialUnitSafe_eq_self_of_norm_eq_one hy, radialUnitSafe_eq_self_of_norm_eq_one hy']
        exact hval
      · have hlt : ‖(y : Fin (n + 1) → ℝ)‖ < 1 := by
          have h1 := Metric.mem_closedBall.mp hycl
          rw [dist_eq_norm, sub_zero] at h1
          exact lt_of_le_of_ne h1 hy
        have heq : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ)
            = RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) := hval
        have hy'ne : ‖(y' : Fin (n + 1) → ℝ)‖ ≠ 1 := by
          intro h1
          have hS' : RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) ∈ skel C n :=
            RelCWComplex.cellFrontier_subset_skeleton (n := n) (j := j')
              ⟨(y' : Fin (n + 1) → ℝ), by
                rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h1, rfl⟩
          have hS : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) ∈ skel C n := heq ▸ hS'
          have hball : (y : Fin (n + 1) → ℝ) ∈ Metric.ball 0 1 := by
            rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
          exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeleton_openCell (C := C)
            (n := (n : ℕ∞)) (m := n + 1) (j := j) (by exact_mod_cast Nat.lt_succ_self n)) hS
            ⟨(y : Fin (n + 1) → ℝ), hball, rfl⟩
        have hy'lt : ‖(y' : Fin (n + 1) → ℝ)‖ < 1 := by
          have h1 := Metric.mem_closedBall.mp hy'cl
          rw [dist_eq_norm, sub_zero] at h1
          exact lt_of_le_of_ne h1 hy'ne
        have hball : (y : Fin (n + 1) → ℝ) ∈ Metric.ball 0 1 := by
          rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
        have hball' : (y' : Fin (n + 1) → ℝ) ∈ Metric.ball 0 1 := by
          rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
        obtain ⟨hj, hyeq⟩ := eq_of_map_eq_of_norm_ne_one j j' hball hball' hval hlt
        subst hj
        refine Subtype.ext ?_
        show RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ))
            = RelCWComplex.map (n + 1) j (radialUnitSafe (y' : Fin (n + 1) → ℝ))
        rw [hyeq]

end Work.CWTOP
