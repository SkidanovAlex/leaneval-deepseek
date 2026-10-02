import Mathlib
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology

noncomputable section

namespace Work.Serre

open Work.RatHurewicz

def sphDomeCoord (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) : Fin (n + 3) → ℝ :=
  Fin.snoc (fun i => (2 * Real.sqrt (1 - ‖y‖ ^ 2)) * y.ofLp i) (2 * ‖y‖ ^ 2 - 1)

def sphDomeMap (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 3)) :=
  WithLp.toLp 2 (sphDomeCoord n y)

@[simp] theorem sphDomeMap_ofLp (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    (sphDomeMap n y).ofLp = sphDomeCoord n y := by simp [sphDomeMap]

@[simp] theorem sphDomeCoord_castSucc (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 2)) :
    sphDomeCoord n y (Fin.castSucc i) = (2 * Real.sqrt (1 - ‖y‖ ^ 2)) * y.ofLp i := by
  simp [sphDomeCoord]

@[simp] theorem sphDomeCoord_last (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    sphDomeCoord n y (Fin.last (n + 2)) = 2 * ‖y‖ ^ 2 - 1 := by simp [sphDomeCoord]

@[simp] theorem sphDomeMap_apply_castSucc (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 2)) :
    (sphDomeMap n y).ofLp (Fin.castSucc i) = (2 * Real.sqrt (1 - ‖y‖ ^ 2)) * y.ofLp i := by
  rw [sphDomeMap_ofLp, sphDomeCoord_castSucc]

@[simp] theorem sphDomeMap_apply_last (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    (sphDomeMap n y).ofLp (Fin.last (n + 2)) = 2 * ‖y‖ ^ 2 - 1 := by
  rw [sphDomeMap_ofLp, sphDomeCoord_last]

theorem sphDomeMap_norm_sq (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    ‖sphDomeMap n y‖ ^ 2
      = (2 * Real.sqrt (1 - ‖y‖ ^ 2)) ^ 2 * ‖y‖ ^ 2 + (2 * ‖y‖ ^ 2 - 1) ^ 2 := by
  have hy : (∑ i : Fin (n + 2), (y.ofLp i) ^ 2) = ‖y‖ ^ 2 :=
    (EuclideanSpace.real_norm_sq_eq y).symm
  have hsum : (∑ i : Fin (n + 2), ((2 * Real.sqrt (1 - ‖y‖ ^ 2)) * y.ofLp i) ^ 2)
      = (2 * Real.sqrt (1 - ‖y‖ ^ 2)) ^ 2 * ‖y‖ ^ 2 := by
    rw [← hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]
  rw [EuclideanSpace.real_norm_sq_eq, sphDomeMap_ofLp, sphDomeCoord, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hsum]

theorem sphDomeMap_norm (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) (hy : ‖y‖ ≤ 1) :
    ‖sphDomeMap n y‖ = 1 := by
  have h1 : (0 : ℝ) ≤ 1 - ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg y, sq_nonneg ‖y‖, sq_nonneg (‖y‖ - 1)]
  have h2 : Real.sqrt (1 - ‖y‖ ^ 2) ^ 2 = 1 - ‖y‖ ^ 2 := Real.sq_sqrt h1
  have h3 : ‖sphDomeMap n y‖ ^ 2 = 1 := by
    rw [sphDomeMap_norm_sq]
    nlinarith [h2]
  rw [← Real.sqrt_sq (norm_nonneg (sphDomeMap n y)), h3, Real.sqrt_one]

theorem sphDomeMap_eq_of_norm_eq_one (n : ℕ) {y y' : EuclideanSpace ℝ (Fin (n + 2))}
    (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1) : sphDomeMap n y = sphDomeMap n y' := by
  show WithLp.toLp 2 (sphDomeCoord n y) = WithLp.toLp 2 (sphDomeCoord n y')
  congr 1
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [sphDomeCoord_last, sphDomeCoord_last, hy, hy']
  · intro j
    rw [sphDomeCoord_castSucc, sphDomeCoord_castSucc, hy, hy']
    norm_num

theorem continuous_sphDomeCoord (n : ℕ) : Continuous (sphDomeCoord n) := by
  have h : sphDomeCoord n = fun y : EuclideanSpace ℝ (Fin (n + 2)) =>
      Fin.snoc (fun i : Fin (n + 2) => (2 * Real.sqrt (1 - ‖y‖ ^ 2)) * y.ofLp i)
        (2 * ‖y‖ ^ 2 - 1) := rfl
  rw [h]
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]; fun_prop
  · intro j
    simp only [Fin.snoc_castSucc]; fun_prop

theorem continuous_sphDomeMap (n : ℕ) : Continuous (sphDomeMap n) := by
  show Continuous fun y => WithLp.toLp 2 (sphDomeCoord n y)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 3) => ℝ)).comp (continuous_sphDomeCoord n)

/-- The north pole. -/
def northPole (n : ℕ) : cellSphere (n + 1) :=
  ⟨sphDomeMap n (EuclideanSpace.single 0 1), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact sphDomeMap_norm n _ (by rw [EuclideanSpace.norm_single]; norm_num)⟩

theorem continuous_sphDomeMap_norm (n : ℕ) : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 2)) => ‖y‖) :=
  continuous_norm

theorem norm_le_one_of_cellDisk (n : ℕ) (y : cellDisk n) :
    ‖(y : EuclideanSpace ℝ (Fin (n + 2)))‖ ≤ 1 := by
  have h : dist ((y : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))) 0 ≤ 1 :=
    Metric.mem_closedBall.mp y.2
  simpa [dist_eq_norm] using h

theorem norm_eq_one_of_cellSphere (n : ℕ) (z : cellSphere n) :
    ‖(z : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
  have h : dist (z : EuclideanSpace ℝ (Fin (n + 2))) 0 = 1 := Metric.mem_sphere.mp z.2
  simpa [dist_eq_norm] using h

def phiFun (n : ℕ) : PUnit ⊕ (Sigma (fun _ : PUnit => cellDisk n)) → cellSphere (n + 1) :=
  Sum.elim (fun _ => northPole n)
    (fun p => ⟨sphDomeMap n (p.2 : EuclideanSpace ℝ (Fin (n + 2))), by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact sphDomeMap_norm n _ (norm_le_one_of_cellDisk n p.2)⟩)

theorem continuous_phiFun (n : ℕ) : Continuous (phiFun n) := by
  show Continuous (Sum.elim _ _)
  refine Continuous.sumElim continuous_const ?_
  have h2 : Continuous (fun p : Sigma (fun _ : PUnit => cellDisk n) =>
      sphDomeMap n ((p.2 : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))) := by
    rw [continuous_sigma_iff]
    intro i
    show Continuous (fun a : cellDisk n => sphDomeMap n ((a : EuclideanSpace ℝ (Fin (n + 2)))))
    exact (continuous_sphDomeMap n).comp continuous_subtype_val
  exact Continuous.subtype_mk h2 _

def attachSetoid (n : ℕ) : Setoid (PUnit ⊕ (Sigma (fun _ : PUnit => cellDisk n))) :=
  Relation.EqvGen.setoid (attachRel n PUnit PUnit
    (fun _ : PUnit => ContinuousMap.const (cellSphere n) PUnit.unit))

theorem phiFun_rel (n : ℕ) :
    ∀ a b : PUnit ⊕ (Sigma (fun _ : PUnit => cellDisk n)),
      Relation.EqvGen (attachRel n PUnit PUnit
        (fun _ : PUnit => ContinuousMap.const (cellSphere n) PUnit.unit)) a b →
      phiFun n a = phiFun n b := by
  intro a b h
  induction h with
  | rel x y hxy =>
      obtain ⟨i, z, rfl, rfl⟩ := hxy
      refine Subtype.ext ?_
      show sphDomeMap n (EuclideanSpace.single 0 1)
        = sphDomeMap n ((z : EuclideanSpace ℝ (Fin (n + 2))))
      exact (sphDomeMap_eq_of_norm_eq_one (y := (z : EuclideanSpace ℝ (Fin (n + 2))))
        (y' := EuclideanSpace.single 0 1) n (norm_eq_one_of_cellSphere n z) (by
          rw [EuclideanSpace.norm_single]; norm_num)).symm
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2

def phiQ (n : ℕ) : Quotient (attachSetoid n) → cellSphere (n + 1) :=
  Quotient.lift (phiFun n) (fun a b h => phiFun_rel n a b h)

theorem phiQ_mk (n : ℕ) (a : PUnit ⊕ (Sigma (fun _ : PUnit => cellDisk n))) :
    phiQ n (Quotient.mk'' a) = phiFun n a := rfl

theorem continuous_phiQ (n : ℕ) : Continuous (phiQ n) := by
  refine (isQuotientMap_quotient_mk' (s := attachSetoid n)).continuous_iff.mpr ?_
  convert continuous_phiFun n using 1
  funext a
  exact phiQ_mk n a

theorem norm_eq_one_of_sphDomeMap_eq_northPole (n : ℕ) {y : EuclideanSpace ℝ (Fin (n + 2))}
    (h : sphDomeMap n y = sphDomeMap n (EuclideanSpace.single 0 1)) : ‖y‖ = 1 := by
  have hlast := congrArg (fun w : EuclideanSpace ℝ (Fin (n + 3)) => w.ofLp (Fin.last (n + 2))) h
  rw [sphDomeMap_apply_last, sphDomeMap_apply_last, EuclideanSpace.norm_single, norm_one] at hlast
  have hsq : ‖y‖ ^ 2 = 1 := by linarith
  have hfac : (‖y‖ - 1) * (‖y‖ + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · linarith
  · have := norm_nonneg y; linarith

theorem eq_northPole_of_norm_eq_one (n : ℕ) {y : EuclideanSpace ℝ (Fin (n + 2))}
    (hy : ‖y‖ = 1) : sphDomeMap n y = sphDomeMap n (EuclideanSpace.single 0 1) :=
  sphDomeMap_eq_of_norm_eq_one n hy (by rw [EuclideanSpace.norm_single]; norm_num)

theorem sphDomeMap_inj_of_norm_lt (n : ℕ) {y y' : EuclideanSpace ℝ (Fin (n + 2))}
    (hy : ‖y‖ < 1) (h : sphDomeMap n y = sphDomeMap n y') : y = y' := by
  have hsq : ‖y‖ ^ 2 = ‖y'‖ ^ 2 := by
    have hlast := congrArg (fun w : EuclideanSpace ℝ (Fin (n + 3)) => w.ofLp (Fin.last (n + 2))) h
    rw [sphDomeMap_apply_last, sphDomeMap_apply_last] at hlast
    linarith
  have hpos : (0 : ℝ) < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 1)]
  have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = Real.sqrt (1 - ‖y'‖ ^ 2) := by rw [hsq]
  have hc : (2 * Real.sqrt (1 - ‖y‖ ^ 2)) ≠ 0 := by
    have hp : (0 : ℝ) < Real.sqrt (1 - ‖y‖ ^ 2) := Real.sqrt_pos.mpr hpos
    linarith
  have hfun : (fun i : Fin (n + 2) => y.ofLp i) = (fun i => y'.ofLp i) := by
    funext i
    have hc' := congrArg (fun w : EuclideanSpace ℝ (Fin (n + 3)) => w.ofLp (Fin.castSucc i)) h
    rw [sphDomeMap_apply_castSucc, sphDomeMap_apply_castSucc] at hc'
    have hp' : (0 : ℝ) < 1 - ‖y'‖ ^ 2 := by nlinarith [norm_nonneg y', sq_nonneg (‖y'‖ - 1)]
    have hc'0 : (2 * Real.sqrt (1 - ‖y'‖ ^ 2)) ≠ 0 := by
      have hp : (0 : ℝ) < Real.sqrt (1 - ‖y'‖ ^ 2) := Real.sqrt_pos.mpr hp'
      linarith
    have hcoef : (2 * Real.sqrt (1 - ‖y‖ ^ 2)) = (2 * Real.sqrt (1 - ‖y'‖ ^ 2)) := by rw [hsqrt]
    rw [hcoef] at hc'
    exact mul_left_cancel₀ hc'0 hc'
  have hcoe : WithLp.toLp 2 (fun i : Fin (n + 2) => y.ofLp i)
      = WithLp.toLp 2 (fun i => y'.ofLp i) := congrArg _ hfun
  simpa using hcoe

theorem phiFun_inl_eq (n : ℕ) (u : PUnit) : phiFun n (Sum.inl u) = northPole n := rfl

theorem phiFun_inr_eq (n : ℕ) (i : PUnit) (y : cellDisk n) :
    phiFun n (Sum.inr (⟨i, y⟩ : Sigma (fun _ : PUnit => cellDisk n))) =
      ⟨sphDomeMap n (y : EuclideanSpace ℝ (Fin (n + 2))), by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        exact sphDomeMap_norm n _ (norm_le_one_of_cellDisk n y)⟩ := rfl

theorem inr_bdry_rel (n : ℕ) (y : cellDisk n)
    (hy : ‖(y : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1) :
    Relation.EqvGen (attachRel n PUnit PUnit
      (fun _ : PUnit => ContinuousMap.const (cellSphere n) PUnit.unit))
      (Sum.inr (⟨PUnit.unit, y⟩ : Sigma (fun _ : PUnit => cellDisk n))) (Sum.inl PUnit.unit) := by
  have hcell : cellSphereToDisk n (⟨(y : EuclideanSpace ℝ (Fin (n + 2))), by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hy⟩ : cellSphere n) = y :=
    Subtype.ext rfl
  refine (Relation.EqvGen.rel _ _ ⟨PUnit.unit,
    (⟨(y : EuclideanSpace ℝ (Fin (n + 2))), by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hy⟩ : cellSphere n),
    rfl, ?_⟩).symm
  exact congrArg (fun t => Sum.inr (⟨PUnit.unit, t⟩ : Sigma (fun _ : PUnit => cellDisk n))) hcell

theorem phiFun_eq_imp_rel (n : ℕ) :
    ∀ a b : PUnit ⊕ (Sigma (fun _ : PUnit => cellDisk n)), phiFun n a = phiFun n b →
      Relation.EqvGen (attachRel n PUnit PUnit
        (fun _ : PUnit => ContinuousMap.const (cellSphere n) PUnit.unit)) a b := by
  intro a b h
  rcases a with u | ⟨i, y⟩
  · rcases b with v | ⟨j, y'⟩
    · obtain rfl : u = v := Subsingleton.elim _ _
      exact Relation.EqvGen.refl _
    · have hd : sphDomeMap n (EuclideanSpace.single 0 1)
          = sphDomeMap n ((y' : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))) :=
        (by have hh := h; rw [phiFun_inl_eq, phiFun_inr_eq] at hh
            exact congrArg Subtype.val hh)
      have hone : ‖((y' : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 :=
        norm_eq_one_of_sphDomeMap_eq_northPole n hd.symm
      obtain rfl : j = PUnit.unit := Subsingleton.elim _ _
      obtain rfl : u = PUnit.unit := Subsingleton.elim _ _
      exact (inr_bdry_rel n y' hone).symm
  · rcases b with v | ⟨j, y'⟩
    · have hd : sphDomeMap n (EuclideanSpace.single 0 1)
          = sphDomeMap n ((y : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))) :=
        (by have hh := h; rw [phiFun_inl_eq, phiFun_inr_eq] at hh
            exact (congrArg Subtype.val hh).symm)
      have hone : ‖((y : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 :=
        norm_eq_one_of_sphDomeMap_eq_northPole n hd.symm
      obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
      obtain rfl : v = PUnit.unit := Subsingleton.elim _ _
      exact inr_bdry_rel n y hone
    · have hd : sphDomeMap n ((y : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))
          = sphDomeMap n ((y' : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))) :=
        (by have hh := h; rw [phiFun_inr_eq, phiFun_inr_eq] at hh
            exact congrArg Subtype.val hh)
      obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
      obtain rfl : j = PUnit.unit := Subsingleton.elim _ _
      rcases lt_or_eq_of_le (norm_le_one_of_cellDisk n y) with hlt | heq
      · have hyy : y = y' := Subtype.ext (sphDomeMap_inj_of_norm_lt n hlt hd)
        subst hyy
        exact Relation.EqvGen.refl _
      · have h1 : ‖((y : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := heq
        have h2 : ‖((y' : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 :=
          norm_eq_one_of_sphDomeMap_eq_northPole n (eq_northPole_of_norm_eq_one n h1 ▸ hd.symm)
        exact Relation.EqvGen.trans _ _ _ (inr_bdry_rel n y h1) (inr_bdry_rel n y' h2).symm

theorem phiQ_injective (n : ℕ) : Function.Injective (phiQ n) := by
  intro x y h
  induction x using Quotient.inductionOn' with
  | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      refine Quotient.sound ?_
      apply phiFun_eq_imp_rel n a b
      show phiFun n a = phiFun n b
      rw [← phiQ_mk n a, ← phiQ_mk n b]
      exact h

theorem phiFun_surjective (n : ℕ) : Function.Surjective (phiFun n) := by
  intro w
  have hw : ‖(w : EuclideanSpace ℝ (Fin (n + 3)))‖ = 1 := by
    have h := norm_eq_one_of_cellSphere (n + 1) w
    simpa using h
  by_cases ht : (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.last (n + 2)) = 1
  · refine ⟨Sum.inl PUnit.unit, ?_⟩
    refine Subtype.ext ?_
    show sphDomeMap n (EuclideanSpace.single 0 1) = (w : EuclideanSpace ℝ (Fin (n + 3)))
    have hsq : (∑ i : Fin (n + 3), ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp i) ^ 2) = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hw]
      norm_num
    rw [Fin.sum_univ_castSucc, ht] at hsq
    simp only [one_pow] at hsq
    have hsq0 : (∑ i : Fin (n + 2),
        ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i)) ^ 2) = 0 := by linarith
    have hzero : ∀ i : Fin (n + 2),
        (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i) = 0 := by
      intro i
      have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (n + 2))),
          0 ≤ ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc j)) ^ 2 :=
        fun j _ => sq_nonneg _
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsq0 i (Finset.mem_univ i)
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hmem
    show WithLp.toLp 2 (sphDomeCoord n (EuclideanSpace.single 0 1))
      = WithLp.toLp 2 (fun i => (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp i)
    congr 1
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [sphDomeCoord_last, EuclideanSpace.norm_single, norm_one, ht]
      norm_num
    · intro j
      rw [sphDomeCoord_castSucc, EuclideanSpace.norm_single, norm_one, hzero j]
      norm_num
  · -- interior case: the explicit inverse
    set t : ℝ := (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.last (n + 2)) with htd
    set c : ℝ := Real.sqrt (2 * (1 - t)) with hcd
    have ht1 : t < 1 := by
      have hle : t ≤ 1 := by
        have : t ^ 2 ≤ 1 := by
          have hsq : (∑ i : Fin (n + 3), ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp i) ^ 2) = 1 := by
            rw [← EuclideanSpace.real_norm_sq_eq, hw]
            norm_num
          rw [Fin.sum_univ_castSucc] at hsq
          have : (0 : ℝ) ≤ ∑ i : Fin (n + 2),
              ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i)) ^ 2 :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          simp only [htd] at hsq
          linarith
        nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
      exact lt_of_le_of_ne hle (fun h => ht h)
    have hcpos : 0 < c := by
      rw [hcd]
      exact Real.sqrt_pos.mpr (by linarith)
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hcsq : c ^ 2 = 2 * (1 - t) := by
      rw [hcd, Real.sq_sqrt (by linarith)]
    have hsum : (∑ i : Fin (n + 2),
        ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i)) ^ 2) = 1 - t ^ 2 := by
      have hsq : (∑ i : Fin (n + 3), ((w : EuclideanSpace ℝ (Fin (n + 3))).ofLp i) ^ 2) = 1 := by
        rw [← EuclideanSpace.real_norm_sq_eq, hw]
        norm_num
      rw [Fin.sum_univ_castSucc] at hsq
      simp only [htd] at hsq
      linarith
    set y0 : EuclideanSpace ℝ (Fin (n + 2)) :=
      WithLp.toLp 2 (fun i => c⁻¹ * (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i))
      with hyd
    have hy0norm : ‖y0‖ ^ 2 = (1 + t) / 2 := by
      rw [hyd]
      rw [show ‖WithLp.toLp 2 (fun i : Fin (n + 2) =>
          c⁻¹ * (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i))‖ ^ 2
        = ∑ i : Fin (n + 2),
          (c⁻¹ * (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp (Fin.castSucc i)) ^ 2 from
        EuclideanSpace.real_norm_sq_eq _]
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, hsum]
      have hcc : c⁻¹ ^ 2 = (c ^ 2)⁻¹ := by rw [inv_pow]
      rw [hcc, hcsq]
      field_simp
      ring
    have hy0le : ‖y0‖ ≤ 1 := by
      have hnn : (0 : ℝ) ≤ ‖y0‖ ^ 2 := sq_nonneg _
      have : (1 + t) / 2 ≤ 1 := by linarith
      nlinarith [norm_nonneg y0, sq_nonneg (‖y0‖ - 1)]
    refine ⟨Sum.inr ⟨PUnit.unit, ⟨y0, ?_⟩⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hy0le
    · refine Subtype.ext ?_
      show sphDomeMap n y0 = (w : EuclideanSpace ℝ (Fin (n + 3)))
      have hsqrt1 : Real.sqrt (1 - ‖y0‖ ^ 2) = Real.sqrt ((1 - t) / 2) := by
        rw [hy0norm]
        congr 1
        ring
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h2sqrt : 2 * Real.sqrt ((1 - t) / 2) = c := by
        rw [hcd, ← h4, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        ring
      show WithLp.toLp 2 (sphDomeCoord n y0)
        = WithLp.toLp 2 (fun i => (w : EuclideanSpace ℝ (Fin (n + 3))).ofLp i)
      congr 1
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [sphDomeCoord_last, hy0norm]
        field_simp
        ring
      · intro j
        rw [sphDomeCoord_castSucc, hyd]
        simp only [WithLp.ofLp_toLp]
        rw [hsqrt1, h2sqrt]
        field_simp

theorem phiQ_surjective (n : ℕ) : Function.Surjective (phiQ n) := by
  intro w
  obtain ⟨a, ha⟩ := phiFun_surjective n w
  exact ⟨Quotient.mk'' a, by rw [phiQ_mk]; exact ha⟩

theorem phiQ_bijective (n : ℕ) : Function.Bijective (phiQ n) :=
  ⟨phiQ_injective n, phiQ_surjective n⟩

instance compactSpace_cellDisk (n : ℕ) : CompactSpace (cellDisk n) := by
  refine isCompact_iff_compactSpace.mp ?_
  have h : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    isCompact_closedBall 0 1
  simpa [cellDisk] using h

theorem sigmaPUnit_surj (n : ℕ) :
    Function.Surjective (fun y : cellDisk n =>
      (⟨PUnit.unit, y⟩ : Sigma (fun _ : PUnit => cellDisk n))) := by
  rintro ⟨i, y⟩
  refine ⟨y, ?_⟩
  cases i
  rfl

instance compactSpace_sigma_cellDisk (n : ℕ) : CompactSpace (Sigma (fun _ : PUnit => cellDisk n)) := by
  haveI := compactSpace_cellDisk n
  refine ⟨?_⟩
  have h : IsCompact (Set.range (fun y : cellDisk n =>
      (⟨PUnit.unit, y⟩ : Sigma (fun _ : PUnit => cellDisk n)))) := by
    have h' := (isCompact_univ (X := cellDisk n)).image (continuous_sigmaMk
      (σ := fun _ : PUnit => cellDisk n) (i := PUnit.unit))
    rwa [Set.image_univ] at h'
  rwa [Set.range_eq_univ.mpr (sigmaPUnit_surj n)] at h

instance compactSpace_attachSetoid (n : ℕ) : CompactSpace (Quotient (attachSetoid n)) := by
  haveI := compactSpace_sigma_cellDisk n
  exact Quotient.compactSpace

theorem isClosedMap_phiQ (n : ℕ) : IsClosedMap (phiQ n) := by
  haveI : CompactSpace (Quotient (attachSetoid n)) := compactSpace_attachSetoid n
  intro s hs
  exact (hs.isCompact.image (continuous_phiQ n)).isClosed

instance attachSetoid_nonempty (n : ℕ) : Nonempty (Quotient (attachSetoid n)) :=
  ⟨Quotient.mk'' (Sum.inl PUnit.unit)⟩

/-- The `attachCells`-shaped form of `attachSetoid_nonempty` (instance search is syntactic). -/
instance attachCellsPUnit_nonempty (n : ℕ) :
    Nonempty (Work.RatHurewicz.attachCells n PUnit PUnit
      (fun _ : PUnit => ContinuousMap.const (Work.RatHurewicz.cellSphere n) PUnit.unit)) :=
  ⟨Quotient.mk'' (Sum.inl PUnit.unit)⟩

theorem invFun_preimage_eq_image (n : ℕ) (U : Set (Quotient (attachSetoid n))) :
    (Function.invFun (phiQ n)) ⁻¹' U = phiQ n '' U := by
  have hbij := phiQ_bijective n
  ext y
  constructor
  · intro hy
    refine ⟨Function.invFun (phiQ n) y, hy, ?_⟩
    exact Function.rightInverse_invFun hbij.2 y
  · rintro ⟨x, hx, rfl⟩
    show Function.invFun (phiQ n) (phiQ n x) ∈ U
    rw [Function.leftInverse_invFun hbij.1 x]
    exact hx

theorem continuous_invFun_phiQ (n : ℕ) : Continuous (Function.invFun (phiQ n)) := by
  haveI : CompactSpace (Quotient (attachSetoid n)) := compactSpace_attachSetoid n
  rw [continuous_iff_isClosed]
  intro U hU
  rw [invFun_preimage_eq_image n U]
  exact isClosedMap_phiQ n U hU

theorem attachCellsPUnitSphere (n : ℕ) :
    Nonempty (Work.RatHurewicz.attachCells n PUnit PUnit
        (fun _ : PUnit => ContinuousMap.const (Work.RatHurewicz.cellSphere n) PUnit.unit) ≃ₜ
      Work.RatHurewicz.cellSphere (n + 1)) := by
  haveI : CompactSpace (Quotient (attachSetoid n)) := compactSpace_attachSetoid n
  have hbij := phiQ_bijective n
  refine ⟨{ toFun := phiQ n
            invFun := Function.invFun (phiQ n)
            left_inv := fun x => Function.leftInverse_invFun hbij.1 x
            right_inv := fun y => Function.rightInverse_invFun hbij.2 y
            continuous_toFun := continuous_phiQ n
            continuous_invFun := continuous_invFun_phiQ n }⟩

end Work.Serre