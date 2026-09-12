import Mathlib
import Submission.LMProbs

/-!
Measurability of the walk and of the events of interest.  (All classical.)
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The cell where the frozen-variable set equals `A`. -/
lemma measurableSet_frozenVars_eq (δ : ℝ) (A : Finset (Fin n)) :
    MeasurableSet {x : Vec n | frozenVars δ x = A} := by
  have hset : {x : Vec n | frozenVars δ x = A} =
      {x : Vec n | ∀ i : Fin n, ((1 - δ ≤ |x i|) ↔ i ∈ A)} := by
    ext x
    unfold frozenVars
    simp [Finset.ext_iff]
  rw [hset]
  rw [show {x : Vec n | ∀ i : Fin n, ((1 - δ ≤ |x i|) ↔ i ∈ A)} =
      ⋂ i : Fin n, {x : Vec n | ((1 - δ ≤ |x i|) ↔ i ∈ A)} by
    ext x
    simp]
  refine MeasurableSet.iInter (fun i : Fin n => ?_)
  by_cases hiA : i ∈ A
  · have hs : {x : Vec n | ((1 - δ ≤ |x i|) ↔ i ∈ A)} = {x : Vec n | 1 - δ ≤ |x i|} := by
      ext x
      simp [hiA]
    rw [hs]
    rw [show {x : Vec n | 1 - δ ≤ |x i|} = (fun x : Vec n => |x i|) ⁻¹' Set.Ici (1 - δ) by
      ext x; simp]
    exact measurableSet_Ici.preimage (measurable_abs_coord n i)
  · have hs : {x : Vec n | ((1 - δ ≤ |x i|) ↔ i ∈ A)} = {x : Vec n | 1 - δ > |x i|} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [show (i ∈ A ↔ False) from ⟨fun h => hiA h, fun hf => False.elim hf⟩]
      rw [iff_false]
      exact not_le (a := 1 - δ) (b := |x i|)
    rw [hs]
    rw [show {x : Vec n | 1 - δ > |x i|} = (fun x : Vec n => |x i|) ⁻¹' Set.Iio (1 - δ) by
      ext x; simp]
    exact measurableSet_Iio.preimage (measurable_abs_coord n i)

/-- The cell where the frozen-row set equals `B`. -/
lemma measurableSet_frozenRows_eq (δ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (B : Finset ι) : MeasurableSet {x : Vec n | frozenRows δ x0 v c x = B} := by
  have hset : {x : Vec n | frozenRows δ x0 v c x = B} =
      {x : Vec n | ∀ j : ι, (((c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|) ↔ j ∈ B)} := by
    ext x
    unfold frozenRows
    simp [Finset.ext_iff]
  rw [hset]
  rw [show {x : Vec n | ∀ j : ι, (((c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|) ↔ j ∈ B)} =
      ⋂ j : ι, {x : Vec n | (((c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|) ↔ j ∈ B)} by
    ext x
    simp]
  refine MeasurableSet.iInter (fun j : ι => ?_)
  have h1 : Measurable (fun x : Vec n => |vin (x - x0) (v j)|) := by
    have hcont : Continuous (fun x : Vec n => vin (x - x0) (v j)) := by
      change Continuous ((fun p : Vec n × Vec n => ⟪p.1, p.2⟫) ∘ (fun x : Vec n => (x - x0, v j)))
      exact continuous_inner.comp (by fun_prop)
    exact hcont.measurable.abs
  by_cases hjB : j ∈ B
  · have hs : {x : Vec n | ((c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|) ↔ j ∈ B} =
        {x : Vec n | (c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|} := by
      ext x
      simp [hjB]
    rw [hs]
    rw [show {x : Vec n | (c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|} =
        (fun x : Vec n => |vin (x - x0) (v j)|) ⁻¹' Set.Ici ((c j - δ) * ‖v j‖) by ext x; simp]
    exact measurableSet_Ici.preimage h1
  · have hs : {x : Vec n | ((c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)|) ↔ j ∈ B} =
        {x : Vec n | (c j - δ) * ‖v j‖ > |vin (x - x0) (v j)|} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [show (j ∈ B ↔ False) from ⟨fun h => hjB h, fun hf => False.elim hf⟩]
      rw [iff_false]
      simpa using (not_le (a := (c j - δ) * ‖v j‖) (b := |vin (x - x0) (v j)|)).symm
    rw [hs]
    rw [show {x : Vec n | (c j - δ) * ‖v j‖ > |vin (x - x0) (v j)|} =
        (fun x : Vec n => |vin (x - x0) (v j)|) ⁻¹' Set.Iio ((c j - δ) * ‖v j‖) by ext x; simp]
    exact measurableSet_Iio.preimage h1

/-- Decomposition of the step into its frozen cells. -/
lemma walkStep_cell_sum (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (p : Vec n × Vec n) :
    walkStep δ γ x0 v c p.1 p.2 =
      ∑ A : Finset (Fin n), ∑ B : Finset ι,
        if frozenVars δ p.1 = A ∧ frozenRows δ x0 v c p.1 = B then
          p.1 + γ • walkProj v A B p.2 else 0 := by
  unfold walkStep
  rw [Finset.sum_eq_single (frozenVars δ p.1)]
  · rw [Finset.sum_eq_single (frozenRows δ x0 v c p.1)]
    · simp
    · intro B hB hne
      by_cases hB2 : frozenRows δ x0 v c p.1 = B
      · exact (hne hB2.symm).elim
      · simp [hB2]
    · intro hB
      exact (hB (Finset.mem_univ _)).elim
  · intro A hA hne
    rw [Finset.sum_eq_zero]
    intro B hB
    by_cases hA2 : frozenVars δ p.1 = A
    · exact (hne hA2.symm).elim
    · simp [hA2]
  · intro hA
    exact (hA (Finset.mem_univ _)).elim

/-- Projection is continuous in the vector. -/
lemma continuous_walkProj (v : ι → Vec n) (A : Finset (Fin n)) (B : Finset ι) :
    Continuous (fun g : Vec n => walkProj v A B g) := by
  unfold walkProj
  exact ((Wspan v A B)ᗮ).starProjection.continuous

/-- The step function is measurable (piecewise, over the frozen cells). -/
lemma measurable_walkStep (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) :
    Measurable (fun p : Vec n × Vec n => walkStep δ γ x0 v c p.1 p.2) := by
  rw [show (fun p : Vec n × Vec n => walkStep δ γ x0 v c p.1 p.2) =
      fun p => ∑ A : Finset (Fin n), ∑ B : Finset ι,
        if frozenVars δ p.1 = A ∧ frozenRows δ x0 v c p.1 = B then
          p.1 + γ • walkProj v A B p.2 else 0 by
    funext p
    exact walkStep_cell_sum δ γ x0 v c p]
  exact Finset.measurable_sum (Finset.univ : Finset (Finset (Fin n))) (by
    intro A hA
    exact Finset.measurable_sum (Finset.univ : Finset (Finset ι)) (by
      intro B hB
      have hcell : MeasurableSet {p : Vec n × Vec n |
          frozenVars δ p.1 = A ∧ frozenRows δ x0 v c p.1 = B} := by
        rw [show {p : Vec n × Vec n | frozenVars δ p.1 = A ∧ frozenRows δ x0 v c p.1 = B} =
            (Prod.fst ⁻¹' {x : Vec n | frozenVars δ x = A}) ∩
              (Prod.fst ⁻¹' {x : Vec n | frozenRows δ x0 v c x = B}) by ext p; simp]
        exact (measurableSet_frozenVars_eq δ A).preimage measurable_fst |>.inter
          ((measurableSet_frozenRows_eq δ x0 v c B).preimage measurable_fst)
      refine Measurable.ite hcell ?_ (by simp)
      have hc1 : Continuous (fun p : Vec n × Vec n => p.1) := continuous_fst
      have hc2 : Continuous (fun p : Vec n × Vec n => γ • walkProj v A B p.2) := by
        exact (continuous_walkProj v A B).comp continuous_snd |>.const_smul γ
      exact (hc1.add hc2).measurable))

/-- Measurability of the trajectory (for `t ≤ T`). -/
lemma measurable_Xn {T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) :
    Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) := by
  induction t with
  | zero =>
      simpa [Xn] using (measurable_const : Measurable (fun _ : Omega n T => x0))
  | succ t ih =>
      have ht2 : t < T := Nat.lt_of_succ_le ht
      have hor : Measurable (fun ω : Omega n T => oracle n T ω t) := by
        by_cases ht3 : t < T
        · rw [show (fun ω : Omega n T => oracle n T ω t) = (fun ω : Omega n T => ω ⟨t, ht3⟩) by
            funext ω; simp [oracle, ht3]]
          exact measurable_pi_apply (⟨t, ht3⟩ : Fin T)
        · rw [show (fun ω : Omega n T => oracle n T ω t) = (fun _ : Omega n T => (0 : Vec n)) by
            funext ω; simp [oracle, ht3]]
          fun_prop
      have hcomp : Measurable (fun ω : Omega n T => (Xn n T δ γ x0 v c ω t, oracle n T ω t)) := by
        exact (ih (Nat.le_of_succ_le ht)).prodMk hor
      have hstep := measurable_walkStep (n := n) (ι := ι) δ γ x0 v c
      have h : (fun ω : Omega n T => Xn n T δ γ x0 v c ω (t + 1)) =
          (fun p : Vec n × Vec n => walkStep δ γ x0 v c p.1 p.2) ∘
            (fun ω : Omega n T => (Xn n T δ γ x0 v c ω t, oracle n T ω t)) := by
        funext ω
        rw [Xn_succ (n := n) (T := T) δ γ x0 v c ω t ht2]
        rfl
      rw [h]
      exact hstep.comp hcomp

/-- Membership of a coordinate in the frozen set after `t` steps is measurable. -/
lemma measurableSet_frozen_coord {T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (i : Fin n) : MeasurableSet {ω : Omega n T | i ∈ frozenVars δ (Xn n T δ γ x0 v c ω t)} := by
  have h : {ω : Omega n T | i ∈ frozenVars δ (Xn n T δ γ x0 v c ω t)} =
      {ω : Omega n T | 1 - δ ≤ |(Xn n T δ γ x0 v c ω t) i|} := by
    ext ω
    unfold frozenVars
    simp
  rw [h]
  exact measurableSet_Ici.preimage ((measurable_abs_coord n i).comp
    (measurable_Xn (n := n) (ι := ι) ht δ γ x0 v c))

/-- Membership of a row in the frozen set after `t` steps is measurable. -/
lemma measurableSet_frozen_row {T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (j : ι) : MeasurableSet {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)} := by
  have h : {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)} =
      {ω : Omega n T | (c j - δ) * ‖v j‖ ≤
        |vin (Xn n T δ γ x0 v c ω t - x0) (v j)|} := by
    ext ω
    unfold frozenRows
    simp
  rw [h]
  have h1 : Measurable (fun ω : Omega n T => |vin (Xn n T δ γ x0 v c ω t - x0) (v j)|) := by
    have hm : Measurable (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω t - x0) (v j)) := by
      change Measurable ((fun x : Vec n => vin x (v j)) ∘
        (fun ω : Omega n T => Xn n T δ γ x0 v c ω t - x0))
      exact (measurable_vin n (v j)).comp
        ((measurable_Xn (n := n) (ι := ι) ht δ γ x0 v c).sub measurable_const)
    exact hm.abs
  exact measurableSet_Ici.preimage h1

/-- Count of frozen rows equals a sum of indicators (real form). -/
lemma frozenRows_card_eq_sum' {T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) :
    ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)).card : ℝ) =
      ∑ j : ι, (if j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) then (1 : ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones]
  norm_num

/-- Count of frozen coordinates equals a sum of indicators (real form). -/
lemma frozenVars_card_eq_sum' {T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) :
    ((frozenVars δ (Xn n T δ γ x0 v c ω t)).card : ℝ) =
      ∑ i : Fin n, (if i ∈ frozenVars δ (Xn n T δ γ x0 v c ω t) then (1 : ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones]
  norm_num

/-- The number of frozen coordinates as a measurable function (into ℝ). -/
lemma measurable_frozenVars_card {T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) : Measurable (fun ω : Omega n T => ((frozenVars δ (Xn n T δ γ x0 v c ω t)).card : ℝ)) := by
  have h : (fun ω : Omega n T => ((frozenVars δ (Xn n T δ γ x0 v c ω t)).card : ℝ)) =
      fun ω => ∑ i : Fin n, (if i ∈ frozenVars δ (Xn n T δ γ x0 v c ω t) then (1 : ℝ) else 0) := by
    funext ω
    rw [frozenVars_card_eq_sum' (n := n) (T := T) (t := t) (ht := ht) δ γ x0 v c ω]
  rw [h]
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n)) (by
    intro i hi
    exact Measurable.ite (measurableSet_frozen_coord (n := n) (ι := ι) ht δ γ x0 v c i)
      (by simp) (by simp))



/-- Curried `Fin.snoc` is continuous, hence measurable. -/
lemma continuous_snoc_curry (n : ℕ) (T : ℕ) :
    Continuous (fun y : Vec n × Omega n T =>
      Fin.snoc (α := fun _ : Fin (T + 1) => Vec n) y.2 y.1) := by
  refine continuous_pi ?_
  intro i
  by_cases h : (i : ℕ) < T
  · have hcast : i = ((⟨i.val, h⟩ : Fin T).castSucc : Fin (T + 1)) := by
      apply Fin.ext
      rfl
    rw [hcast]
    simp only [Fin.snoc_castSucc]
    exact (continuous_apply (⟨i.val, h⟩ : Fin T)).comp continuous_snd
  · have hi : i = Fin.last T := by
      apply Fin.ext
      simp [Fin.last]
      omega
    rw [hi]
    simp only [Fin.snoc_last]
    exact continuous_fst

lemma measurable_snoc_curry (n : ℕ) (T : ℕ) :
    Measurable (fun y : Vec n × Omega n T =>
      Fin.snoc (α := fun _ : Fin (T + 1) => Vec n) y.2 y.1) :=
  (continuous_snoc_curry n T).measurable

end Discrepancy

end Submission