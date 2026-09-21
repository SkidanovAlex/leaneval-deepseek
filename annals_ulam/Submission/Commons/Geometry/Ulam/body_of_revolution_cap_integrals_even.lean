import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Commons.Geometry.Ulam.sum_Ioi_fin_succ
import Submission.Commons.Geometry.Ulam.integral_fin_ball_coord_zero

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-! ## Coordinate splitting for an even body of revolution -/

def lastFin (d : ℕ) [NeZero d] : Fin d :=
  ⟨d - 1, by have hpos : 0 < d := Nat.pos_of_neZero d; omega⟩

def middleIndex (d : ℕ) (h2 : 2 ≤ d) (j : Fin (d - 2)) : Fin d :=
  ⟨j.val + 1, by have hj := j.isLt; omega⟩

lemma middleIndex_ne_zero (d : ℕ) (h2 : 2 ≤ d) [NeZero d] (j : Fin (d - 2)) :
    middleIndex d h2 j ≠ 0 := by
  intro h
  have hval := congr_arg Fin.val h
  change j.val + 1 = 0 at hval
  exact Nat.succ_ne_zero j.val hval

lemma middleIndex_ne_last (d : ℕ) (h2 : 2 ≤ d) [NeZero d] (j : Fin (d - 2)) :
    middleIndex d h2 j ≠ lastFin d := by
  intro h
  have hj := j.isLt
  have hval := congr_arg Fin.val h
  change j.val + 1 = d - 1 at hval
  omega

def isolateFirst (d : ℕ) (hpos : 0 < d) :
    (Fin d → ℝ) ≃ᵐ ℝ × (Fin (d - 1) → ℝ) := by
  let hd : d = (d - 1) + 1 := by omega
  let ecast : (Fin d → ℝ) ≃ᵐ (Fin ((d - 1) + 1) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin ((d - 1) + 1) => ℝ) (finCongr hd)
  let e1 : (Fin ((d - 1) + 1) → ℝ) ≃ᵐ ℝ × (Fin (d - 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin ((d - 1) + 1) => ℝ) 0
  exact ecast.trans e1

lemma isolateFirst_measurePreserving (d : ℕ) (hpos : 0 < d) :
    MeasurePreserving (isolateFirst d hpos) volume volume := by
  unfold isolateFirst
  have hd : d = (d - 1) + 1 := by omega
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin ((d - 1) + 1) => ℝ) (finCongr hd)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin ((d - 1) + 1) => ℝ) 0)

lemma isolateFirst_fst (d : ℕ) [NeZero d] (hpos : 0 < d) (x : Fin d → ℝ) :
    (isolateFirst d hpos x).1 = x 0 := by
  simp [isolateFirst]
  have hd : d = (d - 1) + 1 := by omega
  rw [show (0 : Fin ((d - 1) + 1)) = finCongr hd (0 : Fin d) by
    apply Fin.ext; simp [finCongr_apply_coe]]
  exact MeasurableEquiv.piCongrLeft_apply_apply (e := finCongr hd)
    (β := fun _ : Fin ((d - 1) + 1) => ℝ) x (0 : Fin d)

lemma isolateFirst_snd (d : ℕ) [NeZero d] (hpos : 0 < d) (x : Fin d → ℝ) (j : Fin (d-1)) :
    (isolateFirst d hpos x).2 j = x ⟨j.val+1, by omega⟩ := by
  simp [isolateFirst]
  have hd : d = (d - 1) + 1 := by omega
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin ((d - 1) + 1) => ℝ) (finCongr hd)) x (Fin.succ j) = x ⟨j.val+1, by omega⟩
  rw [show (Fin.succ j : Fin ((d - 1) + 1)) = finCongr hd ⟨j.val+1, by omega⟩ by
    apply Fin.ext; simp [finCongr_apply_coe]]
  exact MeasurableEquiv.piCongrLeft_apply_apply (e := finCongr hd)
    (β := fun _ : Fin ((d - 1) + 1) => ℝ) x ⟨j.val+1, by omega⟩

def isolateLast (d : ℕ) (h2 : 2 ≤ d) :
    (Fin (d - 1) → ℝ) ≃ᵐ ℝ × (Fin (d - 2) → ℝ) := by
  let hd1 : d - 1 = (d - 2) + 1 := by omega
  let ecast : (Fin (d - 1) → ℝ) ≃ᵐ (Fin ((d - 2) + 1) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin ((d - 2) + 1) => ℝ) (finCongr hd1)
  let last1 : Fin ((d - 2) + 1) := ⟨d - 2, by omega⟩
  let e2 : (Fin ((d - 2) + 1) → ℝ) ≃ᵐ ℝ × (Fin (d - 2) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin ((d - 2) + 1) => ℝ) last1
  exact ecast.trans e2

lemma isolateLast_measurePreserving (d : ℕ) (h2 : 2 ≤ d) :
    MeasurePreserving (isolateLast d h2) volume volume := by
  unfold isolateLast
  have hd1 : d - 1 = (d - 2) + 1 := by omega
  let last1 : Fin ((d - 2) + 1) := ⟨d - 2, by omega⟩
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin ((d - 2) + 1) => ℝ) (finCongr hd1)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin ((d - 2) + 1) => ℝ) last1)

lemma isolateLast_fst (d : ℕ) (h2 : 2 ≤ d) (y : Fin (d - 1) → ℝ) :
    (isolateLast d h2 y).1 = y ⟨d - 2, by omega⟩ := by
  simp [isolateLast]
  have hd1 : d - 1 = (d - 2) + 1 := by omega
  let idx : Fin ((d - 2) + 1) := ⟨d - 2, by omega⟩
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin ((d - 2) + 1) => ℝ) (finCongr hd1)) y idx =
    y ⟨d - 2, by omega⟩
  rw [show idx = finCongr hd1 ⟨d - 2, by omega⟩ by
    apply Fin.ext; simp [idx, finCongr_apply_coe]]
  exact MeasurableEquiv.piCongrLeft_apply_apply (e := finCongr hd1)
    (β := fun _ : Fin ((d - 2) + 1) => ℝ) y ⟨d - 2, by omega⟩

lemma isolateLast_snd (d : ℕ) (h2 : 2 ≤ d) (y : Fin (d - 1) → ℝ) (j : Fin (d - 2)) :
    (isolateLast d h2 y).2 j = y ⟨j.val, by omega⟩ := by
  simp [isolateLast]
  have hd1 : d - 1 = (d - 2) + 1 := by omega
  let last1 : Fin ((d - 2) + 1) := ⟨d - 2, by omega⟩
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin ((d - 2) + 1) => ℝ) (finCongr hd1)) y (last1.succAbove j) = y ⟨j.val, by omega⟩
  have hsucc : last1.succAbove j = (finCongr hd1) ⟨j.val, by omega⟩ := by
    apply Fin.ext
    have hlast1 : last1 = Fin.last (d - 2) := by
      ext; simp [last1]
    rw [hlast1, Fin.succAbove_last]
    simp [finCongr_apply_coe]
  rw [hsucc]
  exact MeasurableEquiv.piCongrLeft_apply_apply (e := finCongr hd1)
    (β := fun _ : Fin ((d - 2) + 1) => ℝ) y ⟨j.val, by omega⟩

def coordDecomp (d : ℕ) (h2 : 2 ≤ d) [NeZero d] :
    (Fin d → ℝ) ≃ᵐ ℝ × (ℝ × (Fin (d - 2) → ℝ)) :=
  (isolateFirst d (by omega)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (isolateLast d h2))

lemma coordDecomp_measurePreserving (d : ℕ) (h2 : 2 ≤ d) [NeZero d] :
    MeasurePreserving (coordDecomp d h2)
      (volume : Measure (Fin d → ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin (d - 2) → ℝ)))) := by
  unfold coordDecomp
  have hfirst : MeasurePreserving (isolateFirst d (by omega))
      (volume : Measure (Fin d → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin (d - 1) → ℝ))) := by
    convert isolateFirst_measurePreserving d (by omega) <;> rfl
  have hlast : MeasurePreserving (isolateLast d h2)
      (volume : Measure (Fin (d - 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin (d - 2) → ℝ))) := by
    convert isolateLast_measurePreserving d h2 <;> rfl
  have hprod : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr (isolateLast d h2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin (d - 1) → ℝ)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin (d - 2) → ℝ)))) := by
    exact MeasurePreserving.prod (MeasurePreserving.id volume) hlast
  exact hfirst.trans hprod

lemma coordDecomp_fst (d : ℕ) (h2 : 2 ≤ d) [NeZero d] (x : Fin d → ℝ) :
    (coordDecomp d h2 x).1 = x 0 := by
  unfold coordDecomp
  change ((Prod.map id (isolateLast d h2) ((isolateFirst d (by omega)) x)).1) = x 0
  simp [isolateFirst_fst]

lemma coordDecomp_snd_fst (d : ℕ) (h2 : 2 ≤ d) [NeZero d] (x : Fin d → ℝ) :
    (coordDecomp d h2 x).2.1 = x (lastFin d) := by
  unfold coordDecomp
  change ((Prod.map id (isolateLast d h2) ((isolateFirst d (by omega)) x)).2.1) = x (lastFin d)
  simp [isolateLast_fst, isolateFirst_snd]
  apply congrArg x
  apply Fin.ext
  simp [lastFin]
  omega

lemma coordDecomp_snd_snd (d : ℕ) (h2 : 2 ≤ d) [NeZero d] (x : Fin d → ℝ) (j : Fin (d - 2)) :
    (coordDecomp d h2 x).2.2 j = x (middleIndex d h2 j) := by
  unfold coordDecomp
  change ((Prod.map id (isolateLast d h2) ((isolateFirst d (by omega)) x)).2.2 j) = x (middleIndex d h2 j)
  simp [isolateLast_snd, isolateFirst_snd]
  apply congrArg x
  apply Fin.ext
  simp [middleIndex]

lemma sum_Ioi_eq_last_add_middle {d : ℕ} [NeZero d] (h2 : 2 ≤ d) (x : Fin d → ℝ) :
    (∑ i > (0 : Fin d), (x i)^2) =
      (x (lastFin d))^2 + ∑ j : Fin (d - 2), (x (middleIndex d h2 j))^2 := by
  rw [Commons.Geometry.Ulam.sum_Ioi_fin_succ]
  have hd1 : d - 1 = (d - 2) + 1 := by omega
  let hcast : (d - 1) + 1 = d := by omega
  rw [← Equiv.sum_comp (e := finCongr hd1.symm)
    (g := fun j : Fin (d - 1) => (x (Fin.cast hcast j.succ))^2)]
  rw [Fin.sum_univ_castSucc]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply congrArg (fun i : Fin d => x i ^ 2)
    apply Fin.ext
    simp [lastFin]
    omega
  · apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun i : Fin d => x i ^ 2)
    apply Fin.ext
    simp [middleIndex]

/-! ## Volume of the Euclidean ball cross-section -/

lemma MeasurePreserving.measureReal_preimage_emb {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} {e : α ≃ᵐ β}
    (h : MeasurePreserving (⇑e) μa μb) (S : Set β) :
    μa.real (e ⁻¹' S) = μb.real S := by
  rw [Measure.real, Measure.real, h.measure_preimage_emb e.measurableEmbedding]

lemma MeasurePreserving.setIntegral_comp' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} {e : α ≃ᵐ β}
    (h : MeasurePreserving (⇑e) μa μb) (g : β → ℝ) (S : Set β) (hS : MeasurableSet S) :
    ∫ x in e ⁻¹' S, g (e x) ∂μa = ∫ y in S, g y ∂μb := by
  calc
    ∫ x in e ⁻¹' S, g (e x) ∂μa
        = ∫ x, (e ⁻¹' S).indicator (fun x => g (e x)) x ∂μa := by
            rw [integral_indicator (hS.preimage e.measurable)]
    _ = ∫ x, S.indicator g (e x) ∂μa := by
            simp [Set.indicator, Set.preimage]
    _ = ∫ y, S.indicator g y ∂μb := h.integral_comp' _
    _ = ∫ y in S, g y ∂μb := by rw [integral_indicator hS]

lemma volume_real_closedBall_zero_smul {m : ℕ} [Nonempty (Fin m)] (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R) =
      volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) * R ^ m := by
  simp only [Measure.real, EuclideanSpace.volume_closedBall]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1:ℝ))]
  simp [Fintype.card_fin]
  ring_nf

lemma volume_real_fin_ball_pow {m : ℕ} [Nonempty (Fin m)] (R : ℝ) (hR : 0 ≤ R) :
    volume.real {y : Fin m → ℝ | ∑ j, (y j)^2 ≤ R^2} =
      volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) * R ^ m := by
  let e : (Fin m → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin m) := MeasurableEquiv.toLp 2 (Fin m → ℝ)
  have hmp : MeasurePreserving (⇑e) volume volume := PiLp.volume_preserving_toLp (ι := Fin m)
  have hset : {y : Fin m → ℝ | ∑ j, (y j)^2 ≤ R^2} =
      e ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      have hnorm2 : ‖e y‖ ^ 2 = ∑ j, (y j)^2 := by
        simp [e, PiLp.norm_sq_eq_of_L2]
      have hsq : ‖e y‖ ^ 2 ≤ R ^ 2 := by simpa [hnorm2] using hy
      exact le_of_sq_le_sq hsq hR
    · intro hy
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hy
      have hnorm2 : ‖e y‖ ^ 2 = ∑ j, (y j)^2 := by
        simp [e, PiLp.norm_sq_eq_of_L2]
      have hsq : ‖e y‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by nlinarith [norm_nonneg (e y), hR]) hy
      simpa [hnorm2] using hsq
  rw [hset, MeasurePreserving.measureReal_preimage_emb hmp]
  exact volume_real_closedBall_zero_smul R hR


lemma volume_real_fin_ball_pow_two {m n : ℕ} [Nonempty (Fin m)] (R : ℝ) (hR : 0 ≤ R)
    (hm : m = 2 * n) :
    volume.real {y : Fin m → ℝ | ∑ j, (y j)^2 ≤ R^2} =
      volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) * (R ^ 2) ^ n := by
  rw [volume_real_fin_ball_pow R hR]
  congr 1
  rw [hm]
  rw [pow_mul]

lemma volume_real_cap_section {m n : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ}
    (hm : m = 2 * (n - 1)) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (t z : ℝ) :
    let U : ℝ := max (-f t) (min (f t) (s * t + h))
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    let B : Set (Fin m → ℝ) :=
      {y | t ∈ Set.Icc a b ∧ z ≤ s * t + h ∧ z ^ 2 + ∑ j : Fin m, (y j)^2 ≤ f t ^ 2}
    volume.real B =
      (Set.Icc a b).indicator (fun _ => (Set.Icc (-f t) U).indicator (fun _ => c * (f t ^ 2 - z ^ 2) ^ (n - 1)) z) t := by
  classical
  intro U c B
  let L : ℝ := s * t + h
  have hU : U = max (-f t) (min (f t) L) := rfl
  by_cases ht : t ∈ Set.Icc a b
  · have hf_nonneg_t : 0 ≤ f t := hf_nonneg t ht
    by_cases hz : z ∈ Set.Icc (-f t) U
    · rw [Set.indicator_of_mem ht]
      rw [Set.indicator_of_mem hz]
      have hz_ge : -f t ≤ z := hz.1
      have hz_le_U : z ≤ U := hz.2
      have hU_le_f : U ≤ f t := by
        rw [hU]
        exact max_le (by linarith) (min_le_left _ _)
      have hz_le_f : z ≤ f t := le_trans hz_le_U hU_le_f
      have hzsq_le : z ^ 2 ≤ f t ^ 2 := (sq_le_sq' hz_ge hz_le_f : z ^ 2 ≤ f t ^ 2)
      by_cases hzL : z ≤ L
      · have hB_eq : B = {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
          ext y
          simp only [B, Set.mem_setOf_eq]
          constructor
          · intro hy
            rcases hy with ⟨_, _, hsum⟩
            nlinarith
          · intro hy
            refine ⟨ht, hzL, ?_⟩
            nlinarith
        rw [hB_eq]
        let R : ℝ := Real.sqrt (f t ^ 2 - z ^ 2)
        have hR : 0 ≤ R := Real.sqrt_nonneg _
        have hR2 : R ^ 2 = f t ^ 2 - z ^ 2 := by
          dsimp [R]
          exact Real.sq_sqrt (by nlinarith [hzsq_le])
        rw [← hR2]
        rw [volume_real_fin_ball_pow_two R hR hm]
      · have hz_eq : z = -f t := by
          by_contra hne
          have hz_gt : -f t < z := lt_of_le_of_ne hz_ge (Ne.symm hne)
          by_cases hmin : min (f t) L ≤ -f t
          · have hUeq : U = -f t := by rw [hU, max_eq_left hmin]
            linarith [hz_gt, hz_le_U, hUeq]
          · have hmin_gt : -f t < min (f t) L := lt_of_not_ge hmin
            have hUeq : U = min (f t) L := by rw [hU, max_eq_right (le_of_lt hmin_gt)]
            have hU_le_L : U ≤ L := by rw [hUeq]; exact min_le_right _ _
            exact hzL (le_trans hz_le_U hU_le_L)
        have hB_empty : B = ∅ := by
          ext y
          simp only [B, Set.mem_empty_iff_false]
          constructor
          · intro hy
            exact hzL hy.2.1
          · intro hy
            exact False.elim hy
        rw [hB_empty]
        simp [hz_eq, zero_pow (by omega : n - 1 ≠ 0)]
    · rw [Set.indicator_of_mem ht]
      simp [hz]
      have hB_empty : B = ∅ := by
        ext y
        simp only [B, Set.mem_empty_iff_false]
        constructor
        · intro hy
          rcases hy with ⟨_, hzL, hsum⟩
          have hzsq_le : z ^ 2 ≤ f t ^ 2 := by
            have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by positivity
            nlinarith
          have hz_abs_le : |z| ≤ f t := abs_le_of_sq_le_sq hzsq_le hf_nonneg_t
          have hz_ge : -f t ≤ z := (abs_le.mp hz_abs_le).1
          have hz_le_f : z ≤ f t := (abs_le.mp hz_abs_le).2
          have hz_le_min : z ≤ min (f t) L := le_min hz_le_f hzL
          have hz_le_U : z ≤ U := by
            rw [hU]
            exact le_trans hz_le_min (le_max_right _ _)
          exact hz ⟨hz_ge, hz_le_U⟩
        · intro hy
          exact False.elim hy
      simp [hB_empty]
  · simp [ht]
    have hB_empty : B = ∅ := by
      ext y
      simp only [B, Set.mem_empty_iff_false]
      constructor
      · intro hy
        exact ht hy.1
      · intro hy
        exact False.elim hy
    simp [hB_empty]

lemma volume_fin_ball_lt_top {m : ℕ} [Nonempty (Fin m)] (R : ℝ) :
    volume {y : Fin m → ℝ | ∑ j, (y j)^2 ≤ R^2} < ⊤ := by
  let Rpos : ℝ := |R|
  have hRpos : 0 ≤ Rpos := abs_nonneg R
  have hR2 : R ^ 2 = Rpos ^ 2 := by
    dsimp [Rpos]
    rw [sq_abs]
  let e : (Fin m → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin m) := MeasurableEquiv.toLp 2 (Fin m → ℝ)
  have hmp : MeasurePreserving (⇑e) volume volume := PiLp.volume_preserving_toLp (ι := Fin m)
  have hset : {y : Fin m → ℝ | ∑ j, (y j)^2 ≤ R^2} =
      e ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) Rpos := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      have hnorm2 : ‖e y‖ ^ 2 = ∑ j, (y j)^2 := by
        simp [e, PiLp.norm_sq_eq_of_L2]
      have hsq : ‖e y‖ ^ 2 ≤ Rpos ^ 2 := by
        simpa [hnorm2, ← hR2] using hy
      exact le_of_sq_le_sq hsq hRpos
    · intro hy
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hy
      have hnorm2 : ‖e y‖ ^ 2 = ∑ j, (y j)^2 := by
        simp [e, PiLp.norm_sq_eq_of_L2]
      have hsq : ‖e y‖ ^ 2 ≤ Rpos ^ 2 := sq_le_sq' (by nlinarith [norm_nonneg (e y), hRpos]) hy
      simpa [hnorm2, ← hR2] using hsq
  rw [hset, hmp.measure_preimage_emb e.measurableEmbedding]
  exact measure_closedBall_lt_top

lemma volume_cap_section_lt_top {m n : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ}
    (t z : ℝ) :
    volume {y : Fin m → ℝ | t ∈ Set.Icc a b ∧ z ≤ s * t + h ∧
      z ^ 2 + ∑ j : Fin m, (y j)^2 ≤ f t ^ 2} < ⊤ := by
  let B : Set (Fin m → ℝ) :=
    {y | t ∈ Set.Icc a b ∧ z ≤ s * t + h ∧ z ^ 2 + ∑ j : Fin m, (y j)^2 ≤ f t ^ 2}
  let R : ℝ := |f t|
  have hsub : B ⊆ {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R ^ 2} := by
    intro y hy
    rcases hy with ⟨_, _, hsum⟩
    have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by positivity
    have hle : ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 := by nlinarith
    rw [sq_abs]
    exact hle
  exact lt_of_le_of_lt (measure_mono hsub) (volume_fin_ball_lt_top R)

lemma integral_prod_section_volume {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μa : Measure α} {μb : Measure β} {μc : Measure γ}
    [SFinite μa] [SFinite μb] [SFinite μc]
    {B : α → β → Set γ} {φ : α × β → ℝ}
    (hφ_meas : Measurable φ)
    (hB_meas : MeasurableSet {p : α × (β × γ) | p.2.2 ∈ B p.1 p.2.1})
    (hB_finite : ∀ a b, μc (B a b) ≠ ⊤) :
    ∫ p : α × (β × γ),
        φ (p.1, p.2.1) * (B p.1 p.2.1).indicator (fun _ : γ => (1 : ℝ)) p.2.2
        ∂(μa.prod (μb.prod μc)) =
    ∫ p : α × β,
        φ p * μc.real (B p.1 p.2)
        ∂(μa.prod μb) := by
  classical
  let e : (α × (β × γ)) ≃ᵐ (α × β) × γ := (MeasurableEquiv.prodAssoc).symm
  let S : Set (α × (β × γ)) := {p | p.2.2 ∈ B p.1 p.2.1}
  let F : α × (β × γ) → ℝ := fun p =>
    φ (p.1, p.2.1) * (B p.1 p.2.1).indicator (fun _ : γ => (1 : ℝ)) p.2.2
  let F' : (α × β) × γ → ℝ := fun p =>
    φ p.1 * (B p.1.1 p.1.2).indicator (fun _ : γ => (1 : ℝ)) p.2
  let G : α × β → ℝ := fun p => φ p * μc.real (B p.1 p.2)
  have hF_eq : F = fun p => F' (e p) := by
    ext p; rfl
  have he_mp : MeasurePreserving (⇑e) (μa.prod (μb.prod μc)) ((μa.prod μb).prod μc) := by
    exact (measurePreserving_prodAssoc μa μb μc).symm
  have hS_meas : MeasurableSet S := by
    simpa [S] using hB_meas
  have hF_meas : Measurable F := by
    dsimp [F]
    have hφ' : Measurable (fun p : α × (β × γ) => φ (p.1, p.2.1)) :=
      hφ_meas.comp (Measurable.prod measurable_fst (measurable_fst.comp measurable_snd))
    exact hφ'.mul (Measurable.indicator measurable_const hS_meas)
  have hF'_meas : Measurable F' := by
    have hcomp : F' = F ∘ (⇑e.symm) := by
      ext p; rfl
    simpa [hcomp] using hF_meas.comp e.symm.measurable
  have hB_section_meas : ∀ a b, MeasurableSet (B a b) := by
    intro a b
    let S' : Set ((α × β) × γ) := {p | p.2 ∈ B p.1.1 p.1.2}
    have hS'_meas : MeasurableSet S' := by
      have hS'_eq : S' = e.symm ⁻¹' S := by
        ext p; rfl
      rw [hS'_eq]
      exact hS_meas.preimage e.symm.measurable
    have hsec : MeasurableSet (Prod.mk (a,b) ⁻¹' S') :=
      hS'_meas.preimage (measurable_prodMk_left (x := (a, b)))
    simpa [S'] using hsec
  have hF'_sections_int : ∀ p : α × β, Integrable (fun y : γ => F' (p, y)) μc := by
    intro p
    have hmeas : MeasurableSet (B p.1 p.2) := hB_section_meas p.1 p.2
    have hIntOn : IntegrableOn (fun _ : γ => φ p) (B p.1 p.2) μc := by
      exact MeasureTheory.integrableOn_const (μ := μc) (s := B p.1 p.2) (C := φ p)
        (hB_finite p.1 p.2) (by simp)
    have hind : Integrable ((B p.1 p.2).indicator (fun _ : γ => φ p)) μc :=
      MeasureTheory.IntegrableOn.integrable_indicator hIntOn hmeas
    refine hind.congr (Filter.Eventually.of_forall ?_)
    intro y
    dsimp [F']
    by_cases hy : y ∈ B p.1 p.2 <;> simp [hy]
  have hinner_norm_eq : ∀ p : α × β,
      (∫ y : γ, ‖F' (p, y)‖ ∂μc) = |φ p| * μc.real (B p.1 p.2) := by
    intro p
    have hmeas : MeasurableSet (B p.1 p.2) := hB_section_meas p.1 p.2
    have hnorm : (∫ y : γ, ‖F' (p, y)‖ ∂μc) =
        ∫ y : γ, |φ p| * (B p.1 p.2).indicator (fun _ : γ => (1 : ℝ)) y ∂μc := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [F']
      rw [abs_mul]
      congr 1
      by_cases hy : y ∈ B p.1 p.2 <;> simp [hy]
    rw [hnorm, MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_indicator hmeas]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real]
  have hG_meas : Measurable G := by
    let S' : Set ((α × β) × γ) := {p | p.2 ∈ B p.1.1 p.1.2}
    have hS'_meas : MeasurableSet S' := by
      have hS'_eq : S' = e.symm ⁻¹' S := by
        ext p; rfl
      rw [hS'_eq]
      exact hS_meas.preimage e.symm.measurable
    have hsec_meas : Measurable (fun p : α × β => μc (B p.1 p.2)) := by
      have hsec_meas' : Measurable (fun p : α × β => μc (Prod.mk p ⁻¹' S')) :=
        measurable_measure_prodMk_left (ν := μc) (s := S') hS'_meas
      simpa [S'] using hsec_meas'
    dsimp [G]
    exact hφ_meas.mul (hsec_meas.ennreal_toReal)
  have hF'_aestrong : AEStronglyMeasurable F' ((μa.prod μb).prod μc) :=
    hF'_meas.aestronglyMeasurable
  have hG_aestrong : AEStronglyMeasurable G (μa.prod μb) :=
    hG_meas.aestronglyMeasurable
  have hvol_nonneg : ∀ p : α × β, 0 ≤ μc.real (B p.1 p.2) := by
    intro p; exact MeasureTheory.measureReal_nonneg
  have hG_abs_eq : (fun p : α × β => |G p|) =ᵐ[μa.prod μb]
      (fun p => |φ p| * μc.real (B p.1 p.2)) := by
    filter_upwards with p
    dsimp [G]
    rw [abs_mul, abs_of_nonneg (hvol_nonneg p)]
  have hinner_norm_eq_ae : (fun p : α × β => ∫ y : γ, ‖F' (p, y)‖ ∂μc) =ᵐ[μa.prod μb]
      (fun p => |φ p| * μc.real (B p.1 p.2)) := by
    exact Filter.Eventually.of_forall hinner_norm_eq
  have hF_int_iff :
      Integrable F' ((μa.prod μb).prod μc) ↔ Integrable G (μa.prod μb) := by
    rw [MeasureTheory.integrable_prod_iff hF'_aestrong]
    constructor
    · intro h
      rcases h with ⟨hsec, hnorm_int⟩
      have hnorm_int' : Integrable (fun p : α × β => |φ p| * μc.real (B p.1 p.2)) (μa.prod μb) :=
        hnorm_int.congr hinner_norm_eq_ae
      have hG_abs_int : Integrable (fun p : α × β => |G p|) (μa.prod μb) :=
        hnorm_int'.congr hG_abs_eq.symm
      exact Integrable.mono' hG_abs_int hG_aestrong (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs]))
    · intro hGint
      have hG_abs_int : Integrable (fun p : α × β => |G p|) (μa.prod μb) := hGint.abs
      have hnorm_int : Integrable (fun p : α × β => |φ p| * μc.real (B p.1 p.2)) (μa.prod μb) :=
        hG_abs_int.congr hG_abs_eq
      refine ⟨Filter.Eventually.of_forall hF'_sections_int, ?_⟩
      exact hnorm_int.congr hinner_norm_eq_ae.symm
  by_cases hFint : Integrable F' ((μa.prod μb).prod μc)
  · have hGint : Integrable G (μa.prod μb) := hF_int_iff.mp hFint
    calc
      ∫ p : α × (β × γ), F p ∂(μa.prod (μb.prod μc))
          = ∫ p : (α × β) × γ, F' p ∂((μa.prod μb).prod μc) := by
              rw [hF_eq, MeasurePreserving.integral_comp' he_mp F']
      _ = ∫ p : α × β, ∫ y : γ, F' (p, y) ∂μc ∂(μa.prod μb) := by
              rw [MeasureTheory.integral_prod F' hFint]
      _ = ∫ p : α × β, G p ∂(μa.prod μb) := by
              apply integral_congr_ae
              filter_upwards with p
              dsimp [F', G]
              have hmeas : MeasurableSet (B p.1 p.2) := hB_section_meas p.1 p.2
              rw [MeasureTheory.integral_const_mul]
              rw [MeasureTheory.integral_indicator hmeas]
              rw [MeasureTheory.setIntegral_const]
              simp [Measure.real]
  · have hGnot : ¬ Integrable G (μa.prod μb) := by
      intro hGint; exact hFint (hF_int_iff.mpr hGint)
    change ∫ p : α × (β × γ), F p ∂(μa.prod (μb.prod μc)) = ∫ p : α × β, G p ∂(μa.prod μb)
    rw [hF_eq, MeasurePreserving.integral_comp' he_mp F']
    rw [MeasureTheory.integral_undef hFint, MeasureTheory.integral_undef hGnot]

lemma toLp_preimage_coord {d : ℕ} (i : Fin d) (S : Set ℝ) :
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)) ⁻¹' {x : EuclideanSpace ℝ (Fin d) | x i ∈ S} =
      {y : Fin d → ℝ | y i ∈ S} := by
  ext y
  rw [Set.mem_preimage, Set.mem_setOf_eq]
  simp [PiLp.toLp_apply]

lemma coordDecomp_preimage_set {d : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    (h2 : 2 ≤ d) :
    let Kfun : Set (Fin d → ℝ) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > (0 : Fin d), (x i)^2 ≤ f (x 0)^2}
    let Hfun : Set (Fin d → ℝ) := {x | x (lastFin d) ≤ s * x 0 + h}
    let Kprod : Set (ℝ × (ℝ × (Fin (d - 2) → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin (d - 2), (p.2.2 j)^2 ≤ f p.1^2}
    Kfun ∩ Hfun = coordDecomp d h2 ⁻¹' Kprod := by
  intro Kfun Hfun Kprod
  ext x
  simp [Kfun, Hfun, Kprod, coordDecomp_fst, coordDecomp_snd_fst, coordDecomp_snd_snd,
    sum_Ioi_eq_last_add_middle h2 x, and_left_comm, and_assoc]
  tauto


lemma integral_zW_eq {n : ℕ} (hn : 1 ≤ n) (F U : ℝ) (hF : 0 ≤ F)
    (hU_lower : -F ≤ U) (hU_upper : U ≤ F) :
    (∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)) =
      - (F ^ 2 - U ^ 2) ^ n / (2 * (n : ℝ)) := by
  let f : ℝ → ℝ := fun x => - (F ^ 2 - x ^ 2) ^ n / (2 * (n : ℝ))
  have hderiv : deriv f = fun z => z * (F ^ 2 - z ^ 2) ^ (n - 1) := by
    funext z
    have hden : (2 * (n : ℝ)) ≠ 0 := by positivity
    simp [f, deriv_div, deriv_neg, deriv_pow, deriv_const, deriv_id'', hden]
    field_simp [hden]
  have hdiff : ∀ x ∈ Set.uIcc (-F) U, DifferentiableAt ℝ f x := by
    intro x hx
    dsimp [f]
    fun_prop
  have hcont : ContinuousOn (fun z : ℝ => z * (F ^ 2 - z ^ 2) ^ (n - 1)) (Set.uIcc (-F) U) := by
    fun_prop
  rw [intervalIntegral.integral_deriv_eq_sub' f hderiv hdiff hcont]
  dsimp [f]
  have hzero : (0 : ℝ) ^ n = 0 := zero_pow (by omega)
  simp [hzero]

lemma intervalIntegral_eq_setIntegral_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ t in a..b, f t) = ∫ t in Set.Icc a b, f t := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc

lemma integral_prod_indicator_eq_setIntegral_of_abs_le
    {A : Set ℝ} {C : ℝ → Set ℝ} {φ : ℝ × ℝ → ℝ} {C1 C2 : ℝ}
    (hA_meas : MeasurableSet A)
    (hC_meas : MeasurableSet {p : ℝ × ℝ | p.2 ∈ C p.1})
    (hφ_meas : Measurable φ)
    (hsec_int : ∀ t, IntegrableOn (fun z => φ (t, z)) (C t) volume)
    (habs_bound : ∀ᵐ t ∂(volume.restrict A),
      (∫ z in C t, |φ (t, z)|) ≤ C1 * |∫ z in C t, φ (t, z)| + C2)
    (hC2_int : IntegrableOn (fun _ : ℝ => C2) A volume) :
    (∫ p : ℝ × ℝ,
        A.indicator (fun t => (C t).indicator (fun z => φ (t, z)) p.2) p.1) =
      ∫ t in A, ∫ z in C t, φ (t, z) := by
  classical
  let S : Set (ℝ × ℝ) := {p | p.2 ∈ C p.1}
  let SA : Set (ℝ × ℝ) := S ∩ {p | p.1 ∈ A}
  let F : ℝ × ℝ → ℝ := fun p =>
    A.indicator (fun t => (C t).indicator (fun z => φ (t, z)) p.2) p.1
  let G : ℝ → ℝ := fun t => ∫ z in C t, φ (t, z)
  let H : ℝ → ℝ := fun t => ∫ z in C t, |φ (t, z)|
  have hS_meas : MeasurableSet S := by
    simpa [S] using hC_meas
  have hA_prod_meas : MeasurableSet {p : ℝ × ℝ | p.1 ∈ A} :=
    hA_meas.preimage measurable_fst
  have hSA_meas : MeasurableSet SA := by
    dsimp [SA]
    exact hS_meas.inter hA_prod_meas
  have hF_eq_ind : F = SA.indicator φ := by
    ext p
    rcases p with ⟨t, z⟩
    dsimp [F, SA, S]
    by_cases ht : t ∈ A
    · rw [Set.indicator_of_mem ht]
      by_cases hz : z ∈ C t
      · rw [Set.indicator_of_mem hz]
        have hp : (t, z) ∈ S ∩ {p | p.1 ∈ A} := ⟨hz, ht⟩
        rw [Set.indicator_of_mem hp]
      · have hp : (t, z) ∉ S ∩ {p | p.1 ∈ A} := by
          intro hp; exact hz hp.1
        rw [Set.indicator_apply, if_neg hz]
        rw [Set.indicator_apply, if_neg hp]
    · have hp : (t, z) ∉ S ∩ {p | p.1 ∈ A} := by
        intro hp; exact ht hp.2
      rw [Set.indicator_apply, if_neg ht]
      rw [Set.indicator_apply, if_neg hp]
  have hF_meas : Measurable F := by
    rw [hF_eq_ind]
    exact Measurable.indicator hφ_meas hSA_meas
  have hF_aestrong : AEStronglyMeasurable F (volume.prod volume) :=
    hF_meas.aestronglyMeasurable
  have hC_section_meas : ∀ t, MeasurableSet (C t) := by
    intro t
    have hsec : MeasurableSet (Prod.mk t ⁻¹' S) :=
      hS_meas.preimage (measurable_prodMk_left (x := t))
    simpa [S] using hsec
  have hF_sections_int : ∀ t, Integrable (fun z => F (t, z)) volume := by
    intro t
    by_cases ht : t ∈ A
    · have hmeas : MeasurableSet (C t) := hC_section_meas t
      have hind : Integrable ((C t).indicator (fun z => φ (t, z))) volume :=
        MeasureTheory.IntegrableOn.integrable_indicator (hsec_int t) hmeas
      refine hind.congr (Filter.Eventually.of_forall ?_)
      intro z
      by_cases hz : z ∈ C t <;> simp [F, ht, hz]
    · refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall ?_)
      intro z
      simp [F, ht]
  have hinner_norm_eq : ∀ t, (∫ z, ‖F (t, z)‖) = A.indicator H t := by
    intro t
    by_cases ht : t ∈ A
    · have hmeas : MeasurableSet (C t) := hC_section_meas t
      have h1 : (∫ z, ‖F (t, z)‖) = ∫ z, (C t).indicator (fun z => |φ (t, z)|) z := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ C t <;> simp [F, ht, hz]
      rw [h1, MeasureTheory.integral_indicator hmeas]
      rw [Set.indicator_of_mem ht]
    · have hzero : (∫ z, ‖F (t, z)‖) = 0 := by
        simp [F, ht]
      simp [F, ht, H, hzero]
  have hinner_aestrong : AEStronglyMeasurable (fun t => ∫ z, ‖F (t, z)‖) volume :=
    hF_aestrong.norm.integral_prod_right'
  have hinner_eq_ae : (fun t => ∫ z, ‖F (t, z)‖) =ᵐ[volume] (A.indicator H) :=
    Filter.Eventually.of_forall hinner_norm_eq
  have hH_aestrong : AEStronglyMeasurable (A.indicator H) volume :=
    hinner_aestrong.congr hinner_eq_ae
  have hF_int_iff : Integrable F (volume.prod volume) ↔ Integrable (A.indicator H) volume := by
    rw [MeasureTheory.integrable_prod_iff hF_aestrong]
    constructor
    · intro h
      exact h.2.congr hinner_eq_ae
    · intro hH
      refine ⟨Filter.Eventually.of_forall hF_sections_int, ?_⟩
      exact hH.congr hinner_eq_ae.symm
  have h_ae_bound : ∀ᵐ t ∂volume, t ∈ A → H t ≤ C1 * |G t| + C2 :=
    (MeasureTheory.ae_restrict_iff' hA_meas).mp habs_bound
  have hH_bound : ∀ᵐ t ∂volume,
      ‖A.indicator H t‖ ≤ C1 * |A.indicator G t| + A.indicator (fun _ => C2) t := by
    filter_upwards [h_ae_bound] with t ht
    by_cases htA : t ∈ A
    · have h := ht htA
      have hnonneg : 0 ≤ A.indicator H t := by
        simp [htA, H]
        exact setIntegral_nonneg (hC_section_meas t) (fun z hz => abs_nonneg (φ (t, z)))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa [htA] using h
    · have hzero : A.indicator H t = 0 := by simp [htA]
      simp [htA, hzero]
  change (∫ p : ℝ × ℝ, F p) = ∫ t in A, G t
  rw [← MeasureTheory.integral_indicator hA_meas]
  by_cases hFint : Integrable F (volume.prod volume)
  · have hH_int : Integrable (A.indicator H) volume := hF_int_iff.mp hFint
    calc
      ∫ p : ℝ × ℝ, F p = ∫ t : ℝ, ∫ z : ℝ, F (t, z) :=
        MeasureTheory.integral_prod F hFint
      _ = ∫ t : ℝ, A.indicator G t := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ A
        · have hmeas : MeasurableSet (C t) := hC_section_meas t
          have hfun : (fun z : ℝ => F (t, z)) = (C t).indicator (fun z => φ (t, z)) := by
            ext z
            by_cases hz : z ∈ C t <;> simp [F, ht, hz]
          have hinner : (∫ z : ℝ, F (t, z)) = G t := by
            rw [hfun, MeasureTheory.integral_indicator hmeas]
          simp [ht, hinner]
        · have hzero : (∫ z : ℝ, F (t, z)) = 0 := by
            simp [F, ht]
          simp [ht, hzero]
  · have hH_not_int : ¬ Integrable (A.indicator H) volume := by
      intro hH; exact hFint (hF_int_iff.mpr hH)
    have hGnot : ¬ Integrable (A.indicator G) volume := by
      intro hGint
      have hG_abs_int : Integrable (fun t : ℝ => |A.indicator G t|) volume := hGint.abs
      have hC2_ind_int : Integrable (A.indicator (fun _ : ℝ => C2)) volume :=
        MeasureTheory.IntegrableOn.integrable_indicator hC2_int hA_meas
      have hRHS_int : Integrable (fun t : ℝ => C1 * |A.indicator G t| + A.indicator (fun _ : ℝ => C2) t) volume :=
        (hG_abs_int.const_mul C1).add hC2_ind_int
      have hH_int : Integrable (A.indicator H) volume :=
        Integrable.mono' hRHS_int hH_aestrong hH_bound
      exact hH_not_int hH_int
    have hF_zero : (∫ p : ℝ × ℝ, F p) = 0 := MeasureTheory.integral_undef hFint
    have hG_zero : (∫ x : ℝ, A.indicator G x) = 0 := MeasureTheory.integral_undef hGnot
    rw [hF_zero, hG_zero]

lemma volume_Kprod_eq {d n : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let m : ℕ := d - 2
    let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h))
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    let Kprod : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1^2}
    volume.real Kprod = c * ∫ t in a..b, ∫ z in (-f t)..(U t), W t z := by
  classical
  intro m U W c Kprod
  haveI : Nonempty (Fin m) := by
    have hdpos : 0 < d := Nat.pos_of_neZero d
    have hmpos : 0 < m := by dsimp [m]; omega
    exact Fin.pos_iff_nonempty.mp hmpos
  have hm : m = 2 * (n - 1) := by dsimp [m]; omega
  let A : Set ℝ := Set.Icc a b
  let C : ℝ → Set ℝ := fun t => Set.Icc (-f t) (U t)
  let B : ℝ → ℝ → Set (Fin m → ℝ) := fun t z =>
    {y | t ∈ Set.Icc a b ∧ z ≤ s * t + h ∧ z ^ 2 + ∑ j : Fin m, (y j)^2 ≤ f t ^ 2}
  set_option maxHeartbeats 1000000 in
  have hB_meas : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.2.2 ∈ B p.1 p.2.1} := by
    dsimp [B]
    measurability
  have hB_finite : ∀ t z, (volume : Measure (Fin m → ℝ)) (B t z) ≠ ⊤ := by
    intro t z
    exact ne_of_lt (volume_cap_section_lt_top (m := m) (n := n) t z)
  have hφ_meas : Measurable (fun _ : ℝ × ℝ => (1 : ℝ)) := measurable_const
  have hsec := integral_prod_section_volume (α := ℝ) (β := ℝ) (γ := Fin m → ℝ)
    (μa := volume) (μb := volume) (μc := (volume : Measure (Fin m → ℝ))) (B := B)
    (φ := fun _ => (1 : ℝ)) hφ_meas hB_meas hB_finite
  set_option maxHeartbeats 1000000 in
  have hK_meas : MeasurableSet Kprod := by
    dsimp [Kprod]
    measurability
  have hvol_set : volume.real Kprod = ∫ p in Kprod, (1 : ℝ) := by
    rw [MeasureTheory.setIntegral_const]
    simp
  have hvol_as_int : volume.real Kprod = ∫ p : ℝ × (ℝ × (Fin m → ℝ)),
      (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2 := by
    rw [hvol_set]
    rw [← MeasureTheory.integral_indicator hK_meas]
    apply integral_congr_ae
    filter_upwards with p
    rcases p with ⟨t, z, y⟩
    rfl
  have h_one : (∫ p : ℝ × (ℝ × (Fin m → ℝ)),
      (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2) =
      ∫ p : ℝ × (ℝ × (Fin m → ℝ)), (1 : ℝ) * (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2 := by
    apply integral_congr_ae
    filter_upwards with p
    rw [one_mul]
  have hvolB : ∀ t z, volume.real (B t z) =
      A.indicator (fun _ => (C t).indicator (fun _ => c * W t z) z) t := by
    intro t z
    have hcap := volume_real_cap_section (m := m) (n := n) (a := a) (b := b) (s := s) (h := h)
      (f := f) hm hn hab hf_nonneg t z
    simpa [A, C, U, W, c, B] using hcap
  have hprod : (∫ p : ℝ × ℝ, (1 : ℝ) * volume.real (B p.1 p.2)) =
      ∫ p : ℝ × ℝ, A.indicator (fun t => (C t).indicator (fun z => c * W t z) p.2) p.1 := by
    apply integral_congr_ae
    filter_upwards with p
    rw [one_mul, hvolB p.1 p.2]
    rfl
  have hW_meas : Measurable (fun p : ℝ × ℝ => c * W p.1 p.2) := by
    have hfst : Measurable (fun p : ℝ × ℝ => f p.1) := hf_meas.comp measurable_fst
    have hsnd : Measurable (fun p : ℝ × ℝ => p.2) := measurable_snd
    have hpow_meas : Measurable (fun p : ℝ × ℝ => (f p.1 ^ 2 - p.2 ^ 2) ^ (n - 1)) := by
      exact ((hfst.pow measurable_const).sub (hsnd.pow measurable_const)).pow measurable_const
    dsimp [W]
    exact hpow_meas.const_mul c
  have hsec_int : ∀ t : ℝ, IntegrableOn (fun z => c * W t z) (C t) volume := by
    intro t
    have hcont : ContinuousOn (fun z : ℝ => c * W t z) (C t) := by
      dsimp [W]
      fun_prop
    exact ContinuousOn.integrableOn_compact isCompact_Icc hcont
  have hA_meas : MeasurableSet A := by dsimp [A]; exact measurableSet_Icc
  have hnonneg : ∀ t, t ∈ A → ∀ z, z ∈ C t → 0 ≤ c * W t z := by
    intro t htA z hz
    have hf_nonneg_t : 0 ≤ f t := by
      simpa [A] using hf_nonneg t htA
    have hz1 : -f t ≤ z := hz.1
    have hzU : z ≤ U t := hz.2
    have hUf : U t ≤ f t := by
      dsimp [U]
      exact max_le (by linarith) (min_le_left _ _)
    have hzf : z ≤ f t := le_trans hzU hUf
    have hsq : z ^ 2 ≤ f t ^ 2 := sq_le_sq' hz1 hzf
    have hnonnegW : 0 ≤ W t z := by
      dsimp [W]
      exact pow_nonneg (by nlinarith) _
    exact mul_nonneg (MeasureTheory.measureReal_nonneg) hnonnegW
  have habs_bound : ∀ᵐ t ∂(volume.restrict A),
      (∫ z in C t, |c * W t z|) ≤ 1 * |∫ z in C t, c * W t z| + 0 := by
    rw [MeasureTheory.ae_restrict_iff' hA_meas]
    filter_upwards with t htA
    have h_nonneg_fun : ∀ z, z ∈ C t → 0 ≤ c * W t z := fun z hz => hnonneg t htA z hz
    rw [one_mul, add_zero]
    have hmeasC : MeasurableSet (C t) := measurableSet_Icc
    have h1 : (∫ z in C t, |c * W t z|) = ∫ z in C t, c * W t z := by
      apply MeasureTheory.setIntegral_congr_fun hmeasC
      intro z hz
      simpa using abs_of_nonneg (h_nonneg_fun z hz)
    rw [h1]
    exact le_abs_self _
  have hC2_int : IntegrableOn (fun _ : ℝ => (0 : ℝ)) A volume := by
    exact MeasureTheory.integrableOn_const (μ := volume) (s := A) (C := 0)
      (by dsimp [A]; exact ne_of_lt (measure_Icc_lt_top (μ := volume))) (by simp)
  have hC_meas : MeasurableSet {p : ℝ × ℝ | p.2 ∈ C p.1} := by
    dsimp [C, Set.Icc]
    have hle1 : MeasurableSet {p : ℝ × ℝ | -f p.1 ≤ p.2} := by
      exact measurableSet_le (by fun_prop) measurable_snd
    have hle2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ U p.1} := by
      exact measurableSet_le measurable_snd (by fun_prop)
    exact hle1.inter hle2
  have htwo := integral_prod_indicator_eq_setIntegral_of_abs_le
    (A := A) (C := C) (φ := fun p : ℝ × ℝ => c * W p.1 p.2) (C1 := 1) (C2 := 0)
    measurableSet_Icc hC_meas hW_meas hsec_int habs_bound hC2_int
  have hset_t : (∫ t in A, ∫ z in C t, c * W t z) =
      c * ∫ t in Set.Icc a b, ∫ z in Set.Icc (-f t) (U t), W t z := by
    dsimp [A, C]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp [MeasureTheory.integral_const_mul]
  calc
    volume.real Kprod
        = ∫ p : ℝ × (ℝ × (Fin m → ℝ)), (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2 := hvol_as_int
    _ = ∫ p : ℝ × (ℝ × (Fin m → ℝ)), (1 : ℝ) * (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2 := h_one
    _ = ∫ p : ℝ × ℝ, (1 : ℝ) * volume.real (B p.1 p.2) := hsec
    _ = ∫ p : ℝ × ℝ, A.indicator (fun t => (C t).indicator (fun z => c * W t z) p.2) p.1 := hprod
    _ = ∫ t in A, ∫ z in C t, c * W t z := htwo
    _ = c * ∫ t in Set.Icc a b, ∫ z in Set.Icc (-f t) (U t), W t z := hset_t
    _ = c * ∫ t in a..b, ∫ z in (-f t)..(U t), W t z := by
      congr 1
      rw [intervalIntegral_eq_setIntegral_Icc hab]
      apply integral_congr_ae
      filter_upwards with t
      rw [intervalIntegral_eq_setIntegral_Icc (show -f t ≤ U t by dsimp [U]; exact le_max_left _ _)]

lemma intervalIntegral_abs_zW_le_two_pow {n : ℕ} (hn : 1 ≤ n) (F U : ℝ)
    (hF : 0 ≤ F) (hU_lower : -F ≤ U) (hU_upper : U ≤ F) :
    (∫ z in (-F)..U, |z| * (F ^ 2 - z ^ 2) ^ (n - 1)) ≤ 2 * F ^ (2 * n) := by
  let W : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1)
  have huIcc : Set.uIcc (-F) U = Set.Icc (-F) U := by
    rw [Set.uIcc_of_le hU_lower]
  have hcont_f : ContinuousOn (fun z => |z| * W z) (Set.uIcc (-F) U) := by
    rw [huIcc]
    dsimp [W]
    fun_prop
  have hcont_g : ContinuousOn (fun _ : ℝ => F * F ^ (2 * n - 2)) (Set.uIcc (-F) U) := by
    rw [huIcc]
    fun_prop
  have h_int_f : IntervalIntegrable (fun z => |z| * W z) volume (-F) U := by
    exact hcont_f.intervalIntegrable
  have h_int_g : IntervalIntegrable (fun _ : ℝ => F * F ^ (2 * n - 2)) volume (-F) U := by
    exact hcont_g.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on (a := -F) (b := U) (μ := volume)
    hU_lower h_int_f h_int_g ?_
  · calc
      ∫ z in (-F)..U, |z| * W z ≤ ∫ z in (-F)..U, F * F ^ (2 * n - 2) := hmono
      _ = (U - (-F)) * (F * F ^ (2 * n - 2)) := by
        rw [intervalIntegral.integral_const]
        simp
      _ ≤ (2 * F) * (F * F ^ (2 * n - 2)) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = 2 * F ^ (2 * n) := by
        have hpow1 : F * F ^ (2 * n - 2) = F ^ (2 * n - 1) := by
          rw [← pow_succ' F (2 * n - 2)]
          congr 1
          omega
        have hpow2 : F * F ^ (2 * n - 1) = F ^ (2 * n) := by
          rw [← pow_succ' F (2 * n - 1)]
          congr 1
          omega
        calc
          (2 * F) * (F * F ^ (2 * n - 2)) = 2 * (F * (F * F ^ (2 * n - 2))) := by ring
          _ = 2 * (F * F ^ (2 * n - 1)) := by rw [hpow1]
          _ = 2 * F ^ (2 * n) := by rw [hpow2]
  · intro z hz
    have hz1 : -F ≤ z := hz.1
    have hz2 : z ≤ U := hz.2
    have hz_le_F : z ≤ F := le_trans hz2 hU_upper
    have hz_abs_le : |z| ≤ F := by
      rw [abs_le]
      exact ⟨hz1, hz_le_F⟩
    have hz_sq_le : z ^ 2 ≤ F ^ 2 := sq_le_sq' hz1 hz_le_F
    have hbase_nonneg : 0 ≤ F ^ 2 - z ^ 2 := by nlinarith
    have hbase_le : F ^ 2 - z ^ 2 ≤ F ^ 2 := by nlinarith [sq_nonneg z]
    have hW_le : W z ≤ F ^ (2 * n - 2) := by
      dsimp [W]
      have hpow := pow_le_pow_left₀ hbase_nonneg hbase_le (n - 1)
      have hFpow : (F ^ 2) ^ (n - 1) = F ^ (2 * n - 2) := by
        rw [← pow_mul]
        congr 1
        omega
      simpa [hFpow] using hpow
    have hW_nonneg : 0 ≤ W z := by
      dsimp [W]
      exact pow_nonneg hbase_nonneg _
    exact mul_le_mul hz_abs_le hW_le hW_nonneg hF


lemma F_pow_two_mul_le_const_abs_zW_of_U_nonneg {n : ℕ} (hn : 1 ≤ n) {F L M : ℝ}
    (hF : 0 ≤ F) (hL_abs : |L| ≤ M)
    (hU_nonneg : 0 ≤ max (-F) (min F L)) :
    let U : ℝ := max (-F) (min F L)
    F ^ (2 * n) ≤ (4 / 3 : ℝ) ^ n * (2 * (n : ℝ)) *
        |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| + (2 * M) ^ (2 * n) := by
  intro U
  have hU_upper : U ≤ F := by
    dsimp [U]
    exact max_le (by linarith) (min_le_left _ _)
  have hU_lower : -F ≤ U := by
    dsimp [U]
    exact le_max_left _ _
  have hG := integral_zW_eq hn F U hF hU_lower hU_upper
  have hnonnegR : 0 ≤ F ^ 2 - U ^ 2 := by
    have hU_sq_le : U ^ 2 ≤ F ^ 2 := sq_le_sq' hU_lower hU_upper
    nlinarith
  have hden_pos : 0 < 2 * (n : ℝ) := by positivity
  have hdiv_nonneg : 0 ≤ (F ^ 2 - U ^ 2) ^ n / (2 * (n : ℝ)) :=
    div_nonneg (pow_nonneg hnonnegR _) (le_of_lt hden_pos)
  have hGabs : |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| = (F ^ 2 - U ^ 2) ^ n / (2 * (n : ℝ)) := by
    rw [hG, abs_div, abs_neg, abs_of_nonneg (pow_nonneg hnonnegR _), abs_of_nonneg (le_of_lt hden_pos)]
  by_cases hFle : F ≤ 2 * M
  · calc
      F ^ (2 * n) ≤ (2 * M) ^ (2 * n) := by
        exact pow_le_pow_left₀ hF hFle _
      _ ≤ (4 / 3 : ℝ) ^ n * (2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| + (2 * M) ^ (2 * n) := by
        have hnonneg : 0 ≤ (4 / 3 : ℝ) ^ n * (2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| := by positivity
        linarith
  · have hFgt : 2 * M < F := lt_of_not_ge hFle
    have hM_nonneg : 0 ≤ M := by
      have h0 : 0 ≤ |L| := abs_nonneg L
      nlinarith
    have hLnonneg : 0 ≤ L := by
      by_contra hLneg
      have hL_lt : L < 0 := lt_of_not_ge hLneg
      have hmin_neg : min F L < 0 := lt_of_le_of_lt (min_le_right _ _) hL_lt
      have hU_neg : U < 0 := by
        dsimp [U]
        exact max_lt (by linarith) hmin_neg
      have hU_nonneg' : 0 ≤ U := by simpa [U] using hU_nonneg
      linarith
    have hL_le_F : L ≤ F := by
      have hL_le_abs : L ≤ |L| := le_abs_self L
      have h2M_lt_F : 2 * M < F := hFgt
      nlinarith
    have hU_eq_L : U = L := by
      dsimp [U]
      have hmin : min F L = L := min_eq_right hL_le_F
      have hmax : max (-F) L = L := max_eq_right (by nlinarith [hL_le_F, hFgt, hL_abs, le_abs_self L, neg_le_abs L])
      rw [hmin, hmax]
    have h_abs_half : |L| ≤ F / 2 := by
      have hL_abs_le_M : |L| ≤ M := hL_abs
      nlinarith
    have hL_sq_le : L ^ 2 ≤ (F / 2) ^ 2 := by
      rw [abs_le] at h_abs_half
      exact sq_le_sq' h_abs_half.1 h_abs_half.2
    have hR_lower : 3 / 4 * F ^ 2 ≤ F ^ 2 - U ^ 2 := by
      rw [hU_eq_L]
      nlinarith [hL_sq_le, sq_nonneg F]
    have hpow_R : (3 / 4 * F ^ 2) ^ n ≤ (F ^ 2 - U ^ 2) ^ n := by
      exact pow_le_pow_left₀ (by nlinarith [sq_nonneg F]) hR_lower n
    have hpow_R' : (3 / 4) ^ n * (F ^ 2) ^ n ≤ (F ^ 2 - U ^ 2) ^ n := by
      simpa [mul_pow] using hpow_R
    have hFpow_eq : (F ^ 2) ^ n = F ^ (2 * n) := by
      rw [pow_mul]
    have h_main_pow : F ^ (2 * n) ≤ (4 / 3 : ℝ) ^ n * (F ^ 2 - U ^ 2) ^ n := by
      have hpos : 0 < (3 / 4 : ℝ) ^ n := pow_pos (by norm_num) _
      rw [hFpow_eq] at hpow_R'
      have hpos4 : 0 ≤ (4 / 3 : ℝ) ^ n := pow_nonneg (by norm_num) _
      have hmul := mul_le_mul_of_nonneg_left hpow_R' hpos4
      have hcoeff : (4 / 3 : ℝ) ^ n * (3 / 4 : ℝ) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      have h_left : (4 / 3 : ℝ) ^ n * ((3 / 4 : ℝ) ^ n * F ^ (2 * n)) = F ^ (2 * n) := by
        rw [← mul_assoc, hcoeff, one_mul]
      simpa [h_left] using hmul
    have hR_eq_G : (F ^ 2 - U ^ 2) ^ n = (2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| := by
      rw [hGabs]
      field_simp [ne_of_gt hden_pos]
    calc
      F ^ (2 * n) ≤ (4 / 3 : ℝ) ^ n * (F ^ 2 - U ^ 2) ^ n := h_main_pow
      _ = (4 / 3 : ℝ) ^ n * ((2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)|) := by rw [hR_eq_G]
      _ = (4 / 3 : ℝ) ^ n * (2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| := by ring
      _ ≤ (4 / 3 : ℝ) ^ n * (2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| + (2 * M) ^ (2 * n) := by
        have hnonneg : 0 ≤ (2 * M) ^ (2 * n) := pow_nonneg (by nlinarith) _
        linarith

lemma intervalIntegral_abs_zW_eq_abs_zW_of_U_nonpos {n : ℕ} (hn : 1 ≤ n) {F U : ℝ}
    (hF : 0 ≤ F) (hU_lower : -F ≤ U) (hU_upper : U ≤ F) (hU_nonpos : U ≤ 0) :
    (∫ z in (-F)..U, |z| * (F ^ 2 - z ^ 2) ^ (n - 1)) =
      |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| := by
  have hW : ∀ z ∈ Set.uIcc (-F) U, |z| * (F ^ 2 - z ^ 2) ^ (n - 1) = - (z * (F ^ 2 - z ^ 2) ^ (n - 1)) := by
    intro z hz
    have hz_le : z ≤ 0 := by
      have hzU : z ≤ U := by simpa [max_eq_right hU_lower] using hz.2
      linarith
    rw [abs_of_nonpos hz_le]
    ring
  rw [intervalIntegral.integral_congr hW, intervalIntegral.integral_neg]
  have hG := integral_zW_eq hn F U hF hU_lower hU_upper
  rw [hG]
  have hnonnegR : 0 ≤ F ^ 2 - U ^ 2 := by
    have hU_sq_le : U ^ 2 ≤ F ^ 2 := sq_le_sq' hU_lower hU_upper
    nlinarith
  have hden_pos : 0 < 2 * (n : ℝ) := by positivity
  rw [abs_div, abs_neg, abs_of_nonneg (pow_nonneg hnonnegR _), abs_of_nonneg (le_of_lt hden_pos)]
  ring

lemma intervalIntegral_abs_zW_le_const {n : ℕ} (hn : 1 ≤ n) {F L M : ℝ}
    (hF : 0 ≤ F) (hL_abs : |L| ≤ M) :
    let U : ℝ := max (-F) (min F L)
    (∫ z in (-F)..U, |z| * (F ^ 2 - z ^ 2) ^ (n - 1)) ≤
      (4 * (n : ℝ) * (4 / 3 : ℝ) ^ n) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| +
        2 * ((2 * M) ^ (2 * n)) := by
  intro U
  have hU_upper : U ≤ F := by
    dsimp [U]
    exact max_le (by linarith) (min_le_left _ _)
  have hU_lower : -F ≤ U := by
    dsimp [U]
    exact le_max_left _ _
  by_cases hU_nonpos : U ≤ 0
  · rw [intervalIntegral_abs_zW_eq_abs_zW_of_U_nonpos hn hF hU_lower hU_upper hU_nonpos]
    have hC1_ge : 1 ≤ 4 * (n : ℝ) * (4 / 3 : ℝ) ^ n := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    have hle : |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| ≤
        (4 * (n : ℝ) * (4 / 3 : ℝ) ^ n) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| := by
      have := mul_le_mul_of_nonneg_left (a := |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)|) hC1_ge (abs_nonneg _)
      simpa [one_mul, mul_comm] using this
    have hC2_nonneg : 0 ≤ 2 * ((2 * M) ^ (2 * n)) := by
      have hpow_nonneg : 0 ≤ (2 * M) ^ (2 * n) := by
        simpa [pow_mul] using pow_nonneg (sq_nonneg (2 * M)) n
      linarith
    linarith
  · have hU_nonneg : 0 ≤ U := le_of_not_ge hU_nonpos
    have hstep1 := intervalIntegral_abs_zW_le_two_pow hn F U hF hU_lower hU_upper
    have hstep2 := F_pow_two_mul_le_const_abs_zW_of_U_nonneg hn hF hL_abs hU_nonneg
    have hmul := mul_le_mul_of_nonneg_left hstep2 (by norm_num : 0 ≤ (2:ℝ))
    -- hmul: 2*F^(2n) ≤ 2*((4/3)^n*2n*|G| + (2M)^(2n))
    calc
      ∫ z in (-F)..U, |z| * (F ^ 2 - z ^ 2) ^ (n - 1) ≤ 2 * F ^ (2 * n) := hstep1
      _ ≤ 2 * ((4 / 3 : ℝ) ^ n * (2 * (n : ℝ)) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| + (2 * M) ^ (2 * n)) := hmul
      _ = (4 * (n : ℝ) * (4 / 3 : ℝ) ^ n) * |∫ z in (-F)..U, z * (F ^ 2 - z ^ 2) ^ (n - 1)| + 2 * ((2 * M) ^ (2 * n)) := by ring

lemma abs_affine_le_const {a b s h t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) :
    |s * t + h| ≤ |s| * max |a| |b| + |h| := by
  have ht_abs : |t| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · have ha_abs : -a ≤ |a| := neg_le_abs a
      have ha_max : |a| ≤ max |a| |b| := le_max_left _ _
      have hnegmax_le_a : -max |a| |b| ≤ a := by nlinarith
      nlinarith [ht.1, hnegmax_le_a]
    · have hb_abs : b ≤ |b| := le_abs_self b
      have hb_max : |b| ≤ max |a| |b| := le_max_right _ _
      nlinarith [ht.2, hb_abs, hb_max]
  calc
    |s * t + h| ≤ |s * t| + |h| := abs_add_le _ _
    _ = |s| * |t| + |h| := by rw [abs_mul]
    _ ≤ |s| * max |a| |b| + |h| := by
      nlinarith [mul_le_mul_of_nonneg_left ht_abs (abs_nonneg s)]

lemma Kprod_mul_phi_eq {d n : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    {φ : ℝ × ℝ → ℝ} {C1 C2 : ℝ}
    (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f)
    (hφ_meas : Measurable φ)
    (hsec_int : ∀ t : ℝ, IntegrableOn (fun z => φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)) (Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h)))) volume)
    (habs_bound : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      (∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))), |φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)|) ≤
        C1 * |∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))), φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)| + C2)
    (hC2_int : IntegrableOn (fun _ : ℝ => C2) (Set.Icc a b) volume) :
    let m : ℕ := d - 2
    let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h))
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    let Kprod : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1^2}
    (∫ p in Kprod, φ (p.1, p.2.1)) = c * ∫ t in a..b, ∫ z in (-f t)..(U t), φ (t, z) * W t z := by
  classical
  intro m U W c Kprod
  haveI : Nonempty (Fin m) := by
    have hdpos : 0 < d := Nat.pos_of_neZero d
    have hmpos : 0 < m := by dsimp [m]; omega
    exact Fin.pos_iff_nonempty.mp hmpos
  have hm : m = 2 * (n - 1) := by dsimp [m]; omega
  let A : Set ℝ := Set.Icc a b
  let C : ℝ → Set ℝ := fun t => Set.Icc (-f t) (U t)
  let B : ℝ → ℝ → Set (Fin m → ℝ) := fun t z =>
    {y | t ∈ Set.Icc a b ∧ z ≤ s * t + h ∧ z ^ 2 + ∑ j : Fin m, (y j)^2 ≤ f t ^ 2}
  set_option maxHeartbeats 1000000 in
  have hB_meas : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.2.2 ∈ B p.1 p.2.1} := by
    dsimp [B]
    measurability
  have hB_finite : ∀ t z, (volume : Measure (Fin m → ℝ)) (B t z) ≠ ⊤ := by
    intro t z
    exact ne_of_lt (volume_cap_section_lt_top (m := m) (n := n) t z)
  have hsec := integral_prod_section_volume (α := ℝ) (β := ℝ) (γ := Fin m → ℝ)
    (μa := volume) (μb := volume) (μc := (volume : Measure (Fin m → ℝ))) (B := B)
    (φ := φ) hφ_meas hB_meas hB_finite
  set_option maxHeartbeats 1000000 in
  have hK_meas : MeasurableSet Kprod := by
    dsimp [Kprod]
    measurability
  have hphi_set : (∫ p in Kprod, φ (p.1, p.2.1)) = ∫ p : ℝ × (ℝ × (Fin m → ℝ)),
      φ (p.1, p.2.1) * (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2 := by
    rw [← MeasureTheory.integral_indicator hK_meas]
    apply integral_congr_ae
    filter_upwards with p
    rcases p with ⟨t, z, y⟩
    by_cases hy : y ∈ B t z
    · have hKmem : (t, z, y) ∈ Kprod := by
        rcases hy with ⟨ht, hz, hsum⟩
        dsimp [Kprod]
        exact ⟨ht, hz, hsum⟩
      rw [Set.indicator_of_mem hKmem, Set.indicator_of_mem hy]
      simp
    · have hKnot : (t, z, y) ∉ Kprod := by
        intro hK
        rcases hK with ⟨ht, hz, hsum⟩
        exact hy ⟨ht, hz, hsum⟩
      rw [Set.indicator_apply, if_neg hKnot]
      rw [Set.indicator_apply, if_neg hy]
      simp
  have hvolB : ∀ t z, volume.real (B t z) =
      A.indicator (fun _ => (C t).indicator (fun _ => c * W t z) z) t := by
    intro t z
    have hcap := volume_real_cap_section (m := m) (n := n) (a := a) (b := b) (s := s) (h := h)
      (f := f) hm hn hab hf_nonneg t z
    simpa [A, C, U, W, c, B] using hcap
  have hprod : (∫ p : ℝ × ℝ, φ p * volume.real (B p.1 p.2)) =
      ∫ p : ℝ × ℝ, A.indicator (fun t => (C t).indicator (fun z => φ (t, z) * (c * W t z)) p.2) p.1 := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hvolB p.1 p.2]
    by_cases hp1 : p.1 ∈ A <;> by_cases hp2 : p.2 ∈ C p.1 <;> simp [hp1, hp2, mul_assoc]
  have hφcW_meas : Measurable (fun p : ℝ × ℝ => φ p * (c * W p.1 p.2)) := by
    have hfst : Measurable (fun p : ℝ × ℝ => f p.1) := hf_meas.comp measurable_fst
    have hsnd : Measurable (fun p : ℝ × ℝ => p.2) := measurable_snd
    have hpow_meas : Measurable (fun p : ℝ × ℝ => (f p.1 ^ 2 - p.2 ^ 2) ^ (n - 1)) := by
      exact ((hfst.pow measurable_const).sub (hsnd.pow measurable_const)).pow measurable_const
    dsimp [W]
    exact hφ_meas.mul (hpow_meas.const_mul c)
  have hsec_int_cW : ∀ t : ℝ, IntegrableOn (fun z => φ (t, z) * (c * W t z)) (C t) volume := by
    intro t
    have h := hsec_int t
    dsimp [C, W]
    refine h.const_mul c |>.congr ?_
    apply Filter.Eventually.of_forall
    intro z
    ring
  have hA_meas : MeasurableSet A := by dsimp [A]; exact measurableSet_Icc
  have habs_bound_cW : ∀ᵐ t ∂(volume.restrict A),
      (∫ z in C t, |φ (t, z) * (c * W t z)|) ≤ C1 * |∫ z in C t, φ (t, z) * (c * W t z)| + c * C2 := by
    dsimp [A]
    filter_upwards [habs_bound] with t ht
    dsimp [C, U, W]
    have hc_nonneg : 0 ≤ c := MeasureTheory.measureReal_nonneg
    have h_abs_int : (∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
          |φ (t, z) * (c * (f t ^ 2 - z ^ 2) ^ (n - 1))|) =
        c * ∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
          |φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)| := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change |φ (t, z) * (c * (f t ^ 2 - z ^ 2) ^ (n - 1))| =
        c * |φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)|
      rw [abs_mul, abs_mul, abs_of_nonneg hc_nonneg, abs_mul]
      ring
    have h_int : (∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
          φ (t, z) * (c * (f t ^ 2 - z ^ 2) ^ (n - 1))) =
        c * ∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
          φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change φ (t, z) * (c * (f t ^ 2 - z ^ 2) ^ (n - 1)) =
        c * (φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1))
      ring
    rw [h_abs_int, h_int]
    calc
      c * ∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
          |φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)| ≤
            c * (C1 * |∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
              φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)| + C2) := by
        exact mul_le_mul_of_nonneg_left ht hc_nonneg
      _ = C1 * |c * ∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
            φ (t, z) * (f t ^ 2 - z ^ 2) ^ (n - 1)| + c * C2 := by
        rw [abs_mul, abs_of_nonneg hc_nonneg]
        ring
  have hC2_int_c : IntegrableOn (fun _ : ℝ => c * C2) A volume := by
    exact hC2_int.const_mul c
  have hC_meas : MeasurableSet {p : ℝ × ℝ | p.2 ∈ C p.1} := by
    dsimp [C, Set.Icc]
    have hle1 : MeasurableSet {p : ℝ × ℝ | -f p.1 ≤ p.2} := by
      exact measurableSet_le (by fun_prop) measurable_snd
    have hle2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ U p.1} := by
      exact measurableSet_le measurable_snd (by fun_prop)
    exact hle1.inter hle2
  have htwo := integral_prod_indicator_eq_setIntegral_of_abs_le
    (A := A) (C := C) (φ := fun p : ℝ × ℝ => φ p * (c * W p.1 p.2)) (C1 := C1) (C2 := c * C2)
    measurableSet_Icc hC_meas hφcW_meas hsec_int_cW habs_bound_cW hC2_int_c
  have hset_t : (∫ t in A, ∫ z in C t, φ (t, z) * (c * W t z)) =
      c * ∫ t in Set.Icc a b, ∫ z in Set.Icc (-f t) (U t), φ (t, z) * W t z := by
    dsimp [A, C]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change (∫ z : ℝ in Set.Icc (-f t) (U t), φ (t, z) * (c * W t z)) =
      c * ∫ z : ℝ in Set.Icc (-f t) (U t), φ (t, z) * W t z
    have hfun : (fun z => φ (t, z) * (c * W t z)) = (fun z => (φ (t, z) * W t z) * c) := by
      funext z; ring
    rw [hfun]
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    have h_ind : (fun x : ℝ => (Set.Icc (-f t) (U t)).indicator (fun z => (φ (t, z) * W t z) * c) x) =
        (fun x : ℝ => (Set.Icc (-f t) (U t)).indicator (fun z => φ (t, z) * W t z) x * c) := by
      funext x
      rw [Set.indicator_mul_const]
    rw [h_ind]
    rw [MeasureTheory.integral_mul_const]
    rw [MeasureTheory.integral_indicator measurableSet_Icc]
    ring
  calc
    (∫ p in Kprod, φ (p.1, p.2.1))
        = ∫ p : ℝ × (ℝ × (Fin m → ℝ)), φ (p.1, p.2.1) * (B p.1 p.2.1).indicator (fun _ : Fin m → ℝ => (1 : ℝ)) p.2.2 := hphi_set
    _ = ∫ p : ℝ × ℝ, φ p * volume.real (B p.1 p.2) := hsec
    _ = ∫ p : ℝ × ℝ, A.indicator (fun t => (C t).indicator (fun z => φ (t, z) * (c * W t z)) p.2) p.1 := hprod
    _ = ∫ t in A, ∫ z in C t, φ (t, z) * (c * W t z) := htwo
    _ = c * ∫ t in Set.Icc a b, ∫ z in Set.Icc (-f t) (U t), φ (t, z) * W t z := hset_t
    _ = c * ∫ t in a..b, ∫ z in (-f t)..(U t), φ (t, z) * W t z := by
      congr 1
      rw [intervalIntegral_eq_setIntegral_Icc hab]
      apply integral_congr_ae
      filter_upwards with t
      rw [intervalIntegral_eq_setIntegral_Icc (show -f t ≤ U t by dsimp [U]; exact le_max_left _ _)]

lemma x0_Kprod_eq {d n : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let m : ℕ := d - 2
    let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h))
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    let Kprod : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1^2}
    (∫ p in Kprod, p.1) = c * ∫ t in a..b, ∫ z in (-f t)..(U t), t * W t z := by
  classical
  intro m U W c Kprod
  haveI : Nonempty (Fin m) := by
    have hdpos : 0 < d := Nat.pos_of_neZero d
    have hmpos : 0 < m := by dsimp [m]; omega
    exact Fin.pos_iff_nonempty.mp hmpos
  have hφ_meas : Measurable (fun p : ℝ × ℝ => p.1) := measurable_fst
  have hsec_int : ∀ t : ℝ, IntegrableOn (fun z => t * W t z) (Set.Icc (-f t) (U t)) volume := by
    intro t
    have hcont : ContinuousOn (fun z : ℝ => t * W t z) (Set.Icc (-f t) (U t)) := by
      dsimp [W]
      fun_prop
    exact ContinuousOn.integrableOn_compact isCompact_Icc hcont
  have hW_nonneg : ∀ t, t ∈ Set.Icc a b → ∀ z, z ∈ Set.Icc (-f t) (U t) → 0 ≤ W t z := by
    intro t ht z hz
    have hf_nonneg_t : 0 ≤ f t := hf_nonneg t ht
    have hz1 : -f t ≤ z := hz.1
    have hzU : z ≤ U t := hz.2
    have hUf : U t ≤ f t := by
      dsimp [U]
      exact max_le (by linarith) (min_le_left _ _)
    have hzf : z ≤ f t := le_trans hzU hUf
    have hsq : z ^ 2 ≤ f t ^ 2 := sq_le_sq' hz1 hzf
    dsimp [W]
    exact pow_nonneg (by nlinarith) _
  have habs_bound : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      (∫ z in Set.Icc (-f t) (U t), |t * W t z|) ≤
        1 * |∫ z in Set.Icc (-f t) (U t), t * W t z| + 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t htA
    have hWn : ∀ z, z ∈ Set.Icc (-f t) (U t) → 0 ≤ W t z := fun z hz => hW_nonneg t htA z hz
    have h_abs_int : (∫ z in Set.Icc (-f t) (U t), |t * W t z|) =
        |t| * ∫ z in Set.Icc (-f t) (U t), W t z := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change |t * W t z| = |t| * W t z
      rw [abs_mul, abs_of_nonneg (hWn z hz)]
    have h_int : (∫ z in Set.Icc (-f t) (U t), t * W t z) =
        t * ∫ z in Set.Icc (-f t) (U t), W t z := by
      rw [MeasureTheory.integral_const_mul]
    have hW_int_nonneg : 0 ≤ ∫ z in Set.Icc (-f t) (U t), W t z := by
      exact setIntegral_nonneg measurableSet_Icc (fun z hz => hWn z hz)
    rw [h_abs_int, h_int, one_mul, add_zero]
    rw [abs_mul, abs_of_nonneg hW_int_nonneg]
  have hC2_int : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b) volume := by
    exact MeasureTheory.integrableOn_const (μ := volume) (s := Set.Icc a b) (C := 0)
      (by exact ne_of_lt (measure_Icc_lt_top (μ := volume))) (by finiteness)
  have hmain := Kprod_mul_phi_eq (d := d) (n := n) (a := a) (b := b) (s := s) (h := h)
    (f := f) (φ := fun p : ℝ × ℝ => p.1) (C1 := 1) (C2 := 0)
    hdn hn hab hf_nonneg hf_meas hφ_meas hsec_int habs_bound hC2_int
  simpa [m, U, W, c, Kprod, intervalIntegral.integral_const_mul] using hmain


lemma last_Kprod_eq {d n : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let m : ℕ := d - 2
    let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h))
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    let Kprod : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1^2}
    (∫ p in Kprod, p.2.1) = c * ∫ t in a..b, ∫ z in (-f t)..(U t), z * W t z := by
  classical
  intro m U W c Kprod
  haveI : Nonempty (Fin m) := by
    have hdpos : 0 < d := Nat.pos_of_neZero d
    have hmpos : 0 < m := by dsimp [m]; omega
    exact Fin.pos_iff_nonempty.mp hmpos
  have hn1 : 1 ≤ n := by omega
  let M : ℝ := |s| * max |a| |b| + |h|
  have hφ_meas : Measurable (fun p : ℝ × ℝ => p.2) := measurable_snd
  have hsec_int : ∀ t : ℝ, IntegrableOn (fun z => z * W t z) (Set.Icc (-f t) (U t)) volume := by
    intro t
    have hcont : ContinuousOn (fun z : ℝ => z * W t z) (Set.Icc (-f t) (U t)) := by
      dsimp [W]
      fun_prop
    exact ContinuousOn.integrableOn_compact isCompact_Icc hcont
  have hL_abs : ∀ t, t ∈ Set.Icc a b → |s * t + h| ≤ M := by
    intro t ht
    dsimp [M]
    exact abs_affine_le_const hab ht
  have habs_bound : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      (∫ z in Set.Icc (-f t) (U t), |z * W t z|) ≤
        (4 * (n : ℝ) * (4 / 3 : ℝ) ^ n) * |∫ z in Set.Icc (-f t) (U t), z * W t z| +
          2 * ((2 * M) ^ (2 * n)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t htA
    have hF : 0 ≤ f t := hf_nonneg t htA
    have hL := hL_abs t htA
    have hbound := intervalIntegral_abs_zW_le_const hn1 hF hL
    have hmeasC : MeasurableSet (Set.Icc (-f t) (U t)) := measurableSet_Icc
    have hW_nonneg : ∀ z, z ∈ Set.Icc (-f t) (U t) → 0 ≤ W t z := by
      intro z hz
      have hz1 : -f t ≤ z := hz.1
      have hzU : z ≤ U t := hz.2
      have hUf : U t ≤ f t := by
        dsimp [U]
        exact max_le (by linarith) (min_le_left _ _)
      have hzf : z ≤ f t := le_trans hzU hUf
      have hsq : z ^ 2 ≤ f t ^ 2 := sq_le_sq' hz1 hzf
      dsimp [W]
      exact pow_nonneg (by nlinarith) _
    have h_abs_eq : (∫ z in Set.Icc (-f t) (U t), |z * W t z|) =
        ∫ z in Set.Icc (-f t) (U t), |z| * W t z := by
      apply MeasureTheory.setIntegral_congr_fun hmeasC
      intro z hz
      change |z * W t z| = |z| * W t z
      rw [abs_mul, abs_of_nonneg (hW_nonneg z hz)]
    rw [h_abs_eq]
    rw [← intervalIntegral_eq_setIntegral_Icc (show -f t ≤ U t by dsimp [U]; exact le_max_left _ _)]
    rw [← intervalIntegral_eq_setIntegral_Icc (show -f t ≤ U t by dsimp [U]; exact le_max_left _ _)]
    dsimp [U, W]
    exact hbound
  have hC2_int : IntegrableOn (fun _ : ℝ => 2 * ((2 * M) ^ (2 * n))) (Set.Icc a b) volume := by
    exact MeasureTheory.integrableOn_const (μ := volume) (s := Set.Icc a b) (C := 2 * ((2 * M) ^ (2 * n)))
      (by exact ne_of_lt (measure_Icc_lt_top (μ := volume))) (by finiteness)
  have hmain := Kprod_mul_phi_eq (d := d) (n := n) (a := a) (b := b) (s := s) (h := h)
    (f := f) (φ := fun p : ℝ × ℝ => p.2) (C1 := 4 * (n : ℝ) * (4 / 3 : ℝ) ^ n)
    (C2 := 2 * ((2 * M) ^ (2 * n)))
    hdn hn hab hf_nonneg hf_meas hφ_meas hsec_int habs_bound hC2_int
  simpa [m, U, W, c, Kprod, intervalIntegral.integral_const_mul] using hmain


lemma middle_Kprod_moment_zero {d n : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) {j : Fin (d - 2)} :
    let m : ℕ := d - 2
    let Kprod : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ i : Fin m, (p.2.2 i)^2 ≤ f p.1^2}
    (∫ p in Kprod, p.2.2 j) = 0 := by
  classical
  intro m Kprod
  haveI : Nonempty (Fin m) := by
    have hdpos : 0 < d := Nat.pos_of_neZero d
    have hmpos : 0 < m := by dsimp [m]; omega
    exact Fin.pos_iff_nonempty.mp hmpos
  let e_neg : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) := MeasurableEquiv.neg _
  let e_mid : (ℝ × (Fin m → ℝ)) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    (MeasurableEquiv.refl ℝ).prodCongr e_neg
  let T : (ℝ × (ℝ × (Fin m → ℝ))) ≃ᵐ (ℝ × (ℝ × (Fin m → ℝ))) :=
    (MeasurableEquiv.refl ℝ).prodCongr e_mid
  have h_neg_mp : MeasurePreserving (fun y : Fin m → ℝ => -y) volume volume :=
    Measure.measurePreserving_neg volume
  have h_mid_mp : MeasurePreserving (fun q : ℝ × (Fin m → ℝ) => (q.1, -q.2)) volume volume :=
    MeasurePreserving.prod (MeasurePreserving.id volume) h_neg_mp
  have hT_mp : MeasurePreserving (⇑T) volume volume := by
    dsimp [T, e_mid, e_neg]
    exact MeasurePreserving.prod (MeasurePreserving.id volume) h_mid_mp
  set_option maxHeartbeats 1000000 in
  have hK_meas : MeasurableSet Kprod := by
    dsimp [Kprod]
    measurability
  have hpre : T ⁻¹' Kprod = Kprod := by
    ext p
    rcases p with ⟨t, z, y⟩
    change (t, z, -y) ∈ Kprod ↔ (t, z, y) ∈ Kprod
    simp [Kprod, neg_sq]
  have hchange := MeasurePreserving.setIntegral_preimage_emb hT_mp T.measurableEmbedding
    (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) Kprod
  rw [hpre] at hchange
  have hleft : (∫ p in Kprod, (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) (T p)) =
      ∫ p in Kprod, - (p.2.2 j) := by
    apply setIntegral_congr_fun hK_meas
    intro p hp
    rcases p with ⟨t, z, y⟩
    change - y j = - y j
    rfl
  rw [hleft] at hchange
  have hneg : (∫ p in Kprod, - (p.2.2 j)) = - ∫ p in Kprod, p.2.2 j := by
    simp [integral_neg]
  rw [hneg] at hchange
  linarith


lemma coordDecomp_preimage_Kprod_eq {d : ℕ} [NeZero d] {a b s h : ℝ} {f : ℝ → ℝ}
    (h2 : 2 ≤ d) :
    let K : Set (Fin d → ℝ) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > (0 : Fin d), (x i)^2 ≤ f (x 0)^2}
    let H : Set (Fin d → ℝ) := {x | x (lastFin d) ≤ s * x 0 + h}
    let Kprod : Set (ℝ × (ℝ × (Fin (d - 2) → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin (d - 2), (p.2.2 j)^2 ≤ f p.1^2}
    K ∩ H = coordDecomp d h2 ⁻¹' Kprod := by
  intro K H Kprod
  ext x
  simp [K, H, Kprod, coordDecomp_fst, coordDecomp_snd_fst, coordDecomp_snd_snd,
    sum_Ioi_eq_last_add_middle h2 x, and_left_comm, and_assoc]
  tauto

lemma body_of_revolution_cap_integrals_even_fun {d n : ℕ} [NeZero d] {a b s h : ℝ}
    {f : ℝ → ℝ} (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (Fin d → ℝ) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > (0 : Fin d), (x i)^2 ≤ f (x 0)^2}
    let H : Set (Fin d → ℝ) := {x | x (lastFin d) ≤ s * x 0 + h}
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
    volume.real (K ∩ H) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), W t z ∧
    (∫ x in K ∩ H, x 0) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), t * W t z ∧
    (∫ x in K ∩ H, x (lastFin d)) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), z * W t z ∧
    (∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → (∫ x in K ∩ H, x i) = 0) := by
  intro last K H W c
  have h2 : 2 ≤ d := by omega
  let m : ℕ := d - 2
  haveI : Nonempty (Fin m) := by
    have hdpos : 0 < d := Nat.pos_of_neZero d
    have hmpos : 0 < m := by dsimp [m]; omega
    exact Fin.pos_iff_nonempty.mp hmpos
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h))
  let Kprod : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
    {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
      p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1^2}
  have hpre' : K ∩ H = coordDecomp d h2 ⁻¹' Kprod := by
    simpa [K, H, Kprod, m] using
      (coordDecomp_preimage_Kprod_eq (d := d) (a := a) (b := b) (s := s) (h := h) (f := f) h2)
  have hcoord_mp := coordDecomp_measurePreserving d h2
  set_option maxHeartbeats 1000000 in
  have hKprod_meas : MeasurableSet Kprod := by
    dsimp [Kprod]
    measurability
  have hpre_meas : MeasurableSet (coordDecomp d h2 ⁻¹' Kprod) :=
    hKprod_meas.preimage hcoord_mp.measurable

  have hvolK : volume.real (K ∩ H) = volume.real Kprod := by
    rw [hpre']
    change volume.real (coordDecomp d h2 ⁻¹' Kprod) = volume.real Kprod
    exact MeasurePreserving.measureReal_preimage_emb hcoord_mp Kprod
  have hvolP := volume_Kprod_eq (d := d) (n := n) (a := a) (b := b) (s := s) (h := h) (f := f)
    hdn hn hab hf_nonneg hf_meas
  have hvol_eq : volume.real (K ∩ H) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), W t z := by
    rw [hvolK]
    simpa [m, U, W, c, Kprod] using hvolP

  have hx0K : (∫ x in K ∩ H, x 0) = ∫ p in Kprod, p.1 := by
    rw [hpre']
    refine (setIntegral_congr_fun hpre_meas ?_).trans
      (MeasurePreserving.setIntegral_comp' hcoord_mp (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.1) Kprod hKprod_meas)
    intro x hx
    simp [coordDecomp_fst]
  have hx0P := x0_Kprod_eq (d := d) (n := n) (a := a) (b := b) (s := s) (h := h) (f := f)
    hdn hn hab hf_nonneg hf_meas
  have hx0_eq : (∫ x in K ∩ H, x 0) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), t * W t z := by
    rw [hx0K]
    simpa [m, U, W, c, Kprod] using hx0P

  have hlastK : (∫ x in K ∩ H, x (lastFin d)) = ∫ p in Kprod, p.2.1 := by
    rw [hpre']
    refine (setIntegral_congr_fun hpre_meas ?_).trans
      (MeasurePreserving.setIntegral_comp' hcoord_mp (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.1) Kprod hKprod_meas)
    intro x hx
    simp [coordDecomp_snd_fst]
  have hlastP := last_Kprod_eq (d := d) (n := n) (a := a) (b := b) (s := s) (h := h) (f := f)
    hdn hn hab hf_nonneg hf_meas
  have hlast_eq : (∫ x in K ∩ H, x (lastFin d)) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), z * W t z := by
    rw [hlastK]
    simpa [m, U, W, c, Kprod] using hlastP

  have hmid_all : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → (∫ x in K ∩ H, x i) = 0 := by
    intro i hi0 hilast
    have hi0val : i.val ≠ 0 := by
      intro h
      apply hi0
      exact Fin.ext (by simpa using h)
    have hilastval : i.val ≠ d - 1 := by
      intro h
      apply hilast
      exact Fin.ext (by simpa [lastFin] using h)
    let j : Fin m := ⟨i.val - 1, by dsimp [m]; omega⟩
    have hj : middleIndex d h2 j = i := by
      apply Fin.ext
      dsimp [middleIndex, j]
      omega
    have hmidK : (∫ x in K ∩ H, x i) = ∫ p in Kprod, p.2.2 j := by
      rw [hpre']
      refine (setIntegral_congr_fun hpre_meas ?_).trans
        (MeasurePreserving.setIntegral_comp' hcoord_mp (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) Kprod hKprod_meas)
      intro x hx
      rw [← hj]
      simp [coordDecomp_snd_snd]
    have hmidP := middle_Kprod_moment_zero (d := d) (n := n) (a := a) (b := b) (s := s) (h := h)
      (f := f) hdn hn hab hf_nonneg hf_meas (j := j)
    rw [hmidK]
    simpa [m, Kprod] using hmidP

  exact ⟨hvol_eq, hx0_eq, hlast_eq, hmid_all⟩



/-! ## The main theorem -/

lemma body_of_revolution_cap_integrals_even {d n : ℕ} [NeZero d] {a b s h : ℝ}
    {f : ℝ → ℝ} (hdn : d = 2 * n) (hn : 2 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    let H : Set (EuclideanSpace ℝ (Fin d)) := {x | x last ≤ s * x 0 + h}
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
    volume.real (K ∩ H) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), W t z ∧
    (∫ x in K ∩ H, x 0) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), t * W t z ∧
    (∫ x in K ∩ H, x last) =
      c * ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h))), z * W t z ∧
    (∀ i : Fin d, i ≠ 0 → i ≠ last → (∫ x in K ∩ H, x i) = 0) := by
  intro last K H W c
  have hlast_eq : last = lastFin d := by
    apply Fin.ext
    dsimp [last, lastFin]
  let e : (Fin d → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin d) := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have he_mp : MeasurePreserving (⇑e) volume volume := PiLp.volume_preserving_toLp (ι := Fin d)
  let Kf : Set (Fin d → ℝ) :=
    {x | x 0 ∈ Set.Icc a b ∧ ∑ i > (0 : Fin d), (x i)^2 ≤ f (x 0)^2}
  let Hf : Set (Fin d → ℝ) := {x | x (lastFin d) ≤ s * x 0 + h}
  have hpre_e : e ⁻¹' (K ∩ H) = Kf ∩ Hf := by
    ext x
    simp [K, H, Kf, Hf, e, PiLp.toLp_apply, hlast_eq, lastFin]
  have hKmeas : MeasurableSet (K ∩ H) := by
    dsimp [K, H]
    measurability
  have hKfmeas : MeasurableSet (Kf ∩ Hf) := by
    dsimp [Kf, Hf]
    measurability
  have hvol_trans : volume.real (K ∩ H) = volume.real (Kf ∩ Hf) := by
    rw [← hpre_e]
    exact (MeasurePreserving.measureReal_preimage_emb he_mp (K ∩ H)).symm
  have hx0_trans : (∫ x in K ∩ H, x 0) = ∫ y in Kf ∩ Hf, y 0 := by
    rw [← hpre_e]
    have h := MeasurePreserving.setIntegral_comp' he_mp (fun y : EuclideanSpace ℝ (Fin d) => y 0) (K ∩ H) hKmeas
    simpa [e, PiLp.toLp_apply] using h.symm
  have hlast_trans : (∫ x in K ∩ H, x last) = ∫ y in Kf ∩ Hf, y (lastFin d) := by
    rw [← hpre_e]
    have h := MeasurePreserving.setIntegral_comp' he_mp (fun y : EuclideanSpace ℝ (Fin d) => y last) (K ∩ H) hKmeas
    simpa [e, PiLp.toLp_apply, hlast_eq] using h.symm
  have hmid_trans : ∀ i : Fin d, i ≠ 0 → i ≠ last →
      (∫ x in K ∩ H, x i) = ∫ y in Kf ∩ Hf, y i := by
    intro i hi0 hilast
    rw [← hpre_e]
    have h := MeasurePreserving.setIntegral_comp' he_mp (fun y : EuclideanSpace ℝ (Fin d) => y i) (K ∩ H) hKmeas
    simpa [e, PiLp.toLp_apply] using h.symm
  have hfun := body_of_revolution_cap_integrals_even_fun (d := d) (n := n) (a := a) (b := b) (s := s) (h := h)
    (f := f) hdn hn hab hf_nonneg hf_meas
  rcases hfun with ⟨hvolf, hx0f, hlastf, hmidf⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hvol_trans]
    simpa [Kf, Hf, W, c] using hvolf
  · rw [hx0_trans]
    simpa [Kf, Hf, W, c] using hx0f
  · rw [hlast_trans]
    simpa [Kf, Hf, W, c] using hlastf
  · intro i hi0 hilast
    rw [hmid_trans i hi0 hilast]
    have hilast' : i ≠ lastFin d := by
      intro h; apply hilast; simpa [← hlast_eq] using h
    simpa [Kf, Hf] using hmidf i hi0 hilast'



end

end Commons.Geometry.Ulam