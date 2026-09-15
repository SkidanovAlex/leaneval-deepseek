import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.MeasureTheory.Volume.volume_pi_Icc
import Submission.Commons.Analysis.Complex.zero_set_analyticOnNhd_closedBall_finite

set_option maxHeartbeats 3200000

open _root_.MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.Complex

/-! ## Helper lemmas -/

/-- Sup-norm bound for `Fin.cons`. -/
lemma cartan_norm_finCons_le_one {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1) {w : Fin n → ℂ}
    (hw : ∀ i, ‖w i‖ ≤ 1) : ‖(Fin.cons z w : Fin (n + 1) → ℂ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  induction i using Fin.cases with
  | zero => simpa using hz
  | succ j => simpa using hw j

/-- Coordinatewise description of `Fin.cons` for real sequences. -/
lemma cartan_forall_abs_finCons {n : ℕ} (x1 : ℝ) (w : Fin n → ℝ) (c : ℝ) :
    (∀ i : Fin (n + 1), |(Fin.cons x1 w : Fin (n + 1) → ℝ) i| ≤ c)
      ↔ |x1| ≤ c ∧ ∀ i : Fin n, |w i| ≤ c := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun i => by simpa using h i.succ⟩
  · rintro ⟨h0, h⟩ i
    induction i using Fin.cases with
    | zero => simpa using h0
    | succ j => simpa using h j

/-- Casting `Fin.cons` of real sequences to complex sequences. -/
lemma cartan_ofReal_finCons {n : ℕ} (x1 : ℝ) (w : Fin n → ℝ) :
    (fun i : Fin (n + 1) => (((Fin.cons x1 w : Fin (n + 1) → ℝ) i : ℝ) : ℂ))
      = (Fin.cons (x1 : ℂ) (fun i : Fin n => ((w i : ℝ) : ℂ)) : Fin (n + 1) → ℂ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp

/-- Analyticity of the slice `z ↦ G (Fin.cons z w)`. -/
lemma cartan_analyticOnNhd_finCons_comp_left {n : ℕ} {G : (Fin (n + 1) → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1)) (w : Fin n → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun z : ℂ => G (Fin.cons z w)) (Metric.closedBall 0 1) := by
  classical
  let L : ℂ →L[ℂ] (Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi (R := ℂ) (M := ℂ) (ι := Fin (n + 1)) (φ := fun _ => ℂ)
      (fun i : Fin (n + 1) =>
        Fin.cases (1 : ℂ →L[ℂ] ℂ) (fun _ : Fin n => (0 : ℂ →L[ℂ] ℂ)) i)
  have hL : ∀ z : ℂ, L z = (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) := by
    intro z
    funext i
    show (ContinuousLinearMap.pi (R := ℂ) (M := ℂ) (ι := Fin (n + 1)) (φ := fun _ => ℂ)
      (fun i : Fin (n + 1) =>
        Fin.cases (1 : ℂ →L[ℂ] ℂ) (fun _ : Fin n => (0 : ℂ →L[ℂ] ℂ)) i)) z i = _
    rw [ContinuousLinearMap.pi_apply]
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp [Fin.cons_succ]
  have hAn : AnalyticOnNhd ℂ (fun z : ℂ => L z + Fin.cons 0 w) (Metric.closedBall 0 1) :=
    (ContinuousLinearMap.analyticOnNhd L _).add analyticOnNhd_const
  have hAn2 : AnalyticOnNhd ℂ (fun z : ℂ => G (L z + Fin.cons 0 w)) (Metric.closedBall 0 1) := by
    refine hG.comp hAn ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    change ‖L z + Fin.cons 0 w‖ ≤ 1
    have hzw : L z + Fin.cons 0 w = (Fin.cons z w : Fin (n + 1) → ℂ) := by
      rw [hL z]
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hzw]
    exact cartan_norm_finCons_le_one hz hw
  have hfun : (fun z : ℂ => G (Fin.cons z w)) = (fun z => G (L z + Fin.cons 0 w)) := by
    funext z
    congr 1
    rw [hL z]
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  rw [hfun]
  exact hAn2


/-- Analyticity of the slice `w ↦ G (Fin.cons z w)`. -/
lemma cartan_analyticOnNhd_finCons_comp {n : ℕ} {G : (Fin (n + 1) → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1)) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun w : Fin n → ℂ => G (Fin.cons z w)) (Metric.closedBall 0 1) := by
  classical
  let L : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi (R := ℂ) (M := Fin n → ℂ) (ι := Fin (n + 1)) (φ := fun _ => ℂ)
      (fun i : Fin (n + 1) => Fin.cases (0 : (Fin n → ℂ) →L[ℂ] ℂ)
        (fun j : Fin n => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ)) j) i)
  have hL : ∀ w : Fin n → ℂ, L w = (Fin.cons (0 : ℂ) w : Fin (n + 1) → ℂ) := by
    intro w
    funext i
    show (ContinuousLinearMap.pi (R := ℂ) (M := Fin n → ℂ) (ι := Fin (n + 1)) (φ := fun _ => ℂ)
      (fun i : Fin (n + 1) => Fin.cases (0 : (Fin n → ℂ) →L[ℂ] ℂ)
        (fun j : Fin n => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ)) j) i)) w i = _
    rw [ContinuousLinearMap.pi_apply]
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp [Fin.cons_succ]
  have hAn : AnalyticOnNhd ℂ (fun w : Fin n → ℂ => L w + Fin.cons z 0) (Metric.closedBall 0 1) :=
    (ContinuousLinearMap.analyticOnNhd L _).add analyticOnNhd_const
  have hAn2 : AnalyticOnNhd ℂ (fun w : Fin n → ℂ => G (L w + Fin.cons z 0))
      (Metric.closedBall 0 1) := by
    refine hG.comp hAn ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    change ‖L w + Fin.cons z 0‖ ≤ 1
    have hzw : L w + Fin.cons z 0 = (Fin.cons z w : Fin (n + 1) → ℂ) := by
      rw [hL w]
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hzw]
    exact cartan_norm_finCons_le_one hz (fun i => le_trans (norm_le_pi_norm w i) hw)
  have hfun : (fun w : Fin n → ℂ => G (Fin.cons z w)) = (fun w => G (L w + Fin.cons z 0)) := by
    funext w
    congr 1
    rw [hL w]
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  rw [hfun]
  exact hAn2

/-- Generic measurability: for `f` continuous on a measurable set `s`, the set
`s ∩ f ⁻¹' t` is measurable. -/
lemma cartan_measurableSet_inter_preimage {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {f : α → ℂ} {s : Set α} (hs : MeasurableSet s)
    (hf : ContinuousOn f s) {t : Set ℂ} (ht : MeasurableSet t) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  classical
  have hmeas : Measurable (s.piecewise f 0) :=
    ContinuousOn.measurable_piecewise hf continuous_const.continuousOn hs
  have h : s ∩ f ⁻¹' t = s ∩ (s.piecewise f 0) ⁻¹' t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, by rwa [Set.piecewise_eq_of_mem s f 0 hx]⟩
    · rintro ⟨hx, hpx⟩
      exact ⟨hx, by rwa [Set.piecewise_eq_of_mem s f 0 hx] at hpx⟩
  rw [h]
  exact hs.inter (hmeas ht)

/-- Volume of the unit cube in `Fin n → ℝ`. -/
lemma cartan_volume_cube (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) {w : Fin n → ℝ | ∀ i, |w i| ≤ 1} = ENNReal.ofReal (2 ^ n) := by
  have hset : {w : Fin n → ℝ | ∀ i, |w i| ≤ 1}
      = Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
    ext w
    rw [Set.mem_univ_pi]
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    exact ⟨fun h i => abs_le.mp (h i), fun h i => abs_le.mpr (h i)⟩
  rw [hset, Commons.MeasureTheory.Volume.volume_pi_Icc (1 : ℝ) (by norm_num)]
  norm_num

/-- The polydisk Cartan measure estimate. -/
theorem cartan_polydisk_measure {δ H M m : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hM1 : 1 ≤ M)
    (h1 : ∀ (g : ℂ → ℂ), AnalyticOnNhd ℂ g (Metric.closedBall 0 1) → ∀ (m' : ℝ),
        (∃ z : ℂ, ‖z‖ ≤ 1 - 3 * δ ∧ g z ≠ 0 ∧ m' ≤ Real.log ‖g z‖) →
        (∀ z : ℂ, ‖z‖ ≤ 1 → ‖g z‖ ≤ M) →
        MeasureTheory.volume {x : ℝ | |x| ≤ 1 - 2 * δ ∧
          Real.log ‖g (x : ℂ)‖ < m' - (Real.log M - m') *
            (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))}
          ≤ ENNReal.ofReal (10 * H))
    (d : ℕ) (hd : 1 ≤ d) (G : (Fin d → ℂ) → ℂ) (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1))
    (hm : ∃ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1 - 3 * δ) ∧ G z ≠ 0 ∧ m ≤ Real.log ‖G z‖)
    (hMb : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖G z‖ ≤ M) :
    MeasureTheory.volume {x : Fin d → ℝ | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
        Real.log ‖G (fun i => (x i : ℂ))‖ < m - (Real.log M - m) *
          ((1 + (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) +
            δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))) ^ d - 1)}
      ≤ ENNReal.ofReal (20 ^ d * H) := by
  classical
  set Kc : ℝ := 2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H) with hKc
  set kap : ℝ := 1 + Kc with hkap
  have main : ∀ n : ℕ, ∀ (m' : ℝ) (G' : (Fin n → ℂ) → ℂ),
      AnalyticOnNhd ℂ G' (Metric.closedBall 0 1) →
      (∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1 - 3 * δ) ∧ G' z ≠ 0 ∧ m' ≤ Real.log ‖G' z‖) →
      (∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖G' z‖ ≤ M) →
      MeasureTheory.volume {x : Fin n → ℝ | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
        Real.log ‖G' (fun i => (x i : ℂ))‖ < m' - (Real.log M - m') * (kap ^ n - 1)}
        ≤ ENNReal.ofReal (20 ^ n * H) := by
    intro n
    induction n with
    | zero =>
      intro m' G' hG' hm' hMb'
      have hset : {x : Fin 0 → ℝ | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
          Real.log ‖G' (fun i => (x i : ℂ))‖ < m' - (Real.log M - m') * (kap ^ 0 - 1)} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x
        simp only [Set.mem_setOf_eq]
        rintro ⟨-, hlt⟩
        obtain ⟨z, -, hzne, hzm⟩ := hm'
        have hx : (fun i : Fin 0 => (x i : ℂ)) = z := Subsingleton.elim _ _
        rw [hx] at hlt
        have h0 : m' - (Real.log M - m') * (kap ^ 0 - 1) = m' := by ring
        rw [h0] at hlt
        exact absurd hlt (not_lt.mpr hzm)
      rw [hset, measure_empty]
      exact bot_le
    | succ n ih =>
      intro m0 G0 hG0 hm0 hMb0
      obtain ⟨z0, hz0b, hz0ne, hz0m⟩ := hm0
      set Lg : ℝ := Real.log M - m0 with hLg
      set m1 : ℝ := m0 - Lg * Kc with hm1
      set z0' : Fin n → ℂ := fun i => z0 i.succ with hz0'
      set sliceC : ℂ → ℂ := fun z => G0 (Fin.cons z z0') with hsliceC
      set T : ℝ := m0 - Lg * (kap ^ (n + 1) - 1) with hT
      set E : Set (Fin (n + 1) → ℝ) :=
        {x | (∀ i, |x i| ≤ 1 - 2 * δ) ∧ Real.log ‖G0 (fun i => (x i : ℂ))‖ < T} with hEdef
      set B1 : Set ℝ := {x1 : ℝ | |x1| ≤ 1 - 2 * δ ∧ Real.log ‖sliceC (x1 : ℂ)‖ < m1} with hB1
      set B2 : Set ℝ := {x1 : ℝ | |x1| ≤ 1 ∧ sliceC (x1 : ℂ) = 0} with hB2
      set Bad : Set ℝ := B1 ∪ B2 with hBad
      set Good : Set ℝ := {x1 : ℝ | |x1| ≤ 1 - 2 * δ} \ Bad with hGood
      set sl : ℝ → ENNReal :=
        fun x1 => volume {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} with hsl
      set g : ℝ → ENNReal :=
        fun x1 => if x1 ∈ Bad then ENNReal.ofReal ((2 : ℝ) ^ n)
          else if x1 ∈ Good then ENNReal.ofReal (20 ^ n * H) else 0 with hg
      have hsl_apply : ∀ x1 : ℝ, sl x1 =
          volume {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} := by
        intro x1; rw [hsl]
      have hg_apply : ∀ x1 : ℝ, g x1 = (if x1 ∈ Bad then ENNReal.ofReal ((2 : ℝ) ^ n)
          else if x1 ∈ Good then ENNReal.ofReal (20 ^ n * H) else 0) := by
        intro x1; rw [hg]
      have hGood_mem : ∀ x1 : ℝ, x1 ∈ Good ↔ |x1| ≤ 1 - 2 * δ ∧ x1 ∉ Bad := by
        intro x1; rw [hGood]; simp only [Set.mem_sdiff, Set.mem_setOf_eq]
      have hT_rec : m1 - (Real.log M - m1) * (kap ^ n - 1) = T := by
        rw [hm1, hLg, hT, hkap, pow_succ]
        ring
      have hcons_z0 : (Fin.cons (z0 0) z0' : Fin (n + 1) → ℂ) = z0 := by
        funext i
        rw [hz0']
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      have hsliceC_an : AnalyticOnNhd ℂ sliceC (Metric.closedBall 0 1) := by
        rw [hsliceC]
        exact cartan_analyticOnNhd_finCons_comp_left hG0 z0'
          (fun i => le_trans (hz0b i.succ) (by linarith))
      -- measurability of E
      have hE : MeasurableSet E := by
        rw [hEdef]
        have hSmeas : MeasurableSet {x : Fin (n + 1) → ℝ | ∀ i, |x i| ≤ 1} := by
          have hIcc : {x : Fin (n + 1) → ℝ | ∀ i, |x i| ≤ 1}
              = Set.Icc (fun _ : Fin (n + 1) => (-1 : ℝ)) (fun _ => 1) := by
            ext w
            simp only [Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
            exact ⟨fun h => ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩,
                   fun h i => abs_le.mpr ⟨h.1 i, h.2 i⟩⟩
          rw [hIcc]; exact isClosed_Icc.measurableSet
        have hcont : ContinuousOn (fun x : Fin (n + 1) → ℝ => G0 (fun i => (x i : ℂ)))
            {x : Fin (n + 1) → ℝ | ∀ i, |x i| ≤ 1} := by
          refine hG0.continuousOn.comp
            (continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))).continuousOn ?_
          intro x hx
          rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
          intro i
          simpa [Complex.norm_real, Real.norm_eq_abs] using hx i
        have ht : MeasurableSet {z : ℂ | Real.log ‖z‖ < T} :=
          measurableSet_Iio.preimage (Real.measurable_log.comp continuous_norm.measurable)
        have hkey : {x : Fin (n + 1) → ℝ | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
              Real.log ‖G0 (fun i => (x i : ℂ))‖ < T}
            = {x : Fin (n + 1) → ℝ | ∀ i, |x i| ≤ 1 - 2 * δ} ∩
              ({x : Fin (n + 1) → ℝ | ∀ i, |x i| ≤ 1} ∩
                (fun x : Fin (n + 1) → ℝ => G0 (fun i => (x i : ℂ))) ⁻¹' {z : ℂ | Real.log ‖z‖ < T}) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, (fun i => le_trans (h1 i) (by linarith [hδ0.le])), h2⟩
          · rintro ⟨h1, -, h2⟩
            exact ⟨h1, h2⟩
        rw [hkey]
        refine MeasurableSet.inter ?_ (cartan_measurableSet_inter_preimage hSmeas hcont ht)
        rw [show {x : Fin (n + 1) → ℝ | ∀ i, |x i| ≤ 1 - 2 * δ}
            = ⋂ i, {x : Fin (n + 1) → ℝ | |x i| ≤ 1 - 2 * δ} from by ext x; simp]
        exact MeasurableSet.iInter (fun i => (isClosed_le (continuous_abs.comp (continuous_apply i))
          continuous_const).measurableSet)
      -- slicing
      have hslice : volume E = ∫⁻ x1 : ℝ, sl x1 := by
        have hslice' : volume E
            = ∫⁻ x1 : ℝ, volume {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} := by
          let ee : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
            MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
          have hmp : MeasurePreserving (⇑ee) volume volume :=
            volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
          have hE' : MeasurableSet (ee '' E) := ee.measurableSet_image.mpr hE
          have hee_symm : ∀ (x1 : ℝ) (w : Fin n → ℝ),
              ee.symm (x1, w) = (Fin.cons x1 w : Fin (n + 1) → ℝ) := by
            intro x1 w
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
            simp [Fin.insertNthEquiv]
          have hvol : volume (ee '' E) = volume E := by
            have h1 : volume (ee '' E) = Measure.map ee volume (ee '' E) := by rw [hmp.map_eq]
            rw [h1, Measure.map_apply ee.measurable hE']
            congr 1
            exact Set.preimage_image_eq E ee.injective
          calc volume E = volume (ee '' E) := hvol.symm
            _ = (volume.prod volume) (ee '' E) := rfl
            _ = ∫⁻ x1 : ℝ, volume (Prod.mk x1 ⁻¹' (ee '' E)) := Measure.prod_apply hE'
            _ = ∫⁻ x1 : ℝ, volume {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} := by
                  refine lintegral_congr (fun x1 => ?_)
                  have hmem : Prod.mk x1 ⁻¹' (ee '' E)
                      = {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} := by
                    ext w
                    simp only [Set.mem_preimage, Set.mem_setOf_eq]
                    constructor
                    · rintro ⟨x, hx, hxe⟩
                      have hx' : x = (Fin.cons x1 w : Fin (n + 1) → ℝ) := by
                        rw [← hee_symm x1 w, ← hxe, ee.symm_apply_apply]
                      rwa [← hx']
                    · intro h
                      exact ⟨ee.symm (x1, w), by rwa [hee_symm], ee.apply_symm_apply _⟩
                  rw [hmem]
        rw [show (∫⁻ x1 : ℝ, sl x1)
            = ∫⁻ x1 : ℝ, volume {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E}
            from lintegral_congr hsl_apply]
        exact hslice'
      -- pointwise bound
      have hpoint : ∀ x1 : ℝ, sl x1 ≤ g x1 := by
        intro x1
        rw [hsl_apply x1, hg_apply x1]
        by_cases hxB : x1 ∈ Bad
        · have hcube : volume {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E}
              ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
            by_cases hxle : |x1| ≤ 1 - 2 * δ
            · refine le_trans (measure_mono ?_) (le_of_eq (cartan_volume_cube n))
              intro w hw
              rw [hEdef] at hw
              have hw1 := (cartan_forall_abs_finCons x1 w (1 - 2 * δ)).mp hw.1
              exact fun i => le_trans (hw1.2 i) (by linarith [hδ0.le])
            · have hempty : {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} = ∅ := by
                ext w
                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
                intro hw
                rw [hEdef] at hw
                exact hxle ((cartan_forall_abs_finCons x1 w (1 - 2 * δ)).mp hw.1).1
              rw [hempty, measure_empty]
              exact bot_le
          rw [if_pos hxB]
          exact hcube
        · by_cases hxG : x1 ∈ Good
          · have hxle : |x1| ≤ 1 - 2 * δ := ((hGood_mem x1).mp hxG).1
            have hxBad : x1 ∉ Bad := ((hGood_mem x1).mp hxG).2
            have hlog : m1 ≤ Real.log ‖sliceC (x1 : ℂ)‖ := by
              by_contra hlt
              rw [not_le] at hlt
              exact hxBad (by rw [hBad]; left; rw [hB1]; exact ⟨hxle, hlt⟩)
            have hx1le1 : |x1| ≤ 1 := by linarith [hxle, hδ0.le]
            have hne : sliceC (x1 : ℂ) ≠ 0 := by
              intro hz
              exact hxBad (by rw [hBad]; right; rw [hB2]; exact ⟨hx1le1, hz⟩)
            have hana : AnalyticOnNhd ℂ (fun w : Fin n → ℂ => G0 (Fin.cons (x1 : ℂ) w))
                (Metric.closedBall 0 1) :=
              cartan_analyticOnNhd_finCons_comp hG0 (x1 : ℂ)
                (by rw [Complex.norm_real, Real.norm_eq_abs]
                    exact le_trans hxle (by linarith [hδ0.le]))
            have hbase : ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1 - 3 * δ) ∧
                (fun w : Fin n → ℂ => G0 (Fin.cons (x1 : ℂ) w)) z ≠ 0 ∧
                m1 ≤ Real.log ‖(fun w : Fin n → ℂ => G0 (Fin.cons (x1 : ℂ) w)) z‖ := by
              refine ⟨z0', fun i => le_trans (hz0b i.succ) le_rfl, ?_, ?_⟩
              · simpa [hsliceC] using hne
              · simpa [hsliceC] using hlog
            have hbnd : ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
                ‖(fun w : Fin n → ℂ => G0 (Fin.cons (x1 : ℂ) w)) z‖ ≤ M := by
              intro z hz
              exact hMb0 (Fin.cons (x1 : ℂ) z) (fun i => by
                induction i using Fin.cases with
                | zero => simpa [Fin.cons_zero] using
                    (show ‖(x1 : ℂ)‖ ≤ 1 by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)
                | succ j => simpa [Fin.cons_succ] using hz j)
            have hih := ih m1 (fun w : Fin n → ℂ => G0 (Fin.cons (x1 : ℂ) w)) hana hbase hbnd
            rw [if_neg hxB, if_pos hxG]
            have hseteq : {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E}
                = {w : Fin n → ℝ | (∀ i, |w i| ≤ 1 - 2 * δ) ∧
                    Real.log ‖G0 (Fin.cons (x1 : ℂ) (fun i => ((w i : ℝ) : ℂ)))‖
                      < m1 - (Real.log M - m1) * (kap ^ n - 1)} := by
              ext w
              rw [hEdef]
              simp only [Set.mem_setOf_eq]
              rw [cartan_forall_abs_finCons, cartan_ofReal_finCons]
              constructor
              · rintro ⟨⟨-, hw⟩, hlt⟩
                rw [← hT_rec] at hlt
                exact ⟨hw, hlt⟩
              · rintro ⟨hw, hlt⟩
                rw [hT_rec] at hlt
                exact ⟨⟨hxle, hw⟩, hlt⟩
            rw [hseteq]
            exact hih
          · have hxle : ¬ (|x1| ≤ 1 - 2 * δ) := fun h => hxG ((hGood_mem x1).mpr ⟨h, hxB⟩)
            have hempty : {w : Fin n → ℝ | (Fin.cons x1 w : Fin (n + 1) → ℝ) ∈ E} = ∅ := by
              ext w
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              intro hw
              rw [hEdef] at hw
              exact hxle ((cartan_forall_abs_finCons x1 w (1 - 2 * δ)).mp hw.1).1
            rw [hempty, measure_empty, if_neg hxB, if_neg hxG]
      have hInt : ∫⁻ x1 : ℝ, sl x1 ≤ ∫⁻ x1 : ℝ, g x1 := lintegral_mono hpoint
      -- measurability of Bad and Good, and their volumes
      have hcont1 : ContinuousOn (fun x : ℝ => sliceC (x : ℂ)) (Set.Icc (-1 : ℝ) 1) := by
        refine hsliceC_an.continuousOn.comp Complex.continuous_ofReal.continuousOn ?_
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (abs_le.mpr ⟨hx.1, hx.2⟩) (by norm_num)
      have hA : MeasurableSet {x1 : ℝ | |x1| ≤ 1 - 2 * δ} :=
        (isClosed_le continuous_abs continuous_const).measurableSet
      have hsub : {x1 : ℝ | |x1| ≤ 1 - 2 * δ} ⊆ Set.Icc (-1 : ℝ) 1 := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        rw [Set.mem_Icc]
        exact ⟨by linarith [(abs_le.mp hx).1, hδ0.le], by linarith [(abs_le.mp hx).2, hδ0.le]⟩
      have hB1meas : MeasurableSet B1 := by
        rw [hB1]
        have ht : MeasurableSet {z : ℂ | Real.log ‖z‖ < m1} :=
          measurableSet_Iio.preimage (Real.measurable_log.comp continuous_norm.measurable)
        have hmain := cartan_measurableSet_inter_preimage measurableSet_Icc hcont1 ht
        have hseteq : {x1 : ℝ | |x1| ≤ 1 - 2 * δ ∧ Real.log ‖sliceC (x1 : ℂ)‖ < m1}
            = {x1 : ℝ | |x1| ≤ 1 - 2 * δ} ∩ (Set.Icc (-1 : ℝ) 1 ∩
                (fun x : ℝ => sliceC (x : ℂ)) ⁻¹' {z : ℂ | Real.log ‖z‖ < m1}) := by
          ext x1
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, hsub h1, h2⟩
          · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
        rw [hseteq]
        exact hA.inter hmain
      have hB2meas : MeasurableSet B2 := by
        rw [hB2]
        have ht : MeasurableSet ({0} : Set ℂ) := measurableSet_singleton 0
        have hmain := cartan_measurableSet_inter_preimage measurableSet_Icc hcont1 ht
        have hseteq : {x1 : ℝ | |x1| ≤ 1 ∧ sliceC (x1 : ℂ) = 0}
            = Set.Icc (-1 : ℝ) 1 ∩ (fun x : ℝ => sliceC (x : ℂ)) ⁻¹' {0} := by
          ext x1
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
            Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, h2⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨abs_le.mpr ⟨h1, h2⟩, h3⟩
        rw [hseteq]
        exact hmain
      have hBadmeas : MeasurableSet Bad := by rw [hBad]; exact hB1meas.union hB2meas
      have hGoodmeas : MeasurableSet Good := by rw [hGood]; exact hA.diff hBadmeas
      have hB1vol : volume B1 ≤ ENNReal.ofReal (10 * H) := by
        have hthr : m0 - (Real.log M - m0) * Kc = m1 := by rw [← hLg, hm1]
        have hseteq : B1 = {x : ℝ | |x| ≤ 1 - 2 * δ ∧
            Real.log ‖sliceC (x : ℂ)‖ < m0 - (Real.log M - m0) * Kc} := by
          rw [hB1, hthr]
        rw [hseteq]
        exact h1 sliceC hsliceC_an m0
          ⟨z0 0, le_trans (hz0b 0) (by linarith),
            by rw [hsliceC]; change G0 (Fin.cons (z0 0) z0') ≠ 0; rw [hcons_z0]; exact hz0ne,
            by rw [hsliceC]; change m0 ≤ Real.log ‖G0 (Fin.cons (z0 0) z0')‖; rw [hcons_z0]; exact hz0m⟩
          (fun z hz => hMb0 (Fin.cons z z0') (fun i => by
            induction i using Fin.cases with
            | zero => simpa [Fin.cons_zero] using hz
            | succ j => simpa [Fin.cons_succ] using le_trans (hz0b j.succ) (by linarith)))
      have hB2vol : volume B2 = 0 := by
        rw [hB2]
        have hfin : {x : ℝ | |x| ≤ 1 ∧ sliceC (x : ℂ) = 0}.Finite := by
          refine zero_set_analyticOnNhd_closedBall_finite (R := 1) (by norm_num) hsliceC_an
            ⟨z0 0, ?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact le_trans (hz0b 0) (by linarith)
          · rw [hsliceC]; change G0 (Fin.cons (z0 0) z0') ≠ 0; rw [hcons_z0]; exact hz0ne
        exact hfin.measure_zero volume
      have hBadvol : volume Bad ≤ ENNReal.ofReal (10 * H) := by
        rw [hBad]
        calc volume (B1 ∪ B2) ≤ volume B1 + volume B2 := measure_union_le _ _
          _ = volume B1 + 0 := by rw [hB2vol]
          _ = volume B1 := add_zero _
          _ ≤ ENNReal.ofReal (10 * H) := hB1vol
      have hGoodvol : volume Good ≤ ENNReal.ofReal 2 := by
        rw [hGood]
        calc volume ({x1 : ℝ | |x1| ≤ 1 - 2 * δ} \ Bad)
            ≤ volume {x1 : ℝ | |x1| ≤ 1 - 2 * δ} := measure_mono Set.sdiff_subset
          _ ≤ volume (Set.Icc (-1 : ℝ) 1) := measure_mono hsub
          _ = ENNReal.ofReal 2 := by rw [Real.volume_Icc]; norm_num
      have hgint : ∫⁻ x1 : ℝ, g x1 = ENNReal.ofReal ((2 : ℝ) ^ n) * volume Bad
          + ENNReal.ofReal (20 ^ n * H) * volume Good := by
        have hfun : g = Bad.indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ n))
            + Good.indicator (fun _ => ENNReal.ofReal (20 ^ n * H)) := by
          funext x1
          rw [hg_apply x1, Pi.add_apply]
          by_cases h1 : x1 ∈ Bad
          · have h2 : x1 ∉ Good := fun h => ((hGood_mem x1).mp h).2 h1
            simp [h1, h2]
          · by_cases h2 : x1 ∈ Good
            · simp [h1, h2]
            · simp [h1, h2]
        rw [hfun]
        simp only [Pi.add_apply]
        rw [lintegral_add_left (Measurable.indicator measurable_const hBadmeas),
          lintegral_indicator_const hBadmeas, lintegral_indicator_const hGoodmeas]
      have hfinal : volume E ≤ ENNReal.ofReal (20 ^ (n + 1) * H) := by
        calc volume E = ∫⁻ x1 : ℝ, sl x1 := hslice
          _ ≤ ∫⁻ x1 : ℝ, g x1 := hInt
          _ = ENNReal.ofReal ((2 : ℝ) ^ n) * volume Bad
              + ENNReal.ofReal (20 ^ n * H) * volume Good := hgint
          _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (10 * H)
              + ENNReal.ofReal (20 ^ n * H) * ENNReal.ofReal 2 :=
                add_le_add (mul_le_mul_right hBadvol _) (mul_le_mul_right hGoodvol _)
          _ ≤ ENNReal.ofReal (20 ^ (n + 1) * H) := by
                rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity),
                    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (20 : ℝ) ^ n * H by positivity),
                    ← ENNReal.ofReal_add (show (0 : ℝ) ≤ (2 : ℝ) ^ n * (10 * H) by positivity)
                      (show (0 : ℝ) ≤ (20 : ℝ) ^ n * H * 2 by positivity)]
                apply ENNReal.ofReal_le_ofReal
                have h2n : (2 : ℝ) ^ n ≤ 20 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
                have hH : (0 : ℝ) ≤ H := le_of_lt hH0
                have hA : (2 : ℝ) ^ n * (10 * H) ≤ 20 ^ n * (10 * H) :=
                  mul_le_mul_of_nonneg_right h2n (by positivity)
                rw [pow_succ]
                nlinarith [hA, hH, pow_nonneg (show (0 : ℝ) ≤ 20 by norm_num) n]
      exact hfinal
  exact main d m G hG hm hMb

end Commons.Analysis.Complex