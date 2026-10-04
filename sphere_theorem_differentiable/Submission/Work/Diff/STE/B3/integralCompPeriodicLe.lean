import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.Periodic1_iVec
import Submission.Work.Diff.STE.B3.boxIdx_iUnion
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` norm of a `1`-periodic function composed with a local diffeomorphism

For a smooth `T : (ι → ℝ) → (ι → ℝ)` which is injective on the compact set `K` with
`det (fderiv T) ≠ 0` on `K`, and for a continuous `1`-periodic `v`, the `L²` norm of `v ∘ T` over
`K` is controlled by the `L²` norm of `v` over the fundamental cube.

The two ingredients are:

* the change of variables formula `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
  (on `K`, where `T` is injective and differentiable), together with the uniform positive lower
  bound of `|det (fderiv T)|` on the compact set `K`;
* `periodicIntegralLeCube_local`: a nonnegative `1`-periodic function whose `L²` is integrated over
  a set contained in the box `[-N,N]^ι` is bounded by the number `(2N+1)^(card ι)` of unit cubes
  covering that box, times its integral over the fundamental cube.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.Diff.STE.B3

/-! ## The covering of a box by unit cubes -/

/-- The vector `i ↦ ⌈x i⌉ - 1` of a point of the box `[-N,N]^ι` is an index of
`{-N-1,…,N}^ι`. -/
private lemma ceil_sub_one_mem_piFinset_Icc {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    {x : ι → ℝ} (hx : ∀ i, |x i| ≤ (N : ℝ)) :
    (fun i => ⌈x i⌉ - 1) ∈
      Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ) - 1) (N : ℤ)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : -(N : ℝ) ≤ x i := (abs_le.mp (hx i)).1
  have h2 : x i ≤ (N : ℝ) := (abs_le.mp (hx i)).2
  have hc1 : (-(N : ℤ)) ≤ ⌈x i⌉ := by
    have h : (-(N : ℝ)) ≤ ((⌈x i⌉ : ℤ) : ℝ) := le_trans h1 (Int.le_ceil (x i))
    exact_mod_cast h
  have hc2 : ⌈x i⌉ ≤ (N : ℤ) := (Int.ceil_le).mpr (by exact_mod_cast h2)
  constructor <;> omega

/-- The cells `m + (0,1]^ι`, `m ∈ {-N-1,…,N}^ι`, cover the box `[-N,N]^ι`. -/
private lemma mem_iUnion_piFinset_cells {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} {x : ι → ℝ}
    (hx : ∀ i, |x i| ≤ (N : ℝ)) :
    x ∈ ⋃ m ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ) - 1) (N : ℤ)),
      (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube := by
  refine Set.mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1,
    Set.mem_iUnion.mpr ⟨ceil_sub_one_mem_piFinset_Icc hx, ?_⟩⟩
  rw [mem_image_iVec_unitCube]
  intro i
  constructor
  · have h : ((⌈x i⌉ : ℤ) : ℝ) < x i + 1 := Int.ceil_lt_add_one (x i)
    push_cast
    linarith
  · have h : x i ≤ ((⌈x i⌉ : ℤ) : ℝ) := Int.le_ceil (x i)
    push_cast
    linarith

/-- Membership in the cell `m + (0,1]^ι` is membership of the translate `x - m` in the unit
cube. -/
private lemma mem_image_iVec_unitCube_add_neg {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℤ}
    {x : ι → ℝ} :
    x ∈ (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube ↔
      x + -(Work.Diff.STE.iVec m) ∈ Work.Diff.STE.unitCube := by
  rw [mem_image_iVec_unitCube]
  constructor
  · intro h i
    have hi := h i
    rw [Set.mem_Ioc] at hi
    have hmem : (x + -(Work.Diff.STE.iVec m)) i ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [Set.mem_Ioc]
      simp only [Pi.add_apply, Pi.neg_apply, Work.Diff.STE.iVec_apply] at *
      exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
    simpa only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] using hmem
  · intro h i
    have hi : (x + -(Work.Diff.STE.iVec m)) i ∈ Set.Ioc (0 : ℝ) 1 := by
      have hh := Set.mem_pi.mp h i (Set.mem_univ i)
      simpa only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] using hh
    rw [Set.mem_Ioc] at hi ⊢
    simp only [Pi.add_apply, Pi.neg_apply, Work.Diff.STE.iVec_apply] at hi
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- Change of variables for an integral over a translate of the unit cube: the integral over
`(m + (0,1]^ι)` of `g` is the integral over `(0,1]^ι` of `g (· + m)`. -/
private lemma setLIntegral_image_add_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℝ≥0∞) (hg : Measurable g) (m : ι → ℤ) :
    ∫⁻ x in (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube, g x
      = ∫⁻ x in Work.Diff.STE.unitCube, g (x + Work.Diff.STE.iVec m) := by
  classical
  haveI : (volume : Measure (ι → ℝ)).IsAddHaarMeasure := MeasureTheory.isAddHaarMeasure_volume_pi ι
  have hcube : MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := BesselCont.measSet_unitCube
  have hQmeas : MeasurableSet
      ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube) :=
    ((MeasurableEquiv.addRight (Work.Diff.STE.iVec m)).measurableEmbedding.measurableSet_image).mpr
      hcube
  have hf : Measurable
      (Work.Diff.STE.unitCube.indicator (fun y : ι → ℝ => g (y + Work.Diff.STE.iVec m))) :=
    (hg.comp (measurable_add_const (Work.Diff.STE.iVec m))).indicator hcube
  have hsymm : (∫⁻ x, Work.Diff.STE.unitCube.indicator
        (fun y : ι → ℝ => g (y + Work.Diff.STE.iVec m)) (x + -(Work.Diff.STE.iVec m)))
      = ∫⁻ x, Work.Diff.STE.unitCube.indicator (fun y : ι → ℝ => g (y + Work.Diff.STE.iVec m)) x :=
    (measurePreserving_add_right (volume : Measure (ι → ℝ))
      (-(Work.Diff.STE.iVec m))).lintegral_comp hf
  have hper : ∀ x : ι → ℝ,
      ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube).indicator g x
        = Work.Diff.STE.unitCube.indicator (fun y : ι → ℝ => g (y + Work.Diff.STE.iVec m))
            (x + -(Work.Diff.STE.iVec m)) := by
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube
    · rw [if_pos hx, if_pos (mem_image_iVec_unitCube_add_neg.mp hx)]
      simp only [add_assoc, neg_add_cancel, add_zero]
    · rw [if_neg hx, if_neg (fun hc => hx (mem_image_iVec_unitCube_add_neg.mpr hc))]
  calc ∫⁻ x in (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube, g x
      = ∫⁻ x, ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube).indicator g x :=
        (MeasureTheory.lintegral_indicator hQmeas g).symm
    _ = ∫⁻ x, Work.Diff.STE.unitCube.indicator (fun y : ι → ℝ => g (y + Work.Diff.STE.iVec m))
          (x + -(Work.Diff.STE.iVec m)) := lintegral_congr hper
    _ = ∫⁻ x, Work.Diff.STE.unitCube.indicator (fun y : ι → ℝ => g (y + Work.Diff.STE.iVec m)) x :=
        hsymm
    _ = ∫⁻ x in Work.Diff.STE.unitCube, g (x + Work.Diff.STE.iVec m) :=
        MeasureTheory.lintegral_indicator hcube _

/-- **The periodic bound.**  A nonnegative continuous `1`-periodic `f` integrated over a
measurable set contained in the box `[-N,N]^ι` is bounded by `(2N+1)^(card ι)` times its integral
over the fundamental cube. -/
theorem periodicIntegralLeCube_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hfnn : ∀ x, 0 ≤ f x) (hfcont : Continuous f)
    (hfper : Work.Diff.STE.Periodic1 f)
    (A : Set (ι → ℝ)) (hAmeas : MeasurableSet A) (N : ℕ)
    (hA : ∀ x ∈ A, ∀ i : ι, |x i| ≤ (N : ℝ)) :
    ∫ x in A, f x ≤ (2 * (N : ℝ) + 2) ^ Fintype.card ι *
      ∫ x in Work.Diff.STE.unitCube, f x := by
  classical
  have hcube : MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := BesselCont.measSet_unitCube
  set S : Finset (ι → ℤ) := Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ) - 1) (N : ℤ))
    with hS
  set g : (ι → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hgdef
  have hgmeas : Measurable g := ENNReal.measurable_ofReal.comp hfcont.measurable
  have hgper : ∀ (m : ι → ℤ) (x : ι → ℝ), g (x + Work.Diff.STE.iVec m) = g x := by
    intro m x
    show ENNReal.ofReal (f (x + Work.Diff.STE.iVec m)) = ENNReal.ofReal (f x)
    rw [Periodic1_iVec hfper m x]
  have hcellmeas : ∀ m : ι → ℤ, MeasurableSet
      ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube) := fun m =>
    ((MeasurableEquiv.addRight (Work.Diff.STE.iVec m)).measurableEmbedding.measurableSet_image).mpr
      hcube
  -- the pointwise covering of `A`, and the subadditivity of the `lintegral`
  have hsub : ∫⁻ x in A, g x ≤ ∑ m ∈ S,
      ∫⁻ x in (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube, g x := by
    have hpt : ∀ x : ι → ℝ, A.indicator g x ≤ ∑ m ∈ S,
        ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube).indicator g x := by
      intro x
      by_cases hxA : x ∈ A
      · have hmem : x ∈ ⋃ m ∈ S,
            (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube := by
          rw [hS]; exact mem_iUnion_piFinset_cells (hA x hxA)
        simp only [Set.mem_iUnion, exists_prop] at hmem
        obtain ⟨m, hmS, hxm⟩ := hmem
        rw [Set.indicator_of_mem hxA]
        calc g x = ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) ''
              Work.Diff.STE.unitCube).indicator g x := (Set.indicator_of_mem hxm g).symm
          _ ≤ ∑ m' ∈ S, ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m') ''
                Work.Diff.STE.unitCube).indicator g x :=
              Finset.single_le_sum
                (f := fun m' => ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m') ''
                  Work.Diff.STE.unitCube).indicator g x)
                (fun _ _ => zero_le) hmS
      · rw [Set.indicator_of_notMem hxA]
        exact Finset.sum_nonneg fun m _ => by simp
    rw [← MeasureTheory.lintegral_indicator hAmeas g]
    calc ∫⁻ x, A.indicator g x ≤ ∫⁻ x, ∑ m ∈ S,
          ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube).indicator g x :=
          lintegral_mono hpt
      _ = ∑ m ∈ S, ∫⁻ x,
          ((fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube).indicator g x :=
          lintegral_finsetSum S (fun m _ =>
            hgmeas.indicator (hcellmeas m))
      _ = ∑ m ∈ S,
          ∫⁻ x in (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube, g x := by
          refine Finset.sum_congr rfl fun m _ => ?_
          exact MeasureTheory.lintegral_indicator (hcellmeas m) g
  -- each cell integral is the integral over the fundamental cube
  have hmain : ∫⁻ x in A, g x ≤ (S.card : ℝ≥0∞) * ∫⁻ x in Work.Diff.STE.unitCube, g x := by
    refine hsub.trans ?_
    have hsum : ∑ m ∈ S,
          ∫⁻ x in (fun y : ι → ℝ => y + Work.Diff.STE.iVec m) '' Work.Diff.STE.unitCube, g x
        = ∑ m ∈ S, ∫⁻ x in Work.Diff.STE.unitCube, g x := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [setLIntegral_image_add_eq g hgmeas m]
      exact setLIntegral_congr_fun hcube (fun x _ => hgper m x)
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
  -- a uniform bound for `f` on the cube, and the finiteness of its `lintegral`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ Work.Diff.STE.unitCube (ι := ι), f x ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      hfcont.continuousOn
    refine ⟨C, fun x hx => ?_⟩
    have hxc : x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
      intro i _
      have hi := Set.mem_pi.mp hx i (Set.mem_univ i)
      rw [Set.mem_Ioc] at hi
      exact ⟨le_of_lt hi.1, hi.2⟩
    calc f x ≤ |f x| := le_abs_self _
      _ = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ C := hC x hxc
  have hfin : ∫⁻ x in Work.Diff.STE.unitCube, g x ≠ ⊤ := by
    have h1 : ∫⁻ x in Work.Diff.STE.unitCube, g x ≤ ENNReal.ofReal C := by
      calc ∫⁻ x in Work.Diff.STE.unitCube, g x
          ≤ ∫⁻ x in Work.Diff.STE.unitCube, ENNReal.ofReal C :=
            setLIntegral_mono' hcube (fun x hx => ENNReal.ofReal_le_ofReal (hC x hx))
        _ = ENNReal.ofReal C * (volume : Measure (ι → ℝ)) (Work.Diff.STE.unitCube) :=
            setLIntegral_const _ _
        _ = ENNReal.ofReal C := by rw [BesselCont.vol_unitCube, mul_one]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  -- the cardinality of the index set
  have hcard : (S.card : ℝ) = (2 * (N : ℝ) + 2) ^ Fintype.card ι := by
    have h2 : (Finset.Icc (-(N : ℤ) - 1) (N : ℤ)).card = 2 * N + 2 := by
      rw [Int.card_Icc]
      have hz : (N : ℤ) + 1 - (-(N : ℤ) - 1) = 2 * (N : ℤ) + 2 := by ring
      rw [hz]
      omega
    have h3 : S.card = (2 * N + 2) ^ Fintype.card ι := by
      rw [hS, Fintype.card_piFinset]
      simp only [h2, Finset.prod_const, Finset.card_univ]
    rw [h3]
    push_cast
    ring
  -- the two integrals as `toReal` of their `lintegral`s
  have hAle : ∫ x in A, f x = (∫⁻ x in A, g x).toReal := by
    rw [hgdef]
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfnn)
      (hfcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  have hcubeInt : ∫ x in Work.Diff.STE.unitCube, f x
      = (∫⁻ x in Work.Diff.STE.unitCube, g x).toReal := by
    rw [hgdef]
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfnn)
      (hfcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  calc ∫ x in A, f x = (∫⁻ x in A, g x).toReal := hAle
    _ ≤ ((S.card : ℝ≥0∞) * ∫⁻ x in Work.Diff.STE.unitCube, g x).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top S.card) hfin) hmain
    _ = (S.card : ℝ) * (∫⁻ x in Work.Diff.STE.unitCube, g x).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ = (S.card : ℝ) * ∫ x in Work.Diff.STE.unitCube, f x := by rw [hcubeInt]
    _ = (2 * (N : ℝ) + 2) ^ Fintype.card ι * ∫ x in Work.Diff.STE.unitCube, f x := by rw [hcard]

/-! ## The main theorem -/

theorem integralCompPeriodicLe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (K : Set (ι → ℝ)) (hK : IsCompact K) (hKinj : Set.InjOn T K)
    (hdet : ∀ z ∈ K, (fderiv ℝ T z).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : (ι → ℝ) → ℂ), Continuous v → Work.Diff.STE.Periodic1 v →
      ∫ z in K, ‖v (T z)‖ ^ 2 ≤ C * ∫ x in Work.Diff.STE.unitCube, ‖v x‖ ^ 2 := by
  classical
  have hTcont : Continuous T := hT.continuous
  have hTdiff : Differentiable ℝ T := hT.differentiable (by simp)
  by_cases hKne : K.Nonempty
  · -- a positive lower bound for `|det (fderiv T)|` on `K`
    have hcont_det : Continuous fun z : ι → ℝ => (fderiv ℝ T z).det :=
      ContinuousLinearMap.continuous_det.comp (hT.continuous_fderiv (by simp))
    obtain ⟨c, hcpos, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ |(fderiv ℝ T z).det| := by
      obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hKne (hcont_det.abs.continuousOn)
      exact ⟨|(fderiv ℝ T z₀).det|, abs_pos.mpr (hdet z₀ hz₀K), fun z hz => hmin hz⟩
    -- a coordinate bound for the compact set `T '' K`
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ y ∈ T '' K, ∀ i : ι, |y i| ≤ (N : ℝ) := by
      obtain ⟨r, hsub⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)).mp
        (hK.image hTcont).isBounded
      obtain ⟨N, hNr⟩ := exists_nat_ge r
      refine ⟨N, fun y hy i => ?_⟩
      have h1 : ‖y‖ ≤ r := by
        have h2 : dist y (0 : ι → ℝ) ≤ r := Metric.mem_closedBall.mp (hsub hy)
        simpa [dist_eq_norm] using h2
      calc |y i| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
        _ ≤ r := h1
        _ ≤ (N : ℝ) := hNr
    refine ⟨(1 / c) * (2 * (N : ℝ) + 2) ^ Fintype.card ι, ?_, ?_⟩
    · have : (0 : ℝ) < 2 * (N : ℝ) + 2 := by positivity
      positivity
    · intro v hv hvp
      haveI : (volume : Measure (ι → ℝ)).IsAddHaarMeasure :=
        MeasureTheory.isAddHaarMeasure_volume_pi ι
      set g : (ι → ℝ) → ℝ := fun y => ‖v y‖ ^ 2 with hgdef
      have hgnn : ∀ y, 0 ≤ g y := fun y => by positivity
      have hgcont : Continuous g := hv.norm.pow 2
      have hgper : Work.Diff.STE.Periodic1 g := fun i x => by
        simp only [hgdef]; rw [hvp i x]
      -- the change of variables formula
      have hderiv : ∀ z ∈ K, HasFDerivWithinAt T (fderiv ℝ T z) K z :=
        fun z _ => (hTdiff.differentiableAt (x := z)).hasFDerivAt.hasFDerivWithinAt
      have hcov : ∫ y in T '' K, g y = ∫ z in K, |(fderiv ℝ T z).det| * g (T z) := by
        rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (volume) hK.measurableSet
          hderiv hKinj g]
        simp only [smul_eq_mul]
      -- step 1: the pull back of the integral over `K`
      have hstep1 : ∫ z in K, g (T z) ≤ (1 / c) * ∫ y in T '' K, g y := by
        have hint1 : IntegrableOn (fun z : ι → ℝ => c * g (T z)) K :=
          ContinuousOn.integrableOn_compact hK
            ((continuous_const.mul (hgcont.comp hTcont)).continuousOn)
        have hint2 : IntegrableOn (fun z : ι → ℝ => |(fderiv ℝ T z).det| * g (T z)) K :=
          ContinuousOn.integrableOn_compact hK
            ((hcont_det.abs.mul (hgcont.comp hTcont)).continuousOn)
        have hmono : ∫ z in K, c * g (T z) ≤ ∫ z in K, |(fderiv ℝ T z).det| * g (T z) := by
          refine MeasureTheory.setIntegral_mono_ae_restrict hint1 hint2 ?_
          refine (MeasureTheory.ae_restrict_mem hK.measurableSet).mono fun z hz => ?_
          exact mul_le_mul_of_nonneg_right (hcle z hz) (hgnn (T z))
        rw [MeasureTheory.integral_const_mul] at hmono
        rw [← hcov] at hmono
        have h := (le_div_iff₀' hcpos).mpr hmono
        simpa [div_eq_inv_mul, one_div] using h
      -- step 2: the periodic bound over `T '' K`
      have hstep2 : ∫ y in T '' K, g y ≤ (2 * (N : ℝ) + 2) ^ Fintype.card ι *
          ∫ x in Work.Diff.STE.unitCube, g x :=
        periodicIntegralLeCube_local g hgnn hgcont hgper (T '' K)
          (hK.image hTcont).measurableSet N hN
      calc ∫ z in K, ‖v (T z)‖ ^ 2 = ∫ z in K, g (T z) := by rw [hgdef]
        _ ≤ (1 / c) * ∫ y in T '' K, g y := hstep1
        _ ≤ (1 / c) * ((2 * (N : ℝ) + 2) ^ Fintype.card ι *
              ∫ x in Work.Diff.STE.unitCube, g x) :=
              mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = ((1 / c) * (2 * (N : ℝ) + 2) ^ Fintype.card ι) *
              ∫ x in Work.Diff.STE.unitCube, g x := by ring
        _ = ((1 / c) * (2 * (N : ℝ) + 2) ^ Fintype.card ι) *
              ∫ x in Work.Diff.STE.unitCube, ‖v x‖ ^ 2 := by rw [hgdef]
  · rw [Set.not_nonempty_iff_eq_empty.mp hKne]
    exact ⟨0, le_refl 0, fun v hv hvp => by rw [setIntegral_empty, zero_mul]⟩

end Work.Diff.STE.B3
