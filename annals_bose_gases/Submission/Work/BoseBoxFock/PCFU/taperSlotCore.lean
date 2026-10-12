import Mathlib
import Submission.Work.BoseBoxFock.PCFU.taperAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.taperSlot_core`

The core estimate of the taper piece of the `(A)`-channel alias slot.

Setting: `ℓ > 0`, `κ > 0`, a slot pair `i ≠ j` in `Fin (n+1)`, a smooth state `Φ : X (n+1) → ℝ`,
the slot-`j` low-momentum fibre
`Γ = lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Φ))`, and a kernel `T : E3 → ℂ` whose windowed `y`-pairings
obey the single-slice bound `hTb` (that is `Work.BoseBoxFock.PCFU.taperSlotOne`).  Then

  `‖∫_{abox (n+1) ℓ} Φ·χ(x i)·χ(x j)·T(x j − x i)·Γ‖`
    `≤ CA·√chiSup·(1+R)³·√(ℓ³/Λ)·√D·√(∫_{abox} Φ²)`,

where `D` bounds the peeled Dirichlet integral of the `i`-slot.

The proof is: peel the slot `i` (`abox_integral_peelC`), apply the single-slice bound slicewise
(`hTb`), Cauchy–Schwarz in the peeled configuration `r`, and the `L²`-contraction
`∫ Γ² ≤ ℓ^{-3}∫ Φ²`.

Everything below is `sorry`-free.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The norm of the real embedding of a real number into `ℂ`. -/
lemma norm_complex_ofReal (z : ℝ) : ‖((z : ℝ) : ℂ)‖ = ‖z‖ := by
  rw [Real.norm_eq_abs]
  exact RCLike.norm_ofReal z

/-- The square root of an `L²` nonnegative function is `L²`. -/
lemma memLp_sqrt_of_memLp_two {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : MemLp g 2 μ) (hg0 : 0 ≤ᵐ[μ] g) :
    MemLp (fun a => Real.sqrt (g a)) 2 μ := by
  have haesm : AEStronglyMeasurable (fun a => Real.sqrt (g a)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm haesm]
  exact (hg.integrable one_le_two).congr (hg0.mono fun a ha => by
    show g a = ‖Real.sqrt (g a)‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha])

theorem taperSlot_core {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) {ℓ κ : ℝ} (hℓ : 0 < ℓ)
    (hκ : 0 < κ) (fc : Work.BoseBoxFix.LowCut)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {T : E3 → ℂ} {Λ CA R D DΓ E : ℝ} (hCA0 : 0 ≤ CA) (hΛ0 : 0 < Λ) (hR0 : 0 ≤ R)
    (hDΓ0 : 0 ≤ DΓ) (hE0 : 0 ≤ E)
    (hTb : ∀ (y : E3) (g : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ →
      ‖∫ w : E3, ((g w : ℝ) : ℂ) * T (y - w)‖
        ≤ CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹ * ∫ x : E3, ∑ k : Fin 3,
            ‖fderiv ℝ g x (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
    (hΓm : Measurable (fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
      (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x))
    (hΓb : ∀ x, |Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
      (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x| ≤ DΓ)
    (hΓeq : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x
      = Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
          (Submission.BoseGases.aP ℓ i Φ)) x)
    (hDirm : AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
        ∫ y : E3, ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
          Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
    (hDirb : ∀ r ∈ Submission.BoseGases.abox n ℓ,
      (∫ y : E3, ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ E)
    (hDirInt : (∫ r in Submission.BoseGases.abox n ℓ,
        (∫ y : E3, ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
          Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)) ≤ D) :
    ‖∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        ((Φ x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ) * T (x j - x i)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
              (Submission.BoseGases.aP ℓ i Φ)) x : ℝ) : ℂ)‖
      ≤ CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt (ℓ ^ 3 / Λ)
          * Real.sqrt D
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ, (Φ x) ^ 2) := by
  classical
  -- ### abbreviations
  set ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)
    with hνdef
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hνdef, MeasureTheory.Measure.restrict_apply_univ]
    exact (Work.UBBInputs9.B.abox_isCompact n ℓ).measure_lt_top⟩
  let χ : E3 → ℝ := Submission.BoseGases.chiScale ℓ
  let ΓΦ : Submission.BoseGases.X (n + 1) → ℝ := fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ)) x
  let ΓΘ : Submission.BoseGases.X (n + 1) → ℝ := fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x
  let Dir : Submission.BoseGases.X n → ℝ := fun r => ∫ y : E3, ∑ k : Fin 3,
      ‖fderiv ℝ (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
  let F : Submission.BoseGases.X (n + 1) → ℂ := fun x => ((Φ x : ℝ) : ℂ)
      * ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ) * T (x j - x i)
      * ((ΓΦ x : ℝ) : ℂ)
  let Γr : Submission.BoseGases.X n → ℝ :=
    fun r => ΓΦ (Submission.BoseGases.kcInsN n i (0, r))
  let ff : Submission.BoseGases.X n → ℝ :=
    fun r => χ ((Submission.BoseGases.kcInsN n i (0, r)) j)
      * ΓΦ (Submission.BoseGases.kcInsN n i (0, r))
  let I : ℝ := ∫ x in Submission.BoseGases.abox (n + 1) ℓ, (Φ x) ^ 2
  -- ### the hypotheses, in the abbreviations
  have hΓm' : Measurable ΓΘ := hΓm
  have hΓb' : ∀ x, |ΓΘ x| ≤ DΓ := hΓb
  have hΓeq' : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, ΓΘ x = ΓΦ x := hΓeq
  have hDirb' : ∀ r ∈ Submission.BoseGases.abox n ℓ, Dir r ≤ E := hDirb
  have hDirm' : AEStronglyMeasurable Dir ν := hDirm
  have hDirLe : (∫ r, Dir r ∂ν) ≤ D := hDirInt
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) χ := Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)
  -- ### `χ` vanishes outside the box
  have hχ0 : ∀ {y : E3}, y ∉ Work.BoseK15.corpusBox.boxL ℓ → χ y = 0 := by
    intro y hy
    exact (Function.notMem_support (f := Work.BoseK15.corpusBox.chiLam ℓ)).mp
      (fun hmem => hy (Work.BoseK15.corpusBox.chiLam_supp hℓ hmem))
  have hmem0 : (0 : E3) ∈ Submission.BoseGases.acube ℓ := by
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have h0 : (((0 : E3).ofLp m : ℝ)) = 0 := by simp
    rw [h0, Set.mem_Icc]
    exact ⟨by linarith [hℓ.le], by linarith [hℓ.le]⟩
  have hΓconst : ∀ x (z : E3), ΓΦ (Function.update x i z) = ΓΦ x :=
    fun x z => lowSlot_aQ_aP_const_in_coord i j hij fc κ ℓ Φ x z
  have hΓΦv : ∀ r ∈ Submission.BoseGases.abox n ℓ,
      ΓΦ (Submission.BoseGases.kcInsN n i (0, r))
        = ΓΘ (Submission.BoseGases.kcInsN n i (0, r)) :=
    fun r hr => (hΓeq' _ (kcInsN_mem_abox i hr hmem0)).symm
  have hΓΦm : AEStronglyMeasurable Γr ν :=
    ((hΓm'.comp ((Submission.BoseGases.kcInsN n i).measurable.comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
        with r hr
      exact (hΓΦv r hr).symm)
  have hχqm : AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n => χ ((Submission.BoseGases.kcInsN n i (0, r)) j)) ν :=
    (hχcd.continuous.measurable.comp ((measurable_pi_apply j).comp
      ((Submission.BoseGases.kcInsN n i).measurable.comp
        (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
  -- ### the `L²` bounds of the slices
  have hfL2 : MemLp ff 2 ν := by
    refine MemLp.of_bound (hχqm.mul hΓΦm) (Submission.BoseGases.chiSup * DΓ) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
      with r hr
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (Submission.BoseGases.abs_chiScale_le_chiSup ℓ _) ?_ (abs_nonneg _)
      Submission.BoseGases.chiSup_pos.le
    rw [hΓΦv r hr]
    exact hΓb' _
  have hΓrL2 : MemLp Γr 2 ν := by
    refine MemLp.of_bound hΓΦm DΓ ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
      with r hr
    rw [Real.norm_eq_abs]
    show |ΓΦ (Submission.BoseGases.kcInsN n i (0, r))| ≤ DΓ
    rw [hΓΦv r hr]
    exact hΓb' _
  have hDirL2 : MemLp Dir 2 ν := by
    refine MemLp.of_bound hDirm' E ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
      with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (MeasureTheory.integral_nonneg
      (fun y => Finset.sum_nonneg (fun k _ => sq_nonneg _)))]
    exact hDirb' r hr
  have hDirnn : 0 ≤ᵐ[ν] Dir := by
    filter_upwards with r
    exact MeasureTheory.integral_nonneg (fun y => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  -- ### the Cauchy–Schwarz pair is `L¹`
  have hprod : Integrable (fun r : Submission.BoseGases.X n => ‖ff r‖ * Real.sqrt (Dir r)) ν :=
    hfL2.norm.integrable_mul (memLp_sqrt_of_memLp_two hDirL2 hDirnn)
  -- ### step 1: peel and dominate by the integral of the majorant
  have hstep : ‖∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x‖
      ≤ (CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹))
        * (∫ r, ‖ff r‖ * Real.sqrt (Dir r) ∂ν) := by
    by_cases hInt : IntegrableOn F (Submission.BoseGases.abox (n + 1) ℓ) volume
    · have hpeel := abox_integral_peelC i F hInt
      -- the slice identity: `F (kcInsN (y,r)) = (χ_r Γ_r) · (χ y · Φ · T)`
      have hslice : ∀ r ∈ Submission.BoseGases.abox n ℓ,
          (∫ y : E3 in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN n i (y, r)))
            = ((χ ((Submission.BoseGases.kcInsN n i (0, r)) j)
                * ΓΦ (Submission.BoseGases.kcInsN n i (0, r)) : ℝ) : ℂ)
              * (∫ y : E3 in Submission.BoseGases.acube ℓ, ((χ y : ℝ) : ℂ)
                  * ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
                  * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y)) := by
        intro r hr
        have hpt : ∀ y : E3, F (Submission.BoseGases.kcInsN n i (y, r))
            = ((χ ((Submission.BoseGases.kcInsN n i (0, r)) j)
                * ΓΦ (Submission.BoseGases.kcInsN n i (0, r)) : ℝ) : ℂ)
                * (((χ y : ℝ) : ℂ) * ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
                    * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y)) := by
          intro y
          have hxi : (Submission.BoseGases.kcInsN n i (y, r)) i = y :=
            Submission.BoseGases.kc_insN_apply_same n i y r
          have hxj : (Submission.BoseGases.kcInsN n i (y, r)) j
              = (Submission.BoseGases.kcInsN n i (0, r)) j :=
            Submission.BoseGases.kc_insN_other_indep n i y 0 r j hij.symm
          have hΓ : ΓΦ (Submission.BoseGases.kcInsN n i (y, r))
              = ΓΦ (Submission.BoseGases.kcInsN n i (0, r)) := by
            rw [kcInsN_eq_update i r y]
            exact hΓconst (Submission.BoseGases.kcInsN n i (0, r)) y
          show ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
              * ((χ ((Submission.BoseGases.kcInsN n i (y, r)) i) : ℝ) : ℂ)
              * ((χ ((Submission.BoseGases.kcInsN n i (y, r)) j) : ℝ) : ℂ)
              * T ((Submission.BoseGases.kcInsN n i (y, r)) j
                  - (Submission.BoseGases.kcInsN n i (y, r)) i)
              * ((ΓΦ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ) = _
          rw [hxi, hxj, hΓ]
          push_cast
          ring
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
          MeasureTheory.integral_const_mul]
      -- the single-slice bound, converted to the cube integral
      have hB : ∀ r ∈ Submission.BoseGases.abox n ℓ,
          ‖∫ y : E3 in Submission.BoseGases.acube ℓ, ((χ y : ℝ) : ℂ)
              * ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
              * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y)‖
            ≤ CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹ * Dir r) := by
        intro r hr
        have hfun : (fun y : E3 => χ y * Φ (Submission.BoseGases.kcInsN n i (y, r)))
            = fun y : E3 => χ y * Φ
                (Function.update (Submission.BoseGases.kcInsN n i (0, r)) i y) := by
          funext y
          rw [kcInsN_eq_update]
        have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 =>
            χ y * Φ (Submission.BoseGases.kcInsN n i (y, r))) := by
          rw [hfun]
          exact hχcd.mul (hΦ.comp (contDiff_update (⊤ : ℕ∞)
            (Submission.BoseGases.kcInsN n i (0, r)) i))
        have hsupp : tsupport (fun y : E3 =>
            χ y * Φ (Submission.BoseGases.kcInsN n i (y, r)))
            ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
          show closure (Function.support (fun y : E3 =>
            χ y * Φ (Submission.BoseGases.kcInsN n i (y, r)))) ⊆ Work.BoseK15.corpusBox.boxL ℓ
          refine closure_minimal (fun y hy => ?_)
            (Work.BoseK15.corpusBox.boxL_compact ℓ).isClosed
          by_contra hc
          refine hy ?_
          show χ y * Φ (Submission.BoseGases.kcInsN n i (y, r)) = 0
          rw [hχ0 hc, zero_mul]
        have h1 := hTb ((Submission.BoseGases.kcInsN n i (0, r)) j)
          (fun y : E3 => χ y * Φ (Submission.BoseGases.kcInsN n i (y, r))) hcd hsupp
        have hzer : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
            ((χ y : ℝ) : ℂ) * ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
              * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y) = 0 := by
          intro y hy
          have hy' : y ∉ Work.BoseK15.corpusBox.boxL ℓ := by
            intro hmem
            refine hy ?_
            rw [Submission.BoseGases.mem_acube_iff]
            intro m
            have h2 := Work.BoseFixR.mem_cell.mp (by
              rw [← Work.BoseBoxFock.corpusBox_boxL_eq_cell hℓ]; exact hmem) m
            exact ⟨by simpa only [neg_div] using (abs_le.mp h2).1, (abs_le.mp h2).2⟩
          rw [hχ0 hy']
          simp
        have hDirEq : (∫ x : E3, ∑ k : Fin 3,
              ‖fderiv ℝ (fun y : E3 => χ y * Φ (Submission.BoseGases.kcInsN n i (y, r))) x
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) = Dir r := rfl
        calc ‖∫ y : E3 in Submission.BoseGases.acube ℓ, ((χ y : ℝ) : ℂ)
              * ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
              * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y)‖
            = ‖∫ y : E3, ((χ y * Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
                * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y)‖ := by
              rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzer]
              congr 1
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              rw [Complex.ofReal_mul]
              try ring
          _ ≤ CA * (1 + R) ^ 3 * ℓ ^ 3
                * Real.sqrt (Λ⁻¹ * ∫ x : E3, ∑ k : Fin 3,
                  ‖fderiv ℝ (fun y : E3 => χ y * Φ (Submission.BoseGases.kcInsN n i (y, r))) x
                    (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) := h1
          _ = CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹ * Dir r) := by rw [hDirEq]
      -- the pointwise bound of the peeled integrand
      have hkey0 : ‖∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x‖
          ≤ (CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹))
            * (∫ r, ‖ff r‖ * Real.sqrt (Dir r) ∂ν) := by
        rw [hpeel]
        refine le_trans (MeasureTheory.norm_integral_le_integral_norm
          (fun r : Submission.BoseGases.X n =>
            ∫ y : E3 in Submission.BoseGases.acube ℓ,
              F (Submission.BoseGases.kcInsN n i (y, r)))) ?_
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun r => norm_nonneg _)
          (hprod.const_mul _) ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict
          (Submission.BoseGases.abox_measurable n ℓ)] with r hr
        have hse := hslice r hr
        rw [hse, norm_mul, norm_complex_ofReal]
        have hb := hB r hr
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Λ⁻¹) (Dir r)] at hb
        calc ‖ff r‖ * ‖∫ y : E3 in Submission.BoseGases.acube ℓ, ((χ y : ℝ) : ℂ)
              * ((Φ (Submission.BoseGases.kcInsN n i (y, r)) : ℝ) : ℂ)
              * T ((Submission.BoseGases.kcInsN n i (0, r)) j - y)‖
            ≤ ‖ff r‖ * (CA * (1 + R) ^ 3 * ℓ ^ 3 * (Real.sqrt (Λ⁻¹) * Real.sqrt (Dir r))) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹)
                * (‖ff r‖ * Real.sqrt (Dir r)) := by ring
      exact hkey0
    · have h0 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x) = 0 :=
        MeasureTheory.integral_undef hInt
      rw [h0, norm_zero]
      refine mul_nonneg ?_ (MeasureTheory.integral_nonneg fun r => mul_nonneg
        (norm_nonneg _) (Real.sqrt_nonneg _))
      exact mul_nonneg (mul_nonneg (mul_nonneg hCA0
        (pow_nonneg (by linarith : (0:ℝ) ≤ 1 + R) 3)) (pow_nonneg hℓ.le 3))
        (Real.sqrt_nonneg _)
  -- ### step 2: Cauchy–Schwarz in `r`
  have hCS := cs_sqrt_bound (μ := ν) (f := ff) (g := Dir) hfL2 hDirL2 hDirnn
  have hsq_le : (∫ r, (ff r) ^ 2 ∂ν) ≤ Submission.BoseGases.chiSup ^ 2 * (∫ r, (Γr r) ^ 2 ∂ν) := by
    have hIntg : Integrable (fun r : Submission.BoseGases.X n =>
        Submission.BoseGases.chiSup ^ 2 * (Γr r) ^ 2) ν := by
      have h1 : Integrable (fun r : Submission.BoseGases.X n =>
          Submission.BoseGases.chiSup ^ 2 * ‖Γr r‖ ^ 2) ν :=
        (((MeasureTheory.memLp_two_iff_integrable_sq_norm hΓΦm).mp hΓrL2)).const_mul _
      refine h1.congr (Filter.Eventually.of_forall fun r => ?_)
      show Submission.BoseGases.chiSup ^ 2 * ‖Γr r‖ ^ 2
          = Submission.BoseGases.chiSup ^ 2 * (Γr r) ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    have hpt : ∀ r : Submission.BoseGases.X n,
        (ff r) ^ 2 ≤ Submission.BoseGases.chiSup ^ 2 * (Γr r) ^ 2 := by
      intro r
      have hχb : |χ ((Submission.BoseGases.kcInsN n i (0, r)) j)|
          ≤ Submission.BoseGases.chiSup :=
        Submission.BoseGases.abs_chiScale_le_chiSup ℓ _
      have h2 : (χ ((Submission.BoseGases.kcInsN n i (0, r)) j)) ^ 2
          ≤ Submission.BoseGases.chiSup ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hχb 2
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
      show (χ ((Submission.BoseGases.kcInsN n i (0, r)) j) * Γr r) ^ 2
          = χ ((Submission.BoseGases.kcInsN n i (0, r)) j) ^ 2 * (Γr r) ^ 2
      rw [mul_pow]
    exact le_trans (MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun r => sq_nonneg _)
      hIntg (Filter.Eventually.of_forall hpt)) (le_of_eq (MeasureTheory.integral_const_mul _ _))
  have hkey : (∫ r, ‖ff r‖ * Real.sqrt (Dir r) ∂ν)
      ≤ Submission.BoseGases.chiSup * Real.sqrt (∫ r, (Γr r) ^ 2 ∂ν) * Real.sqrt D := by
    refine le_trans hCS (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) ?_)
    · refine le_trans (Real.sqrt_le_sqrt hsq_le) ?_
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq Submission.BoseGases.chiSup_pos.le]
    · exact Real.sqrt_le_sqrt hDirLe
    · exact mul_nonneg (le_of_lt Submission.BoseGases.chiSup_pos) (Real.sqrt_nonneg _)
  -- ### step 3: the `Γ`-`L²` bound
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hΓsq : (∫ r, (Γr r) ^ 2 ∂ν) ≤ I / ℓ ^ 3 := by
    have hpeelΓ := lowSlot_boxRestrict_sq_peel (n := n) i j hij fc hℓ hDΓ0 hΓm' hΓb'
    have hΓΘsq_eq : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, (ΓΘ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, (ΓΦ x) ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable (n + 1) ℓ)] with x hx
      rw [hΓeq' x hx]
    have hΓΦr_eq : (∫ r, (ΓΘ (Submission.BoseGases.kcInsN n i (0, r))) ^ 2 ∂ν)
        = ∫ r, (ΓΦ (Submission.BoseGases.kcInsN n i (0, r))) ^ 2 ∂ν := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable n ℓ)] with r hr
      rw [hΓeq' _ (kcInsN_mem_abox i hr hmem0)]
    have hΓ_le : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, (ΓΦ x) ^ 2) ≤ I :=
      lowSlot_aQ_aP_sq_le_cont fc i j hℓ hκ hΦ.continuous
    have heq : (∫ r, (Γr r) ^ 2 ∂ν) = (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (ΓΦ x) ^ 2) / ℓ ^ 3 := by
      rw [eq_div_iff (by positivity : (ℓ : ℝ) ^ 3 ≠ 0)]
      show (∫ r, (Γr r) ^ 2 ∂ν) * ℓ ^ 3 = _
      rw [mul_comm]
      show ℓ ^ 3 * (∫ r, (ΓΦ (Submission.BoseGases.kcInsN n i (0, r))) ^ 2 ∂ν) = _
      rw [← hΓΦr_eq, ← hpeelΓ, hΓΘsq_eq]
    rw [heq]
    exact div_le_div_of_nonneg_right hΓ_le (by positivity)
  -- ### assembly
  have hc0 : 0 ≤ CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCA0 (pow_nonneg (by linarith : (0:ℝ) ≤ 1 + R) 3))
      (pow_nonneg hℓ.le 3)) (Real.sqrt_nonneg _)
  have hId : (CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹))
        * (Submission.BoseGases.chiSup * (Real.sqrt I / Real.sqrt (ℓ ^ 3)) * Real.sqrt D)
      = CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt (ℓ ^ 3 / Λ)
        * Real.sqrt D * Real.sqrt I := by
    rw [sqrt_div_eq_aux hℓ hΛ0]
    have h3 : Real.sqrt (ℓ ^ 3) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < ℓ ^ 3)).ne'
    field_simp
    try ring
  have hsqrtΓ : Real.sqrt (∫ r, (Γr r) ^ 2 ∂ν) ≤ Real.sqrt I / Real.sqrt (ℓ ^ 3) := by
    refine le_trans (Real.sqrt_le_sqrt hΓsq) ?_
    rw [Real.sqrt_div hI0]
  have hstep2 : (CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹))
        * (∫ r, ‖ff r‖ * Real.sqrt (Dir r) ∂ν)
      ≤ CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt (ℓ ^ 3 / Λ)
          * Real.sqrt D * Real.sqrt I := by
    refine le_trans (mul_le_mul_of_nonneg_left hkey hc0) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtΓ
        (le_of_lt Submission.BoseGases.chiSup_pos)) (Real.sqrt_nonneg D)) hc0) ?_
    exact le_of_eq hId
  calc ‖∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x‖
      ≤ (CA * (1 + R) ^ 3 * ℓ ^ 3 * Real.sqrt (Λ⁻¹))
          * (∫ r, ‖ff r‖ * Real.sqrt (Dir r) ∂ν) := hstep
    _ ≤ CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt (ℓ ^ 3 / Λ)
          * Real.sqrt D * Real.sqrt I := hstep2

end Work.BoseBoxFock.PCFU
