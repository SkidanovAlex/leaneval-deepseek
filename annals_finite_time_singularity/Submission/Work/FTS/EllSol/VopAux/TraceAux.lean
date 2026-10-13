import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenIntegrability
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW
import Submission.Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW
import Submission.Work.FTS.EllSol.VopAux.sliceW_pthIter2_eq_sliceW_sliceV

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Auxiliary lemmas for the angular Poincaré estimate in the weak (trace) class

Slices of `C^∞`-on-the-open-quadrant data at a fixed `z > 0`, Clairaut for `∂_θ²` and `D_z^j`
on the open quadrant, the congruence of `D_θ`-iterates of functions agreeing on the open
interval, the a.e. strong measurability of the `z`-integral of the `ℋ^k`-integrand, and the
integrability of the individual summands of the `j`-th slice group of `∂_θ² f`.
-/

/-- `Real.sqrt x ≤ max 1 x`. -/
lemma sqrt_le_max_one (x : ℝ) : Real.sqrt x ≤ max 1 x := by
  have h1 : 0 ≤ max 1 x := le_trans zero_le_one (le_max_left _ _)
  have h2 : x ≤ (max 1 x) ^ 2 := by
    calc x ≤ max 1 x := le_max_right _ _
      _ ≤ (max 1 x) * (max 1 x) := le_mul_of_one_le_left h1 (le_max_left _ _)
      _ = (max 1 x) ^ 2 := by ring
  calc Real.sqrt x ≤ Real.sqrt ((max 1 x) ^ 2) := Real.sqrt_le_sqrt h2
    _ = max 1 x := Real.sqrt_sq h1

/-- The angular weight `thEta` is continuous on the open interval. -/
lemma continuousOn_thEta : ContinuousOn Work.FTS.EllipticEst.thEta
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `thGam α` is continuous on the open interval. -/
lemma continuousOn_thGam (α : ℝ) : ContinuousOn (Work.FTS.EllipticEst.thGam α)
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The `θ`-slices of a function `C^∞` on the open quadrant are `C^∞` on the open interval. -/
lemma contDiffOn_slice_of_smoothOpen {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z : ℝ} (hz : 0 < z) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ => g z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  fun n => contDiffOn_iff_forall_nat_le.mp (hg.curry_θ hz) n le_top

/-- **Clairaut for `∂_θ²` and `D_z^j` on the open quadrant**: the second angular derivative of
the slice `θ' ↦ D_z^j f z θ'` is the `j`-th slice of `∂_θ²f`. -/
lemma sliceV_DzIter_openQ {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have h1 : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.DzIter j f) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ' :=
    fun θ' hθ' => Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hf.forall j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
  have h2 : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.pth f)) z θ' :=
    fun θ' hθ' => Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hf.pth.forall j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
  have h3 : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
  rw [h3]
  have e1 : Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ := rfl
  rw [e1]
  have hev1 : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h1 θ' hθ'
  rw [hev1.deriv_eq]
  have e2 : deriv (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [e2]
  exact h2 θ hθ

/-- The `D_θ`-iterates of two functions agreeing at every interior angle agree there. -/
lemma LopIter_congr_Ioo {u v : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = v θ) :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.LopIter i u θ = Work.FTS.EllipticEst.LopIter i v θ := by
  intro i
  induction i with
  | zero => intro θ hθ; exact h θ hθ
  | succ i ih =>
      intro θ hθ
      have heq : (fun θ' => Work.FTS.EllipticEst.LopIter i u θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.FTS.EllipticEst.LopIter i v θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ'
      simp only [Work.FTS.EllipticEst.LopIter_succ, Work.Spaces.Lop]
      rw [heq.deriv_eq]

/-- `L^m` of the second derivative of the `j`-th slice is the mixed derivative
`D_z^j D_θ^m (∂_θ²f)`. -/
lemma LopIter_sliceV_DzIter_eq_mixed_openQ {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (j m : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ := by
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
  have hfun : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ'
        = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ' :=
    fun θ' hθ' => sliceV_DzIter_openQ hf j hz hθ'
  rw [LopIter_congr_Ioo hfun m θ hθ]
  have hslice := Work.FTS.EllipticEst.LopIter_slice m
    (fun z θ => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ) z
  have hval : Work.FTS.EllipticEst.LopIter m
        (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)) z θ :=
    congrFun hslice θ
  rw [hval]
  exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hpth2.forall j m hz hθ

/-- The `θ`-integral of the `ℋ^k`-integrand is a.e. strongly measurable as a function of `z`. -/
lemma aesm_integral_HkIntegrand (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k)
  have h2 := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  simpa using h2

/-- A slice group is integrable on `Iθ` as soon as the whole `ℋ^k`-integrand of the same
function is. -/
lemma integrableOn_sliceGroup_of_HkIntegrand {α : ℝ} {k j : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z : ℝ} (hz : 0 < z) (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k F z θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sliceGroup α k j F z θ)
      Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' hInt ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sliceGroup α k j F p.1 p.2)
      (Work.FTS.EllipticEst.continuousOn_sliceGroup_Q0 hF α k j) hz
  · exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_of_nonneg (Work.FTS.EllipticEst.sliceGroup_nonneg α k j F z θ)]
      exact Work.FTS.EllipticEst.sliceGroup_le_HkIntegrand α k j F z θ
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- Integrability of the `η`-weighted square of the second derivative of the `j`-th slice. -/
lemma integrableOn_sliceV_thEta {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : 0 < z) {j : ℕ} (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
  refine MeasureTheory.Integrable.mono'
    (hInt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
  · -- a.e. strong measurability: continuity of the slice data on the open interval
    have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.DzIter j f z θ')
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hf.DzIter j).curry_θ hz
    have hd1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hd2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hd1.deriv_of_isOpen isOpen_Ioo (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hcont : ContinuousOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hd2.continuousOn.pow 2).mul continuousOn_thEta
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hval := sliceV_DzIter_openQ hf j hz hθ
    have hw := Work.FTS.EllipticEst.w_div_sin_sq hθI z
    have hsq := Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 f) z θ j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθI)), hval]
    have hkey : (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ
        = ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      rw [mul_pow, hw]; field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg _))

/-- Integrability of the `γ`-weighted squares of the higher angular derivatives of the `j`-th
slice of `∂_θ²f`. -/
lemma integrableOn_sliceV_LopIter {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : 0 < z) {j m : ℕ} (hm : 1 ≤ m)
    (hmj : m + j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
  -- integrability of the corresponding mixed summand
  have hInt2 : MeasureTheory.IntegrableOn (fun θ =>
      (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hInt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · have hcont : ContinuousOn (fun θ =>
          (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ((((hf.pth.pth).mixed j m).continuousOn.comp
            (continuous_const.prodMk continuous_id).continuousOn
            (fun θ hθ => ⟨hz, hθ⟩)).pow 2).mul (continuousOn_thGam α)
      rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
      have hmix := Work.FTS.EllipticEst.mix_term_eq (α := α) hθI z
        (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ)
      have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pthIter 2 f)
        z θ m j hm hmj
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thGam_nonneg hθI))]
      have hkey : (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ
          = ((Work.Spaces.w z) ^ 2)⁻¹
            * ((Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                * Work.Spaces.Wt α z θ) ^ 2) := by
        rw [hmix, Work.FTS.EllipticEst.sGam_eq_thGam α]; field_simp
      rw [hkey]
      exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg _))
  -- transport across the a.e. identification of the two functions
  refine hInt2.congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
  show Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ ^ 2
      * Work.FTS.EllipticEst.thGam α θ
    = Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
      * Work.FTS.EllipticEst.thGam α θ
  rw [LopIter_sliceV_DzIter_eq_mixed_openQ hf j m hz hθ]

/-- Integrability of the slice functional from the integrability of its summands. -/
lemma integrableOn_sliceW_of {K : ℕ} {α : ℝ} {u : ℝ → ℝ}
    (h0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hL : ∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => sliceW K α u θ) Work.Spaces.Iθ := by
  have hsum : MeasureTheory.IntegrableOn (fun θ => ∑ i ∈ Finset.Icc 1 K,
      (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      Work.Spaces.Iθ := MeasureTheory.integrable_finsetSum _ hL
  show MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    + ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
    Work.Spaces.Iθ
  exact h0.add hsum

/-- The `θ`-integral of the `j`-th slice group of `f` is `w(z)²` times the single-slice
functional of the slice `θ' ↦ D_z^j f z θ'`. -/
lemma integral_sliceGroup_eq_sliceF (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ}
    (hz : 0 < z) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ)
      = (Work.Spaces.w z) ^ 2
          * sliceF (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') := by
  rw [sliceF, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
      Work.FTS.EllipticEst.sliceGroup α k j f z θ)
    (v := fun θ => (Work.Spaces.w z) ^ 2
      * sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
    (fun θ hθ => sliceGroup_eq_sliceW α k j f hz hf.forall θ hθ)] with θ hθ
  exact hθ

/-- The same identity for the slice group of `∂_θ² f`, whose single-slice datum is the second
derivative of the `j`-th slice of `f`. -/
lemma integral_sliceGroup_pthIter2_eq_sliceF (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ)
    {z : ℝ} (hz : 0 < z) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => sliceW (k - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
      = (Work.Spaces.w z) ^ 2 * sliceF (k - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
  rw [sliceF, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
  filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
      Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
    (v := fun θ => (Work.Spaces.w z) ^ 2 * sliceW (k - j) α
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
    (fun θ hθ => by
      rw [sliceGroup_eq_sliceW α k j (Work.Spaces.pthIter 2 f) hz hpth2.forall θ hθ,
        sliceW_pthIter2_eq_sliceW_sliceV α (k - j) j f hz hf.forall θ hθ])] with θ hθ
  exact hθ

end Work.FTS.EllSol.VopAux
