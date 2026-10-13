import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Honest.zIBP_compact
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.ibpZ
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace Work.FTS.EllipticEst.H2W.AeW

/-! ## Auxiliary: `bslOp` preserves `C^∞` on the open quadrant -/

private lemma smoothOpen_bslOp {α : ℝ} {v : ℝ → ℝ → ℝ}
    (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α v) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Real.tan θ * v z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hv
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero v) := by
    refine Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hv 2))
        h1.pth)
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hv)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl ?_ ?_) h2
  · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2)
          Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl))
      (hv.pzIter 2)
  · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl)
      hv.pz

/-! ## Auxiliary: `Iz`-integrals of functions supported in a `z`-box -/

private lemma setIntegral_Iz_eq_Icc {f : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hvan : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → f z = 0) :
    ∫ z in Work.Spaces.Iz, f z = ∫ z in Set.Icc ε M, f z := by
  have hsubI : Set.Icc ε M ⊆ Set.Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le hε hx.1
  calc ∫ z in Work.Spaces.Iz, f z = ∫ z in Set.Ioi (0:ℝ), f z := by
        refine MeasureTheory.setIntegral_congr_set ?_
        exact (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    _ = ∫ z in Set.Icc ε M, f z :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubI
          (fun z hz => hvan z hz.1 hz.2)

/-- The same support reduction on `Ioi 0` (which is `Iz` up to the null set `{0}`). -/
private lemma setIntegral_Ioi_eq_Icc {f : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hvan : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → f z = 0) :
    ∫ z in Set.Ioi (0:ℝ), f z = ∫ z in Set.Icc ε M, f z := by
  have h1 : (∫ z in Set.Ioi (0:ℝ), f z) = ∫ z in Work.Spaces.Iz, f z := by
    refine MeasureTheory.setIntegral_congr_set ?_
    exact MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)
  rw [h1]
  exact setIntegral_Iz_eq_Icc hε hεM hvan

/-! ## Auxiliary: box integrability of `F² sin(2θ)^{-η}` from `HkMem α 0 F` -/

private lemma boxInt_HkZero {α : ℝ} {F : ℝ → ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hm : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ : ℝ =>
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) := by
  have ha : (0:ℝ) < ε := hε
  have hab : ε < M := hεM
  have hsub : Set.Icc ε M ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (F p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ((hF.continuousOn).pow 2) ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hnn : ∀ z ∈ Set.Icc ε M, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hsin2 θ hθ) _)
  have hdom : ∀ (z θ : ℝ), 0 < z → θ ∈ Work.Spaces.Iθ →
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ Work.Spaces.HkIntegrand α 0 F z θ := by
    intro z θ hz hθ
    have hw1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
      nlinarith [hz]
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have hs0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := Real.rpow_nonneg (hsin2 θ hθ) _
    have hF0 : 0 ≤ F z θ ^ 2 := sq_nonneg _
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α F z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq F z θ (hsin2 θ hθ)]
    have hs0' : 0 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := hs0
    have hstep : F z θ ^ 2 * 1 ≤ F z θ ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_left hw2 hF0
    have hstep2 := mul_le_mul_of_nonneg_right hstep hs0'
    calc F z θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        = F z θ ^ 2 * 1 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by ring
      _ ≤ F z θ ^ 2 * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
          hstep2
  have hsl : ∀ s ∈ Set.Icc ε M, Integrable (fun θ : ℝ =>
      (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hm.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact hdom s θ hspos hθ
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Icc ε M)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F s θ)
        (volume.restrict (Set.Icc ε M)) := hm.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · have hle : (volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (F p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
          ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hg).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := volume.restrict (Set.Icc ε M))
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only using h2
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet (Set.Icc ε M) from measurableSet_Icc)] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have hsz : s ∈ Work.Spaces.Iz := hsub hs
      have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
            with θ hθ
          exact hnn s hs θ hθ)
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
          with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
          with θ hθ
        exact hdom s θ hspos hθ
  exact Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

/-! ## Auxiliary: domination for box integrability -/

private lemma boxInt_mono {f g : ℝ → ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε)
    (hbig : MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc ε M ×ˢ Work.Spaces.Iθ))
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hle : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ)),
      ‖f p.1 p.2‖ ≤ g p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry f) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) := by
  have hboxm : MeasurableSet (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hsub : Set.Icc ε M ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨Set.mem_Ici.mpr (le_trans hε.le hz.1), hθ⟩
  have hmle : ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ))
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [Measure.prod_restrict]
    exact Measure.restrict_mono hsub le_rfl
  have haesm : AEStronglyMeasurable (Function.uncurry f)
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry f) hf).mono_measure hmle
  refine hbig.mono' haesm ?_
  filter_upwards [hle] with p hp
  obtain ⟨a, b⟩ := p
  simpa only [Function.uncurry_apply_pair] using hp

/-! ## Auxiliary: AM–GM with a positive weight -/

private lemma abs_mul_le_amgm (a b s : ℝ) (hs : 0 < s) :
    |a * b| ≤ (1 / 2) * (a ^ 2 * s + b ^ 2 / s) := by
  have h := two_mul_le_add_sq (|a| * Real.sqrt s) (|b| / Real.sqrt s)
  have h1 : (|a| * Real.sqrt s) ^ 2 = a ^ 2 * s := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hs.le]
  have h2 : (|b| / Real.sqrt s) ^ 2 = b ^ 2 / s := by
    rw [div_pow, sq_abs, Real.sq_sqrt hs.le]
  have h3 : 2 * (|a| * Real.sqrt s) * (|b| / Real.sqrt s) = 2 * |a * b| := by
    rw [abs_mul]; field_simp
  rw [h1, h2, h3] at h
  linarith

/-- The θ-wise AM–GM behind the marginal Cauchy–Schwarz:
`2|f g| ≤ HkIntegrand α 0 f + HkIntegrand α 0 g` on the box. -/
private lemma abs_mul_le_half_Hk {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    ‖f z θ * g z θ‖ ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 f z θ
      + Work.Spaces.HkIntegrand α 0 g z θ) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Work.Spaces.sin_two_nonneg_of_Iθ (Set.Ioo_subset_Icc_self hθ)
  have hs1 : 1 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.EllipticEst.Honest.one_le_sEta hθ
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
    nlinarith [hz]
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hpos : 0 < (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hw1) 2)
      (lt_of_lt_of_le zero_lt_one hs1)
  have hb : 1 ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by nlinarith
  have h := abs_mul_le_amgm (f z θ) (g z θ)
    ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) hpos
  have h2 : (g z θ) ^ 2 / ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      ≤ (g z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
    rw [div_le_iff₀ hpos]
    have hb2 : 1 ≤ ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) :=
      one_le_mul_of_one_le_of_one_le hb hb
    calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (g z θ) ^ 2 * (((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
            * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      _ = (g z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
            * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by ring
  rw [Real.norm_eq_abs, abs_mul]
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α f z θ,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq f z θ hsin,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ hsin]
  rw [abs_mul] at h
  exact le_trans h (by linarith [h2])

/-- The square of a function vanishes on `(0,ε) ∪ (M,∞)` together with its first two
derivatives, when the function does. -/
private lemma deriv_deriv_eq_zero_of_supp {g : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M)
    (hleft : ∀ z, 0 < z → z < ε → g z = 0) (hright : ∀ z, M < z → g z = 0) :
    (∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → deriv g z = 0) ∧
      (∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → deriv (deriv g) z = 0) := by
  have hg : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → g =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
    intro z hz hz'
    have hz'' : z < ε ∨ M < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    rcases hz'' with hlt | hgt
    · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
      exact hleft w hw0 hw
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
      exact hright w hw
  constructor
  · intro z hz hz'
    rw [Filter.EventuallyEq.deriv_eq (hg z hz hz')]
    simp
  · intro z hz hz'
    have h1 : deriv g =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      have hz'' : z < ε ∨ M < z := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        have h2 := Filter.EventuallyEq.deriv_eq (hg w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw))
        simpa using h2
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        have h2 := Filter.EventuallyEq.deriv_eq (hg w (lt_trans (lt_trans hε hεM) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw))
        simpa using h2
    rw [Filter.EventuallyEq.deriv_eq h1]
    simp

/-- Almost every point of the box `[ε,M] ×ˢ Iθ` has second coordinate in the open interval. -/
private lemma ae_mem_Ioo_snd {ε M : ℝ} (hε : 0 < ε) :
    ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
  have hboxm : MeasurableSet (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [MeasureTheory.ae_restrict_iff' hboxm, MeasureTheory.ae_iff]
  refine measure_mono_null (t := Set.Icc ε M ×ˢ ({0} ∪ {Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq, not_imp] at hp
    obtain ⟨hpbox, hpne⟩ := hp
    refine ⟨hpbox.1, ?_⟩
    rcases eq_or_lt_of_le hpbox.2.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hpbox.2.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd ⟨h, h2⟩ hpne
  · have h1 : (volume : Measure (ℝ × ℝ)) (Set.Icc ε M ×ˢ ({0} ∪ {Real.pi / 2} : Set ℝ))
        = volume (Set.Icc ε M) * volume ({0} ∪ {Real.pi / 2} : Set ℝ) :=
      MeasureTheory.Measure.prod_prod _ _
    rw [h1, measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2)), mul_zero]

/-! ## Auxiliary: the fixed-θ radial integration by parts on the positive half-line -/

private lemma fixedThetaIBP (α : ℝ) (σ φ : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hσ : ContDiffOn ℝ 2 σ (Set.Ioi 0))
    (hσsupp : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b → σ z = 0)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) :
    (∫ z in Set.Ioi (0 : ℝ), σ z * (α ^ 2 * z ^ 2 * deriv (deriv φ) z
        + (α * (5 + α) * z) * deriv φ z) * φ z)
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), σ z * (z * deriv φ z) ^ 2)
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z => z ^ 2 * σ z)) z * (φ z) ^ 2)
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun z => z * σ z) z * (φ z) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have hW_off : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b →
      deriv (fun y : ℝ => y ^ 2 * σ y) z = 0 := by
    intro z hz hz'
    have hz'' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hev : (fun y : ℝ => y ^ 2 * σ y) =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        rw [hσsupp w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)]
        ring
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        rw [hσsupp w (lt_trans (lt_trans ha hab) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)]
        ring
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  have hddW_off : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b →
      deriv (deriv (fun y : ℝ => y ^ 2 * σ y)) z = 0 := by
    intro z hz hz'
    have hz'' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hev : deriv (fun y : ℝ => y ^ 2 * σ y) =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        exact hW_off w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        exact hW_off w (lt_trans (lt_trans ha hab) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  have hzσ_off : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b →
      deriv (fun y : ℝ => y * σ y) z = 0 := by
    intro z hz hz'
    have hz'' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hev : (fun y : ℝ => y * σ y) =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        rw [hσsupp w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)]
        ring
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        rw [hσsupp w (lt_trans (lt_trans ha hab) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)]
        ring
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  have hW2σ : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * σ y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hσ
  have hW2σ₁ : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * σ y)) (Set.Ioi 0) :=
    hW2σ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hW1σ : ContDiffOn ℝ 2 (fun y : ℝ => y * σ y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hσ
  have hφ₁ : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
    hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcontσ : ContinuousOn σ (Set.Icc a b) := hσ.continuousOn.mono hsub
  have hcontφ : ContinuousOn φ (Set.Icc a b) := hφ.continuousOn.mono hsub
  have hcontdφ : ContinuousOn (deriv φ) (Set.Icc a b) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddφ : ContinuousOn (deriv (deriv φ)) (Set.Icc a b) :=
    (hφ₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdW : ContinuousOn (deriv (fun y : ℝ => y ^ 2 * σ y)) (Set.Icc a b) :=
    (hW2σ.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddW : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * σ y))) (Set.Icc a b) :=
    (hW2σ₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdzσ : ContinuousOn (deriv (fun y : ℝ => y * σ y)) (Set.Icc a b) :=
    (hW1σ.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hi1 : IntegrableOn (fun z : ℝ => z ^ 2 * σ z * φ z * deriv (deriv φ) z)
      (Set.Ioi 0) :=
    ((((continuousOn_id.pow 2).mul hcontσ).mul hcontφ).mul hcontddφ).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show z ^ 2 * σ z * φ z * deriv (deriv φ) z = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hi2 : IntegrableOn
      (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * φ z * deriv φ z) (Set.Ioi 0) :=
    ((hcontdW.mul hcontφ).mul hcontdφ).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show deriv (fun y : ℝ => y ^ 2 * σ y) z * φ z * deriv φ z = 0
          rw [hW_off z hz.1 hz.2]; ring)
  have hi3 : IntegrableOn (fun z : ℝ => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    (hcontσ.mul ((continuousOn_id.mul hcontdφ).pow 2)).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show σ z * (z * deriv φ z) ^ 2 = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hi4 : IntegrableOn
      (fun z : ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * σ y)) z * (φ z) ^ 2) (Set.Ioi 0) :=
    (hcontddW.mul (hcontφ.pow 2)).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show deriv (deriv (fun y : ℝ => y ^ 2 * σ y)) z * (φ z) ^ 2 = 0
          rw [hddW_off z hz.1 hz.2]; ring)
  have hi1' : IntegrableOn (fun z : ℝ => σ z * z ^ 2 * deriv (deriv φ) z * φ z)
      (Set.Ioi 0) :=
    hi1.congr_fun (fun z _ => by ring) measurableSet_Ioi
  have hIntB0 : IntegrableOn (fun z : ℝ => σ z * z * deriv φ z * φ z) (Set.Ioi 0) :=
    (((hcontσ.mul continuousOn_id).mul hcontdφ).mul hcontφ).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show σ z * z * deriv φ z * φ z = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hIntB1 : IntegrableOn (fun z : ℝ => (z * σ z) * (2 * φ z * deriv φ z)) (Set.Ioi 0) :=
    ((continuousOn_id.mul hcontσ).mul (((continuous_const.continuousOn).mul hcontφ).mul hcontdφ))
      |>.integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show (z * σ z) * (2 * φ z * deriv φ z) = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hIntB2 : IntegrableOn (fun z : ℝ => deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2)
      (Set.Ioi 0) :=
    (hcontdzσ.mul (hcontφ.pow 2)).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2 = 0
          rw [hzσ_off z hz.1 hz.2]; ring)
  have hb1 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hσsupp z hz.1 (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb2 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hσsupp z (lt_trans (lt_trans ha hab) hz) (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb3 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hW_off z hz.1 (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb4 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2)
      atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hW_off z (lt_trans (lt_trans ha hab) hz) (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb5 : Tendsto (fun z : ℝ => (z * σ z) * (φ z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => (z * σ z) * (φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hσsupp z hz.1 (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb6 : Tendsto (fun z : ℝ => (z * σ z) * (φ z) ^ 2) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => (z * σ z) * (φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hσsupp z (lt_trans (lt_trans ha hab) hz) (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hzvw : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * σ y) (deriv (fun y : ℝ => y * σ y) z) z := by
    intro z hz
    exact (hW1σ.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hφ2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (φ y) ^ 2) (2 * φ z * deriv φ z) z := by
    intro z hz
    have hφz : HasDerivAt φ (deriv φ z) z :=
      (hφ.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
    convert hφz.pow 2 using 1
    simp [pow_one, mul_assoc]
  have key1 : (∫ z in Set.Ioi (0 : ℝ), σ z * z ^ 2 * deriv (deriv φ) z * φ z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2)
        - (∫ z in Set.Ioi (0 : ℝ), σ z * (z * deriv φ z) ^ 2) :=
    Work.FTS.EllipticEst.remov.ibpZZ σ φ hσ hφ hi1 hi2 hi3 hi4 hb1 hb2 hb3 hb4
  have hIBP2 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun y : ℝ => y * σ y) (u' := fun y : ℝ => deriv (fun y : ℝ => y * σ y) y)
    (v := fun y : ℝ => (φ y) ^ 2) (v' := fun y : ℝ => 2 * φ y * deriv φ y)
    hzvw hφ2 hIntB1 hIntB2 hb5 hb6
  have hIBP2' : (∫ z in Set.Ioi (0 : ℝ), (z * σ z) * (2 * φ z * deriv φ z))
      = -(∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2) := by
    simpa using hIBP2
  have key2 : (∫ z in Set.Ioi (0 : ℝ), σ z * z * deriv φ z * φ z)
      = -(1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2) := by
    have hcongr : (∫ z in Set.Ioi (0 : ℝ), (z * σ z) * (2 * φ z * deriv φ z))
        = 2 * (∫ z in Set.Ioi (0 : ℝ), σ z * z * deriv φ z * φ z) := by
      rw [show (∫ z in Set.Ioi (0 : ℝ), (z * σ z) * (2 * φ z * deriv φ z))
            = ∫ z in Set.Ioi (0 : ℝ), 2 * (σ z * z * deriv φ z * φ z) from
          setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
      rw [integral_const_mul]
    rw [hcongr] at hIBP2'
    linarith
  rw [show (∫ z in Set.Ioi (0 : ℝ), σ z * (α ^ 2 * z ^ 2 * deriv (deriv φ) z
          + (α * (5 + α) * z) * deriv φ z) * φ z)
        = ∫ z in Set.Ioi (0 : ℝ), α ^ 2 * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
            + (α * (5 + α)) * (σ z * z * deriv φ z * φ z) from
      setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [integral_add (hi1'.const_mul (α ^ 2)) (hIntB0.const_mul (α * (5 + α))),
    integral_const_mul, integral_const_mul, key1, key2]
  ring

end Work.FTS.EllipticEst.H2W.AeW

namespace Work.FTS.EllipticEst.H2W.AeW

set_option maxHeartbeats 6400000 in
theorem aeTruncWHon (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hmemU : Work.Spaces.HkMem α 0 u)
    (hmemGU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (hcpt : HasCompactSupport χ)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Icc (0:ℝ) ε, χ z = 0)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
            Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ) :
    (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
  obtain ⟨hαpos, hα4, hbeq, hdir0, hdirpi, hsmA, hmemG, hmemRad2, hmemAng2, hmomU, hmomG⟩ := h
  obtain ⟨ε, hεpos, hεχ⟩ := hε
  have hbdd : Bornology.IsBounded (tsupport χ) := hcpt.isCompact.isBounded
  obtain ⟨R, hRpos, hRle⟩ := hbdd.exists_pos_norm_le
  set M : ℝ := max R ε + 1 with hMdef
  have hmax1 : (0:ℝ) ≤ max R ε := le_trans (le_of_lt hεpos) (le_max_right R ε)
  have hεM : ε < M := by rw [hMdef]; have := le_max_right R ε; linarith
  have hRlt : R ≤ M := by rw [hMdef]; have := le_max_left R ε; linarith
  have hMpos : 0 < M := lt_trans hεpos hεM
  have hMχ : ∀ z, M < z → χ z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hne)
    have h1 := hRle z hmem
    have h2 : ‖z‖ = z := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [h2] at h1
    linarith
  -- ## 0. abbreviations
  let Φ : ℝ → ℝ := fun z => χ z * (Work.Spaces.w z) ^ 2
  let W2 : ℝ → ℝ := deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2))
  let W1 : ℝ → ℝ := deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z)
  let W2e : ℝ → ℝ := deriv (deriv (fun z => z ^ 2 * Φ z))
  let W1e : ℝ → ℝ := deriv (fun z => z * Φ z)
  let rad : ℝ → ℝ → ℝ := fun z θ =>
    -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ - (α * (5 + α) * z) * Work.Spaces.pz u z θ
  let Fr : ℝ → ℝ → ℝ := fun z θ => Φ z * (rad z θ * u z θ)
  let FL : ℝ → ℝ → ℝ := fun z θ => Φ z * (Work.Elliptic.Lzero u z θ * u z θ)
  let HH : ℝ → ℝ → ℝ := fun z θ => Φ z * (G z θ * u z θ)
  let G2 : ℝ → ℝ → ℝ := fun z θ => Φ z * (z * Work.Spaces.pz u z θ) ^ 2
  let GW2 : ℝ → ℝ → ℝ := fun z θ => W2e z * (u z θ) ^ 2
  let GW1 : ℝ → ℝ → ℝ := fun z θ => W1e z * (u z θ) ^ 2
  let Rad : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, rad z θ * u z θ
  let Lz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ
  let Dint : ℝ → ℝ → ℝ := fun z θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ
  let Eint : ℝ → ℝ → ℝ := fun z θ => (z * Work.Spaces.pz u z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ
  let Fint : ℝ → ℝ → ℝ := fun z θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  let Gint : ℝ → ℝ → ℝ := fun z θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  change (∫ z in Work.Spaces.Iz, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, Φ z
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, Φ z
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            W2 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            W1 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
  -- ## 1. support facts
  have hΦsupp : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → Φ z = 0 := by
    intro z hz hz'
    have hz'' : z < ε ∨ M < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hχ0 : χ z = 0 := by
      rcases hz'' with hlt | hgt
      · exact hεχ z ⟨le_of_lt hz, le_of_lt hlt⟩
      · exact hMχ z hgt
    dsimp only [Φ]
    rw [hχ0]; ring
  have hΦL : ∀ z, 0 < z → z < ε → Φ z = 0 := fun z hz hlt =>
    hΦsupp z hz (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hlt)
  have hΦR : ∀ z, M < z → Φ z = 0 := fun z hgt =>
    hΦsupp z (lt_trans (lt_trans hεpos hεM) hgt)
      (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hgt)
  have hW2e0 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W2e z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM (g := fun z => z ^ 2 * Φ z)
      (fun z hz hlt => by rw [hΦL z hz hlt]; ring)
      (fun z hgt => by rw [hΦR z hgt]; ring)).2
  have hW1e0 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W1e z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM (g := fun z => z * Φ z)
      (fun z hz hlt => by rw [hΦL z hz hlt]; ring)
      (fun z hgt => by rw [hΦR z hgt]; ring)).1
  have hW20 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W2 z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM
      (g := fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      (fun z hz hlt => by
        have h := hΦL z hz hlt
        dsimp only [Φ] at h
        rw [h]; ring)
      (fun z hgt => by
        have h := hΦR z hgt
        dsimp only [Φ] at h
        rw [h]; ring)).2
  have hW10 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W1 z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM
      (g := fun z => χ z * (Work.Spaces.w z) ^ 2 * z)
      (fun z hz hlt => by
        have h := hΦL z hz hlt
        dsimp only [Φ] at h
        rw [h]; ring)
      (fun z hgt => by
        have h := hΦR z hgt
        dsimp only [Φ] at h
        rw [h]; ring)).1
  -- ## 2. the weight calculus
  have hw_cd : ContDiffOn ℝ 2 (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    show ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact ContDiffOn.div ((contDiffOn_const.add contDiffOn_id).pow 2) (contDiffOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hw2_cd : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    simpa only [Pi.mul_apply, pow_two] using ContDiffOn.mul hw_cd hw_cd
  have hΦC2 : ContDiffOn ℝ 2 Φ (Set.Ioi 0) := by
    dsimp only [Φ]
    exact ContDiffOn.mul hχ.contDiffOn hw2_cd
  have hΦcont : ContinuousOn Φ (Set.Icc ε M) :=
    hΦC2.continuousOn.mono (fun x hx => lt_of_lt_of_le hεpos hx.1)
  obtain ⟨CΦ, hCΦ⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hΦcont
  have hCΦ0 : 0 ≤ CΦ := by
    have h1 := hCΦ ε ⟨le_rfl, le_of_lt hεM⟩
    linarith [norm_nonneg (Φ ε)]
  have hW2e_cont : ContinuousOn W2e (Set.Ioi 0) := by
    dsimp only [W2e]
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * Φ z) (Set.Ioi 0) :=
      ContDiffOn.mul (contDiffOn_id.pow 2) hΦC2
    have h2 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z ^ 2 * Φ z)) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have h3 : ContDiffOn ℝ 0 (deriv (deriv (fun z : ℝ => z ^ 2 * Φ z))) (Set.Ioi 0) :=
      h2.deriv_of_isOpen isOpen_Ioi le_rfl
    exact h3.continuousOn
  have hW1e_cont : ContinuousOn W1e (Set.Ioi 0) := by
    dsimp only [W1e]
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => z * Φ z) (Set.Ioi 0) :=
      ContDiffOn.mul contDiffOn_id hΦC2
    have h2 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z * Φ z)) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h2.continuousOn
  obtain ⟨CW2, hCW2⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hW2e_cont.mono (fun x hx => lt_of_lt_of_le hεpos hx.1))
  obtain ⟨CW1, hCW1⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hW1e_cont.mono (fun x hx => lt_of_lt_of_le hεpos hx.1))
  have hCW20 : 0 ≤ CW2 := by
    have h1 := hCW2 ε ⟨le_rfl, le_of_lt hεM⟩
    linarith [norm_nonneg (W2e ε)]
  have hCW10 : 0 ≤ CW1 := by
    have h1 := hCW1 ε ⟨le_rfl, le_of_lt hεM⟩
    linarith [norm_nonneg (W1e ε)]
  -- ## 3. box integrability
  have huSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hboxU : MeasureTheory.IntegrableOn (Function.uncurry Fint) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    boxInt_HkZero hεpos hεM huSO hmemU
  have hgradSO : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
        Work.FTS.EllipticEst.Q0 := contDiffOn_fst
    have h2 := ContDiffOn.mul h1 huSO.pz
    have h3 : Function.uncurry (Work.FTS.EllipticEst.H2W.Ae.grad u)
        = fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2 := by funext p; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, h3]
    exact h2
  have hboxD : MeasureTheory.IntegrableOn (Function.uncurry Eint) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    boxInt_HkZero hεpos hεM hgradSO hmemGU
  have hrad2SO : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
        Work.FTS.EllipticEst.Q0 := contDiffOn_fst.pow 2
    have h2 := ContDiffOn.mul h1 (huSO.pzIter 2)
    have h3 : Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2 := by funext p; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, h3]
    exact h2
  have hboxZ : MeasureTheory.IntegrableOn (Function.uncurry Dint) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    boxInt_HkZero hεpos hεM hrad2SO hmemRad2
  have hboxm : MeasurableSet (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- ## 4. the four product integrabilities
  have hcontG2 : ContinuousOn (Function.uncurry G2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) Work.FTS.EllipticEst.Q0 :=
      hΦC2.continuousOn.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h1.mul ((continuousOn_fst.mul huSO.pz.continuousOn).pow 2)
  have IntG2 : Integrable (Function.uncurry G2)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (g := fun z θ => CΦ * Eint z θ) hεpos ?_ hcontG2 ?_
    · exact hboxD.const_mul CΦ
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have hz : p.1 ∈ Set.Icc ε M := hp.1
      have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta p.2 :=
        Work.FTS.EllipticEst.Honest.one_le_sEta hpq
      have hΦb : |Φ p.1| ≤ CΦ := by
        have h := hCΦ p.1 hz
        rwa [Real.norm_eq_abs] at h
      dsimp only [G2]
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2
          ≤ (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := by
        nlinarith [hs1, sq_nonneg (p.1 * Work.Spaces.pz u p.1 p.2)]
      have h3 : |(p.1 * Work.Spaces.pz u p.1 p.2) ^ 2|
          = (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [h3]
      exact mul_le_mul hΦb h2 (sq_nonneg _) hCΦ0
  have hcontGW2 : ContinuousOn (Function.uncurry GW2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => W2e p.1) Work.FTS.EllipticEst.Q0 :=
      hW2e_cont.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h1.mul (huSO.continuousOn.pow 2)
  have IntGW2 : Integrable (Function.uncurry GW2)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (g := fun z θ => CW2 * Fint z θ) hεpos ?_ hcontGW2 ?_
    · exact hboxU.const_mul CW2
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have hz : p.1 ∈ Set.Icc ε M := hp.1
      have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta p.2 :=
        Work.FTS.EllipticEst.Honest.one_le_sEta hpq
      have hWb : |W2e p.1| ≤ CW2 := by
        have h := hCW2 p.1 hz
        rwa [Real.norm_eq_abs] at h
      dsimp only [GW2]
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : (u p.1 p.2) ^ 2 ≤ (u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := by
        nlinarith [hs1, sq_nonneg (u p.1 p.2)]
      have h3 : |(u p.1 p.2) ^ 2| = (u p.1 p.2) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [h3]
      exact mul_le_mul hWb h2 (sq_nonneg _) hCW20
  have hcontGW1 : ContinuousOn (Function.uncurry GW1) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => W1e p.1) Work.FTS.EllipticEst.Q0 :=
      hW1e_cont.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h1.mul (huSO.continuousOn.pow 2)
  have IntGW1 : Integrable (Function.uncurry GW1)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (g := fun z θ => CW1 * Fint z θ) hεpos ?_ hcontGW1 ?_
    · exact hboxU.const_mul CW1
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have hz : p.1 ∈ Set.Icc ε M := hp.1
      have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta p.2 :=
        Work.FTS.EllipticEst.Honest.one_le_sEta hpq
      have hWb : |W1e p.1| ≤ CW1 := by
        have h := hCW1 p.1 hz
        rwa [Real.norm_eq_abs] at h
      dsimp only [GW1]
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : (u p.1 p.2) ^ 2 ≤ (u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := by
        nlinarith [hs1, sq_nonneg (u p.1 p.2)]
      have h3 : |(u p.1 p.2) ^ 2| = (u p.1 p.2) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [h3]
      exact mul_le_mul hWb h2 (sq_nonneg _) hCW10
  have hcontFr : ContinuousOn (Function.uncurry Fr) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) Work.FTS.EllipticEst.Q0 :=
      hΦC2.continuousOn.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    have hrad : ContinuousOn (fun p : ℝ × ℝ =>
        -(α ^ 2 * p.1 ^ 2) * Work.Spaces.pzIter 2 u p.1 p.2
          - (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      ((((continuousOn_fst.pow 2).const_mul (α ^ 2)).neg).mul (huSO.pzIter 2).continuousOn).sub
        (((continuousOn_fst.const_mul (α * (5 + α))).mul huSO.pz.continuousOn))
    exact h1.mul (hrad.mul huSO.continuousOn)
  have hptFr : ∀ z ∈ Set.Icc ε M, ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), ‖Fr z θ‖ ≤
      CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4) * Dint z θ
        + α * (5 + α) * M * (1 / ε ^ 2) * Eint z θ
        + (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint z θ) := by
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le hεpos hz.1
    have hzM : z ≤ M := hz.2
    have hzε : ε ≤ z := hz.1
    have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
    have hs0 : 0 < Work.FTS.EllipticEst.sEta θ := lt_of_lt_of_le zero_lt_one hs1
    have hΦb : |Φ z| ≤ CΦ := by
      have h := hCΦ z hz
      rwa [Real.norm_eq_abs] at h
    -- the three key atom-bounds
    have hkey1 : (Work.Spaces.pzIter 2 u z θ) ^ 2
        ≤ (1 / ε ^ 4) * Dint z θ := by
      have hD : ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
          ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have h1 : ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
            ≤ z ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2 := by
          have h2 : ε ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ hεpos.le hzε 4
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        have h3 : z ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
            = (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 := by ring
        have h4 : (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          have h5 : (0:ℝ) ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 := sq_nonneg _
          nlinarith [hs1, h5]
        calc ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
            ≤ z ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2 := h1
          _ = (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 := h3
          _ ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := h4
      calc (Work.Spaces.pzIter 2 u z θ) ^ 2
          = (ε ^ 4)⁻¹ * (ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2) := by
            rw [inv_mul_cancel_left₀ (by positivity : (ε:ℝ) ^ 4 ≠ 0)]
        _ ≤ (ε ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (1 / ε ^ 4) * Dint z θ := by ring
    have hkey2 : (Work.Spaces.pz u z θ) ^ 2 ≤ (1 / ε ^ 2) * Eint z θ := by
      have hD : ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2
          ≤ (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have h1 : ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2
            ≤ z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 := by
          have h2 : ε ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hεpos.le hzε 2
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        have h3 : z ^ 2 * (Work.Spaces.pz u z θ) ^ 2
            = (z * Work.Spaces.pz u z θ) ^ 2 := by ring
        have h4 : (z * Work.Spaces.pz u z θ) ^ 2
            ≤ (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          have h5 : (0:ℝ) ≤ (z * Work.Spaces.pz u z θ) ^ 2 := sq_nonneg _
          nlinarith [hs1, h5]
        calc ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2 ≤ z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 := h1
          _ = (z * Work.Spaces.pz u z θ) ^ 2 := h3
          _ ≤ (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := h4
      calc (Work.Spaces.pz u z θ) ^ 2
          = (ε ^ 2)⁻¹ * (ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by
            rw [inv_mul_cancel_left₀ (by positivity : (ε:ℝ) ^ 2 ≠ 0)]
        _ ≤ (ε ^ 2)⁻¹ * ((z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (1 / ε ^ 2) * Eint z θ := by ring
    have hkey3 : (u z θ) ^ 2 ≤ Fint z θ := by
      have h5 : (0:ℝ) ≤ (u z θ) ^ 2 := sq_nonneg _
      nlinarith [hs1, h5]
    -- the two AM–GM steps
    have hc1 : 0 ≤ α ^ 2 * M ^ 2 := by nlinarith [hαpos, hMpos]
    have hc2 : 0 ≤ α * (5 + α) * M := by nlinarith [hαpos, hMpos]
    have hAB : |Work.Spaces.pzIter 2 u z θ| * |u z θ|
        ≤ ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2 := by
      have h := abs_mul_le_amgm (Work.Spaces.pzIter 2 u z θ) (u z θ) 1 one_pos
      rw [abs_mul, mul_one, div_one] at h
      linarith [h]
    have hBB : |Work.Spaces.pz u z θ| * |u z θ|
        ≤ ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2 := by
      have h := abs_mul_le_amgm (Work.Spaces.pz u z θ) (u z θ) 1 one_pos
      rw [abs_mul, mul_one, div_one] at h
      linarith [h]
    have e1 : α ^ 2 * M ^ 2 * ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2
        ≤ α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2 := by
      have hh : (Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2
          ≤ (1 / ε ^ 4) * Dint z θ + Fint z θ := add_le_add hkey1 hkey3
      have hc : (0:ℝ) ≤ α ^ 2 * M ^ 2 / 2 := by nlinarith [hαpos, hMpos]
      calc α ^ 2 * M ^ 2 * ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2
          = α ^ 2 * M ^ 2 / 2 * ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) := by ring
        _ ≤ α ^ 2 * M ^ 2 / 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) :=
            mul_le_mul_of_nonneg_left hh hc
        _ = α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2 := by ring
    have e2 : α * (5 + α) * M * ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2
        ≤ α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2 := by
      have hh : (Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2
          ≤ (1 / ε ^ 2) * Eint z θ + Fint z θ := add_le_add hkey2 hkey3
      have hc : (0:ℝ) ≤ α * (5 + α) * M / 2 := by nlinarith [hαpos, hMpos]
      calc α * (5 + α) * M * ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2
          = α * (5 + α) * M / 2 * ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) := by ring
        _ ≤ α * (5 + α) * M / 2 * ((1 / ε ^ 2) * Eint z θ + Fint z θ) :=
            mul_le_mul_of_nonneg_left hh hc
        _ = α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2 := by ring
    have hAB' : α ^ 2 * M ^ 2 * (|Work.Spaces.pzIter 2 u z θ| * |u z θ|)
        ≤ α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2 := by
      have h := mul_le_mul_of_nonneg_left hAB hc1
      linarith [h, e1]
    have hBB' : α * (5 + α) * M * (|Work.Spaces.pz u z θ| * |u z θ|)
        ≤ α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2 := by
      have h := mul_le_mul_of_nonneg_left hBB hc2
      linarith [h, e2]
    -- the bound on `rad`
    have hradb : |rad z θ| ≤ (α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
        + (α * (5 + α) * M) * |Work.Spaces.pz u z θ| := by
      have h1 : |rad z θ| ≤ (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          + (α * (5 + α) * z) * |Work.Spaces.pz u z θ| := by
        have h := abs_add_le ((-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 2 u z θ)
          (-((α * (5 + α) * z) * Work.Spaces.pz u z θ))
        rw [abs_neg] at h
        have h2 : |(-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 2 u z θ|
            = (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter 2 u z θ| := by
          rw [abs_mul, abs_neg, abs_of_nonneg (by nlinarith [hαpos, hz0])]
        have h3 : |(α * (5 + α) * z) * Work.Spaces.pz u z θ|
            = (α * (5 + α) * z) * |Work.Spaces.pz u z θ| := by
          rw [abs_mul, abs_of_nonneg (by nlinarith [hαpos, hz0])]
        rw [h2, h3] at h
        dsimp only [rad]
        exact h
      have hz2 : z ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hz0.le hzM 2
      have h4 : (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          ≤ (α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 (sq_nonneg α))
          (abs_nonneg _)
      have h5 : (α * (5 + α) * z) * |Work.Spaces.pz u z θ|
          ≤ (α * (5 + α) * M) * |Work.Spaces.pz u z θ| := by
        have hc0 : (0:ℝ) ≤ α * (5 + α) := by nlinarith [hαpos]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzM hc0) (abs_nonneg _)
      exact le_trans h1 (add_le_add h4 h5)
    -- assemble
    have hFr1 : ‖Fr z θ‖ = |Φ z| * |rad z θ| * |u z θ| := by
      dsimp only [Fr]
      rw [Real.norm_eq_abs]
      simp only [abs_mul]
      ring
    rw [hFr1]
    have hstep : |rad z θ| * |u z θ| ≤ ((α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          + (α * (5 + α) * M) * |Work.Spaces.pz u z θ|) * |u z θ| :=
      mul_le_mul_of_nonneg_right hradb (abs_nonneg _)
    have hdist : ((α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          + (α * (5 + α) * M) * |Work.Spaces.pz u z θ|) * |u z θ|
        = α ^ 2 * M ^ 2 * (|Work.Spaces.pzIter 2 u z θ| * |u z θ|)
          + α * (5 + α) * M * (|Work.Spaces.pz u z θ| * |u z θ|) := by ring
    calc |Φ z| * |rad z θ| * |u z θ|
        ≤ CΦ * |rad z θ| * |u z θ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΦb (abs_nonneg _))
            (abs_nonneg _)
      _ = CΦ * (|rad z θ| * |u z θ|) := by ring
      _ ≤ CΦ * (((α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
            + (α * (5 + α) * M) * |Work.Spaces.pz u z θ|) * |u z θ|) :=
          mul_le_mul_of_nonneg_left hstep hCΦ0
      _ = CΦ * (α ^ 2 * M ^ 2 * (|Work.Spaces.pzIter 2 u z θ| * |u z θ|)
            + α * (5 + α) * M * (|Work.Spaces.pz u z θ| * |u z θ|)) := by
          rw [hdist]
      _ ≤ CΦ * (α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2
            + α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hAB' hBB') hCΦ0
      _ = CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4) * Dint z θ
            + α * (5 + α) * M * (1 / ε ^ 2) * Eint z θ
            + (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint z θ) := by ring
  have IntFr : Integrable (Function.uncurry Fr)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (f := Fr)
      (g := fun z θ => CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4)) * Dint z θ
        + CΦ / 2 * (α * (5 + α) * M * (1 / ε ^ 2)) * Eint z θ
        + CΦ / 2 * (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint z θ) hεpos ?_ hcontFr ?_
    · exact ((hboxZ.const_mul (CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4)))).add
        (hboxD.const_mul (CΦ / 2 * (α * (5 + α) * M * (1 / ε ^ 2))))).add
        (hboxU.const_mul (CΦ / 2 * (α ^ 2 * M ^ 2 + α * (5 + α) * M)))
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have h := hptFr p.1 hp.1 p.2 hpq
      calc ‖Fr p.1 p.2‖ ≤ CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4) * Dint p.1 p.2
            + α * (5 + α) * M * (1 / ε ^ 2) * Eint p.1 p.2
            + (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint p.1 p.2) := h
        _ = CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4)) * Dint p.1 p.2
            + CΦ / 2 * (α * (5 + α) * M * (1 / ε ^ 2)) * Eint p.1 p.2
            + CΦ / 2 * (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint p.1 p.2 := by ring
  -- ## 5. the LHS honesty and reduction to the `G`-integral  (step (6a))
  have hvol0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by rw [MeasureTheory.ae_iff]; simp
  have hvolpi : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simp
  have hIoo_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hvol0, hvolpi] with θ hθ0 hθpi hmem
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hθ0), lt_of_le_of_ne hmem.2 hθpi⟩
  have hIθ_mem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    ae_restrict_mem measurableSet_Icc
  have hslice' : ∀ᵐ z ∂(volume.restrict (Set.Icc ε M)),
      (MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ) :=
    ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_of_lt_of_le hεpos hx.1) hslice
  have hHkG : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 G z θ
        = (G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α G z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq G z θ (Work.Spaces.sin_two_nonneg_of_Iθ hθ),
      Work.FTS.EllipticEst.sEta]
  have hHkU : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 u z θ
        = (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α u z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq u z θ (Work.Spaces.sin_two_nonneg_of_Iθ hθ),
      Work.FTS.EllipticEst.sEta]
  -- the θ-Cauchy–Schwarz bound, with the (junk) non-integrable case handled by `integral_undef`
  have hGu_bound : ∀ z ∈ Set.Icc ε M,
      ‖∫ θ in Work.Spaces.Iθ, G z θ * u z θ‖
        ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hεpos hz.1
    have hziz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hzpos)
    have hKG : Integrable (fun θ => Work.Spaces.HkIntegrand α 0 G z θ)
        (volume.restrict Work.Spaces.Iθ) := hmemG.1 z hziz
    have hKU : Integrable (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
        (volume.restrict Work.Spaces.Iθ) := hmemU.1 z hziz
    have hw1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
      nlinarith [hzpos]
    by_cases hInt : Integrable (fun θ => G z θ * u z θ) (volume.restrict Work.Spaces.Iθ)
    · rw [Real.norm_eq_abs]
      refine le_trans (MeasureTheory.abs_integral_le_integral_abs (f := fun θ => G z θ * u z θ)
        (μ := volume.restrict Work.Spaces.Iθ)) ?_
      have hmono : ∫ θ in Work.Spaces.Iθ, ‖G z θ * u z θ‖
          ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) := by
        refine MeasureTheory.integral_mono_ae hInt.norm ((hKG.add hKU).const_mul (1/2)) ?_
        filter_upwards [hIoo_ae] with θ hθ
        exact abs_mul_le_half_Hk hzpos hθ
      have heq : ∫ θ in Work.Spaces.Iθ, (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
            + Work.Spaces.HkIntegrand α 0 u z θ)
          = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hKG hKU]
      simp only [Real.norm_eq_abs] at hmono
      linarith [hmono, heq]
    · rw [MeasureTheory.integral_undef hInt, norm_zero]
      have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ :=
        integral_nonneg (fun θ => Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 G z θ)
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ :=
        integral_nonneg (fun θ => Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 u z θ)
      exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  -- `∫_θ bslOp u · u = ∫_θ G · u` for every `z ∈ Icc ε M`
  have hBslG : ∀ z ∈ Set.Icc ε M,
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
        = ∫ θ in Work.Spaces.Iθ, G z θ * u z θ := by
    intro z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hIoo_ae] with θ hθ
    rw [hbeq z (lt_of_lt_of_le hεpos hz.1) θ hθ.1 hθ.2]
  -- the honesty of the target's LHS
  have hLHSint : Integrable
      (fun z => Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      (volume.restrict (Set.Icc ε M)) := by
    have hsubI : Set.Icc ε M ⊆ Work.Spaces.Iz :=
      fun x hx => Set.mem_Ici.mpr (le_trans hεpos.le hx.1)
    have hmono : Integrable (fun z => CΦ / 2 *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ))
        (volume.restrict (Set.Icc ε M)) :=
      ((hmemG.2.mono_set hsubI).add (hmemU.2.mono_set hsubI)).const_mul (CΦ / 2)
    refine Integrable.mono' hmono ?_ ?_
    · have hjoint : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Φ p.1 * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
        have hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) Work.FTS.EllipticEst.Q0 :=
          hΦC2.continuousOn.comp continuousOn_fst
            (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
        exact hΦc.mul ((smoothOpen_bslOp huSO).continuousOn.mul huSO.continuousOn)
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
          Φ z * (Work.Elliptic.bslOp α u z θ * u z θ)) (volume.restrict Work.Spaces.Iz) :=
        hjoint.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
          Φ z * (Work.Elliptic.bslOp α u z θ * u z θ))
          (volume.restrict (Set.Icc ε M)) :=
        h1.mono_measure (Measure.restrict_mono hsubI le_rfl)
      exact h2.congr (Filter.Eventually.of_forall (fun z =>
        (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) (Φ z)
          (fun θ => Work.Elliptic.bslOp α u z θ * u z θ))))
    · filter_upwards [hslice', ae_restrict_mem measurableSet_Icc] with z hzsl hzmem
      rw [hBslG z hzmem]
      have hΦb : |Φ z| ≤ CΦ := by
        have h := hCΦ z hzmem
        rwa [Real.norm_eq_abs] at h
      calc ‖Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ)‖
          = |Φ z| * ‖∫ θ in Work.Spaces.Iθ, G z θ * u z θ‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        _ ≤ CΦ * ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
              + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)) :=
            mul_le_mul hΦb (hGu_bound z hzmem) (norm_nonneg _) hCΦ0
        _ = CΦ / 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
              + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by ring
  have hLHSa : (∫ z in Work.Spaces.Iz, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ z in Set.Icc ε M, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ) :=
    setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by rw [hΦsupp z hz hz']; ring)
  have hLHSb : (∫ z in Set.Icc ε M, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ) := by
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards with z hz
    rw [hBslG z hz]
  have hLHSc : (∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ))
      = ∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, HH z θ :=
    setIntegral_congr_fun measurableSet_Icc (fun z _ => by
      dsimp only [HH]
      rw [MeasureTheory.integral_const_mul])
  -- ## 6. the assembly
  -- (6a) the marginal integrabilities and the a.e. splitting `HH = Φ·Rad + Φ·Lz`
  have hIntFrMarg : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Fr z θ)
      (volume.restrict (Set.Icc ε M)) := Integrable.integral_prod_left IntFr
  have hIntPhiRad : Integrable (fun z => Φ z * Rad z) (volume.restrict (Set.Icc ε M)) := by
    refine hIntFrMarg.congr ?_
    filter_upwards with z
    dsimp only [Rad]
    exact MeasureTheory.integral_const_mul (Φ z) (fun θ => rad z θ * u z θ)
  have hIntHH : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, HH z θ)
      (volume.restrict (Set.Icc ε M)) := by
    refine hLHSint.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hzmem
    dsimp only [HH]
    rw [MeasureTheory.integral_const_mul, hBslG z hzmem]
  have haeSplit : ∀ᵐ z ∂(volume.restrict (Set.Icc ε M)),
      (∫ θ in Work.Spaces.Iθ, HH z θ) = Φ z * Rad z + Φ z * Lz z := by
    filter_upwards [hslice', ae_restrict_mem measurableSet_Icc] with z hzsl hzmem
    obtain ⟨hI1, hI2, -, -, -, -⟩ := hzsl
    have h1 : Integrable (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
        (volume.restrict Work.Spaces.Iθ) := hI1
    have h2 : Integrable (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
        (volume.restrict Work.Spaces.Iθ) := hI2
    have hIrad : Integrable (fun θ => rad z θ * u z θ) (volume.restrict Work.Spaces.Iθ) := by
      refine (h1.sub h2).congr ?_
      filter_upwards with θ
      show Work.Elliptic.bslOp α u z θ * u z θ - Work.Elliptic.Lzero u z θ * u z θ
        = rad z θ * u z θ
      rw [Work.Elliptic.bslOp_apply]
      dsimp only [rad]
      ring
    have hb : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
        = (∫ θ in Work.Spaces.Iθ, rad z θ * u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ) := by
      have hcongr : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
          = ∫ θ in Work.Spaces.Iθ,
              (rad z θ * u z θ + Work.Elliptic.Lzero u z θ * u z θ) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        show Work.Elliptic.bslOp α u z θ * u z θ
          = rad z θ * u z θ + Work.Elliptic.Lzero u z θ * u z θ
        rw [Work.Elliptic.bslOp_apply]
        dsimp only [rad]
        ring
      rw [hcongr, MeasureTheory.integral_add hIrad h2]
    calc (∫ θ in Work.Spaces.Iθ, HH z θ)
        = Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ) := by
          dsimp only [HH]
          rw [MeasureTheory.integral_const_mul]
      _ = Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ) := by
          rw [hBslG z hzmem]
      _ = Φ z * (∫ θ in Work.Spaces.Iθ, rad z θ * u z θ)
            + Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ) := by
          rw [hb]; ring
      _ = Φ z * Rad z + Φ z * Lz z := rfl
  have hIntPhiLz : Integrable (fun z => Φ z * Lz z) (volume.restrict (Set.Icc ε M)) := by
    refine (hIntHH.sub hIntPhiRad).congr ?_
    filter_upwards [haeSplit] with z hz
    show (∫ θ in Work.Spaces.Iθ, HH z θ) - Φ z * Rad z = Φ z * Lz z
    rw [hz]; ring
  have hLHSsplit : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, HH z θ)
      = (∫ z in Set.Icc ε M, Φ z * Rad z)
        + (∫ z in Set.Icc ε M, Φ z * Lz z) :=
    (MeasureTheory.integral_congr_ae haeSplit).trans
      (MeasureTheory.integral_add hIntPhiRad hIntPhiLz)
  -- (6b) the `θ`-marginals of the three smooth weighted pieces
  have hX : Integrable (fun θ => ∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := Integrable.integral_prod_right IntG2
  have hY : Integrable (fun θ => ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := Integrable.integral_prod_right IntGW2
  have hZ : Integrable (fun θ => ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := Integrable.integral_prod_right IntGW1
  -- (6c) the radial integration by parts, `θ` by `θ`
  have hIBPθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ z in Set.Icc ε M, Fr z θ)
        = α ^ 2 * (∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
          - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
          + ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2) := by
    filter_upwards [hIoo_ae] with θ hθ
    have hφ : ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) :=
      (huSO.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
    have hIBP := fixedThetaIBP α Φ (fun z : ℝ => u z θ) hεpos hεM hΦC2 hΦsupp hφ
    have hsupp1 : (∫ z in Set.Icc ε M, Fr z θ) = ∫ z in Set.Ioi (0:ℝ), Fr z θ :=
      (setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        dsimp only [Fr]; rw [hΦsupp z hz hz']; ring)).symm
    have hW2eb : (∫ z in Set.Ioi (0:ℝ),
          deriv (deriv (fun z : ℝ => z ^ 2 * Φ z)) z * (u z θ) ^ 2)
        = ∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      rfl
    have hW1eb : (∫ z in Set.Ioi (0:ℝ), deriv (fun z : ℝ => z * Φ z) z * (u z θ) ^ 2)
        = ∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      rfl
    have hneg : (∫ z in Set.Ioi (0:ℝ), Fr z θ)
        = α ^ 2 * (∫ z in Set.Ioi (0:ℝ),
              Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
          - (α ^ 2 / 2) * (∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2)
          + ((α * (5 + α)) / 2) * (∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2) := by
      have hfun : (fun z : ℝ => Fr z θ) = fun z : ℝ =>
          - (Φ z * (α ^ 2 * z ^ 2 * deriv (deriv (fun z' : ℝ => u z' θ)) z
              + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ) := by
        funext z
        have hpz2 : Work.Spaces.pzIter 2 u z θ = deriv (deriv (fun z' : ℝ => u z' θ)) z := rfl
        have hpz1 : Work.Spaces.pz u z θ = deriv (fun z' : ℝ => u z' θ) z := rfl
        dsimp only [Fr, rad]
        rw [hpz2, hpz1]
        ring
      have hstep : -(∫ z in Set.Ioi (0:ℝ), Φ z * (α ^ 2 * z ^ 2
            * deriv (deriv (fun z' : ℝ => u z' θ)) z
            + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ)
          = -(-α ^ 2 * (∫ z in Set.Ioi (0:ℝ),
                Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
              + (α ^ 2 / 2) * (∫ z in Set.Ioi (0:ℝ),
                  deriv (deriv (fun z : ℝ => z ^ 2 * Φ z)) z * (u z θ) ^ 2)
              - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0:ℝ),
                  deriv (fun z : ℝ => z * Φ z) z * (u z θ) ^ 2)) :=
        congrArg Neg.neg hIBP
      calc (∫ z in Set.Ioi (0:ℝ), Fr z θ)
          = ∫ z in Set.Ioi (0:ℝ), - (Φ z * (α ^ 2 * z ^ 2
              * deriv (deriv (fun z' : ℝ => u z' θ)) z
              + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ) := by
            rw [hfun]
        _ = -(∫ z in Set.Ioi (0:ℝ), Φ z * (α ^ 2 * z ^ 2
              * deriv (deriv (fun z' : ℝ => u z' θ)) z
              + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ) :=
            MeasureTheory.integral_neg _
        _ = α ^ 2 * (∫ z in Set.Ioi (0:ℝ),
                Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
              - (α ^ 2 / 2) * (∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2)
              + ((α * (5 + α)) / 2) * (∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2) := by
            rw [hstep, hW2eb, hW1eb]
            ring
    have hIoi1 : (∫ z in Set.Ioi (0:ℝ), Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
        = ∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2 :=
      setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        rw [hΦsupp z hz hz']; ring)
    have hIoi2 : (∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2)
        = ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2 :=
      setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        rw [hW2e0 z hz hz']; ring)
    have hIoi3 : (∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2)
        = ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2 :=
      setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        rw [hW1e0 z hz hz']; ring)
    first
      | (rw [hsupp1, hneg, hIoi1, hIoi2, hIoi3]; ring)
      | rw [hsupp1, hneg, hIoi1, hIoi2, hIoi3]
  have hIBPlin : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, Fr z θ)
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W2e z * (u z θ) ^ 2)
        + ((α * (5 + α)) / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W1e z * (u z θ) ^ 2) := by
    have h1 : Integrable (fun θ => α ^ 2 * (∫ z in Set.Icc ε M,
        Φ z * (z * Work.Spaces.pz u z θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) :=
      hX.const_mul _
    have h2 : Integrable (fun θ => (α ^ 2 / 2) * (∫ z in Set.Icc ε M,
        W2e z * (u z θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) := hY.const_mul _
    have h3 : Integrable (fun θ => ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M,
        W1e z * (u z θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) := hZ.const_mul _
    have h12 : Integrable (fun θ => α ^ 2 * (∫ z in Set.Icc ε M,
        Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2))
        (volume.restrict Work.Spaces.Iθ) := by
      refine (h1.sub h2).congr ?_
      filter_upwards with θ
      rfl
    refine (MeasureTheory.integral_congr_ae hIBPθ).trans ?_
    show (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 * (∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
          - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
          + ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2)))
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W2e z * (u z θ) ^ 2)
        + ((α * (5 + α)) / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W1e z * (u z θ) ^ 2)
    first
      | (rw [MeasureTheory.integral_add h12 h3, MeasureTheory.integral_sub h1 h2,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
         ring)
      | rw [MeasureTheory.integral_add h12 h3, MeasureTheory.integral_sub h1 h2,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
  have hA : (∫ z in Set.Icc ε M, Φ z * Rad z)
      = ∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, Fr z θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only [Rad]
    exact (MeasureTheory.integral_const_mul (Φ z) (fun θ => rad z θ * u z θ)).symm
  have hAswap : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, Fr z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, Fr z θ :=
    MeasureTheory.integral_integral_swap IntFr
  have hD1 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
        Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
      = ∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2) := by
    have hsw : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ,
          Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            Φ z * (z * Work.Spaces.pz u z θ) ^ 2 :=
      MeasureTheory.integral_integral_swap IntG2
    rw [← hsw]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        = Φ z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
    exact MeasureTheory.integral_const_mul (Φ z) (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
  have hD2 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
      = ∫ z in Set.Icc ε M, W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    have hsw : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, W2e z * (u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2 :=
      MeasureTheory.integral_integral_swap IntGW2
    rw [← hsw]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, W2e z * (u z θ) ^ 2)
        = W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
    exact MeasureTheory.integral_const_mul (W2e z) (fun θ => (u z θ) ^ 2)
  have hD3 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2)
      = ∫ z in Set.Icc ε M, W1e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    have hsw : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, W1e z * (u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2 :=
      MeasureTheory.integral_integral_swap IntGW1
    rw [← hsw]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, W1e z * (u z θ) ^ 2)
        = W1e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
    exact MeasureTheory.integral_const_mul (W1e z) (fun θ => (u z θ) ^ 2)
  have hIBPfinal : (∫ z in Set.Icc ε M, Φ z * Rad z)
      = α ^ 2 * (∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz u z θ) ^ 2))
        - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M, W1e z
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
    first
      | (rw [hA, hAswap, hIBPlin, hD1, hD2, hD3]; ring)
      | rw [hA, hAswap, hIBPlin, hD1, hD2, hD3]
  -- (6d) the support reductions on the `Iz`-side, `W2e = W2`, `W1e = W1`, and the final algebra
  have hW2e_eq : W2e = W2 := by
    have hfun : (fun z : ℝ => z ^ 2 * Φ z)
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2 := by
      funext z
      dsimp only [Φ]
      ring
    dsimp only [W2e, W2]
    rw [hfun]
  have hW1e_eq : W1e = W1 := by
    have hfun : (fun z : ℝ => z * Φ z) = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * z := by
      funext z
      dsimp only [Φ]
      ring
    dsimp only [W1e, W1]
    rw [hfun]
  have hR1 : (∫ z in Work.Spaces.Iz,
        Φ z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ,
          (z * Work.Spaces.pz u z θ) ^ 2) :=
    setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hΦsupp z hz hz']; ring)
  have hR2 : (∫ z in Work.Spaces.Iz,
        Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
      = ∫ z in Set.Icc ε M, Φ z * Lz z :=
    setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hΦsupp z hz hz']; ring)
  have hR3 : (∫ z in Work.Spaces.Iz, W2 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      = ∫ z in Set.Icc ε M, W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    rw [← hW2e_eq]
    exact setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hW2e0 z hz hz']; ring)
  have hR4 : (∫ z in Work.Spaces.Iz, W1 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      = ∫ z in Set.Icc ε M, W1e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    rw [← hW1e_eq]
    exact setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hW1e0 z hz hz']; ring)
  rw [hLHSa, hLHSb, hLHSc, hR1, hR2, hR3, hR4, hLHSsplit, hIBPfinal]
  ring

end Work.FTS.EllipticEst.H2W.AeW
