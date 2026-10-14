import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.THL.mixed_slice_pointwise_le_noTrace
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.SlotBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The crude pointwise bound with the explicit constant -/

/-- **The crude pointwise bound for the low slots, with the explicit constant**
`Cpt α = √(((4/π) + 200/(γ-1))·40)`: `|D_z^jD_θ^i f z θ| ≤ Cpt α · min z 1 · |f|_{ℋ⁴}`
for `j + i ≤ 2`.  This is the proof of `RXT.hkMem_pointwise_min` with its constant exposed. -/
theorem slot_crude {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} {j i : ℕ} (hji : j + i ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    |Work.Spaces.mixed j i f z θ|
      ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
        * min z 1 * Work.Spaces.HkNorm α 4 f := by
  have hγp : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα
    linarith
  have hC0 : (0 : ℝ) ≤ ((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40 := by
    positivity
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hsq := Work.FTS_RegExport.RXT.hkMem_pointwise_min_sq (α := α) hα hα1 h4 hmem
    (by omega : i + j ≤ 2) hz hθ0 hθ1
  calc |Work.Spaces.mixed j i f z θ|
      = Real.sqrt ((Work.Spaces.mixed j i f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40
          * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
          * min z 1 * Work.Spaces.HkNorm α 4 f := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC0, Real.sqrt_sq hmin]
        rfl

/-! ## The tail bound -/

/-- `Iz = [0,∞)` agrees with `(0,∞)` up to a null set. -/
private theorem Iz_ae_eq_Ioi_d3 : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- `w` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_d3 :
    ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- **The tail bound for the low slots.**  For a datum which is `C⁴` on the open quadrant and
honestly in `ℋ⁴`, every mixed slot of order `≤ 1` satisfies

  `(D_z^jD_θ^i f z θ)² ≤ C·|f|_{ℋ⁴}²·z³/(1+z)⁴`  (`z > 0`, `0 < θ < π/2`),

with `C` the constant of the angular-sup bound `RXT.Slots.v2_theta_sup_uniform`. -/
theorem slot_tail {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fn),
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f → ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        (Work.Spaces.mixed j i f z θ) ^ 2
          ≤ C * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
  obtain ⟨K, hK0, hK⟩ := Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform (α := α) hα hα1
  refine ⟨5 * K, by positivity, ?_⟩
  intro f h4 hmem j i hji z θ hz hθ0 hθ1
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  set J : ℝ → ℝ := fun x => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ with hJdef
  have hJint : IntegrableOn J Work.Spaces.Iz := by
    rw [hJdef]; exact hmem.2
  have hJnn : ∀ x, 0 ≤ J x :=
    fun x => integral_nonneg (fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f x σ)
  -- the `θ`-slice of a slot with its weight is integrable on `Iz`, dominated by `K * J`
  have slice_int : ∀ (b a : ℕ), a + b ≤ 2 →
      IntegrableOn (fun x => (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
        Work.Spaces.Iz := by
    intro b a hba
    have hslice : ContDiffOn ℝ 1 (fun x => Work.Spaces.mixed b a f x θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 1 (by omega))
    refine (hJint.const_mul K).mono' ?_ ?_
    · rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi_d3]
      exact ((hslice.continuousOn.mul continuousOn_w_d3).pow 2).aestronglyMeasurable
        measurableSet_Ioi
    · rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi_d3]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact hK f h4 hmem b a (by omega) x hx θ hθ0 hθ1
  have hint1 : IntegrableOn (fun x => (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := slice_int j i (by omega)
  have hint2 : IntegrableOn (fun x => (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
      * Work.Spaces.w x) ^ 2) Work.Spaces.Iz := by
    have := slice_int (j + 1) i (by omega)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ici
    rw [show x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
      = Work.Spaces.mixed (j + 1) i f x θ from rfl]
  -- the pointwise dominations by `K * J`
  have hK1 : ∀ x : ℝ, 0 < x → (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2 ≤ K * J x :=
    fun x hx => hK f h4 hmem j i (by omega) x hx θ hθ0 hθ1
  have hK2 : ∀ x : ℝ, 0 < x →
      (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2 ≤ K * J x :=
    fun x hx => hK f h4 hmem (j + 1) i (by omega) x hx θ hθ0 hθ1
  -- the derivative of the slot's `z`-slice
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x' => Work.Spaces.mixed j i f x' θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i f) x θ) x := by
    intro x hx
    have hslice : ContDiffOn ℝ 1 (fun x' => Work.Spaces.mixed j i f x' θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 j i 1 (by omega))
    exact (hslice.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx) |>.hasDerivAt
  -- the radial Agmon bound for the `θ`-slice
  have hmain := Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay
    (v := fun x => Work.Spaces.mixed j i f x θ)
    (v' := fun x => Work.Spaces.pz (Work.Spaces.mixed j i f) x θ) hz hderiv hint1 hint2
  -- the two tail integrals are bounded by `K · HkSq`
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
  have hKJnn : ∀ x, 0 ≤ K * J x := fun x => mul_nonneg hK0 (hJnn x)
  have hKJi : IntegrableOn (fun x => K * J x) Work.Spaces.Iz := hJint.const_mul K
  have htail_le : (∫ x in Work.Spaces.Iz, K * J x) = K * Work.Spaces.HkSq α 4 f := by
    rw [MeasureTheory.integral_const_mul]
    rfl
  have hbd1 : (∫ x in Set.Ioi z, (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
      ≤ K * Work.Spaces.HkSq α 4 f := by
    have hFint : IntegrableOn (fun x => (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
        (Set.Ioi z) := hint1.mono_set hsub
    have hGint : IntegrableOn (fun x => K * J x) (Set.Ioi z) := hKJi.mono_set hsub
    have h1 : (∫ x in Set.Ioi z, (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
        ≤ ∫ x in Set.Ioi z, K * J x :=
      MeasureTheory.setIntegral_mono_on hFint hGint measurableSet_Ioi
        (fun x hx => hK1 x (lt_trans hz hx))
    have h2 : (∫ x in Set.Ioi z, K * J x) ≤ ∫ x in Work.Spaces.Iz, K * J x :=
      MeasureTheory.setIntegral_mono_set hKJi (Filter.Eventually.of_forall hKJnn)
        (Filter.Eventually.of_forall hsub)
    rw [htail_le] at h2
    linarith
  have hbd2 : (∫ x in Set.Ioi z, (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
      * Work.Spaces.w x) ^ 2) ≤ K * Work.Spaces.HkSq α 4 f := by
    have hFint : IntegrableOn (fun x => (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2) (Set.Ioi z) := hint2.mono_set hsub
    have hGint : IntegrableOn (fun x => K * J x) (Set.Ioi z) := hKJi.mono_set hsub
    have h1 : (∫ x in Set.Ioi z, (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2) ≤ ∫ x in Set.Ioi z, K * J x :=
      MeasureTheory.setIntegral_mono_on hFint hGint measurableSet_Ioi (fun x hx => by
        have hid : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
            = Work.Spaces.mixed (j + 1) i f x θ := rfl
        rw [hid]
        exact hK2 x (lt_trans hz hx))
    have h2 : (∫ x in Set.Ioi z, K * J x) ≤ ∫ x in Work.Spaces.Iz, K * J x :=
      MeasureTheory.setIntegral_mono_set hKJi (Filter.Eventually.of_forall hKJnn)
        (Filter.Eventually.of_forall hsub)
    rw [htail_le] at h2
    linarith
  -- combine
  have hfin : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    have h5 : (4 : ℝ) * (∫ x in Set.Ioi z, (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
        + (∫ x in Set.Ioi z, (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
            * Work.Spaces.w x) ^ 2) ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
      linarith [hbd1, hbd2]
    linarith [hmain, h5]
  -- divide by `w z ^ 2 * z = (1+z)^4/z^3`
  have hwz : (Work.Spaces.w z) ^ 2 * z = (1 + z) ^ 4 / z ^ 3 := by
    rw [Work.Spaces.w, div_pow]
    field_simp
  have hfin' : (Work.Spaces.mixed j i f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * z)
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    rw [← mul_assoc]; exact hfin
  rw [hwz] at hfin'
  have hpos : 0 < (1 + z) ^ 4 / z ^ 3 := by positivity
  have hgoal : (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ 5 * K * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
    rw [show z ^ 3 / (1 + z) ^ 4 = ((1 + z) ^ 4 / z ^ 3)⁻¹ by rw [inv_div]]
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hpos).mpr hfin'
  exact hgoal

end Work.FTS.StrongEps.E4R3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Extract =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Extraction of pointwise bounds from `WlInf` -/

/-- The `𝒲^{4,∞}`-norm is nonnegative on the honest class. -/
theorem wlInf_nonneg {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    0 ≤ Work.Spaces.WlInf α 4 f := by
  rw [Work.Spaces.WlInf]
  refine add_nonneg (Finset.sum_nonneg fun k hk => ?_)
    (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
  · exact Work.Spaces.supAbs_nonneg (hmem.1 k (by have := Finset.mem_range.mp hk; omega))
  · split_ifs with h
    · exact Work.Spaces.supAbs_nonneg
        (hmem.2 j (by have := Finset.mem_range.mp hj; omega) k
          (by have := Finset.mem_range.mp hk; omega) h.1 h.2)
    · exact le_refl 0

/-- The sup norm of the datum itself is bounded by `|f|_{𝒲^{4,∞}}` (the `k = 0` summand). -/
theorem supAbs_le_WlInf {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    Work.Spaces.supAbs f ≤ Work.Spaces.WlInf α 4 f := by
  have hfirst : Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0 * Work.Spaces.pzIter 0 f z θ)
      ≤ ∑ k ∈ Finset.range 5,
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ) :=
    Finset.single_le_sum
      (f := fun k => Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
      (fun k hk => Work.Spaces.supAbs_nonneg (hmem.1 k (by
        have := Finset.mem_range.mp hk; omega)))
      (by simp)
  have hsecond : (∑ k ∈ Finset.range 5,
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
      ≤ Work.Spaces.WlInf α 4 f := by
    rw [Work.Spaces.WlInf]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
    split_ifs with h
    · exact Work.Spaces.supAbs_nonneg (hmem.2 j (by have := Finset.mem_range.mp hj; omega) k
        (by have := Finset.mem_range.mp hk; omega) h.1 h.2)
    · exact le_refl 0
  calc Work.Spaces.supAbs f
      = Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0 * Work.Spaces.pzIter 0 f z θ) := by simp
    _ ≤ _ := hfirst
    _ ≤ Work.Spaces.WlInf α 4 f := hsecond

/-- **The pointwise bound from an honest `𝒲^{4,∞}`-norm.**  For a datum whose `𝒲^{4,∞}`-norm
is finite (`WlInfMem`), every value on the domain is bounded by that norm. -/
theorem abs_le_WlInf {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ| ≤ Work.Spaces.WlInf α 4 f ∧ 0 ≤ Work.Spaces.WlInf α 4 f := by
  have hfin : Work.Spaces.SupFinite f := by
    have h := hmem.1 0 (by norm_num)
    simpa using h
  exact ⟨le_trans (Work.Spaces.abs_le_supAbs hz hθ hfin) (supAbs_le_WlInf hmem),
    wlInf_nonneg hmem⟩

/-! ## The trace-free `ℋ⁴ → L^∞` trade-off -/

/-- **The pointwise bound from `SmoothOpen ∧ HkMem α 4`**: the trace-free `ℋ⁴ → L^∞`
trade-off `v2_hkMem_pointwise_min`, restricted to order `0` and with the `min z 1`-factor
dropped (`min z 1 ≤ 1`). -/
theorem exists_pointwise_bound_of_HQo {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ C := by
  obtain ⟨C, hC0, hbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  refine ⟨C * Work.Spaces.HkNorm α 4 f, mul_nonneg hC0 (Work.Spaces.HkNorm_nonneg α 4 f), ?_⟩
  intro z θ hz hθ0 hθ1
  have h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp h 4
  have hpt := hbd f h4 hm 0 0 (by norm_num) z θ hz hθ0 hθ1
  have hpt' : |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.pthIter_zero] using hpt
  calc |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := hpt'
    _ ≤ C * 1 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right z 1) hC0)
          (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = C * Work.Spaces.HkNorm α 4 f := by ring

/-! ## Pointwise bounds for the star and elliptic parts of `ℛ(Φ̃), U(Φ̃), V(Φ̃)` -/

/-- **The star bounds**: from `StarPkgo2` (whose `𝒲^{4,∞}`-fields bound
`((z+1)/z)ℛ(Φ̃_*)`, `V(Φ̃_*)` and `U(Φ̃_*)/sin 2θ` by `Cs·α`) one gets, at every interior
point, `|ℛ(Φ̃_*)| ≤ Cs·α`, `|V(Φ̃_*)| ≤ Cs·α` and `|U(Φ̃_*)| ≤ Cs·α·|sin 2θ|`. -/
theorem star_op_bounds {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ C ∧
       |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ C ∧
       |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          ≤ C * |Work.Construction.s2 θ|) := by
  obtain ⟨hRmem, hRb⟩ := hstar.RW
  obtain ⟨hVmem, hVb⟩ := hstar.VW
  obtain ⟨hUmem, hUb⟩ := hstar.UsW
  have hCnn : 0 ≤ Cs * α := le_trans (wlInf_nonneg hRmem) hRb
  refine ⟨Cs * α, hCnn, ?_⟩
  intro z θ hz hθ0 hθ1
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  obtain ⟨h1, -⟩ := abs_le_WlInf hRmem hzIz hθIθ
  have hR : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
    have h2 : |(z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ Cs * α := le_trans h1 hRb
    have hzpos : 0 < (z + 1) / z := by positivity
    have hfac : (z / (z + 1)) * ((z + 1) / z) = 1 := by field_simp
    have h3 : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| * ((z + 1) / z)
        ≤ Cs * α := by
      have h2' : (z + 1) / z
          * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
        rwa [abs_mul, abs_of_pos hzpos] at h2
      calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| * ((z + 1) / z)
          = (z + 1) / z * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
            ring
        _ ≤ Cs * α := h2'
    have hz1 : 0 < z + 1 := by linarith
    calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        = |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
            * ((z / (z + 1)) * ((z + 1) / z)) := by rw [hfac, mul_one]
      _ = (|Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| * ((z + 1) / z))
            * (z / (z + 1)) := by ring
      _ ≤ (Cs * α) * (z / (z + 1)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (Cs * α) * 1 :=
          mul_le_mul_of_nonneg_left (by rw [div_le_one hz1]; linarith) hCnn
      _ = Cs * α := by ring
  have hV : |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
    obtain ⟨h1', -⟩ := abs_le_WlInf hVmem hzIz hθIθ
    exact le_trans h1' hVb
  have hU : |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ Cs * α * |Work.Construction.s2 θ| := by
    obtain ⟨h1', -⟩ := abs_le_WlInf hUmem hzIz hθIθ
    have h2 : |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ| ≤ Cs * α := le_trans h1' hUb
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      have h2θ : 0 < 2 * θ := by linarith
      have h2π : 2 * θ < Real.pi := by linarith [Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
    calc |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        = |(Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ) * Work.Construction.s2 θ| := by
          rw [div_mul_cancel₀ _ hs2]
      _ = |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := by rw [abs_mul]
      _ ≤ (Cs * α) * |Work.Construction.s2 θ| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  exact ⟨hR, hV, by simpa only [mul_assoc] using hU⟩

/-- **The elliptic bounds**: from `EllPkgGo` (whose fields are `SmoothOpen ∧ HkMem α 4`, hence
pointwise bounded by `exists_pointwise_bound_of_HQo`) one gets, at every interior point,
`|ℛ(Φ̃_ell)| ≤ C`, `|V(Φ̃_ell)| ≤ C` and `|U(Φ̃_ell)| ≤ C·|sin 2θ|`. -/
theorem ell_op_bounds {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W Φg : ℝ → ℝ → ℝ}
    (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Construction.Rop α (Work.Construction.PhiTil α W Φg) z θ| ≤ C ∧
       |Work.Construction.Vop (Work.Construction.PhiTil α W Φg) z θ| ≤ C ∧
       |Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ|
          ≤ C * |Work.Construction.s2 θ|) := by
  obtain ⟨CR, hCR0, hCR⟩ := exists_pointwise_bound_of_HQo hα hα1 hell.R.1.1 hell.R.1.2
  obtain ⟨CU, hCU0, hCU⟩ := exists_pointwise_bound_of_HQo hα hα1 hell.U.1.1 hell.U.1.2
  obtain ⟨CV, hCV0, hCV⟩ := exists_pointwise_bound_of_HQo hα hα1 hell.V.1.1 hell.V.1.2
  refine ⟨max CR (max CU CV), le_trans hCR0 (le_max_left _ _), ?_⟩
  intro z θ hz hθ0 hθ1
  have hCVmax : |Work.Construction.Vop (Work.Construction.PhiTil α W Φg) z θ|
      ≤ max CR (max CU CV) :=
    le_trans (hCV hz hθ0 hθ1)
      (le_trans (le_max_right CU CV) (le_max_right CR (max CU CV)))
  refine ⟨le_trans (hCR hz hθ0 hθ1) (le_max_left _ _), hCVmax, ?_⟩
  have hU := hCU hz hθ0 hθ1
  have hUC : Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ
      = (Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ
          / Work.Construction.s2 θ) * Work.Construction.s2 θ := by
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      have h2θ : 0 < 2 * θ := by linarith
      have h2π : 2 * θ < Real.pi := by linarith [Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
    rw [div_mul_cancel₀ _ hs2]
  rw [hUC, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact le_trans hU (le_trans (le_max_left CU CV) (le_max_right CR (max CU CV)))

/-! ## Filter bookkeeping -/

/-- `Ici 0` is a neighbourhood of every `z > 0`. -/
theorem Ici_mem_nhds_of_pos {z : ℝ} (hz : 0 < z) : Set.Ici (0 : ℝ) ∈ 𝓝 z :=
  Filter.mem_of_superset (isOpen_Ioi.mem_nhds hz) (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))

/-- Points of the filter `𝓝[>] 0` eventually lie in the open angular interval. -/
theorem eventually_mem_Ioo_left : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)] with θ h
  intro hθ
  exact ⟨hθ, h⟩

/-- Points of the filter `𝓝[<] (π/2)` eventually lie in the open angular interval. -/
theorem eventually_mem_Ioo_right :
    ∀ᶠ θ : ℝ in 𝓝[<] (Real.pi / 2), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)] with θ h
  intro hθ
  exact ⟨h, hθ⟩

/-- **A vanishing factor times an eventually bounded factor vanishes.** -/
theorem tendsto_mul_of_eventually_bounded {f g : ℝ → ℝ} {l : Filter ℝ} {C : ℝ}
    (hf : Filter.Tendsto f l (𝓝 0)) (hg : ∀ᶠ θ in l, |g θ| ≤ C) :
    Filter.Tendsto (fun θ => f θ * g θ) l (𝓝 0) := by
  have h1 : Filter.Tendsto (fun θ => |f θ| * C) l (𝓝 0) := by
    have h := hf.norm.mul_const C
    simpa only [Real.norm_eq_abs, norm_zero, zero_mul] using h
  have habs : Filter.Tendsto (fun θ => |f θ * g θ|) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
      (Eventually.of_forall fun θ => abs_nonneg _) ?_
    filter_upwards [hg] with θ hθ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- **The vanishing of a term bounded by a vanishing one.** -/
theorem tendsto_zero_of_eventually_abs_le {f v : ℝ → ℝ} {l : Filter ℝ}
    (hv : Filter.Tendsto v l (𝓝 0)) (h : ∀ᶠ θ in l, |f θ| ≤ |v θ|) :
    Filter.Tendsto f l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hv ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv
    (Eventually.of_forall fun θ => norm_nonneg _) ?_
  filter_upwards [h] with θ hθ
  simpa only [Real.norm_eq_abs] using hθ

/-- An eventually bounded factor times a vanishing one vanishes (commuted form). -/
theorem tendsto_mul_comm_of_eventually_bounded {f g : ℝ → ℝ} {l : Filter ℝ} {C : ℝ}
    (hf : Filter.Tendsto f l (𝓝 0)) (hg : ∀ᶠ θ in l, |g θ| ≤ C) :
    Filter.Tendsto (fun θ => g θ * f θ) l (𝓝 0) := by
  simpa only [mul_comm] using tendsto_mul_of_eventually_bounded hf hg

/-- `c2m θ = cos 2θ - sin²θ` is bounded by `2`. -/
theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  have ha : |Real.cos (2 * θ)| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hb : |Real.sin θ ^ 2| ≤ 1 := by
    have h : |Real.sin θ| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith [h, abs_nonneg (Real.sin θ)]
  calc |Work.Construction.c2m θ| = |Real.cos (2 * θ) - Real.sin θ ^ 2| := rfl
    _ ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
        simpa only [abs_neg, sub_eq_add_neg] using abs_add_le (Real.cos (2 * θ)) (-(Real.sin θ ^ 2))
    _ ≤ 2 := by linarith


end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.STC.hasDerivAt_L12_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_z L₁₂(f)(z) = - L12dens (f)(z)` for a `C⁴` datum in `ℋ⁴`

This module proves `hasDerivAt_L12_C4`: for `0 < α ≤ 1`, a datum `f` which is `C⁴` on the
*open* quadrant `Q0 = (0,∞) × (0,π/2)` and honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`, i.e.
weighted integrability on the quadrant, with **no** boundary-traces and **no** decay), the
fundamental-model operator

  `Work.Construction.L12 f z = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`

is differentiable at every `z > 0`, with derivative `- L12dens f z`.

## Route

The two analytic inputs are completely independent.

* **Integrability** of the density on `(0,∞)` follows from continuity of `f` on the open quadrant
  and `HkMem α 4 f` alone
  (`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn`: Cauchy–Schwarz in
  `θ` against `K ∈ L²` together with the pointwise domination
  `(f s θ)² ≤ HkIntegrand α 4 f s θ / w(s)²`, then AM–GM against the two integrable pieces
  `(s/(1+s)²)²` and `s ↦ ∫_θ HkIntegrand α 4 f s θ`).

* **Continuity** of the density at `z > 0` (`L12dens_continuousAt_C4` below) is a dominated
  convergence statement: on `Iθ` the integrand `(f s θ/s)·K(θ)` converges pointwise to its value
  at `s = z` (continuity of `f` on the open quadrant, the two endpoints being null) and is
  dominated by the constant `C·|f|_{ℋ⁴}·K(θ)`, where `C` is the trace-free pointwise bound
  `|f s θ| ≤ C·min s 1·|f|_{ℋ⁴}` of `Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min` — the
  `ℋ⁴ → L^∞` trade-off, which needs no boundary traces because it replaces the angular and
  radial Hardy inequalities by a mean-value and an Agmon-type localisation argument.

The fundamental theorem of calculus for the tail integral `∫_z^∞ g`
(`Work.FM.hasDerivAt_L12`) then finishes the proof, since `L₁₂` is the tail integral of its
density.

All declarations in this file rest on `[propext, Classical.choice, Quot.sound]` only.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real

namespace Work.FTS_RegExport.RXT.STC

/-- **Continuity of the `L₁₂`-density of a `C⁴` datum in `ℋ⁴`.**

For `0 < α ≤ 1` and `f` which is `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` and honestly
in `ℋ⁴`, the density `s ↦ ∫_θ K(θ) f(s,θ)/s` is continuous at every `z > 0`.

The only quantitative input is the trace-free pointwise bound
`|f s θ| ≤ C · min s 1 · |f|_{ℋ⁴}` (`v2_hkMem_pointwise_min`), which turns the pointwise
convergence of the integrand into a uniform domination by the integrable function
`C·|f|_{ℋ⁴}·K(·)` on `Iθ`. -/
theorem L12dens_continuousAt_C4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    ContinuousAt (Work.Construction.L12dens f) z := by
  -- the trace-free `ℋ⁴ → L^∞` trade-off
  obtain ⟨C, hC0, hCbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  have hfc : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.continuousOn
  have hCN : 0 ≤ C * Work.Spaces.HkNorm α 4 f :=
    mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hpt : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < π / 2 →
      |f s θ| ≤ C * min s 1 * Work.Spaces.HkNorm α 4 f := by
    intro s θ hs hθ0 hθ1
    exact hCbd f hf hmem 0 0 (by norm_num) s θ hs hθ0 hθ1
  -- the angular weight is continuous
  have hKIθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ := by
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact Work.Elliptic.continuous_ktheta.continuousOn
  have hKIoo : ContinuousOn Work.Spaces.K (Set.Ioo 0 (π / 2)) :=
    hKIθ.mono Set.Ioo_subset_Icc_self
  -- a.e. strong measurability of the integrand for `s` near `z`
  have hG_meas : ∀ᶠ s in 𝓝 z, AEStronglyMeasurable
      (fun θ : ℝ => f s θ / s * Work.Spaces.K θ) (volume.restrict (Set.Ioo 0 (π / 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    have hslice : ContinuousOn (fun θ : ℝ => f s θ) (Set.Ioo 0 (π / 2)) :=
      hfc.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hs, hθ⟩)
    exact ((hslice.div_const s).mul hKIoo).aestronglyMeasurable measurableSet_Ioo
  -- the uniform domination `|f s θ / s| ≤ C·|f|_{ℋ⁴}` for `0 < s` and a.e. `θ`
  have hbound : ∀ᶠ s in 𝓝 z, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ‖f s θ / s‖ ≤ C * Work.Spaces.HkNorm α 4 f := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hle : |f s θ| ≤ C * s * Work.Spaces.HkNorm α 4 f := by
      have h1 := hpt s θ hs hθ.1 hθ.2
      calc |f s θ| ≤ C * min s 1 * Work.Spaces.HkNorm α 4 f := h1
        _ = (C * Work.Spaces.HkNorm α 4 f) * min s 1 := by ring
        _ ≤ (C * Work.Spaces.HkNorm α 4 f) * s :=
            mul_le_mul_of_nonneg_left (min_le_left s 1) hCN
        _ = C * s * Work.Spaces.HkNorm α 4 f := by ring
    have hsabs : |s| = s := abs_of_pos hs
    have hnabs : ‖f s θ / s‖ = |f s θ| / s := by
      rw [Real.norm_eq_abs, abs_div, hsabs]
    rw [hnabs, div_le_iff₀ hs]
    have hrr : C * s * Work.Spaces.HkNorm α 4 f
        = (C * Work.Spaces.HkNorm α 4 f) * s := by ring
    rw [← hrr]
    exact hle
  -- pointwise convergence on the interior of `Iθ`
  have hcont : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ContinuousAt (fun s : ℝ => f s θ / s) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
    have hfat : ContinuousAt (Function.uncurry f) (z, θ) :=
      hfc.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hθQ)
    have h2 : ContinuousAt (fun s : ℝ => (s, θ)) z :=
      (Continuous.prodMk continuous_id continuous_const).continuousAt
    have hsl : ContinuousAt (fun s : ℝ => Function.uncurry f (s, θ)) z :=
      hfat.comp (x := z) (f := fun s : ℝ => (s, θ)) h2
    have hsl' : ContinuousAt (fun s : ℝ => f s θ) z := by
      simpa only [Function.uncurry_apply_pair] using hsl
    exact hsl'.div continuousAt_id (ne_of_gt hz)
  have hmain := Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
      (G := fun s θ => f s θ / s) (φ := Work.Spaces.K) (z₀ := z)
      (K := C * Work.Spaces.HkNorm α 4 f) hCN hKIθ hG_meas hbound hcont
  -- the two integrals agree: `Icc 0 (π/2)` and `Ioo 0 (π/2)` differ by a null set
  have hmeas_eq : volume.restrict (Set.Icc (0 : ℝ) (π / 2))
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  have hfun : Work.Construction.L12dens f
      = fun s => ∫ θ, f s θ / s * Work.Spaces.K θ
          ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    funext s
    show (∫ θ in Set.Icc (0 : ℝ) (π / 2), Work.Spaces.K θ * f s θ / s)
        = ∫ θ, f s θ / s * Work.Spaces.K θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))
    rw [hmeas_eq]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  rw [hfun]
  exact hmain

theorem hasDerivAt_L12_C4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Construction.L12 f z') (-(Work.Construction.L12dens f z)) z := by
  have hcontOn : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.continuousOn
  have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcontOn hmem
  have hcontAt : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    L12dens_continuousAt_C4 hα hα1 hf hmem hz
  exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) hint hcontAt hz

end Work.FTS_RegExport.RXT.STC
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.hkMem_pointwise_min =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.hkMem_pointwise_min`

Pointwise bound for the mixed slots of order `≤ 2` of a datum which is `C⁴` on the *open*
quadrant and honestly in `ℋ⁴`, with the exact weight `min z 1` and **no** boundary-trace
hypothesis:

  `|D_z^b D_θ^a f z θ| ≤ C · min z 1 · |f|_{ℋ⁴}`  for `a + b ≤ 2`, `z > 0`, `0 < θ < π/2`.

This is the sharpened form of the paper's `SecondDerivativesBounded` (`10/√(γ-1)·|f|_{ℋ⁴}`):
the extra factor `min z 1` measures the localisation in the radial variable and reflects the
fact that only `HkMem α 4` (integrability over the quadrant) is available, with no decay at
`z = ∞` and no vanishing at `θ = 0, π/2`.

The proof is the squared estimate `Work.FTS_RegExport.RXT.hkMem_pointwise_min_sq` followed by
elementary square-root algebra.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- **The pointwise bound.** -/
theorem hkMem_pointwise_min {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by linarith [Work.Spaces.one_lt_gam hα]
  refine ⟨Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40),
    Real.sqrt_nonneg _, ?_⟩
  intro f h4 hmem b a hab z θ hz hθ0 hθ1
  have hC0 : (0 : ℝ) ≤ ((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40 := by
    positivity
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hsq := hkMem_pointwise_min_sq (α := α) hα hα1 h4 hmem hab hz hθ0 hθ1
  calc |Work.Spaces.mixed b a f z θ|
      = Real.sqrt ((Work.Spaces.mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40
          * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
          * min z 1 * Work.Spaces.HkNorm α 4 f := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC0, Real.sqrt_sq hmin]
        rfl

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.theta_holder_of_HkMem` — `ℋ⁴` membership gives a uniform `θ`-Hölder modulus

The trace-free leaf **A3** of `THL.Leaves`: for `0 < β ≤ 1`, a function `f` which is `C⁴` on the
open quadrant `Q0 = (0,∞) × (0,π/2)` and honestly in the weighted space `ℋ⁴` is `θ`-Hölder of
exponent `(γ-1)/2 = β/20` (with `γ = gam β = 1 + β/10`), uniformly in `z > 0`:

  `|f(z,θ) - f(z,θ')| ≤ C · min(z,1) · |f|_{ℋ⁴} · |θ - θ'|^{(γ-1)/2}`.

**Route.**  For `0 < a ≤ b < π/2`, the fundamental theorem of calculus for the `θ`-slice gives
`f(z,b) - f(z,a) = ∫_a^b ∂_θ f(z,σ) dσ`; writing `∂_θ f = D_θ f / sin(2σ)` and splitting the
integrand into the two factors

  `A₁ σ = sin(2σ)^{-γ/2} · D_θ f(z,σ)`,  `A₂ σ = sin(2σ)^{(γ-2)/2}`

the interval Cauchy–Schwarz `Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` gives

  `|f(z,b) - f(z,a)|² ≤ (∫_a^b A₁²)(∫_a^b A₂²)`.

The first factor is bounded by the trace-free angular `L²` estimate `angular_L2_noTrace`
(`∫_{Iθ} sin(2σ)^{-γ}(D_θf)² ≤ 5 z³/(1+z)⁴ |f|²_{ℋ⁴}`, monotone in the interval), the second by
the one-variable bound `integral_sin_two_rpow_le` with `p = γ-1 = β/10`.  Extracting square roots
and using `√(z³/(1+z)⁴) ≤ min(z,1)` and `√(2(π/4)^{1-β/10}·10/β) ≤ 10/β + 1` gives the claim with
the explicit constant `C = √5 · (10/β + 1)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.THL

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary angular facts -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos_of_mem_Ioo' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on the closed angular interval `Iθ`. -/
private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## Monotonicity of the interval integral against the set integral over `Iθ` -/

/-- For `0 < a ≤ b < π/2` the interval `[a,b]` sits inside `Iθ`, so the integral of a
nonnegative integrable function over `[a,b]` is at most its integral over `Iθ`. -/
private lemma interval_integral_le_setIntegral_Iθ' {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < Real.pi / 2) (hint : IntegrableOn F Work.Spaces.Iθ)
    (hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Work.Spaces.Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-! ## The radial factor `√(z³/(1+z)⁴) ≤ min(z,1)` -/

private lemma sqrt_z_cube_div_le_min {z : ℝ} (hz : 0 < z) :
    Real.sqrt (z ^ 3 / (1 + z) ^ 4) ≤ min z 1 := by
  have hnn : 0 ≤ min z 1 := le_min hz.le zero_le_one
  refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq hnn))
  rcases le_or_gt z 1 with h | h
  · rw [min_eq_left h, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 4)]
    have h32 : z ^ 3 ≤ z ^ 2 := by
      rw [show z ^ 3 = z ^ 2 * z by ring]
      exact mul_le_of_le_one_right (sq_nonneg z) h
    have h4 : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h4 (sq_nonneg z)
    linarith [h32, h2]
  · rw [min_eq_right h.le, one_pow, div_le_one (by positivity : (0:ℝ) < (1 + z) ^ 4)]
    have h34 : z ^ 3 ≤ z ^ 4 := by nlinarith [h, pow_pos hz 3]
    have h4 : z ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ hz.le (by linarith) 4
    linarith

/-! ## The main estimate -/

theorem theta_holder_of_HkMem {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 → Work.Spaces.HkMem β 4 f →
      ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |f z θ - f z θ'|
          ≤ C * min z 1 * Work.Spaces.HkNorm β 4 f *
            |θ - θ'| ^ ((Work.Spaces.gam β - 1) / 2) := by
  have hgam : Work.Spaces.gam β - 1 = β / 10 := Work.Spaces.gam_sub_one β
  have hpi4pos : (0 : ℝ) < Real.pi / 4 := by positivity
  have hpi4le : Real.pi / 4 ≤ 1 := by nlinarith [Real.pi_lt_four]
  refine ⟨Real.sqrt 5 * (10 / β + 1), by positivity, ?_⟩
  intro f h4 hmem z hz θ hθ θ' hθ'
  -- ### the angular `L²` input (leaf A2)
  obtain ⟨hintL2, hboundL2⟩ := angular_L2_noTrace hβ hβ1 h4 hmem hz
  -- ### the scalar bound `√(2(π/4)^{1-β/10}·10/β) ≤ 10/β + 1`
  have hSle : Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)) ≤ 10 / β + 1 := by
    have hnn : (0 : ℝ) ≤ 10 / β + 1 := by positivity
    rw [Real.sqrt_le_iff]
    refine ⟨hnn, ?_⟩
    have hpow : (Real.pi / 4) ^ (1 - β / 10) ≤ 1 :=
      Real.rpow_le_one hpi4pos.le hpi4le (by linarith)
    have h10 : (0 : ℝ) ≤ 10 / β := by positivity
    nlinarith [hpow, h10, hnn]
  -- ### the estimate for `a ≤ b`
  have key : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      |f z a - f z b|
        ≤ Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
    intro a b ha hab hb
    have hban : 0 ≤ b - a := by linarith
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hab]
      exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    -- (0) the slice derivative and the fundamental theorem of calculus
    have hslice_cd : ContDiffOn ℝ 1 (fun s => f z s) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 0 0 1 (by norm_num) hz
    have hderiv : ∀ σ ∈ Set.uIcc a b,
        HasDerivAt (fun s => f z s) (Work.Spaces.pth f z σ) σ := fun σ hσ =>
      ((hslice_cd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub hσ))).hasDerivAt
    have hpthcont : ContinuousOn (fun s => Work.Spaces.pth f z s) (Set.uIcc a b) :=
      (Work.FTS_RegExport.RXT.Slots.continuousOn_pth_mixed_slice_aux h4 0 0 (by norm_num)
        hz).mono hsub
    have hFTC : ∫ s in a..b, Work.Spaces.pth f z s = f z b - f z a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hpthcont.intervalIntegrable
    -- (1) the two factors and their continuity
    set A1 : ℝ → ℝ := fun σ =>
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2)) * Work.Spaces.mixed 0 1 f z σ with hA1
    set A2 : ℝ → ℝ := fun σ => (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2) with hA2
    have hsincont : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.uIcc a b) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hmixcont : ContinuousOn (fun σ => Work.Spaces.mixed 0 1 f z σ) (Set.uIcc a b) :=
      (Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 0 1 0 (by norm_num) hz).continuousOn.mono
        hsub
    have hA1cont : ContinuousOn A1 (Set.uIcc a b) := by
      rw [hA1]
      exact (hsincont.rpow_const fun σ hσ =>
        Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo' (hsub hσ)))).mul hmixcont
    have hA2cont : ContinuousOn A2 (Set.uIcc a b) := by
      rw [hA2]
      exact hsincont.rpow_const fun σ hσ =>
        Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo' (hsub hσ)))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab hA1cont hA2cont
    -- (2) the two squared integrals, evaluated
    have hA1sq : (∫ σ in a..b, (A1 σ) ^ 2)
        = ∫ σ in a..b, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
            * (Work.Spaces.mixed 0 1 f z σ) ^ 2 := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hspos : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo' (hsub hσ)
      simp only [hA1]
      rw [mul_pow, pow_two, ← Real.rpow_add hspos,
        show -(Work.Spaces.gam β / 2) + -(Work.Spaces.gam β / 2) = -(Work.Spaces.gam β) by ring]
    have hA2sq : (∫ σ in a..b, (A2 σ) ^ 2)
        = ∫ σ in a..b, (Real.sin (2 * σ)) ^ (Work.Spaces.gam β - 2) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hspos : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo' (hsub hσ)
      simp only [hA2]
      rw [pow_two, ← Real.rpow_add hspos,
        show (Work.Spaces.gam β - 2) / 2 + (Work.Spaces.gam β - 2) / 2
          = Work.Spaces.gam β - 2 by ring]
    -- (3) the two square-root bounds
    have hb1 : Real.sqrt (∫ σ in a..b, (A1 σ) ^ 2)
        ≤ Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hA1sq]
      exact le_trans (interval_integral_le_setIntegral_Iθ' ha hab hb hintL2 fun x hx =>
        mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ' hx) _) (sq_nonneg _)) hboundL2
    have hb2 : Real.sqrt (∫ σ in a..b, (A2 σ) ^ 2)
        ≤ Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10)) := by
      rw [hA2sq]
      have h1 : ∫ σ in a..b, (Real.sin (2 * σ)) ^ (Work.Spaces.gam β - 2)
          ≤ 2 * (Real.pi / 4) ^ (1 - β / 10) / (β / 10) * (b - a) ^ (β / 10) := by
        have hp : (0 : ℝ) < β / 10 := by linarith
        have hp1 : β / 10 ≤ 1 := by linarith
        have h := integral_sin_two_rpow_le (p := β / 10) hp hp1 ha hab hb
        rwa [show β / 10 - 1 = Work.Spaces.gam β - 2 by rw [← hgam]; ring] at h
      refine le_trans (Real.sqrt_le_sqrt h1) (le_of_eq ?_)
      congr 1
      rw [div_eq_mul_inv, inv_div]
    -- (4) the product identity
    have hprod : ∫ σ in a..b, A1 σ * A2 σ = f z b - f z a := by
      rw [← hFTC]
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hspos : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo' (hsub hσ)
      have hpow : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2))
          * (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2) * Real.sin (2 * σ) = 1 := by
        rw [← Real.rpow_add hspos, ← Real.rpow_add_one hspos.ne',
          show -(Work.Spaces.gam β / 2) + ((Work.Spaces.gam β - 2) / 2) + 1 = 0 by ring,
          Real.rpow_zero]
      simp only [hA1, hA2]
      rw [show Work.Spaces.mixed 0 1 f z σ
            = Real.sin (2 * σ) * Work.Spaces.pth f z σ from rfl]
      calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2))
            * (Real.sin (2 * σ) * Work.Spaces.pth f z σ)
            * (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2)
          = ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2))
              * (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2) * Real.sin (2 * σ))
            * Work.Spaces.pth f z σ := by ring
        _ = 1 * Work.Spaces.pth f z σ := by rw [hpow]
        _ = Work.Spaces.pth f z σ := one_mul _
    -- (5) the middle estimate
    have hmid : Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
          * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10))
        ≤ Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
          * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
      have hCnn : (0 : ℝ) ≤ 2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) := by positivity
      have hsq : Real.sqrt ((b - a) ^ (β / 10)) = (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hban, hgam,
          show β / 10 * (1 / 2) = β / 10 / 2 by ring]
      have hfac : Real.sqrt 5 * Real.sqrt (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
          ≤ Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (sqrt_z_cube_div_le_min hz) (Real.sqrt_nonneg 5))
            (Work.Spaces.HkNorm_nonneg β 4 f))
          (Real.sqrt_nonneg _)
      calc Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10))
          = (Real.sqrt 5 * Real.sqrt (z ^ 3 / (1 + z) ^ 4)
              * Real.sqrt (Work.Spaces.HkSq β 4 f)
              * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 5 * (z ^ 3 / (1 + z) ^ 4)),
              Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_mul hCnn, hsq]
            ring
        _ ≤ (Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
              * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) :=
            mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hban _)
    -- (6) the constant
    have hconst : Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
          * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)
        ≤ Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
      have hM : (0 : ℝ) ≤ min z 1 * Work.Spaces.HkNorm β 4 f
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) :=
        mul_nonneg (mul_nonneg (le_min hz.le zero_le_one)
          (Work.Spaces.HkNorm_nonneg β 4 f)) (Real.rpow_nonneg hban _)
      rw [show Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)
          = (Real.sqrt 5 * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)))
            * (min z 1 * Work.Spaces.HkNorm β 4 f
              * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)) by ring,
        show Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)
          = (Real.sqrt 5 * (10 / β + 1))
            * (min z 1 * Work.Spaces.HkNorm β 4 f
              * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)) by ring]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSle (Real.sqrt_nonneg 5)) hM
    -- ### assemble
    calc |f z a - f z b| = |f z b - f z a| := abs_sub_comm _ _
      _ = |∫ σ in a..b, A1 σ * A2 σ| := by rw [hprod]
      _ ≤ Real.sqrt (∫ σ in a..b, (A1 σ) ^ 2) * Real.sqrt (∫ σ in a..b, (A2 σ) ^ 2) := hcs
      _ ≤ Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10)) :=
          mul_le_mul hb1 hb2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := hmid
      _ ≤ Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := hconst
  -- ### symmetry in the two angles
  rcases le_or_gt θ θ' with h | h
  · have hk := key θ θ' hθ.1 h hθ'.2
    have h1 : |θ - θ'| ^ ((Work.Spaces.gam β - 1) / 2)
        = (θ' - θ) ^ ((Work.Spaces.gam β - 1) / 2) := by
      rw [abs_sub_comm θ θ', abs_of_nonneg (sub_nonneg.mpr h)]
    rw [h1]
    exact hk
  · have hk := key θ' θ hθ'.1 h.le hθ.2
    have h1 : |f z θ - f z θ'| = |f z θ' - f z θ| := abs_sub_comm _ _
    have h2 : |θ - θ'| ^ ((Work.Spaces.gam β - 1) / 2)
        = (θ - θ') ^ ((Work.Spaces.gam β - 1) / 2) := by
      rw [abs_of_nonneg (sub_nonneg.mpr h.le)]
    rw [h1, h2]
    exact hk

end Work.FTS_RegExport.THL
end
end
