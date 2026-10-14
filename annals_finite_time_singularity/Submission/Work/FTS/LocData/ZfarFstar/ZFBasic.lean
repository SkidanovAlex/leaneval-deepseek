import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.HkSqZfar
-- ===== merged: Submission.Work.ConstructionInstance.ConcreteData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- The zero perturbation of the profile. -/
def gZero : ℝ → ℝ → ℝ := fun _ _ => 0

/-- The modulation `λ̄(t) = (1-t)/2` of the inhabited `ModulatedData` instance (`T = 1`).
(This is *not* the modulation of the `ProfileData` inhabitant, which is `λ̄(t) = 1 - t/2` with
`T = 2`.) -/
def lamZero : ℝ → ℝ := fun t => (1 - t) / 2



@[simp] theorem gZero_apply (z θ : ℝ) : gZero z θ = 0 := rfl

@[simp] theorem lamZero_apply (t : ℝ) : lamZero t = (1 - t) / 2 := rfl


/-- `∂_z` of the zero perturbation vanishes. -/
@[simp] theorem pz_gZero (z θ : ℝ) : Work.Spaces.pz gZero z θ = 0 := by
  simp [Work.Spaces.pz, gZero]










end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.SlotIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/slotIntegrable`: integrability of a single mixed slot

For `f` of class `C^∞` on the open quadrant which is honestly in `ℋ^k`, every mixed slot
`(D_z^j D_θ^i f · W)²` with `1 ≤ i` and `i + j ≤ k` is integrable on every angular slice
`Iθ` (`z ∈ Iz`) and its `θ`-integral is integrable on `Iz`.

The `z`-part is `Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq`; the
`θ`-slice part is proved here, by domination by the `ℋ^k`-integrand
(`Work.Spaces.sq_le_HkIntegrand_mixed`) together with the a.e. strong measurability coming
from the joint continuity of the slot on the open quadrant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The weight `W = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    rw [Set.mem_prod] at hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-- **Integrability of a single mixed slot.**  For `f` of class `C^∞` on the open quadrant
and honestly in `ℋ^k`, and a slot with `1 ≤ i`, `i + j ≤ k`, the slot square
`θ ↦ (D_z^j D_θ^i f · W)²` is integrable on `Iθ` for every `z ∈ Iz`, and its `θ`-integral is
integrable on `Iz`. -/
theorem slotIntegrable (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz := by
  refine ⟨?_, Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq α k hf hmem j i
    hi hij⟩
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
  · -- at `z = 0` the radial weight vanishes and the slot is identically zero
    have hzero : (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← h0]
      simp [Work.Spaces.Wt, Work.Spaces.w]
    rw [hzero]
    exact integrableOn_zero
  · -- for `z > 0`: domination by the `ℋ^k`-integrand of `f`
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hf.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
    refine Integrable.mono' (hmem.1 z hz) haesm ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from
      by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij

end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.LocData.ZfarFstar.ZFBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData
namespace ZF

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary angular fact -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## 2. `D_θ` of a factor independent of `θ` -/

/-- `D_θ` is a derivation vanishing on functions of `z` alone, so a `θ`-independent factor passes
through `D_θ` (and all its iterates). -/
theorem DthIter_mul_left_z (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-! ## 3. `D_z` of a factor independent of `z` -/


/-! ## 4. Smoothness of the `z`-slices -/

theorem contDiffOn_slice_oneSubChi (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / L)) (Set.Ioi (-1)) :=
  (contDiff_const.sub (Work.Stability.chi_contDiff.comp (contDiff_id.div_const L))).contDiffOn

theorem contDiffOn_slice_FM_Fstar :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  have heq : (fun z : ℝ => Work.FM.Fstar z)
      = (fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2) := rfl
  rw [heq]
  exact h

theorem contDiffOn_slice_Fstar (α : ℝ) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Construction.Fstar α z θ)
      (Set.Ioi (-1)) := by
  have hc : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) (Set.Ioi (-1)) :=
    contDiffOn_const
  have h := hc.mul contDiffOn_slice_FM_Fstar
  refine h.congr (fun z _ => ?_)
  rw [Work.Construction.Fstar]


/-! ## 5. A crude bound on the angular polynomials `Pf` -/

/-- **Crude bound on the angular polynomials.**  For `i ≤ 4`, `u ∈ [-1,1]` and `α ∈ [0,1]`,
`|Pf i u α| ≤ 200`.  The sharp constants of `Pf_bounds`/`Pf_bounds_half` are not needed: only
finiteness of the constant matters for the majorant. -/
theorem Pf_abs_le (i : ℕ) (hi : i ≤ 4) {u α : ℝ} (hu : -1 ≤ u) (hu1 : u ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |Pf i u α| ≤ 200 := by
  have hu' : |u| ≤ 1 := abs_le.mpr ⟨hu, hu1⟩
  have ht : |u - 1 / 3| ≤ 4 / 3 := by rw [abs_le]; constructor <;> linarith
  have h1u2 : |1 - u ^ 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have h13u2 : |1 - 3 * u ^ 2| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have huP : |u * (1 - u ^ 2)| ≤ 1 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul hu' h1u2 (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have htP : |(u - 1 / 3) * (1 - u ^ 2)| ≤ 4 / 3 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul ht h1u2 (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hA : |(1 - u ^ 2) * (1 - 3 * u ^ 2)| ≤ 2 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul h1u2 h13u2 (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hB : |(1 - u ^ 2) ^ 2| ≤ 1 := by
    rw [abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) h1u2 2) ?_
    norm_num
  have hC : |u * (u - 1 / 3) * (1 - u ^ 2)| ≤ 4 / 3 := by
    rw [abs_mul, abs_mul]
    refine le_trans (mul_le_mul (mul_le_mul hu' ht (abs_nonneg _) (by norm_num)) h1u2
      (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hD : |(u - 1 / 3) ^ 2 * (1 - u ^ 2)| ≤ 16 / 9 := by
    rw [abs_mul, abs_pow]
    refine le_trans (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ht 2) h1u2
      (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hE3 : |(u - 1 / 3) ^ 3| ≤ 64 / 27 := by
    rw [abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) ht 3) ?_
    norm_num
  have hE4 : |(u - 1 / 3) ^ 4| ≤ 256 / 81 := by
    rw [abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) ht 4) ?_
    norm_num
  have h2 : |(-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9| ≤ 2 := by
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1u2
    obtain ⟨hta, htb⟩ := abs_le.mp ht
    have hq : (3 * u - 1) ^ 2 = 9 * (u - 1 / 3) ^ 2 := by ring
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (u - 1 / 3), sq_nonneg (3 * u - 1)]
    · nlinarith [sq_nonneg (u - 1 / 3), sq_nonneg (3 * u - 1), hα0, hα1]
  have h3 : |(-8) * u * (1 - u ^ 2) - 6 * α * (u - 1 / 3) * (1 - u ^ 2)
      + α ^ 2 * (u - 1 / 3) ^ 3| ≤ 19 := by
    rw [abs_le] at huP htP hE3 ⊢
    constructor <;> nlinarith [hα0, hα1]
  have h4 : |16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * α * (1 - u ^ 2) ^ 2
      - 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * α ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + α ^ 3 * (u - 1 / 3) ^ 4| ≤ 150 := by
    obtain ⟨hAa, hAb⟩ := abs_le.mp hA
    obtain ⟨hBa, hBb⟩ := abs_le.mp hB
    obtain ⟨hCa, hCb⟩ := abs_le.mp hC
    obtain ⟨hDa, hDb⟩ := abs_le.mp hD
    obtain ⟨hEa, hEb⟩ := abs_le.mp hE4
    have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
    have hα3 : 0 ≤ α ^ 3 := by positivity
    have hα3le : α ^ 3 ≤ 1 := by nlinarith [hα0, hα1]
    have hl1 : -(32 : ℝ) ≤ 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)) := by nlinarith [hAa]
    have hl2 : -(12 : ℝ) ≤ 12 * α * (1 - u ^ 2) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hBa hα0
      nlinarith [h, hα1]
    have hl3 : 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) ≤ 128 / 3 := by
      have h1 : α * (u * (u - 1 / 3) * (1 - u ^ 2)) ≤ 4 / 3 := by
        have h := mul_le_mul_of_nonneg_left hCb hα0
        nlinarith [h, hα1]
      nlinarith [h1]
    have hl4 : 12 * α ^ 2 * ((u - 1 / 3) ^ 2 * (1 - u ^ 2)) ≤ 64 / 3 := by
      have h := mul_le_mul_of_nonneg_left hDb (sq_nonneg α)
      nlinarith [h, hα2]
    have hl5 : -(256 : ℝ) / 81 ≤ α ^ 3 * (u - 1 / 3) ^ 4 := by
      have h := mul_le_mul_of_nonneg_left hEa hα3
      nlinarith [h, hα3le]
    have hu1 : 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)) ≤ 32 := by nlinarith [hAb]
    have hu2 : 12 * α * (1 - u ^ 2) ^ 2 ≤ 12 := by
      have h := mul_le_mul_of_nonneg_left hBb hα0
      nlinarith [h, hα1]
    have hu3 : -(128 : ℝ) / 3 ≤ 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) := by
      have h1 : -(4 : ℝ) / 3 ≤ α * (u * (u - 1 / 3) * (1 - u ^ 2)) := by
        have h := mul_le_mul_of_nonneg_left hCa hα0
        nlinarith [h]
      nlinarith [h1]
    have hu4 : -(64 : ℝ) / 3 ≤ 12 * α ^ 2 * ((u - 1 / 3) ^ 2 * (1 - u ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hDa (sq_nonneg α)
      nlinarith [h]
    have hu5 : α ^ 3 * (u - 1 / 3) ^ 4 ≤ 256 / 81 := by
      have h := mul_le_mul_of_nonneg_left hEb hα3
      nlinarith [h, hα3le]
    rw [abs_le]
    constructor <;> nlinarith [hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5]
  interval_cases i
  · rw [Pf_zero]; norm_num
  · rw [Pf_one, abs_mul, abs_of_nonneg hα0]
    have h : |(3 * u - 1) / 3| ≤ 4 / 3 := by
      rw [show (3 * u - 1) / 3 = u - 1 / 3 by ring]; exact ht
    nlinarith [abs_nonneg ((3 * u - 1) / 3)]
  · rw [Pf_two, abs_mul, abs_of_nonneg hα0]
    nlinarith [abs_nonneg ((-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9)]
  · rw [Pf_three, abs_mul, abs_of_nonneg hα0]
    nlinarith [abs_nonneg ((-8) * u * (1 - u ^ 2) - 6 * α * (u - 1 / 3) * (1 - u ^ 2)
      + α ^ 2 * (u - 1 / 3) ^ 3)]
  · rw [Pf_four, abs_mul, abs_of_nonneg hα0]
    nlinarith [abs_nonneg (16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * α * (1 - u ^ 2) ^ 2
      - 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * α ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + α ^ 3 * (u - 1 / 3) ^ 4)]

/-! ## 6. Pointwise bounds for the weighted derivatives of `F_*` -/

/-- `|D_z^a F_* · w| ≤ (10/3)·α·Γ/z` for `z ≥ 1`: `D_z^a F_* = (α/c)·Γ·Φ_a` and
`|w·Φ_a| ≤ 2/z` (`Phi_w_le`), with `1/c ≤ 5/3`. -/
theorem DzIter_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 10 * α * Work.Spaces.Gam α θ / (3 * z) := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi := Phi_w_le a ha hz1 θ
  have heq : Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
          * Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ :=
    congrFun (congrFun (DzIter_Fstar_eq α a) z) θ
  rw [heq, PhiZ_eq a ha z θ]
  have hsplit : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
        * Work.FTS.LocData.Phi a z θ * Work.Spaces.w z
      = ((α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
          * (Work.Spaces.w z * Work.FTS.LocData.Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have h1 : |(α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ :=
    abs_of_nonneg (by positivity)
  rw [h1]
  have h2 : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
        * |Work.Spaces.w z * Work.FTS.LocData.Phi a z θ|
      ≤ (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z) :=
    mul_le_mul_of_nonneg_left hPhi (by positivity)
  refine le_trans h2 ?_
  have hcInv : (Work.Spaces.c α)⁻¹ ≤ (5 : ℝ) / 3 := by
    have h0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 5) hc
    rw [one_div] at h0
    norm_num at h0
    exact h0
  have hA : 0 ≤ α * Work.Spaces.Gam α θ := mul_nonneg hα.le hG0
  have hstep : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z)
      = (α * Work.Spaces.Gam α θ) * (2 * ((Work.Spaces.c α)⁻¹ * z⁻¹)) := by ring
  rw [hstep]
  have h2' : (α * Work.Spaces.Gam α θ) * (2 * ((Work.Spaces.c α)⁻¹ * z⁻¹))
      ≤ (α * Work.Spaces.Gam α θ) * (2 * ((5 : ℝ) / 3 * z⁻¹)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_right hcInv (by positivity)
  refine le_trans h2' ?_
  have hzne : z ≠ 0 := ne_of_gt hz
  refine le_of_eq ?_
  field_simp
  ring

/-- `|mixed_a^i F_* · w| ≤ 200·(10/3)·α·Γ/z` for `z ≥ 1`, `i ≤ 4`: `mixed_a^i F_*` is
`(α/c)·D_θ^iΓ(0,θ)·Φ_a` and `|D_θ^iΓ(0,θ)| ≤ 200·Γ`, `|w·Φ_a| ≤ 2/z`. -/
theorem mixed_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a i : ℕ} (ha : a ≤ 4) (hi : i ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 200 * (10 * α * Work.Spaces.Gam α θ / (3 * z)) := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi := Phi_w_le a ha hz1 θ
  have hgam : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := DthIter_Gam_Pf α i hi 0 θ hθ
  have hPf : |Pf i (Real.cos (2 * θ)) α| ≤ 200 :=
    Pf_abs_le i hi (Real.neg_one_le_cos _) (Real.cos_le_one _) hα.le hα1
  have heq : Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)
          * Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ := by
    have h := congrFun (congrFun (mixed_Fstar_eq α i a) z) θ
    rw [h, hgam]
  rw [heq, PhiZ_eq a ha z θ]
  have hsplit : (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)
        * Work.FTS.LocData.Phi a z θ * Work.Spaces.w z
      = ((α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α))
          * (Work.Spaces.w z * Work.FTS.LocData.Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have h1 : |(α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)| ≤
      (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * 200) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α / Work.Spaces.c α)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul_of_nonneg_left hPf hG0
  have h2 : |(α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)|
        * |Work.Spaces.w z * Work.FTS.LocData.Phi a z θ|
      ≤ ((α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * 200)) * (2 / z) :=
    mul_le_mul h1 hPhi (abs_nonneg _) (by positivity)
  refine le_trans h2 ?_
  have hcInv : (Work.Spaces.c α)⁻¹ ≤ (5 : ℝ) / 3 := by
    have h0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 5) hc
    rw [one_div] at h0
    norm_num at h0
    exact h0
  have hA : 0 ≤ α * Work.Spaces.Gam α θ := mul_nonneg hα.le hG0
  have hstep : (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * 200) * (2 / z)
      = ((α * Work.Spaces.Gam α θ) * 400) * ((Work.Spaces.c α)⁻¹ * z⁻¹) := by ring
  rw [hstep]
  have h2' : ((α * Work.Spaces.Gam α θ) * 400) * ((Work.Spaces.c α)⁻¹ * z⁻¹)
      ≤ ((α * Work.Spaces.Gam α θ) * 400) * ((5 : ℝ) / 3 * z⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hcInv (by positivity)
  refine le_trans h2' ?_
  have hzne : z ≠ 0 := ne_of_gt hz
  refine le_of_eq ?_
  field_simp
  ring

end ZF
end Work.FTS.LocData
end
end
