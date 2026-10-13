import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.R1G.AnG
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.R1G.gA_Zit_mul_w_abs_le
import Submission.Work.R1G.gA_Tit_sq_mul_rpow_le
import Submission.Work.R1G.gA_dz_slice_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.R1G

/-- A general membership criterion: a `SmoothNbhd` function whose `H^k`-integrand is dominated
on the quadrant by an integrable function `M` lies in `H^k`. -/
theorem HkMem_of_majorant (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hslice := Work.Coercivity.aesm_HkIntegrand_slice α k hsm
  have hjoint := Work.Coercivity.aesm_uncurry_HkIntegrand α k hsm
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem hmesθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' hMz hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      (hMslice z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))

/-- The constant majorant `4000000/(1+z)^2` is integrable on `Iz = [0,∞)`. -/
theorem gA_majorant_integrable :
    IntegrableOn (fun z : ℝ => 4000000 / (1 + z) ^ 2) Work.Spaces.Iz := by
  have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Ioi (0:ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
  have hmul : IntegrableOn (fun x : ℝ => (4000000:ℝ) * (x + 1) ^ (-2:ℝ)) (Ioi (0:ℝ)) :=
    hbase.const_mul _
  have hIoi : IntegrableOn (fun z : ℝ => 4000000 / (1 + z) ^ 2) (Ioi (0:ℝ)) := by
    refine hmul.congr_fun (fun z hz => ?_) measurableSet_Ioi
    have hz0 : 0 ≤ z := le_of_lt (mem_Ioi.mp hz)
    change (4000000:ℝ) * (z + 1) ^ (-2:ℝ) = 4000000 / (1 + z) ^ 2
    rw [show (z + 1 : ℝ) = 1 + z by ring, Real.rpow_neg (x := 1 + z) (by linarith : (0:ℝ) ≤ 1 + z),
      div_eq_mul_inv]
    norm_num
  rw [Work.Spaces.Iz]
  exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIoi

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- The pointwise domination of the `H^2`-integrand of `gA`. -/
theorem HkIntegrand_gA_le (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand p 2 gA z θ ≤ 4000000 / (1 + z) ^ 2 := by
  have hz0 : 0 ≤ z := hz
  have hz1 : (1:ℝ) ≤ (1 + z) ^ 2 := by nlinarith [hz0]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hA : ∀ j ∈ Finset.range 3, (Zit j z * Work.Spaces.w z) ^ 2 ≤ 20736 / (1 + z) ^ 2 := by
    intro j hj
    have hj3 : j < 3 := Finset.mem_range.mp hj
    have hb := gA_Zit_mul_w_abs_le j hj3 hz0
    calc (Zit j z * Work.Spaces.w z) ^ 2 = |Zit j z * Work.Spaces.w z| ^ 2 := by rw [sq_abs]
      _ ≤ ((144:ℝ) / (1 + z) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = 20736 / (1 + z) ^ 4 := by rw [div_pow, ← pow_mul]; norm_num
      _ ≤ 20736 / (1 + z) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hsq : (1 + z) ^ 2 ≤ (1 + z) ^ 4 := by
            have h := mul_le_mul_of_nonneg_left hz1 (by positivity : (0:ℝ) ≤ (1 + z) ^ 2)
            calc (1 + z) ^ 2 = (1 + z) ^ 2 * 1 := by ring
              _ ≤ (1 + z) ^ 2 * (1 + z) ^ 2 := h
              _ = (1 + z) ^ 4 := by ring
          linarith
  have h1 : (∑ i ∈ Finset.range 3,
      (Work.Spaces.DzIter i gA z θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
      ≤ 3 * (20736 / (1 + z) ^ 2) := by
    have hstep : (∑ i ∈ Finset.range 3,
        (Work.Spaces.DzIter i gA z θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
        ≤ ∑ i ∈ Finset.range 3, (Zit i z * Work.Spaces.w z) ^ 2 := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [DzIter_gA]
      have hc := gA_dz_slice_le (z := z) (θ := θ) hz0 hθ
      calc (Zit i z * Tf θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2
          = (Zit i z) ^ 2 * (Tf θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2 := by ring
        _ ≤ (Zit i z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_left hc (sq_nonneg _)
        _ = (Zit i z * Work.Spaces.w z) ^ 2 := by ring
    refine le_trans hstep ?_
    refine le_trans (Finset.sum_le_sum hA) ?_
    rw [Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  have h2 : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
      (if 1 ≤ i ∧ i + j ≤ 2 then
        (Work.Spaces.mixed j i gA z θ * Work.Spaces.Wt p z θ) ^ 2 else 0))
      ≤ 144 * (20736 / (1 + z) ^ 2) := by
    have hstep : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then
          (Work.Spaces.mixed j i gA z θ * Work.Spaces.Wt p z θ) ^ 2 else 0))
        ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (16:ℝ) * (20736 / (1 + z) ^ 2) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
      have hi3 : i < 3 := Finset.mem_range.mp hi
      by_cases hc : 1 ≤ i ∧ i + j ≤ 2
      · rw [if_pos hc, mixed_gA]
        have hWt : Work.Spaces.Wt p z θ
            = Work.Spaces.w z * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam p / 2)) := rfl
        have hgam := gA_Tit_sq_mul_rpow_le p hp hp1 i hi3 hθ
        have hr : ((Real.sin (2*θ)) ^ (-(Work.Spaces.gam p / 2))) ^ 2
            = (Real.sin (2*θ)) ^ (-(Work.Spaces.gam p)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
          congr 1
          ring
        have h16 : ((2:ℝ) ^ i) ^ 2 ≤ 16 := by
          have hi2 : i ≤ 2 := by omega
          have hle : (2:ℝ) ^ i ≤ 4 := by
            have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hi2
            have h4 : (2:ℝ) ^ 2 = 4 := by norm_num
            linarith
          calc ((2:ℝ) ^ i) ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
            _ = 16 := by norm_num
        calc (Zit j z * Tit i θ * Work.Spaces.Wt p z θ) ^ 2
            = (Zit j z * Work.Spaces.w z) ^ 2 *
              ((Tit i θ) ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam p))) := by
                rw [hWt,
                  show (Zit j z * Tit i θ * (Work.Spaces.w z *
                      (Real.sin (2*θ)) ^ (-(Work.Spaces.gam p / 2)))) ^ 2
                    = (Zit j z) ^ 2 * (Work.Spaces.w z) ^ 2 * (Tit i θ) ^ 2 *
                      ((Real.sin (2*θ)) ^ (-(Work.Spaces.gam p / 2))) ^ 2 by ring,
                  hr]
                ring
          _ ≤ (Zit j z * Work.Spaces.w z) ^ 2 * ((2:ℝ) ^ i) ^ 2 :=
              mul_le_mul_of_nonneg_left hgam (sq_nonneg _)
          _ ≤ (20736 / (1 + z) ^ 2) * 16 := by
              refine mul_le_mul (hA j hj) h16 (by positivity) (by positivity)
          _ = 16 * (20736 / (1 + z) ^ 2) := by ring
      · rw [if_neg hc]; positivity
    refine le_trans hstep ?_
    have heq : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, (16:ℝ) * (20736 / (1 + z) ^ 2))
        = 144 * (20736 / (1 + z) ^ 2) := by
      rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      ring
    rw [heq]
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add h1 h2) ?_
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (1+z)]

theorem HkMem_gA (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : Work.Spaces.HkMem p 2 Work.R1G.gA := by
  refine HkMem_of_majorant p 2 (f := gA) (M := fun z _ => 4000000 / (1 + z) ^ 2)
    smoothNbhd_gA ?_ ?_ ?_
  · intro z hz
    exact integrableOn_const (s := Work.Spaces.Iθ) (C := 4000000 / (1 + z) ^ 2)
      Work.Spaces.volume_Iθ_lt_top.ne
  · have hMaj := gA_majorant_integrable
    have hcm : IntegrableOn (fun z : ℝ => (volume.real Work.Spaces.Iθ) * (4000000 / (1 + z) ^ 2))
        Work.Spaces.Iz := hMaj.const_mul _
    refine hcm.congr_fun (fun z hz => ?_) measurableSet_Ici
    rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  · intro z hz θ hθ
    exact HkIntegrand_gA_le p hp hp1 hz hθ

end Work.R1G
