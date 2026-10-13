import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false

/-! ## Elementary auxiliary facts about `bump` -/

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h := hf.forall n
  have hfun : Function.uncurry (fun z θ : ℝ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [hfun]
  exact contDiffOn_const.mul h

/-- `bump` vanishes when `z < 1/2`. -/
theorem bump_eq_zero_of_lt_half {z θ : ℝ} (hz : z < 1 / 2) :
    Work.FTS.StrongEps.bump z θ = 0 :=
  Work.FTS.StrongEps.bump_eq_zero_iff.mpr (Or.inl (le_of_lt hz))

/-- `bump` vanishes when `θ ∉ (0, π/2)`. -/
theorem bump_eq_zero_of_not_mem_Ioo {z θ : ℝ} (hθ : θ ∉ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.bump z θ = 0 := by
  rw [Work.FTS.StrongEps.bump_eq_zero_iff]
  rcases not_and_or.mp hθ with h | h
  · exact Or.inr (Or.inr (Or.inl (by push_neg at h; linarith [h, Real.pi_pos])))
  · exact Or.inr (Or.inr (Or.inr (by push_neg at h; linarith [h, Real.pi_pos])))

/-- The bump profile lies in `ℋ^k` for every `k`: it is smooth on the open quadrant and
supported in the compact box `[1/2,1] × [π/4,3π/8]`, so its `ℋ^k`-integrand is dominated by
the integrable majorant `4 M / (z+1)²`. -/
theorem HkMem_bump (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := by
  obtain ⟨M0, hM0nn, hM0⟩ := Work.FTS.StrongEps.exists_bound_HkIntegrand_bump α k
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := Work.FTS.StrongEps.bump) (M := fun z θ => 4 * M0 * (z + 1) ^ (-2 : ℝ))
    (Work.FTS.StrongEps.continuousOn_HkIntegrand_bump α k) ?_ ?_ ?_
  · intro z hz
    refine MeasureTheory.integrableOn_const (hs := ?_)
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · have hbase : MeasureTheory.IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : MeasureTheory.IntegrableOn
        (fun x : ℝ => (4 * M0) * (π / 2) * (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hbase.const_mul _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, 4 * M0 * (z + 1) ^ (-2 : ℝ))
          = (4 * M0) * (π / 2) * (z + 1) ^ (-2 : ℝ) := by
      intro z _
      rw [MeasureTheory.setIntegral_const, Work.Spaces.volume_real_Iθ, smul_eq_mul]
      ring
    have hcon : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, 4 * M0 * (z + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    have hae : Set.Ici (0 : ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
    rw [Work.Spaces.Iz]
    exact hcon.congr_set_ae hae
  · intro z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases le_or_gt z 1 with hz1 | hz1
    · have hp : (4 : ℝ)⁻¹ ≤ (z + 1) ^ (-2 : ℝ) := by
        have h1 : (2 : ℝ) ^ (-2 : ℝ) ≤ (z + 1) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
        have h2 : ((2 : ℝ) ^ (-2 : ℝ)) = (4 : ℝ)⁻¹ := by norm_num
        rw [h2] at h1
        exact h1
      have : M0 ≤ 4 * M0 * (z + 1) ^ (-2 : ℝ) := by nlinarith [hp, hM0nn]
      exact le_trans (hM0 z θ) this
    · rw [Work.FTS.StrongEps.HkIntegrand_bump_eq_zero_of_not_mem α k (Or.inr (Or.inl hz1))]
      exact mul_nonneg (mul_nonneg (by norm_num) hM0nn) (Real.rpow_nonneg (by linarith) _)

/-- The bump profile satisfies the boundary-trace conditions of order `k`: it vanishes off its
support box, hence so do all its mixed derivatives, so every trace is the trace of `0`. -/
theorem bdryTraces_bump (α : ℝ) (k : ℕ) :
    Work.FTS.Nonlin.BdryTraces α k Work.FTS.StrongEps.bump := by
  intro a b hab
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with z hz'
    have h0 : Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ = 0 := by
      simpa only [Work.Spaces.mixed] using
        Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem (Or.inl hz'.2) b a
    rw [h0]; ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioi_mem_atTop (1 : ℝ)] with z hz'
    have h0 : Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ = 0 := by
      simpa only [Work.Spaces.mixed] using
        Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem (Or.inr (Or.inl hz')) b a
    rw [h0]; ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by linarith [Real.pi_pos])]
      with θ hθ'
    have h0 : Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ = 0 := by
      simpa only [Work.Spaces.mixed] using
        Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem
          (Or.inr (Or.inr (Or.inl hθ'.2))) b a
    rw [h0]; ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsLT (show 3 * Real.pi / 8 < Real.pi / 2 by
      linarith [Real.pi_pos])] with θ hθ'
    have h0 : Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ = 0 := by
      simpa only [Work.Spaces.mixed] using
        Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem
          (Or.inr (Or.inr (Or.inr hθ'.1))) b a
    rw [h0]; ring

/-! ## The projection preserves the mollifier class -/

theorem softClass_Pz {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.StrongEps.SoftClass α f) : Work.FTS.StrongEps.SoftClass α (Work.FTS.StrongEps.Pz f) := by
  set c : ℝ := Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm with hc
  have hPz : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-c) * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, ← hc]
    ring
  have hgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) :=
    smoothOpen_const_mul (-c) Work.FTS.StrongEps.smoothOpen_bump
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the angular normalisation is a no-op
    funext z θ
    by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
    · simp only [Work.FTS.EllSol.normTh, if_pos hθ]
    · have hf0 : f z θ = 0 := by
        have h := congrFun (congrFun hf.norm z) θ
        simp only [Work.FTS.EllSol.normTh, if_neg hθ] at h
        exact h.symm
      simp only [Work.FTS.EllSol.normTh, if_neg hθ, Work.FTS.StrongEps.Pz_apply,
        hf0, bump_eq_zero_of_not_mem_Ioo hθ, mul_zero, sub_zero]
  · -- smooth on the open quadrant
    rw [hPz]
    exact Work.FTS.EllipticEst.smoothOpen_add hf.reg hgsm
  · -- `ℋ⁸`-membership
    rw [hPz]
    exact Work.FTS.EllipticEst.HkMem_add_smoothOpen α 8 hα hf.reg hgsm hf.mem8
      (Work.FTS.LocData.HkMem_const_mul α 8 (-c) (HkMem_bump α 8))
  · -- `ℋ¹⁰`-membership (lead install 2026-10-11)
    rw [hPz]
    exact Work.FTS.EllipticEst.HkMem_add_smoothOpen α 10 hα hf.reg hgsm hf.mem10
      (Work.FTS.LocData.HkMem_const_mul α 10 (-c) (HkMem_bump α 10))
  · -- the boundary traces up to order `7`
    rw [hPz]
    refine Work.FTS.ClassC.bdryTraces_add hf.reg hgsm hf.tr7 ?_
    convert Work.FTS.ClassC.bdryTraces_smul (bdryTraces_bump α 7) (-c) using 1
  · -- the axis condition
    intro θ hθ
    refine Filter.Tendsto.congr' ?_ (hf.axis θ hθ)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with z hz
    rw [Work.FTS.StrongEps.Pz_apply, bump_eq_zero_of_lt_half hz.2]
    ring
  · -- the θ-traces up to order `10` (lead install R6, 2026-10-11)
    rw [hPz]
    refine Work.FTS.ClassC.thetaTraces_add hf.reg hgsm hf.thTr ?_
    convert Work.FTS.PhiStar.thetaTraces_of_bdryTraces
      (Work.FTS.ClassC.bdryTraces_smul (bdryTraces_bump α 10) (-c)) using 1

end Work.FTS.StrongEps.PZeroAux
