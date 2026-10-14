import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.EllipticEst.Core.HkSqLHSv2Pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise identification behind `HkSqLHS_le_summands_v2`

`HkIntegrand α k (α • D_z ∂_θV)` is a sum of squares of weighted derivatives.  For `V` of class
`C^∞` on the open quadrant the two blocks of that sum identify, a.e. in `θ`, with the summands
appearing on the right-hand side of `HkSqLHS_le_summands_v2`:

* `v2_zBlock_ae` — the pure `D_z`-block: `D_z^i(α D_z∂_θV) = α D_z∂_θ(D_z^i V)` (which uses
  `∂_θ(D_z^i V) = D_z^i(∂_θV)` on the open quadrant, `Work.EllipticEst.H2W.pth_DzIter_eqOn_Q0`);
* `v2_mixedBlock_ae` — the mixed block: `D_z^jD_θ^i(α D_z∂_θV) = α D_z^{j+1}D_θ^i∂_θV` (which
  uses `D_θ`-`D_z` commutation on the open quadrant).

The elementary commutation identities for constant multiples and for `D_z^i(D_z f)` are proved
here as well (`v2_DzIter_const_mul`, `v2_DthIter_const_mul`, `v2_DzIter_Dz_eq`); they are
unconditional identities of functions.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-! ## Elementary identities for the iterated operators -/

/-- `D_z` commutes with multiplication by a constant. -/
theorem v2_Dz_const_mul (c : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * F z θ) = fun z θ => c * Work.Spaces.Dz F z θ := by
  funext z θ
  show z * deriv (fun z' => c * F z' θ) z = c * (z * deriv (fun z' => F z' θ) z)
  rw [deriv_const_mul_field]
  ring

/-- `D_z^i` commutes with multiplication by a constant. -/
theorem v2_DzIter_const_mul (i : ℕ) (c : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * F z θ)
      = fun z θ => c * Work.Spaces.DzIter i F z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc Work.Spaces.DzIter (i + 1) (fun z θ => c * F z θ)
        = Work.Spaces.Dz (Work.Spaces.DzIter i (fun z θ => c * F z θ)) := rfl
      _ = Work.Spaces.Dz (fun z θ => c * Work.Spaces.DzIter i F z θ) := by rw [ih]
      _ = fun z θ => c * Work.Spaces.DzIter (i + 1) F z θ := by
            rw [v2_Dz_const_mul]
            rfl

/-- `D_z^i (D_z F) = D_z^{i+1} F`. -/
theorem v2_DzIter_Dz_eq (i : ℕ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz F) = Work.Spaces.DzIter (i + 1) F := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc Work.Spaces.DzIter (i + 1) (Work.Spaces.Dz F)
        = Work.Spaces.Dz (Work.Spaces.DzIter i (Work.Spaces.Dz F)) := rfl
      _ = Work.Spaces.Dz (Work.Spaces.DzIter (i + 1) F) := by rw [ih]
      _ = Work.Spaces.DzIter (i + 1 + 1) F := rfl

/-- `D_θ` commutes with multiplication by a constant. -/
theorem v2_Dth_const_mul (c : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * F z θ) = fun z θ => c * Work.Spaces.Dth F z θ := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => c * F z θ') θ
      = c * (Real.sin (2 * θ) * deriv (fun θ' => F z θ') θ)
  rw [deriv_const_mul_field]
  ring

/-- `D_θ^i` commutes with multiplication by a constant. -/
theorem v2_DthIter_const_mul (i : ℕ) (c : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * F z θ)
      = fun z θ => c * Work.Spaces.DthIter i F z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc Work.Spaces.DthIter (i + 1) (fun z θ => c * F z θ)
        = Work.Spaces.Dth (Work.Spaces.DthIter i (fun z θ => c * F z θ)) := rfl
      _ = Work.Spaces.Dth (fun z θ => c * Work.Spaces.DthIter i F z θ) := by rw [ih]
      _ = fun z θ => c * Work.Spaces.DthIter (i + 1) F z θ := by
            rw [v2_Dth_const_mul]
            rfl

/-! ## The pure `D_z` block -/

/-- **The pure `D_z` block of the identification.**  For `V` of class `C^∞` on the open
quadrant and `z ∈ [0,∞)` the `D_z`-block of `HkIntegrand α k (α • D_z∂_θV)` agrees a.e. in
`θ ∈ [0,π/2]` with `α² ∑_{r ≤ k} (D_z∂_θ(D_z^r V))² (w z)² sin(2θ)^{-η}`. -/
theorem v2_zBlock_ae (k : ℕ) {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => α ^ 2 * ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hL : (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => 0 := by
      rw [← hz0]
      funext θ
      simp [Work.Spaces.w]
    have hR : (fun θ : ℝ => α ^ 2 * ∑ r ∈ Finset.range (k + 1),
        (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) = fun _ : ℝ => 0 := by
      rw [← hz0]
      funext θ
      simp [Work.Spaces.w]
    rw [hL, hR]
  · have hmeas_eq : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
          (b := π / 2))).symm
    rw [hmeas_eq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    show (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = α ^ 2 * ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hterm : ∀ i : ℕ,
        (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = α ^ 2 * ((Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      intro i
      have hA : Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
            z θ
          = α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ := by
        have hcongr : Work.Spaces.Dz (Work.Spaces.DzIter i (Work.Spaces.pth V)) z θ
            = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ := by
          simp only [Work.Spaces.Dz]
          rw [Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
            (Work.EllipticEst.H2W.pth_DzIter_eqOn_Q0 hV i).symm hQ]
        calc Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            = (fun z θ => α * Work.Spaces.DzIter i (Work.Spaces.Dz (Work.Spaces.pth V))
                z θ) z θ := by
                rw [v2_DzIter_const_mul i α (Work.Spaces.Dz (Work.Spaces.pth V))]
          _ = (fun z θ => α * Work.Spaces.DzIter (i + 1) (Work.Spaces.pth V) z θ) z θ := by
                rw [v2_DzIter_Dz_eq i (Work.Spaces.pth V)]
          _ = (fun z θ => α * Work.Spaces.Dz (Work.Spaces.DzIter i (Work.Spaces.pth V))
                z θ) z θ := rfl
          _ = α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ := by
                simp only [hcongr]
      have hW := w_div_sin_sq_eq z hθI
      calc (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
              z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
                rw [hA]
        _ = α ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ) ^ 2 := by ring
        _ = α ^ 2 * ((Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
                rw [hW]
                ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.mul_sum]

/-! ## The mixed block -/

/-- **The mixed block of the identification.**  For `0 < α`, `V` of class `C^∞` on the open
quadrant and `z ∈ [0,∞)` the mixed block of `HkIntegrand α k (α • D_z∂_θV)` agrees a.e. in
`θ ∈ [0,π/2]` with `α² ∑_{1 ≤ i, i+j ≤ k} (D_z^{j+1}D_θ^i∂_θV)² (w z)² sin(2θ)^{-γ}`. -/
theorem v2_mixedBlock_ae (k : ℕ) {α : ℝ} (hα : 0 < α) {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => α ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hL : (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0) = fun _ : ℝ => 0 := by
      rw [← hz0]
      funext θ
      simp [Work.Spaces.Wt, Work.Spaces.w]
    have hR : (fun θ : ℝ => α ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
        else 0) = fun _ : ℝ => 0 := by
      rw [← hz0]
      funext θ
      simp [Work.Spaces.w]
    rw [hL, hR]
  · have hmeas_eq : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
          (b := π / 2))).symm
    rw [hmeas_eq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    show (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      = α ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hB : ∀ i j : ℕ,
        Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          = α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ := by
      intro i j
      have hcomm : Set.EqOn
          (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V))))
          (Function.uncurry (Work.Spaces.Dz
            (Work.Spaces.DthIter i (Work.Spaces.pth V))))
          Work.FTS.EllipticEst.Q0 :=
        Work.Blocks.DivSinHalf.DthIter_DzIter_comm_eqOn Work.FTS.EllipticEst.isOpen_Q0
          hV.pth 1 i
      have hcongr : Work.Spaces.DzIter j
            (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V))) z θ
          = Work.Spaces.DzIter j
            (Work.Spaces.Dz (Work.Spaces.DthIter i (Work.Spaces.pth V))) z θ :=
        Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm j hQ
      calc Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
            z θ
          = (fun z θ => α * Work.Spaces.DzIter j
              (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V))) z θ) z θ := by
              simp only [Work.Spaces.mixed]
              rw [v2_DthIter_const_mul i α (Work.Spaces.Dz (Work.Spaces.pth V)),
                v2_DzIter_const_mul j α
                  (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V)))]
        _ = α * Work.Spaces.DzIter j
              (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V))) z θ := rfl
        _ = α * Work.Spaces.DzIter j
              (Work.Spaces.Dz (Work.Spaces.DthIter i (Work.Spaces.pth V))) z θ := by
              simp only [hcongr]
        _ = α * Work.Spaces.DzIter (j + 1)
              (Work.Spaces.DthIter i (Work.Spaces.pth V)) z θ := by
              rw [v2_DzIter_Dz_eq j (Work.Spaces.DthIter i (Work.Spaces.pth V))]
        _ = α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ := rfl
    have hterm : ∀ i j : ℕ,
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
              z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          = α ^ 2 * (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
              else 0) := by
      intro i j
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, if_pos hc]
        have hW := Wt_sq_eq hα z hθI
        calc (Work.Spaces.mixed j i
                (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2
            = (α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ
                * Work.Spaces.Wt α z θ) ^ 2 := by rw [hB i j]
          _ = α ^ 2 * (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.Wt α z θ) ^ 2 := by ring
          _ = α ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ) := by
                rw [hW]
                ring
      · rw [if_neg hc, if_neg hc]
        ring
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm i j)

end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.HkIntegrand_integral_le_pth2_pth_point =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary vocabulary for the proof

`Sfun` (the sum of the three fixed integrable angular weights produced by the boundary
conditions in `slicePhi`, together with `Sfun_nonneg`, `integrableOn_Sfun` and
`integral_Sfun_le`) is imported from `ThetaU.OpenIntegrability`; the dominating function
`Bdom` by which a single angular integrand (at a fixed radial level `z`, with a fixed value
`M` of the `H^k`-integral of `∂_θ² f`) is bounded is defined here. -/





end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {F : ℝ → ℝ → ℝ}

/-! ## Elementary angular facts -/

theorem sin_two_pos_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_ne_zero_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_Q0 hθ)

/-! ## (1) `∂_z (D_z^j D_θ^i F) = D_z^{j+1}D_θ^i F / z`

This is nothing but the defining recursion `D_z^{j+1} = z ∂_z ∘ D_z^j`, divided by `z`
(which is non-zero on the open quadrant). -/

theorem pz_mixed_div (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.mixed j i F) z θ
        = Work.Spaces.mixed (j + 1) i F z θ / z := by
  intro z θ h
  obtain ⟨hz, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hdef : Work.Spaces.mixed (j + 1) i F z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ := rfl
  rw [hdef, mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-! ## (2) `∂_θ (D_z^j D_θ^i F) = D_z^j D_θ^{i+1} F / sin 2θ`

`D_θ^{i+1} = sin 2θ · ∂_θ ∘ D_θ^i`, so this is `∂_θ` commuted with the iterates of `D_z`
(`Dth_DzIter_comm_eqOn`), divided by `sin 2θ` (non-zero on `(0, π/2)`). -/

theorem pth_mixed_div (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.mixed j i F) z θ
        = Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ) := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hs : Real.sin (2 * θ) ≠ 0 := sin_two_ne_zero_Q0 ⟨hθ0, hθ1⟩
  have hcomm := Work.Blocks.DivSinHalf.Dth_DzIter_comm_eqOn
    Work.FTS.EllipticEst.isOpen_Q0 (hF.DthIter i) j h
  have h23 : Work.Spaces.mixed j (i + 1) F z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i F) z θ := by
    have h3 : Work.Spaces.mixed j (i + 1) F z θ
        = Work.Spaces.Dth (Work.Spaces.DzIter j (Work.Spaces.DthIter i F)) z θ := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Function.uncurry] using hcomm.symm
    rw [h3]
    rfl
  rw [h23, mul_div_cancel_left₀ _ hs]

/-! ## (3) `∂_z (D_z^{j+1}D_θ^i F / z) = (D_z^{j+2}D_θ^i F - D_z^{j+1}D_θ^i F) / z²`

The quotient rule in `z`, with `∂_z` of the numerator evaluated by (1). -/

theorem pz_mixed_div_div (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = (Work.Spaces.mixed (j + 2) i F z θ - Work.Spaces.mixed (j + 1) i F z θ) / z ^ 2 := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hz' : z ≠ 0 := ne_of_gt hz
  have hd : HasDerivAt (fun z' : ℝ => Work.Spaces.mixed (j + 1) i F z' θ)
      (Work.Spaces.pz (Work.Spaces.mixed (j + 1) i F) z θ) z :=
    (hF.mixed (j + 1) i).hasDerivAt_slice ⟨hθ0, hθ1⟩ hz
  have hkey : deriv (fun z' : ℝ => Work.Spaces.mixed (j + 1) i F z' θ / z') z
      = (Work.Spaces.pz (Work.Spaces.mixed (j + 1) i F) z θ * z
          - Work.Spaces.mixed (j + 1) i F z θ * 1) / z ^ 2 :=
    (hd.div (hasDerivAt_id' z) hz').deriv
  show deriv (fun z' : ℝ => Work.Spaces.mixed (j + 1) i F z' θ / z') z = _
  rw [hkey, pz_mixed_div (j + 1) i hF z θ h,
    show (j + 1) + 1 = j + 2 from by omega, div_mul_cancel₀ _ hz', mul_one]

/-! ## (4) `∂_z (D_z^j D_θ^{i+1} F / sin 2θ) = D_z^{j+1}D_θ^{i+1} F / (z sin 2θ)`

Here the angular factor `sin 2θ` is a constant as far as `∂_z` is concerned. -/

theorem pz_mixed_angdiv (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ)) := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hkey : deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ / Real.sin (2 * θ)) z
      = deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ) z / Real.sin (2 * θ) :=
    deriv_div_const _
  show deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ / Real.sin (2 * θ)) z = _
  rw [hkey, show deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ) z
      = Work.Spaces.pz (Work.Spaces.mixed j (i + 1) F) z θ from rfl,
    pz_mixed_div j (i + 1) hF z θ h, div_div]

/-! ## (5) `∂_θ (D_z^{j+1}D_θ^i F / z) = D_z^{j+1}D_θ^{i+1} F / (z sin 2θ)`

The radial factor `z` is a constant as far as `∂_θ` is concerned; (2) evaluates the
numerator. -/

theorem pth_mixed_zdiv (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ)) := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hkey : deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ' / z) θ
      = deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ') θ / z :=
    deriv_div_const z
  show deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ' / z) θ = _
  rw [hkey, show deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ') θ
      = Work.Spaces.pth (Work.Spaces.mixed (j + 1) i F) z θ from rfl,
    pth_mixed_div (j + 1) i hF z θ h, div_div, mul_comm (Real.sin (2 * θ)) z]

/-! ## (6) `∂_θ (D_z^j D_θ^{i+1} F / sin 2θ) = D_z^j D_θ^{i+2} F / sin²2θ
  - 2cos 2θ · D_z^j D_θ^{i+1} F / sin²2θ`

The quotient rule in `θ`, with `(sin 2θ)' = 2 cos 2θ` and (2) evaluating the numerator. -/

theorem pth_mixed_angdiv (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ
              / (Real.sin (2 * θ)) ^ 2 := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hs : Real.sin (2 * θ) ≠ 0 := sin_two_ne_zero_Q0 ⟨hθ0, hθ1⟩
  have hds : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have h3 : HasDerivAt (Real.sin ∘ (fun y : ℝ => 2 * y)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    have h4 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
      simpa only [Function.comp_def] using h3
    exact h4.congr_deriv (by ring)
  have hdθ : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ') θ :=
    (((hF.mixed j (i + 1)).curry_θ hz).differentiableOn
        (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)
  have hkey : deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ' / Real.sin (2 * θ')) θ
      = (deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ') θ * Real.sin (2 * θ)
          - Work.Spaces.mixed j (i + 1) F z θ
              * deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) / (Real.sin (2 * θ)) ^ 2 :=
    deriv_div hdθ hds.differentiableAt hs
  show deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ' / Real.sin (2 * θ')) θ = _
  rw [hkey, show deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ') θ
      = Work.Spaces.pth (Work.Spaces.mixed j (i + 1) F) z θ from rfl,
    hds.deriv, pth_mixed_div j (i + 1) hF z θ h,
    show (i + 1) + 1 = i + 2 from by omega]
  rw [div_mul_cancel₀ _ hs, ← sub_div]
  congr 1
  ring

/-! ## The six identities, assembled. -/

theorem mixed_partials_of_smoothOpen (j i : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.mixed j i F) z θ = Work.Spaces.mixed (j + 1) i F z θ / z) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.mixed j i F) z θ
        = Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ)) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = (Work.Spaces.mixed (j + 2) i F z θ - Work.Spaces.mixed (j + 1) i F z θ) / z ^ 2) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ))) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ))) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ / (Real.sin (2 * θ)) ^ 2) := by
  exact ⟨pz_mixed_div j i hF, pth_mixed_div j i hF, pz_mixed_div_div j i hF,
    pz_mixed_angdiv j i hF, pth_mixed_zdiv j i hF, pth_mixed_angdiv j i hF⟩

end Work.FTS.StrongEps.LocUnif
end
end
