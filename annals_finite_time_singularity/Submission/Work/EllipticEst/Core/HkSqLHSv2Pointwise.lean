import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.EllipticEst.Core.mixedFamily_le
import Submission.Work.Blocks.DivSinHalfCore
import Submission.Work.FTS.H2.STSigma

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
