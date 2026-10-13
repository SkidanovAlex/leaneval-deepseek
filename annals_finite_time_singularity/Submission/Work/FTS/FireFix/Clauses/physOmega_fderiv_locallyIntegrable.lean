import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.PhysData
import Submission.Work.FTS.FireFix.Clauses.PhysVortAux
import Submission.Work.FTS.FireFix.Clauses.PhysVortAe
import Submission.Work.FTS.FireFix.Clauses.transfer_rho_theta
import Submission.Work.FTS.FireFix.Clauses.integrableOn_psi_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

theorem physOmega_fderiv_locallyIntegrable {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T,
      MeasureTheory.LocallyIntegrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
          - (Work.FTS.Physical.physOmega α A B g C y t)) x) := by
  intro t ht
  have hτpos : 0 < Work.FTS.Physical.clockInv C t :=
    Work.FTS.Physical.clockInv_pos_of_pos C ht
  set τ : ℝ := Work.FTS.Physical.clockInv C t with hτdef
  have hsel : Work.FTS.RegPkgGal.RegPkg' α τ A B g := hreg τ hτpos
  have hτmem : τ ∈ Set.Icc 0 τ := ⟨le_of_lt hτpos, le_rfl⟩
  have hBτ : 0 < B τ := hsel.hB τ hτmem
  obtain ⟨N, hN⟩ := hsel.hg
  obtain ⟨Npz, hNpz⟩ := hsel.hpz
  obtain ⟨L, hL0, hLsupp⟩ := hsel.hsupp
  have hN' : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 τ → |g z θ τ'| ≤ N :=
    fun z θ τ' hz hθ hτ' => hN.abs_le hz hθ hτ'
  have hNpz' : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 τ →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz :=
    fun z θ τ' hz hθ hτ' => hNpz.abs_le hz hθ hτ'
  have hsupp' : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0 :=
    fun z θ hz => hLsupp τ hτmem z θ hz
  -- (1) the a.e. bound
  have hae := ae_bound_physVort (S := τ) hsel hτmem hN' hNpz' hL0 hsupp'
  -- (2) nonnegativity of the (wrapped) majorant
  have hN0 : 0 ≤ N := le_trans (abs_nonneg (g 0 0 τ))
    (hN.abs_le le_rfl ⟨le_rfl, by linarith [Real.pi_pos]⟩ hτmem)
  have hNpz0 : 0 ≤ Npz := le_trans (abs_nonneg _)
    (hNpz.abs_le le_rfl ⟨le_rfl, by linarith [Real.pi_pos]⟩ hτmem)
  have hFnn : ∀ z θ : ℝ, 0 ≤ (if 0 ≤ z ∧ |θ| ≤ Real.pi / 2 then
      psiBound α A B g τ N Npz L z θ else 0) := by
    intro z θ
    split_ifs with h
    · exact psiBound_nonneg α A B g τ N Npz L z θ (Bpos := hBτ) hN0 hNpz0 hsel.hα h.1 h.2
    · exact le_rfl
  -- (3) the (z,θ)-integrability of the majorant times the weight
  set Ca : ℝ := |(A τ)⁻¹| * ((20 * (3 * α) + N) * 2) with hCa
  set Cb : ℝ := |(A τ)⁻¹| * (2 * ((3 * α) / (B τ)) * (60 * α + Npz)) with hCb
  set Cc : ℝ := |(A τ)⁻¹| * 2 with hCc
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hInt0 := Work.FTS.FireFix.Clauses.integrableOn_psi_weight hsel hτmem hCa0 hCb0 hCc0 hL0.le
  have hint : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (if 0 ≤ q.1 ∧ |q.2| ≤ Real.pi / 2 then psiBound α A B g τ N Npz L q.1 q.2 else 0)
        * q.1 ^ (1 / α - 1) * Real.cos q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hInt0 ?_
      (measurableSet_Ioi.prod measurableSet_Ioo)
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hcond : 0 ≤ q.1 ∧ |q.2| ≤ Real.pi / 2 :=
      ⟨hq1.le, le_of_lt (abs_lt.mpr hq2)⟩
    beta_reduce
    rw [if_pos hcond]
    simp only [psiBound]
    rw [hCa, hCb, hCc]
    split_ifs with h
    · ring_nf
    · ring
  -- (4) the transfer
  have hFint : MeasureTheory.Integrable (fun x : R3 =>
      psiBound α A B g τ N Npz L (Work.Cyl.rho x ^ (3 * α) / B τ) (Work.Cyl.theta x)) := by
    have h1 := (Work.FTS.FireFix.Clauses.transfer_rho_theta (α := α) (B := B τ) hsel.hα hBτ
      hFnn hint).1
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    have hθle : |Work.Cyl.theta x| ≤ Real.pi / 2 :=
      (Set.mem_Icc.mp (Work.FTS.FireFix.Prime.abs_theta_mem_Iθ x)).2
    have hcond : 0 ≤ Work.Cyl.rho x ^ (3 * α) / B τ ∧
        |Work.Cyl.theta x| ≤ Real.pi / 2 :=
      ⟨div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg x) _) hBτ.le, hθle⟩
    beta_reduce
    rw [if_pos hcond]
  -- (5) local integrability of the vorticity slice's fderiv
  have hloc : MeasureTheory.LocallyIntegrable (fun x : R3 =>
      fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x) :=
    locallyIntegrable_fderiv_of_ae_bound hFint.locallyIntegrable hae
  -- (6) the sign and the clock
  have hsgn : (fun x : R3 => fderiv ℝ (fun y : R3 =>
      - Work.FTS.Regularity.physVort α A B g y τ) x)
      = fun x : R3 => - fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x := by
    funext x
    rw [show (fun y : R3 => - Work.FTS.Regularity.physVort α A B g y τ)
        = Neg.neg (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) from rfl]
    exact fderiv_neg
  have hneg : MeasureTheory.LocallyIntegrable (fun x : R3 => fderiv ℝ (fun y : R3 =>
      - Work.FTS.Regularity.physVort α A B g y τ) x) := by
    rw [hsgn]
    exact hloc.neg
  have hfinal : MeasureTheory.LocallyIntegrable (fun x : R3 => fderiv ℝ (fun y : R3 =>
      - Work.FTS.Physical.physOmega α A B g C y t) x) := by
    simpa only [Work.FTS.Physical.physOmega_apply, hτdef] using hneg
  exact hfinal

end Work.FTS.FireFix.Clauses
