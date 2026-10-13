import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs
import Submission.Work.FTS.StrongPersist.IP6Clauses
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.StrongPersist.H6Rows.RowAux
import Submission.Work.FTS.StrongPersist.AK6.HkMem_AK6
import Submission.Work.FTS.StrongPersist.AK6.akRho_jet_bound6
import Submission.Work.FTS.StrongPersist.AK6.Sharp6
import Submission.Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6
import Submission.Work.FTS.Nonlinear.Open.Row23

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The block `AK α` is `ℋ⁶` with an absolute bound

The `-μ̄·AK α` piece of `dynRHS` is the one piece whose coefficient is a *fixed* function, so
its size is a constant and only the `ℋ⁶`-membership and norm of `AK α` are needed.  `AK α` is
the separable datum `(Γ(θ)/c α)·2z²/(1+z)³`; the radial jets are `AK6/akRho_jet_bound6` and the
angular ones `LocData6.DthIter_Gam_abs_le6`, assembled in `AK6/Sharp6` and `AK6/HkMem_AK6`. -/

/-- `AK α = (Γ(θ)/c α)·(2z²/(1+z)³)` is `C^∞` on the open quadrant (a product of the angular
factor `Γ` — `C^∞` by `row23_smoothOpen_Gam` — and the radial rational profile). -/
theorem AK_smoothO (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.AK α z θ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.Gam α θ) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ / Work.Spaces.c α) := by
    have he : (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ / Work.Spaces.c α)
        = fun (_ : ℝ) (θ : ℝ) => (1 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
      funext z θ
      ring
    rw [he]
    exact smoothOpen_const_mul' (1 / Work.Spaces.c α) hG
  have h3 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) (_ : ℝ) => 2 * z ^ 2 / (1 + z) ^ 3) := by
    refine Work.FTS.Nonlinear.Open.row23_smoothOpen_radial
      (r := fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (fun n => ?_)
    have he : (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3)
        = fun z : ℝ => 2 * z ^ 2 * ((1 + z) ^ 3)⁻¹ := by
      funext z
      rw [div_eq_mul_inv]
    rw [he]
    refine ContDiffOn.mul (contDiffOn_const.mul (contDiffOn_id.pow 2)) ?_
    refine ((contDiffOn_const.add contDiffOn_id).pow 3).inv (fun z hz => ?_)
    have hz' : (0 : ℝ) < 1 + z := by
      have h := hz
      rw [Set.mem_Ioi] at h
      linarith
    simpa only [id_eq] using pow_ne_zero 3 (ne_of_gt hz')
  have h4 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ =>
        (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)))
      Work.FTS.EllipticEst.Q0 := h1.mul h3
  have heq : (fun z θ => Work.Construction.AK α z θ)
      = fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := rfl
  rw [heq]
  exact h4

/-- **`AK α ∈ ℋ⁶` with an `α`-uniform norm bound.**  From the radial jet bound `hrad` of
`2z²/(1+z)³` (`akRho_jet_bound6`) and the pointwise domination `AK_integrand_le6`, the
integration criterion `hkSq_le_of_integrand_le6` gives `HkSq α 6 (AK α) ≤ 2(700R·10⁴ +
49·10¹²R·700)`, and `HkMem_AK6` gives the membership. -/
theorem AK6_mem_norm : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6 (Work.Construction.AK α) ∧
      Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ K := by
  obtain ⟨R, hR0, hR⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  refine ⟨Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) + 1,
    by positivity, ?_⟩
  intro α hα hα1
  have hA0 : (0 : ℝ) ≤ 700 * R := by linarith
  have hB0 : (0 : ℝ) ≤ 49 * 10 ^ 12 * R := by linarith
  refine ⟨Work.FTS.StrongPersist.AK6.HkMem_AK6 α hα hα1 hR0 hR, ?_⟩
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Construction.AK α) z θ
        ≤ (1 / (1 + z) ^ 2) * ((700 * R) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + (49 * 10 ^ 12 * R) * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
    Work.FTS.StrongPersist.AK6.AK_integrand_le6 hR0 hR α hα hα1
  have hsq : Work.Spaces.HkSq α 6 (Work.Construction.AK α)
      ≤ 2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700) :=
    Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 (f := Work.Construction.AK α)
      hα hα1 hA0 hB0 hpt
  have hmono : Work.Spaces.HkNorm α 6 (Work.Construction.AK α)
      ≤ Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) := Real.sqrt_le_sqrt hsq
  linarith [Real.sqrt_nonneg (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))]

/-- **The `-μ̄·AK α` row.**  For every honest `f` and every scalar `c`,
`|IP6 α (c·AK α) f| ≤ (CC·K₆)·|c|·|f|_{ℋ⁶}`: the coefficient is a fixed `ℋ⁶`-function
(`AK6_mem_norm`), so Cauchy–Schwarz (`IP6_cs_coeffs`) and homogeneity (`IP6_smul`) close it. -/
theorem AK_pair_le : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f : Fn),
      Work.FTS.VocabO.HQo α 6 f →
      |IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => c * Work.Construction.AK α z θ) f|
        ≤ K * |c| * Xn6 α f := by
  obtain ⟨CC, hCC0, hCS⟩ := IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 1 one_pos
  obtain ⟨K6, hK60, hAK⟩ := AK6_mem_norm
  refine ⟨CC * K6, 1, mul_pos hCC0 hK60, one_pos, le_refl 1, ?_⟩
  intro α hα c f hf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨hmemAK, hnormAK⟩ := hAK α hα0 hα1
  have hsoAK : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.AK α z θ) :=
    AK_smoothO α
  have hso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * Work.Construction.AK α z θ) :=
    smoothOpen_const_mul' c hsoAK
  have hmem : Work.Spaces.HkMem α 6 (fun z θ => c * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 c hmemAK
  have hq : Work.FTS.VocabO.HQo α 6 (fun z θ => c * Work.Construction.AK α z θ) :=
    ⟨hso, hmem⟩
  have hcs := hCS α hα (fun z θ => c * Work.Construction.AK α z θ) f hq hf
  have hXn : Xn6 α (fun z θ => c * Work.Construction.AK α z θ) = |c| * Xn6 α (Work.Construction.AK α) :=
    Work.FTS.EllipticEst.HkNorm_const_mul α 6 c
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoAK n)
  have hf0 : 0 ≤ Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
  have hc0 : 0 ≤ |c| := abs_nonneg c
  calc |IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => c * Work.Construction.AK α z θ) f|
      ≤ CC * Xn6 α (fun z θ => c * Work.Construction.AK α z θ) * Xn6 α f := hcs
    _ = CC * (|c| * Xn6 α (Work.Construction.AK α)) * Xn6 α f := by rw [hXn]
    _ ≤ CC * (|c| * K6) * Xn6 α f := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCC0.le) hf0
        exact mul_le_mul_of_nonneg_left hnormAK hc0
    _ = CC * K6 * |c| * Xn6 α f := by ring


end Work.FTS.StrongPersist
