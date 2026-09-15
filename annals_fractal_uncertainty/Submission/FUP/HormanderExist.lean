import Submission.FUP.Friedrichs2
import Submission.FUP.Dbar2Calc
import Submission.FUP.DbarAdjOp
import Submission.Commons.Analysis.InnerProductSpace.LinearPMap.orthogonal_decomposition_of_range_le_ker
import Submission.Commons.Analysis.InnerProductSpace.LinearPMap.adjoint_adjoint_of_isClosed

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Hörmander's `L²` existence theorem for `∂̄`, from the Friedrichs a priori estimate

This module instantiates the abstract existence theorem
`Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound` with

* `T := dbarOpMin φ = (dbarAdjOp φ)†` (the *minimal* weak `∂̄`-operator), and
* `S := dbarOp2 φ` (the *maximal* weak `∂̄₂`-operator),

the a priori estimate `hbound` being `Submission.FUP.hbound_friedrichs` (the Friedrichs
approximation of `Submission/FUP/Friedrichs2.lean`).

The `hdec` hypothesis of the abstract theorem is proved generically in the commons
(`Commons.Analysis.InnerProductSpace.LinearPMap.orthogonal_decomposition_of_range_le_ker`); its
input `ran T ⊆ ker S` is `∀ y, DbarWeak2 φ (T y) 0`, which follows from
`Dbar2Calc.dbarWeak_ran_le_ker` and `dbarOpMin_weak` below.
-/

namespace Submission.FUP

noncomputable section

variable {d : ℕ}
variable {φ : FormDu d → ℝ}

/-- `liftForm` and `toFormFun` are inverse on functions into `FormSpace d`. -/
@[simp] lemma liftForm_toFormFun_eq {d : ℕ} (ψ : FormDu d → FormSpace d) :
    liftForm (toFormFun ψ) = ψ := by
  funext z
  simp only [liftForm, toFormFun, WithLp.equiv_apply, WithLp.toLp_ofLp]

/-- **The minimal `∂̄`-operator satisfies the weak relation.** -/
theorem dbarOpMin_weak {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {y : H1 φ}
    (hy : y ∈ (dbarOpMin φ).domain) :
    DbarWeak φ y ((dbarOpMin φ) ⟨y, hy⟩) := by
  intro ψ h1 h2 hψ hθ
  have hFA := LinearPMap.adjoint_isFormalAdjoint (T := dbarAdjOp φ) (dense_domain_dbarAdjOp hφ)
  have hψd : ∀ j, ContDiff ℝ ∞ (fun z => toFormFun ψ z j) := contDiff_toFormFun h1
  have hψs : ∀ j, HasCompactSupport (fun z => toFormFun ψ z j) := fun j =>
    Submission.FUP.hasCompactSupport_comp j (hasCompactSupport_toFormFun h2)
  have hψdom : (hψ.toLp ψ) ∈ (dbarAdjOp φ).domain :=
    mem_domain_dbarAdjOp_of_smooth hφ hψd (hasCompactSupport_toFormFun h2) hψ
  have hval : (dbarAdjOp φ) ⟨hψ.toLp ψ, hψdom⟩ = hθ.toLp (dbarAdjoint φ (toFormFun ψ)) :=
    dbarAdjOp_apply_eq (hφ := hφ) hψdom (dbarAdjWeak_smooth hφ hψd hψs hψ hθ)
  have h1' : inner ℂ ((dbarOpMin φ) ⟨y, hy⟩) (hψ.toLp ψ)
      = inner ℂ y (hθ.toLp (dbarAdjoint φ (toFormFun ψ))) := by
    have h := hFA ⟨y, hy⟩ ⟨hψ.toLp ψ, hψdom⟩
    rw [hval] at h
    exact h
  calc inner ℂ (hψ.toLp ψ) ((dbarOpMin φ) ⟨y, hy⟩)
      = star (inner ℂ ((dbarOpMin φ) ⟨y, hy⟩) (hψ.toLp ψ)) :=
        (inner_conj_symm (hψ.toLp ψ) ((dbarOpMin φ) ⟨y, hy⟩)).symm
    _ = star (inner ℂ y (hθ.toLp (dbarAdjoint φ (toFormFun ψ)))) := by rw [h1']
    _ = inner ℂ (hθ.toLp (dbarAdjoint φ (toFormFun ψ))) y :=
        inner_conj_symm (hθ.toLp (dbarAdjoint φ (toFormFun ψ))) y

/-- **The range of the minimal `∂̄`-operator is contained in the kernel of the maximal
`∂̄₂`-operator.**  This is `∂̄∂̄ = 0` in the weak sense. -/
theorem dbarOpMin_range_le_ker (hφ : ContDiff ℝ ∞ φ) :
    ∀ y : (dbarOpMin φ).domain,
      ∃ hy : ((dbarOpMin φ) y) ∈ (dbarOp2 φ).domain,
        (dbarOp2 φ) ⟨(dbarOpMin φ) y, hy⟩ = 0 := by
  intro y
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 : DbarWeak φ (y : H1 φ) ((dbarOpMin φ) y) := dbarOpMin_weak hφ1 y.2
  have h2 : DbarWeak2 φ ((dbarOpMin φ) y) 0 := dbarWeak_ran_le_ker hφ h1
  exact ⟨mem_dbarOp2_domain.mpr ⟨0, h2⟩, dbarOp2_apply_eq (hφ := hφ1) _ h2⟩

/-- **A smooth, compactly supported, `∂̄`-closed `(0,1)`-form is weakly `∂̄₂`-closed.** -/
theorem dbarWeak2_of_dbarClosed_of_hasCompactSupport {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {η : FormDu d → (Fin d → ℂ)} (hη : ∀ j, ContDiff ℝ ∞ (fun z => η z j))
    (hsη : ∀ j, HasCompactSupport (fun z => η z j))
    (hηm : MemLp (liftForm η) 2 (wtMeasure φ)) (hclosed : DbarClosed η) :
    DbarWeak2 φ (hηm.toLp (liftForm η)) 0 := by
  have hzf : dbarFormFun2 η = 0 := by
    funext z i
    have h := congrFun (congrFun (congrFun hclosed z) i.1) i.2
    simpa only [dbarFormFun2, dbarForm, Pi.zero_apply] using h
  have hm0 : MemLp (liftForm2 (dbarFormFun2 η)) 2 (wtMeasure φ) := by
    rw [hzf]; exact MemLp.zero
  have heq : liftForm2 (dbarFormFun2 η) =ᵐ[wtMeasure φ] (0 : FormDu d → FormSpace2 d) := by
    rw [hzf]
    filter_upwards with z
    rfl
  have h := dbarWeak2_smooth hφ hη hsη hηm hm0
  rw [MemLp.toLp_congr hm0 MemLp.zero heq] at h
  simpa only [MemLp.toLp_zero] using h

section Existence

variable {d : ℕ}
variable {φ : FormDu d → ℝ}

/-- **Hörmander's `L²` existence theorem for `∂̄`.**  If `φ`, `κ` satisfy the Kohn--Morrey
(Hermitian Hessian) positivity condition and `η ∈ L²(μ_φ)` is weakly `∂̄₂`-closed, then the
equation `∂̄u = η` has an `L²(μ_φ)` solution `u` with the sharp estimate
`‖u‖² ≤ ∫ |η|²e^{-φ}/κ`.

The proof is the abstract existence theorem
`Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound` applied to the pair
`T = dbarOpMin φ = (dbarAdjOp φ)†`, `S = dbarOp2 φ`, with `hbound` the Friedrichs a priori
estimate `hbound_friedrichs`. -/
theorem exists_L2_solution_of_dbar (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    {η : FormDu d → (Fin d → ℂ)} {κ : FormDu d → ℝ}
    (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    (hηc : ∀ j, Continuous (fun z => η z j))
    (hηint : ∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z) < ⊤)
    (hηm : MemLp (liftForm η) 2 (wtMeasure φ))
    (hhess : HessBound φ κ)
    (hv0 : DbarWeak2 φ (hηm.toLp (liftForm η)) 0) :
    ∃ u : H1 φ, DbarWeak φ u (hηm.toLp (liftForm η)) ∧ ‖u‖ ^ 2 ≤ etaKapNorm η φ κ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hCnn : 0 ≤ etaKapNorm η φ κ := by
    rw [etaKapNorm]
    refine integral_nonneg fun z => div_nonneg (mul_nonneg ?_ (Real.exp_nonneg _)) (hκpos z).le
    rw [formNormSq]
    exact Finset.sum_nonneg fun j _ => by positivity
  let v : H2 φ := hηm.toLp (liftForm η)
  have hvdom : v ∈ (dbarOp2 φ).domain := mem_dbarOp2_domain.mpr ⟨0, hv0⟩
  have hvzero : (dbarOp2 φ) ⟨v, hvdom⟩ = 0 := dbarOp2_apply_eq (hφ := hφ1) hvdom hv0
  have hvnS : LinearPMap.adjoint (LinearPMap.adjoint (dbarOp2 φ)) = dbarOp2 φ :=
    Commons.Analysis.InnerProductSpace.LinearPMap.adjoint_adjoint_of_isClosed (dbarOp2 φ)
      (dense_domain_dbarOp2 hφ1) (isClosed_dbarOp2 hφ1)
  have hdec :=
    Commons.Analysis.InnerProductSpace.LinearPMap.orthogonal_decomposition_of_range_le_ker
      (dbarOp2 φ) (dbarOpMin φ) (dense_domain_dbarOp2 hφ1) hvnS (dense_domain_dbarOpMin hφ1)
      (dbarOpMin_range_le_ker hφ)
  obtain ⟨u, hu, huv, hun⟩ :=
    Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound
      (dbarOpMin φ) (dbarOp2 φ) (dense_domain_dbarOpMin hφ1) (dense_domain_dbarOp2 hφ1)
      (dbarOpMin_adjoint_adjoint hφ1) hdec hCnn v hvdom hvzero (fun x => by
        have hxmem : (x : H2 φ) ∈ (dbarAdjOp φ).domain := by
          rw [← dbarOpMin_adjoint hφ1]
          exact x.2.2
        have h := hbound_friedrichs hφ hd hκc hκpos hηc hηint hhess hηm (x : H2 φ) x.2.1 hxmem
        have hEq : ((dbarOpMin φ).adjoint) ⟨(x : H2 φ), x.2.2⟩
            = (dbarAdjOp φ) ⟨(x : H2 φ), hxmem⟩ :=
          (LinearPMap.ext_iff.mp (dbarOpMin_adjoint hφ1)).2 (x := (x : H2 φ)) (hf := x.2.2) (hg := hxmem)
        rw [hEq]
        exact h)
  refine ⟨u, ?_, hun⟩
  change DbarWeak φ u v
  rw [← huv]
  exact dbarOpMin_weak hφ1 hu

end Existence

end
end Submission.FUP
