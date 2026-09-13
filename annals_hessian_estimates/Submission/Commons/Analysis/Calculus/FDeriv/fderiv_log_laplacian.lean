import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_comp_perm_of_contDiffOn
import Submission.Commons.Analysis.Calculus.FDeriv.secondPartial_directional_deriv

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem fderiv_log_laplacian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E}
    {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s)
    (hL : ∀ z ∈ s, (Laplacian.laplacian u) z ≠ 0) (i : ι) :
    fderiv ℝ (fun z => Real.log ((Laplacian.laplacian u) z)) x (v i) =
      (∑ j : ι, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Laplacian.laplacian u) x := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have huAt : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  have hLx : (Laplacian.laplacian u) x ≠ 0 := hL x hx
  have hL_eq : Laplacian.laplacian u
      = fun z => ∑ j : ι, (iteratedFDeriv ℝ 2 u z) ![v j, v j] :=
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v
  have hφdiff : ∀ j : ι,
      DifferentiableAt ℝ (fun z => (iteratedFDeriv ℝ 2 u z) ![v j, v j]) x := by
    intro j
    have h1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 u) x :=
      huAt.iteratedFDeriv_right (i := 2) (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun z => (iteratedFDeriv ℝ 2 u z) ![v j, v j]) x :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ) ![v j, v j]).contDiff.comp_contDiffAt
        x h1
    exact h2.differentiableAt one_ne_zero
  have hsumHas : HasFDerivAt (fun z => ∑ j : ι, (iteratedFDeriv ℝ 2 u z) ![v j, v j])
      (∑ j : ι, fderiv ℝ (fun z => (iteratedFDeriv ℝ 2 u z) ![v j, v j]) x) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hφdiff j).hasFDerivAt)
  have hLdiff : DifferentiableAt ℝ (Laplacian.laplacian u) x := by
    rw [hL_eq]; exact hsumHas.differentiableAt
  have hLderiv : fderiv ℝ (Laplacian.laplacian u) x (v i)
      = ∑ j : ι, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i] := by
    rw [hL_eq, hsumHas.fderiv]
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [secondPartial_directional_deriv hs hx hu (v j) (v j) (v i)]
    have hperm_eq : ![v i, v j, v j] ∘ (Equiv.swap (0 : Fin 3) 2) = ![v j, v j, v i] := by
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
    have h1 := iteratedFDeriv_comp_perm_of_contDiffOn hs hx hu
      (m := ![v i, v j, v j]) (σ := Equiv.swap (0 : Fin 3) 2)
    rw [hperm_eq] at h1
    exact h1.symm
  have hlog : fderiv ℝ (fun z => Real.log ((Laplacian.laplacian u) z)) x
      = ((Laplacian.laplacian u) x)⁻¹ • fderiv ℝ (Laplacian.laplacian u) x :=
    (hLdiff.hasFDerivAt.log hLx).fderiv
  rw [hlog, smul_apply, hLderiv, smul_eq_mul, div_eq_inv_mul]

end Commons.Analysis.Calculus.FDeriv