import Mathlib
import Submission.Work.WilE7.DimAPI.fderiv_gamma_mem_ker

open Filter
namespace Work.WilE7.CoreStep

theorem fderiv_chart_eq_self {q k : ℕ} (G : (Fin q → ℝ) → (Fin k → ℝ))
    (C : (Fin q → ℝ) →L[ℝ] (fderiv ℝ G 0).ker)
    (γ : (fderiv ℝ G 0).ker → (Fin q → ℝ))
    (V : Set (fderiv ℝ G 0).ker)
    (hGan : AnalyticAt ℝ G 0) (hγ0 : γ 0 = 0) (hγan : AnalyticAt ℝ γ 0)
    (hCid : ∀ x : (fderiv ℝ G 0).ker, C ↑x = x)
    (hVopen : IsOpen V) (h0V : (0 : (fderiv ℝ G 0).ker) ∈ V)
    (hlevel : ∀ v ∈ V, G (γ v) = G 0)
    (hCγ : ∀ v ∈ V, C (γ v) = v) :
    ∀ u : (fderiv ℝ G 0).ker, (fderiv ℝ γ 0) u = (u : Fin q → ℝ) := by
  intro u
  have hVmem : V ∈ nhds (0 : (fderiv ℝ G 0).ker) := hVopen.mem_nhds h0V
  have hlev_ev : ∀ᶠ s in nhds (0 : (fderiv ℝ G 0).ker), G (γ s) = G 0 :=
    Filter.eventually_of_mem hVmem (fun s hs => hlevel s hs)
  have hmem := Work.WilE7.DimAPI.fderiv_gamma_mem_ker (n := q) (k := k)
      (E := (fderiv ℝ G 0).ker) (g := G) (p := 0) (γ := γ) hGan hγ0 hγan hlev_ev
  have hCγev : (fun v : (fderiv ℝ G 0).ker => C (γ v)) =ᶠ[nhds 0] (fun v => v) :=
    Filter.eventually_of_mem hVmem (fun s hs => hCγ s hs)
  have hγdiff : DifferentiableAt ℝ γ 0 := hγan.differentiableAt
  have hcomp : C.comp (fderiv ℝ γ 0) = ContinuousLinearMap.id ℝ (fderiv ℝ G 0).ker := by
    have h1 : fderiv ℝ (fun v : (fderiv ℝ G 0).ker => C (γ v)) 0
        = C.comp (fderiv ℝ γ 0) := by
      exact (C.hasFDerivAt.comp 0 hγdiff.hasFDerivAt).fderiv
    rw [← h1, hCγev.fderiv_eq, fderiv_fun_id]
  have hDu := hmem u
  have h1 : C ((fderiv ℝ γ 0) u) = u := by
    have := DFunLike.congr_fun hcomp u
    simpa [ContinuousLinearMap.comp_apply] using this
  have h2 : ((C ((fderiv ℝ γ 0) u) : (fderiv ℝ G 0).ker) : Fin q → ℝ)
      = (fderiv ℝ γ 0) u := by
    have := congrArg (fun x : (fderiv ℝ G 0).ker => (x : Fin q → ℝ))
      (hCid ⟨(fderiv ℝ γ 0) u, hDu⟩)
    simpa using this
  rw [← h2]
  exact congrArg (fun x : (fderiv ℝ G 0).ker => (x : Fin q → ℝ)) h1

end Work.WilE7.CoreStep
