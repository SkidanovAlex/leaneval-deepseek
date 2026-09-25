import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

theorem iteratedDeriv_comp_smul_eq_iteratedFDeriv {m r : ℕ} (f : (Fin m → ℂ) → ℂ)
    (a : Fin m → ℂ) (hf : ContDiff ℂ r f) :
    iteratedDeriv r (fun t : ℂ => f (t • a)) 0 = iteratedFDeriv ℂ r f 0 (fun _ => a) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  set L : ℂ →L[ℂ] (Fin m → ℂ) := ContinuousLinearMap.toSpanSingleton ℂ a with hLdef
  have hL : ∀ t : ℂ, L t = t • a := by
    intro t
    rw [hLdef, ContinuousLinearMap.toSpanSingleton_apply]
  have hcomp : (fun t : ℂ => f (t • a)) = f ∘ L := by
    funext t
    simp only [Function.comp_apply, hL t]
  rw [hcomp]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hf (0 : ℂ) (i := r) le_rfl]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hL 0, hL 1, zero_smul, one_smul]

end Commons.Analysis.Calculus