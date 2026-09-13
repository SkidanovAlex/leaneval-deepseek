import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.RCLike.Basic

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology in
theorem iteratedFDeriv_apply_congr_of_eventuallyEq {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {x : E} {n : ℕ} (h : f =ᶠ[nhds x] g) (m : Fin n → E) :
    (iteratedFDeriv 𝕜 n f x) m = (iteratedFDeriv 𝕜 n g x) m := by
  have key : iteratedFDeriv 𝕜 n f =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n g :=
    Filter.EventuallyEq.iteratedFDeriv 𝕜 h n
  exact congrArg (fun (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F) => φ m)
    key.self_of_nhds

end Commons.Analysis.Calculus.FDeriv