import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Set Function Metric
open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.STE.B3

theorem transport_exists_cutoff {n : ℕ} (K U : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ z, 0 ≤ η z) ∧ (∀ z ∈ K, η z = 1) ∧ tsupport η ⊆ U := by
  -- A positive thickening of the compact set `K` stays inside the open set `U`.
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Smooth Urysohn on the Euclidean space `Fin n → ℝ` (a σ-compact Hausdorff manifold for the
  -- model `𝓘(ℝ, Fin n → ℝ)`): a smooth function that is `0` on a closed neighbourhood of `Uᶜ`
  -- (namely the complement of the open thickening) and `1` on `K`, with values in `[0,1]`.
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, Fin n → ℝ)) (M := Fin n → ℝ) (n := ⊤)
      (s := (Metric.thickening δ K)ᶜ) (t := K)
      Metric.isOpen_thickening.isClosed_compl
      hK.isClosed
      (Set.disjoint_left.mpr fun x hx hxK => hx (Metric.self_subset_thickening hδpos K hxK))
  refine ⟨fun z => f z, ?_, fun z => (hf01 z).1, fun z hz => hf1 hz, ?_⟩
  · -- smoothness: the manifold model on `Fin n → ℝ` is the self model, so `CMDiff` is `ContDiff`
    exact contMDiff_iff_contDiff.mp f.contMDiff
  · -- the support sits in the thickening, whose closure is the closed thickening inside `U`
    have hsupp : Function.support (fun z => f z) ⊆ Metric.thickening δ K := by
      intro w hw
      by_contra hw'
      exact hw (hf0 hw')
    intro z hz
    exact hδ (Metric.closure_thickening_subset_cthickening δ K (closure_mono hsupp hz))

end Work.Diff.STE.B3
