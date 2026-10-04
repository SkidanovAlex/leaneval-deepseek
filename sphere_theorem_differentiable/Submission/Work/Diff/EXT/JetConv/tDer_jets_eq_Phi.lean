import Mathlib
import Submission.Work.Diff.EXT.ufslice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.JetConv

open Filter
open scoped Topology

/-- The ambient jets of the `k`-th time derivative of `u` agree, at every point `p` of an open set
`V` on which `u` is `C^∞`, with those of the "full jet" expression
`q ↦ (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))`.  (The two functions agree on `V`
pointwise by `Work.Diff.EXT.tder_eq_jet`; the jets are then computed with
`iteratedFDerivWithin_congr` and `iteratedFDerivWithin_of_isOpen`, or with
`Filter.EventuallyEq.iteratedFDeriv` and `hV.mem_nhds`.) -/
theorem tDer_jets_eq_Phi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {V : Set (ℝ × E)} (hV : IsOpen V) {u : ℝ × E → Z}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u V) {p : ℝ × E} (hp : p ∈ V) (m k : ℕ) :
    iteratedFDeriv ℝ m (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => u (s, q.2)) q.1) p
      = iteratedFDeriv ℝ m
          (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))) p := by
  have h : (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => u (s, q.2)) q.1)
      =ᶠ[𝓝 p]
        (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact Work.Diff.EXT.tder_eq_jet (Z := Z) hV hu hq k
  exact (h.iteratedFDeriv ℝ m).eq_of_nhds

end Work.Diff.EXT.JetConv
