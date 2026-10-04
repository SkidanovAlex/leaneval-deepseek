import Mathlib
import Submission.Work.Diff.EXT.ufslice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.JetConv

open scoped Topology

/-- The `k`-th iterated time derivative `q ↦ iteratedDeriv k (fun s => u (s, q.2)) q.1` of a `C^∞`
function `u` on an open set `V` is itself `C^∞` on `V`.

Route: prove first that `q ↦ (iteratedFDeriv ℝ k u q) (fun _ => (1,0))` is `C^∞` on `V` (it is the
composite of `iteratedFDeriv ℝ k u` — smooth by `ContDiffAt.iteratedFDeriv_right` — with the
continuous linear map `ContinuousMultilinearMap.apply`), then transfer along the pointwise equality
on `V` given by `Work.Diff.EXT.tder_eq_jet` using `ContDiffOn.congr`. -/
theorem tDer_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {V : Set (ℝ × E)} (hV : IsOpen V) {u : ℝ × E → Z}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u V) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => u (s, q.2)) q.1) V := by
  -- The "full jet" expression `q ↦ (iteratedFDeriv ℝ k u q) (1,0,…,1,0)` is `C^∞` on `V`: it is
  -- the composite of the smooth `q ↦ iteratedFDeriv ℝ k u q` with the continuous linear map
  -- `ContinuousMultilinearMap.apply` (evaluation at the fixed tuple `oneTup E k`).
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (Work.Diff.EXT.oneTup E k)) V := by
    rw [hV.contDiffOn_iff]
    intro a ha
    have hua : ContDiffAt ℝ (⊤ : ℕ∞) u a := hu.contDiffAt (hV.mem_nhds ha)
    have hjet : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × E => iteratedFDeriv ℝ k u q) a :=
      hua.iteratedFDeriv_right (by simp)
    have hclm : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z =>
          x (Work.Diff.EXT.oneTup E k)) (iteratedFDeriv ℝ k u a) :=
      (ContinuousLinearMap.contDiff
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z
          (Work.Diff.EXT.oneTup E k))).contDiffAt
    exact hclm.comp a hjet
  -- Transfer to the iterated time derivative along the pointwise identity on `V`.
  exact ContDiffOn.congr hF fun x hx => Work.Diff.EXT.tder_eq_jet hV hu hx k

end Work.Diff.EXT.JetConv
