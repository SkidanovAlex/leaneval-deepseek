import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Finite.dist_lt_of_mesh

namespace Work.PL.Approx.Near

lemma oscillation_of_mesh {N n : ℕ} (K K' : PL.Cx N) (hsub : PL.Subdivides K' K) (f : PL.E N → PL.E n)
    {δ ε : ℝ} (hmesh : PL.MeshLT K' δ)
    (hδ : ∀ x ∈ K.space, ∀ y ∈ K.space, dist x y < δ → dist (f x) (f y) < ε) :
    ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < ε := by
  intro s hs x hx y hy
  have hxK' : x ∈ K'.space := K'.convexHull_subset_space hs hx
  have hyK' : y ∈ K'.space := K'.convexHull_subset_space hs hy
  have hxK : x ∈ K.space := hsub.1 ▸ hxK'
  have hyK : y ∈ K.space := hsub.1 ▸ hyK'
  exact hδ x hxK y hyK (Finite.dist_lt_of_mesh K' hmesh hs hx hy)

end Work.PL.Approx.Near
