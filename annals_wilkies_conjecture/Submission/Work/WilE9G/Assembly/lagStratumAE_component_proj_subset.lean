import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Assembly.lagStratumAE_takeZ_mem
import Submission.Work.WilE9G.Assembly.stratProj_takeZ
import Submission.Work.WilE7.pad_component_proj

namespace Work.WilE9G.Assembly

/-- **The projection of a connected component of the Lagrange stratum lands in the projection of a
single component of `X`.**

Every point `w` of the Lagrange stratum's set has its `(x, (y,t))`-part `takeZ w` in `S.X.set`, hence
in `X.set` (since `S.X.set ⊆ X.set`), and `stratProj` only reads the first `n + 1` coordinates, so
`stratProj w = stratProj (takeZ w)`.  The component of `q` is preconnected, so its `takeZ`-image is
preconnected and contained in `X.set`; since by hypothesis it meets the component of `z₀`, it is
contained in that component. -/
theorem lagStratumAE_component_proj_subset {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (X : WilkiesDesign.E.SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
    (hSX : S.X.set ⊆ X.set)
    (q : Fin (n + (1 + (m + S.j + 1))) → ℝ)
    (hmem : ∃ w'' ∈ connectedComponentIn (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set q,
      Work.WilE7.takeZ (by omega : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) w''
        ∈ connectedComponentIn X.set z₀) :
    ∀ w ∈ connectedComponentIn (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set q,
      Work.WilE9.Sharp.stratProj w
        ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ := by
  have hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)) := by omega
  intro w hw
  obtain ⟨w'', hw''C, hw''Z⟩ := hmem
  -- The `takeZ`-image of the component of `q` ...
  -- ... is preconnected (continuous image of a preconnected set),
  have hTpre : IsPreconnected
      (Work.WilE7.takeZ hm ''
        connectedComponentIn (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set q) :=
    (isPreconnected_connectedComponentIn (x := q)).image _
      (Work.WilE7.continuous_takeZ hm).continuousOn
  -- ... lies in `X.set` (`takeZ` lands in `S.X.set ⊆ X.set`),
  have hTsub : Work.WilE7.takeZ hm ''
      connectedComponentIn (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set q ⊆ X.set := by
    rintro y ⟨u, hu, rfl⟩
    exact hSX (lagStratumAE_takeZ_mem S Phi c u (connectedComponentIn_subset _ _ hu))
  -- ... and meets the component of `z₀`.
  have hTmem : Work.WilE7.takeZ hm w'' ∈ Work.WilE7.takeZ hm ''
      connectedComponentIn (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set q :=
    ⟨w'', hw''C, rfl⟩
  have hsub : Work.WilE7.takeZ hm ''
      connectedComponentIn (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set q ⊆
      connectedComponentIn X.set z₀ := by
    rw [connectedComponentIn_eq hw''Z]
    exact hTpre.subset_connectedComponentIn hTmem hTsub
  exact ⟨Work.WilE7.takeZ hm w, hsub ⟨w, hw, rfl⟩, stratProj_takeZ hm w⟩

end Work.WilE9G.Assembly
