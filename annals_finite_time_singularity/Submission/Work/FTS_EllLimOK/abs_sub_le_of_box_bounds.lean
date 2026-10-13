import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem abs_sub_le_of_box_bounds {g : ℝ → ℝ → ℝ} {a b c d L : ℝ}
    (hz : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
      HasDerivWithinAt (fun z' : ℝ => g z' θ) (Work.Spaces.pz g z θ) (Set.Icc a b) z)
    (hth : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt (fun θ' : ℝ => g z θ') (Work.Spaces.pth g z θ) (Set.Icc c d) θ)
    (hzb : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, |Work.Spaces.pz g z θ| ≤ L)
    (hthb : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, |Work.Spaces.pth g z θ| ≤ L) :
    ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d,
      |g p.1 p.2 - g q.1 q.2| ≤ L * (|p.1 - q.1| + |p.2 - q.2|) := by
  intro p hp q hq
  rw [Set.mem_prod] at hp hq
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  -- Mean value inequality along the `z`-direction, at fixed angle `p.2`.
  have hzline : ‖g p.1 p.2 - g q.1 p.2‖ ≤ L * ‖p.1 - q.1‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z' : ℝ => g z' p.2) (f' := fun z' : ℝ => Work.Spaces.pz g z' p.2)
      (fun z' hz' => hz p.2 hp2 z' hz')
      (fun z' hz' => by simpa using hzb z' hz' p.2 hp2)
      (convex_Icc a b) hq1 hp1
  -- Mean value inequality along the `θ`-direction, at fixed radius `q.1`.
  have hthline : ‖g q.1 p.2 - g q.1 q.2‖ ≤ L * ‖p.2 - q.2‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun θ' : ℝ => g q.1 θ') (f' := fun θ' : ℝ => Work.Spaces.pth g q.1 θ')
      (fun θ' hθ' => hth q.1 hq1 θ' hθ')
      (fun θ' hθ' => by simpa using hthb q.1 hq1 θ' hθ')
      (convex_Icc c d) hq2 hp2
  have h1 : |g p.1 p.2 - g q.1 p.2| ≤ L * |p.1 - q.1| := by simpa using hzline
  have h2 : |g q.1 p.2 - g q.1 q.2| ≤ L * |p.2 - q.2| := by simpa using hthline
  calc |g p.1 p.2 - g q.1 q.2|
      = |(g p.1 p.2 - g q.1 p.2) + (g q.1 p.2 - g q.1 q.2)| := by ring_nf
    _ ≤ |g p.1 p.2 - g q.1 p.2| + |g q.1 p.2 - g q.1 q.2| := abs_add_le _ _
    _ ≤ L * |p.1 - q.1| + L * |p.2 - q.2| := add_le_add h1 h2
    _ = L * (|p.1 - q.1| + |p.2 - q.2|) := by ring

end Work.FTS_EllLimOK
