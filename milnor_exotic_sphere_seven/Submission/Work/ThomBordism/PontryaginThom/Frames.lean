import Submission.Work.ThomBordism.PontryaginThom.Pad
import Submission.Work.ThomBordism.Grassmann.Linear

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The frames of an immersion, in the charts

This file fixes the **manifold-side data** of the construction of the normal bundle of an immersion
`f : V → ℝ^{k+8}` (`V` a `Man8`), namely the frames `A i x` of `im (d f_x)` in the chart `i` of `V`:

* `chartRep f i = f ∘ i.symm` — the chart representative of `f` (with junk value outside the chart's
  target);
* `frame f i x j` — the `j`-th column of the derivative of the chart representative at the chart
  coordinates of `x`.

The two facts about them that the construction consumes are stated in the module docstring below and
are the residual differential-geometric content of item 1:

1. **continuity** (`ContinuousOn (fun x => frame f i x) i.1.source`): the derivative of a `C¹` map
   depends continuously on the point, in a chart;
2. **the chart independence of the plane** (`LinearMap.range (coeffMap (frame f i x)) =
   LinearMap.range (coeffMap (frame f j x))` on the overlap): the chain rule — the frames of two
   charts differ by the (invertible) derivative of the chart change, so they span the same subspace
   `im (d f_x)` of `ℝ^{k+8}`.  This is what makes the plane (`ker (P i x)` of the complement data)
   chart-independent, i.e. the hypothesis `ComplementData.ker_agree`.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

/-- The chart representative of `f` in the chart `i`: `f ∘ i.symm`, with the junk value `f (i.symm y)`
outside the target of `i` (where it is never used). -/
def chartRep {V : Man8} {k : ℕ} (f : V.pt → Euc (8 + k)) (i : atlas (Euc 8) V.pt) :
    Euc 8 → Euc (8 + k) :=
  fun y => f (i.1.symm y)

/-- **The frame of the immersion `f` in the chart `i` at `x`**: the `j`-th column is the derivative
of the chart representative at the chart coordinates of `x`, applied to the `j`-th basis vector. -/
def frame {V : Man8} {k : ℕ} (f : V.pt → Euc (8 + k)) (i : atlas (Euc 8) V.pt)
    (x : V.pt) : Fin 8 → Euc (8 + k) :=
  fun j => fderiv ℝ (chartRep f i) (i.1 x) (EuclideanSpace.single j 1)

/-! ## The two facts about the frame -/

/-- **The frame depends continuously on the point, in a chart**: the derivative of the `C¹` chart
representative `f ∘ i.symm` is continuous on the chart's target, and the chart coordinates of `x`
give the claim. -/
theorem continuousOn_frame {V : Man8} {k : ℕ} (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i : atlas (Euc 8) V.pt) :
    ContinuousOn (fun x => frame f i x) (i.1.source) := by
  have hmem : i.1 ∈ IsManifold.maximalAtlas (𝓡 8) 1 V.pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := 1) i.2
  have hsymm : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓡 8) 1 (fun y => i.1.symm y) i.1.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hmem
  have hcomp : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓘(ℝ, Euc (8 + k))) 1
      (fun y => f (i.1.symm y)) i.1.target :=
    (hf.contMDiffOn).comp hsymm (t := Set.univ) (fun y _ => Set.mem_univ (i.1.symm y))
  have hg : ContDiffOn ℝ 1 (chartRep f i) i.1.target := hcomp.contDiffOn
  have hfd : ContinuousOn (fun y => fderiv ℝ (chartRep f i) y) i.1.target :=
    hg.continuousOn_fderiv_of_isOpen i.1.open_target le_rfl
  have hcomp2 : ContinuousOn (fun x => fderiv ℝ (chartRep f i) (i.1 x)) i.1.source :=
    hfd.comp i.1.continuousOn (fun x hx => i.1.map_source hx)
  refine continuousOn_pi.mpr fun j => ?_
  simpa only [frame, chartRep] using
    (hcomp2.clm_apply (continuousOn_const :
      ContinuousOn (fun _ : V.pt => EuclideanSpace.single j (1 : ℝ)) i.1.source))

end

end Work.ThomBordism.PontryaginThom
