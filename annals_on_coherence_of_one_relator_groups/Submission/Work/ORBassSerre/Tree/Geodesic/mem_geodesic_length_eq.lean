import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Geodesic.exists_decomp_of_mem_vertices
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq

namespace Work.ORBassSerre.Tree.Geodesic

universe u

/-- Along the geodesic from `z` to `b` in a tree, the distance to `z` is strictly increasing:
two vertices of the geodesic at the same distance from `z` coincide. -/
theorem mem_geodesic_length_eq {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) {z b x y : V}
    (hx : x ∈ (hT.geodesic z b).vertices) (hy : y ∈ (hT.geodesic z b).vertices)
    (hl : (hT.geodesic z x).length = (hT.geodesic z y).length) : x = y := by
  have hp : (hT.geodesic z b).IsReduced := hT.geodesic_isReduced z b
  -- Split the geodesic `z ↝ b` at `x`, resp. at `y`, obtaining reduced prefixes.
  obtain ⟨ux, vx, hux, _, hcompx, _⟩ := exists_decomp_of_mem_vertices hp hx
  obtain ⟨uy, vy, huy, _, hcompy, _⟩ := exists_decomp_of_mem_vertices hp hy
  -- Each prefix is the (unique) geodesic of its endpoints.
  have ex : ux = hT.geodesic z x := hT.eq_geodesic hux
  have ey : uy = hT.geodesic z y := hT.eq_geodesic huy
  -- Hence the two prefixes have the same length.
  have hlen : ux.length = uy.length := by rw [ex, ey]; exact hl
  -- They are two decompositions of the same path, so the endpoint is determined.
  have hcomp : ux.comp vx = uy.comp vy := by rw [hcompx, hcompy]
  exact Work.ORBassSerre.Tree.Prefix.eq_endpoint_of_comp_eq_comp_of_length_eq
    ux vx uy vy hcomp hlen

end Work.ORBassSerre.Tree.Geodesic
