import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_trace

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

/-!
# L4b, the pullback disjointness of the level's sphere cover

The bundle `Work.Drive.Final.SphereCoverAt` covers the frontier of the level's removed set by
embedded spheres whose *traces on the surface* are pairwise disjoint.  Disjointness of the traces does
**not** survive the pullback along the dent `D.deform`: a point `y` of the surface whose image
`D.deform y` lies in the intersection of two of the spheres (a point which, being off the surface, is
not forbidden by the cover) would lie in the traces of both pulled-back spheres.

What rescues the clause is exactly the *smallness* of the dent.  A pair of spheres whose traces fail
to be disjoint misses the surface only by a margin `η` (`hη`); the dent moves every point by at most
`D.a'`, so if the intersection point of the two spheres is the image of a surface point then it is at
distance at most `a'` from the surface, contradicting the margin as soon as `D.a' < η`.

The two ingredients are
* `anyDentDeform_sub_le`: the dent moves every point by at most `D.a'`
  (`‖D.deform z - z‖ ≤ D.a'`, from `‖d‖ = 1` and `|χ| ≤ 1`), and
* `dist` is `‖·-·‖`, so `hη` at the pair `(D.deform y, y)` bounds `a'` from above by `η`.
-/

/-- **The dent moves every point by at most its depth.**  For the datum of an event of any of the
three types (`AnyDentDatum`), `‖D.deform z - z‖ ≤ D.a'`: the displacement is
`(a' · χ(‖z - centre‖/r)) • d` with `‖d‖ = 1` and `|χ| ≤ 1`. -/
theorem anyDentDeform_sub_le {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    ‖D.deform z - z‖ ≤ D.a' := by
  have hz_eq : D.deform z = z + (D.a' * D.χ (‖z - D.centre‖ / D.r)) • D.d := by
    simp [AnyDentDatum.deform, dentDeform]
  rw [hz_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, D.d_norm, mul_one, abs_mul,
    abs_of_pos D.a'_pos]
  exact mul_le_of_le_one_right (le_of_lt D.a'_pos) (D.χ_le_one _)

/-- **L4b: the pulled-back traces of two distinct spheres of the cover are disjoint.**

Let `Ss` cover the frontier of the undeformed level's removed set by embedded spheres
(`Work.Drive.Final.SphereCoverAt`), and suppose that two distinct spheres of the cover meet only off
the surface by a margin `η`: every point of `Ss i ∩ Ss j` is at distance at least `η` from the
carrier (`hη`).  If the dent is shallow (`D.a' < η`) then the traces on the surface of the
*pulled-back* spheres `D.deform ⁻¹' Ss i` and `D.deform ⁻¹' Ss j` are disjoint — so the clause
demanded by `Work.Drive.Final.EventTraceData` (and consumed by
`Work.Drive.Final.dentOut_trace_noEssential_of_sphereCover`) holds.

Indeed a common point `y` of the surface would have `D.deform y ∈ Ss i ∩ Ss j` at distance
`‖D.deform y - y‖ ≤ D.a' < η` from the surface point `y`, contradicting `hη`. -/
theorem dent_pullback_disjoint {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {m : ℕ} {Ss : Fin m → Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) {η : ℝ}
    (hη : ∀ i j : Fin m, i ≠ j → ∀ x : R3, x ∈ (Ss i ∩ Ss j) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → η ≤ dist x z)
    (ha : D.a' < η) :
    ∀ i j : Fin m, i ≠ j →
      Disjoint ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨hxi, hxc⟩ ⟨hxj, -⟩
  -- `x` is a surface point whose image under the dent lies in `Ss i ∩ Ss j`
  have hmem : D.deform x ∈ Ss i ∩ Ss j := ⟨hxi, hxj⟩
  have hηx := hη i j hij (D.deform x) hmem x hxc
  -- ... hence at distance at most `D.a'` from the surface
  have hle : dist (D.deform x) x ≤ D.a' := by
    rw [dist_eq_norm]
    exact anyDentDeform_sub_le D x
  linarith

end Work.Drive.Final
