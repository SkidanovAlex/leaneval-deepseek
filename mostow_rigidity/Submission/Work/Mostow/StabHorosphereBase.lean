import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper

/-!
# Base lemmas for the horospherical stabiliser

`abs_hdist_sub_le`, `busemann_lipschitz` and `bCocy_parabolic`, factored out of
`Work.Mostow.geomFiniteStabHorosphere` so that the horizon-level cocycle lemmas
(`parabolic_not_commute_levelScaling` and friends) can use them without importing the
target module (which would be an import cycle).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Reverse triangle inequality for `hdist`. -/
lemma abs_hdist_sub_le (hI : HypIsometryProp n) (u v w : E n) :
    |hdist u w - hdist v w| ≤ hdist u v := by
  have hsym : ∀ a b : E n, hdist a b = hdist b a := hI.2.1
  have htri : ∀ a b c : E n, hdist a c ≤ hdist a b + hdist b c := hI.2.2.2.1
  have h1 : hdist u w ≤ hdist u v + hdist v w := htri u v w
  have h2 : hdist v w ≤ hdist v u + hdist u w := htri v u w
  rw [hsym v u] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- The Busemann function is `1`-Lipschitz for the hyperbolic distance. -/
theorem busemann_lipschitz (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n) (u v : E n) :
    |busemann ξ u - busemann ξ v| ≤ hdist u v := by
  have h1 : Filter.Tendsto (fun t : ℝ => hdist u (Real.sinh t • ξ) - t) Filter.atTop
      (nhds (busemann ξ u)) := BusemannRay n ξ hξ u
  have h2 : Filter.Tendsto (fun t : ℝ => hdist v (Real.sinh t • ξ) - t) Filter.atTop
      (nhds (busemann ξ v)) := BusemannRay n ξ hξ v
  have h3 : Filter.Tendsto
      (fun t : ℝ => (hdist u (Real.sinh t • ξ) - t) - (hdist v (Real.sinh t • ξ) - t))
      Filter.atTop (nhds (busemann ξ u - busemann ξ v)) := h1.sub h2
  have h3' : Filter.Tendsto (fun t : ℝ => hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ))
      Filter.atTop (nhds (busemann ξ u - busemann ξ v)) := by
    refine Filter.Tendsto.congr (fun t => ?_) h3
    ring
  have h4 : Filter.Tendsto (fun t : ℝ => |hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ)|)
      Filter.atTop (nhds |busemann ξ u - busemann ξ v|) := h3'.abs
  have h5 : ∀ t : ℝ,
      |hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ)| ≤ hdist u v :=
    fun t => abs_hdist_sub_le hI u v _
  exact le_of_tendsto h4 (Filter.Eventually.of_forall h5)

/-! ## Step 2: the Busemann cocycle of a parabolic element fixing `ξ` vanishes -/

/-- A parabolic element `g` with `bd g ξ = ξ` preserves every horosphere at `ξ`. -/
theorem bCocy_parabolic (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hg : IsParabolic g) (ξ : E n) (hξ : ξ ∈ Sph n) (hgξ : bd g ξ = ξ) :
    bCocy g ξ = 0 := by
  have hbus : ∀ (g : PO n 1) (ξ u : E n), ξ ∈ Sph n →
      busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0) := hI.2.2.2.2.2.2.2.2.2.2.2.2
  have hsym : ∀ a b : E n, hdist a b = hdist b a := hI.2.1
  have hkey : ∀ u : E n, bCocy g ξ = busemann ξ (g • u) - busemann ξ u := by
    intro u
    have h := hbus g ξ u hξ
    rw [hgξ] at h
    simp only [bCocy, hgξ]
    linarith
  have hbdd : ∀ u : E n, |bCocy g ξ| ≤ hdist (g • u) u := by
    intro u
    rw [hkey u]
    exact busemann_lipschitz hI ξ hξ (g • u) u
  by_contra hne
  have hpos : 0 < |bCocy g ξ| := abs_pos.2 hne
  obtain ⟨u, hu⟩ := hg.2 |bCocy g ξ| hpos
  have h := hbdd u
  have h2 : hdist (g • u) u = hdist u (g • u) := hsym (g • u) u
  linarith

end

end Work.Mostow
