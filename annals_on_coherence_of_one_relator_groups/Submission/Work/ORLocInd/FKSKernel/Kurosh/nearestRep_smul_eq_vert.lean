import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection
import Submission.Work.ORBassSerre.Tree.Seg.smul_reducedSpan
import Submission.Work.ORBassSerre.Tree.Seg.reducedSpan_eq_union_of_mem
import Submission.Work.ORBassSerre.Tree.Seg.eq_of_mem_reducedSpan_of_geodesic_length_eq
import Submission.Work.ORBassSerre.Tree.Convex.reducedSpan_or
import Submission.Work.ORBassSerre.Tree.Seg.reducedSpan_comm

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre

universe u

/-!
# The nearest representative after translation by a vertex stabiliser

Let `G` act on a tree `V`, let `d : TreeDatum G V` be a spanning tree datum with
`repSet d = Set.range d.vert` the set of chosen representatives of the vertex orbits, and let
`hbetween` express that `repSet d` is convex.  Then (see `nearestRep_projection`) the nearest
representative `nearestRep hT d v` of a vertex `v` behaves like the orthogonal projection of `v`
onto the convex set `repSet d`.

The purpose of this file is the "trap" lemma used in the ping-pong proof of the Kurosh subgroup
theorem: if `h ≠ 1` fixes the representative `d.vert A` of the vertex orbit `A` (i.e. `h` lies in
the vertex group `d.vgroup A`) and `v` is a vertex whose nearest representative is *not*
`d.vert A`, then the nearest representative of `h • v` *is* `d.vert A`.

The mathematical content is the following.  Let `R = repSet d` and let `T = h • R` be the
translate of `R` by `h`.  Both are convex sets of orbit representatives, and they meet only in
`d.vert A`: if `x ∈ R ∩ T` then `x = d.vert B = h • d.vert C` for some orbits `B`, `C`; the two
sides lie in the same vertex orbit, so `B = C`, hence `h` fixes `x`, and `hfixpt` (a non-trivial
element fixes at most one vertex) forces `x = d.vert A`.

Now let `r = nearestRep hT d v ≠ d.vert A` and `r' = nearestRep hT d (h • v)`.  Since `h` fixes
`d.vert A`, the segment from `h • v` to `d.vert A` is the translate of the segment from `v` to
`d.vert A`, so both `r'` and `h • r` lie on the geodesic from `d.vert A` to `h • v`.  As `R` is
convex, `reducedSpan (d.vert A) r' ⊆ R`, and as `T` is convex, `reducedSpan (d.vert A) (h • r) ⊆
T`.  If `r' ≠ d.vert A` (and hence `h • r ≠ d.vert A`, since `h` is injective), the comparability
of two points of a segment of a tree (`mem_reducedSpan_or_of_mem_reducedSpan`) puts `r'` on the
segment from `d.vert A` to `h • r`, or `h • r` on the segment from `d.vert A` to `r'`; either way
one of `r'`, `h • r` lies in both `R` and `T`, hence equals `d.vert A` — a contradiction.
-/

section Aux

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- **Distance is additive along a segment of a tree**: if `c` lies on the geodesic from `a` to
`b`, then `dist a b = dist a c + dist c b`. -/
theorem dist_add_of_mem (hT : IsTree V) {a b c : V} (hc : c ∈ reducedSpan a b) :
    dist hT a b = dist hT a c + dist hT c b := by
  obtain ⟨p₁, p₂, heq, hp₁, hp₂⟩ :=
    Tree.Seg.geodesic_eq_comp_geodesic_of_mem (hT := hT) hc
  rw [dist, dist, dist, heq, Quiver.Path.length_comp, hp₁, hp₂]

/-- **Two points of a segment from `a` are comparable**: if `x` and `y` both lie on the geodesic
from `a` to `z`, then one of them lies on the segment from `a` to the other. -/
theorem mem_reducedSpan_or_of_mem_reducedSpan (hT : IsTree V) {a z x y : V}
    (hx : x ∈ reducedSpan a z) (hy : y ∈ reducedSpan a z) :
    x ∈ reducedSpan a y ∨ y ∈ reducedSpan a x := by
  rcases Tree.Convex.reducedSpan_or hT a z y hx with h1 | h1
  · exact Or.inl h1
  · -- `x` lies on the segment from `z` to `y`, i.e. from `y` to `z`
    rw [Tree.Seg.reducedSpan_comm z y] at h1
    rcases Tree.Convex.reducedSpan_or hT a z x hy with h2 | h2
    · exact Or.inr h2
    · -- `y` lies on the segment from `z` to `x`, i.e. from `x` to `z`
      rw [Tree.Seg.reducedSpan_comm z x] at h2
      -- in that case the two distance identities force `x = y`
      have e1 := dist_add_of_mem hT h1
      have e2 := dist_add_of_mem hT h2
      have h0 : dist hT x y = 0 := by omega
      have hxy : x = y := (dist_eq_zero_iff hT).1 h0
      rw [hxy]
      exact Or.inl ⟨hT.geodesic a y, hT.geodesic_isReduced a y, hT.end_mem_geodesic a y⟩

end Aux

theorem nearestRep_smul_eq_vert {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V)
    (hbetween : ∀ A B : Work.ORBassSerre.orbitV G V,
      Work.ORBassSerre.reducedSpan (d.vert A) (d.vert B)
        ⊆ Work.ORLocInd.FKSKernel.Kurosh.repSet d)
    (hproj : ∀ v : V, ∀ A, Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v
        ∈ Work.ORBassSerre.reducedSpan v (d.vert A))
    (huniq : ∀ v : V, ∀ C, d.vert C ∈ Work.ORBassSerre.reducedSpan v
        (Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v) →
      d.vert C = Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v)
    (hfix : ∀ A, Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d (d.vert A) = d.vert A)
    (hfixpt : ∀ g : G, g ≠ 1 → ∀ x y : V, g • x = x → g • y = y → x = y)
    (A : Work.ORBassSerre.orbitV G V) (h : ↥(d.vgroup A)) (hne : (h : G) ≠ 1) (v : V)
    (hv : Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v ≠ d.vert A) :
    Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d ((h : G) • v) = d.vert A := by
  classical
  -- `h` fixes the representative `a = d.vert A`
  have ha_fix : (h : G) • d.vert A = d.vert A := h.2
  have ha_fix_inv : (h : G)⁻¹ • d.vert A = d.vert A := by
    rw [← ha_fix, inv_smul_smul, ha_fix]
  -- the orbit of a translate is the orbit of the point
  have h_orbit : ∀ (g : G) (x : V),
      (Quotient.mk'' (g • x) : Work.ORBassSerre.orbitV G V) = Quotient.mk'' x :=
    fun g x => Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)
  -- `R = repSet d` is convex
  have hconvR : ∀ x ∈ repSet d, ∀ y ∈ repSet d, reducedSpan x y ⊆ repSet d := by
    rintro x ⟨Ax, rfl⟩ y ⟨Ay, rfl⟩
    exact hbetween Ax Ay
  have haR : d.vert A ∈ repSet d := vert_mem_repSet d A
  -- `T = (h : G) • R` is convex (as the preimage of `R` under `(h : G)⁻¹`)
  have hconvT : ∀ x ∈ {x : V | (h : G)⁻¹ • x ∈ repSet d},
      ∀ y ∈ {y : V | (h : G)⁻¹ • y ∈ repSet d},
      reducedSpan x y ⊆ {z : V | (h : G)⁻¹ • z ∈ repSet d} := by
    intro x hx y hy z hz
    exact hconvR ((h : G)⁻¹ • x) hx ((h : G)⁻¹ • y) hy
      (Tree.Seg.smul_mem_reducedSpan (G := G) (V := V) (h : G)⁻¹ hz)
  have haT : (h : G)⁻¹ • d.vert A ∈ repSet d := by
    rw [ha_fix_inv]; exact haR
  -- `R` and `(h : G) • R` meet only in `a`
  have hsub : ∀ x ∈ repSet d, (h : G)⁻¹ • x ∈ repSet d → x = d.vert A := by
    intro x hxR hxT
    obtain ⟨B, hB⟩ := hxR
    obtain ⟨C, hC⟩ := hxT
    -- `d.vert B = x` and `d.vert C = (h:G)⁻¹ • x` lie in the same orbit
    have hCB : C = B := by
      rw [← d.vert_mk C, ← d.vert_mk B, hC, hB, h_orbit]
    have hverts : d.vert C = d.vert B := by rw [hCB]
    have hgx : (h : G)⁻¹ • x = x := by
      calc (h : G)⁻¹ • x = d.vert C := hC.symm
        _ = d.vert B := hverts
        _ = x := hB
    exact (hfixpt (h : G)⁻¹ (inv_ne_one.mpr hne) (d.vert A) x ha_fix_inv hgx).symm
  -- the nearest representatives
  have hrR : nearestRep hT d v ∈ repSet d := nearestRep_mem hT d v
  have hrR' : nearestRep hT d ((h : G) • v) ∈ repSet d := nearestRep_mem hT d ((h : G) • v)
  have hgrT : (h : G)⁻¹ • ((h : G) • nearestRep hT d v) ∈ repSet d := by
    rw [inv_smul_smul]; exact hrR
  have hgr : (h : G) • nearestRep hT d v ∈ reducedSpan ((h : G) • v) (d.vert A) := by
    have hh := Tree.Seg.smul_mem_reducedSpan (G := G) (V := V) (h : G) (hproj v A)
    rwa [ha_fix] at hh
  have hr' : nearestRep hT d ((h : G) • v) ∈ reducedSpan ((h : G) • v) (d.vert A) :=
    hproj ((h : G) • v) A
  by_contra hcontra
  -- `(h:G) • r ≠ a`, since `r ≠ a` and `h` fixes `a`
  have hgra : (h : G) • nearestRep hT d v ≠ d.vert A := by
    intro hcon
    have h1 : (h : G)⁻¹ • ((h : G) • nearestRep hT d v) = (h : G)⁻¹ • d.vert A :=
      congrArg (fun z => (h : G)⁻¹ • z) hcon
    rw [inv_smul_smul, ha_fix_inv] at h1
    exact hv h1
  -- both `r'` and `(h:G) • r` lie on the geodesic from `a` to `(h:G) • v`
  have hx1 : nearestRep hT d ((h : G) • v) ∈ reducedSpan (d.vert A) ((h : G) • v) := by
    rw [Tree.Seg.reducedSpan_comm]; exact hr'
  have hx2 : (h : G) • nearestRep hT d v ∈ reducedSpan (d.vert A) ((h : G) • v) := by
    rw [Tree.Seg.reducedSpan_comm]; exact hgr
  rcases mem_reducedSpan_or_of_mem_reducedSpan hT hx1 hx2 with hcase | hcase
  · -- `r' ∈ [a, (h:G) • r] ⊆ T`, so `r' ∈ R ∩ T = {a}`
    exact hcontra (hsub _ hrR' (hconvT (d.vert A) haT _ hgrT hcase))
  · -- `(h:G) • r ∈ [a, r'] ⊆ R`, so `(h:G) • r ∈ R ∩ T = {a}`
    exact hgra (hsub _ (hconvR (d.vert A) haR _ hrR' hcase) hgrT)

end Work.ORLocInd.FKSKernel.Kurosh
