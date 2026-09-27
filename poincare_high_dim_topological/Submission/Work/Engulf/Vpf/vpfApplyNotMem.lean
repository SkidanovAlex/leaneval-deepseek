import Mathlib
import Submission.Work.Engulf.Vpf.Defs

namespace Work.Engulf.Vpf

/-- `Work.Engulf.Vpf.vpfG'` agrees with `g` on a face of `K` containing no `Z`-vertex.  If
`x ∈ PL.simp s` and some face `s' ∋ x` of `K` carries a `Z`-vertex, then
`Work.Engulf.Vpf.vpfG' K Z g y x = Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s' x`
by `Work.Engulf.Vpf.vpfG'_apply_of_mem`; taking `G := (hglin s' hs' hZ').choose` with
`Set.EqOn g G (PL.simp s')`, the maps `Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s'`
and `G` agree on the vertices of `s' ∩ s` (both equal `g` there, since `s` has no `Z`-vertex),
so by `Work.Engulf.Vpf.eqOn_convexHull_of_eqOn_vertices` and `Work.Engulf.simp_inter` they agree
at `x`, and `G x = g x`.  Otherwise `vpfG' x = g x` by definition. -/
theorem vpfApplyNotMem {N n : ℕ} {K : PL.Cx N} {Z : Finset (PL.E N)} {g y : PL.E N → PL.E n}
    (hglin : ∀ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) → ∃ A : PL.E N →ᵃ[ℝ] PL.E n, Set.EqOn g A (PL.simp s))
    {s : Finset (PL.E N)} (hs : s ∈ K.faces) (hnoZ : ∀ v ∈ s, v ∉ Z) {x : PL.E N}
    (hx : x ∈ PL.simp s) :
    Work.Engulf.Vpf.vpfG' K Z g y x = g x := by
  classical
  by_cases h : ∃ s' ∈ K.faces, (∃ v ∈ s', v ∈ Z) ∧ x ∈ PL.simp s'
  · obtain ⟨s', hs', hZ', hxs'⟩ := h
    -- `G` is the affine map on the face `s'` supplied by the linearity hypothesis
    have hG : Set.EqOn g (hglin s' hs' hZ').choose (PL.simp s') := (hglin s' hs' hZ').choose_spec
    have hxv : x ∈ PL.simp (s' ∩ s) := by
      rw [← Work.Engulf.simp_inter hs' hs]; exact ⟨hxs', hx⟩
    -- the two affine maps agree on the vertices of `s' ∩ s`
    have happrox : Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s' x
        = (hglin s' hs' hZ').choose x :=
      Work.Engulf.Vpf.eqOn_convexHull_of_eqOn_vertices
        (A := Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s')
        (B := (hglin s' hs' hZ').choose)
        (fun v hv => by
          rw [Finset.mem_inter] at hv
          rw [Work.Engulf.Vpf.vpfA_apply hs' hv.1,
            Work.Engulf.Vpf.vpfC_apply_of_notMem (hnoZ v hv.2)]
          exact hG (Work.Engulf.subset_simp hv.1))
        hxv
    rw [Work.Engulf.Vpf.vpfG'_apply_of_mem hs' hZ' hxs', happrox]
    exact (hG hxs').symm
  · -- `x` lies in no face carrying a `Z`-vertex, so `vpfG'` is `g` at `x` by definition
    unfold Work.Engulf.Vpf.vpfG'
    rw [dite_eq_right h]

end Work.Engulf.Vpf
