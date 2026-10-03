import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree
import Submission.Work.ORLocInd.FKSKernel.pushoutStarTree_isTree
import Submission.Work.ORLocInd.FKSKernel.pushoutStarTree_stabilizers
import Submission.Work.ORBassSerre.Tree.Seg.smul_eq_self_of_mem_reducedSpan
import Submission.Work.ORBassSerre.Tree.Geodesic.exists_cons_geodesic_of_ne
import Submission.Work.ORLocInd.CohenLyndon.coprod_malnormal

namespace Work.OROneRel

open Quiver Work.ORLocInd.FKSKernel

universe u

/-- Two leaves of the star tree with labels in the same `i`-th vertex group coincide exactly when
the corresponding cosets of the `i`-th vertex subgroup coincide. -/
private theorem lf_mk_eq {ι H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]
    {φ : ∀ i, H →* G i} (i : ι) (a b : Psh φ) :
    lf φ i (Quotient.mk'' a) = lf φ i (Quotient.mk'' b) ↔
      (Quotient.mk'' a : Psh φ ⧸ ofSub φ i) = Quotient.mk'' b := by
  simp only [lf, cosetMap_mk]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
  · intro h
    rw [h]

/-- The action of an element of the pushout on a leaf, in `Quotient.mk''`-form. -/
private theorem smul_lf_mk {ι H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]
    {φ : ∀ i, H →* G i} (i : ι) (x y : Psh φ) :
    x • lf φ i (Quotient.mk'' y) = lf φ i (Quotient.mk'' (x * y)) := by
  rw [show x • lf φ i (Quotient.mk'' y) = smulVtx φ x (lf φ i (Quotient.mk'' y)) from rfl,
    smulVtx_lf, smulCtr_mk]

/-- Every edge of the star tree has a centre as one of its endpoints. -/
private theorem exists_ctr_mem_reducedSpan {ι H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) {v w : Vtx φ}
    (hT : Work.ORBassSerre.IsTree (Vtx φ)) (hne : v ≠ w) :
    ∃ c : Psh φ ⧸ baseSub φ, ctr φ c ∈ Work.ORBassSerre.reducedSpan v w := by
  obtain ⟨cp, q, e, -, hcp⟩ :=
    Work.ORBassSerre.Tree.Geodesic.exists_cons_geodesic_of_ne hT hne
  refine ⟨e.lbl, ?_⟩
  rcases Arrow.endpoints e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1]
    exact hcp
  · rw [← h2, Work.ORBassSerre.IsTree.reducedSpan_eq hT v w]
    exact Quiver.Path.end_mem_vertices (hT.geodesic v w)

/-- An element of the pushout which fixes two distinct vertices of the star tree has a conjugate
lying in the base subgroup: the two fixed points span a geodesic containing a centre, and the
stabiliser of a centre is a conjugate of the base subgroup. -/
private theorem exists_conj_mem_baseSub_of_smul_eq {ι H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) {x : Psh φ} {v w : Vtx φ}
    (hT : Work.ORBassSerre.IsTree (Vtx φ)) (hv : x • v = v) (hw : x • w = w) (hne : v ≠ w) :
    ∃ d : Psh φ, x ∈ (baseSub φ).map (MulEquiv.toMonoidHom (MulAut.conj d)) := by
  obtain ⟨c, hc⟩ := exists_ctr_mem_reducedSpan φ hT hne
  refine ⟨Quotient.out c, ?_⟩
  have hu : x • ctr φ c = ctr φ c :=
    Work.ORBassSerre.Tree.Seg.smul_eq_self_of_mem_reducedSpan hT hv hw hc
  have hx : x ∈ MulAction.stabilizer (Psh φ) (ctr φ c) :=
    MulAction.mem_stabilizer_iff.mpr hu
  have hrepr : ctr φ c = ctr φ (Quotient.mk'' (Quotient.out c)) := by
    rw [Quotient.out_eq' c]
  rw [hrepr, (pushoutStarTree_stabilizers φ).1 (Quotient.out c)] at hx
  exact hx

theorem pushoutI_conj_transfer {ι H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]
    (φ : ∀ i, H →* G i) (hφ : ∀ i, Function.Injective (φ i)) (i : ι) {g h : G i}
    {c : Monoid.PushoutI φ}
    (hc : Monoid.PushoutI.of i g = c * Monoid.PushoutI.of i h * c⁻¹)
    (hg : ∀ d : Monoid.PushoutI φ,
      Monoid.PushoutI.of i g ∉ (Work.ORLocInd.FKSKernel.baseSub φ).map
        (MulAut.conj d).toMonoidHom) :
    ∃ d : G i, g = d * h * d⁻¹ := by
  have hT : Work.ORBassSerre.IsTree (Vtx φ) := pushoutStarTree_isTree φ
  -- the leaf of the star tree whose stabiliser is exactly the `i`-th vertex subgroup
  have hx_v : Monoid.PushoutI.of (φ := φ) i g • lf φ i (Quotient.mk'' (1 : Psh φ))
      = lf φ i (Quotient.mk'' (1 : Psh φ)) := by
    rw [smul_lf_mk, mul_one, lf_mk_eq, QuotientGroup.eq]
    simpa using (ofSub φ i).inv_mem
      (show Monoid.PushoutI.of (φ := φ) i g ∈ ofSub φ i from ⟨g, rfl⟩)
  have hcv_eq : c • lf φ i (Quotient.mk'' (1 : Psh φ)) = lf φ i (Quotient.mk'' c) := by
    rw [smul_lf_mk, mul_one]
  have hxcv_eq : Monoid.PushoutI.of (φ := φ) i g • lf φ i (Quotient.mk'' c)
      = lf φ i (Quotient.mk'' c) := by
    rw [smul_lf_mk, lf_mk_eq, QuotientGroup.eq]
    rw [show (Monoid.PushoutI.of (φ := φ) i g * c)⁻¹ * c
        = (Monoid.PushoutI.of (φ := φ) i h)⁻¹ by rw [hc]; group]
    exact (ofSub φ i).inv_mem ⟨h, rfl⟩
  -- conjugating the fixed leaf by `c` gives another fixed vertex
  have hx_cv : Monoid.PushoutI.of (φ := φ) i g • (c • lf φ i (Quotient.mk'' (1 : Psh φ)))
      = c • lf φ i (Quotient.mk'' (1 : Psh φ)) := by
    rw [hcv_eq, hxcv_eq]
  by_cases hcv : c • lf φ i (Quotient.mk'' (1 : Psh φ)) = lf φ i (Quotient.mk'' (1 : Psh φ))
  · -- the conjugating element stabilises the leaf, hence lies in the `i`-th vertex subgroup
    have hc_mem : c ∈ ofSub φ i := by
      have h : lf φ i (Quotient.mk'' c) = lf φ i (Quotient.mk'' (1 : Psh φ)) := by
        rw [← hcv_eq]
        exact hcv
      rw [lf_mk_eq, QuotientGroup.eq] at h
      simpa using (ofSub φ i).inv_mem h
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hc_mem
    refine ⟨d, ?_⟩
    have hinj : Function.Injective (Monoid.PushoutI.of (φ := φ) i) :=
      Monoid.PushoutI.of_injective (φ := φ) hφ i
    exact hinj (by rw [map_mul, map_mul, map_inv, hd]; exact hc)
  · -- otherwise the element fixes two distinct vertices, hence is conjugate into the base
    obtain ⟨d, hd⟩ := exists_conj_mem_baseSub_of_smul_eq φ hT hx_v hx_cv
      (fun hh => hcv hh.symm)
    exact absurd hd (hg d)

end Work.OROneRel
