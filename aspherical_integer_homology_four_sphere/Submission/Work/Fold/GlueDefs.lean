/-
# Gluing `2^c` closed pieces into a fold chart

This file fixes the framework of the *fold chart lemma* (`Work.Fold.fold_chart_lemma`,
module `Submission.Work.Fold.FoldChart`).

## The geometric situation

A point of a quotient space `Y` is covered by `2^c` "corner pieces" `C r` (`r : Sign c`), each
carrying a chart `ψ r` into `E4` whose image lies in the closed orthant `orthant r = reflVec r ''
posOrthant c`, with the following behaviour:

* the pieces are glued in `Y` exactly along the "common coordinate hyperplanes", i.e. two pieces
  meet in `Y` only where their images agree on a hyperplane (`hagree`, `hcross`),
* the image of the `r`-th piece is the `r`-reflection of the image of the `+`-piece (`himage`,
  the "fold lemma" identity `N D_r K_r = R_r N D_{r₀}` of the blueprint),
* `ψ r` is a homeomorphism onto its image (`inv_*`).

Under these hypotheses the *glued* map `glued : Y → E4` (which is `ψ r` on `U r`) is an
`OpenPartialHomeomorph` with source `⋃ r, U r` and target
`foldMap c hc ⁻¹' (ψ (oneSign c) '' U (oneSign c))`.

## Conventions

* `U r ⊆ C r` are the pieces of the *source* of the chart ("`C`" carries the closed pieces on
  which the identifications are stated, `U` the part that belongs to the chart's source).  In the
  simplest applications `U r = C r`.
* `r₀ = oneSign c` is the all-`+1` piece; the target is stated in terms of it and of `foldMap`,
  so that it is manifestly open in `E4` (`isOpen_foldMap_preimage`).
-/
import Submission.Work.Fold.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Fold

open Set Function

/-- The data of a `c`-fold gluing: `2^c` pieces of a space `Y` whose charts fold onto the closed
orthants of `E4` and glue exactly over the common coordinate hyperplanes. -/
structure FoldGlue (Y : Type*) [TopologicalSpace Y] (c : ℕ) where
  /-- The closed pieces. -/
  C : Sign c → Set Y
  /-- The pieces of the source of the fold chart. -/
  U : Sign c → Set Y
  /-- The chart on each piece. -/
  ψ : Sign c → Y → E4
  /-- The source pieces are contained in the closed pieces. -/
  hU_subset : ∀ r, U r ⊆ C r
  /-- The pieces are closed. -/
  hC_closed : ∀ r, IsClosed (C r)
  /-- The charts are continuous on the pieces. -/
  hψ_cont : ∀ r, ContinuousOn (ψ r) (C r)
  /-- Each chart maps its piece into its orthant. -/
  hψ_orth : ∀ r ⦃p : Y⦄, p ∈ C r → ψ r p ∈ orthant r
  /-- The source is open. -/
  hsource_open : IsOpen (⋃ r, U r)
  /-- The charts agree on the overlaps of the closed pieces. -/
  hagree : ∀ r s ⦃p : Y⦄, p ∈ C r → p ∈ C s → ψ r p = ψ s p
  /-- Distinct points of the source pieces have distinct images unless they lie over a common
  coordinate hyperplane: the identifications in `Y` are exactly the hyperplane ones. -/
  hcross : ∀ r s ⦃p q : Y⦄, p ∈ U r → q ∈ U s → ψ r p = ψ s q → p = q
  /-- The `r`-th image is the `r`-reflection of the `+`-th image (the fold lemma). -/
  himage : ∀ r, ψ r '' U r = reflVec r '' (ψ (oneSign c) '' U (oneSign c))
  /-- The `+`-th image is relatively open in the positive orthant. -/
  htarget_open : IsRelOpen (posOrthant c) (ψ (oneSign c) '' U (oneSign c))
  /-- The local inverses of the charts. -/
  inv : Sign c → E4 → Y
  /-- The local inverse takes values in the piece. -/
  inv_mem : ∀ r ⦃x : E4⦄, x ∈ ψ r '' U r → inv r x ∈ U r
  /-- The local inverse is a right inverse of the chart. -/
  inv_apply : ∀ r ⦃x : E4⦄, x ∈ ψ r '' U r → ψ r (inv r x) = x
  /-- The local inverse is continuous on the image. -/
  inv_cont : ∀ r, ContinuousOn (inv r) (ψ r '' U r)

namespace FoldGlue

variable {Y : Type*} [TopologicalSpace Y] {c : ℕ}

/-- The source of the fold chart: the union of the source pieces. -/
def source (D : FoldGlue Y c) : Set Y := ⋃ r, D.U r

/-- The image of the `+`-piece (a set which is relatively open in the positive orthant). -/
def S (D : FoldGlue Y c) : Set E4 := D.ψ (oneSign c) '' D.U (oneSign c)

/-- The target of the fold chart: the full preimage of `S` under the fold map. -/
def target (D : FoldGlue Y c) (hc : c ≤ 4) : Set E4 := foldMap c hc ⁻¹' D.S

/-- The glued map: `ψ r` on the piece `U r` (arbitrary away from the source). -/
def glued (D : FoldGlue Y c) (y : Y) : E4 := by
  classical
  exact if h : ∃ r, y ∈ D.U r then D.ψ (Classical.choose h) y else 0

/-- The glued inverse: on the target, the point of the piece whose sign pattern is the canonical
one of the image point. -/
def invFun (D : FoldGlue Y c) (hc : c ≤ 4) (x : E4) : Y :=
  D.inv (signOf c hc x) x

variable (D : FoldGlue Y c)

lemma isOpen_source : IsOpen D.source := D.hsource_open

/-- The `+`-piece of the source is contained in the positive orthant. -/
lemma S_subset : D.S ⊆ posOrthant c :=
  fun _ ⟨p, hp, hpx⟩ => hpx ▸ D.hψ_orth (oneSign c) (D.hU_subset (oneSign c) hp)

/-- **The target is the union of the chart images.** -/
theorem target_eq (hc : c ≤ 4) : D.target hc = ⋃ r : Sign c, D.ψ r '' D.U r := by
  rw [target, foldMap_preimage_eq_iUnion hc D.S_subset]
  exact iUnion_congr fun r => (D.himage r).symm

theorem isOpen_target (hc : c ≤ 4) : IsOpen (D.target hc) := isOpen_foldMap_preimage hc D.htarget_open

theorem mem_target_iff (hc : c ≤ 4) {x : E4} :
    x ∈ D.target hc ↔ ∃ r : Sign c, ∃ p ∈ D.U r, D.ψ r p = x := by
  rw [D.target_eq hc, mem_iUnion]
  exact exists_congr fun r => mem_image _ _ _

theorem mem_source_iff {y : Y} : y ∈ D.source ↔ ∃ r : Sign c, y ∈ D.U r := mem_iUnion

/-- The glued map is `ψ r` on the `r`-th piece. -/
theorem glued_apply {p : Y} {r : Sign c} (hp : p ∈ D.U r) : D.glued p = D.ψ r p := by
  have h : ∃ s, p ∈ D.U s := ⟨r, hp⟩
  rw [glued, dite_eq_left h]
  exact D.hagree (Classical.choose h) r (D.hU_subset (Classical.choose h) (Classical.choose_spec h))
    (D.hU_subset r hp)

theorem glued_mem_target (hc : c ≤ 4) {y : Y} (hy : y ∈ D.source) : D.glued y ∈ D.target hc := by
  obtain ⟨r, hr⟩ := D.mem_source_iff.mp hy
  rw [D.glued_apply hr, D.mem_target_iff hc]
  exact ⟨r, y, hr, rfl⟩

/-- The glued map is injective on the source. -/
theorem glued_injOn (hc : c ≤ 4) : InjOn D.glued D.source := by
  intro p hp q hq h
  obtain ⟨r, hr⟩ := D.mem_source_iff.mp hp
  obtain ⟨s, hs⟩ := D.mem_source_iff.mp hq
  rw [D.glued_apply hr, D.glued_apply hs] at h
  exact D.hcross r s hr hs h

/-- The image of the target point `x` lies in the piece whose sign pattern is that of `x`. -/
theorem mem_image_signOf (hc : c ≤ 4) {x : E4} (hx : x ∈ D.target hc) :
    x ∈ D.ψ (signOf c hc x) '' D.U (signOf c hc x) := by
  rw [D.himage (signOf c hc x)]
  refine ⟨foldMap c hc x, ?_, reflVec_signOf_foldMap hc x⟩
  rwa [target, mem_preimage] at hx

theorem invFun_mem (hc : c ≤ 4) {x : E4} (hx : x ∈ D.target hc) : D.invFun hc x ∈ D.source :=
  mem_iUnion.mpr ⟨_, D.inv_mem (signOf c hc x) (D.mem_image_signOf hc hx)⟩

/-- On the target, the glued map is a left inverse of the glued inverse. -/
theorem glued_invFun (hc : c ≤ 4) {x : E4} (hx : x ∈ D.target hc) :
    D.glued (D.invFun hc x) = x := by
  rw [invFun, D.glued_apply (D.inv_mem _ (D.mem_image_signOf hc hx)),
    D.inv_apply _ (D.mem_image_signOf hc hx)]

/-- On the source, the glued inverse is a left inverse of the glued map. -/
theorem invFun_glued (hc : c ≤ 4) {y : Y} (hy : y ∈ D.source) : D.invFun hc (D.glued y) = y := by
  obtain ⟨r, hr⟩ := D.mem_source_iff.mp hy
  set x := D.glued y with hxdef
  have hxr : x ∈ D.ψ r '' D.U r := ⟨y, hr, (D.glued_apply hr).symm⟩
  have hxt : x ∈ D.target hc := hxdef ▸ D.glued_mem_target hc hy
  have hxσ : x ∈ D.ψ (signOf c hc x) '' D.U (signOf c hc x) := D.mem_image_signOf hc hxt
  have h3 : D.inv (signOf c hc x) x = D.inv r x :=
    D.hcross _ _ (D.inv_mem _ hxσ) (D.inv_mem r hxr)
      (by rw [D.inv_apply _ hxσ, D.inv_apply r hxr])
  have h4 : D.inv r x = y :=
    D.hcross _ _ (D.inv_mem r hxr) hr (by rw [D.inv_apply r hxr]; exact hxdef.trans (D.glued_apply hr))
  rw [invFun, h3, h4]

end FoldGlue

end Work.Fold
