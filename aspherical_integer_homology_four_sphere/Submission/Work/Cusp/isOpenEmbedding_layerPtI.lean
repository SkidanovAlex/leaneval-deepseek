/-
# The layer chart `layerPtI a` of the *unslabbed* collar is an open embedding

`layerPtI a z = z.2 • bndOfU z.1` sends the pair (meridian parameter `u`, layer parameter `t`) of the
rectangle

  `layerDomI a = (a, a+1) × (layerLo, 1]`,  `layerLo = 1/4`,

to the point of the filling square `Sq` on the boundary `∂Sq` at perimeter parameter `u`, scaled by
`t`.  This is the layer-direction chart of the collar attached to the *unslabbed* collar box
`cuspBoxTop v c δ` (blueprint §1): its meridian interval is `(a, a+1)` with `a = cuspAnchor v c` —
the box is not confined to a slab of `outerU`, so `a` is an arbitrary real — and its height window
reaches above the junction, so a recovered layer parameter can be as small as just above `layerLo`.

The proof separates the two coordinates of the chart, exactly as for the slabbed version
`isOpenEmbedding_layerPtSq`:

* on the up-collar domain `layerUpDom a = (a,a+1) × (layerLo,∞)` the map
  `layerPtUpA a (u,t) = t • bndOfU u` is an open embedding **into the plane**, because it is the
  composite

    `layerPtUpA a = scal ∘ prodComm ∘ (A × id) ∘ prod`,

  where

  - `A u = ⟨bndOfU u, nrm_bndOfU u⟩` is the perimeter parametrisation `(a,a+1) → ∂Sq`.  It is an
    open embedding because `bndOfU` is `1`-periodic and the composite `u ↦ u mod 1` realises
    `(a,a+1) ≅ ℝ/ℤ ∖ {a mod 1}` (`AddCircle.openPartialHomeomorphCoe`), so `A` factors as
    `BarS ∘ (coe restricted to (a,a+1))` with `BarS` the homeomorphism `ℝ/ℤ ≅ ∂Sq`.  The identity
    `BarS ((x : ℝ/ℤ)) = ⟨bndOfU x, _⟩` for an *arbitrary* real `x` (not just `x ∈ [0,1)`) is
    `BarS_coe`, and is where the general anchor `a` is handled.
  - `scal (b,q) = b • q` is a homeomorphism of `(layerLo,∞) × ∂Sq` onto the open set
    `{p | layerLo < ‖p‖∞}` (`isOpenEmbedding_smulSph_gen`, a repackaging of the `1/2`-threshold
    version `isOpenEmbedding_smulSph` which keeps the strict positivity `0 < layerLo`);
  - `prodComm` and the set-product homeomorphism `Homeomorph.Set.prod` are the reorderings of the
    two factors.

* `layerPtI a` is the corestriction of `layerPtUpA a` to the square `Sq` along the inclusion
  `layerDomI a ⊆ layerUpDom a`.  The extra condition `t ≤ 1` defining `layerDomI a` is *not*
  dropped by it: the range of `layerPtI a` is exactly the preimage under `SquarePt ↪ E2` of the
  (open) range of `layerPtUpA a`, so it is open in the square.  Indeed `t = ‖layerPtUpA a (u,t)‖∞`,
  so a plane-level point lying over a point of `Sq` automatically has `t ≤ 1`.
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.nrm_bndOfU

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-! ### `BarS` at an arbitrary real argument

`Bar = AddCircle.liftIco 1 0 bndOfU` is the continuous lift of `bndOfU` to the circle, and `BarS` is
the induced homeomorphism `ℝ/ℤ ≅ ∂Sq`.  For a real `x` which is *not* in `[0,1)` the coercion
`(x : ℝ/ℤ)` has representative `Int.fract x`, and `bndOfU` depends only on the fractional part, so
`BarS (x : ℝ/ℤ) = ⟨bndOfU x, _⟩` unconditionally. -/

/-- **`bndOfU` depends only on the fractional part of its argument.** -/
theorem bndOfU_fract (x : ℝ) : bndOfU (Int.fract x) = bndOfU x := by
  simp only [bndOfU, Int.fract_fract]

/-- **`BarS` at an arbitrary real argument**: `BarS ((x : ℝ/ℤ)) = ⟨bndOfU x, nrm_bndOfU x⟩`. -/
theorem BarS_coe (x : ℝ) : BarS ((x : AddCircle (1:ℝ))) = ⟨bndOfU x, nrm_bndOfU x⟩ := by
  have hrep : uRep ((x : AddCircle (1:ℝ))) = Int.fract x := by
    refine (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0) (uRep_mem _) ?_).mp ?_
    · exact ⟨Int.fract_nonneg x, by simpa using Int.fract_lt_one x⟩
    · rw [uRep_coe, AddCircle.coe_fract]
  apply Subtype.ext
  show Bar ((x : AddCircle (1:ℝ))) = bndOfU x
  rw [Bar_uRep, hrep]
  exact bndOfU_fract x

/-! ### Scaling the boundary circle of the square -/

/-- **Scaling the boundary circle `∂Sq` by a factor `> c > 0` is an open embedding into the plane**,
with range `{p | c < ‖p‖∞}`.  This is `isOpenEmbedding_smulSph` with the numerical threshold
`1/2` replaced by an arbitrary positive `c` (used with `c = layerLo`); the composite
`p ↦ (‖p‖∞, bnd p)` is a homeomorphism `{c < ‖p‖∞} ≅ {b | c < b} × ∂Sq` with inverse
`(b,q) ↦ b • q`. -/
theorem isOpenEmbedding_smulSph_gen (c : ℝ) (hc : 0 < c) :
    IsOpenEmbedding (fun z : {b : ℝ // c < b} × {q : E2 // nrm q = 1} => z.1.1 • z.2.1) := by
  set T : Set E2 := {p | c < nrm p} with hT
  have hTopen : IsOpen T := isOpen_lt continuous_const nrm_continuous
  have hmem : ∀ z : {b : ℝ // c < b} × {q : E2 // nrm q = 1}, z.1.1 • z.2.1 ∈ T := by
    rintro ⟨b, q⟩
    rw [hT, Set.mem_ofPred_eq, nrm_smul, q.2, mul_one, abs_of_pos (lt_trans hc b.2)]
    exact b.2
  have hne : ∀ p : T, p.1 ≠ 0 := by
    intro p h
    have h2 : c < nrm p.1 := p.2
    rw [h, show nrm (0 : E2) = 0 from by simp [nrm]] at h2
    linarith
  let e : {b : ℝ // c < b} × {q : E2 // nrm q = 1} ≃ T :=
    { toFun := fun z => ⟨z.1.1 • z.2.1, hmem z⟩
      invFun := fun p => (⟨nrm p.1, p.2⟩, ⟨bnd p.1, nrm_bnd (hne p)⟩)
      left_inv := by
        rintro ⟨b, q⟩
        apply Prod.ext
        · apply Subtype.ext
          show nrm (b.1 • q.1) = b.1
          rw [nrm_smul, q.2, mul_one, abs_of_pos (lt_trans hc b.2)]
        · apply Subtype.ext
          show bnd (b.1 • q.1) = q.1
          rw [bnd, nrm_smul, q.2, mul_one, abs_of_pos (lt_trans hc b.2),
            inv_smul_smul₀ (ne_of_gt (lt_trans hc b.2))]
      right_inv := by
        intro p
        apply Subtype.ext
        show nrm (p:E2) • bnd (p:E2) = (p:E2)
        rw [smul_bnd] }
  have hc1 : Continuous e := by
    refine Continuous.subtype_mk
      (f := fun z : {b : ℝ // c < b} × {q : E2 // nrm q = 1} => z.1.1 • z.2.1) ?_ hmem
    fun_prop
  have hc2 : Continuous e.symm := by
    show Continuous (fun p : T => ((⟨nrm (p:E2), p.2⟩ : {b : ℝ // c < b}),
        (⟨bnd (p:E2), nrm_bnd (hne p)⟩ : {q : E2 // nrm q = 1})))
    refine (Continuous.subtype_mk (nrm_continuous.comp continuous_subtype_val)
      (fun p : T => p.2)).prodMk ?_
    refine Continuous.subtype_mk ?_ (fun p : T => nrm_bnd (p := p.1) (hne p))
    have hpos : ∀ p : T, (0:ℝ) < nrm (p:E2) := fun p => lt_trans hc p.2
    have h1 : Continuous (fun p : T => (nrm (p:E2))⁻¹) :=
      (nrm_continuous.comp continuous_subtype_val).inv₀ (fun p => ne_of_gt (hpos p))
    have h3 : Continuous (fun p : T => (nrm (p:E2))⁻¹ • ((p:E2))) :=
      h1.smul continuous_subtype_val
    simpa only [bnd] using h3
  let H : {b : ℝ // c < b} × {q : E2 // nrm q = 1} ≃ₜ T := Homeomorph.mk e hc1 hc2
  have hE : IsOpenEmbedding (fun z : {b : ℝ // c < b} × {q : E2 // nrm q = 1} => (H z : E2)) :=
    (IsOpen.isOpenEmbedding_subtypeVal hTopen).comp H.isOpenEmbedding
  have hfun : (fun z : {b : ℝ // c < b} × {q : E2 // nrm q = 1} => (H z : E2))
      = fun z : {b : ℝ // c < b} × {q : E2 // nrm q = 1} => z.1.1 • z.2.1 := by
    funext z; rfl
  rwa [hfun] at hE

/-! ### The perimeter parametrisation over an interval of length `1` -/

/-- **The perimeter parametrisation `u ↦ bndOfU u` is an open embedding on `(a, a+1)` for every
anchor `a`.**  The parameter interval `(a, a+1)` is the source of the quotient chart
`AddCircle.openPartialHomeomorphCoe 1 a`, and `bndOfU` is the composite of the quotient map with the
homeomorphism `BarS : ℝ/ℤ ≅ ∂Sq` (`BarS_coe`). -/
theorem isOpenEmbedding_bndOfU_layerA (a : ℝ) :
    IsOpenEmbedding
      (fun u : ↥(layerA a) => (⟨bndOfU u.1, nrm_bndOfU u.1⟩ : {q : E2 // nrm q = 1})) := by
  have hmod : IsOpenEmbedding (fun u : ↥(layerA a) => (u.1 : AddCircle (1:ℝ))) := by
    have h := (AddCircle.openPartialHomeomorphCoe (1:ℝ) a).isOpenEmbedding_restrict
    have hfun : ((AddCircle.openPartialHomeomorphCoe (1:ℝ) a).source.domRestrict
          ↑(AddCircle.openPartialHomeomorphCoe (1:ℝ) a))
        = fun u : ↥(layerA a) => (u.1 : AddCircle (1:ℝ)) := by
      funext u
      rw [Set.domRestrict_apply]
      rfl
    rwa [hfun] at h
  have hdir : IsOpenEmbedding (fun u : ↥(layerA a) => BarS ((u.1 : AddCircle (1:ℝ)))) :=
    isOpenEmbedding_barS.comp hmod
  have heq : (fun u : ↥(layerA a) => BarS ((u.1 : AddCircle (1:ℝ))))
      = fun u : ↥(layerA a) => (⟨bndOfU u.1, nrm_bndOfU u.1⟩ : {q : E2 // nrm q = 1}) := by
    funext u; exact BarS_coe u.1
  rwa [heq] at hdir

/-! ### The plane-level layer chart -/

/-- **`(u,t) ↦ t • bndOfU u` is an open embedding of the up-collar domain
`layerUpDom a = (a,a+1) × (layerLo,∞)` into the plane.** -/
theorem isOpenEmbedding_layerPtUpA (a : ℝ) : IsOpenEmbedding (layerPtUpA a) := by
  set A : ↥(layerA a) → {q : E2 // nrm q = 1} := fun u => ⟨bndOfU u.1, nrm_bndOfU u.1⟩ with hAdef
  have hA : IsOpenEmbedding A := isOpenEmbedding_bndOfU_layerA a
  have hP : IsOpenEmbedding (Prod.map A (id : ↥layerUpJ → ↥layerUpJ)) :=
    hA.prodMap IsOpenEmbedding.id
  have hS : IsOpenEmbedding (⇑(Homeomorph.prodComm {q : E2 // nrm q = 1} ↥layerUpJ)) :=
    (Homeomorph.prodComm {q : E2 // nrm q = 1} ↥layerUpJ).isOpenEmbedding
  have hSc : IsOpenEmbedding (fun w : ↥layerUpJ × {q : E2 // nrm q = 1} => w.1.1 • w.2.1) :=
    isOpenEmbedding_smulSph_gen layerLo (by norm_num [layerLo])
  have he : IsOpenEmbedding (⇑(Homeomorph.Set.prod (layerA a) layerUpJ)) :=
    (Homeomorph.Set.prod (layerA a) layerUpJ).isOpenEmbedding
  have hcomp := hSc.comp (hS.comp (hP.comp he))
  have heq : (fun w : ↥layerUpJ × {q : E2 // nrm q = 1} => w.1.1 • w.2.1)
        ∘ (⇑(Homeomorph.prodComm {q : E2 // nrm q = 1} ↥layerUpJ))
        ∘ (Prod.map A (id : ↥layerUpJ → ↥layerUpJ))
        ∘ (⇑(Homeomorph.Set.prod (layerA a) layerUpJ)) = layerPtUpA a := by
    funext z
    rfl
  rwa [heq] at hcomp

/-! ### The layer chart of the unslabbed collar -/

/-- **The layer chart `layerPtI a` of the unslabbed collar is an open embedding into the square.** -/
theorem isOpenEmbedding_layerPtI (a : ℝ) :
    Topology.IsOpenEmbedding (fun z : {z : ℝ × ℝ // z ∈ layerDomI a} => layerPtI a z) := by
  have hsub : layerDomI a ⊆ layerUpDom a := by
    rintro z ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  have hincl : IsEmbedding (Set.inclusion hsub) := IsEmbedding.inclusion hsub
  have hUp := isOpenEmbedding_layerPtUpA a
  have hcomp : IsEmbedding
      (fun z : {z : ℝ × ℝ // z ∈ layerDomI a} => z.1.2 • bndOfU z.1.1) := by
    have h := hUp.isEmbedding.comp hincl
    simpa only [Function.comp_def, Set.inclusion, layerPtUpA] using h
  have hEmb : IsEmbedding (fun z : {z : ℝ × ℝ // z ∈ layerDomI a} => layerPtI a z) := by
    refine (IsEmbedding.of_comp_iff
      (f := fun z : {z : ℝ × ℝ // z ∈ layerDomI a} => layerPtI a z)
      (g := (Subtype.val : Work.Space.SquarePt → E2)) (IsEmbedding.subtypeVal)).mp ?_
    show IsEmbedding (fun z : {z : ℝ × ℝ // z ∈ layerDomI a} =>
      ((layerPtI a z : Work.Space.SquarePt) : E2))
    simpa only [coe_layerPtI, layerPtE] using hcomp
  refine ⟨hEmb, ?_⟩
  have hrange : range (fun z : {z : ℝ × ℝ // z ∈ layerDomI a} => layerPtI a z)
      = (Subtype.val : Work.Space.SquarePt → E2) ⁻¹' (range (layerPtUpA a)) := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨z.1, hsub z.2⟩, rfl⟩
    · rintro ⟨w, hw⟩
      have hb : w.1.2 ≤ 1 := by
        have h1 : nrm (p : E2) ≤ 1 := Work.Space.sqNorm_le_one p
        have h2 : nrm (layerPtUpA a w) = w.1.2 := by
          rw [layerPtUpA, nrm_smul, nrm_bndOfU, mul_one,
            abs_of_pos (lt_trans (by norm_num [layerLo]) w.2.2)]
        rw [hw] at h2
        exact h2 ▸ h1
      refine ⟨⟨w.1, ⟨w.2.1, w.2.2, hb⟩⟩, ?_⟩
      apply Subtype.ext
      show layerPtUpA a w = (p : E2)
      exact hw
  rw [hrange]
  exact hUp.isOpen_range.preimage continuous_subtype_val

end Work.Cusp
