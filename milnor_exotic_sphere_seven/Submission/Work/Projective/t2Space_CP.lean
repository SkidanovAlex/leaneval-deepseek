import Mathlib
import Submission.Work.Projective.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℂPⁿ` is Hausdorff

This module proves that complex projective space `ℂPⁿ`, with the quotient topology of
`Work.Projective.instTopologicalSpaceCP` (the topology making `cpMk n : ℂ^{n+1} ∖ {0} → ℂPⁿ` a
quotient map), is a Hausdorff space:

* `Work.Projective.t2Space_CP : T2Space (CP n)`.

## Strategy

`cpMk n` is an *open* quotient map (`Work.Projective.isOpenQuotientMap_cpMk`): its saturation of
an open set `U` is the union of the images of `U` under the scaling homeomorphisms of
`ℂ^{n+1} ∖ {0}` (`Work.Projective.preimage_image_cpMk_eq_iUnion`).  For an open quotient map the
Hausdorff property of the target is equivalent to closedness of the kernel relation
(`t2Space_iff_of_isOpenQuotientMap`), and the kernel relation of `cpMk n` is described by the
vanishing of all `2 × 2` minors of the pair of vectors (the Plücker relations
`Work.Projective.cpMk_eq_iff_minors`), hence is closed
(`Work.Projective.isClosed_kernel_cpMk`).

## Main results

* `Work.Projective.isOpenMap_cpMk`, `Work.Projective.isOpenQuotientMap_cpMk`;
* `Work.Projective.cpMk_eq_iff_minors`, `Work.Projective.isClosed_kernel_cpMk`;
* `Work.Projective.t2Space_CP`.
-/

open scoped LinearAlgebra.Projectivization

namespace Work.Projective

noncomputable section

/-! ## The scaling action on nonzero vectors

The nonzero vectors of `ℂ^{n+1}` carry a (free) action of `ℂˣ` by scaling; `cpMk n` is precisely
the quotient map for this action, and it is open because the action is by homeomorphisms. -/

/-- Scaling a nonzero vector by a unit `a : ℂˣ`, viewed as a self-map of `{v : ℂ^{n+1} // v ≠ 0}`.
These maps are the deck transformations of the quotient map `cpMk n`, and they are
homeomorphisms. -/
def scaleNonzeroVec (n : ℕ) (a : ℂˣ) (v : {v : CPV n // v ≠ 0}) : {v : CPV n // v ≠ 0} :=
  ⟨(a : ℂ) • (v : CPV n), by
    intro h
    refine v.2 (funext fun i => ?_)
    have hi := congrFun h i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left a.ne_zero⟩

/-- `scaleNonzeroVec n a` is continuous. -/
theorem continuous_scaleNonzeroVec (n : ℕ) (a : ℂˣ) : Continuous (scaleNonzeroVec n a) :=
  Continuous.subtype_mk (continuous_subtype_val.const_smul (a : ℂ)) _

/-- **The saturation of a set under scaling.**  The preimage of the image of `U` under the
quotient map `cpMk n` is the union of the preimages of `U` under the scaling maps
`scaleNonzeroVec n a`, `a : ℂˣ`. -/
theorem preimage_image_cpMk_eq_iUnion (n : ℕ) (U : Set {v : CPV n // v ≠ 0}) :
    cpMk n ⁻¹' (cpMk n '' U) = ⋃ a : ℂˣ, scaleNonzeroVec n a ⁻¹' U := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, huU, hwu⟩ := hw
    obtain ⟨a, ha⟩ := (cpMk_eq_iff n w u).mp hwu.symm
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact w.2 ha.symm
    refine Set.mem_iUnion.mpr ⟨(Units.mk0 a ha0)⁻¹, ?_⟩
    have hscale : scaleNonzeroVec n ((Units.mk0 a ha0)⁻¹) w = u := by
      refine Subtype.ext ?_
      show ((Units.mk0 a ha0 : ℂˣ) : ℂ)⁻¹ • (w : CPV n) = (u : CPV n)
      rw [Units.val_mk0, ← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    change scaleNonzeroVec n ((Units.mk0 a ha0)⁻¹) w ∈ U
    rw [hscale]; exact huU
  · intro hw
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hw
    refine ⟨scaleNonzeroVec n a w, ha, ?_⟩
    exact (cpMk_eq_iff n (scaleNonzeroVec n a w) w).mpr ⟨(a : ℂ), rfl⟩

/-- **The quotient map `cpMk n` is open**: the saturation of an open set is a union of images of
open sets under the scaling homeomorphisms. -/
theorem isOpenMap_cpMk (n : ℕ) : IsOpenMap (cpMk n) := by
  intro U hU
  rw [isOpen_coinduced]
  rw [preimage_image_cpMk_eq_iUnion]
  exact isOpen_iUnion fun a => (continuous_scaleNonzeroVec n a).isOpen_preimage U hU

/-- **`cpMk n` is an open quotient map.** -/
theorem isOpenQuotientMap_cpMk (n : ℕ) : IsOpenQuotientMap (cpMk n) :=
  ⟨cpMk_surjective n, continuous_cpMk n, isOpenMap_cpMk n⟩

/-! ## The kernel relation of `cpMk n`

Two nonzero vectors of `ℂ^{n+1}` define the same point of `ℂPⁿ` iff their `2 × 2` minors all
vanish, i.e. iff they are linearly dependent. -/

/-- **The Plücker criterion**: two nonzero vectors define the same point of `ℂPⁿ` iff all their
`2 × 2` minors vanish (they are linearly dependent). -/
theorem cpMk_eq_iff_minors (n : ℕ) (v w : {v : CPV n // v ≠ 0}) :
    cpMk n v = cpMk n w ↔ ∀ i j : Fin (n + 1),
      (v : CPV n) i * (w : CPV n) j = (v : CPV n) j * (w : CPV n) i := by
  constructor
  · intro h i j
    obtain ⟨a, ha⟩ := (cpMk_eq_iff n v w).mp h
    have hi : (v : CPV n) i = a * (w : CPV n) i := (congrFun ha i).symm
    have hj : (v : CPV n) j = a * (w : CPV n) j := (congrFun ha j).symm
    rw [hi, hj]; ring
  · intro h
    obtain ⟨k, hk⟩ : ∃ k, (w : CPV n) k ≠ 0 := by
      by_contra hc
      exact w.2 (funext fun k => by
        by_contra h
        exact hc ⟨k, h⟩)
    refine (cpMk_eq_iff n v w).mpr ⟨(v : CPV n) k / (w : CPV n) k, ?_⟩
    funext j
    have hjk := h j k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_eq_iff hk]
    exact hjk.symm

/-- **The kernel relation of `cpMk n` is closed** in
`(ℂ^{n+1} ∖ {0}) × (ℂ^{n+1} ∖ {0})`: it is the intersection of the zero sets of the continuous
functions `(v, w) ↦ v i * w j - v j * w i`. -/
theorem isClosed_kernel_cpMk (n : ℕ) :
    IsClosed {q : {v : CPV n // v ≠ 0} × {v : CPV n // v ≠ 0} | cpMk n q.1 = cpMk n q.2} := by
  have h : {q : {v : CPV n // v ≠ 0} × {v : CPV n // v ≠ 0} | cpMk n q.1 = cpMk n q.2}
      = {q | ∀ i j : Fin (n + 1),
          (q.1 : CPV n) i * (q.2 : CPV n) j = (q.1 : CPV n) j * (q.2 : CPV n) i} := by
    ext q
    exact cpMk_eq_iff_minors n q.1 q.2
  rw [h]
  rw [show {q : {v : CPV n // v ≠ 0} × {v : CPV n // v ≠ 0} |
        ∀ i j : Fin (n + 1),
          (q.1 : CPV n) i * (q.2 : CPV n) j = (q.1 : CPV n) j * (q.2 : CPV n) i}
      = ⋂ i, ⋂ j, {q : {v : CPV n // v ≠ 0} × {v : CPV n // v ≠ 0} |
          (q.1 : CPV n) i * (q.2 : CPV n) j = (q.1 : CPV n) j * (q.2 : CPV n) i}
      from by ext q; simp [Set.mem_iInter]]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (f := fun q : {v : CPV n // v ≠ 0} × {v : CPV n // v ≠ 0} =>
        (q.1 : CPV n) i * (q.2 : CPV n) j)
      (g := fun q : {v : CPV n // v ≠ 0} × {v : CPV n // v ≠ 0} =>
        (q.1 : CPV n) j * (q.2 : CPV n) i)
      (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))
      (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

/-! ## Hausdorffness -/

/-- **`ℂPⁿ` is Hausdorff.**  `cpMk n` is an open quotient map, so the Hausdorff property is
equivalent to closedness of its kernel relation, which is the Plücker relation. -/
theorem t2Space_CP (n : ℕ) : T2Space (CP n) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_cpMk n)]
  exact isClosed_kernel_cpMk n

end

end Work.Projective
