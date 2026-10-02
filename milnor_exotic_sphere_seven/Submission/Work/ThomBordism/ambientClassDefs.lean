import Mathlib
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Tubular.LocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

open Work.Tubular

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-!
# The ambient standard class on the tube, and the tube-inverse comparison

This file supplies the *determinate* reference against which the localisation of the Pontryagin–Thom
collapse class `Work.Tubular.collapseRelK8` is to be measured — the missing chapter identified in
`Submission/Work/ThomBordism/NOTE_SESSION41_UNIVERSAL.md` §4 (a)–(d) and
`NOTE_COORFIBRE_SIGNED.md` §4, i.e.

> the local class of `collapseRelK8` at a point of the zero section is the *ambient* orientation
> generator, with a sign that is independent of the datum (it is the product of the global
> sphere-generator convention and a universal model constant).

The reference is built without any new choice: `Work.ThomBordism.stdModelGen (8 + k)` is the
*determinate* (explicitly inductively defined) standard generator of the pair
`(ℝ^{k+8}, ℝ^{k+8}∖0)`, and it is pulled back along the *translation* `y ↦ y - E.e x` on the closed
tube (`tubeInvMap`, `ambientStandardClass`).  The tube inverse `C.inv` identifies the closed tube
with the closed disc bundle, and `tubeInvHomology` is the induced map on relative homology; the pair
`(C.U, C.U∖tubeInvPunct)` is a neighbourhood pair of the zero section in the total space, so that map
is an isomorphism (excision), and it pins the tube-side avatar of `collapseRelK8`.
-/

/-- The tubular map sends the zero section to the embedding. -/
theorem tubeMap_zeroSectionNormal (E : PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    tubeMap E (zeroSectionNormal E x) = E.e x := by
  rw [zeroSectionNormal_apply, Work.Tubular.tubeMap_mk, add_zero]

/-- The tube inverse of an embedding point is the corresponding zero-section point. -/
theorem inv_embed (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (x : V.pt) : C.inv (E.e x) = zeroSectionNormal E x := by
  rw [← tubeMap_zeroSectionNormal E x]
  refine C.inv_tubeMap (zeroSectionNormal E x) ?_
  rw [zeroSectionNormal_apply, Work.Tubular.normalNorm_mk, norm_zero]
  exact C.eps_pos.le

/-- The inverse tube chart, as a continuous map on the closed tube. -/
def tubeInvMap (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε) : C(↥C.U, TopCat.of (NormalTotal E)) :=
  ⟨fun y => C.inv y.1,
    C.continuousOn_inv.comp_continuous continuous_subtype_val (fun y => y.2)⟩

/-- The part of the closed tube whose tube inverse lies in the punctured total space: this is the
excluded set that makes `tubeInvMap` a map of pairs
`(C.U, C.U∖tubeInvPunct) → (ν, ν∖0)`. -/
def tubeInvPunct (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε) : Set ↥C.U :=
  {y | C.inv y.1 ∈ normalNonzero E}

/-- The excluded set `tubeInvPunct` does not contain the embedding point `E.e x` (whose tube inverse
is the zero-section point `0_x`, which is not punctured). -/
theorem tubeInvPunct_sub (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε) (x : V.pt) {y : ↥C.U} (hy : y ∈ tubeInvPunct E C) :
    (y : Euc (8 + k)) ≠ E.e x := by
  intro h
  have h1 : C.inv y.1 = zeroSectionNormal E x := by
    rw [h]
    exact inv_embed E C x
  simp only [tubeInvPunct, Set.mem_setOf_eq] at hy
  rw [h1] at hy
  rw [mem_normalNonzero] at hy
  have h2 : normalNorm E (zeroSectionNormal E x) = 0 := by
    rw [zeroSectionNormal_apply, Work.Tubular.normalNorm_mk, norm_zero]
  exact hy h2

/-- **The determinate ambient standard class on the tube**, based at the embedding point `E.e x`:
the pull-back of the (explicit, `Mpun`-normalised) standard generator `stdModelGen (8+k)` of the pair
`(ℝ^{k+8}, ℝ^{k+8}∖0)` along the translation `y ↦ y - E.e x`.

In the coorientation coordinates given by the σ-corrected normal frame (TEL,
`Work.ThomBordism.sigmaTelescope_gauss`) this is the reference against which the *local* class of
the collapse class is measured. -/
def ambientStandardClass (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε) (x : V.pt) :
    Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) (tubeInvPunct E C) :=
  (Work.Thom.relCohMap
    (⟨fun y : ↥C.U => (y : Euc (8 + k)) - E.e x,
      continuous_subtype_val.sub continuous_const⟩)
    (tubeInvPunct E C) ({0}ᶜ)
    (fun y hy => by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact sub_ne_zero.mpr (tubeInvPunct_sub E C x hy))
    ℤ (8 + k)).hom (stdModelGen (8 + k))

/-- The map induced on relative homology by the tube inverse `C.inv`, from the neighbourhood pair
`(C.U, C.U∖tubeInvPunct)` of the zero section to the pair `(ν, ν∖0)`. -/
def tubeInvHomology (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε) :
    (Work.Cohomology.relChains (TopCat.of ↥C.U) (tubeInvPunct E C)).homology (k + 8) →ₗ[ℤ]
      (Work.Cohomology.relChains (TopCat.of (NormalTotal E))
        (normalNonzero E)).homology (k + 8) :=
  (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
    (TopCat.of (NormalTotal E)) (tubeInvPunct E C) (normalNonzero E)
    (TopCat.ofHom (tubeInvMap E C))
    (TopCat.ofHom ⟨fun y : ↥(tubeInvPunct E C) =>
        ⟨C.inv y.1.1, y.2⟩,
      Continuous.subtype_mk ((tubeInvMap E C).continuous.comp continuous_subtype_val)
        (fun y => (show C.inv (↑(y : ↥C.U) : Euc (8 + k)) ∈ normalNonzero E from y.2))⟩)
    (by apply TopCat.ext; intro a; rfl)) (k + 8)).hom

end

end Work.ThomBordism
