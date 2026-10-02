import Mathlib
import Submission.Work.Tubular.Small
import Submission.Work.Tubular.TubeBasic
import Submission.Work.Tubular.Collapse
import Submission.Work.Tubular.Global

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# The zero section of the normal bundle and the transversality of the collapse

This file exports the **`ν`-side of the transversality data** that the Transversality chapter
(`Submission/Work/ThomBordism/Transversality/`, vocabulary `CoreTarget`, `IsTransverseAt`,
`IsTransverseOn`) consumes from this chapter.

The collapse `c_V` of a tube chart is `thomMk ∘ inv` on the tube, so near the core
(= the image of the zero section of `Th(ν)`) the vertical coordinate of the Thom space pulls back to
the **normal coordinate** `normalCoord E C y = (C.inv y).vec` of the tube chart.  We prove:

* `Work.Tubular.contMDiffOn_normalCoord` — the normal coordinate is `C^∞` on the open tube (so the
  collapse is smooth near the zero section, where the ambient smooth structure of the Thom space
  comes from the tube);
* `Work.Tubular.normalCoord_eq_zero_iff` — its zero locus *is* the image of `V`;
* `Work.Tubular.normalCoord_tubeMap`, `exists_normalCoord_eq` — the normal coordinate is
  *surjective onto the whole normal fibre* over every point of `V`, at distance `< ε` (this is the
  point-set content of transversality: the collapse meets the core exactly in `V`, and crosses it);
* `Work.Tubular.tubeCollapse_mem_normalThomZero_iff` — `c_V⁻¹(core) = e(V)`;
* `Work.Tubular.TubeTransversality` — the one remaining *input* of the chapter: that the normal
  coordinate is a `C^∞` **submersion** along the zero section (equivalently: that the core of `Th(ν)`
  is a submanifold and the collapse is transverse to it).  This is the form
  `Manifold.IsSubmersionAt` in which the Transversality chapter states transversality.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The zero section and the normal coordinate -/

/-- The **zero section** of the normal bundle, as a set of the normal total space. -/
def zeroSection (E : EmbeddingData V (8 + k)) : Set (NormalTotal E) := {p | p.1.2 = 0}

theorem mem_zeroSection {E : EmbeddingData V (8 + k)} {p : NormalTotal E} :
    p ∈ zeroSection E ↔ p.1.2 = 0 := Iff.rfl

/-- The zero section is the image of `V` under the tubular map. -/
theorem tubeMap_zeroSection_eq (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    tubeMap E '' (zeroSection E) = Set.range E.e := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1.1, by rw [tubeMap, hp, add_zero]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x, 0), by simp⟩, rfl, tubeMap_zeroSection E x⟩

/-- The **normal (vertical) coordinate** of a tube chart: the normal component of the foot of `y`.
This is the pullback along the collapse of the vertical coordinate of the Thom space near the core,
and it vanishes exactly on the image of `V`. -/
def normalCoord (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (y : Euc (8 + k)) :
    Euc (8 + k) := (C.inv y).1.2

/-- The normal coordinate is `C^∞` on the open tube: the collapse is smooth near the zero section. -/
theorem contMDiffOn_normalCoord (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Euc (8 + k)) 𝓘(ℝ, Euc (8 + k)) ∞ (normalCoord E C) C.openTube := by
  have h : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) ((𝓡 8).prod 𝓘(ℝ, Euc (8 + k))) ∞
      (fun y => ((C.inv y).1.1, (C.inv y).1.2)) C.openTube := C.contMDiffOn_inv
  exact (contMDiff_snd (I := 𝓡 8) (J := 𝓘(ℝ, Euc (8 + k)))).comp_contMDiffOn h

/-- On the image of the tubular map the normal coordinate is the normal vector. -/
theorem normalCoord_tubeMap (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (p : NormalTotal E) (hp : normalNorm E p < ε) :
    normalCoord E C (tubeMap E p) = p.1.2 := by
  rw [normalCoord, C.inv_tubeMap p (le_of_lt hp)]

/-- **The zero locus of the normal coordinate is the image of `V`.** -/
theorem normalCoord_eq_zero_iff (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    {y : Euc (8 + k)} (hy : y ∈ C.openTube) :
    normalCoord E C y = 0 ↔ y ∈ Set.range E.e := by
  constructor
  · intro h
    refine ⟨(C.inv y).1.1, ?_⟩
    have hmem : (0 : Euc (8 + k)) ∈ normalSpace E (C.inv y).1.1 := by
      rw [← h]; exact (C.inv y).2
    have hinv : C.inv y = (⟨((C.inv y).1.1, 0), hmem⟩ : NormalTotal E) :=
      Subtype.ext (Prod.ext rfl h)
    have htm := C.tubeMap_inv y (C.openTube_subset_U hy)
    rw [hinv, tubeMap_mk] at htm
    simpa using htm
  · rintro ⟨x, rfl⟩
    have h1 : tubeMap E (⟨(x, 0), by simp⟩ : NormalTotal E) = E.e x := tubeMap_zeroSection E x
    have h2 : C.inv (E.e x) = (⟨(x, 0), by simp⟩ : NormalTotal E) := by
      rw [← h1]
      exact C.inv_tubeMap _ (by simpa using C.eps_pos.le)
    have : normalCoord E C (E.e x) = (⟨(x, 0), by simp⟩ : NormalTotal E).1.2 := by
      rw [normalCoord, h2]
    rw [this]

/-- **Every normal direction is realised**: for `w` in the normal space at `x` with `‖w‖ < ε`, the
point `e x + w` lies in the open tube and its normal coordinate is `w`.  This is the point-set
content of the transversality of the collapse to the core at the points of `V`. -/
theorem exists_normalCoord_eq (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (x : V.pt) {w : Euc (8 + k)} (hw : w ∈ normalSpace E x) (hεw : ‖w‖ < ε) :
    tubeMap E (⟨(x, w), hw⟩ : NormalTotal E) ∈ C.openTube ∧
      normalCoord E C (tubeMap E (⟨(x, w), hw⟩ : NormalTotal E)) = w := by
  have hlt : normalNorm E (⟨(x, w), hw⟩ : NormalTotal E) < ε := by simpa using hεw
  exact ⟨C.tubeMap_mem_openTube hlt, normalCoord_tubeMap E C _ hlt⟩

/-! ## The core of the Thom space of the normal bundle -/

/-- **The core of `Th(ν)`**: the image of the zero section of the disc bundle. -/
def normalThomZero (E : EmbeddingData V (8 + k)) (ε : ℝ) : Set (NormalThomSpace E ε) :=
  normalThomMk E ε '' {q : NormalDiscSub E ε | q.1.1.2 = 0}

/-- **`c_V⁻¹(core) = e(V)`**: a point of the tube collapses into the core exactly when it lies on `V`.
This is the "the collapse is transverse to the core with preimage `V`" statement, at the level of
point sets. -/
theorem tubeCollapse_mem_normalThomZero (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {y : Euc (8 + k)} (hy : y ∈ C.U) :
    tubeCollapse C q y ∈ normalThomZero E ε ↔ y ∈ Set.range E.e := by
  rw [tubeCollapse_of_mem C q hy, normalThomZero]
  constructor
  · rintro ⟨q', hq', heq⟩
    rcases (normalThomMk_eq_iff q' (⟨C.inv y, C.inv_mem y hy⟩ : NormalDiscSub E ε)).1 heq with
      h | ⟨h1, h2⟩
    · -- the feet agree, and the normal vector of `q'` is zero
      refine ⟨(C.inv y).1.1, ?_⟩
      have hvec : (C.inv y).1.2 = 0 := by
        have hcast := congrArg (fun z : NormalDiscSub E ε => z.1.1.2) h
        exact hcast.symm.trans hq'
      have htm := C.tubeMap_inv y hy
      rw [tubeMap, hvec, add_zero] at htm
      exact htm
    · have hz : normalNorm E q'.1 = 0 := by simpa [normalNorm] using hq'
      exact absurd (h1.symm.trans hz) C.eps_pos.ne'
  · rintro ⟨x, rfl⟩
    have h1 : tubeMap E (⟨(x, 0), by simp⟩ : NormalTotal E) = E.e x := tubeMap_zeroSection E x
    have h2 : C.inv (E.e x) = (⟨(x, 0), by simp⟩ : NormalTotal E) := by
      rw [← h1]
      exact C.inv_tubeMap _ (by simpa using C.eps_pos.le)
    refine ⟨⟨C.inv (E.e x), C.inv_mem (E.e x) hy⟩, ?_, rfl⟩
    have h3 : (C.inv (E.e x)).1.2 = (0 : Euc (8 + k)) := by rw [h2]
    exact h3

/-! ## The remaining datum -/

/-- **The transversality datum, in its correct form.**

The derivative of the normal coordinate at a point of the zero section has image *exactly* the normal
space `ν_x = T_x^⊥`: geometrically, `d(normalCoord)_{e x}` is the orthogonal projection of
`ℝ^{8+k} = T_x ⊕ ν_x` onto `ν_x`.

**Correction (a mis-stated lemma, found here).**  An earlier version of this structure asked that
`normalCoord E C`, regarded as a map `Euc (8+k) → Euc (8+k)`, be a `Manifold.IsSubmersionAt`
submersion at `E.e x`.  That statement is **false** for every nonempty `V`: the derivative has rank
`k = N - 8` (its image is the *normal* space, `finrank_normalSpace`), so it is never surjective onto
the `N`-dimensional ambient space.  The consumer of this datum
(`Work.ThomBordism.Transversality.CoreTarget`, `Submission/Work/ThomBordism/Transversality/Basic.lean`)
is careful to require the submersion *onto the `k`-dimensional normal space*
(`CoreTarget.isSubmersionAt_Φ : IsSubmersionAt (𝓡 n) (𝓡 k) ∞ Φ x`), which is the correct shape; on
the `ν`-side that shape is reached by composing with a linear isomorphism `ν_x ≅ ℝ^k`, and the
intrinsic content — independent of that choice — is the statement below.

Everything else the Transversality chapter needs from this side *is* proved above
(`contMDiffOn_normalCoord`, `normalCoord_eq_zero_iff`, `exists_normalCoord_eq`,
`tubeCollapse_mem_normalThomZero`). -/
structure TubeTransversality (E : EmbeddingData V (8 + k)) (ε : ℝ) (C : TubeChart E ε) : Prop where
  /-- the derivative of the normal coordinate at a point of the zero section has image the normal
  space -/
  mfderiv_range : ∀ x : V.pt,
    (mfderiv 𝓘(ℝ, Euc (8 + k)) 𝓘(ℝ, Euc (8 + k)) (normalCoord E C) (E.e x)).toLinearMap.range
      = normalSpace E x

end

end Work.Tubular
