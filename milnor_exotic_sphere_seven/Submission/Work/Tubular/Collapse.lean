import Submission.Work.Tubular.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The Pontryagin–Thom collapse of a tubular neighbourhood

Given the tubular neighbourhood theorem in the form of `Work.Tubular.TubeChart` — a radius `ε > 0`, a
closed set `U ⊆ ℝ^N` which is the image of the closed `ε`-disc bundle of the normal bundle under the
tubular map `(x,w) ↦ e x + w`, and a continuous inverse `inv` — this file builds

* `Work.Tubular.tubeInvDisc` — the "normal foot" map `ℝ^N → D_ε(ν)`, which is `inv` on the tube and
  a basepoint off it;
* `Work.Tubular.tubeCollapse` — **the collapse map** `c : ℝ^N → Th(ν)`, `c = thomMk ∘ inv` on the
  tube and the basepoint outside;
* `Work.Tubular.tubeCollapseOnePoint` — `c` as a map `S^N = ℝ^N ∪ {∞} → Th(ν)` of the one-point
  compactification (needs that the tube is compact, `Work.Tubular.TubeChart.isCompact_U`);
* `Work.Tubular.tubeCollapseCube` / `Work.Tubular.tubeGenLoop` — the collapse as an element of
  Mathlib's cube model `GenLoop (Fin N) (Th ν) (basepoint)`, the form the Pontryagin–Thom chapter
  consumes (`Work.ThomBordism.PontryaginThom.PTRep.collapse`).

The mathematical content is the continuity of the collapse: on the closed tube `U` it is
`thomMk ∘ inv`, and off the *open* tube it is constant equal to the basepoint (this is where
`thomMk` of a point of the sphere bundle — `Work.Tubular.tubeCollapse_eq_basepoint` — is used).
The two pieces `U` and `(open tube)ᶜ` are closed and cover `ℝ^N`, so the pasting lemma applies.
-/

open scoped Manifold ContDiff Topology unitInterval
open Function Topology Filter

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-! ## The normal foot map -/

/-- The "normal foot" map of a tube chart: on the (closed) tube it is the inverse `inv` of the
tubular map, and off the tube it is the constant map to a chosen point `q` of the sphere bundle. -/
def tubeInvDisc {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
    (y : Euc N) : NormalDiscSub E ε := by
  classical
  exact if h : y ∈ C.U then ⟨C.inv y, C.inv_mem y h⟩ else ⟨q.1, le_of_eq q.2⟩

theorem tubeInvDisc_of_mem {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {y : Euc N} (h : y ∈ C.U) :
    tubeInvDisc C q y = ⟨C.inv y, C.inv_mem y h⟩ := dif_pos h

theorem tubeInvDisc_of_notMem {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {y : Euc N} (h : y ∉ C.U) :
    tubeInvDisc C q y = ⟨q.1, le_of_eq q.2⟩ := dif_neg h

/-! ## The collapse map -/

/-- **The Pontryagin–Thom collapse map** of a tubular neighbourhood: a point of the tube is sent to
the class of its normal foot in `Th(ν) = D_ε(ν)/S_ε(ν)`, and every point outside the tube is sent to
the basepoint. -/
def tubeCollapse {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
    (y : Euc N) : NormalThomSpace E ε :=
  normalThomMk E ε (tubeInvDisc C q y)

/-- On the tube, the collapse is the class of the normal foot. -/
theorem tubeCollapse_of_mem {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {y : Euc N} (h : y ∈ C.U) :
    tubeCollapse C q y = normalThomMk E ε ⟨C.inv y, C.inv_mem y h⟩ := by
  rw [tubeCollapse, tubeInvDisc_of_mem C q h]

/-- Outside the (closed) tube, the collapse is the basepoint. -/
theorem tubeCollapse_of_notMem {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {y : Euc N} (h : y ∉ C.U) :
    tubeCollapse C q y = normalThomBasepoint E ε q := by
  rw [tubeCollapse, tubeInvDisc_of_notMem C q h]
  rfl

/-- **A point whose normal foot lies on the sphere bundle collapses to the basepoint**: this is what
makes the collapse descend to the quotient `D_ε(ν)/S_ε(ν)`. -/
theorem tubeCollapse_eq_basepoint {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {p : NormalTotal E} (hp : normalNorm E p = ε) :
    tubeCollapse C q (tubeMap E p) = normalThomBasepoint E ε q := by
  have hU : tubeMap E p ∈ C.U := C.mem_U p (le_of_eq hp)
  rw [tubeCollapse_of_mem C q hU]
  refine normalThomBasepoint_eq ⟨C.inv (tubeMap E p), ?_⟩ q
  rw [C.inv_tubeMap p (le_of_eq hp)]
  exact hp

/-- The collapse is continuous on the closed tube. -/
theorem continuousOn_tubeCollapse_tube {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) : ContinuousOn (tubeCollapse C q) C.U := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : C.U.domRestrict (tubeCollapse C q) =
      (fun y : C.U => normalThomMk E ε (⟨C.inv y.1, C.inv_mem y.1 y.2⟩ : NormalDiscSub E ε)) := by
    funext y
    exact tubeCollapse_of_mem C q y.2
  rw [hfun]
  exact (continuous_normalThomMk E ε).comp
    (Continuous.subtype_mk C.continuousOn_inv.domRestrict _)

/-- Off the open tube, the collapse is constant, equal to the basepoint. -/
theorem tubeCollapse_eq_basepoint_of_notMem_openTube {E : EmbeddingData V N} {ε : ℝ}
    (C : TubeChart E ε) (q : NormalSphSub E ε) {y : Euc N} (hy : y ∉ C.openTube) :
    tubeCollapse C q y = normalThomBasepoint E ε q := by
  by_cases hU : y ∈ C.U
  · rw [tubeCollapse_of_mem C q hU]
    have hle : normalNorm E (C.inv y) ≤ ε := C.inv_mem y hU
    have hge : ε ≤ normalNorm E (C.inv y) := by
      by_contra hlt
      exact hy ⟨C.inv y, lt_of_not_ge hlt, C.tubeMap_inv y hU⟩
    refine normalThomBasepoint_eq ⟨C.inv y, le_antisymm hle hge⟩ q
  · rw [tubeCollapse_of_notMem C q hU]

/-- The collapse is continuous off the open tube. -/
theorem continuousOn_tubeCollapse_compl_openTube {E : EmbeddingData V N} {ε : ℝ}
    (C : TubeChart E ε) (q : NormalSphSub E ε) :
    ContinuousOn (tubeCollapse C q) C.openTubeᶜ := by
  have hconst : Set.EqOn (tubeCollapse C q) (fun _ : Euc N => normalThomBasepoint E ε q)
      C.openTubeᶜ := fun _ hy => tubeCollapse_eq_basepoint_of_notMem_openTube C q hy
  rw [continuousOn_congr hconst]
  exact continuousOn_const

/-- **The collapse map is continuous.** -/
theorem continuous_tubeCollapse {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) : Continuous (tubeCollapse C q) := by
  have hunion : C.U ∪ C.openTubeᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases h : y ∈ C.openTube
    · exact Or.inl (C.openTube_subset_U h)
    · exact Or.inr h
  rw [← continuousOn_univ, ← hunion]
  exact ContinuousOn.union_of_isClosed (continuousOn_tubeCollapse_tube C q)
    (continuousOn_tubeCollapse_compl_openTube C q) C.isClosed_U C.isOpen_openTube.isClosed_compl

/-- The collapse map, as a bundled continuous map `ℝ^N → Th(ν)`. -/
def tubeCollapseCM {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε) :
    C(Euc N, NormalThomSpace E ε) :=
  ⟨tubeCollapse C q, continuous_tubeCollapse C q⟩

@[simp] theorem tubeCollapseCM_apply {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) (y : Euc N) :
    tubeCollapseCM C q y = tubeCollapse C q y := rfl

/-! ## The collapse as a map of the one-point compactification -/

/-- **The collapse map on `S^N = ℝ^N ∪ {∞}`**: the one-point compactification of the ambient space,
with `∞ ↦` basepoint and the collapse of the tube on `ℝ^N`. -/
def tubeCollapseOnePoint {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) (hU : IsCompact C.U) : C(OnePoint (Euc N), NormalThomSpace E ε) where
  toFun x := Option.elim x (normalThomBasepoint E ε q) (tubeCollapse C q)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro x
    cases x with
    | infty =>
      rw [OnePoint.continuousAt_infty]
      intro s hs
      refine ⟨C.U, C.isClosed_U, hU, fun y hy => ?_⟩
      rw [Set.mem_compl_iff] at hy
      change tubeCollapse C q y ∈ s
      rw [tubeCollapse_of_notMem C q hy]
      exact mem_of_mem_nhds hs
    | coe y =>
      rw [OnePoint.continuousAt_coe]
      exact (continuous_tubeCollapse C q).continuousAt

@[simp] theorem tubeCollapseOnePoint_coe {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) (hU : IsCompact C.U) (y : Euc N) :
    tubeCollapseOnePoint C q hU y = tubeCollapse C q y := rfl

@[simp] theorem tubeCollapseOnePoint_infty {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) (hU : IsCompact C.U) :
    tubeCollapseOnePoint C q hU OnePoint.infty = normalThomBasepoint E ε q := rfl

/-! ## The collapse in the cube model -/

/-- The linear equivalence `(Fin n → ℝ) ≃ ℝⁿ` (the Euclidean space is the `ℓ²`-product). -/
def funToEuc (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] Euc n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm

/-- The coordinates of the cube of radius `R`: `t ↦ (2R(t_i - 1/2))_i`, whose image is the box
`[-R,R]^N`. -/
def cubeToFun (N : ℕ) (R : ℝ) (t : Fin N → unitInterval) : Fin N → ℝ := fun i => 2 * R * ((t i : ℝ) - 1 / 2)

@[simp] theorem cubeToFun_apply (N : ℕ) (R : ℝ) (t : Fin N → unitInterval) (i : Fin N) :
    cubeToFun N R t i = 2 * R * ((t i : ℝ) - 1 / 2) := rfl

/-- **The cube of radius `R`**: the linear parametrisation `I^N → ℝ^N` sending the cube `[0,1]^N`
onto the box `[-R,R]^N`. -/
def cubeToEuc (N : ℕ) (R : ℝ) : C((Fin N → unitInterval), Euc N) where
  toFun t := funToEuc N (cubeToFun N R t)
  continuous_toFun := (funToEuc N).continuous.comp (continuous_pi fun i => by
    have h1 : Continuous (fun t : Fin N → unitInterval => (t i : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply i)
    have h2 : Continuous (fun t : Fin N → unitInterval => (t i : ℝ) - 1 / 2) :=
      h1.sub continuous_const
    have h3 : Continuous (fun t : Fin N → unitInterval => (2 * R) • ((t i : ℝ) - 1 / 2)) :=
      h2.const_smul (2 * R)
    simpa [cubeToFun_apply, smul_eq_mul] using h3)

@[simp] theorem cubeToEuc_apply (N : ℕ) (R : ℝ) (t : Fin N → unitInterval) :
    cubeToEuc N R t = funToEuc N (cubeToFun N R t) := rfl

theorem funToEuc_symm_cubeToEuc (N : ℕ) (R : ℝ) (t : Fin N → unitInterval) :
    (funToEuc N).symm (cubeToEuc N R t) = cubeToFun N R t :=
  (funToEuc N).symm_apply_apply _

/-- On the boundary of the cube, some coordinate of the cube of radius `R` has absolute value
`R`. -/
theorem cubeToEuc_boundary (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {t : Fin N → unitInterval}
    (ht : t ∈ Cube.boundary (Fin N)) : ∃ i : Fin N, |(cubeToEuc N R t) i| = R := by
  obtain ⟨i, hi | hi⟩ := ht
  · refine ⟨i, ?_⟩
    have h1 : (cubeToEuc N R t) i = 2 * R * ((t i : ℝ) - 1 / 2) :=
      congrFun (funToEuc_symm_cubeToEuc N R t) i
    rw [h1, hi]
    rw [show (((0 : unitInterval) : ℝ)) = 0 from rfl]
    rw [show (2 : ℝ) * R * (0 - 1 / 2) = -R by ring, abs_neg, abs_of_nonneg hR]
  · refine ⟨i, ?_⟩
    have h1 : (cubeToEuc N R t) i = 2 * R * ((t i : ℝ) - 1 / 2) :=
      congrFun (funToEuc_symm_cubeToEuc N R t) i
    rw [h1, hi]
    rw [show (((1 : unitInterval) : ℝ)) = 1 from rfl]
    rw [show (2 : ℝ) * R * (1 - 1 / 2) = R by ring, abs_of_nonneg hR]

/-- The collapse of a tube chart, as a map of the cube `I^N`. -/
def tubeCollapseCube {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
    (R : ℝ) : C((Fin N → unitInterval), NormalThomSpace E ε) :=
  (tubeCollapseCM C q).comp (cubeToEuc N R)

@[simp] theorem tubeCollapseCube_apply {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) (R : ℝ) (t : Fin N → unitInterval) :
    tubeCollapseCube C q R t = tubeCollapse C q (cubeToEuc N R t) := rfl

/-- If the tube is contained in the box of radius `R`, the collapse is constant on the boundary of
the cube: the collapse map in the cube model. -/
theorem tubeCollapseCube_boundary {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin N, |y i| < R) {t : Fin N → unitInterval} (ht : t ∈ Cube.boundary (Fin N)) :
    tubeCollapseCube C q R t = normalThomBasepoint E ε q := by
  rw [tubeCollapseCube_apply]
  rw [tubeCollapse_of_notMem C q (fun hmem => ?_)]
  obtain ⟨i, hi⟩ := cubeToEuc_boundary N hR ht
  have h := hbox (cubeToEuc N R t) hmem i
  rw [hi] at h
  exact absurd h (lt_irrefl R)

/-- **The collapse map in the cube model**: an element of `GenLoop (Fin N) (Th ν) (basepoint)`. -/
theorem tubeCollapseCube_mem_genLoop {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε)
    (q : NormalSphSub E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin N, |y i| < R) :
    tubeCollapseCube C q R ∈ GenLoop (Fin N) (NormalThomSpace E ε) (normalThomBasepoint E ε q) :=
  fun _ ht => tubeCollapseCube_boundary C q hR hbox ht

/-- **The collapse of a tube chart as a genuine loop of the sphere `S^N`**: the element of
`GenLoop (Fin N) (Th ν) (basepoint)` attached to the tubular neighbourhood, in the form consumed by
the Pontryagin–Thom chapter.  The radius `R` is supplied by the caller
(`Work.Tubular.exists_box_tube`). -/
def tubeGenLoop {E : EmbeddingData V N} {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin N, |y i| < R) :
    GenLoop (Fin N) (NormalThomSpace E ε) (normalThomBasepoint E ε q) :=
  ⟨tubeCollapseCube C q R, tubeCollapseCube_mem_genLoop C q hR hbox⟩

end

end Work.Tubular
