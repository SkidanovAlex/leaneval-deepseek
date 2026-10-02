import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.euclideanLocalHomologyTop
import Submission.Work.Cohomology.euclideanLocalHomologyZero
import Submission.Work.Cohomology.relCohomologyDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local cohomology of a charted space in dimension `n`

For a charted space `M` of dimension `n ≥ 1` and a point `x`, the relative singular cohomology
`Hⁿ(M, M ∖ {x}; ℤ)` is `ℤ`.

The proof computes the *homology* of the pair and transfers it to cohomology:

* `homologyTwoCover` (the two-open-set form of excision) shrinks `(M, M ∖ {x})` to the pair
  `(U, U ∖ {x})` given by the source of the chart at `x`;
* `relChains_chart` (a homeomorphism of pairs induces an isomorphism of relative chain complexes)
  replaces the chart source by its target, an open subset of `ℝⁿ`;
* `homologyTwoCover` in `ℝⁿ` (the cover `{target, ℝⁿ ∖ chart x}`) and `relChains_translate`
  (translation of the base point) reduce to the pair `(ℝⁿ, ℝⁿ ∖ {0})`;
* `euclideanLocalHomologyTop` / `euclideanLocalHomologyZero` compute that pair;
* the universal-coefficient statement `relCohomologyDual` (for a degreewise free complex whose
  homology is free) identifies `Hⁿ(M, M ∖ {x})` with the dual of `Hₙ(M, M ∖ {x}) ≅ ℤ`.

Everything is exposed as a lemma about `Work.Cohomology.relChains`/`relComplex`, so no private
notation is needed.
-/

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology Limits

/-- The chain map of singular chains is functorial. -/
lemma chainMap_comp' (X Y Z : TopCat.{0}) (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap ℤ X Z (f ≫ g) = chainMap ℤ X Y f ≫ chainMap ℤ Y Z g :=
  CategoryTheory.Functor.map_comp _ _ _

/-- The chain map of an identity is an identity. -/
lemma chainMap_id' (X : TopCat.{0}) : chainMap ℤ X X (𝟙 X) = 𝟙 (singularChains ℤ X) :=
  CategoryTheory.Functor.map_id _ _

/-- An isomorphism in `ModuleCat` as a linear equivalence of the underlying modules. -/
def moduleIsoToLinearEquiv' {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) :
    ↥M ≃ₗ[R] ↥N :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

/-- **Relative homology is invariant under a homeomorphism of pairs**: if `e : X ≃ₜ Y` maps `A`
onto `B`, then `H_k(X, A) ≅ H_k(Y, B)`. -/
theorem relChains_homeomorph (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    Nonempty ((relChains (TopCat.of X) A).homology k ≅ (relChains (TopCat.of Y) B).homology k) := by
  set E := TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e with hE
  have hEf : ∀ x : X, (E.hom : X → Y) x = e x := by
    intro x
    rw [hE, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply]
    rfl
  have he' : ∀ x, x ∈ A ↔ (E.hom : X → Y) x ∈ B := by
    intro x; rw [hEf x]; exact he x
  have hev : ∀ a : ↥A, (E.hom : X → Y) a.1 ∈ B := fun a => (he' a.1).mp a.2
  have hev' : ∀ b : ↥B, (E.inv : Y → X) b.1 ∈ A := by
    intro b
    refine (he' ((E.inv : Y → X) b.1)).mpr ?_
    have h : (TopCat.Hom.hom E.hom) ((TopCat.Hom.hom E.inv) b.1) = b.1 := by
      have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
        rw [E.inv_hom_id]
      exact DFunLike.congr_fun h2 b.1
    rw [h]; exact b.2
  let hA : ↥A ≃ₜ ↥B :=
    { toFun := fun a => ⟨(E.hom : X → Y) a.1, hev a⟩
      invFun := fun b => ⟨(E.inv : Y → X) b.1, hev' b⟩
      left_inv := by
        intro a
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.hom ≫ E.inv) = TopCat.Hom.hom (𝟙 (TopCat.of X)) := by
          rw [E.hom_inv_id]
        exact DFunLike.congr_fun h2 a.1
      right_inv := by
        intro b
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
          rw [E.inv_hom_id]
        exact DFunLike.congr_fun h2 b.1
      continuous_toFun := ((TopCat.Hom.hom E.hom).continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((TopCat.Hom.hom E.inv).continuous.comp continuous_subtype_val).subtype_mk _ }
  have hsq : inclChains (TopCat.of X) A ≫ chainMap ℤ (TopCat.of X) (TopCat.of Y) E.hom =
      chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B) (TopCat.isoOfHomeo hA).hom ≫
        inclChains (TopCat.of Y) B := by
    have h2 : (subtypeIncl (TopCat.of X) A ≫ E.hom) =
        ((TopCat.isoOfHomeo hA).hom ≫ subtypeIncl (TopCat.of Y) B) := by
      apply TopCat.hom_ext
      ext a
      rfl
    simp only [inclChains]
    rw [← chainMap_comp', ← chainMap_comp', h2]
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
    (cokernel.mapIso (f := inclChains (TopCat.of X) A) (f' := inclChains (TopCat.of Y) B)
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo hA))
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso E) hsq)⟩

/-- Translation of the base point does not change the relative chain complex. -/
def translateHomeo (E : Type) [NormedAddCommGroup E] (q : E) : E ≃ₜ E where
  toFun := fun y => y + q
  invFun := fun y => y - q
  left_inv := by intro y; simp
  right_inv := by intro y; simp
  continuous_toFun := continuous_id.add continuous_const
  continuous_invFun := continuous_id.sub continuous_const

/-- **Translation invariance** of `H_k(ℝⁿ, ℝⁿ ∖ {q})`. -/
theorem relChains_translate (E : Type) [NormedAddCommGroup E] (q : E) (k : ℕ) :
    Nonempty ((relChains (TopCat.of E) {y : E | y ≠ 0}).homology k ≅
      (relChains (TopCat.of E) {y : E | y ≠ q}).homology k) := by
  refine relChains_homeomorph E E {y : E | y ≠ 0} {y : E | y ≠ q} (translateHomeo E q) ?_ k
  intro y
  show y ≠ 0 ↔ y + q ≠ q
  constructor
  · intro h hq
    exact h (add_right_cancel (hq.trans (zero_add q).symm))
  · intro h h0
    exact h (by rw [h0]; simp)

/-- **The chart of a charted space gives a homeomorphism of pairs**
`(source, source ∖ {x}) ≃ (target, target ∖ {chart x})`. -/
theorem relChains_chart (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) (k : ℕ) :
    Nonempty ((relChains (TopCat.of ↥(chartAt (EuclideanSpace ℝ (Fin n)) x).source)
        {y : ↥(chartAt (EuclideanSpace ℝ (Fin n)) x).source | (y : M) ≠ x}).homology k ≅
      (relChains (TopCat.of ↥(chartAt (EuclideanSpace ℝ (Fin n)) x).target)
        {y : ↥(chartAt (EuclideanSpace ℝ (Fin n)) x).target |
          (y : EuclideanSpace ℝ (Fin n)) ≠ (chartAt (EuclideanSpace ℝ (Fin n)) x) x}).homology k) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ c.source := mem_chart_source _ x
  refine relChains_homeomorph ↥c.source ↥c.target _ _ c.toHomeomorphSourceTarget ?_ k
  intro y
  have happly : (c.toHomeomorphSourceTarget y : EuclideanSpace ℝ (Fin n)) = c (y : M) :=
    OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe c y
  change (y : M) ≠ x ↔ (c.toHomeomorphSourceTarget y : EuclideanSpace ℝ (Fin n)) ≠ c x
  rw [happly]
  constructor
  · intro h hc
    exact h (c.toPartialEquiv.injOn y.2 hx hc)
  · intro h h0
    exact h (by rw [h0])

/-- Evaluation at `1` identifies the dual of `ℤ` with `ℤ`.

(Renamed from `Work.Cohomology.dualZ` by the `Islands` subproject: the name `dualZ` is also used
by `Submission/Work/Cohomology/dualZ.lean` for the `ℤ`-dual *cochain complex*, and two declarations
with the same name cannot be imported into one file.  This one has no user outside this file; the
other has ~60, so we rename here.  The statement is unchanged.) -/
def dualZOne : (ℤ →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ where
  toFun f := f 1
  invFun z := z • LinearMap.id
  left_inv f := by
    apply LinearMap.ext
    intro z
    have h : f z = z * f 1 := by
      have h2 := map_smul f z (1 : ℤ)
      simpa using h2
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rw [mul_comm, h]
  right_inv z := by
    show (z • LinearMap.id) 1 = z
    simp
  map_add' f g := by simp
  map_smul' a f := by simp

/-- **The local homology of a charted space**: `H_k(M, M ∖ {x})` is `ℤ` in degree `n` and
vanishes otherwise, for a charted space of dimension `n ≥ 1`. -/
theorem localHomology_charted (n : ℕ) (hn : 1 ≤ n) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) (k : ℕ) :
    (k = n → Nonempty ((relChains (TopCat.of M) {y : M | y ≠ x}).homology k ≅
        ModuleCat.of ℤ ℤ)) ∧
      (k ≠ n → CategoryTheory.Limits.IsZero
        ((relChains (TopCat.of M) {y : M | y ≠ x}).homology k)) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ c.source := mem_chart_source _ x
  haveI : T1Space M := ChartedSpace.t1Space (EuclideanSpace ℝ (Fin n)) M
  have hcompl : IsOpen {y : M | y ≠ x} := isOpen_compl_iff.mpr isClosed_singleton
  have hcov : c.source ∪ {y : M | y ≠ x} = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : y = x
      · exact Or.inl (hy ▸ hx)
      · exact Or.inr hy
  have hq : c x ∈ c.target := c.map_source hx
  have hcompl' : IsOpen {y : EuclideanSpace ℝ (Fin n) | y ≠ c x} :=
    isOpen_compl_iff.mpr isClosed_singleton
  have hcov' : c.target ∪ {y : EuclideanSpace ℝ (Fin n) | y ≠ c x} = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : y = c x
      · exact Or.inl (hy ▸ hq)
      · exact Or.inr hy
  have chain : ∀ k, Nonempty ((relChains (TopCat.of M) {y : M | y ≠ x}).homology k ≅
      (relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ≠ 0}).homology k) := by
    intro k
    obtain ⟨E1⟩ := homologyTwoCover (TopCat.of M) c.source {y : M | y ≠ x} c.open_source
      hcompl hcov k
    obtain ⟨E2⟩ := relChains_chart n M x k
    obtain ⟨E3⟩ := homologyTwoCover (TopCat.of (EuclideanSpace ℝ (Fin n))) c.target
      {y : EuclideanSpace ℝ (Fin n) | y ≠ c x} c.open_target hcompl' hcov' k
    obtain ⟨E4⟩ := relChains_translate (EuclideanSpace ℝ (Fin n)) (c x) k
    exact ⟨E1 ≪≫ E2 ≪≫ E3.symm ≪≫ E4.symm⟩
  constructor
  · intro hk
    rw [hk]
    obtain ⟨E⟩ := chain n
    obtain ⟨E5⟩ := euclideanLocalHomologyTop n hn
    exact ⟨E ≪≫ E5⟩
  · intro hk
    obtain ⟨E⟩ := chain k
    exact CategoryTheory.Limits.IsZero.of_iso (euclideanLocalHomologyZero n k hn hk) E

/-- **The local cohomology of a charted space in dimension `n`.**

For a charted space `M` of dimension `n ≥ 1` and a point `x`, the relative singular cohomology
`Hⁿ(M, M ∖ {x}; ℤ)` is `ℤ`. -/
theorem localCohomology (n : ℕ) (hn : 1 ≤ n) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    Nonempty (((Work.Cohomology.relComplex ℤ (TopCat.of M) {y : M | y ≠ x}).homology n) ≅
      ModuleCat.of ℤ ℤ) := by
  have htop : Nonempty ((relChains (TopCat.of M) {y : M | y ≠ x}).homology n ≅
      ModuleCat.of ℤ ℤ) := (localHomology_charted n hn M x n).1 rfl
  have hzero : ∀ k, k ≠ n → CategoryTheory.Limits.IsZero
      ((relChains (TopCat.of M) {y : M | y ≠ x}).homology k) :=
    fun k hk => (localHomology_charted n hn M x k).2 hk
  have hfree : ∀ k, Module.Free ℤ ↥((relChains (TopCat.of M) {y : M | y ≠ x}).homology k) := by
    intro k
    by_cases hk : k = n
    · rw [hk]
      obtain ⟨E⟩ := htop
      exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) (moduleIsoToLinearEquiv' E).symm
    · haveI : Subsingleton ↥((relChains (TopCat.of M) {y : M | y ≠ x}).homology k) :=
        ModuleCat.subsingleton_of_isZero (hzero k hk)
      exact Module.Free.of_subsingleton ℤ _
  obtain ⟨E⟩ := relCohomologyDual (TopCat.of M) {y : M | y ≠ x} hfree n
  obtain ⟨F⟩ := htop
  refine ⟨E ≪≫ LinearEquiv.toModuleIso ?_⟩
  exact (LinearEquiv.dualMap (moduleIsoToLinearEquiv' F)).symm.trans dualZOne

end

end Work.Cohomology
