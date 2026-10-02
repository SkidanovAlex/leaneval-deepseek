import Submission.Work.StemsB.EucCollarPair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collar pair of the sphere model is the Euclidean collar pair

The inner piece `sphLoopBig n` of the sphere model `SphModel n = OnePoint ℝⁿ`, its collar
`sphLoopCollar n`, and the Euclidean pieces `eucBig n`, `eucCollar n` of
`Submission/Work/StemsB/CollarNorm.lean` are related by the *same* set of vectors: the map

  `q ↦ (the coordinate vector of q, the parameter)`

is a bijection `↥(sphLoopBig n) × Y → ↥(eucBig n) × Y` (with inverse `(v,y) ↦ (↑v, y)`), and it
carries the collar onto the Euclidean collar.  Since `OnePoint.some` is injective, the two maps are
literally mutually inverse, so they give a homeomorphism of pairs, and the relative Künneth theorem
for the Euclidean collar pair (`Work.StemsB.eucCollar_iso`, `Work.StemsB.eucCollar_isZero`)
transports to the sphere model:

* `Work.StemsB.serreSphere_collar_iso`, `Work.StemsB.serreSphere_collar_isZero`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.StemsB

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]

/-! ## The coordinate vector of a point of the model -/

/-- The **coordinate vector** of a point of the sphere model, with the junk value `0` at `∞`. -/
def modelVec (n : ℕ) : SphModel n → EuclideanSpace ℝ (Fin n)
  | none => 0
  | some v => v

@[simp] theorem modelVec_some (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    modelVec n (OnePoint.some v) = v := rfl

@[simp] theorem modelVec_eq_self (n : ℕ) {x : SphModel n} (hx : x ≠ OnePoint.infty) :
    OnePoint.some (modelVec n x) = x := by
  rcases x with _ | v
  · exact absurd rfl hx
  · rfl

theorem continuousAt_modelVec_some (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (modelVec n) (OnePoint.some v) := by
  have hf_oe : Topology.IsOpenEmbedding (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n) :=
    OnePoint.isOpenEmbedding_coe
  have hcomp : ContinuousAt
      (fun w : EuclideanSpace ℝ (Fin n) => modelVec n (OnePoint.some w)) v := by
    change ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) => w) v
    exact continuousAt_id
  exact (hf_oe.continuousAt_iff (g := fun x : SphModel n => modelVec n x)).mp hcomp

/-! ## The membership lemmas -/

theorem set_of_mem_sphLoopBig_of_mem_sphLoopCollar (n : ℕ) {x : SphModel n}
    (hx : x ∈ sphLoopCollar n) : x ∈ sphLoopBig n := hx.2

theorem modelVec_mem_eucBig (n : ℕ) {x : SphModel n} (hx : x ∈ sphLoopBig n) :
    modelVec n x ∈ eucBig n := by
  obtain ⟨v, hv, hvlt⟩ := hx
  rw [hv, modelVec_some]
  exact hvlt

theorem modelVec_mem_eucCollar (n : ℕ) {x : SphModel n} (hx : x ∈ sphLoopCollar n) :
    modelVec n x ∈ eucCollar n := by
  obtain ⟨hout, hbig⟩ := hx
  obtain ⟨v, hv, hvlt⟩ := hbig
  rw [hv, modelVec_some]
  rw [hv] at hout
  rcases hout with h | ⟨w, hw, i, hi⟩
  · exact absurd h (OnePoint.coe_ne_infty v)
  · have hwv : w = v := OnePoint.coe_injective hw.symm
    rw [hwv] at hi
    exact ⟨⟨i, hi⟩, hvlt⟩

theorem some_mem_sphLoopBig (n : ℕ) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ eucBig n) :
    OnePoint.some v ∈ sphLoopBig n := ⟨v, rfl, hv⟩

theorem some_mem_sphLoopCollar (n : ℕ) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ eucCollar n) :
    OnePoint.some v ∈ sphLoopCollar n :=
  ⟨Or.inr ⟨v, rfl, hv.1⟩, ⟨v, rfl, hv.2⟩⟩

theorem modelVec_ne_infty_of_mem_sphLoopBig (n : ℕ) {x : SphModel n} (hx : x ∈ sphLoopBig n) :
    x ≠ OnePoint.infty := by
  obtain ⟨v, hv, -⟩ := hx
  rw [hv]
  exact OnePoint.coe_ne_infty v

/-! ## Continuity of the coordinate extraction -/

/-- Continuity of the coordinate extraction on the inner piece. -/
theorem continuous_modelVec_big (n : ℕ) :
    Continuous fun q : ↥(sphLoopBig n) × Y => modelVec n q.1.1 := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨v, hv, -⟩ := q.1.2
  have hcont : Continuous fun q : ↥(sphLoopBig n) × Y => q.1.1 := by fun_prop
  have hg : ContinuousAt (fun x : SphModel n => modelVec n x) q.1.1 := by
    rw [show q.1.1 = OnePoint.some v from hv]
    exact continuousAt_modelVec_some n v
  have hcomp : ContinuousAt (fun q : ↥(sphLoopBig n) × Y => modelVec n q.1.1) q :=
    hg.comp (f := fun q : ↥(sphLoopBig n) × Y => q.1.1) hcont.continuousAt
  simpa only [Function.comp_apply] using hcomp

/-- Continuity of the coordinate extraction on the collar. -/
theorem continuous_modelVec_collar (n : ℕ) :
    Continuous fun q : ↥(sphLoopCollarProd n Y) => modelVec n q.1.1.1 := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨v, hv, -⟩ := set_of_mem_sphLoopBig_of_mem_sphLoopCollar n q.2
  have hcont : Continuous fun q : ↥(sphLoopCollarProd n Y) => q.1.1.1 := by fun_prop
  have hg : ContinuousAt (fun x : SphModel n => modelVec n x) q.1.1.1 := by
    rw [show q.1.1.1 = OnePoint.some v from hv]
    exact continuousAt_modelVec_some n v
  have hcomp : ContinuousAt (fun q : ↥(sphLoopCollarProd n Y) => modelVec n q.1.1.1) q :=
    hg.comp (f := fun q : ↥(sphLoopCollarProd n Y) => q.1.1.1) hcont.continuousAt
  simpa only [Function.comp_apply] using hcomp

/-! ## The two maps and their inverse identities -/

/-- The coordinate extraction on the inner piece. -/
def bigToEucMap (n : ℕ) : C(↥(sphLoopBig n) × Y, ↥(eucBig n) × Y) :=
  ⟨fun q => (⟨modelVec n q.1.1, modelVec_mem_eucBig n q.1.2⟩, q.2), by
    refine Continuous.prodMk (Continuous.subtype_mk (continuous_modelVec_big (Y := Y) n) _)
      continuous_snd⟩

/-- The inclusion of the Euclidean inner piece into the model. -/
def eucToBigMap (n : ℕ) : C(↥(eucBig n) × Y, ↥(sphLoopBig n) × Y) :=
  ⟨fun q => (⟨OnePoint.some q.1.1, some_mem_sphLoopBig n q.1.2⟩, q.2), by
    refine Continuous.prodMk (Continuous.subtype_mk
      ((OnePoint.continuous_coe (X := EuclideanSpace ℝ (Fin n))).comp (by fun_prop)) _)
      continuous_snd⟩

@[simp] theorem bigToEucMap_apply (n : ℕ) (q : ↥(sphLoopBig n) × Y) :
    bigToEucMap (Y := Y) n q = (⟨modelVec n q.1.1, modelVec_mem_eucBig n q.1.2⟩, q.2) := rfl

@[simp] theorem eucToBigMap_apply (n : ℕ) (q : ↥(eucBig n) × Y) :
    eucToBigMap (Y := Y) n q = (⟨OnePoint.some q.1.1, some_mem_sphLoopBig n q.1.2⟩, q.2) := rfl

theorem bigToEucMap_eucToBigMap (n : ℕ) :
    TopCat.ofHom ((bigToEucMap (Y := Y) n).comp (eucToBigMap (Y := Y) n))
      = 𝟙 (TopCat.of (↥(eucBig n) × Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  show (⟨modelVec n (OnePoint.some q.1.1), _⟩, q.2) = q
  apply Prod.ext
  · apply Subtype.ext
    exact modelVec_some n q.1.1
  · rfl

theorem eucToBigMap_bigToEucMap (n : ℕ) :
    TopCat.ofHom ((eucToBigMap (Y := Y) n).comp (bigToEucMap (Y := Y) n))
      = 𝟙 (TopCat.of (↥(sphLoopBig n) × Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  have hx : q.1.1 ≠ OnePoint.infty := modelVec_ne_infty_of_mem_sphLoopBig n q.1.2
  show (⟨OnePoint.some (modelVec n q.1.1), _⟩, q.2) = q
  apply Prod.ext
  · apply Subtype.ext
    exact modelVec_eq_self n hx
  · rfl

/-! ## The maps on the collar -/

/-- The coordinate extraction on the collar. -/
def bigToEucRelMap (n : ℕ) :
    C(↥(sphLoopCollarProd n Y), ↥(eucCollarProd n Y)) :=
  ⟨fun q => ⟨(⟨modelVec n q.1.1.1, modelVec_mem_eucBig n
        (set_of_mem_sphLoopBig_of_mem_sphLoopCollar n q.2)⟩, q.1.2),
      modelVec_mem_eucCollar n q.2⟩,
    by
      refine Continuous.subtype_mk (f := fun q : ↥(sphLoopCollarProd n Y) =>
        ((⟨modelVec n q.1.1.1, modelVec_mem_eucBig n
          (set_of_mem_sphLoopBig_of_mem_sphLoopCollar n q.2)⟩, q.1.2) : ↥(eucBig n) × Y)) ?_
        (fun q => modelVec_mem_eucCollar n q.2)
      exact Continuous.prodMk (Continuous.subtype_mk (continuous_modelVec_collar (Y := Y) n) _)
        (by fun_prop)⟩

/-- The inclusion of the Euclidean collar into the model. -/
def eucToBigRelMap (n : ℕ) :
    C(↥(eucCollarProd n Y), ↥(sphLoopCollarProd n Y)) :=
  ⟨fun q => ⟨(⟨OnePoint.some q.1.1.1, some_mem_sphLoopBig n q.1.1.2⟩, q.1.2),
      some_mem_sphLoopCollar n q.2⟩, by
    refine Continuous.subtype_mk (f := fun q : ↥(eucCollarProd n Y) =>
      ((⟨OnePoint.some q.1.1.1, some_mem_sphLoopBig n q.1.1.2⟩, q.1.2) :
        ↥(sphLoopBig n) × Y)) ?_ (fun q => some_mem_sphLoopCollar n q.2)
    refine Continuous.prodMk (Continuous.subtype_mk
      ((OnePoint.continuous_coe (X := EuclideanSpace ℝ (Fin n))).comp (by fun_prop)) _)
      (by fun_prop)⟩

theorem eucToBigRelMap_bigToEucRelMap (n : ℕ) :
    TopCat.ofHom ((eucToBigRelMap (Y := Y) n).comp (bigToEucRelMap (Y := Y) n))
      = 𝟙 (TopCat.of ↥(sphLoopCollarProd n Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  have hx : q.1.1.1 ≠ OnePoint.infty :=
    modelVec_ne_infty_of_mem_sphLoopBig n (set_of_mem_sphLoopBig_of_mem_sphLoopCollar n q.2)
  show (⟨(⟨OnePoint.some (modelVec n q.1.1.1), _⟩, q.1.2), _⟩ :
    ↥(sphLoopCollarProd n Y)) = q
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact modelVec_eq_self n hx
  · rfl

theorem bigToEucRelMap_eucToBigRelMap (n : ℕ) :
    TopCat.ofHom ((bigToEucRelMap (Y := Y) n).comp (eucToBigRelMap (Y := Y) n))
      = 𝟙 (TopCat.of ↥(eucCollarProd n Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  show (⟨(⟨modelVec n (OnePoint.some q.1.1.1), _⟩, q.1.2), _⟩ : ↥(eucCollarProd n Y)) = q
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact modelVec_some n q.1.1.1
  · rfl

/-! ## The homological consequences -/

theorem isIso_bigToEucHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (↥(sphLoopBig n) × Y)) (TopCat.of (↥(eucBig n) × Y))
      (TopCat.ofHom (bigToEucMap (Y := Y) n))) k) := by
  have h1 : TopCat.Homotopy (TopCat.ofHom (bigToEucMap (Y := Y) n) ≫
      TopCat.ofHom (eucToBigMap (Y := Y) n)) (𝟙 (TopCat.of (↥(sphLoopBig n) × Y))) := by
    rw [← TopCat.ofHom_comp, eucToBigMap_bigToEucMap]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (TopCat.ofHom (eucToBigMap (Y := Y) n) ≫
      TopCat.ofHom (bigToEucMap (Y := Y) n)) (𝟙 (TopCat.of (↥(eucBig n) × Y))) := by
    rw [← TopCat.ofHom_comp, bigToEucMap_eucToBigMap]
    exact ContinuousMap.Homotopy.refl _
  exact Work.Cohomology.homologyEquiv ℤ _ _ _ _ h1 h2 k

theorem isIso_bigToEucRelHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(sphLoopCollarProd n Y)) (TopCat.of ↥(eucCollarProd n Y))
      (TopCat.ofHom (bigToEucRelMap (Y := Y) n))) k) := by
  have h1 : TopCat.Homotopy (TopCat.ofHom (bigToEucRelMap (Y := Y) n) ≫
      TopCat.ofHom (eucToBigRelMap (Y := Y) n))
      (𝟙 (TopCat.of ↥(sphLoopCollarProd n Y))) := by
    rw [← TopCat.ofHom_comp, eucToBigRelMap_bigToEucRelMap]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (TopCat.ofHom (eucToBigRelMap (Y := Y) n) ≫
      TopCat.ofHom (bigToEucRelMap (Y := Y) n))
      (𝟙 (TopCat.of ↥(eucCollarProd n Y))) := by
    rw [← TopCat.ofHom_comp, bigToEucRelMap_eucToBigRelMap]
    exact ContinuousMap.Homotopy.refl _
  exact Work.Cohomology.homologyEquiv ℤ _ _ _ _ h1 h2 k

theorem bigToEucMap_subtypeIncl (n : ℕ) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × Y)) (sphLoopCollarProd n Y)
        ≫ TopCat.ofHom (bigToEucMap (Y := Y) n)
      = TopCat.ofHom (bigToEucRelMap (Y := Y) n)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(eucBig n) × Y)) (eucCollarProd n Y) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  rfl

/-- The chain map of relative complexes induced by the coordinate extraction. -/
def bigToEucRelChainMap (n : ℕ) :
    Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y)) (sphLoopCollarProd n Y) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(eucBig n) × Y)) (eucCollarProd n Y) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(sphLoopBig n) × Y))
    (TopCat.of (↥(eucBig n) × Y)) (sphLoopCollarProd n Y) (eucCollarProd n Y)
    (TopCat.ofHom (bigToEucMap (Y := Y) n)) (TopCat.ofHom (bigToEucRelMap (Y := Y) n))
    (bigToEucMap_subtypeIncl (Y := Y) n)

theorem isIso_bigToEucRelChains (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (bigToEucRelChainMap (Y := Y) n) k) :=
  Work.Cohomology.relChainsMapOf_isIso (X := TopCat.of (↥(sphLoopBig n) × Y))
    (Y := TopCat.of (↥(eucBig n) × Y)) (sphLoopCollarProd n Y) (eucCollarProd n Y)
    (TopCat.ofHom (bigToEucMap (Y := Y) n)) (TopCat.ofHom (bigToEucRelMap (Y := Y) n))
    (bigToEucMap_subtypeIncl (Y := Y) n) k
    (fun m => isIso_bigToEucHomology (Y := Y) n m)
    (fun m => isIso_bigToEucRelHomology (Y := Y) n m)

/-- **The relative homology of the collar pair of the sphere model, in degrees above the
dimension.** -/
theorem serreSphere_collar_iso (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
        (sphLoopCollarProd n Y)).homology (j + n)) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j) := by
  obtain ⟨e⟩ := eucCollar_iso n hn Y j
  haveI : IsIso (HomologicalComplex.homologyMap (bigToEucRelChainMap (Y := Y) n) (j + n)) :=
    isIso_bigToEucRelChains (Y := Y) n (j + n)
  exact ⟨asIso (HomologicalComplex.homologyMap (bigToEucRelChainMap (Y := Y) n) (j + n)) ≪≫ e⟩

/-- **The relative homology of the collar pair of the sphere model vanishes below the
dimension.** -/
theorem serreSphere_collar_isZero (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (hm : m < n) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
      (sphLoopCollarProd n Y)).homology m) := by
  haveI : IsIso (HomologicalComplex.homologyMap (bigToEucRelChainMap (Y := Y) n) m) :=
    isIso_bigToEucRelChains (Y := Y) n m
  exact IsZero.of_iso (eucCollar_isZero n hn Y m hm)
    (asIso (HomologicalComplex.homologyMap (bigToEucRelChainMap (Y := Y) n) m))

end

end Work.StemsB
