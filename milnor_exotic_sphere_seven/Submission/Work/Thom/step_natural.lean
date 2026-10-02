import Mathlib
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.pairDeltaNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.Thom

open CategoryTheory

noncomputable section

/-! ## Small tools for pulling back relative classes -/

/-- The pullback of relative cohomology does not depend on the proof that the map of pairs carries
the source set into the target set. -/
theorem relCohMap_hcongrA {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (Cset : Set Y) (h h' : ∀ x ∈ A, f x ∈ Cset) (R : Type) [CommRing R] (n : ℕ) :
    relCohMap f A Cset h R n = relCohMap f A Cset h' R n := by
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A Cset (TopCat.ofHom f) h) n
    = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A Cset (TopCat.ofHom f) h') n
  rw [relComplexMap_hcongrA A Cset (TopCat.ofHom f) h h' R]

/-- Applied functoriality of the pullback of relative cohomology. -/
theorem relCohMap_compA_apply {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ C) (hgf : ∀ x ∈ A, g (f x) ∈ C)
    (R : Type) [CommRing R] (n : ℕ) (x : RelCoh R n Z C) :
    (relCohMap f A B hf R n).hom ((relCohMap g B C hg R n).hom x)
      = (relCohMap (g.comp f) A C hgf R n).hom x := by
  rw [← relCohMap_compA A B C f g hf hg hgf R n]
  rfl

/-- Applied functoriality of the pullback of absolute cohomology. -/
theorem CohMap_comp_apply {B₁ B₂ B₃ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    [TopologicalSpace B₃] (f : C(B₁, B₂)) (g : C(B₂, B₃)) (R : Type) [CommRing R] (n : ℕ)
    (x : Coh R n B₃) :
    (CohMap f R n).hom ((CohMap g R n).hom x) = (CohMap (g.comp f) R n).hom x := by
  rw [CohMap_comp f g R n]
  rfl

/-- Applied naturality of `relToAbs`. -/
theorem relCohMap_relToAbs_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R]
    (n : ℕ) (x : RelCoh R n Y B) :
    (relToAbs R A n).hom ((relCohMap f A B hf R n).hom x)
      = (CohMap f R n).hom ((relToAbs R B n).hom x) := by
  have h := congrArg (fun φ => φ.hom x) (relCohMap_relToAbs f A B hf R n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-! ## The base inclusions on the disc and sphere bundles -/

/-- The inclusion `↥W × MBall n → B × MBall n` induced by `W ⊆ B`. -/
def baseInclBall (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    C(↥W × MBall n, B × MBall n) :=
  ⟨fun p => (((p.1 : ↥W) : B), p.2),
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd⟩

/-- The inclusion `↥W × MSph n → B × MSph n` induced by `W ⊆ B`. -/
def baseInclMSph (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    C(↥W × MSph n, B × MSph n) :=
  ⟨fun p => (((p.1 : ↥W) : B), p.2),
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd⟩

/-- The restriction of a map of pairs `f : X → Y` carrying `A ⊆ X` into `C ⊆ Y` to a map
`↥A → ↥C`. -/
def restrictMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (Cset : Set Y) (hf : ∀ x ∈ A, f x ∈ Cset) : C(↥A, ↥Cset) :=
  ⟨fun a : A => ⟨f ↑a, hf ↑a a.2⟩,
    Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) (fun a => hf ↑a a.2)⟩

/-- The restriction of `baseIncl` to the sphere bundles, as a map of pairs. -/
def baseInclSph (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    C(↥(Sph W n), ↥(Sph B n)) :=
  ⟨fun a => ⟨baseIncl B W n ↑a, a.2⟩,
    Continuous.subtype_mk ((baseIncl B W n).continuous.comp continuous_subtype_val)
      (fun a => a.2)⟩

/-- Naturality of the connecting homomorphism, in the applied form with an explicit restricted
map. -/
theorem pairDeltaNatural_restrict {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (Cset : Set Y) (hf : ∀ x ∈ A, f x ∈ Cset) (n : ℕ)
    (y : Coh ℤ n Cset) :
    (relCohMap f A Cset hf ℤ (n + 1)).hom ((pairδC Cset n).hom y)
      = (pairδC A n).hom ((CohMap (restrictMap f A Cset hf) ℤ n).hom y) :=
  pairDeltaNatural f A Cset hf n y

/-- The restricted base inclusion `baseInclSph` agrees with `restrictMap`. -/
theorem baseInclSph_eq_restrictMap (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    baseInclSph B W n
      = restrictMap (baseIncl B W n) (Sph W n) (Sph B n) (fun _ h => h) := by
  apply ContinuousMap.ext
  intro a
  rfl

/-! ## The two auxiliary map identities -/

/-- The disc transfers commute with the base inclusion. -/
theorem discFullMap_comp_baseInclBall (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    (CleanA.discFullMap B n).comp (baseInclBall B W n)
      = (baseIncl B W n).comp (CleanA.discFullMap W n) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- The cap transfers commute with the base inclusion. -/
theorem capMapPairSph_comp_baseInclBall (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    (baseInclMSph B W (n+1)).comp (capMapPairSph W n)
      = (capMapPairSph B n).comp (baseInclBall B W n) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-! ## Naturality of `stepDisc` -/

/-- Naturality of `stepDisc` in the base. -/
theorem stepDisc_natural (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (baseInclBall B W n) (DiscB W n) (DiscB B n) (fun _ h => h) ℤ n).hom
        (stepDisc B n τ)
      = stepDisc W n
          ((relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (fun _ h => h) ℤ n).hom τ) := by
  rw [stepDisc, stepDisc]
  rw [relCohMap_compA_apply (DiscB W n) (DiscB B n) (Sph B n) (baseInclBall B W n)
        (CleanA.discFullMap B n) (fun _ h => h) (CleanA.discFullMap_mem B n) (fun _ h => h) ℤ n τ]
  rw [relCohMap_compA_apply (DiscB W n) (Sph W n) (Sph B n) (CleanA.discFullMap W n)
        (baseIncl B W n) (CleanA.discFullMap_mem W n) (fun _ h => h) (fun _ h => h) ℤ n τ]
  have hm : relCohMap ((CleanA.discFullMap B n).comp (baseInclBall B W n)) (DiscB W n) (Sph B n)
        (fun _ h => h) ℤ n
      = relCohMap ((baseIncl B W n).comp (CleanA.discFullMap W n)) (DiscB W n) (Sph B n)
        (fun _ h => h) ℤ n :=
    relCohMap_congrA (DiscB W n) (Sph B n) (discFullMap_comp_baseInclBall B W n)
      (fun _ h => h) (fun _ h => h) ℤ n
  rw [hm]

/-! ## Naturality of `stepSph` -/

/-- Naturality of `stepSph` in the base. -/
theorem stepSph_natural (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (baseInclMSph B W (n+1)) (SphB W n) (SphB B n) (fun _ h => h) ℤ n).hom
        (stepSph B n τ)
      = stepSph W n
          ((relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (fun _ h => h) ℤ n).hom τ) := by
  have hinj : Function.Injective ((relCohMap (capMapPairSph W n) (DiscB W n) (SphB W n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom) :=
    (CleanA.capRelCohIso W n n).1
  apply hinj
  rw [relCohMap_compA_apply (DiscB W n) (SphB W n) (SphB B n) (capMapPairSph W n)
        (baseInclMSph B W (n+1)) (CleanA.capMapPairSph_mem_mLower n) (fun _ h => h)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n (stepSph B n τ)]
  rw [stepSph_spec W n
        ((relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (fun _ h => h) ℤ n).hom τ)]
  have hm2 : relCohMap ((baseInclMSph B W (n+1)).comp (capMapPairSph W n)) (DiscB W n) (SphB B n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n
      = relCohMap ((capMapPairSph B n).comp (baseInclBall B W n)) (DiscB W n) (SphB B n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n :=
    relCohMap_congrA (DiscB W n) (SphB B n) (capMapPairSph_comp_baseInclBall B W n)
      (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx)
      (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n
  rw [hm2]
  rw [← relCohMap_compA_apply (DiscB W n) (DiscB B n) (SphB B n) (baseInclBall B W n)
        (capMapPairSph B n) (fun _ h => h) (CleanA.capMapPairSph_mem_mLower n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n (stepSph B n τ)]
  rw [stepSph_spec B n τ]
  rw [stepDisc_natural B W n τ]

/-! ## Naturality of the inductive step -/

/-- The homeomorphism `prodSubsetHomeoA` commutes with the base inclusion. -/
theorem prodSubsetHomeoA_symm_comp_baseIncl (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    (baseInclMSph B W (n+1)).comp
        ((prodSubsetHomeoA W (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph W (n+1)), ↥W × MSph (n+1)))
      = ((prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph B (n+1)), B × MSph (n+1))).comp (baseInclSph B W (n+1)) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- **The inductive step is natural in the base.**  For `W ⊆ B` and any class `τ` of the pair
`(B × ℝⁿ, B × Sⁿ⁻¹)`, restricting `τ` to `W` and then performing the inductive step is the same as
performing the step over `B` and restricting the result.  (Uses the naturality of the connecting
homomorphism `Work.Thom.pairDeltaNatural` and the naturality of the pullback.) -/
theorem step_natural (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ)
    (τ : Work.Thom.RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Work.Thom.Sph B n)) :
    Work.Thom.step W n ((Work.Thom.relCohMap (Work.Thom.baseIncl B W n) (Work.Thom.Sph W n)
        (Work.Thom.Sph B n) (fun _ h => h) ℤ n).hom τ)
      = (Work.Thom.relCohMap (Work.Thom.baseIncl B W (n+1)) (Work.Thom.Sph W (n+1))
        (Work.Thom.Sph B (n+1)) (fun _ h => h) ℤ (n+1)).hom (Work.Thom.step B n τ) := by
  rw [step, step]
  rw [pairDeltaNatural_restrict (baseIncl B W (n+1)) (Sph W (n+1)) (Sph B (n+1))
        (fun _ h => h) n]
  refine congrArg (fun w => (pairδC (Sph W (n+1)) n).hom w) ?_
  rw [← stepSph_natural B W n τ]
  rw [relCohMap_relToAbs_apply (baseInclMSph B W (n+1)) (SphB W n) (SphB B n) (fun _ h => h) ℤ n
        (stepSph B n τ)]
  rw [CohMap_comp_apply ((prodSubsetHomeoA W (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
        C(↥(Sph W (n+1)), ↥W × MSph (n+1))) (baseInclMSph B W (n+1)) ℤ n
        ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))]
  rw [prodSubsetHomeoA_symm_comp_baseIncl B W n]
  rw [baseInclSph_eq_restrictMap B W (n+1)]
  rw [CohMap_comp_apply (restrictMap (baseIncl B W (n+1)) (Sph W (n+1)) (Sph B (n+1))
        (fun _ h => h)) ((prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
        C(↥(Sph B (n+1)), B × MSph (n+1))) ℤ n
        ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))]

end

end Work.Thom
