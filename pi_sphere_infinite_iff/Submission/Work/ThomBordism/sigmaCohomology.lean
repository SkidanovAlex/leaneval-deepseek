import Mathlib
import Submission.Work.ThomBordism.sigmaChains
import Submission.Work.Bordism.pullbackRat_coprod_bijective
import Submission.Work.Cohomology.hmv_naturality

/-!
# The cohomological splitting of a `σ`-type of spaces

The chain-level splitting of `Work.ThomBordism.chainSigmaRetract` transposes to a splitting of the
cohomology: for a finite family of spaces `α : ι → TopCat`, the canonical map

`Φ : Hᵏ(Σ i, α i ; ℚ) ⟶ ∏ i, Hᵏ(α i ; ℚ),  x ↦ (i ↦ (incl i)* x)`

is bijective, with explicit inverse `x ↦ ∑ i (pᵢ)* xᵢ` built from the transposed retractions.
This is `Work.ThomBordism.pullbackRat_sigma_bijective`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory Limits Topology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

variable {ι : Type} [Fintype ι] (α : ι → TopCat.{0})

/-! ## The cochain complexes of the pieces -/

/-- The cochain complex of the `i`-th piece, as the dual of its chain complex. -/
abbrev pieceCochain (i : ι) : CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  Work.Cohomology.dualComplex ℤ (pieceChains α i)

/-- The cochain complex of the whole `σ`-type. -/
abbrev sigmaCochain : CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  Work.Cohomology.dualComplex ℤ (sigmaChains α)

/-- The `k`-th cohomology of a piece, rationalised. -/
abbrev ratPiece (k : ℕ) (i : ι) : Type := ℚ ⊗[ℤ] (pieceCochain α i).homology k

/-- The `k`-th cohomology of the whole `σ`-type, rationalised. -/
abbrev ratSigma (k : ℕ) : Type := ℚ ⊗[ℤ] (sigmaCochain α).homology k

/-! ## Additivity of the dual, of homology and of base change over finite sums -/

/-- The dual of a finite sum of chain maps is the sum of the duals. -/
lemma dualComplexMap_sum_aux {R : Type} [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    {κ : Type} (s : Finset κ) (f : κ → (C ⟶ D)) :
    Work.Cohomology.dualComplexMap R C D (∑ i ∈ s, f i)
      = ∑ i ∈ s, Work.Cohomology.dualComplexMap R C D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Work.Bordism.dualComplexMap_zero']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Work.Bordism.dualComplexMap_add', ih]

/-- The dual of a finite sum of chain maps is the sum of the duals. -/
lemma dualComplexMap_sum {R : Type} [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    {κ : Type} [Fintype κ] (f : κ → (C ⟶ D)) :
    Work.Cohomology.dualComplexMap R C D (∑ i, f i)
      = ∑ i, Work.Cohomology.dualComplexMap R C D (f i) := by
  simpa using dualComplexMap_sum_aux (s := Finset.univ) f

/-- The homology functor is additive: it preserves finite sums of cochain maps (for any
complex shape). -/
lemma homologyMap_sum_aux {c : ComplexShape ℕ} {C D : HomologicalComplex (ModuleCat ℤ) c}
    {κ : Type} (s : Finset κ) (f : κ → (C ⟶ D)) (k : ℕ) :
    HomologicalComplex.homologyMap (∑ i ∈ s, f i) k
      = ∑ i ∈ s, HomologicalComplex.homologyMap (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, HomologicalComplex.homologyMap_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, HomologicalComplex.homologyMap_add, ih]

/-- The homology functor is additive: it preserves finite sums of cochain maps. -/
lemma homologyMap_sum {c : ComplexShape ℕ} {C D : HomologicalComplex (ModuleCat ℤ) c}
    {κ : Type} [Fintype κ] (f : κ → (C ⟶ D)) (k : ℕ) :
    HomologicalComplex.homologyMap (∑ i, f i) k
      = ∑ i, HomologicalComplex.homologyMap (f i) k := by
  simpa using homologyMap_sum_aux (s := Finset.univ) f k

/-- Base change to `ℚ` commutes with finite sums of `ℤ`-linear maps. -/
lemma baseChange_sum_aux {κ : Type} {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (s : Finset κ) (f : κ → (M →ₗ[ℤ] N)) :
    (∑ i ∈ s, f i).baseChange ℚ = ∑ i ∈ s, (f i).baseChange ℚ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, LinearMap.baseChange_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.baseChange_add, ih]

/-- Base change to `ℚ` commutes with finite sums of `ℤ`-linear maps. -/
lemma baseChange_sum {κ : Type} [Fintype κ] {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : κ → (M →ₗ[ℤ] N)) :
    (∑ i, f i).baseChange ℚ = ∑ i, (f i).baseChange ℚ := by
  simpa using baseChange_sum_aux (s := Finset.univ) f

/-- The components of a finite sum of morphisms of `ℤ`-modules. -/
lemma moduleCatHom_sum_aux {κ : Type} {M N : ModuleCat ℤ} (s : Finset κ) (f : κ → (M ⟶ N)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ModuleCat.hom_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModuleCat.hom_add, ih]

/-- The components of a finite sum of morphisms of `ℤ`-modules. -/
lemma moduleCatHom_sum {κ : Type} [Fintype κ] {M N : ModuleCat ℤ} (f : κ → (M ⟶ N)) :
    (∑ i, f i).hom = ∑ i, (f i).hom := by
  simpa using moduleCatHom_sum_aux (s := Finset.univ) f

/-- Evaluating a finite sum of `ℚ`-linear maps: `(∑ j, h j) x = ∑ j, h j x`. -/
lemma sum_apply_univ {κ : Type} [Fintype κ] {M N : Type} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] (h : κ → (M →ₗ[ℚ] N)) (x : M) :
    (∑ j, h j) x = ∑ j, h j x :=
  map_sum (G := (M →ₗ[ℚ] N) →+ N)
    { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl } h Finset.univ

/-! ## The cochain maps induced by the inclusions and the retractions -/

/-- The cochain pullback along the inclusion of the `i`-th piece. -/
noncomputable def sigmaPullbackCochain (i : ι) : sigmaCochain α ⟶ pieceCochain α i :=
  Work.Cohomology.dualComplexMap ℤ (pieceChains α i) (sigmaChains α)
    (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))

/-- The cochain map induced by the `i`-th retraction (it goes the other way in cohomology). -/
noncomputable def sigmaRetractCochain (i : ι) : pieceCochain α i ⟶ sigmaCochain α :=
  Work.Cohomology.dualComplexMap ℤ (sigmaChains α) (pieceChains α i)
    (chainSigmaRetract α i)

/-- The composite of the cochain maps induced by an inclusion and a retraction, displayed via the
dual of a single chain map. -/
lemma retractCochain_comp_pullbackCochain_eq (i j : ι) :
    sigmaRetractCochain α j ≫ sigmaPullbackCochain α i
      = Work.Cohomology.dualComplexMap ℤ (pieceChains α i) (pieceChains α j)
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
            ≫ chainSigmaRetract α j) :=
  (Work.Cohomology.dualComplexMap_comp (R := ℤ) (C := pieceChains α i)
    (D := sigmaChains α) (E := pieceChains α j)
    (f := Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
    (g := chainSigmaRetract α j)).symm

/-- The transposed retraction is a section of the transposed inclusion. -/
theorem retractCochain_comp_pullbackCochain (i : ι) :
    sigmaRetractCochain α i ≫ sigmaPullbackCochain α i = 𝟙 (pieceCochain α i) := by
  rw [retractCochain_comp_pullbackCochain_eq, chainMap_sigmaι_comp_retract,
    Work.Cohomology.dualComplexMap_id]

/-- The transposed retraction kills the other inclusions. -/
theorem retractCochain_comp_pullbackCochain_ne {i j : ι} (h : i ≠ j) :
    sigmaRetractCochain α j ≫ sigmaPullbackCochain α i = 0 := by
  have hz : Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
      ≫ chainSigmaRetract α j = 0 := chainMap_sigmaι_comp_retract_ne α h
  calc sigmaRetractCochain α j ≫ sigmaPullbackCochain α i
      = Work.Cohomology.dualComplexMap ℤ (pieceChains α i) (pieceChains α j)
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
            ≫ chainSigmaRetract α j) := retractCochain_comp_pullbackCochain_eq α i j
    _ = Work.Cohomology.dualComplexMap ℤ (pieceChains α i) (pieceChains α j) 0 :=
        congrArg (fun z => Work.Cohomology.dualComplexMap ℤ (pieceChains α i)
          (pieceChains α j) z) hz
    _ = 0 := Work.Bordism.dualComplexMap_zero' _ _

/-- The transposed retractions and inclusions are complementary. -/
theorem sum_pullbackCochain_comp_retractCochain :
    ∑ i, sigmaPullbackCochain α i ≫ sigmaRetractCochain α i = 𝟙 (sigmaCochain α) := by
  have hterm : ∀ i, sigmaPullbackCochain α i ≫ sigmaRetractCochain α i
      = Work.Cohomology.dualComplexMap ℤ (sigmaChains α) (sigmaChains α)
          (chainSigmaRetract α i
            ≫ Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)) := by
    intro i
    rw [sigmaPullbackCochain, sigmaRetractCochain, Work.Cohomology.dualComplexMap_comp]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [show (∑ i, Work.Cohomology.dualComplexMap ℤ (sigmaChains α) (sigmaChains α)
        (chainSigmaRetract α i
          ≫ Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)))
      = Work.Cohomology.dualComplexMap ℤ (sigmaChains α) (sigmaChains α)
          (∑ i, (chainSigmaRetract α i
            ≫ Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)))
      from (dualComplexMap_sum (fun i => chainSigmaRetract α i
            ≫ Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))).symm]
  rw [sum_retract_comp_chainMap, Work.Cohomology.dualComplexMap_id]

/-! ## The splitting on cohomology -/

/-- The pullback on the `k`-th cohomology along the inclusion of the `i`-th piece. -/
noncomputable def pullbackLM (k : ℕ) (i : ι) :
    (sigmaCochain α).homology k →ₗ[ℤ] (pieceCochain α i).homology k :=
  (HomologicalComplex.homologyMap (sigmaPullbackCochain α i) k).hom

/-- The pushforward on the `k`-th cohomology along the `i`-th retraction. -/
noncomputable def retractLM (k : ℕ) (i : ι) :
    (pieceCochain α i).homology k →ₗ[ℤ] (sigmaCochain α).homology k :=
  (HomologicalComplex.homologyMap (sigmaRetractCochain α i) k).hom

/-- The transposed retraction is a section of the transposed inclusion, on cohomology. -/
theorem pullbackLM_comp_retractLM (k : ℕ) (i : ι) :
    (pullbackLM α k i).comp (retractLM α k i) = LinearMap.id := by
  show (HomologicalComplex.homologyMap (sigmaPullbackCochain α i) k).hom.comp
      (HomologicalComplex.homologyMap (sigmaRetractCochain α i) k).hom = LinearMap.id
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    retractCochain_comp_pullbackCochain, HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

/-- On cohomology, the transposed retraction of one piece kills the transposed inclusion of
another. -/
theorem pullbackLM_comp_retractLM_ne (k : ℕ) {i j : ι} (h : j ≠ i) :
    (pullbackLM α k i).comp (retractLM α k j) = 0 := by
  have h0 : sigmaRetractCochain α j ≫ sigmaPullbackCochain α i = 0 :=
    retractCochain_comp_pullbackCochain_ne α (Ne.symm h)
  show (HomologicalComplex.homologyMap (sigmaPullbackCochain α i) k).hom.comp
      (HomologicalComplex.homologyMap (sigmaRetractCochain α j) k).hom = 0
  calc (HomologicalComplex.homologyMap (sigmaPullbackCochain α i) k).hom.comp
        (HomologicalComplex.homologyMap (sigmaRetractCochain α j) k).hom
      = (HomologicalComplex.homologyMap
          (sigmaRetractCochain α j ≫ sigmaPullbackCochain α i) k).hom := by
        rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    _ = (HomologicalComplex.homologyMap
          (0 : pieceCochain α j ⟶ pieceCochain α i) k).hom := by rw [h0]
    _ = 0 := by rw [HomologicalComplex.homologyMap_zero, ModuleCat.hom_zero]

/-- **The transposed retractions and inclusions are complementary on cohomology**: their sum is the
identity. -/
theorem sum_retractLM_comp_pullbackLM (k : ℕ) :
    ∑ i, (retractLM α k i).comp (pullbackLM α k i) = LinearMap.id := by
  have hterm : ∀ i, (retractLM α k i).comp (pullbackLM α k i)
      = (HomologicalComplex.homologyMap
          (sigmaPullbackCochain α i ≫ sigmaRetractCochain α i) k).hom := by
    intro i
    show (HomologicalComplex.homologyMap (sigmaRetractCochain α i) k).hom.comp
        (HomologicalComplex.homologyMap (sigmaPullbackCochain α i) k).hom = _
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [← moduleCatHom_sum,
    show (∑ i, HomologicalComplex.homologyMap
        (sigmaPullbackCochain α i ≫ sigmaRetractCochain α i) k)
      = HomologicalComplex.homologyMap
          (∑ i, (sigmaPullbackCochain α i ≫ sigmaRetractCochain α i)) k
      from (homologyMap_sum (C := sigmaCochain α) (D := sigmaCochain α)
        (fun i => sigmaPullbackCochain α i ≫ sigmaRetractCochain α i) k).symm,
    sum_pullbackCochain_comp_retractCochain, HomologicalComplex.homologyMap_id,
    ModuleCat.hom_id]

/-! ## The comparison with `pullbackRat` -/

/-- The rationalised pullback is the base change of `pullbackLM`. -/
lemma pullbackRat_sigmaι_eq (k : ℕ) (i : ι) :
    Work.Bordism.pullbackRat k (TopCat.sigmaι α i) = (pullbackLM α k i).baseChange ℚ := by
  rw [Work.Bordism.pullbackRat, pullbackLM, sigmaPullbackCochain,
    Work.Cohomology.singularCohomologyMap, Work.Cohomology.dualChainMap_eq_dualComplexMap]

/-! ## The splitting of the rationalised cohomology -/

/-- **The rationalised cohomology of a `σ`-type splits off its pieces**: the product of the
pullbacks along the inclusions is bijective. -/
theorem pullbackRat_sigma_bijective (k : ℕ) :
    Function.Bijective (LinearMap.pi (fun i => Work.Bordism.pullbackRat k (TopCat.sigmaι α i))) := by
  change Function.Bijective (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ))
  let Ψ : (∀ i, ℚ ⊗[ℤ] (pieceCochain α i).homology k) →ₗ[ℚ]
      (ℚ ⊗[ℤ] (sigmaCochain α).homology k) :=
    ∑ i, ((retractLM α k i).baseChange ℚ).comp
      (LinearMap.proj (φ := fun i => ℚ ⊗[ℤ] (pieceCochain α i).homology k) i)
  have h1 : (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ)).comp Ψ = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    funext i
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.pi_apply]
    have hΨv : Ψ v = ∑ j, (retractLM α k j).baseChange ℚ (v j) := by
      change (∑ j, ((retractLM α k j).baseChange ℚ).comp
          (LinearMap.proj (φ := fun j => ℚ ⊗[ℤ] (pieceCochain α j).homology k) j)) v = _
      rw [sum_apply_univ]
      exact Finset.sum_congr rfl fun j _ => by
        rw [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hΨv, map_sum]
    refine (Finset.sum_eq_single i ?_ ?_).trans ?_
    · intro j _ hj
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        pullbackLM_comp_retractLM_ne α k hj, LinearMap.baseChange_zero, LinearMap.zero_apply]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
    · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, pullbackLM_comp_retractLM,
        LinearMap.baseChange_id, LinearMap.id_apply]
  have h2 : Ψ.comp (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ)) = LinearMap.id := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    have hΨw : Ψ (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ) w)
        = (∑ j, ((retractLM α k j).comp (pullbackLM α k j)).baseChange ℚ) w := by
      change (∑ j, ((retractLM α k j).baseChange ℚ).comp
          (LinearMap.proj (φ := fun j => ℚ ⊗[ℤ] (pieceCochain α j).homology k) j))
          (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ) w) = _
      rw [sum_apply_univ]
      rw [show (∑ j, ((retractLM α k j).comp (pullbackLM α k j)).baseChange ℚ) w
          = ∑ j, ((retractLM α k j).comp (pullbackLM α k j)).baseChange ℚ w
          from sum_apply_univ _ w]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply, ← LinearMap.comp_apply,
        ← LinearMap.baseChange_comp]
    have hsum_base : (∑ j, ((retractLM α k j).comp (pullbackLM α k j)).baseChange ℚ)
        = (∑ j, (retractLM α k j).comp (pullbackLM α k j)).baseChange ℚ :=
      (baseChange_sum (fun j => (retractLM α k j).comp (pullbackLM α k j))).symm
    rw [hΨw, hsum_base, sum_retractLM_comp_pullbackLM, LinearMap.baseChange_id,
      LinearMap.id_apply]
  constructor
  · intro x y hxy
    have hx : x = Ψ (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ) x) := by
      have := congrArg (fun (f : (ℚ ⊗[ℤ] (sigmaCochain α).homology k) →ₗ[ℚ]
        (ℚ ⊗[ℤ] (sigmaCochain α).homology k)) => f x) h2
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this.symm
    have hy : y = Ψ (LinearMap.pi (fun i => (pullbackLM α k i).baseChange ℚ) y) := by
      have := congrArg (fun (f : (ℚ ⊗[ℤ] (sigmaCochain α).homology k) →ₗ[ℚ]
        (ℚ ⊗[ℤ] (sigmaCochain α).homology k)) => f y) h2
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this.symm
    rw [hx, hy, hxy]
  · intro v
    refine ⟨Ψ v, ?_⟩
    have := congrArg (fun (f : (∀ i, ℚ ⊗[ℤ] (pieceCochain α i).homology k) →ₗ[ℚ]
      (∀ i, ℚ ⊗[ℤ] (pieceCochain α i).homology k)) => f v) h1
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this

end

end Work.ThomBordism
