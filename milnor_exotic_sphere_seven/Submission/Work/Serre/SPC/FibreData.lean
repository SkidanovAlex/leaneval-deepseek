import Mathlib
import Submission.Work.Serre.SPC.B1Setup
import Submission.Work.Cohomology.localHomology
import Submission.Work.Serre.Assembly.pullbackFst_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Fibre connectivity data of a pullback, and its transport along paths

Two elementary transfers used by the `b = 1` construction:

* `Work.Serre.SPC.fibreData_pullback_base`: the connectivity data of the fibre of
  `pullbackFst g p` over `γ₀` follows from the data of the fibre of `p` over `g γ₀` (the two fibres
  are homeomorphic);
* `Work.Serre.SPC.fibreData_all`: the data is constant over a path-connected base
  (this is `Work.Serre.SPC.FibreTransport`, applied along a path).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-! ## Transfer of the two conditions along a homeomorphism -/

/-- The integral homology of a space vanishes in degree `j` iff it does for a homeomorphic space. -/
theorem isZero_homology_of_homeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (j : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology j) ↔
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of B)).homology j) := by
  let f : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom (⟨e.toFun, e.continuous_toFun⟩ : C(A, B))
  have hf : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of A)
      (TopCat.of B) f) j) :=
    Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of A)
      (Y := TopCat.of B) e.toHomotopyEquiv j
  let φ := HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of A)
    (TopCat.of B) f) j
  haveI := hf
  constructor
  · intro h
    haveI : Subsingleton ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology j) :=
      ModuleCat.isZero_iff_subsingleton.mp h
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
    have hsurj : Function.Surjective φ.hom :=
      (ModuleCat.epi_iff_surjective _).mp (IsIso.epi_of_iso _)
    obtain ⟨x', rfl⟩ := hsurj x
    obtain ⟨y', rfl⟩ := hsurj y
    rw [Subsingleton.elim x' y']
  · intro h
    haveI : Subsingleton ((Work.Cohomology.singularChains ℤ (TopCat.of B)).homology j) :=
      ModuleCat.isZero_iff_subsingleton.mp h
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
    have hinj : Function.Injective φ.hom :=
      (ModuleCat.mono_iff_injective _).mp (IsIso.mono_of_iso _)
    exact hinj (Subsingleton.elim _ _)

/-- The degree-`0` augmentation is an isomorphism on one side of a homeomorphism. -/
theorem isIso_augmentation_of_homeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) :
    IsIso (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ)) ↔
      IsIso (TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℤ ℤ)) := by
  let f : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom (⟨e.toFun, e.continuous_toFun⟩ : C(A, B))
  have hf : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of A)
      (TopCat.of B) f) 0) :=
    Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of A)
      (Y := TopCat.of B) e.toHomotopyEquiv 0
  have hnat := Work.Cohomology.epsilonNaturality (TopCat.of A) (TopCat.of B) f
  let φ := HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of A)
    (TopCat.of B) f) 0
  let εA := TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ)
  let εB := TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℤ ℤ)
  have hnat' : φ ≫ TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℤ ℤ)
      = TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ) := hnat
  constructor
  · intro hA
    haveI hc : IsIso (φ ≫ εB) := by rw [hnat']; exact hA
    exact IsIso.of_isIso_comp_left φ εB
  · intro hB
    have hc : IsIso (φ ≫ TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℤ ℤ)) :=
      IsIso.comp_isIso' hf hB
    exact hnat' ▸ hc

/-! ## The fibre of the first projection of a pullback -/

/-- The fibre of `Work.StemsB.pullbackFst g p` over `γ₀` is homeomorphic to the fibre of `p` over
`g γ₀`. -/
def fibrePullbackHomeo {B E Γ : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] (p : C(E, B)) (g : C(Γ, B)) (γ₀ : Γ) :
    Work.StemsB.fibre (Work.StemsB.pullbackFst g p) γ₀ ≃ₜ Work.StemsB.fibre p (g γ₀) where
  toFun e := ⟨e.1.1.2, by
    have h1 : g e.1.1.1 = p e.1.1.2 := e.1.2
    have h2 : e.1.1.1 = γ₀ := e.2
    rw [← h1, h2]⟩
  invFun f := ⟨⟨(γ₀, f.1), f.2.symm⟩, rfl⟩
  left_inv e := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    exact Prod.ext e.2.symm rfl
  right_inv f := by
    refine Subtype.ext ?_
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.prodMk continuous_subtype_val

/-! ## The two conditions at the base point of the pullback -/

/-- **The fibre data of a pullback at the base point**, from the data of the fibre of `p` over the
image point. -/
theorem fibreData_pullback_base {B E Γ : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] (p : C(E, B)) (g : C(Γ, B)) (γ₀ : Γ) (φ : ℕ)
    (hfib : ∀ j : ℕ, 0 < j → j < φ → IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (g γ₀)))).homology j))
    (h0 : IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre p (g γ₀)))
      (ModuleCat.of ℤ ℤ))) :
    (∀ j : ℕ, 0 < j → j < φ → IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) γ₀))).homology j)) ∧
      IsIso (TopCat.singularHomology₀ε
        (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) γ₀)) (ModuleCat.of ℤ ℤ)) :=
  ⟨fun j hj1 hj2 => (isZero_homology_of_homeo (fibrePullbackHomeo p g γ₀) j).mpr (hfib j hj1 hj2),
    (isIso_augmentation_of_homeo (fibrePullbackHomeo p g γ₀)).mpr h0⟩

/-! ## The two conditions over a path-connected base -/

/-- **The fibre data of a Serre fibration is constant over a path-connected base** (an instance of
`Work.Serre.SPC.FibreTransport`). -/
theorem fibreData_all {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q) (htr : FibreTransport) (φ : ℕ) (x₀ : Γ)
    [PathConnectedSpace Γ]
    (hdata : (∀ j : ℕ, 0 < j → j < φ → IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q x₀))).homology j)) ∧
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q x₀))
        (ModuleCat.of ℤ ℤ))) :
    ∀ y : Γ, (∀ j : ℕ, 0 < j → j < φ → IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q y))).homology j)) ∧
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ)) := by
  intro y
  obtain ⟨γ⟩ := PathConnectedSpace.joined x₀ y
  exact htr q hq φ x₀ y γ.toContinuousMap γ.source γ.target hdata.1 hdata.2

end

end Work.Serre.SPC
