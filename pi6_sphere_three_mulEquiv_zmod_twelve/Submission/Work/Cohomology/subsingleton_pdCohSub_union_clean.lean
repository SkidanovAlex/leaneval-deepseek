import Mathlib
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.Relocate.HonestFMV

/-!
# Vanishing of `H^d` on a union of two open pieces (island-clean copy)

An island-clean copy of `Work.Cohomology.subsingleton_pdCohSub_union`, whose own module cannot be
imported together with this file's import island.  The helpers carry a `subUc_` prefix so that no
name can collide with the original development.
-/
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Functoriality of the pair map on relative cochains (local copies) -/

/-- The pair map only depends on the map of spaces, not on the proof that it carries `A₁` into
`A₂`. -/
theorem subUc_relComplexMap_congr {X₁ X₂ : TopCat} (A₁ : Set ↥X₁) (A₂ : Set ↥X₂) {f f' : X₁ ⟶ X₂}
    (hf : f = f') (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, f' x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f' h' := by
  subst hf
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The pair map of the identity is the identity. -/
theorem subUc_relComplexMap_id {X : TopCat} (A : Set ↥X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap ℤ A A (𝟙 X) h = 𝟙 (relComplex ℤ X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, relMapLM_coe, dualChainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- The pair map is functorial in the composition. -/
theorem subUc_relComplexMap_comp {X₀ X₁ X₂ : TopCat} (A₀ : Set ↥X₀) (A₁ : Set ↥X₁) (A₂ : Set ↥X₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) :
    relComplexMap ℤ A₀ A₂ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = relComplexMap ℤ A₁ A₂ g hg ≫ relComplexMap ℤ A₀ A₁ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relComplexMap_f, relComplexMap_f, relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply, relMapLM_coe,
    dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

/-- An isomorphism of pairs induces an isomorphism on relative cohomology. -/
theorem subUc_relComplexMap_iso_of_isIso_pairs {X₁ X₂ : TopCat} (A₁ : Set ↥X₁) (A₂ : Set ↥X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (g : X₂ ⟶ X₁) (hg : ∀ y ∈ A₂, g y ∈ A₁)
    (hfg : f ≫ g = 𝟙 X₁) (hgf : g ≫ f = 𝟙 X₂) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ f h) n) := by
  have h1 : relComplexMap ℤ A₁ A₂ f h ≫ relComplexMap ℤ A₂ A₁ g hg = 𝟙 (relComplex ℤ X₂ A₂) := by
    rw [← subUc_relComplexMap_comp A₂ A₁ A₂ g f hg h]
    refine (subUc_relComplexMap_congr A₂ A₂ hgf (fun x hx => h (g x) (hg x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact subUc_relComplexMap_id A₂ (fun x hx => by simpa using hx)
  have h2 : relComplexMap ℤ A₂ A₁ g hg ≫ relComplexMap ℤ A₁ A₂ f h = 𝟙 (relComplex ℤ X₁ A₁) := by
    rw [← subUc_relComplexMap_comp A₁ A₂ A₁ f g h hg]
    refine (subUc_relComplexMap_congr A₁ A₁ hfg (fun x hx => hg (f x) (h x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact subUc_relComplexMap_id A₁ (fun x hx => by simpa using hx)
  haveI : IsIso (relComplexMap ℤ A₁ A₂ f h) := ⟨relComplexMap ℤ A₂ A₁ g hg, h1, h2⟩
  exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n) _

/-- A `Subsingleton` module is a subsingleton after transporting along an isomorphism. -/
theorem subUc_subsingleton_of_iso {M N : ModuleCat ℤ} (e : M ≅ N) (h : Subsingleton M) :
    Subsingleton N := by
  obtain ⟨-, hs⟩ := ConcreteCategory.bijective_of_isIso e.hom
  exact ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    rw [Subsingleton.elim x y]⟩

/-! ## The piece `U ⊆ W` inside the subspace `W` -/

/-- The canonical homeomorphism `↥U ≅ (Subtype.val)⁻¹ U ⊆ ↥W` for `U ⊆ W`. -/
noncomputable def subUc_homeoIso {X : Type} [TopologicalSpace X] {W U : Set X} (hUW : U ⊆ W) :
    TopCat.of ↥U ≅ TopCat.of ↥((Subtype.val : ↥W → X) ⁻¹' U) :=
  HMV.subSubIso (X := TopCat.of X) (C := U) (B := W) hUW

/-- The underlying point of `subUc_homeoIso`. -/
theorem subUc_homeoIso_hom_coe {X : Type} [TopologicalSpace X] {W U : Set X} (hUW : U ⊆ W) (x : ↥U) :
    ((subUc_homeoIso hUW).hom x : X) = (x : X) := rfl

/-- The underlying point of the inverse of `subUc_homeoIso`. -/
theorem subUc_homeoIso_inv_coe {X : Type} [TopologicalSpace X] {W U : Set X} (hUW : U ⊆ W)
    (y : ↥((Subtype.val : ↥W → X) ⁻¹' U)) :
    ((subUc_homeoIso hUW).inv y : X) = (y : X) := rfl

/-- **Transport of vanishing of relative cohomology along a subset inclusion.**  If the relative
cohomology `H^k(U, U∩A)` vanishes when computed in `X`, then it vanishes for the piece
`(Subtype.val)⁻¹ U` of the subspace `W ⊇ U`. -/
theorem subUc_pdCohSub_transfer {X : Type} [TopologicalSpace X] (A : Set X) {W U : Set X}
    (hUW : U ⊆ W) (k : ℕ) (h : Subsingleton (pdCohSub (TopCat.of X) A U k)) :
    Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
      ((Subtype.val : ↥W → X) ⁻¹' U) k) := by
  let X₁ : TopCat := TopCat.of ↥U
  let X₂ : TopCat := TopCat.of ↥((Subtype.val : ↥W → X) ⁻¹' U)
  let A₁ : Set ↥X₁ := {y : ↥U | (y : X) ∈ A}
  let A₂ : Set ↥X₂ := {y : ↥X₂ | (y : X) ∈ A}
  have hm : ∀ x ∈ A₁, (subUc_homeoIso hUW).hom x ∈ A₂ := by
    intro x hx
    show ((subUc_homeoIso hUW).hom x : X) ∈ A
    rw [subUc_homeoIso_hom_coe hUW x]
    show (x : X) ∈ A
    exact hx
  have hmg : ∀ y ∈ A₂, (subUc_homeoIso hUW).inv y ∈ A₁ := by
    intro y hy
    show ((subUc_homeoIso hUW).inv y : X) ∈ A
    rw [subUc_homeoIso_inv_coe hUW y]
    show (y : X) ∈ A
    exact hy
  haveI : IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ A₁ A₂ (subUc_homeoIso hUW).hom hm) k) :=
    subUc_relComplexMap_iso_of_isIso_pairs A₁ A₂ (subUc_homeoIso hUW).hom hm
      (subUc_homeoIso hUW).inv hmg (subUc_homeoIso hUW).hom_inv_id (subUc_homeoIso hUW).inv_hom_id k
  exact subUc_subsingleton_of_iso
    (asIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ A₁ A₂ (subUc_homeoIso hUW).hom hm) k)).symm h

/-! ## The two-piece vanishing theorem -/

theorem subsingleton_pdCohSub_union_clean_aux {X : Type} [TopologicalSpace X] (A : Set X) {W U V : Set X}
    (hW : IsOpen W) (hU : IsOpen U) (hV : IsOpen V) (hUW : U ⊆ W) (hVW : V ⊆ W)
    (hcov : U ∪ V = W) (d : ℕ)
    (hU' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A U d))
    (hV' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A V d))
    (hUV : ∀ e, e + 1 = d → Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (U ∩ V) e)) :
    Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A W d) := by
  have hUWopen : IsOpen ((Subtype.val : ↥W → X) ⁻¹' U) := hU.preimage continuous_subtype_val
  have hVWopen : IsOpen ((Subtype.val : ↥W → X) ⁻¹' V) := hV.preimage continuous_subtype_val
  have hcovW : ((Subtype.val : ↥W → X) ⁻¹' U) ∪ ((Subtype.val : ↥W → X) ⁻¹' V) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h : (y : X) ∈ U ∪ V := by rw [hcov]; exact y.2
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hUt : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
      ((Subtype.val : ↥W → X) ⁻¹' U) d) := subUc_pdCohSub_transfer A hUW d hU'
  have hVt : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
      ((Subtype.val : ↥W → X) ⁻¹' V) d) := subUc_pdCohSub_transfer A hVW d hV'
  have hmain : Subsingleton (pdCoh (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A} d) := by
    rcases d with _ | n
    · -- degree `0`: the Mayer–Vietoris map is injective into a vanishing biproduct
      haveI : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) 0) := hUt
      haveI : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' V) 0) := hVt
      have hinj := Work.Thom.honestF_injective_zero (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
        ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) hUWopen hVWopen hcovW
      have hzU : IsZero (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) 0) := ModuleCat.isZero_of_subsingleton _
      have hzV : IsZero (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' V) 0) := ModuleCat.isZero_of_subsingleton _
      have hz : IsZero (pdCohBiprod (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) 0) :=
        (biprod_isZero_iff _ _).mpr ⟨hzU, hzV⟩
      haveI : Subsingleton (pdCohBiprod (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) 0) :=
        ModuleCat.subsingleton_of_isZero hz
      exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
    · -- degree `k+1`: the connecting map is surjective out of a vanishing overlap
      haveI : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) (n + 1)) := hUt
      haveI : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' V) (n + 1)) := hVt
      have hzU : IsZero (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) (n + 1)) := ModuleCat.isZero_of_subsingleton _
      have hzV : IsZero (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' V) (n + 1)) := ModuleCat.isZero_of_subsingleton _
      have hz : IsZero (pdCohBiprod (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) (n + 1)) :=
        (biprod_isZero_iff _ _).mpr ⟨hzU, hzV⟩
      have hF0 : honestF (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) (n + 1) = 0 :=
        IsZero.eq_zero_of_tgt hz _
      have hex := honest_exact₁ (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
        ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) hUWopen hVWopen hcovW n
      have hker : LinearMap.range (ModuleCat.Hom.hom
            (honestDelta (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
              ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V)
              hUWopen hVWopen hcovW n)) = ⊤ := by
        have h := ShortComplex.Exact.moduleCat_range_eq_ker hex
        change LinearMap.range (ModuleCat.Hom.hom
            (honestDelta (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
              ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V)
              hUWopen hVWopen hcovW n))
          = LinearMap.ker (ModuleCat.Hom.hom
            (honestF (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
              ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V) (n + 1))) at h
        rw [hF0, ModuleCat.hom_zero, LinearMap.ker_zero] at h
        exact h
      have hsurj : Function.Surjective (ModuleCat.Hom.hom
          (honestDelta (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
            ((Subtype.val : ↥W → X) ⁻¹' U) ((Subtype.val : ↥W → X) ⁻¹' V)
            hUWopen hVWopen hcovW n)) := LinearMap.range_eq_top.mp hker
      have hOV : Subsingleton (pdCohSub (TopCat.of ↥W) {y : ↥W | (y : X) ∈ A}
          (((Subtype.val : ↥W → X) ⁻¹' U) ∩ ((Subtype.val : ↥W → X) ⁻¹' V)) n) :=
        subUc_pdCohSub_transfer A (Set.inter_subset_left.trans hUW) n (hUV n rfl)
      haveI := hOV
      exact ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hsurj a
        obtain ⟨y, rfl⟩ := hsurj b
        rw [Subsingleton.elim x y]⟩
  exact hmain

/-- **Vanishing of `H^d` on a union of two open pieces** — an island-clean copy of the existing
result `Work.Cohomology.subsingleton_pdCohSub_union`, whose own module cannot be imported together
with this file's import island.

If an open set `W` is the union of two open sets `U, V ⊆ W`, and the relative cohomologies
`H^d(U, U∩A)`, `H^d(V, V∩A)` and `H^{d-1}(U∩V, U∩V∩A)` all vanish, then `H^d(W, W∩A)` vanishes.

The argument is the relative Mayer–Vietoris long exact sequence of the pair `(W, W∩A)` for the open
cover `W = U ∪ V`: in degree `d ≥ 1`, the map `H^d(W,W∩A) → H^d(U,U∩A) ⊞ H^d(V,V∩A)` is zero (its
target vanishes) and its kernel is the image of the connecting map out of
`H^{d-1}(U∩V, U∩V∩A)`, which vanishes; in degree `0` there is no incoming connecting map, and one
uses injectivity of the Mayer–Vietoris comparison map in degree zero instead.

Please give your helper lemmas fresh names so that they cannot collide with the existing ones. -/
theorem subsingleton_pdCohSub_union_clean {X : Type} [TopologicalSpace X] (A : Set X) {W U V : Set X}
    (hW : IsOpen W) (hU : IsOpen U) (hV : IsOpen V) (hUW : U ⊆ W) (hVW : V ⊆ W)
    (hcov : U ∪ V = W) (d : ℕ)
    (hU' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A U d))
    (hV' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A V d))
    (hUV : ∀ e, e + 1 = d → Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (U ∩ V) e)) :
    Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A W d) := by
  exact subsingleton_pdCohSub_union_clean_aux A hW hU hV hUW hVW hcov d hU' hV' hUV

end

end Work.Cohomology
