import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Mayer--Vietoris ladder: the five lemma for the first term

The classical proof of the Thom isomorphism for a general (non-trivial) oriented real vector bundle
proceeds by Mayer--Vietoris: for a two-piece open cover of the base one compares the Mayer--Vietoris
long exact sequence of the base with that of the Thom pair, and the five lemma gives the Thom
isomorphism in the middle.

This file contains the **pure homological-algebra** rung of that argument, in the form needed by the
Thom chapter: given a morphism `φ : S₁ ⟶ S₂` of short exact sequences of cochain complexes of
`ℤ`-modules, if the maps induced on the *two outer* terms (`φ.τ₂` and `φ.τ₃`) are quasi-isomorphisms
then so is the map induced on the *first* term (`φ.τ₁`).

Mathlib has the corresponding statement for the *third* term
(`HomologicalComplex.HomologySequence.quasiIso_τ₃`); the version for the first term is what the
Mayer--Vietoris argument for the Thom isomorphism needs, because it is the two *pieces* over which
the bundle is trivial (the second and third terms of the Mayer--Vietoris short complex) whose Thom
maps are known to be isomorphisms, while the conclusion is about the base (the first term).

## Main results

* `Work.Thom.mono_homologyMap_τ₁`, `Work.Thom.epi_homologyMap_τ₁` — the two halves of the five
  lemma, degreewise;
* `Work.Thom.quasiIso_τ₁` — the five lemma in quasi-isomorphism form.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

noncomputable section

/-- The shape relation `k - 1 ~ k` of the complex shape `ComplexShape.up ℕ`, for `k ≥ 1`. -/
theorem upRel_pred (k : ℕ) (hk : k ≠ 0) : (ComplexShape.up ℕ).Rel (k - 1) k :=
  ComplexShape.up_mk (k - 1) k (by omega)

/-- **The first differential of a short exact sequence of cochain complexes is injective on
homology in degree `0`.**  (In degree `0` the group `H₀` is the *kernel* of the first differential,
so an injective map of complexes induces an injective map.) -/
theorem mono_homologyMap_f_zero {K L : CochainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) [Mono f] :
    Mono (HomologicalComplex.homologyMap f 0) := by
  haveI : Mono (f.f 0) :=
    Functor.map_mono (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) 0) f
  exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel f 0 (fun i hi => by
    simp [ComplexShape.up] at hi)

section Five

variable {S₁ S₂ : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)}

/-! ## The commuting squares of the induced maps -/

/-- The first square, at the level of morphisms of `ℤ`-modules. -/
theorem sq₁_mor (φ : S₁ ⟶ S₂) (k : ℕ) :
    HomologicalComplex.homologyMap S₁.f k ≫ HomologicalComplex.homologyMap φ.τ₂ k
      = HomologicalComplex.homologyMap φ.τ₁ k ≫ HomologicalComplex.homologyMap S₂.f k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, φ.comm₁₂]

/-- The second square, at the level of morphisms of `ℤ`-modules. -/
theorem sq₂_mor (φ : S₁ ⟶ S₂) (k : ℕ) :
    HomologicalComplex.homologyMap S₁.g k ≫ HomologicalComplex.homologyMap φ.τ₃ k
      = HomologicalComplex.homologyMap φ.τ₂ k ≫ HomologicalComplex.homologyMap S₂.g k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, φ.comm₂₃]

/-- The first square, evaluated on an element. -/
theorem sq₁_apply (φ : S₁ ⟶ S₂) (k : ℕ) (x : (S₁.X₁).homology k) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₂ k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.f k) x)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) x) := by
  have h := congrArg (fun (g : (S₁.X₁).homology k ⟶ (S₂.X₂).homology k) =>
    ModuleCat.Hom.hom g x) (sq₁_mor φ k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The second square, evaluated on an element. -/
theorem sq₂_apply (φ : S₁ ⟶ S₂) (k : ℕ) (x : (S₁.X₂).homology k) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.g k) x)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.g k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₂ k) x) := by
  have h := congrArg (fun (g : (S₁.X₂).homology k ⟶ (S₂.X₃).homology k) =>
    ModuleCat.Hom.hom g x) (sq₂_mor φ k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Naturality of the connecting homomorphism, evaluated on an element. -/
theorem delta_naturality_apply (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (k : ℕ) (hk : k ≠ 0) (w : (S₁.X₃).homology (k - 1)) :
    ModuleCat.Hom.hom (hS₂.δ (k - 1) k (upRel_pred k hk))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ (k - 1)) w)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k)
        (ModuleCat.Hom.hom (hS₁.δ (k - 1) k (upRel_pred k hk)) w) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ (k - 1) k
    (upRel_pred k hk)
  have h' := congrArg (fun (g : (S₁.X₃).homology (k - 1) ⟶ (S₂.X₁).homology k) =>
    ModuleCat.Hom.hom g w) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'.symm

/-! ## The five lemma -/

/-- **The injectivity half of the five lemma for the first term.** -/
theorem mono_homologyMap_τ₁ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (k : ℕ)
    (h₂ : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₂ i))
    (h₃ : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₃ i)) :
    Mono (HomologicalComplex.homologyMap φ.τ₁ k) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have hxy' : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) x
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) y := hxy
  have hz : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) (x - y) = 0 := by
    rw [map_sub, hxy', sub_self]
  have hβinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₂ k)) :=
    (ModuleCat.mono_iff_injective _).mp ((isIso_iff_mono_and_epi _).mp (h₂ k)).1
  have ha0 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.f k) (x - y) = 0 := by
    apply hβinj
    rw [sq₁_apply φ k (x - y), hz]
    simp only [map_zero]
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  by_cases hk : k = 0
  · subst hk
    haveI : Mono S₁.f := hS₁.mono_f
    haveI : Mono (HomologicalComplex.homologyMap S₁.f 0) := mono_homologyMap_f_zero S₁.f
    have hinj : Function.Injective
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.f 0)) :=
      (ModuleCat.mono_iff_injective _).mp this
    exact hinj (by rw [ha0, map_zero])
  · have hker : x - y ∈ (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap S₁.f k)).ker := LinearMap.mem_ker.mpr ha0
    rw [← ShortComplex.Exact.moduleCat_range_eq_ker
      (hS₁.homology_exact₁ (k - 1) k (upRel_pred k hk))] at hker
    obtain ⟨w, hw⟩ := hker
    have hδ' : ModuleCat.Hom.hom (hS₂.δ (k - 1) k (upRel_pred k hk))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ (k - 1)) w) = 0 := by
      rw [delta_naturality_apply φ hS₁ hS₂ k hk w, hw, hz]
    have hker₂ : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ (k - 1)) w ∈
        (ModuleCat.Hom.hom (hS₂.δ (k - 1) k (upRel_pred k hk))).ker :=
      LinearMap.mem_ker.mpr hδ'
    rw [← ShortComplex.Exact.moduleCat_range_eq_ker
      (hS₂.homology_exact₃ (k - 1) k (upRel_pred k hk))] at hker₂
    obtain ⟨v, hv⟩ := hker₂
    have hβsurj : Function.Surjective
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₂ (k - 1))) :=
      (ModuleCat.epi_iff_surjective _).mp ((isIso_iff_mono_and_epi _).mp (h₂ (k - 1))).2
    obtain ⟨u, hu⟩ := hβsurj v
    have hγinj : Function.Injective
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ (k - 1))) :=
      (ModuleCat.mono_iff_injective _).mp ((isIso_iff_mono_and_epi _).mp (h₃ (k - 1))).1
    have hwu : w = ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.g (k - 1)) u := by
      apply hγinj
      rw [sq₂_apply φ (k - 1) u, hu, hv]
    have h0 : ModuleCat.Hom.hom (hS₁.δ (k - 1) k (upRel_pred k hk))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.g (k - 1)) u) = 0 := by
      have h := congrArg (fun (g : (S₁.X₂).homology (k - 1) ⟶ (S₁.X₁).homology k) =>
        ModuleCat.Hom.hom g u) (hS₁.comp_δ (k - 1) k (upRel_pred k hk))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply]
        at h
      exact h
    rw [hwu, h0] at hw
    exact hw.symm

/-- **The surjectivity half of the five lemma for the first term.** -/
theorem epi_homologyMap_τ₁ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (k : ℕ)
    (h₂ : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₂ i))
    (h₃ : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₃ i)) :
    Epi (HomologicalComplex.homologyMap φ.τ₁ k) := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  have hβsurj : Function.Surjective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₂ k)) :=
    (ModuleCat.epi_iff_surjective _).mp ((isIso_iff_mono_and_epi _).mp (h₂ k)).2
  have hγinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ k)) :=
    (ModuleCat.mono_iff_injective _).mp ((isIso_iff_mono_and_epi _).mp (h₃ k)).1
  -- the composite `b' ∘ a'` is zero, via exactness at `H_k(S₂.X₂)`
  have hb'a' : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.g k)
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k) y) = 0 := by
    have hmem : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k) y ∈
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.g k)).ker := by
      rw [← ShortComplex.Exact.moduleCat_range_eq_ker (hS₂.homology_exact₂ k)]
      exact ⟨y, rfl⟩
    exact LinearMap.mem_ker.mp hmem
  obtain ⟨z, hz⟩ := hβsurj (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k) y)
  have hbz : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.g k) z = 0 := by
    have hb : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.g k) z) = 0 := by
      rw [sq₂_apply φ k z, hz]
      exact hb'a'
    exact hγinj (by rw [hb, map_zero])
  have hker : z ∈ (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₁.g k)).ker :=
    LinearMap.mem_ker.mpr hbz
  rw [← ShortComplex.Exact.moduleCat_range_eq_ker (hS₁.homology_exact₂ k)] at hker
  obtain ⟨x, hx⟩ := hker
  have ha' : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k)
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) x)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k) y := by
    rw [← sq₁_apply φ k x, hx, hz]
  by_cases hk : k = 0
  · subst hk
    haveI : Mono S₂.f := hS₂.mono_f
    haveI : Mono (HomologicalComplex.homologyMap S₂.f 0) := mono_homologyMap_f_zero S₂.f
    have hinj : Function.Injective
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f 0)) :=
      (ModuleCat.mono_iff_injective _).mp this
    exact ⟨x, hinj ha'⟩
  · have hdiff : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) x - y) = 0 := by
      rw [map_sub, ha', sub_self]
    have hker' : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) x - y ∈
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S₂.f k)).ker :=
      LinearMap.mem_ker.mpr hdiff
    rw [← ShortComplex.Exact.moduleCat_range_eq_ker
      (hS₂.homology_exact₁ (k - 1) k (upRel_pred k hk))] at hker'
    obtain ⟨u, hu⟩ := hker'
    have hγsurj : Function.Surjective
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ (k - 1))) :=
      (ModuleCat.epi_iff_surjective _).mp ((isIso_iff_mono_and_epi _).mp (h₃ (k - 1))).2
    obtain ⟨w, hw⟩ := hγsurj u
    refine ⟨x - ModuleCat.Hom.hom (hS₁.δ (k - 1) k (upRel_pred k hk)) w, ?_⟩
    have h1 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k)
        (ModuleCat.Hom.hom (hS₁.δ (k - 1) k (upRel_pred k hk)) w)
        = ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k) x - y := by
      rw [← delta_naturality_apply φ hS₁ hS₂ k hk w, hw, hu]
    rw [map_sub, h1]
    abel

/-- **The five lemma for the first term of a short exact sequence of cochain complexes.** -/
theorem quasiIso_τ₁ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₂' : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₂ i) := fun i => by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact h₂.quasiIsoAt i
  have h₃' : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₃ i) := fun i => by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact h₃.quasiIsoAt i
  haveI := mono_homologyMap_τ₁ φ hS₁ hS₂ k h₂' h₃'
  haveI := epi_homologyMap_τ₁ φ hS₁ hS₂ k h₂' h₃'
  exact isIso_of_mono_of_epi _

end Five

end

end Work.Thom

namespace Work.Thom

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-!
## The five lemma in long-exact-sequence form

The version above is stated for short exact sequences of cochain complexes.  For the
Mayer--Vietoris ladder of the Thom chapter it is more convenient to have the statement in the form
in which it is used: two long exact sequences with connecting maps
`δ₁ k : Q₁ k ⟶ M₁ (k+1)`, `δ₂ k : Q₂ k ⟶ M₂ (k+1)` and a ladder of maps `TM`, `TP`, `TQ` which
commutes with `F`, `G` and `δ`.  If `TP` and `TQ` are isomorphisms in every degree, then so is `TM`.
-/

/-- **The five lemma for two long exact sequences.**

The two sequences are enumerated starting at the *third* term, so that the connecting homomorphism
is `δ k : Q k ⟶ M k` and the exactness hypotheses read `im δ k = ker F k`, `im F k = ker G k`,
`im G k = ker (δ (k+1))`.  The single extra hypothesis `ker (δ₂ 0) = ⊥` is the "left end" of the
second sequence (in the applications it holds because there is nothing to the left of degree `0`). -/
theorem five_lemma_LES {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℤ}
    (F₁ : ∀ k, M₁ k ⟶ P₁ k) (G₁ : ∀ k, P₁ k ⟶ Q₁ (k + 1)) (δ₁ : ∀ k, Q₁ k ⟶ M₁ k)
    (F₂ : ∀ k, M₂ k ⟶ P₂ k) (G₂ : ∀ k, P₂ k ⟶ Q₂ (k + 1)) (δ₂ : ∀ k, Q₂ k ⟶ M₂ k)
    (e₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (F₁ k)))
    (e₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (G₁ k)))
    (e₃ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (δ₁ (k + 1))))
    (f₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (F₂ k)))
    (f₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (G₂ k)))
    (f₃ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (δ₂ (k + 1))))
    (f₀ : LinearMap.ker (ModuleCat.Hom.hom (δ₂ 0)) = ⊥)
    (TM : ∀ k, M₁ k ⟶ M₂ k) (TP : ∀ k, P₁ k ⟶ P₂ k) (TQ : ∀ k, Q₁ k ⟶ Q₂ k)
    (hF : ∀ k, F₁ k ≫ TP k = TM k ≫ F₂ k) (hG : ∀ k, G₁ k ≫ TQ (k + 1) = TP k ≫ G₂ k)
    (hδ : ∀ k, δ₁ k ≫ TM k = TQ k ≫ δ₂ k)
    (hP : ∀ k, IsIso (TP k)) (hQ : ∀ k, IsIso (TQ k)) :
    ∀ k, IsIso (TM k) := by
  have hF' : ∀ j, ModuleCat.Hom.hom (TP j) ∘ₗ ModuleCat.Hom.hom (F₁ j)
      = ModuleCat.Hom.hom (F₂ j) ∘ₗ ModuleCat.Hom.hom (TM j) := by
    intro j
    have h := congrArg ModuleCat.Hom.hom (hF j)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  have hG' : ∀ j, ModuleCat.Hom.hom (TQ (j + 1)) ∘ₗ ModuleCat.Hom.hom (G₁ j)
      = ModuleCat.Hom.hom (G₂ j) ∘ₗ ModuleCat.Hom.hom (TP j) := by
    intro j
    have h := congrArg ModuleCat.Hom.hom (hG j)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  have hδ' : ∀ j, ModuleCat.Hom.hom (TM j) ∘ₗ ModuleCat.Hom.hom (δ₁ j)
      = ModuleCat.Hom.hom (δ₂ j) ∘ₗ ModuleCat.Hom.hom (TQ j) := by
    intro j
    have h := congrArg ModuleCat.Hom.hom (hδ j)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  haveI hPm : ∀ j, Mono (TP j) := fun j => ((isIso_iff_mono_and_epi _).mp (hP j)).1
  haveI hPe : ∀ j, Epi (TP j) := fun j => ((isIso_iff_mono_and_epi _).mp (hP j)).2
  haveI hQm : ∀ j, Mono (TQ j) := fun j => ((isIso_iff_mono_and_epi _).mp (hQ j)).1
  haveI hQe : ∀ j, Epi (TQ j) := fun j => ((isIso_iff_mono_and_epi _).mp (hQ j)).2
  have hinjP : ∀ j, Function.Injective (ModuleCat.Hom.hom (TP j)) :=
    fun j => (ModuleCat.mono_iff_injective _).mp (hPm j)
  have hsurjP : ∀ j, Function.Surjective (ModuleCat.Hom.hom (TP j)) :=
    fun j => (ModuleCat.epi_iff_surjective _).mp (hPe j)
  have hinjQ : ∀ j, Function.Injective (ModuleCat.Hom.hom (TQ j)) :=
    fun j => (ModuleCat.mono_iff_injective _).mp (hQm j)
  have hsurjQ : ∀ j, Function.Surjective (ModuleCat.Hom.hom (TQ j)) :=
    fun j => (ModuleCat.epi_iff_surjective _).mp (hQe j)
  intro k
  rw [isIso_iff_mono_and_epi]
  constructor
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have hx : ModuleCat.Hom.hom (TM k) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hF0 : ModuleCat.Hom.hom (F₁ k) (x - y) = 0 := by
      apply hinjP k
      have h1 : ModuleCat.Hom.hom (TP k) (ModuleCat.Hom.hom (F₁ k) (x - y))
          = ModuleCat.Hom.hom (F₂ k) (ModuleCat.Hom.hom (TM k) (x - y)) := by
        have h := LinearMap.congr_fun (hF' k) (x - y)
        rwa [LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [h1, hx]
      simp only [map_zero]
    obtain ⟨w, hw⟩ := (show (x - y) ∈ LinearMap.range (ModuleCat.Hom.hom (δ₁ k)) from by
      rw [e₁ k]
      exact LinearMap.mem_ker.mpr hF0)
    have hTMδ : ModuleCat.Hom.hom (TM k) (ModuleCat.Hom.hom (δ₁ k) w) = 0 := by
      rw [hw]; exact hx
    have hδ2 : ModuleCat.Hom.hom (δ₂ k) (ModuleCat.Hom.hom (TQ k) w) = 0 := by
      have h := LinearMap.congr_fun (hδ' k) w
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [← h, hTMδ]
    rcases k with _ | k'
    · -- left end of the second sequence
      have hw0 : ModuleCat.Hom.hom (TQ 0) w = 0 := by
        have hmem : ModuleCat.Hom.hom (TQ 0) w ∈ LinearMap.ker (ModuleCat.Hom.hom (δ₂ 0)) :=
          LinearMap.mem_ker.mpr hδ2
        rw [f₀] at hmem
        simpa using hmem
      have hw' : w = 0 := hinjQ 0 (by rw [hw0, map_zero])
      rw [hw', map_zero] at hw
      exact sub_eq_zero.mp hw.symm
    · obtain ⟨u, hu⟩ := (show ModuleCat.Hom.hom (TQ (k' + 1)) w
          ∈ LinearMap.range (ModuleCat.Hom.hom (G₂ k')) from by
        rw [f₃ k']
        exact LinearMap.mem_ker.mpr hδ2)
      obtain ⟨v, hv⟩ := hsurjP k' u
      have hwu : w = ModuleCat.Hom.hom (G₁ k') v := by
        apply hinjQ (k' + 1)
        rw [← hu, ← hv]
        exact (LinearMap.congr_fun (hG' k') v).symm
      have h0 : ModuleCat.Hom.hom (δ₁ (k' + 1)) (ModuleCat.Hom.hom (G₁ k') v) = 0 := by
        have hmem : ModuleCat.Hom.hom (G₁ k') v ∈ LinearMap.range (ModuleCat.Hom.hom (G₁ k')) :=
          ⟨v, rfl⟩
        rw [e₃ k'] at hmem
        exact LinearMap.mem_ker.mp hmem
      rw [hwu, h0] at hw
      exact sub_eq_zero.mp hw.symm
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨z, hz⟩ := hsurjP k (ModuleCat.Hom.hom (F₂ k) y)
    have hG1z : ModuleCat.Hom.hom (G₁ k) z = 0 := by
      have h1 : ModuleCat.Hom.hom (TQ (k + 1)) (ModuleCat.Hom.hom (G₁ k) z) = 0 := by
        have h2 : ModuleCat.Hom.hom (TQ (k + 1)) (ModuleCat.Hom.hom (G₁ k) z)
            = ModuleCat.Hom.hom (G₂ k) (ModuleCat.Hom.hom (TP k) z) := by
          have h := LinearMap.congr_fun (hG' k) z
          rwa [LinearMap.comp_apply, LinearMap.comp_apply] at h
        rw [h2, hz]
        have hmem : ModuleCat.Hom.hom (F₂ k) y ∈ LinearMap.range (ModuleCat.Hom.hom (F₂ k)) :=
          ⟨y, rfl⟩
        rw [f₂ k] at hmem
        exact LinearMap.mem_ker.mp hmem
      exact hinjQ (k + 1) (by rw [h1]; simp only [map_zero])
    obtain ⟨x, hx⟩ := (show z ∈ LinearMap.range (ModuleCat.Hom.hom (F₁ k)) from by
      rw [e₂ k]
      exact LinearMap.mem_ker.mpr hG1z)
    have hdiff : ModuleCat.Hom.hom (F₂ k) (ModuleCat.Hom.hom (TM k) x - y) = 0 := by
      rw [map_sub]
      have h1 : ModuleCat.Hom.hom (F₂ k) (ModuleCat.Hom.hom (TM k) x)
          = ModuleCat.Hom.hom (TP k) (ModuleCat.Hom.hom (F₁ k) x) :=
        (LinearMap.congr_fun (hF' k) x).symm
      rw [h1, hx, hz, sub_self]
    obtain ⟨u, hu⟩ := (show ModuleCat.Hom.hom (TM k) x - y
        ∈ LinearMap.range (ModuleCat.Hom.hom (δ₂ k)) from by
      rw [f₁ k]
      exact LinearMap.mem_ker.mpr hdiff)
    obtain ⟨w, hw⟩ := hsurjQ k u
    refine ⟨x - ModuleCat.Hom.hom (δ₁ k) w, ?_⟩
    have h1 : ModuleCat.Hom.hom (TM k) (ModuleCat.Hom.hom (δ₁ k) w)
        = ModuleCat.Hom.hom (TM k) x - y := by
      have h := LinearMap.congr_fun (hδ' k) w
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [h, hw, hu]
    rw [map_sub, h1]
    abel

end

end Work.Thom
