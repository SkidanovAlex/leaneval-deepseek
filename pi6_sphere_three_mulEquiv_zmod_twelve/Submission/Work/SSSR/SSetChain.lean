import Mathlib
import Submission.Work.SSSR.StemsB.SerreFiltration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

/-!
# Singular chains of a simplicial set: the componentwise description of induced chain maps

The singular chain complex of a simplicial set `X` with coefficients in `R` is
`(X.chainComplex R).X n = ∐_{x : X_n} R`, the coproduct of one copy of `R` for each `n`-simplex of
`X`; the differential is the alternating sum of the face maps (`SSet.chainComplex`,
`SSet.ιChainComplex`).

This file records the elementary facts about this description that the Serre filtration
(`Work.StemsB.serreChainFiltration`) needs:

* `Work.SSSR.sChainMap_f` — the `n`-th component of the chain map induced by a morphism of
  simplicial sets `f : X ⟶ Y` is the map of coproducts `∐_{x : X_n} R ⟶ ∐_{y : Y_n} R` induced by
  the map of index sets `f.app _ : X_n → Y_n` (`Limits.Sigma.map'`);
* `Work.SSSR.sChainMap_mono` — such a chain map is a monomorphism when `f` is;
* `Work.SSSR.isIso_f_of_bijective` — its `n`-th component is an isomorphism when `f` is bijective on
  `n`-simplices (this is the saturation property of the Serre filtration);
* `Work.SSSR.mono_serreChainFiltration_map` — the structure maps of the Serre filtration of the
  singular chain complex are monomorphisms;
* `Work.SSSR.serreFiltration_map_iota` — the interaction of those structure maps with the inclusions
  of the filtration levels into the ambient complex;
* `Work.SSSR.serreSubcomplex_obj_eq_top` — the `(P+1)`-st term of the Serre filtration contains every
  `P`-simplex;
* `Work.SSSR.natShift` — the functor `ℕ ⥤ ℕ`, `n ↦ n + 1` (the reindexing of the Serre filtration by
  the `(P+1)`-skeleton, so that the `0`-th term is the singular chain complex of the empty
  subcomplex).
-/

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- The singular chain complex of a simplicial set `X` with coefficients in `R`, spelled through
the coproduct description `(X.chainComplex R).X n = ∐_{x : X_n} R`. -/
abbrev sChains (R : Type) [CommRing R] (X : SSet) : ChainComplex (ModuleCat R) ℕ :=
  X.chainComplex (ModuleCat.of R R)

/-- The chain map induced by a morphism of simplicial sets. -/
abbrev sChainMap (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) :
    sChains R X ⟶ sChains R Y :=
  SSet.chainComplexMap f (ModuleCat.of R R)

/-- The chain map induced by a composition of morphisms of simplicial sets is the composition of
the induced chain maps. -/
lemma sChainMap_comp (R : Type) [CommRing R] {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sChainMap R f ≫ sChainMap R g = sChainMap R (f ≫ g) := by
  simp only [sChainMap, SSet.chainComplexMap, Functor.map_comp]

/-- The `n`-th component of the chain map induced by `f : X ⟶ Y` is the map of coproducts
`∐_{x : X_n} R ⟶ ∐_{y : Y_n} R` induced by the map of index sets `f.app (op ⦋n⦌)`. -/
lemma sChainMap_f (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) (n : ℕ) :
    (sChainMap R f).f n =
      Sigma.map' (fun x : X _⦋n⦌ => (f.app (op ⦋n⦌) x : Y _⦋n⦌))
        (fun _ => 𝟙 (ModuleCat.of R R)) := by
  apply SSet.chainComplex_hom_ext
  intro x
  have h1 : X.ιChainComplex x ≫ (sChainMap R f).f n =
      Y.ιChainComplex (f.app (op ⦋n⦌) x) :=
    SSet.ι_chainComplexMap_f X Y f (ModuleCat.of R R) x
  have h2 : X.ιChainComplex x ≫
        Sigma.map' (g := fun _ : X _⦋n⦌ => ModuleCat.of R R)
          (f := fun _ : Y _⦋n⦌ => ModuleCat.of R R) (fun x => f.app (op ⦋n⦌) x)
          (fun _ => 𝟙 (ModuleCat.of R R)) =
      Y.ιChainComplex (f.app (op ⦋n⦌) x) := by
    change Sigma.ι (fun _ : X _⦋n⦌ => ModuleCat.of R R) x ≫
        Sigma.map' (fun x : X _⦋n⦌ => (f.app (op ⦋n⦌) x : Y _⦋n⦌)) (fun _ => 𝟙 (ModuleCat.of R R)) =
      Sigma.ι (fun _ : Y _⦋n⦌ => ModuleCat.of R R) (f.app (op ⦋n⦌) x)
    rw [Sigma.ι_comp_map']
    rfl
  exact h1.trans h2.symm

/-- The map of coproducts induced by an injective map of index sets is a monomorphism. -/
lemma mono_sigma_map'_of_injective (R : Type) [CommRing R] {A B : Type} (σ : B → A)
    (hσ : Function.Injective σ) :
    Mono (Sigma.map' (g := fun _ : B => ModuleCat.of R R)
      (f := fun _ : A => ModuleCat.of R R) σ (fun _ => 𝟙 (ModuleCat.of R R))) :=
  MonoCoprod.mono_map'_of_injective (fun _ : A => ModuleCat.of R R) σ hσ

/-- A monomorphism of simplicial sets is injective on `n`-simplices. -/
lemma injective_app_of_mono {X Y : SSet} (f : X ⟶ Y) (hf : Mono f) (n : ℕ) :
    Function.Injective (f.app (op ⦋n⦌)) :=
  (mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app f).mp hf (op ⦋n⦌))

/-- The chain map induced by a monomorphism of simplicial sets is a monomorphism. -/
lemma sChainMap_mono (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) (hf : Mono f) :
    Mono (sChainMap R f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [sChainMap_f R f n]
  exact mono_sigma_map'_of_injective R _ (injective_app_of_mono f hf n)

/-- The inverse of the map of coproducts induced by a bijection of index sets, built from a
section of that bijection. -/
lemma isIso_sigma_map'_of_bijective (R : Type) [CommRing R] {A B : Type} (σ : B → A)
    (hσ : Function.Bijective σ) :
    IsIso (Sigma.map' (g := fun _ : B => ModuleCat.of R R)
      (f := fun _ : A => ModuleCat.of R R) σ (fun _ => 𝟙 (ModuleCat.of R R))) := by
  obtain ⟨s, hs⟩ : ∃ s : A → B, ∀ a, σ (s a) = a :=
    ⟨fun a => Classical.choose (hσ.2 a), fun a => Classical.choose_spec (hσ.2 a)⟩
  refine ⟨Sigma.map' (g := fun _ : A => ModuleCat.of R R)
    (f := fun _ : B => ModuleCat.of R R) s (fun _ => 𝟙 (ModuleCat.of R R)), ?_, ?_⟩
  · rw [Sigma.map'_comp_map']
    have h2 : (s ∘ σ) = id := funext (fun b => hσ.1 (hs (σ b)))
    rw [h2]
    exact Sigma.map'_id_id
  · rw [Sigma.map'_comp_map']
    rw [show (σ ∘ s) = id from funext hs]
    exact Sigma.map'_id_id

/-- The `n`-th component of the chain map induced by a morphism of simplicial sets which is
bijective on `n`-simplices is an isomorphism. -/
lemma isIso_f_of_bijective (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) (n : ℕ)
    (h : Function.Bijective (f.app (op ⦋n⦌))) : IsIso ((sChainMap R f).f n) := by
  rw [sChainMap_f R f n]
  exact isIso_sigma_map'_of_bijective R _ h

/-- The inclusion `S.ι : S ⟶ X` of a subcomplex is bijective on `n`-simplices as soon as `S`
contains every `n`-simplex of `X`. -/
lemma bijective_iota_app_of_obj_eq_top {X : SSet} (S : X.Subcomplex) (n : ℕ)
    (h : S.obj (op ⦋n⦌) = ⊤) :
    Function.Bijective ((Subfunctor.ι S).app (op ⦋n⦌)) := by
  constructor
  · intro a b hab
    exact Subtype.ext hab
  · intro x
    exact ⟨⟨x, h ▸ Set.mem_univ x⟩, rfl⟩

/-- The reindexing `n ↦ n + 1` of `ℕ` as a functor. -/
def natShift : ℕ ⥤ ℕ where
  obj n := n + 1
  map f := homOfLE (Nat.succ_le_succ (leOfHom f))

/-- The `(P+1)`-st term of the Serre filtration of a simplicial set `X` along `f : X ⟶ Y` contains
every `P`-simplex (an `P`-simplex lies in the `P`-skeleton of the base, hence in its `(P+1)`-skeleton
too). -/
lemma serreSubcomplex_obj_eq_top {X Y : SSet} (f : X ⟶ Y) (P : ℕ) :
    (Work.SSSR.StemsB.serreSubcomplex f (P + 1)).obj (op ⦋P⦌) = ⊤ := by
  rw [← top_le_iff]
  intro x _
  rw [Work.SSSR.StemsB.mem_serreSubcomplex]
  rw [SSet.skeleton_obj_eq_top (X := Y) (Nat.lt_succ_self P)]
  exact trivial

/-- The structure maps `F_s ⟶ F_{s+1}` of the Serre filtration of the singular chain complex are
monomorphisms. -/
lemma mono_serreChainFiltration_map (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y)
    {a b : ℕ} (φ : a ⟶ b) :
    Mono ((Work.SSSR.StemsB.serreChainFiltration f R).map φ) := by
  have hφ : Mono ((Work.SSSR.StemsB.serreFiltration f).map φ) := by
    change Mono (Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono f (leOfHom φ)))
    infer_instance
  exact sChainMap_mono R ((Work.SSSR.StemsB.serreFiltration f).map φ) hφ

/-- The structure map `F_s ⟶ F_{s+1}` of the Serre filtration, shifted by `n ↦ n+1`, followed by
the inclusion of `F_{t+1}` into the ambient complex, is the inclusion of `F_{s+1}`. -/
lemma serreFiltration_map_iota {X Y : SSet} (f : X ⟶ Y) (s t : ℕ) (h : s ≤ t) :
    (Work.SSSR.StemsB.serreFiltration f).map (natShift.map (homOfLE h)) ≫
        Subfunctor.ι (Work.SSSR.StemsB.serreSubcomplex f (t + 1)) =
      Subfunctor.ι (Work.SSSR.StemsB.serreSubcomplex f (s + 1)) :=
  Subfunctor.homOfLe_ι (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.succ_le_succ h))

end

end Work.SSSR
