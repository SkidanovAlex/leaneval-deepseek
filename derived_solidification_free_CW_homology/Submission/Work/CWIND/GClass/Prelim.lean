import Mathlib
import Submission.Work.CWIND.Basic

/-!
# CWIND/T9 auxiliary lemmas

Small independent facts used in the proof of `Work.CWIND.GClass.G_exhaust`:

* `types_colim` — a cocone over an `ℕ`-indexed diagram of types with injective legs which jointly
  cover its point is a colimit cocone;
* `zero_cocone` — a cocone over a diagram of zero objects with zero point is a colimit cocone;
* `mapping_compact` — compactness in the compact-open mapping space `X^{Δᵏ}`;
* `singSpace_subtype_iso` — the mapping space on a subspace.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

universe u

namespace Work.CWIND.GClass

open Work.CWIND

/-! ## Types -/

/-- If a cocone over an `ℕ`-indexed diagram of types has injective legs which jointly cover its
point, it is a colimit cocone. -/
theorem types_colim {J : ℕ ⥤ Type u} (c : Cocone J)
    (hinj : ∀ n, Function.Injective (c.ι.app n))
    (hsurj : ∀ y : c.pt, ∃ n, ∃ x : J.obj n, c.ι.app n x = y) :
    Nonempty (IsColimit c) := by
  classical
  have cocone_apply : ∀ {m n : ℕ} (f : m ⟶ n) (x : J.obj m),
      c.ι.app n (J.map f x) = c.ι.app m x := by
    intro m n f x
    have h := c.ι.naturality f
    simp only [Functor.const_obj_map] at h
    exact congrArg (fun φ : J.obj m ⟶ c.pt => φ x) h
  have key : ∀ (s : Cocone J) (bx : c.pt) (n : ℕ) (x : J.obj n),
      c.ι.app n x = bx → ∀ (m : ℕ) (x' : J.obj m), c.ι.app m x' = bx →
      s.ι.app n x = s.ι.app m x' := by
    intro s bx n x hx m x' hx'
    have h1 : J.map (homOfLE (le_max_left n m)) x = J.map (homOfLE (le_max_right n m)) x' := by
      apply hinj (max n m)
      rw [cocone_apply, cocone_apply, hx, hx']
    have hs1 : s.ι.app (max n m) (J.map (homOfLE (le_max_left n m)) x) = s.ι.app n x := by
      have h := s.ι.naturality (homOfLE (le_max_left n m))
      simp only [Functor.const_obj_map] at h
      exact congrArg (fun φ : J.obj n ⟶ s.pt => φ x) h
    have hs2 : s.ι.app (max n m) (J.map (homOfLE (le_max_right n m)) x') = s.ι.app m x' := by
      have h := s.ι.naturality (homOfLE (le_max_right n m))
      simp only [Functor.const_obj_map] at h
      exact congrArg (fun φ : J.obj m ⟶ s.pt => φ x') h
    rw [← hs1, ← hs2, h1]
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro s
    exact ConcreteCategory.ofHom ⟨fun y => s.ι.app (Classical.choose (hsurj y))
      (Classical.choose (Classical.choose_spec (hsurj y)))⟩
  · intro s n
    apply ConcreteCategory.hom_ext
    intro x
    exact key s (c.ι.app n x) (Classical.choose (hsurj (c.ι.app n x)))
      (Classical.choose (Classical.choose_spec (hsurj (c.ι.app n x))))
      (Classical.choose_spec (Classical.choose_spec (hsurj (c.ι.app n x)))) n x rfl
  · intro s m hm
    apply ConcreteCategory.hom_ext
    intro y
    have h := congrArg (fun φ : J.obj (Classical.choose (hsurj y)) ⟶ s.pt => φ
        (Classical.choose (Classical.choose_spec (hsurj y)))) (hm (Classical.choose (hsurj y)))
    simp only [ConcreteCategory.comp_apply] at h
    rw [Classical.choose_spec (Classical.choose_spec (hsurj y))] at h
    simpa using h

/-! ## Zero cocones -/

/-- A cocone over a diagram of zero objects, with zero point, is a colimit cocone. -/
theorem zero_cocone {J : Type*} [Category* J] {C : Type*} [Category* C] [HasZeroMorphisms C]
    {F : J ⥤ C} (c : Cocone F) (hpt : IsZero c.pt) (hF : ∀ j, IsZero (F.obj j)) :
    Nonempty (IsColimit c) :=
  ⟨{ desc := fun s => hpt.to_ s.pt
     fac := fun s j => (hF j).eq_of_src _ _
     uniq := fun s m _ => hpt.eq_of_src _ _ }⟩

/-! ## Compactness of the mapping space -/

/-- If every compact subset of `X` is contained in some `A n`, then the same holds for the
compact-open mapping space `X^{Δᵏ} = singSpace X k`, with the subspaces `singSpace (A n) k`. -/
theorem mapping_compact {X : TopCat.{0}} [T2Space X] {A : ℕ → Set X}
    (hcpt : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) (k : ℕ)
    {K : Set (singSpace X k)} (hK : IsCompact K) :
    ∃ n, ∀ f ∈ K, ∀ s, f s ∈ A n := by
  haveI : CompactSpace ↥(Δ k) := Convexity.StdSimplex.compactSpace ℝ (Fin (k + 1))
  have hcont : Continuous fun p : ↥(singSpace X k) × ↥(Δ k) => (p.1 p.2 : ↥X) :=
    continuous_eval
  have hprod : IsCompact (K ×ˢ (Set.univ : Set ↥(Δ k))) := hK.prod isCompact_univ
  have himg : IsCompact ((fun p : ↥(singSpace X k) × ↥(Δ k) => (p.1 p.2 : ↥X)) ''
      (K ×ˢ (Set.univ : Set ↥(Δ k)))) := hprod.image hcont
  obtain ⟨n, hn⟩ := hcpt _ himg
  exact ⟨n, fun f hf s => hn ⟨(f, s), ⟨hf, Set.mem_univ s⟩, rfl⟩⟩

/-! ## The mapping space on a subspace -/

/-- For `A ⊆ X` and `k : ℕ`, the space of continuous maps `Δᵏ → X` with image in `A` (a subspace
of the compact-open mapping space `X^{Δᵏ}`) is canonically homeomorphic to `A^{Δᵏ}`, compatibly
with the inclusions into `X^{Δᵏ}`. -/
theorem singSpace_subtype_iso {X : TopCat.{0}} [T2Space X] (A : Set X) (k : ℕ) :
    ∃ (e : TopCat.of {f : ↥(singSpace X k) // ∀ s, f s ∈ A} ≅ singSpace (TopCat.of A) k),
      (e.hom ≫ singSpacePostcomp (X := TopCat.of A) (Y := X)
          (Submission.Blueprint.inclTop A) k :
        TopCat.of {f : ↥(singSpace X k) // ∀ s, f s ∈ A} ⟶ singSpace X k) =
      Submission.Blueprint.inclTop
        (A := {f : ↥(singSpace X k) | ∀ s, f s ∈ A}) := by
  haveI : CompactSpace ↥(Δ k) := Convexity.StdSimplex.compactSpace ℝ (Fin (k + 1))
  let β : Type := {f : ↥(singSpace X k) // ∀ s, f s ∈ A}
  let φ : β → ↥(singSpace (TopCat.of A) k) :=
    fun g => ContinuousMap.mk (fun s => (⟨g.1 s, g.2 s⟩ : ↥A))
      (Continuous.subtype_mk (g.1 : C(Δ k, ↥X)).continuous (fun s => g.2 s))
  let ψ : ↥(singSpace (TopCat.of A) k) → β :=
    fun g => ⟨ContinuousMap.mk (fun s => ((g : C(Δ k, ↥A)) s : ↥X))
        (continuous_subtype_val.comp (g : C(Δ k, ↥A)).continuous),
      fun s => ((g : C(Δ k, ↥A)) s).2⟩
  have hφ : Continuous φ := by
    refine ContinuousMap.continuous_of_continuous_uncurry (fun g => (φ g : C(Δ k, ↥A))) ?_
    change Continuous (fun p : β × ↥(Δ k) => (⟨(p.1.1 : C(Δ k, ↥X)) p.2, p.1.2 p.2⟩ : ↥A))
    have h1 : Continuous (fun p : β × ↥(Δ k) => (((p.1.1 : C(Δ k, ↥X)) p.2 : ↥X))) :=
      (continuous_eval (F := C(Δ k, ↥X)) (X := ↥(Δ k)) (Y := ↥X)).comp
        (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd)
    exact Continuous.subtype_mk h1 (fun p => p.1.2 p.2)
  have hψ : Continuous ψ := by
    refine Continuous.subtype_mk (p := fun f : ↥(singSpace X k) => ∀ s, f s ∈ A) ?_
      (fun g s => (((g : C(Δ k, ↥A)) s)).2)
    refine ContinuousMap.continuous_of_continuous_uncurry (fun g =>
      (ContinuousMap.mk (fun s => (((g : C(Δ k, ↥A)) s) : ↥X))
        (continuous_subtype_val.comp (g : C(Δ k, ↥A)).continuous) : C(Δ k, ↥X))) ?_
    change Continuous (fun p : ↥(singSpace (TopCat.of A) k) × ↥(Δ k) =>
      (((p.1 : C(Δ k, ↥A)) p.2 : ↥A) : ↥X))
    have h1 : Continuous (fun p : ↥(singSpace (TopCat.of A) k) × ↥(Δ k) =>
        (((p.1 : C(Δ k, ↥A)) p.2 : ↥A) : ↥X)) :=
      ((continuous_eval (F := C(Δ k, ↥A)) (X := ↥(Δ k)) (Y := ↥A)).comp
        (Continuous.prodMk continuous_fst continuous_snd)).subtype_val
    exact h1
  have hleft : Function.LeftInverse ψ φ := by
    intro g
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    rfl
  have hright : Function.RightInverse ψ φ := by
    intro g
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl
  refine ⟨Iso.mk (TopCat.ofHom ⟨φ, hφ⟩) (TopCat.ofHom ⟨ψ, hψ⟩) ?_ ?_, ?_⟩
  · apply TopCat.ext
    intro g
    exact hleft g
  · apply TopCat.ext
    intro g
    exact hright g
  · apply TopCat.ext
    intro g
    rfl

/-! ## Coproducts over an increasing union -/

section CoprodUnion

variable {C : Type*} [Category* C] [HasCoproducts.{0} C]

abbrev coprodObj (β : Type) (G : C) : C := sigmaObj (fun _ : β => G)

def coprodMap {β γ : Type} (u : β → γ) (G : C) : coprodObj β G ⟶ coprodObj γ G :=
  Sigma.desc (fun x : β => Sigma.ι (fun _ : γ => G) (u x))

@[simp]
lemma coprodMap_ι {β γ : Type} (u : β → γ) (G : C) (x : β) :
    Sigma.ι (fun _ : β => G) x ≫ coprodMap u G = Sigma.ι (fun _ : γ => G) (u x) :=
  Sigma.ι_comp_desc _ x

abbrev coprodDiagram (J : ℕ ⥤ Type) (G : C) : ℕ ⥤ C where
  obj n := coprodObj (J.obj n) G
  map {m n} f := coprodMap (J.map f) G
  map_id m := by
    apply Sigma.hom_ext
    intro x
    rw [coprodMap_ι, Category.comp_id]
    simp
  map_comp {m n k} f g := by
    apply Sigma.hom_ext
    intro x
    rw [← Category.assoc, coprodMap_ι, coprodMap_ι, coprodMap_ι, Functor.map_comp]
    rfl

@[simp]
lemma coprodDiagram_map {J : ℕ ⥤ Type} (G : C) {m n : ℕ} (f : m ⟶ n) :
    (coprodDiagram J G).map f = coprodMap (J.map f) G := rfl

abbrev coprodUnionCocone (J : ℕ ⥤ Type) (G : C) (c : Cocone J) : Cocone (coprodDiagram J G) where
  pt := coprodObj c.pt G
  ι :=
    { app := fun n => coprodMap (c.ι.app n) G
      naturality := by
        intro m n f
        rw [Functor.const_obj_map]
        erw [Category.comp_id]
        apply Sigma.hom_ext
        intro x
        rw [← Category.assoc, coprodMap_ι, coprodMap_ι, coprodMap_ι]
        have h : c.ι.app n ((J.map f) x) = c.ι.app m x := by
          have h' := congrArg (fun φ : J.obj m ⟶ c.pt => φ x) (c.w f)
          simpa only [ConcreteCategory.comp_apply] using h'
        exact congrArg (Sigma.ι (fun _ : c.pt => G)) h }

@[simp]
lemma coprodUnionCocone_ι_app (J : ℕ ⥤ Type) (G : C) (c : Cocone J) (n : ℕ) :
    (coprodUnionCocone J G c).ι.app n = coprodMap (c.ι.app n) G := rfl

@[simp]
lemma coprodUnionCocone_pt (J : ℕ ⥤ Type) (G : C) (c : Cocone J) :
    (coprodUnionCocone J G c).pt = coprodObj c.pt G := rfl

theorem coprod_union_colimit {J : ℕ ⥤ Type} (c : Cocone J) (G : C)
    (hinj : ∀ n, Function.Injective (c.ι.app n))
    (hsurj : ∀ y : c.pt, ∃ n, ∃ x : J.obj n, c.ι.app n x = y) :
    Nonempty (IsColimit (coprodUnionCocone J G c)) := by
  classical
  have hw : ∀ {m n : ℕ} (f : m ⟶ n) (x : J.obj m),
      c.ι.app n ((J.map f) x) = c.ι.app m x := by
    intro m n f x
    have h := congrArg (fun φ : J.obj m ⟶ c.pt => φ x) (c.w f)
    simpa only [ConcreteCategory.comp_apply] using h
  have key : ∀ (s : Cocone (coprodDiagram J G)) (n m : ℕ) (x : J.obj n) (x' : J.obj m),
      c.ι.app n x = c.ι.app m x' →
      Sigma.ι (fun _ : J.obj n => G) x ≫ s.ι.app n =
        Sigma.ι (fun _ : J.obj m => G) x' ≫ s.ι.app m := by
    intro s n m x x' h
    have h1 : (J.map (homOfLE (le_max_left n m))) x =
        (J.map (homOfLE (le_max_right n m))) x' := by
      apply hinj (max n m)
      rw [hw (homOfLE (le_max_left n m)) x, hw (homOfLE (le_max_right n m)) x', h]
    have hs1 : Sigma.ι (fun _ : J.obj (max n m) => G)
          ((J.map (homOfLE (le_max_left n m))) x) ≫ s.ι.app (max n m) =
        Sigma.ι (fun _ : J.obj n => G) x ≫ s.ι.app n := by
      rw [← s.w (homOfLE (le_max_left n m)), ← Category.assoc, coprodDiagram_map, coprodMap_ι]
    have hs2 : Sigma.ι (fun _ : J.obj (max n m) => G)
          ((J.map (homOfLE (le_max_right n m))) x') ≫ s.ι.app (max n m) =
        Sigma.ι (fun _ : J.obj m => G) x' ≫ s.ι.app m := by
      rw [← s.w (homOfLE (le_max_right n m)), ← Category.assoc, coprodDiagram_map, coprodMap_ι]
    rw [← hs1, ← hs2, h1]
  refine ⟨IsColimit.mk (fun s => Sigma.desc (fun y : c.pt =>
      Sigma.ι (fun _ : J.obj (Classical.choose (hsurj y)) => G)
        (Classical.choose (Classical.choose_spec (hsurj y))) ≫
          s.ι.app (Classical.choose (hsurj y)))) ?_ ?_⟩
  · intro s n
    apply Sigma.hom_ext
    intro x
    rw [coprodUnionCocone_ι_app, ← Category.assoc, coprodMap_ι, Sigma.ι_comp_desc]
    exact (key s n (Classical.choose (hsurj (c.ι.app n x))) x
      (Classical.choose (Classical.choose_spec (hsurj (c.ι.app n x))))
      (Classical.choose_spec (Classical.choose_spec (hsurj (c.ι.app n x)))).symm).symm
  · intro s m' hm'
    apply Sigma.hom_ext
    intro y
    rw [Sigma.ι_comp_desc]
    have hleg : Sigma.ι (fun _ : J.obj (Classical.choose (hsurj y)) => G)
          (Classical.choose (Classical.choose_spec (hsurj y))) ≫
            coprodMap (c.ι.app (Classical.choose (hsurj y))) G =
        Sigma.ι (fun _ : c.pt => G) y := by
      rw [coprodMap_ι]
      exact congrArg (Sigma.ι (fun _ : c.pt => G))
        (Classical.choose_spec (Classical.choose_spec (hsurj y)))
    calc (Sigma.ι (fun _ : c.pt => G) y) ≫ m'
        = (Sigma.ι (fun _ : J.obj (Classical.choose (hsurj y)) => G)
              (Classical.choose (Classical.choose_spec (hsurj y))) ≫
                coprodMap (c.ι.app (Classical.choose (hsurj y))) G) ≫ m' := by rw [hleg]
      _ = Sigma.ι (fun _ : J.obj (Classical.choose (hsurj y)) => G)
              (Classical.choose (Classical.choose_spec (hsurj y))) ≫
            (coprodMap (c.ι.app (Classical.choose (hsurj y))) G ≫ m') :=
            Category.assoc _ _ _
      _ = Sigma.ι (fun _ : J.obj (Classical.choose (hsurj y)) => G)
              (Classical.choose (Classical.choose_spec (hsurj y))) ≫
            s.ι.app (Classical.choose (hsurj y)) :=
        congrArg (fun t => Sigma.ι (fun _ : J.obj (Classical.choose (hsurj y)) => G)
              (Classical.choose (Classical.choose_spec (hsurj y))) ≫ t)
          (hm' (Classical.choose (hsurj y)))


end CoprodUnion

end Work.CWIND.GClass
