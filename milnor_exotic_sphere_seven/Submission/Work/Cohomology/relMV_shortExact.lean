import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.coprod_shortExact
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.cokernel_map_shortExact
import Submission.Work.Cohomology.cokernel_biprod_map_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Mayer–Vietoris short exact sequence

For a space `X` and subsets `A, U, V ⊆ X` the sequence of relative small chain complexes

`0 → C^{U,V}(U ∩ V, U ∩ V ∩ A) → C^{U,V}(U, U ∩ A) ⊕ C^{U,V}(V, V ∩ A) → C^{U,V}(X, A) → 0`

is short exact, where the complexes are those of `Submission/Work/Cohomology/RelMVDefs.lean` and the
maps are induced by the inclusions `U ∩ V ⊆ U`, `U ∩ V ⊆ V` (together with `U ∩ A ⊆ U` etc.).

The proof has three parts.

* The *absolute* Mayer–Vietoris rows
  `0 → C(U∩V) → C(U) ⊞ C(V) → C^{U,V}(X) → 0` and `0 → C(U∩V∩A) → C(U∩A) ⊞ C(V∩A) → C^{U,V}(A) → 0`
  are short exact.  This is proved degreewise from the abstract `Work.Cohomology.coprod_shortExact`
  (the hypotheses there — the square of index types is a pullback, and the cover condition — are
  trivial for sets of simplices).
* The vertical maps `C(…) → C(…)` are monomorphisms, so the snake lemma applied to the map of short
  exact sequences exhibits the cokernels as a short exact sequence
  (`Work.Cohomology.cokernel_map_shortExact`).
* The middle cokernel of the vertical map is identified with the biproduct
  `C(U, U∩A) ⊞ C(V, V∩A)` of the two relative complexes (`Work.Cohomology.cokernel_biprod_map_iso`).

## Main result

* `relMV_shortExact` — the relative Mayer–Vietoris sequence is short exact.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## 1. The index maps of the two rows -/

/-- The inclusion of the `n`-simplices of `U ∩ V` into those of `U`. -/
def idxUVU (U V : Set X) (n : ℕ) :
    (smallInSSet U V (U ∩ V)) _⦋n⦌ → (smallInSSet U V U) _⦋n⦌ :=
  fun σ => ⟨σ.1, ⟨σ.2.1, fun x hx => (σ.2.2 hx).1⟩⟩

/-- The inclusion of the `n`-simplices of `U ∩ V` into those of `V`. -/
def idxUVV (U V : Set X) (n : ℕ) :
    (smallInSSet U V (U ∩ V)) _⦋n⦌ → (smallInSSet U V V) _⦋n⦌ :=
  fun σ => ⟨σ.1, ⟨σ.2.1, fun x hx => (σ.2.2 hx).2⟩⟩

/-- The inclusion of the small `n`-simplices lying in `U` into all small `n`-simplices. -/
def idxUsm (U V : Set X) (n : ℕ) :
    (smallInSSet U V U) _⦋n⦌ → (smallSSet U V) _⦋n⦌ :=
  fun σ => ⟨σ.1, σ.2.1⟩

/-- The inclusion of the small `n`-simplices lying in `V` into all small `n`-simplices. -/
def idxVsm (U V : Set X) (n : ℕ) :
    (smallInSSet U V V) _⦋n⦌ → (smallSSet U V) _⦋n⦌ :=
  fun σ => ⟨σ.1, σ.2.1⟩

/-- The inclusion of the `n`-simplices of `U ∩ V ∩ A` into those of `U ∩ A`. -/
def idxA1 (U V A : Set X) (n : ℕ) :
    (smallInSSet U V (U ∩ V ∩ A)) _⦋n⦌ → (smallInSSet U V (U ∩ A)) _⦋n⦌ :=
  fun σ => ⟨σ.1, ⟨σ.2.1, fun x hx => ⟨(σ.2.2 hx).1.1, (σ.2.2 hx).2⟩⟩⟩

/-- The inclusion of the `n`-simplices of `U ∩ V ∩ A` into those of `V ∩ A`. -/
def idxA2 (U V A : Set X) (n : ℕ) :
    (smallInSSet U V (U ∩ V ∩ A)) _⦋n⦌ → (smallInSSet U V (V ∩ A)) _⦋n⦌ :=
  fun σ => ⟨σ.1, ⟨σ.2.1, fun x hx => ⟨(σ.2.2 hx).1.2, (σ.2.2 hx).2⟩⟩⟩

/-- The inclusion of the small `n`-simplices lying in `U ∩ A` into those lying in `A`. -/
def idxAU (U V A : Set X) (n : ℕ) :
    (smallInSSet U V (U ∩ A)) _⦋n⦌ → (smallInSSet U V A) _⦋n⦌ :=
  fun σ => ⟨σ.1, ⟨σ.2.1, fun x hx => (σ.2.2 hx).2⟩⟩

/-- The inclusion of the small `n`-simplices lying in `V ∩ A` into those lying in `A`. -/
def idxAV (U V A : Set X) (n : ℕ) :
    (smallInSSet U V (V ∩ A)) _⦋n⦌ → (smallInSSet U V A) _⦋n⦌ :=
  fun σ => ⟨σ.1, ⟨σ.2.1, fun x hx => (σ.2.2 hx).2⟩⟩

/-! ## 2. Auxiliary lemmas on the chain maps of the small subcomplexes -/

/-- Two chain maps between the chain complexes of simplicial sets agree as soon as they agree on
the generators of every degree. -/
theorem chainMap_SSet_ext {Y Z : SSet}
    {f g : Y.chainComplex (ModuleCat.of ℤ ℤ) ⟶ Z.chainComplex (ModuleCat.of ℤ ℤ)}
    (h : ∀ n (σ : Y _⦋n⦌), Y.ιChainComplex σ ≫ f.f n = Y.ιChainComplex σ ≫ g.f n) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  exact SSet.chainComplex_hom_ext (fun σ => h n σ)

/-- The inclusion of the small chains lying in `C` into those lying in `B`, composed with the
inclusion of the latter into the small chains of `X`, is the inclusion of the small chains lying
in `C`. -/
theorem subInclChain_smallInToSmall (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    subInclChain U V h ≫ smallInToSmall U V B = smallInToSmall U V C := by
  apply chainMap_SSet_ext
  intro n σ
  rw [HomologicalComplex.comp_f]
  dsimp only [subInclChain, smallInToSmall]
  rw [← Category.assoc]
  simp only [SSet.ι_chainComplexMap_f]
  rfl

/-- Functoriality of `subInclChain`. -/
theorem subInclChain_comp (U V : Set X) {A₁ A₂ A₃ : Set X} (h₁ : A₁ ⊆ A₂) (h₂ : A₂ ⊆ A₃) :
    subInclChain U V h₁ ≫ subInclChain U V h₂ = subInclChain U V (h₁.trans h₂) := by
  apply chainMap_SSet_ext
  intro n σ
  rw [HomologicalComplex.comp_f]
  dsimp only [subInclChain]
  rw [← Category.assoc]
  simp only [SSet.ι_chainComplexMap_f]
  rfl

/-- `subInclChain` is a monomorphism. -/
theorem mono_subInclChain (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    Mono (subInclChain U V h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono (coprodMap (fun σ : (smallInSSet U V C) _⦋n⦌ =>
    (⟨σ.1, ⟨σ.2.1, σ.2.2.trans h⟩⟩ : (smallInSSet U V B) _⦋n⦌)))
  refine mono_coprodMap _ (fun a b hab => ?_)
  have ha : ((⟨a.1, ⟨a.2.1, a.2.2.trans h⟩⟩ : (smallInSSet U V B) _⦋n⦌) :
      (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
  have hb : ((⟨b.1, ⟨b.2.1, b.2.2.trans h⟩⟩ : (smallInSSet U V B) _⦋n⦌) :
      (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
  exact Subtype.ext (by rw [← ha, ← hb, hab])

/-- The inclusion of the small chains lying in `B` into the small chains of `X` is a monomorphism. -/
theorem mono_smallInToSmall (U V : Set X) (B : Set X) : Mono (smallInToSmall U V B) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono (coprodMap (fun σ : (smallInSSet U V B) _⦋n⦌ =>
    (⟨σ.1, σ.2.1⟩ : (smallSSet U V) _⦋n⦌)))
  refine mono_coprodMap _ (fun a b hab => ?_)
  have ha : ((⟨a.1, a.2.1⟩ : (smallSSet U V) _⦋n⦌) : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
  have hb : ((⟨b.1, b.2.1⟩ : (smallSSet U V) _⦋n⦌) : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
  exact Subtype.ext (by rw [← ha, ← hb, hab])

/-! ## 3. The two Mayer–Vietoris rows -/

/-- The first map of the small Mayer–Vietoris sequence of the cover `(U,V)`:
`C(U ∩ V) ⟶ C(U) ⊞ C(V)`. -/
def mvLeftSmall (U V : Set X) :
    smallInChains U V (U ∩ V) ⟶ smallInChains U V U ⊞ smallInChains U V V :=
  biprod.lift (subInclChain U V (by intro x hx; exact hx.1))
    (subInclChain U V (by intro x hx; exact hx.2))

/-- The second map of the small Mayer–Vietoris sequence of the cover `(U,V)`:
`C(U) ⊞ C(V) ⟶ C^{U,V}(X)`. -/
def mvRightSmall (U V : Set X) :
    smallInChains U V U ⊞ smallInChains U V V ⟶ smallChains U V :=
  biprod.desc (smallInToSmall U V U) (-(smallInToSmall U V V))

/-- The composite of the two Mayer–Vietoris maps of the row `(U,V)` is zero. -/
theorem mvCompSmall (U V : Set X) : mvLeftSmall U V ≫ mvRightSmall U V = 0 := by
  rw [mvLeftSmall, mvRightSmall, biprod.lift_desc]
  rw [Preadditive.comp_neg,
    subInclChain_smallInToSmall U V (show U ∩ V ⊆ U from fun x hx => hx.1),
    subInclChain_smallInToSmall U V (show U ∩ V ⊆ V from fun x hx => hx.2)]
  simp

/-- The first map of the small Mayer–Vietoris sequence of the cover `(U ∩ A, V ∩ A)`:
`C(U ∩ V ∩ A) ⟶ C(U ∩ A) ⊞ C(V ∩ A)` (all small chains with respect to the pair `(U,V)`). -/
def mvLeftSmallA (U V A : Set X) :
    smallInChains U V (U ∩ V ∩ A) ⟶ smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) :=
  biprod.lift (subInclChain U V (by intro x hx; exact ⟨hx.1.1, hx.2⟩))
    (subInclChain U V (by intro x hx; exact ⟨hx.1.2, hx.2⟩))

/-- The second map of the small Mayer–Vietoris sequence of the cover `(U ∩ A, V ∩ A)`:
`C(U ∩ A) ⊞ C(V ∩ A) ⟶ C(A)`. -/
def mvRightSmallA (U V A : Set X) :
    smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶ smallInChains U V A :=
  biprod.desc (subInclChain U V (by intro x hx; exact hx.2))
    (-(subInclChain U V (by intro x hx; exact hx.2)))

/-- The composite of the two Mayer–Vietoris maps of the row `(U ∩ A, V ∩ A)` is zero. -/
theorem mvCompSmallA (U V A : Set X) : mvLeftSmallA U V A ≫ mvRightSmallA U V A = 0 := by
  rw [mvLeftSmallA, mvRightSmallA, biprod.lift_desc]
  have h₁ := subInclChain_comp U V
    (show U ∩ V ∩ A ⊆ U ∩ A from fun x hx => ⟨hx.1.1, hx.2⟩)
    (show U ∩ A ⊆ A from fun x hx => hx.2)
  have h₂ := subInclChain_comp U V
    (show U ∩ V ∩ A ⊆ V ∩ A from fun x hx => ⟨hx.1.2, hx.2⟩)
    (show V ∩ A ⊆ A from fun x hx => hx.2)
  rw [Preadditive.comp_neg, h₁, h₂]
  simp

/-! ## 4. Degreewise computations -/

/-- The degreewise component of a `biprod.lift`, conjugated by the degreewise biproduct
isomorphism. -/
lemma biprod_lift_f_comp_biprodXIso_hom {K L M : ChainComplex (ModuleCat ℤ) ℕ}
    (α : M ⟶ K) (β : M ⟶ L) (n : ℕ) :
    (biprod.lift α β).f n ≫ (HomologicalComplex.biprodXIso K L n).hom
      = biprod.lift (α.f n) (β.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      HomologicalComplex.biprod_lift_fst_f, biprod.lift_fst]
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      HomologicalComplex.biprod_lift_snd_f, biprod.lift_snd]

/-- The degreewise component of a `biprod.desc`, conjugated by the degreewise biproduct
isomorphism. -/
lemma biprodXIso_inv_comp_desc_f {K L M : ChainComplex (ModuleCat ℤ) ℕ}
    (α : K ⟶ M) (β : L ⟶ M) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).inv ≫ (biprod.desc α β).f n
      = biprod.desc (α.f n) (β.f n) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      HomologicalComplex.biprod_inl_desc_f, biprod.inl_desc]
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      HomologicalComplex.biprod_inr_desc_f, biprod.inr_desc]

/-- The `inl` component of the second Mayer–Vietoris map. -/
lemma mvRightSmall_inl_eval (U V : Set X) (n : ℕ) (a : (smallInChains U V U).X n) :
    (mvRightSmall U V).f n ((biprod.inl : smallInChains U V U ⟶
        smallInChains U V U ⊞ smallInChains U V V).f n a)
      = coprodMap (idxUsm U V n) a := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvRightSmall]
  rw [HomologicalComplex.biprod_inl_desc_f]
  rfl

/-- The `inr` component of the second Mayer–Vietoris map. -/
lemma mvRightSmall_inr_eval (U V : Set X) (n : ℕ) (b : (smallInChains U V V).X n) :
    (mvRightSmall U V).f n ((biprod.inr : smallInChains U V V ⟶
        smallInChains U V U ⊞ smallInChains U V V).f n b)
      = -(coprodMap (idxVsm U V n) b) := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvRightSmall]
  rw [HomologicalComplex.biprod_inr_desc_f]
  rfl

/-- The `fst` component of the first Mayer–Vietoris map. -/
lemma mvLeftSmall_eval_fst (U V : Set X) (n : ℕ) (y : (smallInChains U V (U ∩ V)).X n) :
    (biprod.fst : smallInChains U V U ⊞ smallInChains U V V ⟶ smallInChains U V U).f n
        ((mvLeftSmall U V).f n y) = coprodMap (idxUVU U V n) y := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvLeftSmall]
  rw [HomologicalComplex.biprod_lift_fst_f]
  rfl

/-- The `snd` component of the first Mayer–Vietoris map. -/
lemma mvLeftSmall_eval_snd (U V : Set X) (n : ℕ) (y : (smallInChains U V (U ∩ V)).X n) :
    (biprod.snd : smallInChains U V U ⊞ smallInChains U V V ⟶ smallInChains U V V).f n
        ((mvLeftSmall U V).f n y) = coprodMap (idxUVV U V n) y := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvLeftSmall]
  rw [HomologicalComplex.biprod_lift_snd_f]
  rfl

/-- The morphism `coprodMap` with coefficients pinned to `ℤ`. -/
def coprodMapZ {A S : Type} (f : A → S) : mvCoprodMod A ⟶ mvCoprodMod S := coprodMap f

/-- A generic degreewise Mayer–Vietoris short exactness statement: the abstract input
(`coprod_shortExact`) applied to a degree. -/
theorem coprodShortComplex_shortExact {A B C S : Type} (γ : C → A) (δ : C → B) (α : A → S)
    (β : B → S) (hγ : Function.Injective γ) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hcomm : α ∘ γ = β ∘ δ)
    (hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b)
    (hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s)) :
    (coprodShortComplex (R := ℤ) γ δ α β hcomm).ShortExact :=
  coprod_shortExact ℤ γ δ α β hγ hα hβ hcomm hpb hcov

/-- The `inl` component of the second Mayer–Vietoris map of the row `(U ∩ A, V ∩ A)`. -/
lemma mvRightSmallA_inl_eval (U V A : Set X) (n : ℕ) (a : (smallInChains U V (U ∩ A)).X n) :
    (mvRightSmallA U V A).f n ((biprod.inl : smallInChains U V (U ∩ A) ⟶
        smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A)).f n a)
      = coprodMap (idxAU U V A n) a := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvRightSmallA]
  rw [HomologicalComplex.biprod_inl_desc_f]
  rfl

/-- The `inr` component of the second Mayer–Vietoris map of the row `(U ∩ A, V ∩ A)`. -/
lemma mvRightSmallA_inr_eval (U V A : Set X) (n : ℕ) (b : (smallInChains U V (V ∩ A)).X n) :
    (mvRightSmallA U V A).f n ((biprod.inr : smallInChains U V (V ∩ A) ⟶
        smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A)).f n b)
      = -(coprodMap (idxAV U V A n) b) := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvRightSmallA]
  rw [HomologicalComplex.biprod_inr_desc_f]
  rfl

/-- The `fst` component of the first Mayer–Vietoris map of the row `(U ∩ A, V ∩ A)`. -/
lemma mvLeftSmallA_eval_fst (U V A : Set X) (n : ℕ) (y : (smallInChains U V (U ∩ V ∩ A)).X n) :
    (biprod.fst : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (U ∩ A)).f n ((mvLeftSmallA U V A).f n y)
      = coprodMap (idxA1 U V A n) y := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvLeftSmallA]
  rw [HomologicalComplex.biprod_lift_fst_f]
  rfl

/-- The `snd` component of the first Mayer–Vietoris map of the row `(U ∩ A, V ∩ A)`. -/
lemma mvLeftSmallA_eval_snd (U V A : Set X) (n : ℕ) (y : (smallInChains U V (U ∩ V ∩ A)).X n) :
    (biprod.snd : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (V ∩ A)).f n ((mvLeftSmallA U V A).f n y)
      = coprodMap (idxA2 U V A n) y := by
  rw [← ConcreteCategory.comp_apply]
  dsimp only [mvLeftSmallA]
  rw [HomologicalComplex.biprod_lift_snd_f]
  rfl

/-- **Degreewise short exactness of the Mayer–Vietoris row `(U,V)`.** -/
theorem mvSmall_degreewise (U V : Set X) (n : ℕ) :
    ((ShortComplex.mk (mvLeftSmall U V) (mvRightSmall U V) (mvCompSmall U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact := by
  let γ : (smallInSSet U V (U ∩ V)) _⦋n⦌ → (smallInSSet U V U) _⦋n⦌ := idxUVU U V n
  let δ : (smallInSSet U V (U ∩ V)) _⦋n⦌ → (smallInSSet U V V) _⦋n⦌ := idxUVV U V n
  let α : (smallInSSet U V U) _⦋n⦌ → (smallSSet U V) _⦋n⦌ := idxUsm U V n
  let β : (smallInSSet U V V) _⦋n⦌ → (smallSSet U V) _⦋n⦌ := idxVsm U V n
  have hcomm : α ∘ γ = β ∘ δ := by funext c; exact Subtype.ext rfl
  have hγ : Function.Injective γ := by
    intro a b hab
    have ha : (γ a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
    have hb : (γ b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
    exact Subtype.ext (by rw [← ha, ← hb, hab])
  have hα : Function.Injective α := by
    intro a b hab
    have ha : (α a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
    have hb : (α b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
    exact Subtype.ext (by rw [← ha, ← hb, hab])
  have hβ : Function.Injective β := by
    intro a b hab
    have ha : (β a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
    have hb : (β b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
    exact Subtype.ext (by rw [← ha, ← hb, hab])
  have hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b := by
    intro a b hab
    have h1 : (a.1 : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := by
      have h2 : (α a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
      have h3 : (β b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
      rw [← h2, ← h3, hab]
    refine ⟨⟨a.1, ⟨a.2.1, fun x hx => ⟨a.2.2 hx, ?_⟩⟩⟩, Subtype.ext rfl, Subtype.ext h1⟩
    exact b.2.2 (by rw [h1] at hx; exact hx)
  have hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s) := by
    intro s
    have hs : Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) s.1 z) ⊆ U ∨
      Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) s.1 z) ⊆ V := s.2
    rcases hs with h | h
    · exact Or.inl ⟨⟨s.1, ⟨s.2, h⟩⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨⟨s.1, ⟨s.2, h⟩⟩, Subtype.ext rfl⟩
  have hT : (coprodShortComplex (R := ℤ) γ δ α β hcomm).ShortExact :=
    coprodShortComplex_shortExact γ δ α β hγ hα hβ hcomm hpb hcov
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- exactness
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    let a : (smallInChains U V U).X n :=
      ((biprod.fst : smallInChains U V U ⊞ smallInChains U V V ⟶ smallInChains U V U).f n) x₂
    let b : (smallInChains U V V).X n :=
      ((biprod.snd : smallInChains U V U ⊞ smallInChains U V V ⟶ smallInChains U V V).f n) x₂
    have hx : x₂ = (biprod.inl : smallInChains U V U ⟶
        smallInChains U V U ⊞ smallInChains U V V).f n a
        + (biprod.inr : smallInChains U V V ⟶
        smallInChains U V U ⊞ smallInChains U V V).f n b := by rw [biprodX_total_apply x₂]
    have hab : coprodMapZ α a = coprodMapZ β b := by
      have h1 : (mvRightSmall U V).f n x₂ = 0 := hx₂
      rw [hx, map_add] at h1
      rw [mvRightSmall_inl_eval, mvRightSmall_inr_eval] at h1
      rw [show coprodMap (idxUsm U V n) a = coprodMapZ α a from rfl,
        show coprodMap (idxVsm U V n) b = coprodMapZ β b from rfl] at h1
      refine sub_eq_zero.mp ?_
      rw [sub_eq_add_neg]
      exact h1
    have hg0 : (coprodShortComplex (R := ℤ) γ δ α β hcomm).g
        ((biprod.inl : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) a
        + (biprod.inr : mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) b) = 0 := by
      rw [show (coprodShortComplex (R := ℤ) γ δ α β hcomm).g
          ((biprod.inl : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) a
          + (biprod.inr : mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) b)
        = coprodMap α a - coprodMap β b from coprodShortComplex_g_eval γ δ α β hcomm a b]
      rw [show coprodMap α a = coprodMapZ α a from rfl,
        show coprodMap β b = coprodMapZ β b from rfl, hab, sub_self]
    obtain ⟨y₁, hy₁⟩ := (ShortComplex.moduleCat_exact_iff
      (coprodShortComplex (R := ℤ) γ δ α β hcomm)).1 hT.exact
      ((biprod.inl : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) a
        + (biprod.inr : mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) b) hg0
    refine ⟨y₁, ?_⟩
    have hy₁' : biprod.lift (coprodMapZ γ) (coprodMapZ δ) y₁
        = (biprod.inl : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) a
          + (biprod.inr : mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞ mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) b := hy₁
    have hfst : (biprod.fst : smallInChains U V U ⊞ smallInChains U V V ⟶
        smallInChains U V U).f n ((mvLeftSmall U V).f n y₁) =
        (biprod.fst : smallInChains U V U ⊞ smallInChains U V V ⟶
        smallInChains U V U).f n x₂ := by
      calc (biprod.fst : smallInChains U V U ⊞ smallInChains U V V ⟶
              smallInChains U V U).f n ((mvLeftSmall U V).f n y₁)
          = coprodMap (idxUVU U V n) y₁ := mvLeftSmall_eval_fst U V n y₁
        _ = (biprod.fst : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V U) _⦋n⦌))
              (biprod.lift (coprodMapZ γ) (coprodMapZ δ) y₁) := by
            rw [← ConcreteCategory.comp_apply, biprod.lift_fst]
            rfl
        _ = (biprod.fst : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V U) _⦋n⦌))
              ((biprod.inl : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
                mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) a
              + (biprod.inr : mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
                mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) b) := by rw [hy₁']
        _ = a := by rw [map_add, biprod_fst_inl_apply, biprod_fst_inr_apply, add_zero]
        _ = (biprod.fst : smallInChains U V U ⊞ smallInChains U V V ⟶
              smallInChains U V U).f n x₂ := rfl
    have hsnd : (biprod.snd : smallInChains U V U ⊞ smallInChains U V V ⟶
        smallInChains U V V).f n ((mvLeftSmall U V).f n y₁) =
        (biprod.snd : smallInChains U V U ⊞ smallInChains U V V ⟶
        smallInChains U V V).f n x₂ := by
      calc (biprod.snd : smallInChains U V U ⊞ smallInChains U V V ⟶
              smallInChains U V V).f n ((mvLeftSmall U V).f n y₁)
          = coprodMap (idxUVV U V n) y₁ := mvLeftSmall_eval_snd U V n y₁
        _ = (biprod.snd : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V V) _⦋n⦌))
              (biprod.lift (coprodMapZ γ) (coprodMapZ δ) y₁) := by
            rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
            rfl
        _ = (biprod.snd : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V V) _⦋n⦌))
              ((biprod.inl : mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
                mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) a
              + (biprod.inr : mvCoprodMod ((smallInSSet U V V) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V U) _⦋n⦌) ⊞
                mvCoprodMod ((smallInSSet U V V) _⦋n⦌)) b) := by rw [hy₁']
        _ = b := by rw [map_add, biprod_snd_inl_apply, biprod_snd_inr_apply, zero_add]
        _ = (biprod.snd : smallInChains U V U ⊞ smallInChains U V V ⟶
              smallInChains U V V).f n x₂ := rfl
    exact biprodX_ext_apply hfst hsnd
  · -- mono
    have hconj : (mvLeftSmall U V).f n ≫ (HomologicalComplex.biprodXIso
        (smallInChains U V U) (smallInChains U V V) n).hom
        = biprod.lift (coprodMapZ γ) (coprodMapZ δ) := by
      rw [mvLeftSmall, biprod_lift_f_comp_biprodXIso_hom]
      rfl
    haveI : Mono ((mvLeftSmall U V).f n ≫ (HomologicalComplex.biprodXIso
        (smallInChains U V U) (smallInChains U V V) n).hom) := by
      rw [hconj]; exact hT.mono_f
    exact mono_of_mono ((mvLeftSmall U V).f n) ((HomologicalComplex.biprodXIso
      (smallInChains U V U) (smallInChains U V V) n).hom)
  · -- epi
    have hconj : (HomologicalComplex.biprodXIso (smallInChains U V U)
        (smallInChains U V V) n).inv ≫ (mvRightSmall U V).f n
        = biprod.desc (coprodMapZ α) (-(coprodMapZ β)) := by
      rw [mvRightSmall, biprodXIso_inv_comp_desc_f]
      rfl
    haveI : Epi ((HomologicalComplex.biprodXIso (smallInChains U V U)
        (smallInChains U V V) n).inv ≫ (mvRightSmall U V).f n) := by
      rw [hconj]; exact hT.epi_g
    exact epi_of_epi ((HomologicalComplex.biprodXIso (smallInChains U V U)
      (smallInChains U V V) n).inv) ((mvRightSmall U V).f n)

/-- **The small Mayer–Vietoris sequence of the cover `(U,V)` is short exact.** -/
theorem mvSmall_shortExact (U V : Set X) :
    (ShortComplex.mk (mvLeftSmall U V) (mvRightSmall U V) (mvCompSmall U V)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => mvSmall_degreewise U V n)


/-- **Degreewise short exactness of the Mayer–Vietoris row `(U ∩ A, V ∩ A)`.** -/
theorem mvSmallA_degreewise (U V A : Set X) (n : ℕ) :
    ((ShortComplex.mk (mvLeftSmallA U V A) (mvRightSmallA U V A) (mvCompSmallA U V A)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact := by
  let γ : (smallInSSet U V (U ∩ V ∩ A)) _⦋n⦌ → (smallInSSet U V (U ∩ A)) _⦋n⦌ := idxA1 U V A n
  let δ : (smallInSSet U V (U ∩ V ∩ A)) _⦋n⦌ → (smallInSSet U V (V ∩ A)) _⦋n⦌ := idxA2 U V A n
  let α : (smallInSSet U V (U ∩ A)) _⦋n⦌ → (smallInSSet U V A) _⦋n⦌ := idxAU U V A n
  let β : (smallInSSet U V (V ∩ A)) _⦋n⦌ → (smallInSSet U V A) _⦋n⦌ := idxAV U V A n
  have hcomm : α ∘ γ = β ∘ δ := by funext c; exact Subtype.ext rfl
  have hγ : Function.Injective γ := by
    intro a b hab
    have ha : (γ a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
    have hb : (γ b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
    exact Subtype.ext (by rw [← ha, ← hb, hab])
  have hα : Function.Injective α := by
    intro a b hab
    have ha : (α a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
    have hb : (α b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
    exact Subtype.ext (by rw [← ha, ← hb, hab])
  have hβ : Function.Injective β := by
    intro a b hab
    have ha : (β a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
    have hb : (β b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
    exact Subtype.ext (by rw [← ha, ← hb, hab])
  have hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b := by
    intro a b hab
    have h1 : (a.1 : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := by
      have h2 : (α a : (TopCat.toSSet.obj X) _⦋n⦌) = a.1 := rfl
      have h3 : (β b : (TopCat.toSSet.obj X) _⦋n⦌) = b.1 := rfl
      rw [← h2, ← h3, hab]
    refine ⟨⟨a.1, ⟨a.2.1, fun x hx => ⟨⟨(a.2.2 hx).1, ?_⟩, (a.2.2 hx).2⟩⟩⟩,
      Subtype.ext rfl, Subtype.ext h1⟩
    exact (b.2.2 (by rw [h1] at hx; exact hx)).1
  have hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s) := by
    intro s
    have hs : Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) s.1 z) ⊆ U ∨
      Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) s.1 z) ⊆ V := s.2.1
    rcases hs with h | h
    · exact Or.inl ⟨⟨s.1, ⟨s.2.1, fun x hx => ⟨h hx, s.2.2 hx⟩⟩⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨⟨s.1, ⟨s.2.1, fun x hx => ⟨h hx, s.2.2 hx⟩⟩⟩, Subtype.ext rfl⟩
  have hT : (coprodShortComplex (R := ℤ) γ δ α β hcomm).ShortExact :=
    coprodShortComplex_shortExact γ δ α β hγ hα hβ hcomm hpb hcov
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- exactness
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    let a : (smallInChains U V (U ∩ A)).X n :=
      ((biprod.fst : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (U ∩ A)).f n) x₂
    let b : (smallInChains U V (V ∩ A)).X n :=
      ((biprod.snd : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (V ∩ A)).f n) x₂
    have hx : x₂ = (biprod.inl : smallInChains U V (U ∩ A) ⟶
        smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A)).f n a
        + (biprod.inr : smallInChains U V (V ∩ A) ⟶
        smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A)).f n b :=
      by rw [biprodX_total_apply x₂]
    have hab : coprodMapZ α a = coprodMapZ β b := by
      have h1 : (mvRightSmallA U V A).f n x₂ = 0 := hx₂
      rw [hx, map_add] at h1
      rw [mvRightSmallA_inl_eval, mvRightSmallA_inr_eval] at h1
      rw [show coprodMap (idxAU U V A n) a = coprodMapZ α a from rfl,
        show coprodMap (idxAV U V A n) b = coprodMapZ β b from rfl] at h1
      refine sub_eq_zero.mp ?_
      rw [sub_eq_add_neg]
      exact h1
    have hg0 : (coprodShortComplex (R := ℤ) γ δ α β hcomm).g
        ((biprod.inl : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
            mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) a
        + (biprod.inr : mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
            mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) b) = 0 := by
      rw [show (coprodShortComplex (R := ℤ) γ δ α β hcomm).g
          ((biprod.inl : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) a
          + (biprod.inr : mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) b)
        = coprodMap α a - coprodMap β b from coprodShortComplex_g_eval γ δ α β hcomm a b]
      rw [show coprodMap α a = coprodMapZ α a from rfl,
        show coprodMap β b = coprodMapZ β b from rfl, hab, sub_self]
    obtain ⟨y₁, hy₁⟩ := (ShortComplex.moduleCat_exact_iff
      (coprodShortComplex (R := ℤ) γ δ α β hcomm)).1 hT.exact
      ((biprod.inl : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
            mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) a
        + (biprod.inr : mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
          mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
            mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) b) hg0
    refine ⟨y₁, ?_⟩
    have hy₁' : biprod.lift (coprodMapZ γ) (coprodMapZ δ) y₁
        = (biprod.inl : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) a
          + (biprod.inr : mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
            mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) b := hy₁
    have hfst : (biprod.fst : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (U ∩ A)).f n ((mvLeftSmallA U V A).f n y₁) =
        (biprod.fst : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (U ∩ A)).f n x₂ := by
      calc (biprod.fst : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
              smallInChains U V (U ∩ A)).f n ((mvLeftSmallA U V A).f n y₁)
          = coprodMap (idxA1 U V A n) y₁ := mvLeftSmallA_eval_fst U V A n y₁
        _ = (biprod.fst : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌))
              (biprod.lift (coprodMapZ γ) (coprodMapZ δ) y₁) := by
            rw [← ConcreteCategory.comp_apply, biprod.lift_fst]
            rfl
        _ = (biprod.fst : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌))
              ((biprod.inl : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
                  mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) a
              + (biprod.inr : mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
                  mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) b) := by rw [hy₁']
        _ = a := by rw [map_add, biprod_fst_inl_apply, biprod_fst_inr_apply, add_zero]
        _ = (biprod.fst : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
              smallInChains U V (U ∩ A)).f n x₂ := rfl
    have hsnd : (biprod.snd : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (V ∩ A)).f n ((mvLeftSmallA U V A).f n y₁) =
        (biprod.snd : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
        smallInChains U V (V ∩ A)).f n x₂ := by
      calc (biprod.snd : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
              smallInChains U V (V ∩ A)).f n ((mvLeftSmallA U V A).f n y₁)
          = coprodMap (idxA2 U V A n) y₁ := mvLeftSmallA_eval_snd U V A n y₁
        _ = (biprod.snd : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌))
              (biprod.lift (coprodMapZ γ) (coprodMapZ δ) y₁) := by
            rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
            rfl
        _ = (biprod.snd : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
              mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌))
              ((biprod.inl : mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
                  mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) a
              + (biprod.inr : mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌) ⟶
                mvCoprodMod ((smallInSSet U V (U ∩ A)) _⦋n⦌) ⊞
                  mvCoprodMod ((smallInSSet U V (V ∩ A)) _⦋n⦌)) b) := by rw [hy₁']
        _ = b := by rw [map_add, biprod_snd_inl_apply, biprod_snd_inr_apply, zero_add]
        _ = (biprod.snd : smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
              smallInChains U V (V ∩ A)).f n x₂ := rfl
    exact biprodX_ext_apply hfst hsnd
  · -- mono
    have hconj : (mvLeftSmallA U V A).f n ≫ (HomologicalComplex.biprodXIso
        (smallInChains U V (U ∩ A)) (smallInChains U V (V ∩ A)) n).hom
        = biprod.lift (coprodMapZ γ) (coprodMapZ δ) := by
      rw [mvLeftSmallA, biprod_lift_f_comp_biprodXIso_hom]
      rfl
    haveI : Mono ((mvLeftSmallA U V A).f n ≫ (HomologicalComplex.biprodXIso
        (smallInChains U V (U ∩ A)) (smallInChains U V (V ∩ A)) n).hom) := by
      rw [hconj]; exact hT.mono_f
    exact mono_of_mono ((mvLeftSmallA U V A).f n) ((HomologicalComplex.biprodXIso
      (smallInChains U V (U ∩ A)) (smallInChains U V (V ∩ A)) n).hom)
  · -- epi
    have hconj : (HomologicalComplex.biprodXIso (smallInChains U V (U ∩ A))
        (smallInChains U V (V ∩ A)) n).inv ≫ (mvRightSmallA U V A).f n
        = biprod.desc (coprodMapZ α) (-(coprodMapZ β)) := by
      rw [mvRightSmallA, biprodXIso_inv_comp_desc_f]
      rfl
    haveI : Epi ((HomologicalComplex.biprodXIso (smallInChains U V (U ∩ A))
        (smallInChains U V (V ∩ A)) n).inv ≫ (mvRightSmallA U V A).f n) := by
      rw [hconj]; exact hT.epi_g
    exact epi_of_epi ((HomologicalComplex.biprodXIso (smallInChains U V (U ∩ A))
      (smallInChains U V (V ∩ A)) n).inv) ((mvRightSmallA U V A).f n)

/-- **The small Mayer–Vietoris sequence of the cover `(U ∩ A, V ∩ A)` is short exact.** -/
theorem mvSmallA_shortExact (U V A : Set X) :
    (ShortComplex.mk (mvLeftSmallA U V A) (mvRightSmallA U V A) (mvCompSmallA U V A)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => mvSmallA_degreewise U V A n)


/-! ## 6. The relative Mayer–Vietoris short exact sequence -/

/-- The biproduct of two monomorphisms of a preadditive category is a monomorphism. -/
lemma mono_biprod_map {C : Type*} [Category C] [Preadditive C] {A B A' B' : C}
    [HasBinaryBiproduct A A'] [HasBinaryBiproduct B B'] {f : A ⟶ B} {g : A' ⟶ B'}
    (hf : Mono f) (hg : Mono g) : Mono (biprod.map f g) := by
  have h1 : ∀ {Z : C} (u : Z ⟶ A ⊞ A'), u ≫ biprod.map f g = 0 → u ≫ biprod.fst = 0 := by
    intro Z u hu
    rw [← cancel_mono f]
    rw [Category.assoc]
    rw [show (biprod.fst : A ⊞ A' ⟶ A) ≫ f = biprod.map f g ≫ (biprod.fst : B ⊞ B' ⟶ B)
      from (biprod.map_fst f g).symm]
    rw [← Category.assoc, hu, zero_comp, zero_comp]
  have h2 : ∀ {Z : C} (u : Z ⟶ A ⊞ A'), u ≫ biprod.map f g = 0 → u ≫ biprod.snd = 0 := by
    intro Z u hu
    rw [← cancel_mono g]
    rw [Category.assoc]
    rw [show (biprod.snd : A ⊞ A' ⟶ A') ≫ g = biprod.map f g ≫ (biprod.snd : B ⊞ B' ⟶ B')
      from (biprod.map_snd f g).symm]
    rw [← Category.assoc, hu, zero_comp, zero_comp]
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z u hu
  have hu1 : u ≫ biprod.fst = 0 := h1 u hu
  have hu2 : u ≫ biprod.snd = 0 := h2 u hu
  have htot : (biprod.fst : A ⊞ A' ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ A')
      + (biprod.snd : A ⊞ A' ⟶ A') ≫ (biprod.inr : A' ⟶ A ⊞ A') = 𝟙 (A ⊞ A') := by
    have h := IsBilimit.binary_total (BinaryBiproduct.isBilimit A A')
    simpa [BinaryBiproduct.bicone_fst, BinaryBiproduct.bicone_snd, BinaryBiproduct.bicone_inl,
      BinaryBiproduct.bicone_inr] using h
  calc u = u ≫ 𝟙 (A ⊞ A') := (Category.comp_id u).symm
    _ = u ≫ ((biprod.fst : A ⊞ A' ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ A')
          + (biprod.snd : A ⊞ A' ⟶ A') ≫ (biprod.inr : A' ⟶ A ⊞ A')) := by rw [htot]
    _ = u ≫ ((biprod.fst : A ⊞ A' ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ A'))
          + u ≫ ((biprod.snd : A ⊞ A' ⟶ A') ≫ (biprod.inr : A' ⟶ A ⊞ A')) := by
          rw [Preadditive.comp_add]
    _ = (u ≫ biprod.fst) ≫ biprod.inl + (u ≫ biprod.snd) ≫ biprod.inr := by
          rw [← Category.assoc, ← Category.assoc]
    _ = 0 := by rw [hu1, hu2, zero_comp, zero_comp, add_zero]

/-- The inclusion `C(U ∩ V ∩ A) ⟶ C(U ∩ V)`. -/
def relMVτ₁ (U V A : Set X) : smallInChains U V (U ∩ V ∩ A) ⟶ smallInChains U V (U ∩ V) :=
  subInclChain U V Set.inter_subset_left

/-- The inclusion `C(U ∩ A) ⟶ C(U)`. -/
def relMVτ₂U (U V A : Set X) : smallInChains U V (U ∩ A) ⟶ smallInChains U V U :=
  subInclChain U V Set.inter_subset_left

/-- The inclusion `C(V ∩ A) ⟶ C(V)`. -/
def relMVτ₂V (U V A : Set X) : smallInChains U V (V ∩ A) ⟶ smallInChains U V V :=
  subInclChain U V Set.inter_subset_left

/-- The inclusion `C(A) ⟶ C^{U,V}(X)`. -/
def relMVτ₃ (U V A : Set X) : smallInChains U V A ⟶ smallChains U V :=
  smallInToSmall U V A

/-- **The vertical morphism of short complexes** from the `(U ∩ V ∩ A)`-row to the `(U ∩ V)`-row:
the inclusion of the small chains lying in `A` into the small chains of `(U,V)`. -/
def relMVv (U V A : Set X) :
    ShortComplex.mk (mvLeftSmallA U V A) (mvRightSmallA U V A) (mvCompSmallA U V A) ⟶
      ShortComplex.mk (mvLeftSmall U V) (mvRightSmall U V) (mvCompSmall U V) where
  τ₁ := relMVτ₁ U V A
  τ₂ := biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)
  τ₃ := relMVτ₃ U V A
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [mvLeftSmall, mvLeftSmallA, relMVτ₁, relMVτ₂U, Category.assoc,
        biprod.lift_fst_assoc, biprod.lift_fst, biprod.map_fst, subInclChain_comp]
    · simp only [mvLeftSmall, mvLeftSmallA, relMVτ₁, relMVτ₂V, Category.assoc,
        biprod.lift_snd_assoc, biprod.lift_snd, biprod.map_snd, subInclChain_comp]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [mvRightSmall, mvRightSmallA, relMVτ₂U, relMVτ₃, Category.assoc,
        biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc,
        subInclChain_smallInToSmall]
    · simp only [mvRightSmall, mvRightSmallA, relMVτ₂V, relMVτ₃, Category.assoc,
        biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
        Preadditive.comp_neg, Preadditive.neg_comp, subInclChain_smallInToSmall]

/-- **The relative Mayer–Vietoris sequence is short exact.** -/
theorem relMV_shortExact (X : TopCat) (A U V : Set X) :
    ∃ (f : Work.Cohomology.relSmallChains U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left ⟶
          CategoryTheory.Limits.biprod
            (Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left)
            (Work.Cohomology.relSmallChains U V V (V ∩ A) Set.inter_subset_left))
      (g : CategoryTheory.Limits.biprod
            (Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left)
            (Work.Cohomology.relSmallChains U V V (V ∩ A) Set.inter_subset_left) ⟶
          Work.Cohomology.relSmallTop U V A)
      (h : CategoryTheory.CategoryStruct.comp f g = 0),
      (CategoryTheory.ShortComplex.mk f g h).ShortExact := by
  obtain ⟨f₀, g₀, h₀, hS₀⟩ := cokernel_map_shortExact
    (mvSmallA_shortExact U V A) (mvSmall_shortExact U V) (relMVv U V A)
    (mono_subInclChain U V Set.inter_subset_left)
    (mono_biprod_map (mono_subInclChain U V Set.inter_subset_left)
      (mono_subInclChain U V Set.inter_subset_left))
    (mono_smallInToSmall U V A)
  obtain ⟨e⟩ := cokernel_biprod_map_iso (relMVτ₂U U V A) (relMVτ₂V U V A)
  have hzero : (f₀ ≫ e.hom) ≫ (e.inv ≫ g₀) = 0 := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, h₀]
  have hiso : (ShortComplex.mk f₀ g₀ h₀) ≅
      (ShortComplex.mk (f₀ ≫ e.hom) (e.inv ≫ g₀) hzero) :=
    ShortComplex.isoMk (Iso.refl _) e (Iso.refl _)
      (by rw [show (Iso.refl _).hom = 𝟙 _ from rfl, Category.id_comp])
      (by rw [show (Iso.refl _).hom = 𝟙 _ from rfl, Category.comp_id, Iso.hom_inv_id_assoc])
  exact ⟨f₀ ≫ e.hom, e.inv ≫ g₀, hzero, ShortComplex.shortExact_of_iso hiso hS₀⟩

end

end Work.Cohomology
