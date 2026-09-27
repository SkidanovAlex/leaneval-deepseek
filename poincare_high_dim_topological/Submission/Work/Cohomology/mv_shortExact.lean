import Mathlib
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mvComp
import Submission.Work.Cohomology.CoprodMVDefs
import Submission.Work.Cohomology.coprod_shortExact
import Submission.Work.Cohomology.smallLift_pullback
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Cohomology.smallLift_injective
import Submission.Work.Cohomology.inclUV_injective

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology
noncomputable section

variable {X : TopCat}

/-- The coproduct of copies of `ℤ` indexed by a type, as an object of `ModuleCat ℤ`. -/
abbrev mvCoprodMod (A : Type) : ModuleCat ℤ := ∐ (fun _ : A => ModuleCat.of ℤ ℤ)

/-! ## elementwise helpers for binary biproducts of modules -/

section BiprodElem

variable {M N P : ModuleCat ℤ} [HasBinaryBiproduct M N]

lemma biprod_total_apply (x : (M ⊞ N : ModuleCat ℤ)) :
    (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) x)
      + (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) x) = x := by
  have htot : (biprod.fst : M ⊞ N ⟶ M) ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (M ⊞ N) := by
    have := IsBilimit.binary_total (BinaryBiproduct.isBilimit M N)
    simpa [BinaryBiproduct.bicone_fst, BinaryBiproduct.bicone_snd, BinaryBiproduct.bicone_inl,
      BinaryBiproduct.bicone_inr] using this
  have h := congrArg (fun (f : (M ⊞ N : ModuleCat ℤ) ⟶ (M ⊞ N : ModuleCat ℤ)) => f x) htot
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at h
  exact h

lemma biprod_ext_apply {x y : (M ⊞ N : ModuleCat ℤ)}
    (h₁ : (biprod.fst : M ⊞ N ⟶ M) x = (biprod.fst : M ⊞ N ⟶ M) y)
    (h₂ : (biprod.snd : M ⊞ N ⟶ N) x = (biprod.snd : M ⊞ N ⟶ N) y) : x = y := by
  rw [← biprod_total_apply x, ← biprod_total_apply y, h₁, h₂]

lemma biprod_fst_inl_apply (a : M) :
    (biprod.fst : M ⊞ N ⟶ M) ((biprod.inl : M ⟶ M ⊞ N) a) = a := by
  have h := congrArg (fun (f : M ⟶ M) => f a) (biprod.inl_fst (X := M) (Y := N))
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

lemma biprod_snd_inl_apply (a : M) :
    (biprod.snd : M ⊞ N ⟶ N) ((biprod.inl : M ⟶ M ⊞ N) a) = 0 := by
  have h := congrArg (fun (f : M ⟶ N) => f a) (biprod.inl_snd (X := M) (Y := N))
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h

lemma biprod_fst_inr_apply (b : N) :
    (biprod.fst : M ⊞ N ⟶ M) ((biprod.inr : N ⟶ M ⊞ N) b) = 0 := by
  have h := congrArg (fun (f : N ⟶ M) => f b) (biprod.inr_fst (X := M) (Y := N))
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h

lemma biprod_snd_inr_apply (b : N) :
    (biprod.snd : M ⊞ N ⟶ N) ((biprod.inr : N ⟶ M ⊞ N) b) = b := by
  have h := congrArg (fun (f : N ⟶ N) => f b) (biprod.inr_snd (X := M) (Y := N))
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

lemma biprod_desc_inl_add_inr (f : M ⟶ P) (g : N ⟶ P) (a : M) (b : N) :
    (biprod.desc f g) ((biprod.inl : M ⟶ M ⊞ N) a + (biprod.inr : N ⟶ M ⊞ N) b)
      = f a + g b := by
  have h1 : (biprod.desc f g) ((biprod.inl : M ⟶ M ⊞ N) a) = f a :=
    congrArg (fun (k : M ⟶ P) => k a) (biprod.inl_desc f g)
  have h2 : (biprod.desc f g) ((biprod.inr : N ⟶ M ⊞ N) b) = g b :=
    congrArg (fun (k : N ⟶ P) => k b) (biprod.inr_desc f g)
  rw [map_add, h1, h2]

end BiprodElem

/-- The degreewise first map of the Mayer-Vietoris sequence, transported across the canonical
isomorphism `(K ⊞ L).X n ≅ K.X n ⊞ L.X n`. -/
lemma mvLeft_comp_biprodXIso (U V : Set X) (n : ℕ) :
    (mvLeft U V).f n ≫ (HomologicalComplex.biprodXIso (singularChains ℤ (TopCat.of U))
      (singularChains ℤ (TopCat.of V)) n).hom
      = biprod.lift (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)))
          (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌))) := by
  apply biprod.hom_ext
  · calc (((mvLeft U V).f n ≫ (HomologicalComplex.biprodXIso (singularChains ℤ (TopCat.of U))
        (singularChains ℤ (TopCat.of V)) n).hom) ≫ biprod.fst)
        = (mvLeft U V).f n ≫ (biprod.fst : singularChains ℤ (TopCat.of U) ⊞
            singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U)).f n := by
          rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst]
      _ = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)) :=
          HomologicalComplex.biprod_lift_fst_f (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)) (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n
      _ = biprod.lift (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)))
            (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌))) ≫ biprod.fst :=
          (biprod.lift_fst _ _).symm
  · calc (((mvLeft U V).f n ≫ (HomologicalComplex.biprodXIso (singularChains ℤ (TopCat.of U))
        (singularChains ℤ (TopCat.of V)) n).hom) ≫ biprod.snd)
        = (mvLeft U V).f n ≫ (biprod.snd : singularChains ℤ (TopCat.of U) ⊞
            singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of V)).f n := by
          rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd]
      _ = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌)) :=
          HomologicalComplex.biprod_lift_snd_f (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)) (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n
      _ = biprod.lift (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)))
            (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌))) ≫ biprod.snd :=
          (biprod.lift_snd _ _).symm


/-- The `fst`-component of the first Mayer-Vietoris map, at degree `n`. -/
lemma mvLeft_fst_apply (U V : Set X) (n : ℕ) :
    (mvLeft U V).f n ≫ (biprod.fst : singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U)).f n
      = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)) :=
  HomologicalComplex.biprod_lift_fst_f
    (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ))
    (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n

/-- The `snd`-component of the first Mayer-Vietoris map, at degree `n`. -/
lemma mvLeft_snd_apply (U V : Set X) (n : ℕ) :
    (mvLeft U V).f n ≫ (biprod.snd : singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of V)).f n
      = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌)) :=
  HomologicalComplex.biprod_lift_snd_f
    (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ))
    (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n

/-- The `inl`-component of the second Mayer-Vietoris map, at degree `n`. -/
lemma mvRight_inl_apply (U V : Set X) (n : ℕ) :
    (biprod.inl : singularChains ℤ (TopCat.of U) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n
      ≫ (biprod.desc (smallOfU U V) (-(smallOfV U V))).f n
      = (smallOfU U V).f n :=
  HomologicalComplex.biprod_inl_desc_f (smallOfU U V) (-(smallOfV U V)) n

/-- The `inr`-component of the second Mayer-Vietoris map, at degree `n`. -/
lemma mvRight_inr_apply (U V : Set X) (n : ℕ) :
    (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n
      ≫ (biprod.desc (smallOfU U V) (-(smallOfV U V))).f n
      = (-(smallOfV U V)).f n :=
  HomologicalComplex.biprod_inr_desc_f (smallOfU U V) (-(smallOfV U V)) n


section MoreHelpers

variable {K L : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ}

/-- Elementwise form of `HomologicalComplex.biprod_total_f`. -/
lemma biprodX_total_apply (x : (K ⊞ L : ChainComplex (ModuleCat ℤ) ℕ).X n) :
    (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n x)
      + (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n x) = x := by
  have htot := HomologicalComplex.biprod_total_f (K := K) (L := L) n
  have h := congrArg (fun (f : (K ⊞ L).X n ⟶ (K ⊞ L).X n) => f x) htot
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- Two elements of the degree-`n` part of a biproduct of complexes agree as soon as their
projections do. -/
lemma biprodX_ext_apply {x y : (K ⊞ L : ChainComplex (ModuleCat ℤ) ℕ).X n}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y := by
  rw [← biprodX_total_apply x, ← biprodX_total_apply y, h₁, h₂]

end MoreHelpers

section MoreHelpers2

variable {X : TopCat}

/-- The `inl`-component of `mvRight` composed with `mvRight` itself. -/
lemma mvRight_inl_apply' (U V : Set X) (n : ℕ) :
    (biprod.inl : singularChains ℤ (TopCat.of U) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n ≫ (mvRight U V).f n = (smallOfU U V).f n := by
  rw [show (mvRight U V) = biprod.desc (smallOfU U V) (-(smallOfV U V)) from rfl]
  exact HomologicalComplex.biprod_inl_desc_f (smallOfU U V) (-(smallOfV U V)) n

/-- The `inr`-component of `mvRight` composed with `mvRight` itself. -/
lemma mvRight_inr_apply' (U V : Set X) (n : ℕ) :
    (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n ≫ (mvRight U V).f n = (-(smallOfV U V)).f n := by
  rw [show (mvRight U V) = biprod.desc (smallOfU U V) (-(smallOfV U V)) from rfl]
  exact HomologicalComplex.biprod_inr_desc_f (smallOfU U V) (-(smallOfV U V)) n

end MoreHelpers2


section EvalHelpers

variable {X : TopCat}

lemma mvRight_inl_eval (U V : Set X) (n : ℕ) (a : (singularChains ℤ (TopCat.of U)).X n) :
    (mvRight U V).f n ((biprod.inl : singularChains ℤ (TopCat.of U) ⟶
        singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n a)
      = coprodMap (R:=ℤ) ((smallLiftU U V).app (Opposite.op ⦋n⦌)) a := by
  rw [← ConcreteCategory.comp_apply, mvRight_inl_apply']
  rfl

lemma mvRight_inr_eval (U V : Set X) (n : ℕ) (b : (singularChains ℤ (TopCat.of V)).X n) :
    (mvRight U V).f n ((biprod.inr : singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n b)
      = -(coprodMap (R:=ℤ) ((smallLiftV U V).app (Opposite.op ⦋n⦌)) b) := by
  rw [← ConcreteCategory.comp_apply, mvRight_inr_apply']
  rfl

lemma mvLeft_eval_fst (U V : Set X) (n : ℕ) (y : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X n) :
    (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n ((mvLeft U V).f n y)
      = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)) y := by
  rw [← ConcreteCategory.comp_apply, mvLeft_fst_apply]
  rfl

lemma mvLeft_eval_snd (U V : Set X) (n : ℕ) (y : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X n) :
    (biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n ((mvLeft U V).f n y)
      = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌)) y := by
  rw [← ConcreteCategory.comp_apply, mvLeft_snd_apply]
  rfl

lemma coprodShortComplex_g_eval {A B C S : Type} (γ : C → A) (δ : C → B) (α : A → S)
    (β : B → S) (hcomm : α ∘ γ = β ∘ δ) (a : mvCoprodMod A) (b : mvCoprodMod B) :
    (coprodShortComplex (R:=ℤ) γ δ α β hcomm).g
        ((biprod.inl : mvCoprodMod A ⟶ mvCoprodMod A ⊞ mvCoprodMod B) a
          + (biprod.inr : mvCoprodMod B ⟶ mvCoprodMod A ⊞ mvCoprodMod B) b)
      = coprodMap (R:=ℤ) α a - coprodMap (R:=ℤ) β b := by
  dsimp only [coprodShortComplex]
  rw [biprod_desc_inl_add_inr]
  rw [show (-(coprodMap (R:=ℤ) β)) b = -(coprodMap (R:=ℤ) β b) from rfl]
  rw [sub_eq_add_neg]

end EvalHelpers


theorem mv_degreewise (U V : Set X) (n : ℕ) :
    ((ShortComplex.mk (mvLeft U V) (mvRight U V) (mvComp U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact := by
  let n' : SimplexCategoryᵒᵖ := Opposite.op ⦋n⦌
  let γ : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).obj n' → (TopCat.toSSet.obj (TopCat.of U)).obj n' :=
    (TopCat.toSSet.map (inclUVU U V)).app n'
  let δ : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).obj n' → (TopCat.toSSet.obj (TopCat.of V)).obj n' :=
    (TopCat.toSSet.map (inclUVV U V)).app n'
  let α : (TopCat.toSSet.obj (TopCat.of U)).obj n' → (smallSSet U V).obj n' := (smallLiftU U V).app n'
  let β : (TopCat.toSSet.obj (TopCat.of V)).obj n' → (smallSSet U V).obj n' := (smallLiftV U V).app n'
  have hcomm : α ∘ γ = β ∘ δ := by
    have h := congrArg (fun (τ : TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)) ⟶ smallSSet U V) =>
        τ.app n') (smallLiftU_comp_inclUVU U V)
    funext c
    have hc := congrArg (fun (g : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).obj n' ⟶
        (smallSSet U V).obj n') => ConcreteCategory.hom g c) h
    simpa only [α, β, γ, δ, NatTrans.comp_app, types_comp_apply, Function.comp_apply] using hc
  have hγ : Function.Injective γ := by simpa only [γ] using (inclUV_injective U V n').1
  have hα : Function.Injective α := by simpa only [α] using (smallLift_injective U V n').1
  have hβ : Function.Injective β := by simpa only [β] using (smallLift_injective U V n').2
  have hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b := by
    intro a b hab
    exact smallLift_pullback U V n' a b hab
  have hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s) := fun s => smallLift_cov U V n' s
  have hT : (coprodShortComplex (R:=ℤ) γ δ α β hcomm).ShortExact :=
    coprod_shortExact ℤ γ δ α β hγ hα hβ hcomm hpb hcov
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Exact
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    let a : (singularChains ℤ (TopCat.of U)).X n :=
      ((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n) x₂
    let b : (singularChains ℤ (TopCat.of V)).X n :=
      ((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n) x₂
    have hx : x₂ = (biprod.inl : singularChains ℤ (TopCat.of U) ⟶
        singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n a
        + (biprod.inr : singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n b := by
      rw [biprodX_total_apply x₂]
    have hab : coprodMap (R:=ℤ) α a = coprodMap (R:=ℤ) β b := by
      have h1 : (mvRight U V).f n x₂ = 0 := hx₂
      rw [hx, map_add] at h1
      rw [mvRight_inl_eval, mvRight_inr_eval] at h1
      have h2 : coprodMap (R:=ℤ) α a - coprodMap (R:=ℤ) β b = 0 := by
        simpa only [α, β, sub_eq_add_neg] using h1
      exact sub_eq_zero.mp h2
    have hg0 : (coprodShortComplex (R:=ℤ) γ δ α β hcomm).g
        ((biprod.inl : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⟶
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) a
          + (biprod.inr : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) b) = 0 := by
      rw [coprodShortComplex_g_eval, hab, sub_self]
    obtain ⟨y₁, hy₁⟩ := (ShortComplex.moduleCat_exact_iff
      (coprodShortComplex (R:=ℤ) γ δ α β hcomm)).1 hT.exact
      ((biprod.inl : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⟶
          mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
          mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) a
        + (biprod.inr : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
          mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
          mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) b) hg0
    refine ⟨y₁, ?_⟩
    have hy₁' : biprod.lift (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app n'))
          (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app n')) y₁
        = (biprod.inl : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⟶
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) a
          + (biprod.inr : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
            mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) b := hy₁
    have hfst : (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n ((mvLeft U V).f n y₁) =
        (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n x₂ := by
      calc (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
              singularChains ℤ (TopCat.of U)).f n ((mvLeft U V).f n y₁)
          = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app n') y₁ :=
            mvLeft_eval_fst U V n y₁
        _ = (biprod.fst : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n'))
              (biprod.lift (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app n'))
                (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app n')) y₁) := by
            rw [← ConcreteCategory.comp_apply, biprod.lift_fst]
        _ = (biprod.fst : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n'))
              ((biprod.inl : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⟶
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) a
              + (biprod.inr : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) b) := by rw [hy₁']
        _ = a := by rw [map_add, biprod_fst_inl_apply, biprod_fst_inr_apply, add_zero]
        _ = (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
              singularChains ℤ (TopCat.of U)).f n x₂ := rfl
    have hsnd : (biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n ((mvLeft U V).f n y₁) =
        (biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n x₂ := by
      calc (biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
              singularChains ℤ (TopCat.of V)).f n ((mvLeft U V).f n y₁)
          = coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app n') y₁ :=
            mvLeft_eval_snd U V n y₁
        _ = (biprod.snd : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n'))
              (biprod.lift (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app n'))
                (coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app n')) y₁) := by
            rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
        _ = (biprod.snd : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
              mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n'))
              ((biprod.inl : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⟶
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) a
              + (biprod.inr : mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n') ⟶
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of U)).obj n') ⊞
                mvCoprodMod ((TopCat.toSSet.obj (TopCat.of V)).obj n')) b) := by rw [hy₁']
        _ = b := by rw [map_add, biprod_snd_inl_apply, biprod_snd_inr_apply, zero_add]
        _ = (biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
              singularChains ℤ (TopCat.of V)).f n x₂ := rfl
    exact biprodX_ext_apply hfst hsnd
  · -- Mono
    have hF := mvLeft_comp_biprodXIso U V n
    have h1 : Mono ((mvLeft U V).f n ≫ (HomologicalComplex.biprodXIso
        (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V)) n).hom) := by
      rw [hF]
      exact hT.mono_f
    rw [Preadditive.mono_iff_cancel_zero] at h1 ⊢
    intro Z u hu
    exact h1 Z u (by rw [← Category.assoc]; rw [show u ≫ (mvLeft U V).f n = 0 from hu]; rw [zero_comp])
  · -- Epi
    rw [Preadditive.epi_iff_cancel_zero]
    intro Z q hq
    apply Sigma.hom_ext
    intro s
    rcases hcov s with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have h1 : coprodMap (R:=ℤ) α ≫ q = 0 := by
        rw [show coprodMap (R:=ℤ) α = (smallOfU U V).f n from rfl]
        rw [show (smallOfU U V).f n = (biprod.inl : singularChains ℤ (TopCat.of U) ⟶
              singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n ≫
              (mvRight U V).f n from (mvRight_inl_apply' U V n).symm]
        rw [Category.assoc]
        rw [show (mvRight U V).f n ≫ q = 0 from hq]
        rw [comp_zero]
      rw [← ι_coprodMap (R:=ℤ) α a]
      simp only [Category.assoc, h1, zero_comp, comp_zero]
    · have h1 : coprodMap (R:=ℤ) β ≫ q = 0 := by
        have h2 : (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
            singularChains ℤ (TopCat.of V)).f n ≫ ((mvRight U V).f n ≫ q) = 0 := by
          rw [show (mvRight U V).f n ≫ q = 0 from hq, comp_zero]
        rw [← Category.assoc] at h2
        rw [mvRight_inr_apply'] at h2
        rw [show (-(smallOfV U V)).f n = -((smallOfV U V)).f n from rfl, Preadditive.neg_comp, neg_eq_zero,
          show (smallOfV U V).f n = coprodMap (R:=ℤ) β from rfl] at h2
        exact h2
      rw [← ι_coprodMap (R:=ℤ) β b]
      simp only [Category.assoc, h1, zero_comp, comp_zero]


/-- **The Mayer–Vietoris sequence is short exact.** -/
theorem mv_shortExact {X : TopCat} (U V : Set X) :
    (CategoryTheory.ShortComplex.mk (mvLeft U V) (mvRight U V) (mvComp U V)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => mv_degreewise U V n)

end
end Work.Cohomology
