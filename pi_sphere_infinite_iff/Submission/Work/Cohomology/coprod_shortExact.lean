import Mathlib
import Submission.Work.Cohomology.CoprodMVDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory Limits Classical

namespace Work.Cohomology

open Work.Cohomology

noncomputable section

/-! ## Auxiliary rewriting lemma -/

/-- Reassociation of `ι` composed with `coprodMap`. -/
lemma iota_coprodMap_comp {R : Type} [Ring R] {A S : Type} (f : A → S) (a : A) {X : ModuleCat R}
    (g : (∐ (fun _ : S => ModuleCat.of R R)) ⟶ X) :
    Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ (coprodMap (R:=R) f ≫ g)
      = Sigma.ι (fun _ : S => ModuleCat.of R R) (f a) ≫ g := by
  rw [← Category.assoc, ι_coprodMap]

/-! ## Retracting `coprodMap f` for injective `f` -/

variable {R : Type} [Ring R]

/-- The `s`-th component of a retraction of `coprodMap f` for an injective `f`. -/
def coprodRetractVal {A S : Type} (f : A → S) (s : S) :
    ModuleCat.of R R ⟶ (∐ (fun _ : A => ModuleCat.of R R)) :=
  if h : ∃ a, f a = s then Sigma.ι (fun _ : A => ModuleCat.of R R) (Classical.choose h) else 0

/-- For injective `f : A → S`, a retraction of `coprodMap f : ∐_A R ⟶ ∐_S R`. -/
def coprodRetract {A S : Type} (f : A → S) :
    (∐ (fun _ : S => ModuleCat.of R R)) ⟶ (∐ (fun _ : A => ModuleCat.of R R)) :=
  Sigma.desc (coprodRetractVal (R:=R) f)

lemma coprodRetractVal_eq {A S : Type} (f : A → S) (hf : Function.Injective f) (a : A) :
    coprodRetractVal (R:=R) f (f a) = Sigma.ι (fun _ : A => ModuleCat.of R R) a := by
  have hm : ∃ a', f a' = f a := ⟨a, rfl⟩
  simp only [coprodRetractVal]
  rw [dif_pos hm]
  exact congrArg (Sigma.ι (fun _ : A => ModuleCat.of R R)) (hf (Classical.choose_spec hm))

lemma coprodMap_coprodRetract {A S : Type} (f : A → S) (hf : Function.Injective f) :
    coprodMap (R:=R) f ≫ coprodRetract (R:=R) f = 𝟙 _ := by
  apply Sigma.hom_ext
  intro a
  rw [iota_coprodMap_comp (R:=R) f a (g := coprodRetract (R:=R) f)]
  simp only [coprodRetract]
  rw [Sigma.ι_desc, coprodRetractVal_eq f hf a]
  simp

lemma mono_coprodMap {A S : Type} (f : A → S) (hf : Function.Injective f) :
    Mono (coprodMap (R:=R) f) :=
  mono_of_mono_fac (coprodMap_coprodRetract (R:=R) f hf)

/-! ## The cokernel property -/

/-- The `s`-th component of the morphism `∐_S R ⟶ W` associated with a cofork datum. -/
def cokerDescVal {R : Type} [Ring R] {A B C S : Type} (γ : C → A) (δ : C → B) (α : A → S)
    (β : B → S) (hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s)) {W : ModuleCat R}
    (h : (∐ (fun _ : A => ModuleCat.of R R)) ⊞ (∐ (fun _ : B => ModuleCat.of R R)) ⟶ W)
    (s : S) : ModuleCat.of R R ⟶ W :=
  if hs : ∃ a, α a = s then
    Sigma.ι (fun _ : A => ModuleCat.of R R) (Classical.choose hs) ≫ (biprod.inl ≫ h)
  else
    Sigma.ι (fun _ : B => ModuleCat.of R R) (Classical.choose ((hcov s).resolve_left hs)) ≫
      (-(biprod.inr ≫ h))

lemma coprod_lift_desc_zero {R : Type} [Ring R] {A B C S : Type} (γ : C → A) (δ : C → B)
    (α : A → S) (β : B → S) (hcomm : α ∘ γ = β ∘ δ) :
    biprod.lift (coprodMap (R:=R) γ) (coprodMap (R:=R) δ) ≫
      biprod.desc (coprodMap (R:=R) α) (-(coprodMap (R:=R) β)) = 0 := by
  rw [biprod.lift_desc, coprodMap_comp (R:=R) γ α, Preadditive.comp_neg,
    coprodMap_comp (R:=R) δ β, ← hcomm]
  simp

lemma iota_cokerDescVal_alpha {R : Type} [Ring R] {A B C S : Type} (γ : C → A) (δ : C → B)
    (α : A → S) (β : B → S) (hα : Function.Injective α)
    (hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s)) {W : ModuleCat R}
    (h : (∐ (fun _ : A => ModuleCat.of R R)) ⊞ (∐ (fun _ : B => ModuleCat.of R R)) ⟶ W)
    (a : A) :
    Sigma.ι (fun _ : S => ModuleCat.of R R) (α a) ≫
        Sigma.desc (cokerDescVal (R:=R) γ δ α β hcov h)
      = Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ (biprod.inl ≫ h) := by
  rw [Sigma.ι_desc]
  have hm : ∃ a', α a' = α a := ⟨a, rfl⟩
  have hv : cokerDescVal (R:=R) γ δ α β hcov h (α a)
      = Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ (biprod.inl ≫ h) := by
    simp only [cokerDescVal]
    rw [dif_pos hm]
    exact congrArg (fun a' => Sigma.ι (fun _ : A => ModuleCat.of R R) a' ≫ (biprod.inl ≫ h))
      (hα (Classical.choose_spec hm))
  rw [hv]

lemma iota_cokerDescVal_beta {R : Type} [Ring R] {A B C S : Type} (γ : C → A) (δ : C → B)
    (α : A → S) (β : B → S) (hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b)
    (hβ : Function.Injective β)
    (hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s)) {W : ModuleCat R}
    (h : (∐ (fun _ : A => ModuleCat.of R R)) ⊞ (∐ (fun _ : B => ModuleCat.of R R)) ⟶ W)
    (hh : biprod.lift (coprodMap (R:=R) γ) (coprodMap (R:=R) δ) ≫ h = 0) (b : B) :
    Sigma.ι (fun _ : S => ModuleCat.of R R) (β b) ≫
        Sigma.desc (cokerDescVal (R:=R) γ δ α β hcov h)
      = -(Sigma.ι (fun _ : B => ModuleCat.of R R) b ≫ (biprod.inr ≫ h)) := by
  rw [Sigma.ι_desc]
  by_cases hb : ∃ a, α a = β b
  · have hv : cokerDescVal (R:=R) γ δ α β hcov h (β b)
        = Sigma.ι (fun _ : A => ModuleCat.of R R) (Classical.choose hb) ≫ (biprod.inl ≫ h) := by
      simp only [cokerDescVal]
      rw [dif_pos hb]
    rw [hv]
    obtain ⟨c, hc1, hc2⟩ := hpb (Classical.choose hb) b (Classical.choose_spec hb)
    have h1 : coprodMap (R:=R) γ ≫ (biprod.inl ≫ h)
        + coprodMap (R:=R) δ ≫ (biprod.inr ≫ h) = 0 := by
      have h2 := hh
      rw [biprod.lift_eq, Preadditive.add_comp] at h2
      simpa only [Category.assoc] using h2
    have h3 : coprodMap (R:=R) γ ≫ (biprod.inl ≫ h)
        = -(coprodMap (R:=R) δ ≫ (biprod.inr ≫ h)) :=
      eq_neg_of_add_eq_zero_left h1
    have h5 := congrArg (fun m => Sigma.ι (fun _ : C => ModuleCat.of R R) c ≫ m) h3
    rw [Preadditive.comp_neg, iota_coprodMap_comp (R:=R) γ c (g := biprod.inl ≫ h), hc1,
      iota_coprodMap_comp (R:=R) δ c (g := biprod.inr ≫ h), hc2] at h5
    exact h5
  · have hv : cokerDescVal (R:=R) γ δ α β hcov h (β b)
        = Sigma.ι (fun _ : B => ModuleCat.of R R) b ≫ (-(biprod.inr ≫ h)) := by
      simp only [cokerDescVal]
      rw [dif_neg hb]
      rw [hβ (Classical.choose_spec ((hcov (β b)).resolve_left hb))]
    rw [hv]
    simp

/-- The morphism `g = (α_*, -β_*)` is the cokernel of `f = (γ_*, δ_*)`. -/
def coker_isColimit {R : Type} [Ring R] {A B C S : Type} (γ : C → A) (δ : C → B)
    (α : A → S) (β : B → S)
    (hcomm : α ∘ γ = β ∘ δ)
    (hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s)) :
    IsColimit (CokernelCofork.ofπ (biprod.desc (coprodMap (R:=R) α) (-(coprodMap (R:=R) β)))
      (coprod_lift_desc_zero (R:=R) γ δ α β hcomm)) := by
  classical
  refine Cofork.IsColimit.mk
    (CokernelCofork.ofπ (biprod.desc (coprodMap (R:=R) α) (-(coprodMap (R:=R) β)))
      (coprod_lift_desc_zero (R:=R) γ δ α β hcomm))
    (fun s => Sigma.desc (cokerDescVal (R:=R) γ δ α β hcov s.π)) ?_ ?_
  · intro s
    have hh : biprod.lift (coprodMap (R:=R) γ) (coprodMap (R:=R) δ) ≫ s.π = 0 := by
      have h := s.condition
      rw [zero_comp] at h
      exact h
    rw [CokernelCofork.π_ofπ]
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc]
      apply Sigma.hom_ext
      intro a
      rw [iota_coprodMap_comp (R:=R) α a
        (g := Sigma.desc (cokerDescVal (R:=R) γ δ α β hcov s.π))]
      exact iota_cokerDescVal_alpha (R:=R) γ δ α β hα hcov s.π a
    · rw [← Category.assoc, biprod.inr_desc]
      apply Sigma.hom_ext
      intro b
      rw [Preadditive.neg_comp, Preadditive.comp_neg,
        iota_coprodMap_comp (R:=R) β b
          (g := Sigma.desc (cokerDescVal (R:=R) γ δ α β hcov s.π)),
        iota_cokerDescVal_beta (R:=R) γ δ α β hpb hβ hcov s.π hh b, neg_neg]
  · intro s m hm
    have hh : biprod.lift (coprodMap (R:=R) γ) (coprodMap (R:=R) δ) ≫ s.π = 0 := by
      have h := s.condition
      rw [zero_comp] at h
      exact h
    rw [CokernelCofork.π_ofπ] at hm
    apply Sigma.hom_ext
    intro t
    rcases hcov t with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have hαm : coprodMap (R:=R) α ≫ m = biprod.inl ≫ s.π := by
        have h := congrArg (fun k => biprod.inl ≫ k) hm
        rw [← Category.assoc, biprod.inl_desc] at h
        exact h
      have h1 : Sigma.ι (fun _ : S => ModuleCat.of R R) (α a) ≫ m
          = Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ (biprod.inl ≫ s.π) := by
        rw [← ι_coprodMap (R:=R) α a, Category.assoc, hαm]
      rw [h1, iota_cokerDescVal_alpha (R:=R) γ δ α β hα hcov s.π a]
    · have hβm : coprodMap (R:=R) β ≫ m = -(biprod.inr ≫ s.π) := by
        have h := congrArg (fun k => biprod.inr ≫ k) hm
        rw [← Category.assoc, biprod.inr_desc, Preadditive.neg_comp] at h
        rw [← h, neg_neg]
      have h2 : Sigma.ι (fun _ : S => ModuleCat.of R R) (β b) ≫ m
          = -(Sigma.ι (fun _ : B => ModuleCat.of R R) b ≫ (biprod.inr ≫ s.π)) := by
        rw [← ι_coprodMap (R:=R) β b, Category.assoc, hβm, Preadditive.comp_neg]
      rw [h2, iota_cokerDescVal_beta (R:=R) γ δ α β hpb hβ hcov s.π hh b]

/-! ## The main theorem -/

theorem coprod_shortExact (R : Type) [Ring R] {A B C S : Type} (γ : C → A) (δ : C → B)
    (α : A → S) (β : B → S) (hγ : Function.Injective γ) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hcomm : α ∘ γ = β ∘ δ)
    (hpb : ∀ a b, α a = β b → ∃ c, γ c = a ∧ δ c = b)
    (hcov : ∀ s, (∃ a, α a = s) ∨ (∃ b, β b = s)) :
    (coprodShortComplex (R:=R) γ δ α β hcomm).ShortExact := by
  classical
  haveI hm : Mono (coprodMap (R:=R) γ) := mono_coprodMap (R:=R) γ hγ
  have hmono : Mono (biprod.lift (coprodMap (R:=R) γ) (coprodMap (R:=R) δ)) :=
    mono_of_mono_fac (biprod.lift_fst (coprodMap (R:=R) γ) (coprodMap (R:=R) δ))
  have hck : IsColimit (CokernelCofork.ofπ (coprodShortComplex (R:=R) γ δ α β hcomm).g
      (coprodShortComplex (R:=R) γ δ α β hcomm).zero) :=
    coker_isColimit (R:=R) γ δ α β hcomm hpb hα hβ hcov
  have h := (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
    (coprodShortComplex (R:=R) γ δ α β hcomm)).mpr ⟨hck⟩
  exact ShortComplex.ShortExact.mk' h.1 hmono h.2

end

end Work.Cohomology
