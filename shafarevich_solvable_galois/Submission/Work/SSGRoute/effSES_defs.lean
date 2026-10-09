import Mathlib
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.exists_effacing_object
import Submission.Work.SSGRoute.exists_e_zero_natural
import Submission.Work.SSGRoute.extClass_comp_props
import Submission.Work.SSGRoute.groupCohomology_delta_props
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 3200000

/-!
# Effacement data for `Rep Coeff G`: the definitions

This file sets up the Grothendieck/effacement machinery used to build the `Ext`/group-cohomology
bridge `Work.SSGRoute.Phi1.ExtGroupCohomologyBridge` in
`Submission/Work/SSGRoute/extH_groupCohomology_bridge_nonempty.lean`.

For every `A : Rep Coeff G` we choose an injective `I(A)` with `A ↪ I(A)`, acyclic for both
`groupCohomology` and `extH` in positive degrees (`effacing`).  Then `effSES A` is the short exact
sequence `0 → A → I(A) → coker → 0`, with connecting maps `dH` (group side) and `dE` (`Ext` side).
Because `I(A)` is injective, `dH` and `dE` are surjective, which is what allows the "descent"
construction of the higher-degree isomorphism (`eStepFun`).
-/

namespace Work.SSGRoute

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

variable (G : Type) [Group G]

/-- The effacement data of a representation: an embedding into an injective object acyclic for
both cohomology theories in positive degrees. -/
structure Effacing (A : Rep.{0} SSGRoute.PTExt.Coeff G) where
  I : Rep.{0} SSGRoute.PTExt.Coeff G
  inj : CategoryTheory.Injective I
  i : A ⟶ I
  mono_i : CategoryTheory.Mono i
  acycH : ∀ n : ℕ, 1 ≤ n → Subsingleton (groupCohomology I n)
  acycE : ∀ n : ℕ, 1 ≤ n → Subsingleton (SSGRoute.PTExt.extH I n)

noncomputable def effacing (A : Rep.{0} SSGRoute.PTExt.Coeff G) : Effacing G A :=
  let h := exists_effacing_object G A
  let I := Classical.choose h
  have hI : CategoryTheory.Injective I := Classical.choose (Classical.choose_spec h)
  let i : A ⟶ I :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec h))
  have hi := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  ⟨I, hI, i, hi.1, hi.2.1, hi.2.2⟩

/-- The effacement short exact sequence `0 → A → I(A) → coker → 0`. -/
noncomputable abbrev effSES (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G) :=
  ShortComplex.mk (effacing G A).i (cokernel.π (effacing G A).i)
    (cokernel.condition (effacing G A).i)

@[simp] lemma effSES_X₁ (A : Rep.{0} SSGRoute.PTExt.Coeff G) : (effSES G A).X₁ = A := rfl

@[simp] lemma effSES_X₂ (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (effSES G A).X₂ = (effacing G A).I := rfl

@[simp] lemma effSES_X₃ (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (effSES G A).X₃ = cokernel (effacing G A).i := rfl

@[simp] lemma effSES_f (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (effSES G A).f = (effacing G A).i := rfl

@[simp] lemma effSES_g (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (effSES G A).g = cokernel.π (effacing G A).i := rfl

theorem effSES_exact (A : Rep.{0} SSGRoute.PTExt.Coeff G) : (effSES G A).Exact :=
  ShortComplex.exact_of_g_is_cokernel (effSES G A) (cokernelIsCokernel (effacing G A).i)

/-- The second map of the effacement sequence is an epimorphism. -/
theorem effSES_epi_g (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.Epi (effSES G A).g := by
  first
    | rw [effSES_g]; infer_instance
    | exact (inferInstance :
        CategoryTheory.Epi (ShortComplex.cokernelSequence (effacing G A).i).g)
    | exact epi_of_isColimit_cofork (colimit.isColimit (parallelPair (effacing G A).i 0))

theorem effSES_shortExact (A : Rep.{0} SSGRoute.PTExt.Coeff G) : (effSES G A).ShortExact :=
  ShortComplex.ShortExact.mk' (effSES_exact G A) (effacing G A).mono_i (effSES_epi_g G A)

/-- The connecting map `dH : Hⁿ(coker) → Hⁿ⁺¹(A)` of the effacement sequence. -/
noncomputable def dH (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    groupCohomology (effSES G A).X₃ n →+ groupCohomology A (n + 1) :=
  ((groupCohomology.δ (effSES_shortExact G A) n (n + 1) rfl).hom).toAddMonoidHom

/-- The connecting map `dE : Extⁿ(coker) → Extⁿ⁺¹(A)` of the effacement sequence. -/
noncomputable def dE (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    SSGRoute.PTExt.extH (effSES G A).X₃ n →+ SSGRoute.PTExt.extH A (n + 1) :=
  AddMonoidHom.mk'
    (fun y => y.comp (effSES_shortExact G A).extClass (rfl : n + 1 = n + 1))
    (fun y₁ y₂ => Abelian.Ext.add_comp y₁ y₂ ((effSES_shortExact G A).extClass)
      (rfl : n + 1 = n + 1))

@[simp] lemma dH_apply (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (y : groupCohomology (effSES G A).X₃ n) :
    dH G n A y = (groupCohomology.δ (effSES_shortExact G A) n (n + 1) rfl).hom y := rfl

@[simp] lemma dE_apply (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (y : SSGRoute.PTExt.extH (effSES G A).X₃ n) :
    dE G n A y = y.comp (effSES_shortExact G A).extClass (rfl : n + 1 = n + 1) := rfl

theorem dH_surj (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Function.Surjective (dH G n A) := by
  have h : Subsingleton (groupCohomology (effSES G A).X₂ (n + 1)) :=
    (effacing G A).acycH (n + 1) (by omega)
  intro z
  obtain ⟨y, hy⟩ :=
    (groupCohomology_delta_props G (effSES G A) (effSES_shortExact G A) n).2 h z
  exact ⟨y, hy⟩

theorem dE_surj (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Function.Surjective (dE G n A) := by
  have h : Subsingleton (SSGRoute.PTExt.extH (effSES G A).X₂ (n + 1)) :=
    (effacing G A).acycE (n + 1) (by omega)
  intro z
  obtain ⟨y, hy⟩ :=
    (extClass_comp_props G (effSES G A) (effSES_shortExact G A) n).2 h z
  exact ⟨y, hy⟩

theorem dH_inj (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) (hn : 1 ≤ n) :
    Function.Injective (dH G n A) := by
  have h : Subsingleton (groupCohomology (effSES G A).X₂ n) := (effacing G A).acycH n hn
  intro x y hxy
  have h0 : dH G n A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 : x - y = 0 :=
    (groupCohomology_delta_props G (effSES G A) (effSES_shortExact G A) n).1 h (x - y) h0
  exact sub_eq_zero.mp h1

theorem dE_inj (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) (hn : 1 ≤ n) :
    Function.Injective (dE G n A) := by
  have h : Subsingleton (SSGRoute.PTExt.extH (effSES G A).X₂ n) := (effacing G A).acycE n hn
  intro x y hxy
  have h0 : dE G n A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 : x - y = 0 :=
    (extClass_comp_props G (effSES G A) (effSES_shortExact G A) n).1 h (x - y) h0
  exact sub_eq_zero.mp h1

/-- Exactness of the group-cohomology long exact sequence at `Hⁿ(S.X₃)`: an element is killed by
the connecting map iff it comes from `Hⁿ(S.X₂)`. -/
theorem groupCohomology_delta_ker_iff (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (n : ℕ) :
    ∀ (y : groupCohomology S.X₃ n),
      (groupCohomology.δ hS n (n + 1) rfl).hom y = 0 ↔
        ∃ (y₂ : groupCohomology S.X₂ n),
          (groupCohomology.map (MonoidHom.id G) S.g n).hom y₂ = y := by
  intro y
  have hex := groupCohomology.mapShortComplex₃_exact (X := S) (hX := hS)
    (rfl : n + 1 = n + 1)
  have h1 := (ShortComplex.moduleCat_exact_iff
    (S := groupCohomology.mapShortComplex₃ (X := S) (hX := hS) (rfl : n + 1 = n + 1))).1 hex
  constructor
  · intro hy
    exact h1 y hy
  · rintro ⟨y₂, hy₂⟩
    rw [← hy₂]
    exact (groupCohomology.mapShortComplex₃ (X := S) (hX := hS) (rfl : n + 1 = n + 1)).zero_apply y₂

/-- Exactness of the `Ext` long exact sequence at `Extⁿ(S.X₃)`: an element is killed by
composition with `hS.extClass` iff it comes from `Extⁿ(S.X₂)`. -/
theorem extClass_comp_ker_iff (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (n : ℕ) :
    ∀ (y : SSGRoute.PTExt.extH S.X₃ n),
      y.comp hS.extClass (rfl : n + 1 = n + 1) = 0 ↔
        ∃ (y₂ : SSGRoute.PTExt.extH S.X₂ n),
          y₂.comp (Abelian.Ext.mk₀ S.g) (add_zero n) = y := by
  intro y
  have hex := Abelian.Ext.covariant_sequence_exact₃'
    (C := Rep.{0} SSGRoute.PTExt.Coeff G) (X := SSGRoute.PTExt.unitRep G) hS n (n + 1) rfl
  have h2 := (ShortComplex.ab_exact_iff_function_exact _).1 hex
  constructor
  · intro hy
    exact (h2 y).1 hy
  · rintro ⟨y₂, hy₂⟩
    exact (h2 y).2 ⟨y₂, hy₂⟩

/-- Descent of an additive map along a surjective additive map, when the second map kills the
kernel of the first. -/
noncomputable def liftOfSurj {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →+ N) (hf : Function.Surjective f) (g : M →+ P)
    (h : ∀ x, f x = 0 → g x = 0) : N →+ P where
  toFun z := g (Classical.choose (hf z))
  map_zero' := h _ (Classical.choose_spec (hf 0))
  map_add' z z' := by
    have hd : f (Classical.choose (hf (z + z')) -
        (Classical.choose (hf z) + Classical.choose (hf z'))) = 0 := by
      rw [map_sub, map_add, Classical.choose_spec (hf (z + z')),
        Classical.choose_spec (hf z), Classical.choose_spec (hf z'), sub_self]
    have hh := h _ hd
    rw [map_sub, map_add] at hh
    exact sub_eq_zero.mp hh

theorem liftOfSurj_apply_apply {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →+ N) (hf : Function.Surjective f) (g : M →+ P)
    (h : ∀ x, f x = 0 → g x = 0) (x : M) :
    liftOfSurj f hf g h (f x) = g x := by
  have hd : f (Classical.choose (hf (f x)) - x) = 0 := by
    rw [map_sub, Classical.choose_spec (hf (f x)), sub_self]
  have hh := h _ hd
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

/-- Naturality of the degree-zero family `eZero`. -/
theorem eZero_nat (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B)
    (y : groupCohomology A 0) :
    eZero G B ((groupCohomology.map (MonoidHom.id G) φ 0).hom y) =
      (eZero G A y).comp (Abelian.Ext.mk₀ φ) (add_zero 0) := by
  rw [eZero_apply, eZero_apply, H0_map_H0Iso, eZeroOfInv_naturality,
    Abelian.Ext.mk₀_comp_mk₀]

/-! ## Generic helpers for extending morphisms along monos and descending along epis -/

/-- Extension of a morphism along a monomorphism into an injective object, with the injectivity
and monomorphism hypotheses passed explicitly (so that no type class inference is needed). -/
noncomputable def efac {X Y J : Rep.{0} SSGRoute.PTExt.Coeff G}
    (hJ : CategoryTheory.Injective J) (i : X ⟶ J) (f : X ⟶ Y)
    (hf : CategoryTheory.Mono f) : Y ⟶ J :=
  letI : CategoryTheory.Injective J := hJ
  letI : CategoryTheory.Mono f := hf
  Injective.factorThru i f

theorem efac_comm {X Y J : Rep.{0} SSGRoute.PTExt.Coeff G} (hJ : CategoryTheory.Injective J)
    (i : X ⟶ J) (f : X ⟶ Y) (hf : CategoryTheory.Mono f) :
    f ≫ efac G hJ i f hf = i := by
  letI : CategoryTheory.Injective J := hJ
  letI : CategoryTheory.Mono f := hf
  exact Injective.comp_factorThru i f

/-- Descent of a morphism `k : S.X₂ ⟶ W` with `S.f ≫ k = 0` along the epimorphism `S.g`, with the
epimorphism hypothesis passed explicitly. -/
noncomputable def edesc {S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)} (hS : S.Exact)
    (hE : CategoryTheory.Epi S.g) {W : Rep.{0} SSGRoute.PTExt.Coeff G} (k : S.X₂ ⟶ W)
    (hk : S.f ≫ k = 0) : S.X₃ ⟶ W :=
  letI : CategoryTheory.Epi S.g := hE
  hS.desc k hk

theorem edesc_comm {S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)} (hS : S.Exact)
    (hE : CategoryTheory.Epi S.g) {W : Rep.{0} SSGRoute.PTExt.Coeff G} (k : S.X₂ ⟶ W)
    (hk : S.f ≫ k = 0) : S.g ≫ edesc G hS hE k hk = k := by
  letI : CategoryTheory.Epi S.g := hE
  exact ShortComplex.Exact.g_desc hS k hk

/-! ## Comparison morphisms between effacement sequences -/

/-- The middle comparison map `I(A) ⟶ I(B)` induced by `φ : A ⟶ B`, using injectivity of `I(B)`. -/
noncomputable def effMap {A B : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : A ⟶ B) :
    (effSES G A).X₂ ⟶ (effSES G B).X₂ :=
  efac G (effacing G B).inj (φ ≫ (effSES G B).f) (effSES G A).f (effacing G A).mono_i

theorem effMap_comm {A B : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : A ⟶ B) :
    (effSES G A).f ≫ effMap G φ = φ ≫ (effSES G B).f :=
  efac_comm G (effacing G B).inj (φ ≫ (effSES G B).f) (effSES G A).f (effacing G A).mono_i

/-- The comparison morphism `effSES A ⟶ effSES B` induced by `φ : A ⟶ B`. -/
noncomputable def effHom {A B : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : A ⟶ B) :
    effSES G A ⟶ effSES G B :=
  ShortComplex.homMk φ (effMap G φ)
    (edesc G (effSES_shortExact G A).exact (effSES_shortExact G A).epi_g
      (effMap G φ ≫ (effSES G B).g)
      (by rw [← Category.assoc, effMap_comm, Category.assoc]; simp))
    (effMap_comm G φ).symm
    ((edesc_comm G (effSES_shortExact G A).exact (effSES_shortExact G A).epi_g
      (effMap G φ ≫ (effSES G B).g) _).symm)

@[simp] lemma effHom_τ₁ {A B : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : A ⟶ B) :
    (effHom G φ).τ₁ = φ := rfl

@[simp] lemma effHom_τ₂ {A B : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : A ⟶ B) :
    (effHom G φ).τ₂ = effMap G φ := rfl

/-- The middle comparison map `S.X₂ ⟶ I(S.X₁)` extending the identity of `S.X₁`, using that `S.f`
is a mono and `I(S.X₁)` is injective. -/
noncomputable def bridgeMap (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) : S.X₂ ⟶ (effSES G S.X₁).X₂ :=
  efac G (effacing G S.X₁).inj (effSES G S.X₁).f S.f hS.mono_f

theorem bridgeMap_comm (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) :
    S.f ≫ bridgeMap G S hS = (effSES G S.X₁).f :=
  efac_comm G (effacing G S.X₁).inj (effSES G S.X₁).f S.f hS.mono_f

/-- The comparison morphism `S ⟶ effSES S.X₁` extending the identity of `S.X₁`. -/
noncomputable def bridgeHom (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) : S ⟶ effSES G S.X₁ :=
  ShortComplex.homMk (𝟙 S.X₁) (bridgeMap G S hS)
    (edesc G hS.exact hS.epi_g
      (bridgeMap G S hS ≫ (effSES G S.X₁).g)
      (by rw [← Category.assoc, bridgeMap_comm]; exact (effSES G S.X₁).zero))
    (by rw [Category.id_comp]; exact (bridgeMap_comm G S hS).symm)
    ((edesc_comm G hS.exact hS.epi_g
      (bridgeMap G S hS ≫ (effSES G S.X₁).g) _).symm)

@[simp] lemma bridgeHom_τ₁ (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) : (bridgeHom G S hS).τ₁ = 𝟙 S.X₁ := rfl

@[simp] lemma bridgeHom_τ₂ (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) : (bridgeHom G S hS).τ₂ = bridgeMap G S hS := rfl

/-! ## The descent step -/

/-- The kernel condition of the descent: an element of `Hⁿ(coker)` killed by `dH` is also killed
by `dE ∘ e`, provided `e` is natural.  Uses exactness of the two long exact sequences at
`Hⁿ(coker)` / `Extⁿ(coker)` together with naturality of `e`. -/
theorem eStep_kernel (n : ℕ)
    (e : ∀ A : Rep.{0} SSGRoute.PTExt.Coeff G, groupCohomology A n ≃+ SSGRoute.PTExt.extH A n)
    (hnat : ∀ (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B) (y : groupCohomology A n),
      e B ((groupCohomology.map (MonoidHom.id G) φ n).hom y) =
        (e A y).comp (Abelian.Ext.mk₀ φ) (add_zero n))
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∀ x : groupCohomology (effSES G A).X₃ n,
      dH G n A x = 0 → (dE G n A).comp ((e (effSES G A).X₃).toAddMonoidHom) x = 0 := by
  intro x hx
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  obtain ⟨x₂, hx₂⟩ :=
    (groupCohomology_delta_ker_iff G (effSES G A) (effSES_shortExact G A) n x).1 hx
  rw [← hx₂]
  rw [hnat (effSES G A).X₂ (effSES G A).X₃ (effSES G A).g x₂]
  rw [dE_apply]
  first
    | (rw [Abelian.Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero])
    | simp

/-- The descent step: given `e : Hⁿ(·) ≃+ Extⁿ(·)` natural in the coefficients and satisfying the
kernel condition, `dE ∘ e` descends along the surjection `dH`. -/
noncomputable def eStepFun (n : ℕ)
    (e : ∀ A : Rep.{0} SSGRoute.PTExt.Coeff G, groupCohomology A n ≃+ SSGRoute.PTExt.extH A n)
    (hnat : ∀ (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B) (y : groupCohomology A n),
      e B ((groupCohomology.map (MonoidHom.id G) φ n).hom y) =
        (e A y).comp (Abelian.Ext.mk₀ φ) (add_zero n))
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    groupCohomology A (n + 1) →+ SSGRoute.PTExt.extH A (n + 1) :=
  liftOfSurj (dH G n A) (dH_surj G n A)
    ((dE G n A).comp ((e (effSES G A).X₃).toAddMonoidHom))
    (eStep_kernel G n e hnat A)

theorem eStepFun_dH (n : ℕ)
    (e : ∀ A : Rep.{0} SSGRoute.PTExt.Coeff G, groupCohomology A n ≃+ SSGRoute.PTExt.extH A n)
    (hnat : ∀ (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B) (y : groupCohomology A n),
      e B ((groupCohomology.map (MonoidHom.id G) φ n).hom y) =
        (e A y).comp (Abelian.Ext.mk₀ φ) (add_zero n))
    (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (x : groupCohomology (effSES G A).X₃ n) :
    eStepFun G n e hnat A (dH G n A x) = dE G n A (e (effSES G A).X₃ x) := by
  unfold eStepFun
  rw [liftOfSurj_apply_apply]
  first
    | rfl
    | simp

/-- A natural family of additive isomorphisms `Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)`. -/
structure NatFamily (G : Type) [Group G] (n : ℕ) where
  /-- the additive isomorphisms. -/
  e : ∀ A : Rep.{0} SSGRoute.PTExt.Coeff G, groupCohomology A n ≃+ SSGRoute.PTExt.extH A n
  /-- naturality in the coefficient module. -/
  nat : ∀ (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B)
    (y : groupCohomology A n),
    e B ((groupCohomology.map (MonoidHom.id G) φ n).hom y) =
      (e A y).comp (Abelian.Ext.mk₀ φ) (add_zero n)

/-- The descent step, phrased with a `NatFamily`. -/
noncomputable def eStep (n : ℕ) (D : NatFamily G n)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    groupCohomology A (n + 1) →+ SSGRoute.PTExt.extH A (n + 1) :=
  eStepFun G n D.e D.nat A

theorem eStep_dH (n : ℕ) (D : NatFamily G n)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (x : groupCohomology (effSES G A).X₃ n) :
    eStep G n D A (dH G n A x) = dE G n A (D.e (effSES G A).X₃ x) :=
  eStepFun_dH G n D.e D.nat A x


end

end Work.SSGRoute
