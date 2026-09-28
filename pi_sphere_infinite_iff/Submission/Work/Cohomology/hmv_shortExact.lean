import Mathlib
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.relCohMV_honest_prereq

/-!
# The honest relative Mayer–Vietoris sequence of cochain complexes is short exact

For a topological space `X`, a subset `A ⊆ X` and subsets `U, V ⊆ X`, the **honest** relative
Mayer–Vietoris sequence

`0 ⟶ C^*(X,A) --F--> C^*(U, U∩A) ⊞ C^*(V, V∩A) --G--> C^*(U ∩ V, U ∩ V ∩ A) ⟶ 0`

is exhibited in `relCohMV_honest_defs` as the short complex
`ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)`, where `hmvF` is the transpose of
the canonical chain maps `HMV.alphaU`, `HMV.alphaV` and `hmvG` is the transpose of the canonical
chain maps `HMV.gamma`, `-HMV.delta`.

This file proves (`hmv_shortExact`) that this short complex is short exact, **without any
hypothesis** on `U`, `V`, `A`, in two steps.

* The *chain level* honest relative Mayer–Vietoris sequence
  `C^{U,V}(U∩V, U∩V∩A) --(γ, -δ)--> C^{U,V}(U,U∩A) ⊞ C^{U,V}(V,V∩A) --(αU, αV)--> C^{U,V}(X,A)`
  is short exact (`hmv_chain_shortExact`).  This is proved by applying
  `Work.Cohomology.cokernel_map_shortExact` to the morphism `relMVv` between the two absolute
  small Mayer–Vietoris rows (`mvSmallA_shortExact`, `mvSmall_shortExact`), and then identifying the
  cokernel-induced maps with `(γ, -δ)` and `(αU, αV)` (the identification uses
  `cokernel_biprod_map_iso` and the defining rules `HMV.gamma_comp`, `HMV.delta_comp`,
  `HMV.alphaU_comp`, `HMV.alphaV_comp`).

* Dualising (`hmvF`, `hmvG` are transposes of `(αU, αV)` and of `(γ, -δ)`), the cochain level
  sequence is short exact.  Degreewise, this uses
  * the dual of a surjection is injective (`hmvF_injective`),
  * the dual of an injection with cokernel of projective degree parts is surjective
    (`hmvG_surjective`, via the splitting `Work.Cohomology.existsLeftInverseOfKerEqRange` and the
    projectivity `Work.Cohomology.relSmallTopProjective`), and
  * the dual of a short exact sequence is exact in the middle
    (`hmvG_ker_le_range`, via `Work.Cohomology.exists_dualMap_eq_of_mem_ker`).

The short exactness then follows from the degreewise statement
(`HomologicalComplex.shortExact_of_degreewise_shortExact`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

/-! ## 0. The cokernel of a morphism of short exact sequences, with explicit maps

`Work.Cohomology.cokernel_map_shortExact` states that the cokernel of a morphism of short exact
complexes whose components are monomorphisms is short exact, but returns the two maps as the
witnesses of an existential.  For the identification of the cokernel-induced maps with the
canonical maps of the honest relative Mayer–Vietoris sequence we need the statement with the two
maps given explicitly by the universal property of the cokernels.  This is `cokernelMap_shortExact`
below: any pair of maps with the defining rules of `cokernel.map` is a short exact sequence. -/

section CokernelMap

open scoped ZeroObject

variable {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
  {S₁ S₂ : ShortComplex C}

/-- **The cokernel of a morphism of short exact sequences is short exact**, for any pair of maps
satisfying the defining rules of the cokernel-induced maps. -/
theorem cokernelMap_shortExact (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (v : S₁ ⟶ S₂)
    (hv₁ : Mono v.τ₁) (hv₂ : Mono v.τ₂) (hv₃ : Mono v.τ₃)
    {f : cokernel v.τ₁ ⟶ cokernel v.τ₂} {g : cokernel v.τ₂ ⟶ cokernel v.τ₃}
    (hf : cokernel.π v.τ₁ ≫ f = S₂.f ≫ cokernel.π v.τ₂)
    (hg : cokernel.π v.τ₂ ≫ g = S₂.g ≫ cokernel.π v.τ₃)
    (hfg : f ≫ g = 0) : (ShortComplex.mk f g hfg).ShortExact := by
  let C₀ : ShortComplex C := ShortComplex.mk f g hfg
  -- the map `S₂ ⟶ C₀` given by the three cokernel projections
  let φ : S₂ ⟶ C₀ :=
    ShortComplex.homMk (cokernel.π v.τ₁) (cokernel.π v.τ₂) (cokernel.π v.τ₃) hf hg
  have w₁₃ : v ≫ φ = 0 := by
    ext <;> simp [ShortComplex.comp_τ₁, φ, cokernel.condition]
  -- the snake input
  let sn : ShortComplex.SnakeInput C :=
    { L₀ := ShortComplex.mk (0 : (0 : C) ⟶ (0 : C)) (0 : (0 : C) ⟶ (0 : C)) (by simp)
      L₁ := S₁
      L₂ := S₂
      L₃ := C₀
      v₀₁ := 0
      v₁₂ := v
      v₂₃ := φ
      w₀₂ := by simp
      w₁₃ := w₁₃
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₁)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₂)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₃)
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₃)
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hex : C₀.Exact := sn.L₃_exact
  have hepi : Epi g := by
    haveI h2 : Epi S₂.g := h₂.epi_g
    haveI h1 : Epi (cokernel.π v.τ₂ ≫ g) := by
      rw [hg]
      exact epi_comp _ _
    exact epi_of_epi (cokernel.π v.τ₂) g
  have hδ : sn.δ = 0 := IsZero.eq_zero_of_src (X := sn.L₀.X₃) (isZero_zero C) sn.δ
  have hmono : Mono f := ShortComplex.Exact.mono_g sn.L₂'_exact hδ
  exact ShortComplex.ShortExact.mk' hex hmono hepi

end CokernelMap

noncomputable section

open DualBiprod

variable {X : TopCat}

/-! ## 0. Notation -/

/-- The cochain complex `C^*(X,A)` of the pair, as the dual of the relative small chains. -/
abbrev cohTop (X : TopCat) (A U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVTopC X A U V)

/-- The cochain complex `C^*(U, U ∩ A)`, as the dual of the relative small chains. -/
abbrev cohUU (X : TopCat) (A U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVUU X A U V)

/-- The cochain complex `C^*(V, V ∩ A)`, as the dual of the relative small chains. -/
abbrev cohVV (X : TopCat) (A U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVVV X A U V)

/-- The cochain complex `C^*(U ∩ V, U ∩ V ∩ A)`, as the dual of the relative small chains. -/
abbrev cohUV (X : TopCat) (A U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (relMVUV X A U V)

/-- The first map of the honest chain level relative Mayer–Vietoris sequence,
`(γ, -δ) : C^{U,V}(U∩V, U∩V∩A) ⟶ C^{U,V}(U,U∩A) ⊞ C^{U,V}(V,V∩A)`. -/
abbrev hmvChainLeft (X : TopCat) (A U V : Set X) :
    relMVUV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V :=
  biprod.lift (HMV.gamma X A U V) (-(HMV.delta X A U V))

/-- The second map of the honest chain level relative Mayer–Vietoris sequence,
`(αU, αV) : C^{U,V}(U,U∩A) ⊞ C^{U,V}(V,V∩A) ⟶ C^{U,V}(X,A)`. -/
abbrev hmvChainRight (X : TopCat) (A U V : Set X) :
    relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVTopC X A U V :=
  biprod.desc (HMV.alphaU X A U V) (HMV.alphaV X A U V)

/-- The two maps of the honest chain level relative Mayer–Vietoris sequence compose to zero. -/
theorem hmv_chain_zero (X : TopCat) (A U V : Set X) :
    hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0 := by
  rw [hmvChainLeft, hmvChainRight, biprod.lift_desc, Preadditive.neg_comp,
    gamma_comp_alphaU_eq_delta_comp_alphaV X A U V, add_neg_cancel]

/-! ## 1. Elementwise lemmas for biproducts of homological complexes -/

theorem biprodTotal_apply_coh {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat ℤ) c) (n : ι) (x : (K ⊞ L).X n) :
    (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n x)
      + (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n x) = x := by
  have htot := HomologicalComplex.biprod_total_f (K := K) (L := L) n
  have h := congrArg (fun (f : (K ⊞ L).X n ⟶ (K ⊞ L).X n) => f x) htot
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h

theorem biprod_ext_apply_coh {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat ℤ) c} {n : ι} {x y : (K ⊞ L).X n}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y := by
  rw [← biprodTotal_apply_coh K L n x, ← biprodTotal_apply_coh K L n y, h₁, h₂]

theorem fst_inl_apply_coh {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat ℤ) c) (n : ι) (a : K.X n) :
    (biprod.fst : K ⊞ L ⟶ K).f n ((biprod.inl : K ⟶ K ⊞ L).f n a) = a := by
  have hh := congrArg (fun (k : K.X n ⟶ K.X n) => ModuleCat.Hom.hom k a)
    (HomologicalComplex.biprod_inl_fst_f (K := K) (L := L) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    using hh

theorem snd_inl_apply_coh {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat ℤ) c) (n : ι) (a : K.X n) :
    (biprod.snd : K ⊞ L ⟶ L).f n ((biprod.inl : K ⟶ K ⊞ L).f n a) = 0 := by
  have hh := congrArg (fun (k : K.X n ⟶ L.X n) => ModuleCat.Hom.hom k a)
    (HomologicalComplex.biprod_inl_snd_f (K := K) (L := L) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    using hh

theorem fst_inr_apply_coh {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat ℤ) c) (n : ι) (b : L.X n) :
    (biprod.fst : K ⊞ L ⟶ K).f n ((biprod.inr : L ⟶ K ⊞ L).f n b) = 0 := by
  have hh := congrArg (fun (k : L.X n ⟶ K.X n) => ModuleCat.Hom.hom k b)
    (HomologicalComplex.biprod_inr_fst_f (K := K) (L := L) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    using hh

theorem snd_inr_apply_coh {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat ℤ) c) (n : ι) (b : L.X n) :
    (biprod.snd : K ⊞ L ⟶ L).f n ((biprod.inr : L ⟶ K ⊞ L).f n b) = b := by
  have hh := congrArg (fun (k : L.X n ⟶ L.X n) => ModuleCat.Hom.hom k b)
    (HomologicalComplex.biprod_inr_snd_f (K := K) (L := L) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    using hh

theorem biprod_desc_apply_total {ι : Type*} {c : ComplexShape ι}
    {K L M : HomologicalComplex (ModuleCat ℤ) c} (f : K ⟶ M) (g : L ⟶ M) (n : ι)
    (x : (K ⊞ L).X n) :
    (biprod.desc f g).f n x
      = f.f n ((biprod.fst : K ⊞ L ⟶ K).f n x) + g.f n ((biprod.snd : K ⊞ L ⟶ L).f n x) := by
  have h1 : ∀ a : K.X n, (biprod.desc f g).f n ((biprod.inl : K ⟶ K ⊞ L).f n a) = f.f n a := by
    intro a
    have hh := congrArg (fun (k : K.X n ⟶ M.X n) => ModuleCat.Hom.hom k a)
      (HomologicalComplex.biprod_inl_desc_f f g n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have h2 : ∀ b : L.X n, (biprod.desc f g).f n ((biprod.inr : L ⟶ K ⊞ L).f n b) = g.f n b := by
    intro b
    have hh := congrArg (fun (k : L.X n ⟶ M.X n) => ModuleCat.Hom.hom k b)
      (HomologicalComplex.biprod_inr_desc_f f g n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  conv_lhs => rw [← biprodTotal_apply_coh K L n x]
  rw [map_add, h1, h2]

/-- The transpose of a negation is the negation of the transpose. -/
lemma dualMapHom_neg {A B : ModuleCat ℤ} (f : A ⟶ B) : dualMapHom (-f) = -dualMapHom f := by
  rw [eq_neg_iff_add_eq_zero, ← dualMapHom_add, neg_add_cancel, dualMapHom_zero]

/-- The transpose of a negation, evaluated on a functional. -/
lemma dualMapHom_neg_apply {A B : ModuleCat ℤ} (f : A ⟶ B) (φ : ↥(DualBiprod.dualObj B)) :
    (dualMapHom (-f)).hom φ = -((dualMapHom f).hom φ) := by
  rw [dualMapHom_neg, ModuleCat.hom_neg, LinearMap.neg_apply]

theorem biprod_lift_apply_total {ι : Type*} {c : ComplexShape ι}
    {K L M : HomologicalComplex (ModuleCat ℤ) c} (f : M ⟶ K) (g : M ⟶ L) (n : ι) (x : M.X n) :
    (biprod.lift f g).f n x
      = (biprod.inl : K ⟶ K ⊞ L).f n (f.f n x) + (biprod.inr : L ⟶ K ⊞ L).f n (g.f n x) := by
  conv_lhs => rw [← biprodTotal_apply_coh K L n ((biprod.lift f g).f n x)]
  have h1 : ∀ a, (biprod.fst : K ⊞ L ⟶ K).f n ((biprod.lift f g).f n a) = f.f n a := by
    intro a
    have hh := congrArg (fun (k : M.X n ⟶ K.X n) => ModuleCat.Hom.hom k a)
      (HomologicalComplex.biprod_lift_fst_f f g n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have h2 : ∀ a, (biprod.snd : K ⊞ L ⟶ L).f n ((biprod.lift f g).f n a) = g.f n a := by
    intro a
    have hh := congrArg (fun (k : M.X n ⟶ L.X n) => ModuleCat.Hom.hom k a)
      (HomologicalComplex.biprod_lift_snd_f f g n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h1, h2]

/-! ## 2. The degreewise consequences of the chain level short exactness -/

/-- The `fst`-component of the chain level map `(γ, -δ)` on an element. -/
theorem hmvChainLeft_fst_apply (X : TopCat) (A U V : Set X) (n : ℕ)
    (m : (relMVUV X A U V).X n) :
    ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶
        relMVUU X A U V).f n) (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n) m)
      = ModuleCat.Hom.hom ((HMV.gamma X A U V).f n) m := by
  have hh := congrArg (fun (k : (relMVUV X A U V).X n ⟶ (relMVUU X A U V).X n) =>
    ModuleCat.Hom.hom k m)
    (HomologicalComplex.biprod_lift_fst_f (HMV.gamma X A U V) (-(HMV.delta X A U V)) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- The `snd`-component of the chain level map `(γ, -δ)` on an element. -/
theorem hmvChainLeft_snd_apply (X : TopCat) (A U V : Set X) (n : ℕ)
    (m : (relMVUV X A U V).X n) :
    ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶
        relMVVV X A U V).f n) (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n) m)
      = ModuleCat.Hom.hom ((-(HMV.delta X A U V)).f n) m := by
  have hh := congrArg (fun (k : (relMVUV X A U V).X n ⟶ (relMVVV X A U V).X n) =>
    ModuleCat.Hom.hom k m)
    (HomologicalComplex.biprod_lift_snd_f (HMV.gamma X A U V) (-(HMV.delta X A U V)) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- The degreewise part of the honest chain level relative Mayer–Vietoris sequence. -/
theorem hmvChainDW (X : TopCat) (A U V : Set X) (n : ℕ)
    (hz : hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0)
    (hchain : (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).ShortExact) :
    ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact := by
  have h1 : Mono ((hmvChainLeft X A U V).f n) := by
    haveI : Mono (hmvChainLeft X A U V) := hchain.mono_f
    infer_instance
  have h2 : Epi ((hmvChainRight X A U V).f n) := by
    haveI : Epi (hmvChainRight X A U V) := hchain.epi_g
    infer_instance
  have h3 : Mono ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (hmvChainLeft X A U V)) := h1
  have h4 : Epi ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (hmvChainRight X A U V)) := h2
  haveI := h3
  haveI := h4
  exact hchain.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)

/-- The first honest chain level relative Mayer–Vietoris map is degreewise injective. -/
theorem hmvChainDW_injective (X : TopCat) (A U V : Set X) (n : ℕ)
    (hz : hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0)
    (hchain : (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).ShortExact) :
    Function.Injective (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n)) := by
  have h : Mono (((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f) :=
    (hmvChainDW X A U V n hz hchain).mono_f
  rw [show ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f
        = (hmvChainLeft X A U V).f n from
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (hmvChainLeft X A U V)] at h
  exact (ModuleCat.mono_iff_injective _).1 h

/-- The second honest chain level relative Mayer–Vietoris map is degreewise surjective. -/
theorem hmvChainDW_surjective (X : TopCat) (A U V : Set X) (n : ℕ)
    (hz : hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0)
    (hchain : (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).ShortExact) :
    Function.Surjective (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n)) := by
  have h : Epi (((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g) :=
    (hmvChainDW X A U V n hz hchain).epi_g
  rw [show ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g
        = (hmvChainRight X A U V).f n from
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (hmvChainRight X A U V)] at h
  exact (ModuleCat.epi_iff_surjective _).1 h

/-- Degreewise exactness of the honest chain level relative Mayer–Vietoris sequence. -/
theorem hmvChainDW_ker (X : TopCat) (A U V : Set X) (n : ℕ)
    (hz : hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0)
    (hchain : (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).ShortExact) :
    LinearMap.ker (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n))
      = LinearMap.range (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n)) := by
  have hS := hmvChainDW X A U V n hz hchain
  have hd : ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f
      ≫ ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g = 0 :=
    ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).zero
  have hf : ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f
        = (hmvChainLeft X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (hmvChainLeft X A U V)
  have hg : ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g
        = (hmvChainRight X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (hmvChainRight X A U V)
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_range]
    have hx' : ((ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).map
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g x = 0 := by
      rw [hg]; exact hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS.exact x hx'
    exact ⟨y, by rw [← hf]; exact hy⟩
  · rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have h2 := congrArg ModuleCat.Hom.hom hd
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    rw [hf, hg] at h2
    exact LinearMap.congr_fun h2 y

/-! ## 3. The degreewise components of the cochain level maps -/

/-- The `fst`-component of `hmvF` is the transpose of `HMV.alphaU`. -/
lemma hmvF_fst (X : TopCat) (A U V : Set X) (n : ℕ) :
    (hmvF X A U V).f n ≫ (biprod.fst : cohUU X A U V ⊞ cohVV X A U V ⟶ cohUU X A U V).f n
      = dualMapHom ((HMV.alphaU X A U V).f n) := by
  rw [hmvF, HomologicalComplex.biprod_lift_fst_f]
  rfl

/-- The `snd`-component of `hmvF` is the transpose of `HMV.alphaV`. -/
lemma hmvF_snd (X : TopCat) (A U V : Set X) (n : ℕ) :
    (hmvF X A U V).f n ≫ (biprod.snd : cohUU X A U V ⊞ cohVV X A U V ⟶ cohVV X A U V).f n
      = dualMapHom ((HMV.alphaV X A U V).f n) := by
  rw [hmvF, HomologicalComplex.biprod_lift_snd_f]
  rfl

/-- The `inl`-component of `hmvG` is the transpose of `HMV.gamma`. -/
lemma hmvG_inl (X : TopCat) (A U V : Set X) (n : ℕ) :
    (biprod.inl : cohUU X A U V ⟶ cohUU X A U V ⊞ cohVV X A U V).f n ≫ (hmvG X A U V).f n
      = dualMapHom ((HMV.gamma X A U V).f n) := by
  rw [hmvG, HomologicalComplex.biprod_inl_desc_f]
  rfl

/-- The `inr`-component of `hmvG` is minus the transpose of `HMV.delta`. -/
lemma hmvG_inr (X : TopCat) (A U V : Set X) (n : ℕ) :
    (biprod.inr : cohVV X A U V ⟶ cohUU X A U V ⊞ cohVV X A U V).f n ≫ (hmvG X A U V).f n
      = -(dualMapHom ((HMV.delta X A U V).f n)) := by
  rw [hmvG, HomologicalComplex.biprod_inr_desc_f]
  rfl

/-- The `fst`-component of `hmvF`, evaluated on a cochain. -/
lemma hmvF_fst_apply (X : TopCat) (A U V : Set X) (n : ℕ) (χ : (cohTop X A U V).X n) :
    ModuleCat.Hom.hom ((biprod.fst : cohUU X A U V ⊞ cohVV X A U V ⟶ cohUU X A U V).f n)
      (ModuleCat.Hom.hom ((hmvF X A U V).f n) χ)
      = χ.comp ((HMV.alphaU X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hmvF_fst]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-- The `snd`-component of `hmvF`, evaluated on a cochain. -/
lemma hmvF_snd_apply (X : TopCat) (A U V : Set X) (n : ℕ) (χ : (cohTop X A U V).X n) :
    ModuleCat.Hom.hom ((biprod.snd : cohUU X A U V ⊞ cohVV X A U V ⟶ cohVV X A U V).f n)
      (ModuleCat.Hom.hom ((hmvF X A U V).f n) χ)
      = χ.comp ((HMV.alphaV X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hmvF_snd]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-- The `inl`-component of `hmvG`, evaluated on a cochain. -/
lemma hmvG_inl_apply (X : TopCat) (A U V : Set X) (n : ℕ) (a : (cohUU X A U V).X n) :
    ModuleCat.Hom.hom ((hmvG X A U V).f n)
      (ModuleCat.Hom.hom ((biprod.inl : cohUU X A U V ⟶ cohUU X A U V ⊞ cohVV X A U V).f n) a)
      = a.comp ((HMV.gamma X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hmvG_inl]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-- The `inr`-component of `hmvG`, evaluated on a cochain. -/
lemma hmvG_inr_apply (X : TopCat) (A U V : Set X) (n : ℕ) (b : (cohVV X A U V).X n) :
    ModuleCat.Hom.hom ((hmvG X A U V).f n)
      (ModuleCat.Hom.hom ((biprod.inr : cohVV X A U V ⟶ cohUU X A U V ⊞ cohVV X A U V).f n) b)
      = -(b.comp ((HMV.delta X A U V).f n).hom) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hmvG_inr]
  simp only [ModuleCat.hom_neg, DualBiprod.dualMapHom_hom]
  rfl

/-! ## 4. Degreewise injectivity of `hmvF` -/

/-- **`hmvF` is degreewise injective**, since its two components are the transposes of the two
components `αU`, `αV` of a surjection. -/
theorem hmvF_injective (X : TopCat) (A U V : Set X) (n : ℕ)
    (hsurj : Function.Surjective (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n))) :
    Function.Injective (ModuleCat.Hom.hom ((hmvF X A U V).f n)) := by
  intro x y hxy
  have h1 : (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp ((HMV.alphaU X A U V).f n).hom
      = (y : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp ((HMV.alphaU X A U V).f n).hom := by
    have h := congrArg (fun (w : ↥((cohUU X A U V ⊞ cohVV X A U V).X n)) =>
      ModuleCat.Hom.hom ((biprod.fst : cohUU X A U V ⊞ cohVV X A U V ⟶ cohUU X A U V).f n) w) hxy
    simpa only [hmvF_fst_apply X A U V n] using h
  have h2 : (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp ((HMV.alphaV X A U V).f n).hom
      = (y : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp ((HMV.alphaV X A U V).f n).hom := by
    have h := congrArg (fun (w : ↥((cohUU X A U V ⊞ cohVV X A U V).X n)) =>
      ModuleCat.Hom.hom ((biprod.snd : cohUU X A U V ⊞ cohVV X A U V ⟶ cohVV X A U V).f n) w) hxy
    simpa only [hmvF_snd_apply X A U V n] using h
  change (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ) = (y : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ)
  apply LinearMap.ext
  intro z
  obtain ⟨w, hw⟩ := hsurj z
  rw [← hw, biprod_desc_apply_total (HMV.alphaU X A U V) (HMV.alphaV X A U V) n w]
  rw [map_add, map_add]
  congr 1
  · simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h1 ((biprod.fst :
      relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVUU X A U V).f n w)
  · simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h2 ((biprod.snd :
      relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVVV X A U V).f n w)

/-! ## 5. Exactness in the middle -/

/-- **Exactness at the middle of the cochain level relative Mayer–Vietoris sequence**, degreewise:
the dual of the degreewise short exact chain level sequence is exact in the middle. -/
theorem hmvG_ker_le_range (X : TopCat) (A U V : Set X) (n : ℕ)
    (hsurj : Function.Surjective (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n)))
    (hker : LinearMap.ker (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n))
      = LinearMap.range (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n))) :
    LinearMap.ker (ModuleCat.Hom.hom ((hmvG X A U V).f n))
      ≤ LinearMap.range (ModuleCat.Hom.hom ((hmvF X A U V).f n)) := by
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [LinearMap.mem_range]
  -- the two components of `y` and their compatibility
  set a : (relMVUU X A U V).X n →ₗ[ℤ] ℤ :=
    ModuleCat.Hom.hom ((biprod.fst : cohUU X A U V ⊞ cohVV X A U V ⟶ cohUU X A U V).f n) y with ha
  set b : (relMVVV X A U V).X n →ₗ[ℤ] ℤ :=
    ModuleCat.Hom.hom ((biprod.snd : cohUU X A U V ⊞ cohVV X A U V ⟶ cohVV X A U V).f n) y with hb
  have hydec : ModuleCat.Hom.hom ((biprod.inl : cohUU X A U V ⟶
        cohUU X A U V ⊞ cohVV X A U V).f n) a
      + ModuleCat.Hom.hom ((biprod.inr : cohVV X A U V ⟶ cohUU X A U V ⊞ cohVV X A U V).f n) b
        = y := by
    rw [ha, hb]
    exact biprodTotal_apply_coh (cohUU X A U V) (cohVV X A U V) n y
  have hcond : a.comp ((HMV.gamma X A U V).f n).hom
      + -(b.comp ((HMV.delta X A U V).f n).hom) = 0 := by
    have h0 : ModuleCat.Hom.hom ((hmvG X A U V).f n)
        (ModuleCat.Hom.hom ((biprod.inl : cohUU X A U V ⟶ cohUU X A U V ⊞
            cohVV X A U V).f n) a
          + ModuleCat.Hom.hom ((biprod.inr : cohVV X A U V ⟶ cohUU X A U V ⊞
            cohVV X A U V).f n) b) = 0 := by
      rw [hydec]; exact hy
    rw [map_add, hmvG_inl_apply, hmvG_inr_apply] at h0
    exact h0
  -- the chain level functional killed by `(αU, αV)`
  set F : ↥((relMVUU X A U V ⊞ relMVVV X A U V).X n) →ₗ[ℤ] ℤ :=
    a.comp (ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶
        relMVUU X A U V).f n))
      + b.comp (ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶
        relMVVV X A U V).f n)) with hF
  have hF0 : ∀ m, F (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n) m) = 0 := by
    intro m
    rw [hF, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      hmvChainLeft_fst_apply X A U V n m, hmvChainLeft_snd_apply X A U V n m]
    rw [HomologicalComplex.neg_f_apply, ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]
    have hh := LinearMap.congr_fun hcond m
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply] at hh
    exact hh
  obtain ⟨χ, hχ⟩ := exists_dualMap_eq_of_mem_ker (((hmvChainLeft X A U V).f n).hom)
    (((hmvChainRight X A U V).f n).hom) hsurj hker F hF0
  refine ⟨χ, ?_⟩
  apply biprod_ext_apply_coh
  · show ModuleCat.Hom.hom ((biprod.fst : cohUU X A U V ⊞ cohVV X A U V ⟶ cohUU X A U V).f n)
        (ModuleCat.Hom.hom ((hmvF X A U V).f n) χ) = a
    rw [hmvF_fst_apply X A U V n]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply]
    have hA : ModuleCat.Hom.hom ((HMV.alphaU X A U V).f n) x
        = ModuleCat.Hom.hom ((hmvChainRight X A U V).f n)
            (ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞
              relMVVV X A U V).f n) x) := by
      rw [biprod_desc_apply_total (HMV.alphaU X A U V) (HMV.alphaV X A U V) n
        (ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞
          relMVVV X A U V).f n) x)]
      rw [fst_inl_apply_coh, snd_inl_apply_coh, map_zero, add_zero]
    rw [hA, hχ]
    rw [hF, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      fst_inl_apply_coh, snd_inl_apply_coh, map_zero, add_zero]
  · show ModuleCat.Hom.hom ((biprod.snd : cohUU X A U V ⊞ cohVV X A U V ⟶ cohVV X A U V).f n)
        (ModuleCat.Hom.hom ((hmvF X A U V).f n) χ) = b
    rw [hmvF_snd_apply X A U V n]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply]
    have hA : ModuleCat.Hom.hom ((HMV.alphaV X A U V).f n) x
        = ModuleCat.Hom.hom ((hmvChainRight X A U V).f n)
            (ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞
              relMVVV X A U V).f n) x) := by
      rw [biprod_desc_apply_total (HMV.alphaU X A U V) (HMV.alphaV X A U V) n
        (ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞
          relMVVV X A U V).f n) x)]
      rw [fst_inr_apply_coh, snd_inr_apply_coh, map_zero, zero_add]
    rw [hA, hχ]
    rw [hF, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      fst_inr_apply_coh, snd_inr_apply_coh, map_zero, zero_add]

/-! ## 6. Degreewise surjectivity of `hmvG` -/

/-- **`hmvG` is degreewise surjective**: the transpose of a degreewise injection whose cokernel is
degreewise projective is surjective. -/
theorem hmvG_surjective (X : TopCat) (A U V : Set X) (n : ℕ)
    (hinj : Function.Injective (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n)))
    (hsurj : Function.Surjective (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n)))
    (hker : LinearMap.ker (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n))
      = LinearMap.range (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n))) :
    Function.Surjective (ModuleCat.Hom.hom ((hmvG X A U V).f n)) := by
  haveI hproj : Module.Projective ℤ ↥((relMVTopC X A U V).X n) := relSmallTopProjective X U V A n
  obtain ⟨r, hr⟩ := existsLeftInverseOfKerEqRange
    (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n))
    (ModuleCat.Hom.hom ((hmvChainRight X A U V).f n)) hinj hsurj hker
  have hr_apply : ∀ a, r (ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n) a) = a := fun a =>
    LinearMap.congr_fun hr a
  -- the two components of the splitting
  let ρ₁ : (relMVUU X A U V).X n →ₗ[ℤ] (relMVUV X A U V).X n :=
    r.comp (ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶
      relMVUU X A U V ⊞ relMVVV X A U V).f n))
  let ρ₂ : (relMVVV X A U V).X n →ₗ[ℤ] (relMVUV X A U V).X n :=
    r.comp (ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶
      relMVUU X A U V ⊞ relMVVV X A U V).f n))
  have hkey : ∀ a, ρ₁ (ModuleCat.Hom.hom ((HMV.gamma X A U V).f n) a)
      + ρ₂ (ModuleCat.Hom.hom ((-(HMV.delta X A U V)).f n) a) = a := by
    intro a
    show r (ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞
          relMVVV X A U V).f n) (ModuleCat.Hom.hom ((HMV.gamma X A U V).f n) a))
        + r (ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞
          relMVVV X A U V).f n) (ModuleCat.Hom.hom ((-(HMV.delta X A U V)).f n) a)) = a
    rw [← map_add]
    have hL : ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞
          relMVVV X A U V).f n) (ModuleCat.Hom.hom ((HMV.gamma X A U V).f n) a)
        + ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞
          relMVVV X A U V).f n) (ModuleCat.Hom.hom ((-(HMV.delta X A U V)).f n) a)
        = ModuleCat.Hom.hom ((hmvChainLeft X A U V).f n) a :=
      (biprod_lift_apply_total (HMV.gamma X A U V) (-(HMV.delta X A U V)) n a).symm
    rw [hL, hr_apply]
  -- the transpose of the splitting defines the required preimage
  intro ρ
  refine ⟨ModuleCat.Hom.hom ((biprod.inl : cohUU X A U V ⟶
        cohUU X A U V ⊞ cohVV X A U V).f n) (dualMapHom (ModuleCat.ofHom ρ₁) ρ)
      + ModuleCat.Hom.hom ((biprod.inr : cohVV X A U V ⟶
        cohUU X A U V ⊞ cohVV X A U V).f n) (dualMapHom (ModuleCat.ofHom ρ₂) ρ), ?_⟩
  have hG1 : (ModuleCat.Hom.hom ((hmvG X A U V).f n))
      (ModuleCat.Hom.hom ((biprod.inl : cohUU X A U V ⟶ cohUU X A U V ⊞
        cohVV X A U V).f n) (dualMapHom (ModuleCat.ofHom ρ₁) ρ))
      = (dualMapHom ((HMV.gamma X A U V).f n)).hom (dualMapHom (ModuleCat.ofHom ρ₁) ρ) := by
    rw [hmvG_inl_apply]
    simp only [DualBiprod.dualMapHom_hom]
    rfl
  have hG2 : (ModuleCat.Hom.hom ((hmvG X A U V).f n))
      (ModuleCat.Hom.hom ((biprod.inr : cohVV X A U V ⟶ cohUU X A U V ⊞
        cohVV X A U V).f n) (dualMapHom (ModuleCat.ofHom ρ₂) ρ))
      = -((dualMapHom ((HMV.delta X A U V).f n)).hom (dualMapHom (ModuleCat.ofHom ρ₂) ρ)) := by
    rw [hmvG_inr_apply]
    simp only [ModuleCat.hom_neg, DualBiprod.dualMapHom_hom]
    rfl
  have hc1 := dualMapHom_comp_apply ((HMV.gamma X A U V).f n) (ModuleCat.ofHom ρ₁) ρ
  have hc2 := dualMapHom_comp_apply ((HMV.delta X A U V).f n) (ModuleCat.ofHom ρ₂) ρ
  have hsum := dualMapHom_add_apply
    (((HMV.gamma X A U V).f n) ≫ (ModuleCat.ofHom ρ₁))
    ((-((HMV.delta X A U V).f n)) ≫ (ModuleCat.ofHom ρ₂)) ρ
  have hkeymap : (((HMV.gamma X A U V).f n) ≫ (ModuleCat.ofHom ρ₁))
      + ((-((HMV.delta X A U V).f n)) ≫ (ModuleCat.ofHom ρ₂))
      = 𝟙 ((relMVUV X A U V).X n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
      ModuleCat.hom_id, LinearMap.id_apply]
    exact hkey a
  rw [map_add, hG1, hG2, hc1, hc2, ← dualMapHom_neg_apply, ← Preadditive.neg_comp,
    ← hsum, hkeymap, dualMapHom_id_apply]

/-! ## 7. The short exactness of the cochain level sequence -/

/-- The degreewise part of the honest relative cohomological Mayer–Vietoris sequence. -/
theorem hmv_degreewise_shortExact (X : TopCat) (A U V : Set X) (n : ℕ)
    (hz : hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0)
    (hchain : (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).ShortExact) :
    ((ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).ShortExact := by
  have hinj := hmvChainDW_injective X A U V n hz hchain
  have hsurj := hmvChainDW_surjective X A U V n hz hchain
  have hker := hmvChainDW_ker X A U V n hz hchain
  have hf : ((ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).f
        = (hmvF X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.up ℕ) n (hmvF X A U V)
  have hg : ((ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).g
        = (hmvG X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.up ℕ) n (hmvG X A U V)
  haveI hmono : Mono (((ShortComplex.mk (hmvF X A U V) (hmvG X A U V)
      (hmv_comp X A U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).f) := by
    rw [hf]
    exact (ModuleCat.mono_iff_injective _).2 (hmvF_injective X A U V n hsurj)
  haveI hepi : Epi (((ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).g) := by
    rw [hg]
    exact (ModuleCat.epi_iff_surjective _).2 (hmvG_surjective X A U V n hinj hsurj hker)
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range, hf, hg]
  exact hmvG_ker_le_range X A U V n hsurj hker

/-- **The honest relative cohomological Mayer–Vietoris sequence is short exact**, given the chain
level short exactness. -/
theorem hmv_shortExact_of_chain (X : TopCat) (A U V : Set X)
    (hz : hmvChainLeft X A U V ≫ hmvChainRight X A U V = 0)
    (hchain : (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V) hz).ShortExact) :
    (ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => hmv_degreewise_shortExact X A U V n hz hchain)

/-! ## 8. The chain level honest relative Mayer–Vietoris sequence -/

/-- The middle map `C^{U,V}(U∩A) ⊞ C^{U,V}(V∩A) ⟶ C^{U,V}(U) ⊞ C^{U,V}(V)` of the relative
Mayer–Vietoris rows. -/
abbrev hmvPsi (X : TopCat) (A U V : Set X) :
    smallInChains U V (U ∩ A) ⊞ smallInChains U V (V ∩ A) ⟶
      smallInChains U V U ⊞ smallInChains U V V :=
  biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)

/-- The first cokernel-induced map of the honest relative Mayer–Vietoris sequence,
`C^{U,V}(U ∩ V, U ∩ V ∩ A) ⟶ C^{U,V}(U, U ∩ A) ⊞ C^{U,V}(V, V ∩ A)`. -/
abbrev cokerLeft (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₁ U V A) ⟶ cokernel (hmvPsi X A U V) :=
  cokernel.map (relMVτ₁ U V A) (hmvPsi X A U V) (mvLeftSmallA U V A) (mvLeftSmall U V)
    (relMVv U V A).comm₁₂

/-- The second cokernel-induced map of the honest relative Mayer–Vietoris sequence,
`C^{U,V}(U, U ∩ A) ⊞ C^{U,V}(V, V ∩ A) ⟶ C^{U,V}(X, A)`. -/
abbrev cokerRight (X : TopCat) (A U V : Set X) :
    cokernel (hmvPsi X A U V) ⟶ cokernel (smallInToSmall U V A) :=
  cokernel.map (hmvPsi X A U V) (smallInToSmall U V A) (mvRightSmallA U V A) (mvRightSmall U V)
    (relMVv U V A).comm₂₃

/-- The defining rule of `cokerLeft`. -/
theorem cokerLeft_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₁ U V A) ≫ cokerLeft X A U V
      = mvLeftSmall U V ≫ cokernel.π (hmvPsi X A U V) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The defining rule of `cokerRight`. -/
theorem cokerRight_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (hmvPsi X A U V) ≫ cokerRight X A U V
      = mvRightSmall U V ≫ cokernel.π (smallInToSmall U V A) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The composite of the two cokernel-induced maps is zero. -/
theorem cokerLeft_comp_cokerRight (X : TopCat) (A U V : Set X) :
    cokerLeft X A U V ≫ cokerRight X A U V = 0 := by
  rw [← cancel_epi (cokernel.π (relMVτ₁ U V A)), comp_zero, ← Category.assoc,
    cokerLeft_comp, Category.assoc, cokerRight_comp, ← Category.assoc, mvCompSmall U V, zero_comp]

/-- The `fst`-component of the canonical isomorphism
`coker (biprod.map τ₂U τ₂V) ⟶ coker τ₂U ⊞ coker τ₂V`. -/
abbrev cokerD₁ (X : TopCat) (A U V : Set X) :
    cokernel (hmvPsi X A U V) ⟶ cokernel (relMVτ₂U U V A) :=
  cokernel.desc (hmvPsi X A U V) (biprod.fst ≫ cokernel.π (relMVτ₂U U V A))
    (by rw [← Category.assoc, biprod.map_fst, Category.assoc, cokernel.condition, comp_zero])

/-- The `snd`-component of the canonical isomorphism
`coker (biprod.map τ₂U τ₂V) ⟶ coker τ₂U ⊞ coker τ₂V`. -/
abbrev cokerD₂ (X : TopCat) (A U V : Set X) :
    cokernel (hmvPsi X A U V) ⟶ cokernel (relMVτ₂V U V A) :=
  cokernel.desc (hmvPsi X A U V) (biprod.snd ≫ cokernel.π (relMVτ₂V U V A))
    (by rw [← Category.assoc, biprod.map_snd, Category.assoc, cokernel.condition, comp_zero])

/-- The `inl`-component of the inverse of the canonical isomorphism. -/
abbrev cokerM₁ (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂U U V A) ⟶ cokernel (hmvPsi X A U V) :=
  cokernel.map (relMVτ₂U U V A) (hmvPsi X A U V) biprod.inl biprod.inl
    (biprod.inl_map (relMVτ₂U U V A) (relMVτ₂V U V A)).symm

/-- The `inr`-component of the inverse of the canonical isomorphism. -/
abbrev cokerM₂ (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂V U V A) ⟶ cokernel (hmvPsi X A U V) :=
  cokernel.map (relMVτ₂V U V A) (hmvPsi X A U V) biprod.inr biprod.inr
    (biprod.inr_map (relMVτ₂U U V A) (relMVτ₂V U V A)).symm

/-- The canonical isomorphism `C^{U,V}(U ∩ V, U ∩ V ∩ A) ⟶ coker τ₂U ⊞ coker τ₂V`, obtained from
the universal property of `cokernel (biprod.map τ₂U τ₂V)`. -/
abbrev cokerE (X : TopCat) (A U V : Set X) :
    cokernel (hmvPsi X A U V) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) :=
  biprod.lift (cokerD₁ X A U V) (cokerD₂ X A U V)

/-- The inverse of `cokerE`. -/
abbrev cokerF (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) ⟶ cokernel (hmvPsi X A U V) :=
  biprod.desc (cokerM₁ X A U V) (cokerM₂ X A U V)

/-- The defining rule of `cokerD₁`. -/
theorem cokerD₁_π (X : TopCat) (A U V : Set X) :
    cokernel.π (hmvPsi X A U V) ≫ cokerD₁ X A U V
      = biprod.fst ≫ cokernel.π (relMVτ₂U U V A) :=
  cokernel.π_desc _ _ _

/-- The defining rule of `cokerD₂`. -/
theorem cokerD₂_π (X : TopCat) (A U V : Set X) :
    cokernel.π (hmvPsi X A U V) ≫ cokerD₂ X A U V
      = biprod.snd ≫ cokernel.π (relMVτ₂V U V A) :=
  cokernel.π_desc _ _ _

/-- The defining rule of `cokerM₁`. -/
theorem cokerM₁_π (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂U U V A) ≫ cokerM₁ X A U V
      = (biprod.inl : smallInChains U V U ⟶ smallInChains U V U ⊞ smallInChains U V V)
          ≫ cokernel.π (hmvPsi X A U V) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The defining rule of `cokerM₂`. -/
theorem cokerM₂_π (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂V U V A) ≫ cokerM₂ X A U V
      = (biprod.inr : smallInChains U V V ⟶ smallInChains U V U ⊞ smallInChains U V V)
          ≫ cokernel.π (hmvPsi X A U V) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The `inl`-component of `cokerF`. -/
theorem inl_cokerF (X : TopCat) (A U V : Set X) :
    biprod.inl ≫ cokerF X A U V = cokerM₁ X A U V := by
  rw [cokerF]; exact biprod.inl_desc _ _

/-- The `inr`-component of `cokerF`. -/
theorem inr_cokerF (X : TopCat) (A U V : Set X) :
    biprod.inr ≫ cokerF X A U V = cokerM₂ X A U V := by
  rw [cokerF]; exact biprod.inr_desc _ _

/-- The defining rule of `cokerE`. -/
theorem cokerE_π (X : TopCat) (A U V : Set X) :
    cokernel.π (hmvPsi X A U V) ≫ cokerE X A U V
      = biprod.lift (biprod.fst ≫ cokernel.π (relMVτ₂U U V A))
          (biprod.snd ≫ cokernel.π (relMVτ₂V U V A)) := by
  rw [cokerE]
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst, cokernel.π_desc]
  · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd, cokernel.π_desc]

/-- The `inl`-component of `cokerE`. -/
theorem inl_cokerE (X : TopCat) (A U V : Set X) :
    (biprod.inl : smallInChains U V U ⟶ smallInChains U V U ⊞ smallInChains U V V)
        ≫ biprod.lift (biprod.fst ≫ cokernel.π (relMVτ₂U U V A))
            (biprod.snd ≫ cokernel.π (relMVτ₂V U V A))
      = cokernel.π (relMVτ₂U U V A)
          ≫ (biprod.inl : cokernel (relMVτ₂U U V A) ⟶
              cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst]
    rw [← Category.assoc, biprod.inl_fst, Category.id_comp]
    rw [Category.assoc, biprod.inl_fst, Category.comp_id]
  · rw [Category.assoc, biprod.lift_snd]
    rw [← Category.assoc, biprod.inl_snd, zero_comp]
    rw [Category.assoc, biprod.inl_snd, comp_zero]

/-- The `inr`-component of `cokerE`. -/
theorem inr_cokerE (X : TopCat) (A U V : Set X) :
    (biprod.inr : smallInChains U V V ⟶ smallInChains U V U ⊞ smallInChains U V V)
        ≫ biprod.lift (biprod.fst ≫ cokernel.π (relMVτ₂U U V A))
            (biprod.snd ≫ cokernel.π (relMVτ₂V U V A))
      = cokernel.π (relMVτ₂V U V A)
          ≫ (biprod.inr : cokernel (relMVτ₂V U V A) ⟶
              cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst]
    rw [← Category.assoc, biprod.inr_fst, zero_comp]
    rw [Category.assoc, biprod.inr_fst, comp_zero]
  · rw [Category.assoc, biprod.lift_snd]
    rw [← Category.assoc, biprod.inr_snd, Category.id_comp]
    rw [Category.assoc, biprod.inr_snd, Category.comp_id]

/-- `cokerF` is a right inverse of `cokerE`. -/
theorem cokerE_cokerF (X : TopCat) (A U V : Set X) :
    cokerE X A U V ≫ cokerF X A U V = 𝟙 (cokernel (hmvPsi X A U V)) := by
  apply (cancel_epi (cokernel.π (hmvPsi X A U V))).1
  rw [Category.comp_id]
  rw [← Category.assoc, cokerE_π, cokerF, biprod.lift_desc]
  simp only [Category.assoc, cokerM₁_π, cokerM₂_π]
  simp only [← Category.assoc]
  rw [← Preadditive.add_comp, biprod.total, Category.id_comp]

/-- `cokerF` is a left inverse of `cokerE`. -/
theorem cokerF_cokerE (X : TopCat) (A U V : Set X) :
    cokerF X A U V ≫ cokerE X A U V
      = 𝟙 (cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) := by
  rw [cokerE]
  apply biprod.hom_ext'
  · apply (cancel_epi (cokernel.π (relMVτ₂U U V A))).1
    rw [Category.comp_id]
    rw [← Category.assoc (biprod.inl) (cokerF X A U V)
      (biprod.lift (cokerD₁ X A U V) (cokerD₂ X A U V)), inl_cokerF]
    rw [← Category.assoc (cokernel.π (relMVτ₂U U V A)) (cokerM₁ X A U V)
      (biprod.lift (cokerD₁ X A U V) (cokerD₂ X A U V)), cokerM₁_π]
    rw [Category.assoc, cokerE_π]
    exact inl_cokerE X A U V
  · apply (cancel_epi (cokernel.π (relMVτ₂V U V A))).1
    rw [Category.comp_id]
    rw [← Category.assoc (biprod.inr) (cokerF X A U V)
      (biprod.lift (cokerD₁ X A U V) (cokerD₂ X A U V)), inr_cokerF]
    rw [← Category.assoc (cokernel.π (relMVτ₂V U V A)) (cokerM₂ X A U V)
      (biprod.lift (cokerD₁ X A U V) (cokerD₂ X A U V)), cokerM₂_π]
    rw [Category.assoc, cokerE_π]
    exact inr_cokerE X A U V

/-- The canonical isomorphism `coker (biprod.map τ₂U τ₂V) ≅ coker τ₂U ⊞ coker τ₂V`. -/
noncomputable def cokerIso (X : TopCat) (A U V : Set X) :
    cokernel (hmvPsi X A U V) ≅
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) :=
  ⟨cokerE X A U V, cokerF X A U V, cokerE_cokerF X A U V, cokerF_cokerE X A U V⟩

/-! ### The canonical maps of the two relative complexes, in the `cokernel` spelling -/

/-- `γ` with its source and target spelled out as cokernels. -/
abbrev hmvGamma (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₁ U V A) ⟶ cokernel (relMVτ₂U U V A) :=
  HMV.gamma X A U V

/-- `δ` with its source and target spelled out as cokernels. -/
abbrev hmvDelta (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₁ U V A) ⟶ cokernel (relMVτ₂V U V A) :=
  HMV.delta X A U V

/-- `αU` with its source and target spelled out as cokernels. -/
abbrev hmvAlphaU (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂U U V A) ⟶ cokernel (smallInToSmall U V A) :=
  HMV.alphaU X A U V

/-- `αV` with its source and target spelled out as cokernels. -/
abbrev hmvAlphaV (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂V U V A) ⟶ cokernel (smallInToSmall U V A) :=
  HMV.alphaV X A U V

/-- The defining rule of `hmvGamma`. -/
theorem hmvGamma_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₁ U V A) ≫ hmvGamma X A U V
      = subInclChain U V Set.inter_subset_left ≫ cokernel.π (relMVτ₂U U V A) :=
  HMV.gamma_comp X A U V

/-- The defining rule of `hmvDelta`. -/
theorem hmvDelta_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₁ U V A) ≫ hmvDelta X A U V
      = subInclChain U V Set.inter_subset_right ≫ cokernel.π (relMVτ₂V U V A) :=
  HMV.delta_comp X A U V

/-- The defining rule of `hmvAlphaU`. -/
theorem hmvAlphaU_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂U U V A) ≫ hmvAlphaU X A U V
      = smallInToSmall U V U ≫ cokernel.π (smallInToSmall U V A) :=
  HMV.alphaU_comp X A U V

/-- The defining rule of `hmvAlphaV`. -/
theorem hmvAlphaV_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂V U V A) ≫ hmvAlphaV X A U V
      = smallInToSmall U V V ≫ cokernel.π (smallInToSmall U V A) :=
  HMV.alphaV_comp X A U V

/-- The `fst`-component of `cokerLeft` composed with the isomorphism is `γ`. -/
theorem cokerLeft_cokerD₁ (X : TopCat) (A U V : Set X) :
    cokerLeft X A U V ≫ cokerD₁ X A U V = hmvGamma X A U V := by
  rw [← cancel_epi (cokernel.π (relMVτ₁ U V A))]
  simp only [← Category.assoc, cokerLeft_comp]
  rw [Category.assoc, cokerD₁_π, ← Category.assoc]
  simp only [mvLeftSmall, biprod.lift_fst]
  rw [← hmvGamma_comp]

/-- The `snd`-component of `cokerLeft` composed with the isomorphism is `δ`. -/
theorem cokerLeft_cokerD₂ (X : TopCat) (A U V : Set X) :
    cokerLeft X A U V ≫ cokerD₂ X A U V = hmvDelta X A U V := by
  rw [← cancel_epi (cokernel.π (relMVτ₁ U V A))]
  simp only [← Category.assoc, cokerLeft_comp]
  rw [Category.assoc, cokerD₂_π, ← Category.assoc]
  simp only [mvLeftSmall, biprod.lift_snd]
  rw [← hmvDelta_comp]

/-- The `inl`-component of `cokerRight` composed with the inverse isomorphism is `αU`. -/
theorem cokerM₁_cokerRight (X : TopCat) (A U V : Set X) :
    cokerM₁ X A U V ≫ cokerRight X A U V = hmvAlphaU X A U V := by
  rw [← cancel_epi (cokernel.π (relMVτ₂U U V A))]
  rw [← Category.assoc (cokernel.π (relMVτ₂U U V A)) (cokerM₁ X A U V)
    (cokerRight X A U V), cokerM₁_π, Category.assoc, cokerRight_comp, ← Category.assoc]
  simp only [mvRightSmall, biprod.inl_desc]
  rw [← hmvAlphaU_comp]

/-- The `inr`-component of `cokerRight` composed with the inverse isomorphism is `-αV`. -/
theorem cokerM₂_cokerRight (X : TopCat) (A U V : Set X) :
    cokerM₂ X A U V ≫ cokerRight X A U V = -(hmvAlphaV X A U V) := by
  rw [← cancel_epi (cokernel.π (relMVτ₂V U V A))]
  rw [← Category.assoc (cokernel.π (relMVτ₂V U V A)) (cokerM₂ X A U V)
    (cokerRight X A U V), cokerM₂_π, Category.assoc, cokerRight_comp, ← Category.assoc]
  simp only [mvRightSmall, biprod.inr_desc]
  rw [Preadditive.neg_comp, ← hmvAlphaV_comp, Preadditive.comp_neg]

/-! ### The automorphism `diag (1, -1)` of the middle term -/

/-- The automorphism `diag (1, -1)` of `coker τ₂U ⊞ coker τ₂V`, characterised by
`σ ≫ fst = fst` and `σ ≫ snd = -snd`. -/
abbrev sigmaAut (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) :=
  biprod.lift (biprod.fst : cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)
      ⟶ cokernel (relMVτ₂U U V A))
    (-(biprod.snd : cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)
      ⟶ cokernel (relMVτ₂V U V A)))

/-- The inverse of `sigmaAut`, characterised by `inl ≫ σ⁻¹ = inl` and `inr ≫ σ⁻¹ = -inr`. -/
abbrev sigmaInv (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) :=
  biprod.desc (biprod.inl : cokernel (relMVτ₂U U V A) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A))
    (-(biprod.inr : cokernel (relMVτ₂V U V A) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)))

/-- The defining rule of `sigmaAut` on the first summand. -/
theorem sigmaAut_fst (X : TopCat) (A U V : Set X) :
    sigmaAut X A U V ≫ (biprod.fst : cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)
      ⟶ cokernel (relMVτ₂U U V A))
      = biprod.fst := by
  rw [sigmaAut, biprod.lift_fst]

/-- The defining rule of `sigmaAut` on the second summand. -/
theorem sigmaAut_snd (X : TopCat) (A U V : Set X) :
    sigmaAut X A U V ≫ (biprod.snd : cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)
      ⟶ cokernel (relMVτ₂V U V A))
      = -(biprod.snd) := by
  rw [sigmaAut, biprod.lift_snd]

/-- The defining rule of `sigmaInv` on the first summand. -/
theorem sigmaInv_inl (X : TopCat) (A U V : Set X) :
    (biprod.inl : cokernel (relMVτ₂U U V A) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) ≫ sigmaInv X A U V
      = biprod.inl := by
  rw [sigmaInv, biprod.inl_desc]

/-- The defining rule of `sigmaInv` on the second summand. -/
theorem sigmaInv_inr (X : TopCat) (A U V : Set X) :
    (biprod.inr : cokernel (relMVτ₂V U V A) ⟶
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) ≫ sigmaInv X A U V
      = -(biprod.inr) := by
  rw [sigmaInv, biprod.inr_desc]

/-- `sigmaInv` is a right inverse of `sigmaAut`. -/
theorem sigmaAut_sigmaInv (X : TopCat) (A U V : Set X) :
    sigmaAut X A U V ≫ sigmaInv X A U V
      = 𝟙 (cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) := by
  rw [sigmaAut, sigmaInv, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
    biprod.total]

/-- The `inl`-component of `sigmaAut` is the identity. -/
theorem inl_sigmaAut (X : TopCat) (A U V : Set X) :
    (biprod.inl : cokernel (relMVτ₂U U V A) ⟶
        cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) ≫ sigmaAut X A U V
      = biprod.inl := by
  apply biprod.hom_ext
  · rw [Category.assoc, sigmaAut_fst, biprod.inl_fst]
  · rw [Category.assoc, sigmaAut_snd, Preadditive.comp_neg, biprod.inl_snd, neg_zero]

/-- The `inr`-component of `sigmaAut` is the negation of the identity. -/
theorem inr_sigmaAut (X : TopCat) (A U V : Set X) :
    (biprod.inr : cokernel (relMVτ₂V U V A) ⟶
        cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) ≫ sigmaAut X A U V
      = -(biprod.inr) := by
  apply biprod.hom_ext
  · rw [Category.assoc, sigmaAut_fst, Preadditive.neg_comp, biprod.inr_fst, neg_zero]
  · rw [Category.assoc, sigmaAut_snd, Preadditive.comp_neg, Preadditive.neg_comp,
      biprod.inr_snd]

/-- `sigmaInv` is a left inverse of `sigmaAut`. -/
theorem sigmaInv_sigmaAut (X : TopCat) (A U V : Set X) :
    sigmaInv X A U V ≫ sigmaAut X A U V
      = 𝟙 (cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, sigmaInv_inl, inl_sigmaAut, Category.comp_id]
  · rw [← Category.assoc, sigmaInv_inr, Preadditive.neg_comp, inr_sigmaAut, neg_neg,
      Category.comp_id]

/-- The automorphism `diag (1, -1)`, as an isomorphism. -/
noncomputable def sigmaIso (X : TopCat) (A U V : Set X) :
    (cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) ≅
      (cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A)) :=
  ⟨sigmaAut X A U V, sigmaInv X A U V, sigmaAut_sigmaInv X A U V,
    sigmaInv_sigmaAut X A U V⟩

/-- The composite isomorphism used to transport the cokernel sequence. -/
noncomputable def cokerIsoSigma (X : TopCat) (A U V : Set X) :
    cokernel (hmvPsi X A U V) ≅
      cokernel (relMVτ₂U U V A) ⊞ cokernel (relMVτ₂V U V A) :=
  ⟨cokerE X A U V ≫ sigmaAut X A U V, sigmaInv X A U V ≫ cokerF X A U V, by
    rw [Category.assoc (cokerE X A U V) (sigmaAut X A U V) (sigmaInv X A U V ≫ cokerF X A U V),
      ← Category.assoc (sigmaAut X A U V) (sigmaInv X A U V) (cokerF X A U V),
      sigmaAut_sigmaInv, Category.id_comp, cokerE_cokerF],
   by
    rw [Category.assoc (sigmaInv X A U V) (cokerF X A U V) (cokerE X A U V ≫ sigmaAut X A U V),
      ← Category.assoc (cokerF X A U V) (cokerE X A U V) (sigmaAut X A U V),
      cokerF_cokerE, Category.id_comp, sigmaInv_sigmaAut]⟩

/-- **The chain level honest relative Mayer–Vietoris sequence is short exact.** -/
theorem hmvChainSES (X : TopCat) (A U V : Set X) :
    (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V)
      (hmv_chain_zero X A U V)).ShortExact := by
  have hS₀ : (ShortComplex.mk (cokerLeft X A U V) (cokerRight X A U V)
      (cokerLeft_comp_cokerRight X A U V)).ShortExact :=
    cokernelMap_shortExact (mvSmallA_shortExact U V A) (mvSmall_shortExact U V) (relMVv U V A)
      (mono_subInclChain U V Set.inter_subset_left)
      (mono_biprod_map (mono_subInclChain U V Set.inter_subset_left)
        (mono_subInclChain U V Set.inter_subset_left))
      (mono_smallInToSmall U V A) (cokerLeft_comp X A U V) (cokerRight_comp X A U V)
      (cokerLeft_comp_cokerRight X A U V)
  have hzero : (cokerLeft X A U V ≫ (cokerIsoSigma X A U V).hom) ≫
      ((cokerIsoSigma X A U V).inv ≫ cokerRight X A U V) = 0 := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, cokerLeft_comp_cokerRight]
  have hiso : (ShortComplex.mk (cokerLeft X A U V) (cokerRight X A U V)
        (cokerLeft_comp_cokerRight X A U V)) ≅
      (ShortComplex.mk (cokerLeft X A U V ≫ (cokerIsoSigma X A U V).hom)
        ((cokerIsoSigma X A U V).inv ≫ cokerRight X A U V) hzero) :=
    ShortComplex.isoMk (Iso.refl _) (cokerIsoSigma X A U V) (Iso.refl _)
      (by rw [show (Iso.refl _).hom = 𝟙 _ from rfl, Category.id_comp])
      (by rw [show (Iso.refl _).hom = 𝟙 _ from rfl, Category.comp_id, Iso.hom_inv_id_assoc])
  have hSconj : (ShortComplex.mk (cokerLeft X A U V ≫ (cokerIsoSigma X A U V).hom)
      ((cokerIsoSigma X A U V).inv ≫ cokerRight X A U V) hzero).ShortExact :=
    ShortComplex.shortExact_of_iso hiso hS₀
  have hfE : cokerLeft X A U V ≫ (cokerIsoSigma X A U V).hom = hmvChainLeft X A U V := by
    have h : cokerLeft X A U V ≫ cokerE X A U V ≫ sigmaAut X A U V
        = biprod.lift (hmvGamma X A U V) (-(hmvDelta X A U V)) := by
      apply biprod.hom_ext
      · simp only [sigmaAut, Category.assoc, biprod.lift_fst, cokerLeft_cokerD₁]
      · simp only [sigmaAut, Category.assoc, Preadditive.comp_neg, biprod.lift_snd,
          cokerLeft_cokerD₂]
    rw [show (cokerIsoSigma X A U V).hom = cokerE X A U V ≫ sigmaAut X A U V from rfl, h]
    rfl
  have hFe : (cokerIsoSigma X A U V).inv ≫ cokerRight X A U V = hmvChainRight X A U V := by
    have h : (sigmaInv X A U V ≫ cokerF X A U V) ≫ cokerRight X A U V
        = biprod.desc (hmvAlphaU X A U V) (hmvAlphaV X A U V) := by
      rw [Category.assoc]
      apply biprod.hom_ext'
      · simp only [sigmaInv, ← Category.assoc, biprod.inl_desc, inl_cokerF, cokerM₁_cokerRight]
      · simp only [sigmaInv, ← Category.assoc, biprod.inr_desc, Preadditive.neg_comp,
          inr_cokerF, cokerM₂_cokerRight, neg_neg]
    rw [show (cokerIsoSigma X A U V).inv = sigmaInv X A U V ≫ cokerF X A U V from rfl, h]
    rfl
  have hiso₂ : (ShortComplex.mk (cokerLeft X A U V ≫ (cokerIsoSigma X A U V).hom)
        ((cokerIsoSigma X A U V).inv ≫ cokerRight X A U V) hzero) ≅
      (ShortComplex.mk (hmvChainLeft X A U V) (hmvChainRight X A U V)
        (hmv_chain_zero X A U V)) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, hfE])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, hFe])
  exact ShortComplex.shortExact_of_iso hiso₂ hSconj

theorem hmv_shortExact (X : TopCat) (A U V : Set X) :
    (CategoryTheory.ShortComplex.mk (Work.Cohomology.hmvF X A U V)
      (Work.Cohomology.hmvG X A U V) (Work.Cohomology.hmv_comp X A U V)).ShortExact :=
  hmv_shortExact_of_chain X A U V (hmv_chain_zero X A U V) (hmvChainSES X A U V)

end

end Work.Cohomology
