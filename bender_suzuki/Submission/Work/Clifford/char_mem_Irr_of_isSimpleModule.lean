import Mathlib
import Submission.Work.Clifford.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.char_mem_Irr_of_isSimpleModule`

The character of a simple finite dimensional `ℂ[G]`-module lies in the set
`Work.Clifford.Irr G` of irreducible complex characters of `G`.

The mathematical content is Schur's lemma: a simple `ℂ[G]`-module `M` has no proper
non-trivial `ℂ[G]`-submodules, so the `ℂ[G]`-submodule of `M` spanned by the image of a
morphism `f : Y ⟶ M` of `FDRep ℂ G` with `f ≠ 0` is everything; hence a nonzero monomorphism
of `FDRep ℂ G` into `M` is an isomorphism, which is precisely simplicity of `M` in the
category `FDRep ℂ G`.

One subtlety is that `FDRep ℂ G` is built from `ℂ`-vector spaces in the *same* universe as
`ℂ`, whereas the statement quantifies over `ℂ[G]`-modules in an arbitrary universe.  We
therefore transport the module structure along a `ℂ`-linear isomorphism `M ≃ₗ[ℂ] (Fin n → ℂ)`
(Schur's lemma is invariant under isomorphism, and so is the character).
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical
open scoped MonoidAlgebra
open CategoryTheory

namespace Work.Clifford

universe u

section Prep

variable {G : Type u} [Group G]

/-- `Representation.ofModule'` acts by multiplication by `MonoidAlgebra.of ℂ G g`. -/
theorem ofModule'_apply_of {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] (g : G) (v : M) :
    (Representation.ofModule' (k := ℂ) (G := G) M) g v = MonoidAlgebra.of ℂ G g • v := by
  show (MonoidAlgebra.lift ℂ (M →ₗ[ℂ] M) G).symm (Algebra.lsmul ℂ (B := ℂ) (M := M)) g v = _
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply, Algebra.lsmul_apply]

/-- `single g c` acts as `c` times the action of `of g`. -/
theorem single_smul_eq {M : Type*} [AddCommMonoid M] [Module ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] (g : G) (c : ℂ) (v : M) :
    (MonoidAlgebra.single g c : ℂ[G]) • v = c • (MonoidAlgebra.of ℂ G g • v) := by
  have h : (MonoidAlgebra.single g c : ℂ[G]) = c • MonoidAlgebra.of ℂ G g := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rw [h, smul_assoc]

/-- The underlying linear map of a morphism of `FDRep` intertwines the actions. -/
theorem hom_apply_action {A B : FDRep ℂ G} (f : A ⟶ B) (g : G) (x : ↥A.V) :
    (ConcreteCategory.hom f.hom) (FDRep.ρ A g x) = FDRep.ρ B g ((ConcreteCategory.hom f.hom) x) := by
  have h1 := ConcreteCategory.congr_hom (f.comm g) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  exact h1

/-- The character of `FDRep.of ρ` is the character of `ρ`. -/
theorem character_fdRep_of {M : Type} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) :
    (FDRep.of ρ).character = ρ.character := by
  ext g
  rw [FDRep.character, Representation.character, FDRep.of_ρ']

end Prep

section Simple

variable {G : Type u} [Group G]

/-- **Schur's lemma, categorical form.**  If `M` is a simple finite dimensional
`ℂ[G]`-module in the same universe as `ℂ`, then it is a simple object of `FDRep ℂ G`. -/
theorem simple_fdRep_ofModule' (M : Type) [AddCommGroup M] [Module ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] [FiniteDimensional ℂ M]
    (h : IsSimpleModule ℂ[G] M) :
    CategoryTheory.Simple (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)) := by
  haveI := h
  haveI : IsSimpleOrder (Submodule ℂ[G] M) := (isSimpleModule_iff ℂ[G] M).mp h
  set W := FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M) with hW
  have hact : ∀ (g : G) (v : M), FDRep.ρ W g v = MonoidAlgebra.of ℂ G g • v := by
    intro g v
    show FDRep.ρ (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)) g v
      = MonoidAlgebra.of ℂ G g • v
    rw [FDRep.of_ρ', ofModule'_apply_of]
  refine CategoryTheory.Simple.mk fun {Y} f hfmono => ⟨?_, ?_⟩
  · -- a nonzero isomorphism cannot be the zero morphism
    intro hfiso hf0
    exfalso
    have h1 : (𝟙 W : W ⟶ W) = 0 := by
      calc 𝟙 W = inv f ≫ f := (IsIso.inv_hom_id f).symm
        _ = inv f ≫ 0 := congrArg (fun u : Y ⟶ W => inv f ≫ u) hf0
        _ = 0 := CategoryTheory.Limits.HasZeroMorphisms.comp_zero _ _
    have h3 : (𝟙 W.V : W.V ⟶ W.V) = 0 := by
      have h4 := congrArg (fun u : W ⟶ W => u.hom) h1
      simpa [Action.id_hom, Action.zero_hom] using h4
    have h5 : (𝟙 W.V.obj : W.V.obj ⟶ W.V.obj) = 0 := by
      have h4 := congrArg (fun u : W.V ⟶ W.V => (ModuleCat.isFG ℂ).ι.map u) h3
      simpa using h4
    have h6 : Subsingleton ↥(W.V.obj) :=
      ModuleCat.isZero_iff_subsingleton.mp ((CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr h5)
    exact (not_subsingleton_iff_nontrivial.mpr (IsSimpleModule.nontrivial ℂ[G] M)) h6
  · -- a nonzero monomorphism is an isomorphism
    intro hfne
    have hepi : Epi f := by
      apply Preadditive.epi_of_cancel_zero f
      intro Z g hg
      let T : ↥Y.V →ₗ[ℂ] M := ConcreteCategory.hom f.hom
      let S : M →ₗ[ℂ] ↥Z.V := ConcreteCategory.hom g.hom
      have hST : ∀ y : ↥Y.V, S (T y) = 0 := by
        intro y
        have h1 : f.hom ≫ g.hom = 0 := by
          have h2 := congrArg (fun u : Y ⟶ Z => u.hom) hg
          simpa [Action.comp_hom, Action.zero_hom] using h2
        have h3 := ConcreteCategory.congr_hom h1 y
        rw [ConcreteCategory.comp_apply] at h3
        have h4 : ConcreteCategory.hom (0 : Y.V ⟶ Z.V) y = 0 := by
          show ConcreteCategory.hom (0 : Y.V ⟶ Z.V).hom y = 0
          rfl
        rw [h4] at h3
        exact h3
      have hcomm : ∀ (g : G) (y : ↥Y.V), T (FDRep.ρ Y g y) = MonoidAlgebra.of ℂ G g • T y := by
        intro g y
        have h1 := hom_apply_action f g y
        rw [hact g (T y)] at h1
        exact h1
      -- the range of `T` is a `ℂ[G]`-submodule of `M`
      let p : Submodule ℂ[G] M :=
        { __ := LinearMap.range T
          smul_mem' := fun r x hx => by
            obtain ⟨y, rfl⟩ := hx
            induction r using MonoidAlgebra.induction_linear with
            | zero => simp
            | add a b ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
            | single g c =>
                rw [single_smul_eq g c (T y)]
                rw [← hcomm g y]
                exact Submodule.smul_mem _ c (LinearMap.mem_range_self T _) }
      have hTne : T ≠ 0 := by
        intro hT0
        apply hfne
        have h1 : f.hom = 0 := by
          apply ConcreteCategory.ext
          show T = ConcreteCategory.hom (0 : Y.V ⟶ W.V)
          rw [hT0]
          show (0 : ↥Y.V →ₗ[ℂ] ↥W.V) = ConcreteCategory.hom (0 : Y.V ⟶ W.V).hom
          rfl
        exact Action.hom_ext f 0 (by rw [h1, Action.zero_hom])
      have hp_ne : p ≠ ⊥ := by
        intro hpbot
        apply hTne
        ext y
        have hy : T y ∈ (⊥ : Submodule ℂ[G] M) := by
          rw [← hpbot]
          exact ⟨y, rfl⟩
        simpa using hy
      have hp_top : p = ⊤ := (eq_bot_or_eq_top p).resolve_left hp_ne
      have hS0 : S = 0 := by
        ext x
        have hx : x ∈ p := by rw [hp_top]; exact Submodule.mem_top
        have hx' : x ∈ LinearMap.range T := hx
        obtain ⟨y, hy⟩ := hx'
        rw [← hy]
        exact hST y
      have hg0 : g.hom = 0 := by
        apply ConcreteCategory.ext
        show S = ConcreteCategory.hom (0 : W.V ⟶ Z.V)
        rw [hS0]
        show (0 : ↥W.V →ₗ[ℂ] ↥Z.V) = ConcreteCategory.hom (0 : W.V ⟶ Z.V).hom
        rfl
      exact Action.hom_ext g 0 (by rw [hg0, Action.zero_hom])
    exact isIso_of_mono_of_epi f

end Simple

section Main

/-- The character of a simple finite dimensional `ℂ[G]`-module lies in the set of irreducible
complex characters of `G`. -/
theorem char_mem_Irr_of_isSimpleModule {G : Type*} [Group G] [Fintype G] (M : Type*)
    [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [FiniteDimensional ℂ M] [IsSimpleModule (MonoidAlgebra ℂ G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).character ∈ Work.Clifford.Irr G := by
  -- move to the universe of `ℂ`
  let n := Module.finrank ℂ M
  let N := Fin n → ℂ
  have hfrn : Module.finrank ℂ N = n := by simp [N, n]
  let e : M ≃ₗ[ℂ] N := LinearEquiv.ofFinrankEq (R := ℂ) M N (by rw [hfrn])
  -- transport the `ℂ[G]`-module structure along `e`
  let φ : ℂ[G] →+* Module.End ℂ N :=
    (LinearEquiv.conjRingEquiv e).toRingHom.comp (Algebra.lsmul ℂ (B := ℂ) (M := M)).toRingHom
  letI : Module ℂ[G] N := Module.compHom N φ
  have hφ : ∀ (r : ℂ[G]) (w : N), r • w = e (r • e.symm w) := by
    intro r w
    show φ r w = e (r • e.symm w)
    rw [show φ r = (LinearEquiv.conjRingEquiv e) ((Algebra.lsmul ℂ (B := ℂ) (M := M)) r) from rfl,
      LinearEquiv.conjRingEquiv_apply_apply, Algebra.lsmul_apply]
  haveI : IsScalarTower ℂ ℂ[G] N :=
    ⟨fun c r w => by
      calc (c • r) • w = e ((c • r) • e.symm w) := hφ (c • r) w
        _ = e (c • (r • e.symm w)) := by rw [IsScalarTower.smul_assoc]
        _ = c • e (r • e.symm w) := by rw [map_smul]
        _ = c • (r • w) := by rw [hφ r w]⟩
  have hN : IsSimpleModule ℂ[G] N := by
    have e' : M ≃ₗ[ℂ[G]] N :=
      { toFun := e
        map_add' := e.map_add
        map_smul' := fun r m => by
          show e (r • m) = r • e m
          rw [hφ r (e m), e.symm_apply_apply]
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv }
    exact IsSimpleModule.congr e'.symm
  have hchar : (Representation.ofModule' (k := ℂ) (G := G) N).character
      = (Representation.ofModule' (k := ℂ) (G := G) M).character := by
    funext g
    rw [Representation.character, Representation.character]
    have key : e.conj ((Representation.ofModule' (k := ℂ) (G := G) M) g)
        = (Representation.ofModule' (k := ℂ) (G := G) N) g := by
      refine LinearMap.ext fun w => ?_
      rw [LinearEquiv.conj_apply_apply, ofModule'_apply_of, ofModule'_apply_of]
      exact (hφ (MonoidAlgebra.of ℂ G g) w).symm
    rw [← key, LinearMap.trace_conj']
  refine ⟨FDRep.of (Representation.ofModule' (k := ℂ) (G := G) N),
    simple_fdRep_ofModule' N hN, ?_⟩
  rw [character_fdRep_of]
  exact hchar

end Main

end Work.Clifford
