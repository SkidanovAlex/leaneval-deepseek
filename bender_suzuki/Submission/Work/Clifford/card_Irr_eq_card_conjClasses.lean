import Mathlib
import Submission.Work.Clifford.CharPair
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal
import Submission.Work.CharCore.star_Irr
import Submission.Work.CharCore.fdRep_simple_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of irreducible characters equals the number of conjugacy classes

For a finite group `G`, the number of irreducible complex characters equals the number of
conjugacy classes.  This is the "`Irr G` is a basis of the class functions" theorem, stated
for the set `Work.Clifford.Irr G` of characters of simple finite dimensional complex
representations.

## The argument

1. The space of class functions is `|ConjClasses G|`-dimensional
   (`Work.Clifford.finrank_classFun_eq_card_conjClasses`).
2. The bilinear character pairing `Work.Clifford.charPair` is orthonormal on
   `Work.CharCore.Irr G` (`Work.Clifford.charPair_eq_ite_of_mem_Irr`): this is Mathlib's
   `Representation.char_orthonormal`, and it needs no knowledge of `star (χ g) = χ g⁻¹`.
3. A class function orthogonal to every irreducible character vanishes
   (`Work.Clifford.charPair_eq_zero_of_classFun`): this is
   `Work.CharCore.classFun_eq_zero_of_orthogonal` transported along `Work.CharCore.star_Irr`.
4. Hence `Work.CharCore.Irr G` has cardinality the dimension of the space of class functions
   (`Work.Clifford.card_Irr_eq_finrank_classFun`).

The remaining step is the bridge between the `ℂ[G]`-module formulation of `Work.CharCore`
(whose simple submodules of the regular module live in an arbitrary universe) and the
`FDRep`-categorical set `Work.Clifford.Irr G` (whose carriers live in the base universe):
`Work.Clifford.mem_Irr_iff_fdrep`.  The only non-formal input is
`Work.Clifford.exists_fdRep_char_eq_ofModule'`, the observation that the character of a
finite dimensional `ℂ[G]`-module is the character of a representation on `ℂⁿ` (transport
along a basis).
-/

noncomputable section
set_option linter.unusedSectionVars false
open Classical Finset

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G]

/-! ## Orthogonality -/

theorem charPair_add_left (f₁ f₂ g : G → ℂ) :
    charPair (f₁ + f₂) g = charPair f₁ g + charPair f₂ g := by
  simp only [charPair, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem charPair_smul_left (c : ℂ) (f g : G → ℂ) :
    charPair (c • f) g = c * charPair f g := by
  simp only [charPair, Pi.smul_apply, smul_eq_mul]
  have h : (∑ x : G, c * f x * g x⁻¹) = c * ∑ x : G, f x * g x⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [h]
  ring

theorem charPair_sub_left (f₁ f₂ g : G → ℂ) :
    charPair (f₁ - f₂) g = charPair f₁ g - charPair f₂ g := by
  have h : (f₁ - f₂ : G → ℂ) = f₁ + (-1 : ℂ) • f₂ := by ext x; simp [sub_eq_add_neg]
  rw [h, charPair_add_left, charPair_smul_left]
  ring

theorem charPair_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ) (g : G → ℂ) :
    charPair (∑ i ∈ s, c i • F i) g = ∑ i ∈ s, c i * charPair (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp [charPair]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, charPair_add_left, charPair_smul_left, ih]

/-- A class function which is orthogonal (for `charPair`) to every irreducible character is
zero. -/
theorem charPair_eq_zero_of_classFun {f : G → ℂ} (hf : Work.CharCore.IsClassFun f)
    (h : ∀ χ : G → ℂ, χ ∈ Work.CharCore.Irr G → charPair f χ = 0) : f = 0 := by
  refine Work.CharCore.classFun_eq_zero_of_orthogonal hf (fun χ hχ => ?_)
  rw [← h χ hχ, Work.CharCore.cfInner, charPair, Nat.card_eq_fintype_card]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by rw [Work.CharCore.star_Irr χ hχ x])

/-! ## `Irr G` is a basis of the class functions -/

/-- The irreducible characters are a basis of the space of class functions. -/
theorem card_Irr_eq_finrank_classFun :
    (Work.CharCore.Irr G).card = Module.finrank ℂ (Work.CharCore.classFunSubmodule G) := by
  classical
  set S := Work.CharCore.Irr G with hS
  have hcl : ∀ χ : ↥S, Work.CharCore.IsClassFun (χ : G → ℂ) :=
    fun χ => Work.CharCore.isClassFun_of_mem_Irr χ.2
  -- the pairing against the irreducibles, as a linear map
  let Φ : Work.CharCore.classFunSubmodule G →ₗ[ℂ] (↥S → ℂ) :=
    { toFun := fun f => fun χ => charPair (f : G → ℂ) χ
      map_add' := by
        intro f₁ f₂
        funext χ
        show charPair ((f₁ + f₂ : Work.CharCore.classFunSubmodule G) : G → ℂ) χ =
          charPair (f₁ : G → ℂ) χ + charPair (f₂ : G → ℂ) χ
        rw [Submodule.coe_add, charPair_add_left]
      map_smul' := by
        intro c f
        funext χ
        show charPair ((c • f : Work.CharCore.classFunSubmodule G) : G → ℂ) χ =
          c * charPair (f : G → ℂ) χ
        rw [Submodule.coe_smul, charPair_smul_left] }
  have hΦinj : Function.Injective Φ := by
    intro f g hfg
    have h0 : ((f - g : Work.CharCore.classFunSubmodule G) : G → ℂ) = 0 := by
      refine charPair_eq_zero_of_classFun
        (f := ((f - g : Work.CharCore.classFunSubmodule G) : G → ℂ))
        (f - g).2 (fun χ hχ => ?_)
      have hthis := congrFun hfg ⟨χ, hχ⟩
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at hthis
      rw [Submodule.coe_sub, charPair_sub_left, hthis, sub_self]
    have hsub : f - g = 0 := Subtype.ext h0
    exact sub_eq_zero.mp hsub
  -- the span of the irreducibles, as a linear map
  let Ψ : (↥S → ℂ) →ₗ[ℂ] Work.CharCore.classFunSubmodule G :=
    { toFun := fun a => ⟨fun x => ∑ χ : ↥S, a χ * (χ : G → ℂ) x, by
        intro x y
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [hcl χ x y]⟩
      map_add' := by
        intro a b
        ext x
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Submodule.coe_add]
      map_smul' := by
        intro c a
        ext x
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Submodule.coe_smul,
          RingHom.id_apply]
        exact Finset.sum_congr rfl (fun χ _ => by ring) }
  have hcoe : ∀ a : ↥S → ℂ, ((Ψ a : Work.CharCore.classFunSubmodule G) : G → ℂ) =
      ∑ χ : ↥S, a χ • (χ : G → ℂ) := by
    intro a
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hΦΨ : ∀ a : ↥S → ℂ, Φ (Ψ a) = a := by
    intro a
    funext χ₀
    show charPair ((Ψ a : Work.CharCore.classFunSubmodule G) : G → ℂ) χ₀ = a χ₀
    rw [hcoe a, charPair_sum_left]
    rw [Finset.sum_eq_single χ₀]
    · rw [charPair_eq_ite_of_mem_Irr χ₀.2 χ₀.2, if_pos rfl, mul_one]
    · intro χ _ hχ
      rw [charPair_eq_ite_of_mem_Irr χ.2 χ₀.2, if_neg (fun h => hχ (Subtype.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ χ₀) h
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have hthis := congrArg Φ hab
    rwa [hΦΨ, hΦΨ] at hthis
  have h1 : Module.finrank ℂ (Work.CharCore.classFunSubmodule G) ≤ Module.finrank ℂ (↥S → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hΦinj
  have h2 : Module.finrank ℂ (↥S → ℂ) ≤ Module.finrank ℂ (Work.CharCore.classFunSubmodule G) :=
    LinearMap.finrank_le_finrank_of_injective hΨinj
  have hfun : Module.finrank ℂ (↥S → ℂ) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card ℂ, Fintype.card_coe]
  omega

/-! ## The bridge to `FDRep` -/

/-- The character of a finite dimensional `ℂ[G]`-module is the character of an honest
`FDRep ℂ G`.  This is the (universe) transport along a `ℂ`-basis: replace `M` by `ℂⁿ`. -/
theorem exists_fdRep_char_eq_ofModule' {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (Work.CharCore.groupAlgebra G) M] [IsScalarTower ℂ (Work.CharCore.groupAlgebra G) M]
    [FiniteDimensional ℂ M] [IsSimpleModule (Work.CharCore.groupAlgebra G) M] :
    ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧
      V.character = (Representation.ofModule' (k := ℂ) (G := G) M).character := by
  classical
  set n := Module.finrank ℂ M with hn
  let b : Module.Basis (Fin n) ℂ M := Module.finBasis ℂ M
  let e : M ≃ₗ[ℂ] (Fin n → ℂ) := b.equivFun
  let ψ : Work.CharCore.groupAlgebra G →ₐ[ℂ] Module.End ℂ M :=
    Representation.asAlgebraHom (Representation.ofModule' (k := ℂ) (G := G) M)
  let φ : Work.CharCore.groupAlgebra G →ₐ[ℂ] Module.End ℂ (Fin n → ℂ) :=
    (LinearEquiv.conjAlgEquiv ℂ e).toAlgHom.comp ψ
  letI : Module (Work.CharCore.groupAlgebra G) (Fin n → ℂ) :=
    Module.compHom _ (φ : Work.CharCore.groupAlgebra G →+* Module.End ℂ (Fin n → ℂ))
  haveI hST : IsScalarTower ℂ (Work.CharCore.groupAlgebra G) (Fin n → ℂ) := by
    refine ⟨fun c r x => ?_⟩
    show φ (c • r) x = c • (φ r x)
    rw [map_smul, LinearMap.smul_apply]
  have hφ_eq : ∀ r : Work.CharCore.groupAlgebra G, φ r = e.conj (ψ r) := by
    intro r
    simp only [φ, ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, LinearEquiv.conjAlgEquiv_apply,
      LinearEquiv.conj_apply, LinearMap.comp_assoc]
  have hesmul : ∀ (r : Work.CharCore.groupAlgebra G) (x : M), e (r • x) = r • e x := by
    intro r x
    show e (r • x) = φ r (e x)
    rw [hφ_eq r, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact congrArg e (asAlgebraHom_ofModule'_apply r x).symm
  let eLin : M ≃ₗ[Work.CharCore.groupAlgebra G] (Fin n → ℂ) :=
    { e with map_smul' := hesmul }
  have hsimple : IsSimpleModule (Work.CharCore.groupAlgebra G) (Fin n → ℂ) :=
    IsSimpleModule.congr (e := eLin.symm)
  let ρ' : Representation ℂ G (Fin n → ℂ) :=
    Representation.ofModule' (k := ℂ) (G := G) (Fin n → ℂ)
  haveI hρ'irr : ρ'.IsIrreducible := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    exact isSimpleModule_ofModule'_asModule_iff.mpr hsimple
  refine ⟨FDRep.of ρ', (Work.CharCore.fdRep_simple_iff (FDRep.of ρ')).mpr ?_, ?_⟩
  · rw [FDRep.of_ρ']; exact hρ'irr
  · funext g
    show LinearMap.trace ℂ (Fin n → ℂ) (ρ' g) =
      LinearMap.trace ℂ M ((Representation.ofModule' (k := ℂ) (G := G) M) g)
    have hρ'g : ρ' g = φ (MonoidAlgebra.single g (1 : ℂ)) := by
      apply LinearMap.ext
      intro x
      show (Representation.ofModule' (k := ℂ) (G := G) (Fin n → ℂ)) g x =
        φ (MonoidAlgebra.single g (1 : ℂ)) x
      rw [← Representation.asAlgebraHom_single_one
        (Representation.ofModule' (k := ℂ) (G := G) (Fin n → ℂ)) g]
      exact asAlgebraHom_ofModule'_apply (MonoidAlgebra.single g (1 : ℂ)) x
    have hφg : φ (MonoidAlgebra.single g (1 : ℂ)) =
        e.conj ((Representation.ofModule' (k := ℂ) (G := G) M) g) := by
      rw [hφ_eq (MonoidAlgebra.single g 1),
        Representation.asAlgebraHom_single_one]
    rw [hρ'g, hφg, LinearMap.trace_conj']

/-- The bridge: `Work.CharCore.Irr G` consists exactly of the characters of the simple
objects of `FDRep ℂ G`. -/
theorem mem_Irr_iff_fdrep_aux (χ : G → ℂ) :
    χ ∈ Work.CharCore.Irr G ↔
      ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = χ := by
  classical
  constructor
  · intro hχ
    obtain ⟨N, hN, rfl⟩ := (Work.CharCore.mem_Irr_iff_exists χ).mp hχ
    haveI := Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
    exact exists_fdRep_char_eq_ofModule' (M := ↥N)
  · rintro ⟨V, hV, rfl⟩
    exact Work.CharCore.irreducible_character_mem_Irr V.ρ
      ((Work.CharCore.fdRep_simple_iff V).mp hV)

/-! ## The main theorem -/

theorem card_Irr_eq_card_conjClasses {G : Type*} [Group G] [Fintype G] :
    Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} = Nat.card (ConjClasses G) := by
  classical
  have hset : (Work.CharCore.Irr G : Set (G → ℂ)) = Work.Clifford.Irr G := by
    ext χ
    exact mem_Irr_iff_fdrep_aux χ
  have he : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} ≃ ↥(Work.CharCore.Irr G) :=
    { toFun := fun x => ⟨x.1, hset.ge x.2⟩
      invFun := fun x => ⟨x.1, hset.le x.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [card_Irr_eq_finrank_classFun, finrank_classFun_eq_card_conjClasses]

end Work.Clifford
