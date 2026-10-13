import Mathlib
import Submission.Work.DSG4a.Criterion
import Submission.Work.DSEQ0.exists_lift_of_quasiIso

/-!
# DSG4a: `IsSplitMono (Q.map cc) ↔ ChainSplit P cc` for a K-projective `P`

This is statement (1) of the "remaining work" section of
`Submission/Work/DSG4a/Criterion.lean`: for a K-projective complex `P` and a coaugmentation
`cc : A[0] ⟶ P`, the derived morphism `Q.map cc` is a split monomorphism in `D(A)` if and only
if `cc` splits at the chain level (`Criterion.ChainSplit P cc`).

The proof is assembled from three independent pieces:

* `homotopic_end_single_f_zero` : homotopic endomorphisms of the single complex `A[0]` agree
  in degree `0` (the complex is concentrated in degree `0`);
* `chainSplit_iff_exists_chainRetraction` : `ChainSplit P cc` is exactly the existence of a
  chain map `S : P ⟶ A[0]` with `cc ≫ S = 𝟙`;
* `isSplitMono_Q_map_iff_isSplitMono_quotient_map` : `Q.map cc` is split mono in `D(A)` iff
  `cc` is split mono in the homotopy category.  This is where K-projectivity of `P` enters:
  `Hom_K(P, A[0]) → Hom_D(QP, QA[0])` is bijective
  (`CochainComplex.IsKProjective.Qh_map_bijective`, consumed through
  `Work.DSEQ0.Q_map_surjective_of_isKProjective`), and `A[0]` is itself K-projective
  (`Work.DSEQ0.singleZ_isKProjective`).

The remaining assembly `isSplitMono_quotient_map_iff_chainSplit` combines the first two pieces:
a retraction of `q.map cc` in the homotopy category lifts (the quotient functor is full) to a
chain map `S : P ⟶ A[0]` with `cc ≫ S` homotopic to `𝟙`; homotopic endomorphisms of the single
complex agree in degree `0`, so `cc ≫ S = 𝟙` strictly.
-/

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.DSG4a

universe u

section ChainLevel

variable {A : Type u} [CommRing A]

/-- Homotopic endomorphisms of the single complex `A[0]` agree in degree `0`: the complex has
nothing in degrees `≠ 0`, so both `dNext 0` and `prevD 0` vanish on any homotopy. -/
theorem homotopic_end_single_f_zero
    {f g : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A) ⟶
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A)}
    (h : Homotopy f g) : f.f 0 = g.f 0 := by
  have hc := h.comm 0
  have hd : dNext (0 : ℤ) h.hom = 0 := by
    rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 from by
      rw [ComplexShape.up_Rel]; norm_num)]
    simp [HomologicalComplex.single_obj_d]
  have hp : prevD (0 : ℤ) h.hom = 0 := by
    rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 from by
      rw [ComplexShape.up_Rel]; norm_num)]
    simp [HomologicalComplex.single_obj_d]
  rw [hd, hp] at hc
  simpa using hc

/-- **The chain-level half.**  `ChainSplit P cc` says that some linear functional on `P.X 0`
kills `im (d⁻¹)` and takes the value `1` at the class of the unit; equivalently, `cc` has a
retraction in the category of cochain complexes (with target the single complex `A[0]`). -/
theorem chainSplit_iff_exists_chainRetraction
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) :
    Work.DSG4a.Criterion.ChainSplit P cc ↔
      ∃ S : P ⟶ (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A),
        cc ≫ S = 𝟙 _ := by
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  have heinv : (ConcreteCategory.hom e.inv) (1 : A) = (1 : A) := by
    dsimp only [e]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single]
  constructor
  · -- `ChainSplit P cc` gives a retraction `S : P ⟶ A[0]` with `cc ≫ S = 𝟙`.
    rintro ⟨s, hsd, hse⟩
    refine ⟨HomologicalComplex.mkHomToSingle (ModuleCat.ofHom s) ?_, ?_⟩
    · intro i hi
      rw [ComplexShape.up_Rel] at hi
      have hi' : i = -1 := by omega
      subst hi'
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
      simpa using hsd
    · apply HomologicalComplex.to_single_hom_ext (j := 0)
      rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f, HomologicalComplex.id_f]
      -- goal: `cc.f 0 ≫ (ModuleCat.ofHom s ≫ e.inv) = 𝟙 (K.X 0)`; we conjugate by `e`.
      have hehom : ∀ z : A,
          (ConcreteCategory.hom e.hom) ((ConcreteCategory.hom e.inv) z) = z := by
        intro z
        have h := congrArg (fun (f : ModuleCat.of A A ⟶ ModuleCat.of A A) =>
          (ConcreteCategory.hom f) z) (Iso.inv_hom_id e)
        rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
        exact h
      have hconj : e.inv ≫ (cc.f 0 ≫ (ModuleCat.ofHom s ≫ e.inv)) ≫ e.hom =
          𝟙 (ModuleCat.of A A) := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
        rw [heinv]
        rw [show (ConcreteCategory.hom (cc.f 0)) (1 : A) = Criterion.coaugElem P cc from rfl]
        rw [ModuleCat.ofHom_apply, hse]
        exact hehom 1
      have hX : e.hom ≫ (e.inv ≫ (cc.f 0 ≫ (ModuleCat.ofHom s ≫ e.inv)) ≫ e.hom) ≫ e.inv =
          cc.f 0 ≫ (ModuleCat.ofHom s ≫ e.inv) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
      rw [← hX, hconj, Category.id_comp, Iso.hom_inv_id]
  · -- A retraction `S` of `cc` gives the functional `S.f 0 ≫ e.hom`.
    rintro ⟨S, hS⟩
    refine ⟨ModuleCat.Hom.hom (S.f 0 ≫ e.hom), ?_, ?_⟩
    · -- `s ∘ d⁻¹ = 0`
      have hc : P.d (-1) 0 ≫ S.f 0 = 0 := by
        rw [← S.comm (-1) 0, HomologicalComplex.single_obj_d]
        simp
      have key : ModuleCat.Hom.hom (S.f 0) ∘ₗ ModuleCat.Hom.hom (P.d (-1) 0) = 0 := by
        rw [← ModuleCat.hom_comp, hc, ModuleCat.hom_zero]
      rw [ModuleCat.hom_comp, LinearMap.comp_assoc, key]
      simp
    · -- `s (coaugElem P cc) = 1`
      have h0 : cc.f 0 ≫ S.f 0 = 𝟙 _ := by
        have h := HomologicalComplex.comp_f cc S 0
        rw [hS, HomologicalComplex.id_f] at h
        exact h.symm
      have key : ModuleCat.Hom.hom (S.f 0) ∘ₗ ModuleCat.Hom.hom (cc.f 0) = LinearMap.id := by
        rw [← ModuleCat.hom_comp, h0, ModuleCat.hom_id]
      show ModuleCat.Hom.hom (S.f 0 ≫ e.hom) (Criterion.coaugElem P cc) = 1
      rw [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [show Criterion.coaugElem P cc = ModuleCat.Hom.hom (cc.f 0) (1 : A) from rfl]
      rw [show (ModuleCat.Hom.hom (S.f 0)) ((ModuleCat.Hom.hom (cc.f 0)) (1 : A)) =
          (ModuleCat.Hom.hom (S.f 0) ∘ₗ ModuleCat.Hom.hom (cc.f 0)) (1 : A) from rfl, key]
      simp only [LinearMap.id_apply]
      rw [show (ConcreteCategory.hom e.hom) (1 : A) = (1 : A) from heinv]

end ChainLevel

section Derived

variable {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]

/-- **The derived-category bridge.**  For a K-projective `P`, `Q.map cc` is a split
monomorphism in `D(A)` iff `cc` is a split monomorphism in the homotopy category. -/
theorem isSplitMono_Q_map_iff_isSplitMono_quotient_map
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective]
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) :
    CategoryTheory.IsSplitMono (DerivedCategory.Q.map cc) ↔
      CategoryTheory.IsSplitMono
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map cc) := by
  let q : CochainComplex (ModuleCat.{u} A) ℤ ⥤
      HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ) :=
    HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  constructor
  · -- `Q.map cc` split mono in `D(A)` ⟹ `q.map cc` split mono in the homotopy category
    intro h
    obtain ⟨⟨r, hr⟩⟩ := h.exists_splitMono
    obtain ⟨S, hS⟩ := Work.DSEQ0.Q_map_surjective_of_isKProjective (K := P) _ r
    refine ⟨⟨q.map S, ?_⟩⟩
    haveI : CochainComplex.IsKProjective
        ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A)) := Work.DSEQ0.singleZ_isKProjective (A := A)
    apply (CochainComplex.IsKProjective.Qh_map_bijective
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A)) (q.obj _)).injective
    rw [DerivedCategory.Qh.map_comp, ← cancel_mono (e.hom.app _), Category.assoc,
      DerivedCategory.quotientCompQhIso_hom_naturality S, ← Category.assoc,
      DerivedCategory.quotientCompQhIso_hom_naturality cc, Category.assoc, hS, hr]
    dsimp only [e]
    simp
  · -- `q.map cc` split mono ⟹ `Q.map cc` split mono
    intro h
    obtain ⟨⟨r, hr⟩⟩ := h.exists_splitMono
    refine ⟨⟨e.inv.app P ≫ DerivedCategory.Qh.map r ≫ e.hom.app _, ?_⟩⟩
    rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc cc
      (DerivedCategory.Qh.map r ≫ e.hom.app _)]
    rw [← DerivedCategory.Qh.map_comp_assoc, hr]
    dsimp only [e]
    simp

end Derived

section Assembly

variable {A : Type u} [CommRing A]

/-- **A retraction in the homotopy category is a chain-level retraction.**  Since `A[0]` is
concentrated in degree `0`, a split monomorphism `q.map cc` in the homotopy category can be
represented by a strict chain map `S : P ⟶ A[0]` with `cc ≫ S = 𝟙`. -/
theorem isSplitMono_quotient_map_iff_chainSplit
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) :
    CategoryTheory.IsSplitMono
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map cc) ↔
      Work.DSG4a.Criterion.ChainSplit P cc := by
  constructor
  · intro h
    obtain ⟨⟨r, hr⟩⟩ := h.exists_splitMono
    obtain ⟨S, hS⟩ :=
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_surjective r
    rw [chainSplit_iff_exists_chainRetraction P cc]
    refine ⟨S, ?_⟩
    apply HomologicalComplex.to_single_hom_ext
    exact homotopic_end_single_f_zero (f := cc ≫ S) (g := 𝟙 _)
      (HomotopyCategory.homotopyOfEq (cc ≫ S) (𝟙 _) (by
        show (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map (cc ≫ S) =
          (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map (𝟙 _)
        rw [Functor.map_comp, hS, hr,
          (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_id]))
  · intro h
    rw [chainSplit_iff_exists_chainRetraction P cc] at h
    obtain ⟨S, hS⟩ := h
    refine ⟨⟨(HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map S, ?_⟩⟩
    have hc : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map cc ≫
        (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map S =
        (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map (cc ≫ S) :=
      (Functor.map_comp _ _ _).symm
    rw [hc, hS, (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_id]

end Assembly

theorem isSplitMono_Q_map_iff_chainSplit {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective]
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A) ⟶ P) :
    CategoryTheory.IsSplitMono (DerivedCategory.Q.map cc) ↔
      Work.DSG4a.Criterion.ChainSplit P cc := by
  rw [isSplitMono_Q_map_iff_isSplitMono_quotient_map P cc]
  exact isSplitMono_quotient_map_iff_chainSplit P cc

end Work.DSG4a
