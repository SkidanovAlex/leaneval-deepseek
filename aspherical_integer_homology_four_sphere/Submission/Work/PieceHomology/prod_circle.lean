/-
# `H_{n+1}(X × S¹) ≅ H_{n+1}(X) ⊕ H_n(X)`

Künneth with a circle factor, proved by Mayer–Vietoris along the two-arc cover of the circle.
-/
import Mathlib
import Submission.Work.PieceHomology.CircCover
import Submission.Work.PieceHomology.cover_pieces
import Submission.Work.PieceHomology.projSet_iso
import Submission.Work.PieceHomology.clopenSplit_isIso
import Submission.Work.Homology.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Work.PieceHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

namespace PC

variable (X : Type) [TopologicalSpace X]

/-! ## §1  The cover of `X × Circ` -/

/-- The cylinder `X × W` over a subset `W` of the circle, as a subset of `X × Circ`. -/
abbrev S (W : Set Circ) : Set (X × Circ) := {p | p.2 ∈ W}

@[simp] theorem mem_S {W : Set Circ} {p : X × Circ} : p ∈ S X W ↔ p.2 ∈ W := Iff.rfl

/-- The first piece of the cover: `X × cU`. -/
abbrev cylU : Set (X × Circ) := S X cU

/-- The second piece of the cover: `X × cV`. -/
abbrev cylV : Set (X × Circ) := S X cV

@[simp] theorem mem_cylU {p : X × Circ} : p ∈ cylU X ↔ p.2 ∈ cU := Iff.rfl

@[simp] theorem mem_cylV {p : X × Circ} : p ∈ cylV X ↔ p.2 ∈ cV := Iff.rfl

theorem isOpen_cylU : IsOpen (cylU X) := isOpen_cU.preimage continuous_snd

theorem isOpen_cylV : IsOpen (cylV X) := isOpen_cV.preimage continuous_snd

theorem cylU_union_cylV : cylU X ∪ cylV X = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  rcases (show p.2 ∈ cU ∪ cV by rw [cU_union_cV]; trivial) with h | h
  · exact Or.inl ((mem_cylU X).mpr h)
  · exact Or.inr ((mem_cylV X).mpr h)

/-- The ambient space `X × Circ`. -/
abbrev YS : TopCat := TopCat.of (X × Circ)

/-- The intersection `X × (cU ∩ cV)`. -/
abbrev ZS : TopCat := TopCat.of ↥(cylU X ∩ cylV X)

/-- The cylinder `X × cU`. -/
abbrev US : TopCat := TopCat.of ↥(cylU X)

/-- The cylinder `X × cV`. -/
abbrev VS : TopCat := TopCat.of ↥(cylV X)

/-- The cylinder `X × cA1`. -/
abbrev AS1 : TopCat := TopCat.of ↥(S X cA1)

/-- The cylinder `X × cA2`. -/
abbrev AS2 : TopCat := TopCat.of ↥(S X cA2)

/-- The projection `X × Circ → X`. -/
def projTop : YS X ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The section `X → X × Circ` at a point of the circle. -/
def sectTop (w : Circ) : TopCat.of X ⟶ YS X :=
  TopCat.ofHom ⟨fun x => (x, w), continuous_id.prodMk continuous_const⟩

@[simp] theorem projTop_apply (p : X × Circ) : projTop X p = p.1 := rfl

@[simp] theorem sectTop_apply (w : Circ) (x : X) : (sectTop X w x).1 = x := rfl

theorem sectTop_projTop (w : Circ) : sectTop X w ≫ projTop X = 𝟙 (TopCat.of X) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- The inclusion of the cylinder over `W` followed by the projection is the projection of the
piece. -/
theorem incl_projTop (W : Set Circ) :
    Work.Homology.incl (X := YS X) (S X W) ≫ projTop X = projSet X W := by
  apply TopCat.hom_ext
  ext p
  rfl

/-! ## §2  The clopen splitting of the intersection -/

/-- A point of the second arc `cA2`. -/
def cw2 : Circ := ((5 / 8 : ℝ) : Circ)

theorem cw2_mem_cA2 : cw2 ∈ cA2 := ⟨5 / 8, by norm_num [K2], rfl⟩

/-- The first clopen piece of the intersection `X × (cU ∩ cV)`. -/
abbrev subA : Set ↥(cylU X ∩ cylV X) := {p | (p : X × Circ).2 ∈ cA1}

theorem mem_subA (p : ↥(cylU X ∩ cylV X)) : p ∈ subA X ↔ (p : X × Circ).2 ∈ cA1 := Iff.rfl

theorem cA1_subset_cyl : cA1 ⊆ cU ∩ cV := by
  rw [cover_pieces.1]; exact Set.subset_union_left

theorem cA2_subset_cyl : cA2 ⊆ cU ∩ cV := by
  rw [cover_pieces.1]; exact Set.subset_union_right

theorem mem_subA_compl (p : ↥(cylU X ∩ cylV X)) : p ∈ (subA X)ᶜ ↔ (p : X × Circ).2 ∈ cA2 := by
  have hp : (p : X × Circ).2 ∈ cA1 ∪ cA2 := by
    rw [← cover_pieces.1]; exact ⟨p.2.1, p.2.2⟩
  rw [Set.mem_compl_iff, mem_subA]
  constructor
  · intro h
    rcases hp with h1 | h2
    · exact absurd h1 h
    · exact h2
  · intro h h'
    exact (Set.disjoint_left.mp cover_pieces.2.1 h') h

theorem isOpen_subA : IsOpen (subA X) :=
  cover_pieces.2.2.1.preimage (continuous_snd.comp continuous_subtype_val)

theorem isClosed_subA : IsClosed (subA X) := by
  rw [← isOpen_compl_iff]
  have h : (subA X)ᶜ = {p : ↥(cylU X ∩ cylV X) | (p : X × Circ).2 ∈ cA2} :=
    Set.ext (fun p => mem_subA_compl X p)
  rw [h]
  exact cover_pieces.2.2.2.preimage (continuous_snd.comp continuous_subtype_val)

theorem isClopen_subA : IsClopen (subA X) := ⟨isClosed_subA X, isOpen_subA X⟩

/-- The homeomorphism from the first clopen piece of the intersection to the cylinder `X × cA1`. -/
def homeoA1 : ↥(subA X) ≃ₜ ↥(S X cA1) where
  toFun p := ⟨(p.1 : X × Circ), p.2⟩
  invFun q := ⟨⟨(q : X × Circ), by
    rw [Set.mem_inter_iff, mem_cylU, mem_cylV]
    exact cA1_subset_cyl q.2⟩, q.2⟩
  left_inv p := Subtype.ext (Subtype.ext rfl)
  right_inv q := Subtype.ext rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun p => p.2)
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk (fun q : ↥(S X cA1) => by
        rw [Set.mem_inter_iff, mem_cylU, mem_cylV]
        exact cA1_subset_cyl q.2)).subtype_mk (fun q => q.2)

/-- The homeomorphism from the second clopen piece of the intersection to the cylinder
`X × cA2`. -/
def homeoA2 : ↥((subA X)ᶜ) ≃ₜ ↥(S X cA2) where
  toFun p := ⟨(p.1 : X × Circ), (mem_subA_compl X p.1).mp p.2⟩
  invFun q := ⟨⟨(q : X × Circ), by
    rw [Set.mem_inter_iff, mem_cylU, mem_cylV]
    exact cA2_subset_cyl q.2⟩, (mem_subA_compl X _).mpr q.2⟩
  left_inv p := Subtype.ext (Subtype.ext rfl)
  right_inv q := Subtype.ext rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun p => (mem_subA_compl X p.1).mp p.2)
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk (fun q : ↥(S X cA2) => by
        rw [Set.mem_inter_iff, mem_cylU, mem_cylV]
        exact cA2_subset_cyl q.2)).subtype_mk (fun q => (mem_subA_compl X _).mpr q.2)

/-- A homeomorphism of spaces induces an isomorphism on singular homology. -/
def homeoIso {Y Z : TopCat} (e : Y ≃ₜ Z) (k : ℕ) :
    Work.Homology.singHomology Work.Homology.ZMod k Y
      ≅ Work.Homology.singHomology Work.Homology.ZMod k Z where
  hom := Work.Homology.singHomologyMap Work.Homology.ZMod k (Work.Homology.homeomorphTopCatHom e)
  inv := Work.Homology.singHomologyMap Work.Homology.ZMod k (Work.Homology.homeomorphTopCatInv e)
  hom_inv_id := by
    rw [← Work.Homology.singHomologyMap_comp, Work.Homology.homeomorphTopCatHom_comp_inv,
      Work.Homology.singHomologyMap_id]
  inv_hom_id := by
    rw [← Work.Homology.singHomologyMap_comp, Work.Homology.homeomorphTopCatInv_comp_hom,
      Work.Homology.singHomologyMap_id]

/-- The space of the first clopen piece of the intersection. -/
abbrev ASa : TopCat := TopCat.of ↥(subA X)

/-- The space of the second clopen piece of the intersection. -/
abbrev ASc : TopCat := TopCat.of ↥((subA X)ᶜ)

/-- **The clopen splitting of the intersection**: `H_k(X × (cU ∩ cV))` is the biproduct of the
homologies of the two cylinders, through the two inclusions. -/
def eZK (k : ℕ) :
    Work.Homology.singHomology Work.Homology.ZMod k (ASa X)
        ⊞ Work.Homology.singHomology Work.Homology.ZMod k (ASc X)
      ≅ Work.Homology.singHomology Work.Homology.ZMod k (ZS X) := by
  haveI : IsIso (biprod.desc
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (X := ZS X) (subA X)))
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (X := ZS X) ((subA X)ᶜ)))) :=
    clopenSplit_isIso (X := ZS X) (A := subA X) (isClopen_subA X) k
  exact asIso (biprod.desc
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (X := ZS X) (subA X)))
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (X := ZS X) ((subA X)ᶜ))))

theorem eZK_hom (k : ℕ) : (eZK X k).hom =
    biprod.desc
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (X := ZS X) (subA X)))
      (Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Homology.incl (X := ZS X) ((subA X)ᶜ))) := rfl

/-- **The assembly map** `H_k(X × cA1) ⊞ H_k(X × cA2) → H_k(X × (cU ∩ cV))`. -/
def assembleW (k : ℕ) :
    Work.Homology.singHomology Work.Homology.ZMod k (AS1 X)
        ⊞ Work.Homology.singHomology Work.Homology.ZMod k (AS2 X)
      ≅ Work.Homology.singHomology Work.Homology.ZMod k (ZS X) :=
  biprod.mapIso (homeoIso (homeoA1 X).symm k) (homeoIso (homeoA2 X).symm k) ≪≫ eZK X k

theorem assembleW_hom (k : ℕ) : (assembleW X k).hom =
    biprod.map (homeoIso (homeoA1 X).symm k).hom (homeoIso (homeoA2 X).symm k).hom
      ≫ (eZK X k).hom := by
  rw [assembleW, Iso.trans_hom, biprod.mapIso_hom]

theorem assembleW_inl (k : ℕ) :
    biprod.inl ≫ (assembleW X k).hom
      = (homeoIso (homeoA1 X).symm k).hom
        ≫ Work.Homology.singHomologyMap Work.Homology.ZMod k
            (Work.Homology.incl (X := ZS X) (subA X)) := by
  rw [assembleW_hom, ← Category.assoc, biprod.inl_map, Category.assoc, eZK_hom, biprod.inl_desc]

theorem assembleW_inr (k : ℕ) :
    biprod.inr ≫ (assembleW X k).hom
      = (homeoIso (homeoA2 X).symm k).hom
        ≫ Work.Homology.singHomologyMap Work.Homology.ZMod k
            (Work.Homology.incl (X := ZS X) ((subA X)ᶜ)) := by
  rw [assembleW_hom, ← Category.assoc, biprod.inr_map, Category.assoc, eZK_hom, biprod.inr_desc]

/-! ## §3  The projection isomorphisms -/

/-- `H_k(X × cA1) ≅ H_k(X)`, induced by the projection. -/
def eA1 (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (AS1 X)
    ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X) :=
  Classical.choose (projSet_iso X cA1 ⟨cw, cw_mem_cA1⟩ inferInstance k)

theorem eA1_hom (k : ℕ) : (eA1 X k).hom =
    Work.Homology.singHomologyMap Work.Homology.ZMod k (projSet X cA1) :=
  Classical.choose_spec (projSet_iso X cA1 ⟨cw, cw_mem_cA1⟩ inferInstance k)

/-- `H_k(X × cA2) ≅ H_k(X)`, induced by the projection. -/
def eA2 (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (AS2 X)
    ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X) :=
  Classical.choose (projSet_iso X cA2 ⟨cw2, cw2_mem_cA2⟩ inferInstance k)

theorem eA2_hom (k : ℕ) : (eA2 X k).hom =
    Work.Homology.singHomologyMap Work.Homology.ZMod k (projSet X cA2) :=
  Classical.choose_spec (projSet_iso X cA2 ⟨cw2, cw2_mem_cA2⟩ inferInstance k)

/-- `H_k(X × cU) ≅ H_k(X)`, induced by the projection. -/
def eU (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (US X)
    ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X) :=
  Classical.choose (projSet_iso X cU ⟨cw, cw_mem_cU⟩ inferInstance k)

theorem eU_hom (k : ℕ) : (eU X k).hom =
    Work.Homology.singHomologyMap Work.Homology.ZMod k (projSet X cU) :=
  Classical.choose_spec (projSet_iso X cU ⟨cw, cw_mem_cU⟩ inferInstance k)

/-- `H_k(X × cV) ≅ H_k(X)`, induced by the projection. -/
def eV (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (VS X)
    ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X) :=
  Classical.choose (projSet_iso X cV ⟨cw, cw_mem_cV⟩ inferInstance k)

theorem eV_hom (k : ℕ) : (eV X k).hom =
    Work.Homology.singHomologyMap Work.Homology.ZMod k (projSet X cV) :=
  Classical.choose_spec (projSet_iso X cV ⟨cw, cw_mem_cV⟩ inferInstance k)

/-- The map `X × (cU ∩ cV) → X`, as the composite of the inclusion into `X × cU` with the
projection of the cylinder. -/
abbrev wToX : ZS X ⟶ TopCat.of X :=
  Work.Cohomology.inclUVU (X := YS X) (cylU X) (cylV X) ≫ projSet X cU

/-- The same map, through the other piece. -/
theorem inclUVV_proj : Work.Cohomology.inclUVV (X := YS X) (cylU X) (cylV X) ≫ projSet X cV
    = wToX X := by
  apply TopCat.hom_ext
  ext p
  rfl

theorem wToX_apply (p : ↥(cylU X ∩ cylV X)) : (wToX X) p = (p : X × Circ).1 := rfl

theorem homeoIso_hom {Y Z : TopCat} (e : Y ≃ₜ Z) (k : ℕ) :
    (homeoIso e k).hom = Work.Homology.singHomologyMap Work.Homology.ZMod k
      (Work.Homology.homeomorphTopCatHom e) := rfl


/-- The map from `X × cA1` to `X`, on both sides of the homeomorphism. -/
theorem assembleW_inl_map :
    Work.Homology.homeomorphTopCatHom (homeoA1 X).symm
      ≫ Work.Homology.incl (X := ZS X) (subA X) ≫ wToX X = projSet X cA1 := by
  apply TopCat.hom_ext
  ext p
  rfl

/-- The map from `X × cA2` to `X`, on both sides of the homeomorphism. -/
theorem assembleW_inr_map :
    Work.Homology.homeomorphTopCatHom (homeoA2 X).symm
      ≫ Work.Homology.incl (X := ZS X) ((subA X)ᶜ) ≫ wToX X = projSet X cA2 := by
  apply TopCat.hom_ext
  ext p
  rfl

theorem assembleW_inl_proj (k : ℕ) :
    biprod.inl ≫ (assembleW X k).hom
        ≫ Work.Homology.singHomologyMap Work.Homology.ZMod k (wToX X)
      = (eA1 X k).hom := by
  rw [← Category.assoc, assembleW_inl, Category.assoc, homeoIso_hom,
    ← Work.Homology.singHomologyMap_comp, ← Work.Homology.singHomologyMap_comp,
    assembleW_inl_map, eA1_hom]

theorem assembleW_inr_proj (k : ℕ) :
    biprod.inr ≫ (assembleW X k).hom
        ≫ Work.Homology.singHomologyMap Work.Homology.ZMod k (wToX X)
      = (eA2 X k).hom := by
  rw [← Category.assoc, assembleW_inr, Category.assoc, homeoIso_hom,
    ← Work.Homology.singHomologyMap_comp, ← Work.Homology.singHomologyMap_comp,
    assembleW_inr_map, eA2_hom]

/-- The assembly map followed by the projection of the intersection is the sum of the two
projections of the arcs. -/
theorem assembleW_proj (k : ℕ) :
    (assembleW X k).hom
        ≫ Work.Homology.singHomologyMap Work.Homology.ZMod k (wToX X)
      = biprod.desc (eA1 X k).hom (eA2 X k).hom := by
  apply biprod.ext_from_iff.mpr
  constructor
  · rw [biprod.inl_desc]
    exact assembleW_inl_proj X k
  · rw [biprod.inr_desc]
    exact assembleW_inr_proj X k

/-- The identification `H_k(X) ⊞ H_k(X) ≅ H_k(X × (cU ∩ cV))`. -/
def Psi (k : ℕ) :
    Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X)
        ⊞ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X)
      ≅ Work.Homology.singHomology Work.Homology.ZMod k (ZS X) :=
  (biprod.mapIso (eA1 X k) (eA2 X k)).symm ≪≫ assembleW X k

theorem Psi_proj (k : ℕ) :
    (Psi X k).hom
        ≫ Work.Homology.singHomologyMap Work.Homology.ZMod k (wToX X)
      = biprod.fst + biprod.snd := by
  rw [Psi, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_inv, Category.assoc, assembleW_proj]
  apply biprod.ext_from_iff.mpr
  constructor
  · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc, Iso.inv_hom_id]
    rw [Preadditive.comp_add, biprod.inl_fst, biprod.inl_snd, add_zero]
  · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc, Iso.inv_hom_id]
    rw [Preadditive.comp_add, biprod.inr_fst, biprod.inr_snd, zero_add]

/-! ## §4  The identification of the Mayer–Vietoris map -/

/-- The singular chain complex of `X × cU`. -/
abbrev cplxU : ChainComplex (ModuleCat ℤ) ℕ := Work.Homology.singChain Work.Homology.ZMod (US X)

/-- The singular chain complex of `X × cV`. -/
abbrev cplxV : ChainComplex (ModuleCat ℤ) ℕ := Work.Homology.singChain Work.Homology.ZMod (VS X)

/-- The homology of a biproduct of chain complexes, with the components pinned down. -/
def hbIso (k : ℕ) : (cplxU X ⊞ cplxV X).homology k
    ≅ (cplxU X).homology k ⊞ (cplxV X).homology k where
  hom := biprod.lift
    (HomologicalComplex.homologyMap (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X) k)
    (HomologicalComplex.homologyMap (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X) k)
  inv := biprod.desc
    (HomologicalComplex.homologyMap (biprod.inl : cplxU X ⟶ cplxU X ⊞ cplxV X) k)
    (HomologicalComplex.homologyMap (biprod.inr : cplxV X ⟶ cplxU X ⊞ cplxV X) k)
  hom_inv_id := by
    rw [biprod.lift_desc]
    simp only [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_add,
      biprod.total, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    apply Work.Homology.biprod_desc_lift
    · simp only [← HomologicalComplex.homologyMap_comp, biprod.inl_fst,
        HomologicalComplex.homologyMap_id]
    · simp only [← HomologicalComplex.homologyMap_comp, biprod.inr_fst,
        HomologicalComplex.homologyMap_zero]
    · simp only [← HomologicalComplex.homologyMap_comp, biprod.inl_snd,
        HomologicalComplex.homologyMap_zero]
    · simp only [← HomologicalComplex.homologyMap_comp, biprod.inr_snd,
        HomologicalComplex.homologyMap_id]

theorem hbIso_hom_fst (k : ℕ) : (hbIso X k).hom ≫ biprod.fst
    = HomologicalComplex.homologyMap (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X) k :=
  biprod.lift_fst _ _

theorem hbIso_hom_snd (k : ℕ) : (hbIso X k).hom ≫ biprod.snd
    = HomologicalComplex.homologyMap (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X) k :=
  biprod.lift_snd _ _

/-- The identification `H_k(X × cU) ⊞ H_k(X × cV) ≅ H_k(X) ⊞ H_k(X)`. -/
def PhiN (k : ℕ) : (cplxU X ⊞ cplxV X).homology k
    ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X)
      ⊞ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X) :=
  hbIso X k ≪≫ biprod.mapIso (eU X k) (eV X k)

theorem PhiN_hom_fst (k : ℕ) : (PhiN X k).hom ≫ biprod.fst
    = HomologicalComplex.homologyMap (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X) k
      ≫ (eU X k).hom := by
  rw [PhiN, Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.map_fst, ← Category.assoc,
    hbIso_hom_fst]

theorem PhiN_hom_snd (k : ℕ) : (PhiN X k).hom ≫ biprod.snd
    = HomologicalComplex.homologyMap (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X) k
      ≫ (eV X k).hom := by
  rw [PhiN, Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.map_snd, ← Category.assoc,
    hbIso_hom_snd]

/-- The first map of the Mayer–Vietoris sequence, in degree `k`. -/
abbrev alpha (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (ZS X)
    ⟶ (cplxU X ⊞ cplxV X).homology k :=
  HomologicalComplex.homologyMap (Work.Cohomology.mvLeft (X := YS X) (cylU X) (cylV X)) k

theorem alpha_fst (k : ℕ) : alpha X k
    ≫ HomologicalComplex.homologyMap (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X) k
    = Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Cohomology.inclUVU (X := YS X) (cylU X) (cylV X)) := by
  rw [alpha, ← HomologicalComplex.homologyMap_comp,
    show Work.Cohomology.mvLeft (X := YS X) (cylU X) (cylV X)
        ≫ (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X)
      = Work.Homology.singChainMap Work.Homology.ZMod
          (Work.Cohomology.inclUVU (X := YS X) (cylU X) (cylV X)) from biprod.lift_fst _ _]

theorem alpha_snd (k : ℕ) : alpha X k
    ≫ HomologicalComplex.homologyMap (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X) k
    = Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.Cohomology.inclUVV (X := YS X) (cylU X) (cylV X)) := by
  rw [alpha, ← HomologicalComplex.homologyMap_comp,
    show Work.Cohomology.mvLeft (X := YS X) (cylU X) (cylV X)
        ≫ (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X)
      = Work.Homology.singChainMap Work.Homology.ZMod
          (Work.Cohomology.inclUVV (X := YS X) (cylU X) (cylV X)) from biprod.lift_snd _ _]

/-- **The Mayer–Vietoris map becomes `(a, b) ↦ (a + b, a + b)`** under the identifications of
`Psi` (on the intersection) and `PhiN` (on the two pieces). -/
theorem Psi_alpha_fst (k : ℕ) :
    (Psi X k).hom ≫ alpha X k ≫ (PhiN X k).hom ≫ biprod.fst = biprod.fst + biprod.snd := by
  have haux : alpha X k
      ≫ HomologicalComplex.homologyMap (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X) k
      ≫ (eU X k).hom = Work.Homology.singHomologyMap Work.Homology.ZMod k (wToX X) := by
    rw [← Category.assoc, alpha_fst, eU_hom, ← Work.Homology.singHomologyMap_comp]
  rw [PhiN_hom_fst, haux, Psi_proj]

theorem Psi_alpha_snd (k : ℕ) :
    (Psi X k).hom ≫ alpha X k ≫ (PhiN X k).hom ≫ biprod.snd = biprod.fst + biprod.snd := by
  have haux : alpha X k
      ≫ HomologicalComplex.homologyMap (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X) k
      ≫ (eV X k).hom = Work.Homology.singHomologyMap Work.Homology.ZMod k (wToX X) := by
    rw [← Category.assoc, alpha_snd, eV_hom, ← Work.Homology.singHomologyMap_comp, inclUVV_proj]
  rw [PhiN_hom_snd, haux, Psi_proj]

/-! ## §5  The assembly -/

/-- `H_k(X)`. -/
abbrev Hpt (k : ℕ) : ModuleCat ℤ := Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X)

/-- `H_k(X × Circ)`. -/
abbrev Hcyl (k : ℕ) : ModuleCat ℤ := Work.Homology.singHomology Work.Homology.ZMod k (YS X)

/-- `H_k(X × (cU ∩ cV))`. -/
abbrev Hint (k : ℕ) : ModuleCat ℤ := Work.Homology.singHomology Work.Homology.ZMod k (ZS X)

/-- `H_k(X) ⊞ H_k(X)`. -/
abbrev H2 (k : ℕ) : ModuleCat ℤ := Hpt X k ⊞ Hpt X k

/-- The cylinder `X × cU`. -/
abbrev USX : TopCat := TopCat.of ↥(cylU X)

/-- The cylinder `X × cV`. -/
abbrev VSX : TopCat := TopCat.of ↥(cylV X)

/-- The section `X → X × cU` at the base point. -/
abbrev secU (k : ℕ) : Hpt X k ⟶ Work.Homology.singHomology Work.Homology.ZMod k (USX X) :=
  Work.Homology.singHomologyMap Work.Homology.ZMod k (sectSet X cU ⟨cw, cw_mem_cU⟩)

/-- The section `X → X × cV` at the base point. -/
abbrev secV (k : ℕ) : Hpt X k ⟶ Work.Homology.singHomology Work.Homology.ZMod k (VSX X) :=
  Work.Homology.singHomologyMap Work.Homology.ZMod k (sectSet X cV ⟨cw, cw_mem_cV⟩)

/-- The inclusion `X × cU ↪ X × Circ`, on homology. -/
abbrev incU (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (USX X) ⟶ Hcyl X k :=
  Work.Homology.singHomologyMap Work.Homology.ZMod k
    (Work.Cohomology.inclUX (X := YS X) (cylU X))

/-- The inclusion `X × cV ↪ X × Circ`, on homology. -/
abbrev incV (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (VSX X) ⟶ Hcyl X k :=
  Work.Homology.singHomologyMap Work.Homology.ZMod k
    (Work.Cohomology.inclVX (X := YS X) (cylV X))

/-- `H_k(X × cU) ⊞ H_k(X × cV)`. -/
abbrev HBD (k : ℕ) : ModuleCat ℤ := (cplxU X ⊞ cplxV X).homology k

/-- The first component of the homology biproduct. -/
abbrev hmf (k : ℕ) : HBD X k ⟶ Work.Homology.singHomology Work.Homology.ZMod k (USX X) :=
  HomologicalComplex.homologyMap (biprod.fst : cplxU X ⊞ cplxV X ⟶ cplxU X) k

/-- The second component of the homology biproduct. -/
abbrev hms (k : ℕ) : HBD X k ⟶ Work.Homology.singHomology Work.Homology.ZMod k (VSX X) :=
  HomologicalComplex.homologyMap (biprod.snd : cplxU X ⊞ cplxV X ⟶ cplxV X) k

/-- The first inclusion into the homology biproduct. -/
abbrev hmi (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (USX X) ⟶ HBD X k :=
  HomologicalComplex.homologyMap (biprod.inl : cplxU X ⟶ cplxU X ⊞ cplxV X) k

/-- The second inclusion into the homology biproduct. -/
abbrev hmj (k : ℕ) : Work.Homology.singHomology Work.Homology.ZMod k (VSX X) ⟶ HBD X k :=
  HomologicalComplex.homologyMap (biprod.inr : cplxV X ⟶ cplxU X ⊞ cplxV X) k

/-- The connecting map of the Mayer–Vietoris sequence of the cover. -/
abbrev mvdel (n : ℕ) : Hcyl X (n + 1) ⟶ Hint X n :=
  Work.Cohomology.mvδX (X := YS X) (cylU X) (cylV X) (isOpen_cylU X) (isOpen_cylV X)
    (cylU_union_cylV X) n

/-- The second Mayer–Vietoris map of the cover. -/
abbrev mvmr (n : ℕ) : (cplxU X ⊞ cplxV X).homology n ⟶ Hcyl X n :=
  Work.Cohomology.mvRightX (X := YS X) (cylU X) (cylV X) (isOpen_cylU X) (isOpen_cylV X)
    (cylU_union_cylV X) n

/-- The section `X → X × Circ` at the base point. -/
abbrev hsect (k : ℕ) : Hpt X k ⟶ Hcyl X k :=
  Work.Homology.singHomologyMap Work.Homology.ZMod k (sectTop X cw)

/-- The projection `X × Circ → X`. -/
abbrev hproj (k : ℕ) : Hcyl X k ⟶ Hpt X k :=
  Work.Homology.singHomologyMap Work.Homology.ZMod k (projTop X)

/-- The anti-diagonal `a ↦ (a, -a)`. -/
abbrev adiag (k : ℕ) : Hpt X k ⟶ H2 X k :=
  biprod.lift (𝟙 _) (-(𝟙 _))

/-- The sum map `(a, b) ↦ a + b`. -/
abbrev sm (k : ℕ) : H2 X k ⟶ Hpt X k := biprod.fst + biprod.snd

/-- The map `(a, b) ↦ (a + b, a + b)`. -/
abbrev lft (k : ℕ) : H2 X k ⟶ H2 X k := biprod.lift (sm X k) (sm X k)

/-- The map of the long exact sequence out of `H_{n+1}(X × S¹)`, in the coordinates of `Psi`. -/
abbrev qm (n : ℕ) : Hcyl X (n + 1) ⟶ Hpt X n := mvdel X n ≫ ((Psi X n).inv ≫ biprod.fst)

theorem hsect_hproj (k : ℕ) : hsect X k ≫ hproj X k = 𝟙 (Hpt X k) := by
  rw [hsect, hproj, ← Work.Homology.singHomologyMap_comp, sectTop_projTop,
    Work.Homology.singHomologyMap_id]

/-! ### Elementary biproduct identities -/

/-- The decomposition of an element of a biproduct into its two components. -/
theorem biprod_decomp (n : ℕ) (x : H2 X n) :
    ModuleCat.Hom.hom (biprod.inl : Hpt X n ⟶ H2 X n)
        (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x)
      + ModuleCat.Hom.hom (biprod.inr : Hpt X n ⟶ H2 X n)
        (ModuleCat.Hom.hom (biprod.snd : H2 X n ⟶ Hpt X n) x) = x := by
  have h := congrArg ModuleCat.Hom.hom (biprod.total (X := Hpt X n) (Y := Hpt X n))
  have h2 := LinearMap.congr_fun h x
  simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply] using h2

/-- The kernel of the sum map `(a, b) ↦ a + b` is the anti-diagonal. -/
theorem ker_sum (n : ℕ) :
    (ModuleCat.Hom.hom (biprod.fst + biprod.snd : H2 X n ⟶ Hpt X n)).ker
      = (ModuleCat.Hom.hom (adiag X n)).range := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    refine LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x, ?_⟩
    have hf : ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n)
        (ModuleCat.Hom.hom (adiag X n) (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x))
        = ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (biprod.lift_fst (𝟙 (Hpt X n)) (-(𝟙 (Hpt X n))))) _
    have hs : ModuleCat.Hom.hom (biprod.snd : H2 X n ⟶ Hpt X n)
        (ModuleCat.Hom.hom (adiag X n) (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x))
        = ModuleCat.Hom.hom (biprod.snd : H2 X n ⟶ Hpt X n) x := by
      have h := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (biprod.lift_snd (𝟙 (Hpt X n)) (-(𝟙 (Hpt X n)))))
        (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x)
      rw [ModuleCat.hom_neg, ModuleCat.hom_id, LinearMap.neg_apply, LinearMap.id_apply,
        ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h]
      have hx' : ModuleCat.Hom.hom (biprod.snd : H2 X n ⟶ Hpt X n) x
          = -ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x := by
        rw [ModuleCat.hom_add, LinearMap.add_apply] at hx
        exact eq_neg_of_add_eq_zero_right hx
      rw [hx']
    calc ModuleCat.Hom.hom (adiag X n) (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x)
        = ModuleCat.Hom.hom (biprod.inl : Hpt X n ⟶ H2 X n)
            (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n)
              (ModuleCat.Hom.hom (adiag X n)
                (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x)))
          + ModuleCat.Hom.hom (biprod.inr : Hpt X n ⟶ H2 X n)
            (ModuleCat.Hom.hom (biprod.snd : H2 X n ⟶ Hpt X n)
              (ModuleCat.Hom.hom (adiag X n)
                (ModuleCat.Hom.hom (biprod.fst : H2 X n ⟶ Hpt X n) x))) :=
          (biprod_decomp X n _).symm
      _ = _ := by rw [hf, hs]; exact biprod_decomp X n x
  · intro x hx
    rw [LinearMap.mem_ker]
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    have h : (adiag X n) ≫ (biprod.fst + biprod.snd : H2 X n ⟶ Hpt X n) = 0 := by
      rw [Preadditive.comp_add, biprod.lift_fst, biprod.lift_snd, add_neg_cancel]
    have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2

/-- The value of `lft` on an element. -/
theorem lft_apply (k : ℕ) (x : H2 X k) :
    ModuleCat.Hom.hom (lft X k) x
      = ModuleCat.Hom.hom (biprod.inl : Hpt X k ⟶ H2 X k)
          (ModuleCat.Hom.hom (sm X k) x)
        + ModuleCat.Hom.hom (biprod.inr : Hpt X k ⟶ H2 X k)
          (ModuleCat.Hom.hom (sm X k) x) := by
  rw [lft, sm, biprod.lift_eq]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The kernel of `lft` is the kernel of the sum map. -/
theorem lft_ker (k : ℕ) : (ModuleCat.Hom.hom (lft X k)).ker
    = (ModuleCat.Hom.hom (sm X k)).ker := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [lft_apply X k x] at hx
    have h1 : ModuleCat.Hom.hom (biprod.fst : H2 X k ⟶ Hpt X k)
        (ModuleCat.Hom.hom (biprod.inl : Hpt X k ⟶ H2 X k) (ModuleCat.Hom.hom (sm X k) x))
        = ModuleCat.Hom.hom (sm X k) x := by
      have h := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (biprod.inl_fst (X := Hpt X k) (Y := Hpt X k)))
        (ModuleCat.Hom.hom (sm X k) x)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using h
    have h2 : ModuleCat.Hom.hom (biprod.fst : H2 X k ⟶ Hpt X k)
        (ModuleCat.Hom.hom (biprod.inr : Hpt X k ⟶ H2 X k) (ModuleCat.Hom.hom (sm X k) x)) = 0 := by
      have h := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (biprod.inr_fst (X := Hpt X k) (Y := Hpt X k)))
        (ModuleCat.Hom.hom (sm X k) x)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    have h := congrArg (ModuleCat.Hom.hom (biprod.fst : H2 X k ⟶ Hpt X k)) hx
    rw [LinearMap.map_add, h1, h2, add_zero, LinearMap.map_zero] at h
    exact h
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [lft_apply X k x, hx]
    simp

/-! ### The kernel of the Mayer–Vietoris map -/

/-- The inverse of `Psi` on the right. -/
theorem Psi_inv_fwd (n : ℕ) (z : Hint X n) :
    ModuleCat.Hom.hom (Psi X n).hom (ModuleCat.Hom.hom (Psi X n).inv z) = z := by
  have h : (Psi X n).inv ≫ (Psi X n).hom = 𝟙 (Hint X n) := Iso.inv_hom_id (Psi X n)
  have h2 := congrArg (fun (f : Hint X n ⟶ Hint X n) => ModuleCat.Hom.hom f) h
  exact LinearMap.congr_fun (by simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using h2) z

/-- `Psi` is injective. -/
theorem Psi_fwd_inv (n : ℕ) (x : H2 X n) :
    ModuleCat.Hom.hom (Psi X n).inv (ModuleCat.Hom.hom (Psi X n).hom x) = x := by
  have h : (Psi X n).hom ≫ (Psi X n).inv = 𝟙 (H2 X n) := Iso.hom_inv_id (Psi X n)
  have h2 := congrArg (fun (f : H2 X n ⟶ H2 X n) => ModuleCat.Hom.hom f) h
  exact LinearMap.congr_fun (by simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using h2) x

/-- `PhiN` is injective. -/
theorem PhiN_fwd_inv (n : ℕ) (x : (cplxU X ⊞ cplxV X).homology n) :
    ModuleCat.Hom.hom (PhiN X n).inv (ModuleCat.Hom.hom (PhiN X n).hom x) = x := by
  have h : (PhiN X n).hom ≫ (PhiN X n).inv = 𝟙 ((cplxU X ⊞ cplxV X).homology n) :=
    Iso.hom_inv_id (PhiN X n)
  have h2 := congrArg (fun (f : (cplxU X ⊞ cplxV X).homology n ⟶ (cplxU X ⊞ cplxV X).homology n) =>
    ModuleCat.Hom.hom f) h
  exact LinearMap.congr_fun (by simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using h2) x

theorem PhiN_inj (n : ℕ) : Function.Injective (ModuleCat.Hom.hom (PhiN X n).hom) := by
  intro a b hab
  rw [← PhiN_fwd_inv X n a, ← PhiN_fwd_inv X n b, hab]

/-- The Mayer–Vietoris map in the coordinates of `Psi` and `PhiN`. -/
theorem Psi_alpha_eq (n : ℕ) : (Psi X n).hom ≫ alpha X n ≫ (PhiN X n).hom = lft X n := by
  apply biprod.hom_ext
  · rw [biprod.lift_fst, Category.assoc, Category.assoc, Psi_alpha_fst]
  · rw [biprod.lift_snd, Category.assoc, Category.assoc, Psi_alpha_snd]

/-- **The kernel of the Mayer–Vietoris map `α_n` is the anti-diagonal.** -/
theorem ker_alpha_eq (n : ℕ) :
    (alpha X n).hom.ker = (adiag X n ≫ (Psi X n).hom).hom.range := by
  have hL : (ModuleCat.Hom.hom (lft X n)).ker = (ModuleCat.Hom.hom (adiag X n)).range := by
    rw [lft_ker X n]; exact ker_sum X n
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    have hLz : ModuleCat.Hom.hom (lft X n) (ModuleCat.Hom.hom (Psi X n).inv z) = 0 := by
      have hh := congrArg ModuleCat.Hom.hom (Psi_alpha_eq X n)
      have h2 := LinearMap.congr_fun hh (ModuleCat.Hom.hom (Psi X n).inv z)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h2
      rw [Psi_inv_fwd X n z, hz, LinearMap.map_zero] at h2
      exact h2.symm
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (by rw [← hL]; exact LinearMap.mem_ker.mpr hLz)
    refine LinearMap.mem_range.mpr ⟨a, ?_⟩
    calc ModuleCat.Hom.hom (adiag X n ≫ (Psi X n).hom) a
        = ModuleCat.Hom.hom (Psi X n).hom (ModuleCat.Hom.hom (adiag X n) a) := by
          rw [ModuleCat.hom_comp, LinearMap.comp_apply]
      _ = ModuleCat.Hom.hom (Psi X n).hom (ModuleCat.Hom.hom (Psi X n).inv z) := by rw [ha]
      _ = z := Psi_inv_fwd X n z
  · intro z hz
    rw [LinearMap.mem_ker]
    obtain ⟨a, hza⟩ := LinearMap.mem_range.mp hz
    rw [← hza]
    have hL0 : ModuleCat.Hom.hom (lft X n) (ModuleCat.Hom.hom (adiag X n) a) = 0 :=
      LinearMap.mem_ker.mp (by rw [hL]; exact LinearMap.mem_range_self _ a)
    have key : ModuleCat.Hom.hom (PhiN X n).hom
        (ModuleCat.Hom.hom (alpha X n) (ModuleCat.Hom.hom (Psi X n).hom
          (ModuleCat.Hom.hom (adiag X n) a))) = 0 := by
      have hh := congrArg ModuleCat.Hom.hom (Psi_alpha_eq X n)
      have h2 := LinearMap.congr_fun hh (ModuleCat.Hom.hom (adiag X n) a)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h2
      rw [h2, hL0]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact PhiN_inj X n (by rw [key, LinearMap.map_zero])

/-! ### The components of the second Mayer–Vietoris map -/

theorem smallIso_hom_eq' {U V : Set (YS X)} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    (Work.Cohomology.smallIso (X := YS X) U V hU hV hcov n).hom =
      HomologicalComplex.homologyMap (Work.Cohomology.smallToSing (X := YS X) U V) n := by
  simp only [Work.Cohomology.smallIso]
  dsimp only [CategoryTheory.asIso]

theorem smallOfU_comp (U V : Set (YS X)) :
    Work.Cohomology.smallOfU (X := YS X) U V ≫ Work.Cohomology.smallToSing (X := YS X) U V
    = Work.Homology.singChainMap Work.Homology.ZMod (Work.Cohomology.inclUX (X := YS X) U) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (Work.Cohomology.smallLiftU (X := YS X) U V)
    ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      ((Work.Cohomology.smallSubcomplex (X := YS X) U V).ι)
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.toSSet.map (Work.Cohomology.inclUX (X := YS X) U))
  rw [← Functor.map_comp]
  rfl

theorem smallOfV_comp (U V : Set (YS X)) :
    Work.Cohomology.smallOfV (X := YS X) U V ≫ Work.Cohomology.smallToSing (X := YS X) U V
    = Work.Homology.singChainMap Work.Homology.ZMod (Work.Cohomology.inclVX (X := YS X) V) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (Work.Cohomology.smallLiftV (X := YS X) U V)
    ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      ((Work.Cohomology.smallSubcomplex (X := YS X) U V).ι)
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.toSSet.map (Work.Cohomology.inclVX (X := YS X) V))
  rw [← Functor.map_comp]
  rfl

theorem smallOfU_homology (U V : Set (YS X)) (k : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.smallOfU (X := YS X) U V) k
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.smallToSing (X := YS X) U V) k
    = Work.Homology.singHomologyMap Work.Homology.ZMod k (Work.Cohomology.inclUX (X := YS X) U) := by
  rw [← HomologicalComplex.homologyMap_comp, smallOfU_comp]

theorem smallOfV_homology (U V : Set (YS X)) (k : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.smallOfV (X := YS X) U V) k
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.smallToSing (X := YS X) U V) k
    = Work.Homology.singHomologyMap Work.Homology.ZMod k (Work.Cohomology.inclVX (X := YS X) V) := by
  rw [← HomologicalComplex.homologyMap_comp, smallOfV_comp]

/-- The first component of the second Mayer–Vietoris map is the inclusion of `X × cU`. -/
theorem mvr_inl (k : ℕ) : hmi X k ≫ mvmr X k = incU X k := by
  have hmv : biprod.inl ≫ Work.Cohomology.mvRight (X := YS X) (cylU X) (cylV X)
      = Work.Cohomology.smallOfU (X := YS X) (cylU X) (cylV X) := by
    rw [show Work.Cohomology.mvRight (X := YS X) (cylU X) (cylV X)
        = biprod.desc (Work.Cohomology.smallOfU (X := YS X) (cylU X) (cylV X))
            (-(Work.Cohomology.smallOfV (X := YS X) (cylU X) (cylV X))) from rfl, biprod.inl_desc]
  have h1 : hmi X k ≫ HomologicalComplex.homologyMap
        (Work.Cohomology.mvRight (X := YS X) (cylU X) (cylV X)) k
      = HomologicalComplex.homologyMap
          (Work.Cohomology.smallOfU (X := YS X) (cylU X) (cylV X)) k := by
    rw [← HomologicalComplex.homologyMap_comp, hmv]
  rw [mvmr, Work.Cohomology.mvRightX, smallIso_hom_eq', hmi, ← Category.assoc, h1]
  exact smallOfU_homology X (cylU X) (cylV X) k

/-- The second component of the second Mayer–Vietoris map is minus the inclusion of `X × cV`. -/
theorem mvr_inr (k : ℕ) : hmj X k ≫ mvmr X k = -(incV X k) := by
  have hmv : biprod.inr ≫ Work.Cohomology.mvRight (X := YS X) (cylU X) (cylV X)
      = -(Work.Cohomology.smallOfV (X := YS X) (cylU X) (cylV X)) := by
    rw [show Work.Cohomology.mvRight (X := YS X) (cylU X) (cylV X)
        = biprod.desc (Work.Cohomology.smallOfU (X := YS X) (cylU X) (cylV X))
            (-(Work.Cohomology.smallOfV (X := YS X) (cylU X) (cylV X))) from rfl, biprod.inr_desc]
  have h1 : hmj X k ≫ HomologicalComplex.homologyMap
        (Work.Cohomology.mvRight (X := YS X) (cylU X) (cylV X)) k
      = - HomologicalComplex.homologyMap
          (Work.Cohomology.smallOfV (X := YS X) (cylU X) (cylV X)) k := by
    rw [← HomologicalComplex.homologyMap_comp, hmv, HomologicalComplex.homologyMap_neg]
  rw [mvmr, Work.Cohomology.mvRightX, smallIso_hom_eq', hmj, ← Category.assoc, h1,
    Preadditive.neg_comp]
  rw [smallOfV_homology, incV]

/-! ### The exactness statements, and the identification of the two ends -/

/-- **`mvdel` and `mvmr` are the kernel and the range of one another.** -/
theorem del_ker (n : ℕ) : (mvdel X n).hom.ker = (mvmr X (n + 1)).hom.range := by
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker
    (Work.Homology.mvShortXRel (X := YS X) (cylU X) (cylV X) (isOpen_cylU X) (isOpen_cylV X)
      (cylU_union_cylV X) n)).mp
    (Work.Homology.mv_exact_Hrel (X := YS X) (cylU X) (cylV X) (isOpen_cylU X) (isOpen_cylV X)
      (cylU_union_cylV X) n)
  exact h.symm

/-- **The range of `mvdel` is the kernel of the Mayer–Vietoris map.** -/
theorem del_range (n : ℕ) : (mvdel X n).hom.range = (alpha X n).hom.ker := by
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker
    (Work.Homology.mvShortXInter (X := YS X) (cylU X) (cylV X) (isOpen_cylU X) (isOpen_cylV X)
      (cylU_union_cylV X) n)).mp
    (Work.Homology.mv_exact_Hinter (X := YS X) (cylU X) (cylV X) (isOpen_cylU X) (isOpen_cylV X)
      (cylU_union_cylV X) n)
  exact h

theorem hsect_eq_U (k : ℕ) : hsect X k = secU X k ≫ incU X k := by
  rw [hsect, secU, incU, ← Work.Homology.singHomologyMap_comp]
  congr 1

theorem hsect_eq_V (k : ℕ) : hsect X k = secV X k ≫ incV X k := by
  rw [hsect, secV, incV, ← Work.Homology.singHomologyMap_comp]
  congr 1

theorem secU_range (k : ℕ) : (secU X k).hom.range = ⊤ := by
  obtain ⟨e, he⟩ := projSet_iso X cU ⟨cw, cw_mem_cU⟩ inferInstance k
  have hg : secU X k ≫ e.hom = 𝟙 (Hpt X k) := by
    rw [secU, he, ← Work.Homology.singHomologyMap_comp, projSet_sectSet,
      Work.Homology.singHomologyMap_id]
  have h2 : secU X k = e.inv := by
    rw [← Category.id_comp e.inv, ← hg, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [h2, LinearMap.range_eq_top]
  intro y
  refine ⟨ModuleCat.Hom.hom e.hom y, ?_⟩
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.hom_inv_id) y
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h

theorem secV_range (k : ℕ) : (secV X k).hom.range = ⊤ := by
  obtain ⟨e, he⟩ := projSet_iso X cV ⟨cw, cw_mem_cV⟩ inferInstance k
  have hg : secV X k ≫ e.hom = 𝟙 (Hpt X k) := by
    rw [secV, he, ← Work.Homology.singHomologyMap_comp, projSet_sectSet,
      Work.Homology.singHomologyMap_id]
  have h2 : secV X k = e.inv := by
    rw [← Category.id_comp e.inv, ← hg, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [h2, LinearMap.range_eq_top]
  intro y
  refine ⟨ModuleCat.Hom.hom e.hom y, ?_⟩
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.hom_inv_id) y
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h

theorem hsect_range_U (k : ℕ) : (hsect X k).hom.range = (incU X k).hom.range := by
  rw [hsect_eq_U, ModuleCat.hom_comp, LinearMap.range_comp, secU_range, Submodule.map_top]

theorem hsect_range_V (k : ℕ) : (hsect X k).hom.range = (incV X k).hom.range := by
  rw [hsect_eq_V, ModuleCat.hom_comp, LinearMap.range_comp, secV_range, Submodule.map_top]

/-- The second Mayer–Vietoris map is the difference of its two components. -/
theorem mvmr_decomp (k : ℕ) : mvmr X k = hmf X k ≫ incU X k - hms X k ≫ incV X k := by
  have htot : hmf X k ≫ hmi X k + hms X k ≫ hmj X k = 𝟙 (HBD X k) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]
  rw [← Category.id_comp (mvmr X k), ← htot, Preadditive.add_comp, Category.assoc, Category.assoc,
    show hmi X k ≫ mvmr X k = incU X k from mvr_inl X k,
    show hmj X k ≫ mvmr X k = -(incV X k) from mvr_inr X k]
  rw [Preadditive.comp_neg, sub_eq_add_neg]

/-- **The range of `mvmr` is the range of the section `X → X × S¹`.** -/
theorem mvr_range (n : ℕ) : (mvmr X (n + 1)).hom.range = (hsect X (n + 1)).hom.range := by
  apply le_antisymm
  · rw [hsect_range_U X (n+1)]
    rw [mvmr_decomp X (n+1), ModuleCat.hom_sub]
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · exact LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom (hmf X (n+1)) x, by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]⟩
    · have hUV : (incV X (n+1)).hom.range = (incU X (n+1)).hom.range :=
        (hsect_range_V X (n+1)).symm.trans (hsect_range_U X (n+1))
      rw [← hUV]
      exact LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom (hms X (n+1)) x, by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]⟩
  · rw [hsect_range_U X (n+1)]
    rw [← mvr_inl X (n+1)]
    intro y hy
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom (hmi X (n+1)) z, by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply]⟩

/-- **The kernel of `qm` is the range of the section.** -/
theorem qmap_ker (n : ℕ) : (qm X n).hom.ker = (hsect X (n + 1)).hom.range := by
  have hcomp : (adiag X n ≫ (Psi X n).hom) ≫ ((Psi X n).inv ≫ (biprod.fst : H2 X n ⟶ Hpt X n))
      = 𝟙 (Hpt X n) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, adiag, biprod.lift_fst]
  rw [qm, ModuleCat.hom_comp, ← mvr_range X n, ← del_ker X n]
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hzr : ModuleCat.Hom.hom (mvdel X n) z ∈ (ModuleCat.Hom.hom (mvdel X n)).range :=
      LinearMap.mem_range_self _ z
    rw [del_range X n, ker_alpha_eq X n] at hzr
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hzr
    have hone : ModuleCat.Hom.hom ((Psi X n).inv ≫ biprod.fst)
        (ModuleCat.Hom.hom (adiag X n ≫ (Psi X n).hom) y) = y := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomp) y
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using h
    have hy0 : y = 0 := by
      have h := hz
      rw [LinearMap.comp_apply, ← hy, hone] at h
      exact h
    rw [← hy, hy0, LinearMap.map_zero]
  · intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    rw [LinearMap.comp_apply, hz, LinearMap.map_zero]

/-- **`qm` is surjective.** -/
theorem qmap_range (n : ℕ) : (qm X n).hom.range = ⊤ := by
  have hcomp : (adiag X n ≫ (Psi X n).hom) ≫ ((Psi X n).inv ≫ (biprod.fst : H2 X n ⟶ Hpt X n))
      = 𝟙 (Hpt X n) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, adiag, biprod.lift_fst]
  rw [qm, ModuleCat.hom_comp, LinearMap.range_comp, del_range X n, ker_alpha_eq X n,
    ← LinearMap.range_comp, ← ModuleCat.hom_comp, hcomp, ModuleCat.hom_id, LinearMap.range_id]

/-- **The splitting lemma for `ℤ`-modules.**  If `A --c--> E --q--> B` is a short exact sequence
of `ℤ`-modules which is split by a retraction `r` of `c`, then `E ≅ A ⊞ B`. -/
theorem split_of_retraction {A E B : ModuleCat ℤ} (c : A ⟶ E) (q : E ⟶ B) (r : E ⟶ A)
    (hrc : c ≫ r = 𝟙 A) (hq : q.hom.range = ⊤) (hker : q.hom.ker = c.hom.range) :
    Nonempty (E ≅ biprod A B) := by
  have hzero : c ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : c.hom x ∈ LinearMap.ker q.hom := by
      rw [hker]; exact LinearMap.mem_range_self c.hom x
    have hx' : q.hom (c.hom x) = 0 := (LinearMap.mem_ker).mp hx
    simpa using hx'
  let S : ShortComplex (ModuleCat ℤ) := ShortComplex.mk c q hzero
  have hS : S.Exact :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mpr (by
      change c.hom.range = q.hom.ker
      exact hker.symm)
  have hfr : S.f ≫ r = 𝟙 S.X₁ := by
    change c ≫ r = 𝟙 A
    exact hrc
  have hepi : Epi S.g := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective q.hom
    exact LinearMap.range_eq_top.mp hq
  exact ⟨(ShortComplex.Splitting.ofExactOfRetraction S hS r hfr hepi).isoBinaryBiproduct⟩

/-- **Künneth with a circle**: `H_{n+1}(X × S¹) ≅ H_{n+1}(X) ⊞ H_n(X)`. -/
theorem prod_circle_aux (n : ℕ) : Nonempty (Hcyl X (n + 1) ≅ Hpt X (n + 1) ⊞ Hpt X n) := by
  exact split_of_retraction (hsect X (n+1)) (qm X n) (hproj X (n+1)) (hsect_hproj X (n+1))
    (qmap_range X n) (qmap_ker X n)

end PC

/-- **Künneth with a circle**: `H_{n+1}(X × S¹) ≅ H_{n+1}(X) ⊞ H_n(X)`. -/
theorem prod_circle (X : Type) [TopologicalSpace X] (n : ℕ) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod (n + 1)
        (TopCat.of (X × Work.PieceHomology.Circ))
      ≅ CategoryTheory.Limits.biprod
          (Work.Homology.singHomology Work.Homology.ZMod (n + 1) (TopCat.of X))
          (Work.Homology.singHomology Work.Homology.ZMod n (TopCat.of X))) := by
  exact PC.prod_circle_aux X n

end

end Work.PieceHomology
