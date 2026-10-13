import Mathlib
import Submission.Work.DSF1.Sheaf.FHCCDesign

/-!
# Dévissage helpers for flasque resolutions

Vocabulary and elementary lemmas used by
`Work.DSF1.Sheaf.cechTrivAt_of_flasque_terms`: restriction algebra for functors
`(Opens X)ᵒᵖ ⥤ AddCommGrpCat`, gluing/separation for presheaves satisfying the sheaf
condition, and the extension property `CyclesFlasque` of the (pre)sheaf of cycles.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u v

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ## Restriction bookkeeping -/

/-- Restriction maps of a presheaf with equal proofs of the inclusion agree. -/
lemma res_congr {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})} {A B : X.Opens}
    {h₁ h₂ : B ≤ A} : P.map (homOfLE h₁).op = P.map (homOfLE h₂).op := by
  rw [Subsingleton.elim h₁ h₂]

/-- Restriction maps are transitive. -/
lemma res_trans {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})} {A B C : X.Opens}
    (h₁ : B ≤ A) (h₂ : C ≤ B) (x : P.obj (op A)) :
    P.map (homOfLE h₂).op (P.map (homOfLE h₁).op x) = P.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- Naturality of the differentials along restriction. -/
lemma d_naturality {K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (d : ∀ n : ℕ, K n ⟶ K (n+1)) (n : ℕ) {A B : X.Opens} (h : B ≤ A)
    (x : (K n).obj (op A)) :
    (d n).app (op B) ((K n).map (homOfLE h).op x)
      = (K (n+1)).map (homOfLE h).op ((d n).app (op A) x) :=
  NatTrans.naturality_apply (d n) (homOfLE h).op x

/-- Naturality of the augmentation along restriction. -/
lemma aug_naturality {K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    {F : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})} (aug : F ⟶ K 0)
    {A B : X.Opens} (h : B ≤ A) (x : F.obj (op A)) :
    (aug.app (op B)) (F.map (homOfLE h).op x)
      = (K 0).map (homOfLE h).op ((aug.app (op A)) x) :=
  NatTrans.naturality_apply aug (homOfLE h).op x

/-- Transport of sections of a presheaf along an equality of opens. -/
noncomputable def resEq (P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) {A B : X.Opens}
    (h : A = B) : P.obj (op A) ⟶ P.obj (op B) :=
  P.map (eqToHom h.symm).op

lemma resEq_self (P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) {A B : X.Opens}
    (h : A = B) (x : P.obj (op A)) : resEq P h.symm (resEq P h x) = x := by
  simp only [resEq]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp

/-- Restricting a transported section. -/
lemma resEq_res (P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) {A B C : X.Opens}
    (h : A = B) (hCB : C ≤ B) (x : P.obj (op A)) :
    P.map (homOfLE hCB).op (resEq P h x)
      = P.map (homOfLE (hCB.trans (le_of_eq h.symm))).op x := by
  simp only [resEq]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- Naturality of the differentials under transport along an equality of opens. -/
lemma d_resEq {K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (d : ∀ n : ℕ, K n ⟶ K (n+1)) (n : ℕ) {A B : X.Opens} (h : A = B)
    (x : (K n).obj (op A)) :
    (d n).app (op B) (resEq (K n) h x) = resEq (K (n+1)) h ((d n).app (op A) x) := by
  simp only [resEq]
  exact NatTrans.naturality_apply (d n) (eqToHom h.symm).op x

/-! ## Gluing and separation for sheaves of abelian groups -/

/-- Separation: two sections of a sheaf over `V` which agree on a family covering `V` agree. -/
lemma sheaf_sep_supr {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {ι : Type v} (U : ι → X.Opens)
    {s t : P.obj (op (iSup U))}
    (h : ∀ i, P.map (Opens.leSupr U i).op s = P.map (Opens.leSupr U i).op t) : s = t := by
  let sf : ∀ i, P.obj (op (U i)) := fun i => P.map (Opens.leSupr U i).op s
  have hc : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    dsimp only [sf]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 1
  obtain ⟨gl, -, huniq⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing hP U sf hc
  rw [huniq s (fun i => rfl), huniq t (fun i => (h i).symm)]

/-- Gluing: a compatible family of sections of a sheaf, indexed by a family of opens `U`
contained in `V` and covering `V`, glues to a section over `V`. -/
lemma sheaf_glue_at {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {ι : Type v} (U : ι → X.Opens) {V : X.Opens}
    (hUV : ∀ i, U i ≤ V) (hcov : V ≤ iSup U) (sf : ∀ i, P.obj (op (U i)))
    (hc : TopCat.Presheaf.IsCompatible P U sf) :
    ∃ s : P.obj (op V), ∀ i, P.map (homOfLE (hUV i)).op s = sf i := by
  have hVeq : V = iSup U := le_antisymm hcov (iSup_le fun i => (hUV i))
  obtain ⟨gl, hgl, -⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing hP U sf hc
  refine ⟨P.map (eqToHom hVeq).op gl, fun i => ?_⟩
  have hcomp : (eqToHom hVeq).op ≫ (homOfLE (hUV i)).op = (Opens.leSupr U i).op :=
    Subsingleton.elim _ _
  calc P.map (homOfLE (hUV i)).op (P.map (eqToHom hVeq).op gl)
      = P.map ((eqToHom hVeq).op ≫ (homOfLE (hUV i)).op) gl := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    _ = P.map (Opens.leSupr U i).op gl := by rw [hcomp]
    _ = sf i := hgl i

/-- Separation, for sections over a prescribed open `V`. -/
lemma sheaf_sep_at {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {ι : Type v} (U : ι → X.Opens) {V : X.Opens}
    (hUV : ∀ i, U i ≤ V) (hcov : V ≤ iSup U) {s t : P.obj (op V)}
    (h : ∀ i, P.map (homOfLE (hUV i)).op s = P.map (homOfLE (hUV i)).op t) : s = t := by
  have hVeq : V = iSup U := le_antisymm hcov (iSup_le fun i => (hUV i))
  have key : ∀ i, P.map (Opens.leSupr U i).op (resEq P hVeq s)
      = P.map (Opens.leSupr U i).op (resEq P hVeq t) := by
    intro i
    show P.map (homOfLE (le_iSup U i)).op (resEq P hVeq s)
      = P.map (homOfLE (le_iSup U i)).op (resEq P hVeq t)
    rw [resEq_res P hVeq (le_iSup U i) s, resEq_res P hVeq (le_iSup U i) t]
    have e : (homOfLE ((le_iSup U i).trans (le_of_eq hVeq.symm))).op
        = (homOfLE (hUV i)).op := Subsingleton.elim _ _
    rw [e]
    exact h i
  have key2 := sheaf_sep_supr hP U key
  have key3 := congrArg (resEq P hVeq.symm) key2
  rw [resEq_self P hVeq s, resEq_self P hVeq t] at key3
  exact key3

/-- A sheaf has contractible sections over the union of an empty family of opens. -/
lemma subsingleton_obj_of_isSheaf_of_isEmpty {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {ι : Type v} [IsEmpty ι] (U : ι → X.Opens) :
    Subsingleton (P.obj (op (iSup U))) := by
  have h : ∃! s : P.obj (op (iSup U)),
      TopCat.Presheaf.IsGluing P U (fun i => isEmptyElim i) s :=
    TopCat.Presheaf.IsSheaf.isSheafUniqueGluing (C := AddCommGrpCat.{u}) (X := (X : TopCat.{u}))
      hP U (fun i => isEmptyElim i) (fun i => isEmptyElim i)
  refine ⟨fun a b => ?_⟩
  refine h.unique ?_ ?_
  · intro i; exact isEmptyElim i
  · intro i; exact isEmptyElim i

/-- Transport of the triviality of the sections of a sheaf along an equality. -/
lemma subsingleton_obj_of_eq {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    {A B : X.Opens} (h : A = B) (hs : Subsingleton (P.obj (op A))) :
    Subsingleton (P.obj (op B)) := by
  haveI := hs
  refine ⟨fun a b => ?_⟩
  have h1 : resEq P h (resEq P h.symm a) = resEq P h (resEq P h.symm b) :=
    congrArg (resEq P h) (Subsingleton.elim _ _)
  exact (resEq_self P h.symm a).symm.trans (h1.trans (resEq_self P h.symm b))

/-- A sheaf has at most one section over an open which is the union of an empty family. -/
lemma subsingleton_obj_of_isSheaf_of_iSup_eq {P : Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})}
    (hP : TopCat.Presheaf.IsSheaf P) {ι : Type v} [IsEmpty ι] (U : ι → X.Opens)
    {W : X.Opens} (hW : iSup U = W) : Subsingleton (P.obj (op W)) :=
  subsingleton_obj_of_eq hW (subsingleton_obj_of_isSheaf_of_isEmpty hP U)

/-! ## The extension property of the sheaf of cycles -/

/-- `CyclesFlasque K d V n`: the presheaf of `n`-cycles (the kernel of `d n`) has surjective
restriction maps between opens contained in `V`. -/
def CyclesFlasque (K : ℕ → Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (d : ∀ n : ℕ, K n ⟶ K (n+1)) (V : X.Opens) (n : ℕ) : Prop :=
  ∀ ⦃W' W : X.Opens⦄ (h : W' ≤ W), W ≤ V → ∀ z : (K n).obj (op W'),
    (d n).app (op W') z = 0 →
    ∃ z' : (K n).obj (op W), (d n).app (op W) z' = 0 ∧
      (K n).map (homOfLE h).op z' = z

/-! ## `iSup` over `Fin` -/

lemma iSup_fin_succ {α : Type*} [CompleteLattice α] (m : ℕ) (f : Fin (m+1) → α) :
    iSup f = iSup (fun i : Fin m => f i.castSucc) ⊔ f (Fin.last m) := by
  apply le_antisymm
  · refine iSup_le fun j => Fin.lastCases ?_ ?_ j
    · exact le_sup_right
    · intro i
      exact (le_iSup (fun i : Fin m => f i.castSucc) i).trans le_sup_left
  · exact sup_le (iSup_le fun i => le_iSup f i.castSucc) (le_iSup f (Fin.last m))

lemma iSup_fin_one {α : Type*} [CompleteLattice α] (f : Fin 1 → α) : iSup f = f 0 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [Subsingleton.elim i 0]
  · exact le_iSup f 0

end Work.DSF1.Sheaf
