import Mathlib
import Submission.Work.SymQuot.RelQuot.Setup
import Submission.Work.SymQuot.RelQuot.relQuot
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.isSeparated_sym
import Submission.Work.SymQuot.Product.permIso_hom_proj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry
open scoped MonoidalCategory Classical

universe u

variable {K : Type u} [Field K]

/-- The `n`-fold product `Cⁿ`, written as the categorical product so that the
`Pi.lift`/`CartesianMonoidalCategory.lift` computations match syntactically. -/
noncomputable abbrev Prodm (C : Work.CurveBasics.Curve K) (n : ℕ) : Work.SpecLin.Sch K :=
  ∏ᶜ (fun _ : Fin n => C.toOver)

/-- The family of projections of `Cᵐ ⊗ Cⁿ` onto `C` indexed by `Fin (m+n)`. -/
noncomputable def pjFam (C : Work.CurveBasics.Curve K) (m n : ℕ) :
    Fin (m+n) → (Prodm C m ⊗ Prodm C n ⟶ C.toOver) :=
  Fin.append
    (fun i : Fin m => SemiCartesianMonoidalCategory.fst (Prodm C m) (Prodm C n)
      ≫ Work.SymQuot.proj C.toOver m i)
    (fun j : Fin n => SemiCartesianMonoidalCategory.snd (Prodm C m) (Prodm C n)
      ≫ Work.SymQuot.proj C.toOver n j)

/-- `Cⁿ` is separated over `K` (it is a product of the separated `C`). -/
instance instIsSeparatedProdm (C : Work.CurveBasics.Curve K) (n : ℕ) :
    IsSeparated (Prodm C n).hom :=
  Work.SymQuot.instIsSeparatedProd C.toOver n

/-- `Sym^n C` is separated over `K`. -/
instance instIsSeparatedSym (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (n : ℕ) : IsSeparated (Work.SymQuot.Sym C n).hom :=
  Work.SymQuot.Sym.isSeparated_sym C n

/-- **The map `Cᵐ ⊗ Cⁿ ⟶ Sym^{m+n} C`** given by the sum of the `m+n` points, where the
`m+n` points are read off via `Fin.append`. -/
noncomputable def phiP (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) : Prodm C m ⊗ Prodm C n ⟶ Work.SymQuot.Sym C (m+n) :=
  Limits.Pi.lift (pjFam C m n) ≫ Work.SymQuot.Sym.quot C (m+n)

/-- The defining property of the projection family: postcomposing the cartesian pairing of the
two `Pi.lift`s with `Pi.lift (pjFam C m n)` gives `Pi.lift (Fin.append x y)`. -/
theorem lift_piLift_pjFam (C : Work.CurveBasics.Curve K) (m n : ℕ) {T : Work.SpecLin.Sch K}
    (x : Fin m → (T ⟶ C.toOver)) (y : Fin n → (T ⟶ C.toOver)) :
    CartesianMonoidalCategory.lift (Limits.Pi.lift x) (Limits.Pi.lift y)
        ≫ Limits.Pi.lift (pjFam C m n)
      = Limits.Pi.lift (Fin.append x y) := by
  apply Limits.Pi.hom_ext
  intro k
  simp only [Category.assoc, Limits.Pi.lift_comp_π]
  revert k
  refine Fin.addCases ?_ ?_
  · intro i
    simp only [pjFam, Fin.append_left]
    rw [← Category.assoc, CartesianMonoidalCategory.lift_fst]
    exact Limits.Pi.lift_comp_π x i
  · intro j
    simp only [pjFam, Fin.append_right]
    rw [← Category.assoc, CartesianMonoidalCategory.lift_snd]
    exact Limits.Pi.lift_comp_π y j

/-- The value of `phiP` on the pairing of two `Pi.lift`s. -/
theorem lift_phiP (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C] (m n : ℕ)
    {T : Work.SpecLin.Sch K}
    (x : Fin m → (T ⟶ C.toOver)) (y : Fin n → (T ⟶ C.toOver)) :
    CartesianMonoidalCategory.lift (Limits.Pi.lift x) (Limits.Pi.lift y) ≫ phiP C m n
      = Limits.Pi.lift (Fin.append x y) ≫ Work.SymQuot.Sym.quot C (m+n) := by
  rw [phiP, ← Category.assoc, lift_piLift_pjFam]

/-! ## The `S_n`-action and its interaction with `phiP` -/

/-- The `S_n`-action on `Cⁿ`, as a morphism of `K`-schemes. -/
noncomputable abbrev actm (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) : Prodm C n ⟶ Prodm C n :=
  Work.SymQuot.actOver (Prodm C n) (Work.SymQuot.symData C n)
    (Work.SymQuot.sym_hom_invariant C n) σ

/-- The action morphism on `Cⁿ` underlying `actm` is `permIso`. -/
@[simp]
theorem actm_eq (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    actm C n σ = (Work.SymQuot.permIso C.toOver σ.down).hom := by
  apply Over.OverMorphism.ext
  rfl

/-- The projection formula for the `S_n`-action on `Cⁿ`. -/
theorem actm_proj (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) (i : Fin n) :
    actm C n σ ≫ Work.SymQuot.proj C.toOver n i
      = Work.SymQuot.proj C.toOver n (σ.down.symm i) := by
  rw [actm_eq]
  exact Work.SymQuot.Product.permIso_hom_proj C.toOver σ.down i

/-- The quotient map `Sym.quot C n` is invariant under the action of `S_n` on `Cⁿ`. -/
theorem sym_quot_invariant (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    (Work.SymQuot.permIso C.toOver τ).hom ≫ Work.SymQuot.Sym.quot C n
      = Work.SymQuot.Sym.quot C n := by
  apply Over.OverMorphism.ext
  have h := (Work.SymQuot.symData C n).quotientMap_isInvariant (ULift.up τ)
  show (Work.SymQuot.permIso C.toOver τ).hom.left ≫ (Work.SymQuot.symData C n).quotientMap
      = (Work.SymQuot.symData C n).quotientMap
  exact h

/-- The `S_n`-action on `Cⁿ` fixes the quotient map. -/
theorem actm_quot (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    actm C n σ ≫ Work.SymQuot.Sym.quot C n = Work.SymQuot.Sym.quot C n := by
  rw [actm_eq]
  exact sym_quot_invariant C n σ.down

/-- The permutation of `Fin (m+n)` which applies `σ` to the first `m` coordinates and fixes
the last `n`. -/
noncomputable def permAppend {m : ℕ} (n : ℕ) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m+n)) :=
  (Equiv.trans finSumFinEquiv.symm (Equiv.sumCongr σ (Equiv.refl (Fin n)))).trans finSumFinEquiv

/-- The permutation of `Fin (m+n)` which fixes the first `m` coordinates and applies `τ` to
the last `n`. -/
noncomputable def permPrepend (m : ℕ) {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m+n)) :=
  (Equiv.trans finSumFinEquiv.symm (Equiv.sumCongr (Equiv.refl (Fin m)) τ)).trans finSumFinEquiv

lemma permAppend_castAdd {m n : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    permAppend n σ (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  simp only [permAppend, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]

lemma permAppend_natAdd {m n : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin n) :
    permAppend n σ (Fin.natAdd m j) = Fin.natAdd m j := by
  simp only [permAppend, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]

lemma permAppend_symm_castAdd {m n : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (permAppend n σ).symm (Fin.castAdd n i) = Fin.castAdd n (σ.symm i) := by
  rw [Equiv.symm_apply_eq, permAppend_castAdd, Equiv.apply_symm_apply]

lemma permAppend_symm_natAdd {m n : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin n) :
    (permAppend n σ).symm (Fin.natAdd m j) = Fin.natAdd m j := by
  rw [Equiv.symm_apply_eq, permAppend_natAdd]

lemma permPrepend_castAdd {m n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin m) :
    permPrepend m τ (Fin.castAdd n i) = Fin.castAdd n i := by
  simp only [permPrepend, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]

lemma permPrepend_natAdd {m n : ℕ} (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    permPrepend m τ (Fin.natAdd m j) = Fin.natAdd m (τ j) := by
  simp only [permPrepend, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]

lemma permPrepend_symm_castAdd {m n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin m) :
    (permPrepend m τ).symm (Fin.castAdd n i) = Fin.castAdd n i := by
  rw [Equiv.symm_apply_eq, permPrepend_castAdd]

lemma permPrepend_symm_natAdd {m n : ℕ} (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    (permPrepend m τ).symm (Fin.natAdd m j) = Fin.natAdd m (τ.symm j) := by
  rw [Equiv.symm_apply_eq, permPrepend_natAdd, Equiv.apply_symm_apply]

/-- **`phiP` is invariant under the `S_m`-action on the first factor.** -/
theorem phiP_invariant_first (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin m))) :
    (actm C m σ ▷ Prodm C n) ≫ phiP C m n = phiP C m n := by
  rw [phiP, ← Category.assoc]
  have hkey : (actm C m σ ▷ Prodm C n) ≫ Limits.Pi.lift (pjFam C m n)
      = Limits.Pi.lift (pjFam C m n)
        ≫ actm C (m+n) (ULift.up (permAppend n σ.down)) := by
    apply Limits.Pi.hom_ext
    intro k
    simp only [Category.assoc, Limits.Pi.lift_comp_π, actm_proj]
    revert k
    refine Fin.addCases ?_ ?_
    · intro i
      simp only [pjFam, permAppend_symm_castAdd, Fin.append_left]
      rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
      rw [Category.assoc, actm_proj]
    · intro j
      simp only [pjFam, permAppend_symm_natAdd, Fin.append_right]
      rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_snd]
  rw [hkey, Category.assoc, actm_quot]

/-- **`phiP` is invariant under the `S_n`-action on the second factor.** -/
theorem phiP_invariant_second (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) (τ : ULift.{u} (Equiv.Perm (Fin n))) :
    (Prodm C m ◁ actm C n τ) ≫ phiP C m n = phiP C m n := by
  rw [phiP, ← Category.assoc]
  have hkey : (Prodm C m ◁ actm C n τ) ≫ Limits.Pi.lift (pjFam C m n)
      = Limits.Pi.lift (pjFam C m n)
        ≫ actm C (m+n) (ULift.up (permPrepend m τ.down)) := by
    apply Limits.Pi.hom_ext
    intro k
    simp only [Category.assoc, Limits.Pi.lift_comp_π, actm_proj]
    revert k
    refine Fin.addCases ?_ ?_
    · intro i
      simp only [pjFam, permPrepend_symm_castAdd, Fin.append_left]
      rw [← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]
    · intro j
      simp only [pjFam, permPrepend_symm_natAdd, Fin.append_right]
      rw [← Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd]
      rw [Category.assoc, actm_proj]
  rw [hkey, Category.assoc, actm_quot]


/-- Composition of two right whiskerings. -/
lemma whiskerR_comp {X Y Z : Work.SpecLin.Sch K} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Work.SpecLin.Sch K) :
    (f ▷ W) ≫ (g ▷ W) = (f ≫ g) ▷ W := by
  rw [← MonoidalCategory.tensorHom_id f W, ← MonoidalCategory.tensorHom_id g W,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, MonoidalCategory.tensorHom_id]

/-! ## The relative-quotient calculus -/

/-- The quotient map of `relQuotScheme` is invariant under the group action. -/
theorem actOver_relQuotSchemeMap {X : Work.SpecLin.Sch K} {Γ : Type u} [Group Γ] [Fintype Γ]
    (D : QuotientData Γ X.left) (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (g : Γ) :
    Work.SymQuot.actOver X D hbase g ≫ Work.SymQuot.relQuotSchemeMap X D hbase
      = Work.SymQuot.relQuotSchemeMap X D hbase := by
  apply Over.OverMorphism.ext
  show D.action.hom g ≫ D.quotientMap = D.quotientMap
  exact D.quotientMap_isInvariant g

/-- The quotient map `X ⟶ X/Γ` of the relative quotient is an epimorphism (in the sense that
it is left-cancellable after whiskering with any `Y`). -/
theorem relQuot_epi (X Y Z : Work.SpecLin.Sch K) {Γ : Type u} [Group Γ] [Fintype Γ]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    (D : QuotientData Γ X.left) (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    {g₁ g₂ : (Work.SymQuot.relQuotScheme X D hbase) ⊗ Y ⟶ Z}
    (h : (Work.SymQuot.relQuotSchemeMap X D hbase ▷ Y) ≫ g₁
        = (Work.SymQuot.relQuotSchemeMap X D hbase ▷ Y) ≫ g₂) : g₁ = g₂ := by
  have hinv : ∀ γ : Γ,
      (Work.SymQuot.actOver X D hbase γ ▷ Y)
        ≫ ((Work.SymQuot.relQuotSchemeMap X D hbase ▷ Y) ≫ g₁)
        = (Work.SymQuot.relQuotSchemeMap X D hbase ▷ Y) ≫ g₁ := by
    intro γ
    have hw : (Work.SymQuot.actOver X D hbase γ ▷ Y)
        ≫ (Work.SymQuot.relQuotSchemeMap X D hbase ▷ Y)
        = ((Work.SymQuot.actOver X D hbase γ ≫ Work.SymQuot.relQuotSchemeMap X D hbase) ▷ Y) :=
      whiskerR_comp _ _ Y
    rw [← Category.assoc, hw, actOver_relQuotSchemeMap]
  obtain ⟨h', hh', huniq⟩ := relQuot X Y Z D hbase
    ((Work.SymQuot.relQuotSchemeMap X D hbase ▷ Y) ≫ g₁) hinv
  have e₁ : g₁ = h' := huniq g₁ rfl
  have e₂ : g₂ = h' := huniq g₂ (by rw [h])
  rw [e₁, e₂]

/-- The quotient map `Cᵐ ⟶ Sym^m C`, printed in the relative-quotient form so that the
whiskering computations match syntactically. -/
noncomputable abbrev qsym (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m : ℕ) : Prodm C m ⟶ Work.SymQuot.Sym C m :=
  Work.SymQuot.relQuotSchemeMap (Prodm C m) (Work.SymQuot.symData C m)
    (Work.SymQuot.sym_hom_invariant C m)

theorem qsym_eq_quot (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m : ℕ) : qsym C m = Work.SymQuot.Sym.quot C m := rfl

theorem relQuotScheme_sym (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m : ℕ) :
    Work.SymQuot.relQuotScheme (Prodm C m) (Work.SymQuot.symData C m)
        (Work.SymQuot.sym_hom_invariant C m) = Work.SymQuot.Sym C m := rfl

/-- The quotient of `Cᵐ ⊗ Cⁿ` by the `S_m`-action on the first factor, as a morphism
`Sym^m C ⊗ Cⁿ ⟶ Sym^{m+n} C`. -/
noncomputable def phi1 (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) : Work.SymQuot.Sym C m ⊗ Prodm C n ⟶ Work.SymQuot.Sym C (m+n) :=
  Classical.choose (relQuot (Prodm C m) (Prodm C n) (Work.SymQuot.Sym C (m+n))
    (Work.SymQuot.symData C m) (Work.SymQuot.sym_hom_invariant C m)
    (phiP C m n) (phiP_invariant_first C m n))

/-- The defining property of `phi1`. -/
theorem phi1_spec (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C] (m n : ℕ) :
    (qsym C m ▷ Prodm C n) ≫ phi1 C m n = phiP C m n :=
  (Classical.choose_spec (relQuot (Prodm C m) (Prodm C n) (Work.SymQuot.Sym C (m+n))
    (Work.SymQuot.symData C m) (Work.SymQuot.sym_hom_invariant C m)
    (phiP C m n) (phiP_invariant_first C m n))).1

/-- **`phi1` is invariant under the `S_n`-action on the second factor.** -/
theorem phi1_invariant_second (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) (τ : ULift.{u} (Equiv.Perm (Fin n))) :
    (Work.SymQuot.Sym C m ◁ actm C n τ) ≫ phi1 C m n = phi1 C m n := by
  refine relQuot_epi (Prodm C m) (Prodm C n) (Work.SymQuot.Sym C (m+n))
    (Work.SymQuot.symData C m) (Work.SymQuot.sym_hom_invariant C m) ?_
  have qterm : (qsym C m ▷ Prodm C n) ≫ (Work.SymQuot.Sym C m ◁ actm C n τ)
      = (Prodm C m ◁ actm C n τ) ≫ (qsym C m ▷ Prodm C n) :=
    (MonoidalCategory.tensorHom_def (qsym C m) (actm C n τ)).symm.trans
      (MonoidalCategory.tensorHom_def' (qsym C m) (actm C n τ))
  rw [← Category.assoc, qterm, Category.assoc]
  simp only [phi1_spec, phiP_invariant_second]


/-! ## The second relative quotient: `Sym^n C ⊗ Sym^m C ⟶ Sym^{m+n} C` -/

/-- The braided map `Cⁿ ⊗ Sym^m C ⟶ Sym^{m+n} C` is invariant under the `S_n`-action on the
first factor. -/
theorem h2_invariant (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) (τ : ULift.{u} (Equiv.Perm (Fin n))) :
    (actm C n τ ▷ Work.SymQuot.Sym C m)
        ≫ ((β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom ≫ phi1 C m n)
      = (β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom ≫ phi1 C m n := by
  rw [← Category.assoc,
    BraidedCategory.braiding_naturality_left (actm C n τ) (Work.SymQuot.Sym C m),
    Category.assoc, phi1_invariant_second]

/-- The quotient of `Cⁿ ⊗ Sym^m C` by the `S_n`-action on the first factor. -/
noncomputable def h2 (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) : Work.SymQuot.Sym C n ⊗ Work.SymQuot.Sym C m ⟶ Work.SymQuot.Sym C (m+n) :=
  Classical.choose (relQuot (Prodm C n) (Work.SymQuot.Sym C m) (Work.SymQuot.Sym C (m+n))
    (Work.SymQuot.symData C n) (Work.SymQuot.sym_hom_invariant C n)
    ((β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom ≫ phi1 C m n) (h2_invariant C m n))

/-- The defining property of `h2`. -/
theorem h2_spec (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C] (m n : ℕ) :
    (qsym C n ▷ Work.SymQuot.Sym C m) ≫ h2 C m n
      = (β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom ≫ phi1 C m n :=
  (Classical.choose_spec (relQuot (Prodm C n) (Work.SymQuot.Sym C m) (Work.SymQuot.Sym C (m+n))
    (Work.SymQuot.symData C n) (Work.SymQuot.sym_hom_invariant C n)
    ((β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom ≫ phi1 C m n) (h2_invariant C m n))).1

/-- **The addition map `Sym^m C ⊗ Sym^n C ⟶ Sym^{m+n} C`.** -/
noncomputable def addMap (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]
    (m n : ℕ) : Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n ⟶ Work.SymQuot.Sym C (m+n) :=
  (β_ (Work.SymQuot.Sym C m) (Work.SymQuot.Sym C n)).hom ≫ h2 C m n

/-- The defining property of `addMap`: composed with the quotient maps it is `phiP`. -/
theorem addMap_spec (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C] (m n : ℕ) :
    (qsym C m ⊗ₘ qsym C n) ≫ addMap C m n = phiP C m n := by
  rw [addMap]
  calc (qsym C m ⊗ₘ qsym C n)
        ≫ ((β_ (Work.SymQuot.Sym C m) (Work.SymQuot.Sym C n)).hom ≫ h2 C m n)
      = ((qsym C m ⊗ₘ qsym C n)
          ≫ (β_ (Work.SymQuot.Sym C m) (Work.SymQuot.Sym C n)).hom) ≫ h2 C m n :=
          (Category.assoc _ _ _).symm
    _ = ((β_ (Prodm C m) (Prodm C n)).hom ≫ (qsym C n ⊗ₘ qsym C m)) ≫ h2 C m n := by
          rw [BraidedCategory.braiding_naturality (qsym C m) (qsym C n)]
    _ = (β_ (Prodm C m) (Prodm C n)).hom ≫ ((qsym C n ⊗ₘ qsym C m) ≫ h2 C m n) :=
          Category.assoc _ _ _
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ (((Prodm C n ◁ qsym C m) ≫ (qsym C n ▷ Work.SymQuot.Sym C m)) ≫ h2 C m n) := by
          rw [MonoidalCategory.tensorHom_def' (qsym C n) (qsym C m)]
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ ((Prodm C n ◁ qsym C m)
            ≫ ((qsym C n ▷ Work.SymQuot.Sym C m) ≫ h2 C m n)) := by
          rw [Category.assoc]
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ ((Prodm C n ◁ qsym C m)
            ≫ ((β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom ≫ phi1 C m n)) := by
          rw [h2_spec]
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ (((Prodm C n ◁ qsym C m) ≫ (β_ (Prodm C n) (Work.SymQuot.Sym C m)).hom)
            ≫ phi1 C m n) := by
          rw [Category.assoc]
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ (((β_ (Prodm C n) (Prodm C m)).hom ≫ (qsym C m ▷ Prodm C n)) ≫ phi1 C m n) := by
          rw [BraidedCategory.braiding_naturality_right (Prodm C n) (qsym C m)]
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ ((β_ (Prodm C n) (Prodm C m)).hom
            ≫ ((qsym C m ▷ Prodm C n) ≫ phi1 C m n)) := by
          rw [Category.assoc]
    _ = (β_ (Prodm C m) (Prodm C n)).hom
          ≫ ((β_ (Prodm C n) (Prodm C m)).hom ≫ phiP C m n) := by
          rw [phi1_spec]
    _ = ((β_ (Prodm C m) (Prodm C n)).hom
          ≫ (β_ (Prodm C n) (Prodm C m)).hom) ≫ phiP C m n :=
          (Category.assoc _ _ _).symm
    _ = 𝟙 (Prodm C m ⊗ Prodm C n) ≫ phiP C m n := by
          rw [SymmetricCategory.symmetry (Prodm C m) (Prodm C n)]
    _ = phiP C m n := Category.id_comp _

/-! ## The addition map is compatible with `Sym.powMap` -/

open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem exists_addMap {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [Work.SymQuot.CurveAffineCover C] (m n : ℕ) :
    ∃ f : Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n ⟶ Work.SymQuot.Sym C (m + n),
      ∀ {T : Work.SpecLin.Sch K} (x : Fin m → (T ⟶ C.toOver)) (y : Fin n → (T ⟶ C.toOver)),
        CartesianMonoidalCategory.lift (Work.SymQuot.Sym.powMap C m x)
          (Work.SymQuot.Sym.powMap C n y) ≫ f
          = Work.SymQuot.Sym.powMap C (m + n) (Fin.append x y) := by
  refine ⟨addMap C m n, ?_⟩
  intro T x y
  show CartesianMonoidalCategory.lift (Limits.Pi.lift x ≫ Work.SymQuot.Sym.quot C m)
      (Limits.Pi.lift y ≫ Work.SymQuot.Sym.quot C n) ≫ addMap C m n
    = Limits.Pi.lift (Fin.append x y) ≫ Work.SymQuot.Sym.quot C (m+n)
  rw [← CartesianMonoidalCategory.lift_map (Limits.Pi.lift x) (Limits.Pi.lift y)
    (Work.SymQuot.Sym.quot C m) (Work.SymQuot.Sym.quot C n)]
  rw [Category.assoc, ← qsym_eq_quot C m, ← qsym_eq_quot C n, addMap_spec, lift_phiP]

end Work.SymQuot.RelQuot
