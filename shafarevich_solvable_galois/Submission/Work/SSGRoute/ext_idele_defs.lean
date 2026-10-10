import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.NK.HassePrinciple.exists_level_of_h2
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level/orbit layer of the idèle Shapiro lemma (E2 of the Poitou–Tate design)

Definitions and elementary compatibility lemmas used by `Work.SSGRoute.ext_idele_shapiro`.

The level `𝕀_K^S = {x ∈ 𝕀_K | x_v ∈ 𝒪_vˣ for v ∉ S}` (NK's `levelRep`) is the filtered union of the
`Gal(K/k)`-stable levels; evaluation at a transversal `R` of the `Gal(K/k)`-orbits identifies
`Ext^r_G(M, 𝕀_K^S)` with `∏_{w ∈ R} Ext^r_{D_w}(M, B_w^S)`, where `B_w^S = K_wˣ` if `w ∈ S` and
`B_w^S = 𝒪_wˣ` otherwise.  This is the lemma `Work.SSGRoute.level_decomp_bijective`.
-/

set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-! ## The transversal of the Galois orbits -/

/-- Every place of `K` is the conjugate of the unique point of `R` in its orbit. -/
theorem exists_smul_eq_of_mem {R : Set (NK.GlobalCFT.Place K)}
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) : ∃ w : R, ∃ σ : K ≃ₐ[k] K, σ • v = w.1 := by
  obtain ⟨w, hw, -⟩ := hR v
  exact ⟨w, hw⟩

/-- Every place of `K` is the conjugate of a point of `R`. -/
theorem exists_eq_smul_of_mem {R : Set (NK.GlobalCFT.Place K)}
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (v : NK.GlobalCFT.Place K) : ∃ w : R, ∃ σ : K ≃ₐ[k] K, σ • w.1 = v := by
  obtain ⟨w, σ, hσ⟩ := exists_smul_eq_of_mem k K hR v
  exact ⟨w, σ⁻¹, by rw [← hσ, inv_smul_smul]⟩

/-- The conjugate of a point of the transversal which is again a point of the transversal is
itself: the transversal meets every orbit exactly once. -/
theorem mem_transversal_unique {R : Set (NK.GlobalCFT.Place K)}
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    {w : R} {σ : K ≃ₐ[k] K} (h : σ • w.1 ∈ R) : σ • w.1 = w.1 := by
  obtain ⟨u, -, huniq⟩ := hR w.1
  have hw : (⟨w.1, w.2⟩ : R) = u := huniq ⟨w.1, w.2⟩ ⟨1, by simp⟩
  have hw' : (⟨σ • w.1, h⟩ : R) = u := huniq ⟨σ • w.1, h⟩ ⟨σ, rfl⟩
  have : (⟨σ • w.1, h⟩ : R) = ⟨w.1, w.2⟩ := by rw [hw', hw]
  exact congrArg Subtype.val this

/-- A conjugate of a point of the transversal lies in the transversal iff it is the point
itself. -/
theorem smul_mem_transversal_iff {R : Set (NK.GlobalCFT.Place K)}
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (w : R) (σ : K ≃ₐ[k] K) : σ • w.1 ∈ R ↔ σ • w.1 = w.1 := by
  refine ⟨fun h => mem_transversal_unique k K hR h, fun h => ?_⟩
  rw [h]
  exact w.2

/-! ## The level `𝕀_K^S` and the local coefficient `B_w^S` -/

/-- The level `𝕀_K^S` as a `Gal(K/k)`-representation (NK's `levelRep`). -/
abbrev lvl (S : NK.HassePrinciple.GStableSet k K) : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K) :=
  NK.HassePrinciple.levelRep k K S

/-- **The local coefficient at `w` at the level `S`**: `K_wˣ` if `w ∈ S`, `𝒪_wˣ` otherwise. -/
noncomputable def BOf (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K) :
    Rep.{0, 0, 0} Coeff (decompK (k := k) w) := by
  classical
  exact if w ∈ S.carrier then localUnitsK (k := k) w
    else NK.HassePrinciple.localUnitsSubRep k K w

theorem BOf_of_mem {w : NK.GlobalCFT.Place K} {S : NK.HassePrinciple.GStableSet k K}
    (h : w ∈ S.carrier) : BOf k K w S = localUnitsK (k := k) w := by
  classical rw [BOf, if_pos h]

theorem BOf_of_notMem {w : NK.GlobalCFT.Place K} {S : NK.HassePrinciple.GStableSet k K}
    (h : w ∉ S.carrier) : BOf k K w S = NK.HassePrinciple.localUnitsSubRep k K w := by
  classical rw [BOf, if_neg h]

/-- The evaluation `𝕀_K^S → 𝒪_wˣ` at a place `w ∉ S`, as a monoid homomorphism. -/
noncomputable def levelEvalSubHom (w : NK.GlobalCFT.Place K)
    (S : NK.HassePrinciple.GStableSet k K) (hw : w ∉ S.carrier) :
    ↥(NK.HassePrinciple.levelSubgroup S.carrier) →*
      ↥(NK.GlobalCFT.Place.localUnits K w) :=
  MonoidHom.codRestrict ((NK.GlobalCFT.Idele.eval w).comp (Subgroup.subtype _))
    (NK.GlobalCFT.Place.localUnits K w)
    (fun x => NK.HassePrinciple.mem_levelSubgroup.mp x.2 w hw)

theorem levelEvalSubHom_apply (w : NK.GlobalCFT.Place K)
    (S : NK.HassePrinciple.GStableSet k K) (hw : w ∉ S.carrier)
    (x : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
    levelEvalSubHom k K w S hw x
      = ⟨(x : NK.GlobalCFT.Idele K) w,
          NK.HassePrinciple.mem_levelSubgroup.mp x.2 w hw⟩ := rfl

theorem levelEvalSubHom_equivariant (w : NK.GlobalCFT.Place K)
    (S : NK.HassePrinciple.GStableSet k K) (hw : w ∉ S.carrier)
    (σ : decompK (k := k) w) (x : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
    levelEvalSubHom k K w S hw (σ • x) = σ • levelEvalSubHom k K w S hw x := by
  apply Subtype.ext
  exact NK.HassePrinciple.smul_apply_stabilizer (K := k) (L := K) w σ
    (x : NK.GlobalCFT.Idele K)

/-- **Evaluation at `w` of a level idèle, into `𝒪_wˣ`** (valid when `w ∉ S`). -/
noncomputable def levelEvalSub (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K)
    (hw : w ∉ S.carrier) :
    Rep.res (decompK (k := k) w).subtype (lvl k K S) ⟶
      NK.HassePrinciple.localUnitsSubRep k K w :=
  NK.HassePrinciple.repHomOfMonoidHom (f := levelEvalSubHom k K w S hw)
    (hf := levelEvalSubHom_equivariant k K w S hw)

theorem levelEvalSub_apply (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K)
    (hw : w ∉ S.carrier) (x : (Rep.res (decompK (k := k) w).subtype (lvl k K S)).V) :
    (levelEvalSub k K w S hw).hom x = Additive.ofMul
      ⟨((Additive.toMul x : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
          NK.GlobalCFT.Idele K) w,
        NK.HassePrinciple.mem_levelSubgroup.mp (Additive.toMul x).2 w hw⟩ := rfl

/-- The inclusion `B_w^S ⟶ K_wˣ` of the local coefficient at the level `S` into the local
units. -/
noncomputable def BOfIncl (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K) :
    BOf k K w S ⟶ localUnitsK (k := k) w := by
  classical
  by_cases h : w ∈ S.carrier
  · exact eqToHom (BOf_of_mem (k := k) (K := K) h)
  · exact eqToHom (BOf_of_notMem (k := k) (K := K) h) ≫
      NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w

/-- **Evaluation at `w` of a level idèle, into `K_wˣ`.** -/
noncomputable def levelEvalA (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K) :
    Rep.res (decompK (k := k) w).subtype (lvl k K S) ⟶ localUnitsK (k := k) w :=
  Rep.resMap (decompK (k := k) w).subtype (NK.HassePrinciple.levelIncl k K S) ≫
    NK.HassePrinciple.ideleToLocalUnits k K w

theorem levelEvalA_apply (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K)
    (x : (Rep.res (decompK (k := k) w).subtype (lvl k K S)).V) :
    (levelEvalA k K w S).hom x = Additive.ofMul
      ((Additive.toMul x : ↥(NK.HassePrinciple.levelSubgroup S.carrier)) :
        NK.GlobalCFT.Idele K) w := by
  show (NK.HassePrinciple.ideleToLocalUnits (K := k) (L := K) w).hom
      ((Rep.resMap (decompK (k := k) w).subtype
        (NK.HassePrinciple.levelIncl k K S)).hom x) = _
  rw [Rep.resMap_hom_apply]
  rfl

/-- The evaluation into `𝒪_wˣ`, followed by the inclusion into `K_wˣ`, is the evaluation into
`K_wˣ` (for `w ∉ S`). -/
theorem levelEvalSub_comp_incl (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K)
    (hw : w ∉ S.carrier) :
    levelEvalSub k K w S hw ≫ NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w
      = levelEvalA k K w S := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w).hom
      ((levelEvalSub k K w S hw).hom x) = (levelEvalA k K w S).hom x
  rw [levelEvalSub_apply, levelEvalA_apply]
  rfl

/-- **Evaluation at `w` of a level idèle**, with values in the local coefficient `B_w^S`. -/
noncomputable def levelEval (w : NK.GlobalCFT.Place K) (S : NK.HassePrinciple.GStableSet k K) :
    Rep.res (decompK (k := k) w).subtype (lvl k K S) ⟶ BOf k K w S := by
  classical
  by_cases h : w ∈ S.carrier
  · exact levelEvalA k K w S ≫ eqToHom (BOf_of_mem (k := k) (K := K) h).symm
  · exact levelEvalSub k K w S h ≫ eqToHom (BOf_of_notMem (k := k) (K := K) h).symm

/-- The evaluation into `B_w^S` followed by the inclusion into `K_wˣ` is the evaluation. -/
theorem levelEval_comp_BOfIncl (w : NK.GlobalCFT.Place K)
    (S : NK.HassePrinciple.GStableSet k K) :
    levelEval k K w S ≫ BOfIncl k K w S = levelEvalA k K w S := by
  classical
  have key1 : ∀ {A B : Rep.{0, 0, 0} Coeff (decompK (k := k) w)} (e : A = B),
      eqToHom e.symm ≫ eqToHom e = 𝟙 B := by
    intro A B e
    cases e
    simp
  have key2 : ∀ {A B D : Rep.{0, 0, 0} Coeff (decompK (k := k) w)} (e : A = B) (g : B ⟶ D),
      eqToHom e.symm ≫ (eqToHom e ≫ g) = g := by
    intro A B D e g
    cases e
    simp
  by_cases h : w ∈ S.carrier
  · rw [levelEval, dif_pos h, BOfIncl, dif_pos h]
    simp only [Category.assoc]
    rw [key1 (BOf_of_mem (k := k) (K := K) h), Category.comp_id]
  · rw [levelEval, dif_neg h, BOfIncl, dif_neg h]
    simp only [Category.assoc]
    rw [key2 (BOf_of_notMem (k := k) (K := K) h)
      (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w)]
    exact levelEvalSub_comp_incl k K w S h

/-! ## The localisation maps -/

/-- **The level decomposition map**: localisation of `Ext^r_G(M, 𝕀_K^S)` at the places of the
transversal `R`, with values in `Ext^r_{D_w}(res M, B_w^S)`. -/
noncomputable def thetaL (R : Set (NK.GlobalCFT.Place K)) (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
    (r : ℕ) (S : NK.HassePrinciple.GStableSet k K) :
    Abelian.Ext M (lvl k K S) r → (w : R) →
      Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M) (BOf k K w.1 S) r :=
  fun x w => (extRes (decompK (k := k) w.1).subtype x).comp
    (Abelian.Ext.mk₀ (levelEval k K w.1 S)) (add_zero r)

/-- The push-forward of a class at the level `S` to the idèles. -/
noncomputable def pushLevel (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (r : ℕ)
    (S : NK.HassePrinciple.GStableSet k K) (x : Abelian.Ext M (lvl k K S) r) :
    Abelian.Ext M (idelesK k K) r :=
  x.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.levelIncl k K S)) (add_zero r)

/-- **The localisation of a pushed-forward level class**, in the coordinates `B_w^S`. -/
theorem extLoc_pushLevel (R : Set (NK.GlobalCFT.Place K))
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (r : ℕ)
    (S : NK.HassePrinciple.GStableSet k K) (x : Abelian.Ext M (lvl k K S) r)
    (w : R) :
    extLoc (k := k) w.1 (pushLevel k K M r S x)
      = ((thetaL k K R M r S x) w).comp
          (Abelian.Ext.mk₀ (BOfIncl k K w.1 S)) (add_zero r) := by
  have h1 : extRes (decompK (k := k) w.1).subtype (pushLevel k K M r S x)
      = (extRes (decompK (k := k) w.1).subtype x).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w.1).subtype
            (NK.HassePrinciple.levelIncl k K S))) (add_zero r) := by
    rw [extRes, pushLevel, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    rfl
  have inner : (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w.1).subtype
        (NK.HassePrinciple.levelIncl k K S))).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K w.1)) (zero_add 0)
      = (Abelian.Ext.mk₀ (levelEval k K w.1 S)).comp
          (Abelian.Ext.mk₀ (BOfIncl k K w.1 S)) (zero_add 0) := by
    rw [Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀,
      show Rep.resMap (decompK (k := k) w.1).subtype (NK.HassePrinciple.levelIncl k K S) ≫
          NK.HassePrinciple.ideleToLocalUnits k K w.1
        = levelEval k K w.1 S ≫ BOfIncl k K w.1 S from
        (levelEval_comp_BOfIncl k K w.1 S).symm]
  rw [extLoc, h1, thetaL]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [inner]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]

/-- The inclusion of the local coefficient at a place inside the level. -/
theorem BOfIncl_of_mem {w : NK.GlobalCFT.Place K} {S : NK.HassePrinciple.GStableSet k K}
    (h : w ∈ S.carrier) :
    BOfIncl k K w S = eqToHom (BOf_of_mem (k := k) (K := K) h) := by
  classical rw [BOfIncl, dif_pos h]

theorem BOfIncl_of_notMem {w : NK.GlobalCFT.Place K} {S : NK.HassePrinciple.GStableSet k K}
    (h : w ∉ S.carrier) :
    BOfIncl k K w S = eqToHom (BOf_of_notMem (k := k) (K := K) h) ≫
      NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w := by
  classical rw [BOfIncl, dif_neg h]

section Generic

variable {G : Type} [Group G]

/-- Composing with `mk₀` of an equality of coefficient modules is injective. -/
theorem ext_comp_mk₀_eqToHom_eq_zero_iff {X A B : Rep.{0, 0, 0} Coeff G} {n : ℕ}
    (e : A = B) (α : Abelian.Ext X A n) :
    α.comp (Abelian.Ext.mk₀ (eqToHom e)) (add_zero n) = 0 ↔ α = 0 := by
  constructor
  · intro h
    have h3 : (α.comp (Abelian.Ext.mk₀ (eqToHom e)) (add_zero n)).comp
        (Abelian.Ext.mk₀ (eqToHom e.symm)) (add_zero n) = 0 := by
      rw [h]
      simp
    have hkey : eqToHom e ≫ eqToHom e.symm = 𝟙 A := by
      cases e
      simp
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hkey,
      Abelian.Ext.comp_mk₀_id] at h3
    exact h3
  · intro h
    rw [h]
    simp

/-- Casting an `Ext`-class along an equality of coefficient modules is a bijection. -/
theorem ext_comp_cast_round {X A B : Rep.{0, 0, 0} Coeff G} {n : ℕ}
    (e : A = B) (α : Abelian.Ext X B n) :
    (α.comp (Abelian.Ext.mk₀ (eqToHom e.symm)) (add_zero n)).comp
      (Abelian.Ext.mk₀ (eqToHom e)) (add_zero n) = α := by
  have hkey : eqToHom e.symm ≫ eqToHom e = 𝟙 B := by
    cases e
    simp
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hkey,
    Abelian.Ext.comp_mk₀_id]

/-- Casting an `Ext`-class along an equality of coefficient modules, followed by a coefficient
map. -/
theorem ext_comp_cast_round' {X A B D : Rep.{0, 0, 0} Coeff G} {n : ℕ}
    (e : A = B) (β : B ⟶ D) (α : Abelian.Ext X B n) :
    (α.comp (Abelian.Ext.mk₀ (eqToHom e.symm)) (add_zero n)).comp
        (Abelian.Ext.mk₀ (eqToHom e ≫ β)) (add_zero n)
      = α.comp (Abelian.Ext.mk₀ β) (add_zero n) := by
  have hkey : eqToHom e.symm ≫ (eqToHom e ≫ β) = β := by
    cases e
    simp
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hkey]

end Generic

/-- The cast round trip for the local coefficient at a place inside the level. -/
theorem bofIncl_cast_mem {w : NK.GlobalCFT.Place K} {S : NK.HassePrinciple.GStableSet k K}
    (h : w ∈ S.carrier) (X : Rep.{0, 0, 0} Coeff (decompK (k := k) w)) {n : ℕ}
    (α : Abelian.Ext X (localUnitsK (k := k) w) n) :
    (α.comp (Abelian.Ext.mk₀ (eqToHom (BOf_of_mem (k := k) (K := K) h).symm))
        (add_zero n)).comp (Abelian.Ext.mk₀ (BOfIncl k K w S)) (add_zero n) = α := by
  rw [BOfIncl_of_mem (k := k) (K := K) h]
  exact ext_comp_cast_round (X := X) (n := n) (BOf_of_mem (k := k) (K := K) h) α

/-- The cast round trip for the local coefficient at a place outside the level. -/
theorem bofIncl_cast_notMem {w : NK.GlobalCFT.Place K} {S : NK.HassePrinciple.GStableSet k K}
    (h : w ∉ S.carrier) (X : Rep.{0, 0, 0} Coeff (decompK (k := k) w)) {n : ℕ}
    (z : Abelian.Ext X (NK.HassePrinciple.localUnitsSubRep k K w) n) :
    (z.comp (Abelian.Ext.mk₀ (eqToHom (BOf_of_notMem (k := k) (K := K) h).symm))
        (add_zero n)).comp (Abelian.Ext.mk₀ (BOfIncl k K w S)) (add_zero n)
      = z.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w))
          (add_zero n) := by
  rw [BOfIncl_of_notMem (k := k) (K := K) h]
  exact ext_comp_cast_round' (X := X) (n := n) (BOf_of_notMem (k := k) (K := K) h)
    (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w) z
/-- A pushed-forward level class is unramified at every place outside the level. -/
theorem isUnramifiedExt_extLoc_pushLevel (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (r : ℕ)
    (S : NK.HassePrinciple.GStableSet k K) (w : NK.GlobalCFT.Place K) (hw : w ∉ S.carrier)
    (x : Abelian.Ext M (lvl k K S) r) :
    IsUnramifiedExt w (extLoc (k := k) w (pushLevel k K M r S x)) := by
  refine ⟨((extRes (decompK (k := k) w).subtype x).comp
      (Abelian.Ext.mk₀ (levelEval k K w S)) (add_zero r)).comp
      (Abelian.Ext.mk₀ (eqToHom (BOf_of_notMem (k := k) (K := K) hw))) (add_zero r), ?_⟩
  have h1 : extLoc (k := k) w (pushLevel k K M r S x)
      = ((Abelian.Ext.mapExactFunctor (Rep.resFunctor (decompK (k := k) w).subtype) x).comp
          (Abelian.Ext.mk₀ (levelEval k K w S ≫ BOfIncl k K w S)) (add_zero r)) := by
    rw [extLoc, pushLevel, extRes, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀,
      show Rep.resMap (decompK (k := k) w).subtype (NK.HassePrinciple.levelIncl k K S) ≫
          NK.HassePrinciple.ideleToLocalUnits k K w = levelEval k K w S ≫ BOfIncl k K w S from
        (levelEval_comp_BOfIncl k K w S).symm]
  rw [h1, BOfIncl_of_notMem (k := k) (K := K) hw]
  rw [show levelEval k K w S ≫ (eqToHom (BOf_of_notMem (k := k) (K := K) hw) ≫
        NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w)
      = (levelEval k K w S ≫ eqToHom (BOf_of_notMem (k := k) (K := K) hw)) ≫
        NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w from
        (Category.assoc _ _ _).symm]
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_comp_mk₀,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero]
  rfl


/-- The level decomposition map sends `0` to `0`. -/
theorem thetaL_zero (R : Set (NK.GlobalCFT.Place K)) (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
    (r : ℕ) (S : NK.HassePrinciple.GStableSet k K) :
    thetaL k K R M r S (0 : Abelian.Ext M (lvl k K S) r) = 0 := by
  funext w
  simp [thetaL, extRes, Abelian.Ext.mapExactFunctor_zero]

/-- A finite representation is finitely generated as a `ℤ`-module. -/
theorem module_finite_int (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) [Finite M] :
    Module.Finite ℤ M.V :=
  by first | exact inferInstance | exact Module.Finite.of_finite

/-- **The local inclusion `𝒪_wˣ ↪ K_wˣ` admits a `D_w`-equivariant retraction.**  (This holds for all
but finitely many places `w`, see `local_retraction_ae`.) -/
def HasLocalRetraction (w : NK.GlobalCFT.Place K) : Prop :=
  ∃ r : localUnitsK (k := k) w ⟶ NK.HassePrinciple.localUnitsSubRep k K w,
    NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w ≫ r
      = 𝟙 (NK.HassePrinciple.localUnitsSubRep k K w)

/-- A retraction gives, for every local class, a class coming from `𝒪_wˣ`. -/
theorem exists_retraction_apply {w : NK.GlobalCFT.Place K} (h : HasLocalRetraction k K w) :
    ∃ r : localUnitsK (k := k) w ⟶ NK.HassePrinciple.localUnitsSubRep k K w,
      NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w ≫ r
        = 𝟙 (NK.HassePrinciple.localUnitsSubRep k K w) := h

end

end Work.SSGRoute
