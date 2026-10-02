import Mathlib
import Submission.Work.Whitney.TCMQDefs
import Submission.Work.Whitney.tcmRelCup_assoc
import Submission.Work.Whitney.pd3InclRelR_quasiIso
import Submission.Work.Cohomology.cupAssoc
import Submission.Work.Whitney.RelABComplex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

/-!
# Associativity of the canonical relative–relative cup product

The canonical relative–relative cup product `Work.Whitney.tcmRelCup` is the Alexander–Whitney
product on the `A+B` complex `C^*(X,A) ∩ C^*(X,B)`, transported along the inverse of the
quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`.  This module proves its associativity.

The two bracketings of the triple product are compared inside the three-fold intersection complex
`C^*(X, A+B+C)` (`Work.Whitney.pd3CohR`): both are computed by a *triple cup* on representatives,
and the two representatives agree by `Work.Cohomology.cupAssoc`; the common value is computed with
the descents `Work.Whitney.ThreeCup.exists_cup3_of_generic` of the two star products
`C^*(X,A+B) × C^*(X,C) → C^*(X,A+B+C)` and `C^*(X,A) × C^*(X,B+C) → C^*(X,A+B+C)`.  Injectivity of
`H^*(X, A∪B∪C) → H^*(X, A+B+C)` (`Work.Whitney.pd3InclRelR_quasiIso`) then gives the result.
-/

variable {X : Type} [TopologicalSpace X]

/-! ## Membership and coercion rules for the three-fold intersection complex -/

/-- The cup of a cochain vanishing on `A` and on `B` with one vanishing on `C` vanishes on
`A`, `B` and `C`. -/
lemma tcmRA_mem_AB_C (X : TopCat) {A B C : Set X} {m n : ℕ}
    (a : Cochain ℤ (TopCat.toSSet.obj X) m) (b : Cochain ℤ (TopCat.toSSet.obj X) n)
    (haA : a ∈ relKern ℤ X A m) (haB : a ∈ relKern ℤ X B m) (hbC : b ∈ relKern ℤ X C n) :
    cup ℤ (TopCat.toSSet.obj X) a b ∈ pd3KernR X A B C (m + n) := by
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact cup_mem_relKern_left ℤ X A haA b
  · exact cup_mem_relKern_left ℤ X B haB b
  · exact cup_mem_relKern_right ℤ X C a hbC

/-- The cup of a cochain vanishing on `A` with one vanishing on `B` and on `C` vanishes on
`A`, `B` and `C`. -/
lemma tcmRA_mem_A_BC (X : TopCat) {A B C : Set X} {m n : ℕ}
    (a : Cochain ℤ (TopCat.toSSet.obj X) m) (b : Cochain ℤ (TopCat.toSSet.obj X) n)
    (haA : a ∈ relKern ℤ X A m) (hbB : b ∈ relKern ℤ X B n) (hbC : b ∈ relKern ℤ X C n) :
    cup ℤ (TopCat.toSSet.obj X) a b ∈ pd3KernR X A B C (m + n) := by
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact cup_mem_relKern_left ℤ X A haA b
  · exact cup_mem_relKern_right ℤ X B a hbB
  · exact cup_mem_relKern_right ℤ X C a hbC

/-- The underlying cochain of the differential of the three-fold complex. -/
lemma tcmRA_pd3CohR_d_coe (X : TopCat) (A B C : Set X) (n : ℕ) (x : (pd3CohR X A B C).X n) :
    (((pd3CohR X A B C).d n (n+1)).hom x).1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := by
  rw [pd3CohR_d]
  change (((pd3DiffLMR X A B C n) x).1 : Cochain ℤ (TopCat.toSSet.obj X) (n+1)) = _
  rw [pd3DiffLMR_coe]
  exact singularCochain_d_apply ℤ X x.1

/-- Transporting an element of the three-fold complex along a degree equality commutes with the
underlying cochain. -/
lemma tcmRA_eqRec_pd3KernR_coe (X : TopCat) (A B C : Set X) {p q : ℕ} (h : p = q)
    (x : pd3KernR X A B C p) :
    ((h ▸ x : pd3KernR X A B C q).1 : Cochain ℤ (TopCat.toSSet.obj X) q)
      = h ▸ (x.1 : Cochain ℤ (TopCat.toSSet.obj X) p) := by
  cases h; rfl

/-- A morphism of cochain complexes sends a cocycle to a cocycle. -/
lemma tcmRA_map_d_eq_zero {K L : CochainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {n : ℕ}
    (x : K.X n) (hx : (K.d n (n+1)).hom x = 0) :
    (L.d n (n+1)).hom ((φ.f n).hom x) = 0 := by
  have hc := congrArg (fun (g : K.X n ⟶ L.X (n+1)) => g.hom x)
    (HomologicalComplex.Hom.comm φ n (n+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  rw [hx, map_zero] at hc
  exact hc

/-! ## The two star products into the three-fold complex, and their Leibniz rules -/

/-- The cup of an `A+B`-cochain with a `C`-relative cochain, landing in the three-fold complex
`C^*(X, A+B+C)`. -/
noncomputable def tcmRA_starAB_C (X : TopCat) (A B C : Set X) (m n : ℕ) :
    (pdABCohR (R := ℤ) X A B).X m →ₗ[ℤ] (relComplex ℤ X C).X n →ₗ[ℤ]
      (pd3CohR X A B C).X (m + n) :=
  LinearMap.mk₂ ℤ
    (fun a b => ⟨cup ℤ (TopCat.toSSet.obj X) a.1 b.1,
      tcmRA_mem_AB_C X a.1 b.1 (Submodule.mem_inf.mp a.2).1 (Submodule.mem_inf.mp a.2).2 b.2⟩)
    (fun a a' b => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).1 a.1 a'.1 b.1)
    (fun c a b => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.1 c a.1 b.1)
    (fun a b b' => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.1 a.1 b.1 b'.1)
    (fun c a b => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.2 c a.1 b.1)

lemma tcmRA_starAB_C_coe (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (pdABCohR (R := ℤ) X A B).X m) (b : (relComplex ℤ X C).X n) :
    ((tcmRA_starAB_C X A B C m n a b).1 : Cochain ℤ (TopCat.toSSet.obj X) (m + n))
      = cup ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
          (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := rfl

lemma tcmRA_Leibniz3_starAB_C (X : TopCat) (A B C : Set X) :
    ThreeCup.Leibniz3 (pdABCohR (R := ℤ) X A B) (relComplex ℤ X C)
      (pd3CohR X A B C) (tcmRA_starAB_C X A B C) := by
  intro m n a b
  apply Subtype.ext
  rw [tcmRA_pd3CohR_d_coe, Submodule.coe_add, Submodule.coe_smul, tcmRA_eqRec_pd3KernR_coe]
  simp only [tcmRA_starAB_C_coe, pdABCohR_d_coe, relComplex_d_coe', singularCochain_d_apply]
  exact cupLeibniz ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
    (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n)

/-- The cup of an `A`-relative cochain with a `B+C`-cochain, landing in the three-fold complex. -/
noncomputable def tcmRA_starA_BC (X : TopCat) (A B C : Set X) (m n : ℕ) :
    (relComplex ℤ X A).X m →ₗ[ℤ] (pdABCohR (R := ℤ) X B C).X n →ₗ[ℤ]
      (pd3CohR X A B C).X (m + n) :=
  LinearMap.mk₂ ℤ
    (fun a b => ⟨cup ℤ (TopCat.toSSet.obj X) a.1 b.1,
      tcmRA_mem_A_BC X a.1 b.1 a.2 (Submodule.mem_inf.mp b.2).1 (Submodule.mem_inf.mp b.2).2⟩)
    (fun a a' b => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).1 a.1 a'.1 b.1)
    (fun c a b => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.1 c a.1 b.1)
    (fun a b b' => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.1 a.1 b.1 b'.1)
    (fun c a b => by apply Subtype.ext; exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.2 c a.1 b.1)

lemma tcmRA_starA_BC_coe (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (relComplex ℤ X A).X m) (b : (pdABCohR (R := ℤ) X B C).X n) :
    ((tcmRA_starA_BC X A B C m n a b).1 : Cochain ℤ (TopCat.toSSet.obj X) (m + n))
      = cup ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
          (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := rfl

lemma tcmRA_Leibniz3_starA_BC (X : TopCat) (A B C : Set X) :
    ThreeCup.Leibniz3 (relComplex ℤ X A) (pdABCohR (R := ℤ) X B C)
      (pd3CohR X A B C) (tcmRA_starA_BC X A B C) := by
  intro m n a b
  apply Subtype.ext
  rw [tcmRA_pd3CohR_d_coe, Submodule.coe_add, Submodule.coe_smul, tcmRA_eqRec_pd3KernR_coe]
  simp only [tcmRA_starA_BC_coe, pdABCohR_d_coe, relComplex_d_coe', singularCochain_d_apply]
  exact cupLeibniz ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
    (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n)

/-! ## The descents of the two star products -/

/-- The descent of `Work.Whitney.tcmRA_starAB_C` to cohomology. -/
noncomputable def tcmRA_cupAB_C (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (pdABCohR (R := ℤ) X A B).homology m) (b : (relComplex ℤ X C).homology n) :
    (pd3CohR X A B C).homology (m + n) :=
  (Classical.choose (ThreeCup.exists_cup3_of_generic (pdABCohR (R := ℤ) X A B) (relComplex ℤ X C)
    (pd3CohR X A B C) (tcmRA_starAB_C X A B C) (tcmRA_Leibniz3_starAB_C X A B C))) m n a b

lemma tcmRA_cupAB_C_spec (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (pdABCohR (R := ℤ) X A B).X m) (b : (relComplex ℤ X C).X n)
    (ha : ((pdABCohR (R := ℤ) X A B).d m (m + 1)).hom a = 0)
    (hb : ((relComplex ℤ X C).d n (n + 1)).hom b = 0)
    (h : ((pd3CohR X A B C).d (m + n) (m + n + 1)).hom (tcmRA_starAB_C X A B C m n a b) = 0) :
    tcmRA_cupAB_C X A B C m n
        (((pdABCohR (R := ℤ) X A B).homologyπ m).hom (cocycleOfK _ a ha))
        (((relComplex ℤ X C).homologyπ n).hom (cocycleOfK _ b hb)) =
      ((pd3CohR X A B C).homologyπ (m + n)).hom
        (cocycleOfK _ (tcmRA_starAB_C X A B C m n a b) h) :=
  Classical.choose_spec (ThreeCup.exists_cup3_of_generic (pdABCohR (R := ℤ) X A B) (relComplex ℤ X C)
    (pd3CohR X A B C) (tcmRA_starAB_C X A B C) (tcmRA_Leibniz3_starAB_C X A B C)) m n a b ha hb h

/-- The descent of `Work.Whitney.tcmRA_starA_BC` to cohomology. -/
noncomputable def tcmRA_cupA_BC (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (relComplex ℤ X A).homology m) (b : (pdABCohR (R := ℤ) X B C).homology n) :
    (pd3CohR X A B C).homology (m + n) :=
  (Classical.choose (ThreeCup.exists_cup3_of_generic (relComplex ℤ X A) (pdABCohR (R := ℤ) X B C)
    (pd3CohR X A B C) (tcmRA_starA_BC X A B C) (tcmRA_Leibniz3_starA_BC X A B C))) m n a b

lemma tcmRA_cupA_BC_spec (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (relComplex ℤ X A).X m) (b : (pdABCohR (R := ℤ) X B C).X n)
    (ha : ((relComplex ℤ X A).d m (m + 1)).hom a = 0)
    (hb : ((pdABCohR (R := ℤ) X B C).d n (n + 1)).hom b = 0)
    (h : ((pd3CohR X A B C).d (m + n) (m + n + 1)).hom (tcmRA_starA_BC X A B C m n a b) = 0) :
    tcmRA_cupA_BC X A B C m n
        (((relComplex ℤ X A).homologyπ m).hom (cocycleOfK _ a ha))
        (((pdABCohR (R := ℤ) X B C).homologyπ n).hom (cocycleOfK _ b hb)) =
      ((pd3CohR X A B C).homologyπ (m + n)).hom
        (cocycleOfK _ (tcmRA_starA_BC X A B C m n a b) h) :=
  Classical.choose_spec (ThreeCup.exists_cup3_of_generic (relComplex ℤ X A) (pdABCohR (R := ℤ) X B C)
    (pd3CohR X A B C) (tcmRA_starA_BC X A B C) (tcmRA_Leibniz3_starA_BC X A B C)) m n a b ha hb h

/-! ## Coercion rules for the structural inclusions -/

lemma tcmRA_pdABInclRelR_coe (X : TopCat) (A B : Set X) (n : ℕ)
    (x : (relComplex ℤ X (A ∪ B)).X n) :
    ((ModuleCat.Hom.hom ((pdABInclRelR (R := ℤ) X A B).f n)) x).1 = x.1 := rfl

lemma tcmRA_pdABCOhR_to_pd3CohR_left_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (pdABCohR (R := ℤ) X (A ∪ B) C).X n) :
    ((ModuleCat.Hom.hom ((pdABCOhR_to_pd3CohR_left X A B C).f n)) x).1 = x.1 := rfl

lemma tcmRA_pdABCOhR_to_pd3CohR_right_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (pdABCohR (R := ℤ) X A (B ∪ C)).X n) :
    ((ModuleCat.Hom.hom ((pdABCOhR_to_pd3CohR_right X A B C).f n)) x).1 = x.1 := rfl

/-! ## The image of `relRelCupHMap` in the three-fold complex -/

/-- The image of the `(A∪B)+C` cup of two relative classes in `H^*(X, A+B+C)` is the triple
product computed by the descent `Work.Whitney.tcmRA_cupAB_C`. -/
theorem tcmRA_inc_left (X : TopCat) (A B C : Set X) (m n : ℕ)
    (u : (relComplex ℤ X (A ∪ B)).homology m) (c : (relComplex ℤ X C).homology n) :
    (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_left X A B C) (m + n)).hom
        ((relRelCupHMap X (A ∪ B) C m n) u c)
      = tcmRA_cupAB_C X A B C m n
          ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) X A B) m).hom u) c := by
  obtain ⟨x, hx, rfl⟩ := exists_relClassOf ℤ X (A ∪ B) m u
  obtain ⟨γ, hγ, rfl⟩ := exists_relClassOf ℤ X C n c
  have hx' : ((relComplex ℤ X (A ∪ B)).d m (m+1)).hom x = 0 := by
    rw [relComplex_d_apply]; exact hx
  have hγ' : ((relComplex ℤ X C).d n (n+1)).hom γ = 0 := by
    rw [relComplex_d_apply]; exact hγ
  have hstar : ((pdABCohR (R := ℤ) X (A ∪ B) C).d (m+n) (m+n+1)).hom
      (starAB X (A ∪ B) C m n x γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB X (A ∪ B) C) m n x γ hx' hγ'
  have hφ : ((pdABCohR (R := ℤ) X A B).d m (m+1)).hom
      ((pdABInclRelR (R := ℤ) X A B).f m x) = 0 :=
    tcmRA_map_d_eq_zero (pdABInclRelR (R := ℤ) X A B) x hx'
  have hstar3 : ((pd3CohR X A B C).d (m+n) (m+n+1)).hom
      (tcmRA_starAB_C X A B C m n ((pdABInclRelR (R := ℤ) X A B).f m x) γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (tcmRA_Leibniz3_starAB_C X A B C) m n _ γ hφ hγ'
  have hstar2 : ((pd3CohR X A B C).d (m+n) (m+n+1)).hom
      ((pdABCOhR_to_pd3CohR_left X A B C).f (m+n) (starAB X (A ∪ B) C m n x γ)) = 0 :=
    tcmRA_map_d_eq_zero (pdABCOhR_to_pd3CohR_left X A B C) (starAB X (A ∪ B) C m n x γ) hstar
  rw [relClassOf_eq_homologyπ_cocycleOfK ℤ X (A ∪ B) x hx hx',
      relClassOf_eq_homologyπ_cocycleOfK ℤ X C γ hγ hγ']
  rw [relRelCupHMap_apply X (A ∪ B) C m n x γ hx' hγ' hstar]
  rw [homologyMap_cocycleOfK (R := ℤ)
    (pdABCOhR_to_pd3CohR_left X A B C) (starAB X (A ∪ B) C m n x γ) hstar hstar2]
  rw [homologyMap_cocycleOfK (R := ℤ) (pdABInclRelR (R := ℤ) X A B) x hx' hφ]
  rw [tcmRA_cupAB_C_spec X A B C m n ((pdABInclRelR (R := ℤ) X A B).f m x) γ hφ hγ' hstar3]
  apply homologyπ_cocycleOfK_congr
  apply Subtype.ext
  rw [tcmRA_pdABCOhR_to_pd3CohR_left_coe, starAB_coe, tcmRA_starAB_C_coe,
    tcmRA_pdABInclRelR_coe]

/-- The image of the `A+(B∪C)` cup of two relative classes in `H^*(X, A+B+C)` is the triple
product computed by the descent `Work.Whitney.tcmRA_cupA_BC`. -/
theorem tcmRA_inc_right (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (relComplex ℤ X A).homology m) (v : (relComplex ℤ X (B ∪ C)).homology n) :
    (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_right X A B C) (m + n)).hom
        ((relRelCupHMap X A (B ∪ C) m n) a v)
      = tcmRA_cupA_BC X A B C m n a
          ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) X B C) n).hom v) := by
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf ℤ X A m a
  obtain ⟨y, hy, rfl⟩ := exists_relClassOf ℤ X (B ∪ C) n v
  have hα' : ((relComplex ℤ X A).d m (m+1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hy' : ((relComplex ℤ X (B ∪ C)).d n (n+1)).hom y = 0 := by
    rw [relComplex_d_apply]; exact hy
  have hstar : ((pdABCohR (R := ℤ) X A (B ∪ C)).d (m+n) (m+n+1)).hom
      (starAB X A (B ∪ C) m n α y) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB X A (B ∪ C)) m n α y hα' hy'
  have hφ : ((pdABCohR (R := ℤ) X B C).d n (n+1)).hom
      ((pdABInclRelR (R := ℤ) X B C).f n y) = 0 :=
    tcmRA_map_d_eq_zero (pdABInclRelR (R := ℤ) X B C) y hy'
  have hstar3 : ((pd3CohR X A B C).d (m+n) (m+n+1)).hom
      (tcmRA_starA_BC X A B C m n α ((pdABInclRelR (R := ℤ) X B C).f n y)) = 0 :=
    ThreeCup.star3_cocycle_cochain (tcmRA_Leibniz3_starA_BC X A B C) m n α _ hα' hφ
  have hstar2 : ((pd3CohR X A B C).d (m+n) (m+n+1)).hom
      ((pdABCOhR_to_pd3CohR_right X A B C).f (m+n) (starAB X A (B ∪ C) m n α y)) = 0 :=
    tcmRA_map_d_eq_zero (pdABCOhR_to_pd3CohR_right X A B C) (starAB X A (B ∪ C) m n α y) hstar
  rw [relClassOf_eq_homologyπ_cocycleOfK ℤ X A α hα hα',
      relClassOf_eq_homologyπ_cocycleOfK ℤ X (B ∪ C) y hy hy']
  rw [relRelCupHMap_apply X A (B ∪ C) m n α y hα' hy' hstar]
  rw [homologyMap_cocycleOfK (R := ℤ)
    (pdABCOhR_to_pd3CohR_right X A B C) (starAB X A (B ∪ C) m n α y) hstar hstar2]
  rw [homologyMap_cocycleOfK (R := ℤ) (pdABInclRelR (R := ℤ) X B C) y hy' hφ]
  rw [tcmRA_cupA_BC_spec X A B C m n α ((pdABInclRelR (R := ℤ) X B C).f n y) hα' hφ hstar3]
  apply homologyπ_cocycleOfK_congr
  apply Subtype.ext
  rw [tcmRA_pdABCOhR_to_pd3CohR_right_coe, starAB_coe, tcmRA_starA_BC_coe,
    tcmRA_pdABInclRelR_coe]

/-! ## The degree transport of a class of a cocycle -/

lemma tcmRA_eqRec_homologyπ_cocycleOfK {K : CochainComplex (ModuleCat ℤ) ℕ} {m m' : ℕ}
    (h : m = m') (w : K.X m) (hw : (K.d m (m+1)).hom w = 0) (w' : K.X m')
    (hw' : (K.d m' (m'+1)).hom w' = 0) (hww' : h ▸ w = w') :
    h ▸ ((K.homologyπ m).hom (cocycleOfK K w hw))
      = (K.homologyπ m').hom (cocycleOfK K w' hw') := by
  cases h
  subst hww'
  rw [cocycleOfK_proof_irrel K w hw hw']

/-! ## The two triple products agree on representatives -/

/-- **The two bracketings of the triple product agree in `H^*(X, A+B+C)`**: the triple product
computed from the `A+B` complex and the triple product computed from the `B+C` complex coincide,
the common value being `[cup (cup α β) γ] = [cup α (cup β γ)]` on cocycle representatives. -/
theorem tcmRA_cup_eq (X : TopCat) (A B C : Set X) (p q r : ℕ)
    (a : (relComplex ℤ X A).homology p) (b : (relComplex ℤ X B).homology q)
    (c : (relComplex ℤ X C).homology r) :
    (Nat.add_assoc p q r) ▸
        tcmRA_cupAB_C X A B C (p+q) r ((relRelCupHMap X A B p q) a b) c
      = tcmRA_cupA_BC X A B C p (q+r) a ((relRelCupHMap X B C q r) b c) := by
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf ℤ X A p a
  obtain ⟨β, hβ, rfl⟩ := exists_relClassOf ℤ X B q b
  obtain ⟨γ, hγ, rfl⟩ := exists_relClassOf ℤ X C r c
  have hα' : ((relComplex ℤ X A).d p (p+1)).hom α = 0 := by rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex ℤ X B).d q (q+1)).hom β = 0 := by rw [relComplex_d_apply]; exact hβ
  have hγ' : ((relComplex ℤ X C).d r (r+1)).hom γ = 0 := by rw [relComplex_d_apply]; exact hγ
  have hAB : ((pdABCohR (R := ℤ) X A B).d (p+q) (p+q+1)).hom
      (starAB X A B p q α β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB X A B) p q α β hα' hβ'
  have hBC : ((pdABCohR (R := ℤ) X B C).d (q+r) (q+r+1)).hom
      (starAB X B C q r β γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB X B C) q r β γ hβ' hγ'
  have hABC : ((pd3CohR X A B C).d ((p+q)+r) ((p+q)+r+1)).hom
      (tcmRA_starAB_C X A B C (p+q) r (starAB X A B p q α β) γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (tcmRA_Leibniz3_starAB_C X A B C) (p+q) r _ γ hAB hγ'
  have hABC2 : ((pd3CohR X A B C).d (p+(q+r)) (p+(q+r)+1)).hom
      (tcmRA_starA_BC X A B C p (q+r) α (starAB X B C q r β γ)) = 0 :=
    ThreeCup.star3_cocycle_cochain (tcmRA_Leibniz3_starA_BC X A B C) p (q+r) α _ hα' hBC
  rw [relClassOf_eq_homologyπ_cocycleOfK ℤ X A α hα hα',
      relClassOf_eq_homologyπ_cocycleOfK ℤ X B β hβ hβ',
      relClassOf_eq_homologyπ_cocycleOfK ℤ X C γ hγ hγ']
  rw [relRelCupHMap_apply X A B p q α β hα' hβ' hAB,
      relRelCupHMap_apply X B C q r β γ hβ' hγ' hBC]
  rw [tcmRA_cupAB_C_spec X A B C (p+q) r (starAB X A B p q α β) γ hAB hγ' hABC]
  rw [tcmRA_cupA_BC_spec X A B C p (q+r) α (starAB X B C q r β γ) hα' hBC hABC2]
  have hw : (Nat.add_assoc p q r) ▸ (tcmRA_starAB_C X A B C (p+q) r (starAB X A B p q α β) γ)
      = tcmRA_starA_BC X A B C p (q+r) α (starAB X B C q r β γ) := by
    apply Subtype.ext
    rw [tcmRA_eqRec_pd3KernR_coe, tcmRA_starAB_C_coe, tcmRA_starA_BC_coe, starAB_coe, starAB_coe]
    exact cupAssoc ℤ (TopCat.toSSet.obj X) α.1 β.1 γ.1
  rw [tcmRA_eqRec_homologyπ_cocycleOfK (h := Nat.add_assoc p q r) _ hABC _ hABC2 hw]

/-! ## The structural inclusion, for an arbitrary presentation of the union -/

/-- The inclusion `C^*(X,S) → C^*(X,A+B+C)` for a set `S` containing `A`, `B`, `C` (the
presentation of the union is irrelevant to the underlying cochain map). -/
def tcmRA_pd3InclRelROf (X : TopCat) (A B C S : Set X) (hA : A ⊆ S) (hB : B ⊆ S)
    (hC : C ⊆ S) : relComplex ℤ X S ⟶ pd3CohR X A B C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (le_inf (le_inf (relKern_mono hA) (relKern_mono hB)) (relKern_mono hC))))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        relComplex_d, pd3CohR_d]
      rfl)

lemma tcmRA_pd3InclRelROf_congr (X : TopCat) (A B C S : Set X) (h1 h1' : A ⊆ S)
    (h2 h2' : B ⊆ S) (h3 h3' : C ⊆ S) :
    tcmRA_pd3InclRelROf X A B C S h1 h2 h3 = tcmRA_pd3InclRelROf X A B C S h1' h2' h3' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The structural inclusion of `C^*(X,(A∪B)∪C)`. -/
abbrev tcmRA_ιS (X : TopCat) (A B C : Set X) : relComplex ℤ X ((A ∪ B) ∪ C) ⟶ pd3CohR X A B C :=
  tcmRA_pd3InclRelROf X A B C ((A ∪ B) ∪ C)
    (fun x hx => Or.inl (Or.inl hx)) (fun x hx => Or.inl (Or.inr hx)) (fun x hx => Or.inr hx)

/-- The structural inclusion of `C^*(X,A∪(B∪C))`. -/
abbrev tcmRA_ιT (X : TopCat) (A B C : Set X) : relComplex ℤ X (A ∪ (B ∪ C)) ⟶ pd3CohR X A B C :=
  tcmRA_pd3InclRelROf X A B C (A ∪ (B ∪ C))
    (fun x hx => Or.inl hx) (fun x hx => Or.inr (Or.inl hx)) (fun x hx => Or.inr (Or.inr hx))

/-- `Work.Whitney.pd3InclRelR` is the structural inclusion of `C^*(X,(A∪B)∪C)`. -/
lemma tcmRA_pd3InclRelR_eq_ιS (X : TopCat) (A B C : Set X) :
    pd3InclRelR X A B C = tcmRA_ιS X A B C := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- **The structural inclusion commutes with the transport of the source set**: transporting a
cohomology class of `C^*(X,S)` along an equality `S = T` of sets does not change its image in the
three-fold complex. -/
lemma tcmRA_pd3InclRelROf_transport (X : TopCat) (A B C : Set X) {S T : Set X} (h : S = T)
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hCS : C ⊆ S) (hAT : A ⊆ T) (hBT : B ⊆ T) (hCT : C ⊆ T)
    (n : ℕ) (x : (relComplex ℤ X S).homology n) :
    (HomologicalComplex.homologyMap (tcmRA_pd3InclRelROf X A B C T hAT hBT hCT) n).hom (h ▸ x)
      = (HomologicalComplex.homologyMap (tcmRA_pd3InclRelROf X A B C S hAS hBS hCS) n).hom x := by
  cases h
  rw [tcmRA_pd3InclRelROf_congr X A B C S hAS hAT hBS hBT hCS hCT]

/-! ## Transport of classes along an equality of sets -/

lemma tcmRA_eqRec_swap (X : TopCat) {S T : Set X} (h : S = T) {m m' : ℕ} (hN : m = m')
    (x : (relComplex ℤ X S).homology m) :
    h ▸ (hN ▸ x) = hN ▸ (h ▸ x) := by
  cases h; cases hN; rfl

lemma tcmRA_eqRec_self_symm (X : TopCat) {S T : Set X} (h : S = T) (n : ℕ)
    (x : (relComplex ℤ X S).homology n) : h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

lemma tcmRA_eqRec_symm_self (X : TopCat) {S T : Set X} (h : S = T) (n : ℕ)
    (x : (relComplex ℤ X T).homology n) : h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

lemma tcmRA_eqRec_symm_inj (X : TopCat) {S T : Set X} (h : S = T) (n : ℕ) :
    Function.Injective (fun x : (relComplex ℤ X T).homology n => h.symm ▸ x) := by
  intro x y hxy
  have h' := congrArg (fun z => h ▸ z) hxy
  rwa [tcmRA_eqRec_symm_self X h n x, tcmRA_eqRec_symm_self X h n y] at h'

/-! ## The target -/

theorem tcmRelCup_assoc_general {X : Type} [TopologicalSpace X] (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : Work.Thom.RelCoh ℤ p X A) (b : Work.Thom.RelCoh ℤ q X B)
    (c : Work.Thom.RelCoh ℤ r X C) :
    (Nat.add_assoc p q r) ▸ (Set.union_assoc A B C) ▸
      (Work.Whitney.tcmRelCup (A ∪ B) C (hA.union hB) hC (p + q) r
        (Work.Whitney.tcmRelCup A B hA hB p q a b) c)
    = (Work.Whitney.tcmRelCup A (B ∪ C) hA (hB.union hC) p (q + r) a
        (Work.Whitney.tcmRelCup B C hB hC q r b c)) := by
  set L₀ : Work.Thom.RelCoh ℤ ((p + q) + r) X ((A ∪ B) ∪ C) :=
    Work.Whitney.tcmRelCup (A ∪ B) C (hA.union hB) hC (p + q) r
      (Work.Whitney.tcmRelCup A B hA hB p q a b) c with hL₀
  set R₀ : Work.Thom.RelCoh ℤ (p + (q + r)) X (A ∪ (B ∪ C)) :=
    Work.Whitney.tcmRelCup A (B ∪ C) hA (hB.union hC) p (q + r) a
      (Work.Whitney.tcmRelCup B C hB hC q r b c) with hR₀
  -- the two images of the bracketed triple products in `H^*(X,A+B+C)`
  have hL : (HomologicalComplex.homologyMap (tcmRA_ιS (TopCat.of X) A B C) ((p + q) + r)).hom L₀
      = tcmRA_cupAB_C (TopCat.of X) A B C (p + q) r
          ((relRelCupHMap (TopCat.of X) A B p q) a b) c := by
    rw [hL₀]
    rw [show tcmRA_ιS (TopCat.of X) A B C
        = pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C
          ≫ pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C from rfl]
    rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tcmRelCup_gauge (A ∪ B) C (hA.union hB) hC (p + q) r
      (Work.Whitney.tcmRelCup A B hA hB p q a b) c]
    rw [tcmRA_inc_left (TopCat.of X) A B C (p + q) r
      (Work.Whitney.tcmRelCup A B hA hB p q a b) c]
    rw [tcmRelCup_gauge A B hA hB p q a b]
  have hR : (HomologicalComplex.homologyMap (tcmRA_ιT (TopCat.of X) A B C) (p + (q + r))).hom R₀
      = tcmRA_cupA_BC (TopCat.of X) A B C p (q + r) a
          ((relRelCupHMap (TopCat.of X) B C q r) b c) := by
    rw [hR₀]
    rw [show tcmRA_ιT (TopCat.of X) A B C
        = pdABInclRelR (R := ℤ) (TopCat.of X) A (B ∪ C)
          ≫ pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C from rfl]
    rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tcmRelCup_gauge A (B ∪ C) hA (hB.union hC) p (q + r) a
      (Work.Whitney.tcmRelCup B C hB hC q r b c)]
    rw [tcmRA_inc_right (TopCat.of X) A B C p (q + r) a
      (Work.Whitney.tcmRelCup B C hB hC q r b c)]
    rw [tcmRelCup_gauge B C hB hC q r b c]
  rw [← tcmRA_eqRec_swap (TopCat.of X) (Set.union_assoc A B C) (Nat.add_assoc p q r) L₀]
  refine tcmRA_eqRec_symm_inj (TopCat.of X) (Set.union_assoc A B C) (p + (q + r)) ?_
  show (Set.union_assoc A B C).symm ▸ ((Set.union_assoc A B C) ▸ ((Nat.add_assoc p q r) ▸ L₀))
      = (Set.union_assoc A B C).symm ▸ R₀
  rw [tcmRA_eqRec_self_symm (TopCat.of X) (Set.union_assoc A B C) (p + (q + r))
    ((Nat.add_assoc p q r) ▸ L₀)]
  apply pd3InclRelR_injective A B C hA hB hC (p + (q + r))
  show (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) (p + (q + r))).hom
        ((Nat.add_assoc p q r) ▸ L₀)
      = (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) (p + (q + r))).hom
        ((Set.union_assoc A B C).symm ▸ R₀)
  rw [tcmRA_pd3InclRelR_eq_ιS]
  rw [← eqRec_homologyMap (tcmRA_ιS (TopCat.of X) A B C) (Nat.add_assoc p q r) L₀]
  rw [tcmRA_pd3InclRelROf_transport (TopCat.of X) A B C (S := A ∪ (B ∪ C)) (T := (A ∪ B) ∪ C)
    (Set.union_assoc A B C).symm
    (fun x hx => Or.inl hx) (fun x hx => Or.inr (Or.inl hx)) (fun x hx => Or.inr (Or.inr hx))
    (fun x hx => Or.inl (Or.inl hx)) (fun x hx => Or.inl (Or.inr hx)) (fun x hx => Or.inr hx)
    (p + (q + r)) R₀]
  rw [hL, hR]
  exact tcmRA_cup_eq (TopCat.of X) A B C p q r a b c

end

end Work.Whitney
