import Mathlib
import Submission.Work.Whitney.TripleRel
import Submission.Work.Whitney.TCMQDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two bracketings of the triple relative cup have the same image in `C^*(X,A+B+C)`

`Work.Whitney.tcmRelCup_tripleImage_agreeA` compares the two bracketings of the triple product of
`Work.Whitney.tcmRelCup` in the three-fold intersection complex `Work.Whitney.pd3CohR`.

## The argument (no representative-level Cauchy-Schwarz)

Write `K3 = C^*(X,A+B+C)`.  Both sides are images in `H(K3)` of classes on the two-fold complexes
`C^*(X,(A∪B)+C)` and `C^*(X,A+(B∪C))`, so that a priori one has to compare arbitrary cocycle
representatives.  The comparison is organised so that *no* such comparison is needed:

* `exists_cup3_of_generic` (a three-complex descent, `Submission/Work/Whitney/RelABComplex.lean`)
  is applied to the two *left-nested* products `taStarL` and `taStarR` below, producing the
  well-defined pairings `cupH13A` and `cupH31A` on relative cohomology.  Their defining property
  (`cupH13A_spec`, `cupH31A_spec`) computes them from **any** cocycle representatives; this is
  exactly the "well-definedness" that would otherwise be the delicate step.
* Consequently the left hand side is `cupH13A (relRelCupHMap X A B a b) c`, which by the defining
  property may be evaluated on the *explicit* representative `starAB α β` of
  `relRelCupHMap X A B a b` (obtained from `relRelCupHMap_apply`); similarly on the right.
* The two explicit classes `[taStarL (starAB α β) γ]` and `[taStarR α (starAB β γ)]` are compared
  by the single cochain identity `cupAssoc` (strict associativity of the Alexander–Whitney
  product), which carries the degree transport `Nat.add_assoc p q r`.

The file is self-contained: the cast/star toolkit (`taStarL`, `taStarR`, `taMemPd3`,
`taEqRecPd3Coe`) is reproduced locally so that this module does not depend on the work-in-progress
external-product file.
-/

namespace Work.Whitney
open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type} [TopologicalSpace X]

theorem tcmRelCup_gaugeA (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh ℤ m X A) (b : Work.Thom.RelCoh ℤ n X B) :
    (HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A B) (m + n)).hom
        (tcmRelCup A B hA hB m n a b) = relRelCupHMap (TopCat.of X) A B m n a b := by
  rw [tcmRelCup, tcmRelCupG_apply]
  exact tcmRelCupInv_spec (R := ℤ) A B hA hB (m + n) _

lemma cochainMap_cocycleA {R : Type} [CommRing R] {K L : CochainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) {n : ℕ} (x : K.X n) (hx : (K.d n (n+1)).hom x = 0) :
    (L.d n (n+1)).hom ((φ.f n) x) = 0 := by
  have h2 : (L.d n (n+1)).hom ((φ.f n).hom x) = (φ.f (n+1)).hom ((K.d n (n+1)).hom x) := by
    have h := congrArg (fun (g : K.X n ⟶ L.X (n+1)) => ModuleCat.Hom.hom g x)
      (HomologicalComplex.Hom.comm φ n (n+1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [h2, hx, map_zero]

lemma eqRec_homologyπ_genA {R : Type} [CommRing R] {K : CochainComplex (ModuleCat R) ℕ}
    {a b : ℕ} (h : a = b) (z : K.cycles a) :
    h ▸ ((K.homologyπ a).hom z) = (K.homologyπ b).hom (h ▸ z) := by
  cases h; rfl

lemma homologyMap_cocycleOfKA {R : Type} [CommRing R] {K L : CochainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) {k : ℕ} (γ : (K.X k)) (h : ((K.d k (k+1)).hom) γ = 0)
    (h' : ((L.d k (k+1)).hom) ((φ.f k).hom γ) = 0) :
    (HomologicalComplex.homologyMap φ k).hom ((K.homologyπ k).hom (cocycleOfK K γ h))
      = (L.homologyπ k).hom (cocycleOfK L ((φ.f k).hom γ) h') := by
  rw [homologyMap_homologyπ]
  refine congrArg (fun z => (L.homologyπ k).hom z) ?_
  apply iCycles_injective_K L k
  rw [cyclesMap_i_apply_gen φ k (cocycleOfK K γ h), iCycles_cocycleOfK K γ h,
    iCycles_cocycleOfK L ((φ.f k).hom γ) h']

lemma eqRec_iCycles_genA {R : Type} [CommRing R] {K : CochainComplex (ModuleCat R) ℕ}
    {a b : ℕ} (h : a = b) (z : K.cycles a) :
    h ▸ ((K.iCycles a).hom z) = (K.iCycles b).hom (h ▸ z) := by
  cases h; rfl

/-! ## Local copies of the cast and star-product toolkit -/

/-- The cup of a cochain vanishing on `A` and on `B` with one vanishing on `C` vanishes on
`A`, `B` and `C`. -/
lemma taMemPd3 {X : TopCat} {A B C : Set X} {m n : ℕ}
    (a : Cochain ℤ (TopCat.toSSet.obj X) m) (b : Cochain ℤ (TopCat.toSSet.obj X) n)
    (haA : a ∈ relKern ℤ X A m) (haB : a ∈ relKern ℤ X B m) (hbC : b ∈ relKern ℤ X C n) :
    cup ℤ (TopCat.toSSet.obj X) a b ∈ pd3KernR X A B C (m + n) :=
  Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr
    ⟨cup_mem_relKern_left ℤ X A haA b, cup_mem_relKern_left ℤ X B haB b⟩,
    cup_mem_relKern_right ℤ X C a hbC⟩

/-- The cup of a cochain vanishing on `A` with one vanishing on `B` and on `C`. -/
lemma taMemPd3' {X : TopCat} {A B C : Set X} {m n : ℕ}
    (a : Cochain ℤ (TopCat.toSSet.obj X) m) (b : Cochain ℤ (TopCat.toSSet.obj X) n)
    (haA : a ∈ relKern ℤ X A m) (hbB : b ∈ relKern ℤ X B n) (hbC : b ∈ relKern ℤ X C n) :
    cup ℤ (TopCat.toSSet.obj X) a b ∈ pd3KernR X A B C (m + n) :=
  Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr
    ⟨cup_mem_relKern_left ℤ X A haA b, cup_mem_relKern_right ℤ X B a hbB⟩,
    cup_mem_relKern_right ℤ X C a hbC⟩

/-- Transporting an element of the three-fold complex along a degree equality commutes with the
underlying cochain. -/
lemma taEqRecPd3Coe (X : TopCat) (A B C : Set X) {p q : ℕ} (h : p = q)
    (x : pd3KernR X A B C p) :
    ((h ▸ x : pd3KernR X A B C q).1 : Cochain ℤ (TopCat.toSSet.obj X) q)
      = h ▸ (x.1 : Cochain ℤ (TopCat.toSSet.obj X) p) := by
  cases h; rfl

/-- The underlying cochain of the differential of the three-fold complex. -/
lemma taPd3CohR_d_coe (X : TopCat) (A B C : Set X) (n : ℕ) (x : (pd3CohR X A B C).X n) :
    (((pd3CohR X A B C).d n (n+1)).hom x).1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := by
  have h1 : (ModuleCat.Hom.hom ((pd3CohR X A B C).d n (n+1))) x = (pd3DiffLMR X A B C n) x := by
    rw [pd3CohR_d]; rfl
  rw [h1, pd3DiffLMR_coe]
  have h2 : (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n + 1)))
      (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n)
      = cochainDiff ℤ (TopCat.toSSet.obj X) (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := by
    rw [show (singularCochainComplex ℤ X).d n (n+1)
        = dualDifferential ℤ X n from CochainComplex.of_d (dualChains ℤ X) (dualDifferential ℤ X) n]
    rfl
  exact congrArg (fun φ => (φ : Cochain ℤ (TopCat.toSSet.obj X) (n+1))) h2

/-- The underlying cochain of the differential of the `A+B` complex. -/
lemma taPdABCohR_d_coe_diff (X : TopCat) (A B : Set X) (n : ℕ) (x : (pdABCohR (R := ℤ) X A B).X n) :
    (((pdABCohR (R := ℤ) X A B).d n (n+1)).hom x).1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := by
  rw [show (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) X A B).d n (n+1))) x
      = (pdABDiffLMR X A B n) x from by rw [pdABCohR_d]; rfl, pdABDiffLMR_coe]
  have h2 : (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n + 1)))
      (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n)
      = cochainDiff ℤ (TopCat.toSSet.obj X) (x.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := by
    rw [show (singularCochainComplex ℤ X).d n (n+1)
        = dualDifferential ℤ X n from CochainComplex.of_d (dualChains ℤ X) (dualDifferential ℤ X) n]
    rfl
  exact congrArg (fun φ => (φ : Cochain ℤ (TopCat.toSSet.obj X) (n+1))) h2

/-- The cup of an `A+B`-cochain with a `C`-relative cochain, landing in the `A+B+C` complex. -/
def taStarL (X : TopCat) (A B C : Set X) (m n : ℕ) :
    (pdABCohR (R := ℤ) X A B).X m →ₗ[ℤ] (relComplex ℤ X C).X n →ₗ[ℤ]
      (pd3CohR X A B C).X (m + n) :=
  LinearMap.mk₂ ℤ
    (fun a b => ⟨cup ℤ (TopCat.toSSet.obj X) a.1 b.1,
      taMemPd3 a.1 b.1 (Submodule.mem_inf.mp a.2).1 (Submodule.mem_inf.mp a.2).2 b.2⟩)
    (fun a a' b => by
      apply Subtype.ext
      simp only [Submodule.coe_add, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).1 a.1 a'.1 b.1)
    (fun c a b => by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.1 c a.1 b.1)
    (fun a b b' => by
      apply Subtype.ext
      simp only [Submodule.coe_add, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.1 a.1 b.1 b'.1)
    (fun c a b => by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.2 c a.1 b.1)

lemma taStarL_coe (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (pdABCohR (R := ℤ) X A B).X m) (b : (relComplex ℤ X C).X n) :
    ((taStarL X A B C m n a b).1 : Cochain ℤ (TopCat.toSSet.obj X) (m + n))
      = cup ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
          (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := rfl

/-- **The Leibniz rule for `taStarL`**. -/
lemma taLeibniz3_starL (X : TopCat) (A B C : Set X) :
    Work.Whitney.ThreeCup.Leibniz3 (pdABCohR (R := ℤ) X A B) (relComplex ℤ X C)
      (pd3CohR X A B C) (taStarL X A B C) := by
  intro m n a b
  apply Subtype.ext
  rw [taPd3CohR_d_coe, Submodule.coe_add, Submodule.coe_smul, taEqRecPd3Coe]
  simp only [taStarL_coe, taPdABCohR_d_coe_diff, relComplex_d_coe', singularCochain_d_apply]
  exact cupLeibniz ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
    (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n)

/-- The cup of an `A`-relative cochain with a `B+C`-cochain, landing in the `A+B+C` complex. -/
def taStarR (X : TopCat) (A B C : Set X) (m n : ℕ) :
    (relComplex ℤ X A).X m →ₗ[ℤ] (pdABCohR (R := ℤ) X B C).X n →ₗ[ℤ]
      (pd3CohR X A B C).X (m + n) :=
  LinearMap.mk₂ ℤ
    (fun a b => ⟨cup ℤ (TopCat.toSSet.obj X) a.1 b.1,
      taMemPd3' a.1 b.1 a.2 (Submodule.mem_inf.mp b.2).1
        (Submodule.mem_inf.mp b.2).2⟩)
    (fun a a' b => by
      apply Subtype.ext
      simp only [Submodule.coe_add, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).1 a.1 a'.1 b.1)
    (fun c a b => by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.1 c a.1 b.1)
    (fun a b b' => by
      apply Subtype.ext
      simp only [Submodule.coe_add, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.1 a.1 b.1 b'.1)
    (fun c a b => by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subtype.coe_mk]
      exact (cupBilinear ℤ (TopCat.toSSet.obj X) m n).2.2.2 c a.1 b.1)

lemma taStarR_coe (X : TopCat) (A B C : Set X) (m n : ℕ)
    (a : (relComplex ℤ X A).X m) (b : (pdABCohR (R := ℤ) X B C).X n) :
    ((taStarR X A B C m n a b).1 : Cochain ℤ (TopCat.toSSet.obj X) (m + n))
      = cup ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
          (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n) := rfl

/-- **The Leibniz rule for `taStarR`**. -/
lemma taLeibniz3_starR (X : TopCat) (A B C : Set X) :
    Work.Whitney.ThreeCup.Leibniz3 (relComplex ℤ X A) (pdABCohR (R := ℤ) X B C)
      (pd3CohR X A B C) (taStarR X A B C) := by
  intro m n a b
  apply Subtype.ext
  rw [taPd3CohR_d_coe, Submodule.coe_add, Submodule.coe_smul, taEqRecPd3Coe]
  simp only [taStarR_coe, taPdABCohR_d_coe_diff, relComplex_d_coe', singularCochain_d_apply]
  exact cupLeibniz ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
    (b.1 : Cochain ℤ (TopCat.toSSet.obj X) n)

noncomputable def cupH13A (A B C : Set X) (p q : ℕ) :
    (pdABCohR (R := ℤ) (TopCat.of X) A B).homology p →
      ((relComplex ℤ (TopCat.of X) C).homology q →
        (pd3CohR (TopCat.of X) A B C).homology (p + q)) :=
  fun x y => ((Classical.choose (ThreeCup.exists_cup3_of_generic
    (pdABCohR (R := ℤ) (TopCat.of X) A B) (relComplex ℤ (TopCat.of X) C)
    (pd3CohR (TopCat.of X) A B C) (taStarL (TopCat.of X) A B C)
    (taLeibniz3_starL (TopCat.of X) A B C))) p q) x y

lemma cupH13A_spec (A B C : Set X) (m n : ℕ)
    (y : (pdABCohR (R := ℤ) (TopCat.of X) A B).X m)
    (w : (relComplex ℤ (TopCat.of X) C).X n)
    (hy : ((pdABCohR (R := ℤ) (TopCat.of X) A B).d m (m+1)).hom y = 0)
    (hw : ((relComplex ℤ (TopCat.of X) C).d n (n+1)).hom w = 0)
    (h : ((pd3CohR (TopCat.of X) A B C).d (m+n) (m+n+1)).hom
        (((taStarL (TopCat.of X) A B C m n) y) w) = 0) :
    cupH13A A B C m n
        (((pdABCohR (R := ℤ) (TopCat.of X) A B).homologyπ m).hom (cocycleOfK _ y hy))
        (((relComplex ℤ (TopCat.of X) C).homologyπ n).hom (cocycleOfK _ w hw))
      = ((pd3CohR (TopCat.of X) A B C).homologyπ (m+n)).hom
          (cocycleOfK _ (((taStarL (TopCat.of X) A B C m n) y) w) h) :=
  Classical.choose_spec (ThreeCup.exists_cup3_of_generic
    (pdABCohR (R := ℤ) (TopCat.of X) A B) (relComplex ℤ (TopCat.of X) C)
    (pd3CohR (TopCat.of X) A B C) (taStarL (TopCat.of X) A B C)
    (taLeibniz3_starL (TopCat.of X) A B C)) m n y w hy hw h

noncomputable def cupH31A (A B C : Set X) (p q : ℕ) :
    (relComplex ℤ (TopCat.of X) A).homology p →
      ((pdABCohR (R := ℤ) (TopCat.of X) B C).homology q →
        (pd3CohR (TopCat.of X) A B C).homology (p + q)) :=
  fun x y => ((Classical.choose (ThreeCup.exists_cup3_of_generic
    (relComplex ℤ (TopCat.of X) A) (pdABCohR (R := ℤ) (TopCat.of X) B C)
    (pd3CohR (TopCat.of X) A B C) (taStarR (TopCat.of X) A B C)
    (taLeibniz3_starR (TopCat.of X) A B C))) p q) x y

lemma cupH31A_spec (A B C : Set X) (m n : ℕ)
    (y : (relComplex ℤ (TopCat.of X) A).X m)
    (w : (pdABCohR (R := ℤ) (TopCat.of X) B C).X n)
    (hy : ((relComplex ℤ (TopCat.of X) A).d m (m+1)).hom y = 0)
    (hw : ((pdABCohR (R := ℤ) (TopCat.of X) B C).d n (n+1)).hom w = 0)
    (h : ((pd3CohR (TopCat.of X) A B C).d (m+n) (m+n+1)).hom
        (((taStarR (TopCat.of X) A B C m n) y) w) = 0) :
    cupH31A A B C m n
        (((relComplex ℤ (TopCat.of X) A).homologyπ m).hom (cocycleOfK _ y hy))
        (((pdABCohR (R := ℤ) (TopCat.of X) B C).homologyπ n).hom (cocycleOfK _ w hw))
      = ((pd3CohR (TopCat.of X) A B C).homologyπ (m+n)).hom
          (cocycleOfK _ (((taStarR (TopCat.of X) A B C m n) y) w) h) :=
  Classical.choose_spec (ThreeCup.exists_cup3_of_generic
    (relComplex ℤ (TopCat.of X) A) (pdABCohR (R := ℤ) (TopCat.of X) B C)
    (pd3CohR (TopCat.of X) A B C) (taStarR (TopCat.of X) A B C)
    (taLeibniz3_starR (TopCat.of X) A B C)) m n y w hy hw h


theorem tcmRelCup_tripleImage_agreeA {X : Type} [TopologicalSpace X] (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ) (a : Work.Thom.RelCoh ℤ p X A) (b : Work.Thom.RelCoh ℤ q X B) (c : Work.Thom.RelCoh ℤ r X C) : (Nat.add_assoc p q r) ▸ (((HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) (p + q + r)).hom ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) (p + q + r)).hom (tcmRelCup (A ∪ B) C (hA.union hB) hC (p + q) r (tcmRelCup A B hA hB p q a b) c))) : (pd3CohR (TopCat.of X) A B C).homology (p + q + r)) = (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C) (p + (q + r))).hom ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A (B ∪ C)) (p + (q + r))).hom (tcmRelCup A (B ∪ C) hA (hB.union hC) p (q + r) a (tcmRelCup B C hB hC q r b c))) := by

  obtain ⟨α, hα, hαa⟩ := exists_relClassOf ℤ (TopCat.of X) A p a
  obtain ⟨β, hβ, hβb⟩ := exists_relClassOf ℤ (TopCat.of X) B q b
  obtain ⟨γ, hγ, hγc⟩ := exists_relClassOf ℤ (TopCat.of X) C r c
  obtain ⟨x, hx, hxu⟩ := exists_relClassOf ℤ (TopCat.of X) (A ∪ B) (p + q)
    (tcmRelCup A B hA hB p q a b)
  obtain ⟨z, hz, hzv⟩ := exists_relClassOf ℤ (TopCat.of X) (B ∪ C) (q + r)
    (tcmRelCup B C hB hC q r b c)
  have hα' : ((relComplex ℤ (TopCat.of X) A).d p (p+1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex ℤ (TopCat.of X) B).d q (q+1)).hom β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hγ' : ((relComplex ℤ (TopCat.of X) C).d r (r+1)).hom γ = 0 := by
    rw [relComplex_d_apply]; exact hγ
  have hx' : ((relComplex ℤ (TopCat.of X) (A ∪ B)).d (p+q) ((p+q)+1)).hom x = 0 := by
    rw [relComplex_d_apply]; exact hx
  have hz' : ((relComplex ℤ (TopCat.of X) (B ∪ C)).d (q+r) ((q+r)+1)).hom z = 0 := by
    rw [relComplex_d_apply]; exact hz
  have hsAB : ((pdABCohR (R := ℤ) (TopCat.of X) A B).d (p+q) ((p+q)+1)).hom
      (((starAB (TopCat.of X) A B p q) α) β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (R := ℤ) (TopCat.of X) A B) p q α β hα' hβ'
  have hsBC : ((pdABCohR (R := ℤ) (TopCat.of X) B C).d (q+r) ((q+r)+1)).hom
      (((starAB (TopCat.of X) B C q r) β) γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (R := ℤ) (TopCat.of X) B C) q r β γ hβ' hγ'
  have hsx : ((pdABCohR (R := ℤ) (TopCat.of X) (A ∪ B) C).d ((p+q)+r) (((p+q)+r)+1)).hom
      (((starAB (TopCat.of X) (A ∪ B) C (p+q) r) x) γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (R := ℤ) (TopCat.of X) (A ∪ B) C) (p+q) r x γ hx' hγ'
  have hsz : ((pdABCohR (R := ℤ) (TopCat.of X) A (B ∪ C)).d (p+(q+r)) ((p+(q+r))+1)).hom
      (((starAB (TopCat.of X) A (B ∪ C) p (q+r)) α) z) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (R := ℤ) (TopCat.of X) A (B ∪ C)) p (q+r) α z hα' hz'
  have hφx : ((pdABCohR (R := ℤ) (TopCat.of X) A B).d (p+q) ((p+q)+1)).hom
      (((pdABInclRelR (R := ℤ) (TopCat.of X) A B).f (p+q)) x) = 0 :=
    cochainMap_cocycleA (φ := pdABInclRelR (R := ℤ) (TopCat.of X) A B) x hx'
  have hφz : ((pdABCohR (R := ℤ) (TopCat.of X) B C).d (q+r) ((q+r)+1)).hom
      (((pdABInclRelR (R := ℤ) (TopCat.of X) B C).f (q+r)) z) = 0 :=
    cochainMap_cocycleA (φ := pdABInclRelR (R := ℤ) (TopCat.of X) B C) z hz'
  have hw1 : ((pd3CohR (TopCat.of X) A B C).d ((p+q)+r) (((p+q)+r)+1)).hom
      (((taStarL (TopCat.of X) A B C (p+q) r) (((starAB (TopCat.of X) A B p q) α) β)) γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (taLeibniz3_starL (TopCat.of X) A B C) (p+q) r _ γ hsAB hγ'
  have hw1x : ((pd3CohR (TopCat.of X) A B C).d ((p+q)+r) (((p+q)+r)+1)).hom
      (((taStarL (TopCat.of X) A B C (p+q) r) (((pdABInclRelR (R := ℤ) (TopCat.of X) A B).f (p+q)) x)) γ) = 0 :=
    ThreeCup.star3_cocycle_cochain (taLeibniz3_starL (TopCat.of X) A B C) (p+q) r _ γ hφx hγ'
  have hw2 : ((pd3CohR (TopCat.of X) A B C).d (p+(q+r)) ((p+(q+r))+1)).hom
      (((taStarR (TopCat.of X) A B C p (q+r)) α) (((starAB (TopCat.of X) B C q r) β) γ)) = 0 :=
    ThreeCup.star3_cocycle_cochain (taLeibniz3_starR (TopCat.of X) A B C) p (q+r) α _ hα' hsBC
  have hw2z : ((pd3CohR (TopCat.of X) A B C).d (p+(q+r)) ((p+(q+r))+1)).hom
      (((taStarR (TopCat.of X) A B C p (q+r)) α) (((pdABInclRelR (R := ℤ) (TopCat.of X) B C).f (q+r)) z)) = 0 :=
    ThreeCup.star3_cocycle_cochain (taLeibniz3_starR (TopCat.of X) A B C) p (q+r) α _ hα' hφz
  -- the two representations of S = relRelCupHMap A B a b
  have hSab : relRelCupHMap (TopCat.of X) A B p q a b =
      ((pdABCohR (R := ℤ) (TopCat.of X) A B).homologyπ (p+q)).hom
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A B)
          (((starAB (TopCat.of X) A B p q) α) β) hsAB) := by
    have h1 := relRelCupHMap_apply (TopCat.of X) A B p q α β hα' hβ' hsAB
    rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα hα',
        ← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) B β hβ hβ', hαa, hβb] at h1
    exact h1
  have hSx : relRelCupHMap (TopCat.of X) A B p q a b =
      ((pdABCohR (R := ℤ) (TopCat.of X) A B).homologyπ (p+q)).hom
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A B)
          (((pdABInclRelR (R := ℤ) (TopCat.of X) A B).f (p+q)) x) hφx) := by
    rw [← tcmRelCup_gaugeA A B hA hB p q a b, ← hxu,
        relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) (A ∪ B) x hx hx']
    exact homologyMap_cocycleOfKA (R := ℤ) (pdABInclRelR (R := ℤ) (TopCat.of X) A B) x hx' hφx
  have hTbc : relRelCupHMap (TopCat.of X) B C q r b c =
      ((pdABCohR (R := ℤ) (TopCat.of X) B C).homologyπ (q+r)).hom
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) B C)
          (((starAB (TopCat.of X) B C q r) β) γ) hsBC) := by
    have h1 := relRelCupHMap_apply (TopCat.of X) B C q r β γ hβ' hγ' hsBC
    rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) B β hβ hβ',
        ← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C γ hγ hγ', hβb, hγc] at h1
    exact h1
  have hTz : relRelCupHMap (TopCat.of X) B C q r b c =
      ((pdABCohR (R := ℤ) (TopCat.of X) B C).homologyπ (q+r)).hom
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) B C)
          (((pdABInclRelR (R := ℤ) (TopCat.of X) B C).f (q+r)) z) hφz) := by
    rw [← tcmRelCup_gaugeA B C hB hC q r b c, ← hzv,
        relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) (B ∪ C) z hz hz']
    exact homologyMap_cocycleOfKA (R := ℤ) (pdABInclRelR (R := ℤ) (TopCat.of X) B C) z hz' hφz
  -- the LHS computation
  have hL : (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) (p + q + r)).hom
        ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) (p + q + r)).hom
          (tcmRelCup (A ∪ B) C (hA.union hB) hC (p + q) r (tcmRelCup A B hA hB p q a b) c))
      = ((pd3CohR (TopCat.of X) A B C).homologyπ ((p+q)+r)).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((taStarL (TopCat.of X) A B C (p+q) r) (((starAB (TopCat.of X) A B p q) α) β)) γ) hw1) := by
    rw [tcmRelCup_gaugeA (A ∪ B) C (hA.union hB) hC (p + q) r (tcmRelCup A B hA hB p q a b) c]
    have hrep1 : relRelCupHMap (TopCat.of X) (A ∪ B) C (p + q) r (tcmRelCup A B hA hB p q a b) c =
        ((pdABCohR (R := ℤ) (TopCat.of X) (A ∪ B) C).homologyπ ((p+q)+r)).hom
          (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) (A ∪ B) C)
            (((starAB (TopCat.of X) (A ∪ B) C (p+q) r) x) γ) hsx) := by
      have h1 := relRelCupHMap_apply (TopCat.of X) (A ∪ B) C (p+q) r x γ hx' hγ' hsx
      rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) (A ∪ B) x hx hx',
          ← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C γ hγ hγ', hxu, hγc] at h1
      exact h1
    rw [hrep1]
    have hdef1 : (((pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C).f ((p+q)+r))
        (((starAB (TopCat.of X) (A ∪ B) C (p+q) r) x) γ))
        = (((taStarL (TopCat.of X) A B C (p+q) r)
            (((pdABInclRelR (R := ℤ) (TopCat.of X) A B).f (p+q)) x)) γ) := rfl
    have hinc1c : ((pd3CohR (TopCat.of X) A B C).d ((p+q)+r) (((p+q)+r)+1)).hom
        (((pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C).f ((p+q)+r))
          (((starAB (TopCat.of X) (A ∪ B) C (p+q) r) x) γ)) = 0 :=
      cochainMap_cocycleA (φ := pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C)
        (((starAB (TopCat.of X) (A ∪ B) C (p+q) r) x) γ) hsx
    rw [homologyMap_cocycleOfKA (R := ℤ) (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) _ hsx hinc1c]
    have hstep1 : ((pd3CohR (TopCat.of X) A B C).homologyπ ((p+q)+r)).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C).f ((p+q)+r))
              (((starAB (TopCat.of X) (A ∪ B) C (p+q) r) x) γ)) hinc1c)
        = ((pd3CohR (TopCat.of X) A B C).homologyπ ((p+q)+r)).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((taStarL (TopCat.of X) A B C (p+q) r)
              (((pdABInclRelR (R := ℤ) (TopCat.of X) A B).f (p+q)) x)) γ) hw1x) := rfl
    rw [hstep1]
    rw [← cupH13A_spec A B C (p+q) r (((pdABInclRelR (R := ℤ) (TopCat.of X) A B).f (p+q)) x) γ hφx hγ' hw1x,
        ← hSx, hSab]
    exact cupH13A_spec A B C (p+q) r _ γ hsAB hγ' hw1
  -- the RHS computation
  have hR : (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C) (p + (q + r))).hom
        ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A (B ∪ C)) (p + (q + r))).hom
          (tcmRelCup A (B ∪ C) hA (hB.union hC) p (q + r) a (tcmRelCup B C hB hC q r b c)))
      = ((pd3CohR (TopCat.of X) A B C).homologyπ (p+(q+r))).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((taStarR (TopCat.of X) A B C p (q+r)) α) (((starAB (TopCat.of X) B C q r) β) γ)) hw2) := by
    rw [tcmRelCup_gaugeA A (B ∪ C) hA (hB.union hC) p (q + r) a (tcmRelCup B C hB hC q r b c)]
    have hrep2 : relRelCupHMap (TopCat.of X) A (B ∪ C) p (q + r) a (tcmRelCup B C hB hC q r b c) =
        ((pdABCohR (R := ℤ) (TopCat.of X) A (B ∪ C)).homologyπ (p+(q+r))).hom
          (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A (B ∪ C))
            (((starAB (TopCat.of X) A (B ∪ C) p (q+r)) α) z) hsz) := by
      have h1 := relRelCupHMap_apply (TopCat.of X) A (B ∪ C) p (q+r) α z hα' hz' hsz
      rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα hα',
          ← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) (B ∪ C) z hz hz', hαa, hzv] at h1
      exact h1
    rw [hrep2]
    have hdef2 : (((pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C).f (p+(q+r)))
        (((starAB (TopCat.of X) A (B ∪ C) p (q+r)) α) z))
        = (((taStarR (TopCat.of X) A B C p (q+r)) α)
            (((pdABInclRelR (R := ℤ) (TopCat.of X) B C).f (q+r)) z)) := rfl
    have hinc2c : ((pd3CohR (TopCat.of X) A B C).d (p+(q+r)) ((p+(q+r))+1)).hom
        (((pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C).f (p+(q+r)))
          (((starAB (TopCat.of X) A (B ∪ C) p (q+r)) α) z)) = 0 :=
      cochainMap_cocycleA (φ := pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C)
        (((starAB (TopCat.of X) A (B ∪ C) p (q+r)) α) z) hsz
    rw [homologyMap_cocycleOfKA (R := ℤ) (pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C) _ hsz hinc2c]
    have hstep2 : ((pd3CohR (TopCat.of X) A B C).homologyπ (p+(q+r))).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C).f (p+(q+r)))
              (((starAB (TopCat.of X) A (B ∪ C) p (q+r)) α) z)) hinc2c)
        = ((pd3CohR (TopCat.of X) A B C).homologyπ (p+(q+r))).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((taStarR (TopCat.of X) A B C p (q+r)) α)
              (((pdABInclRelR (R := ℤ) (TopCat.of X) B C).f (q+r)) z)) hw2z) := rfl
    rw [hstep2]
    rw [← cupH31A_spec A B C p (q+r) α (((pdABInclRelR (R := ℤ) (TopCat.of X) B C).f (q+r)) z) hα' hφz hw2z,
        ← hTz, hTbc]
    exact cupH31A_spec A B C p (q+r) α _ hα' hsBC hw2
  -- the comparison
  have hcast : ((Nat.add_assoc p q r) ▸
        (((taStarL (TopCat.of X) A B C (p+q) r) (((starAB (TopCat.of X) A B p q) α) β)) γ)
      : (pd3CohR (TopCat.of X) A B C).X (p+(q+r)))
      = (((taStarR (TopCat.of X) A B C p (q+r)) α) (((starAB (TopCat.of X) B C q r) β) γ)) := by
    apply Subtype.ext
    rw [taEqRecPd3Coe, taStarL_coe, starAB_coe, taStarR_coe, starAB_coe]
    exact cupAssoc ℤ (TopCat.toSSet.obj (TopCat.of X)) α.1 β.1 γ.1
  have hmid : (Nat.add_assoc p q r) ▸
        ((pd3CohR (TopCat.of X) A B C).homologyπ ((p+q)+r)).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((taStarL (TopCat.of X) A B C (p+q) r) (((starAB (TopCat.of X) A B p q) α) β)) γ) hw1)
      = ((pd3CohR (TopCat.of X) A B C).homologyπ (p+(q+r))).hom
          (cocycleOfK (pd3CohR (TopCat.of X) A B C)
            (((taStarR (TopCat.of X) A B C p (q+r)) α) (((starAB (TopCat.of X) B C q r) β) γ)) hw2) := by
    rw [eqRec_homologyπ_genA]
    congr 1
    apply iCycles_injective_K (pd3CohR (TopCat.of X) A B C) (p+(q+r))
    rw [← eqRec_iCycles_genA, iCycles_cocycleOfK, iCycles_cocycleOfK]
    exact hcast
  rw [hL, hR]
  exact hmid

end

end Work.Whitney
