import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Cohomology.CupRing
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.sph3DiscMixedDefs
import Submission.Work.Cohomology.cupAssoc
import Submission.Work.Cohomology.cupNatural
import Submission.Work.Cohomology.relCupHNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace Work.Thom

open Work.TangentClasses

open Work.Cohomology

noncomputable section

/-- The cocycle condition is transported along an equality of degrees (general complex). -/
lemma cocycle_transport_K {K : CochainComplex (ModuleCat ℤ) ℕ} {k j : ℕ} (h : k = j)
    (u : K.X k) (hu : ModuleCat.Hom.hom (K.d k (k+1)) u = 0) :
    ModuleCat.Hom.hom (K.d j (j+1)) ((K.XIsoOfEq h).hom u) = 0 := by
  have e1 := HomologicalComplex.XIsoOfEq_hom_comp_d K h (j+1)
  have e1' := congrArg (fun (g : K.X k ⟶ K.X (j+1)) => ModuleCat.Hom.hom g u) e1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1'
  have e2 := HomologicalComplex.d_comp_XIsoOfEq_hom K (congrArg (fun t => t + 1) h) k
  have e2' := congrArg (fun (g : K.X k ⟶ K.X (j+1)) => ModuleCat.Hom.hom g u) e2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2'
  rw [e1', ← e2', hu, map_zero]

lemma relComplex_XIsoOfEq_coe {Y : TopCat} {B : Set Y} {k j : ℕ} (h : k = j)
    (y : (relComplex ℤ Y B).X k) :
    ((((relComplex ℤ Y B).XIsoOfEq h).hom y)).1 =
      (h ▸ (y.1 : Cochain ℤ (TopCat.toSSet.obj Y) k) : Cochain ℤ (TopCat.toSSet.obj Y) j) := by
  subst h; simp

lemma eqRec_homologyπ_cocycleOfK {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (y : K.X a) (hy : (K.d a (a+1)).hom y = 0)
    (hy' : (K.d b (b+1)).hom ((K.XIsoOfEq h).hom y) = 0) :
    (h ▸ (K.homologyπ a (cocycleOfK K y hy)) : K.homology b)
      = K.homologyπ b (cocycleOfK K ((K.XIsoOfEq h).hom y) hy') := by
  cases h; simp

lemma relClassOf_cast {Y : TopCat} {A : Set Y} {k j : ℕ} (h : k = j)
    (u : relKern ℤ Y A k) (hu : relDiffLM ℤ Y A k u = 0)
    (hu' : relDiffLM ℤ Y A j (((relComplex ℤ Y A).XIsoOfEq h).hom u) = 0) :
    (h ▸ relClassOf ℤ Y A u hu : (relComplex ℤ Y A).homology j)
      = relClassOf ℤ Y A (((relComplex ℤ Y A).XIsoOfEq h).hom u) hu' := by
  rw [show relClassOf ℤ Y A u hu = (relComplex ℤ Y A).homologyπ k
      (cocycleOfK (relComplex ℤ Y A) u (show ((relComplex ℤ Y A).d k (k+1)).hom u = 0 by
        rw [relComplex_d]; exact hu)) from rfl,
    show relClassOf ℤ Y A (((relComplex ℤ Y A).XIsoOfEq h).hom u) hu'
      = (relComplex ℤ Y A).homologyπ j
        (cocycleOfK (relComplex ℤ Y A) (((relComplex ℤ Y A).XIsoOfEq h).hom u)
          (show ((relComplex ℤ Y A).d j (j+1)).hom (((relComplex ℤ Y A).XIsoOfEq h).hom u) = 0 by
            rw [relComplex_d]; exact hu')) from rfl]
  exact eqRec_homologyπ_cocycleOfK (K := relComplex ℤ Y A) h u _ _

lemma cup_cast_right {X : SSet} (m : ℕ) (α : Cochain ℤ X m) {k j : ℕ}
    (h : k = j) (h' : m + k = m + j) (β : Cochain ℤ X k) :
    cup ℤ X α (h ▸ β) = (h' ▸ (cup ℤ X α β) : Cochain ℤ X (m + j)) := by
  rw [Subsingleton.elim h' (congrArg (fun t => m + t) h)]
  cases h
  rfl

lemma eqRec_comp {P : ℕ → Type*} {a b c : ℕ} (h₂ : a = b) (h₁ : b = c) (x : P a) :
    (h₁ ▸ (h₂ ▸ x) : P c) = ((h₂.trans h₁) ▸ x : P c) := by
  cases h₂; cases h₁; rfl

lemma eqRec_zero_add_cancel (P : ℕ → Type*) (n : ℕ)
    (h₁ : 0 + (0 + n) = 0 + n) (h₂ : (0 + 0) + n = 0 + (0 + n)) (x : P ((0 + 0) + n)) :
    (h₁ ▸ (h₂ ▸ x) : P (0 + n)) = x := by
  rw [eqRec_comp h₂ h₁ x]



lemma mixedCupC_zero_cast_assoc {B : Type} [TopologicalSpace B] (A : Set B) (n : ℕ)
    (h : 0 + n = n) (a b : Coh ℤ 0 B) (z : RelCoh ℤ n B A) :
    (mixedCupC ℤ A 0 n) a (h ▸ ((mixedCupC ℤ A 0 n) b z))
      = (mixedCupC ℤ A 0 n) (cupH' ℤ (TopCat.toSSet.obj (TopCat.of B)) 0 0 a b) z := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of B)) 0 a
  obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of B)) 0 b
  obtain ⟨ζ, hζ, rfl⟩ := exists_relClassOf ℤ (TopCat.of B) A n z
  simp only [mixedCupC_eq_mixedCup]
  obtain ⟨hmem1, hcoc1, h1⟩ := mixedCup_apply (TopCat.of B) A 0 n β ζ hβ hζ
  rw [h1]
  let u : relKern ℤ (TopCat.of B) A (0 + n) :=
    ⟨cup ℤ (TopCat.toSSet.obj (TopCat.of B)) β ζ.1, hmem1⟩
  have hu : relDiffLM ℤ (TopCat.of B) A (0+n) u = 0 := hcoc1
  have hu' : relDiffLM ℤ (TopCat.of B) A n
      (((relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u) = 0 := by
    rw [← relComplex_d_apply]
    exact cocycle_transport_K (K := relComplex ℤ (TopCat.of B) A) h u
      (by rw [relComplex_d_apply]; exact hu)
  have hcast : (h ▸ relClassOf ℤ (TopCat.of B) A u hu : RelCoh ℤ n B A)
      = relClassOf ℤ (TopCat.of B) A (((relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u) hu' :=
    relClassOf_cast h u hu hu'
  rw [hcast]
  obtain ⟨hmem2, hcoc2, h2⟩ := mixedCup_apply (TopCat.of B) A 0 n α
    (((relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u) hα hu'
  rw [h2]
  rw [cupH'_apply' ℤ (TopCat.toSSet.obj (TopCat.of B)) α β hα hβ]
  obtain ⟨hmem3, hcoc3, h3⟩ := mixedCup_apply (TopCat.of B) A 0 n
    (cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α β) ζ
    (cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj (TopCat.of B)) α β hα hβ) hζ
  rw [h3]
  have hcoch : cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α
        (((relComplex ℤ (TopCat.of B) A).XIsoOfEq h).hom u).1
      = cup ℤ (TopCat.toSSet.obj (TopCat.of B))
          (cup ℤ (TopCat.toSSet.obj (TopCat.of B)) α β) ζ.1 := by
    rw [relComplex_XIsoOfEq_coe h u]
    rw [show u.1 = cup ℤ (TopCat.toSSet.obj (TopCat.of B)) β ζ.1 from rfl]
    rw [cup_cast_right (m := 0) (α := α) (h := h) (h' := congrArg (fun t => 0 + t) h)
      (β := cup ℤ (TopCat.toSSet.obj (TopCat.of B)) β ζ.1)]
    rw [← cupAssoc ℤ (TopCat.toSSet.obj (TopCat.of B)) α β ζ.1]
    exact eqRec_zero_add_cancel (fun t => Cochain ℤ (TopCat.toSSet.obj (TopCat.of B)) t) n _ _ _
  exact relClassOf_congr ℤ (TopCat.of B) A hcoc2 hcoc3 (Subtype.ext hcoch)



theorem localThomMap_cup_zero {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : Work.Thom.PieceCoh Z W n) (x c : Work.Thom.Coh ℤ 0 ↥W) :
    Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 c)) 0 x =
      Work.Thom.localThomMap Z n W τ 0
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c) := by
  simp only [localThomMap_apply]
  rw [Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (pieceProj Z W)) 0 0 x c]
  exact mixedCupC_zero_cast_assoc
    ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z)
    n (Nat.zero_add n) _ _ τ

end

end Work.Thom
