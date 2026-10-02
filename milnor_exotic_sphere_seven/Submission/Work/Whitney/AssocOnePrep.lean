import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.TCMAssocUp
import Submission.Work.Whitney.TCMAssocUpOne
import Submission.Work.Whitney.tcmRelCup_assoc_general
import Submission.Work.Whitney.tcmRelCup_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- The three coordinate sets of the `(p, q+1)`-world, read off by the block projections. -/
def SA (B : Type) [TopologicalSpace B] (p q : ℕ) : Set (tcmX B p (q + 1)) :=
  (TCMAssocUp.q1A B p q) ⁻¹' (Punct B p)

def ST (B : Type) [TopologicalSpace B] (p q : ℕ) : Set (tcmX B p (q + 1)) :=
  (TCMAssocUp.q2A B p q) ⁻¹' (Punct B q)

def SU (B : Type) [TopologicalSpace B] (p q : ℕ) : Set (tcmX B p (q + 1)) :=
  (TCMAssocUp.q3A B p q) ⁻¹' (Punct B 1)

/-- `Punct` is open. -/
theorem isOpen_Punct_aux (B : Type) [TopologicalSpace B] (n : ℕ) : IsOpen (Punct B n) :=
  isOpen_compl_singleton.preimage continuous_snd

theorem isOpen_SA (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (SA B p q) :=
  (isOpen_Punct_aux B p).preimage (TCMAssocUp.q1A B p q).continuous

theorem isOpen_ST (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (ST B p q) :=
  (isOpen_Punct_aux B q).preimage (TCMAssocUp.q2A B p q).continuous

theorem isOpen_SU (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (SU B p q) :=
  (isOpen_Punct_aux B 1).preimage (TCMAssocUp.q3A B p q).continuous

/-- The first block is `tcmA`. -/
theorem SA_eq (B : Type) [TopologicalSpace B] (p q : ℕ) : SA B p q = tcmA B p (q + 1) := by
  ext x
  exact Iff.rfl

/-- The coordinate description of the middle block. -/
theorem mem_ST_eq (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p (q + 1)) :
    (x ∈ ST B p q) = (((tcmSumLin q 1).symm x.2.2).1 ≠ 0) := rfl

/-- The coordinate description of the last block. -/
theorem mem_SU_eq (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p (q + 1)) :
    (x ∈ SU B p q) = (((tcmSumLin q 1).symm x.2.2).2 ≠ 0) := rfl

/-- The second component of the middle block. -/
theorem q2A_snd (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p (q + 1)) :
    ((TCMAssocUp.q2A B p q) x).2 = ((tcmSumLin q 1).symm x.2.2).1 := rfl

/-- The second component of the last block. -/
theorem q3A_snd (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p (q + 1)) :
    ((TCMAssocUp.q3A B p q) x).2 = ((tcmSumLin q 1).symm x.2.2).2 := rfl

/-- The second block splits into the middle and the last coordinate. -/
theorem ST_union_SU (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ST B p q ∪ SU B p q = tcmC B p (q + 1) := by
  apply Set.ext
  intro x
  show ((tcmSumLin q 1).symm x.2.2).1 ≠ 0 ∨ ((tcmSumLin q 1).symm x.2.2).2 ≠ 0
    ↔ x.2.2 ≠ 0
  constructor
  · rintro (h | h) h0
    · exact h (by rw [h0, map_zero, Prod.fst_zero])
    · exact h (by rw [h0, map_zero, Prod.snd_zero])
  · intro h
    by_cases h1 : ((tcmSumLin q 1).symm x.2.2).1 = 0
    · refine Or.inr (fun h2 => h ?_)
      rw [← (tcmSumLin q 1).apply_symm_apply x.2.2,
        show ((tcmSumLin q 1).symm x.2.2)
          = (((tcmSumLin q 1).symm x.2.2).1, ((tcmSumLin q 1).symm x.2.2).2) from rfl,
        h1, h2]
      exact map_zero (tcmSumLin q 1)
    · exact Or.inl h1

/-- The second component of `tcmF`. -/
theorem tcmF_snd (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p q) :
    (tcmF B p q x).2 = tcmSumLin p q x.2 := rfl

/-- The splitting is zero only for the zero vector. -/
theorem tcmSumLin_eq_zero_iff (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : tcmSumLin p q (u, v) = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have h2 : (u, v) = 0 := (tcmSumLin p q).injective (by rw [h, map_zero])
    exact Prod.mk_eq_zero.mp h2
  · rintro ⟨rfl, rfl⟩
    exact map_zero _

/-- The splitting is nonzero iff one of the two components is nonzero. -/
theorem tcmSumLin_ne_zero_iff (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : tcmSumLin p q (u, v) ≠ 0 ↔ u ≠ 0 ∨ v ≠ 0 := by
  rw [ne_eq, tcmSumLin_eq_zero_iff]
  exact not_and_or

/-- **The `psiA`-preimage of the first block** is the union of the first and the middle block. -/
theorem psiA_preimage_SA_union_ST (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (TCMAssocUp.psiA B p q) ⁻¹' (tcmA B (p + q) 1) = SA B p q ∪ ST B p q := by
  apply Set.ext
  intro x
  have h := TCMAssocUp.tcmOuter1_comp_castMap B p q 1 (tcmF B p (q + 1) x)
  rw [TCMAssocUp.castMap_add_assoc_one] at h
  have h4 := congrArg Prod.snd h
  have h2 : (TCMAssocUp.psiA B p q x).2.1
      = tcmSumLin p q (x.2.1, ((tcmSumLin q 1).symm x.2.2).1) := by
    change ((tcmPr1 B (p + q) 1)
      ((Fib.tcmF_inv B (p + q) 1) ((tcmF B p (q + 1)) x))).2
      = tcmSumLin p q (x.2.1, ((tcmSumLin q 1).symm x.2.2).1)
    rw [h4, tcmF_snd, ContinuousLinearEquiv.symm_apply_apply]
  show ((TCMAssocUp.psiA B p q x).2.1 ≠ 0) ↔ (x.2.1 ≠ 0 ∨ ((tcmSumLin q 1).symm x.2.2).1 ≠ 0)
  rw [h2, tcmSumLin_ne_zero_iff]


/-- The middle block is contained in the preimage of the punctured set under `tcmPr2`. -/
theorem ST_mem_punct (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ ST B p q ∪ SU B p q, (tcmPr2 B p (q + 1)) x ∈ Punct B (q + 1) := by
  intro x hx
  have hx' : x.2.2 ≠ 0 := by
    rcases hx with h | h
    · intro h0
      exact h (by rw [q2A_snd B p q x, h0, map_zero, Prod.fst_zero])
    · intro h0
      exact h (by rw [q3A_snd B p q x, h0, map_zero, Prod.snd_zero])
  exact hx'

/-- `q2A` maps the middle block into the punctured set. -/
theorem ST_mem_punct_q2A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ ST B p q, (TCMAssocUp.q2A B p q) x ∈ Punct B q :=
  fun x hx => hx

/-- `q3A` maps the last block into the punctured set. -/
theorem SU_mem_punct_q3A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ SU B p q, (TCMAssocUp.q3A B p q) x ∈ Punct B 1 :=
  fun x hx => hx

/-- The composite `Fib.tcmF_inv B q 1 ∘ tcmPr2 B p (q+1)`. -/
def f2 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p (q + 1), tcmX B q 1) :=
  (Fib.tcmF_inv B q 1).comp (tcmPr2 B p (q + 1))

theorem tcmPr1_preimage (B : Type) [TopologicalSpace B] (q : ℕ) :
    (tcmPr1 B q 1) ⁻¹' (Punct B q) = tcmA B q 1 := by
  apply Set.ext
  intro x
  exact Iff.rfl

theorem tcmPr2_preimage (B : Type) [TopologicalSpace B] (q : ℕ) :
    (tcmPr2 B q 1) ⁻¹' (Punct B 1) = tcmC B q 1 := by
  apply Set.ext
  intro x
  exact Iff.rfl

theorem tcmPr1_preimage_gen (B : Type) [TopologicalSpace B] (m n : ℕ) :
    (tcmPr1 B m n) ⁻¹' (Punct B m) = tcmA B m n := by
  apply Set.ext
  intro x
  exact Iff.rfl

theorem tcmPr2_preimage_gen (B : Type) [TopologicalSpace B] (m n : ℕ) :
    (tcmPr2 B m n) ⁻¹' (Punct B n) = tcmC B m n := by
  apply Set.ext
  intro x
  exact Iff.rfl

theorem ST_eq_f2_preimage (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ST B p q = (f2 B p q) ⁻¹' (tcmA B q 1) := by
  rw [← tcmPr1_preimage B q, Set.preimage_preimage]
  rfl

theorem SU_eq_f2_preimage (B : Type) [TopologicalSpace B] (p q : ℕ) :
    SU B p q = (f2 B p q) ⁻¹' (tcmC B q 1) := by
  rw [← tcmPr2_preimage B q, Set.preimage_preimage]
  rfl

/-- **The inner cup of the left hand side**, expanded along `f2 = tcmF_inv ∘ tcmPr2`. -/
theorem LHS_inner (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    (relCohMap (f2 B p q) ((f2 B p q) ⁻¹' (tcmA B q 1) ∪ (f2 B p q) ⁻¹' (tcmC B q 1))
        (tcmA B q 1 ∪ tcmC B q 1) (fun x hx => hx) ℤ (q + 1)).hom
      (tcmRelCup (tcmA B q 1) (tcmC B q 1) (isOpen_tcmA B q 1) (isOpen_tcmC B q 1) q 1
        ((relCohMap (tcmPr1 B q 1) (tcmA B q 1) (Punct B q) (fun x hx => hx) ℤ q).hom b)
        ((relCohMap (tcmPr2 B q 1) (tcmC B q 1) (Punct B 1) (fun x hx => hx) ℤ 1).hom c))
      = tcmRelCup ((f2 B p q) ⁻¹' (tcmA B q 1)) ((f2 B p q) ⁻¹' (tcmC B q 1))
          ((isOpen_tcmA B q 1).preimage (f2 B p q).continuous)
          ((isOpen_tcmC B q 1).preimage (f2 B p q).continuous) q 1
          ((relCohMap (f2 B p q) ((f2 B p q) ⁻¹' (tcmA B q 1)) (tcmA B q 1) (fun x hx => hx)
            ℤ q).hom
            ((relCohMap (tcmPr1 B q 1) (tcmA B q 1) (Punct B q) (fun x hx => hx) ℤ q).hom b))
          ((relCohMap (f2 B p q) ((f2 B p q) ⁻¹' (tcmC B q 1)) (tcmC B q 1) (fun x hx => hx)
            ℤ 1).hom
            ((relCohMap (tcmPr2 B q 1) (tcmC B q 1) (Punct B 1) (fun x hx => hx) ℤ 1).hom c)) :=
  tcmRelCup_natural ℤ (f2 B p q) (tcmA B q 1) (tcmC B q 1) ((f2 B p q) ⁻¹' (tcmA B q 1))
    ((f2 B p q) ⁻¹' (tcmC B q 1)) (isOpen_tcmA B q 1) (isOpen_tcmC B q 1)
    ((isOpen_tcmA B q 1).preimage (f2 B p q).continuous)
    ((isOpen_tcmC B q 1).preimage (f2 B p q).continuous)
    (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) q 1
    ((relCohMap (tcmPr1 B q 1) (tcmA B q 1) (Punct B q) (fun x hx => hx) ℤ q).hom b)
    ((relCohMap (tcmPr2 B q 1) (tcmC B q 1) (Punct B 1) (fun x hx => hx) ℤ 1).hom c)
/-- The composite `Fib.tcmF_inv B p q ∘ tcmPr1 B (p+q) 1`. -/
def f1 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B (p + q) 1, tcmX B p q) :=
  (Fib.tcmF_inv B p q).comp (tcmPr1 B (p + q) 1)

/-- **The inner cup of the right hand side**, expanded along `f1 = tcmF_inv ∘ tcmPr1`. -/
theorem RHS_inner (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap (f1 B p q) ((f1 B p q) ⁻¹' (tcmA B p q) ∪ (f1 B p q) ⁻¹' (tcmC B p q))
        (tcmA B p q ∪ tcmC B p q) (fun x hx => hx) ℤ (p + q)).hom
      (tcmRelCup (tcmA B p q) (tcmC B p q) (isOpen_tcmA B p q) (isOpen_tcmC B p q) p q
        ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a)
        ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b))
      = tcmRelCup ((f1 B p q) ⁻¹' (tcmA B p q)) ((f1 B p q) ⁻¹' (tcmC B p q))
          ((isOpen_tcmA B p q).preimage (f1 B p q).continuous)
          ((isOpen_tcmC B p q).preimage (f1 B p q).continuous) p q
          ((relCohMap (f1 B p q) ((f1 B p q) ⁻¹' (tcmA B p q)) (tcmA B p q) (fun x hx => hx)
            ℤ p).hom
            ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a))
          ((relCohMap (f1 B p q) ((f1 B p q) ⁻¹' (tcmC B p q)) (tcmC B p q) (fun x hx => hx)
            ℤ q).hom
            ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b)) :=
  tcmRelCup_natural ℤ (f1 B p q) (tcmA B p q) (tcmC B p q) ((f1 B p q) ⁻¹' (tcmA B p q))
    ((f1 B p q) ⁻¹' (tcmC B p q)) (isOpen_tcmA B p q) (isOpen_tcmC B p q)
    ((isOpen_tcmA B p q).preimage (f1 B p q).continuous)
    ((isOpen_tcmC B p q).preimage (f1 B p q).continuous)
    (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) p q
    ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a)
    ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b)

/-- **The outer cup of the right hand side** transported along `psiA`. -/
theorem RHS_outer (B : Type) [TopologicalSpace B] (p q : ℕ)
    (x : RelCoh ℤ (p + q) (B × EuclideanSpace ℝ (Fin (p + q))) (Punct B (p + q)))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    (relCohMap (TCMAssocUp.psiA B p q)
        ((TCMAssocUp.psiA B p q) ⁻¹' (tcmA B (p + q) 1) ∪
          (TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1))
        (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1) (fun x hx => hx) ℤ (p + q + 1)).hom
      (tcmRelCup (tcmA B (p + q) 1) (tcmC B (p + q) 1) (isOpen_tcmA B (p + q) 1)
        (isOpen_tcmC B (p + q) 1) (p + q) 1
        ((relCohMap (tcmPr1 B (p + q) 1) (tcmA B (p + q) 1) (Punct B (p + q))
          (fun x hx => hx) ℤ (p + q)).hom x)
        ((relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1) (Punct B 1) (fun x hx => hx)
          ℤ 1).hom c))
      = tcmRelCup ((TCMAssocUp.psiA B p q) ⁻¹' (tcmA B (p + q) 1))
          ((TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1))
          ((isOpen_tcmA B (p + q) 1).preimage (TCMAssocUp.psiA B p q).continuous)
          ((isOpen_tcmC B (p + q) 1).preimage (TCMAssocUp.psiA B p q).continuous) (p + q) 1
          ((relCohMap (TCMAssocUp.psiA B p q) ((TCMAssocUp.psiA B p q) ⁻¹' (tcmA B (p + q) 1))
            (tcmA B (p + q) 1) (fun x hx => hx) ℤ (p + q)).hom
            ((relCohMap (tcmPr1 B (p + q) 1) (tcmA B (p + q) 1) (Punct B (p + q))
              (fun x hx => hx) ℤ (p + q)).hom x))
          ((relCohMap (TCMAssocUp.psiA B p q) ((TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1))
            (tcmC B (p + q) 1) (fun x hx => hx) ℤ 1).hom
            ((relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1) (Punct B 1) (fun x hx => hx)
              ℤ 1).hom c)) :=
  tcmRelCup_natural ℤ (TCMAssocUp.psiA B p q) (tcmA B (p + q) 1) (tcmC B (p + q) 1)
    ((TCMAssocUp.psiA B p q) ⁻¹' (tcmA B (p + q) 1)) ((TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1))
    (isOpen_tcmA B (p + q) 1) (isOpen_tcmC B (p + q) 1)
    ((isOpen_tcmA B (p + q) 1).preimage (TCMAssocUp.psiA B p q).continuous)
    ((isOpen_tcmC B (p + q) 1).preimage (TCMAssocUp.psiA B p q).continuous)
    (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) (p + q) 1
    ((relCohMap (tcmPr1 B (p + q) 1) (tcmA B (p + q) 1) (Punct B (p + q)) (fun x hx => hx)
      ℤ (p + q)).hom x)
    ((relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1) (Punct B 1) (fun x hx => hx) ℤ 1).hom c)
/-- The first factor of the right hand side, in the `q1B`-form. -/
theorem RHS_factor1 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p)) :
    (relCohMap (f1 B p q) ((f1 B p q) ⁻¹' (tcmA B p q)) (tcmA B p q) (fun x hx => hx)
        ℤ p).hom
      ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun y hy => hy) ℤ p).hom a)
      = (relCohMap (TCMAssocUp.q1B B p q) ((f1 B p q) ⁻¹' (tcmA B p q)) (Punct B p)
          (fun x hx => hx) ℤ p).hom a := by
  rw [relCohMap_compA_apply ((f1 B p q) ⁻¹' (tcmA B p q)) (tcmA B p q) (Punct B p)
    (f1 B p q) (tcmPr1 B p q) (fun x hx => hx) (fun y hy => hy) (fun x hx => hx) ℤ p a]
  rw [relCohMap_congrA ((f1 B p q) ⁻¹' (tcmA B p q)) (Punct B p)
    (show (tcmPr1 B p q).comp (f1 B p q) = TCMAssocUp.q1B B p q from rfl)
    (fun x hx => hx) (fun x hx => hx) ℤ p]

/-- The second factor of the right hand side, in the `q2B`-form. -/
theorem RHS_factor2 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap (f1 B p q) ((f1 B p q) ⁻¹' (tcmC B p q)) (tcmC B p q) (fun x hx => hx)
        ℤ q).hom
      ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun y hy => hy) ℤ q).hom b)
      = (relCohMap (TCMAssocUp.q2B B p q) ((f1 B p q) ⁻¹' (tcmC B p q)) (Punct B q)
          (fun x hx => hx) ℤ q).hom b := by
  rw [relCohMap_compA_apply ((f1 B p q) ⁻¹' (tcmC B p q)) (tcmC B p q) (Punct B q)
    (f1 B p q) (tcmPr2 B p q) (fun x hx => hx) (fun y hy => hy) (fun x hx => hx) ℤ q b]
  rw [relCohMap_congrA ((f1 B p q) ⁻¹' (tcmC B p q)) (Punct B q)
    (show (tcmPr2 B p q).comp (f1 B p q) = TCMAssocUp.q2B B p q from rfl)
    (fun x hx => hx) (fun x hx => hx) ℤ q]

/-- The last factor of the right hand side, in the `q3B`-form. -/
theorem RHS_factor3 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    (relCohMap (TCMAssocUp.psiA B p q)
        ((TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1)) (tcmC B (p + q) 1)
        (fun x hx => hx) ℤ 1).hom
      ((relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1) (Punct B 1) (fun y hy => hy)
        ℤ 1).hom c)
      = (relCohMap ((TCMAssocUp.q3B B p q).comp (TCMAssocUp.psiA B p q))
          ((TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1)) (Punct B 1) (fun x hx => hx)
          ℤ 1).hom c :=
  relCohMap_compA_apply ((TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1))
    (tcmC B (p + q) 1) (Punct B 1) (TCMAssocUp.psiA B p q) (tcmPr2 B (p + q) 1)
    (fun x hx => hx) (fun y hy => hy) (fun x hx => hx) ℤ 1 c
/-- The inner `(p,q)`-cup of the right hand side, decomposed along `f1 ∘ psiA`. -/
theorem RHS_inner_psiA (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q))
        (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q) ∪
          ((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q))
        (tcmA B p q ∪ tcmC B p q) (fun x hx => hx) ℤ (p + q)).hom
      (tcmRelCup (tcmA B p q) (tcmC B p q) (isOpen_tcmA B p q) (isOpen_tcmC B p q) p q
        ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a)
        ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b))
      = tcmRelCup (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q))
          (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q))
          ((isOpen_tcmA B p q).preimage ((f1 B p q).comp (TCMAssocUp.psiA B p q)).continuous)
          ((isOpen_tcmC B p q).preimage ((f1 B p q).comp (TCMAssocUp.psiA B p q)).continuous) p q
          ((relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q))
            (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q)) (tcmA B p q)
            (fun x hx => hx) ℤ p).hom
            ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a))
          ((relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q))
            (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q)) (tcmC B p q)
            (fun x hx => hx) ℤ q).hom
            ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b)) :=
  tcmRelCup_natural ℤ ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmA B p q) (tcmC B p q)
    (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q))
    (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q))
    (isOpen_tcmA B p q) (isOpen_tcmC B p q)
    ((isOpen_tcmA B p q).preimage ((f1 B p q).comp (TCMAssocUp.psiA B p q)).continuous)
    ((isOpen_tcmC B p q).preimage ((f1 B p q).comp (TCMAssocUp.psiA B p q)).continuous)
    (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) p q
    ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a)
    ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b)
/-- The first block projection sends `tcmA` into `Punct`. -/
theorem tcmPr1_mem (B : Type) [TopologicalSpace B] (m n : ℕ) :
    ∀ y ∈ tcmA B m n, (tcmPr1 B m n) y ∈ Punct B m := fun y hy => by
  rw [← tcmPr1_preimage_gen B m n] at hy
  simpa only [Set.mem_preimage] using hy

/-- The second block projection sends `tcmC` into `Punct`. -/
theorem tcmPr2_mem (B : Type) [TopologicalSpace B] (m n : ℕ) :
    ∀ y ∈ tcmC B m n, (tcmPr2 B m n) y ∈ Punct B n := fun y hy => by
  rw [← tcmPr2_preimage_gen B m n] at hy
  simpa only [Set.mem_preimage] using hy

/-- The composite `tcmPr1 ∘ f1 ∘ psiA` is the block projection `q1A`. -/
theorem comp_eq_q1A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (tcmPr1 B p q).comp ((f1 B p q).comp (TCMAssocUp.psiA B p q))
      = TCMAssocUp.q1A B p q := by
  rw [TCMAssocUp.q1A_eq B p q]
  apply ContinuousMap.ext
  intro x
  rfl

/-- `q1A` maps the pullback of `tcmA B p q` into `Punct B p`. -/
theorem q1A_mem (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ ((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q),
      (TCMAssocUp.q1A B p q) x ∈ Punct B p := by
  intro x hx
  rw [← comp_eq_q1A B p q]
  exact tcmPr1_mem B p q _ hx

/-- **The first factor of the right hand side, in the `q1A`-form.** -/
theorem RHS_factor1' (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p)) :
    (relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q))
        (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q)) (tcmA B p q)
        (fun x hx => hx) ℤ p).hom
      ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (tcmPr1_mem B p q) ℤ p).hom a)
      = (relCohMap (TCMAssocUp.q1A B p q)
          (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q)) (Punct B p)
          (q1A_mem B p q) ℤ p).hom a := by
  have hgf : ∀ x ∈ ((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q),
      (tcmPr1 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x) ∈ Punct B p :=
    fun x hx => tcmPr1_mem B p q _ hx
  rw [relCohMap_compA_apply (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q))
    (tcmA B p q) (Punct B p) ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmPr1 B p q)
    (fun x hx => hx) (tcmPr1_mem B p q) hgf ℤ p a]
  rw [relCohMap_congrA (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmA B p q))
    (Punct B p) (comp_eq_q1A B p q) hgf (q1A_mem B p q) ℤ p]
/-- The composite `tcmPr2 ∘ f1 ∘ psiA` is the block projection `q2A`. -/
theorem comp_eq_q2A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (tcmPr2 B p q).comp ((f1 B p q).comp (TCMAssocUp.psiA B p q))
      = TCMAssocUp.q2A B p q := by
  rw [TCMAssocUp.q2A_eq B p q]
  apply ContinuousMap.ext
  intro x
  rfl

/-- `q2A` maps the pullback of `tcmC B p q` into `Punct B q`. -/
theorem q2A_mem (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ ((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q),
      (TCMAssocUp.q2A B p q) x ∈ Punct B q := by
  intro x hx
  rw [← comp_eq_q2A B p q]
  exact tcmPr2_mem B p q _ hx

/-- **The second factor of the right hand side, in the `q2A`-form.** -/
theorem RHS_factor2' (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q))
        (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q)) (tcmC B p q)
        (fun x hx => hx) ℤ q).hom
      ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (tcmPr2_mem B p q) ℤ q).hom b)
      = (relCohMap (TCMAssocUp.q2A B p q)
          (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q)) (Punct B q)
          (q2A_mem B p q) ℤ q).hom b := by
  have hgf : ∀ x ∈ ((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q),
      (tcmPr2 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x) ∈ Punct B q :=
    fun x hx => tcmPr2_mem B p q _ hx
  rw [relCohMap_compA_apply (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q))
    (tcmC B p q) (Punct B q) ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmPr2 B p q)
    (fun x hx => hx) (tcmPr2_mem B p q) hgf ℤ q b]
  rw [relCohMap_congrA (((f1 B p q).comp (TCMAssocUp.psiA B p q)) ⁻¹' (tcmC B p q))
    (Punct B q) (comp_eq_q2A B p q) hgf (q2A_mem B p q) ℤ q]
/-- The middle factor of the left hand side, in the `q2A`-form. -/
theorem LHS_factor1 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap (f2 B p q) ((f2 B p q) ⁻¹' (tcmA B q 1)) (tcmA B q 1) (fun x hx => hx)
        ℤ q).hom
      ((relCohMap (tcmPr1 B q 1) (tcmA B q 1) (Punct B q) (tcmPr1_mem B q 1) ℤ q).hom b)
      = (relCohMap (TCMAssocUp.q2A B p q) ((f2 B p q) ⁻¹' (tcmA B q 1)) (Punct B q)
          (fun x hx => tcmPr1_mem B q 1 _ hx) ℤ q).hom b := by
  have hgf : ∀ x ∈ (f2 B p q) ⁻¹' (tcmA B q 1),
      (tcmPr1 B q 1) ((f2 B p q) x) ∈ Punct B q := fun x hx => tcmPr1_mem B q 1 _ hx
  rw [relCohMap_compA_apply ((f2 B p q) ⁻¹' (tcmA B q 1)) (tcmA B q 1) (Punct B q)
    (f2 B p q) (tcmPr1 B q 1) (fun x hx => hx) (tcmPr1_mem B q 1) hgf ℤ q b]
  rw [relCohMap_congrA ((f2 B p q) ⁻¹' (tcmA B q 1)) (Punct B q)
    (show (tcmPr1 B q 1).comp (f2 B p q) = TCMAssocUp.q2A B p q from rfl)
    hgf (fun x hx => tcmPr1_mem B q 1 _ hx) ℤ q]

/-- The last factor of the left hand side, in the `q3A`-form. -/
theorem LHS_factor2 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    (relCohMap (f2 B p q) ((f2 B p q) ⁻¹' (tcmC B q 1)) (tcmC B q 1) (fun x hx => hx)
        ℤ 1).hom
      ((relCohMap (tcmPr2 B q 1) (tcmC B q 1) (Punct B 1) (tcmPr2_mem B q 1) ℤ 1).hom c)
      = (relCohMap (TCMAssocUp.q3A B p q) ((f2 B p q) ⁻¹' (tcmC B q 1)) (Punct B 1)
          (fun x hx => tcmPr2_mem B q 1 _ hx) ℤ 1).hom c := by
  have hgf : ∀ x ∈ (f2 B p q) ⁻¹' (tcmC B q 1),
      (tcmPr2 B q 1) ((f2 B p q) x) ∈ Punct B 1 := fun x hx => tcmPr2_mem B q 1 _ hx
  rw [relCohMap_compA_apply ((f2 B p q) ⁻¹' (tcmC B q 1)) (tcmC B q 1) (Punct B 1)
    (f2 B p q) (tcmPr2 B q 1) (fun x hx => hx) (tcmPr2_mem B q 1) hgf ℤ 1 c]
  rw [relCohMap_congrA ((f2 B p q) ⁻¹' (tcmC B q 1)) (Punct B 1)
    (show (tcmPr2 B q 1).comp (f2 B p q) = TCMAssocUp.q3A B p q from rfl)
    hgf (fun x hx => tcmPr2_mem B q 1 _ hx) ℤ 1]
/-! ## The three coordinate blocks of the `(p, q+1)`-world

`tcmProd B p (q+1) a (tcmProd B q 1 b c)` unfolds into a cup in `tcmX B p (q+1)` relative to the
sets `tcmA B p (q+1)` and `tcmC B p (q+1)`, whose second factor is the pullback of
`tcmProd B q 1 b c` along `f2 = Fib.tcmF_inv B q 1 ∘ tcmPr2 B p (q+1)`.  Expanding that pullback
(`LHS_inner`) replaces the second block by the two blocks `S2`, `S3` below. -/

/-- The first `p` coordinates. -/
abbrev tcmS1 (B : Type) [TopologicalSpace B] (p q : ℕ) : Set (tcmX B p (q + 1)) :=
  tcmA B p (q + 1)

/-- The middle `q` coordinates. -/
abbrev tcmS2 (B : Type) [TopologicalSpace B] (p q : ℕ) : Set (tcmX B p (q + 1)) :=
  (f2 B p q) ⁻¹' (tcmA B q 1)

/-- The last coordinate. -/
abbrev tcmS3 (B : Type) [TopologicalSpace B] (p q : ℕ) : Set (tcmX B p (q + 1)) :=
  (f2 B p q) ⁻¹' (tcmC B q 1)

theorem isOpen_tcmS1 (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (tcmS1 B p q) :=
  isOpen_tcmA B p (q + 1)

theorem isOpen_tcmS2 (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (tcmS2 B p q) :=
  (isOpen_tcmA B q 1).preimage (f2 B p q).continuous

theorem isOpen_tcmS3 (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (tcmS3 B p q) :=
  (isOpen_tcmC B q 1).preimage (f2 B p q).continuous

/-- The `psiA`-preimage of the last block. -/
theorem psiA_preimage_SU (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1) = SU B p q := by
  show (TCMAssocUp.psiA B p q) ⁻¹' ((tcmPr2 B (p + q) 1) ⁻¹' (Punct B 1)) = SU B p q
  rw [show SU B p q = (TCMAssocUp.q3A B p q) ⁻¹' (Punct B 1) from rfl,
    TCMAssocUp.q3A_eq B p q, Set.preimage_preimage]
  rfl

/-- **The two inner blocks of the `(p, q+1)`-world fill the second block
`tcmC B p (q+1)`.** -/
theorem tcmS2_union_tcmS3 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    tcmS2 B p q ∪ tcmS3 B p q = tcmC B p (q + 1) := by
  rw [tcmS2, tcmS3, ← ST_eq_f2_preimage B p q, ← SU_eq_f2_preimage B p q]
  exact ST_union_SU B p q

/-- **The `psiA`-preimage of the first block** is the union of the first two blocks. -/
theorem psiA_preimage_S1_union_S2 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (TCMAssocUp.psiA B p q) ⁻¹' (tcmA B (p + q) 1) = tcmS1 B p q ∪ tcmS2 B p q := by
  rw [tcmS1, tcmS2, ← SA_eq B p q, ← ST_eq_f2_preimage B p q]
  exact psiA_preimage_SA_union_ST B p q

/-- **The `psiA`-preimage of the second block** is the last block. -/
theorem psiA_preimage_S3 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (TCMAssocUp.psiA B p q) ⁻¹' (tcmC B (p + q) 1) = tcmS3 B p q := by
  rw [tcmS3, ← SU_eq_f2_preimage B p q]
  exact psiA_preimage_SU B p q

/-! ## The classes of the three blocks and the two bracketings -/

/-- The `(q,1)`-inner cup of `tcmProd B q 1 b c` (in the `tcmX B q 1`-world). -/
abbrev tcmZ (B : Type) [TopologicalSpace B] (q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ (q + 1) (tcmX B q 1) (tcmA B q 1 ∪ tcmC B q 1) :=
  tcmRelCup (tcmA B q 1) (tcmC B q 1) (isOpen_tcmA B q 1) (isOpen_tcmC B q 1) q 1
    ((relCohMap (tcmPr1 B q 1) (tcmA B q 1) (Punct B q) (fun x hx => hx) ℤ q).hom b)
    ((relCohMap (tcmPr2 B q 1) (tcmC B q 1) (Punct B 1) (fun x hx => hx) ℤ 1).hom c)

/-- The class of the first `p` coordinates. -/
abbrev tcmAlpha (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p)) :
    RelCoh ℤ p (tcmX B p (q + 1)) (tcmS1 B p q) :=
  (relCohMap (tcmPr1 B p (q + 1)) (tcmS1 B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a

/-- The class of the middle `q` coordinates. -/
abbrev tcmBeta (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    RelCoh ℤ q (tcmX B p (q + 1)) (tcmS2 B p q) :=
  (relCohMap (f2 B p q) (tcmS2 B p q) (tcmA B q 1) (fun x hx => hx) ℤ q).hom
    ((relCohMap (tcmPr1 B q 1) (tcmA B q 1) (Punct B q) (fun x hx => hx) ℤ q).hom b)

/-- The class of the last coordinate. -/
abbrev tcmGamma (B : Type) [TopologicalSpace B] (p q : ℕ)
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ 1 (tcmX B p (q + 1)) (tcmS3 B p q) :=
  (relCohMap (f2 B p q) (tcmS3 B p q) (tcmC B q 1) (fun x hx => hx) ℤ 1).hom
    ((relCohMap (tcmPr2 B q 1) (tcmC B q 1) (Punct B 1) (fun x hx => hx) ℤ 1).hom c)

/-- The second factor of the unfolded left hand side. -/
abbrev tcmF2 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ (q + 1) (tcmX B p (q + 1)) (tcmC B p (q + 1)) :=
  (relCohMap (tcmPr2 B p (q + 1)) (tcmC B p (q + 1)) (Punct B (q + 1)) (fun x hx => hx)
    ℤ (q + 1)).hom (tcmProd B q 1 b c)

/-- The inner cup of the unfolded left hand side. -/
abbrev tcmX0 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ (p + (q + 1)) (tcmX B p (q + 1)) (tcmA B p (q + 1) ∪ tcmC B p (q + 1)) :=
  tcmRelCup (tcmA B p (q + 1)) (tcmC B p (q + 1)) (isOpen_tcmA B p (q + 1))
    (isOpen_tcmC B p (q + 1)) p (q + 1)
    (tcmAlpha B p q a) (tcmF2 B p q b c)

/-- The inner cup of the unfolded right hand side. -/
abbrev tcmY0 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ ((p + q) + 1) (tcmX B (p + q) 1) (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1) :=
  tcmRelCup (tcmA B (p + q) 1) (tcmC B (p + q) 1) (isOpen_tcmA B (p + q) 1)
    (isOpen_tcmC B (p + q) 1) (p + q) 1
    ((relCohMap (tcmPr1 B (p + q) 1) (tcmA B (p + q) 1) (Punct B (p + q)) (fun x hx => hx)
      ℤ (p + q)).hom (tcmProd B p q a b))
    ((relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1) (Punct B 1) (fun x hx => hx)
      ℤ 1).hom c)

/-- The left bracketing of the three block classes in the `(p, q+1)`-world. -/
abbrev tcmBrackL (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ (p + (q + 1)) (tcmX B p (q + 1)) (tcmS1 B p q ∪ (tcmS2 B p q ∪ tcmS3 B p q)) :=
  tcmRelCup (tcmS1 B p q) (tcmS2 B p q ∪ tcmS3 B p q) (isOpen_tcmS1 B p q)
    ((isOpen_tcmS2 B p q).union (isOpen_tcmS3 B p q)) p (q + 1)
    (tcmAlpha B p q a)
    (tcmRelCup (tcmS2 B p q) (tcmS3 B p q) (isOpen_tcmS2 B p q) (isOpen_tcmS3 B p q) q 1
      (tcmBeta B p q b) (tcmGamma B p q c))

/-- The right bracketing of the three block classes in the `(p, q+1)`-world. -/
abbrev tcmBrackR (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ ((p + q) + 1) (tcmX B p (q + 1)) ((tcmS1 B p q ∪ tcmS2 B p q) ∪ tcmS3 B p q) :=
  tcmRelCup (tcmS1 B p q ∪ tcmS2 B p q) (tcmS3 B p q)
    ((isOpen_tcmS1 B p q).union (isOpen_tcmS2 B p q)) (isOpen_tcmS3 B p q) (p + q) 1
    (tcmRelCup (tcmS1 B p q) (tcmS2 B p q) (isOpen_tcmS1 B p q) (isOpen_tcmS2 B p q) p q
      (tcmAlpha B p q a) (tcmBeta B p q b))
    (tcmGamma B p q c)

/-! ## Unfoldings -/

/-- The left hand side of the associativity, unfolded into `tcmX B p (q+1)`. -/
theorem tcmProd_assoc_one_LHS_unfold (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    tcmProd B p (q + 1) a (tcmProd B q 1 b c)
      = (relCohMap (Fib.tcmF_inv B p (q + 1)) (Punct B (p + (q + 1)))
          (tcmA B p (q + 1) ∪ tcmC B p (q + 1)) (tcmF_inv_mem_punct_union B p (q + 1))
          ℤ (p + (q + 1))).hom (tcmX0 B p q a b c) := rfl

/-- The right hand side of the associativity, unfolded into `tcmX B (p+q) 1`. -/
theorem tcmProd_assoc_one_RHS_unfold (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    tcmProd B (p + q) 1 (tcmProd B p q a b) c
      = (relCohMap (Fib.tcmF_inv B (p + q) 1) (Punct B (p + (q + 1)))
          (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1) (tcmF_inv_mem_punct_union B (p + q) 1)
          ℤ ((p + q) + 1)).hom (tcmY0 B p q a b c) := rfl

/-! ## Transport of `tcmRelCup` along an equality of the sets -/

/-- Transport of a relative–relative cup along an equality of the *second* set. -/
theorem tcmRelCup_cast_right {X : Type} [TopologicalSpace X] {A B B' : Set X} (hA : IsOpen A)
    (hB : IsOpen B) (hB' : IsOpen B') (h : B' = B) (m n : ℕ)
    (u : RelCoh ℤ m X A) (v : RelCoh ℤ n X B') :
    (congrArg (fun D => A ∪ D) h) ▸ (tcmRelCup A B' hA hB' m n u v)
      = tcmRelCup A B hA hB m n u (h ▸ v) := by
  cases h
  rw [Subsingleton.elim hB' hB]

/-- Transport of a relative–relative cup along an equality of the *first* set. -/
theorem tcmRelCup_cast_left {X : Type} [TopologicalSpace X] {A A' B : Set X} (hA : IsOpen A)
    (hA' : IsOpen A') (hB : IsOpen B) (h : A' = A) (m n : ℕ)
    (u : RelCoh ℤ m X A') (v : RelCoh ℤ n X B) :
    (congrArg (fun D => D ∪ B) h) ▸ (tcmRelCup A' B hA' hB m n u v)
      = tcmRelCup A B hA hB m n (h ▸ u) v := by
  cases h
  rw [Subsingleton.elim hA' hA]


theorem tcmF2_eq (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    tcmF2 B p q b c
      = (tcmS2_union_tcmS3 B p q) ▸
          (tcmRelCup (tcmS2 B p q) (tcmS3 B p q) (isOpen_tcmS2 B p q) (isOpen_tcmS3 B p q)
            q 1 (tcmBeta B p q b) (tcmGamma B p q c)) := by
  rw [show tcmF2 B p q b c = (relCohMap (tcmPr2 B p (q + 1)) (tcmC B p (q + 1))
      (Punct B (q + 1)) (fun x hx => hx) ℤ (q + 1)).hom (tcmProd B q 1 b c) from rfl]
  rw [show tcmProd B q 1 b c = (relCohMap (Fib.tcmF_inv B q 1) (Punct B (q + 1))
      (tcmA B q 1 ∪ tcmC B q 1) (tcmF_inv_mem_punct_union B q 1) ℤ (q + 1)).hom
      (tcmZ B q b c) from rfl]
  rw [relCohMap_compA_apply (tcmC B p (q + 1)) (Punct B (q + 1)) (tcmA B q 1 ∪ tcmC B q 1)
    (tcmPr2 B p (q + 1)) (Fib.tcmF_inv B q 1) (fun x hx => hx) (tcmF_inv_mem_punct_union B q 1)
    (fun x hx => tcmF_inv_mem_punct_union B q 1 (tcmPr2 B p (q + 1) x) hx) ℤ (q + 1)
    (tcmZ B q b c)]
  rw [relCohMap_congrA (tcmC B p (q + 1)) (tcmA B q 1 ∪ tcmC B q 1)
    (show (Fib.tcmF_inv B q 1).comp (tcmPr2 B p (q + 1)) = f2 B p q from rfl)
    (fun x hx => tcmF_inv_mem_punct_union B q 1 (tcmPr2 B p (q + 1) x) hx)
    (fun x hx => tcmF_inv_mem_punct_union B q 1 (tcmPr2 B p (q + 1) x) hx) ℤ (q + 1)]
  rw [← TCMAssocUp.relCohMap_set_cast (h := tcmS2_union_tcmS3 B p q) (f := f2 B p q)
    (B := tcmA B q 1 ∪ tcmC B q 1)
    (hB := fun x hx => tcmF_inv_mem_punct_union B q 1 (tcmPr2 B p (q + 1) x) hx)
    (hB' := fun x hx => by rcases hx with h | h; exacts [Or.inl h, Or.inr h])
    (n := q + 1) (x := tcmZ B q b c)]
  rw [LHS_inner B p q b c]

/-! ## The remaining endgame: membership, naturality instances, assembly -/

/-- The `(p,q)`-inner cup of `tcmProd B p q a b`. -/
abbrev tcmZpq (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    RelCoh ℤ (p + q) (tcmX B p q) (tcmA B p q ∪ tcmC B p q) :=
  tcmRelCup (tcmA B p q) (tcmC B p q) (isOpen_tcmA B p q) (isOpen_tcmC B p q) p q
    ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a)
    ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom b)

/-- The `tcmA B (p+q) 1`-block class of the right hand side. -/
abbrev tcmF1Y (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    RelCoh ℤ (p + q) (tcmX B (p + q) 1) (tcmA B (p + q) 1) :=
  (relCohMap (tcmPr1 B (p + q) 1) (tcmA B (p + q) 1) (Punct B (p + q)) (fun x hx => hx)
    ℤ (p + q)).hom (tcmProd B p q a b)

/-- The `tcmC B (p+q) 1`-block class of the right hand side. -/
abbrev tcmF2Y (B : Type) [TopologicalSpace B] (p q : ℕ)
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ 1 (tcmX B (p + q) 1) (tcmC B (p + q) 1) :=
  (relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1) (Punct B 1) (fun x hx => hx)
    ℤ 1).hom c

/-! ### Membership lemmas -/

theorem mem_E1 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmS1 B p q ∪ tcmS2 B p q, (TCMAssocUp.psiA B p q) x ∈ tcmA B (p + q) 1 := by
  intro x hx
  rw [← psiA_preimage_S1_union_S2 B p q] at hx
  rwa [Set.mem_preimage] at hx

theorem mem_E2 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmS3 B p q, (TCMAssocUp.psiA B p q) x ∈ tcmC B (p + q) 1 := by
  intro x hx
  rw [← psiA_preimage_S3 B p q] at hx
  rwa [Set.mem_preimage] at hx

theorem mem_E12 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ (tcmS1 B p q ∪ tcmS2 B p q) ∪ tcmS3 B p q,
      (TCMAssocUp.psiA B p q) x ∈ tcmA B (p + q) 1 ∪ tcmC B (p + q) 1 := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (mem_E1 B p q x hx)
  · exact Or.inr (mem_E2 B p q x hx)

theorem mem_D1 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmS1 B p q, ((f1 B p q).comp (TCMAssocUp.psiA B p q)) x ∈ tcmA B p q := by
  intro x hx
  have h : (TCMAssocUp.q1A B p q) x ∈ Punct B p := hx
  rw [← tcmPr1_preimage_gen B p q]
  show (tcmPr1 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x) ∈ Punct B p
  rw [show (tcmPr1 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x)
      = (TCMAssocUp.q1A B p q) x from by
    rw [← ContinuousMap.comp_apply, comp_eq_q1A B p q]]
  exact h

theorem mem_D2 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmS2 B p q, ((f1 B p q).comp (TCMAssocUp.psiA B p q)) x ∈ tcmC B p q := by
  intro x hx
  have h1 : (tcmPr1 B q 1) ((f2 B p q) x) ∈ Punct B q := tcmPr1_mem B q 1 _ hx
  have h2 : (TCMAssocUp.q2A B p q) x ∈ Punct B q := by
    show ((tcmPr1 B q 1).comp (f2 B p q)) x ∈ Punct B q
    exact h1
  rw [← tcmPr2_preimage_gen B p q]
  show (tcmPr2 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x) ∈ Punct B q
  rw [show (tcmPr2 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x)
      = (TCMAssocUp.q2A B p q) x from by
    rw [← ContinuousMap.comp_apply, comp_eq_q2A B p q]]
  exact h2

theorem mem_D12 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmS1 B p q ∪ tcmS2 B p q,
      ((f1 B p q).comp (TCMAssocUp.psiA B p q)) x ∈ tcmA B p q ∪ tcmC B p q := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (mem_D1 B p q x hx)
  · exact Or.inr (mem_D2 B p q x hx)

/-- The composite `tcmPr2 B (p+q) 1 ∘ psiA` is the block projection `q3A`. -/
theorem comp_eq_q3A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (tcmPr2 B (p + q) 1).comp (TCMAssocUp.psiA B p q) = TCMAssocUp.q3A B p q :=
  (TCMAssocUp.q3A_eq B p q).symm

/-! ### The two factor transfers with the source sets `tcmS1`, `tcmS2` -/

theorem RHS_factor1_S1 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p)) :
    (relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmS1 B p q) (tcmA B p q)
        (mem_D1 B p q) ℤ p).hom
      ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (tcmPr1_mem B p q) ℤ p).hom a)
      = (relCohMap (TCMAssocUp.q1A B p q) (tcmS1 B p q) (Punct B p)
          (fun x hx => hx) ℤ p).hom a := by
  have hgf : ∀ x ∈ tcmS1 B p q,
      (tcmPr1 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x) ∈ Punct B p :=
    fun x hx => tcmPr1_mem B p q _ (mem_D1 B p q x hx)
  rw [relCohMap_compA_apply (tcmS1 B p q) (tcmA B p q) (Punct B p)
    ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmPr1 B p q) (mem_D1 B p q)
    (tcmPr1_mem B p q) hgf ℤ p a]
  rw [relCohMap_congrA (tcmS1 B p q) (Punct B p) (comp_eq_q1A B p q) hgf
    (fun x hx => hx) ℤ p]

theorem RHS_factor2_S2 (B : Type) [TopologicalSpace B] (p q : ℕ)
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmS2 B p q) (tcmC B p q)
        (mem_D2 B p q) ℤ q).hom
      ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (tcmPr2_mem B p q) ℤ q).hom b)
      = (relCohMap (TCMAssocUp.q2A B p q) (tcmS2 B p q) (Punct B q)
          (fun x hx => tcmPr1_mem B q 1 _ hx) ℤ q).hom b := by
  have hgf : ∀ x ∈ tcmS2 B p q,
      (tcmPr2 B p q) (((f1 B p q).comp (TCMAssocUp.psiA B p q)) x) ∈ Punct B q :=
    fun x hx => tcmPr2_mem B p q _ (mem_D2 B p q x hx)
  rw [relCohMap_compA_apply (tcmS2 B p q) (tcmC B p q) (Punct B q)
    ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmPr2 B p q) (mem_D2 B p q)
    (tcmPr2_mem B p q) hgf ℤ q b]
  rw [relCohMap_congrA (tcmS2 B p q) (Punct B q) (comp_eq_q2A B p q) hgf
    (fun x hx => tcmPr1_mem B q 1 _ hx) ℤ q]

/-! ### The expansions of the two factors of the outer cup -/

theorem factor1_expand (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap (TCMAssocUp.psiA B p q) (tcmS1 B p q ∪ tcmS2 B p q) (tcmA B (p + q) 1)
        (mem_E1 B p q) ℤ (p + q)).hom (tcmF1Y B p q a b)
      = tcmRelCup (tcmS1 B p q) (tcmS2 B p q) (isOpen_tcmS1 B p q) (isOpen_tcmS2 B p q)
          p q (tcmAlpha B p q a) (tcmBeta B p q b) := by
  rw [show tcmF1Y B p q a b = (relCohMap (tcmPr1 B (p + q) 1) (tcmA B (p + q) 1)
      (Punct B (p + q)) (fun x hx => hx) ℤ (p + q)).hom (tcmProd B p q a b) from rfl]
  rw [relCohMap_compA_apply (tcmS1 B p q ∪ tcmS2 B p q) (tcmA B (p + q) 1)
    (Punct B (p + q)) (TCMAssocUp.psiA B p q) (tcmPr1 B (p + q) 1) (mem_E1 B p q)
    (fun x hx => hx) (mem_E1 B p q) ℤ (p + q) (tcmProd B p q a b)]
  rw [show tcmProd B p q a b = (relCohMap (Fib.tcmF_inv B p q) (Punct B (p + q))
      (tcmA B p q ∪ tcmC B p q) (tcmF_inv_mem_punct_union B p q) ℤ (p + q)).hom
      (tcmZpq B p q a b) from rfl]
  rw [relCohMap_compA_apply (tcmS1 B p q ∪ tcmS2 B p q) (Punct B (p + q))
    (tcmA B p q ∪ tcmC B p q) ((tcmPr1 B (p + q) 1).comp (TCMAssocUp.psiA B p q))
    (Fib.tcmF_inv B p q) (mem_E1 B p q) (tcmF_inv_mem_punct_union B p q)
    (fun x hx => tcmF_inv_mem_punct_union B p q
      ((tcmPr1 B (p + q) 1) (TCMAssocUp.psiA B p q x)) (mem_E1 B p q x hx))
    ℤ (p + q) (tcmZpq B p q a b)]
  rw [relCohMap_congrA (tcmS1 B p q ∪ tcmS2 B p q) (tcmA B p q ∪ tcmC B p q)
    (show (Fib.tcmF_inv B p q).comp ((tcmPr1 B (p + q) 1).comp (TCMAssocUp.psiA B p q))
      = ((f1 B p q).comp (TCMAssocUp.psiA B p q)) from rfl)
    (fun x hx => tcmF_inv_mem_punct_union B p q
      ((tcmPr1 B (p + q) 1) (TCMAssocUp.psiA B p q x)) (mem_E1 B p q x hx))
    (mem_D12 B p q) ℤ (p + q)]
  rw [tcmRelCup_natural ℤ ((f1 B p q).comp (TCMAssocUp.psiA B p q)) (tcmA B p q) (tcmC B p q)
    (tcmS1 B p q) (tcmS2 B p q) (isOpen_tcmA B p q) (isOpen_tcmC B p q)
    (isOpen_tcmS1 B p q) (isOpen_tcmS2 B p q) (mem_D1 B p q) (mem_D2 B p q) (mem_D12 B p q)
    p q _ _]
  rw [RHS_factor1_S1 B p q a, RHS_factor2_S2 B p q b]
  rw [show (relCohMap (TCMAssocUp.q1A B p q) (tcmS1 B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a
      = tcmAlpha B p q a from rfl]
  rw [← LHS_factor1 B p q b]

theorem factor2_expand (B : Type) [TopologicalSpace B] (p q : ℕ)
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    (relCohMap (TCMAssocUp.psiA B p q) (tcmS3 B p q) (tcmC B (p + q) 1)
        (mem_E2 B p q) ℤ 1).hom (tcmF2Y B p q c)
      = tcmGamma B p q c := by
  rw [show tcmF2Y B p q c = (relCohMap (tcmPr2 B (p + q) 1) (tcmC B (p + q) 1)
      (Punct B 1) (fun x hx => hx) ℤ 1).hom c from rfl]
  rw [relCohMap_compA_apply (tcmS3 B p q) (tcmC B (p + q) 1) (Punct B 1)
    (TCMAssocUp.psiA B p q) (tcmPr2 B (p + q) 1) (mem_E2 B p q) (fun x hx => hx)
    (mem_E2 B p q) ℤ 1 c]
  rw [relCohMap_congrA (tcmS3 B p q) (Punct B 1) (comp_eq_q3A B p q)
    (mem_E2 B p q) (fun x hx => tcmPr2_mem B q 1 (f2 B p q x) hx) ℤ 1]
  rw [← LHS_factor2 B p q c]


/-! ### The two assemblies -/

/-- The source-set comparison of the outer pullback, transported. -/
theorem tcmS_union (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (tcmS1 B p q ∪ tcmS2 B p q) ∪ tcmS3 B p q = tcmS1 B p q ∪ tcmC B p (q + 1) :=
  (Set.union_assoc (tcmS1 B p q) (tcmS2 B p q) (tcmS3 B p q)).trans
    (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))

theorem mem_SAB (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmS1 B p q ∪ tcmC B p (q + 1),
      (TCMAssocUp.psiA B p q) x ∈ tcmA B (p + q) 1 ∪ tcmC B (p + q) 1 := by
  intro x hx
  rw [show tcmS1 B p q ∪ tcmC B p (q + 1)
    = (tcmS1 B p q ∪ tcmS2 B p q) ∪ tcmS3 B p q from (tcmS_union B p q).symm] at hx
  rcases hx with hx | hx
  · exact Or.inl (mem_E1 B p q x hx)
  · exact Or.inr (mem_E2 B p q x hx)

/-- The pullback of `tcmY0` along `psiA`, over the source set of `tcmX0`. -/
abbrev tcmPsiY (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    RelCoh ℤ (p + (q + 1)) (tcmX B p (q + 1)) (tcmS1 B p q ∪ tcmC B p (q + 1)) :=
  (relCohMap (TCMAssocUp.psiA B p q) (tcmS1 B p q ∪ tcmC B p (q + 1))
    (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1) (mem_SAB B p q)
    ℤ ((p + q) + 1)).hom (tcmY0 B p q a b c)

/-- **The left hand side assembly**: `tcmX0` is the left bracketing, transported along
`tcmS2 ∪ tcmS3 = tcmC B p (q+1)`. -/
theorem tcmX0_eq_brackL (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    tcmX0 B p q a b c
      = (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))
          ▸ tcmBrackL B p q a b c := by
  rw [show tcmX0 B p q a b c = tcmRelCup (tcmA B p (q + 1)) (tcmC B p (q + 1))
      (isOpen_tcmA B p (q + 1)) (isOpen_tcmC B p (q + 1)) p (q + 1)
      (tcmAlpha B p q a) (tcmF2 B p q b c) from rfl]
  rw [tcmF2_eq B p q b c]
  rw [← tcmRelCup_cast_right (A := tcmS1 B p q) (B := tcmC B p (q + 1))
    (B' := tcmS2 B p q ∪ tcmS3 B p q) (isOpen_tcmA B p (q + 1)) (isOpen_tcmC B p (q + 1))
    ((isOpen_tcmS2 B p q).union (isOpen_tcmS3 B p q)) (tcmS2_union_tcmS3 B p q) p (q + 1)
    (tcmAlpha B p q a)
    (tcmRelCup (tcmS2 B p q) (tcmS3 B p q) (isOpen_tcmS2 B p q) (isOpen_tcmS3 B p q) q 1
      (tcmBeta B p q b) (tcmGamma B p q c))]

/-- **The right hand side assembly**: the `psiA`-pullback of `tcmY0` is the right bracketing,
transported along `(tcmS1 ∪ tcmS2) ∪ tcmS3 = tcmS1 ∪ tcmC B p (q+1)`. -/
theorem tcmPsiY_eq_brackR (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    tcmPsiY B p q a b c = (tcmS_union B p q) ▸ tcmBrackR B p q a b c := by
  rw [show tcmPsiY B p q a b c = (relCohMap (TCMAssocUp.psiA B p q)
      (tcmS1 B p q ∪ tcmC B p (q + 1)) (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1)
      (mem_SAB B p q) ℤ ((p + q) + 1)).hom (tcmY0 B p q a b c) from rfl]
  rw [← TCMAssocUp.relCohMap_set_cast (h := tcmS_union B p q) (f := TCMAssocUp.psiA B p q)
    (B := tcmA B (p + q) 1 ∪ tcmC B (p + q) 1)
    (hB := mem_SAB B p q) (hB' := mem_E12 B p q) (n := (p + q) + 1)
    (x := tcmY0 B p q a b c)]
  rw [show (tcmY0 B p q a b c : RelCoh ℤ ((p + q) + 1) (tcmX B (p + q) 1)
      (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1))
      = tcmRelCup (tcmA B (p + q) 1) (tcmC B (p + q) 1) (isOpen_tcmA B (p + q) 1)
        (isOpen_tcmC B (p + q) 1) (p + q) 1 (tcmF1Y B p q a b) (tcmF2Y B p q c) from rfl]
  rw [tcmRelCup_natural ℤ (TCMAssocUp.psiA B p q) (tcmA B (p + q) 1) (tcmC B (p + q) 1)
    (tcmS1 B p q ∪ tcmS2 B p q) (tcmS3 B p q) (isOpen_tcmA B (p + q) 1)
    (isOpen_tcmC B (p + q) 1) ((isOpen_tcmS1 B p q).union (isOpen_tcmS2 B p q))
    (isOpen_tcmS3 B p q) (mem_E1 B p q) (mem_E2 B p q) (mem_E12 B p q) (p + q) 1
    (tcmF1Y B p q a b) (tcmF2Y B p q c)]
  rw [factor1_expand B p q a b, factor2_expand B p q c]

/-- The composite `psiA ∘ Fib.tcmF_inv B p (q+1)` is `Fib.tcmF_inv B (p+q) 1`. -/
theorem psiA_comp_tcmF_inv (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (TCMAssocUp.psiA B p q).comp (Fib.tcmF_inv B p (q + 1)) = Fib.tcmF_inv B (p + q) 1 := by
  apply ContinuousMap.ext
  intro y
  show Fib.tcmF_inv B (p + q) 1 (tcmF B p (q + 1) (Fib.tcmF_inv B p (q + 1) y))
    = Fib.tcmF_inv B (p + q) 1 y
  rw [Fib.tcmF_tcmF_inv]

/-- The degree cast `Nat.add_assoc p q 1` is trivial. -/
theorem addAssoc_one_cast (B : Type) [TopologicalSpace B] (p q : ℕ)
    (S : Set (tcmX B p (q + 1))) (z : RelCoh ℤ ((p + q) + 1) (tcmX B p (q + 1)) S) :
    ((Nat.add_assoc p q 1) ▸ z : RelCoh ℤ (p + (q + 1)) (tcmX B p (q + 1)) S) = z := rfl

/-- The associativity of the three block classes. -/
theorem tcmBrack_assoc (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    (Set.union_assoc (tcmS1 B p q) (tcmS2 B p q) (tcmS3 B p q)) ▸ tcmBrackR B p q a b c
      = tcmBrackL B p q a b c := by
  have h := tcmRelCup_assoc_general (tcmS1 B p q) (tcmS2 B p q) (tcmS3 B p q)
    (isOpen_tcmS1 B p q) (isOpen_tcmS2 B p q) (isOpen_tcmS3 B p q) p q 1
    (tcmAlpha B p q a) (tcmBeta B p q b) (tcmGamma B p q c)
  rw [addAssoc_one_cast B p q] at h
  exact h

/-- Transport of a cast of the index along a composition of equalities. -/
lemma eqRec_trans_gen' {α : Sort*} {P : α → Sort*} {a b c : α} (h1 : a = b) (h2 : b = c)
    (x : P a) : ((h1.trans h2) ▸ x : P c) = h2 ▸ (h1 ▸ x) := by
  cases h1; cases h2; rfl

/-- **The key identity** `tcmX0 = psiA^* tcmY0`. -/
theorem tcmX0_eq_psiY (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p))
    (b : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q))
    (c : RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Punct B 1)) :
    tcmX0 B p q a b c = tcmPsiY B p q a b c := by
  have h1 := tcmX0_eq_brackL B p q a b c
  have h2 := tcmPsiY_eq_brackR B p q a b c
  have h3 := tcmBrack_assoc B p q a b c
  have h4 : (tcmS_union B p q) ▸ tcmBrackR B p q a b c
      = (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))
          ▸ tcmBrackL B p q a b c := by
    calc (tcmS_union B p q) ▸ tcmBrackR B p q a b c
        = ((Set.union_assoc (tcmS1 B p q) (tcmS2 B p q) (tcmS3 B p q)).trans
            (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q)))
            ▸ tcmBrackR B p q a b c :=
          congrArg (fun (e : (tcmS1 B p q ∪ tcmS2 B p q) ∪ tcmS3 B p q
              = tcmS1 B p q ∪ tcmC B p (q + 1)) => e ▸ tcmBrackR B p q a b c)
            (Subsingleton.elim _ _)
      _ = (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))
            ▸ ((Set.union_assoc (tcmS1 B p q) (tcmS2 B p q) (tcmS3 B p q))
                ▸ tcmBrackR B p q a b c) :=
          eqRec_trans_gen' (P := fun S => RelCoh ℤ ((p + q) + 1) (tcmX B p (q + 1)) S)
            (Set.union_assoc (tcmS1 B p q) (tcmS2 B p q) (tcmS3 B p q))
            (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))
            (tcmBrackR B p q a b c)
      _ = (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))
            ▸ tcmBrackL B p q a b c :=
          congrArg (fun z => (congrArg (fun D => tcmS1 B p q ∪ D)
            (tcmS2_union_tcmS3 B p q)) ▸ z) h3
  calc tcmX0 B p q a b c
      = (congrArg (fun D => tcmS1 B p q ∪ D) (tcmS2_union_tcmS3 B p q))
          ▸ tcmBrackL B p q a b c := h1
    _ = (tcmS_union B p q) ▸ tcmBrackR B p q a b c := h4.symm
    _ = tcmPsiY B p q a b c := h2.symm

end

end Work.Whitney
