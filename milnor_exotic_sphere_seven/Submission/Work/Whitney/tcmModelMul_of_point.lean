import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmRelCup_natural
import Submission.Work.Whitney.Mpun_eq_of_fibrewise

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# `Work.Whitney.tcmModelMul` from its point case

The model product formula `Work.Whitney.tcmModelMul` over an arbitrary base `B` is *detected* by its
restrictions to the fibres `↥{b} × (ℝ^p × ℝ^q)`: the model class of the trivial bundle is a model
class (`Work.Thom.Mpun_isModel`), so a relative class of
`H^{p+q}(B × (ℝ^p × ℝ^q), A ∪ C)` is determined by its restrictions to the fibres
(`Work.Whitney.Mpun_eq_of_fibrewise`).  On each fibre the formula is the point case over the
one-point base `↥{b}`, so `Work.Whitney.tcmModelMul_point` implies `Work.Whitney.tcmModelMul`.

The reduction is `Fib.tcmModel_detect` (a class agreeing with another one on every fibre is equal,
proved through the inverse `Fib.tcmF_inv` of the coordinate identification `tcmF` and
`Mpun_eq_of_fibrewise`), and the two computations of the fibre restrictions are
`Fib.fibre_pullback_pr1`, `Fib.fibre_pullback_pr2` (the pulled-back model classes) and
`Fib.fibre_pullback_tcmF` (the pulled-back model class of the sum).
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

namespace Fib

/-! ## The inverse of the coordinate identification and the pair condition -/

/-- The inverse of the coordinate identification `tcmF : B × (ℝ^p × ℝ^q) → B × ℝ^{p+q}`, as a
continuous map. -/
def tcmF_inv (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(B × EuclideanSpace ℝ (Fin (p + q)), tcmX B p q) :=
  ⟨fun y => (y.1, (tcmSumLin p q).symm y.2),
    continuous_fst.prodMk ((tcmSumLin p q).symm.continuous.comp continuous_snd)⟩

@[simp] theorem tcmF_inv_apply (B : Type) [TopologicalSpace B] (p q : ℕ)
    (y : B × EuclideanSpace ℝ (Fin (p + q))) :
    tcmF_inv B p q y = (y.1, (tcmSumLin p q).symm y.2) := rfl

theorem tcmF_inv_tcmF (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p q) :
    tcmF_inv B p q (tcmF B p q x) = x := by
  apply Prod.ext
  · rfl
  · exact (tcmSumLin p q).symm_apply_apply x.2

theorem tcmF_tcmF_inv (B : Type) [TopologicalSpace B] (p q : ℕ)
    (y : B × EuclideanSpace ℝ (Fin (p + q))) :
    tcmF B p q (tcmF_inv B p q y) = y := by
  apply Prod.ext
  · rfl
  · exact (tcmSumLin p q).apply_symm_apply y.2

/-- The pair condition of the coordinate identification: `tcmF` carries `A ∪ C` onto the punctured
part. -/
theorem tcmF_punct_iff (B : Type) [TopologicalSpace B] (p q : ℕ) (x : tcmX B p q) :
    x ∈ tcmA B p q ∪ tcmC B p q ↔ tcmF B p q x ∈ Punct B (p + q) := by
  constructor
  · rintro (h | h)
    · intro h0
      exact h (congrArg (@Prod.fst _ _)
        ((tcmSumLin p q).injective (h0.trans (map_zero (tcmSumLin p q)).symm)))
    · intro h0
      exact h (congrArg (@Prod.snd _ _)
        ((tcmSumLin p q).injective (h0.trans (map_zero (tcmSumLin p q)).symm)))
  · intro hx
    by_cases h : x.2.1 = 0
    · right
      intro h2
      have hz : x.2 = 0 := Prod.ext h h2
      exact hx (show tcmSumLin p q x.2 = 0 from by rw [hz]; exact map_zero (tcmSumLin p q))
    · exact Or.inl h

/-- The preimage form of the pair condition. -/
theorem tcmF_preimage_punct' (B : Type) [TopologicalSpace B] (p q : ℕ) :
    (tcmF B p q) ⁻¹' Punct B (p + q) = tcmA B p q ∪ tcmC B p q :=
  Set.ext (fun x => (tcmF_punct_iff B p q x).symm)

/-! ## The fibre inclusion and its interaction with the structure maps -/

/-- The inclusion of the fibre of the base over a point `b` into the total space. -/
def tcmFibIncl (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    C(tcmX ↥({b} : Set B) p q, tcmX B p q) :=
  ⟨fun x => (((x.1 : ↥({b} : Set B)) : B), x.2),
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd⟩

@[simp] theorem tcmFibIncl_apply (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B)
    (x : tcmX ↥({b} : Set B) p q) : tcmFibIncl B p q b x = ((x.1 : B), x.2) := rfl

theorem tcmFibIncl_mem (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    ∀ x ∈ tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q,
      tcmFibIncl B p q b x ∈ tcmA B p q ∪ tcmC B p q := fun _ hx => hx

theorem tcmFibIncl_memA (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    ∀ x ∈ tcmA ↥({b} : Set B) p q, tcmFibIncl B p q b x ∈ tcmA B p q := fun _ hx => hx

theorem tcmFibIncl_memC (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    ∀ x ∈ tcmC ↥({b} : Set B) p q, tcmFibIncl B p q b x ∈ tcmC B p q := fun _ hx => hx

theorem tcmF_comp_tcmFibIncl (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    (tcmF B p q).comp (tcmFibIncl B p q b)
      = (baseIncl B ({b} : Set B) (p + q)).comp (tcmF ↥({b} : Set B) p q) :=
  ContinuousMap.ext (fun _ => rfl)

theorem tcmF_inv_comp_baseIncl (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    (tcmF_inv B p q).comp (baseIncl B ({b} : Set B) (p + q))
      = (tcmFibIncl B p q b).comp (tcmF_inv ↥({b} : Set B) p q) :=
  ContinuousMap.ext (fun _ => rfl)

theorem tcmPr1_comp_tcmFibIncl (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    (tcmPr1 B p q).comp (tcmFibIncl B p q b)
      = (baseIncl B ({b} : Set B) p).comp (tcmPr1 ↥({b} : Set B) p q) :=
  ContinuousMap.ext (fun _ => rfl)

theorem tcmPr2_comp_tcmFibIncl (B : Type) [TopologicalSpace B] (p q : ℕ) (b : B) :
    (tcmPr2 B p q).comp (tcmFibIncl B p q b)
      = (baseIncl B ({b} : Set B) q).comp (tcmPr2 ↥({b} : Set B) p q) :=
  ContinuousMap.ext (fun _ => rfl)

/-! ## The fibre restriction of the pulled-back model classes -/

/-- **The fibre restriction of the first pulled-back model class**: on the fibre over `b` it is the
first argument of the point case over `↥{b}`. -/
theorem fibre_pullback_pr1 {B : Type} [TopologicalSpace B] (p q : ℕ) (b : B)
    (a : RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Punct B p)) :
    (relCohMap (tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q) (tcmA B p q)
        (tcmFibIncl_memA B p q b) ℤ p).hom
      ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom a)
    = (relCohMap (tcmPr1 ↥({b} : Set B) p q) (tcmA ↥({b} : Set B) p q)
        (Punct ↥({b} : Set B) p) (fun x hx => hx) ℤ p).hom
      ((relCohMap (baseIncl B ({b} : Set B) p) (Punct ↥({b} : Set B) p) (Punct B p)
        (fun _ hp => hp) ℤ p).hom a) := by
  rw [relCohMap_compA_apply (tcmA ↥({b} : Set B) p q) (tcmA B p q) (Punct B p)
    (tcmFibIncl B p q b) (tcmPr1 B p q) (tcmFibIncl_memA B p q b) (fun x hx => hx)
    (fun x hx => hx) ℤ p a]
  rw [relCohMap_congrA (tcmA ↥({b} : Set B) p q) (Punct B p)
    (tcmPr1_comp_tcmFibIncl B p q b) (fun x hx => hx) (fun x hx => hx) ℤ p]
  rw [← relCohMap_compA_apply (tcmA ↥({b} : Set B) p q) (Punct ↥({b} : Set B) p) (Punct B p)
    (tcmPr1 ↥({b} : Set B) p q) (baseIncl B ({b} : Set B) p) (fun x hx => hx)
    (fun _ hp => hp) (fun x hx => hx) ℤ p a]

/-- **The fibre restriction of the second pulled-back model class**. -/
theorem fibre_pullback_pr2 {B : Type} [TopologicalSpace B] (p q : ℕ) (b : B)
    (a : RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Punct B q)) :
    (relCohMap (tcmFibIncl B p q b) (tcmC ↥({b} : Set B) p q) (tcmC B p q)
        (tcmFibIncl_memC B p q b) ℤ q).hom
      ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom a)
    = (relCohMap (tcmPr2 ↥({b} : Set B) p q) (tcmC ↥({b} : Set B) p q)
        (Punct ↥({b} : Set B) q) (fun x hx => hx) ℤ q).hom
      ((relCohMap (baseIncl B ({b} : Set B) q) (Punct ↥({b} : Set B) q) (Punct B q)
        (fun _ hp => hp) ℤ q).hom a) := by
  rw [relCohMap_compA_apply (tcmC ↥({b} : Set B) p q) (tcmC B p q) (Punct B q)
    (tcmFibIncl B p q b) (tcmPr2 B p q) (tcmFibIncl_memC B p q b) (fun x hx => hx)
    (fun x hx => hx) ℤ q a]
  rw [relCohMap_congrA (tcmC ↥({b} : Set B) p q) (Punct B q)
    (tcmPr2_comp_tcmFibIncl B p q b) (fun x hx => hx) (fun x hx => hx) ℤ q]
  rw [← relCohMap_compA_apply (tcmC ↥({b} : Set B) p q) (Punct ↥({b} : Set B) q) (Punct B q)
    (tcmPr2 ↥({b} : Set B) p q) (baseIncl B ({b} : Set B) q) (fun x hx => hx)
    (fun _ hp => hp) (fun x hx => hx) ℤ q a]

/-- **The fibre restriction of the model class of the sum**: on the fibre over `b` it is
`Mpun (p+q) ↥{b}`. -/
theorem fibre_pullback_tcmF {B : Type} [TopologicalSpace B] (p q : ℕ) (b : B)
    (a : RelCoh ℤ (p + q) (B × EuclideanSpace ℝ (Fin (p + q))) (Punct B (p + q))) :
    (relCohMap (tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
        (tcmA B p q ∪ tcmC B p q) (tcmFibIncl_mem B p q b) ℤ (p + q)).hom
      ((relCohMap (tcmF B p q) (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
        (tcmF_mem B p q) ℤ (p + q)).hom a)
    = (relCohMap (tcmF ↥({b} : Set B) p q)
        (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q) (Punct ↥({b} : Set B) (p + q))
        (tcmF_mem ↥({b} : Set B) p q) ℤ (p + q)).hom
      ((relCohMap (baseIncl B ({b} : Set B) (p + q)) (Punct ↥({b} : Set B) (p + q))
        (Punct B (p + q)) (fun _ hp => hp) ℤ (p + q)).hom a) := by
  rw [relCohMap_compA_apply (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
    (tcmA B p q ∪ tcmC B p q) (Punct B (p + q)) (tcmFibIncl B p q b) (tcmF B p q)
    (tcmFibIncl_mem B p q b) (tcmF_mem B p q)
    (fun x hx => (tcmF_punct_iff ↥({b} : Set B) p q x).mp hx) ℤ (p + q) a]
  rw [relCohMap_congrA (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q) (Punct B (p + q))
    (tcmF_comp_tcmFibIncl B p q b) (fun x hx => (tcmF_punct_iff ↥({b} : Set B) p q x).mp hx)
    (fun x hx => (tcmF_punct_iff ↥({b} : Set B) p q x).mp hx) ℤ (p + q)]
  rw [← relCohMap_compA_apply (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
    (Punct ↥({b} : Set B) (p + q)) (Punct B (p + q)) (tcmF ↥({b} : Set B) p q)
    (baseIncl B ({b} : Set B) (p + q)) (tcmF_mem ↥({b} : Set B) p q) (fun _ hp => hp)
    (fun x hx => (tcmF_punct_iff ↥({b} : Set B) p q x).mp hx) ℤ (p + q) a]

/-! ## Fibrewise detection -/

/-- `Work.Whitney.Mpun_eq_of_fibrewise` without its (unused) hypothesis `1 ≤ n`: the punctured model
class of a trivial bundle is detected by its restrictions to the fibres of the base. -/
theorem Mpun_eq_of_fibrewise' {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (P Q : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Punct Y n))
    (h : ∀ y : Y,
      (relCohMap (baseIncl Y ({y} : Set Y) n)
        (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ n).hom P
      = (relCohMap (baseIncl Y ({y} : Set Y) n)
        (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ n).hom Q) :
    P = Q := by
  classical
  obtain ⟨a, ha⟩ := (Mpun_isModel n Y 0).2 ((Nat.zero_add n).symm ▸ P)
  obtain ⟨b, hb⟩ := (Mpun_isModel n Y 0).2 ((Nat.zero_add n).symm ▸ Q)
  have hpt : ∀ y : Y, (CohMap (setIncl ({y} : Set Y)) ℤ 0).hom a
      = (CohMap (setIncl ({y} : Set Y)) ℤ 0).hom b := by
    intro y
    have keyP := congrArg (fun z => (relCohMap (baseIncl Y ({y} : Set Y) n)
      (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom z) ha
    have keyQ := congrArg (fun z => (relCohMap (baseIncl Y ({y} : Set Y) n)
      (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom z) hb
    have hmid : (relCohMap (baseIncl Y ({y} : Set Y) n)
        (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom
          ((Nat.zero_add n).symm ▸ P)
        = (relCohMap (baseIncl Y ({y} : Set Y) n)
        (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom
          ((Nat.zero_add n).symm ▸ Q) := by
      rw [relCohMap_cast (baseIncl Y ({y} : Set Y) n) (Punct ↥({y} : Set Y) n)
            (Punct Y n) (fun _ hp => hp) (h := (Nat.zero_add n).symm) P,
          relCohMap_cast (baseIncl Y ({y} : Set Y) n) (Punct ↥({y} : Set Y) n)
            (Punct Y n) (fun _ hp => hp) (h := (Nat.zero_add n).symm) Q,
          h y]
    have hLa := baseIncl_mixedCup_Mpun n ({y} : Set Y) a
    have hLb := baseIncl_mixedCup_Mpun n ({y} : Set Y) b
    refine (Mpun_isModel n ↥({y} : Set Y) 0).1 ?_
    exact hLa.symm.trans (keyP.trans (hmid.trans (keyQ.symm.trans hLb)))
  have hzero : ∀ y : Y, (CohMap (setIncl ({y} : Set Y)) ℤ 0).hom (a - b) = 0 := by
    intro y
    rw [map_sub, hpt y, sub_self]
  have hab : a = b := sub_eq_zero.mp (h0_eq_zero_of_point_incl (a - b) hzero)
  rw [hab] at ha
  exact eq_of_cast_eq (α := fun k => RelCoh ℤ k (Y × EuclideanSpace ℝ (Fin n)) (Punct Y n))
    (h := (Nat.zero_add n).symm) (ha.symm.trans hb)

/-- **A relative class over `B × (ℝ^p × ℝ^q)` is determined by its restrictions to the fibres of the
base**: this is `Mpun_eq_of_fibrewise'` moved along the inverse `tcmF_inv` of the coordinate
identification. -/
theorem tcmModel_detect {B : Type} [TopologicalSpace B] (p q : ℕ)
    (P Q : RelCoh ℤ (p + q) (tcmX B p q) (tcmA B p q ∪ tcmC B p q))
    (h : ∀ b : B,
      (relCohMap (tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
        (tcmA B p q ∪ tcmC B p q) (tcmFibIncl_mem B p q b) ℤ (p + q)).hom P
      = (relCohMap (tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
        (tcmA B p q ∪ tcmC B p q) (tcmFibIncl_mem B p q b) ℤ (p + q)).hom Q) :
    P = Q := by
  classical
  -- the identities expressing that `tcmF_inv` inverts `tcmF`
  have hGF : (tcmF_inv B p q).comp (tcmF B p q) = ContinuousMap.id (tcmX B p q) :=
    ContinuousMap.ext (fun x => tcmF_inv_tcmF B p q x)
  have hGF_mem : ∀ x ∈ tcmA B p q ∪ tcmC B p q,
      ((tcmF_inv B p q).comp (tcmF B p q)) x ∈ tcmA B p q ∪ tcmC B p q :=
    fun x hx => by rw [ContinuousMap.comp_apply, tcmF_inv_tcmF]; exact hx
  -- the punctured part of the target lies in the two closed sets
  have hg_mem : ∀ y ∈ Punct B (p + q), tcmF_inv B p q y ∈ tcmA B p q ∪ tcmC B p q :=
    fun y hy => (tcmF_punct_iff B p q (tcmF_inv B p q y)).mpr (by rw [tcmF_tcmF_inv]; exact hy)
  -- `tcmF^*` inverts `tcmF_inv^*`
  have hcompF (x : RelCoh ℤ (p + q) (tcmX B p q) (tcmA B p q ∪ tcmC B p q)) :
      (relCohMap (tcmF B p q) (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
        (tcmF_mem B p q) ℤ (p + q)).hom
        ((relCohMap (tcmF_inv B p q) (Punct B (p + q)) (tcmA B p q ∪ tcmC B p q)
          hg_mem ℤ (p + q)).hom x) = x := by
    rw [relCohMap_compA_apply (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
      (tcmA B p q ∪ tcmC B p q) (tcmF B p q) (tcmF_inv B p q) (tcmF_mem B p q) hg_mem hGF_mem
      ℤ (p + q) x]
    rw [relCohMap_congrA (tcmA B p q ∪ tcmC B p q) (tcmA B p q ∪ tcmC B p q) hGF hGF_mem
      (fun _ hx => hx) ℤ (p + q)]
    rw [relCohMap_idA (tcmA B p q ∪ tcmC B p q) ℤ (p + q)]
    rfl
  -- the fibre conditions of the two classes, transported along `tcmF_inv`
  have hgb_mem (b : B) : ∀ y ∈ Punct ↥({b} : Set B) (p + q),
      tcmF_inv ↥({b} : Set B) p q y ∈ tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q :=
    fun y hy => (tcmF_punct_iff ↥({b} : Set B) p q (tcmF_inv ↥({b} : Set B) p q y)).mpr
      (by rw [tcmF_tcmF_inv]; exact hy)
  have hgf_mem (b : B) : ∀ x ∈ Punct ↥({b} : Set B) (p + q),
      ((tcmFibIncl B p q b).comp (tcmF_inv ↥({b} : Set B) p q)) x ∈ tcmA B p q ∪ tcmC B p q :=
    fun x hx => tcmFibIncl_mem B p q b (tcmF_inv ↥({b} : Set B) p q x)
      ((tcmF_punct_iff ↥({b} : Set B) p q (tcmF_inv ↥({b} : Set B) p q x)).mpr
        (by rw [tcmF_tcmF_inv]; exact hx))
  have step (b : B) (x : RelCoh ℤ (p + q) (tcmX B p q) (tcmA B p q ∪ tcmC B p q)) :
      (relCohMap (baseIncl B ({b} : Set B) (p + q)) (Punct ↥({b} : Set B) (p + q))
        (Punct B (p + q)) (fun _ hp => hp) ℤ (p + q)).hom
        ((relCohMap (tcmF_inv B p q) (Punct B (p + q)) (tcmA B p q ∪ tcmC B p q)
          hg_mem ℤ (p + q)).hom x)
      = (relCohMap (tcmF_inv ↥({b} : Set B) p q) (Punct ↥({b} : Set B) (p + q))
          (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q) (hgb_mem b) ℤ (p + q)).hom
        ((relCohMap (tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
          (tcmA B p q ∪ tcmC B p q) (tcmFibIncl_mem B p q b) ℤ (p + q)).hom x) := by
    rw [relCohMap_compA_apply (Punct ↥({b} : Set B) (p + q)) (Punct B (p + q))
      (tcmA B p q ∪ tcmC B p q) (baseIncl B ({b} : Set B) (p + q)) (tcmF_inv B p q)
      (fun _ hp => hp) hg_mem (fun x hx => hg_mem _ hx) ℤ (p + q) x]
    rw [relCohMap_congrA (Punct ↥({b} : Set B) (p + q)) (tcmA B p q ∪ tcmC B p q)
      (tcmF_inv_comp_baseIncl B p q b) (fun x hx => hg_mem _ hx) (hgf_mem b) ℤ (p + q)]
    rw [relCohMap_compA_apply (Punct ↥({b} : Set B) (p + q))
      (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q) (tcmA B p q ∪ tcmC B p q)
      (tcmF_inv ↥({b} : Set B) p q) (tcmFibIncl B p q b) (hgb_mem b) (tcmFibIncl_mem B p q b)
      (hgf_mem b) ℤ (p + q) x]
  have hfib : ∀ b : B,
      (relCohMap (baseIncl B ({b} : Set B) (p + q)) (Punct ↥({b} : Set B) (p + q))
        (Punct B (p + q)) (fun _ hp => hp) ℤ (p + q)).hom
        ((relCohMap (tcmF_inv B p q) (Punct B (p + q)) (tcmA B p q ∪ tcmC B p q)
          hg_mem ℤ (p + q)).hom P)
      = (relCohMap (baseIncl B ({b} : Set B) (p + q)) (Punct ↥({b} : Set B) (p + q))
        (Punct B (p + q)) (fun _ hp => hp) ℤ (p + q)).hom
        ((relCohMap (tcmF_inv B p q) (Punct B (p + q)) (tcmA B p q ∪ tcmC B p q)
          hg_mem ℤ (p + q)).hom Q) := by
    intro b
    rw [step b P, step b Q, h b]
  have hPQ : (relCohMap (tcmF_inv B p q) (Punct B (p + q)) (tcmA B p q ∪ tcmC B p q)
      hg_mem ℤ (p + q)).hom P
      = (relCohMap (tcmF_inv B p q) (Punct B (p + q)) (tcmA B p q ∪ tcmC B p q)
      hg_mem ℤ (p + q)).hom Q := Mpun_eq_of_fibrewise' _ _ hfib
  rw [← hcompF P, hPQ, hcompF Q]

end Fib

/-! ## The reduction to the point case -/

/-- **The model product formula over an arbitrary base follows from its point case.**  If the
relative–relative cup of the two pulled-back model Thom classes is the model class of the sum over
every one-point base (hypothesis `h`), then the same identity holds over every base `B`:

`tcmRelCup (pr₁^* Mpun p) (pr₂^* Mpun q) = tcmF^* (Mpun (p+q))` in
`H^{p+q}(B × (ℝ^p × ℝ^q), A ∪ C)`.

The proof restricts both sides to the fibres `↥{b} × (ℝ^p × ℝ^q)`, where the identity is `h` at the
one-point base `↥{b}` (the fibre restrictions of `pr₁^* Mpun p`, `pr₂^* Mpun q` and
`tcmF^* Mpun (p+q)` are computed by `Fib.fibre_pullback_pr1`, `Fib.fibre_pullback_pr2`,
`Fib.fibre_pullback_tcmF` together with `Work.Thom.Mpun_natural`), and then applies the fibrewise
detection `Fib.tcmModel_detect`. -/
theorem tcmModelMul_of_point
    (h : ∀ (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (p q : ℕ),
      Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p q) (Work.Whitney.tcmC Y p q)
          (Work.Whitney.isOpen_tcmA Y p q) (Work.Whitney.isOpen_tcmC Y p q) p q
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p q) (Work.Whitney.tcmA Y p q)
          (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p q) (Work.Whitney.tcmC Y p q)
          (Work.Thom.Punct Y q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q Y))
      = (Work.Thom.relCohMap (Work.Whitney.tcmF Y p q)
          (Work.Whitney.tcmA Y p q ∪ Work.Whitney.tcmC Y p q) (Work.Thom.Punct Y (p + q))
          (Work.Whitney.tcmF_mem Y p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) Y))
    {B : Type} [TopologicalSpace B] (p q : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA B p q) (Work.Whitney.tcmC B p q)
        (Work.Whitney.isOpen_tcmA B p q) (Work.Whitney.isOpen_tcmC B p q) p q
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 B p q) (Work.Whitney.tcmA B p q)
        (Work.Thom.Punct B p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p B))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 B p q) (Work.Whitney.tcmC B p q)
        (Work.Thom.Punct B q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q B))
    = (Work.Thom.relCohMap (Work.Whitney.tcmF B p q)
        (Work.Whitney.tcmA B p q ∪ Work.Whitney.tcmC B p q) (Work.Thom.Punct B (p + q))
        (Work.Whitney.tcmF_mem B p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) B) := by
  have hfib : ∀ b : B,
      (relCohMap (Fib.tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
        (tcmA B p q ∪ tcmC B p q) (Fib.tcmFibIncl_mem B p q b) ℤ (p + q)).hom
        (tcmRelCup (tcmA B p q) (tcmC B p q) (isOpen_tcmA B p q) (isOpen_tcmC B p q) p q
          ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom
            (Mpun p B))
          ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom
            (Mpun q B)))
      = (relCohMap (Fib.tcmFibIncl B p q b) (tcmA ↥({b} : Set B) p q ∪ tcmC ↥({b} : Set B) p q)
        (tcmA B p q ∪ tcmC B p q) (Fib.tcmFibIncl_mem B p q b) ℤ (p + q)).hom
        ((relCohMap (tcmF B p q) (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
          (tcmF_mem B p q) ℤ (p + q)).hom (Mpun (p + q) B)) := by
    intro b
    rw [tcmRelCup_natural ℤ (Fib.tcmFibIncl B p q b) (tcmA B p q) (tcmC B p q)
      (tcmA ↥({b} : Set B) p q) (tcmC ↥({b} : Set B) p q) (isOpen_tcmA B p q)
      (isOpen_tcmC B p q) (isOpen_tcmA ↥({b} : Set B) p q)
      (isOpen_tcmC ↥({b} : Set B) p q) (Fib.tcmFibIncl_memA B p q b)
      (Fib.tcmFibIncl_memC B p q b) (Fib.tcmFibIncl_mem B p q b) p q
      ((relCohMap (tcmPr1 B p q) (tcmA B p q) (Punct B p) (fun x hx => hx) ℤ p).hom
        (Mpun p B))
      ((relCohMap (tcmPr2 B p q) (tcmC B p q) (Punct B q) (fun x hx => hx) ℤ q).hom
        (Mpun q B))]
    rw [Fib.fibre_pullback_pr1 (B := B) p q b (Mpun p B),
      Fib.fibre_pullback_pr2 (B := B) p q b (Mpun q B),
      Fib.fibre_pullback_tcmF (B := B) p q b (Mpun (p + q) B)]
    rw [Mpun_natural p B ({b} : Set B), Mpun_natural q B ({b} : Set B),
      Mpun_natural (p + q) B ({b} : Set B)]
    exact h ↥({b} : Set B) p q
  exact Fib.tcmModel_detect p q _ _ hfib

end

end Work.Whitney
