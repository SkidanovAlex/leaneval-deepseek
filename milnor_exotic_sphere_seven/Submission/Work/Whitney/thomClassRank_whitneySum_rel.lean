import Mathlib
import Submission.Work.Whitney.WSumChars
import Submission.Work.Whitney.tcmCup_step
import Submission.Work.Whitney.RankOneLHS
import Submission.Work.Whitney.tcmRankOneLHS_eq_Mn
import Submission.Work.Whitney.tcmModelMul_signed_of_point
import Submission.Work.Whitney.tcmRelCup_natural
import Submission.Work.Whitney.Mpun_eq_of_fibrewise
import Submission.Work.Gen.RifStd
import Submission.Work.Thom.localThomOfComplexCover_pdCohMap_subset
import Submission.Work.Thom.openThom_eq_zero_of_baseSet_rank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## The signed model product formula, assembled from the suspension step

`Work.Whitney.tcmCup_step` (proved, from the rank-one crux `Work.Whitney.tcmPunctCore_signed`) is the
induction step of the signed model product formula over a one-point base.  Assembled from it here:
the point case `tcmModelMul_point_signed'`, the signed formula `tcmModelMul_signed'` over an
arbitrary base (via `Work.Whitney.tcmModelMul_signed_of_point`), and the **sign-free even-rank
instance** `tcmModelMul_even'`, which is the mathematical input of the chart bookkeeping of
`Work.Whitney.thomClassRank_whitneySum_rel`.
-/


/-! ## The Koszul-signed model product formula, from the rank-one case

The chain below is a self-contained copy of the corresponding part of
`Submission/Work/Whitney/tcmCup_step.lean`, with one difference: the rank-one case `tcmJ Y n 1` is
`Work.Whitney.tcmRankOneLHS_eq_Mn` (the spherical form of the rank-one case, proved in
`Submission/Work/Whitney/tcmRankOneLHS_eq_Mn.lean` and turned into the punctured form by
`Work.Whitney.tcmProd_eq_of_tcmRankOneLHS`) rather than the placeholder
`Work.Whitney.tcmPunctCore_signed`.  Nothing else in the chain changes.
-/

section CleanChain

open Work.Thom

theorem tcmJ_one_clean (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (n : ℕ) :
    Work.Whitney.tcmJ Y n 1 = (-1 : ℤ) ^ n • Work.Thom.Mpun (n + 1) Y := by
  have h := Work.Whitney.tcmProd_eq_of_tcmRankOneLHS Y n (Work.Whitney.tcmRankOneLHS_eq_Mn Y n)
  simpa only [Work.Whitney.tcmJ] using h

/-- **The recursion of the punctured suspension on the model class**, from the rank-one case
`tcmJ_one_clean` and `Mpun_succ`. -/
theorem Pstep_Mpun_clean (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (q : ℕ) :
    Pstep Y q (Mpun q Y) = (-1 : ℤ) ^ q • tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y) := by
  have h := tcmJ_one_clean Y q
  rw [show tcmJ Y q 1 = tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y) from rfl] at h
  rw [← Mpun_succ Y q, h, smul_smul, Work.Thom.negOnePow_mul_self, one_smul]

/-- **The model product formula in the punctured group for `q ≥ 1`**, by induction on `q` from the
rank-one case `tcmJ_one_clean` and the associativity `hA` of `tcmProd` at `r = 1`. -/
theorem tcmJ_model_of_assoc_clean (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (hA : ∀ (p q : ℕ)
        (a : RelCoh ℤ p (Y × EuclideanSpace ℝ (Fin p)) (Punct Y p))
        (b : RelCoh ℤ q (Y × EuclideanSpace ℝ (Fin q)) (Punct Y q))
        (c : RelCoh ℤ 1 (Y × EuclideanSpace ℝ (Fin 1)) (Punct Y 1)),
        tcmProd Y p (q + 1) a (tcmProd Y q 1 b c)
          = tcmProd Y (p + q) 1 (tcmProd Y p q a b) c)
    (p : ℕ) :
    ∀ q : ℕ, 1 ≤ q → tcmJ Y p q = (-1 : ℤ) ^ (p * q) • Mpun (p + q) Y := by
  intro q
  induction q with
  | zero => intro hq; omega
  | succ q ih =>
      intro hq
      rcases Nat.eq_zero_or_pos q with h0 | hpos
      · subst h0
        simpa only [Nat.mul_one, Nat.zero_add] using tcmJ_one_clean Y p
      · have hqn : tcmJ Y p q = (-1 : ℤ) ^ (p * q) • Mpun (p + q) Y := ih hpos
        have hsign : (-1 : ℤ) ^ (p * (q + 1))
            = (-1 : ℤ) ^ q * ((-1 : ℤ) ^ (p * q) * (-1 : ℤ) ^ (p + q)) := by
          calc (-1 : ℤ) ^ (p * (q + 1))
              = (-1 : ℤ) ^ (p * q + p) := by rw [Nat.mul_succ]
            _ = (-1 : ℤ) ^ (p * q + p) * 1 := (mul_one _).symm
            _ = (-1 : ℤ) ^ (p * q + p) * (-1 : ℤ) ^ (2 * q) := by
                  rw [Even.neg_one_pow (even_two_mul q)]
            _ = (-1 : ℤ) ^ ((p * q + p) + 2 * q) := (pow_add _ _ _).symm
            _ = (-1 : ℤ) ^ (q + (p * q + (p + q))) := by
                  rw [show (p * q + p) + 2 * q = q + (p * q + (p + q)) from by omega]
            _ = (-1 : ℤ) ^ q * (-1 : ℤ) ^ (p * q + (p + q)) := pow_add _ _ _
            _ = (-1 : ℤ) ^ q * ((-1 : ℤ) ^ (p * q) * (-1 : ℤ) ^ (p + q)) := by
                  rw [pow_add]
        calc tcmJ Y p (q + 1)
            = tcmProd Y p (q + 1) (Mpun p Y) (Mpun (q + 1) Y) := rfl
          _ = tcmProd Y p (q + 1) (Mpun p Y) (Pstep Y q (Mpun q Y)) := by rw [Mpun_succ Y q]
          _ = tcmProd Y p (q + 1) (Mpun p Y)
                ((-1 : ℤ) ^ q • tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y)) := by rw [Pstep_Mpun_clean Y q]
          _ = (-1 : ℤ) ^ q • tcmProd Y p (q + 1) (Mpun p Y)
                (tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y)) := by rw [tcmProd_zsmul_right]
          _ = (-1 : ℤ) ^ q • tcmProd Y (p + q) 1
                (tcmProd Y p q (Mpun p Y) (Mpun q Y)) (Mpun 1 Y) := by
                rw [hA p q (Mpun p Y) (Mpun q Y) (Mpun 1 Y)]
          _ = (-1 : ℤ) ^ q • tcmProd Y (p + q) 1 (tcmJ Y p q) (Mpun 1 Y) := rfl
          _ = (-1 : ℤ) ^ q • tcmProd Y (p + q) 1
                ((-1 : ℤ) ^ (p * q) • Mpun (p + q) Y) (Mpun 1 Y) := by rw [hqn]
          _ = (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (p * q) •
                tcmProd Y (p + q) 1 (Mpun (p + q) Y) (Mpun 1 Y)) := by rw [tcmProd_zsmul_left]
          _ = (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (p * q) •
                ((-1 : ℤ) ^ (p + q) • Mpun (p + q + 1) Y)) := by
                rw [show tcmProd Y (p + q) 1 (Mpun (p + q) Y) (Mpun 1 Y)
                      = tcmJ Y (p + q) 1 from rfl, tcmJ_one_clean Y (p + q)]
          _ = (-1 : ℤ) ^ (p * (q + 1)) • Mpun (p + (q + 1)) Y := by
                rw [hsign, smul_smul, smul_smul, mul_assoc]
                rfl

/-- **The suspension step of the model class in the punctured group for `q ≥ 1`**, from the model
formula at `q` and at `q+1` plus `Mpun_succ` and `Pstep_zsmul`. -/
theorem tcmJ_succ_of_assoc_clean (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (hA : ∀ (p q : ℕ)
        (a : RelCoh ℤ p (Y × EuclideanSpace ℝ (Fin p)) (Punct Y p))
        (b : RelCoh ℤ q (Y × EuclideanSpace ℝ (Fin q)) (Punct Y q))
        (c : RelCoh ℤ 1 (Y × EuclideanSpace ℝ (Fin 1)) (Punct Y 1)),
        tcmProd Y p (q + 1) a (tcmProd Y q 1 b c)
          = tcmProd Y (p + q) 1 (tcmProd Y p q a b) c)
    (p : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    tcmJ Y p (q + 1) = (-1 : ℤ) ^ p • Pstep Y (p + q) (tcmJ Y p q) := by
  have hsign : (-1 : ℤ) ^ (p * (q + 1)) = (-1 : ℤ) ^ p * (-1 : ℤ) ^ (p * q) := by
    rw [Nat.mul_succ, ← pow_add]
    congr 1
    exact Nat.add_comm _ _
  rw [tcmJ_model_of_assoc_clean Y hA p (q + 1) (by omega), tcmJ_model_of_assoc_clean Y hA p q hq,
    Pstep_zsmul, ← Mpun_succ Y (p + q), smul_smul, hsign]
  rfl

theorem tcmCup_step_of_assoc_clean (Y : Type) [TopologicalSpace Y] [Subsingleton Y]
    (hA : ∀ (p q : ℕ)
        (a : RelCoh ℤ p (Y × EuclideanSpace ℝ (Fin p)) (Punct Y p))
        (b : RelCoh ℤ q (Y × EuclideanSpace ℝ (Fin q)) (Punct Y q))
        (c : RelCoh ℤ 1 (Y × EuclideanSpace ℝ (Fin 1)) (Punct Y 1)),
        tcmProd Y p (q + 1) a (tcmProd Y q 1 b c)
          = tcmProd Y (p + q) 1 (tcmProd Y p q a b) c)
    (p q : ℕ) :
    (Work.Thom.relCohMap (Work.Whitney.Fib.tcmF_inv Y p (q + 1)) (Work.Thom.Sph Y (p + (q + 1)))
      (Work.Whitney.tcmA Y p (q + 1) ∪ Work.Whitney.tcmC Y p (q + 1))
      (Work.Whitney.tcmF_inv_mem' (Y := Y) p (q + 1)) ℤ (p + (q + 1))).hom
      (Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p (q + 1)) (Work.Whitney.tcmC Y p (q + 1))
        (Work.Whitney.isOpen_tcmA Y p (q + 1)) (Work.Whitney.isOpen_tcmC Y p (q + 1)) p (q + 1)
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p (q + 1)) (Work.Whitney.tcmA Y p (q + 1))
          (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p (q + 1)) (Work.Whitney.tcmC Y p (q + 1))
          (Work.Thom.Punct Y (q + 1)) (fun x hx => hx) ℤ (q + 1)).hom
          (Work.Thom.Mpun (q + 1) Y)))
    = ((-1 : ℤ) ^ p) •
      (Work.Thom.step Y (p + q)
        ((Work.Thom.relCohMap (Work.Whitney.Fib.tcmF_inv Y p q) (Work.Thom.Sph Y (p + q))
          (Work.Whitney.tcmA Y p q ∪ Work.Whitney.tcmC Y p q)
          (Work.Whitney.tcmF_inv_mem' (Y := Y) p q) ℤ (p + q)).hom
          (Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p q) (Work.Whitney.tcmC Y p q)
            (Work.Whitney.isOpen_tcmA Y p q) (Work.Whitney.isOpen_tcmC Y p q) p q
            ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p q) (Work.Whitney.tcmA Y p q)
              (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
            ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p q) (Work.Whitney.tcmC Y p q)
              (Work.Thom.Punct Y q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q Y))))) := by
  by_cases hY : Nonempty Y
  · haveI : Nonempty Y := hY
    change tcmCupLHS Y p (q + 1) = ((-1 : ℤ) ^ p) • (step Y (p + q) (tcmCupLHS Y p q))
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · -- `q = 0`: the unit law plus `Mn (n+1) = step n (Mn n)`
      subst hq0
      have h1 : tcmCupLHS Y p 1 = (-1 : ℤ) ^ p • Mn (p + 1) Y := by
        rw [tcmCupLHS_eq_jMap, tcmJ_one_clean, map_zsmul, Mpun_spec]
      have h0 : tcmCupLHS Y p 0 = Mn (p + 0) Y := by
        have h := congrArg (fun z => (relCohMap (Fib.tcmF_inv Y p 0) (Sph Y (p + 0))
            (tcmA Y p 0 ∪ tcmC Y p 0) (tcmF_inv_mem' (Y := Y) p 0) ℤ (p + 0)).hom z)
          (tcmModelMul_point_zero Y p)
        have h2 := map_zsmul ((relCohMap (Fib.tcmF_inv Y p 0) (Sph Y (p + 0))
            (tcmA Y p 0 ∪ tcmC Y p 0) (tcmF_inv_mem' (Y := Y) p 0) ℤ (p + 0)).hom)
          ((-1 : ℤ) ^ (p * 0))
          ((relCohMap (tcmF Y p 0) (tcmA Y p 0 ∪ tcmC Y p 0) (Punct Y (p + 0))
            (tcmF_mem Y p 0) ℤ (p + 0)).hom (Mpun (p + 0) Y))
        have h3 := congrArg (fun z => (-1 : ℤ) ^ (p * 0) • z) (phi_Mpun (Y := Y) p 0)
        have h4 : (-1 : ℤ) ^ (p * 0) • Mn (p + 0) Y = Mn (p + 0) Y := by
          rw [Nat.mul_zero, pow_zero, one_smul]
        exact (h.trans (h2.trans h3)).trans h4
      change tcmCupLHS Y p 1 = (-1 : ℤ) ^ p • step Y (p + 0) (tcmCupLHS Y p 0)
      rw [h1, h0]
      congr 1
    · -- `q ≥ 1`: the model formula at `q` and at `q + 1`
      have hstep := tcmJ_succ_of_assoc_clean Y hA p hqpos
      rw [tcmCupLHS_eq_jMap Y p (q + 1), tcmCupLHS_eq_jMap Y p q, hstep, map_zsmul]
      exact congrArg (fun z => ((-1 : ℤ) ^ p) • z) (Pstep_spec Y (p + q) (tcmJ Y p q))
  · haveI : IsEmpty Y := not_nonempty_iff.mp hY
    haveI : IsEmpty (Y × EuclideanSpace ℝ (Fin (p + (q + 1)))) :=
      ⟨fun x => isEmptyElim x.1⟩
    haveI : Subsingleton (RelCoh ℤ (p + (q + 1))
        (Y × EuclideanSpace ℝ (Fin (p + (q + 1)))) (Sph Y (p + (q + 1)))) :=
      subsingleton_relCoh_of_isEmpty _ _
    exact Subsingleton.elim _ _

end CleanChain

/-- **The signed model product formula over a one-point base**, from the suspension step
`Work.Whitney.tcmCup_step` (the only non-formal input). -/
theorem tcmModelMul_point_signed' {Y : Type} [TopologicalSpace Y] [Subsingleton Y] (p q : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p q) (Work.Whitney.tcmC Y p q)
        (Work.Whitney.isOpen_tcmA Y p q) (Work.Whitney.isOpen_tcmC Y p q) p q
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p q) (Work.Whitney.tcmA Y p q)
        (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p q) (Work.Whitney.tcmC Y p q)
        (Work.Thom.Punct Y q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q Y))
    = ((-1 : ℤ) ^ (p * q)) •
      ((Work.Thom.relCohMap (Work.Whitney.tcmF Y p q)
        (Work.Whitney.tcmA Y p q ∪ Work.Whitney.tcmC Y p q) (Work.Thom.Punct Y (p + q))
        (Work.Whitney.tcmF_mem Y p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) Y)) := by
  have hstep : ∀ (p q : ℕ),
      (Work.Thom.relCohMap (Work.Whitney.Fib.tcmF_inv Y p (q + 1))
        (Work.Thom.Sph Y (p + (q + 1)))
        (Work.Whitney.tcmA Y p (q + 1) ∪ Work.Whitney.tcmC Y p (q + 1))
        (Work.Whitney.tcmF_inv_mem' (Y := Y) p (q + 1)) ℤ (p + (q + 1))).hom
        (Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p (q + 1)) (Work.Whitney.tcmC Y p (q + 1))
          (Work.Whitney.isOpen_tcmA Y p (q + 1)) (Work.Whitney.isOpen_tcmC Y p (q + 1)) p (q + 1)
          ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p (q + 1))
            (Work.Whitney.tcmA Y p (q + 1)) (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom
            (Work.Thom.Mpun p Y))
          ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p (q + 1))
            (Work.Whitney.tcmC Y p (q + 1)) (Work.Thom.Punct Y (q + 1)) (fun x hx => hx) ℤ (q + 1)).hom
            (Work.Thom.Mpun (q + 1) Y)))
      = ((-1 : ℤ) ^ p) •
        (Work.Thom.step Y (p + q)
          ((Work.Thom.relCohMap (Work.Whitney.Fib.tcmF_inv Y p q) (Work.Thom.Sph Y (p + q))
            (Work.Whitney.tcmA Y p q ∪ Work.Whitney.tcmC Y p q)
            (Work.Whitney.tcmF_inv_mem' (Y := Y) p q) ℤ (p + q)).hom
            (Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p q) (Work.Whitney.tcmC Y p q)
              (Work.Whitney.isOpen_tcmA Y p q) (Work.Whitney.isOpen_tcmC Y p q) p q
              ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p q) (Work.Whitney.tcmA Y p q)
                (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
              ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p q) (Work.Whitney.tcmC Y p q)
                (Work.Thom.Punct Y q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q Y))))) := by
    intro p q
    exact tcmCup_step_of_assoc_clean Y
      (fun p q a b c => Work.Whitney.tcmProd_assoc_one Y p q a b c) p q
  induction q with
  | zero => exact Work.Whitney.tcmModelMul_point_zero Y p
  | succ q ih =>
      refine Work.Whitney.phi_injective (Y := Y) p (q + 1) (p + (q + 1)) ?_
      rw [map_zsmul]
      rw [hstep p q]
      rw [ih]
      rw [map_zsmul]
      rw [Work.Whitney.phi_Mpun (Y := Y) p q]
      rw [Work.Whitney.step_zsmul]
      rw [show Work.Thom.step Y (p + q) (Work.Thom.Mn (p + q) Y)
          = Work.Thom.Mn (p + q + 1) Y from rfl]
      rw [smul_smul]
      congr 1
      · rw [Nat.mul_succ, pow_add]
        exact mul_comm _ _
      · exact (Work.Whitney.phi_Mpun (Y := Y) p (q + 1)).symm

/-- **The signed model product formula over an arbitrary base**: assembled from the point case by
`Work.Whitney.tcmModelMul_signed_of_point`. -/
theorem tcmModelMul_signed' {B : Type} [TopologicalSpace B] (p q : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA B p q) (Work.Whitney.tcmC B p q)
        (Work.Whitney.isOpen_tcmA B p q) (Work.Whitney.isOpen_tcmC B p q) p q
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 B p q) (Work.Whitney.tcmA B p q)
        (Work.Thom.Punct B p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p B))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 B p q) (Work.Whitney.tcmC B p q)
        (Work.Thom.Punct B q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q B))
    = ((-1 : ℤ) ^ (p * q)) •
      ((Work.Thom.relCohMap (Work.Whitney.tcmF B p q)
        (Work.Whitney.tcmA B p q ∪ Work.Whitney.tcmC B p q) (Work.Thom.Punct B (p + q))
        (Work.Whitney.tcmF_mem B p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) B)) :=
  Work.Whitney.tcmModelMul_signed_of_point
    (fun Y _ _ p q => tcmModelMul_point_signed' (Y := Y) p q) (B := B) p q

/-- **The model product formula in even ranks** (the sign-free case): for the realified ranks
`p = 2*m₁`, `q = 2*m₂` the sign `(-1)^{p*q}` is `1`, so the relative–relative cup of the two
pulled-back model classes is the model class of the sum. -/
theorem tcmModelMul_even' {B : Type} [TopologicalSpace B] (m₁ m₂ : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA B (2 * m₁) (2 * m₂))
        (Work.Whitney.tcmC B (2 * m₁) (2 * m₂))
        (Work.Whitney.isOpen_tcmA B (2 * m₁) (2 * m₂))
        (Work.Whitney.isOpen_tcmC B (2 * m₁) (2 * m₂))
        (2 * m₁) (2 * m₂)
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 B (2 * m₁) (2 * m₂))
        (Work.Whitney.tcmA B (2 * m₁) (2 * m₂))
        (Work.Thom.Punct B (2 * m₁)) (fun x hx => hx) ℤ (2 * m₁)).hom (Work.Thom.Mpun (2 * m₁) B))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 B (2 * m₁) (2 * m₂))
        (Work.Whitney.tcmC B (2 * m₁) (2 * m₂))
        (Work.Thom.Punct B (2 * m₂)) (fun x hx => hx) ℤ (2 * m₂)).hom (Work.Thom.Mpun (2 * m₂) B))
    = (Work.Thom.relCohMap (Work.Whitney.tcmF B (2 * m₁) (2 * m₂))
        (Work.Whitney.tcmA B (2 * m₁) (2 * m₂) ∪ Work.Whitney.tcmC B (2 * m₁) (2 * m₂))
        (Work.Thom.Punct B (2 * m₁ + 2 * m₂))
        (Work.Whitney.tcmF_mem B (2 * m₁) (2 * m₂)) ℤ (2 * m₁ + 2 * m₂)).hom
        (Work.Thom.Mpun (2 * m₁ + 2 * m₂) B) := by
  rw [tcmModelMul_signed' (B := B) (2 * m₁) (2 * m₂),
    Even.neg_one_pow (show Even (2 * m₁ * (2 * m₂)) from ⟨2 * m₁ * m₂, by ring⟩), one_smul]



/-! ## Cast bookkeeping

The chart identity compares classes living in degrees `2 * (m₁ + m₂)` (the chart class of the
realified sum, whose fibre is `ℂ^{m₁+m₂}`) and `2 * m₁ + 2 * m₂` (the model product formula).  The
transports between these two degrees are organised so that every class lives in the cohomology of a
*fixed* space and only the degree moves:

* `castCLE h` — the linear identification `ℝ^a ≅ ℝ^b` for `h : a = b` (definitionally the identity);
* `castMap h` — the induced map `B × ℝ^a → B × ℝ^b`;
* `Mpun_cast` — `Mpun` is invariant under the degree cast;
* `Mpun_castMap` — the model class is invariant under `castMap`;
* `relCohMap_cast_set` — the pullback commutes with the transport along an equality of the
  relative sets.
-/

section Casts

/-- The canonical linear equivalence `ℝ^a ≃L[ℝ] ℝ^b` induced by `h : a = b`. -/
noncomputable def castCLE {a b : ℕ} (h : a = b) :
    EuclideanSpace ℝ (Fin a) ≃L[ℝ] EuclideanSpace ℝ (Fin b) :=
  h ▸ ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin a))

theorem castCLE_apply {a b : ℕ} (h : a = b) (x : EuclideanSpace ℝ (Fin a)) :
    castCLE h x = cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) x := by
  cases h
  rfl

theorem castCLE_symm_apply {a b : ℕ} (h : a = b) (y : EuclideanSpace ℝ (Fin b)) :
    (castCLE h).symm y =
      cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h.symm) y := by
  cases h
  rfl

@[simp] theorem castCLE_zero {a b : ℕ} (h : a = b) :
    castCLE h (0 : EuclideanSpace ℝ (Fin a)) = 0 := by
  cases h
  rfl

theorem castCLE_eq_zero_iff {a b : ℕ} (h : a = b) (x : EuclideanSpace ℝ (Fin a)) :
    castCLE h x = 0 ↔ x = 0 := by
  cases h
  simp

theorem castCLE_injective {a b : ℕ} (h : a = b) : Function.Injective (castCLE h) :=
  (castCLE h).injective

theorem castCLE_symm_apply_apply {a b : ℕ} (h : a = b) (x : EuclideanSpace ℝ (Fin a)) :
    (castCLE h).symm (castCLE h x) = x :=
  (castCLE h).symm_apply_apply x

theorem castCLE_apply_symm_apply {a b : ℕ} (h : a = b) (y : EuclideanSpace ℝ (Fin b)) :
    castCLE h ((castCLE h).symm y) = y :=
  (castCLE h).apply_symm_apply y

theorem castCLE_symm_eq {a b : ℕ} (h : a = b) : castCLE h.symm = (castCLE h).symm := by
  cases h
  rfl

/-- The composite of the cast with its reverse is the identity. -/
theorem castCLE_apply_castCLE_symm {a b : ℕ} (h : a = b) (y : EuclideanSpace ℝ (Fin b)) :
    castCLE h (castCLE h.symm y) = y := by
  cases h
  rfl

/-- The map `B × ℝ^a → B × ℝ^b` induced by the identification `a = b`. -/
noncomputable def castMap {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b) :
    C(B × EuclideanSpace ℝ (Fin a), B × EuclideanSpace ℝ (Fin b)) :=
  ⟨fun x => (x.1, castCLE h x.2),
    continuous_fst.prodMk ((castCLE h).continuous.comp continuous_snd)⟩

@[simp] theorem castMap_apply {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin a)) :
    castMap h x = (x.1, castCLE h x.2) := rfl

@[simp] theorem castMap_id {B : Type} [TopologicalSpace B] {a : ℕ} :
    castMap (rfl : a = a) = ContinuousMap.id (B × EuclideanSpace ℝ (Fin a)) := by
  ext x <;> rfl

theorem castMap_mem_punct {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b) :
    ∀ x ∈ Work.Thom.Punct B a, castMap h x ∈ Work.Thom.Punct B b := by
  intro x hx h0
  exact hx ((castCLE_eq_zero_iff h x.2).mp h0)

theorem castMap_punct_iff {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin a)) :
    castMap h x ∈ Work.Thom.Punct B b ↔ x ∈ Work.Thom.Punct B a := by
  exact not_congr (castCLE_eq_zero_iff h x.2)

/-- **The model class is invariant under the degree cast.** -/
theorem Mpun_cast {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b) :
    (h ▸ (Work.Thom.Mpun a B) : Work.Thom.RelCoh ℤ b (B × EuclideanSpace ℝ (Fin b))
      (Work.Thom.Punct B b)) = Work.Thom.Mpun b B := by
  cases h
  rfl

/-- **The model class is invariant under `castMap`**: the pullback along the cast identification of
the fibres is the same model class, transported in degree. -/
theorem Mpun_castMap {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b) :
    (Work.Thom.relCohMap (castMap h) (Work.Thom.Punct B a) (Work.Thom.Punct B b)
        (castMap_mem_punct h) ℤ b).hom (Work.Thom.Mpun b B)
      = (h ▸ (Work.Thom.Mpun a B) : Work.Thom.RelCoh ℤ b (B × EuclideanSpace ℝ (Fin a))
          (Work.Thom.Punct B a)) := by
  cases h
  rw [Work.Thom.relCohMap_congrA (Work.Thom.Punct B a) (Work.Thom.Punct B a) castMap_id
    (castMap_mem_punct rfl) (fun _ hx => hx) ℤ a]
  rw [Work.Thom.relCohMap_idA (Work.Thom.Punct B a) ℤ a]
  rfl

/-- **The pullback commutes with the transport along an equality of the relative sets**, for a
fixed source set `Z₀` (so that the two pullbacks have the same codomain and no cast is needed). -/
theorem relCohMap_cast_set {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {S S' : Set Y} (h : S = S') {Z₀ : Set X} {k : ℕ} (hm : ∀ x ∈ Z₀, f x ∈ S)
    (hm' : ∀ x ∈ Z₀, f x ∈ S') (x : Work.Thom.RelCoh ℤ k Y S) :
    (Work.Thom.relCohMap f Z₀ S' hm' ℤ k).hom (h ▸ x)
      = (Work.Thom.relCohMap f Z₀ S hm ℤ k).hom x := by
  cases h
  rw [Work.Thom.relCohMap_hcongrA f Z₀ S hm hm' ℤ k]

/-- A degree cast cancels with its reverse. -/
theorem cast_cast_symm {α : ℕ → Type} {a b : ℕ} (h : a = b) (x : α a) :
    (h.symm ▸ (h ▸ x)) = x := by
  cases h
  rfl

theorem cast_symm_cast {α : ℕ → Type} {a b : ℕ} (h : a = b) (y : α b) :
    (h ▸ (h.symm ▸ y)) = y := by
  cases h
  rfl

end Casts


/-! ## The chart identity: the comparison maps

The chart class of the realified sum over `W ⊆ (Z₁ ⊕ Z₂)_ℝ.baseSet (k₁,k₂)` is the pullback of the
model class `Mpun (2*(m₁+m₂))` along the chart homeomorphism of the sum; the relative–relative cup
of the two pulled-back Thom classes is, after pulling back along the *product* of the two chart
homeomorphisms, the model product formula over `↥W`.  The two comparison maps are

* `wsumPhi W` — `↥W × (ℝ^{2m₁} × ℝ^{2m₂}) → ↥W × ℝ^{2(m₁+m₂)}`, the coordinate identification
  `(b, (v₁,v₂)) ↦ (b, cast (v₁ ++ v₂))` (the cast being the identity on coordinates), and
* `wsumQ hm₁ hm₂ k W hW` — its inverse composed with the chart homeomorphism of the sum, a
  homeomorphism `↥W × (ℝ^{2m₁} × ℝ^{2m₂}) ≅ (Z₁ ⊕ Z₂)_ℝ|_W`.
-/

section ChartIdentity

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
variable {Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁}
variable {Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂}

/-- The comparison map `↥W × (ℝ^{2m₁} × ℝ^{2m₂}) → ↥W × ℝ^{2(m₁+m₂)}` of the chart identity. -/
noncomputable def wsumPhi (W : Set B) :
    C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂),
      ↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂)))) :=
  (castMap (Nat.mul_add 2 m₁ m₂).symm).comp (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))

theorem wsumPhi_apply (W : Set B) (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    wsumPhi W x =
      (x.1, castCLE (Nat.mul_add 2 m₁ m₂).symm
        (Work.Whitney.tcmSumLin (2 * m₁) (2 * m₂) x.2)) := rfl

/-- The second coordinate of the comparison map. -/
theorem wsumPhi_snd (W : Set B) (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    (wsumPhi W x).2 = castCLE (Nat.mul_add 2 m₁ m₂).symm
      (Work.Whitney.tcmSumLin (2 * m₁) (2 * m₂) x.2) := rfl

/-- **The comparison map of the chart identity is a map of the punctured models.** -/
theorem wsumPhi_mem (W : Set B) :
    ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
        ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      wsumPhi W x ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) := by
  intro x hx h0
  have hx' : Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂) x
      ∈ Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂) := by
    rwa [← Work.Whitney.tcmF_preimage_punct] at hx
  have h0' : (wsumPhi W x).2 = 0 := h0
  rw [wsumPhi_apply] at h0'
  exact hx' ((castCLE_eq_zero_iff (Nat.mul_add 2 m₁ m₂).symm
    (Work.Whitney.tcmSumLin (2 * m₁) (2 * m₂) x.2)).mp h0')

/-- The chart homeomorphism of the realified sum, in the form of a homeomorphism onto the chart
`↥W × ℝ^{2(m₁+m₂)}`. -/
noncomputable def wsumChartHomeo (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)
      ≃ₜ (↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂)))) :=
  Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) (2 * (m₁ + m₂))
    (Work.Thom.covE (m := m₁ + m₂)) k W hW

/-- The comparison homeomorphism `↥W × (ℝ^{2m₁} × ℝ^{2m₂}) ≅ (Z₁ ⊕ Z₂)_ℝ|_W`: the inverse of the
chart homeomorphism of the realified sum, composed with `wsumPhi`. -/
noncomputable def wsumQ (_hm₁ : 1 ≤ m₁) (_hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂),
      ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)) :=
  (((wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW).symm :
      C(↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂))),
        ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))).comp
    (wsumPhi W))

/-- **The defining equation of the comparison homeomorphism**: the chart of the realified sum
composed with `wsumQ` is the coordinate identification `wsumPhi`. -/
theorem wsumQ_chart (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
      = wsumPhi W x :=
  Homeomorph.apply_symm_apply _ _

/-- If `π` preserves the base point, the base point of `π (wsumQ x)` lies in `W`. -/
theorem wsumQ_map_mem {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace, Z.TotalSpace))
    (hπ : ∀ p : (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (π p).1 = p.1) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    Z.proj (π ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)) ∈ W := by
  have hy : (π ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).1
      = ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).1 := hπ _
  rw [show Z.proj (π ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1))
      = (π ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).1 from rfl, hy]
  exact (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).2

/-- The first-coordinate projection `↥W × (ℝ^{2m₁}×ℝ^{2m₂}) → (Z₁)_ℝ|_W` of the comparison
homeomorphism. -/
noncomputable def wsumQ₁ (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂), ↥((Work.Thom.realification Z₁).proj ⁻¹' W)) :=
  ⟨fun x => ⟨π₁ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1),
      wsumQ_map_mem (Z₁ := Z₁) (Z₂ := Z₂) (Work.Thom.realification Z₁) hm₁ hm₂ π₁
        (fun p => by rw [hπ₁ p]) k W hW x⟩,
    Continuous.subtype_mk
      (((π₁.comp (Work.Thom.subtypeMap
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))).comp
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)).continuous)
      (fun x => wsumQ_map_mem (Z₁ := Z₁) (Z₂ := Z₂) (Work.Thom.realification Z₁) hm₁ hm₂ π₁
        (fun p => by rw [hπ₁ p]) k W hW x)⟩

theorem wsumQ₁_apply (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x).1
      = π₁ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1) := rfl

/-- The second-coordinate projection `↥W × (ℝ^{2m₁}×ℝ^{2m₂}) → (Z₂)_ℝ|_W` of the comparison
homeomorphism. -/
noncomputable def wsumQ₂ (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂), ↥((Work.Thom.realification Z₂).proj ⁻¹' W)) :=
  ⟨fun x => ⟨π₂ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1),
      wsumQ_map_mem (Z₁ := Z₁) (Z₂ := Z₂) (Work.Thom.realification Z₂) hm₁ hm₂ π₂
        (fun p => by rw [hπ₂ p]) k W hW x⟩,
    Continuous.subtype_mk
      (((π₂.comp (Work.Thom.subtypeMap
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))).comp
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)).continuous)
      (fun x => wsumQ_map_mem (Z₁ := Z₁) (Z₂ := Z₂) (Work.Thom.realification Z₂) hm₁ hm₂ π₂
        (fun p => by rw [hπ₂ p]) k W hW x)⟩

theorem wsumQ₂_apply (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x).1
      = π₂ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1) := rfl

end ChartIdentity


/-! ## The coordinate content of the comparison maps

The chart of the realified sum and the charts of the two summands are related by the *sum
compatibility* of the canonical realification (`Work.Gen.rifStd_sum_compatible_cast`): the fibre
coordinate of the sum in its chart is the interleaving of the two summands' fibre coordinates.
Concretely, `wsumQ₁_coord` and `wsumQ₂_coord` identify the chart coordinates of the comparison
image with the coordinates of the model space, i.e. `c₁ ∘ wsumQ₁ = tcmPr1` and
`c₂ ∘ wsumQ₂ = tcmPr2`.
-/

section ChartCoords

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
variable {Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁}
variable {Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂}

/-- The base set of the realified sum is the intersection of the base sets of the summands. -/
theorem wsum_sub_base₁ {k : ι₁ × ι₂} {W : Set B}
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    W ⊆ (Work.Thom.realification Z₁).baseSet k.1 := by
  intro b hb
  have hb' : b ∈ (Whitney.whitneySum Z₁ Z₂).baseSet k := by
    rw [← Work.Thom.realification_baseSet]
    exact hW hb
  rw [Whitney.whitneySum_baseSet] at hb'
  rw [Work.Thom.realification_baseSet]
  exact hb'.1

theorem wsum_sub_base₂ {k : ι₁ × ι₂} {W : Set B}
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    W ⊆ (Work.Thom.realification Z₂).baseSet k.2 := by
  intro b hb
  have hb' : b ∈ (Whitney.whitneySum Z₁ Z₂).baseSet k := by
    rw [← Work.Thom.realification_baseSet]
    exact hW hb
  rw [Whitney.whitneySum_baseSet] at hb'
  rw [Work.Thom.realification_baseSet]
  exact hb'.2

/-- The second component of a chart homeomorphism: the fibre coordinate in the chart. -/
theorem chartHomeo_snd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) (p : ↥(Z.proj ⁻¹' W)) :
    (Work.Thom.chartHomeo Z n e i W hW p).2 =
      e (Z.coordChange (Z.indexAt (p : Z.TotalSpace).1) i (p : Z.TotalSpace).1
        (p : Z.TotalSpace).2) :=
  congrArg Prod.snd (Work.Thom.chartHomeo_apply Z n e i W hW p)

/-- The second component of the chart homeomorphism of the realified sum. -/
theorem wsumChartHomeo_snd (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (p : ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)) :
    (wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW p).2 =
      Work.Thom.covE (m := m₁ + m₂)
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).coordChange
          ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).indexAt
            (p : (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace).1) k
          (p : (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace).1
          (p : (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace).2) :=
  congrArg Prod.snd (Work.Thom.chartHomeo_apply (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
    (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW p)

/-- The transition function of the realified sum, in terms of the summands. -/
theorem wsumR_coordChange_eq (k : ι₁ × ι₂) (b : B)
    (v : EuclideanSpace ℂ (Fin (m₁ + m₂))) :
    (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).coordChange
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).indexAt b) k b v
      = Whitney.sumFibreC m₁ m₂
          ((Z₁.coordChange (Z₁.indexAt b) k.1 b) ((Whitney.sumFibreC m₁ m₂).symm v).1,
           (Z₂.coordChange (Z₂.indexAt b) k.2 b) ((Whitney.sumFibreC m₁ m₂).symm v).2) := by
  set w := (Whitney.sumFibreC m₁ m₂).symm v with hw
  have hw' : (Whitney.sumFibreC m₁ m₂).symm v = (w.1, w.2) := by
    rw [← hw]
  have h1 : ⇑((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).coordChange
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).indexAt b) k b)
      = ⇑((Whitney.whitneySum Z₁ Z₂).coordChange
        ((Whitney.whitneySum Z₁ Z₂).indexAt b) k b) := by
    rw [Work.Thom.realification_indexAt]
    exact Work.Thom.realification_coordChange (Whitney.whitneySum Z₁ Z₂)
      ((Whitney.whitneySum Z₁ Z₂).indexAt b) k b
  show (⇑((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).coordChange
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).indexAt b) k b)) v = _
  rw [h1, Whitney.whitneySum_indexAt, Whitney.whitneySum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    ContinuousLinearEquiv.coe_coe, hw']
  rw [show ∀ p : EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂),
      Prod.map (⇑(Z₁.coordChange (Z₁.indexAt b) k.1 b)) (⇑(Z₂.coordChange (Z₂.indexAt b) k.2 b)) p
        = ((Z₁.coordChange (Z₁.indexAt b) k.1 b) p.1,
            (Z₂.coordChange (Z₂.indexAt b) k.2 b) p.2) from fun p => by cases p; rfl]

/-- The transition function of a summand, read through the realification. -/
theorem wsumR₁_coordChange_eq (k : ι₁ × ι₂) (b : B) (v : EuclideanSpace ℂ (Fin m₁)) :
    (Work.Thom.realification Z₁).coordChange ((Work.Thom.realification Z₁).indexAt b) k.1 b v
      = Z₁.coordChange (Z₁.indexAt b) k.1 b v := by
  rw [Work.Thom.realification_indexAt]
  exact congrFun (Work.Thom.realification_coordChange Z₁ (Z₁.indexAt b) k.1 b) v

theorem wsumR₂_coordChange_eq (k : ι₁ × ι₂) (b : B) (v : EuclideanSpace ℂ (Fin m₂)) :
    (Work.Thom.realification Z₂).coordChange ((Work.Thom.realification Z₂).indexAt b) k.2 b v
      = Z₂.coordChange (Z₂.indexAt b) k.2 b v := by
  rw [Work.Thom.realification_indexAt]
  exact congrFun (Work.Thom.realification_coordChange Z₂ (Z₂.indexAt b) k.2 b) v

/-- **The sum compatibility of the canonical realification**, in the form used by the chart
identity: the realification of the sum's coordinate is the real splitting of the summands'. -/
theorem wsum_realification_sum_compatible (k : ι₁ × ι₂) (b : B)
    (u : EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)) :
    castCLE (Nat.mul_add 2 m₁ m₂)
        (Work.Thom.covE (m := m₁ + m₂) (Whitney.sumFibreC m₁ m₂ u))
      = Whitney.sumFibreR (2 * m₁) (2 * m₂)
          (Work.Thom.covE (m := m₁) u.1, Work.Thom.covE (m := m₂) u.2) := by
  rw [castCLE_apply]
  exact Work.Gen.rifStd_sum_compatible_cast m₁ m₂ u

/-- **The first coordinate of the comparison image**: the chart coordinate of `π₁ (wsumQ x)` is the
first coordinate of `x`. -/
theorem wsumQ₁_coord (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    (Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
      k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)
      (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)).2 = x.2.1 := by
  -- the chart identity at the chart of the realified sum
  have hchart := wsumChartHomeo_snd (Z₁ := Z₁) (Z₂ := Z₂) k W hW
    (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
  rw [wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x] at hchart
  rw [wsumPhi_snd W x] at hchart
  rw [wsumR_coordChange_eq (Z₁ := Z₁) (Z₂ := Z₂) k
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)] at hchart
  -- cast both sides to `ℝ^{2m₁+2m₂}` and use the sum compatibility of the realification
  have hcast := congrArg (castCLE (Nat.mul_add 2 m₁ m₂)) hchart
  rw [castCLE_apply_castCLE_symm] at hcast
  have hcompat := wsum_realification_sum_compatible k
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)
    ((Z₁.coordChange (Z₁.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.1
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
      ((Whitney.sumFibreC m₁ m₂).symm
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).1,
     (Z₂.coordChange (Z₂.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.2
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
      ((Whitney.sumFibreC m₁ m₂).symm
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).2)
  have hfinal : Whitney.sumFibreR (2 * m₁) (2 * m₂)
      (Work.Thom.covE (m := m₁)
          ((Z₁.coordChange (Z₁.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.1
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
            ((Whitney.sumFibreC m₁ m₂).symm
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).1),
        Work.Thom.covE (m := m₂)
          ((Z₂.coordChange (Z₂.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.2
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
            ((Whitney.sumFibreC m₁ m₂).symm
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).2))
      = Whitney.sumFibreR (2 * m₁) (2 * m₂) (x.2.1, x.2.2) := by
    rw [← hcompat, ← hcast]
    rfl
  have hcov : Work.Thom.covE (m := m₁)
      ((Z₁.coordChange (Z₁.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.1
          ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
        ((Whitney.sumFibreC m₁ m₂).symm
          ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).1) = x.2.1 :=
    congrArg Prod.fst ((Whitney.sumFibreR (2 * m₁) (2 * m₂)).injective hfinal)
  -- the chart formula of the first summand
  rw [chartHomeo_snd, wsumQ₁_apply]
  rw [show (π₁ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).1
      = ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).1 from by rw [hπ₁]]
  rw [show (π₁ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).2
      = ((Whitney.sumFibreC m₁ m₂).symm
          ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).2).1 from by rw [hπ₁]]
  rw [wsumR₁_coordChange_eq (Z₁ := Z₁) k
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)
    ((Whitney.sumFibreC m₁ m₂).symm
      ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).1]
  exact hcov


/-- **The second coordinate of the comparison image**: the chart coordinate of `π₂ (wsumQ x)` is
the second coordinate of `x`. -/
theorem wsumQ₂_coord (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    (Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
      k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)
      (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)).2 = x.2.2 := by
  have hchart := wsumChartHomeo_snd (Z₁ := Z₁) (Z₂ := Z₂) k W hW
    (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
  rw [wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x] at hchart
  rw [wsumPhi_snd W x] at hchart
  rw [wsumR_coordChange_eq (Z₁ := Z₁) (Z₂ := Z₂) k
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)] at hchart
  have hcast := congrArg (castCLE (Nat.mul_add 2 m₁ m₂)) hchart
  rw [castCLE_apply_castCLE_symm] at hcast
  have hcompat := wsum_realification_sum_compatible k
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)
    ((Z₁.coordChange (Z₁.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.1
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
      ((Whitney.sumFibreC m₁ m₂).symm
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).1,
     (Z₂.coordChange (Z₂.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.2
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
      ((Whitney.sumFibreC m₁ m₂).symm
        ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).2)
  have hfinal : Whitney.sumFibreR (2 * m₁) (2 * m₂)
      (Work.Thom.covE (m := m₁)
          ((Z₁.coordChange (Z₁.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.1
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
            ((Whitney.sumFibreC m₁ m₂).symm
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).1),
        Work.Thom.covE (m := m₂)
          ((Z₂.coordChange (Z₂.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.2
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
            ((Whitney.sumFibreC m₁ m₂).symm
              ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).2))
      = Whitney.sumFibreR (2 * m₁) (2 * m₂) (x.2.1, x.2.2) := by
    rw [← hcompat, ← hcast]
    rfl
  have hcov : Work.Thom.covE (m := m₂)
      ((Z₂.coordChange (Z₂.indexAt ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)) k.2
          ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1))
        ((Whitney.sumFibreC m₁ m₂).symm
          ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).2) = x.2.2 :=
    congrArg Prod.snd ((Whitney.sumFibreR (2 * m₁) (2 * m₂)).injective hfinal)
  rw [chartHomeo_snd, wsumQ₂_apply]
  rw [show (π₂ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).1
      = ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).1 from by rw [hπ₂]]
  rw [show (π₂ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).2
      = ((Whitney.sumFibreC m₁ m₂).symm
          ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).2).2 from by rw [hπ₂]]
  rw [wsumR₂_coordChange_eq (Z₂ := Z₂) k
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.1)
    ((Whitney.sumFibreC m₁ m₂).symm
      ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1.2)).2]
  exact hcov


end ChartCoords


/-! ## The pair conditions of the comparison maps

The comparison homeomorphism `wsumQ` maps the punctured model space to the punctured part of the
realified sum, and the chart coordinates of its first and second coordinates are the coordinates of
the model space (`wsumQ₁_coord`, `wsumQ₂_coord`); together with the chart criterion
(`chartHomeo_mem_punct`) this gives the pair conditions used in the chart identity.
-/

section PairConds

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
variable {Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁}
variable {Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂}

/-- The pullback commutes with the transport along an equality of the *target* pair-set, for an
arbitrary source set. -/
theorem relCohMap_cast_target_set {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {S S' : Set Y} (h : S = S') (B : Set X)
    (hm : ∀ x ∈ B, f x ∈ S) (hm' : ∀ x ∈ B, f x ∈ S') {k : ℕ}
    (x : Work.Thom.RelCoh ℤ k Y S) :
    (Work.Thom.relCohMap f B S' hm' ℤ k).hom (h ▸ x)
      = (Work.Thom.relCohMap f B S hm ℤ k).hom x := by
  cases h
  rw [Work.Thom.relCohMap_hcongrA f B S hm hm' ℤ k]

/-- The chart criterion for the chart homeomorphism of the realified sum. -/
theorem wsumChartHomeo_mem_punct (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (p : ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)) :
    p ∈ Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W
      ↔ wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW p
          ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) :=
  Work.Thom.chartHomeo_mem_punct _ _ _ _ _ _ p

/-- **The comparison map lands in the punctured part of the sum.** -/
theorem wsumQ_mem_zeroComplement (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
        ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x :
        (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace)
        ∈ Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) := by
  intro x hx
  have hmem : wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW
      (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
      ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) := by
    rw [wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x]
    exact wsumPhi_mem W x hx
  exact (wsumChartHomeo_mem_punct (Z₁ := Z₁) (Z₂ := Z₂) k W hW
    (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)).mpr hmem

/-- The fibre coordinate of the first coordinate of the comparison point is nonzero in the first
chart. -/
theorem wsumQ₁_fibre_ne_zero (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂))
    (hx : x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)) :
    ((wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x :
      (Work.Thom.realification Z₁).TotalSpace))
      ∈ Work.Thom.zeroComplement (Work.Thom.realification Z₁) := by
  have hc : Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
      k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)
      (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)
      ∈ Work.Thom.Punct ↥W (2 * m₁) := by
    show (Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
      k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)
      (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)).2 ≠ 0
    rw [wsumQ₁_coord (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x]
    exact hx
  have hpiece := (Work.Thom.chartHomeo_mem_punct (Work.Thom.realification Z₁) (2 * m₁)
    (Work.Thom.covE (m := m₁)) k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)
    (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)).mpr hc
  exact hpiece

/-- The fibre coordinate of the second coordinate of the comparison point is nonzero in the second
chart. -/
theorem wsumQ₂_fibre_ne_zero (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂))
    (hx : x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂)) :
    ((wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x :
      (Work.Thom.realification Z₂).TotalSpace))
      ∈ Work.Thom.zeroComplement (Work.Thom.realification Z₂) := by
  have hc : Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
      k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)
      (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)
      ∈ Work.Thom.Punct ↥W (2 * m₂) := by
    show (Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
      k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)
      (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)).2 ≠ 0
    rw [wsumQ₂_coord (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x]
    exact hx
  have hpiece := (Work.Thom.chartHomeo_mem_punct (Work.Thom.realification Z₂) (2 * m₂)
    (Work.Thom.covE (m := m₂)) k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)
    (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)).mpr hc
  exact hpiece

/-- The first coordinate of the comparison point lies in the first summand's piece. -/
theorem wsumQ₁_mem_pieceZero (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)
        ∈ Work.Thom.pieceZero (Work.Thom.realification Z₁) W :=
  fun x hx =>
    wsumQ₁_fibre_ne_zero (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x hx

/-- The second coordinate of the comparison point lies in the second summand's piece. -/
theorem wsumQ₂_mem_pieceZero (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)
        ∈ Work.Thom.pieceZero (Work.Thom.realification Z₂) W :=
  fun x hx =>
    wsumQ₂_fibre_ne_zero (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x hx

end PairConds


/-! ## The comparison homeomorphism

`wsumQ` is a homeomorphism onto its image; recording it as such gives the injectivity of the
pullback used to compare the two sides of the chart identity.
-/

section ChartHomeo

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
variable {Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁}
variable {Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂}

/-- The homeomorphism `ℝ^a ≅ ℝ^b` induced by `h : a = b`. -/
noncomputable def castHomeo {a b : ℕ} (h : a = b) :
    EuclideanSpace ℝ (Fin a) ≃ₜ EuclideanSpace ℝ (Fin b) where
  toFun := castCLE h
  invFun := (castCLE h).symm
  left_inv := (castCLE h).left_inv
  right_inv := (castCLE h).right_inv
  continuous_toFun := (castCLE h).continuous
  continuous_invFun := (castCLE h).symm.continuous

@[simp] theorem castHomeo_apply {a b : ℕ} (h : a = b) (x : EuclideanSpace ℝ (Fin a)) :
    castHomeo h x = castCLE h x := rfl

/-- The homeomorphism `B × ℝ^a ≅ B × ℝ^b` induced by `h : a = b`. -/
noncomputable def castMapHomeo {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b) :
    (B × EuclideanSpace ℝ (Fin a)) ≃ₜ (B × EuclideanSpace ℝ (Fin b)) :=
  Homeomorph.prodCongr (Homeomorph.refl B) (castHomeo h)

@[simp] theorem castMapHomeo_apply {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin a)) :
    castMapHomeo h x = castMap h x := rfl

/-- The comparison map `wsumPhi` as a homeomorphism. -/
noncomputable def wsumPhiHomeo (W : Set B) :
    Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂) ≃ₜ
      (↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂)))) :=
  (Work.Whitney.tcmFHomeo (B := ↥W) (2 * m₁) (2 * m₂)).trans
    (castMapHomeo (Nat.mul_add 2 m₁ m₂).symm)

theorem wsumPhiHomeo_apply (W : Set B) (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    wsumPhiHomeo W x = wsumPhi W x := rfl

/-- **The comparison map `wsumQ` as a homeomorphism** from the punctured model space onto the
piece of the realified sum over `W`. -/
noncomputable def wsumQHomeo (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)
      ≃ₜ ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W) :=
  (wsumPhiHomeo W).trans (wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW).symm

theorem wsumQHomeo_apply (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    wsumQHomeo (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
      = wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x := rfl

/-- The pair condition of the comparison homeomorphism, in both directions. -/
theorem wsumQ_mem_zeroComplement_iff (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
        ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂)
      ↔ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x :
          (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace))
          ∈ Work.Thom.zeroComplement
              (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) := by
  constructor
  · intro hx
    have hmem : wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
        ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) := by
      rw [wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x]
      exact wsumPhi_mem W x hx
    exact (wsumChartHomeo_mem_punct (Z₁ := Z₁) (Z₂ := Z₂) k W hW
      (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)).mpr hmem
  · intro hx
    have hmem : wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
        ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) :=
      (wsumChartHomeo_mem_punct (Z₁ := Z₁) (Z₂ := Z₂) k W hW
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)).mp hx
    have hmem' : wsumPhi W x ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) := by
      rw [← wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x]
      exact hmem
    have hmem2 : (wsumPhi W x).2 ≠ 0 := hmem'
    rw [wsumPhi_snd W x] at hmem2
    rw [← Work.Whitney.tcmF_preimage_punct]
    show Work.Whitney.tcmSumLin (2 * m₁) (2 * m₂) x.2 ≠ 0
    intro h0
    exact hmem2 (by rw [h0, castCLE_zero])

end ChartHomeo


/-! ## The restriction of a global Thom class to one of its charts

`Work.Thom.thomClassRank` is built from the local chart data `localThomOfComplexCover`; this section
records that its restriction to the piece over a subset of a chart is the explicit chart class
`localThomOfChart`.
-/

section ThomRestrict

variable {B : Type} [TopologicalSpace B]
variable {m : ℕ} {ι : Type} [Fintype ι]
variable {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι}

/-- The inclusion of the pieces over `W ⊆ U` inside the space of the whole bundle, for the piece of
the realification of a complex bundle. -/
theorem subtypeMap_proj_comp_pieceIncl {W U : Set B} (hWU : W ⊆ U) :
    (Work.Thom.subtypeMap ((Work.Thom.realification Z).proj ⁻¹' W))
      = (Work.Thom.subtypeMap ((Work.Thom.realification Z).proj ⁻¹' U)).comp
          (Work.Thom.pieceIncl (Work.Thom.realification Z) W U hWU) := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- **The restriction of the global Thom class of a realified complex bundle to a chart is the
explicit chart class.** -/
theorem thomClassRank_restrict_chart (hm : 1 ≤ m) (i : ι) {W : Set B}
    (hW : W ⊆ (Work.Thom.realification Z).baseSet i) :
    (Work.Thom.relCohMap (Work.Thom.subtypeMap ((Work.Thom.realification Z).proj ⁻¹' W))
        (Work.Thom.pieceZero (Work.Thom.realification Z) W)
        (Work.Thom.zeroComplement (Work.Thom.realification Z)) (fun _ hx => hx) ℤ (2 * m)).hom
        ((Work.Thom.thomClassRank m hm Z).τ)
      = (Work.Thom.localThomOfChart (Work.Thom.realification Z) (2 * m)
          (Work.Thom.covE (m := m)) i W hW).τ := by
  rw [Work.Thom.thomClassRank_def]
  -- express the pullback along the subtype inclusion of `↥(proj⁻¹W)` through the whole space
  have hmap : (Work.Thom.subtypeMap
        ((Work.Thom.realification Z).proj ⁻¹' (Set.univ : Set B)))
      = (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((Work.Thom.realification Z).proj ⁻¹' (Set.univ : Set B)),
            (Work.Thom.realification Z).TotalSpace)) := by
    apply ContinuousMap.ext
    intro y
    rfl
  rw [Work.Thom.relCohMap_congrA (Work.Thom.pieceZero (Work.Thom.realification Z) W)
    (Work.Thom.zeroComplement (Work.Thom.realification Z))
    (Work.Whitney.subtypeMap_proj_comp_pieceIncl (Z := Z) (U := Set.univ) (W := W)
      (fun _ _ => Set.mem_univ _))
    (fun _ hx => hx) (fun _ hx => hx) ℤ (2 * m)]
  rw [← Work.Thom.relCohMap_compA_apply (Work.Thom.pieceZero (Work.Thom.realification Z) W)
    (Work.Thom.pieceZero (Work.Thom.realification Z) Set.univ)
    (Work.Thom.zeroComplement (Work.Thom.realification Z))
    (Work.Thom.pieceIncl (Work.Thom.realification Z) W Set.univ (fun _ _ => Set.mem_univ _))
    (Work.Thom.subtypeMap ((Work.Thom.realification Z).proj ⁻¹' (Set.univ : Set B)))
    (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℤ (2 * m)
    ((Work.Thom.thomClassOf hm Z).τ)]
  -- the inner term is the local data over the whole base
  have hinner : (Work.Thom.relCohMap
        (Work.Thom.subtypeMap ((Work.Thom.realification Z).proj ⁻¹' (Set.univ : Set B)))
        (Work.Thom.pieceZero (Work.Thom.realification Z) Set.univ)
        (Work.Thom.zeroComplement (Work.Thom.realification Z)) (fun _ hx => hx) ℤ (2 * m)).hom
        ((Work.Thom.thomClassOf hm Z).τ)
      = (Work.Thom.localThomOfComplexCover hm Z).τ := by
    rw [Work.Thom.relCohMap_congrA (Work.Thom.pieceZero (Work.Thom.realification Z) Set.univ)
      (Work.Thom.zeroComplement (Work.Thom.realification Z)) hmap
      (fun _ hx => hx) (fun _ hx => hx) ℤ (2 * m)]
    exact Work.Thom.thomClassOf_spec hm Z
  rw [hinner]
  rw [← Work.Thom.pdCohMap_eq_relCohMap (Work.Thom.realification Z) W Set.univ
    (fun _ _ => Set.mem_univ _) (2 * m)]
  exact Work.Thom.localThomOfComplexCover_pdCohMap_subset hm Z i hW

end ThomRestrict


/-! ## The chart identity: the coordinate maps

`wsumQ₁_coord` and `wsumQ₂_coord` identify the *fibre* coordinates of the chart images with the
coordinates of the model space; here they are upgraded to the statements that the charts of the two
summands composed with `wsumQ₁`/`wsumQ₂` are the projections `tcmPr1`/`tcmPr2` of the model space.
-/

section CoordMaps

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
variable {Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁}
variable {Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂}

/-- The base point of the comparison image is the base point of the model space. -/
theorem wsumQ_base (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x :
      (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace).1) = x.1.1 := by
  have h1 : ((wsumChartHomeo (Z₁ := Z₁) (Z₂ := Z₂) k W hW
      (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)).1 : B)
      = ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x :
          (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace).1) := rfl
  rw [wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x] at h1
  rw [← h1]
  show (wsumPhi W x).1.1 = x.1.1
  rw [wsumPhi_apply]

/-- The base point of the first coordinate of the comparison image. -/
theorem wsumQ₁_base (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    ((wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x :
      (Work.Thom.realification Z₁).TotalSpace).1) = x.1.1 := by
  rw [wsumQ₁_apply]
  rw [show (π₁ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).1
      = ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).1 from by rw [hπ₁]]
  exact wsumQ_base (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x

/-- The base point of the second coordinate of the comparison image. -/
theorem wsumQ₂_base (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    ((wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x :
      (Work.Thom.realification Z₂).TotalSpace).1) = x.1.1 := by
  rw [wsumQ₂_apply]
  rw [show (π₂ ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1)).1
      = ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).1).1 from by rw [hπ₂]]
  exact wsumQ_base (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x

/-- **The chart of the first summand composed with `wsumQ₁` is `tcmPr1`.** -/
theorem wsumChartHomeo_comp_wsumQ₁ (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ((Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
        k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW) :
        C(↥((Work.Thom.realification Z₁).proj ⁻¹' W),
          ↥W × EuclideanSpace ℝ (Fin (2 * m₁)))).comp
      (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW))
      = Work.Whitney.tcmPr1 ↥W (2 * m₁) (2 * m₂) := by
  apply ContinuousMap.ext
  intro x
  refine Prod.ext ?_ (wsumQ₁_coord (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)
  apply Subtype.ext
  show (Work.Thom.realification Z₁).proj
      ((wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x :
        ↥((Work.Thom.realification Z₁).proj ⁻¹' W)).1) = x.1.1
  exact wsumQ₁_base (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x

/-- **The chart of the second summand composed with `wsumQ₂` is `tcmPr2`.** -/
theorem wsumChartHomeo_comp_wsumQ₂ (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ((Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
        k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW) :
        C(↥((Work.Thom.realification Z₂).proj ⁻¹' W),
          ↥W × EuclideanSpace ℝ (Fin (2 * m₂)))).comp
      (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW))
      = Work.Whitney.tcmPr2 ↥W (2 * m₁) (2 * m₂) := by
  apply ContinuousMap.ext
  intro x
  refine Prod.ext ?_ (wsumQ₂_coord (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)
  apply Subtype.ext
  show (Work.Thom.realification Z₂).proj
      ((wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x :
        ↥((Work.Thom.realification Z₂).proj ⁻¹' W)).1) = x.1.1
  exact wsumQ₂_base (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x

end CoordMaps


/-! ## The first factor of the chart identity

The pullback of `wsumRelTau1` (the Thom class of `Z₁` pulled back to the total space of the sum) along
the comparison map is the pullback of the model class of rank `2*m₁` along `tcmPr1`.
-/

section FactorOne

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
variable {Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁}
variable {Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂}

/-- The comparison map `f = subtypeMap ∘ wsumQ` of the chart identity. -/
noncomputable def wsumF (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂),
      (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace) :=
  (Work.Thom.subtypeMap
    ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
    (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)

theorem wsumF_apply (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (x : Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂)) :
    wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
      = (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x :
          (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace) := rfl

/-- The first projection composed with `wsumF` is the subtype inclusion of the first summand's
piece composed with `wsumQ₁`. -/
theorem wsumPr1_comp_wsumF (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    π₁.comp (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
      = (Work.Thom.subtypeMap ((Work.Thom.realification Z₁).proj ⁻¹' W)).comp
          (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW) := by
  apply ContinuousMap.ext
  intro x
  rfl

theorem wsumPr2_comp_wsumF (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    π₂.comp (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
      = (Work.Thom.subtypeMap ((Work.Thom.realification Z₂).proj ⁻¹' W)).comp
          (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW) := by
  apply ContinuousMap.ext
  intro x
  rfl


/-- **The first factor of the chart identity.** -/
theorem relCohMap_wsumRelTau1 (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (hmA : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) :
    (Work.Thom.relCohMap (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
        (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) hmA ℤ (2 * m₁)).hom
        (Work.Whitney.wsumRelTau1 hm₁ Z₁ Z₂ π₁)
      = (Work.Thom.relCohMap (Work.Whitney.tcmPr1 ↥W (2 * m₁) (2 * m₂))
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.Punct ↥W (2 * m₁)) (fun _ hx => hx) ℤ (2 * m₁)).hom
          (Work.Thom.Mpun (2 * m₁) ↥W) := by
  have hmap1 : π₁.comp (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
      = (Work.Thom.subtypeMap ((Work.Thom.realification Z₁).proj ⁻¹' W)).comp
          (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW) :=
    wsumPr1_comp_wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW
  have hf1 : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)
        ∈ Work.Thom.pieceZero (Work.Thom.realification Z₁) W :=
    wsumQ₁_mem_pieceZero (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW
  have hgf1 : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      (Work.Thom.subtypeMap ((Work.Thom.realification Z₁).proj ⁻¹' W))
        (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x)
        ∈ Work.Thom.zeroComplement (Work.Thom.realification Z₁) :=
    fun x hx => hf1 x hx
  have hcc : ∀ y ∈ Work.Thom.pieceZero (Work.Thom.realification Z₁) W,
      (Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
        k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)) y
        ∈ Work.Thom.Punct ↥W (2 * m₁) :=
    Work.Thom.chartHomeo_mem (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
      k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)
  have hq1p : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      ((Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
        k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW) :
          C(↥((Work.Thom.realification Z₁).proj ⁻¹' W),
            ↥W × EuclideanSpace ℝ (Fin (2 * m₁)))).comp
        (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW)) x
        ∈ Work.Thom.Punct ↥W (2 * m₁) :=
    fun x hx => hcc _ (hf1 x hx)
  have hτ : (Work.Whitney.wsumRelTau1 hm₁ Z₁ Z₂ π₁)
      = (Work.Thom.relCohMap π₁ (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁)
          (Work.Thom.zeroComplement (Work.Thom.realification Z₁)) (fun _ hx => hx) ℤ (2 * m₁)).hom
          (Work.Thom.thomClassRank m₁ hm₁ Z₁).τ := rfl
  rw [hτ]
  rw [Work.Thom.relCohMap_compA_apply (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
    (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) (Work.Thom.zeroComplement (Work.Thom.realification Z₁))
    (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW) π₁ hmA (fun _ hx => hx) hmA
    ℤ (2 * m₁) (Work.Thom.thomClassRank m₁ hm₁ Z₁).τ]
  have hstep2 := congrArg (fun φ => φ.hom (Work.Thom.thomClassRank m₁ hm₁ Z₁).τ)
    (Work.Thom.relCohMap_congrA (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
      (Work.Thom.zeroComplement (Work.Thom.realification Z₁)) hmap1 hmA hgf1 ℤ (2 * m₁))
  rw [hstep2]
  rw [← Work.Thom.relCohMap_compA_apply (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
    (Work.Thom.pieceZero (Work.Thom.realification Z₁) W)
    (Work.Thom.zeroComplement (Work.Thom.realification Z₁))
    (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW)
    (Work.Thom.subtypeMap ((Work.Thom.realification Z₁).proj ⁻¹' W))
    hf1 (fun _ hx => hx) hgf1 ℤ (2 * m₁) (Work.Thom.thomClassRank m₁ hm₁ Z₁).τ]
  rw [Work.Whitney.thomClassRank_restrict_chart (Z := Z₁) hm₁ k.1
    (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)]
  rw [Work.Thom.localThomOfChart_tau (Work.Thom.realification Z₁) (2 * m₁)
    (Work.Thom.covE (m := m₁)) k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW)]
  rw [Work.Thom.relCohMap_compA_apply (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
    (Work.Thom.pieceZero (Work.Thom.realification Z₁) W) (Work.Thom.Punct ↥W (2 * m₁))
    (wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW)
    ((Work.Thom.chartHomeo (Work.Thom.realification Z₁) (2 * m₁) (Work.Thom.covE (m := m₁))
      k.1 W (wsum_sub_base₁ (Z₁ := Z₁) (Z₂ := Z₂) hW) :
        C(↥((Work.Thom.realification Z₁).proj ⁻¹' W),
          ↥W × EuclideanSpace ℝ (Fin (2 * m₁)))))
    hf1 hcc hq1p ℤ (2 * m₁) (Work.Thom.Mpun (2 * m₁) ↥W)]
  have hstep7 := congrArg (fun φ => φ.hom (Work.Thom.Mpun (2 * m₁) ↥W))
    (Work.Thom.relCohMap_congrA (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂))
      (Work.Thom.Punct ↥W (2 * m₁))
      (wsumChartHomeo_comp_wsumQ₁ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW)
      hq1p (fun _ hx => hx) ℤ (2 * m₁))
  rw [hstep7]

/-- **The second factor of the chart identity.** -/
theorem relCohMap_wsumRelTau2 (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (hmC : ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) :
    (Work.Thom.relCohMap (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) hmC ℤ (2 * m₂)).hom
        (Work.Whitney.wsumRelTau2 hm₂ Z₁ Z₂ π₂)
      = (Work.Thom.relCohMap (Work.Whitney.tcmPr2 ↥W (2 * m₁) (2 * m₂))
          (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.Punct ↥W (2 * m₂)) (fun _ hx => hx) ℤ (2 * m₂)).hom
          (Work.Thom.Mpun (2 * m₂) ↥W) := by
  have hmap2 : π₂.comp (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
      = (Work.Thom.subtypeMap ((Work.Thom.realification Z₂).proj ⁻¹' W)).comp
          (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW) :=
    wsumPr2_comp_wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW
  have hf2 : ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)
        ∈ Work.Thom.pieceZero (Work.Thom.realification Z₂) W :=
    wsumQ₂_mem_pieceZero (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW
  have hgf2 : ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      (Work.Thom.subtypeMap ((Work.Thom.realification Z₂).proj ⁻¹' W))
        (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x)
        ∈ Work.Thom.zeroComplement (Work.Thom.realification Z₂) :=
    fun x hx => hf2 x hx
  have hcc2 : ∀ y ∈ Work.Thom.pieceZero (Work.Thom.realification Z₂) W,
      (Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
        k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)) y
        ∈ Work.Thom.Punct ↥W (2 * m₂) :=
    Work.Thom.chartHomeo_mem (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
      k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)
  have hq2p : ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      ((Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
        k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW) :
          C(↥((Work.Thom.realification Z₂).proj ⁻¹' W),
            ↥W × EuclideanSpace ℝ (Fin (2 * m₂)))).comp
        (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW)) x
        ∈ Work.Thom.Punct ↥W (2 * m₂) :=
    fun x hx => hcc2 _ (hf2 x hx)
  have hτ : (Work.Whitney.wsumRelTau2 hm₂ Z₁ Z₂ π₂)
      = (Work.Thom.relCohMap π₂ (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
          (Work.Thom.zeroComplement (Work.Thom.realification Z₂)) (fun _ hx => hx) ℤ (2 * m₂)).hom
          (Work.Thom.thomClassRank m₂ hm₂ Z₂).τ := rfl
  rw [hτ]
  rw [Work.Thom.relCohMap_compA_apply (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
    (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) (Work.Thom.zeroComplement (Work.Thom.realification Z₂))
    (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW) π₂ hmC (fun _ hx => hx) hmC
    ℤ (2 * m₂) (Work.Thom.thomClassRank m₂ hm₂ Z₂).τ]
  have hstep2 := congrArg (fun φ => φ.hom (Work.Thom.thomClassRank m₂ hm₂ Z₂).τ)
    (Work.Thom.relCohMap_congrA (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
      (Work.Thom.zeroComplement (Work.Thom.realification Z₂)) hmap2 hmC hgf2 ℤ (2 * m₂))
  rw [hstep2]
  rw [← Work.Thom.relCohMap_compA_apply (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
    (Work.Thom.pieceZero (Work.Thom.realification Z₂) W)
    (Work.Thom.zeroComplement (Work.Thom.realification Z₂))
    (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW)
    (Work.Thom.subtypeMap ((Work.Thom.realification Z₂).proj ⁻¹' W))
    hf2 (fun _ hx => hx) hgf2 ℤ (2 * m₂) (Work.Thom.thomClassRank m₂ hm₂ Z₂).τ]
  rw [Work.Whitney.thomClassRank_restrict_chart (Z := Z₂) hm₂ k.2
    (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)]
  rw [Work.Thom.localThomOfChart_tau (Work.Thom.realification Z₂) (2 * m₂)
    (Work.Thom.covE (m := m₂)) k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW)]
  rw [Work.Thom.relCohMap_compA_apply (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
    (Work.Thom.pieceZero (Work.Thom.realification Z₂) W) (Work.Thom.Punct ↥W (2 * m₂))
    (wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW)
    ((Work.Thom.chartHomeo (Work.Thom.realification Z₂) (2 * m₂) (Work.Thom.covE (m := m₂))
      k.2 W (wsum_sub_base₂ (Z₁ := Z₁) (Z₂ := Z₂) hW) :
        C(↥((Work.Thom.realification Z₂).proj ⁻¹' W),
          ↥W × EuclideanSpace ℝ (Fin (2 * m₂)))))
    hf2 hcc2 hq2p ℤ (2 * m₂) (Work.Thom.Mpun (2 * m₂) ↥W)]
  have hstep7 := congrArg (fun φ => φ.hom (Work.Thom.Mpun (2 * m₂) ↥W))
    (Work.Thom.relCohMap_congrA (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
      (Work.Thom.Punct ↥W (2 * m₂))
      (wsumChartHomeo_comp_wsumQ₂ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW)
      hq2p (fun _ hx => hx) ℤ (2 * m₂))
  rw [hstep7]


/-- The chart homeomorphism of the sum composed with `wsumQ` is the coordinate map `wsumPhi`. -/
theorem wsumChartHomeo_comp_wsumQ (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    ((Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) (2 * (m₁ + m₂))
        (Work.Thom.covE (m := m₁ + m₂)) k W hW :
        C(↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W),
          ↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂))))).comp
      (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
      = wsumPhi W := by
  apply ContinuousMap.ext
  intro x
  exact wsumQ_chart (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x

/-- **The pullback of `wsumCup` along the comparison map is the model class of the sum.** -/
theorem wsumCup_comp_wsumF (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (hAopen : IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁))
    (hCopen : IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂))
    (k : ι₁ × ι₂) (W : Set B)
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (hmA : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece1 Z₁ Z₂ π₁)
    (hmC : ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) :
    (Work.Thom.relCohMap (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
        (fun x hx => Or.elim hx (fun h => Or.inl (hmA x h)) (fun h => Or.inr (hmC x h)))
        ℤ (2 * m₁ + 2 * m₂)).hom
        (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
      = (Work.Thom.relCohMap (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂))
          (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂)) ℤ (2 * m₁ + 2 * m₂)).hom
          (Work.Thom.Mpun (2 * m₁ + 2 * m₂) ↥W) := by
  have hcup : (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
      = Work.Whitney.tcmRelCup (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁)
          (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) hAopen hCopen (2 * m₁) (2 * m₂)
          (Work.Whitney.wsumRelTau1 hm₁ Z₁ Z₂ π₁)
          (Work.Whitney.wsumRelTau2 hm₂ Z₁ Z₂ π₂) := rfl
  rw [hcup, Work.Whitney.tcmRelCup_natural ℤ (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
    (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
    (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)) (Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
    hAopen hCopen (Work.Whitney.isOpen_tcmA ↥W (2 * m₁) (2 * m₂))
    (Work.Whitney.isOpen_tcmC ↥W (2 * m₁) (2 * m₂)) hmA hmC
    (fun x hx => Or.elim hx (fun h => Or.inl (hmA x h)) (fun h => Or.inr (hmC x h)))
    (2 * m₁) (2 * m₂) (Work.Whitney.wsumRelTau1 hm₁ Z₁ Z₂ π₁)
    (Work.Whitney.wsumRelTau2 hm₂ Z₁ Z₂ π₂)]
  rw [relCohMap_wsumRelTau1 (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW hmA,
    relCohMap_wsumRelTau2 (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW hmC]
  rw [Work.Whitney.tcmModelMul_even' (B := ↥W) m₁ m₂]



/-- **The chart identity**: the restriction of the (transported) relative–relative cup of the two
pulled-back Thom classes to the piece of the realified sum over `W` is the chart class of the sum. -/
theorem wsum_chart_class (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (π₁ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (hset : Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂
      = Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
    (hAopen : IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁))
    (hCopen : IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂))
    (k : ι₁ × ι₂) {W : Set B}
    (hW : W ⊆ (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    (Work.Cohomology.pdCohRes
        (TopCat.of (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W) (2 * (m₁ + m₂))).hom
        (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
          (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)))
      = (Work.Thom.localThomOfChart (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
          (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW).τ := by
  have hmA : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ :=
    fun x hx => wsumQ₁_fibre_ne_zero (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ hπ₁ k W hW x hx
  have hmC : ∀ x ∈ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂ :=
    fun x hx => wsumQ₂_fibre_ne_zero (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₂ hπ₂ k W hW x hx
  have hq : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
      ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      ((wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x :
        (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace))
        ∈ Work.Thom.zeroComplement
            (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) :=
    fun x hx => (wsumQ_mem_zeroComplement_iff (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x).mp hx
  have hbij : Function.Injective ((Work.Thom.relCohMap
      (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
      (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
        ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
      (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) hq
      ℤ (2 * (m₁ + m₂))).hom) := by
    have hb := (Work.Thom.bijective_relCohMap_of_homeomorphA
      (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂) ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
      (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W)
      (wsumQHomeo (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
      (fun x => wsumQ_mem_zeroComplement_iff (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
      ℤ (2 * (m₁ + m₂))).1
    have hmeq : ((wsumQHomeo (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW :
        C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂),
          ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))))
        = wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW := by
      apply ContinuousMap.ext
      intro x
      exact wsumQHomeo_apply (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
    rw [show (Work.Thom.relCohMap (↑(wsumQHomeo (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW) :
          C(Work.Whitney.tcmX ↥W (2 * m₁) (2 * m₂),
            ↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)))
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) _ ℤ (2 * (m₁ + m₂)))
        = (Work.Thom.relCohMap (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) hq
            ℤ (2 * (m₁ + m₂))) from
      Work.Thom.relCohMap_congrA _ _ hmeq _ hq ℤ (2 * (m₁ + m₂))] at hb
    exact hb
  refine hbij ?_
  have hmU : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
      ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x
        ∈ Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂ :=
    fun x hx => Or.elim hx (fun h => Or.inl (hmA x h)) (fun h => Or.inr (hmC x h))
  have hqsub : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
      ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      (Work.Thom.subtypeMap
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW x)
        ∈ Work.Thom.zeroComplement
            (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) :=
    fun x hx => hq x hx
  have hL : (Work.Thom.relCohMap (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) hq
        ℤ (2 * (m₁ + m₂))).hom
        ((Work.Cohomology.pdCohRes
          (TopCat.of (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace)
          (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
          ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W) (2 * (m₁ + m₂))).hom
          (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
            (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))))
      = (Nat.mul_add 2 m₁ m₂).symm ▸
          ((Work.Thom.relCohMap (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂))
            (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂)) ℤ (2 * m₁ + 2 * m₂)).hom
            (Work.Thom.Mpun (2 * m₁ + 2 * m₂) ↥W)) := by
    have hres : (Work.Cohomology.pdCohRes
        (TopCat.of (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
        ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W) (2 * (m₁ + m₂)))
        = Work.Thom.relCohMap
            (Work.Thom.subtypeMap
              ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))
            (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W)
            (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
            (fun _ hx => hx) ℤ (2 * (m₁ + m₂)) := rfl
    rw [hres]
    have hcomp : (Work.Thom.relCohMap (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) hq
          ℤ (2 * (m₁ + m₂))).hom
          ((Work.Thom.relCohMap
            (Work.Thom.subtypeMap
              ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))
            (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W)
            (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
            (fun _ hx => hx) ℤ (2 * (m₁ + m₂))).hom
            (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
              (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))))
        = (Work.Thom.relCohMap
            ((Work.Thom.subtypeMap
              ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
              (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
            hqsub ℤ (2 * (m₁ + m₂))).hom
            (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
              (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))) :=
      Work.Thom.relCohMap_compA_apply
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W)
        (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Thom.subtypeMap
          ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W))
        hq (fun _ hx => hx) hqsub ℤ (2 * (m₁ + m₂))
        (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
          (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)))
    erw [hcomp]
    have hsetpush : (Work.Thom.relCohMap
          ((Work.Thom.subtypeMap
            ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
            (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.zeroComplement (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)))
          hqsub ℤ (2 * (m₁ + m₂))).hom
          (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
            (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)))
        = (Work.Thom.relCohMap
            ((Work.Thom.subtypeMap
              ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
              (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
            hmU ℤ (2 * (m₁ + m₂))).hom
            ((Nat.mul_add 2 m₁ m₂).symm ▸
              (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)) :=
      relCohMap_cast_target_set
        ((Work.Thom.subtypeMap
          ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
          (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
        hset
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        hmU hqsub
        ((Nat.mul_add 2 m₁ m₂).symm ▸
          (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))
    rw [hsetpush]
    have hdeg : (Work.Thom.relCohMap
          ((Work.Thom.subtypeMap
            ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
            (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
          hmU ℤ (2 * (m₁ + m₂))).hom
          ((Nat.mul_add 2 m₁ m₂).symm ▸
            (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))
        = (Nat.mul_add 2 m₁ m₂).symm ▸
            ((Work.Thom.relCohMap
              ((Work.Thom.subtypeMap
                ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
                (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
              (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
                ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
              (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
              hmU ℤ (2 * m₁ + 2 * m₂)).hom
              (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)) :=
      Work.Thom.relCohMap_cast
        ((Work.Thom.subtypeMap
          ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
          (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
        hmU (Nat.mul_add 2 m₁ m₂).symm
        (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
    rw [hdeg]
    have hfus : (Work.Thom.relCohMap
          ((Work.Thom.subtypeMap
            ((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W)).comp
            (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
          hmU ℤ (2 * m₁ + 2 * m₂))
        = (Work.Thom.relCohMap (wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
            hmU ℤ (2 * m₁ + 2 * m₂)) := rfl
    rw [hfus]
    rw [wsumCup_comp_wsumF (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ π₂ hπ₁ hπ₂ hAopen hCopen
      k W hW hmA hmC]
  have hchart := Work.Thom.chartHomeo_mem
    (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) (2 * (m₁ + m₂))
    (Work.Thom.covE (m := m₁ + m₂)) k W hW
  have hqr : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
      ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
      ((Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
        (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW :
          C(↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W),
            ↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂))))).comp
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)) x
        ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) :=
    fun x hx => hchart _ (hq x hx)
  have hR : (Work.Thom.relCohMap (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) hq
        ℤ (2 * (m₁ + m₂))).hom
        ((Work.Thom.localThomOfChart (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
          (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW).τ)
      = (Nat.mul_add 2 m₁ m₂).symm ▸
          ((Work.Thom.relCohMap (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂))
            (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂)) ℤ (2 * m₁ + 2 * m₂)).hom
            (Work.Thom.Mpun (2 * m₁ + 2 * m₂) ↥W)) := by
    rw [Work.Thom.localThomOfChart_tau (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
      (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW]
    have hcompR : (Work.Thom.relCohMap (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W) hq
          ℤ (2 * (m₁ + m₂))).hom
          ((Work.Thom.relCohMap
            (Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
              (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW)
            (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W)
            (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) hchart ℤ (2 * (m₁ + m₂))).hom
            (Work.Thom.Mpun (2 * (m₁ + m₂)) ↥W))
        = (Work.Thom.relCohMap
            ((Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
              (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW :
                C(↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W),
                  ↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂))))).comp
              (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) hqr ℤ (2 * (m₁ + m₂))).hom
            (Work.Thom.Mpun (2 * (m₁ + m₂)) ↥W) :=
      Work.Thom.relCohMap_compA_apply
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.pieceZero (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)) W)
        (Work.Thom.Punct ↥W (2 * (m₁ + m₂)))
        (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW)
        (Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
          (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW)
        hq hchart hqr ℤ (2 * (m₁ + m₂)) (Work.Thom.Mpun (2 * (m₁ + m₂)) ↥W)
    rw [hcompR]
    have hphi_eq : (Work.Thom.relCohMap (wsumPhi W)
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) (wsumPhi_mem W) ℤ (2 * (m₁ + m₂))).hom
          (Work.Thom.Mpun (2 * (m₁ + m₂)) ↥W)
        = (Nat.mul_add 2 m₁ m₂).symm ▸
            ((Work.Thom.relCohMap (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))
              (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
                ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
              (Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂))
              (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂)) ℤ (2 * m₁ + 2 * m₂)).hom
              (Work.Thom.Mpun (2 * m₁ + 2 * m₂) ↥W)) := by
      have hsplit : wsumPhi W = (castMap (Nat.mul_add 2 m₁ m₂).symm).comp
          (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂)) := rfl
      have hsplitmem : ∀ x ∈ Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂),
          ((castMap (Nat.mul_add 2 m₁ m₂).symm).comp
            (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))) x
            ∈ Work.Thom.Punct ↥W (2 * (m₁ + m₂)) :=
        fun x hx => castMap_mem_punct (Nat.mul_add 2 m₁ m₂).symm
          (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂) x)
          (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂) x hx)
      rw [show (Work.Thom.relCohMap (wsumPhi W)
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) (wsumPhi_mem W) ℤ (2 * (m₁ + m₂)))
          = (Work.Thom.relCohMap
              ((castMap (Nat.mul_add 2 m₁ m₂).symm).comp
                (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂)))
              (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
                ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
              (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) hsplitmem ℤ (2 * (m₁ + m₂))) from
        Work.Thom.relCohMap_congrA _ _ hsplit (wsumPhi_mem W) hsplitmem ℤ (2 * (m₁ + m₂))]
      rw [← Work.Thom.relCohMap_compA_apply
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂)) (Work.Thom.Punct ↥W (2 * (m₁ + m₂)))
        (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))
        (castMap (Nat.mul_add 2 m₁ m₂).symm)
        (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂))
        (castMap_mem_punct (Nat.mul_add 2 m₁ m₂).symm) hsplitmem ℤ (2 * (m₁ + m₂))
        (Work.Thom.Mpun (2 * (m₁ + m₂)) ↥W)]
      rw [Mpun_castMap (Nat.mul_add 2 m₁ m₂).symm]
      rw [Work.Thom.relCohMap_cast (Work.Whitney.tcmF ↥W (2 * m₁) (2 * m₂))
        (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
          ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
        (Work.Thom.Punct ↥W (2 * m₁ + 2 * m₂))
        (Work.Whitney.tcmF_mem ↥W (2 * m₁) (2 * m₂)) (Nat.mul_add 2 m₁ m₂).symm
        (Work.Thom.Mpun (2 * m₁ + 2 * m₂) ↥W)]
    have hfus : (Work.Thom.relCohMap
          ((Work.Thom.chartHomeo (Work.Thom.realification (Whitney.whitneySum Z₁ Z₂))
            (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW :
              C(↥((Work.Thom.realification (Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W),
                ↥W × EuclideanSpace ℝ (Fin (2 * (m₁ + m₂))))).comp
            (wsumQ (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ k W hW))
          (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
            ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
          (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) hqr ℤ (2 * (m₁ + m₂)))
        = (Work.Thom.relCohMap (wsumPhi W)
            (Work.Whitney.tcmA ↥W (2 * m₁) (2 * m₂)
              ∪ Work.Whitney.tcmC ↥W (2 * m₁) (2 * m₂))
            (Work.Thom.Punct ↥W (2 * (m₁ + m₂))) (wsumPhi_mem W) ℤ (2 * (m₁ + m₂))) :=
      Work.Thom.relCohMap_congrA _ _ (wsumChartHomeo_comp_wsumQ (Z₁ := Z₁) (Z₂ := Z₂)
        hm₁ hm₂ k W hW) hqr (wsumPhi_mem W) ℤ (2 * (m₁ + m₂))
    rw [hfus, hphi_eq]
  rw [hL, hR]

end FactorOne
/-- **The chart identity of the cup in the `wsumCast` form.**  This is
`Work.Whitney.wsum_chart_class` with the transported cup written as the application
`Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset (wsumCup …)` of the top-level definition, which is the form in
which the target theorem `Work.Whitney.thomClassRank_whitneySum_rel` states the cup. -/
theorem wsum_chart_class_cast {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ}
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (hset : Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂
      = Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
    (hAopen : IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁))
    (hCopen : IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂))
    (k : ι₁ × ι₂) {W : Set B}
    (hW : W ⊆ (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k) :
    (Work.Cohomology.pdCohRes
        (TopCat.of (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
        ((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' W) (2 * (m₁ + m₂))).hom
        (Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
          (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))
      = (Work.Thom.localThomOfChart (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂))
          (2 * (m₁ + m₂)) (Work.Thom.covE (m := m₁ + m₂)) k W hW).τ := by
  rw [show Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
        (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
      = (hset ▸ ((Nat.mul_add 2 m₁ m₂).symm ▸
          (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen))) from rfl]
  exact wsum_chart_class (Z₁ := Z₁) (Z₂ := Z₂) hm₁ hm₂ π₁ π₂ hπ₁ hπ₂ hset hAopen hCopen k hW




/-- **The relative Thom product formula for a Whitney sum.**

`tau_{Z1 (+) Z2} = pr1^* tau_{Z1} cup_rel pr2^* tau_{Z2}`: the Thom class of the realification of a
Whitney sum of two complex gluing-data bundles is the relative-relative cup of the two pulled-back
Thom classes along the two coordinate projections of the total space of the sum.  The vocabulary is
`Submission/Work/Whitney/WSumChars.lean` (`Work.Whitney.wsumCup`, `wsumTau`, `wsumCast`); the
statement is the hypothesis of the assembly
`Work.Whitney.chernClass_whitneySum_top_of_thomProduct`, hence the mathematical heart of
`Work.Whitney.chernClass_whitneySum_top` (= `Work.Whitney.TopClassMul`).

PROOF.  By `Work.Thom.localThom_eq_of_cover_rel` (with `P = Set.univ`) it suffices to compare the
two classes over the pieces of the cover of `B` by the base sets `(Z₁ ⊕ Z₂)_ℝ.baseSet (k₁,k₂)`
(supplying the local Thom property of the chart classes `Work.Thom.localThomOfChart.isThom` for the
injectivity hypothesis).  Over such a piece both sides are the *chart class of the sum*
(`Work.Thom.localThomOfComplexCover_pdCohMap_subset` for the Thom class, and
`Work.Whitney.wsum_chart_class` -- the chart identity -- for the cup), and the chart identity is
proved by pulling both sides back along the comparison homeomorphism `Work.Whitney.wsumQ`: the
coordinate content is `Work.Whitney.wsumQ₁_coord`/`wsumQ₂_coord` (the chart coordinates of the two
summands are the coordinates of the model space, via the sum-compatibility
`Work.Gen.rifStd_sum_compatible_cast` of the canonical realification), the identification of the
pulled-back Thom classes with the model classes is
`Work.Whitney.relCohMap_wsumRelTau1`/`relCohMap_wsumRelTau2` (from
`Work.Whitney.thomClassRank_restrict_chart`), and the cup is computed by the naturality
`Work.Whitney.tcmRelCup_natural` and the even-rank model product formula
`Work.Whitney.tcmModelMul_even'`. -/
theorem thomClassRank_whitneySum_rel {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ}
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (hset : Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂
      = Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
    (hAopen : IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁))
    (hCopen : IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)) :
    Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
        (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
      = Work.Whitney.wsumTau hm₁ hm₂ Z₁ Z₂ := by
  have hm : 1 ≤ m₁ + m₂ := Nat.le_trans hm₁ (Nat.le_add_right m₁ m₂)
  have hR : (Work.Cohomology.pdCohRes
      (TopCat.of (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace)
      (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
      Set.univ (2 * (m₁ + m₂))).hom (Work.Whitney.wsumTau hm₁ hm₂ Z₁ Z₂)
      = (Work.Thom.localThomOfComplexCover hm (Work.Whitney.whitneySum Z₁ Z₂)).τ := by
    show (Work.Cohomology.pdCohRes
        (TopCat.of (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
        Set.univ (2 * (m₁ + m₂))).hom
        ((Work.Thom.thomClassOf hm (Work.Whitney.whitneySum Z₁ Z₂)).τ) = _
    exact Work.Thom.thomClassOf_spec hm (Work.Whitney.whitneySum Z₁ Z₂)
  have hcover := Work.Thom.localThom_eq_of_cover_rel
    (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)) (2 * (m₁ + m₂))
    (fun k : ι₁ × ι₂ => (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k)
    (fun k => (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).isOpen_baseSet k)
    Finset.univ (fun _ _ => Set.subset_univ _)
    (fun x _ => Set.mem_iUnion.mpr ⟨(Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).indexAt x,
      Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).mem_baseSet_at x⟩⟩)
    ((Work.Thom.localThomOfComplexCover hm (Work.Whitney.whitneySum Z₁ Z₂)).τ)
    ((Work.Cohomology.pdCohRes
        (TopCat.of (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
        ((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' Set.univ)
        (2 * (m₁ + m₂))).hom (Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
        (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)))
    ((Work.Thom.localThomOfComplexCover hm (Work.Whitney.whitneySum Z₁ Z₂)).isThom 0)
    (fun k _ => by
      simp only [Subsingleton.elim]
      rw [Work.Thom.localThomOfComplexCover_pdCohMap_subset hm
        (Work.Whitney.whitneySum Z₁ Z₂) k (subset_rfl :
          (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k ⊆
            (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k)]
      exact ((Work.Thom.localThomOfChart
        (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)) (2 * (m₁ + m₂))
        (Work.Thom.covE (m := m₁ + m₂)) k
        ((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k) subset_rfl).isThom 0).1)
    (fun k hk => by
      have hh := congrArg (fun φ => φ.hom (Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
          (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)))
        (Work.Thom.pdCohRes_eq_pdCohMap (TopCat.of (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace) (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂))) ((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' Set.univ) ((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).proj ⁻¹' ((fun k : ι₁ × ι₂ => (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k) k))
          (Set.preimage_mono ((fun _ _ => Set.subset_univ _) k hk)) (2 * (m₁ + m₂)))
      rw [ModuleCat.comp_apply] at hh
      rw [← hh]
      rw [wsum_chart_class_cast hm₁ hm₂ Z₁ Z₂ π₁ π₂ hπ₁ hπ₂ hset hAopen hCopen
        k (hW := (subset_rfl : (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k ⊆ (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k))]
      exact (Work.Thom.localThomOfComplexCover_pdCohMap_subset hm (Work.Whitney.whitneySum Z₁ Z₂) k
        (subset_rfl : (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k ⊆ (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).baseSet k)).symm)
  apply Work.Thom.pdCohRes_univ_injective (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂))) (2 * (m₁ + m₂))
  rw [hR]
  exact hcover

end Work.Whitney
