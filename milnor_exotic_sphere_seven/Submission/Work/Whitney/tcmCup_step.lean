import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.tcmF_inv_general
import Submission.Work.Whitney.tcmSuccOneAux
import Submission.Work.Whitney.tcmRelCup_natural
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Whitney.tcmPhiAux
import Submission.Work.Whitney.tcmModelMul_point_zero
import Submission.Work.Whitney.tcmPunctCore_signed
import Submission.Work.Whitney.tcmProd_assoc_one
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

/-!
# The suspension step of the model product formula (`Work.Whitney.tcmCup_step`)

## What is being proved

`Work.Whitney.tcmCup_step` is the **induction step** of the model product formula over a
subsingleton base `Y`.  Writing

  `S(p,q) := (Fib.tcmF_inv Y p q)^* ( tcmRelCup (A_p) (C_q) (pr₁^* Mpun p) (pr₂^* Mpun q) )`,
  `∈ H^{p+q}(Y × ℝ^{p+q}, Sph Y (p+q))`,

it says `S(p,q+1) = (-1)^p • step Y (p+q) (S(p,q))`.

## Why it is the crux, and the route taken here

`step Y (p+q)` is the suspension and `Mn (n+1) Y = step Y n (Mn n Y)` *by definition*, so the
identity is *equivalent* (modulo the base case `S(p,0) = Mn p`) to the whole signed model product
formula `S(p,q) = (-1)^{p q} Mn (p+q) Y`:  the formula at `q` and at `q+1` give the identity, and
conversely the identity plus `S(p,0) = Mn p` gives the formula by induction on `q`.  So there is no
purely formal proof of `tcmCup_step`: it carries the content of the crux of the top-class
multiplicativity (the "cross product of the two model Thom classes is the model class of the sum",
with the Koszul sign `(-1)^{p q}`).

## The plan (external-product algebra + the rank-one case)

The definitions and their bilinearity live in `Submission/Work/Whitney/TCMProdDefs.lean`
(`Pstep`, `Pstep_spec`, `Mpun_succ`, `tcmProd`, `tcmJ`, `tcmProd_add_*`, `tcmProd_zsmul_*`).  The
proof below reduces the statement to exactly two inputs, neither of them naturality:

1. **the rank-one case** `tcmJ Y n 1 = (-1)^n • Mpun (n+1) Y`, i.e. `Work.Whitney.tcmPunctCore_signed`
   (`Submission/Work/Whitney/tcmPunctCore_signed.lean`, importable here).  This is the single genuine
   computation of the chapter (the sign calibration `eps(1,1) = -1` plus the recursion);
2. **the associativity of the external product** `tcmProd` at `r = 1`,

     `tcmProd Y p (q+1) a (tcmProd Y q 1 b c) = tcmProd Y (p+q) 1 (tcmProd Y p q a b) c`,

   the `r = 1` instance of `Nat.add_assoc`-casted associativity
   (`Submission/Work/Whitney/tcmProd_assoc.lean`; its prover's module cannot be imported here because
   it imports *this* file, so the instance used below is `Work.Whitney.tcmProd_assoc_up`, whose
   statement lives upstream of this file).

Everything else is formal and is proved here:

* `tcmJ_zero` — the base case `tcmJ Y p 0 = Mpun p Y`, from the proved
  `Work.Whitney.tcmModelMul_point_zero` (the unit law) moved along the transports
  `Work.Whitney.tcmF_inv_tcmF_transport_zero`;
* `tcmJ_model_of_assoc` — the *whole* model product formula in the punctured group,
  `tcmJ Y p q = (-1)^{p q} • Mpun (p+q) Y`, by induction on `q` from the two inputs above;
* `tcmJ_succ_of_model` — the suspension step of `tcmJ` in the punctured group, i.e. the model
  formula at `q` and at `q+1` plus `Mpun_succ` and `Pstep_zsmul`;
* `tcmCupLHS_eq_jMap` — the bookkeeping identifying the left hand side of the statement with
  `jMap (tcmJ Y p q)`;
* the empty-base case (`Subsingleton Y` without `Nonempty Y`), where both sides lie in subsingleton
  groups (`Work.Whitney.subsingleton_relCoh_of_isEmpty`).

The final transport along `jMap` uses only `Pstep_spec` (the gauge equation of `Pstep`) and the
`ℤ`-linearity of the pullback.
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

/-! ## The left hand side of the statement, in the sphere group -/

/-- The left hand side of `Work.Whitney.tcmCup_step` at `(p,q)`: the relative–relative cup of the
two pulled-back model classes, transported into the **sphere** group by the inverse coordinate
identification.  It is `jMap (tcmJ Y p q)` (`tcmCupLHS_eq_jMap`). -/
noncomputable def tcmCupLHS (Y : Type) [TopologicalSpace Y] (p q : ℕ) :
    RelCoh ℤ (p + q) (Y × EuclideanSpace ℝ (Fin (p + q))) (Sph Y (p + q)) :=
  (relCohMap (Fib.tcmF_inv Y p q) (Sph Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
    (tcmF_inv_mem' (Y := Y) p q) ℤ (p + q)).hom
    (tcmRelCup (tcmA Y p q) (tcmC Y p q) (isOpen_tcmA Y p q) (isOpen_tcmC Y p q) p q
      ((relCohMap (tcmPr1 Y p q) (tcmA Y p q) (Punct Y p) (fun x hx => hx) ℤ p).hom
        (Mpun p Y))
      ((relCohMap (tcmPr2 Y p q) (tcmC Y p q) (Punct Y q) (fun x hx => hx) ℤ q).hom
        (Mpun q Y)))

/-- The composite `jMap ∘ (punctured pullback)` is the sphere pullback: the linear-map form of the
bookkeeping. -/
theorem tcmJ_comp_eq' (Y : Type) [TopologicalSpace Y] (p q : ℕ)
    (x : RelCoh ℤ (p + q) (tcmX Y p q) (tcmA Y p q ∪ tcmC Y p q)) :
    (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q)))) (Sph Y (p + q))
        (Punct Y (p + q)) (mem_Sph_punct Y (p + q)) ℤ (p + q)).hom
      ((relCohMap (Fib.tcmF_inv Y p q) (Punct Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
        (tcmF_inv_mem_punct_union Y p q) ℤ (p + q)).hom x)
      = (relCohMap (Fib.tcmF_inv Y p q) (Sph Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
        (tcmF_inv_mem' (Y := Y) p q) ℤ (p + q)).hom x := by
  have h := relCohMap_compA_apply (Sph Y (p + q)) (Punct Y (p + q))
    (tcmA Y p q ∪ tcmC Y p q) (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q))))
    (Fib.tcmF_inv Y p q) (mem_Sph_punct Y (p + q)) (tcmF_inv_mem_punct_union Y p q)
    (fun y hy => tcmF_inv_mem_punct_union Y p q y (mem_Sph_punct Y (p + q) y hy)) ℤ (p + q) x
  rw [h]
  rfl

/-- **Bookkeeping**: the left hand side of the statement is the pair inclusion `jMap` applied to the
external product `tcmJ Y p q` in the punctured group. -/
theorem tcmCupLHS_eq_jMap (Y : Type) [TopologicalSpace Y] (p q : ℕ) :
    tcmCupLHS Y p q
      = (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q)))) (Sph Y (p + q))
          (Punct Y (p + q)) (mem_Sph_punct Y (p + q)) ℤ (p + q)).hom (tcmJ Y p q) := by
  simp only [tcmCupLHS, tcmProd]
  exact (tcmJ_comp_eq' Y p q _).symm

/-! ## The rank-one case, from `Work.Whitney.tcmPunctCore_signed` -/

/-- **The rank-one case of the model product formula**: `tcmJ Y n 1 = (-1)^n • Mpun (n+1) Y`.  This
is `Work.Whitney.tcmPunctCore_signed` (whose membership proof for the pair condition differs from
the one of `tcmProd`, which is all that separates the two statements). -/
theorem tcmJ_one (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (n : ℕ) :
    tcmJ Y n 1 = (-1 : ℤ) ^ n • Mpun (n + 1) Y := by
  have h := tcmPunctCore_signed Y n
  simpa only [tcmProd, Nat.mul_one] using h

/-! ## The model product formula in the punctured group, for `q ≥ 1`

The base of the induction is the rank-one case `tcmJ_one` (itself
`Work.Whitney.tcmPunctCore_signed`).  The `q = 0` case is not needed here: the statement for the
*sphere* group at `q = 0` follows directly from the proved unit law
`Work.Whitney.tcmModelMul_point_zero` together with the definition `Mn (n+1) = step n (Mn n)`, and
the `q = 0` case of the target statement below is proved directly from those two. -/

/-- **The recursion of the punctured suspension on the model class**, from the rank-one case
`tcmJ_one` and `Mpun_succ`. -/
theorem Pstep_Mpun (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (q : ℕ) :
    Pstep Y q (Mpun q Y) = (-1 : ℤ) ^ q • tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y) := by
  have h := tcmJ_one Y q
  rw [show tcmJ Y q 1 = tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y) from rfl] at h
  rw [← Mpun_succ Y q, h, smul_smul, Work.Thom.negOnePow_mul_self, one_smul]

/-- **The model product formula in the punctured group for `q ≥ 1`**, by induction on `q` from the
rank-one case `tcmJ_one` and the associativity `hA` of `tcmProd` at `r = 1`. -/
theorem tcmJ_model_of_assoc (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
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
        simpa only [Nat.mul_one, Nat.zero_add] using tcmJ_one Y p
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
                ((-1 : ℤ) ^ q • tcmProd Y q 1 (Mpun q Y) (Mpun 1 Y)) := by rw [Pstep_Mpun Y q]
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
                      = tcmJ Y (p + q) 1 from rfl, tcmJ_one Y (p + q)]
          _ = (-1 : ℤ) ^ (p * (q + 1)) • Mpun (p + (q + 1)) Y := by
                rw [hsign, smul_smul, smul_smul, mul_assoc]
                rfl

/-- **The suspension step of the model class in the punctured group for `q ≥ 1`**, from the model
formula at `q` and at `q+1` plus `Mpun_succ` and `Pstep_zsmul`. -/
theorem tcmJ_succ_of_assoc (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
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
  rw [tcmJ_model_of_assoc Y hA p (q + 1) (by omega), tcmJ_model_of_assoc Y hA p q hq,
    Pstep_zsmul, ← Mpun_succ Y (p + q), smul_smul, hsign]
  rfl

theorem tcmCup_step_of_assoc (Y : Type) [TopologicalSpace Y] [Subsingleton Y]
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
        rw [tcmCupLHS_eq_jMap, tcmJ_one, map_zsmul, Mpun_spec]
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
      have hstep := tcmJ_succ_of_assoc Y hA p hqpos
      rw [tcmCupLHS_eq_jMap Y p (q + 1), tcmCupLHS_eq_jMap Y p q, hstep, map_zsmul]
      exact congrArg (fun z => ((-1 : ℤ) ^ p) • z) (Pstep_spec Y (p + q) (tcmJ Y p q))
  · haveI : IsEmpty Y := not_nonempty_iff.mp hY
    haveI : IsEmpty (Y × EuclideanSpace ℝ (Fin (p + (q + 1)))) :=
      ⟨fun x => isEmptyElim x.1⟩
    haveI : Subsingleton (RelCoh ℤ (p + (q + 1))
        (Y × EuclideanSpace ℝ (Fin (p + (q + 1)))) (Sph Y (p + (q + 1)))) :=
      subsingleton_relCoh_of_isEmpty _ _
    exact Subsingleton.elim _ _

/-- **The suspension step of the model product formula** (the lemma this file is the home of).

See the module docstring for the plan of the proof: it is the induction step of the signed model
product formula over a subsingleton base, so it carries the crux of the top-class multiplicativity;
the only non-formal input is the rank-one case `Work.Whitney.tcmPunctCore_signed`. -/
theorem tcmCup_step (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (p q : ℕ) :
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
  exact tcmCup_step_of_assoc Y
    (fun p q a b c => tcmProd_assoc_one Y p q a b c) p q

end

end Work.Whitney
