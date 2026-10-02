import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmModelMul_of_point

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

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- **The signed model product formula reduces to its point case.**

The signed form of `Work.Whitney.tcmModelMul_of_point`: the general-base statement follows from the
one-point-base statement *at the same* `(p,q)`, by the fibrewise detection
`Work.Whitney.Mpun_eq_of_fibrewise` (a class of `H^n(B × ℝ^n, B × (ℝ^n∖0))` is determined by its
restrictions to the fibres `{b} × ℝ^n`).  The scalar `(-1)^{p*q}` is constant in `b`, so it passes
through every `relCohMap` (`map_smul`), which is the only change with respect to the unsigned
`Work.Whitney.tcmModelMul_of_point` (`Submission/Work/Whitney/tcmModelMul_of_point.lean`, proved,
same proof with the scalar carried along). -/
theorem tcmModelMul_signed_of_point
    (h : ∀ (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (p q : ℕ),
      Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p q) (Work.Whitney.tcmC Y p q)
          (Work.Whitney.isOpen_tcmA Y p q) (Work.Whitney.isOpen_tcmC Y p q) p q
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p q) (Work.Whitney.tcmA Y p q)
          (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p q) (Work.Whitney.tcmC Y p q)
          (Work.Thom.Punct Y q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q Y))
      = ((-1 : ℤ) ^ (p * q)) •
        ((Work.Thom.relCohMap (Work.Whitney.tcmF Y p q)
          (Work.Whitney.tcmA Y p q ∪ Work.Whitney.tcmC Y p q) (Work.Thom.Punct Y (p + q))
          (Work.Whitney.tcmF_mem Y p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) Y)))
    {B : Type} [TopologicalSpace B] (p q : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA B p q) (Work.Whitney.tcmC B p q)
        (Work.Whitney.isOpen_tcmA B p q) (Work.Whitney.isOpen_tcmC B p q) p q
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 B p q) (Work.Whitney.tcmA B p q)
        (Work.Thom.Punct B p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p B))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 B p q) (Work.Whitney.tcmC B p q)
        (Work.Thom.Punct B q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q B))
    = ((-1 : ℤ) ^ (p * q)) •
      ((Work.Thom.relCohMap (Work.Whitney.tcmF B p q)
        (Work.Whitney.tcmA B p q ∪ Work.Whitney.tcmC B p q) (Work.Thom.Punct B (p + q))
        (Work.Whitney.tcmF_mem B p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) B)) := by
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
        (((-1 : ℤ) ^ (p * q)) •
          ((relCohMap (tcmF B p q) (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
            (tcmF_mem B p q) ℤ (p + q)).hom (Mpun (p + q) B))) := by
    intro b
    rw [map_zsmul]
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
