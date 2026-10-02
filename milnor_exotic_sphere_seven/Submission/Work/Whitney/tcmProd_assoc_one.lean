import Mathlib
import Submission.Work.Whitney.AssocOnePrep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- **Associativity of the external product `Work.Whitney.tcmProd`, `r = 1` instance.**

`tcmProd B m n a b = (Fib.tcmF_inv B m n)^* (a ⌣ b)`; this is the case `r = 1` of
`(a ⊠ b) ⊠ c = a ⊠ (b ⊠ c)`, in the cast-free form in which `Work.Whitney.tcmCup_step` needs it.

**Proof** (all steps in `Submission/Work/Whitney/AssocOnePrep.lean`).  With
`Φ₁ = Fib.tcmF_inv B p (q+1)`, `Φ₂ = Fib.tcmF_inv B (p+q) 1` and `ψ = TCMAssocUp.psiA B p q`
(so that `ψ ∘ Φ₁ = Φ₂`, `psiA_comp_tcmF_inv`), `tcmProd_assoc_one_LHS_unfold` and
`tcmProd_assoc_one_RHS_unfold` write both sides as `Φ₁^* X₀` and `Φ₂^* Y₀`.  The key identity
`tcmX0_eq_psiY` is `X₀ = ψ^* Y₀`:

* `tcmX0_eq_brackL` expands `X₀` (via `tcmF2_eq`, which is `LHS_inner` — the naturality of
  `tcmRelCup` along `f2 = Φ_{q1} ∘ tcmPr2 B p (q+1)`) into the left bracketing `tcmBrackL` over the
  three blocks `tcmS1 = tcmA B p (q+1)`, `tcmS2 = f2⁻¹(tcmA B q 1)`, `tcmS3 = f2⁻¹(tcmC B q 1)`
  (the set equality `tcmS2 ∪ tcmS3 = tcmC B p (q+1)` is `tcmS2_union_tcmS3`, transported by
  `tcmRelCup_cast_right`);
* `tcmPsiY_eq_brackR` expands `ψ^* Y₀` into the right bracketing `tcmBrackR`: the outer pullback by
  `tcmRelCup_natural` along `ψ` (sets `tcmS1 ∪ tcmS2`, `tcmS3`, using `psiA_preimage_S1_union_S2`
  and `psiA_preimage_S3`), and the two factors by `tcmRelCup_natural` along
  `g = f1 B p q ∘ ψ`, `RHS_factor1_S1`/`RHS_factor2_S2` (`q1A`-, resp. `q2A`-form) and
  `LHS_factor1`/`LHS_factor2` (back to the composite form);
* `tcmBrack_assoc` is `Work.Whitney.tcmRelCup_assoc_general` on `(tcmS1, tcmS2, tcmS3)`; the degree
  cast `Nat.add_assoc p q 1` is eliminated by `addAssoc_one_cast` (it is trivial at `r = 1`).

Applying `Φ₁^*` to `X₀ = ψ^* Y₀` gives `Φ₁^* X₀ = (ψ ∘ Φ₁)^* Y₀ = Φ₂^* Y₀` by
`relCohMap_compA_apply` and `relCohMap_congrA`. -/
theorem tcmProd_assoc_one (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : Work.Thom.RelCoh ℤ p (B × EuclideanSpace ℝ (Fin p)) (Work.Thom.Punct B p))
    (b : Work.Thom.RelCoh ℤ q (B × EuclideanSpace ℝ (Fin q)) (Work.Thom.Punct B q))
    (c : Work.Thom.RelCoh ℤ 1 (B × EuclideanSpace ℝ (Fin 1)) (Work.Thom.Punct B 1)) :
    Work.Whitney.tcmProd B p (q + 1) a (Work.Whitney.tcmProd B q 1 b c)
      = Work.Whitney.tcmProd B (p + q) 1 (Work.Whitney.tcmProd B p q a b) c := by
  rw [tcmProd_assoc_one_LHS_unfold B p q a b c, tcmProd_assoc_one_RHS_unfold B p q a b c]
  rw [show (relCohMap (Fib.tcmF_inv B p (q + 1)) (Punct B (p + (q + 1)))
      (tcmA B p (q + 1) ∪ tcmC B p (q + 1)) (tcmF_inv_mem_punct_union B p (q + 1))
      ℤ (p + (q + 1))).hom (tcmX0 B p q a b c)
    = (relCohMap (Fib.tcmF_inv B p (q + 1)) (Punct B (p + (q + 1)))
      (tcmA B p (q + 1) ∪ tcmC B p (q + 1)) (tcmF_inv_mem_punct_union B p (q + 1))
      ℤ ((p + q) + 1)).hom (tcmX0 B p q a b c) from rfl]
  rw [tcmX0_eq_psiY B p q a b c]
  rw [show tcmPsiY B p q a b c = (relCohMap (TCMAssocUp.psiA B p q)
      (tcmS1 B p q ∪ tcmC B p (q + 1)) (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1)
      (mem_SAB B p q) ℤ ((p + q) + 1)).hom (tcmY0 B p q a b c) from rfl]
  rw [relCohMap_compA_apply (Punct B (p + (q + 1))) (tcmS1 B p q ∪ tcmC B p (q + 1))
    (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1) (Fib.tcmF_inv B p (q + 1)) (TCMAssocUp.psiA B p q)
    (tcmF_inv_mem_punct_union B p (q + 1)) (mem_SAB B p q)
    (fun x hx => mem_SAB B p q (Fib.tcmF_inv B p (q + 1) x)
      (tcmF_inv_mem_punct_union B p (q + 1) x hx))
    ℤ ((p + q) + 1) (tcmY0 B p q a b c)]
  rw [relCohMap_congrA (Punct B (p + (q + 1))) (tcmA B (p + q) 1 ∪ tcmC B (p + q) 1)
    (psiA_comp_tcmF_inv B p q)
    (fun x hx => mem_SAB B p q (Fib.tcmF_inv B p (q + 1) x)
      (tcmF_inv_mem_punct_union B p (q + 1) x hx))
    (tcmF_inv_mem_punct_union B (p + q) 1) ℤ ((p + q) + 1)]
  rfl

end

end Work.Whitney
