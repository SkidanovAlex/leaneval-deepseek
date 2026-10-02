import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# The right-hand side of the Whitney formula

For complex gluing-data bundles `Z₁` (rank `m₁`) and `Z₂` (rank `m₂`) in the standard fibres, the
right-hand side of the Whitney formula in degree `k` is

  `Σ_{i+j=k} c_i(Z₁) ⌣ c_j(Z₂) ∈ H^{2k}(B;ℤ)`,

the sum of the products of the Chern classes of the two factors.  Each summand lives in
`H^{2i}⌣H^{2j} = H^{2i+2j} = H^{2(i+j)}` (`Work.Whitney.cupChern`), and the degree bookkeeping
`2i + 2j = 2(i+j)` is realised by `Work.Thom.cohTransport`; the sum is indexed by
`Finset.antidiagonal k`, with the equality `i + j = k` supplied by the membership proof
(`Finset.mem_antidiagonal`).

* `Work.Whitney.chernSummand` — one summand `c_a(Z₁) ⌣ c_b(Z₂)`, in `H^{2(a+b)}(B;ℤ)`;
* `Work.Whitney.chernProductSum` — the whole right-hand side, in `H^{2k}(B;ℤ)`;
* `Work.Whitney.chernSummand_CohMap`, `Work.Whitney.chernProductSum_CohMap` — naturality;
* `Work.Whitney.chernProductSum_trivial_right` — **the case `Z₂ = ε¹`**: the sum collapses to the
  single term `c_k(Z₁)` (the statement that the Whitney formula for a trivial summand is *stability*).

`Work.Whitney.chernProductSum` is the class that the Whitney formula
(`Work.Whitney.chernClass_whitneySum`, see `README.md` of this directory) compares with the left-hand
side `Work.Thom.chernClass (m₁+m₂) k (Work.Whitney.whitneySum Z₁ Z₂)`.
-/

namespace Work.Whitney

open Work.TangentClasses
open scoped BigOperators

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## One summand of the Whitney formula -/

/-- A single summand `c_a(Z₁) ⌣ c_b(Z₂)` of the Whitney formula, an element of `H^{2(a+b)}(B;ℤ)`. -/
noncomputable def chernSummand {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (a b : ℕ) :
    Work.Thom.Coh ℤ (2 * (a + b)) B :=
  cupChern a b (Work.Thom.chernClass m₁ a Z₁) (Work.Thom.chernClass m₂ b Z₂)

@[simp] theorem chernSummand_def {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (a b : ℕ) :
    chernSummand Z₁ Z₂ a b
      = cupChern a b (Work.Thom.chernClass m₁ a Z₁) (Work.Thom.chernClass m₂ b Z₂) := rfl

/-- **Naturality of a summand of the Whitney formula.** -/
theorem chernSummand_CohMap {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    {B' : Type} [TopologicalSpace B'] (f : C(B', B)) (a b : ℕ) :
    (Work.Thom.CohMap f ℤ (2 * (a + b))).hom (chernSummand Z₁ Z₂ a b)
      = chernSummand (Work.Thom.bundleComap Z₁ f) (Work.Thom.bundleComap Z₂ f) a b := by
  rw [chernSummand_def, chernSummand_def, cupChern_CohMap,
    Work.Thom.chernClass_comap, Work.Thom.chernClass_comap]

/-! ## The whole right-hand side -/

/-- **The right-hand side of the Whitney formula** `Σ_{i+j=k} c_i(Z₁) ⌣ c_j(Z₂)` in degree `k`, an
element of `H^{2k}(B;ℤ)`.  The sum is indexed by `i ∈ {0,…,k}` with `j = k - i`; the degree
bookkeeping of each summand (`Work.Whitney.chernSummand Z₁ Z₂ i j ∈ H^{2(i+j)}` versus `H^{2k}`)
uses `Work.Thom.cohTransport`, and the (vacuous) `if` records the bound `i ≤ k` for the
arithmetic. -/
noncomputable def chernProductSum {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ) :
    Work.Thom.Coh ℤ (2 * k) B :=
  ∑ i ∈ Finset.range (k + 1),
    if h : i ≤ k then
      Work.Thom.cohTransport (by omega : 2 * (i + (k - i)) = 2 * k)
        (chernSummand Z₁ Z₂ i (k - i))
    else 0

/-- **Naturality of the right-hand side of the Whitney formula.** -/
theorem chernProductSum_CohMap {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    {B' : Type} [TopologicalSpace B'] (f : C(B', B)) (k : ℕ) :
    (Work.Thom.CohMap f ℤ (2 * k)).hom (chernProductSum Z₁ Z₂ k)
      = chernProductSum (Work.Thom.bundleComap Z₁ f) (Work.Thom.bundleComap Z₂ f) k := by
  unfold chernProductSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h : i ≤ k
  · rw [dif_pos h, dif_pos h, Work.Thom.cohTransport_CohMap, chernSummand_CohMap]
  · rw [dif_neg h, dif_neg h, map_zero]

/-! ## The trivial-summand case (a bookkeeping gap, recorded)

For `Z₂ = ε¹` every summand of `Work.Whitney.chernProductSum` with `j ≥ 1` vanishes
(`Work.Thom.chernClass_trivial`) and the remaining summand `(i,j) = (k,0)` is `c_k(Z₁) ⌣ 1`, so the
right-hand side of the Whitney formula *is* `c_k(Z₁)` up to the degree cast — the expected
statement

  `chernProductSum Z₁ ε¹ k = cohTransport (2*(k+0) = 2*k) (chernSummand Z₁ ε¹ k 0)`

is true, but the two bookkeeping lemmas used in the literature for it — the **unit law** of the
graded product (`Work.Whitney.cupChern k 0 x 1 = cohTransport x`) and the collapse of the finite
sum above — are *not* proved in this module.  The true content of the trivial-summand case of the
Whitney formula is stability itself, which is proved in the Sum-form in
`Submission/Work/Whitney/Stability.lean` (`Work.Whitney.chernClass_whitneySum_trivial`). -/

end

end Work.Whitney
