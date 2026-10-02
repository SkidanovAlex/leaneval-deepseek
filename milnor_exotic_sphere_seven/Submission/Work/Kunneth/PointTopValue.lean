import Mathlib
import Submission.Work.Kunneth.PointBasic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The top Leray–Hirsch summand for `P(ε^{n+1}) = ℂPⁿ`

This module computes the `i = k` ("top") summand of the Leray–Hirsch decomposition of
`H^{2k}(P(ε^{n+1});ℤ)` for the trivial bundle over the point:

```
Work.LerayHirsch.lhTerm (trivCore (n+1)) k (iTop n k hk) (a • oneHtop n k hk)
  = a • Work.LerayHirsch.zetaPow (trivCore (n+1)) k
```

i.e. the summand `π^*(x) ⌣ ζ^k` of `lhMap` evaluated on the class `a • 1 ∈ H⁰(pt;ℤ)` in the
degree of the index `iTop n k hk = k` is the `k`-th power of the hyperplane class `ζ` of
`P(ε^{n+1})`.  Together with `Work.LerayHirsch.lhMap_eq_single` this identifies the image of the
Leray–Hirsch map on the family supported at the top index with the multiples of `ζ^k`, i.e. it is
the inclusion "`H^{2k}(P(ε^{n+1})) ⊇ ℤ⟨ζ^k⟩`" used to show that `ζ^k` is in the image of `lhMap`
(surjectivity of the Leray–Hirsch map needs at most this for the powers of `ζ`, see
`Work.Kunneth.keyLH`).

The content is the two unit laws of the graded cup product (`1 ⌣ y = y`, and `π^*` fixes `1`
— `Work.Thom.CohMap_oneH`) together with the bookkeeping of the degree casts
`Work.Thom.cohTransport` (the index `iTop n k hk` has value `k`, so the degree
`2 * (k - i)` is `0` up to a cast).  The auxiliary lemmas

* `Work.Kunneth.cupH'_zsmul_left`, `Work.Kunneth.cupChern_zsmul_left` — the graded product is
  `ℤ`-linear in its first argument (note the two `ℤ`-actions on cohomology, the canonical
  `ZSMul.toSMul` of the `•` notation and the `Module ℤ` action of the linear maps, bridged by
  `int_smul_eq_zsmul`);
* `Work.Kunneth.cupChern_cohTransport_left` — the degree cast commutes with the graded product in
  the first argument;
* `Work.Kunneth.lhTerm_zsmul` — the Leray–Hirsch summand is `ℤ`-linear in the coefficient;

are the general tools with which the computation is done.
-/

namespace Work.Kunneth

noncomputable section

/-! ## The two scalar actions on cohomology are the same

The `•` notation on `Coh ℤ n B` resolves to the canonical `ZSMul.toSMul` of an additive
commutative group, whereas the lemmas about linear maps (`Work.Cohomology.cupH'_smul_left`, which
is stated for a variable ring `R`) produce the `SMul` coming from the `Module ℤ` structure.  The
two agree by definition, but not definitionally, so every transfer between them goes through
Mathlib's bridge `int_smul_eq_zsmul`. -/

/-- **`cupH'` is `ℤ`-linear in its first argument**, in the normalisation of the `•` notation of
this file. -/
theorem cupH'_zsmul_left {B : Type} [TopologicalSpace B] {n m : ℕ} (c : ℤ)
    (x : Work.Thom.Coh ℤ n B) (y : Work.Thom.Coh ℤ m B) :
    ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n m) (c • x)) y
      = c • (((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n m) x) y) := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.Coh ℤ n B)) c x]
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.Coh ℤ (n + m) B)) c
        (((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n m) x) y)]
  exact Work.Cohomology.cupH'_smul_left ℤ (Work.Whitney.ssB B) n m c x y

/-- **The graded cup product is `ℤ`-linear in its first argument.** -/
theorem cupChern_zsmul_left {B : Type} [TopologicalSpace B] (a b : ℕ) (c : ℤ)
    (x : Work.Thom.Coh ℤ (2 * a) B) (y : Work.Thom.Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b (c • x) y = c • Work.Whitney.cupChern a b x y := by
  rw [Work.Whitney.cupChern_def, Work.Whitney.cupChern_def]
  rw [← Work.Thom.cohTransport_zsmul]
  exact congrArg (Work.Thom.cohTransport (Nat.mul_add 2 a b).symm) (cupH'_zsmul_left c x y)

/-! ## The degree casts in the arguments of the graded product -/

/-- **The degree cast commutes with the graded product in the first argument.**  Both sides are
`cohTransport` of `cupChern a b x y`, along two (propositionally equal) identifications of the same
two degrees; the result follows from the commutativity of the cast with `cupH'`
(`Work.LerayHirsch.cupH'_cast_left`), the composition of casts
(`Work.Whitney.cohTransport_trans`) and the proof-irrelevance of `cohTransport`
(`Work.LerayHirsch.cohTransport_congr_proof`). -/
theorem cupChern_cohTransport_left {B : Type} [TopologicalSpace B] {a a' b : ℕ}
    (h : 2 * a = 2 * a') (x : Work.Thom.Coh ℤ (2 * a) B) (y : Work.Thom.Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a' b (Work.Thom.cohTransport h x) y
      = Work.Thom.cohTransport (by omega : 2 * (a + b) = 2 * (a' + b))
          (Work.Whitney.cupChern a b x y) := by
  rw [Work.Whitney.cupChern_def, Work.Whitney.cupChern_def, Work.LerayHirsch.cupH'_cast_left]
  refine (Work.Whitney.cohTransport_trans _ _ _).trans
    ((Work.LerayHirsch.cohTransport_congr_proof _ _).trans
      (Work.Whitney.cohTransport_trans _ _ _).symm)

/-! ## Linearity of the Leray–Hirsch summand -/

/-- **The Leray–Hirsch summand is `ℤ`-linear in its coefficient**: every ingredient of
`Work.LerayHirsch.lhTerm` — the pullback `π^*`, the graded product and the degree cast — is. -/
theorem lhTerm_zsmul {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (c : ℤ)
    (x : Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.LerayHirsch.lhTerm Z k i (c • x) = c • Work.LerayHirsch.lhTerm Z k i x := by
  rw [Work.LerayHirsch.lhTerm_def, Work.LerayHirsch.lhTerm_def, Work.Thom.CohMap_zsmul,
    cupChern_zsmul_left, Work.Thom.cohTransport_zsmul]

/-! ## The computation -/

/-- **The top Leray–Hirsch summand for `P(ε^{n+1})` on the unit class is `ζ^k`.**  Here
`iTop n k hk` is the index `i = k`, so the summand is `π^*(1) ⌣ ζ^k`, `π^*` fixes the unit class
(`Work.Thom.CohMap_oneH`) and `1 ⌣ ζ^k = ζ^k`
(`Work.LerayHirsch.cohTransport_cupChern_one_left`).  The index `iTop n k hk` is `k`, so the
degree `2 * (k - i)` of the coefficient is `0` only up to the cast `Work.Thom.cohTransport` — the
whole content of the proof is the bookkeeping of that cast
(`Work.Kunneth.cupChern_cohTransport_left`). -/
theorem lhTerm_iTop_oneHtop (n k : ℕ) (hk : k ≤ n) :
    Work.LerayHirsch.lhTerm (Work.LerayHirsch.trivCore (n + 1)) k (iTop n k hk)
        (oneHtop n k hk)
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k := by
  rw [Work.LerayHirsch.lhTerm_def, oneHtop, Work.Thom.cohTransport_CohMap, Work.Thom.CohMap_oneH]
  have h2 := cupChern_cohTransport_left (a := 0) (a' := k - ↑↑(iTop n k hk))
    (b := ↑↑(iTop n k hk)) (h := by rw [Nat.mul_zero]; exact oneHtop_deg n k hk)
    (x := Work.Cohomology.oneH ℤ (Work.Whitney.ssB
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))))
    (y := Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) ↑↑(iTop n k hk))
  exact (congrArg (Work.Thom.cohTransport _) h2).trans
    ((Work.Whitney.cohTransport_trans _ _ _).trans
      ((Work.LerayHirsch.cohTransport_congr_proof _ _).trans
        (Work.LerayHirsch.cohTransport_cupChern_one_left k
          (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k))))

/-- **`Work.Kunneth.PointTopValue`.**  The value of the top (`i = k`) Leray–Hirsch summand of
`P(ε^{n+1}) = ℂPⁿ` on `a • 1 ∈ H⁰(pt;ℤ)` is `a • ζ^k`: the linearity of the summand
(`Work.Kunneth.lhTerm_zsmul`) reduces to the case `a = 1`, which is
`Work.Kunneth.lhTerm_iTop_oneHtop`. -/
theorem PointTopValue (n k : ℕ) (hk : k ≤ n) (a : ℤ) :
    Work.LerayHirsch.lhTerm (Work.LerayHirsch.trivCore (n + 1)) k (iTop n k hk)
        (a • oneHtop n k hk)
      = a • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k := by
  rw [lhTerm_zsmul, lhTerm_iTop_oneHtop]

end

end Work.Kunneth
