import Mathlib
import Submission.Work.LerayHirsch.LhGlueDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [-instance] AddCommGroup.toIntModule

/-!
# The uniform Leray–Hirsch map in every degree

`Work.LerayHirsch.LhGlueDefs` introduces the *uniform* Leray–Hirsch map

```
Work.LerayHirsch.lhAny Z k :
  ((i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) → Coh ℤ k (ProjSpace Z)
```

with the index type `lhIdx m k = {i : Fin m // 2 * (i : ℕ) ≤ k}`, mapping a family `(x_i)` to
`Σ_i π^*(x_i) ⌣ ζ^i`.  It is defined for **every** degree `k` at once, so that the Mayer–Vietoris
ladder of the Leray–Hirsch induction can be run in each degree without a parity case split.

The chapter's headline statement `Work.LerayHirsch.LerayHirschFull Z`, on the other hand, is
phrased with the *even* map `lhMap Z k` (`Σ_i π^*(x_i) ⌣ ζ^i` for `x_i ∈ H^{2(k-i)}(B)`,
`i ≤ k`) and the *odd* map `lhMapOdd Z k` (`x_i ∈ H^{2k+1-2i}(B)`).

The theorem of this file, `Work.LerayHirsch.lhAny_bijective_iff`, is the dictionary between the
two formulations:

> `∀ k, Function.Bijective (lhAny Z k)` **if and only if** `LerayHirschFull Z`.

The index type of `lhAny Z k` is `{i : Fin m // 2i ≤ k}`, which for `k = 2k'` (resp. `k = 2k'+1`)
is canonically the index type `{i : Fin m // i ≤ k'}` of `lhMap Z k'` (resp. `lhMapOdd Z k'`), and
the degree of the `i`-th component is `k - 2i` — the same module as `2(k'-i)` (resp. `2k'+1-2i`) up
to the degree cast `Work.Thom.cohTransport`, which is a `ℤ`-linear isomorphism.  Concretely:

* **even degrees** (`Work.LerayHirsch.lhAny_even_eq`): `lhAny Z (2*k') = lhMap Z k' ∘ e`, where
  `e = lhAnyEvenReindex` is the reindexing of the families along the index equivalence
  `lhAnyIdxEvenEquiv` and the degree cast `2*k' - 2*i = 2*(k'-i)`; `e` is a bijection
  (`lhAnyEvenReindex_bijective`), so the bijectivity of the two maps is equivalent;
* **odd degrees** (`Work.LerayHirsch.lhAny_odd_eq`): `lhAny Z (2*k'+1) = lhMapOdd Z k' ∘ e`, with
  `e = lhAnyOddReindex` the (transport-free) reindexing.

The identity `lhAny Z (2*k') = lhMap Z k' ∘ e` is proved summand by summand
(`lhAny_even_summand`, `lhAny_odd_summand`): both summands are
`cohTransport _ (π^*(x) ⌣ ζ^i)`, with the two degree bookkeepings (`cupChern` transports from
`2(k'-i) + 2i`, `lhAnySummand` from `k - 2i + 2i`) identified by `cohTransport_trans`, and the
transport of the first cup-product argument by the pullback `π^*` moved through the degree cast by
`Work.Whitney.cohTransport_CohMap` and `lhAny_cupH'_transport_left`.

The parity split at the end is `Nat.even_or_odd'`; since `lhAny` is the *same* map in both parities,
nothing else is needed.

No geometry of `P(E)` is used here: this is a statement about the bookkeeping of the uniform
Leray–Hirsch map versus the even/odd pair, and it is what lets the Mayer–Vietoris rung
(`LhGlueDefs`) hand its hypotheses to the chapter's consumers (`LH.lean`, `Splitting.lean`) and
vice versa.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## 1. The index equivalences `{i | 2i ≤ 2k'} ≃ {i | i ≤ k'}` (and the odd companion) -/

/-- The index of the uniform map in degree `2k'`, read as an index of `lhMap Z k'`.  This is
injective (indeed a bijection, `lhAnyIdxEvenEquiv`). -/
def lhAnyIdxEvenTo (m k' : ℕ) (i : lhIdx m (2*k')) : {j : Fin m // (j:ℕ) ≤ k'} :=
  ⟨i.1, by omega⟩

/-- The inverse of `lhAnyIdxEvenTo`: an index `j ≤ k'` is an index of the uniform map in degree
`2k'`, because `2j ≤ 2k'`. -/
def lhAnyIdxToEven (m k' : ℕ) (j : {j : Fin m // (j:ℕ) ≤ k'}) : lhIdx m (2*k') :=
  ⟨j.1, by omega⟩

/-- **The index equivalence of the even case**: `{i : Fin m // 2i ≤ 2k'} ≃ {i : Fin m // i ≤ k'}`. -/
def lhAnyIdxEvenEquiv (m k' : ℕ) : lhIdx m (2*k') ≃ {j : Fin m // (j:ℕ) ≤ k'} where
  toFun := lhAnyIdxEvenTo m k'
  invFun := lhAnyIdxToEven m k'
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The index of the uniform map in degree `2k'+1`, read as an index of `lhMapOdd Z k'`
(injective, indeed a bijection `lhAnyIdxOddEquiv`). -/
def lhAnyIdxOddTo (m k' : ℕ) (i : lhIdx m (2*k'+1)) : {j : Fin m // (j:ℕ) ≤ k'} :=
  ⟨i.1, by omega⟩

/-- The inverse of `lhAnyIdxOddTo`: an index `j ≤ k'` is an index of the uniform map in degree
`2k'+1`, because `2j ≤ 2k'+1`. -/
def lhAnyIdxToOdd (m k' : ℕ) (j : {j : Fin m // (j:ℕ) ≤ k'}) : lhIdx m (2*k'+1) :=
  ⟨j.1, by omega⟩

/-- **The index equivalence of the odd case**: `{i : Fin m // 2i ≤ 2k'+1} ≃ {i : Fin m // i ≤ k'}`. -/
def lhAnyIdxOddEquiv (m k' : ℕ) : lhIdx m (2*k'+1) ≃ {j : Fin m // (j:ℕ) ≤ k'} where
  toFun := lhAnyIdxOddTo m k'
  invFun := lhAnyIdxToOdd m k'
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## 2. Reindexing the families of the uniform map to the families of `lhMap`/`lhMapOdd` -/

/-- **The even reindexing.**  A family `(x_i)_{2i ≤ 2k'}` with `x_i ∈ H^{2k'-2i}(B)` is sent to the
family `(y_j)_{j ≤ k'}` with `y_j ∈ H^{2(k'-j)}(B)` given by the degree cast
`2k'-2j = 2(k'-j)` of `x_j`.  The cast is `Nat.mul_sub_left_distrib`; it is what makes the degrees
of the uniform family agree with the degrees used by `lhMap`. -/
def lhAnyEvenReindex (m k' : ℕ) :
    ((i : lhIdx m (2*k')) → Coh ℤ (2*k' - 2*(i:ℕ)) B) →
    ((j : {j : Fin m // (j:ℕ) ≤ k'}) → Coh ℤ (2*(k' - (j:ℕ))) B) :=
  fun x j => cohTransport (Nat.mul_sub_left_distrib 2 k' (j:ℕ)).symm (x (lhAnyIdxToEven m k' j))

/-- The inverse reindexing of `lhAnyEvenReindex`. -/
def lhAnyEvenUnreindex (m k' : ℕ) :
    ((j : {j : Fin m // (j:ℕ) ≤ k'}) → Coh ℤ (2*(k' - (j:ℕ))) B) →
    ((i : lhIdx m (2*k')) → Coh ℤ (2*k' - 2*(i:ℕ)) B) :=
  fun y i => cohTransport (Nat.mul_sub_left_distrib 2 k' (i:ℕ)) (y (lhAnyIdxEvenTo m k' i))

/-- **The odd reindexing.**  In odd degrees the degree of the `i`-th summand is the *same*
expression `2k'+1-2i` for `lhAny` and for `lhMapOdd`, so the reindexing is a pure relabelling of
the index set: no degree cast is needed. -/
def lhAnyOddReindex (m k' : ℕ) :
    ((i : lhIdx m (2*k'+1)) → Coh ℤ (2*k'+1 - 2*(i:ℕ)) B) →
    ((j : {j : Fin m // (j:ℕ) ≤ k'}) → Coh ℤ (2*k'+1 - 2*(j:ℕ)) B) :=
  fun x j => x (lhAnyIdxToOdd m k' j)

/-- The inverse reindexing of `lhAnyOddReindex`. -/
def lhAnyOddUnreindex (m k' : ℕ) :
    ((j : {j : Fin m // (j:ℕ) ≤ k'}) → Coh ℤ (2*k'+1 - 2*(j:ℕ)) B) →
    ((i : lhIdx m (2*k'+1)) → Coh ℤ (2*k'+1 - 2*(i:ℕ)) B) :=
  fun y i => y (lhAnyIdxOddTo m k' i)

/-- `lhAnyEvenUnreindex` is a left inverse of `lhAnyEvenReindex`: the two degree casts cancel by
`Work.Whitney.cohTransport_trans` and proof irrelevance. -/
theorem lhAnyEvenReindex_left_inv (m k' : ℕ) :
    Function.LeftInverse (lhAnyEvenUnreindex (B:=B) m k') (lhAnyEvenReindex (B:=B) m k') := by
  intro x; funext i
  rw [lhAnyEvenUnreindex, lhAnyEvenReindex, Work.Whitney.cohTransport_trans]
  simp only [Work.Thom.cohTransport_rfl]
  rfl

/-- `lhAnyEvenUnreindex` is a right inverse of `lhAnyEvenReindex`. -/
theorem lhAnyEvenReindex_right_inv (m k' : ℕ) :
    Function.RightInverse (lhAnyEvenUnreindex (B:=B) m k') (lhAnyEvenReindex (B:=B) m k') := by
  intro y; funext j
  rw [lhAnyEvenReindex, lhAnyEvenUnreindex, Work.Whitney.cohTransport_trans]
  simp only [Work.Thom.cohTransport_rfl]
  rfl

/-- `lhAnyOddUnreindex` is a left inverse of `lhAnyOddReindex` (pure relabelling). -/
theorem lhAnyOddReindex_left_inv (m k' : ℕ) :
    Function.LeftInverse (lhAnyOddUnreindex (B:=B) m k') (lhAnyOddReindex (B:=B) m k') := by
  intro x; funext i; rfl

/-- `lhAnyOddUnreindex` is a right inverse of `lhAnyOddReindex` (pure relabelling). -/
theorem lhAnyOddReindex_right_inv (m k' : ℕ) :
    Function.RightInverse (lhAnyOddUnreindex (B:=B) m k') (lhAnyOddReindex (B:=B) m k') := by
  intro y; funext j; rfl

/-- **The even reindexing is a bijection** (its two-sided inverse is `lhAnyEvenUnreindex`). -/
theorem lhAnyEvenReindex_bijective (m k' : ℕ) :
    Function.Bijective (lhAnyEvenReindex (B:=B) m k') :=
  ⟨Function.LeftInverse.injective (lhAnyEvenReindex_left_inv (B:=B) m k'),
   Function.RightInverse.surjective (lhAnyEvenReindex_right_inv (B:=B) m k')⟩

/-- **The odd reindexing is a bijection**. -/
theorem lhAnyOddReindex_bijective (m k' : ℕ) :
    Function.Bijective (lhAnyOddReindex (B:=B) m k') :=
  ⟨Function.LeftInverse.injective (lhAnyOddReindex_left_inv (B:=B) m k'),
   Function.RightInverse.surjective (lhAnyOddReindex_right_inv (B:=B) m k')⟩

/-! ## 3. The degree cast commutes with the cup product

The cup product `Work.Cohomology.cupH'` is only defined between *named* degrees, whereas the degree
casts `Work.Thom.cohTransport` connect the different names (`2k'-2i` and `2(k'-i)`) under which the
same module appears.  Since the cast is an isomorphism of `ModuleCat ℤ` and `cupH'`'s two arguments
are carried by the same `H^*`, the cast of the left argument may be pushed outside the product. -/

/-- **The degree cast commutes with the cup product in the first variable**: casting the left
argument of `⌣` from degree `n` to degree `n'` casts the product from degree `n + mm` to degree
`n' + mm`. -/
theorem lhAny_cupH'_transport_left {B : Type} [TopologicalSpace B] {n n' mm : ℕ} (h : n = n')
    (a : Coh ℤ n B) (b : Coh ℤ mm B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n' mm (cohTransport h a) b
      = cohTransport (congrArg (· + mm) h)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n mm a b) := by
  subst h
  simp

/-! ## 4. The summands of `lhAny` are the summands of `lhMap`/`lhMapOdd` -/

/-- **The even summands agree** (up to the reindexing and the degree cast of the `i`-th component):
the `i`-th summand of `lhAny Z (2*k')` is the `i`-th summand of `lhMap Z k'`.

Both sides are `cohTransport _ (π^*(x_i) ⌣ ζ^i)`; the only difference is that the uniform map
remembers the degree of `x_i` as `2k'-2i` while `lhMap` uses `2(k'-i)`, and the degree of the
product accordingly (`2k'-2i + 2i` versus `2(k'-i) + 2i`).  The reindexing transports `x_i` along
`Nat.mul_sub_left_distrib`, and `lhAny_cupH'_transport_left` moves that transport through `⌣`; the
remaining transports are merged by `cohTransport_trans` and proof irrelevance. -/
theorem lhAny_even_summand (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k' : ℕ) (i : lhIdx m (2*k'))
    (x : (i : lhIdx m (2*k')) → Coh ℤ (2*k' - 2*(i:ℕ)) B) :
    lhAnySummand Z (2*k') i x
      = lhTerm Z k' (lhAnyIdxEvenTo m k' i)
          (lhAnyEvenReindex (B:=B) m k' x (lhAnyIdxEvenTo m k' i)) := by
  rw [lhAnySummand, lhTerm_def, Work.Whitney.cupChern_def, Work.Whitney.cohTransport_trans]
  simp only [LinearMap.comp_apply, Work.Thom.cohTransportLM_apply, evalLM]
  rw [lhAnyEvenReindex, Work.Whitney.cohTransport_CohMap,
    show ∀ {n n' mm : ℕ} (h : n = n') (a : Coh ℤ n (ProjSpace Z)) (b : Coh ℤ mm (ProjSpace Z)),
      Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z)) n' mm (cohTransport h a) b
        = cohTransport (congrArg (· + mm) h)
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z)) n mm a b) from by
      intro n n' mm h a b; subst h; simp,
    Work.Whitney.cohTransport_trans]
  rfl

/-- **The odd summands agree**: the `i`-th summand of `lhAny Z (2*k'+1)` is the `i`-th summand of
`lhMapOdd Z k'`; here no degree cast is needed at all. -/
theorem lhAny_odd_summand (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k' : ℕ) (i : lhIdx m (2*k'+1))
    (x : (i : lhIdx m (2*k'+1)) → Coh ℤ (2*k'+1 - 2*(i:ℕ)) B) :
    lhAnySummand Z (2*k'+1) i x
      = lhTermOdd Z k' (lhAnyIdxOddTo m k' i)
          (lhAnyOddReindex (B:=B) m k' x (lhAnyIdxOddTo m k' i)) := by
  rw [lhAnySummand, lhTermOdd, lhAnyOddReindex]
  rfl

/-! ## 5. `lhAny` is the Leray–Hirsch map, reindexed -/

/-- **The uniform Leray–Hirsch map in an even degree is the even Leray–Hirsch map**, up to the
reindexing of the families: `lhAny Z (2*k') = lhMap Z k' ∘ lhAnyEvenReindex` (as functions).  The
sums are matched index by index through the index equivalence `lhAnyIdxEvenEquiv`
(`Equiv.sum_comp`) and the summand-wise identity `lhAny_even_summand`. -/
theorem lhAny_even_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k' : ℕ) (x : (i : lhIdx m (2*k')) → Coh ℤ (2*k' - 2*(i:ℕ)) B) :
    lhAny Z (2*k') x = lhMap Z k' (lhAnyEvenReindex (B:=B) m k' x) := by
  rw [lhAny_apply, lhAnyLM, lhMap_apply, LinearMap.sum_apply]
  rw [← Equiv.sum_comp (lhAnyIdxEvenEquiv m k')
    (fun j => lhTerm Z k' j (lhAnyEvenReindex (B:=B) m k' x j))]
  exact Finset.sum_congr rfl (fun i _ => lhAny_even_summand Z k' i x)

/-- **The uniform Leray–Hirsch map in an odd degree is the odd Leray–Hirsch map**:
`lhAny Z (2*k'+1) = lhMapOdd Z k' ∘ lhAnyOddReindex` (as functions). -/
theorem lhAny_odd_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k' : ℕ) (x : (i : lhIdx m (2*k'+1)) → Coh ℤ (2*k'+1 - 2*(i:ℕ)) B) :
    lhAny Z (2*k'+1) x = lhMapOdd Z k' (lhAnyOddReindex (B:=B) m k' x) := by
  rw [lhAny_apply, lhAnyLM, lhMapOdd, LinearMap.sum_apply]
  rw [← Equiv.sum_comp (lhAnyIdxOddEquiv m k')
    (fun j => lhTermOdd Z k' j (lhAnyOddReindex (B:=B) m k' x j))]
  exact Finset.sum_congr rfl (fun i _ => lhAny_odd_summand Z k' i x)

/-! ## 6. Bijectivity transfers through the reindexing -/

/-- **Even degrees: the uniform map is bijective in degree `2k'` exactly when the even
Leray–Hirsch map is.**  This is `lhAny_even_eq` together with the fact that the reindexing is a
bijection (`Function.Bijective.of_comp_iff`). -/
theorem lhAny_even_bijective_iff (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (k' : ℕ) :
    Function.Bijective (lhAny Z (2*k')) ↔ Function.Bijective (lhMap Z k') := by
  have hcomp : lhAny Z (2*k') = lhMap Z k' ∘ lhAnyEvenReindex (B:=B) m k' := by
    funext x; exact lhAny_even_eq Z k' x
  rw [hcomp]
  exact Function.Bijective.of_comp_iff (lhMap Z k') (lhAnyEvenReindex_bijective (B:=B) m k')

/-- **Odd degrees: the uniform map is bijective in degree `2k'+1` exactly when the odd
Leray–Hirsch map is.** -/
theorem lhAny_odd_bijective_iff (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (k' : ℕ) :
    Function.Bijective (lhAny Z (2*k'+1)) ↔ Function.Bijective (lhMapOdd Z k') := by
  have hcomp : lhAny Z (2*k'+1) = lhMapOdd Z k' ∘ lhAnyOddReindex (B:=B) m k' := by
    funext x; exact lhAny_odd_eq Z k' x
  rw [hcomp]
  exact Function.Bijective.of_comp_iff (lhMapOdd Z k') (lhAnyOddReindex_bijective (B:=B) m k')

/-! ## 7. The uniform map in every degree is Leray–Hirsch -/

/-- **The uniform Leray–Hirsch map is bijective in every degree if and only if the even and odd
Leray–Hirsch maps are** — i.e. `∀ k, Bijective (lhAny Z k) ↔ LerayHirschFull Z`.

Forward: degrees `2k'` and `2k'+1` give, through `lhAny_even_bijective_iff` and
`lhAny_odd_bijective_iff`, the two halves of `LerayHirschFull`.  Backward: a general degree `k` is
`2k'` or `2k'+1` for some `k'` (`Nat.even_or_odd'`), and the corresponding map is bijective. -/
theorem lhAny_bijective_iff {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    (∀ k : ℕ, Function.Bijective (Work.LerayHirsch.lhAny Z k)) ↔
      Work.LerayHirsch.LerayHirschFull Z := by
  constructor
  · intro h
    refine ⟨fun k' => (lhAny_even_bijective_iff Z k').mp (h (2*k')),
      fun k' => (lhAny_odd_bijective_iff Z k').mp (h (2*k'+1))⟩
  · rintro ⟨he, ho⟩ k
    obtain ⟨k', hk | hk⟩ := Nat.even_or_odd' k
    · rw [hk]
      exact (lhAny_even_bijective_iff Z k').mpr (he k')
    · rw [hk]
      exact (lhAny_odd_bijective_iff Z k').mpr (ho k')

end

end Work.LerayHirsch
