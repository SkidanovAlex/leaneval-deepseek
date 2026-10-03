import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.OrbitF
import Submission.Work.ORHughesFree.Rat.Psi_mem_A_iff
import Submission.Work.ORHughesFree.Rat.A_ratOp
import Submission.Work.ORHughesFree.Rat.Weak.Assembly
import Submission.Work.ORHughesFree.Rat.Weak.Attain
import Submission.Work.ORHughesFree.Rat.Weak.Structural
import Submission.Work.ORHughesFree.Rat.first_letter
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.mem_NUV_of_list
-- (the imports of `Rat.exists_min_pair` and its chain have been quarantined: their statements
--  `Rat.NUV_ugne_coset_or_univ`, `Rat.T_subset_mul_of_least`, ... are FALSE in the model `RatU`,
--  and the proof below does not use them.)
import Submission.Work.ORHughesFree.Rat.exists_inv_ratOp
import Submission.Work.ORHughesFree.Rat.PhiCoset
import Submission.Work.ORHughesFree.Rat.exists_source_fg
import Submission.Work.ORHughesFree.Rat.FreeProduct.Model
import Submission.Work.ORHughesFree.Rat.Word
import Submission.Work.ORHughesFree.RatU.mul_ne_zero
import Submission.Work.ORHughesFree.RatU.add_eq_zero_iff
import Submission.Work.ORHughesFree.Rat.Source.Setup
import Submission.Work.ORHughesFree.Rat.Source.Induction
import Submission.Work.ORHughesFree.Rat.Source.F_left_translate
import Submission.Work.ORHughesFree.Rat.Source.F_add
import Submission.Work.ORHughesFree.Rat.Source.FL_add
import Submission.Work.ORHughesFree.Rat.Source.F_mul2
import Submission.Work.ORHughesFree.Rat.Source.FL_mul2
import Submission.Work.ORHughesFree.Rat.exists_source_subgroup_weak

/-!
# The source subgroup of an element of `Rat(U)` ([DHS04, Theorem 5.7])

This file proves `Work.ORHughesFree.Rat.source_subgroup_exists`: for every `α : RatU U` the family

`Rat.F α = {V ≤ U | ∃ u β, RatU.ofSubgroup V β * RatU.ofGroup u = α}`

has a least element, which is finitely generated.

## Structure of the development

The model here is `RatU U`, the initial *total* rational `U`-semiring.  By the axiom
`RationalUSemiring.ratOp_zero` this is the paper's `Rat(U) ∪ {0}`: the spurious element `⋄0`
satisfies `⋄0 = 0`.  Consequently no *reachable* letter of the free product `U ♮ X` is
degenerate: for `x ≠ 0` the support of `Psi x` consists of words whose `X`-letters carry
non-zero indices.

The proof follows [DHS04, §5].  The essential combinatorial input is the *translate dichotomy*
`Rat.Dich.both_of_ne_zero`: for `x ≠ 0` and `b ∈ Rat.A V`, every left or right translate of `b`
that lands in `Rat.A V` comes from an element of `V`.  It gives the *coset structure* of the
translate sets (`Rat.Source.T_eq_coset`, `Rat.Source.TL_eq_coset`), and hence, by
well-founded induction on the complexity `Rat.treeOfRat U α` along the four-way decomposition
`RatU.exists_decomp`, the least element of `Rat.F α`:

* `Rat.Source.Induction.exists_least_of_cases` : the induction, from the four case lemmas
  `Rat.Source.F_add`, `Rat.Source.FL_add` (the sum case) and `Rat.Source.F_mul`,
  `Rat.Source.FL_mul` (the product case), together with the equivariance
  `Rat.Source.F_left_translate` of `Rat.F` under left translation;
* `exists_source_subgroup_weak_of_le` (in `Rat/exists_source_subgroup_weak.lean`) finishes: the
  least element of `Rat.F α` is finitely generated.

The two auxiliary statements [DHS04, Lemma 5.2(iv), (v)] (`⟨Q⟩·U = U ♮ X` and `P·U = Rat(U)∖{0}`)
for the notions `Rat.InH`/`Rat.InP` below are proved in `Rat/Src/exists_inH_mul_ofGroup.lean` and
`Rat/Src/exists_inP_mul_ofGroup.lean`; they are not needed for the argument used here.
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

variable {U : Type} [Group U]

mutual
  /-- `InH x`: `x` is a *word* over the primitive elements, i.e. a product of letters `⋄a` with `a`
  primitive ([DHS04, Definition 5.1], the set denoted `⟨Q⟩`). -/
  inductive InH : RatU U → Prop
    /-- the empty product -/
    | one : InH 1
    /-- a letter `⋄a` with `a` primitive -/
    | letter {a : RatU U} (ha : InP a) : InH (RatU.ratOp a)
    /-- a product of two words -/
    | mul {x y : RatU U} (hx : InH x) (hy : InH y) : InH (x * y)

  /-- `InP x`: `x` is *primitive* ([DHS04, Definition 5.1], the set denoted `P`), i.e. `x = 1`, or
  a word, or a sum whose first summand is a word and whose second summand is non-zero. -/
  inductive InP : RatU U → Prop
    /-- a word is primitive -/
    | h {x : RatU U} (hx : InH x) : InP x
    /-- a sum with a word summand -/
    | add {h y : RatU U} (hh : InH h) (hy : y ≠ 0) : InP (h + y)
end

/-- `1` is a word. -/
theorem inH_one : InH (1 : RatU U) := InH.one

/-- `1` is primitive. -/
theorem inP_one : InP (1 : RatU U) := InP.h InH.one

/-- A `⋄`-value of a primitive element is a word. -/
theorem InP.ratOp {a : RatU U} (ha : InP a) : InH (RatU.ratOp a) := InH.letter ha

/-- **Every element of `Rat(U)` has a least source subgroup**: the family `Rat.F α` has a least
element.  This is the `F`-part of the induction `Rat.Source.exists_least_of_cases`. -/
theorem exists_leastF (α : RatU U) : ∃ S : Subgroup U, IsLeastF α S :=
  (exists_least_of_cases (U := U) Source.F_left_translate Source.F_add Source.FL_add
    Source.SF.F_mul Source.SF.FL_mul α).1

theorem source_subgroup_exists {U : Type} [Group U] (α : Work.ORHughesFree.RatU U) :
    ∃ (S : Subgroup U), S.FG ∧
      (∃ (u : U) (β : Work.ORHughesFree.RatU ↥S),
        Work.ORHughesFree.RatU.ofSubgroup S β * Work.ORHughesFree.RatU.ofGroup u = α) ∧
      (∀ (V : Subgroup U) (u : U) (β : Work.ORHughesFree.RatU ↥V),
        Work.ORHughesFree.RatU.ofSubgroup V β * Work.ORHughesFree.RatU.ofGroup u = α → S ≤ V) :=
  exists_source_subgroup_weak_of_le (fun β => exists_leastF β) α

end Work.ORHughesFree.Rat
