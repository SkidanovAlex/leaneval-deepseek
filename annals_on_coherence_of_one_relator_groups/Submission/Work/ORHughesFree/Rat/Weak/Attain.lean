import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.Weak.A_add_left
import Submission.Work.ORHughesFree.Rat.Weak.A_ofGroup
import Submission.Work.ORHughesFree.Rat.Weak.A_ratOp
import Submission.Work.ORHughesFree.Rat.Weak.Structural

/-!
# The steps of the `A`-attainment

`Weak.FA y = {V ≤ U | y ∈ Rat(V)}` is the one-sided family; the target theorem is proved once we
know that every `FA y` has a least element `σA y` (`Weak.IsSource σA`) and that the family
`{σA (α * φ u)}` has a least element (`Weak.exists_source_subgroup_weak_of_source`).

The least element of an `FA y` is produced by induction on the complexity `Tree y`, using the
four-way decomposition `RatU.exists_decomp`, and this file discharges the three inductive steps:

* `FA_ratOp` : `FA (⋄ y) = FA y` (the `⋄`-step);
* `FA_add_source` : if `FA x = ↑(σA x)` and `FA y = ↑(σA y)` then
  `FA (x + y) = ↑(σA x ⊔ σA y)` (the sum step, from `FA_add`);
* `FA_mul_eq_of_min` : if `FA` is already given by `σA` along the two families of *shifted*
  factors `a * φ x` and `φ x⁻¹ * b` (that is what the induction hypothesis provides, since
  `Tree (a * φ x) = Tree a < Tree (a * b)`), if the splitting formula `hsplit` holds, and if the
  family `x ↦ σA (a * φ x) ⊔ σA (φ x⁻¹ * b)` has a least element (the remaining input), then
  `FA (a * b)` has a least element, namely the value of that family at a minimising `x₀`.

The product step is the heart: from `a * φ x ∈ Rat(V)` and `φ x⁻¹ * b ∈ Rat(V)` one gets
`a * b ∈ Rat(V)`, so the value at every `x` — in particular at the minimiser — lies in
`FA (a * b)`; and conversely every member of `FA (a * b)` contains one of the values, by the
splitting formula.
-/

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel

variable {U : Type} [Group U]

/-- **The `⋄`-step**: `y ∈ Rat(V)` iff `⋄ y ∈ Rat(V)`. -/
theorem FA_ratOp (y : RatU U) : FA (RatU.ratOp y) = FA y := by
  ext V
  constructor
  · intro h
    exact A_ratOp h
  · intro h
    exact A_ratOp_mem h

/-- **The sum step**: the `FA`-family of a sum is the intersection of those of the summands, so if
both summands have least elements then so does the sum. -/
theorem FA_add_source (σA : RatU U → Subgroup U) {x y : RatU U}
    (hx : FA x = Set.Ici (σA x)) (hy : FA y = Set.Ici (σA y)) :
    FA (x + y) = Set.Ici (σA x ⊔ σA y) := by
  ext V
  rw [FA_add, hx, hy, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ici, Set.mem_Ici, sup_le_iff]

/-- **The product step.**  Assume `σA` is a source function along the two families of shifted
factors (`hσ`), that the splitting formula `hsplit` holds, and that the family
`x ↦ σA (a * φ x) ⊔ σA (φ x⁻¹ * b)` has a least element (`hmin`).  Then `FA (a * b)` has a least
element, namely the value of that family at a minimising `x₀`.

**Warning.**  `hsplit` is *not* available in the workspace model for arbitrary `a b : RatU U`: the
file `Submission/Work/ORHughesFree/Rat/Weak/FA_mul_eq_iUnion.lean` proves
`Weak.FA_mul_eq_iUnion_refuted`, showing that the identity
`FA (a*b) = ⋃ x, (FA (a*φ x) ∩ FA (φ x⁻¹*b))` fails already for `a = 0` (where `FA 0` is the whole
lattice) and for `a = ⋄ 0`.  The cause is that `⋄` is total in `RatU U` with `⋄ 0 ≠ 0`, so `0`
and its `⋄`-iterates lie in `Rat(A V)` for **every** `V ≤ U`; the paper's model
`Rat(U) = ℕ[U ♮ X] ∖ {0}` has no such elements.  In the induction this step is only needed for
`(a, b)` the two *words* produced by `RatU.exists_decomp`, so a usable version of `hsplit` has to
be restricted (and proved) for those; the statement below is the conditional form. -/
theorem FA_mul_eq_of_min (σA : RatU U → Subgroup U) (hσ : ∀ y : RatU U, FA y = Set.Ici (σA y))
    (hsplit : ∀ a b : RatU U, FA (a * b) =
      ⋃ x : U, (FA (a * RatU.ofGroup x) ∩ FA (RatU.ofGroup x⁻¹ * b)))
    (hmin : ∀ a b : RatU U, ∃ x₀ : U, ∀ x : U,
      σA (a * RatU.ofGroup x₀) ⊔ σA (RatU.ofGroup x₀⁻¹ * b) ≤
        σA (a * RatU.ofGroup x) ⊔ σA (RatU.ofGroup x⁻¹ * b))
    (a b : RatU U) :
    ∃ x₀ : U, FA (a * b) =
      Set.Ici (σA (a * RatU.ofGroup x₀) ⊔ σA (RatU.ofGroup x₀⁻¹ * b)) := by
  obtain ⟨x₀, hx₀⟩ := hmin a b
  refine ⟨x₀, ?_⟩
  ext V
  rw [Set.mem_Ici]
  constructor
  · intro hV
    rw [hsplit a b] at hV
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hV
    have h1 : σA (a * RatU.ofGroup x) ≤ V := by
      have h := hx.1
      rw [hσ (a * RatU.ofGroup x), Set.mem_Ici] at h
      exact h
    have h2 : σA (RatU.ofGroup x⁻¹ * b) ≤ V := by
      have h := hx.2
      rw [hσ (RatU.ofGroup x⁻¹ * b), Set.mem_Ici] at h
      exact h
    exact le_trans (hx₀ x) (sup_le h1 h2)
  · intro hm
    have hmem : σA (a * RatU.ofGroup x₀) ⊔ σA (RatU.ofGroup x₀⁻¹ * b) ∈ FA (a * b) := by
      have ha : a * RatU.ofGroup x₀ ∈
          Rat.A (σA (a * RatU.ofGroup x₀) ⊔ σA (RatU.ofGroup x₀⁻¹ * b)) := by
        refine Rat.A_mono le_sup_left ?_
        have h : σA (a * RatU.ofGroup x₀) ∈ FA (a * RatU.ofGroup x₀) := by
          rw [hσ (a * RatU.ofGroup x₀), Set.mem_Ici]
        exact h
      have hb : RatU.ofGroup x₀⁻¹ * b ∈
          Rat.A (σA (a * RatU.ofGroup x₀) ⊔ σA (RatU.ofGroup x₀⁻¹ * b)) := by
        refine Rat.A_mono le_sup_right ?_
        have h : σA (RatU.ofGroup x₀⁻¹ * b) ∈ FA (RatU.ofGroup x₀⁻¹ * b) := by
          rw [hσ (RatU.ofGroup x₀⁻¹ * b), Set.mem_Ici]
        exact h
      have h : a * b = (a * RatU.ofGroup x₀) * (RatU.ofGroup x₀⁻¹ * b) := by
        rw [mul_assoc, ← mul_assoc (RatU.ofGroup x₀) (RatU.ofGroup x₀⁻¹) b,
          ofGroup_mul_inv, one_mul]
      rw [h]
      exact (ASub (σA (a * RatU.ofGroup x₀) ⊔ σA (RatU.ofGroup x₀⁻¹ * b))).mul_mem ha hb
    exact Rat.A_mono hm hmem

end Work.ORHughesFree.Rat.Weak
