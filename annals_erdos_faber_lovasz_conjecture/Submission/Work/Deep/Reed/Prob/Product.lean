import Submission.Work.Deep.Reed.Prob.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Product spaces: independence of events on disjoint coordinates

This module contains the second ingredient of the probability layer: the
*product* of finite probability spaces, and the fundamental independence
fact that in a product measure two events which depend on disjoint sets of
coordinates are independent.

* `FinProb.pi μ` — the product of the finite probability spaces `μ i` on
  `∀ i, Ω i` (the coordinate projections are independent),
* `DependsOn S A` — the event `A` is determined by the coordinates in `S`,
* `FinProb.pi_prob_inter_eq_mul_of_disjoint` — the independence statement.

The last statement is the form in which independence is used when applying
the Lovász Local Lemma to a family of events each of which is determined by
the random choices on a small set of vertices.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed

/-- An event in a product space **depends only on the coordinates in `S`**. -/
def DependsOn {ι : Type*} {Ω : ι → Type*} (S : Finset ι) (A : Set (∀ i, Ω i)) : Prop :=
  ∀ f g : ∀ i, Ω i, (∀ i ∈ S, f i = g i) → (f ∈ A ↔ g ∈ A)

namespace DependsOn

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {S T : Finset ι} {A B : Set (∀ i, Ω i)}

lemma univ (A : Set (∀ i, Ω i)) : DependsOn (Finset.univ : Finset ι) A :=
  fun f g h => by rw [funext fun i => h i (Finset.mem_univ i)]

lemma mono (h : DependsOn S A) (hST : S ⊆ T) : DependsOn T A :=
  fun f g hfg => h f g fun i hi => hfg i (hST hi)

lemma inter (hA : DependsOn S A) (hB : DependsOn S B) : DependsOn S (A ∩ B) :=
  fun f g h => by simp only [Set.mem_inter_iff]; rw [hA f g h, hB f g h]

lemma union (hA : DependsOn S A) (hB : DependsOn S B) : DependsOn S (A ∪ B) :=
  fun f g h => by simp only [Set.mem_union]; rw [hA f g h, hB f g h]

lemma compl (h : DependsOn S A) : DependsOn S Aᶜ :=
  fun f g hfg => not_congr (h f g hfg)

lemma diff (hA : DependsOn S A) (hB : DependsOn S B) : DependsOn S (A \ B) :=
  fun f g h => by simp only [Set.mem_sdiff]; rw [hA f g h, hB f g h]

lemma biInter {κ : Type*} {s : Finset κ} {F : κ → Set (∀ i, Ω i)}
    (h : ∀ k ∈ s, DependsOn S (F k)) : DependsOn S (⋂ k ∈ s, F k) :=
  fun f g hfg => by
    simp only [Set.mem_iInter]
    exact ⟨fun hf k hk => ((h k hk f g hfg).mp (hf k hk)),
           fun hg k hk => ((h k hk f g hfg).mpr (hg k hk))⟩

lemma biUnion {κ : Type*} {s : Finset κ} {F : κ → Set (∀ i, Ω i)}
    (h : ∀ k ∈ s, DependsOn S (F k)) : DependsOn S (⋃ k ∈ s, F k) :=
  fun f g hfg => by
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨k, hk, hf⟩ => ⟨k, hk, (h k hk f g hfg).mp hf⟩,
           fun ⟨k, hk, hg⟩ => ⟨k, hk, (h k hk f g hfg).mpr hg⟩⟩

end DependsOn

namespace FinProb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **product** of finite probability spaces: the weight of a function is
the product of the weights of its values. -/
noncomputable def pi {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i)) :
    FinProb (∀ i, Ω i) where
  wt := fun f => ∏ i, (μ i).wt (f i)
  wt_nonneg := fun f => Finset.prod_nonneg (fun i _ => (μ i).wt_nonneg (f i))
  wt_sum := by
    rw [← Fintype.prod_sum (fun i (x : Ω i) => (μ i).wt x)]
    simp [FinProb.wt_sum]

@[simp]
lemma pi_wt {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i))
    (f : ∀ i, Ω i) : (pi μ).wt f = ∏ i, (μ i).wt (f i) := rfl

end FinProb

end Work.Deep.Reed
