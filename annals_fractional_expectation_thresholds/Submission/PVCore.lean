import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.Mono2

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

/-!
# Cover-cost machinery (Park--Vondrák "q-cost" framework)

All families are subsets of the power set of a finite `X`.  We develop:

* `Up H` = upward closure of a family;
* covers and the `q`-cost of a family;
* fragments and minimal fragments relative to a set `W`;
* the large-fragment families `ℒ_m` and small-fragment families `𝒮_m`.

Everything is elementary (finite sums). -/

namespace Submission
namespace PVC

universe u
variable {X : Type u} [Fintype X]

/-- upward closure of a family `H`. -/
def Up (H : Set (Set X)) : Set (Set X) := {Y | ∃ S ∈ H, S ⊆ Y}

/-- `H ⊆ ⟨G⟩`: `G` covers `H`. -/
def Covers (G H : Set (Set X)) : Prop := ∀ S ∈ H, ∃ T ∈ G, T ⊆ S

/-- q-cost of a family `G`. -/
noncomputable def ecost (q : ℝ) (G : Set (Set X)) : ℝ :=
  ∑ S : Set X, if S ∈ G then q ^ S.ncard else 0

/-- the q-cost `c_q(H)` of `H` is the infimum of cover costs. -/
noncomputable def ccost (q : ℝ) (H : Set (Set X)) : ℝ :=
  sInf {a : ℝ | ∃ G : Set (Set X), Covers G H ∧ ecost q G = a}

/-- fragments of `H` relative to `W`. -/
def Frag (H : Set (Set X)) (W : Set X) : Set (Set X) :=
  {F | ∃ S ∈ H, F = S \ W}

/-- `F` is an inclusion-minimal fragment of `H` relative to `W`. -/
def IsMinFrag (H : Set (Set X)) (W : Set X) (F : Set X) : Prop :=
  F ∈ Frag H W ∧ ∀ G, G ∈ Frag H W → G ⊆ F → G = F

/-- minimal fragments. -/
def FStar (H : Set (Set X)) (W : Set X) : Set (Set X) := {F | IsMinFrag H W F}

/-- large minimal fragments (size ≥ m). -/
def Lm (H : Set (Set X)) (W : Set X) (m : ℕ) : Set (Set X) :=
  {F | IsMinFrag H W F ∧ m ≤ F.ncard}

/-- small minimal fragments (size < m). -/
def Sm (H : Set (Set X)) (W : Set X) (m : ℕ) : Set (Set X) :=
  {F | IsMinFrag H W F ∧ F.ncard < m}

/-- `H` is `ℓ`-bounded. -/
def Bounded (H : Set (Set X)) (ℓ : ℕ) : Prop := ∀ S ∈ H, S.ncard ≤ ℓ

/-- family of sets of size exactly `n`. -/
def sizeEq (n : ℕ) : Set (Set X) := {S | S.ncard = n}

/-- every member of `H` has nonempty size at least one (no empty set in `H`). -/
def NoEmpty (H : Set (Set X)) : Prop := ∀ S ∈ H, S ≠ ∅

end PVC
end Submission
