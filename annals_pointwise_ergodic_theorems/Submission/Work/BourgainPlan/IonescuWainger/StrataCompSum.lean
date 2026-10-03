import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs

/-!
# Sums over the strata square-function index set

The pair set `strataCompPairSet S k` of Tao's square function is the image of the `sigma`-type
```
{ p : Sigma fun A₀ : Finset ℕ => Circle // p.1 ∈ S.powerset.filter (·.card ≤ k)
                                    ∧ p.2 ∈ strataCompFinset S k p.1 }
```
under the injective map `p ↦ (p.1, p.2)`.  This file records the resulting reindexing of sums,
`sum_strataCompPairSet`, which turns a sum over the pair set into the nested sum
`∑_{A₀ ∈ binom(S,≤k)} ∑_{α ∈ Σ_{(A₀)}}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- The `sigma`-type finset whose image is `strataCompPairSet`. -/
noncomputable def strataCompSigmaSet (S : Finset ℕ) (k : ℕ) :
    Finset (Σ _ : Finset ℕ, Circle) :=
  (S.powerset.filter (fun A₀ => A₀.card ≤ k)).sigma (fun A₀ => strataCompFinset S k A₀)

/-- `strataCompPairSet` is the image of `strataCompSigmaSet` under `p ↦ (p.1, p.2)`. -/
theorem strataCompPairSet_eq_image (S : Finset ℕ) (k : ℕ) :
    strataCompPairSet S k = (strataCompSigmaSet S k).image (fun p => (p.1, p.2)) := rfl

/-- The pairing map is injective on `strataCompSigmaSet`. -/
theorem strataCompSigmaSet_pair_injOn (S : Finset ℕ) (k : ℕ) :
    ∀ x ∈ strataCompSigmaSet S k, ∀ y ∈ strataCompSigmaSet S k,
      (x.1, x.2) = (y.1, y.2) → x = y := by
  intro x _ y _ h
  have h1 : x.1 = y.1 := congrArg Prod.fst h
  have h2 : x.2 = y.2 := congrArg Prod.snd h
  cases x with
  | mk x1 x2 => cases y with
    | mk y1 y2 =>
      simp only at h1 h2
      subst h1; subst h2; rfl

/-- **Reindexing a sum over the pair set as the nested sum over `A₀` and `α ∈ Σ_{(A₀)}`.** -/
theorem sum_strataCompPairSet {β : Type*} [AddCommMonoid β] {S : Finset ℕ} {k : ℕ}
    (g : Finset ℕ × Circle → β) :
    (∑ p ∈ strataCompPairSet S k, g p)
      = ∑ A₀ ∈ S.powerset.filter (fun A₀ => A₀.card ≤ k),
          ∑ α ∈ strataCompFinset S k A₀, g (A₀, α) := by
  classical
  rw [strataCompPairSet_eq_image, Finset.sum_image (strataCompSigmaSet_pair_injOn S k),
    strataCompSigmaSet, Finset.sum_sigma]

/-- **Reindexing a sum over the pair set as a nested sum over subtypes** (the form in which the
vector-valued interpolation consumes the square function). -/
theorem sum_strataCompPairSet_subtype {β : Type*} [AddCommMonoid β] {S : Finset ℕ} {k : ℕ}
    (g : Finset ℕ × Circle → β) :
    (∑ p ∈ strataCompPairSet S k, g p)
      = ∑ A₀ : ↥(S.powerset.filter (fun A₀ => A₀.card ≤ k)),
          ∑ α : ↥(strataCompFinset S k A₀.1), g (A₀.1, α.1) := by
  classical
  rw [sum_strataCompPairSet g]
  refine (Finset.sum_coe_sort (s := S.powerset.filter (fun A₀ => A₀.card ≤ k))
    (f := fun A₀ => ∑ α ∈ strataCompFinset S k A₀, g (A₀, α))).symm.trans ?_
  refine Finset.sum_congr rfl (fun A₀ _ => ?_)
  exact (Finset.sum_coe_sort (s := strataCompFinset S k A₀.1)
    (f := fun α => g (A₀.1, α))).symm

/-- **Reindexing the nested sum over subtypes inside an arbitrary function of the inner sum** (the
form in which the `ℓ^p`-power of the inner `ℓ²`-sum occurs in the interpolation). -/
theorem sum_strataCompPairSet_pow {β γ : Type*} [AddCommMonoid γ] [AddCommMonoid β]
    {S : Finset ℕ} {k : ℕ}
    (g : Finset ℕ × Circle → γ) (F : γ → β) :
    (∑ A₀ ∈ S.powerset.filter (fun A₀ => A₀.card ≤ k),
        F (∑ α ∈ strataCompFinset S k A₀, g (A₀, α)))
      = ∑ A₀ : ↥(S.powerset.filter (fun A₀ => A₀.card ≤ k)),
          F (∑ α : ↥(strataCompFinset S k A₀.1), g (A₀.1, α.1)) := by
  classical
  refine (Finset.sum_coe_sort (s := S.powerset.filter (fun A₀ => A₀.card ≤ k))
    (f := fun A₀ => F (∑ α ∈ strataCompFinset S k A₀, g (A₀, α)))).symm.trans ?_
  refine Finset.sum_congr rfl (fun A₀ _ => ?_)
  rw [← Finset.sum_coe_sort (s := strataCompFinset S k A₀.1) (f := fun α => g (A₀.1, α))]

end Work.BourgainPlan.IonescuWainger
