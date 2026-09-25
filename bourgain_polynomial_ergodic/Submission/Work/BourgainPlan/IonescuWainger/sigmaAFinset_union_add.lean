import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_exists_unique_add

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **The direct-sum decomposition `Σ_{A₀ ∪ B} = Σ_{A₀} ⊕ Σ_B` at the level of `Finset` sums.**

Let `S` be a finite set of pairwise coprime integers `≥ 2`, and let `A₀, B ⊆ S` be disjoint.  Then
the addition map `(γ, α) ↦ γ + α` is a bijection from `sigmaAFinset A₀ × sigmaAFinset B` onto
`sigmaAFinset (A₀ ∪ B)` (this is the `Finset` form of `sigmaA_exists_unique_add`), so any sum over
the exact-denominator arc `Σ_{A₀ ∪ B}` can be expanded as a double sum over `Σ_{A₀}` and `Σ_B`.
This is the summation step in expanding `f_{Σ_{A₀ ∪ A_i}} = Σ_{α ∈ Σ_{A_i}} f_{α + Σ_{A₀}}` in the
proof of Tao's Theorem `ortho-apply`(i) (arXiv:2008.05066). -/
theorem sigmaAFinset_union_add {S A₀ B : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A₀ B) (f : Circle → ℤ → ℂ) (m : ℤ) :
    (∑ δ ∈ sigmaAFinset (A₀ ∪ B), f δ m)
      = ∑ α ∈ sigmaAFinset B, ∑ γ ∈ sigmaAFinset A₀, f (γ + α) m := by
  classical
  have hA₀2 : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀ hq)
  have hB2 : ∀ q ∈ B, 2 ≤ q := fun q hq => h2 q (hB hq)
  have hUsub : A₀ ∪ B ⊆ S := Finset.union_subset hA₀ hB
  have hU2 : ∀ q ∈ A₀ ∪ B, 2 ≤ q := fun q hq => h2 q (hUsub hq)
  have h0A : 0 ∉ A₀ := fun h => by have := hA₀2 0 h; omega
  have h0B : 0 ∉ B := fun h => by have := hB2 0 h; omega
  have h0U : 0 ∉ A₀ ∪ B := fun h => by have := hU2 0 h; omega
  -- the `Finset` of exact-denominator points coincides with Tao's arc `Σ_·` as a `Set`
  have eA : ((sigmaAFinset A₀ : Finset Circle) : Set Circle) = sigmaA A₀ := coe_sigmaAFinset h0A
  have eB : ((sigmaAFinset B : Finset Circle) : Set Circle) = sigmaA B := coe_sigmaAFinset h0B
  have eU : ((sigmaAFinset (A₀ ∪ B) : Finset Circle) : Set Circle) = sigmaA (A₀ ∪ B) :=
    coe_sigmaAFinset h0U
  have memA : ∀ x : Circle, x ∈ sigmaAFinset A₀ ↔ x ∈ sigmaA A₀ := fun x => by
    rw [← eA]; exact Finset.mem_coe
  have memB : ∀ x : Circle, x ∈ sigmaAFinset B ↔ x ∈ sigmaA B := fun x => by
    rw [← eB]; exact Finset.mem_coe
  have memU : ∀ x : Circle, x ∈ sigmaAFinset (A₀ ∪ B) ↔ x ∈ sigmaA (A₀ ∪ B) := fun x => by
    rw [← eU]; exact Finset.mem_coe
  -- every point of `Σ_{A₀ ∪ B}` has a *unique* decomposition `γ + α` with `γ ∈ Σ_{A₀}`, `α ∈ Σ_B`
  have key : ∀ x ∈ sigmaAFinset (A₀ ∪ B),
      ∃! p : Circle × Circle,
        p.1 ∈ sigmaAFinset A₀ ∧ p.2 ∈ sigmaAFinset B ∧ p.1 + p.2 = x := by
    intro x hx
    obtain ⟨p, hp, huniq⟩ :=
      sigmaA_exists_unique_add h2 hS hA₀ hB hdisj ((memU x).mp hx)
    obtain ⟨hp1, hp2, hps⟩ := hp
    refine ⟨p, ⟨(memA p.1).mpr hp1, (memB p.2).mpr hp2, hps⟩, ?_⟩
    rintro q ⟨hq1, hq2, hqs⟩
    exact huniq q ⟨(memA q.1).mp hq1, (memB q.2).mp hq2, hqs⟩
  -- the image of the product under `+` is exactly `Σ_{A₀ ∪ B}`
  have hT : (sigmaAFinset A₀ ×ˢ sigmaAFinset B).image (fun p : Circle × Circle => p.1 + p.2)
      = sigmaAFinset (A₀ ∪ B) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      rw [Finset.mem_product] at hp
      exact (memU _).mpr
        (sigmaA_add_mem h2 hS hA₀ hB hdisj ((memA p.1).mp hp.1) ((memB p.2).mp hp.2))
    · intro x hx
      obtain ⟨p, hp, -⟩ := key x hx
      exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr ⟨hp.1, hp.2.1⟩, hp.2.2⟩
  -- and `+` is injective there, by uniqueness of the decomposition
  have hinj : Set.InjOn (fun p : Circle × Circle => p.1 + p.2)
      ↑(sigmaAFinset A₀ ×ˢ sigmaAFinset B) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    have hxU := sigmaA_add_mem h2 hS hA₀ hB hdisj ((memA x.1).mp hx.1) ((memB x.2).mp hx.2)
    obtain ⟨p, -, huniq⟩ := sigmaA_exists_unique_add h2 hS hA₀ hB hdisj hxU
    have e1 : x = p := huniq x ⟨(memA x.1).mp hx.1, (memB x.2).mp hx.2, rfl⟩
    have e2 : y = p := huniq y ⟨(memA y.1).mp hy.1, (memB y.2).mp hy.2, hxy.symm⟩
    rw [e1, e2]
  rw [← hT, Finset.sum_image hinj, Finset.sum_product, Finset.sum_comm]

end Work.BourgainPlan.IonescuWainger
