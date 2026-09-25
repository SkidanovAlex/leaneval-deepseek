import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.farey_cover_by_taoSetS
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset

/-!
# Helpers for **(Σ2)**: the Farey arcs lie in Tao's Ionescu–Wainger superset

The divisibility form of Tao's Lemma `iwac`(i) (`farey_cover_by_taoSetS`) says that every
`1 ≤ q ≤ N` divides the product `Q_A = ∏_{a ∈ A} a` of at most `k = ⌊2/ρ⌋ + 1` elements of
Tao's set `S = taoSetS ρ N`.  The topological form needed by the maximal route is that the
Farey *point* `a/q ∈ 𝕋` belongs to the torsion subgroup `Σ_{⊆A} = 𝕋[Q_A] = sigmaSubAFinset A`.

This file supplies that bridge:

* `smallPrimePowerProd_ne_zero`, `taoSetS_ne_zero_of_mem`: every element of `taoSetS ρ N` is a
  nonzero natural number (a product of prime powers, or a single prime power);
* `QA_ne_zero_of_subset_taoSetS`: hence `Q_A ≠ 0` for `A ⊆ taoSetS ρ N`;
* `arcPt_mem_sigmaSubAFinset_of_dvd`: **if `1 ≤ q` and `q ∣ Q_A` (with `Q_A ≠ 0`) then the point
  `a/q ∈ 𝕋` lies in `Σ_{⊆A}`** — write `Q_A = q·(Q_A/q)`, so that `a/q = (a·(Q_A/q))/Q_A`
  (`arcPt_commonDenom`) and reduce the numerator of the latter modulo `Q_A`
  (`arcPt_emod_toNat`) to land in the `Finset` listing `Σ_{⊆A}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

/-- The "small" element of `taoSetS ρ N` is a product of prime powers, hence nonzero. -/
lemma smallPrimePowerProd_ne_zero (ρ : ℝ) (N : ℕ) : smallPrimePowerProd ρ N ≠ 0 := by
  rw [smallPrimePowerProd, Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.mp hp).2)

/-- Every element of Tao's set `taoSetS ρ N` is nonzero (a product of powers of primes, or a power
of a prime). -/
lemma taoSetS_ne_zero_of_mem {ρ : ℝ} {N q : ℕ} (hq : q ∈ taoSetS ρ N) : q ≠ 0 := by
  rw [taoSetS, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · exact smallPrimePowerProd_ne_zero ρ N
  · rw [largePrimePowers, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.mp hp).2)

/-- `Q_A = ∏_{a ∈ A} a` does not vanish for `A ⊆ taoSetS ρ N`. -/
lemma QA_ne_zero_of_subset_taoSetS {ρ : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ taoSetS ρ N) : QA A ≠ 0 :=
  QA_ne_zero fun _ hq => taoSetS_ne_zero_of_mem (hA hq)

/-- **The Farey point of a divisor of `Q_A` lies in the torsion subgroup `Σ_{⊆A}`.**  If `1 ≤ q` and
`q ∣ Q_A ≠ 0` then `a/q ∈ 𝕋` is a point of `Σ_{⊆A} = 𝕋[Q_A]`: with `Q_A = q · m` one has
`a/q = (a·m)/Q_A` in `𝕋` (`arcPt_commonDenom`), and the numerator of the latter is reduced modulo
`Q_A` (`arcPt_emod_toNat`) to give an element of the `Finset` `sigmaSubAFinset A`. -/
lemma arcPt_mem_sigmaSubAFinset_of_dvd {A : Finset ℕ} {q : ℕ} (hq : 1 ≤ q)
    (hQA : QA A ≠ 0) (hdvd : q ∣ QA A) (a : ℤ) : arcPt q a ∈ sigmaSubAFinset A := by
  have hL : 1 ≤ QA A := Nat.one_le_iff_ne_zero.mpr hQA
  have hQZ : (QA A : ℤ) ≠ 0 := by exact_mod_cast hQA
  have hQpos : (0 : ℤ) < (QA A : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hQA
  set c : ℤ := a * ((QA A / q : ℕ) : ℤ) with hc
  rw [sigmaSubAFinset, Finset.mem_image]
  refine ⟨(c % (QA A : ℤ)).toNat, ?_, ?_⟩
  · rw [Finset.mem_range, Int.toNat_lt (Int.emod_nonneg c hQZ)]
    exact Int.emod_lt_of_pos c hQpos
  · rw [arcPt_emod_toNat hQA c, hc]
    exact (arcPt_commonDenom hq hL hdvd a).symm

end Work.BourgainPlan.Maximal
