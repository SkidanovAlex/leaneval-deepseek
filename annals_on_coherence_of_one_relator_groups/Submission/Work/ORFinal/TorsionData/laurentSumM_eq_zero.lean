import Mathlib
import Submission.Work.ORFinal.TorsionData.OreSetup

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-- `genZPow L s z` is the image in `U` of the group element `s ^ z`: this is `L.gen` being a
monoid homomorphism into the units of `U`. -/
theorem genZPow_eq_gen_pow (L : LinnellDatum K G U) (s : G) (z : ℤ) :
    genZPow L s z = ↑(L.gen (s ^ z)) := by
  rw [genZPow, map_zpow]

/-- **Linnell independence in the `ℤ`-power form**, for an abstract Linnell datum.

If `s : G` has infinite order modulo `N` (hypothesis `hs0`) and the exponents `z i` are pairwise
distinct, then a `D N`-linear combination of the powers `(gen s) ^ (z i)` which vanishes has all
coefficients `0`.  This is `LinnellDatum.independence` (Linnell independence **(I1)**) applied to
the group elements `s ^ (z i)`, which are pairwise distinct modulo `N` precisely because `s` has
infinite order there.  It is the `LinnellDatum` mirror of
`Work.ORFinal.OreField.independence_gen_zpow`. -/
theorem independence_genZPow (L : LinnellDatum K G U) {N : Subgroup G} (s : G)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N → k = 0)
    (n : ℕ) (z : Fin n → ℤ) (hz : Function.Injective z)
    (a : Fin n → U) (ha : ∀ i, a i ∈ L.D N)
    (hsum : ∑ i, a i * genZPow L s (z i) = 0) : ∀ i, a i = 0 := by
  have hsum' : ∑ i, a i * ↑(L.gen (s ^ (z i))) = 0 := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [genZPow_eq_gen_pow])
  refine L.independence N n (fun i => s ^ (z i)) ?_ a ha hsum'
  intro i j hij
  have h1 : s ^ (z i - z j) ∈ N := by rwa [zpow_sub]
  exact hz (sub_eq_zero.mp (hs0 _ h1))

theorem laurentSumM_eq_zero {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {N H : Subgroup G}
    (s : H) (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0)
    (c : Multiplicative ℤ →₀ ↥(L.D N))
    (hc : Work.ORFinal.TorsionData.laurentSumM L (s : G) c = 0) : c = 0 := by
  classical
  -- `s` has infinite order modulo `N` as an element of `G`.
  have hs0' : ∀ k : ℤ, (s : G) ^ k ∈ N → k = 0 := by
    intro k hk
    exact hs0 k (Subgroup.mem_subgroupOf.mpr (by rwa [Subgroup.coe_zpow]))
  -- Unfold the twisted Laurent sum.
  have hsum0 : c.sum (fun i d => (d : U) * genZPow L (s : G) (Multiplicative.toAdd i)) = 0 := by
    simpa [laurentSumM] using hc
  -- Enumerate the support of `c`.
  let e : ↥c.support ≃ Fin c.support.card := Finset.equivFin c.support
  -- Rewrite the finsupp sum as a sum over `Fin c.support.card`.
  have hA : c.sum (fun i d => (d : U) * genZPow L (s : G) (Multiplicative.toAdd i))
      = ∑ x ∈ c.support, (c x : U) * genZPow L (s : G) (Multiplicative.toAdd x) :=
    Finsupp.sum_of_support_subset c (Finset.Subset.refl _) _ (by intro i _; simp)
  have hB : (∑ x ∈ c.support, (c x : U) * genZPow L (s : G) (Multiplicative.toAdd x))
      = ∑ x : ↥c.support, (c (x : Multiplicative ℤ) : U) *
          genZPow L (s : G) (Multiplicative.toAdd (x : Multiplicative ℤ)) :=
    Finset.sum_subtype c.support (fun _ => Iff.rfl) _
  have hC : (∑ x : ↥c.support, (c (x : Multiplicative ℤ) : U) *
          genZPow L (s : G) (Multiplicative.toAdd (x : Multiplicative ℤ)))
      = ∑ i : Fin c.support.card,
          (c ((e.symm i : ↥c.support) : Multiplicative ℤ) : U) *
            genZPow L (s : G)
              (Multiplicative.toAdd ((e.symm i : ↥c.support) : Multiplicative ℤ)) :=
    Fintype.sum_equiv e _ _ (by intro x; simp)
  have hsum : (∑ i : Fin c.support.card,
        (c ((e.symm i : ↥c.support) : Multiplicative ℤ) : U) *
          genZPow L (s : G)
            (Multiplicative.toAdd ((e.symm i : ↥c.support) : Multiplicative ℤ))) = 0 := by
    rw [← hC, ← hB, ← hA]
    exact hsum0
  -- Linnell independence at the exponents `Multiplicative.toAdd (e.symm i)`.
  have hind := independence_genZPow L (s : G) hs0' c.support.card
    (fun i : Fin c.support.card =>
      Multiplicative.toAdd ((e.symm i : ↥c.support) : Multiplicative ℤ))
    (by
      intro i j hij
      exact e.symm.injective (Subtype.ext (Multiplicative.toAdd.injective hij)))
    (fun i : Fin c.support.card =>
      (c ((e.symm i : ↥c.support) : Multiplicative ℤ) : U))
    (fun i => (c ((e.symm i : ↥c.support) : Multiplicative ℤ)).2)
    hsum
  have hc0 : ∀ i : Fin c.support.card,
      c ((e.symm i : ↥c.support) : Multiplicative ℤ) = 0 :=
    fun i => Subtype.ext (by simpa using hind i)
  refine Finsupp.ext (fun j => ?_)
  by_cases hj : j ∈ c.support
  · have h3 : c ((e.symm (e ⟨j, hj⟩) : ↥c.support) : Multiplicative ℤ) = 0 := hc0 (e ⟨j, hj⟩)
    rwa [show ((e.symm (e ⟨j, hj⟩) : ↥c.support) : Multiplicative ℤ) = j from by simp] at h3
  · by_contra hne
    exact hj ((Finsupp.mem_support_iff).mpr hne)

end Work.ORFinal.TorsionData
