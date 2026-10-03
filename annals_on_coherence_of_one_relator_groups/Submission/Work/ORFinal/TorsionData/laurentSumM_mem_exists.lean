import Mathlib
import Submission.Work.ORFinal.TorsionData.OreSetup

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-- `genZPow L (s : G) j` is the `j`-th element of the Laurent basis used by
`Work.ORLinnell.Laurent.laurentSum`: both are the image in `U` of `s ^ j`. -/
theorem genZPow_eq_laurentBasis (L : LinnellDatum K G U) {H : Subgroup G} (s : H) (j : ℤ) :
    genZPow L (s : G) j = Work.ORLinnell.Laurent.laurentBasis L s j := by
  rw [genZPow_eq_gen L H s j]
  rfl

/-- The `ℤ`-indexed Laurent sum of `Work.ORLinnell.Laurent` is the transport of the
`Multiplicative ℤ`-indexed sum `laurentSumM` along the index bijection
`Multiplicative.ofAdd : ℤ → Multiplicative ℤ`. -/
theorem laurentSumM_mapDomain_ofAdd (L : LinnellDatum K G U) {N H : Subgroup G} (s : H)
    (c : ℤ →₀ ↥(L.D N)) :
    laurentSumM L (s : G) (Finsupp.mapDomain Multiplicative.ofAdd c)
      = Work.ORLinnell.Laurent.laurentSum L s c := by
  rw [laurentSumM, Work.ORLinnell.Laurent.laurentSum]
  rw [Finsupp.sum_mapDomain_index (f := Multiplicative.ofAdd)
      (h := fun j (d : ↥(L.D N)) => (d : U) * genZPow L (s : G) (Multiplicative.toAdd j))
      (by intro j; simp) (by intro j x y; simp [add_mul])]
  apply Finsupp.sum_congr
  intro j _
  simp only [toAdd_ofAdd]
  rw [genZPow_eq_laurentBasis L s j]

theorem laurentSumM_mem_exists {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {N H : Subgroup G}
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H) :
    (∀ c : Multiplicative ℤ →₀ ↥(L.D N), Work.ORFinal.TorsionData.laurentSumM L (s : G) c ∈
        Work.ORFinal.TorsionData.TorsionR L N H) ∧
    (∀ x ∈ Work.ORFinal.TorsionData.TorsionR L N H,
        ∃ c : Multiplicative ℤ →₀ ↥(L.D N), Work.ORFinal.TorsionData.laurentSumM L (s : G) c = x)
    := by
  constructor
  · intro c
    rw [laurentSumM, Finsupp.sum]
    apply Subring.sum_mem
    intro i _
    refine (TorsionR L N H).mul_mem
      (Subring.subset_closure (Set.mem_union_left _ (c i).2)) ?_
    exact (mem_TorsionR L N H _).mpr
      (zpow_gen_mem_TorsionRsub L N H s (Multiplicative.toAdd i))
  · intro x hx
    obtain ⟨c, hc⟩ := Work.ORLinnell.Laurent.laurentSum_exists L hNH hNn s hs x hx
    exact ⟨Finsupp.mapDomain Multiplicative.ofAdd c,
      by rw [laurentSumM_mapDomain_ofAdd, hc]⟩

end Work.ORFinal.TorsionData
