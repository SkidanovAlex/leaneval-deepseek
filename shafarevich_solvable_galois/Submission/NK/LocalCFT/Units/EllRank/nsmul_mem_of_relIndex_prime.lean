import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalCFT.Units.EllRank

/-- If `V`, `W` are additive subgroups of an abelian group `G` with `V` of prime relative
index `p` in `W` (i.e. `[W : V ⊓ W] = p`), then every element `w ∈ W` has `p • w ∈ V`.

Indeed `W ⧸ (V ⊓ W)` is a group of order `p`, so every element of it has order dividing
`p`; applying this to the image of `w` gives `p • w ∈ V ⊓ W ≤ V`. -/
theorem nsmul_mem_of_relIndex_prime {G : Type*} [AddCommGroup G] {V W : AddSubgroup G}
    {p : ℕ} (hp : p.Prime) (h : V.relIndex W = p) {w : G} (hw : w ∈ W) : p • w ∈ V := by
  -- `V.relIndex W = p` says that `V.addSubgroupOf W` has index `p` in `↥W`.
  have hcard : Nat.card (↥W ⧸ V.addSubgroupOf W) = p := by
    rw [← AddSubgroup.index_eq_card]
    exact h
  -- hence the image of `w` in the quotient `↥W ⧸ V.addSubgroupOf W` is killed by `p`.
  have hdvd : addOrderOf (QuotientAddGroup.mk' (V.addSubgroupOf W) (⟨w, hw⟩ : ↥W)) ∣ p := by
    rw [← hcard]
    exact addOrderOf_dvd_natCard _
  have hzero : (p : ℕ) • (QuotientAddGroup.mk' (V.addSubgroupOf W) (⟨w, hw⟩ : ↥W)) = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mp hdvd
  -- so `p • w ∈ V.addSubgroupOf W`, i.e. `p • w ∈ V`.
  have hmem : (p : ℕ) • (⟨w, hw⟩ : ↥W) ∈ V.addSubgroupOf W := by
    refine (QuotientAddGroup.eq_zero_iff (N := V.addSubgroupOf W) _).mp ?_
    change (QuotientAddGroup.mk' (V.addSubgroupOf W)) (p • (⟨w, hw⟩ : ↥W)) = 0
    rw [map_nsmul]
    exact hzero
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  simpa using hmem

end NK.LocalCFT.Units.EllRank
