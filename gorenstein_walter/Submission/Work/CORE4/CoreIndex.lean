import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10

namespace Work.CORE4

/-- **LEAF C10.A8 `CoreIndex`** (pure group theory, closing the `A₇` chain): "each 7-subgroup of
`M` lies in all conjugates of `M`", formalised in the stronger form the assembly uses:

    CoreIndexProp  =  ∀ (G) [Group G] [Finite G], IsSimpleGroup G → ∀ M : Subgroup G, M ≠ ⊤ →
                        ∀ p : ℕ, p.Prime → p ∣ Nat.card M → M.index ≤ p → False

Proof (reviewed): the action of `G` on `G ⧸ M` has kernel `core_G(M) ≤ M < ⊤`, which must be `⊥`
by simplicity, so `G ↪ Equiv.Perm (G ⧸ M)` and `Nat.card G ∣ M.index !`; `p ∣ Nat.card M` and
`Nat.card G = M.index * Nat.card M` give `p ∣ Nat.card G`, hence `p ≤ M.index`, so
`M.index = p`; then `p² ∣ Nat.card G ∣ p!`, impossible. -/
theorem CoreIndex : Work.GW2.CoreIndexProp := by
  intro G _ _ hsimple M hM p hp hpdvd hle
  -- The kernel of the action of `G` on `G ⧸ M` is `M.normalCore ≤ M < ⊤`, hence `⊥`.
  have hcore : M.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ Subgroup.normalCore_le M)) hM
  -- Faithful action on the `M.index` cosets: `Nat.card G ∣ M.index !`.
  have hdvd_fact : Nat.card G ∣ M.index.factorial := by
    have h := Subgroup.index_normalCore_dvd_factorial_index M
    rwa [hcore, Subgroup.index_bot] at h
  -- `p ∣ Nat.card M` and `Nat.card G = M.index * Nat.card M`, so `p ∣ Nat.card G`.
  have hpdvdG : p ∣ Nat.card G := by
    rw [← Subgroup.index_mul_card M]
    exact dvd_mul_of_dvd_right hpdvd M.index
  have hpdvdfact : p ∣ M.index.factorial := hpdvdG.trans hdvd_fact
  have hp_le_index : p ≤ M.index := (Nat.Prime.dvd_factorial hp).mp hpdvdfact
  have hidx : M.index = p := le_antisymm hle hp_le_index
  -- Then `p ^ 2 ∣ Nat.card G ∣ p !`, impossible for a prime `p`.
  have hp2G : p ^ 2 ∣ Nat.card G := by
    rw [← Subgroup.index_mul_card M, hidx, pow_two]
    exact mul_dvd_mul_left p hpdvd
  have hp2fact : p ^ 2 ∣ p.factorial := by
    have h := hdvd_fact
    rw [hidx] at h
    exact hp2G.trans h
  have hnot : ¬ p ^ 2 ∣ p.factorial := by
    intro hcon
    rw [pow_two] at hcon
    have hfac : p.factorial = p * (p - 1).factorial := by
      have h1 : 1 ≤ p := hp.one_le
      conv_lhs => rw [show p = (p - 1) + 1 by omega, Nat.factorial_succ]
      rw [Nat.sub_add_cancel h1]
    rw [hfac, Nat.mul_dvd_mul_iff_left hp.pos] at hcon
    have hp2 : 2 ≤ p := hp.two_le
    have hle' : p ≤ p - 1 := (Nat.Prime.dvd_factorial hp).mp hcon
    omega
  exact hnot hp2fact

end Work.CORE4
