import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
-- RETIRED STUB (on disk for reference only; NOT on the delivered path): the declaration this
-- module was created for is retired because the step `O₂(M) = 1` it encodes is not derivable from `L27Hyp` (needs `F(U) ≤ M`): one hypothesis short as written.
-- Its corrected form, the reason, and the counterexample configuration are recorded in the
-- `RETIRED` block below and in `Submission/Work/CORE2B/NOTES_FALSE_L27_commutator_odd.md`.
-- Nothing in the delivered closure of `Work.CORE2B.Proved` / `L27su_assembly` /
-- `L29_lemma_assembly` / `Thm210_assembly` imports this module.

/-!
# CORE2B — elementary facts about `⁅M, t⁆` (helpers of Bender 1981 Lemma 2.7)

`t² = 1`; `t` inverts the generators `⁅m,t⁆` of `⁅M,t⁆`; `t` normalizes `⁅M,t⁆`; `⁅M,t⁆ ≤ M`;
`M` normalizes `⁅M,t⁆`; and if `⁅M,t⁆` has odd order then `⁅M,t⁆ ⊓ O₂(M) = ⊥`.

These declarations used to live in `Submission/Work/CORE2B/L27_commutator_odd.lean`, which is kept on
disk as a retired stub (its target `L27_commutator_odd`, the oddness of `|⁅M,t⁆|`, is one hypothesis
short of the area's hypotheses and is superseded by `Work.CORE2B.L27fin_odd_of_O2_bot`).  They were
moved here so that the retired stub is imported by nothing on the delivered path.

Consumers: `Submission/Work/CORE2B/L27su_fittingPiIn_compl_ne_bot{,2}.lean`
(`L27odd_t_inv`).
-/

open scoped commutatorElement

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

section

variable {G : Type} [Group G] [Finite G]

/-- `t² = 1` for the involution `B.t` of a `BenderSetup`. -/
theorem L27odd_t_sq (B : Work.GW2.BenderSetup G) : B.t * B.t = 1 := by
  have h := pow_orderOf_eq_one B.t
  rw [B.t_order] at h
  simpa [pow_two] using h

/-- `t` inverts `⁅m,t⁆`: on `⁅m,t⁆ = m * t * m⁻¹ * t⁻¹` conjugation by the involution `t`
is inversion.  (This is the source of the classical "`[M,t]` consists of elements inverted by
`t`"; note however that this property does *not* propagate to products.) -/
theorem L27odd_t_inv (B : Work.GW2.BenderSetup G) (m : G) :
    B.t * ⁅m, B.t⁆ * B.t⁻¹ = ⁅m, B.t⁆⁻¹ := by
  have ht2 : B.t * B.t = 1 := L27odd_t_sq B
  have htinv : B.t⁻¹ = B.t := inv_eq_of_mul_eq_one_right ht2
  simp only [commutatorElement_def]
  have key : (m * B.t * m⁻¹ * B.t⁻¹)⁻¹ = B.t * m * B.t⁻¹ * m⁻¹ := by
    simp only [mul_inv_rev, inv_inv]
    group
  rw [key, htinv]
  rw [show B.t * (m * B.t * m⁻¹ * B.t) * B.t = B.t * m * B.t * m⁻¹ * (B.t * B.t) from by group,
    ht2, mul_one]

/-- `t` normalizes `⁅M, t⁆` (Mathlib's `normalizer_commutator_ge_right`). -/
theorem L27odd_t_mem_normalizer (B : Work.GW2.BenderSetup G) (M : Subgroup G) :
    B.t ∈ Subgroup.normalizer ((⁅M, Subgroup.zpowers B.t⁆ : Subgroup G) : Set G) := by
  rw [← Subgroup.zpowers_le]
  exact Subgroup.normalizer_commutator_ge_right M (Subgroup.zpowers B.t)

/-- `M` normalizes `⁅M,t⁆` (Mathlib's `normalizer_commutator_ge_left`). -/
theorem L27odd_K_normal (B : Work.GW2.BenderSetup G) (M : Subgroup G) :
    M ≤ Subgroup.normalizer ((⁅M, Subgroup.zpowers B.t⁆ : Subgroup G) : Set G) :=
  Subgroup.normalizer_commutator_ge_left M (Subgroup.zpowers B.t)

/-- `⁅M,t⁆ ≤ M` (both `M` and `⟨t⟩` are subgroups of `M` since `t ∈ M`). -/
theorem L27odd_K_le (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G) ≤ M := by
  rw [Subgroup.commutator_le]
  intro m hm y hy
  have hyM : y ∈ M := (Subgroup.zpowers_le.mpr hD.t_mem) hy
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)) (M.inv_mem hyM)

/-- If `⁅M,t⁆` has odd order then it meets the `2`-group `O₂(M)` trivially.  (The converse is
what Bender's argument supplies via `[M,t] ⊆ F_{π'}(M)`; it is *not* available from the
elementary theory of `[M,t]`, see the module docstring.) -/
theorem L27odd_odd_imp_disjoint_O2 (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hodd : Odd (Nat.card (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G))) :
    (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G) ⊓ Work.GW2.pCoreIn 2 M = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Subgroup.eq_bot_iff_forall _ |>.mpr ?_
  intro x hx
  have h1 : orderOf x ∣ Nat.card (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G) :=
    Subgroup.orderOf_dvd_natCard _ hx.1
  have h2 : orderOf x ∣ Nat.card (Work.GW2.pCoreIn 2 M) :=
    Subgroup.orderOf_dvd_natCard _ hx.2
  have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd h1
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_dvd_pow (isPGroup_pCoreIn_two M)
  have h2' : orderOf x ∣ 2 ^ n := h2.trans hn
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2'
  have hodd2 : Odd (2 ^ k) := by rw [← hk_eq]; exact hodd'
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h)
      exact (Nat.not_even_iff_odd.mpr hodd2) (even_iff_two_dvd.mpr hdvd)
  have h1' : orderOf x = 1 := by rw [hk_eq, hk0, pow_zero]
  exact orderOf_eq_one_iff.mp h1'

end


end Work.CORE2B
