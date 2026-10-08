import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_conj_t_inverts
import Submission.Work.CORE2B.L27_pi_subgroup_in_fittingPi

/-!
# CORE2B — the `π`-refinement of `[M,t] ⊆ F_{π'}(M)` for odd `[M,t]`

This is the "crux" reduction of Bender 1981, Lemma 2.7 (a): given that `[M,t] ≤ F(M)`,
`[M,t] ≤ C(F(M))`, that `t` centralizes `F_π(M)`, and that `[M,t]` has **odd order**, conclude
`[M,t] ≤ F_{π'}(M)`.

The proof is purely group-theoretic and uses only those four hypotheses:

* `[M,t]` is commutative (it lies in `F(M)` and centralizes it), and the involution `t` inverts
  it (`L27_conj_t_inverts`: `⟨t⟩ = {1,t}`, and `t` inverts each generator `⁅m,t⁆` of `[M,t]`);
* let `q` be a prime divisor of `|[M,t]|`.  By Cauchy there is `x ∈ [M,t]` of order `q`.  If
  `q ∈ π`, then `x ∈ F(M)` has prime order `q ∈ π`, so `x ∈ F_π(M)`
  (`L27_pi_subgroup_in_fittingPi` applied to `⟨x⟩`); hence `t` centralizes `x`, while `t` also
  inverts `x`, so `x = x⁻¹` and `q = 2`.  As `|[M,t]|` is odd, `q` is odd — contradiction.
  Thus every prime divisor of `|[M,t]|` lies in `πᶜ`.
* `[M,t]` is therefore a `πᶜ`-subgroup of the nilpotent group `F(M)`, so it lies in
  `O_{πᶜ}(F(M)) = F_{π'}(M)` (`L27_pi_subgroup_in_fittingPi` again).
-/

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

theorem L27_commutator_le_of_odd_crux {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : Work.CORE2B.L27Hyp B M)
    (hcenπ : Work.GW2.fittingPiIn B.pi M ≤ Subgroup.centralizer ({B.t} : Set G))
    (hcent : ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G))
    (hKF : ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingIn M)
    (hodd : Odd (Nat.card (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G))) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M := by
  -- `t` is an involution
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  -- `[M,t]` is commutative: it lies in `F(M)` and centralizes it
  have hKcomm : ∀ x ∈ ⁅M, Subgroup.zpowers B.t⁆, ∀ y ∈ ⁅M, Subgroup.zpowers B.t⁆,
      x * y = y * x := by
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hcent hx)) y (hKF hy)).symm
  -- the involution `t` inverts `[M,t]`
  have hinv : ∀ x ∈ ⁅M, Subgroup.zpowers B.t⁆, B.t * x * B.t⁻¹ = x⁻¹ :=
    L27_conj_t_inverts M ht2 hKcomm
  -- no prime divisor of `|[M,t]|` lies in `π`
  have hKpi : Subgroup.IsPiSubgroup B.piᶜ (⁅M, Subgroup.zpowers B.t⁆) := by
    intro q hq
    simp only [Set.mem_compl_iff]
    intro hqpi
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ Nat.card ↥(⁅M, Subgroup.zpowers B.t⁆) := (Nat.mem_primeFactors.mp hq).2.1
    haveI : Fact q.Prime := ⟨hqprime⟩
    -- Cauchy: an element of `[M,t]` of order `q`
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(⁅M, Subgroup.zpowers B.t⁆)) q hqdvd
    set x : G := (y : G) with hxdef
    have hxK : x ∈ ⁅M, Subgroup.zpowers B.t⁆ := by rw [hxdef]; exact y.2
    have hxo : orderOf x = q := by rw [hxdef, Subgroup.orderOf_coe]; exact hy
    -- `x ∈ F(M)` has prime order `q ∈ π`, hence `x ∈ F_π(M)`
    have hxPi : x ∈ Work.GW2.fittingPiIn B.pi M := by
      have hzp : Subgroup.zpowers x ≤ Work.GW2.fittingIn M :=
        Subgroup.zpowers_le.mpr (hKF hxK)
      have hpi : Subgroup.IsPiSubgroup B.pi (Subgroup.zpowers x) := by
        intro p hp
        rw [Nat.card_zpowers, hxo] at hp
        obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
        rwa [(Nat.prime_dvd_prime_iff_eq hpp hqprime).mp hpdvd]
      exact L27_pi_subgroup_in_fittingPi M (Subgroup.zpowers x) B.pi hzp hpi
        (Subgroup.mem_zpowers x)
    -- `t` centralizes `x` and inverts `x`, so `x = x⁻¹` and `q = 2`
    have hxt : B.t * x * B.t⁻¹ = x := by
      have hcx : B.t * x = x * B.t :=
        (Subgroup.mem_centralizer_iff.mp (hcenπ hxPi)) B.t rfl
      rw [hcx, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : x = x⁻¹ := by
      have h := hinv x hxK
      rwa [hxt] at h
    have hx2 : x * x = 1 := by
      have h := congrArg (fun w => w * x) h1
      rwa [inv_mul_cancel] at h
    have hq2 : q = 2 := by
      have hdvd2 : q ∣ 2 := by
        rw [← hxo]
        exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact absurd h hqprime.ne_one
      · exact h
    -- but `|[M,t]|` is odd
    exact hodd.not_two_dvd_nat (hq2 ▸ hqdvd)
  exact L27_pi_subgroup_in_fittingPi M (⁅M, Subgroup.zpowers B.t⁆) B.piᶜ hKF hKpi

end Work.CORE2B
