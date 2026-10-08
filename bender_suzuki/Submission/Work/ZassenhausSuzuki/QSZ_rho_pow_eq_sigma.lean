import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausTwoGroup.centralizer_le_H
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ZassenhausSuzuki.QSZ_invH_le_centerQ
import Submission.Work.ZassenhausSuzuki.QSZ_t_rPow_t_mem
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.QSZ_rho_pow_eq_sigma` (Suzuki 1962, Prop. 12)

Let `G` be a finite simple group with a Zassenhaus split rank-one configuration
`H = Q ⋊ D`, `D = H ∩ Hᵗ` (`Submission.Blueprint.IsSplitRankOne H Q t`,
`Submission.Blueprint.IsZassenhaus H`), with `Q` a 2-group.  Let `s, r ∈ Q` with `s` an
involution satisfy the *structure identity* `t s t = r⁻¹ t r`.  Then `s` is a power of `r`.

Proof route.  `Work.ThmF.ChV12.structureIdentity` gives that the pair `(s, r⁻¹)` is the
*unique* pair `(p.1, p.2)` with `p.1 ∈ Q` an involution, `p.2 ∈ Q` and
`t * p.1 * t⁻¹ = p.2 * t * p.2⁻¹`.  Hence it suffices to show that the unique involution
`w = r ^ (2 ^ (a - 1))` of the cyclic group `⟨r⟩` (where `orderOf r = 2 ^ a`) is again a first
component of such a pair: `t * w * t = q1 * t * q1⁻¹` for some `q1 ∈ Q`.  That is exactly the
delegated statement `Work.ZassenhausSuzuki.QSZ_t_rPow_t_mem` (a canonical-form fact for the
conjugate of `w` by `t`); the conversion `∈ Q t Q → = q1 t q1⁻¹` uses that `w` is an involution
together with `Q ⊓ twoPoint H t = ⊥`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem QSZ_rho_pow_eq_sigma {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {s r : G} (hsQ : s ∈ Q) (hs2 : orderOf s = 2) (hrQ : r ∈ Q)
    (hsr : t * s * t⁻¹ = r⁻¹ * t * r) :
    ∃ k : ℕ, r ^ k = s := by
  -- `t` is an involution.
  have ht2 : t * t = 1 := by
    have hh : t ^ 2 = 1 := by simpa [h.invol] using pow_orderOf_eq_one t
    simpa [pow_two] using hh
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `r ≠ 1`, else the structure identity forces `s = t ∉ H`.
  have hr1 : r ≠ 1 := by
    intro hr
    have h1 : t * s * t⁻¹ = t := by rw [hsr, hr]; group
    have hs_eq_t : s = t := by
      calc s = t⁻¹ * (t * s * t⁻¹) * t := by group
        _ = t⁻¹ * t * t := by rw [h1]
        _ = t := by rw [htinv, ht2, one_mul]
    exact h.not_mem (hs_eq_t ▸ h.le hsQ)
  -- `orderOf r = 2 ^ a` with `a ≥ 1` (as `r` is a nontrivial element of the 2-group `Q`).
  obtain ⟨a, ha⟩ : ∃ a : ℕ, orderOf r = 2 ^ a := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf (⟨r, hrQ⟩ : ↥Q) = 2 ^ k :=
      h2.exists_orderOf_eq_pow (⟨r, hrQ⟩ : ↥Q)
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | hp
    · exfalso; rw [h0, pow_zero] at ha
      exact hr1 (orderOf_eq_one_iff.mp ha)
    · exact hp
  -- `w = r ^ (2 ^ (a-1))` is the unique involution of `⟨r⟩`.
  set w : G := r ^ (2 ^ (a - 1)) with hwdef
  have hwQ : w ∈ Q := by rw [hwdef]; exact Q.pow_mem hrQ _
  have hwexp : 2 ^ (a - 1) * 2 = 2 ^ a := by
    rw [← pow_succ, Nat.sub_add_cancel ha1]
  have hw_sq : w ^ 2 = 1 := by
    rw [hwdef, ← pow_mul, hwexp, ← ha, pow_orderOf_eq_one]
  have hw_ne : w ≠ 1 := by
    intro hzz
    rw [hwdef] at hzz
    have hdvd : orderOf r ∣ 2 ^ (a - 1) := orderOf_dvd_iff_pow_eq_one.mpr hzz
    rw [ha] at hdvd
    have hle : 2 ^ a ≤ 2 ^ (a - 1) := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
    have hale : a ≤ a - 1 := (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).mp hle
    omega
  have hword : orderOf w = 2 := orderOf_eq_prime hw_sq hw_ne
  -- The canonical form of `t * w * t` has both entries in `Q`.
  obtain ⟨q1, hq1, q2, hq2, hcanon⟩ :=
    QSZ_t_rPow_t_mem hs H Q t h hZ h2 hsQ hs2 hrQ hsr a ha ha1
  have hcanon' : t * w * t = q1 * t * q2 := hcanon
  have hww : w * w = 1 := by rw [← pow_two]; exact hw_sq
  have htwtw : (t * w * t) ^ 2 = 1 := by
    rw [pow_two]
    calc (t * w * t) * (t * w * t) = t * w * (t * t) * w * t := by group
      _ = t * w * 1 * w * t := by rw [ht2]
      _ = t * (w * w) * t := by group
      _ = t * 1 * t := by rw [hww]
      _ = 1 := by rw [mul_one, ht2]
  have hsq : (q1 * t * q2) * (q1 * t * q2) = 1 := by
    rw [← hcanon', ← pow_two]; exact htwtw
  -- Hence `q2 * q1 = 1`, so `t * w * t = q1 * t * q1⁻¹`.
  have hconj : t * (q2 * q1) * t = (q2 * q1)⁻¹ := by
    have h' : q1 * (t * (q2 * q1) * t) * q2 = 1 := by
      rw [show q1 * (t * (q2 * q1) * t) * q2 = (q1 * t * q2) * (q1 * t * q2) from by group, hsq]
    have hX : (t * (q2 * q1) * t) * (q2 * q1) = 1 := by
      rw [show (t * (q2 * q1) * t) * (q2 * q1)
            = q1⁻¹ * (q1 * (t * (q2 * q1) * t) * q2) * q1 from by group, h']
      group
    exact eq_inv_of_mul_eq_one_left hX
  have hmemH : q2 * q1 ∈ H := h.le (Q.mul_mem hq2 hq1)
  have hconj2 : t * (q2 * q1)⁻¹ * t = q2 * q1 := by
    calc t * (q2 * q1)⁻¹ * t = t⁻¹ * (q2 * q1)⁻¹ * t⁻¹ := by rw [htinv]
      _ = (t * (q2 * q1) * t)⁻¹ := by group
      _ = q2 * q1 := by rw [hconj, inv_inv]
  have hmemT : q2 * q1 ∈ Submission.Blueprint.conj t H := by
    rw [Submission.Blueprint.conj, Subgroup.mem_map]
    exact ⟨(q2 * q1)⁻¹, H.inv_mem hmemH, by
      show t * (q2 * q1)⁻¹ * t⁻¹ = q2 * q1
      rw [htinv]; exact hconj2⟩
  have hone : q2 * q1 = 1 := by
    have hmem : q2 * q1 ∈ Q ⊓ twoPoint H t := ⟨Q.mul_mem hq2 hq1, hmemH, hmemT⟩
    rw [h.inf_eq] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hq2eq : q2 = q1⁻¹ := eq_inv_of_mul_eq_one_left hone
  have hconj1 : t * w * t = q1 * t * q1⁻¹ := by rw [hcanon', hq2eq]
  -- Uniqueness of the pair in the structure identity.
  obtain ⟨p, _hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData h)
  have hps : (s, r⁻¹) = p :=
    huniq (s, r⁻¹) ⟨hsQ, hs2, Q.inv_mem hrQ, by rw [inv_inv]; exact hsr⟩
  have hpw : (w, q1) = p :=
    huniq (w, q1) ⟨hwQ, hword, hq1, by rw [htinv]; exact hconj1⟩
  have hsw : s = w := congrArg Prod.fst (hps.trans hpw.symm)
  exact ⟨2 ^ (a - 1), by rw [hsw, hwdef]⟩

end Work.ZassenhausSuzuki
