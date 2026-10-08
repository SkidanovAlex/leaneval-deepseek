import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V = 1` implies the Zassenhaus property (Peterfalvi II, p. 236)

Peterfalvi II, introduction (p. 236): *"Il est facile de voir que `G` est un groupe de
Zassenhaus si et seulement si `V = 1`."*  This file proves the direction

  `IsSplitRankOne H Q t → IsPGroup 2 Q → centD H t = ⊥ → IsZassenhaus H`,

i.e. `V = C_D(t) = ⊥` forces the pointwise stabiliser of three points of `Ω = G ⧸ H` to be
trivial.  (No `Situation`, simplicity or induction hypothesis is needed, and the proof is the
contrapositive of `Work.PSU3.StageA.centD_ne_bot`.)

The argument, in full detail:

* Suppose `H` is *not* a Zassenhaus subgroup: there are three distinct points `a,b,c` of `Ω`
  and `1 ≠ g` fixing all three.  By 2-transitivity (from `IsSplitRankOne`) we may replace the
  ordered pair `(a,b)` by `(∞, t • ∞)` where `∞ = H`; then `d = x g x⁻¹` lies in
  `D = twoPoint H t` and fixes a third point `c' ∉ {∞, t • ∞}`.
* `Q` acts regularly on `Ω ∖ {∞}` (`IsTIQ`), so `c' = q • (t • ∞)` for a unique `q ∈ Q`, `q ≠ 1`;
  as `c'` is fixed by `d`, the conjugate `d q d⁻¹ ∈ Q` equals `q`, i.e. `d` commutes with `q`.
* Since `Q` is a 2-group, some power `u = q ^ (2 ^ (j-1))` is an involution of `Q`; it is still
  centralised by `d`.
* If `V = 1`, then `|K| = |D|` (`|K| · |V| = |D|`, `K ⊆ D` with `K = Kset H t`), so
  `K = D ∋ d`.  But the map `x ↦ x u x⁻¹` is injective on `K` (Peterfalvi I, Ch. I §2 Lemma 1,
  `Kset_conj_injective`), and both `d` and `1` map to `u`; hence `d = 1`, a contradiction.

The only structural inputs are `IsSplitRankOne H Q t` and `IsPGroup 2 Q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## `V = 1` gives `K = D` -/

/-- If `centD H t = V = C_D(t)` is trivial then `K = J(D,t) = Kset H t` is all of
`D = twoPoint H t`: indeed `|K| · |V| = |D|` and `K ⊆ D`. -/
theorem Kset_eq_twoPoint_of_centD_eq_bot {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hc : centD H t = ⊥) :
    Work.ThmF.Kset H t = (twoPoint H t : Set G) := by
  have hdata : Work.ThmF.IsSplitRankOneData G H Q t := Work.ThmF.IsSplitRankOne.toData h
  have hcard := Work.ThmF.card_centD_mul_card_Kset hdata
  have hV : Nat.card ↥(centD H t) = 1 := by rw [hc, Subgroup.card_bot]
  have hKn : (Work.ThmF.Kset H t).ncard = Nat.card ↥(twoPoint H t) := by
    rw [hV, one_mul] at hcard
    exact hcard
  have hDncard : (twoPoint H t : Set G).ncard = (Work.ThmF.Kset H t).ncard := by
    rw [hKn]
    exact (Nat.card_coe_set_eq _).symm
  exact Set.eq_of_subset_of_ncard_le (Work.ThmF.Kset_subset H t) (le_of_eq hDncard)

/-! ## The reduction: `¬ IsZassenhaus` produces a nontrivial `d ∈ D` centralising an
involution of `Q` -/

/-- If `H` is not a Zassenhaus subgroup (`IsSplitRankOne H Q t`, `Q` a 2-group) then there is
`1 ≠ d ∈ twoPoint H t` commuting with an involution `u ∈ Q`:
`d * u * d⁻¹ = u`.  This is the reduction used in the proof of `centD ≠ ⊥` (Peterfalvi II,
p. 236 / Ch. I §2). -/
theorem exists_involution_centralized_of_not_isZassenhaus {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) (hZ : ¬ IsZassenhaus H) :
    ∃ d ∈ twoPoint H t, d ≠ 1 ∧ ∃ u ∈ Q, orderOf u = 2 ∧ d * u * d⁻¹ = u := by
  classical
  have ht2 : orderOf t = 2 := h.invol
  have htH : t ∉ H := h.not_mem
  -- Step 1: `¬ IsZassenhaus H` gives three distinct points fixed by a non-identity element.
  rw [Submission.Blueprint.IsZassenhaus] at hZ
  push_neg at hZ
  obtain ⟨a, b, c, hab, hac, hbc, g, hga, hgb, hgc, hg1⟩ := hZ
  -- Step 2: move the ordered pair `(a, b)` to `(∞, t • ∞)`.
  have h2t : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := h.twoTransitive
  rw [MulAction.is_two_pretransitive_iff] at h2t
  have htpt_ne : t • Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.t_smul_pt_ne h
  obtain ⟨x, hxa, hxb⟩ := h2t hab htpt_ne.symm
  set c' : G ⧸ H := x • c with hc'_def
  set d : G := x * g * x⁻¹ with hd_def
  have hd_pt : d • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H := by
    rw [hd_def, ← hxa]
    calc (x * g * x⁻¹) • (x • a) = ((x * g * x⁻¹) * x) • a := (mul_smul (x * g * x⁻¹) x a).symm
      _ = (x * g) • a := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • a) := mul_smul x g a
      _ = x • a := by rw [hga]
  have hd_tpt : d • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    rw [hd_def, ← hxb]
    calc (x * g * x⁻¹) • (x • b) = ((x * g * x⁻¹) * x) • b := (mul_smul (x * g * x⁻¹) x b).symm
      _ = (x * g) • b := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • b) := mul_smul x g b
      _ = x • b := by rw [hgb]
  have hd_c' : d • c' = c' := by
    rw [hc'_def, hd_def]
    calc (x * g * x⁻¹) • (x • c) = ((x * g * x⁻¹) * x) • c := (mul_smul (x * g * x⁻¹) x c).symm
      _ = (x * g) • c := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • c) := mul_smul x g c
      _ = x • c := by rw [hgc]
  have hc'_ne_pt : c' ≠ Work.RankOneUniqueness.pt H := by
    intro hcon
    rw [hc'_def] at hcon
    have h1 : x⁻¹ • (x • c) = x⁻¹ • (x • a) := by rw [hcon, hxa]
    rw [inv_smul_smul, inv_smul_smul] at h1
    exact hac h1.symm
  have hc'_ne_tpt : c' ≠ t • Work.RankOneUniqueness.pt H := by
    intro hcon
    rw [hc'_def] at hcon
    have h1 : x⁻¹ • (x • c) = x⁻¹ • (x • b) := by rw [hcon, hxb]
    rw [inv_smul_smul, inv_smul_smul] at h1
    exact hbc h1.symm
  have hd_ne_one : d ≠ 1 := by
    intro h1
    apply hg1
    have h2 : x * g * x⁻¹ = 1 := by rw [← hd_def]; exact h1
    have h3 := congrArg (fun z : G => x⁻¹ * z * x) h2
    simpa [mul_assoc] using h3
  have hd_ptH : d ∈ H := (Work.RankOneUniqueness.smul_pt_iff H d).mp hd_pt
  have hd_memD : d ∈ twoPoint H t :=
    (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t d).mpr
      ⟨hd_ptH, by rw [← Work.RankOneUniqueness.smul_pt H t]; exact hd_tpt⟩
  -- Step 3: the third fixed point determines `q ∈ Q#` centralised by `d`.
  obtain ⟨h', hhH, hh⟩ := Work.ZassenhausTwoGroup.IsTIQ.h_transitive h
    (t • Work.RankOneUniqueness.pt H) c' htpt_ne hc'_ne_pt
  obtain ⟨q, hqQ, e, heD, hqe⟩ := Work.RankOneUniqueness.fact_exists h hhH
  have he_tpt : e • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    have h1 := (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t e).mp heD
    rw [← Work.RankOneUniqueness.smul_pt H t] at h1
    exact h1.2
  have hq_smul : q • (t • Work.RankOneUniqueness.pt H) = c' := by
    calc q • (t • Work.RankOneUniqueness.pt H)
        = q • (e • (t • Work.RankOneUniqueness.pt H)) := by rw [he_tpt]
      _ = (q * e) • (t • Work.RankOneUniqueness.pt H) :=
          (mul_smul q e (t • Work.RankOneUniqueness.pt H)).symm
      _ = h' • (t • Work.RankOneUniqueness.pt H) := by rw [hqe]
      _ = c' := hh
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    rw [hq1, one_smul] at hq_smul
    exact hc'_ne_tpt hq_smul.symm
  have hd_inv_tpt : d⁻¹ • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    have h1 : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hd_memD
    have h2 := (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t d⁻¹).mp h1
    rw [← Work.RankOneUniqueness.smul_pt H t] at h2
    exact h2.2
  have hdq_conj : d * q * d⁻¹ = q := by
    have h1 : (d * q * d⁻¹) • (t • Work.RankOneUniqueness.pt H)
        = q • (t • Work.RankOneUniqueness.pt H) := by
      calc (d * q * d⁻¹) • (t • Work.RankOneUniqueness.pt H)
          = d • (q • (d⁻¹ • (t • Work.RankOneUniqueness.pt H))) := by
            rw [mul_smul, mul_smul]
        _ = d • (q • (t • Work.RankOneUniqueness.pt H)) := by rw [hd_inv_tpt]
        _ = d • c' := by rw [hq_smul]
        _ = c' := hd_c'
        _ = q • (t • Work.RankOneUniqueness.pt H) := hq_smul.symm
    have hmem : d * q * d⁻¹ ∈ Q :=
      Work.RankOneUniqueness.conj_mem_of_mem h hd_ptH hqQ
    have hfix : ((d * q * d⁻¹)⁻¹ * q) • (t • Work.RankOneUniqueness.pt H)
        = t • Work.RankOneUniqueness.pt H := by
      rw [mul_smul, ← h1, inv_smul_smul]
    have hone : (d * q * d⁻¹)⁻¹ * q = 1 :=
      Work.ZassenhausTwoGroup.IsTIQ.Q_smul_eq_self h
        (Q.mul_mem (Q.inv_mem hmem) hqQ) hfix htpt_ne
    exact inv_mul_eq_one.mp hone
  -- Step 4: an involution `u ∈ Q` centralised by `d`.
  obtain ⟨n, hn⟩ := h2 ⟨q, hqQ⟩
  have hqpow : q ^ (2 ^ n) = 1 := by
    have hh := congrArg (fun z : ↥Q => (z : G)) hn
    simpa using hh
  have hdvd : orderOf q ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hqpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hjpos : 1 ≤ j := by
    by_contra h1
    have hj0 : j = 0 := by omega
    rw [hj0] at hj
    exact hq_ne_one (orderOf_eq_one_iff.mp (by simpa using hj))
  set u : G := q ^ (2 ^ (j - 1)) with hu_def
  have hu_mem_Q : u ∈ Q := Subgroup.pow_mem Q hqQ _
  have hu_sq : u * u = 1 := by
    have h2j : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      have h1 : (2 : ℕ) ^ j = 2 ^ (j - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hjpos]
      rw [h1]; ring
    rw [hu_def]
    calc q ^ 2 ^ (j - 1) * q ^ 2 ^ (j - 1) = q ^ (2 ^ (j - 1) + 2 ^ (j - 1)) :=
          (pow_add _ _ _).symm
      _ = q ^ 2 ^ j := by rw [h2j]
      _ = q ^ orderOf q := by rw [← hj]
      _ = 1 := pow_orderOf_eq_one q
  have hu_ne_one : u ≠ 1 := by
    intro hu1
    have hdvd2 : orderOf q ∣ 2 ^ (j - 1) := by
      rw [hu_def] at hu1
      exact orderOf_dvd_iff_pow_eq_one.mpr hu1
    rw [hj] at hdvd2
    have hlt : 2 ^ (j - 1) < 2 ^ j :=
      Nat.pow_lt_pow_right (by norm_num)
        (Nat.sub_lt (by omega) (by norm_num))
    have hle : 2 ^ j ≤ 2 ^ (j - 1) :=
      Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd2
    omega
  have hu_ord : orderOf u = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hu_sq
    · exact hu_ne_one
  have hdu : d * u * d⁻¹ = u := by
    have hconj : d * u * d⁻¹ = (d * q * d⁻¹) ^ (2 ^ (j - 1)) := by
      rw [hu_def]
      have hh := map_pow (MulAut.conj d).toMonoidHom q (2 ^ (j - 1))
      simpa [MulAut.conj_apply] using hh
    rw [hconj, hdq_conj]
  exact ⟨d, hd_memD, hd_ne_one, u, hu_mem_Q, hu_ord, hdu⟩

/-! ## The main theorem -/

theorem isZassenhaus_of_centD_eq_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q)
    (hc : Submission.Blueprint.centD H t = ⊥) : Submission.Blueprint.IsZassenhaus H := by
  by_contra hZ
  obtain ⟨d, hdD, hd1, u, huQ, hu2, hdu⟩ :=
    exists_involution_centralized_of_not_isZassenhaus h h2 hZ
  have hKeq := Kset_eq_twoPoint_of_centD_eq_bot h hc
  have hdK : d ∈ Work.ThmF.Kset H t := by rw [hKeq]; exact hdD
  have h1K : (1 : G) ∈ Work.ThmF.Kset H t := Work.ThmF.one_mem_Kset H t
  have hinj := Work.ThmF.Bender.Kset_conj_injective h.stronglyEmbedded h.invol h.not_mem
    (h.le huQ) hu2
  have himg : d * u * d⁻¹ = 1 * u * 1⁻¹ := by
    rw [one_mul, inv_one, mul_one]; exact hdu
  exact hd1 (hinj hdK h1K himg)

end Work.ThmF.ChV12
