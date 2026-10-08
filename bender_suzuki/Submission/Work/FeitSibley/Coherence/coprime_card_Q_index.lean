import Mathlib
import Submission.Work.FeitSibley.Basic
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.inf_H_conj_Q_eq_bot
import Submission.Work.FeitSibley.Coherence.normalizer_le_H_of_le_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.coprime_card_Q_index`

`(|Q|, [G : Q]) = 1` for the Feit–Sibley data `h : FSData G`: the T.I. subgroup `Q` is a Hall
subgroup of `G`.  This is the "Hall property of `Q`" used by Peterfalvi II Appendice XII, step
(7) (`irr_congr_mod_card_Q`) and the parenthetical remark on p. 288: *"These hypotheses imply `Q`
is a Hall subgroup of `G`, since if `P` is a Sylow subgroup `≠ 1` of `Q`, then `N_G(P) ⊆ H`."*

The argument, with `p` a prime dividing `|Q|`:

* every nontrivial subgroup `P ≤ Q` has `N_G(P) ≤ H` — this is the T.I. property
  (`normalizer_le_H_of_le_Q`);
* since `H = Q ⋊ D` with `(|Q|,|D|) = 1`, every `p`-subgroup of `H` lies in `Q`
  (`pSubgroup_le_Q_of_le_H`);
* take an element `x ∈ Q` of order `p` and a Sylow `p`-subgroup `S ≤ G` containing `⟨x⟩`.  The
  centre of `S` gives a nontrivial `p`-subgroup `Z ≤ S` centralising `S`
  (`exists_center_subgroup_le_centralizer`).  Then `Z ≤ C_G(⟨x⟩) ≤ N_G(⟨x⟩) ≤ H`, so `Z ≤ Q`;
  applying the first bullet again to `Z` gives `N_G(Z) ≤ H`, and `S ≤ C_G(Z) ≤ N_G(Z) ≤ H`;
* hence `p ∣ [G : H]`.  But `[G : H]·[H : Q] = [G : Q]` and `p ∤ [H : Q]` (the latter is `|D|`),
  so a Sylow `p`-subgroup of `G` contained in `H` has index divisible by `p`, contradicting
  `Sylow.not_dvd_index`.
-/

noncomputable section

open Classical

set_option linter.style.haveILetI false

namespace Work.FeitSibley.Coherence

/-- If a prime `p` divides `|Q|` then it does not divide `|D|` (as `(|D|,|Q|) = 1`).  Equivalently,
`p ∤ [H : Q]`. -/
theorem not_dvd_card_D_of_dvd_card_Q {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpQ : p ∣ Nat.card h.Q) : ¬ p ∣ Nat.card h.D := by
  intro hpdvd
  have hcop : Nat.Coprime p (Nat.card h.Q) := h.coprime_D_Q.coprime_dvd_left hpdvd
  exact (hp.coprime_iff_not_dvd.mp hcop) hpQ

/-- **Hall uniqueness for `p`-subgroups.**  Since `H = Q ⋊ D` with `(|Q|,|D|) = 1` and
`p ∣ |Q|`, the quotient `H ⧸ Q` has order `|D|` coprime to `p`, so every `p`-subgroup of `H`
lies in `Q`. -/
theorem pSubgroup_le_Q_of_le_H {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpQ : p ∣ Nat.card h.Q) {K : Subgroup G} (hK : IsPGroup p K) (hKH : K ≤ h.H) :
    K ≤ h.Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpd : ¬ p ∣ Nat.card h.D := not_dvd_card_D_of_dvd_card_Q h hp hpQ
  haveI hQn : (h.Q.subgroupOf h.H).Normal :=
    (Subgroup.normal_subgroupOf_iff h.Q_le_H).mpr (fun q _ hq hk =>
      (Subgroup.mem_normalizer_iff.mp (h.Q_normal_in_H hk) q).mp hq)
  refine le_of_coprime_card_quotient_subgroupOf (H := h.H) (N := h.Q) (K := K) hKH ?_
  rw [card_quot_H_Q_eq_card_D h]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hK
  rw [hn]
  exact (hp.coprime_pow_of_not_dvd hpd).symm

/-- **The centre of a nontrivial Sylow `p`-subgroup.**  A nontrivial Sylow `p`-subgroup `S` of `G`
contains a nontrivial `p`-subgroup `Z` (the image of the centre of `S`) that centralises `S`. -/
theorem exists_center_subgroup_le_centralizer {G : Type} [Group G] [Fintype G] {p : ℕ}
    [Fact p.Prime] (S : Sylow p G) (hS : (S : Subgroup G) ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≠ ⊥ ∧ Z ≤ (S : Subgroup G) ∧ IsPGroup p Z ∧
      Z ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  haveI : Nontrivial ↥(S : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS
  have hcenter : Subgroup.center ↥(S : Subgroup G) ≠ ⊥ :=
    ne_of_gt (IsPGroup.bot_lt_center S.isPGroup')
  refine ⟨(Subgroup.center ↥(S : Subgroup G)).map (S : Subgroup G).subtype, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
    have hmem : ((a : ↥(S : Subgroup G)) : G)
        ∈ (Subgroup.center ↥(S : Subgroup G)).map (S : Subgroup G).subtype :=
      Subgroup.mem_map.mpr ⟨(a : ↥(S : Subgroup G)), a.2, rfl⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨((a : ↥(S : Subgroup G)) : G), hmem⟩, ?_⟩
    intro hcon
    have h1 : ((a : ↥(S : Subgroup G)) : G) = 1 := by
      simpa using congrArg Subtype.val hcon
    exact ha (Subtype.ext (Subtype.ext h1))
  · exact Subgroup.map_subtype_le _
  · exact IsPGroup.to_le S.isPGroup' (Subgroup.map_subtype_le _)
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw (⟨s, hs⟩ : ↥(S : Subgroup G)))

/-- **`Q` is a Hall subgroup of `G`.** -/
theorem coprime_card_Q_index {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    Nat.Coprime (Nat.card h.Q) h.Q.index := by
  by_contra hcon
  rw [Nat.Prime.not_coprime_iff_dvd] at hcon
  obtain ⟨p, hp, hpQ, hpidx⟩ := hcon
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p ∤ [H : Q]` and `p ∣ [G : Q]`, hence `p ∣ [G : H]`
  have hpdD : ¬ p ∣ Nat.card h.D := not_dvd_card_D_of_dvd_card_Q h hp hpQ
  have hpdidx : ¬ p ∣ (h.Q.subgroupOf h.H).index := by
    intro hc
    rw [Subgroup.index_eq_card] at hc
    rw [card_quot_H_Q_eq_card_D h] at hc
    exact hpdD hc
  have hpdrel : ¬ p ∣ h.Q.relIndex h.H := hpdidx
  have hpH : p ∣ h.H.index := by
    have h1 : p ∣ h.Q.index := hpidx
    rw [← Subgroup.relIndex_mul_index h.Q_le_H] at h1
    rcases hp.dvd_mul.mp h1 with hh | hh
    · exact absurd hh hpdrel
    · exact hh
  -- a subgroup of `Q` of order `p` (Cauchy)
  obtain ⟨x, hx⟩ : ∃ x : ↥h.Q, orderOf x = p :=
    exists_prime_orderOf_dvd_card' (G := ↥h.Q) p hpQ
  set P : Subgroup G := (Subgroup.zpowers x).map h.Q.subtype with hPdef
  have hPcard : Nat.card P = p := by
    rw [hPdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective h.Q), Nat.card_zpowers,
      hx]
  have hPle : P ≤ h.Q := by rw [hPdef]; exact Subgroup.map_subtype_le _
  have hPne : P ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hPpg : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  -- a Sylow `p`-subgroup of `G` containing `P`
  obtain ⟨S, hSle⟩ := hPpg.exists_le_sylow
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hb
    exact hPne (le_bot_iff.mp (hSle.trans (le_of_eq hb)))
  -- its centre gives a nontrivial `p`-subgroup `Z` centralising `S`
  obtain ⟨Z, hZne, _hZS, hZpg, hZcentS⟩ := exists_center_subgroup_le_centralizer S hSne
  have hZcentP : Z ≤ Subgroup.centralizer (P : Set G) :=
    hZcentS.trans (Subgroup.centralizer_le hSle)
  have hZleH : Z ≤ h.H :=
    hZcentP.trans ((Subgroup.centralizer_le_normalizer (P : Set G)).trans
      (normalizer_le_H_of_le_Q h hPle hPne))
  have hZleQ : Z ≤ h.Q := pSubgroup_le_Q_of_le_H h hp hpQ hZpg hZleH
  have hSZ : (S : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) :=
    ((Subgroup.le_centralizer_iff).mpr hZcentS).trans
      (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hSH : (S : Subgroup G) ≤ h.H := hSZ.trans (normalizer_le_H_of_le_Q h hZleQ hZne)
  -- but a Sylow `p`-subgroup of `G` has index coprime to `p`
  exact Sylow.not_dvd_index S (dvd_trans hpH (Subgroup.index_dvd_of_le hSH))

end Work.FeitSibley.Coherence
