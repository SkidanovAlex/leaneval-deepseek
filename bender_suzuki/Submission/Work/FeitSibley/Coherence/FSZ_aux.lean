import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.FSZ_aux`

Standalone copies (with `_aux` suffixes) of the `Z = [Q₁,Q₁] ∩ Z(Q₁)` lemmas and of the
regular-character identity of Peterfalvi II, App. XII, step (8), extracted from
`Coherence/coherent_scriptSR_of_pgroup.lean` and `Coherence/step1.lean` so that they can be
imported by modules which must *not* depend on those files (breaking an import cycle).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical
open scoped commutatorElement

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

theorem FSZ_le_Q1_aux (h : Work.FeitSibley.FSData G) : FSZ h ≤ h.Q1 :=
  (inf_le_left.trans (Subgroup.commutator_le_sup h.Q1 h.Q1)).trans (le_of_eq (sup_idem h.Q1))

theorem FSZ_le_H_aux (h : Work.FeitSibley.FSData G) : FSZ h ≤ h.H :=
  (FSZ_le_Q1_aux h).trans h.Q1_le_H

theorem H_le_normalizer_commutator_Q1_aux {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer ((⁅h.Q1, h.Q1⁆ : Subgroup G) : Set G) := by
  have hmem : ∀ x ∈ h.H, (h.Q1).map (MulAut.conj x).toMonoidHom = h.Q1 := by
    intro x hx
    have hiff : ∀ y : G, y ∈ (h.Q1 : Set G) ↔ (MulAut.conj x) y ∈ (h.Q1 : Set G) := by
      intro y
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_set_normalizer_iff.mp (h.Q1_normal_in_H hx) y)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hiff z).mp hz
    · intro hy
      refine ⟨(MulAut.conj x).symm y, (hiff _).mpr ?_, MulEquiv.apply_symm_apply _ y⟩
      rw [MulEquiv.apply_symm_apply]
      exact hy
  rw [Subgroup.le_normalizer_iff]
  intro t ht k hk
  have hmap : (⁅h.Q1, h.Q1⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅h.Q1, h.Q1⁆ := by
    rw [Subgroup.map_commutator, hmem t ht]
  show (MulAut.conj t) k ∈ (⁅h.Q1, h.Q1⁆ : Subgroup G)
  have hthis : (MulAut.conj t) k
      ∈ (⁅h.Q1, h.Q1⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
  rwa [hmap] at hthis

theorem H_le_normalizer_centralizer_Q1_aux (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (Subgroup.centralizer (h.Q1 : Set G)) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx z hz
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro q hq
  have hx' : x⁻¹ ∈ h.H := h.H.inv_mem hx
  have hq' : x⁻¹ * q * (x⁻¹)⁻¹ ∈ h.Q1 :=
    (Subgroup.mem_set_normalizer_iff.mp (h.Q1_normal_in_H hx') q).mp hq
  have h1 : x⁻¹ * q * (x⁻¹)⁻¹ * z = z * (x⁻¹ * q * (x⁻¹)⁻¹) := hz _ hq'
  calc q * (x * z * x⁻¹) = x * ((x⁻¹ * q * (x⁻¹)⁻¹) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * q * (x⁻¹)⁻¹)) * x⁻¹ := by rw [h1]
    _ = (x * z * x⁻¹) * q := by group

theorem FSZ_normal_in_H_aux (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (FSZ h : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.le_normalizer_iff.mp (H_le_normalizer_commutator_Q1_aux h) x hx z hz1,
     Subgroup.le_normalizer_iff.mp (H_le_normalizer_centralizer_Q1_aux h) x hx z hz2⟩

theorem FSZ_commute_Q_aux (h : Work.FeitSibley.FSData G) {z : G} (hz : z ∈ FSZ h) :
    ∀ q ∈ h.Q, z * q = q * z := by
  have hzc : z ∈ Subgroup.centralizer (h.Q1 : Set G) := (Subgroup.mem_inf.mp hz).2
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_Q_decomp hq
  have h1 : z * a = a * z := (h.commute a ha z (FSZ_le_Q1_aux h hz)).symm
  have h2 : z * b = b * z := (Subgroup.mem_centralizer_iff.mp hzc b hb).symm
  calc z * (a * b) = z * a * b := by rw [mul_assoc]
    _ = a * z * b := by rw [h1]
    _ = a * (z * b) := by rw [mul_assoc]
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by rw [mul_assoc]

theorem commutator_inf_center_ne_bot_aux {X : Type*} [Group X] (hX : Group.IsNilpotent X)
    (hX' : commutator X ≠ ⊥) :
    commutator X ⊓ Subgroup.center X ≠ ⊥ := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup X) := Group.isNilpotent_top.mpr hX
  have hex : ∃ m, (⊤ : Subgroup X).lowerCentralSeries m = ⊥ :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries (⊤ : Subgroup X)).mp ‹_›
  have hspec : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex) = ⊥ := Nat.find_spec hex
  have htop_ne : (⊤ : Subgroup X) ≠ ⊥ := by
    intro htop
    exact hX' (eq_bot_iff.mpr (by rw [← htop]; exact le_top))
  have hNpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, Subgroup.lowerCentralSeries_zero] at hspec
      exact absurd hspec htop_ne
    · exact h
  have hN2 : 2 ≤ Nat.find hex := by
    by_contra hcon
    have hle : Nat.find hex = 0 ∨ Nat.find hex = 1 := by omega
    rcases hle with h | h
    · rw [h, Subgroup.lowerCentralSeries_zero] at hspec
      exact absurd hspec htop_ne
    · rw [h, Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
          Subgroup.commutator_comm] at hspec
      exact hX' hspec
  have hprev : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≠ ⊥ := by
    intro hc
    exact Nat.find_min hex (by omega) hc
  have hstep : ⁅(⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1), (⊤ : Subgroup X)⁆ = ⊥ := by
    have h1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [← Subgroup.lowerCentralSeries_succ, h1, hspec]
  have hcen : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≤ Subgroup.center X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hstep
    exact Subgroup.mem_centralizer_iff.mp (hle hz) g (Subgroup.mem_top g)
  have hle' : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≤ commutator X := by
    have hmono := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup X)
      (by omega : 1 ≤ Nat.find hex - 1)
    rwa [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
      Subgroup.commutator_comm] at hmono
  intro hc
  refine hprev (le_bot_iff.mp ?_)
  exact (le_inf hle' hcen).trans (le_of_eq hc)

theorem FSZ_ne_bot_aux (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) : FSZ h ≠ ⊥ := by
  intro hbot
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Group.IsNilpotent ↥h.Q1 := hpg.isNilpotent
  have hcomm : commutator ↥h.Q1 ≠ ⊥ := by
    intro hc
    apply hab
    have hmap := Subgroup.map_subtype_commutator h.Q1
    rw [← hmap, hc, Subgroup.map_bot]
  have hne := commutator_inf_center_ne_bot_aux (X := ↥h.Q1) ‹Group.IsNilpotent ↥h.Q1› hcomm
  apply hne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hx1' : (x : G) ∈ ⁅h.Q1, h.Q1⁆ := by
    have hmap := Subgroup.map_subtype_commutator h.Q1
    rw [← hmap]
    exact ⟨x, hx1, rfl⟩
  have hx2' : (x : G) ∈ Subgroup.centralizer (h.Q1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h2 := Subgroup.mem_center_iff.mp hx2 ⟨q, hq⟩
    exact congrArg Subtype.val h2
  have hmem : (x : G) ∈ FSZ h := Subgroup.mem_inf.mpr ⟨hx1', hx2'⟩
  rw [hbot] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hmem)

theorem Q1_eq_one_of_sq_eq_one_aux (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1) {z : G} (hz : z ∈ h.Q1) (hz2 : z ^ 2 = 1) :
    z = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hdvd1 : orderOf (⟨z, hz⟩ : ↥h.Q1) ∣ p ^ n := by
    rw [← hn]; exact orderOf_dvd_natCard _
  have hdvd2 : orderOf (⟨z, hz⟩ : ↥h.Q1) ∣ 2 := by
    rw [(Subgroup.orderOf_coe (⟨z, hz⟩ : ↥h.Q1)).symm]
    exact orderOf_dvd_of_pow_eq_one hz2
  have hcop : Nat.Coprime 2 (p ^ n) :=
    (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow_right n
  have hg : orderOf (⟨z, hz⟩ : ↥h.Q1) ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd hdvd2 hdvd1
  have h1 : (⟨z, hz⟩ : ↥h.Q1) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  simpa using Subtype.ext_iff.mp h1

theorem FSZ_not_inv_aux (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : IsPGroup p h.Q1) {z : G} (hz : z ∈ FSZ h) (hz1 : z ≠ 1) :
    ∀ g : G, g * z * g⁻¹ ≠ z⁻¹ := by
  intro g hg
  have hzQ1 : z ∈ h.Q1 := FSZ_le_Q1_aux h hz
  by_cases hgH : g ∈ h.H
  · obtain ⟨q, hq, dd, hd, rfl⟩ := h.mem_H_decomp hgH
    have hw : dd * z * dd⁻¹ = z⁻¹ := by
      have hqw : q * (dd * z * dd⁻¹) * q⁻¹ = z⁻¹ := by
        rw [show q * (dd * z * dd⁻¹) * q⁻¹ = q * dd * z * (q * dd)⁻¹ by group]
        exact hg
      calc dd * z * dd⁻¹ = q⁻¹ * (q * (dd * z * dd⁻¹) * q⁻¹) * q := by group
        _ = q⁻¹ * z⁻¹ * q := by rw [hqw]
        _ = q⁻¹ * (z⁻¹ * q) := by group
        _ = q⁻¹ * (q * z⁻¹) := by
            have hz' : z⁻¹ ∈ FSZ h := (FSZ h).inv_mem hz
            rw [FSZ_commute_Q_aux h hz' q hq]
        _ = z⁻¹ := by group
    by_cases hdd1 : dd = 1
    · rw [hdd1] at hw
      simp at hw
      have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_inv_eq.mpr hw.symm
      exact hz1 (Q1_eq_one_of_sq_eq_one_aux h hp hp2 hpg hzQ1 hz2)
    · have hdd2' : (dd * dd) * z * (dd * dd)⁻¹ = z := by
        calc (dd * dd) * z * (dd * dd)⁻¹ = dd * (dd * z * dd⁻¹) * dd⁻¹ := by group
          _ = dd * z⁻¹ * dd⁻¹ := by rw [hw]
          _ = (dd * z * dd⁻¹)⁻¹ := by group
          _ = (z⁻¹)⁻¹ := by rw [hw]
          _ = z := by group
      have hdd2D : dd * dd ∈ h.D := h.D.mul_mem hd hd
      have hdd2ne : dd * dd ≠ 1 := by
        intro hc
        have hdvd2 : orderOf dd ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc)
        have hdvdD : orderOf dd ∣ Nat.card h.D := by
          have h1 : orderOf dd = orderOf (⟨dd, hd⟩ : ↥h.D) :=
            Subgroup.orderOf_coe (⟨dd, hd⟩ : ↥h.D)
          rw [h1]
          simpa using orderOf_dvd_natCard (⟨dd, hd⟩ : ↥h.D)
        have hcop : Nat.Coprime 2 (Nat.card h.D) := Nat.coprime_two_left.mpr h.D_odd
        have hg1 : orderOf dd ∣ 1 := by
          rw [← Nat.Coprime.gcd_eq_one hcop]
          exact Nat.dvd_gcd hdvd2 hdvdD
        exact hdd1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg1))
      exact hz1 (h.D_fpf_Q1 (dd * dd) hdd2D hdd2ne z hzQ1 hdd2')
  · have hTI := h.Q_TI g hgH
    have hzQ : z ∈ h.Q := h.Q1_le_Q hzQ1
    have hzg : z ∈ Submission.Blueprint.conj g h.Q := by
      rw [Submission.Blueprint.conj, Subgroup.mem_map]
      refine ⟨z⁻¹, h.Q.inv_mem hzQ, ?_⟩
      change g * z⁻¹ * g⁻¹ = z
      rw [show g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ by group, hg]
      group
    have : z ∈ (⊥ : Subgroup G) := by
      rw [← hTI]; exact Subgroup.mem_inf.mpr ⟨hzQ, hzg⟩
    exact hz1 (Subgroup.mem_bot.mp this)

theorem sum_deg_chi_sdiff_FSZ_aux {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {z : G} (hz : z ∈ FSZ h) (hz1 : z ≠ 1) :
    (∑ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        (χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩)
      - (∑ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        (χ 1) * χ 1)
      = -(Nat.card h.H : ℂ) := by
  classical
  set X : Finset (↥h.H → ℂ) := Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) with hX
  have hXsub : X ⊆ Work.CharCore.Irr ↥h.H := fun χ hχ =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hχ).1).1
  have hzH : (⟨z, FSZ_le_H_aux h hz⟩ : ↥h.H) ≠ 1 := fun hc => hz1 (Subtype.ext_iff.mp hc)
  have hzero : (∑ χ ∈ (Work.CharCore.Irr ↥h.H \ X),
      ((χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩ - (χ 1) * χ 1)) = 0 := by
    refine Finset.sum_eq_zero fun χ hχ => ?_
    rw [Finset.mem_sdiff] at hχ
    obtain ⟨hχIrr, hχX⟩ := hχ
    have hval : χ ⟨z, FSZ_le_H_aux h hz⟩ = χ 1 := by
      by_cases hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1
      · have hχZ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) := by
          by_contra hc
          exact hχX (Finset.mem_sdiff.mpr ⟨hχS, hc⟩)
        exact (mem_scriptSR_iff h (FSZ h)).mp hχZ |>.2 ⟨z, FSZ_le_H_aux h hz⟩ hz
      · have hall : ∀ x : ↥h.H, (x : G) ∈ h.Q1 → χ x = χ 1 := by
          intro x hx
          by_contra hc
          exact hχS (Finset.mem_filter.mpr ⟨hχIrr, ⟨x, hx, hc⟩⟩)
        exact hall ⟨z, FSZ_le_H_aux h hz⟩ (FSZ_le_Q1_aux h hz)
    rw [hval]; ring
  have hsum_eq : (∑ χ ∈ X, ((χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩ - (χ 1) * χ 1))
      = ∑ χ ∈ Work.CharCore.Irr ↥h.H,
          ((χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩ - (χ 1) * χ 1) := by
    have hs := Finset.sum_sdiff (f := fun χ : ↥h.H → ℂ =>
      ((χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩ - (χ 1) * χ 1)) hXsub
    rw [← hs, hzero, zero_add]
  have hreg : (∑ χ ∈ Work.CharCore.Irr ↥h.H,
      ((χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩ - (χ 1) * χ 1))
      = (Work.CharCore.regularChar ↥h.H) ⟨z, FSZ_le_H_aux h hz⟩
        - (Work.CharCore.regularChar ↥h.H) 1 := by
    have h1 : (∑ χ ∈ Work.CharCore.Irr ↥h.H, (χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩)
        = (∑ χ ∈ Work.CharCore.Irr ↥h.H, (Work.CharCore.irrDeg χ : ℂ) • χ)
            ⟨z, FSZ_le_H_aux h hz⟩ := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun χ hχ => by
        rw [Pi.smul_apply, smul_eq_mul, Work.CharCore.irrDeg_spec hχ]
    have h2 : (∑ χ ∈ Work.CharCore.Irr ↥h.H, (χ 1) * χ 1)
        = (∑ χ ∈ Work.CharCore.Irr ↥h.H, (Work.CharCore.irrDeg χ : ℂ) • χ) 1 := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun χ hχ => by
        rw [Pi.smul_apply, smul_eq_mul, Work.CharCore.irrDeg_spec hχ]
    rw [Finset.sum_sub_distrib, h1, h2, ← Work.CharCore.regularChar_eq_sum]
  rw [hX] at hsum_eq ⊢
  rw [← Finset.sum_sub_distrib, hsum_eq, hreg]
  simp [Work.CharCore.regularChar, hzH]

end Work.FeitSibley.Coherence
