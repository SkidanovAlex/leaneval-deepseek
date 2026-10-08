import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.S_le_H
import Submission.Work.BG.hyp12OfBGData
import Submission.Work.BG.indexOdd
import Submission.Work.GLUE.Defs
import Submission.Work.BG.conjClassCard
import Submission.Work.BG.invS_conj_t1_or_t2
import Submission.Work.BG.not_conj_t1_t2_in_S

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [Fintype G]

noncomputable def invJD (D : Work.GW2.BGData G) [Fintype ↥D.H] : Finset ↥D.H := by
  classical
  exact Finset.univ.filter (fun x : ↥D.H => x ^ 2 = 1 ∧ x ≠ 1 ∧ (x : G) ∉ H1 D)

noncomputable def conjClassF (K : Type) [Group K] [Fintype K] (x : K) : Finset K := by
  classical
  exact Finset.univ.image (fun g : K => g * x * g⁻¹)

variable (D : Work.GW2.BGData G)

theorem S_le_H' : (D.S : Subgroup G) ≤ D.H := S_le_H D
theorem U_le_H : D.U ≤ D.H := Subgroup.map_subtype_le _
theorem H_le_normalizer_U : D.H ≤ Subgroup.normalizer (D.U : Set G) := by
  rw [show D.U = Work.GW2.oddCoreIn D.H from rfl, Work.GW2.oddCoreIn_eq_opiCoreInG]
  exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _
theorem S_le_normalizer_U : (D.S : Subgroup G) ≤ Subgroup.normalizer (D.U : Set G) :=
  (S_le_H' D).trans (H_le_normalizer_U D)
theorem S0_le_normalizer_U : D.S0 ≤ Subgroup.normalizer (D.U : Set G) :=
  D.S0_le.trans (S_le_normalizer_U D)
theorem U_isPiSubgroup : IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
  rw [show D.U = Work.GW2.oddCoreIn D.H from rfl, Work.GW2.oddCoreIn_eq_opiCoreInG]
  exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
theorem odd_card_U : Odd (Nat.card ↥D.U) :=
  (Work.GW2.odd_card_iff_isPiSubgroup_ne_two D.U).mpr (U_isPiSubgroup D)
theorem U_inf_S : D.U ⊓ (D.S : Subgroup G) = ⊥ :=
  OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (U_isPiSubgroup D)
    (Subgroup.isPiSubgroup_of_isPGroup_of_mem D.S.isPGroup' (by simp))
theorem t1_sq : D.t1 ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t1_order).1
theorem t1_ne_one : D.t1 ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t1_order).2
theorem t2_sq : D.t2 ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t2_order).1
theorem t2_ne_one : D.t2 ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t2_order).2
theorem coe_U_sup_S0 : ↑(D.U ⊔ D.S0 : Subgroup G) = (↑D.U : Set G) * (↑D.S0 : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left D.U D.S0 (S0_le_normalizer_U D)
theorem coe_U_sup_S : ↑(D.U ⊔ (D.S : Subgroup G)) =
    (↑D.U : Set G) * (↑(D.S : Subgroup G) : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left D.U (D.S : Subgroup G) (S_le_normalizer_U D)
theorem H1_le_H : H1 D ≤ D.H := sup_le (U_le_H D) (D.S0_le.trans (S_le_H' D))
theorem mem_H1_of_eq_mul {u s : G} (hu : u ∈ D.U) (hs : s ∈ D.S0) : u * s ∈ H1 D := by
  have : u * s ∈ (↑D.U : Set G) * (↑D.S0 : Set G) := ⟨u, hu, s, hs, rfl⟩
  rwa [← coe_U_sup_S0 D] at this
theorem t1_notMem_H1 : D.t1 ∉ H1 D := by
  intro h
  have hmul : (D.t1 : G) ∈ (↑D.U : Set G) * (↑D.S0 : Set G) := by rw [← coe_U_sup_S0 D]; exact h
  obtain ⟨u, hu, s0, hs0, hus⟩ := Set.mem_mul.mp hmul
  have h1 : D.t1 * s0⁻¹ = u := by rw [← hus]; group
  have h2 : D.t1 * s0⁻¹ ∈ (D.S : Subgroup G) :=
    (D.S : Subgroup G).mul_mem D.t1_mem ((D.S : Subgroup G).inv_mem (D.S0_le hs0))
  have h3 : D.t1 * s0⁻¹ ∈ D.U := by rw [h1]; exact hu
  have h4 : D.t1 * s0⁻¹ = 1 := by
    have : D.t1 * s0⁻¹ ∈ D.U ⊓ (D.S : Subgroup G) := ⟨h3, h2⟩
    rw [U_inf_S D] at this
    simpa using this
  have h5 : D.t1 = s0 := mul_inv_eq_one.mp h4
  exact D.t1_nmem (h5 ▸ hs0)
theorem t2_notMem_H1 : D.t2 ∉ H1 D := by
  intro h
  have hmul : (D.t2 : G) ∈ (↑D.U : Set G) * (↑D.S0 : Set G) := by rw [← coe_U_sup_S0 D]; exact h
  obtain ⟨u, hu, s0, hs0, hus⟩ := Set.mem_mul.mp hmul
  have h1 : D.t2 * s0⁻¹ = u := by rw [← hus]; group
  have h2 : D.t2 * s0⁻¹ ∈ (D.S : Subgroup G) :=
    (D.S : Subgroup G).mul_mem D.t2_mem ((D.S : Subgroup G).inv_mem (D.S0_le hs0))
  have h3 : D.t2 * s0⁻¹ ∈ D.U := by rw [h1]; exact hu
  have h4 : D.t2 * s0⁻¹ = 1 := by
    have : D.t2 * s0⁻¹ ∈ D.U ⊓ (D.S : Subgroup G) := ⟨h3, h2⟩
    rw [U_inf_S D] at this
    simpa using this
  have h5 : D.t2 = s0 := mul_inv_eq_one.mp h4
  exact D.t2_nmem (h5 ▸ hs0)
theorem U_sup_S_eq_H (hrel : (H1 D).relIndex D.H = 2) :
    D.U ⊔ (D.S : Subgroup G) = D.H := by
  have ht1H : D.t1 ∈ D.H := S_le_H' D D.t1_mem
  have h1 : H1 D ⊔ Subgroup.zpowers D.t1 = D.H :=
    sup_zpowers_eq_of_relIndex_eq_two (H1_le_H D) hrel ht1H (t1_notMem_H1 D)
  have h2 : D.S0 ⊔ Subgroup.zpowers D.t1 = (D.S : Subgroup G) :=
    sup_zpowers_eq_of_relIndex_eq_two D.S0_le D.S0_index D.t1_mem D.t1_nmem
  calc D.U ⊔ (D.S : Subgroup G) = D.U ⊔ (D.S0 ⊔ Subgroup.zpowers D.t1) := by rw [h2]
    _ = D.U ⊔ D.S0 ⊔ Subgroup.zpowers D.t1 := (sup_assoc _ _ _).symm
    _ = H1 D ⊔ Subgroup.zpowers D.t1 := rfl
    _ = D.H := h1
theorem H1_normal (hrel : (H1 D).relIndex D.H = 2) : ((H1 D).subgroupOf D.H).Normal :=
  Subgroup.normal_of_index_eq_two (by rw [← Subgroup.relIndex]; exact hrel)
end Work.BG

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [Fintype G]

lemma mem_invJD (D : Work.GW2.BGData G) [Fintype ↥D.H] (x : ↥D.H) :
    x ∈ invJD D ↔ x ^ 2 = 1 ∧ x ≠ 1 ∧ (x : G) ∉ H1 D := by
  classical
  rw [invJD, Finset.mem_filter]
  simp

lemma mem_conjClassF {K : Type} [Group K] [Fintype K] (x y : K) :
    y ∈ conjClassF K x ↔ IsConj y x := by
  classical
  rw [conjClassF, Finset.mem_image]
  constructor
  · rintro ⟨g, -, hg⟩
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    rw [← hg]; group
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    exact ⟨g⁻¹, Finset.mem_univ _, by rw [← hg]; group⟩

theorem card_invJD (D : Work.GW2.BGData G) [Fintype ↥D.H] (hrel : (H1 D).relIndex D.H = 2) :
    (invJD D).card = (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H +
      (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := by
  classical
  have hUS := U_sup_S_eq_H D hrel
  have hnorm := H1_normal D hrel
  have ht1H : D.t1 ∈ D.H := S_le_H' D D.t1_mem
  have ht2H : D.t2 ∈ D.H := S_le_H' D D.t2_mem
  have ht1mul : D.t1 * D.t1 = 1 := by rw [← pow_two]; exact t1_sq D
  have ht2mul : D.t2 * D.t2 = 1 := by rw [← pow_two]; exact t2_sq D
  have ht1inv : D.t1⁻¹ = D.t1 := inv_eq_of_mul_eq_one_right ht1mul
  have ht2inv : D.t2⁻¹ = D.t2 := inv_eq_of_mul_eq_one_right ht2mul
  have hc1mul : (⟨D.t1, ht1H⟩ : ↥D.H) * ⟨D.t1, ht1H⟩ = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_mul, pow_two] using t1_sq D
  have hc2mul : (⟨D.t2, ht2H⟩ : ↥D.H) * ⟨D.t2, ht2H⟩ = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_mul, pow_two] using t2_sq D
  have hdecomp : ∀ x : ↥D.H, ∃ u : ↥D.U, ∃ s : ↥(D.S : Subgroup G), (u : G) * (s : G) = (x : G) := by
    intro x
    have hx : (x : G) ∈ (D.U ⊔ (D.S : Subgroup G) : Subgroup G) := by
      rw [hUS]; exact x.2
    have hx2 : (x : G) ∈ (↑D.U : Set G) * (↑(D.S : Subgroup G) : Set G) := by
      rw [← coe_U_sup_S D]; exact hx
    obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.mp hx2
    exact ⟨⟨u, hu⟩, ⟨s, hs⟩, hus⟩
  have huniq : ∀ (u u' : ↥D.U) (s s' : ↥(D.S : Subgroup G)),
      (u : G) * (s : G) = (u' : G) * (s' : G) → u = u' ∧ s = s' := by
    intro u u' s s' h
    have hkey : ((u' : G))⁻¹ * (u : G) = (s' : G) * ((s : G))⁻¹ := by
      calc ((u' : G))⁻¹ * (u : G)
          = ((u' : G))⁻¹ * ((u : G) * (s : G)) * (s : G)⁻¹ := by group
        _ = ((u' : G))⁻¹ * ((u' : G) * (s' : G)) * (s : G)⁻¹ := by rw [h]
        _ = (s' : G) * (s : G)⁻¹ := by group
    have hU : ((u' : G))⁻¹ * (u : G) ∈ D.U := D.U.mul_mem (D.U.inv_mem u'.2) u.2
    have hS : (s' : G) * ((s : G))⁻¹ ∈ (D.S : Subgroup G) :=
      (D.S : Subgroup G).mul_mem s'.2 ((D.S : Subgroup G).inv_mem s.2)
    have hmem : (s' : G) * ((s : G))⁻¹ ∈ D.U ⊓ (D.S : Subgroup G) := ⟨hkey ▸ hU, hS⟩
    rw [U_inf_S D] at hmem
    have h1 : (s' : G) * ((s : G))⁻¹ = 1 := by simpa using hmem
    have hs_eq : (s' : G) = (s : G) := mul_inv_eq_one.mp h1
    have hu_eq : (u : G) = (u' : G) := by
      have h' := h
      rw [hs_eq] at h'
      exact mul_right_cancel h'
    exact ⟨Subtype.ext hu_eq, Subtype.ext hs_eq.symm⟩
  have hsq : ∀ (u : ↥D.U) (s : ↥(D.S : Subgroup G)), ((u : G) * (s : G)) ^ 2 = 1 →
      (s : G) ^ 2 = 1 ∧ (s : G) * (u : G) * (s : G)⁻¹ = (u : G)⁻¹ := by
    intro u s h
    have hsplit : (u : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (s : G) ^ 2 =
        ((u : G) * (s : G)) ^ 2 := by rw [pow_two, pow_two]; group
    have hsplit1 : (u : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (s : G) ^ 2 = 1 := by
      rw [hsplit]; exact h
    have hU : (u : G) * ((s : G) * (u : G) * (s : G)⁻¹) ∈ D.U :=
      D.U.mul_mem u.2 ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_U D (S_le_H' D s.2))
        (u : G)).mp u.2)
    have hS : (s : G) ^ 2 ∈ (D.S : Subgroup G) := (D.S : Subgroup G).pow_mem s.2 2
    have heq : (u : G) * ((s : G) * (u : G) * (s : G)⁻¹) = ((s : G) ^ 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left hsplit1
    have hmem : (u : G) * ((s : G) * (u : G) * (s : G)⁻¹) ∈ D.U ⊓ (D.S : Subgroup G) :=
      ⟨hU, heq ▸ ((D.S : Subgroup G).inv_mem hS)⟩
    rw [U_inf_S D] at hmem
    have h1 : (u : G) * ((s : G) * (u : G) * (s : G)⁻¹) = 1 := by simpa using hmem
    have h2 : ((s : G) ^ 2)⁻¹ = 1 := by rw [← heq]; exact h1
    have hs2 : (s : G) ^ 2 = 1 := by
      have := congrArg Inv.inv h2
      simpa using this
    refine ⟨hs2, ?_⟩
    calc (s : G) * (u : G) * (s : G)⁻¹
        = (u : G)⁻¹ * ((u : G) * ((s : G) * (u : G) * (s : G)⁻¹)) := by group
      _ = (u : G)⁻¹ * 1 := by rw [h1]
      _ = (u : G)⁻¹ := mul_one _
  have hw : ∀ (u : ↥D.U) (s : ↥(D.S : Subgroup G)),
      (s : G) * (u : G) * (s : G)⁻¹ = (u : G)⁻¹ →
      ∃ g : ↥D.H, (g : G) * (s : G) * (g : G)⁻¹ = (u : G) * (s : G) := by
    intro u s hconj
    have hoddU : Odd (Nat.card ↥D.U) := odd_card_U D
    have hodd : Odd (orderOf (u : G)) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      exact hoddU.not_two_dvd_nat (h2.trans (Subgroup.orderOf_dvd_natCard D.U u.2))
    set m : ℕ := (orderOf (u : G) + 1) / 2 with hm
    have h2m : 2 * m = orderOf (u : G) + 1 := by
      rw [hm]; exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hodd.add_one)
    have hpowOU : (u : G) ^ orderOf (u : G) = 1 := pow_orderOf_eq_one (u : G)
    have hpow : (u : G) ^ (m + m) = (u : G) := by
      rw [show m + m = 2 * m from by ring, h2m, pow_succ, hpowOU, one_mul]
    have h1 : (s : G) * (u : G) ^ m * (s : G)⁻¹ = ((u : G) ^ m)⁻¹ := by
      have hconj' : (MulAut.conj (s : G)) (u : G) = (u : G)⁻¹ := by
        rw [MulAut.conj_apply]; exact hconj
      have : (MulAut.conj (s : G)) ((u : G) ^ m) = ((u : G) ^ m)⁻¹ := by
        rw [map_pow, hconj', ← inv_pow]
      simpa [MulAut.conj_apply] using this
    have h1' : (s : G) * ((u : G) ^ m)⁻¹ * (s : G)⁻¹ = (u : G) ^ m := by
      have : (s : G) * ((u : G) ^ m)⁻¹ * (s : G)⁻¹ = ((s : G) * (u : G) ^ m * (s : G)⁻¹)⁻¹ := by
        group
      rw [this, h1, inv_inv]
    refine ⟨⟨(u : G) ^ m, D.H.pow_mem (U_le_H D u.2) m⟩, ?_⟩
    calc (u : G) ^ m * (s : G) * ((u : G) ^ m)⁻¹
        = (u : G) ^ m * ((s : G) * ((u : G) ^ m)⁻¹ * (s : G)⁻¹) * (s : G) := by group
      _ = (u : G) ^ m * (u : G) ^ m * (s : G) := by rw [h1']
      _ = (u : G) ^ (m + m) * (s : G) := by rw [← pow_add]
      _ = (u : G) * (s : G) := by rw [hpow]
  have hmem_char : ∀ y : ↥D.H, y ∈ invJD D ↔
      IsConj y (⟨D.t1, ht1H⟩ : ↥D.H) ∨ IsConj y (⟨D.t2, ht2H⟩ : ↥D.H) := by
    intro y
    constructor
    · intro hy
      rw [mem_invJD] at hy
      obtain ⟨hy2, hyne, hyH1⟩ := hy
      have hy2G : ((y : G)) ^ 2 = 1 := by
        simpa using congrArg (fun z : ↥D.H => (z : G)) hy2
      obtain ⟨u, s, hus⟩ := hdecomp y
      have hs0 : (s : G) ∉ D.S0 := by
        intro hs0
        apply hyH1
        rw [← hus]
        exact mem_H1_of_eq_mul D u.2 hs0
      have hsqs : ((u : G) * (s : G)) ^ 2 = 1 := by rw [hus]; exact hy2G
      obtain ⟨hs2, hconj⟩ := hsq u s hsqs
      obtain ⟨g, hg⟩ := hw u s hconj
      have hconj_sy : IsConj (⟨(s : G), S_le_H' D s.2⟩ : ↥D.H) y := by
        refine isConj_iff.mpr ⟨⟨(g : G), g.2⟩, ?_⟩
        apply Subtype.ext
        simpa [hus] using hg
      rcases invS_conj_t1_or_t2 D s.2 hs0 with ⟨g', hg'S, hg'⟩ | ⟨g', hg'S, hg'⟩
      · left
        have hconj_s1 : IsConj (⟨(s : G), S_le_H' D s.2⟩ : ↥D.H) (⟨D.t1, ht1H⟩ : ↥D.H) := by
          refine isConj_iff.mpr ⟨⟨g', S_le_H' D hg'S⟩, ?_⟩
          apply Subtype.ext
          simpa using hg'
        exact hconj_sy.symm.trans hconj_s1
      · right
        have hconj_s2 : IsConj (⟨(s : G), S_le_H' D s.2⟩ : ↥D.H) (⟨D.t2, ht2H⟩ : ↥D.H) := by
          refine isConj_iff.mpr ⟨⟨g', S_le_H' D hg'S⟩, ?_⟩
          apply Subtype.ext
          simpa using hg'
        exact hconj_sy.symm.trans hconj_s2
    · intro hy
      have hmain : ∀ c : ↥D.H, c * c = 1 → (c : G) ∉ H1 D → IsConj y c → y ∈ invJD D := by
        intro c hcmul hcH1 hyc
        obtain ⟨a, ha⟩ := isConj_iff.mp hyc
        have hyeq : y = a⁻¹ * c * a := by rw [← ha]; group
        have hcmul' : c * c = 1 := hcmul
        have hy2 : y ^ 2 = 1 := by
          rw [hyeq, pow_two]
          have h3 : (a⁻¹ * c * a) * (a⁻¹ * c * a) = a⁻¹ * (c * c) * a := by group
          rw [h3, hcmul']; group
        have hcne : c ≠ 1 := by
          intro h1
          exact hcH1 (by rw [h1]; exact (H1 D).one_mem)
        have hyne : y ≠ 1 := by
          intro h1
          exact hcne (by rw [← ha, h1]; group)
        have hyH1 : (y : G) ∉ H1 D := by
          intro hyin
          have hsub : y ∈ (H1 D).subgroupOf D.H := by
            rw [Subgroup.mem_subgroupOf]; exact hyin
          have hcsub : c ∈ (H1 D).subgroupOf D.H := by
            rw [← ha]; exact hnorm.conj_mem y hsub a
          exact hcH1 (Subgroup.mem_subgroupOf.mp hcsub)
        rw [mem_invJD]
        exact ⟨hy2, hyne, hyH1⟩
      rcases hy with hy | hy
      · exact hmain ⟨D.t1, ht1H⟩ hc1mul (t1_notMem_H1 D) hy
      · exact hmain ⟨D.t2, ht2H⟩ hc2mul (t2_notMem_H1 D) hy
  have hdisj : Disjoint (conjClassF (↥D.H) (⟨D.t1, ht1H⟩ : ↥D.H))
      (conjClassF (↥D.H) (⟨D.t2, ht2H⟩ : ↥D.H)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [mem_conjClassF] at hy1 hy2
    have hconj : IsConj (⟨D.t1, ht1H⟩ : ↥D.H) (⟨D.t2, ht2H⟩ : ↥D.H) :=
      hy1.symm.trans hy2
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    have haG : (a : G) * D.t1 * (a : G)⁻¹ = D.t2 := by
      simpa using congrArg (fun z : ↥D.H => (z : G)) ha
    obtain ⟨v, sv, hvs⟩ := hdecomp a
    have key : (sv : G) * D.t1 * (sv : G)⁻¹ = D.t2 := by
      have h1 : (v : G) * ((sv : G) * D.t1 * (sv : G)⁻¹) * (v : G)⁻¹ = D.t2 := by
        rw [← haG, ← hvs]; group
      have hxS : (sv : G) * D.t1 * (sv : G)⁻¹ ∈ (D.S : Subgroup G) :=
        (D.S : Subgroup G).mul_mem ((D.S : Subgroup G).mul_mem sv.2 D.t1_mem)
          ((D.S : Subgroup G).inv_mem sv.2)
      have hxe : (sv : G) * D.t1 * (sv : G)⁻¹ = (v : G)⁻¹ * (D.t2) * (v : G) := by
        rw [← h1]; group
      have hmemU : (sv : G) * D.t1 * (sv : G)⁻¹ * D.t2 ∈ D.U := by
        rw [hxe]
        have htv : D.t2 * (v : G) * (D.t2)⁻¹ ∈ D.U :=
          (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_U D ht2H) (v : G)).mp v.2
        have e : (v : G)⁻¹ * D.t2 * (v : G) * D.t2 = (v : G)⁻¹ * (D.t2 * (v : G) * (D.t2)⁻¹) := by
          rw [ht2inv]; group
        rw [e]
        exact D.U.mul_mem (D.U.inv_mem v.2) htv
      have hmemS : (sv : G) * D.t1 * (sv : G)⁻¹ * D.t2 ∈ (D.S : Subgroup G) :=
        (D.S : Subgroup G).mul_mem hxS D.t2_mem
      have hmem : (sv : G) * D.t1 * (sv : G)⁻¹ * D.t2 ∈ D.U ⊓ (D.S : Subgroup G) :=
        ⟨hmemU, hmemS⟩
      rw [U_inf_S D] at hmem
      have h1' : (sv : G) * D.t1 * (sv : G)⁻¹ * D.t2 = 1 := by simpa using hmem
      rw [eq_inv_of_mul_eq_one_left h1', ht2inv]
    exact not_conj_t1_t2_in_S D ⟨sv, sv.2, key⟩
  have hcardCls : ∀ c : ↥D.H, (conjClassF (↥D.H) c).card = Nat.card {y : ↥D.H // IsConj y c} := by
    intro c
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe (conjClassF (↥D.H) c)]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun y => ⟨y.1, (mem_conjClassF c y.1).mp y.2⟩
        invFun := fun y => ⟨y.1, (mem_conjClassF c y.1).mpr y.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro y; ext; rfl
    · intro y; ext; rfl
  have hcent : ∀ (x : G) (hx : x ∈ D.H),
      Subgroup.centralizer ({⟨x, hx⟩} : Set ↥D.H) =
        (Subgroup.centralizer ({x} : Set G)).subgroupOf D.H := by
    intro x hx
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; simpa using congrArg (fun z : ↥D.H => (z : G)) h
    · intro h; exact Subtype.ext (by simpa using h)
  have h1card : (conjClassF (↥D.H) (⟨D.t1, ht1H⟩ : ↥D.H)).card =
      (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H := by
    rw [hcardCls, conjClassCard, Subgroup.relIndex, hcent D.t1 ht1H]
  have h2card : (conjClassF (↥D.H) (⟨D.t2, ht2H⟩ : ↥D.H)).card =
      (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := by
    rw [hcardCls, conjClassCard, Subgroup.relIndex, hcent D.t2 ht2H]
  have hset : invJD D = conjClassF (↥D.H) (⟨D.t1, ht1H⟩ : ↥D.H) ∪
      conjClassF (↥D.H) (⟨D.t2, ht2H⟩ : ↥D.H) := by
    ext y
    rw [Finset.mem_union, mem_conjClassF, mem_conjClassF]
    exact hmem_char y
  rw [hset, Finset.card_union_of_disjoint hdisj, h1card, h2card]

end Work.BG

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup
open scoped Pointwise

noncomputable def subgrpEquiv {G : Type} [Group G] {A B : Subgroup G} (h : A = B) : ↥A ≃ ↥B :=
  { toFun := fun z => ⟨z.1, by rw [← h]; exact z.2⟩
    invFun := fun z => ⟨z.1, by rw [h]; exact z.2⟩
    left_inv := fun z => by ext; rfl
    right_inv := fun z => by ext; rfl }

lemma mem_invJ {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    [Fintype ↥C.P.H] (x : ↥C.P.H) :
    x ∈ Work.GW2.C16.invJ C ↔ x ^ 2 = 1 ∧ x ≠ 1 ∧ (x : G) ∉ C.P.H0 := by
  classical
  rw [Work.GW2.C16.invJ, Finset.mem_filter]
  simp

theorem invJCard {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H] :
    Work.GW2.C16.InvJCardProp D C := by
  classical
  intro hC
  obtain ⟨hH, hU, hH0, ht, hs⟩ := hC
  have hrel : (H1 D).relIndex D.H = 2 := by
    have h := C.P.H0_relIndex
    rw [hH0, hH] at h
    exact h
  have hcard : (Work.GW2.C16.invJ C).card = (invJD D).card := by
    have hmain : ∀ x : ↥C.P.H, (x ∈ Work.GW2.C16.invJ C) ↔ ((subgrpEquiv hH x) ∈ invJD D) := by
      intro x
      have hv : ((subgrpEquiv hH x : ↥D.H) : G) = (x : G) := rfl
      have hsq : ((subgrpEquiv hH x) ^ 2 = 1) ↔ (x ^ 2 = 1) := by
        constructor
        · intro h
          apply Subtype.ext
          have := congrArg (fun z : ↥D.H => (z : G)) h
          simpa [Subgroup.coe_pow, hv] using this
        · intro h
          apply Subtype.ext
          have := congrArg (fun z : ↥C.P.H => (z : G)) h
          simpa [Subgroup.coe_pow, hv] using this
      have hne : ((subgrpEquiv hH x : ↥D.H) ≠ 1) ↔ (x ≠ 1) := by
        constructor
        · intro h h1
          refine h (Subtype.ext ?_)
          rw [hv]
          simpa using congrArg (fun z : ↥C.P.H => (z : G)) h1
        · intro h h1
          refine h (Subtype.ext ?_)
          rw [← hv]
          simpa using congrArg (fun z : ↥D.H => (z : G)) h1
      rw [mem_invJ, mem_invJD]
      rw [hsq, hne, hv, hH0]
    rw [← Fintype.card_coe (Work.GW2.C16.invJ C), ← Fintype.card_coe (invJD D)]
    exact Fintype.card_congr (Equiv.subtypeEquiv (subgrpEquiv hH) hmain)
  show (Work.GW2.C16.invJ C).card = D.k
  rw [hcard]
  exact card_invJD D hrel

end Work.BG
