/-
Area `A7REC`, file `Char/a7Excl24.lean`: exclusion of `|H| = 24` (design pass 8 §1.4).

The lemma `A7Excl24Prop` states that in a finite group `G` no subgroup `H` of order `24` can
contain the Suzuki configuration `(U, S', τ')` with `|U| = 3`, `|S'| = 8`, `τ' ∈ Z(S')` of order
`2` normalizing `U` and `S' ∩ C_G(U) = 1`.

The argument (Suzuki 1959, p. 270) is the "kernel argument":

* `N = N_H(U)` satisfies `|N| = 6` (Sylow: `|N| ≥ 6`, and `|N| ∈ {12, 24}` would force `U ⊴ H`,
  whence `H/C_H(U) ↪ Aut(U) ≅ C₂` gives `|C_H(U)| ≥ 12`, contradicting
  `S' ∩ C_H(U) = 1` via `|S'| · |C_H(U)| ≤ |H|`).
* `C_H(τ') = S'` (as `|C_H(τ')| ∈ {8, 24}`), so `τ'` has exactly `3` conjugates in `H`; these are
  the three involutions of `N = ⟨U, τ'⟩ ≅ S₃`, hence every conjugate of `τ'` normalizes `U`.
* Hence `τ'` lies in the core `K` of `N` in `H`.  For `u ∈ U` the commutator
  `[u, τ'] = u τ' u⁻¹ τ'⁻¹` lies in `K` (normality) and in `U`, and it is `≠ 1`; as `U` has prime
  order, `U = ⟨[u,τ']⟩ ≤ K`.
* `K ⊴ H` and `K ≤ N` then force all conjugates of `U` to lie in `N`, a group of order `6` that
  cannot contain two distinct subgroups of order `3` (their product would have `9` elements) —
  contradicting the fact that `U` has `4` conjugates in `H`.

Everything is proved for an abstract finite group `C` of order `24` (`excl24_aux`), and then
transported to `H ≤ G`.
-/
import Mathlib
import Submission.Work.A7REC.Excl

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup

/-- In a subgroup of order `3`, every nonidentity element generates the whole subgroup. -/
theorem zpowers_eq_of_card_three {C : Type*} [Group C] [Finite C] {U : Subgroup C}
    (hU : Nat.card U = 3) {u : C} (hu : u ∈ U) (hu1 : u ≠ 1) : Subgroup.zpowers u = U := by
  have hle : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.mpr hu
  have h3 : orderOf u = 3 := by
    have hdvd : orderOf u ∣ 3 := by
      rw [← Nat.card_zpowers, ← hU]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hU, Nat.card_zpowers, h3]

/-- Conjugation does not change the cardinality of a subgroup. -/
theorem card_map_conj {C : Type*} [Group C] (U : Subgroup C) (g : C) :
    Nat.card ↥(U.map (MulAut.conj g).toMonoidHom) = Nat.card ↥U :=
  (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) U).toEquiv).symm

/-- **Exclusion of `|C| = 24`** for the Suzuki configuration `(U, S, τ)`. -/
theorem excl24_aux {C : Type*} [Group C] [Finite C] (hC : Nat.card C = 24)
    {U S : Subgroup C} {τ : C} (hU3 : Nat.card U = 3) (hS8 : Nat.card S = 8)
    (hτS : τ ∈ S) (hτ2 : orderOf τ = 2) (hτcen : ∀ x ∈ S, x * τ = τ * x)
    (hτN : τ ∈ Subgroup.normalizer (U : Set C))
    (hdisj : S ⊓ Subgroup.centralizer (U : Set C) = ⊥) : False := by
  classical
  have hτ1 : τ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hτ2; omega
  have hτK : τ ∉ Subgroup.centralizer (U : Set C) := by
    intro hmem
    have h : τ ∈ S ⊓ Subgroup.centralizer (U : Set C) := ⟨hτS, hmem⟩
    rw [hdisj, Subgroup.mem_bot] at h
    exact hτ1 h
  set N : Subgroup C := Subgroup.normalizer (U : Set C) with hN
  have hUleN : U ≤ N := by rw [hN]; exact Subgroup.le_normalizer
  have hτNin : τ ∈ N := by rw [hN]; exact hτN
  -- ### `|N|` is a multiple of `6`
  have hdvd6 : 6 ∣ Nat.card N := by
    have h3 : 3 ∣ Nat.card N := by
      rw [← hU3]; exact Subgroup.card_dvd_of_le hUleN
    have h2 : 2 ∣ Nat.card N := by
      rw [← hτ2, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hτNin)
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by norm_num) h2 h3
    simpa using h
  have hNdvd : Nat.card N ∣ 24 := by
    have h := Subgroup.card_dvd_of_le (K := ⊤) (show N ≤ ⊤ from le_top)
    rwa [Subgroup.card_top, hC] at h
  -- ### `U` is not normal in `C`
  have hUnotNormal : ¬ U.Normal := by
    intro hUn
    haveI := hUn
    have hrange : Nat.card (MulAut.conjNormal (H := U)).range ≤ 2 := by
      calc Nat.card (MulAut.conjNormal (H := U)).range
          ≤ Nat.card (⊤ : Subgroup (MulAut ↥U)) := Subgroup.card_le_of_le le_top
        _ = Nat.card (MulAut ↥U) := Subgroup.card_top
        _ = 2 := by
            haveI : IsCyclic ↥U := isCyclic_of_card_dvd_prime (p := 3) (by rw [hU3])
            rw [IsCyclic.card_mulAut, hU3]
            decide
    have hkersub : (MulAut.conjNormal (H := U)).ker = Subgroup.centralizer (U : Set C) := by
      ext g
      constructor
      · intro hg
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hgy : (MulAut.conjNormal g) ⟨u, hu⟩ = ⟨u, hu⟩ := by
          have h1 := congrArg (fun f : MulAut ↥U => f ⟨u, hu⟩) hg
          simpa using h1
        have h1 := congrArg (fun y : ↥U => (y : C)) hgy
        rw [MulAut.conjNormal_apply] at h1
        have h2 : g * u * g⁻¹ = u := h1
        calc u * g = (g * u * g⁻¹) * g := by rw [h2]
          _ = g * u := by group
      · intro h
        rw [MonoidHom.mem_ker]
        refine MulEquiv.ext (fun y => ?_)
        apply Subtype.ext
        show g * (y : C) * g⁻¹ = (y : C)
        have hy : (y : C) * g = g * (y : C) := h (y : C) y.2
        rw [← hy]; group
    have hmul := Subgroup.card_ker_mul_card_range (MulAut.conjNormal (H := U))
    rw [hkersub, hC] at hmul
    have hinj : Function.Injective
        (fun p : ↥S × ↥(Subgroup.centralizer (U : Set C)) => (p.1 : C) * (p.2 : C)) := by
      rintro ⟨s1, k1⟩ ⟨s2, k2⟩ heq
      simp only at heq
      have h1 : (s1 : C)⁻¹ * (s2 : C) = (k1 : C) * (k2 : C)⁻¹ := by
        have hh := congrArg (fun x : C => (s1 : C)⁻¹ * x * (k2 : C)⁻¹) heq
        simpa [mul_assoc] using hh.symm
      have hmem : (s1 : C)⁻¹ * (s2 : C) ∈ S ⊓ Subgroup.centralizer (U : Set C) :=
        ⟨S.mul_mem (S.inv_mem s1.2) s2.2, by
          rw [h1]
          exact Subgroup.mul_mem _ k1.2 (Subgroup.inv_mem _ k2.2)⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      have hs : s1 = s2 := Subtype.ext (by
        have hc := congrArg (fun x : C => (s1 : C) * x) hmem
        simpa using hc.symm)
      have hk' : (k1 : C) = (k2 : C) := by
        have hc : (k1 : C) * (k2 : C)⁻¹ = 1 := by rw [← h1, hmem]
        exact mul_inv_eq_one.mp hc
      exact Prod.ext hs (Subtype.ext hk')
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hS8, hC] at hle
    have hKle : Nat.card ↥(Subgroup.centralizer (U : Set C)) ≤ 3 := by omega
    have hKge : 12 ≤ Nat.card ↥(Subgroup.centralizer (U : Set C)) := by
      have h2 : 24 ≤ Nat.card ↥(Subgroup.centralizer (U : Set C)) * 2 := by
        calc (24 : ℕ) = Nat.card ↥(Subgroup.centralizer (U : Set C))
              * Nat.card (MulAut.conjNormal (H := U)).range := hmul.symm
          _ ≤ Nat.card ↥(Subgroup.centralizer (U : Set C)) * 2 := Nat.mul_le_mul_left _ hrange
      omega
    omega
  -- ### `|N| ∈ {6, 12, 24}`
  obtain ⟨k, hk⟩ := hdvd6
  have hkpos : 0 < k := by
    have hNpos : 0 < Nat.card N := Nat.card_pos
    rw [hk] at hNpos
    omega
  have hkle : k ≤ 4 := by
    have h24 : 6 * k ≤ 24 := by
      rw [← hk]; rw [← hC]; exact Subgroup.card_le_card_group N
    omega
  interval_cases k
  · -- ### `|N| = 6`
    have hN6 : Nat.card N = 6 := by rw [hk]
    -- ### `C_C(τ) = S`
    have hSleC : S ≤ Subgroup.centralizer ({τ} : Set C) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hτcen x hx).symm
    have hCS : Subgroup.centralizer ({τ} : Set C) = S := by
      have hdvd : Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) ∣ 24 := by
        have h := Subgroup.card_dvd_of_le (K := ⊤)
          (show Subgroup.centralizer ({τ} : Set C) ≤ ⊤ from le_top)
        rwa [Subgroup.card_top, hC] at h
      have hdvd8 : 8 ∣ Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) := by
        rw [← hS8]; exact Subgroup.card_dvd_of_le hSleC
      obtain ⟨j, hj⟩ := hdvd8
      have hjdvd : j ∣ 3 := by
        rw [hj] at hdvd
        obtain ⟨m, hm⟩ := hdvd
        refine ⟨m, ?_⟩
        have h' : 8 * 3 = 8 * (j * m) := by rw [← mul_assoc, ← hm]
        exact Nat.eq_of_mul_eq_mul_left (show 0 < 8 by norm_num) h'
      rcases (Nat.dvd_prime Nat.prime_three).mp hjdvd with hj1 | hj3
      · refine (Subgroup.eq_of_le_of_card_ge (H := S)
          (K := Subgroup.centralizer ({τ} : Set C)) hSleC ?_).symm
        rw [hS8, hj, hj1]
      · exfalso
        have htop : Subgroup.centralizer ({τ} : Set C) = ⊤ :=
          Subgroup.eq_top_of_card_eq _ (by rw [hj, hj3, hC])
        have hτUcen : τ ∈ Subgroup.centralizer (U : Set C) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have hz' : z ∈ Subgroup.centralizer ({τ} : Set C) := by rw [htop]; trivial
          exact ((Subgroup.mem_centralizer_iff.mp hz') τ (Set.mem_singleton τ)).symm
        exact hτK hτUcen
    -- ### the conjugacy class of `τ` has `3` elements
    have hclass : (conjugatesOf τ).ncard = 3 := by
      have h1 : (Subgroup.centralizer ({τ} : Set C)).index = 3 := by
        rw [hCS]
        have h2 := Subgroup.card_mul_index S
        rw [hS8, hC] at h2
        omega
      rw [← Subgroup.index_centralizer_eq_ncard (G := C) τ]
      exact h1
    -- ### a nonidentity element of `U`
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
      by_contra hcon
      have hcon' : ∀ x ∈ U, x = 1 := fun x hx => by
        by_contra hx1
        exact hcon ⟨x, hx, hx1⟩
      have hbot : U = ⊥ := by
        ext x
        constructor
        · intro hx; exact hcon' x hx
        · intro hx; rw [Subgroup.mem_bot] at hx; rw [hx]; exact U.one_mem
      rw [hbot, Subgroup.card_bot] at hU3
      omega
    have hgen : Subgroup.zpowers u = U := zpowers_eq_of_card_three hU3 hu hu1
    -- auxiliary: a nonidentity element of `U` commuting with `τ` puts `τ` in `C_C(U)`
    have hkey : ∀ {w : C}, w ∈ U → w ≠ 1 → w * τ = τ * w →
        τ ∈ Subgroup.centralizer (U : Set C) := by
      intro w hw hwne hcomm
      have hwC : w ∈ Subgroup.centralizer ({τ} : Set C) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm.symm
      have hUle : U ≤ Subgroup.centralizer ({τ} : Set C) := by
        rw [← zpowers_eq_of_card_three hU3 hw hwne]
        exact Subgroup.zpowers_le.mpr hwC
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp (hUle hz)) τ (Set.mem_singleton τ)).symm
    have hu2 : u * u ∈ U := U.mul_mem hu hu
    have hu2ne1 : u * u ≠ 1 := by
      intro h
      have h3 : orderOf u = 3 := by rw [← Nat.card_zpowers, hgen, hU3]
      have hp : u ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one u
      have huu : u = u ^ 3 * (u * u)⁻¹ := by group
      rw [hp, h, inv_one, mul_one] at huu
      exact hu1 huu
    have hA : u * τ * u⁻¹ ≠ τ := by
      intro h
      have hcomm : u * τ = τ * u := by
        have hh := congrArg (fun x => x * u) h
        simpa [mul_assoc] using hh
      exact hτK (hkey hu hu1 hcomm)
    have hB : u⁻¹ * τ * u ≠ τ := by
      intro h
      apply hA
      have hh := congrArg (fun x => u * x * u⁻¹) h
      simpa [mul_assoc] using hh.symm
    have hCne : u * τ * u⁻¹ ≠ u⁻¹ * τ * u := by
      intro h
      have h2 : (u * u) * τ = τ * (u * u) := by
        have hh := congrArg (fun x => u⁻¹ * x * u) h
        have hh2 : τ = (u * u)⁻¹ * τ * (u * u) := by simpa [mul_assoc] using hh
        nth_rewrite 1 [hh2]
        group
      exact hτK (hkey hu2 hu2ne1 h2)
    -- ### every conjugate of `τ` normalizes `U`
    have hmemN1 : u * τ * u⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (hUleN hu) hτNin) (hUleN (U.inv_mem hu))
    have hmemN2 : u⁻¹ * τ * u ∈ N :=
      N.mul_mem (N.mul_mem (hUleN (U.inv_mem hu)) hτNin) (hUleN hu)
    have hT : ({τ, u * τ * u⁻¹, u⁻¹ * τ * u} : Set C) ⊆ conjugatesOf τ := by
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact isConj_iff.mpr ⟨1, by simp⟩
      · exact isConj_iff.mpr ⟨u, rfl⟩
      · exact isConj_iff.mpr ⟨u⁻¹, by rw [inv_inv]⟩
    have hTncard : ({τ, u * τ * u⁻¹, u⁻¹ * τ * u} : Set C).ncard = 3 := by
      have h1 : τ ∉ ({u * τ * u⁻¹, u⁻¹ * τ * u} : Set C) := by
        intro hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · exact hA hx.symm
        · exact hB hx.symm
      have h2 : u * τ * u⁻¹ ∉ ({u⁻¹ * τ * u} : Set C) := by
        intro hx
        rw [Set.mem_singleton_iff] at hx
        exact hCne hx
      rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
    have hTeq : ({τ, u * τ * u⁻¹, u⁻¹ * τ * u} : Set C) = conjugatesOf τ :=
      Set.eq_of_subset_of_ncard_le hT (by rw [hclass, hTncard])
    have hconjN : ∀ c : C, c⁻¹ * τ * c ∈ N := by
      intro c
      have hmem : c⁻¹ * τ * c ∈ conjugatesOf τ := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩
      rw [← hTeq] at hmem
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · rw [h]; exact hτNin
      · rw [h]; exact hmemN1
      · rw [h]; exact hmemN2
    -- ### `τ` lies in the core of `N`, whence `U ≤ N.normalCore`
    have hcore_le : N.normalCore ≤ N := Subgroup.normalCore_le N
    have hcore_normal : N.normalCore.Normal := Subgroup.normalCore_normal N
    have hτcore : τ ∈ N.normalCore := by
      rw [Subgroup.normalCore_eq_iInf_map_conj, Subgroup.mem_iInf]
      intro c
      rw [Subgroup.mem_map]
      refine ⟨c⁻¹ * τ * c, hconjN c, ?_⟩
      show c * (c⁻¹ * τ * c) * c⁻¹ = τ
      group
    have hw_mem : u * τ * u⁻¹ * τ⁻¹ ∈ N.normalCore :=
      (N.normalCore).mul_mem (hcore_normal.conj_mem τ hτcore u) ((N.normalCore).inv_mem hτcore)
    have hτinvU : τ * u⁻¹ * τ⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hτN u⁻¹).mp (U.inv_mem hu)
    have hw_U : u * τ * u⁻¹ * τ⁻¹ ∈ U := by
      have heq : u * τ * u⁻¹ * τ⁻¹ = u * (τ * u⁻¹ * τ⁻¹) := by group
      rw [heq]; exact U.mul_mem hu hτinvU
    have hw_ne : u * τ * u⁻¹ * τ⁻¹ ≠ 1 := by
      intro h
      apply hA
      have hh := congrArg (fun x => x * τ) h
      simpa [mul_assoc] using hh
    have hU_le_core : U ≤ N.normalCore := by
      have hgen' : Subgroup.zpowers (u * τ * u⁻¹ * τ⁻¹) = U :=
        zpowers_eq_of_card_three hU3 hw_U hw_ne
      rw [← hgen']
      exact Subgroup.zpowers_le.mpr hw_mem
    -- ### some conjugate of `U` differs from `U`
    have hexists : ∃ c : C, U.map (MulAut.conj c).toMonoidHom ≠ U := by
      by_contra hcon
      have hcon' : ∀ c : C, U.map (MulAut.conj c).toMonoidHom = U := fun c => by
        by_contra hc
        exact hcon ⟨c, hc⟩
      exact hUnotNormal ⟨fun n hn g => by
        rw [← hcon' g]
        exact Subgroup.mem_map.mpr ⟨n, hn, MulAut.conj_apply g n⟩⟩
    obtain ⟨c, hc⟩ := hexists
    set Uc : Subgroup C := U.map (MulAut.conj c).toMonoidHom with hUc
    have hUc_card : Nat.card ↥Uc = 3 := by
      rw [hUc]
      exact (card_map_conj U c).trans hU3
    have hUc_le_core : Uc ≤ N.normalCore := by
      intro x hx
      rw [hUc] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hcore_normal.conj_mem y (hU_le_core hy) c
    have hUc_le_N : Uc ≤ N := hUc_le_core.trans hcore_le
    have hdisj2 : U ⊓ Uc = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      have hdvd : Nat.card ↥(U ⊓ Uc) ∣ 3 := by
        rw [← hU3]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exfalso
        have hEq : U ⊓ Uc = U :=
          Subgroup.eq_of_le_of_card_ge (H := U ⊓ Uc) (K := U) inf_le_left (by rw [h, hU3])
        have hle : U ≤ Uc := hEq ▸ inf_le_right
        exact hc ((Subgroup.eq_of_le_of_card_ge (H := U) (K := Uc) hle
          (by rw [hUc_card, hU3])).symm)
    have hinj2 : Function.Injective (fun p : ↥U × ↥Uc =>
        (⟨(p.1 : C) * (p.2 : C),
          N.mul_mem (hcore_le (hU_le_core p.1.2)) (hUc_le_N p.2.2)⟩ : ↥N)) := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ heq
      simp only [Subtype.mk.injEq] at heq
      have h1 : (a1 : C)⁻¹ * (a2 : C) = (b1 : C) * (b2 : C)⁻¹ := by
        have hh := congrArg (fun x : C => (a1 : C)⁻¹ * x * (b2 : C)⁻¹) heq
        simpa [mul_assoc] using hh.symm
      have hmem : (a1 : C)⁻¹ * (a2 : C) ∈ U ⊓ Uc :=
        ⟨U.mul_mem (U.inv_mem a1.2) a2.2, by
          rw [h1]
          exact Uc.mul_mem b1.2 (Uc.inv_mem b2.2)⟩
      rw [hdisj2, Subgroup.mem_bot] at hmem
      have ha : a1 = a2 := Subtype.ext (by
        have hc' := congrArg (fun x : C => (a1 : C) * x) hmem
        simpa using hc'.symm)
      have hb : b1 = b2 := Subtype.ext (by
        have hc' : (b1 : C) * (b2 : C)⁻¹ = 1 := by rw [← h1, hmem]
        exact mul_inv_eq_one.mp hc')
      exact Prod.ext ha hb
    have hle9 := Nat.card_le_card_of_injective _ hinj2
    rw [Nat.card_prod, hU3, hUc_card, hN6] at hle9
    omega
  · -- ### `|N| = 12` violates Sylow's congruence `n₃ ≡ 1 (mod 3)`
    exfalso
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hfac : (Nat.card C).factorization 3 = 1 := by
      rw [hC]
      rw [show (24 : ℕ) = 3 * 8 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 8)]
    let H3 : Sylow 3 C := Sylow.ofCard U (by rw [hfac, pow_one]; exact hU3)
    have hH3 : ((H3 : Subgroup C) : Set C) = (U : Set C) := by
      rw [Sylow.coe_ofCard]
    have hidx : Nat.card (Sylow 3 C) = N.index := by
      have h1 : Nat.card (Sylow 3 C)
          = (Subgroup.normalizer (((H3 : Subgroup C)) : Set C)).index :=
        Sylow.card_eq_index_normalizer H3
      rw [h1, hH3, hN]
    have hidx2 : N.index = 2 := by
      have h2 := Subgroup.card_mul_index N
      rw [hC] at h2
      rw [hk] at h2
      omega
    have hmod := card_sylow_modEq_one 3 C
    rw [hidx, hidx2] at hmod
    simp only [Nat.ModEq] at hmod
    omega
  · -- ### `|N| = 18` is impossible as `18 ∤ 24`
    exfalso
    have h18 : Nat.card N = 18 := by rw [hk]
    have hd : (18 : ℕ) ∣ 24 := h18 ▸ hNdvd
    norm_num at hd
  · -- ### `|N| = 24` forces `U ⊴ C`
    exact hUnotNormal (by
      have h24' : Nat.card N = 24 := by rw [hk]
      have htop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [h24', hC])
      rw [← Subgroup.normalizer_eq_top_iff, ← hN]
      exact htop)

/-- **`A7Excl24Prop`**: no subgroup `H` of order `24` contains the Suzuki configuration. -/
theorem a7Excl24 : Work.A7REC.A7Excl24Prop := by
  intro G _ _ U S' H τ hconf hUH hS'H h24
  obtain ⟨hU3, hS8, hτS, hτ2, hτcen, hτN, hdisj⟩ := hconf
  have hτH : τ ∈ H := hS'H hτS
  refine excl24_aux (C := ↥H) (U := U.subgroupOf H) (S := S'.subgroupOf H)
    (τ := ⟨τ, hτH⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h24]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]; exact hU3
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'H).toEquiv]; exact hS8
  · exact hτS
  · rw [← Subgroup.orderOf_coe (⟨τ, hτH⟩ : ↥H)]; exact hτ2
  · intro x hx
    apply Subtype.ext
    exact hτcen (x : G) hx
  · have hτN' : τ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hτN
    have hmem : (⟨τ, hτH⟩ : ↥H) ∈ (Subgroup.normalizer (U : Set G)).subgroupOf H := hτN'
    rwa [Subgroup.subgroupOf_normalizer_eq hUH] at hmem
  · refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxC⟩ := hx
    have hxS' : (x : G) ∈ S' := hxS
    have hxc : ∀ u ∈ U, u * (x : G) = (x : G) * u := by
      intro u hu
      have humem : (⟨u, hUH hu⟩ : ↥H) ∈ U.subgroupOf H := hu
      exact congrArg (fun y : ↥H => (y : G))
        ((Subgroup.mem_centralizer_iff.mp hxC) ⟨u, hUH hu⟩ humem)
    have hmem : (x : G) ∈ S' ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨hxS', Subgroup.mem_centralizer_iff.mpr hxc⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem

end Work.A7REC.Char
