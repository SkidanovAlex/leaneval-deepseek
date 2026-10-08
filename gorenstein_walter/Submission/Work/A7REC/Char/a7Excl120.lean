/-
Area `A7REC`, file `Char/a7Excl120.lean`: the exclusion of `|H| = 120` (leaf `A7Excl120Prop`).

Given a finite group `G` with the Suzuki configuration `(U, S', τ)` (`ExclHyps`), the
involution-centralizer input `InvCent G`, and a subgroup `H ≤ G` of order `120` containing `U`
and `S'`, we derive a contradiction.

Everything happens inside `H`: with `U' := U.subgroupOf H`, `S'' := S'.subgroupOf H` and
`τ' := ⟨τ, _⟩`, the `Excl120Setup` bundle holds (`excl120_setup_of`), and the number of Sylow
`3`-subgroups of `H` (the index of `N_H(U')`) is `1`, `4`, `10` or `40`; each case is impossible
(the sibling files `a7Excl120IdxOne`, `a7Excl120IdxFour`, `a7Excl120IdxTen`, `a7Excl120IdxForty`).
-/
import Mathlib
import Submission.Work.A7REC.Excl
import Submission.Work.A7REC.Char.a7Excl120Common
import Submission.Work.A7REC.Char.a7Excl120Tools
import Submission.Work.A7REC.Char.a7Excl120IdxOne
import Submission.Work.A7REC.Char.a7Excl120IdxFour
import Submission.Work.A7REC.Char.a7Excl120IdxTen
import Submission.Work.A7REC.Char.a7Excl120IdxForty

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup

/-- The centralizer of `x` inside `H ∋ x` is the `subgroupOf` of `C_G(x)`. -/
theorem centralizer_subgroupOf_eq {G : Type*} [Group G] {H : Subgroup G} (x : G) (hx : x ∈ H) :
    (Subgroup.centralizer ({x} : Set G)).subgroupOf H
      = Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H) := by
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subtype.ext (h x (Set.mem_singleton x))
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact congrArg (fun w : ↥H => (w : G)) (h ⟨x, hx⟩ (Set.mem_singleton _))

/-- `↥(K.subgroupOf H)` and `↥(K ⊓ H)` are canonically in bijection. -/
def subgroupOfEquivInf {G : Type*} [Group G] (K H : Subgroup G) :
    ↥(K.subgroupOf H) ≃ ↥(K ⊓ H) where
  toFun z := ⟨(z.1 : G), Subgroup.mem_inf.mpr ⟨(Subgroup.mem_subgroupOf.mp z.2), z.1.2⟩⟩
  invFun w := ⟨⟨(w.1 : G), (Subgroup.mem_inf.mp w.2).2⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp w.2).1⟩
  left_inv z := by ext; rfl
  right_inv w := by ext; rfl

/-- The centralizer of `x` inside a subgroup `H ∋ x` has order dividing that of `C_G(x)`. -/
theorem card_centralizer_subgroupOf_dvd {G : Type*} [Group G] {H : Subgroup G} (x : G)
    (hx : x ∈ H) (h24 : Nat.card (Subgroup.centralizer ({x} : Set G)) = 24) :
    Nat.card (Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H)) ∣ 24 := by
  have hcard : Nat.card ↥((Subgroup.centralizer ({x} : Set G)).subgroupOf H)
      = Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ H) :=
    Nat.card_congr (subgroupOfEquivInf _ _)
  have hdvd : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ H)
      ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_dvd_of_le (K := Subgroup.centralizer ({x} : Set G)) inf_le_left
  rw [← centralizer_subgroupOf_eq x hx, hcard]
  rw [h24] at hdvd
  exact hdvd

/-- Uniqueness of the subgroup of order `3` in an involution centralizer is inherited by the
centralizer inside a subgroup. -/

theorem uniq_C3_subgroupOf {G : Type*} [Group G] {H : Subgroup G} (x : G) (hx : x ∈ H)
    (huniq : ∀ A B : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) →
      B ≤ Subgroup.centralizer ({x} : Set G) → Nat.card A = 3 → Nat.card B = 3 → A = B) :
    ∀ A B : Subgroup ↥H, A ≤ Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H) →
      B ≤ Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H) → Nat.card A = 3 → Nat.card B = 3 →
      A = B := by
  have hsub : (Subgroup.centralizer ({x} : Set G)).subgroupOf H
      = Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H) := centralizer_subgroupOf_eq x hx
  intro A B hA hB hAc hBc
  have hA' : A.map H.subtype ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z ∈ (Subgroup.centralizer ({x} : Set G)).subgroupOf H := by
      rw [hsub]; exact hA hz
    rwa [Subgroup.mem_subgroupOf] at hz'
  have hB' : B.map H.subtype ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z ∈ (Subgroup.centralizer ({x} : Set G)).subgroupOf H := by
      rw [hsub]; exact hB hz
    rwa [Subgroup.mem_subgroupOf] at hz'
  have hcA : Nat.card ↥(A.map H.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (K := A) Subtype.val_injective, hAc]
  have hcB : Nat.card ↥(B.map H.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (K := B) Subtype.val_injective, hBc]
  have heq : A.map H.subtype = B.map H.subtype := huniq _ _ hA' hB' hcA hcB
  calc A = (A.map H.subtype).comap H.subtype :=
        (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective A).symm
    _ = (B.map H.subtype).comap H.subtype := by rw [heq]
    _ = B := Subgroup.comap_map_eq_self_of_injective Subtype.val_injective B

theorem sylow3_card_cases {n : ℕ} (hdvd : n ∣ 120) (hmod : n ≡ 1 [MOD 3]) :
    n = 1 ∨ n = 4 ∨ n = 10 ∨ n = 40 := by
  have hm : n % 3 = 1 := by simpa [Nat.ModEq] using hmod
  have h120 : n ∈ (120 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hlist : (120 : ℕ).divisors.filter (fun k => k % 3 = 1) = {1, 4, 10, 40} := by decide
  have hmem : n ∈ (120 : ℕ).divisors.filter (fun k => k % 3 = 1) :=
    Finset.mem_filter.mpr ⟨h120, hm⟩
  rw [hlist] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  tauto

/-! ## Building `Excl120Setup` inside `H` -/




/-- The hypotheses of `Excl120Setup` for `↥H`, transported from `G`. -/
theorem excl120_setup_of {G : Type} [Group G] [Finite G] {U S' H : Subgroup G} {τ : G}
    (hconf : Work.A7REC.ExclHyps U S' τ) (hic : Work.A7REC.InvCent G)
    (hUH : U ≤ H) (hS'H : S' ≤ H) (h120 : Nat.card H = 120) :
    Excl120Setup (U.subgroupOf H) (S'.subgroupOf H) (⟨τ, hS'H hconf.2.2.1⟩ : ↥H) := by
  obtain ⟨hU3, hS8, hτS, hτ2, hτcen, hτN, hdisj⟩ := hconf
  have hτH : τ ∈ H := hS'H hτS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Nat.card ↥H = 120
    exact h120
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]; exact hU3
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'H).toEquiv]; exact hS8
  · exact hτS
  · rw [← Subgroup.orderOf_coe (⟨τ, hτH⟩ : ↥H)]; exact hτ2
  · intro x hx
    apply Subtype.ext
    exact hτcen (x : G) hx
  · have hsub : (U.subgroupOf H).map (MulAut.conj (⟨τ, hτH⟩ : ↥H)).toMonoidHom
        ≤ U.subgroupOf H := by
      rintro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      rw [Subgroup.mem_subgroupOf] at hu
      rw [Subgroup.mem_subgroupOf]
      have hmem : (MulAut.conj τ) (u : G) ∈ U := by
        rw [← hτN]
        exact Subgroup.mem_map.mpr ⟨(u : G), hu, rfl⟩
      rwa [MulAut.conj_apply] at hmem
    have hcard : Nat.card ↥((U.subgroupOf H).map
            (MulAut.conj (⟨τ, hτH⟩ : ↥H)).toMonoidHom)
        = Nat.card ↥(U.subgroupOf H) :=
      (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj (⟨τ, hτH⟩ : ↥H))
        (U.subgroupOf H)).toEquiv).symm
    exact Subgroup.eq_of_le_of_card_ge
      (H := (U.subgroupOf H).map (MulAut.conj (⟨τ, hτH⟩ : ↥H)).toMonoidHom)
      (K := U.subgroupOf H) hsub (le_of_eq hcard.symm)
  · refine le_antisymm ?_ bot_le
    intro z hz
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzS, hzC⟩ := hz
    have hzS' : (z : G) ∈ S' := hzS
    have hzc : ∀ u ∈ U, u * (z : G) = (z : G) * u := by
      intro u hu
      have humem : (⟨u, hUH hu⟩ : ↥H) ∈ U.subgroupOf H := hu
      have h := (Subgroup.mem_centralizer_iff.mp hzC) ⟨u, hUH hu⟩ humem
      exact congrArg (fun y : ↥H => (y : G)) h
    have hmem : (z : G) ∈ S' ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨hzS', Subgroup.mem_centralizer_iff.mpr hzc⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · intro x hx2
    have hx2' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe x]; exact hx2
    exact card_centralizer_subgroupOf_dvd (x : G) x.2 (hic (x : G) hx2').1
  · intro x hx2 A B hA hB hAc hBc
    have hx2' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe x]; exact hx2
    exact uniq_C3_subgroupOf (x : G) x.2 (hic (x : G) hx2').2 A B hA hB hAc hBc

/-! ## 3. The Sylow counting in a group with `Excl120Setup` -/

/-- The index of `N_C(U)` (= the number of Sylow `3`-subgroups) is `1`, `4`, `10` or `40`. -/
theorem excl120_index_mem {C : Type*} [Group C] [Finite C] {U S : Subgroup C} {τ : C}
    (h : Excl120Setup U S τ) :
    (Subgroup.normalizer (U : Set C)).index = 1 ∨
      (Subgroup.normalizer (U : Set C)).index = 4 ∨
      (Subgroup.normalizer (U : Set C)).index = 10 ∨
      (Subgroup.normalizer (U : Set C)).index = 40 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac : (Nat.card C).factorization 3 = 1 := by
    rw [h.card_eq]
    rw [show (120 : ℕ) = 3 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 40)]
  let P : Sylow 3 C := Sylow.ofCard U (by rw [hfac, pow_one]; exact h.card_U)
  have hP : (P : Subgroup C) = U := Sylow.coe_ofCard U _
  have hn3 : Nat.card (Sylow 3 C) = (Subgroup.normalizer (U : Set C)).index := by
    rw [← hP]
    exact Sylow.card_eq_index_normalizer P
  have hdvd : Nat.card (Sylow 3 C) ∣ 120 := by
    rw [hn3, ← h.card_eq]
    exact Subgroup.index_dvd_card _
  have hmod : Nat.card (Sylow 3 C) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 C
  have hcases := sylow3_card_cases hdvd hmod
  rw [← hn3]
  exact hcases

/-! ## 4. The exclusion -/

theorem a7Excl120 : Work.A7REC.A7Excl120Prop := by
  intro G _ _ U S' H τ hconf hic hUH hS'H h120
  have hτH : τ ∈ H := hS'H hconf.2.2.1
  have hset : Excl120Setup (U.subgroupOf H) (S'.subgroupOf H) (⟨τ, hτH⟩ : ↥H) :=
    excl120_setup_of hconf hic hUH hS'H h120
  rcases excl120_index_mem hset with h | h | h | h
  · exact a7Excl120IdxOne hset h
  · exact a7Excl120IdxFour hset h
  · exact a7Excl120IdxTen hset h
  · exact a7Excl120IdxForty hset h


end Work.A7REC.Char
