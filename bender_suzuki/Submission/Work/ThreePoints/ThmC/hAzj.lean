/-
# `Work.ThreePoints.ThmC.hAzj` — `ZJ`-invariance helpers for the `hAexists` assembly

Given `hZJ` (Glauberman's `ZJ` theorem) and `Q` a `p`-Sylow of a solvable odd-order subgroup `D`
of `G` with `O_{p'}(D) = ⊥`, the subgroup `ZJ Q` is characteristic in `D`; consequently it is
invariant under `N_G(D)`.
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.app1_2
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem3
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.ZJ_map_of_ker_inf_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- **Characteristic subgroups of `↥D` are invariant under `N_G(D)`.**  If `Z ≤ ↥D` is
characteristic in `↥D` then `e Z e⁻¹ = Z` for every `e ∈ N_G(D)` (viewing `Z` inside `G` via
`D.subtype`). -/
theorem conj_map_subtype_of_characteristic {G : Type} [Group G] [Finite G]
    {D : Subgroup G} {Z : Subgroup ↥D} (hZ : Z.Characteristic) {e : G}
    (he : e ∈ Subgroup.normalizer (D : Set G)) :
    Submission.Blueprint.conj e (Z.map D.subtype) = Z.map D.subtype := by
  have hD : D.map (MulAut.conj e).toMonoidHom = D :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer e D).mpr he
  let φ : ↥D ≃* ↥D :=
    (Subgroup.equivMapOfInjective D (MulAut.conj e).toMonoidHom (MulAut.conj e).injective).trans
      (MulEquiv.subgroupCongr hD)
  have hcomp : D.subtype.comp φ.toMonoidHom = (MulAut.conj e).toMonoidHom.comp D.subtype := by
    ext x
    rfl
  have key : Z.map φ.toMonoidHom = Z := (Subgroup.characteristic_iff_map_eq.mp hZ) φ
  calc Submission.Blueprint.conj e (Z.map D.subtype)
      = (Z.map D.subtype).map (MulAut.conj e).toMonoidHom := rfl
    _ = Z.map ((MulAut.conj e).toMonoidHom.comp D.subtype) := Subgroup.map_map ..
    _ = Z.map (D.subtype.comp φ.toMonoidHom) := by rw [← hcomp]
    _ = (Z.map φ.toMonoidHom).map D.subtype := (Subgroup.map_map ..).symm
    _ = Z.map D.subtype := by rw [key]

/-- Sylow `2`-subgroups of a finite group of odd order are abelian (indeed trivial). -/
theorem isAbelianSubgroup_sylow_two_of_odd {G : Type} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (S : Sylow 2 G) :
    Submission.Blueprint.IsAbelianSubgroup (S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(S : Subgroup G) = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) S.isPGroup'
    have hdvd : Nat.card ↥(S : Subgroup G) ∣ Nat.card G := by
      have h := Subgroup.card_dvd_of_le (le_top : (S : Subgroup G) ≤ ⊤)
      rwa [Subgroup.card_top] at h
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hkne
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hkne
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
    rw [hk0, pow_zero] at hk
    exact hk
  intro x hx y hy
  have hx1 : x = 1 := by
    have h : orderOf (⟨x, hx⟩ : ↥(S : Subgroup G)) ∣ 1 := by
      rw [← hcard]; exact orderOf_dvd_natCard _
    exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h))
  have hy1 : y = 1 := by
    have h : orderOf (⟨y, hy⟩ : ↥(S : Subgroup G)) ∣ 1 := by
      rw [← hcard]; exact orderOf_dvd_natCard _
    exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h))
  rw [hx1, hy1, one_mul]

/-- **`ZJ` of a Sylow of a solvable odd-order `D` with trivial `O_{p'}` is
`N_G(D)`-invariant.** -/
theorem normalizer_le_normalizer_ZJ {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp)
    {D : Subgroup G} {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hodd : Odd (Nat.card ↥D)) {Q : Subgroup G} (hQ : IsSylowOf p Q D)
    (hbot : pPrimeCoreSub p D = ⊥) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (Submission.Blueprint.ZJ Q : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsolv : Group.IsSolvable ↥D := hFT ↥D hodd
  have habel : ∀ S : Sylow 2 ↥D, Submission.Blueprint.IsAbelianSubgroup (S : Subgroup ↥D) :=
    isAbelianSubgroup_sylow_two_of_odd hodd
  obtain ⟨Q₀, hQ₀⟩ := isSylowOf_toSylow hQ
  have hpCore : Submission.Blueprint.pPrimeCore p ↥D = ⊥ := by
    have hmap : (Submission.Blueprint.pPrimeCore p ↥D).map D.subtype = ⊥ := hbot
    refine Subgroup.map_injective D.subtype_injective ?_
    rw [hmap, Subgroup.map_bot]
  have hchar : (Submission.Blueprint.ZJ (Q₀ : Subgroup ↥D)).Characteristic := by
    have h := hZJ ↥D p hp hpodd hsolv habel Q₀
    rwa [hpCore, bot_sup_eq] at h
  have hZJmap : Submission.Blueprint.ZJ Q =
      (Submission.Blueprint.ZJ (Q₀ : Subgroup ↥D)).map D.subtype := by
    rw [Work.GlaubermanZJ.ZJ_eq Q, Work.GlaubermanZJ.ZJ_eq (Q₀ : Subgroup ↥D)]
    have hker : (Q₀ : Subgroup ↥D) ⊓ D.subtype.ker = ⊥ := by
      rw [show D.subtype.ker = ⊥ from
        (MonoidHom.ker_eq_bot_iff D.subtype).mpr D.subtype_injective, inf_bot_eq]
    have h := Work.PGroup.ZJ_map_of_ker_inf_eq_bot D.subtype (Q₀ : Subgroup ↥D) hker
    rw [show (Q₀ : Subgroup ↥D).map D.subtype = Q from by
      rw [hQ₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ.1]] at h
    exact h
  intro e he
  rw [hZJmap]
  exact (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer e
    (Submission.Blueprint.ZJ (Q₀ : Subgroup ↥D) |>.map D.subtype)).mp
      (conj_map_subtype_of_characteristic hchar he)

/-- `O_{p'}(X) ≤ X`. -/
theorem pPrimeCoreSub_le {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    pPrimeCoreSub p X ≤ X := Subgroup.map_subtype_le _

/-- Elements normalising `D` normalise `O_{p'}(D)` (which is characteristic in `D`). -/
theorem pPrimeCoreSub_mem_normalizer_of_mem_normalizer {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {D : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (D : Set G)) :
    e ∈ Subgroup.normalizer (pPrimeCoreSub p D : Set G) := by
  refine (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer e (pPrimeCoreSub p D)).mp ?_
  rw [← pPrimeCoreSub_conj p hp D e,
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer e D).mpr he]

/-- `D` normalises `O_{p'}(D)`. -/
theorem pPrimeCoreSub_le_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (X : Subgroup G) : X ≤ Subgroup.normalizer (pPrimeCoreSub p X : Set G) := by
  intro x hx
  exact pPrimeCoreSub_mem_normalizer_of_mem_normalizer hp
    ((Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer x X).mp
      (Work.ThreePoints.conj_eq_self_of_mem hx))

/-- A nontrivial finite `p`-group has order divisible by `p`. -/
theorem prime_dvd_card_of_isPGroup_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hPp : IsPGroup p P) (hP : P ≠ ⊥) : p ∣ Nat.card ↥P := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥P)
  exact (hPp.dvd_orderOf hg).trans (orderOf_dvd_natCard g)

/-- A `p`-Sylow of `D` is nontrivial as soon as `p ∣ |D|`. -/
theorem sylow_ne_bot_of_dvd {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {D Q : Subgroup G} (hQ : IsSylowOf p Q D) (hdvd : p ∣ Nat.card ↥D) : Q ≠ ⊥ := by
  intro hQbot
  have hindex : ¬ p ∣ (Q.subgroupOf D).index := not_dvd_index_of_isSylowOf hp hQ
  apply hindex
  have hmul : Nat.card ↥D = Nat.card ↥Q * (Q.subgroupOf D).index := by
    rw [← Subgroup.card_mul_index (Q.subgroupOf D),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.1).toEquiv]
  have hQ1 : Nat.card ↥Q = 1 := by
    rw [hQbot]; exact Subgroup.card_bot
  rw [hmul, hQ1, one_mul] at hdvd
  exact hdvd

end Work.ThreePoints.ThmC