import Mathlib
import Submission.Work.DoubleTransitivity.Sec2.inv_class
import Submission.Work.DoubleTransitivity.Sec1.restrict
import Submission.Work.ThmF.Setup
import Submission.Work.Reductions.stronglyEmbedded_subgroupOf
import Submission.Work.Reductions.stronglyEmbedded_involutions_conj
import Submission.Work.Hering.Step4.count_order_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|C_G(x)|` is odd for `x` conjugate to `u * t`

Peterfalvi II, Chapter V §2, Lemma 4 (p. 246): a strongly real element `x` with `x² ≠ 1` of a
group `G` in situation (B0)–(B2) is conjugate to `u * t` for an involution `u ∈ H`, and its
centraliser has odd order.

Here we prove the group-theoretic core, which needs only `IsStronglyEmbedded`:

* If `H` is strongly embedded in the finite group `G`, `u ∈ H` and `t ∉ H` are involutions and
  `(u * t)² ≠ 1`, then **no involution commutes with `u * t`**.

The argument is Bender's.  Put `c = u * t` and `N = N_G(⟨c⟩)`, so that `u`, `t` (both invert
`c`) and any involution `s` commuting with `c` lie in `N`.  Since `u ∈ H ⊓ N`, the intersection
`H ⊓ N` has even order and is proper in `N` (it misses `t`), so by
`Work.Reductions.stronglyEmbedded_subgroupOf` it is strongly embedded in `N`; hence all
involutions of `N` are conjugate in `N` (`Work.Reductions.stronglyEmbedded_involutions_conj`).
So `s = n u n⁻¹` for some `n ∈ N`; as `n` normalises `⟨c⟩`, the element `n c n⁻¹` is a power of
`c`, hence is fixed by `s`, and `u = n⁻¹ s n` commutes with `c`.  But `u c u⁻¹ = c⁻¹`, so
`c = c⁻¹`, i.e. `c² = 1`, contradicting `(u * t)² ≠ 1`.

The target statement then follows by transporting along the conjugacy `x = g⁻¹ (u * t) g`.
-/

set_option autoImplicit false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint

/-- Conjugation by an element sending `c` into `⟨c⟩` preserves `⟨c⟩`. -/
private lemma conj_mem_zpowers_of_mem {G : Type*} [Group G] {g c : G}
    (hc : g * c * g⁻¹ ∈ Subgroup.zpowers c) {y : G} (hy : y ∈ Subgroup.zpowers c) :
    g * y * g⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h : g * c ^ k * g⁻¹ = (g * c * g⁻¹) ^ k := by
    have hh := map_zpow (MulAut.conj g).toMonoidHom c k
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hh
  rw [h]
  exact Subgroup.zpow_mem _ hc k

/-- An involution `g` with `g c g⁻¹ ∈ ⟨c⟩` normalises `⟨c⟩`. -/
private lemma mem_normalizer_zpowers_of_involution {G : Type*} [Group G] {g c : G}
    (hg : g * g = 1) (hc : g * c * g⁻¹ ∈ Subgroup.zpowers c) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers c) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn; exact conj_mem_zpowers_of_mem hc hn
  · intro hn
    have hgg : g * (g * n * g⁻¹) * g⁻¹ = n := by
      calc g * (g * n * g⁻¹) * g⁻¹ = (g * g) * n * (g⁻¹ * g⁻¹) := by group
        _ = n := by
          have hgg2 : g⁻¹ * g⁻¹ = 1 := by rw [inv_eq_of_mul_eq_one_right hg, hg]
          rw [hg, hgg2, one_mul, mul_one]
    rw [← hgg]
    exact conj_mem_zpowers_of_mem hc hn

/-- **Peterfalvi I, Ch. I §2 Prop. 1 (a) and II, Ch. V §2 Lemma 4 (core).**  With `H` strongly
embedded, `u ∈ H` and `t ∉ H` involutions and `(u * t)² ≠ 1`, no involution of `G` commutes
with `u * t`. -/
private lemma no_involution_comm_mul {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {u t : G} (huH : u ∈ H) (hu2 : orderOf u = 2)
    (ht2 : orderOf t = 2) (htH : t ∉ H) (h2 : u * t * (u * t) ≠ 1) :
    ∀ s : G, orderOf s = 2 → s * (u * t) ≠ (u * t) * s := by
  intro s hs2 hcomm
  set c : G := u * t with hc_def
  have hu_mul : u * u = 1 := by
    have h := pow_orderOf_eq_one u; rw [hu2] at h; simpa [pow_two] using h
  have ht_mul : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht2] at h; simpa [pow_two] using h
  have hs_mul : s * s = 1 := by
    have h := pow_orderOf_eq_one s; rw [hs2] at h; simpa [pow_two] using h
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu_mul
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_mul
  have hc_inv : c⁻¹ = t * u := by rw [hc_def, mul_inv_rev, hu_inv, ht_inv]
  -- `u` and `t` both invert `c`
  have hucu : u * c * u⁻¹ = c⁻¹ := by
    rw [hc_def, hc_inv, hu_inv]
    calc u * (u * t) * u = (u * u) * (t * u) := by group
      _ = t * u := by rw [hu_mul, one_mul]
  have htct : t * c * t⁻¹ = c⁻¹ := by
    rw [hc_def, hc_inv, ht_inv]
    calc t * (u * t) * t = t * u * (t * t) := by group
      _ = t * u := by rw [ht_mul, mul_one]
  have hcommc : s * c = c * s := by rw [hc_def]; exact hcomm
  have hscs : s * c * s⁻¹ = c := by rw [hcommc]; group
  -- `N = N_G(⟨c⟩)` contains `u`, `t`, `s`
  let N : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c)
  have huN : u ∈ N := by
    change u ∈ Subgroup.normalizer (Subgroup.zpowers c)
    exact mem_normalizer_zpowers_of_involution hu_mul
      (by rw [hucu]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  have htN : t ∈ N := by
    change t ∈ Subgroup.normalizer (Subgroup.zpowers c)
    exact mem_normalizer_zpowers_of_involution ht_mul
      (by rw [htct]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  have hsN : s ∈ N := by
    change s ∈ Subgroup.normalizer (Subgroup.zpowers c)
    exact mem_normalizer_zpowers_of_involution hs_mul
      (by rw [hscs]; exact Subgroup.mem_zpowers c)
  -- `H ⊓ N` is strongly embedded in `N`
  have huHN : u ∈ H ⊓ N := ⟨huH, huN⟩
  have heven : Even (Nat.card ↥(H ⊓ N)) := by
    refine even_iff_two_dvd.mpr ?_
    have hd := Subgroup.orderOf_dvd_natCard (H ⊓ N) huHN
    rwa [hu2] at hd
  have hne : H ⊓ N ≠ N := by
    intro hEq
    have ht_in : t ∈ H ⊓ N := by rw [hEq]; exact htN
    exact htH ht_in.1
  have hstrong : IsStronglyEmbedded ((H ⊓ N).subgroupOf N) :=
    Work.Reductions.stronglyEmbedded_subgroupOf hH hne heven
  have hu2' : orderOf (⟨u, huN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hs2' : orderOf (⟨s, hsN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  -- hence `u` and `s` are conjugate in `N`
  obtain ⟨n, hn⟩ := Work.Reductions.stronglyEmbedded_involutions_conj (G := ↥N) hstrong
    (u := ⟨u, huN⟩) (v := ⟨s, hsN⟩) hu2' hs2'
  have hnval : (n : G) * u * (n : G)⁻¹ = s := by
    simpa using congrArg (fun z : ↥N => (z : G)) hn
  have hnc' : (n : G) * c * (n : G)⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp n.2 c).mp (Subgroup.mem_zpowers c)
  have hu_eq : u = (n : G)⁻¹ * s * (n : G) := by rw [← hnval]; group
  -- `s` fixes every element of `⟨c⟩`
  have hsc_comm : ∀ y ∈ Subgroup.zpowers c, s * y * s⁻¹ = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : s * c ^ k * s⁻¹ = (s * c * s⁻¹) ^ k := by
      have hh := map_zpow (MulAut.conj s).toMonoidHom c k
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hh
    rw [h1, hscs]
  -- consequently `u` also commutes with `c`
  have hcomm_uc : u * c * u⁻¹ = c := by
    rw [hu_eq]
    have hstep : ((n : G)⁻¹ * s * (n : G)) * c * ((n : G)⁻¹ * s * (n : G))⁻¹
        = (n : G)⁻¹ * (s * ((n : G) * c * (n : G)⁻¹) * s⁻¹) * (n : G) := by group
    rw [hstep, hsc_comm _ hnc']
    group
  -- contradicting `u c u⁻¹ = c⁻¹` together with `c² ≠ 1`
  have h1 : c = c⁻¹ := hcomm_uc.symm.trans hucu
  have hcc : c * c = 1 := by
    nth_rewrite 2 [h1]
    exact mul_inv_cancel c
  exact h2 (hc_def ▸ hcc)

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem odd_card_centralizer_of_conj_ut {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H) {x u : G} (hu : u ∈ involutions (H : Set G)) (hx2 : x * x ≠ 1) (hconj : ∃ g : G, g * x * g⁻¹ = u * t) : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  obtain ⟨huH, hu2⟩ := hu
  obtain ⟨g, hg⟩ := hconj
  -- `x = g⁻¹ (u t) g` and `(u t)² ≠ 1`
  have hx_eq : x = g⁻¹ * (u * t) * g := by rw [← hg]; group
  have h2 : u * t * (u * t) ≠ 1 := by
    intro h1
    apply hx2
    rw [hx_eq]
    rw [show (g⁻¹ * (u * t) * g) * (g⁻¹ * (u * t) * g)
        = g⁻¹ * (u * t * (u * t)) * g from by group, h1]
    group
  -- no involution commutes with `u * t`; transport along conjugacy
  have hnoinv : ∀ s : G, orderOf s = 2 → s * (u * t) ≠ (u * t) * s :=
    no_involution_comm_mul hH huH hu2 ht htH h2
  have hnoinv_x : ∀ s : G, orderOf s = 2 → s * x ≠ x * s := by
    intro s hs2 hcomm
    have hs'2 : orderOf (g * s * g⁻¹) = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj g) s
      rw [MulAut.conj_apply] at h
      rw [h, hs2]
    have hconjcomm : (g * s * g⁻¹) * (u * t) = (u * t) * (g * s * g⁻¹) := by
      rw [← hg]
      calc (g * s * g⁻¹) * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
        _ = g * (x * s) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * (g * s * g⁻¹) := by group
    exact hnoinv (g * s * g⁻¹) hs'2 hconjcomm
  exact Work.Hering.Step4.odd_card_centralizer hnoinv_x

end Work.ThmF.ChV12
