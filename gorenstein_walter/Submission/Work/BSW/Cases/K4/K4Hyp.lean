import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.K4.Setup
import Submission.Work.BSW.Cases.K4.CardSup

namespace Work.BSW.Cases.K4

open Subgroup Work.GW2

/-- `C_G(u)`, the centralizer of the element `u`. -/
abbrev cent (G : Type*) [Group G] (u : G) : Subgroup G := Subgroup.centralizer ({u} : Set G)

/-- A Klein four-group: an elementary abelian subgroup of order `4`. -/
def IsV4 {G : Type*} [Group G] (V : Subgroup G) : Prop := Nat.card ↥V = 4 ∧ ∀ v ∈ V, v * v = 1

/-- The Bender §3 setting: `G` has involutions, every involution centralizer is dihedral of order
`8` (non-abelian of order `8` containing a four-group), and all involutions are conjugate. -/
def K4Hyp (G : Type*) [Group G] [Finite G] : Prop :=
  (∃ t : G, orderOf t = 2) ∧
  (∀ u : G, orderOf u = 2 → Nat.card ↥(cent G u) = 8) ∧
  (∀ u : G, orderOf u = 2 → ¬ IsMulCommutative ↥(cent G u)) ∧
  (∀ u : G, orderOf u = 2 → ∃ W : Subgroup G, W ≤ cent G u ∧ IsV4 W) ∧
  (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)

variable {G : Type} [Group G] [Finite G]

/-- Conjugation carries centralizers to centralizers: `c C_G(u) c⁻¹ = C_G(c u c⁻¹)`. -/
theorem map_conj_cent (c u : G) :
    (cent G u).map (MulAut.conj c).toMonoidHom = cent G (c * u * c⁻¹) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    change c * y * c⁻¹ ∈ Subgroup.centralizer ({c * u * c⁻¹} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hy']
      _ = (c * u * c⁻¹) * (c * y * c⁻¹) := by group
  · intro hx
    have hx' : x * (c * u * c⁻¹) = (c * u * c⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · change c⁻¹ * x * c ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc c⁻¹ * x * c * u = c⁻¹ * (x * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * x) * c := by rw [hx']
        _ = u * (c⁻¹ * x * c) := by group
    · change c * (c⁻¹ * x * c) * c⁻¹ = x
      group

/-- Non-commutativity is preserved by conjugation: if `c u c⁻¹ = t` and `C_G(t)` is not abelian
then neither is `C_G(u)`. -/
theorem not_isMulCommutative_cent_of_conj (c u t : G) (hcu : c * u * c⁻¹ = t)
    (hnt : ¬ IsMulCommutative ↥(cent G t)) : ¬ IsMulCommutative ↥(cent G u) := by
  rw [isMulCommutative_iff] at hnt ⊢
  push Not at hnt ⊢
  obtain ⟨A, B, hAB⟩ := hnt
  have hu : u = c⁻¹ * t * c := by rw [← hcu]; group
  refine ⟨⟨c⁻¹ * (A : G) * c, ?_⟩, ⟨c⁻¹ * (B : G) * c, ?_⟩, ?_⟩
  · have hAt : (A : G) * t = t * (A : G) := Subgroup.mem_centralizer_singleton_iff.mp A.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c⁻¹ * (A : G) * c) * u
        = (c⁻¹ * (A : G) * c) * (c⁻¹ * t * c) := by rw [hu]
      _ = c⁻¹ * ((A : G) * t) * c := by group
      _ = c⁻¹ * (t * (A : G)) * c := by rw [hAt]
      _ = (c⁻¹ * t * c) * (c⁻¹ * (A : G) * c) := by group
      _ = u * (c⁻¹ * (A : G) * c) := by rw [hu]
  · have hBt : (B : G) * t = t * (B : G) := Subgroup.mem_centralizer_singleton_iff.mp B.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c⁻¹ * (B : G) * c) * u
        = (c⁻¹ * (B : G) * c) * (c⁻¹ * t * c) := by rw [hu]
      _ = c⁻¹ * ((B : G) * t) * c := by group
      _ = c⁻¹ * (t * (B : G)) * c := by rw [hBt]
      _ = (c⁻¹ * t * c) * (c⁻¹ * (B : G) * c) := by group
      _ = u * (c⁻¹ * (B : G) * c) := by rw [hu]
  · intro heq
    apply hAB
    have h2 : (c⁻¹ * (A : G) * c) * (c⁻¹ * (B : G) * c)
        = (c⁻¹ * (B : G) * c) * (c⁻¹ * (A : G) * c) := by
      simpa using congrArg Subtype.val heq
    refine Subtype.ext ?_
    have h4 := congrArg (fun z : G => c * z * c⁻¹) h2
    rwa [show c * ((c⁻¹ * (A : G) * c) * (c⁻¹ * (B : G) * c)) * c⁻¹
          = (A : G) * (B : G) from by group,
         show c * ((c⁻¹ * (B : G) * c) * (c⁻¹ * (A : G) * c)) * c⁻¹
          = (B : G) * (A : G) from by group] at h4

/-- `C_G(t)` is not abelian in the `|K| = 4` case: `K = ⟨k⟩` is cyclic of order `4` and `s` inverts
it, so `s k ≠ k s`. -/
theorem not_isMulCommutative_cent_t {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) :
    ¬ IsMulCommutative ↥(cent G t) := by
  obtain ⟨k, hk4, hkgen, _hkt⟩ := exists_gen_K h hK
  have hkK : k ∈ K := by rw [hkgen]; exact Subgroup.mem_zpowers k
  have hkct : k ∈ cent G t := Work.BSW.K_le_centralizer_t h hkK
  have hsct : s ∈ cent G t := Work.BSW.s_mem_centralizer_t h
  have hinv : s * k * s⁻¹ = k⁻¹ := Work.BSW.inverts_s_K h k hkK
  have hne : k ≠ k⁻¹ := by
    intro hh
    have h2 : k * k = 1 := eq_inv_iff_mul_eq_one.mp hh
    have hd : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rw [hk4] at hd
    omega
  intro hcomm
  have h1 : (⟨k, hkct⟩ : cent G t) * ⟨s, hsct⟩ = ⟨s, hsct⟩ * ⟨k, hkct⟩ :=
    isMulCommutative_iff.mp hcomm _ _
  have h2 : k * s = s * k := by simpa using congrArg Subtype.val h1
  have h3 : s * k * s⁻¹ = k := by rw [← h2]; group
  rw [hinv] at h3
  exact hne h3.symm

/-- `⟨t⟩ ⊔ ⟨s⟩` is a four-group inside `C_G(t)`: the two involutions `t`, `s` commute and are
distinct. -/
theorem fourGroup_in_cent_t {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) : IsV4 (Subgroup.zpowers t ⊔ Subgroup.zpowers s) ∧
    Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ cent G t := by
  have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy z hz
    rcases Work.BSW.mem_zpowers_s h hy with hy1 | hy2
    · rw [hy1]; simpa using hz
    · rw [hy2]
      rcases Work.BSW.mem_zpowers_t h hz with hz1 | hz2
      · rw [hz1]; simp
      · rw [hz2, show s * t * s⁻¹ = t from by rw [Work.BSW.s_mul_t_eq_t_mul_s h]; group]
        exact Subgroup.mem_zpowers t
  have hd : Subgroup.zpowers t ⊓ Subgroup.zpowers s = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hy⟩
    rcases Work.BSW.mem_zpowers_t h hx with rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · rcases Work.BSW.mem_zpowers_s h hy with h1 | h1
      · exact absurd h1 (Work.BSW.t_ne_one h)
      · exact absurd (h1 ▸ Work.BSW.t_mem_K h) (Work.BSW.s_notMem_K h)
  have hle : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ cent G t :=
    sup_le (Subgroup.zpowers_le.mpr (Work.BSW.t_mem_centralizer_t h))
      (Subgroup.zpowers_le.mpr (Work.BSW.s_mem_centralizer_t h))
  have hcard : Nat.card ↥(Subgroup.zpowers t ⊔ Subgroup.zpowers s) = 4 := by
    rw [card_sup_of_le_normalizer_of_inf_eq_bot hsN hd, Nat.card_zpowers, Nat.card_zpowers,
      Work.BSW.orderOf_t h, Work.BSW.orderOf_s h]
  have hsq : ∀ w ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s, w * w = 1 := by
    intro w hw
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers t)
      (Subgroup.zpowers s) hsN
    change w ∈ ((Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) : Set G) at hw
    rw [hcoe] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hw
    rw [show w = a * b from hab.symm]
    rcases Work.BSW.mem_zpowers_t h ha with ha1 | ha2
    · rw [ha1]
      rcases Work.BSW.mem_zpowers_s h hb with hb1 | hb2
      · rw [hb1]; simp
      · rw [hb2]; simp [Work.BSW.s_mul_self h]
    · rw [ha2]
      rcases Work.BSW.mem_zpowers_s h hb with hb1 | hb2
      · rw [hb1]; simp [Work.BSW.t_mul_self h]
      · rw [hb2]
        have hst : s * t = t * s := Work.BSW.s_mul_t_eq_t_mul_s h
        calc (t * s) * (t * s)
            = t * (s * (t * s)) := by group
          _ = t * ((s * t) * s) := by group
          _ = t * ((t * s) * s) := by rw [hst]
          _ = (t * t) * (s * s) := by group
          _ = 1 := by rw [Work.BSW.t_mul_self h, Work.BSW.s_mul_self h, mul_one]
  exact ⟨⟨hcard, hsq⟩, hle⟩

/-- The `|K| = 4` case of `BSWHyps2` satisfies the Bender §3 setting. -/
theorem k4Hyp_of_hyps {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) : K4Hyp G := by
  obtain ⟨hV4, hle⟩ := fourGroup_in_cent_t h
  refine ⟨⟨t, Work.BSW.orderOf_t h⟩, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact card_centralizer_of_orderOf_eq_two h hK hu
  · intro u hu
    obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h u hu)
    exact not_isMulCommutative_cent_of_conj c u t hc (not_isMulCommutative_cent_t h hK)
  · intro u hu
    obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h u hu)
    have hcu : c⁻¹ * t * c = u := by rw [← hc]; group
    refine ⟨(Subgroup.zpowers t ⊔ Subgroup.zpowers s).map (MulAut.conj c⁻¹).toMonoidHom,
      ?_, ?_⟩
    · have hmap := map_conj_cent (G := G) c⁻¹ t
      simp only [inv_inv] at hmap
      rw [hcu] at hmap
      rw [← hmap]
      exact Subgroup.map_mono hle
    · refine ⟨?_, ?_⟩
      · rw [Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
          (MulAut.conj c⁻¹).injective]
        exact hV4.1
      · rintro w hw
        rcases Subgroup.mem_map.mp hw with ⟨y, hy, rfl⟩
        have hy1 : y * y = 1 := hV4.2 y hy
        have hkey : ((MulAut.conj c⁻¹).toMonoidHom y) = c⁻¹ * y * c := by
          show ((MulAut.conj c⁻¹) y) = c⁻¹ * y * c
          rw [MulAut.conj_apply, inv_inv]
        rw [hkey]
        calc c⁻¹ * y * c * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
          _ = 1 := by rw [hy1]; group
  · intro u v hu hv
    exact (Work.BSW.involutions_conj h u hu).trans (Work.BSW.involutions_conj h v hv).symm

end Work.BSW.Cases.K4
