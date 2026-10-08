import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.IsoDihedralFourOfCardEight
import Submission.Work.CORE3.nat_card_involutions_dihedral_four
import Submission.Work.CORE3.Case1bSetup

/-!
# `I_{VU}(y) = 1` for `y ∉ Ĥ`, restricted to `U`

Bender 1981, §3, p. 223, (5): an involution `y ∉ Ĥ` inverts no nontrivial element of `U = O(Ĥ)`.
This file proves the CORE3 leaf `Work.CORE3.CosetFourUCase` (the `U^#` part of
`Work.GW2.Case1bFiveProp`), used by `Work.CORE3.CosetPairCountFour`.

Bender's sketch: `V = O₂(Ĥ) = S ⊓ C_G(U)` is a four-group with `N_G(V) = Ĥ`
(`NormalizerPcoreEqHhat`) and `V ≤ C_G(U) ⊓ C_G(x)`; Bender's Sylow argument
(`C4UNormalizerConj`) produces an element `z ∈ Ĥ` inverting `x`; taking the `2`-part of `z`
(`C4UTwoPartPow`) gives a `2`-element `s ∈ ⟨z⟩ ⊆ Ĥ` inverting `x`; if `s` is an involution it
already lies in `Ĥ − V`, so `x ∈ I_U(s) = D.K ≤ F(U)`; otherwise `T := V ⊔ ⟨s⟩` is a
`2`-subgroup of `G` of order `8`, hence (`IsoDihedralFourOfCardEight`) `T ≃* DihedralGroup 4`,
and the explicit `DihedralGroup 4` computation `c4u_coset_involution` produces an involution
`s * w ∈ Ĥ − V` inverting `x`. In both cases `x ∈ D.K ≤ F(U)`, so `N_G(⟨x⟩) ≤ Ĥ` (`h1.2`)
while `y ∈ N_G(⟨x⟩)` — contradicting `y ∉ Ĥ`.
-/

namespace Work.CORE3

open Work.GW2

open Subgroup

/-! ## 1. Odd powers of an inverting element -/

/-- If `h` inverts `x`, then so does every odd power of `h`. -/
private lemma c4u_pow_odd_conj_eq_inv {G : Type*} [Group G] {h x : G}
    (hh : h * x * h⁻¹ = x⁻¹) {m : ℕ} (hm : Odd m) : h ^ m * x * (h ^ m)⁻¹ = x⁻¹ := by
  obtain ⟨t, rfl⟩ := hm
  have h2 : h ^ 2 * x * (h ^ 2)⁻¹ = x := by
    have e : h ^ 2 * x * (h ^ 2)⁻¹ = h * (h * x * h⁻¹) * h⁻¹ := by
      rw [pow_two]; group
    rw [e, hh]
    have e2 : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e2, hh, inv_inv]
  have heven : ∀ s : ℕ, (h ^ 2) ^ s * x * ((h ^ 2) ^ s)⁻¹ = x := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have e : (h ^ 2) ^ (s + 1) * x * ((h ^ 2) ^ (s + 1))⁻¹
          = (h ^ 2) ^ s * (h ^ 2 * x * (h ^ 2)⁻¹) * ((h ^ 2) ^ s)⁻¹ := by
        rw [pow_succ]; group
      rw [e, h2, ih]
  have hsplit : h ^ (2 * t + 1) = (h ^ 2) ^ t * h := by rw [pow_succ, pow_mul]
  rw [hsplit]
  have e : ((h ^ 2) ^ t * h) * x * ((h ^ 2) ^ t * h)⁻¹
      = (h ^ 2) ^ t * (h * x * h⁻¹) * ((h ^ 2) ^ t)⁻¹ := by group
  rw [e, hh]
  have e2 : (h ^ 2) ^ t * x⁻¹ * ((h ^ 2) ^ t)⁻¹
      = ((h ^ 2) ^ t * x * ((h ^ 2) ^ t)⁻¹)⁻¹ := by group
  rw [e2, heven t]

/-! ## 2. The `2`-part of an inverting element -/

/-- If an element `h` inverts an element `x` of odd order, then some power of `h` that generates
a `2`-subgroup already inverts `x`. -/
theorem C4UTwoPartPow {G : Type} [Group G] [Finite G] {x h : G}
    (hx : Odd (orderOf x)) (hh : h * x * h⁻¹ = x⁻¹) :
    ∃ s ∈ Subgroup.zpowers h, IsPGroup 2 (Subgroup.zpowers s) ∧ s * x * s⁻¹ = x⁻¹ := by
  classical
  obtain ⟨k, m, hm_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  have hdvd : Nat.card ↥(Subgroup.zpowers (h ^ m)) ∣ 2 ^ k := by
    rw [Nat.card_zpowers]
    refine orderOf_dvd_iff_pow_eq_one.mpr ?_
    rw [← pow_mul, mul_comm m (2 ^ k), ← hm_eq, pow_orderOf_eq_one]
  exact ⟨h ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers h) m, IsPGroup.of_card_dvd_pow hdvd,
    c4u_pow_odd_conj_eq_inv hh hm_odd⟩

/-! ## 3. An involution in the coset of a four-group in `DihedralGroup 4` -/

/-- In `DihedralGroup 4`, the elements of order `4` are `r 1` and `r 3`. -/
private lemma c4u_d4_orderOf_eq_four {x : DihedralGroup 4} (hx : orderOf x = 4) :
    x = DihedralGroup.r 1 ∨ x = DihedralGroup.r 3 := by
  rcases x with i | i
  · have hg : Nat.gcd 4 i.val = 1 := by
      have h4 : 4 / Nat.gcd 4 i.val = 4 := by
        have h := DihedralGroup.orderOf_r (n := 4) i
        rw [h] at hx
        exact hx
      have hdvd : Nat.gcd 4 i.val ∣ 4 := Nat.gcd_dvd_left 4 i.val
      have hmul := Nat.div_mul_cancel hdvd
      rw [h4] at hmul
      omega
    have hlt : i.val < 4 := ZMod.val_lt i
    have hnot : ¬ (2 ∣ i.val) := by
      intro hd
      have h2 : 2 ∣ Nat.gcd 4 i.val := Nat.dvd_gcd (by norm_num) hd
      rw [hg] at h2
      omega
    have hval : i.val = 1 ∨ i.val = 3 := by
      have hmod : i.val % 2 = 1 := by
        have h0 : i.val % 2 ≠ 0 := fun h0 => hnot (Nat.dvd_of_mod_eq_zero h0)
        omega
      omega
    rcases hval with h1 | h1
    · left; rw [← ZMod.natCast_zmod_val i, h1]; norm_num
    · right; rw [← ZMod.natCast_zmod_val i, h1]; norm_num
  · rw [DihedralGroup.orderOf_sr] at hx
    omega

/-- A subgroup of `DihedralGroup 4` of order `4` all of whose elements square to `1` contains a
reflection `sr i`. -/
private lemma c4u_d4_exists_sr_mem {V : Subgroup (DihedralGroup 4)}
    (hcard : Nat.card ↥V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ i : ZMod 4, DihedralGroup.sr i ∈ V := by
  by_contra h
  simp only [not_exists] at h
  have hmem : ∀ v ∈ V, v = 1 ∨ v = DihedralGroup.r 2 := by
    intro v hv
    rcases v with i | i
    · by_cases h1 : DihedralGroup.r i = 1
      · exact Or.inl h1
      · right
        have h2 : orderOf (DihedralGroup.r i) = 2 := by
          have hdv : orderOf (DihedralGroup.r i) ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hsq _ hv)
          rcases (Nat.dvd_prime Nat.prime_two).mp hdv with hh | hh
          · exact absurd (orderOf_eq_one_iff.mp hh) h1
          · exact hh
        rw [Work.CORE3.r_eq_two_of_orderOf_eq_two h2]
    · exact absurd hv (h i)
  have hle : V ≤ Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 4) := by
    intro v hv
    rcases hmem v hv with h1 | h2
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h2]; exact Subgroup.mem_zpowers _
  have hcard2 : Nat.card ↥(Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 4)) = 2 := by
    rw [Nat.card_zpowers, Work.CORE3.orderOf_r_two]
  have hle2 : Nat.card ↥V
      ≤ Nat.card ↥(Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 4)) := by
    have h := Subgroup.card_le_card_group
      (V.subgroupOf (Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 4)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  omega

/-- **Coset involution.** Let `V ≤ T` be a four-group of a group `T` with a fixed isomorphism
`T ≃* DihedralGroup 4`, and let `s ∈ T \ V` have order `4`. Then the coset `s·V` contains an
involution. -/
private lemma c4u_coset_involution {G : Type} [Group G] (T V : Subgroup G)
    (hVT : V ≤ T) (hVcard : Nat.card ↥V = 4) (hVsq : ∀ v ∈ V, v ^ 2 = 1)
    (hTcard : Nat.card ↥T = 8) (e : ↥T ≃* DihedralGroup 4) {s : G} (hsT : s ∈ T)
    (hsV : s ∉ V) (hord : orderOf s = 4) :
    ∃ w ∈ V, (s * w) * (s * w) = 1 := by
  classical
  set V' : Subgroup ↥T := V.subgroupOf T with hV'def
  have hV'card : Nat.card ↥V' = 4 := by
    rw [hV'def]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv).trans hVcard
  have hV'sq : ∀ v ∈ V', v ^ 2 = 1 := by
    intro v hv
    have hvG : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    exact Subtype.ext (by simpa using hVsq (v : G) hvG)
  have hsT' : (⟨s, hsT⟩ : ↥T) ∉ V' := fun hv => hsV (Subgroup.mem_subgroupOf.mp hv)
  have hord' : orderOf (⟨s, hsT⟩ : ↥T) = 4 := by
    rw [Subgroup.orderOf_mk]; exact hord
  -- work in `DihedralGroup 4`
  set W : Subgroup (DihedralGroup 4) := V'.map (e : ↥T →* DihedralGroup 4) with hWdef
  have hWcard : Nat.card ↥W = 4 := by
    rw [hWdef, Subgroup.card_map_of_injective (K := V')
      (f := (e : ↥T →* DihedralGroup 4)) (MulEquiv.injective e), hV'card]
  have hWsq : ∀ v ∈ W, v ^ 2 = 1 := by
    intro v hv
    rw [hWdef] at hv
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_pow, hV'sq y hy, map_one]
  obtain ⟨i, hi⟩ := c4u_d4_exists_sr_mem hWcard hWsq
  have hesord : orderOf (e (⟨s, hsT⟩ : ↥T)) = 4 := by
    rw [MulEquiv.orderOf_eq]; exact hord'
  have hw : e (⟨s, hsT⟩ : ↥T) * DihedralGroup.sr i
      * (e (⟨s, hsT⟩ : ↥T) * DihedralGroup.sr i) = 1 := by
    rcases c4u_d4_orderOf_eq_four hesord with h1 | h1
    · rw [h1, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
      simp
    · rw [h1, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
      simp
  -- transport back to `T` and then to `G`
  refine ⟨((e.symm (DihedralGroup.sr i) : ↥T) : G), ?_, ?_⟩
  · obtain ⟨y, hy, hyi⟩ := Subgroup.mem_map.mp hi
    have hys : e.symm (DihedralGroup.sr i) = y := by
      rw [← hyi]
      exact MulEquiv.symm_apply_apply e y
    rw [hys]
    exact Subgroup.mem_subgroupOf.mp hy
  · have hmap : e (((⟨s, hsT⟩ : ↥T) * e.symm (DihedralGroup.sr i))
        * ((⟨s, hsT⟩ : ↥T) * e.symm (DihedralGroup.sr i)))
        = (e (⟨s, hsT⟩ : ↥T) * DihedralGroup.sr i)
          * (e (⟨s, hsT⟩ : ↥T) * DihedralGroup.sr i) := by
      simp only [map_mul, MulEquiv.apply_symm_apply]
    have hw' : ((⟨s, hsT⟩ : ↥T) * e.symm (DihedralGroup.sr i))
        * ((⟨s, hsT⟩ : ↥T) * e.symm (DihedralGroup.sr i)) = 1 := by
      refine e.injective ?_
      rw [hmap, map_one]
      exact hw
    have := congrArg (fun t : ↥T => (t : G)) hw'
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-! ## 4. Bender's Sylow argument: an element of `N_G(V)` inverting `x` -/

/-- **Bender 1981, §3 p. 223.** Let `V ≤ G` be a four-group with `N_G(V) = H`, let every
`2`-subgroup of `G` have order at most `8`, and let `y ∉ H` be an involution inverting `x`
(with `V ≤ C_G(x)`, `x ≠ 1` of odd order). Then some element of `H` inverts `x`. -/
theorem C4UNormalizerConj {G : Type} [Group G] [Finite G]
    (V H : Subgroup G) (hV : Work.GW2.IsFourGroup V)
    (hNV : Subgroup.normalizer (V : Set G) = H)
    (h2 : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card P ≤ 8)
    {x y : G} (hxV : V ≤ Subgroup.centralizer ({x} : Set G)) (hy2 : orderOf y = 2)
    (hyx : y * x * y⁻¹ = x⁻¹) (hyH : y ∉ H) (hx1 : x ≠ 1) (hxodd : Odd (orderOf x)) :
    ∃ z ∈ H, z * x * z⁻¹ = x⁻¹ := by
  classical
  set A : Subgroup G := Subgroup.centralizer ({x} : Set G) with hAdef
  have hxne : x ≠ x⁻¹ := by
    intro h
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp h
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
    · exact hx1 (orderOf_eq_one_iff.mp hh)
    · obtain ⟨k, hk⟩ := hxodd; omega
  have hyA : y ∉ A := by
    intro hy
    have hc : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hy) x (by simp)
    refine hxne ?_
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = y⁻¹ * x⁻¹ * y := by rw [hyx]
      _ = x⁻¹ := by
            have h2 : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by
              have := congrArg Inv.inv hc
              rwa [mul_inv_rev, mul_inv_rev] at this
            rw [h2]; group
  -- `y` is an involution
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2] at h
    simpa [pow_two] using h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyx' : y * x * y = x⁻¹ := by
    have h := hyx
    rwa [hyinv] at h
  -- the commutation identities used below
  have hA1 : y * x = x⁻¹ * y := by
    calc y * x = ((y * x) * y) * y := by rw [mul_assoc, hyy, mul_one]
      _ = x⁻¹ * y := by rw [hyx']
  have hA2 : x * y = y * x⁻¹ := by
    calc x * y = y * (y * x * y) := by rw [← mul_assoc, ← mul_assoc, hyy, one_mul]
      _ = y * x⁻¹ := by rw [hyx']
  have hA3 : y⁻¹ * x = x⁻¹ * y⁻¹ := by rw [hyinv]; exact hA1
  have hA4 : x * y⁻¹ = y⁻¹ * x⁻¹ := by rw [hyinv]; exact hA2
  have hconjA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro a ha
    have ha' : x * a = a * x := (Subgroup.mem_centralizer_iff.mp ha) x (by simp)
    have h1 : x⁻¹ * a = a * x⁻¹ := by
      have := congrArg (fun t => x⁻¹ * t * x⁻¹) ha'
      simpa [mul_assoc] using this.symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc x * (y * a * y⁻¹) = (x * y) * a * y⁻¹ := by group
      _ = (y * x⁻¹) * a * y⁻¹ := by rw [hA2]
      _ = y * (x⁻¹ * a) * y⁻¹ := by group
      _ = y * (a * x⁻¹) * y⁻¹ := by rw [h1]
      _ = (y * a) * (x⁻¹ * y⁻¹) := by group
      _ = (y * a) * (y⁻¹ * x) := by rw [← hA3]
      _ = (y * a * y⁻¹) * x := by group
  have hconjAinv : ∀ a ∈ A, y⁻¹ * a * y ∈ A := by
    intro a ha
    have ha' : x * a = a * x := (Subgroup.mem_centralizer_iff.mp ha) x (by simp)
    have h1 : x⁻¹ * a = a * x⁻¹ := by
      have := congrArg (fun t => x⁻¹ * t * x⁻¹) ha'
      simpa [mul_assoc] using this.symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc x * (y⁻¹ * a * y) = (x * y⁻¹) * a * y := by group
      _ = (y⁻¹ * x⁻¹) * a * y := by rw [hA4]
      _ = y⁻¹ * (x⁻¹ * a) * y := by group
      _ = y⁻¹ * (a * x⁻¹) * y := by rw [h1]
      _ = (y⁻¹ * a) * (x⁻¹ * y) := by group
      _ = (y⁻¹ * a) * (y * x) := by rw [← hA1]
      _ = (y⁻¹ * a * y) * x := by group
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha; simpa using hconjA a ha
    · intro ha
      have := hconjAinv (y * a * y⁻¹) ha
      simpa [mul_assoc] using this
  -- ### Bender's Sylow argument
  have hmemN : ∀ a : G, a ∈ A ↔ y * a * y⁻¹ ∈ A :=
    Subgroup.mem_normalizer_iff.mp hyN
  have hmemNinv : ∀ a : G, a ∈ A ↔ y⁻¹ * a * y ∈ A := by
    have h := Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem (Subgroup.normalizer (A : Set G)) hyN)
    simpa [inv_inv] using h
  -- the automorphism of `A` induced by conjugation with `y`
  let σ : ↥A ≃* ↥A :=
    { toFun := fun a => ⟨y * (a : G) * y⁻¹, (hmemN (a : G)).mp a.2⟩
      invFun := fun a => ⟨y⁻¹ * (a : G) * y, (hmemNinv (a : G)).mp a.2⟩
      left_inv := fun a => Subtype.ext (by
        show y⁻¹ * (y * (a : G) * y⁻¹) * y = (a : G); group)
      right_inv := fun a => Subtype.ext (by
        show y * (y⁻¹ * (a : G) * y) * y⁻¹ = (a : G); group)
      map_mul' := fun a b => Subtype.ext (by
        show y * ((a : G) * (b : G)) * y⁻¹
          = (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹)
        group) }
  -- a Sylow `2`-subgroup `W` of `A` containing `V`
  have hV2 : IsPGroup 2 ↥(V.subgroupOf A) :=
    ((IsPGroup.of_card (p := 2) (n := 2) (by rw [hV.1]; norm_num)) :
      IsPGroup 2 ↥V).of_equiv (Subgroup.subgroupOfEquivOfLe hxV).symm
  obtain ⟨W, hVW⟩ := IsPGroup.exists_le_sylow hV2
  set W₁ : Subgroup G := (W : Subgroup ↥A).map A.subtype with hW₁def
  have hW₁card : Nat.card ↥W₁ = Nat.card ↥(W : Subgroup ↥A) := by
    rw [hW₁def]
    exact Subgroup.card_map_of_injective (f := A.subtype) Subtype.coe_injective
  have hVleW₁ : V ≤ W₁ := by
    intro v hv
    rw [hW₁def]
    exact Subgroup.mem_map.mpr
      ⟨⟨v, hxV hv⟩, hVW (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  have hW₁2 : IsPGroup 2 W₁ := by
    rw [hW₁def]
    exact IsPGroup.map (IsPGroup.of_card (Sylow.card_eq_multiplicity W)) A.subtype
  have hW₁le : Nat.card ↥W₁ ≤ 8 := h2 W₁ hW₁2
  have hW₁ge : 4 ≤ Nat.card ↥W₁ := by
    have h1 : Nat.card ↥(V.subgroupOf A) ≤ Nat.card ↥(W : Subgroup ↥A) := by
      have h2' := Subgroup.card_le_card_group
        ((V.subgroupOf A).subgroupOf (W : Subgroup ↥A))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv] at h2'
    have h3 : Nat.card ↥(V.subgroupOf A) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxV).toEquiv).trans hV.1
    rw [hW₁card]
    omega
  -- Sylow conjugacy inside `A`: `W` and its image under `σ` are `A`-conjugate
  have hcardσ : Nat.card ↥((W : Subgroup ↥A).map (σ : ↥A →* ↥A)) = 2 ^ (Nat.card ↥A).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective σ), Sylow.card_eq_multiplicity W]
  let W₂ : Sylow 2 ↥A := Sylow.ofCard ((W : Subgroup ↥A).map (σ : ↥A →* ↥A)) hcardσ
  obtain ⟨κ, hκ⟩ : ∃ κ : ↥A, κ • W = W₂ :=
    MulAction.IsPretransitive.exists_smul_eq W W₂
  have hκ' : (W : Subgroup ↥A).map (MulAut.conj κ).toMonoidHom = (W : Subgroup ↥A).map (σ : ↥A →* ↥A) := by
    have h := congrArg (fun S : Sylow 2 ↥A => (S : Subgroup ↥A)) hκ
    rw [Sylow.coe_subgroup_smul, Work.CORE2A.smul_conj_eq_map, Sylow.coe_ofCard] at h
    exact h
  -- transport to `G`
  have hfunκ : (MulAut.conj (κ : G)).toMonoidHom.comp A.subtype
      = A.subtype.comp (MulAut.conj κ).toMonoidHom := by
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MulAut.conj_apply]
    rfl
  have hfuny : (MulAut.conj y).toMonoidHom.comp A.subtype
      = A.subtype.comp σ := by
    ext a
    exact (MulAut.conj_apply y (a : G)).trans rfl
  have hkey : W₁.map (MulAut.conj (κ : G)).toMonoidHom
      = W₁.map (MulAut.conj y).toMonoidHom := by
    have h := congrArg (fun S : Subgroup ↥A => S.map A.subtype) hκ'
    rw [Subgroup.map_map, Subgroup.map_map, ← hfunκ, ← hfuny] at h
    rw [Subgroup.map_map, Subgroup.map_map]
    exact h
  -- membership description of the conjugated subgroups
  have conj_mem_iff : ∀ (t g : G),
      g ∈ W₁.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * g * t ∈ W₁ := by
    intro t g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwg⟩
      have : t⁻¹ * g * t = w := by
        rw [← hwg, MulEquiv.toMonoidHom_eq_coe]
        show t⁻¹ * ((MulAut.conj t) w) * t = w
        rw [MulAut.conj_apply]
        group
      rwa [this]
    · intro hg
      refine ⟨t⁻¹ * g * t, hg, ?_⟩
      rw [MulEquiv.toMonoidHom_eq_coe]
      show (MulAut.conj t) (t⁻¹ * g * t) = g
      rw [MulAut.conj_apply]
      group
  have hzN : y⁻¹ * (κ : G) ∈ Subgroup.normalizer (W₁ : Set G) := by
    have hstep : ∀ z : G, ((κ : G)⁻¹ * z * (κ : G)) ∈ W₁ ↔ (y⁻¹ * z * y) ∈ W₁ := by
      intro z
      rw [← conj_mem_iff (κ : G) z, ← conj_mem_iff y z, hkey]
    have hEquiv : ∀ z : G, z ∈ W₁ ↔ y⁻¹ * ((κ : G) * z * (κ : G)⁻¹) * y ∈ W₁ := by
      intro z
      have h1 : ((κ : G)⁻¹ * ((κ : G) * z * (κ : G)⁻¹) * (κ : G)) = z := by group
      have h2 := hstep ((κ : G) * z * (κ : G)⁻¹)
      rwa [h1] at h2
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h3 : (y⁻¹ * (κ : G)) * g * (y⁻¹ * (κ : G))⁻¹
        = y⁻¹ * ((κ : G) * g * (κ : G)⁻¹) * y := by group
    rw [h3]
    exact hEquiv g
  -- `y⁻¹ * κ` inverts `x`
  have hκx : (κ : G) * x * (κ : G)⁻¹ = x := by
    have hcomm : x * (κ : G) = (κ : G) * x :=
      (Subgroup.mem_centralizer_iff.mp (κ : ↥A).2) x (by simp)
    rw [← hcomm]; group
  have hzX : (y⁻¹ * (κ : G)) * x * (y⁻¹ * (κ : G))⁻¹ = x⁻¹ := by
    have h3 : (y⁻¹ * (κ : G)) * x * (y⁻¹ * (κ : G))⁻¹
        = y⁻¹ * ((κ : G) * x * (κ : G)⁻¹) * y := by group
    rw [h3, hκx, hyinv]
    exact hyx'
  -- order of the Sylow of `A`
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW₁2
  have hcases : Nat.card ↥W₁ = 4 ∨ Nat.card ↥W₁ = 8 := by
    have hk3 : k ≤ 3 := by
      by_contra h
      push_neg at h
      have h4 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h8 : 2 ^ k ≤ 8 := by rw [← hk]; exact hW₁le
      norm_num at h4
      omega
    have hk2 : 2 ≤ k := by
      by_contra h
      push_neg at h
      have h4 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hge : 4 ≤ 2 ^ k := by rw [← hk]; exact hW₁ge
      norm_num at h4
      omega
    rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
    · left; rw [hk]; norm_num
    · right; rw [hk]; norm_num
  rcases hcases with h4 | h8
  · -- `W₁ = V`, so the conjugating element lies in `N_G(V) = H`
    have hWV : (W : Subgroup ↥A) = V.subgroupOf A := by
      have h1 : Nat.card ↥(V.subgroupOf A) = 4 :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxV).toEquiv).trans hV.1
      have h2 : Nat.card ↥(W : Subgroup ↥A) = 4 := by rw [← hW₁card]; exact h4
      exact (Subgroup.eq_of_le_of_card_ge hVW (by omega)).symm
    have hW₁V : W₁ = V := by
      rw [hW₁def, hWV, Subgroup.map_subgroupOf_eq_of_le hxV]
    exact ⟨y⁻¹ * (κ : G), by rw [← hNV, ← hW₁V]; exact hzN, hzX⟩
  · -- otherwise `W₁` is a Sylow `2`-subgroup of `G`, and the `2`-part of the conjugating
    -- element would lie in it, forcing `x = x⁻¹`
    obtain ⟨s, hsz, hs2, hsx⟩ := C4UTwoPartPow hxodd hzX
    have hsN : s ∈ Subgroup.normalizer (W₁ : Set G) := (Subgroup.zpowers_le.mpr hzN) hsz
    have hsup2 : IsPGroup 2 ↥(Subgroup.zpowers s ⊔ W₁ : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (H := Subgroup.zpowers s) (K := W₁) hs2 hW₁2
        (Subgroup.zpowers_le.mpr hsN)
    have hsupcard : Nat.card ↥(Subgroup.zpowers s ⊔ W₁ : Subgroup G) ≤ 8 :=
      h2 _ hsup2
    have hsupge : 8 ≤ Nat.card ↥(Subgroup.zpowers s ⊔ W₁) := by
      have h1 : Nat.card ↥W₁ ≤ Nat.card ↥(Subgroup.zpowers s ⊔ W₁) := by
        have h2' := Subgroup.card_le_card_group
          (W₁.subgroupOf (Subgroup.zpowers s ⊔ W₁))
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (le_sup_right : W₁ ≤ Subgroup.zpowers s ⊔ W₁)).toEquiv] at h2'
      omega
    have hW₁eq : W₁ = Subgroup.zpowers s ⊔ W₁ := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
      omega
    have hsW : s ∈ W₁ := by
      have : s ∈ Subgroup.zpowers s ⊔ W₁ := Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
      rwa [← hW₁eq] at this
    have hsA : s ∈ A := by
      rw [hW₁def] at hsW
      obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp hsW
      rw [← hw]
      exact w.2
    have hcomm : x * s = s * x := (Subgroup.mem_centralizer_iff.mp hsA) x (by simp)
    have hxinv : x = x⁻¹ := by
      have h1 : s * x * s⁻¹ = x := by rw [← hcomm]; group
      rw [← hsx, h1]
    exact (hxne hxinv).elim

/-- **Bender 1981 §3 (5), restricted to `U^#`.** -/
theorem CosetFourUCase {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ x y : G, x ∈ B.U → x ≠ 1 → orderOf y = 2 → y ∉ B.Hhat → y * x * y⁻¹ = x⁻¹ → False := by
  intro x y hxU hx1 hy2 hyH hyx
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hV4 : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hVleHhat : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hNV : Subgroup.normalizer (((pCoreIn 2 B.Hhat) : Subgroup G) : Set G) = B.Hhat :=
    NormalizerPcoreEqHhat G h B D.four
  have hVc : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer ({x} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (Subgroup.mem_centralizer_iff.mp (hVcU hv)) x hxU
  have h2sub : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card P ≤ 8 := by
    intro P hP
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hP
    have hQcard : Nat.card ↥(Q : Subgroup G) = 8 := by
      rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity B.S, D.S8]
    calc Nat.card P = Nat.card ↥(P.subgroupOf (Q : Subgroup G)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv).symm
      _ ≤ Nat.card ↥(Q : Subgroup G) := Subgroup.card_le_card_group _
      _ = 8 := hQcard
  have hxodd : Odd (orderOf x) :=
    (Work.CORE2A.bSetup_U_odd B).of_dvd_nat (Subgroup.orderOf_dvd_natCard B.U hxU)
  -- Bender's Sylow argument
  obtain ⟨z, hzH, hzx⟩ :=
    C4UNormalizerConj (pCoreIn 2 B.Hhat) B.Hhat D.four hNV h2sub hVc hy2 hyx hyH hx1 hxodd
  obtain ⟨s, hsz, hs2, hsx⟩ := C4UTwoPartPow hxodd hzx
  have hsH : s ∈ B.Hhat := (Subgroup.zpowers_le.mpr hzH) hsz
  have hsV : s ∉ pCoreIn 2 B.Hhat := by
    intro hsVin
    have hc : s ∈ Subgroup.centralizer ({x} : Set G) := hVc hsVin
    have hcomm : x * s = s * x := (Subgroup.mem_centralizer_iff.mp hc) x (by simp)
    have h1 : s * x * s⁻¹ = x := by rw [← hcomm]; group
    have hxinv : x = x⁻¹ := by rw [← hsx, h1]
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hxinv
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
    · exact hx1 (orderOf_eq_one_iff.mp hh)
    · obtain ⟨k, hk⟩ := hxodd; omega
  -- produce an involution of `Ĥ − V` inverting `x`
  have key : x ∈ D.K := by
    by_cases hss : s * s = 1
    · have hs1 : s ≠ 1 := fun h1 => hsV (h1 ▸ (pCoreIn 2 B.Hhat).one_mem)
      have hord2 : orderOf s = 2 := by
        have hdv : orderOf s ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hss)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdv with hh | hh
        · exact absurd (orderOf_eq_one_iff.mp hh) hs1
        · exact hh
      change x ∈ (D.K : Set G)
      rw [D.inv s hsH hord2 hsV]
      exact ⟨hxU, hsx⟩
    · -- `s` has order `4`; the coset `s·V` contains an involution
      set T : Subgroup G := pCoreIn 2 B.Hhat ⊔ Subgroup.zpowers s with hTdef
      have hVT : pCoreIn 2 B.Hhat ≤ T := le_sup_left
      have hsT : s ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
      have hzpV : Subgroup.zpowers s ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
        rw [hNV]; exact Subgroup.zpowers_le.mpr hsH
      have hT2 : IsPGroup 2 ↥T := by
        rw [hTdef]
        exact IsPGroup.to_sup_of_normal_left' (H := pCoreIn 2 B.Hhat) (K := Subgroup.zpowers s)
          (IsPGroup.of_card (p := 2) (n := 2) (by rw [hV4.1]; norm_num)) hs2 hzpV
      have hTle : Nat.card ↥T ≤ 8 := h2sub T hT2
      have hTge : 4 ≤ Nat.card ↥T := by
        have h1 : Nat.card ↥(pCoreIn 2 B.Hhat) ≤ Nat.card ↥T := by
          have h2' := Subgroup.card_le_card_group ((pCoreIn 2 B.Hhat).subgroupOf T)
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv] at h2'
        have h3 : Nat.card ↥(pCoreIn 2 B.Hhat) = 4 := hV4.1
        exact h3 ▸ h1
      have hTne : Nat.card ↥T ≠ 4 := by
        intro h4
        have h2 : Nat.card ↥T ≤ Nat.card ↥(pCoreIn 2 B.Hhat) := by
          rw [h4]
          exact le_of_eq hV4.1.symm
        have h3 : T = pCoreIn 2 B.Hhat := (Subgroup.eq_of_le_of_card_ge hVT h2).symm
        exact hsV (h3 ▸ hsT)
      have hTcard : Nat.card ↥T = 8 := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
        have hk3 : k ≤ 3 := by
          by_contra hc
          push Not at hc
          have h4 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h8 : 2 ^ k ≤ 8 := by rw [← hk]; exact hTle
          norm_num at h4; omega
        have hk2 : 2 ≤ k := by
          by_contra hc
          push Not at hc
          have h4 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hge : 4 ≤ 2 ^ k := by rw [← hk]; exact hTge
          norm_num at h4; omega
        rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
        · exact absurd (show Nat.card ↥T = 4 by rw [hk]; norm_num) hTne
        · rw [hk]; norm_num
      have hsord : orderOf s = 4 := by
        have hdv : orderOf s ∣ Nat.card ↥T := by
          have h1 : Nat.card ↥((Subgroup.zpowers s).subgroupOf T)
              = Nat.card ↥(Subgroup.zpowers s) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Subgroup.zpowers s ≤ T)).toEquiv
          have h2 := Subgroup.card_subgroup_dvd_card ((Subgroup.zpowers s).subgroupOf T)
          rw [h1, Nat.card_zpowers] at h2
          exact h2
        have hsne1 : orderOf s ≠ 1 :=
          fun hc => hsV (orderOf_eq_one_iff.mp hc ▸ (pCoreIn 2 B.Hhat).one_mem)
        have hsne2 : orderOf s ≠ 2 := by
          intro hc
          apply hss
          have h2 : s ^ (orderOf s) = 1 := pow_orderOf_eq_one s
          rw [hc] at h2
          simpa [pow_two] using h2
        have hsne8 : orderOf s ≠ 8 := by
          intro h8
          have hsub : Subgroup.zpowers s ≤ T := le_sup_right
          have heq : Subgroup.zpowers s = T := by
            refine Subgroup.eq_of_le_of_card_ge hsub ?_
            rw [Nat.card_zpowers, h8, hTcard]
          have hVT' : pCoreIn 2 B.Hhat ≤ Subgroup.zpowers s := by rw [heq]; exact hVT
          have hcyc : IsCyclic ↥(pCoreIn 2 B.Hhat) :=
            isCyclic_of_injective (Subgroup.inclusion hVT') (Subgroup.inclusion_injective hVT')
          exact Work.CORE3.not_isCyclic_of_isFourGroup D.four hcyc
        have hpow : orderOf s ∣ 2 ^ 3 := by rw [hTcard] at hdv; norm_num at hdv ⊢; exact hdv
        obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with h0 | h1 | h2 | h3
        · exact absurd (by rw [hj, h0]; norm_num : orderOf s = 1) hsne1
        · exact absurd (by rw [hj, h1]; norm_num : orderOf s = 2) hsne2
        · rw [hj, h2]; norm_num
        · exact absurd (by rw [hj, h3]; norm_num : orderOf s = 8) hsne8
      obtain ⟨e⟩ := IsoDihedralFourOfCardEight h B D T hTcard hVT
      obtain ⟨w, hwV, hw⟩ := c4u_coset_involution T (pCoreIn 2 B.Hhat) hVT hV4.1 hV4.2
        hTcard e hsT hsV hsord
      have hswH : s * w ∈ B.Hhat := B.Hhat.mul_mem hsH (hVleHhat hwV)
      have hswV : s * w ∉ pCoreIn 2 B.Hhat := by
        intro hmem
        have : s ∈ pCoreIn 2 B.Hhat := by
          have h1 : s = (s * w) * w⁻¹ := by group
          rw [h1]
          exact (pCoreIn 2 B.Hhat).mul_mem hmem ((pCoreIn 2 B.Hhat).inv_mem hwV)
        exact hsV this
      have hsw1 : s * w ≠ 1 := by
        intro h1
        have h2 : s = w⁻¹ := by
          have h3 : s = (s * w) * w⁻¹ := by group
          rw [h3, h1, one_mul]
        exact hsV (h2 ▸ (pCoreIn 2 B.Hhat).inv_mem hwV)
      have hsword : orderOf (s * w) = 2 := by
        have hdv : orderOf (s * w) ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hw)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdv with hh | hh
        · exact absurd (orderOf_eq_one_iff.mp hh) hsw1
        · exact hh
      have hswx : (s * w) * x * (s * w)⁻¹ = x⁻¹ := by
        have hwcomm : x * w = w * x := (Subgroup.mem_centralizer_iff.mp (hVcU hwV)) x hxU
        have hwconj : w * x * w⁻¹ = x := by rw [← hwcomm]; group
        calc (s * w) * x * (s * w)⁻¹ = s * (w * x * w⁻¹) * s⁻¹ := by group
          _ = s * x * s⁻¹ := by rw [hwconj]
          _ = x⁻¹ := hsx
      change x ∈ (D.K : Set G)
      rw [D.inv (s * w) hswH hsword hswV]
      exact ⟨hxU, hswx⟩
  -- `⟨x⟩ ≤ F(U)`, so `y ∈ N_G(⟨x⟩) ≤ Ĥ`, contradicting `y ∉ Ĥ`
  have hfill : Subgroup.zpowers x ≤ fittingIn B.U := Subgroup.zpowers_le.mpr (D.hall.1 key)
  have hNle : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ B.Hhat :=
    h1.2 (Subgroup.zpowers x) (fun hbot => hx1 (Subgroup.zpowers_eq_bot.mp hbot)) hfill
  have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    have hxinv_mem : x⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : y * x ^ n * y⁻¹ = (x⁻¹) ^ n := by
        have h2 : (MulAut.conj y) (x ^ n) = (MulAut.conj y) x ^ n :=
          map_zpow (MulAut.conj y) x n
        have h3 : (MulAut.conj y) (x ^ n) = y * x ^ n * y⁻¹ := MulAut.conj_apply y (x ^ n)
        have h4 : (MulAut.conj y) x = x⁻¹ := by rw [MulAut.conj_apply]; exact hyx
        rw [← h3, h2, h4]
      rw [h1]
      exact Subgroup.zpow_mem _ hxinv_mem n
    · intro hw
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : y⁻¹ * x * y = x⁻¹ := by
        have h2 : y⁻¹ * x⁻¹ * y = x := by rw [← hyx]; group
        have h3 := congrArg Inv.inv h2
        simpa [mul_inv_rev, mul_assoc] using h3
      have h5 : y⁻¹ * x ^ n * y = (x⁻¹) ^ n := by
        have h6 : (MulAut.conj y⁻¹) (x ^ n) = (MulAut.conj y⁻¹) x ^ n :=
          map_zpow (MulAut.conj y⁻¹) x n
        have h7 : (MulAut.conj y⁻¹) (x ^ n) = y⁻¹ * x ^ n * y := by
          rw [MulAut.conj_apply, inv_inv]
        have h8 : (MulAut.conj y⁻¹) x = x⁻¹ := by rw [MulAut.conj_apply, inv_inv]; exact h1
        rw [← h7, h6, h8]
      have hconv : w = (x⁻¹) ^ n := by
        have h9 : w = y⁻¹ * x ^ n * y := by
          calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
            _ = y⁻¹ * x ^ n * y := by rw [hn]
        rw [h9, h5]
      rw [hconv]
      exact Subgroup.zpow_mem _ hxinv_mem n
  exact hyH (hNle hyN)

end Work.CORE3
