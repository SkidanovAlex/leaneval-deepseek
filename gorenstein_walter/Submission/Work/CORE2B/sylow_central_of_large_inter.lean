import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.Dihedral.Defs

/-!
# CORE2B — the case `8 ≤ |S ⊓ M|` of "`t` is 2-central in `M`"

Let `S` be a Sylow 2-subgroup of a finite group `G` with `S ≅ DihedralGroup n`, and let
`t ∈ G` be an involution centralising `S`.  If `M ≤ G` contains `t` and `|S ⊓ M| ≥ 8`, then
some Sylow 2-subgroup `P` of `M` is centralised by `t` (equivalently `t ∈ Z(P)`).

The mathematics:

* `t ∈ S` (`mem_sylow_of_centralizes`): `S ⊔ ⟨t⟩` is a 2-subgroup of `G` containing the Sylow
  subgroup `S`, hence equals it.
* Let `Q = S ⊓ M` (`|Q| ≥ 8`), a 2-subgroup of `M`, and let `P` be a Sylow 2-subgroup of `M`
  containing `Q`; then `P`, viewed inside `G`, lies in some Sylow 2-subgroup `S'` of `G`
  (`exists_sylow_le_of_inf`).  Composing a Sylow conjugacy `S' ≅ S` with the given isomorphism
  `S ≅ DihedralGroup n` puts everything inside the concrete group `DihedralGroup n`.
* **The key point** (`dihedral_isCentral_of_large_subgroup`): in `DihedralGroup n`, if `u` is an
  involution central in a subgroup `R` of order at least `8`, then `u` is central in the whole
  group.  Indeed a reflection `sr i` centralising a subgroup `R` of order `≥ 8` would centralise
  an element `g = r k` of order `≥ 4` (the generator of `R ⊓ ⟨r⟩`, whose index in `R` is at most
  `2`); but `sr i * r k * (sr i)⁻¹ = r (-k) = r k` forces `(r k) ^ 2 = 1`.  Hence `u = r k` is a
  rotation with `2k = 0`, and such an element commutes with every `r j` and every `sr j`.
* Transporting back along the isomorphism gives `t` central in `P`.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.style.haveILetI false

/-! ## 1. An involution centralising a Sylow 2-subgroup lies in it -/

theorem mem_sylow_of_centralizes {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (t : G)
    (ht : orderOf t = 2) (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) : t ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, ht]; norm_num⟩
  have hS2 : IsPGroup 2 ↥(S : Subgroup G) := S.isPGroup'
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (S : Subgroup G) := by
    refine le_trans (Subgroup.zpowers_le.mpr ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun h hh => htc h hh
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ (S : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' hz hS2 hle
  have hH : (Subgroup.zpowers t ⊔ (S : Subgroup G)) = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_right
  have : t ∈ (Subgroup.zpowers t ⊔ (S : Subgroup G)) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  rwa [hH] at this

/-! ## 2. The abstract dihedral statement -/

open DihedralGroup in
/-- In `DihedralGroup n`, an involution which is central in a subgroup of order at least `8` is
central in the whole group. -/
theorem dihedral_isCentral_of_large_subgroup {n : ℕ} (R : Subgroup (DihedralGroup n))
    (hR : 8 ≤ Nat.card R) (u : DihedralGroup n) (huR : u ∈ R) (hu2 : orderOf u = 2)
    (huC : ∀ w ∈ R, u * w = w * u) :
    ∀ x : DihedralGroup n, x * u = u * x := by
  -- `u` is a rotation: a reflection centralising a subgroup of order `≥ 8` is impossible.
  have hu_mem_rot : u ∈ Work.Dihedral.rot n := by
    by_contra hu_not
    obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hu_not
    let f : ↥R →* Multiplicative (ZMod 2) := (Work.RED.dihedralSign n).comp R.subtype
    have hker : f.ker = (R ⊓ Work.Dihedral.rot n).subgroupOf R := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show Work.RED.dihedralSign n ((x : ↥R) : DihedralGroup n) = 1 ↔ _
      rw [Work.RED.dihedralSign_eq_one_iff]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    have hidx : ((R ⊓ Work.Dihedral.rot n).subgroupOf R).index = Nat.card ↥f.range := by
      rw [← hker, Subgroup.index_ker]
    have hrange_le : Nat.card ↥f.range ≤ 2 := by
      have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Work.RED.natCard_multiplicative_zmod_two
      calc Nat.card ↥f.range ≤ Nat.card (Multiplicative (ZMod 2)) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = 2 := h2
    -- `R ⊓ ⟨r⟩` has index at most `2` in `R`, hence at least `4` elements.
    have hcardR : Nat.card ↥R
        = Nat.card ↥((R ⊓ Work.Dihedral.rot n).subgroupOf R)
          * ((R ⊓ Work.Dihedral.rot n).subgroupOf R).index :=
      (Subgroup.card_mul_index ((R ⊓ Work.Dihedral.rot n).subgroupOf R)).symm
    have hcardA : 4 ≤ Nat.card ↥(R ⊓ Work.Dihedral.rot n) := by
      have h1 : Nat.card ↥(R ⊓ Work.Dihedral.rot n)
          = Nat.card ↥((R ⊓ Work.Dihedral.rot n).subgroupOf R) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (show R ⊓ Work.Dihedral.rot n ≤ R from inf_le_left)).toEquiv).symm
      have h2 : 8 ≤ Nat.card ↥((R ⊓ Work.Dihedral.rot n).subgroupOf R)
          * ((R ⊓ Work.Dihedral.rot n).subgroupOf R).index := by
        rw [← hcardR]; exact hR
      have hidx2 : ((R ⊓ Work.Dihedral.rot n).subgroupOf R).index ≤ 2 := hidx ▸ hrange_le
      have h3 : 8 ≤ Nat.card ↥((R ⊓ Work.Dihedral.rot n).subgroupOf R) * 2 :=
        le_trans h2 (Nat.mul_le_mul_left _ hidx2)
      have h4 : 4 ≤ Nat.card ↥((R ⊓ Work.Dihedral.rot n).subgroupOf R) := by omega
      rwa [h1]
    -- a generator of `R ⊓ ⟨r⟩`, of order at least `4`
    haveI : IsCyclic ↥(R ⊓ Work.Dihedral.rot n) :=
      Subgroup.isCyclic_of_le
        (show R ⊓ Work.Dihedral.rot n ≤ Work.Dihedral.rot n from inf_le_right)
    obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := ↥(R ⊓ Work.Dihedral.rot n))
    have htop : Subgroup.zpowers g = ⊤ := by
      ext x; exact ⟨fun _ => Subgroup.mem_top x, fun _ => hgen x⟩
    have hordg : orderOf g = Nat.card ↥(R ⊓ Work.Dihedral.rot n) := by
      rw [← Nat.card_zpowers g, htop, Subgroup.card_top]
    obtain ⟨k, hk⟩ := Work.Dihedral.mem_rot.mp (g.2).2
    -- `u` centralises `g`, i.e. `sr i * r k * (sr i)⁻¹ = r k`
    have hconj : u * (g : DihedralGroup n) * u⁻¹ = (g : DihedralGroup n) := by
      rw [huC (g : DihedralGroup n) (g.2).1]
      group
    rw [hi, hk, DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr] at hconj
    have h2 : -k = k := by
      have h3 := DihedralGroup.r.inj hconj
      have h4 : i - (i + k) = -k := by abel
      rwa [h4] at h3
    have hkk : k + k = 0 := neg_eq_iff_add_eq_zero.mp h2
    -- hence `(r k) ^ 2 = 1`, contradicting `4 ≤ orderOf (r k)`
    have hsq : (DihedralGroup.r k : DihedralGroup n) ^ 2 = 1 := by
      rw [DihedralGroup.r_pow]
      have hk2 : k * ((2 : ℕ) : ZMod n) = 0 := by
        rw [show ((2 : ℕ) : ZMod n) = 2 by norm_num, mul_comm, two_mul]
        exact hkk
      rw [hk2, DihedralGroup.r_zero]
    have hdvd : orderOf (DihedralGroup.r k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    have hle2 : orderOf (DihedralGroup.r k) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge4 : 4 ≤ orderOf (DihedralGroup.r k) := by
      rw [← hk, ← Subgroup.orderOf_mk (g : DihedralGroup n) (g.2), hordg]
      exact hcardA
    omega
  -- `u = r k` with `k + k = 0`, and such an element is central.
  obtain ⟨k, hk⟩ := Work.Dihedral.mem_rot.mp hu_mem_rot
  have hkk : k + k = 0 := by
    have h1 : (DihedralGroup.r k : DihedralGroup n) ^ 2 = 1 := by
      rw [← hk]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hu2])
    rw [DihedralGroup.r_pow] at h1
    have h2 : k * ((2 : ℕ) : ZMod n) = 0 := DihedralGroup.r.inj h1
    rw [show ((2 : ℕ) : ZMod n) = 2 by norm_num, mul_comm, two_mul] at h2
    exact h2
  intro x
  rw [hk]
  rcases Work.Dihedral.eq_r_or_sr x with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
    congr 1
    ring
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    rw [sub_eq_add_neg]
    congr 1
    exact eq_neg_iff_add_eq_zero.mpr hkk

/-! ## 3. Sylow bookkeeping -/

/-- `S ⊓ M` is a 2-subgroup of `M` contained in a Sylow 2-subgroup `P` of `M`, and `P` (viewed
in `G`) lies in a Sylow 2-subgroup `S'` of `G`. -/
theorem exists_sylow_le_of_inf {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (M : Subgroup G) :
    ∃ (P : Sylow 2 M) (S' : Sylow 2 G),
      ((S : Subgroup G) ⊓ M : Subgroup G) ≤ (P : Subgroup M).map M.subtype ∧
      (P : Subgroup M).map M.subtype ≤ (S' : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥(((S : Subgroup G) ⊓ M).subgroupOf M) := by
    have hQinf : IsPGroup 2 ↥((S : Subgroup G) ⊓ M) :=
      IsPGroup.to_inf_left (H := (S : Subgroup G)) (K := M) S.isPGroup'
    exact hQinf.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (S : Subgroup G) ⊓ M ≤ M)).symm
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  have hPG : IsPGroup 2 ↥((P : Subgroup M).map M.subtype) := P.isPGroup'.map M.subtype
  obtain ⟨S', hS'⟩ := hPG.exists_le_sylow
  refine ⟨P, S', ?_, hS'⟩
  intro x hx
  exact ⟨⟨x, hx.2⟩, hP (by rwa [Subgroup.mem_subgroupOf]), rfl⟩

/-! ## 4. The main lemma -/

theorem sylow_central_of_large_inter {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (t : G) (ht : orderOf t = 2)
    (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) (M : Subgroup G) (htM : t ∈ M)
    (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P)
    (hbig : 8 ≤ Nat.card ((S : Subgroup G) ⊓ M : Subgroup G)) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `t` lies in `S`, hence in `S ⊓ M`
  have htS : t ∈ (S : Subgroup G) := mem_sylow_of_centralizes S t ht htc
  -- Sylow bookkeeping
  obtain ⟨P, S', hQS', hPS'⟩ := exists_sylow_le_of_inf S M
  have htQ : t ∈ ((S : Subgroup G) ⊓ M : Subgroup G) := ⟨htS, htM⟩
  have htS' : t ∈ (S' : Subgroup G) := hPS' (hQS' htQ)
  -- an isomorphism putting `S'` inside the concrete dihedral group
  haveI : Finite (Sylow 2 G) := inferInstance
  obtain ⟨eS⟩ := hS
  let e : ↥(S' : Subgroup G) ≃* DihedralGroup n := (Sylow.equiv S' S).trans eS
  -- the image `R` of `S ⊓ M`, and `u = e t`
  let Q : Subgroup ↥(S' : Subgroup G) :=
    ((S : Subgroup G) ⊓ M : Subgroup G).subgroupOf (S' : Subgroup G)
  let R : Subgroup (DihedralGroup n) := Q.map (e : ↥(S' : Subgroup G) →* DihedralGroup n)
  have hR : 8 ≤ Nat.card R := by
    have h1 : Nat.card R = Nat.card ↥Q :=
      Subgroup.card_map_of_injective
        (f := (e : ↥(S' : Subgroup G) →* DihedralGroup n)) e.injective
    have h2 : Nat.card ↥Q = Nat.card ↥((S : Subgroup G) ⊓ M : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := ((S : Subgroup G) ⊓ M : Subgroup G)) (K := (S' : Subgroup G))
        (hQS'.trans hPS')).toEquiv
    rw [h1, h2]
    exact hbig
  have huR : e ⟨t, htS'⟩ ∈ R := by
    rw [Subgroup.mem_map]
    exact ⟨⟨t, htS'⟩, Subgroup.mem_subgroupOf.mpr htQ, rfl⟩
  have hu2 : orderOf (e ⟨t, htS'⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h3 : orderOf (⟨t, htS'⟩ : ↥(S' : Subgroup G)) = 2 := by
        rw [Subgroup.orderOf_mk]; exact ht
      have h2 : (⟨t, htS'⟩ : ↥(S' : Subgroup G)) ^ 2 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (by rw [h3])
      rw [← map_pow, h2, map_one]
    · intro h
      have h1 : (⟨t, htS'⟩ : ↥(S' : Subgroup G)) = 1 := e.injective (by rw [h, map_one])
      have h2 : orderOf (⟨t, htS'⟩ : ↥(S' : Subgroup G)) = 2 := by
        rw [Subgroup.orderOf_mk]; exact ht
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  have huC : ∀ w ∈ R, e ⟨t, htS'⟩ * w = w * e ⟨t, htS'⟩ := by
    intro w hw
    rw [Subgroup.mem_map] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hyS : (y : G) ∈ (S : Subgroup G) := (Subgroup.mem_subgroupOf.mp hy).1
    have hcomm : (y : ↥(S' : Subgroup G)) * ⟨t, htS'⟩ = ⟨t, htS'⟩ * y := by
      apply Subtype.ext
      exact htc (y : G) hyS
    calc e ⟨t, htS'⟩ * e y = e (⟨t, htS'⟩ * y) := (map_mul e _ _).symm
      _ = e (y * ⟨t, htS'⟩) := by rw [hcomm]
      _ = e y * e ⟨t, htS'⟩ := map_mul e _ _
  -- the abstract dihedral statement
  have hcent : ∀ x : DihedralGroup n, x * e ⟨t, htS'⟩ = e ⟨t, htS'⟩ * x :=
    dihedral_isCentral_of_large_subgroup R hR (e ⟨t, htS'⟩) huR hu2 huC
  refine ⟨P, ?_⟩
  intro x hx
  have hxS' : (x : G) ∈ (S' : Subgroup G) :=
    hPS' ⟨x, hx, rfl⟩
  have hcomm := hcent (e ⟨(x : G), hxS'⟩)
  have h2 : (⟨(x : G), hxS'⟩ : ↥(S' : Subgroup G)) * ⟨t, htS'⟩
      = ⟨t, htS'⟩ * ⟨(x : G), hxS'⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact hcomm
  exact congrArg Subtype.val h2

end Work.CORE2B
