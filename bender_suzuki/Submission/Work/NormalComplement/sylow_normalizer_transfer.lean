/-
# `Work.NormalComplement.sylow_normalizer_transfer`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. III §1, proof of Lemma 2, step 2:

> A `p`-Sylow `S` of `N_E(U)` is a `p`-Sylow of `N_W(U)`

(here `U = V`, `E ≤ W`).  The two normaliser hypotheses `h1`, `h2` of the lemma supply the
identity `N_W(S) = O_{p'}(C_W(S)) · N_E(S)` for every `p`-Sylow `S` of `N_E(V)`: if `S` is not
cyclic one conjugates `S` into the Sylow `P ≤ E` (hypothesis `h2`); if `S` is cyclic then one
first shows that `S` is a Sylow of `E`, hence conjugate to `P` (hypothesis `h1`).

The file is self-contained: the auxiliary Sylow lemmas about the (locally defined) predicate
`IsSylowIn` are proved here.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.isSylowIn_of_sylowIn_normalizer
import Submission.Work.NormalComplement.not_dvd_index_sylowIn_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Classical
open scoped Pointwise

namespace Work.NormalComplement

/-! ## Auxiliary Sylow lemmas for `IsSylowIn` -/

section Infra

variable {G : Type*} [Group G] [Finite G]

/-- Membership in the conjugate `H^x = x H x⁻¹`, spelled out. -/
private lemma mem_map_conj_iff {H : Subgroup G} {x y : G} :
    y ∈ H.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    have hy : y = x * h * x⁻¹ := hhx.symm.trans (MulAut.conj_apply x h)
    have hx : x⁻¹ * y * x = h := by rw [hy]; group
    rw [hx]; exact hh
  · intro h
    exact ⟨x⁻¹ * y * x, h, by
      show (MulAut.conj x) (x⁻¹ * y * x) = y
      rw [MulAut.conj_apply]
      group⟩

/-- `|H.subgroupOf Y| = |H|` for `H ≤ Y`. -/
private lemma card_subgroupOf_eq (H Y : Subgroup G) (h : H ≤ Y) :
    Nat.card ↥(H.subgroupOf Y) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- Conjugation by an element of `X` fixes `X`. -/
private lemma map_conj_eq_self_of_mem {X : Subgroup G} {x : G} (hx : x ∈ X) :
    X.map (MulAut.conj x).toMonoidHom = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)

/-- `(g^n)` and `(g^{gcd (orderOf g) n})` generate the same cyclic subgroup. -/
private lemma zpowers_pow_eq_zpowers_gcd (g : G) (n : ℕ) :
    Subgroup.zpowers (g ^ n) = Subgroup.zpowers (g ^ (orderOf g).gcd n) := by
  have hle : Subgroup.zpowers (g ^ n) ≤ Subgroup.zpowers (g ^ (orderOf g).gcd n) := by
    refine Subgroup.zpowers_le.mpr ?_
    have hbase : g ^ n = (g ^ (orderOf g).gcd n) ^ (n / (orderOf g).gcd n) := by
      have h := pow_mul g ((orderOf g).gcd n) (n / (orderOf g).gcd n)
      rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right (orderOf g) n)] at h
    rw [hbase]
    exact Subgroup.npow_mem_zpowers _ _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcard : Nat.card ↥(Subgroup.zpowers (g ^ (orderOf g).gcd n)) =
      Nat.card ↥(Subgroup.zpowers (g ^ n)) := by
    rw [Nat.card_zpowers (g ^ (orderOf g).gcd n), Nat.card_zpowers (g ^ n),
      orderOf_pow (n := (orderOf g).gcd n) g, orderOf_pow (n := n) g]
    congr 1
    exact Nat.dvd_antisymm (Nat.gcd_dvd_right (orderOf g) ((orderOf g).gcd n))
      (Nat.dvd_gcd (Nat.gcd_dvd_left (orderOf g) n) (Nat.dvd_refl _))
  exact le_of_eq hcard

/-- In a finite cyclic group, subgroups of equal order are equal. -/
private lemma subgroup_eq_of_card_eq_of_isCyclic {H : Type*} [Group H] [Finite H]
    (hG : IsCyclic H) {A B : Subgroup H} (h : Nat.card ↥A = Nat.card ↥B) : A = B := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  obtain ⟨n, rfl⟩ := (Subgroup.le_zpowers_iff g A).mp (hg ▸ le_top)
  obtain ⟨m, rfl⟩ := (Subgroup.le_zpowers_iff g B).mp (hg ▸ le_top)
  have h1 : Nat.card ↥(Subgroup.zpowers (g ^ n)) = Nat.card ↥(Subgroup.zpowers (g ^ m)) := h
  rw [Nat.card_zpowers (g ^ n), Nat.card_zpowers (g ^ m),
    orderOf_pow (n := n) g, orderOf_pow (n := m) g] at h1
  have hdn : (orderOf g).gcd n ∣ orderOf g := Nat.gcd_dvd_left _ _
  have hdm : (orderOf g).gcd m ∣ orderOf g := Nat.gcd_dvd_left _ _
  have hd : (orderOf g).gcd n = (orderOf g).gcd m := by
    have hkey : (orderOf g).gcd n * (orderOf g / (orderOf g).gcd n) =
        (orderOf g).gcd m * (orderOf g / (orderOf g).gcd n) := by
      rw [Nat.mul_div_cancel' hdn, h1, Nat.mul_div_cancel' hdm]
    have hcp : 0 < orderOf g / (orderOf g).gcd n := by
      have : 0 < Nat.card ↥(Subgroup.zpowers (g ^ n)) := Nat.card_pos
      rwa [Nat.card_zpowers (g ^ n), orderOf_pow (n := n) g] at this
    exact Nat.eq_of_mul_eq_mul_right hcp hkey
  rw [zpowers_pow_eq_zpowers_gcd g n, zpowers_pow_eq_zpowers_gcd g m, hd]

variable {p : ℕ} [Fact p.Prime]

/-- A `p`-subgroup of `X` has order dividing the order of a `p`-Sylow of `X`. -/
private lemma card_dvd_card_of_isPGroup_of_isSylowIn {U P X : Subgroup G} (hUX : U ≤ X)
    (hU : IsPGroup p U) (hP : IsSylowIn p P X) : Nat.card U ∣ Nat.card P := by
  have h1 : Nat.card U ∣ Nat.card X := by
    rw [← card_subgroupOf_eq U X hUX]
    exact Subgroup.card_subgroup_dvd_card (U.subgroupOf X)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have h2 : Nat.card X = (P.subgroupOf X).index * Nat.card P := by
    rw [← Subgroup.index_mul_card (P.subgroupOf X), card_subgroupOf_eq P X hP.2.1]
  have h3 : p ^ k ∣ Nat.card P * (P.subgroupOf X).index := by
    rw [mul_comm (Nat.card P), ← h2, ← hk]
    exact h1
  have h4 : Nat.Coprime (p ^ k) (P.subgroupOf X).index :=
    Nat.Coprime.pow_left _ ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hP.2.2)
  rw [hk]
  exact h4.dvd_of_dvd_mul_right h3

/-- Every `p`-subgroup of `X` is contained in a `p`-Sylow of `X`. -/
private lemma exists_isSylowIn_ge {T X : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup p T) :
    ∃ S : Subgroup G, T ≤ S ∧ IsSylowIn p S X := by
  have hT' : IsPGroup p (T.subgroupOf X) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  refine ⟨(S' : Subgroup ↥X).map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTX hx⟩, hS' (by simpa [Subgroup.mem_subgroupOf] using hx),
      rfl⟩
  · exact S'.isPGroup'.map X.subtype
  · exact Subgroup.map_subtype_le (S' : Subgroup ↥X)
  · intro hdiv
    have hle : (S' : Subgroup ↥X) ≤ ((S' : Subgroup ↥X).map X.subtype).subgroupOf X := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact (Sylow.not_dvd_index S') (dvd_trans hdiv (Subgroup.index_dvd_of_le hle))

/-- Two `p`-Sylows of the same subgroup have the same order. -/
private lemma card_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G} (hA : IsSylowIn p A X)
    (hB : IsSylowIn p B X) : Nat.card A = Nat.card B :=
  le_antisymm (Nat.le_of_dvd (Nat.card_pos)
      (card_dvd_card_of_isPGroup_of_isSylowIn hA.2.1 hA.1 hB))
    (Nat.le_of_dvd (Nat.card_pos)
      (card_dvd_card_of_isPGroup_of_isSylowIn hB.2.1 hB.1 hA))

/-- Two `p`-Sylows of the same subgroup are conjugate. -/
private lemma exists_conj_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G}
    (hA : IsSylowIn p A X) (hB : IsSylowIn p B X) :
    ∃ g ∈ X, A.map (MulAut.conj g).toMonoidHom = B := by
  have hA' : IsPGroup p (A.subgroupOf X) :=
    hA.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  have hB' : IsPGroup p (B.subgroupOf X) :=
    hB.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥X)
    (IsPGroup.toSylow hA' hA.2.2) (IsPGroup.toSylow hB' hB.2.2)
  have hsmul : MulAut.conj g • (A.subgroupOf X) = B.subgroupOf X := by
    have hcoe : (↑(g • IsPGroup.toSylow hA' hA.2.2) : Subgroup ↥X) =
        ↑(IsPGroup.toSylow hB' hB.2.2) := congrArg _ hg
    simpa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using hcoe
  refine ⟨(g : G), g.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have h1 : (⟨u, hA.2.1 hu⟩ : ↥X) ∈ A.subgroupOf X := by
      simpa [Subgroup.mem_subgroupOf] using hu
    have h2 : (MulAut.conj g) (⟨u, hA.2.1 hu⟩ : ↥X) ∈ B.subgroupOf X := by
      rw [← hsmul]
      exact ⟨_, h1, rfl⟩
    have h3 : ((MulAut.conj g) (⟨u, hA.2.1 hu⟩ : ↥X) : G) = (g : G) * u * (g : G)⁻¹ := by
      rw [MulAut.conj_apply]; simp
    rw [Subgroup.mem_subgroupOf] at h2
    rwa [h3] at h2
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective,
      card_eq_of_isSylowIn_of_isSylowIn hA hB]

/-- A `p`-subgroup of `X` of the order of a `p`-Sylow of `X` is a `p`-Sylow of `X`. -/
private lemma isSylowIn_of_le_of_card_eq {U P X : Subgroup G} (hUX : U ≤ X) (hU : IsPGroup p U)
    (hP : IsSylowIn p P X) (hcard : Nat.card U = Nat.card P) : IsSylowIn p U X := by
  obtain ⟨Q, hUQ, hQsyl⟩ := exists_isSylowIn_ge hUX hU
  have hQcard : Nat.card Q = Nat.card U :=
    (card_eq_of_isSylowIn_of_isSylowIn hQsyl hP).trans hcard.symm
  have hQU : U = Q := Subgroup.eq_of_le_of_card_ge hUQ (le_of_eq hQcard)
  rwa [hQU]

/-- Conjugating a `p`-Sylow gives a `p`-Sylow of the conjugate. -/
private lemma isSylowIn_map_conj {A X : Subgroup G} (hA : IsSylowIn p A X) (g : G) :
    IsSylowIn p (A.map (MulAut.conj g).toMonoidHom)
      (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map _, Subgroup.map_mono hA.2.1, ?_⟩
  have h : ((A.map (MulAut.conj g).toMonoidHom).subgroupOf
      (X.map (MulAut.conj g).toMonoidHom)).index = (A.subgroupOf X).index := by
    rw [← Subgroup.relIndex, ← Subgroup.relIndex]
    exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A X
      (MulAut.conj g).injective
  rw [h]
  exact hA.2.2

/-- Conjugation is compatible with composition. -/
private lemma map_conj_map_conj (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Conjugating by `a` and then by `a⁻¹` is the identity. -/
private lemma map_conj_inv (A : Subgroup G) (a : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = A := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp [Subgroup.mem_map]

/-- Cyclicity is preserved by conjugation. -/
private lemma isCyclic_map_conj_iff (A : Subgroup G) (g : G) :
    IsCyclic A ↔ IsCyclic (A.map (MulAut.conj g).toMonoidHom) :=
  MulEquiv.isCyclic (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)

/-- A `p`-Sylow of `X` remains a `p`-Sylow of any intermediate subgroup `Y`. -/
private lemma isSylowIn_of_le_of_le {S X Y : Subgroup G} (h : IsSylowIn p S X) (hSY : S ≤ Y)
    (hYX : Y ≤ X) : IsSylowIn p S Y := by
  refine ⟨h.1, hSY, ?_⟩
  intro hdiv
  have hdiv' : p ∣ S.relIndex X := by
    rw [← Subgroup.relIndex_mul_relIndex S Y X hSY hYX]
    exact dvd_mul_of_dvd_left (show p ∣ S.relIndex Y from hdiv) _
  exact h.2.2 (show p ∣ (S.subgroupOf X).index from hdiv')

/-- `N_G(P) ⊓ W` normalizes the centralizer `C_W(P) = C_G(P) ⊓ W`. -/
private lemma normalizer_inf_le_normalizer_centralizer_inf {P W : Subgroup G} :
    Subgroup.normalizer (P : Set G) ⊓ W ≤
      Subgroup.normalizer ((Subgroup.centralizer (P : Set G) ⊓ W : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  have hxP : x ∈ Subgroup.normalizer (P : Set G) := hx.1
  have hxW : x ∈ W := hx.2
  have hcC : c ∈ Subgroup.centralizer (P : Set G) := hc.1
  have hcW : c ∈ W := hc.2
  refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hxW hcW) (inv_mem hxW)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : x⁻¹ * a * x ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hxP (x⁻¹ * a * x)).mpr (by
      show x * (x⁻¹ * a * x) * x⁻¹ ∈ P
      rw [show x * (x⁻¹ * a * x) * x⁻¹ = a from by group]
      exact ha)
  have hcomm := (Subgroup.mem_centralizer_iff.mp hcC) (x⁻¹ * a * x) ha'
  calc a * (x * c * x⁻¹) = x * ((x⁻¹ * a * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * c * x⁻¹) * a := by group

/-- `O_{p'}(C)` is normal in any subgroup normalising `C`. -/
private lemma le_normalizer_pPrimeCoreSub {C N : Subgroup G}
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) :
    N ≤ Subgroup.normalizer (pPrimeCoreSub p C : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hxC : C.map (MulAut.conj x).toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNC hx)
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normalizer (C : Set G)).inv_mem (hNC hx)
  have hxCinv : C.map (MulAut.conj x⁻¹).toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxinv
  have hQ : pPrimeCoreSub p C = (Work.Fitting.pPrimeCore p ↥C).map C.subtype := by
    show (Submission.Blueprint.pPrimeCore p ↥C).map C.subtype =
      (Work.Fitting.pPrimeCore p ↥C).map C.subtype
    rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p (Fact.out : p.Prime)]
  have hle : (pPrimeCoreSub p C).map (MulAut.conj x).toMonoidHom ≤ pPrimeCoreSub p C := by
    rw [hQ, Subgroup.map_map]
    rintro y ⟨k, hk, rfl⟩
    have hmem : x * (k : G) * x⁻¹ ∈ (Work.Fitting.pPrimeCore p ↥C).map C.subtype := by
      obtain ⟨D, hD, hkD⟩ :=
        (Work.Fitting.mem_piCore_iff (G := ↥C) (π := fun q => q ≠ p) (x := k)).mp hk
      obtain ⟨hDnorm, hDpi⟩ := Work.Fitting.mem_piCoreSet.mp hD
      have hDC : (D.map C.subtype).map (MulAut.conj x).toMonoidHom ≤ C := by
        intro z hz
        have hz' : x⁻¹ * z * x ∈ D.map C.subtype :=
          (mem_map_conj_iff (H := D.map C.subtype)).mp hz
        obtain ⟨d, hd, hdd⟩ := Subgroup.mem_map.mp hz'
        have hdd' : (d : G) = x⁻¹ * z * x := hdd
        have hzeq : z = x * (d : G) * x⁻¹ := by rw [hdd']; group
        have hconj : x * (d : G) * x⁻¹ = (MulAut.conj x) (d : G) :=
          (MulAut.conj_apply x (d : G)).symm
        have hdC : (MulAut.conj x) (d : G) ∈ C := by
          have h1 : (MulAut.conj x) (d : G) ∈ C.map (MulAut.conj x).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨(d : G), d.2, rfl⟩
          rwa [hxC] at h1
        rw [hzeq, hconj]; exact hdC
      set D' : Subgroup ↥C :=
        ((D.map C.subtype).map (MulAut.conj x).toMonoidHom).comap C.subtype with hD'
      have hmapD' : D'.map C.subtype = (D.map C.subtype).map (MulAut.conj x).toMonoidHom :=
        Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
      have hcardD' : Nat.card ↥D' = Nat.card ↥D := by
        have h1 : Nat.card ↥D' = Nat.card ↥((D.map C.subtype).map
            (MulAut.conj x).toMonoidHom) := by
          rw [← Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective, hmapD']
        have h2 : Nat.card ↥((D.map C.subtype).map (MulAut.conj x).toMonoidHom) =
            Nat.card ↥(D.map C.subtype) :=
          Subgroup.card_map_of_injective (MulAut.conj x).injective
        have h3 : Nat.card ↥(D.map C.subtype) = Nat.card ↥D :=
          Subgroup.card_map_of_injective C.subtype_injective
        exact h1.trans (h2.trans h3)
      have hD'normal : D'.Normal := by
        refine ⟨fun a ha b => ?_⟩
        have haX : (a : G) ∈ (D.map C.subtype).map (MulAut.conj x).toMonoidHom := ha
        have hpre : x⁻¹ * (a : G) * x ∈ D.map C.subtype :=
          (mem_map_conj_iff (H := D.map C.subtype)).mp haX
        obtain ⟨d, hd, hdd⟩ := Subgroup.mem_map.mp hpre
        have hbC : x⁻¹ * (b : G) * x ∈ C :=
          (mem_map_conj_iff (H := C)).mp (by rw [hxC]; exact b.2)
        have hconjD : (⟨x⁻¹ * (b : G) * x, hbC⟩ : ↥C) * d *
            (⟨x⁻¹ * (b : G) * x, hbC⟩ : ↥C)⁻¹ ∈ D :=
          hDnorm.conj_mem d hd _
        have hG : (x⁻¹ * (b : G) * x) * (d : G) * (x⁻¹ * (b : G) * x)⁻¹
            ∈ D.map C.subtype := Subgroup.mem_map.mpr ⟨_, hconjD, rfl⟩
        have heq : (x⁻¹ * (b : G) * x) * (d : G) * (x⁻¹ * (b : G) * x)⁻¹ =
            x⁻¹ * ((b : G) * (a : G) * (b : G)⁻¹) * x := by
          have hdd' : (d : G) = x⁻¹ * (a : G) * x := hdd
          rw [hdd']; group
        have hgoal : ((b * a * b⁻¹ : ↥C) : G)
            ∈ (D.map C.subtype).map (MulAut.conj x).toMonoidHom := by
          refine (mem_map_conj_iff (H := D.map C.subtype)).mpr ?_
          show x⁻¹ * ((b : G) * (a : G) * (b : G)⁻¹) * x ∈ D.map C.subtype
          rw [← heq]
          exact hG
        exact hgoal
      have hD'pi : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥D') := by
        rw [hcardD']; exact hDpi
      have hD'le : D' ≤ Work.Fitting.pPrimeCore p ↥C :=
        Work.Fitting.le_piCore hD'normal hD'pi
      have hk'C : x * (k : G) * x⁻¹ ∈ C := by
        have h1 : (MulAut.conj x) (k : G) ∈ C.map (MulAut.conj x).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(k : G), k.2, rfl⟩
        have h2 : (MulAut.conj x) (k : G) = x * (k : G) * x⁻¹ := MulAut.conj_apply x k
        rw [h2, hxC] at h1
        exact h1
      let k' : ↥C := ⟨x * (k : G) * x⁻¹, hk'C⟩
      have hk'D' : k' ∈ D' := by
        have h1 : (k' : G) ∈ (D.map C.subtype).map (MulAut.conj x).toMonoidHom := by
          refine (mem_map_conj_iff (H := D.map C.subtype)).mpr ?_
          show x⁻¹ * (x * (k : G) * x⁻¹) * x ∈ D.map C.subtype
          rw [show x⁻¹ * (x * (k : G) * x⁻¹) * x = (k : G) from by group]
          exact Subgroup.mem_map.mpr ⟨k, hkD, rfl⟩
        exact h1
      exact Subgroup.mem_map.mpr ⟨k', hD'le hk'D', rfl⟩
    show (MulAut.conj x) (k : G) ∈ (Work.Fitting.pPrimeCore p ↥C).map C.subtype
    have hgoal : (MulAut.conj x) (k : G) = x * (k : G) * x⁻¹ := MulAut.conj_apply x k
    rw [hgoal]
    exact hmem
  refine le_antisymm hle ?_
  have hcard : Nat.card ↥((pPrimeCoreSub p C).map (MulAut.conj x).toMonoidHom) =
      Nat.card ↥(pPrimeCoreSub p C) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  exact ge_of_eq (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))

/-- If `A` normalises `O`, every element of `O ⊔ A` is a product `o * a`. -/
private lemma mem_mul_of_mem_sup {O A : Subgroup G} (h : A ≤ Subgroup.normalizer (O : Set G)) :
    ∀ x ∈ (O ⊔ A : Subgroup G), x ∈ (O : Set G) * (A : Set G) := by
  have hmul : ∀ {x y : G}, x ∈ (O : Set G) * (A : Set G) →
      y ∈ (O : Set G) * (A : Set G) → x * y ∈ (O : Set G) * (A : Set G) := by
    intro x y hx hy
    rw [Set.mem_mul] at hx hy ⊢
    obtain ⟨o₁, ho₁, a₁, ha₁, rfl⟩ := hx
    obtain ⟨o₂, ho₂, a₂, ha₂, rfl⟩ := hy
    exact ⟨o₁ * (a₁ * o₂ * a₁⁻¹),
      O.mul_mem ho₁ ((Subgroup.le_normalizer_iff.mp h) a₁ ha₁ o₂ ho₂),
      a₁ * a₂, A.mul_mem ha₁ ha₂, by group⟩
  have hone : (1 : G) ∈ (O : Set G) * (A : Set G) :=
    Set.mem_mul.mpr ⟨1, O.one_mem, 1, A.one_mem, one_mul 1⟩
  have hinv : ∀ {x : G}, x ∈ (O : Set G) * (A : Set G) → x⁻¹ ∈ (O : Set G) * (A : Set G) := by
    intro x hx
    rw [Set.mem_mul] at hx ⊢
    obtain ⟨o, ho, a, ha, rfl⟩ := hx
    refine ⟨a⁻¹ * o⁻¹ * a, ?_, a⁻¹, A.inv_mem ha, by group⟩
    simpa using (Subgroup.le_normalizer_iff.mp h) a⁻¹ (A.inv_mem ha) o⁻¹ (O.inv_mem ho)
  let K : Subgroup G :=
    { carrier := (O : Set G) * (A : Set G)
      mul_mem' := fun hx hy => hmul hx hy
      one_mem' := hone
      inv_mem' := fun hx => hinv hx }
  have hsub : O ⊔ A ≤ K := sup_le
    (fun y hy => Set.mem_mul.mpr ⟨y, hy, 1, A.one_mem, mul_one y⟩)
    (fun y hy => Set.mem_mul.mpr ⟨1, O.one_mem, y, hy, one_mul y⟩)
  intro x hx
  exact hsub hx

/-- `V ≤ S` when `S` is a `p`-Sylow of `N_G(V) ⊓ E` and `V ≤ E` is a `p`-group. -/
private lemma le_of_isSylowIn_normalizer {V S E : Subgroup G} (hVE : V ≤ E) (hVp : IsPGroup p V)
    (hS : IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ E)) : V ≤ S := by
  have hVN : V ≤ Subgroup.normalizer (V : Set G) ⊓ E := le_inf Subgroup.le_normalizer hVE
  obtain ⟨Q, hVQ, hQ⟩ := exists_isSylowIn_ge hVN hVp
  obtain ⟨g, hg, hgQ⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hQ hS
  have hVg : V.map (MulAut.conj g).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg.1
  calc V = V.map (MulAut.conj g).toMonoidHom := hVg.symm
    _ ≤ Q.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hVQ
    _ = S := hgQ

end Infra

/-! ## The transfer step -/

section Transfer

variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Conjugation of the whole configuration. -/
private lemma isSylowIn_map_conj_normalizer_inf {V S E : Subgroup G} {g : G} (hgE : g ∈ E)
    (hS : IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ E)) :
    IsSylowIn p (S.map (MulAut.conj g).toMonoidHom)
      (Subgroup.normalizer ((V.map (MulAut.conj g).toMonoidHom) : Subgroup G) ⊓ E) := by
  have h := isSylowIn_map_conj hS g
  rw [Subgroup.map_inf (Subgroup.normalizer (V : Set G)) E (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective,
      Subgroup.map_equiv_normalizer_eq V (MulAut.conj g),
      map_conj_eq_self_of_mem (X := E) hgE] at h
  exact h

/-- A cyclic `p`-Sylow of `N_G(V) ⊓ E` is a `p`-Sylow of `E`. -/
private lemma isSylowIn_of_isCyclic_of_isSylowIn_normalizer {V E S : Subgroup G} (hVE : V ≤ E)
    (hVS : V ≤ S) (hS : IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ E))
    (hcyc : IsCyclic ↥S) : IsSylowIn p S E := by
  have hSE : S ≤ E := hS.2.1.trans inf_le_right
  have hle : Subgroup.normalizer (S : Set G) ⊓ E ≤ Subgroup.normalizer (V : Set G) ⊓ E := by
    intro x hx
    obtain ⟨hxS, hxE⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, hxE⟩
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have hxSmap : S.map (MulAut.conj x).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxS
    have hVx : V.map (MulAut.conj x).toMonoidHom ≤ S := by
      rw [← hxSmap]; exact Subgroup.map_mono hVS
    have huniq : V.subgroupOf S = (V.map (MulAut.conj x).toMonoidHom).subgroupOf S := by
      refine subgroup_eq_of_card_eq_of_isCyclic (H := ↥S) hcyc ?_
      rw [card_subgroupOf_eq V S hVS, card_subgroupOf_eq _ S hVx,
        Subgroup.card_map_of_injective (MulAut.conj x).injective]
    calc V.map (MulAut.conj x).toMonoidHom
        = ((V.map (MulAut.conj x).toMonoidHom).subgroupOf S).map S.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hVx).symm
      _ = (V.subgroupOf S).map S.subtype := by rw [← huniq]
      _ = V := Subgroup.map_subgroupOf_eq_of_le hVS
  have hSsyl : IsSylowIn p S (Subgroup.normalizer (S : Set G) ⊓ E) :=
    isSylowIn_of_le_of_le hS (le_inf Subgroup.le_normalizer hSE) hle
  refine ⟨hS.1, hSE, ?_⟩
  exact not_dvd_index_sylowIn_normalizer hS.1 hSE hSsyl.2.2

/-- Core transfer step: if `S` is a `p`-Sylow of `N_G(V) ⊓ E` and
`N_G(S) ⊓ W = O_{p'}(C_W(S)) ⊔ (N_G(S) ⊓ E)`, then `S` is a `p`-Sylow of `N_G(V) ⊓ W`. -/
private lemma transfer_core {V S E W : Subgroup G} (hEW : E ≤ W) (hVS : V ≤ S)
    (hS : IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ E))
    (hstruct : Subgroup.normalizer (S : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (S : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (S : Set G) ⊓ E)) :
    IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ W) := by
  set NS : Subgroup G := Subgroup.normalizer (S : Set G) with hNS
  set NV : Subgroup G := Subgroup.normalizer (V : Set G) with hNV
  set C : Subgroup G := Subgroup.centralizer (S : Set G) ⊓ W with hC
  set O : Subgroup G := pPrimeCoreSub p C with hO
  set M : Subgroup G := NS ⊓ NV ⊓ E with hM
  set L : Subgroup G := NS ⊓ NV ⊓ W with hL
  have hstruct' : NS ⊓ W = O ⊔ (NS ⊓ E) := hstruct
  have hOnorm : NS ⊓ W ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreSub (normalizer_inf_le_normalizer_centralizer_inf (P := S) (W := W))
  have hONE : NS ⊓ E ≤ Subgroup.normalizer (O : Set G) :=
    (inf_le_inf_left NS hEW).trans hOnorm
  have hCS_NV : Subgroup.centralizer (S : Set G) ≤ NV := by
    rw [hNV]
    exact (Subgroup.centralizer_le (show (V : Set G) ⊆ (S : Set G) from hVS)).trans
      (Subgroup.centralizer_le_normalizer (V : Set G))
  have hCS_NS : Subgroup.centralizer (S : Set G) ≤ NS := by
    rw [hNS]; exact Subgroup.centralizer_le_normalizer (S : Set G)
  have hOC : pPrimeCoreSub p C ≤ C := Subgroup.map_subtype_le _
  have hONV : O ≤ NV := by
    rw [hO]
    exact hOC.trans ((inf_le_left : C ≤ Subgroup.centralizer (S : Set G)).trans hCS_NV)
  have hONS : O ≤ NS := by
    rw [hO]
    exact hOC.trans ((inf_le_left : C ≤ Subgroup.centralizer (S : Set G)).trans hCS_NS)
  have hOW : O ≤ W := by
    rw [hO]
    exact hOC.trans (inf_le_right : C ≤ W)
  have hprod : NS ⊓ W ≤ (O : Set G) * ((NS ⊓ E : Subgroup G) : Set G) := by
    intro y hy
    have hy' : y ∈ O ⊔ (NS ⊓ E) := hstruct' ▸ hy
    exact mem_mul_of_mem_sup (O := O) (A := NS ⊓ E) hONE y hy'
  have hL_eq : L = O ⊔ M := by
    refine le_antisymm ?_ ?_
    · intro y hy
      have hyNSW : y ∈ NS ⊓ W := by rw [hL] at hy; exact ⟨hy.1.1, hy.2⟩
      have hyNV : y ∈ NV := by rw [hL] at hy; exact hy.1.2
      obtain ⟨o, ho, n, hn, hon⟩ := Set.mem_mul.mp (hprod hyNSW)
      have hnNV : n ∈ NV := by
        have h2 : n = o⁻¹ * y := by rw [← hon]; group
        rw [h2]
        exact NV.mul_mem (NV.inv_mem (hONV ho)) hyNV
      have hmM : n ∈ M := by
        rw [hM]; exact ⟨⟨hn.1, hnNV⟩, hn.2⟩
      rw [← hon]
      exact (O ⊔ M).mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hmM)
    · refine sup_le ?_ ?_
      · intro y hy
        rw [hL]
        exact ⟨⟨hONS hy, hONV hy⟩, hOW hy⟩
      · intro y hy
        rw [hM] at hy
        rw [hL]
        exact ⟨⟨hy.1.1, hy.1.2⟩, hEW hy.2⟩
  have hSM : IsSylowIn p S M := by
    refine isSylowIn_of_le_of_le hS ?_ ?_
    · rw [hM]
      exact le_inf (le_inf Subgroup.le_normalizer (hS.2.1.trans inf_le_left))
        (hS.2.1.trans inf_le_right)
    · rw [hM]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hML : M ≤ L := by
    rw [hM, hL]
    exact le_inf inf_le_left (inf_le_right.trans hEW)
  have h1 : Subgroup.normalizer (S : Set G) ⊓ L =
      pPrimeCoreSub p (Subgroup.centralizer (S : Set G) ⊓ L) ⊔
        (Subgroup.normalizer (S : Set G) ⊓ M) := by
    have hleft : Subgroup.normalizer (S : Set G) ⊓ L = L :=
      inf_eq_right.mpr (by rw [hL]; exact le_trans inf_le_left inf_le_left)
    have hcen : Subgroup.centralizer (S : Set G) ⊓ L = C := by
      rw [hC]
      refine le_antisymm ?_ ?_
      · rw [hL]
        exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
      · have hleL : Subgroup.centralizer (S : Set G) ⊓ W ≤ L := by
          rw [hL]
          exact le_inf (le_inf (le_trans inf_le_left hCS_NS) (le_trans inf_le_left hCS_NV))
            inf_le_right
        exact le_inf inf_le_left hleL
    have hrig : Subgroup.normalizer (S : Set G) ⊓ M = M :=
      inf_eq_right.mpr (by rw [hM]; exact le_trans inf_le_left inf_le_left)
    rw [hleft, hcen, hrig, ← hO, hL_eq]
  have hSL : IsSylowIn p S L := isSylowIn_of_sylowIn_normalizer hML hSM h1
  have hSL' : S ≤ NV ⊓ W :=
    hSL.2.1.trans (by rw [hL]; exact le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  refine ⟨hSL.1, hSL', ?_⟩
  refine not_dvd_index_sylowIn_normalizer hSL.1 hSL' ?_
  have hkey : Subgroup.normalizer (S : Set G) ⊓ (NV ⊓ W) = L := by
    rw [hL, hNS, inf_assoc]
  rw [hkey]
  exact hSL.2.2

end Transfer

/-! ## The main theorem -/

theorem sylow_normalizer_transfer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E W : Subgroup G} (hEW : E ≤ W) {P : Subgroup G}
    (hPsyl : Work.NormalComplement.IsSylowIn p P E)
    (h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E))
    (h2 : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E))
    {V S : Subgroup G} (hVE : V ≤ E) (hVp : IsPGroup p V)
    (hS : Work.NormalComplement.IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ E)) :
    Work.NormalComplement.IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ W) := by
  have hVS : V ≤ S := le_of_isSylowIn_normalizer hVE hVp hS
  have key : ∀ g ∈ E, IsSylowIn p (S.map (MulAut.conj g).toMonoidHom)
      (Subgroup.normalizer ((V.map (MulAut.conj g).toMonoidHom) : Subgroup G) ⊓ W) →
      IsSylowIn p S (Subgroup.normalizer (V : Set G) ⊓ W) := by
    intro g hgE hconj
    have hgW : g ∈ W := hEW hgE
    have hgWinv : g⁻¹ ∈ W := W.inv_mem hgW
    have h := isSylowIn_map_conj hconj g⁻¹
    rw [map_conj_inv S g,
        Subgroup.map_inf (Subgroup.normalizer (V.map (MulAut.conj g).toMonoidHom)) W
          (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective,
        Subgroup.map_equiv_normalizer_eq (V.map (MulAut.conj g).toMonoidHom) (MulAut.conj g⁻¹),
        map_conj_inv V g, map_conj_eq_self_of_mem (X := W) hgWinv] at h
    exact h
  by_cases hcyc : IsCyclic ↥S
  · obtain ⟨g, hgE, hgP⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn
      (isSylowIn_of_isCyclic_of_isSylowIn_normalizer hVE hVS hS hcyc) hPsyl
    refine key g hgE ?_
    refine transfer_core hEW (Subgroup.map_mono hVS)
      (isSylowIn_map_conj_normalizer_inf hgE hS) ?_
    rw [hgP]
    exact h1
  · have hSE : S ≤ E := hS.2.1.trans inf_le_right
    obtain ⟨Q, hSQ, hQ⟩ := exists_isSylowIn_ge hSE hS.1
    obtain ⟨g, hgE, hgQ⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hQ hPsyl
    have hle : S.map (MulAut.conj g).toMonoidHom ≤ P := by
      rw [← hgQ]; exact Subgroup.map_mono hSQ
    have hnc : ¬ IsCyclic ↥(S.map (MulAut.conj g).toMonoidHom) :=
      fun h => hcyc ((isCyclic_map_conj_iff S g).mpr h)
    refine key g hgE ?_
    exact transfer_core hEW (Subgroup.map_mono hVS)
      (isSylowIn_map_conj_normalizer_inf hgE hS) (h2 _ hle hnc)

end Work.NormalComplement
