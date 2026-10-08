import Mathlib
import Submission.Work.LEAD.Core27
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.PGroupCentralPrime
import Submission.Work.CORE4.SupProjPrimeOrder
import Submission.Work.CORE4.ConjSub.conjSub_mul
import Submission.Work.CORE4.CopyLocalDiagFixed
import Submission.Work.CORE4.CopyLocalPPart
import Submission.Work.CORE4.CopyLocalCount
import Submission.Work.CORE4._copy_probe

namespace Work.CORE4

open Subgroup

/-- `g` lies in the normaliser of `H` iff `H^g = H` (in the `conjSub` notation). -/
theorem mem_normalizer_conjSub_iff {G : Type*} [Group G] {H : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ Work.GW2.conjSub g H = H := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

/-- **Assembly.**  `CopyLocalProp` from the single-copy `L₂(q)` input `L2pLocalProp` together with
four helper lemmas. -/
theorem main_assembly :
    Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp := by
  intro hL2
  intro G _ _ P0 E0 T0 X1 Y p r e _
  intro hrodd hq5 hiso hpprime hp2 hpr
  intro hPcard hPcent hPdisj hTle hTcard hTcyc hXle hXcard hXneP hXneT
  intro hYcard hYX hnotPY hfour
  classical
  haveI hFp : Fact p.Prime := ⟨hpprime⟩
  have hpodds : Odd p := by
    rcases Nat.Prime.eq_two_or_odd' hpprime with h | h
    · exact absurd h hp2
    · exact h
  -- ### 0. commutation and the diagonal form of X1
  have hcomm : ∀ x ∈ P0, ∀ y ∈ E0, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hPcent hx) y hy).symm
  have hcommT : ∀ x ∈ P0, ∀ y ∈ T0, x * y = y * x := fun x hx y hy => hcomm x hx y (hTle hy)
  have hP0T0 : P0 ⊓ T0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxT⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    have : x ∈ P0 ⊓ E0 := ⟨hxP, hTle hxT⟩
    rwa [hPdisj, Subgroup.mem_bot] at this
  have hX1W : X1 ≤ P0 ⊔ E0 := hXle.trans (sup_le le_sup_left (hTle.trans le_sup_right))
  have hX1CY : X1 ≤ Subgroup.centralizer (Y : Set G) := Subgroup.le_centralizer_iff.mpr hYX
  obtain ⟨x0, hx0ne⟩ : ∃ x : ↥X1, x ≠ 1 := by
    have hnt : Nontrivial ↥X1 := by
      rw [← Finite.one_lt_card_iff_nontrivial, hXcard]; exact hpprime.one_lt
    exact exists_ne (1 : ↥X1)
  have hx0X : (x0 : G) ∈ X1 := x0.2
  have hx0ne' : (x0 : G) ≠ 1 := fun h => hx0ne (Subtype.ext h)
  have hordX0 : orderOf (x0 : G) = p := by
    have hdvd : orderOf (x0 : G) ∣ p := by
      have h := X1.orderOf_dvd_natCard hx0X
      rwa [hXcard] at h
    rcases Nat.Prime.eq_one_or_self_of_dvd hpprime _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx0ne'
    · exact h1
  have hzpX0 : Subgroup.zpowers (x0 : G) = X1 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx0X)
      (by rw [Nat.card_zpowers, hordX0, hXcard])
  obtain ⟨a1, ha1, t1, ht1, hmul⟩ := (mem_sup_iff_exists_mul P0 T0 hcommT (x0 : G)).mp (hXle hx0X)
  have ha1ne : a1 ≠ 1 := by
    intro h
    have hx0T : (x0 : G) ∈ T0 := by rw [← hmul, h, one_mul]; exact ht1
    have : X1 = T0 := Subgroup.eq_of_le_of_card_ge (hzpX0 ▸ Subgroup.zpowers_le.mpr hx0T)
      (by rw [hXcard, hTcard])
    exact hXneT this
  have ht1ne : t1 ≠ 1 := by
    intro h
    have hx0P : (x0 : G) ∈ P0 := by rw [← hmul, h, mul_one]; exact ha1
    have : X1 = P0 := Subgroup.eq_of_le_of_card_ge (hzpX0 ▸ Subgroup.zpowers_le.mpr hx0P)
      (by rw [hXcard, hPcard])
    exact hXneP this
  have hord_t1 : orderOf t1 = p := by
    have hdvd : orderOf t1 ∣ p := by
      have h := T0.orderOf_dvd_natCard ht1
      rwa [hTcard] at h
    exact orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.mp hdvd) ht1ne
  have hord_a1 : orderOf a1 = p := by
    have hdvd : orderOf a1 ∣ p := by
      have h := P0.orderOf_dvd_natCard ha1
      rwa [hPcard] at h
    exact orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.mp hdvd) ha1ne
  have hacent : ∀ x ∈ P0, x * a1 = a1 * x := by
    intro x hx
    have hP0zp : Subgroup.zpowers a1 = P0 :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha1)
        (by rw [Nat.card_zpowers, hord_a1, hPcard])
    rw [← hP0zp] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    rw [show a1 ^ k * a1 = a1 ^ (k + 1) by rw [zpow_add, zpow_one],
      show a1 * a1 ^ k = a1 ^ (1 + k) by rw [zpow_add, zpow_one], add_comm]
  have hct : Commute a1 t1 := hcommT a1 ha1 t1 ht1
  have hzp_t1 : Subgroup.zpowers t1 = T0 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht1)
      (by rw [Nat.card_zpowers, hord_t1, hTcard])
  have hX1zp : Subgroup.zpowers (a1 * t1) = X1 := by rw [hmul]; exact hzpX0
  -- ### 1. the diagonal-normalizer facts
  obtain ⟨hdiag1, hdiag2⟩ :=
    Work.CORE4.CopyLocalDiagFixed P0 E0 hcomm hPdisj ha1 (hTle ht1) hacent hord_a1 hord_t1
  have hdiag1' : ∀ e ∈ E0, e ∈ Subgroup.normalizer (X1 : Set G) ↔
      e ∈ Subgroup.centralizer (T0 : Set G) := by
    intro e he
    have h := hdiag1 e he
    rwa [hzp_t1, hX1zp] at h
  have hdiag2' : Subgroup.normalizer (X1 : Set G) ⊓ (P0 ⊔ E0) ≤
      P0 ⊔ (E0 ⊓ Subgroup.centralizer (T0 : Set G)) := by
    have h := hdiag2
    rwa [hzp_t1, hX1zp] at h
  -- ### 2. D, and the basic facts
  set D : Subgroup G := (P0 ⊔ E0) ⊓ Subgroup.centralizer (Y : Set G) with hDdef
  have hDleW : D ≤ P0 ⊔ E0 := inf_le_left
  have hX1D : X1 ≤ D := fun x hx => ⟨hX1W hx, hX1CY hx⟩
  have hDbot : D ⊓ P0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxP⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    have hordx : orderOf x = p := by
      have hdvd : orderOf x ∣ p := by
        have h := P0.orderOf_dvd_natCard hxP
        rwa [hPcard] at h
      rcases Nat.Prime.eq_one_or_self_of_dvd hpprime _ hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact h1
    have hzp : Subgroup.zpowers x = P0 :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP)
        (by rw [Nat.card_zpowers, hordx, hPcard])
    have hP0CY : P0 ≤ Subgroup.centralizer (Y : Set G) := by
      rw [← hzp]
      exact Subgroup.zpowers_le.mpr hxD.2
    exact hnotPY hP0CY
  have hX1E0 : X1 ⊓ E0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxE⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    obtain ⟨a2, ha2, t2, ht2, hat2⟩ :=
      (mem_sup_iff_exists_mul P0 T0 hcommT x).mp (hXle hxX)
    have ht2E : t2 ∈ E0 := hTle ht2
    have hdec := mul_decomp_unique P0 E0 hcomm hPdisj ha2 (P0.one_mem) ht2E hxE
      (by rw [one_mul, ← hat2])
    have hxT : x ∈ T0 := hdec.2 ▸ ht2
    have hordx : orderOf x = p := by
      have hdvd : orderOf x ∣ p := by
        have h := T0.orderOf_dvd_natCard hxT
        rwa [hTcard] at h
      exact orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.mp hdvd) hxne
    have hX1eqT : X1 = T0 := by
      have h1 : Subgroup.zpowers x = T0 :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxT)
          (by rw [Nat.card_zpowers, hordx, hTcard])
      have h2 : Subgroup.zpowers x = X1 :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
          (by rw [Nat.card_zpowers, hordx, hXcard])
      rw [← h2, h1]
    exact hXneT hX1eqT
  -- ### 3. |P0 ⊔ T0| = p² and D ⊓ (P0 ⊔ T0) = X1
  have hPTnorm : P0 ≤ Subgroup.normalizer (T0 : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      (fun y hy => (hcommT x hx y hy).symm))
  have hcardPT : Nat.card ↥(P0 ⊔ T0) = p ^ 2 := by
    apply le_antisymm
    · have hsurj : Function.Surjective
          (fun z : ↥P0 × ↥T0 =>
            (⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩ : ↥(P0 ⊔ T0))) := by
        rintro ⟨y, hy⟩
        have hy' : y ∈ (↑(P0 ⊔ T0) : Set G) := hy
        rw [Subgroup.coe_mul_of_left_le_normalizer_right P0 T0 hPTnorm] at hy'
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
      have h := Nat.card_le_card_of_surjective _ hsurj
      simpa [Nat.card_prod, hPcard, hTcard, pow_two] using h
    · have hinj : Function.Injective
          (fun z : ↥P0 × ↥T0 =>
            (⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩ : ↥(P0 ⊔ T0))) := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        have hab' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
        obtain ⟨h1, h2⟩ := mul_decomp_unique P0 T0 hcommT hP0T0 a.2 a'.2 b.2 b'.2 hab'
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
      have h := Nat.card_le_card_of_injective _ hinj
      simpa [Nat.card_prod, hPcard, hTcard, pow_two] using h
  have hD_P0T0 : D ⊓ (P0 ⊔ T0) = X1 := by
    have hZcard : Nat.card ↥(D ⊓ (P0 ⊔ T0)) = p := by
      have hdvd2 : Nat.card ↥(D ⊓ (P0 ⊔ T0)) ∣ p ^ 2 := by
        have h1 := Subgroup.card_dvd_of_le (inf_le_right : D ⊓ (P0 ⊔ T0) ≤ P0 ⊔ T0)
        rwa [hcardPT] at h1
      have hdvdp : p ∣ Nat.card ↥(D ⊓ (P0 ⊔ T0)) := by
        have h1 := Subgroup.card_dvd_of_le (le_inf hX1D hXle : X1 ≤ D ⊓ (P0 ⊔ T0))
        rwa [hXcard] at h1
      obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hpprime).mp hdvd2
      rw [hkc]
      interval_cases k
      · exfalso
        rw [pow_zero] at hkc
        rw [hkc] at hdvdp
        exact hpprime.ne_one (Nat.dvd_one.mp hdvdp)
      · rw [pow_one]
      · exfalso
        have hZeq : D ⊓ (P0 ⊔ T0) = P0 ⊔ T0 :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hkc, hcardPT])
        have hP0D : P0 ≤ D := by
          have h1 : P0 ≤ D ⊓ (P0 ⊔ T0) := by rw [hZeq]; exact le_sup_left
          exact h1.trans inf_le_left
        have hbot : P0 = ⊥ := by
          have hle : P0 ≤ D ⊓ P0 := le_inf hP0D le_rfl
          rw [hDbot] at hle
          exact le_bot_iff.mp hle
        have hp1 : p = 1 := by
          have h : Nat.card ↥P0 = 1 := by rw [hbot, Subgroup.card_bot]
          rwa [hPcard] at h
        exact hpprime.ne_one hp1
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hX1D hXle) (by rw [hZcard, hXcard])).symm
  -- ### 4. the projection to E0 and the "shadow" of a subgroup
  obtain ⟨proj, hproj⟩ := ProjOfInfBot P0 E0 hcomm hPdisj
  let φ : ↥(P0 ⊔ E0) →* G := E0.subtype.comp proj
  have hφE : ∀ w : ↥(P0 ⊔ E0), φ w ∈ E0 := fun w => (proj w).2
  have hφ : ∀ (a : G) (ha : a ∈ P0) (e : G) (he : e ∈ E0),
      φ ⟨a * e, Subgroup.mul_mem_sup ha he⟩ = e := by
    intro a ha e he
    show (E0.subtype (proj ⟨a * e, Subgroup.mul_mem_sup ha he⟩) : G) = e
    rw [hproj a ha e he]
    rfl
  have hφE0 : ∀ (e : G) (he : e ∈ E0), φ ⟨e, (le_sup_right : E0 ≤ P0 ⊔ E0) he⟩ = e := by
    intro e he
    have h := hφ 1 (P0.one_mem) e he
    have h2 : (⟨1 * e, Subgroup.mul_mem_sup (P0.one_mem) he⟩ : ↥(P0 ⊔ E0)) =
        ⟨e, (le_sup_right : E0 ≤ P0 ⊔ E0) he⟩ := Subtype.ext (one_mul e)
    rwa [h2] at h
  set sh : Subgroup G → Subgroup G := (fun A => (A.subgroupOf (P0 ⊔ E0)).map φ) with hshdef
  have mem_sh : ∀ {A : Subgroup G} {y : G}, y ∈ sh A ↔
      ∃ x : ↥(P0 ⊔ E0), (x : G) ∈ A ∧ φ x = y := by
    intro A y
    rw [hshdef, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩; exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩; exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, hxy⟩
  have sh_mono : ∀ {A B : Subgroup G}, A ≤ B → sh A ≤ sh B := by
    intro A B hAB
    rw [hshdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono (P0 ⊔ E0) hAB)
  have sh_le : ∀ A : Subgroup G, sh A ≤ E0 := by
    intro A y hy
    rw [hshdef] at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact hφE x
  have sh_X1 : sh X1 = T0 := by
    apply le_antisymm
    · intro y hy
      rw [mem_sh] at hy
      obtain ⟨x, hxX, rfl⟩ := hy
      have hxzp : (x : G) ∈ Subgroup.zpowers (a1 * t1) := hX1zp ▸ hxX
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxzp
      have hxval : φ x = t1 ^ k := by
        have hxe : x = ⟨a1 ^ k * t1 ^ k, Subgroup.mul_mem_sup (P0.zpow_mem ha1 k)
            (hTle (T0.zpow_mem ht1 k))⟩ := by
          apply Subtype.ext
          show (x : G) = a1 ^ k * t1 ^ k
          rw [← hk, ← hct.mul_zpow]
        rw [hxe]
        exact hφ _ (P0.zpow_mem ha1 k) _ (hTle (T0.zpow_mem ht1 k))
      rw [hxval]
      exact T0.zpow_mem ht1 k
    · intro t ht
      have ht' : t ∈ Subgroup.zpowers t1 := hzp_t1 ▸ ht
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht'
      rw [mem_sh]
      refine ⟨⟨a1 ^ k * t1 ^ k, Subgroup.mul_mem_sup (P0.zpow_mem ha1 k)
          (hTle (T0.zpow_mem ht1 k))⟩, ?_, ?_⟩
      · show a1 ^ k * t1 ^ k ∈ X1
        rw [← hX1zp, ← hct.mul_zpow]
        exact Subgroup.zpow_mem (Subgroup.zpowers (a1 * t1)) (Subgroup.mem_zpowers (a1 * t1)) k
      · show φ ⟨a1 ^ k * t1 ^ k, Subgroup.mul_mem_sup (P0.zpow_mem ha1 k)
            (hTle (T0.zpow_mem ht1 k))⟩ = t
        rw [← hk]
        exact hφ _ (P0.zpow_mem ha1 k) _ (hTle (T0.zpow_mem ht1 k))
  have hT0Hs : T0 ≤ sh D := by rw [← sh_X1]; exact sh_mono hX1D
  -- conjugation compatibility of `sh`
  have sh_conj : ∀ (A : Subgroup G), A ≤ P0 ⊔ E0 → ∀ g : ↥(P0 ⊔ E0),
      sh (Work.GW2.conjSub (g : G) A) = Work.GW2.conjSub (φ g) (sh A) := by
    intro A hA g
    ext z
    rw [mem_sh, Work.CORE4.ConjSub.mem_conjSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Work.CORE4.ConjSub.mem_conjSub] at hx
      obtain ⟨k, hkA, hkx⟩ := hx
      refine ⟨φ ⟨k, hA hkA⟩, mem_sh.mpr ⟨⟨k, hA hkA⟩, hkA, rfl⟩, ?_⟩
      have hxW : (x : ↥(P0 ⊔ E0)) = g * ⟨k, hA hkA⟩ * g⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hkx.symm
      have hxx : φ x = φ g * φ ⟨k, hA hkA⟩ * (φ g)⁻¹ := by
        rw [hxW]
        simp only [map_mul, map_inv]
      rw [← hxx]
    · rintro ⟨y, hy, hyz⟩
      rw [mem_sh] at hy
      obtain ⟨k, hkA, hky⟩ := hy
      refine ⟨g * k * g⁻¹, ?_, ?_⟩
      · rw [Work.CORE4.ConjSub.mem_conjSub]
        refine ⟨(k : G), hkA, ?_⟩
        show (g : G) * (k : G) * (g : G)⁻¹ = ((g * k * g⁻¹ : ↥(P0 ⊔ E0)) : G)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      · have hxx : φ (g * k * g⁻¹) = φ g * φ k * (φ g)⁻¹ := by
          simp only [map_mul, map_inv]
        rw [hxx, hky]
        exact hyz
  -- ### 5. auxiliary facts about `sh`
  have hkerφ : ∀ w : ↥(P0 ⊔ E0), φ w = 1 → (w : G) ∈ P0 := by
    intro w hw
    obtain ⟨a, ha, e, he, hae⟩ := (mem_sup_iff_exists_mul P0 E0 hcomm (w : G)).mp w.2
    have hprojx : (proj w : G) = e := by
      have hwe : w = ⟨a * e, Subgroup.mul_mem_sup ha he⟩ := Subtype.ext hae.symm
      rw [hwe]; exact congrArg Subtype.val (hproj a ha e he)
    have h1 : (proj w : G) = 1 := by
      show (E0.subtype (proj w) : G) = 1
      simpa only [φ, MonoidHom.comp_apply] using hw
    rw [hprojx] at h1
    rw [← hae, h1, mul_one]
    exact ha
  have hcard_sh : ∀ Z : Subgroup G, Z ≤ D → Nat.card ↥Z = p → Nat.card ↥(sh Z) = p := by
    intro Z hZD hZc
    rw [hshdef, card_map_subgroupOf_eq (hZD.trans hDleW) φ]
    · exact hZc
    · rintro ⟨x, hx⟩ hx1
      apply Subtype.ext
      apply Subtype.ext
      have hxP : (x : G) ∈ P0 := hkerφ x hx1
      have hxZ : (x : G) ∈ Z := Subgroup.mem_subgroupOf.mp hx
      have hZbot : Z ⊓ P0 = ⊥ := by
        have h1 : Z ⊓ P0 ≤ D ⊓ P0 := le_inf (inf_le_left.trans hZD) inf_le_right
        rw [hDbot] at h1
        exact le_bot_iff.mp h1
      have hx2 : (x : G) ∈ Z ⊓ P0 := ⟨hxZ, hxP⟩
      rw [hZbot, Subgroup.mem_bot] at hx2
      exact hx2
  have hcardHs : Nat.card ↥(sh D) = Nat.card ↥D := by
    rw [hshdef, card_map_subgroupOf_eq hDleW φ]
    rintro ⟨x, hx⟩ hx1
    apply Subtype.ext
    apply Subtype.ext
    have hxP : (x : G) ∈ P0 := hkerφ x hx1
    have hx2 : (x : G) ∈ D ⊓ P0 := ⟨Subgroup.mem_subgroupOf.mp hx, hxP⟩
    rw [hDbot, Subgroup.mem_bot] at hx2
    exact hx2
  have hZ_le_sup : ∀ Z : Subgroup G, Z ≤ D → Z ≤ P0 ⊔ sh Z := by
    intro Z hZD z hz
    obtain ⟨a, ha, e, he, hae⟩ := (mem_sup_iff_exists_mul P0 E0 hcomm z).mp (hZD hz).1
    have hzsh : φ ⟨z, (hZD hz).1⟩ ∈ sh Z :=
      mem_sh.mpr ⟨⟨z, (hZD hz).1⟩, hz, rfl⟩
    have heφ : e = φ ⟨z, (hZD hz).1⟩ := by
      have hze : (⟨z, (hZD hz).1⟩ : ↥(P0 ⊔ E0)) = ⟨a * e, Subgroup.mul_mem_sup ha he⟩ :=
        Subtype.ext hae.symm
      rw [hze, hφ a ha e he]
    rw [← hae, heφ]
    exact Subgroup.mul_mem_sup ha hzsh
  have hD_inf : ∀ Z : Subgroup G, Z ≤ D → Nat.card ↥Z = p → D ⊓ (P0 ⊔ sh Z) = Z := by
    intro Z hZD hZc
    have hZbE : sh Z ≤ E0 := sh_le Z
    have hcommZ : ∀ x ∈ P0, ∀ y ∈ sh Z, x * y = y * x := fun x hx y hy => hcomm x hx y (hZbE hy)
    have hinfZ : P0 ⊓ sh Z = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      obtain ⟨hxP, hxZ⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_bot]
      have : x ∈ P0 ⊓ E0 := ⟨hxP, hZbE hxZ⟩
      rwa [hPdisj, Subgroup.mem_bot] at this
    obtain ⟨projZ, hprojZ⟩ := ProjOfInfBot P0 (sh Z) hcommZ hinfZ
    have hkerZ : ∀ w : ↥(P0 ⊔ sh Z), projZ w = 1 → (w : G) ∈ P0 := by
      intro w hw
      obtain ⟨a, ha, e, he, hae⟩ := (mem_sup_iff_exists_mul P0 (sh Z) hcommZ w).mp w.2
      have hwe : w = ⟨a * e, Subgroup.mul_mem_sup ha he⟩ := Subtype.ext hae.symm
      have h1 : (⟨e, he⟩ : ↥(sh Z)) = 1 := by
        rw [← hprojZ a ha e he, ← hwe]; exact hw
      have he1 : e = 1 := congrArg Subtype.val h1
      rw [← hae, he1, mul_one]; exact ha
    have hcardle : Nat.card ↥(D ⊓ (P0 ⊔ sh Z)) ≤ p := by
      have hinj : Function.Injective (fun w : ↥(D ⊓ (P0 ⊔ sh Z)) =>
          projZ ⟨(w : G), (Subgroup.mem_inf.mp w.2).2⟩) := by
        intro w1 w2 h
        have hmem : ((w1 : G) * (w2 : G)⁻¹) ∈ D ⊓ (P0 ⊔ sh Z) :=
          ⟨D.mul_mem (Subgroup.mem_inf.mp w1.2).1 (D.inv_mem (Subgroup.mem_inf.mp w2.2).1),
           (P0 ⊔ sh Z).mul_mem (Subgroup.mem_inf.mp w1.2).2
            ((P0 ⊔ sh Z).inv_mem (Subgroup.mem_inf.mp w2.2).2)⟩
        have hzero : projZ ⟨(w1 : G) * (w2 : G)⁻¹, hmem.2⟩ = 1 := by
          have h1 : (⟨(w1 : G) * (w2 : G)⁻¹, hmem.2⟩ : ↥(P0 ⊔ sh Z)) =
              ⟨(w1 : G), (Subgroup.mem_inf.mp w1.2).2⟩ *
                ⟨(w2 : G), (Subgroup.mem_inf.mp w2.2).2⟩⁻¹ := by
            apply Subtype.ext
            rw [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [h1, map_mul, map_inv]
          rw [show projZ ⟨(w1 : G), (Subgroup.mem_inf.mp w1.2).2⟩ =
              projZ ⟨(w2 : G), (Subgroup.mem_inf.mp w2.2).2⟩ from h, mul_inv_cancel]
        have hP : (w1 : G) * (w2 : G)⁻¹ ∈ P0 := hkerZ _ hzero
        have hmem2 : (w1 : G) * (w2 : G)⁻¹ ∈ D ⊓ P0 := ⟨hmem.1, hP⟩
        rw [hDbot, Subgroup.mem_bot] at hmem2
        exact Subtype.ext (mul_inv_eq_one.mp hmem2)
      have hc := Nat.card_le_card_of_injective _ hinj
      rwa [hcard_sh Z hZD hZc] at hc
    have hcardH : Nat.card ↥(D ⊓ (P0 ⊔ sh Z)) = p := by
      refine le_antisymm hcardle ?_
      have h2 : Nat.card ↥Z ≤ Nat.card ↥(D ⊓ (P0 ⊔ sh Z)) :=
        Nat.card_le_card_of_injective _
          (Subgroup.inclusion_injective (le_inf hZD (hZ_le_sup Z hZD)))
      rwa [hZc] at h2
    have hHeq : Z = D ⊓ (P0 ⊔ sh Z) :=
      Subgroup.eq_of_le_of_card_ge (le_inf hZD (hZ_le_sup Z hZD)) (by rw [hcardH, hZc])
    rw [← hHeq]
  have hsh_inj : ∀ Z1 Z2 : Subgroup G, Z1 ≤ D → Z2 ≤ D → Nat.card ↥Z1 = p → Nat.card ↥Z2 = p →
      sh Z1 = sh Z2 → Z1 = Z2 := by
    intro Z1 Z2 hZ1D hZ2D hZ1c hZ2c hsh
    have hZ2le : Z2 ≤ P0 ⊔ sh Z1 := (hZ_le_sup Z2 hZ2D).trans (by rw [hsh])
    have hZ2H : Z2 ≤ D ⊓ (P0 ⊔ sh Z1) := le_inf hZ2D hZ2le
    rw [hD_inf Z1 hZ1D hZ1c] at hZ2H
    have hZ1le : Z1 ≤ P0 ⊔ sh Z2 := (hZ_le_sup Z1 hZ1D).trans (by rw [hsh])
    have hZ1H : Z1 ≤ D ⊓ (P0 ⊔ sh Z2) := le_inf hZ1D hZ1le
    rw [hD_inf Z2 hZ2D hZ2c] at hZ1H
    exact le_antisymm hZ1H hZ2H
  -- ### 6. sh D ⊓ N(T0) ≤ C(T0)
  have hHsCent : sh D ⊓ Subgroup.normalizer (T0 : Set G) ≤ Subgroup.centralizer (T0 : Set G) := by
    intro y hy
    obtain ⟨hyHs, hyN⟩ := Subgroup.mem_inf.mp hy
    rw [mem_sh] at hyHs
    obtain ⟨dd, hddD, hddy⟩ := hyHs
    have hdN : (dd : G) ∈ Subgroup.normalizer (X1 : Set G) := by
      rw [mem_normalizer_conjSub_iff]
      have hconjD : Work.GW2.conjSub (dd : G) X1 ≤ D := by
        rw [Work.GW2.conjSub]
        refine (Subgroup.map_mono (hX1D : X1 ≤ D)).trans ?_
        rw [← Work.GW2.conjSub]
        rw [mem_normalizer_conjSub_iff.mp (mem_normalizer_conjSub_iff.mpr (by
          ext z
          rw [Work.CORE4.ConjSub.mem_conjSub]
          constructor
          · rintro ⟨k, hk, rfl⟩
            exact D.mul_mem (D.mul_mem hddD hk) (D.inv_mem hddD)
          · intro hz
            exact ⟨(dd : G)⁻¹ * z * (dd : G),
              D.mul_mem (D.mul_mem (D.inv_mem hddD) hz) hddD, by group⟩))]
      have hcardconj : Nat.card ↥(Work.GW2.conjSub (dd : G) X1) = p := by
        rw [Work.GW2.conjSub,
          Subgroup.card_map_of_injective (MulAut.conj (dd : G)).injective, hXcard]
      have hshconj : sh (Work.GW2.conjSub (dd : G) X1) = sh X1 := by
        rw [sh_conj X1 hX1W dd, hddy, sh_X1]
        exact mem_normalizer_conjSub_iff.mp hyN
      exact hsh_inj (Work.GW2.conjSub (dd : G) X1) X1 hconjD hX1D hcardconj hXcard hshconj
    have hdM : (dd : G) ∈ P0 ⊔ (E0 ⊓ Subgroup.centralizer (T0 : Set G)) :=
      hdiag2' ⟨hdN, dd.2⟩
    obtain ⟨a3, ha3, c3, hc3, hac3⟩ :=
      (mem_sup_iff_exists_mul P0 (E0 ⊓ Subgroup.centralizer (T0 : Set G))
        (fun x hx y hy => hcomm x hx y (Subgroup.mem_inf.mp hy).1) (dd : G)).mp hdM
    have hyc : y = c3 := by
      have hxe : (dd : ↥(P0 ⊔ E0)) =
          ⟨a3 * c3, Subgroup.mul_mem_sup ha3 (Subgroup.mem_inf.mp hc3).1⟩ :=
        Subtype.ext hac3.symm
      rw [← hddy, hxe]
      exact hφ a3 ha3 c3 (Subgroup.mem_inf.mp hc3).1
    rw [hyc]
    exact (Subgroup.mem_inf.mp hc3).2
  -- ### 7. elements of sh D of order coprime to p lie in D
  have hcopl : ∀ x : G, x ∈ sh D → Nat.Coprime (orderOf x) p → x ∈ D := by
    intro x hxH hcop
    have hxE : x ∈ E0 := sh_le D hxH
    rw [mem_sh] at hxH
    obtain ⟨dd, hddD, hdφ⟩ := hxH
    obtain ⟨a, ha, e, he, hae⟩ := (mem_sup_iff_exists_mul P0 E0 hcomm dd).mp dd.2
    have heφ : e = x := by
      have hdde : (dd : ↥(P0 ⊔ E0)) = ⟨a * e, Subgroup.mul_mem_sup ha he⟩ :=
        Subtype.ext hae.symm
      rw [← hdφ, hdde, hφ a ha e he]
    have hdd_eq : (dd : G) = a * x := by rw [← hae, heφ]
    have hcommax : a * x = x * a := hcomm a ha x hxE
    have hpowa : ((dd : G) ^ orderOf x) = a ^ orderOf x := by
      rw [hdd_eq, (show Commute a x from hcommax).mul_pow, pow_orderOf_eq_one, mul_one]
    have hmemD : ((dd : G) ^ orderOf x) ∈ D := D.pow_mem hddD (orderOf x)
    have haP : a ^ orderOf x ∈ P0 := P0.pow_mem ha (orderOf x)
    have habot : a ^ orderOf x ∈ D ⊓ P0 := ⟨by rw [← hpowa]; exact hmemD, haP⟩
    rw [hDbot, Subgroup.mem_bot] at habot
    have hdvd1 : orderOf a ∣ p := by
      have h := P0.orderOf_dvd_natCard ha
      rwa [hPcard] at h
    have hdvd2 : orderOf a ∣ orderOf x := orderOf_dvd_iff_pow_eq_one.mpr habot
    have h1 : orderOf a = 1 := (hcop.coprime_dvd_right hdvd1).symm.eq_one_of_dvd hdvd2
    have ha1 : a = 1 := orderOf_eq_one_iff.mp h1
    rw [ha1, one_mul] at hdd_eq
    rw [← hdd_eq]; exact hddD
  -- ### 8. IsCyclic of D ⊓ N(X1), and ¬ p² ∣ |D|
  have hcyc : IsCyclic ↥(D ⊓ Subgroup.normalizer (X1 : Set G)) := by
    haveI hcycT : IsCyclic ↥(E0 ⊓ Subgroup.centralizer (T0 : Set G)) := hTcyc
    have hle2 : (P0 ⊔ E0) ⊓ Subgroup.normalizer (X1 : Set G) ≤
        P0 ⊔ (E0 ⊓ Subgroup.centralizer (T0 : Set G)) := by
      rw [inf_comm]; exact hdiag2'
    have hle : D ⊓ Subgroup.normalizer (X1 : Set G) ≤
        P0 ⊔ (E0 ⊓ Subgroup.centralizer (T0 : Set G)) :=
      (inf_le_inf hDleW le_rfl).trans hle2
    have hcommN : ∀ x ∈ P0, ∀ y ∈ (E0 ⊓ Subgroup.centralizer (T0 : Set G)), x * y = y * x :=
      fun x hx y hy => hcomm x hx y (Subgroup.mem_inf.mp hy).1
    have hinfN : P0 ⊓ (E0 ⊓ Subgroup.centralizer (T0 : Set G)) = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      obtain ⟨hxP, hxEC⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_bot]
      have : x ∈ P0 ⊓ E0 := ⟨hxP, (Subgroup.mem_inf.mp hxEC).1⟩
      rwa [hPdisj, Subgroup.mem_bot] at this
    obtain ⟨projN, hprojN⟩ := ProjOfInfBot P0 (E0 ⊓ Subgroup.centralizer (T0 : Set G)) hcommN hinfN
    have hker : ∀ w : ↥(D ⊓ Subgroup.normalizer (X1 : Set G)),
        projN (Subgroup.inclusion hle w) = 1 → w = 1 := by
      intro w hw
      obtain ⟨a, ha, n, hn, han⟩ :=
        (mem_sup_iff_exists_mul P0 (E0 ⊓ Subgroup.centralizer (T0 : Set G)) hcommN (w : G)).mp
          (hle w.2)
      have hwe : (Subgroup.inclusion hle w : ↥(P0 ⊔ (E0 ⊓ Subgroup.centralizer (T0 : Set G)))) =
          ⟨a * n, Subgroup.mul_mem_sup ha hn⟩ := Subtype.ext han.symm
      have hn1 : (⟨n, hn⟩ : ↥(E0 ⊓ Subgroup.centralizer (T0 : Set G))) = 1 := by
        rw [← hprojN a ha n hn, ← hwe]; exact hw
      have hn1val : n = 1 := congrArg Subtype.val hn1
      have hwn : (w : G) = a := by rw [← han, hn1val, mul_one]
      have hwP : (w : G) ∈ P0 := hwn ▸ ha
      have hmem : (w : G) ∈ D ⊓ P0 := ⟨(Subgroup.mem_inf.mp w.2).1, hwP⟩
      rw [hDbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hinj : Function.Injective (projN.comp (Subgroup.inclusion hle)) := by
      intro w1 w2 h
      have h1 : (projN.comp (Subgroup.inclusion hle)) (w1 * w2⁻¹) = 1 := by
        rw [map_mul, map_inv, h, mul_inv_cancel]
      have h2 := hker (w1 * w2⁻¹) h1
      exact mul_inv_eq_one.mp h2
    exact isCyclic_of_injective _ hinj
  have hNormP : ∀ {Y P' : Subgroup G}, Nat.card Y = p → Nat.card P' = p →
      Y ≤ Subgroup.normalizer (P' : Set G) → P' ≤ Subgroup.centralizer (Y : Set G) := by
    intro Y P' hYc hP'c hYN
    have hdvd : p ∣ Nat.card ↥(P' ⊓ Subgroup.centralizer (Y : Set G)) :=
      Work.CORE4.PGroupActionCentralizer hpprime hYN hYc (by rw [hP'c])
    have hdvd' : Nat.card ↥(P' ⊓ Subgroup.centralizer (Y : Set G)) ∣ p := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : P' ⊓ Subgroup.centralizer (Y : Set G) ≤ P')
      rwa [hP'c] at h
    rcases (Nat.dvd_prime hpprime).mp hdvd' with h1 | h1
    · rw [h1] at hdvd
      exact absurd (Nat.dvd_one.mp hdvd) hpprime.ne_one
    · have heq : P' ⊓ Subgroup.centralizer (Y : Set G) = P' :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hP'c])
      exact heq ▸ inf_le_right
  have hP2notD : ¬ p ^ 2 ∣ Nat.card ↥D :=
    Work.CORE4.CopyLocalPPart hpprime hcomm hPdisj hDleW hDbot hPcard hXcard hX1D hX1E0 hcyc
  have hP2notHs : ¬ p ^ 2 ∣ Nat.card ↥(sh D) := by rw [hcardHs]; exact hP2notD
  -- ### 9. apply L2pLocalProp
  rcases hL2 G E0 r e hrodd hq5 hiso p hpprime hp2 hpr T0 (sh D) hT0Hs (sh_le D) hTcard
      hP2notHs hHsCent with hcase1 | hcase2 | hcase3
  · -- case 1: T0 is the only order-p subgroup of sh D
    left
    ext Z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hZD, hZc⟩
      have hshZcard : Nat.card ↥(sh Z) = p := hcard_sh Z hZD hZc
      refine hsh_inj Z X1 hZD hX1D hZc hXcard ?_
      rw [hcase1 (sh Z) (sh_mono hZD) hshZcard, sh_X1]
    · rintro rfl
      exact ⟨hX1D, hXcard⟩
  · -- case 2: a four-group inside sh D is impossible
    obtain ⟨V, hVH, hV4⟩ := hcase2
    exfalso
    have hVD : V ≤ D := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]; exact D.one_mem
      · have hord : orderOf v = 2 := orderOf_eq_prime (hV4.2 v hv) hv1
        have hcop : Nat.Coprime (orderOf v) p := by
          rw [hord]
          exact Nat.coprime_two_left.mpr hpodds
        exact hcopl v (hVH hv) hcop
    have hYCV : Y ≤ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      exact hVD.trans inf_le_right
    have hYNP : Y ≤ Subgroup.normalizer (P0 : Set G) :=
      hfour V (hVH.trans (sh_le D)) hV4 hYCV
    exact hnotPY (hNormP hYcard hPcard hYNP)
  · -- case 3: the R-case
    obtain ⟨R, hRE, hRcard, hTR, hcl⟩ := hcase3
    have hKodd : Odd (Nat.card ↥(R ⊓ sh D)) := by
      have hdiv : Nat.card ↥(R ⊓ sh D) ∣ r ^ e := by
        have h1 : Nat.card ↥(R ⊓ sh D) ∣ Nat.card ↥R := Subgroup.card_dvd_of_le inf_le_left
        rwa [hRcard] at h1
      obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).mp hdiv
      rw [hkc]
      exact Odd.pow (a := r) (n := k) hrodd
    have hcl2 : ∀ Z : Subgroup G, Z ≤ D → Nat.card ↥Z = p →
        ∃ c ∈ R ⊓ sh D, Z = Work.GW2.conjSub c X1 := by
      intro Z hZD hZc
      have hshZcard : Nat.card ↥(sh Z) = p := hcard_sh Z hZD hZc
      obtain ⟨c, hc, hccl⟩ := hcl (sh Z) (sh_mono hZD) hshZcard
      obtain ⟨hcR, hcH⟩ := Subgroup.mem_inf.mp hc
      have hccard : orderOf c ∣ r ^ e := by
        have h1 : orderOf c ∣ Nat.card ↥(R ⊓ sh D) :=
          (R ⊓ sh D).orderOf_dvd_natCard (⟨hcR, hcH⟩ : c ∈ R ⊓ sh D)
        have h2 : Nat.card ↥(R ⊓ sh D) ∣ Nat.card ↥R := Subgroup.card_dvd_of_le inf_le_left
        exact h1.trans (h2.trans ⟨1, by rw [hRcard, mul_one]⟩)
      have hccop : Nat.Coprime (orderOf c) p := by
        have hrp : Nat.Coprime r p := by
          rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)]
          intro hdvd
          rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
          · exact (Fact.out : r.Prime).ne_one h
          · exact hpr h.symm
        exact (hrp.pow_left e).coprime_dvd_left hccard
      have hcD : c ∈ D := hcopl c hcH hccop
      have hconjD : Work.GW2.conjSub c X1 ≤ D := by
        rw [Work.GW2.conjSub]
        refine (Subgroup.map_mono (hX1D : X1 ≤ D)).trans ?_
        rw [← Work.GW2.conjSub]
        have hDc : Work.GW2.conjSub c D = D := by
          ext z
          rw [Work.CORE4.ConjSub.mem_conjSub]
          constructor
          · rintro ⟨k, hk, rfl⟩
            exact D.mul_mem (D.mul_mem hcD hk) (D.inv_mem hcD)
          · intro hz
            exact ⟨c⁻¹ * z * c, D.mul_mem (D.mul_mem (D.inv_mem hcD) hz) hcD, by group⟩
        rw [hDc]
      have hconjcard : Nat.card ↥(Work.GW2.conjSub c X1) = p := by
        rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj c).injective, hXcard]
      have hshconj : sh (Work.GW2.conjSub c X1) = sh Z := by
        have hcE : c ∈ E0 := sh_le D hcH
        have hcW : c ∈ P0 ⊔ E0 := (le_sup_right : E0 ≤ P0 ⊔ E0) hcE
        rw [sh_conj X1 hX1W ⟨c, hcW⟩, hφE0 c hcE, sh_X1, hccl]
      exact ⟨c, ⟨hcR, hcH⟩,
        (hsh_inj (Work.GW2.conjSub c X1) Z hconjD hZD hconjcard hZc hshconj).symm⟩
    have hSeq : {Z : Subgroup G | Z ≤ D ∧ Nat.card Z = p} =
        {Z : Subgroup G | ∃ c ∈ R ⊓ sh D, Z = Work.GW2.conjSub c X1} := by
      ext Z
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hZD, hZc⟩
        exact hcl2 Z hZD hZc
      · rintro ⟨c, hcK, rfl⟩
        obtain ⟨hcR, hcH⟩ := Subgroup.mem_inf.mp hcK
        have hccard : orderOf c ∣ r ^ e := by
          have h1 : orderOf c ∣ Nat.card ↥(R ⊓ sh D) :=
            (R ⊓ sh D).orderOf_dvd_natCard (hcK : c ∈ R ⊓ sh D)
          have h2 : Nat.card ↥(R ⊓ sh D) ∣ Nat.card ↥R := Subgroup.card_dvd_of_le inf_le_left
          exact h1.trans (h2.trans ⟨1, by rw [hRcard, mul_one]⟩)
        have hccop : Nat.Coprime (orderOf c) p := by
          have hrp : Nat.Coprime r p := by
            rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)]
            intro hdvd
            rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
            · exact (Fact.out : r.Prime).ne_one h
            · exact hpr h.symm
          exact (hrp.pow_left e).coprime_dvd_left hccard
        have hcD : c ∈ D := hcopl c hcH hccop
        refine ⟨?_, ?_⟩
        · rw [Work.GW2.conjSub]
          refine (Subgroup.map_mono (hX1D : X1 ≤ D)).trans ?_
          rw [← Work.GW2.conjSub]
          have hDc : Work.GW2.conjSub c D = D := by
            ext z
            rw [Work.CORE4.ConjSub.mem_conjSub]
            constructor
            · rintro ⟨k, hk, rfl⟩
              exact D.mul_mem (D.mul_mem hcD hk) (D.inv_mem hcD)
            · intro hz
              exact ⟨c⁻¹ * z * c, D.mul_mem (D.mul_mem (D.inv_mem hcD) hz) hcD, by group⟩
          rw [hDc]
        · rw [Work.GW2.conjSub,
            Subgroup.card_map_of_injective (MulAut.conj c).injective, hXcard]
    refine Or.inr ⟨R, hRE, hRcard, hTR, ?_, ?_, ?_⟩
    · intro Z hZD hZc
      obtain ⟨c, hc, hcZ⟩ := hcl2 Z hZD hZc
      exact ⟨c, (Subgroup.mem_inf.mp hc).1, hcZ⟩
    · exact Work.CORE4.CopyLocalCount hpprime hpodds hXcard hX1D (R ⊓ sh D) hKodd hSeq (by
        intro Z hZD hZc hX1N
        have hcX1Z : Z ≤ Subgroup.centralizer (X1 : Set G) :=
          hNormP hXcard hZc hX1N
        have hshZ_le : sh Z ≤ E0 ⊓ Subgroup.centralizer (T0 : Set G) := by
          refine le_inf (sh_le Z) ?_
          intro y hy
          rw [mem_sh] at hy
          obtain ⟨z, hzZ, hzφ⟩ := hy
          have hzW : (z : G) ∈ P0 ⊔ E0 := (hZD hzZ).1
          have hx1W : a1 * t1 ∈ P0 ⊔ E0 := Subgroup.mul_mem_sup ha1 (hTle ht1)
          have hmem1 : a1 * t1 ∈ X1 := hX1zp ▸ Subgroup.mem_zpowers _
          have hcomm1 : (a1 * t1) * z = z * (a1 * t1) :=
            Subgroup.mem_centralizer_iff.mp (hcX1Z hzZ) (a1 * t1) hmem1
          have hzw : (⟨a1 * t1, Subgroup.mul_mem_sup ha1 (hTle ht1)⟩ : ↥(P0 ⊔ E0)) *
              ⟨z, hzW⟩ = ⟨z, hzW⟩ * ⟨a1 * t1, Subgroup.mul_mem_sup ha1 (hTle ht1)⟩ :=
            Subtype.ext hcomm1
          have hyt1 : t1 * y = y * t1 := by
            have h1 : φ (⟨a1 * t1, Subgroup.mul_mem_sup ha1 (hTle ht1)⟩ * ⟨z, hzW⟩) =
                φ (⟨z, hzW⟩ * ⟨a1 * t1, Subgroup.mul_mem_sup ha1 (hTle ht1)⟩) := congrArg φ hzw
            simp only [map_mul] at h1
            rw [hφ a1 ha1 t1 (hTle ht1), hzφ] at h1
            exact h1
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [← hzp_t1] at hw
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
          rw [← hk]
          exact ((show Commute y t1 from hyt1.symm).zpow_right k).symm
        haveI : IsCyclic ↥(E0 ⊓ Subgroup.centralizer (T0 : Set G)) := hTcyc
        have hT0C : T0 ≤ Subgroup.centralizer (T0 : Set G) := by
          intro x hx
          rw [← hzp_t1] at hx
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [← hzp_t1] at hy
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
          rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
        have hT0le : T0 ≤ E0 ⊓ Subgroup.centralizer (T0 : Set G) := le_inf hTle hT0C
        have hcard1 : Nat.card ↥((sh Z).subgroupOf (E0 ⊓ Subgroup.centralizer (T0 : Set G))) = p := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hshZ_le).toEquiv]
          exact hcard_sh Z hZD hZc
        have hcard2 : Nat.card ↥(T0.subgroupOf (E0 ⊓ Subgroup.centralizer (T0 : Set G))) = p := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT0le).toEquiv, hTcard]
        have heq : (sh Z).subgroupOf (E0 ⊓ Subgroup.centralizer (T0 : Set G)) =
            T0.subgroupOf (E0 ⊓ Subgroup.centralizer (T0 : Set G)) :=
          (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [hcard1, hcard2])
        have hshZT : sh Z = T0 := by
          have h1 := congrArg (Subgroup.map (E0 ⊓ Subgroup.centralizer (T0 : Set G)).subtype) heq
          rwa [Subgroup.map_subgroupOf_eq_of_le hshZ_le, Subgroup.map_subgroupOf_eq_of_le hT0le] at h1
        exact hsh_inj Z X1 hZD hX1D hZc hXcard (by rw [hshZT, sh_X1]))
    · -- |{Z ≤ D : |Z| = p}| ≤ r^e
      rw [hSeq]
      have himg : {Z : Subgroup G | ∃ c ∈ R ⊓ sh D, Z = Work.GW2.conjSub c X1}
          = (fun c : G => Work.GW2.conjSub c X1) '' ((R ⊓ sh D : Subgroup G) : Set G) := by
        ext Z; simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
        constructor
        · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
        · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
      rw [himg]
      refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
      rw [← Nat.card_coe_set_eq]
      refine Nat.le_of_dvd ?_ ?_
      · exact pow_pos (Fact.out : r.Prime).pos e
      · exact (Subgroup.card_dvd_of_le inf_le_left).trans ⟨1, by rw [hRcard, mul_one]⟩

end Work.CORE4
