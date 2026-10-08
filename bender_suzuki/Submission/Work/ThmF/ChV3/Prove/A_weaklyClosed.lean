import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.cst_center_sylow
import Submission.Work.ThmF.ChV3.Prove.A_stronglyReal_normalizer
import Submission.Work.ThmF.ChV3.Prove.A_LV_facts
import Submission.Work.ThmF.ChV3.Prove.A_le_cst
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs
import Submission.Work.ThmF.ChV3.Prove.zpow_emod_eq
import Submission.Work.PGroup.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.A_weaklyClosed` — Peterfalvi II Ch. V §3, step (17), weak closure

`A = Z₁PΣ = Ω₁(LV)` is weakly closed in the Sylow 3-subgroup `C_G(st) = Cst s t`:
for `g : G` with `A^g ≤ Cst s t` one has `A^g = A`.

Source (Peterfalvi II Ch. V §3 (17), see `REFS/peterfalvi_II_ch5_6.md`):

> Let `x ∈ G` with `(Z₁PΣ)^x ⊆ R₂`.  Suppose `Z₁^x ⊄ LV`.  Then `R₂ = (LV) ⋊ Z₁^x` and
> `(Z₁PΣ)^x = A × Z₁^x`. By (16) elements of `A^#` are not strongly real, so `A ∩ Z₁ = 1` and
> `Z₁ΣP = Z₁A`.  Then `Z₁^x` centralises `Z₁ΣP`, so `Z₁Σ ⊆ Z(R₂)`, contradicting (14).  Hence
> `Z₁^x ⊆ Ω₁(LV)`, so `Z₁^x = Z₁` by (16), and `x ∈ N_G(Z₁) = R₂⟨s⟩` normalises `Z₁PΣ`.

Formalised here as: if `Z₁^g ≤ LV := Lsub H s t ⊔ centD H t`, then `(st)^g ∈ LV` has cube `1`,
hence lies in `Ω₁(LV) = A`; it is strongly real, so (16) gives `(st)^g ∈ Z₁`, whence
`Z₁^g = Z₁` and `g ∈ N_G(Z₁) = Cst s t ⊔ ⟨s⟩ = N_G(A)` by `A_stronglyReal_normalizer` (16),
so `A^g = A`.  Otherwise `Z₁^g ⊓ LV = 1`, `Cst s t = LV ⊔ Z₁^g`, and `B := A^g ⊓ LV` has order
`9` and lies in `Ω₁(LV) = A`; `Z₁ ⊓ B = 1` (by (16) applied to the conjugating element `g`), so
`A = Z₁ ⊔ B`.  Since `Z₁ = Z(Cst s t)` (14) and `A^g` is abelian, `Z₁^g` centralises `Z₁ ⊔ B = A`,
hence `Σ`; `LV` centralises `Z₁Σ` by (15d), so `Σ ≤ Z(Cst s t) = Z₁` (14) meets
`Z₁ ⊓ (P ⊔ Σ) = 1` (15d) in `Σ = 1`, contradicting `|Σ| = 3`.

The elementary group-theoretic and index-theoretic lemmas used are proved above; the leaves of
§3 (14)–(16) are imported (`cst_center_sylow`, `A_stronglyReal_normalizer`, `A_LV_facts`).
-/

set_option maxHeartbeats 1000000

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3 Submission.Blueprint

section Helpers

variable {G : Type} [Group G]

theorem StronglyReal_conj (g x : G) (h : StronglyReal x) : StronglyReal (g * x * g⁻¹) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact ⟨g * a * g⁻¹, g * b * g⁻¹,
    by rw [show (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ha]; group,
    by rw [show (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ by group, hb]; group,
    by rw [show (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hab]⟩

theorem Awc_stronglyReal_zpow {s t : G} (hs : s * s = 1) (ht : t * t = 1) (k : ℤ) :
    StronglyReal ((s * t) ^ k) := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hconj : s * (s * t) ^ k * s = ((s * t) ^ k)⁻¹ := by
    have h1 : (MulAut.conj s) (s * t) = (s * t)⁻¹ := by
      rw [MulAut.conj_apply]
      calc s * (s * t) * s⁻¹ = (s * s) * t * s⁻¹ := by group
        _ = t * s := by simp [hs, hs']
        _ = (s * t)⁻¹ := by rw [mul_inv_rev, ht', hs']
    have h2 : (MulAut.conj s) ((s * t) ^ k) = ((s * t) ^ k)⁻¹ := by
      rw [map_zpow, h1, inv_zpow]
    rwa [MulAut.conj_apply, hs'] at h2
  exact ⟨s, s * (s * t) ^ k, hs,
    by rw [show s * (s * t) ^ k * (s * (s * t) ^ k) = (s * (s * t) ^ k * s) * (s * t) ^ k by
          group, hconj, inv_mul_cancel],
    by rw [← mul_assoc, hs, one_mul]⟩

theorem Awc_mem_sup_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, a * b = x) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, B.one_mem, by rw [mul_one]⟩
    · exact ⟨1, A.one_mem, x, hx, by rw [one_mul]⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by rw [mul_one]⟩
  · rintro x y _ _ ⟨a1, ha1, b1, hb1, hxy⟩ ⟨a2, ha2, b2, hb2, hxy2⟩
    refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
    rw [← hxy, ← hxy2]
    have hc : a2 * b1 = b1 * a2 := hcomm a2 ha2 b1 hb1
    calc (a1 * a2) * (b1 * b2) = a1 * a2 * b1 * b2 := by group
      _ = a1 * (a2 * b1) * b2 := by group
      _ = a1 * (b1 * a2) * b2 := by rw [hc]
      _ = a1 * b1 * a2 * b2 := by group
      _ = (a1 * b1) * (a2 * b2) := by group
  · rintro x _ ⟨a1, ha1, b1, hb1, hxy⟩
    refine ⟨a1⁻¹, A.inv_mem ha1, b1⁻¹, B.inv_mem hb1, ?_⟩
    rw [← hxy]
    have hc : a1 * b1 = b1 * a1 := hcomm a1 ha1 b1 hb1
    calc a1⁻¹ * b1⁻¹ = (b1 * a1)⁻¹ := by group
      _ = (a1 * b1)⁻¹ := by rw [hc]

theorem Awc_le_centralizer_sup {K X S : Subgroup G}
    (hK : S ≤ Subgroup.centralizer (K : Set G)) (hX : S ≤ Subgroup.centralizer (X : Set G)) :
    S ≤ Subgroup.centralizer ((K ⊔ X : Subgroup G) : Set G) := by
  rw [Subgroup.le_centralizer_iff] at hK hX ⊢
  exact sup_le hK hX

theorem Awc_Z1_le_centralizer_Cst (s t : G) :
    Z1 s t ≤ Subgroup.centralizer ((Cst s t : Subgroup G) : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hyc : Commute y (s * t) := Subgroup.mem_centralizer_singleton_iff.mp hy
  exact (hyc.zpow_right k).eq

theorem Awc_isMulCommutative_cj {A : Subgroup G} (h : IsMulCommutative ↥A) (g : G) :
    IsMulCommutative ↥(cj g A) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ A, (MulAut.conj g).toMonoidHom x' = (x : G) :=
    Subgroup.mem_map.mp x.2
  obtain ⟨y', hy', hy''⟩ : ∃ y' ∈ A, (MulAut.conj g).toMonoidHom y' = (y : G) :=
    Subgroup.mem_map.mp y.2
  have hxy : x' * y' = y' * x' := by
    have hc := congrArg Subtype.val (h.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
    simpa only [Subgroup.coe_mul] using hc
  show (x : G) * (y : G) = (y : G) * (x : G)
  rw [← hx'', ← hy'', ← map_mul, ← map_mul, hxy]

end Helpers

/-! ## `N_G(Z₁) = C_G(st)⟨s⟩` -/

theorem Awc_NG_Z1 {G : Type} [Group G] (s t : G)
    (h3 : (s * t) ^ 3 = 1) (hne : s * t ≠ 1) (hinv : s * (s * t) * s⁻¹ = (s * t)⁻¹) :
    NG (Z1 s t) = Cst s t ⊔ Subgroup.zpowers s := by
  have hsq : (s * t) ^ 2 = (s * t)⁻¹ := by
    have h : (s * t) ^ 2 * (s * t) = 1 := by
      rw [← pow_succ, show 2 + 1 = 3 by norm_num]
      exact h3
    exact (inv_eq_of_mul_eq_one_left h).symm
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx
    have hmem : x * (s * t) * x⁻¹ ∈ Subgroup.zpowers (s * t) :=
      (hx (s * t)).mp (Subgroup.mem_zpowers (s * t))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk3 : (s * t) ^ (k % 3) = x * (s * t) * x⁻¹ := by
      rw [← hk, zpow_emod_eq (s * t) h3 k]
    have hk0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hklt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h | h | h
    · rw [h, zpow_zero] at hk3
      exact absurd (by
        calc s * t = x⁻¹ * (x * (s * t) * x⁻¹) * x := by group
          _ = 1 := by rw [← hk3]; group) hne
    · rw [h] at hk3
      simp only [zpow_one] at hk3
      have hcom : x * (s * t) = (s * t) * x := by
        calc x * (s * t) = (x * (s * t) * x⁻¹) * x := by group
          _ = (s * t) * x := by rw [← hk3]
      exact Subgroup.mem_sup_left (show x ∈ Cst s t from
        Subgroup.mem_centralizer_singleton_iff.mpr hcom)
    · rw [h] at hk3
      have hk2 : (s * t) ^ (2 : ℤ) = (s * t) ^ 2 := zpow_ofNat _ _
      rw [hk2, hsq] at hk3
      have hconjs : (x * s) * (s * t) * (x * s)⁻¹ = s * t := by
        calc (x * s) * (s * t) * (x * s)⁻¹ = x * (s * (s * t) * s⁻¹) * x⁻¹ := by group
          _ = x * (s * t)⁻¹ * x⁻¹ := by rw [hinv]
          _ = (x * (s * t) * x⁻¹)⁻¹ := by group
          _ = ((s * t)⁻¹)⁻¹ := by rw [← hk3]
          _ = s * t := inv_inv _
      have hcom : (x * s) * (s * t) = (s * t) * (x * s) := by
        calc (x * s) * (s * t) = ((x * s) * (s * t) * (x * s)⁻¹) * (x * s) := by group
          _ = (s * t) * (x * s) := by rw [hconjs]
      have hxs : x * s ∈ Cst s t := Subgroup.mem_centralizer_singleton_iff.mpr hcom
      have hxeq : x = (x * s) * s⁻¹ := by group
      rw [hxeq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxs)
        (Subgroup.mem_sup_right ((Subgroup.zpowers s).inv_mem (Subgroup.mem_zpowers s)))
  · refine sup_le ?_ ?_
    · rw [Cst, Z1, Subgroup.zpowers_eq_closure]
      exact (Subgroup.centralizer_le_normalizer ({s * t} : Set G)).trans
        (Subgroup.normalizer_le_normalizer_closure {s * t})
    · rw [Subgroup.zpowers_le, ← cj_eq_self_iff s (Z1 s t)]
      rw [Z1, cj, MonoidHom.map_zpowers]
      have h1 : (MulAut.conj s).toMonoidHom (s * t) = (s * t)⁻¹ := by
        rw [show (MulAut.conj s).toMonoidHom (s * t) = (MulAut.conj s) (s * t) from rfl,
          MulAut.conj_apply]
        exact hinv
      rw [h1, Subgroup.zpowers_inv]

/-! ## Index arithmetic -/

theorem Awc_card_inf_nine {G : Type} [Group G] [Finite G] {C K H : Subgroup G}
    (hH : H ≤ C) (hK : K ≤ C) (hnot : ¬ H ≤ K)
    (hcard : Nat.card ↥C = 3 * Nat.card ↥K) (hHcard : Nat.card ↥H = 27) :
    Nat.card ↥(H ⊓ K) = 9 := by
  have hrelC : K.relIndex C = 3 := by
    have h := Subgroup.card_mul_index (K.subgroupOf C)
    have hc : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
    rw [hc, hcard] at h
    have h' : (K.subgroupOf C).index * Nat.card ↥K = 3 * Nat.card ↥K := by
      rw [mul_comm]; exact h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  have hkey : Nat.card ↥(H ⊓ K) * (H ⊓ K).relIndex H = 27 := by
    have h2 := Subgroup.card_mul_index ((H ⊓ K).subgroupOf H)
    have hcard_sub : Nat.card ↥((H ⊓ K).subgroupOf H) = Nat.card ↥(H ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ K ≤ H)).toEquiv
    rw [hcard_sub, hHcard] at h2
    exact h2
  have hHrelC : H.relIndex C ≠ 0 :=
    (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card H C) Nat.card_pos).ne'
  have hr3 : (H ⊓ K).relIndex H ≤ 3 := by
    have hmul : (H ⊓ K).relIndex H * H.relIndex C = (H ⊓ K).relIndex C :=
      Subgroup.relIndex_mul_relIndex (H ⊓ K) H C inf_le_left hH
    have hineq := Subgroup.relIndex_inf_le (H := H) (K := K) (L := C)
    rw [← hmul, hrelC, mul_comm (H.relIndex C) 3] at hineq
    exact Nat.le_of_mul_le_mul_right hineq (Nat.pos_of_ne_zero hHrelC)
  have hdvd : (H ⊓ K).relIndex H ∣ 27 :=
    ⟨Nat.card ↥(H ⊓ K), hkey.symm.trans (mul_comm _ _)⟩
  have hk13 : (H ⊓ K).relIndex H = 1 ∨ (H ⊓ K).relIndex H = 3 := by
    obtain ⟨k, _hk3, hk⟩ : ∃ k ≤ 3, (H ⊓ K).relIndex H = 3 ^ k := by
      have h3 : (H ⊓ K).relIndex H ∣ 3 ^ 3 := by simpa using hdvd
      exact (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp h3
    interval_cases k
    · left; simpa using hk
    · right; simpa using hk
    · exfalso; rw [hk] at hr3; norm_num at hr3
    · exfalso; rw [hk] at hr3; norm_num at hr3
  rcases hk13 with h1 | h3
  · exact absurd ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right) hnot
  · rw [h3] at hkey; omega

theorem Awc_sup_eq_of_not_le {G : Type} [Group G] [Finite G] {C K X : Subgroup G}
    (hX : X ≤ C) (hK : K ≤ C) (hnot : ¬ X ≤ K) (hcard : Nat.card ↥C = 3 * Nat.card ↥K) :
    K ⊔ X = C := by
  have hle : K ⊔ X ≤ C := sup_le hK hX
  have hrelC : K.relIndex C = 3 := by
    have h := Subgroup.card_mul_index (K.subgroupOf C)
    have hc : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
    rw [hc, hcard] at h
    have h' : (K.subgroupOf C).index * Nat.card ↥K = 3 * Nat.card ↥K := by
      rw [mul_comm]; exact h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  have hprod : K.relIndex (K ⊔ X) * (K ⊔ X).relIndex C = 3 := by
    rw [← hrelC]
    exact Subgroup.relIndex_mul_relIndex K (K ⊔ X) C le_sup_left hle
  have hdvd : (K ⊔ X).relIndex C ∣ 3 :=
    ⟨K.relIndex (K ⊔ X), hprod.symm.trans (mul_comm _ _)⟩
  have hne3 : (K ⊔ X).relIndex C ≠ 3 := by
    intro h
    rw [h] at hprod
    have h1 : K.relIndex (K ⊔ X) = 1 := by omega
    exact hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1))
  have hone : (K ⊔ X).relIndex C = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact h
    · exact absurd h hne3
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)


variable {G : Type} [Group G]

/-- Join of two commuting subgroups of exponent `3` has exponent `3`. -/
theorem Awc_pow_three_of_sup {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ a ∈ A, a ^ 3 = 1) (hB : ∀ b ∈ B, b ^ 3 = 1) :
    ∀ x ∈ A ⊔ B, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Awc_mem_sup_of_commute hcomm hx
  have hc : Commute a b := (hcomm a ha b hb)
  rw [hc.mul_pow]
  rw [hA a ha, hB b hb, mul_one]

/-- `Asub H P s t` has exponent `3`. -/
theorem Awc_Asub_pow_three {H : Subgroup G} {t s : G} {P : Subgroup G}
    (h3 : (s * t) ^ 3 = 1) (hP : Nat.card P = 3)
    (hSig : Nat.card ↥(Sig H t P) = 3)
    (hPc : P ≤ Cst s t) (hSigc : Sig H t P ≤ Cst s t) :
    ∀ a ∈ Asub H P s t, a ^ 3 = 1 := by
  have hZ1exp : ∀ z ∈ Z1 s t, z ^ 3 = 1 := by
    intro z hz
    have hdvd : orderOf z ∣ 3 :=
      (orderOf_dvd_of_mem_zpowers hz).trans ((orderOf_dvd_iff_pow_eq_one).mpr h3)
    rwa [orderOf_dvd_iff_pow_eq_one] at hdvd
  have hPexp : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    have hdvd : orderOf p ∣ 3 := by
      rw [← hP]; exact Subgroup.orderOf_dvd_natCard P hp
    rwa [orderOf_dvd_iff_pow_eq_one] at hdvd
  have hSigexp : ∀ σ ∈ Sig H t P, σ ^ 3 = 1 := by
    intro σ hσ
    have hdvd : orderOf σ ∣ 3 := by
      rw [← hSig]; exact Subgroup.orderOf_dvd_natCard _ hσ
    rwa [orderOf_dvd_iff_pow_eq_one] at hdvd
  have hcommZ1P : ∀ a ∈ Z1 s t, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (Awc_Z1_le_centralizer_Cst s t ha) b (hPc hb)).symm
  have hcommZ1Sig : ∀ a ∈ Z1 s t, ∀ b ∈ Sig H t P, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (Awc_Z1_le_centralizer_Cst s t ha) b (hSigc hb)).symm
  have hcommPSig : ∀ a ∈ P, ∀ b ∈ Sig H t P, a * b = b * a := by
    intro a ha b hb
    have hbP : b ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hb).2
    exact Subgroup.mem_centralizer_iff.mp hbP a ha
  have hcommA : ∀ a ∈ Z1 s t ⊔ P, ∀ b ∈ Sig H t P, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Awc_mem_sup_of_commute hcommZ1P ha
    calc (a1 * a2) * b = a1 * (a2 * b) := by group
      _ = a1 * (b * a2) := by rw [hcommPSig a2 ha2 b hb]
      _ = (a1 * b) * a2 := by group
      _ = (b * a1) * a2 := by rw [hcommZ1Sig a1 ha1 b hb]
      _ = b * (a1 * a2) := by group
  exact Awc_pow_three_of_sup hcommA
    (Awc_pow_three_of_sup hcommZ1P hZ1exp hPexp) hSigexp


/-! ## The main assembly (leaves of §3 (14)–(16) taken as hypotheses) -/


/-- Conjugation distributes over powers. -/
theorem Awc_conj_pow {G : Type} [Group G] (g x : G) (n : ℕ) :
    (g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹ := by
  rw [show g * x * g⁻¹ = (MulAut.conj g) x by rw [MulAut.conj_apply], ← map_pow,
    MulAut.conj_apply]

/-- `Z₁ ≤ Asub`. -/
theorem Awc_Z1_le_Asub {G : Type} [Group G] {H P : Subgroup G} (s t : G) :
    Z1 s t ≤ Asub H P s t := by
  rw [Asub]
  exact le_sup_left.trans le_sup_left

/-- `P ≤ Asub`. -/
theorem Awc_P_le_Asub {G : Type} [Group G] {H P : Subgroup G} (s t : G) :
    P ≤ Asub H P s t := by
  rw [Asub]
  exact le_sup_right.trans le_sup_left

/-- `Σ ≤ Asub`. -/
theorem Awc_Sig_le_Asub {G : Type} [Group G] {H P : Subgroup G} (s t : G) :
    Sig H t P ≤ Asub H P s t := by
  rw [Asub]
  exact le_sup_right

/-- **§3 step (17), weak closure.**  `A = Z₁PΣ` is weakly closed in the Sylow 3-subgroup
`C_G(st)`: any conjugate of `A` inside `C_G(st)` is `A` itself.  See the module docstring for the
two-case argument (which follows Peterfalvi II Ch. V §3 (17)). -/
theorem A_weaklyClosed {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ g : G, Work.ThmF.ChV3.cj g (Work.ThmF.ChV3.Asub H P s t) ≤ Work.ThmF.ChV3.Cst s t →
      Work.ThmF.ChV3.cj g (Work.ThmF.ChV3.Asub H P s t) = Work.ThmF.ChV3.Asub H P s t := by
  -- ## the leaves of §3 (14)–(16)
  obtain ⟨hAb, hAcard, hZ1PSig, hLVcard, hA_le_LV, hOmega, hcent⟩ :=
    A_LV_facts hFT hC4 c h15 h7 hpf h11 d
  obtain ⟨hSR, hNG⟩ := A_stronglyReal_normalizer hFT hC4 c h15 h7 hpf h11 d
  obtain ⟨hcstZ, hcstcard⟩ := cst_center_sylow hFT hC4 c h15 h7 hpf h11 d
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- ## (a) standing numerical and structural facts
  have hst3 : (s * t) ^ 3 = 1 := by rw [← d.f3]; exact pow_orderOf_eq_one _
  have hstne : s * t ≠ 1 := by
    intro h
    have h3 := d.f3
    rw [h, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [c.s_inv, pow_two] at h
  have hZ1card : Nat.card ↥(Z1 s t) = 3 := by rw [Z1, Nat.card_zpowers, d.f3]
  have hAcst : Asub H P s t ≤ Cst s t := A_le_cst c
  have hPc : P ≤ Cst s t :=
    ((le_sup_right : P ≤ Z1 s t ⊔ P).trans
      (le_sup_left : Z1 s t ⊔ P ≤ (Z1 s t ⊔ P) ⊔ Sig H t P)).trans hAcst
  have hSigc : Sig H t P ≤ Cst s t :=
    (le_sup_right : Sig H t P ≤ (Z1 s t ⊔ P) ⊔ Sig H t P).trans hAcst
  have hVle : centD H t ≤ Cst s t := by
    refine le_trans (le_inf ?_ ?_) (centralizer_mul_le_centralizer s t)
    · exact Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
    · intro x hx; exact (Subgroup.mem_inf.mp hx).2
  have hLVle : Lsub H s t ⊔ centD H t ≤ Cst s t := sup_le inf_le_right hVle
  have hCstcard : Nat.card ↥(Cst s t) = 3 * Nat.card ↥(Lsub H s t ⊔ centD H t) := by
    rw [hcstcard, d.G3, hLVcard]; ring
  obtain ⟨_hLcyc, _hLcard, hLinv, hstL⟩ := L_facts hFT hC4 c h15 d
  have hst_inv_s : s * (s * t) * s⁻¹ = (s * t)⁻¹ := hLinv (s * t) hstL
  have ht2 : t * t = 1 := by
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
    have hinv_st : s * (s * t) * s = (s * t)⁻¹ := by simpa [hs'] using hst_inv_s
    have ht_eq : t = s * (s * t) := by rw [← mul_assoc, hs2, one_mul]
    rw [ht_eq]
    calc (s * (s * t)) * (s * (s * t)) = (s * (s * t) * s) * (s * t) := by group
      _ = (s * t)⁻¹ * (s * t) := by rw [hinv_st]
      _ = 1 := inv_mul_cancel _
  have hAexp0 : ∀ a ∈ Asub H P s t, a ^ 3 = 1 := Awc_Asub_pow_three hst3 d.p3 d.sig3 hPc hSigc
  -- ## (b) the elementwise argument
  intro g hg
  set A := Asub H P s t with hA
  set LV := Lsub H s t ⊔ centD H t with hLV
  set B := cj g A ⊓ LV with hB
  have hAb' : IsMulCommutative ↥A := by rw [hA]; exact hAb
  have hAcard' : Nat.card ↥A = 27 := by rw [hA]; exact hAcard
  have hA_le_LV' : A ≤ LV := by rw [hA, hLV]; exact hA_le_LV
  have hOmega' : ∀ x ∈ LV, x ^ 3 = 1 → x ∈ A := by
    intro x hx h3
    rw [hLV] at hx
    rw [hA]
    exact hOmega x hx h3
  have hcent' : ∀ a ∈ Z1 s t ⊔ Sig H t P, ∀ y ∈ LV, a * y = y * a := by
    intro a ha y hy
    rw [hLV] at hy
    exact hcent a ha y hy
  have hSR' : ∀ g : G, ∀ a ∈ A, StronglyReal (g * a * g⁻¹) → a ∈ Z1 s t := by
    intro g a ha hsr
    rw [hA] at ha
    exact hSR g a ha hsr
  have hNG' : NG A = Cst s t ⊔ Subgroup.zpowers s := by rw [hA]; exact hNG
  have hAexp : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    rw [hA] at ha
    exact hAexp0 a ha
  have hAcst' : A ≤ Cst s t := by rw [hA]; exact hAcst
  have hLVle' : LV ≤ Cst s t := by rw [hLV]; exact hLVle
  have hCstcard' : Nat.card ↥(Cst s t) = 3 * Nat.card ↥LV := by rw [hLV]; exact hCstcard
  have hZ1leA : Z1 s t ≤ A := by rw [hA]; exact Awc_Z1_le_Asub (H := H) (P := P) s t
  have hZ'card : Nat.card ↥(cj g (Z1 s t)) = 3 := by rw [card_cj, hZ1card]
  have hZ'le : cj g (Z1 s t) ≤ Cst s t := (cj_mono hZ1leA g).trans hg
  by_cases hcase : cj g (Z1 s t) ≤ LV
  · -- ## Case 1: `Z₁^g ≤ LV`
    have hstgZ' : g * (s * t) * g⁻¹ ∈ cj g (Z1 s t) := by
      rw [mem_cj_iff]
      have h1 : g⁻¹ * (g * (s * t) * g⁻¹) * g = s * t := by group
      rw [h1]
      exact Subgroup.mem_zpowers _
    have hstgLV : g * (s * t) * g⁻¹ ∈ LV := hcase hstgZ'
    have hstg3 : (g * (s * t) * g⁻¹) ^ 3 = 1 := by
      rw [Awc_conj_pow g (s * t) 3, hst3]
      group
    have hstgA : g * (s * t) * g⁻¹ ∈ A := hOmega' _ hstgLV hstg3
    have hsr : StronglyReal (g * (s * t) * g⁻¹) := StronglyReal_conj g (s * t) (by
      have h := Awc_stronglyReal_zpow hs2 ht2 (1 : ℤ)
      simpa using h)
    have hstgZ1 : g * (s * t) * g⁻¹ ∈ Z1 s t := by
      have h := hSR' 1 (g * (s * t) * g⁻¹) hstgA (by simpa using hsr)
      simpa using h
    have hne_stg : g * (s * t) * g⁻¹ ≠ 1 := by
      intro h
      apply hstne
      calc s * t = g⁻¹ * (g * (s * t) * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hord : orderOf (g * (s * t) * g⁻¹) = 3 := orderOf_eq_prime hstg3 hne_stg
    have hZ'eq : cj g (Z1 s t) = Z1 s t := by
      have hzp : Subgroup.zpowers (g * (s * t) * g⁻¹) = Z1 s t := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hstgZ1) ?_
        rw [hZ1card, Nat.card_zpowers, hord]
      have hmap : cj g (Z1 s t) = Subgroup.zpowers (g * (s * t) * g⁻¹) := by
        rw [cj, Z1, MonoidHom.map_zpowers]
        rfl
      rw [hmap, hzp]
    have hgN : g ∈ NG A := by
      have hgN1 : g ∈ NG (Z1 s t) := (cj_eq_self_iff g (Z1 s t)).mp hZ'eq
      have h1 : NG (Z1 s t) = Cst s t ⊔ Subgroup.zpowers s :=
        Awc_NG_Z1 s t hst3 hstne hst_inv_s
      rw [h1] at hgN1
      rw [hNG']
      exact hgN1
    exact (cj_eq_self_iff g A).mpr hgN
  · -- ## Case 2: `Z₁^g ≰ LV` is impossible
    have hCst_eq : LV ⊔ cj g (Z1 s t) = Cst s t :=
      Awc_sup_eq_of_not_le hZ'le hLVle' hcase hCstcard'
    have hZ'inf_eq : cj g (Z1 s t) ⊓ LV = ⊥ := by
      rw [← Subgroup.card_eq_one]
      have hdvd : Nat.card ↥(cj g (Z1 s t) ⊓ LV) ∣ 3 := by
        rw [← hZ'card]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact h1
      · exfalso
        refine hcase ?_
        have heq : cj g (Z1 s t) ⊓ LV = cj g (Z1 s t) :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hZ'card])
        exact heq ▸ inf_le_right
    have hA'card : Nat.card ↥(cj g A) = 27 := by rw [card_cj, hAcard']
    have hA'notle : ¬ cj g A ≤ LV := by
      intro h
      exact hcase ((cj_mono hZ1leA g).trans h)
    have hBcard : Nat.card ↥B = 9 := by
      rw [hB]
      exact Awc_card_inf_nine hg hLVle' hA'notle hCstcard' hA'card
    have hA'exp : ∀ x ∈ cj g A, x ^ 3 = 1 := by
      intro x hx
      have hx' : g⁻¹ * x * g ∈ A := by
        have := (mem_cj_iff g A x).mp hx
        rwa [hA] at this
      have h3 := hAexp _ hx'
      rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group, Awc_conj_pow g _ 3, h3]
      group
    have hB_le_A : B ≤ A := by
      intro b hb
      have hb' : b ∈ cj g A ⊓ LV := by rwa [hB] at hb
      exact hOmega' b (Subgroup.mem_inf.mp hb').2 (hA'exp b (Subgroup.mem_inf.mp hb').1)
    have hZ1B_inf : Z1 s t ⊓ B = ⊥ := by
      rw [← Subgroup.card_eq_one]
      have hdvd : Nat.card ↥(Z1 s t ⊓ B) ∣ 3 := by
        rw [← hZ1card]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact h1
      · exfalso
        have hle : Z1 s t ≤ B := by
          have heq : Z1 s t ⊓ B = Z1 s t :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hZ1card])
          exact heq ▸ inf_le_right
        have hle' : Z1 s t ≤ cj g A ⊓ LV := by rwa [hB] at hle
        have hst_mem : s * t ∈ Z1 s t := Subgroup.mem_zpowers _
        have hst_A' : s * t ∈ cj g A := (hle' hst_mem).1
        have hst_LV : s * t ∈ LV := (hle' hst_mem).2
        have hstinv_A : g⁻¹ * (s * t) * g ∈ A := by
          have := (mem_cj_iff g A (s * t)).mp hst_A'
          rwa [hA] at this
        have hsr : StronglyReal (g * (g⁻¹ * (s * t) * g) * g⁻¹) := by
          have heq : g * (g⁻¹ * (s * t) * g) * g⁻¹ = s * t := by group
          rw [heq]
          have h := Awc_stronglyReal_zpow hs2 ht2 (1 : ℤ)
          simpa using h
        have haZ1 : g⁻¹ * (s * t) * g ∈ Z1 s t := hSR' g _ hstinv_A hsr
        have hst_Z' : s * t ∈ cj g (Z1 s t) := by
          rw [mem_cj_iff]
          exact haZ1
        have hbot : (s * t) ∈ (⊥ : Subgroup G) := by
          rw [← hZ'inf_eq]
          exact ⟨hst_Z', hst_LV⟩
        exact hstne (by simpa using hbot)
    have hA_eq : Z1 s t ⊔ B = A := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hZ1leA hB_le_A) ?_
      have hcomm : ∀ a ∈ Z1 s t, ∀ b ∈ B, a * b = b * a := by
        intro a ha b hb
        have haA : a ∈ A := hZ1leA ha
        have hbA : b ∈ A := hB_le_A hb
        exact congrArg Subtype.val (hAb'.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)
      have hcard : Nat.card ↥(Z1 s t ⊔ B) = 27 := by
        have h1 := Work.PGroup.card_sup_mul_card_inf (Z1 s t) B hcomm
        rw [hZ1card, hBcard, hZ1B_inf, Subgroup.card_bot] at h1
        simpa using h1
      rw [hAcard', hcard]
    have hA'b : IsMulCommutative ↥(cj g A) := Awc_isMulCommutative_cj hAb' g
    have hZ'cent_Z1 : cj g (Z1 s t) ≤ Subgroup.centralizer ((Z1 s t : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hyC : y ∈ Cst s t := hZ'le hy
      exact (Awc_Z1_le_centralizer_Cst s t hz y hyC).symm
    have hZ'cent_B : cj g (Z1 s t) ≤ Subgroup.centralizer ((B : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : b ∈ cj g A ⊓ LV := by rwa [hB] at hb
      have hyA' : y ∈ cj g A := (cj_mono hZ1leA g) hy
      have hbA' : b ∈ cj g A := (Subgroup.mem_inf.mp hb').1
      have hcyb : y * b = b * y :=
        congrArg Subtype.val (hA'b.is_comm.comm ⟨y, hyA'⟩ ⟨b, hbA'⟩)
      exact hcyb.symm
    have hZ'cent_A : cj g (Z1 s t) ≤ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
      have hcomb := Awc_le_centralizer_sup hZ'cent_Z1 hZ'cent_B
      rwa [hA_eq] at hcomb
    have hSig_le_A : Sig H t P ≤ A := by
      rw [hA]
      exact Awc_Sig_le_Asub (H := H) (P := P) s t
    have hSig_cen_Z' : Sig H t P ≤ Subgroup.centralizer ((cj g (Z1 s t) : Subgroup G) : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      have hcen : Subgroup.centralizer ((A : Subgroup G) : Set G) ≤
          Subgroup.centralizer ((Sig H t P : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (fun x hx => hSig_le_A hx)
      exact hZ'cent_A.trans hcen
    have hSig_cen_Cst : Sig H t P ≤ Subgroup.centralizer ((Cst s t : Subgroup G) : Set G) := by
      have hLVcen : Sig H t P ≤ Subgroup.centralizer ((LV : Subgroup G) : Set G) := by
        intro σ hσ
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcent' σ (Subgroup.mem_sup_right hσ) y hy).symm
      have hcomb := Awc_le_centralizer_sup hLVcen hSig_cen_Z'
      rwa [hCst_eq] at hcomb
    have hSig_le_Z1 : Sig H t P ≤ Z1 s t := by
      intro σ hσ
      have hσA : σ ∈ A := hSig_le_A hσ
      have hσLV : σ ∈ LV := hA_le_LV' hσA
      have hσCst : σ ∈ Cst s t := hLVle' hσLV
      exact hcstZ σ hσCst (fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hSig_cen_Cst hσ) y hy).symm)
    have hSig_bot : Sig H t P = ⊥ := by
      rw [← le_bot_iff]
      intro σ hσ
      have hmem : σ ∈ Z1 s t ⊓ (P ⊔ Sig H t P) := ⟨hSig_le_Z1 hσ, Subgroup.mem_sup_right hσ⟩
      rwa [hZ1PSig] at hmem
    have h1 : Nat.card ↥(Sig H t P) = 1 := by rw [hSig_bot, Subgroup.card_bot]
    rw [d.sig3] at h1
    exact absurd h1 (by norm_num)

end Work.ThmF.ChV3.Prove
