import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.sec1_lemma3
import Submission.Work.NormalComplement.sec1_lemma3_structure
import Submission.Work.NormalComplement.sec3_step1
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.section2_prop1_v2
import Submission.Work.NormalComplement.commutator_ne_of_solvable
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.mem_piCore_iff
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.ZassenhausTwoGroup.twoPart_sup_oddPart

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type} [Group G] [Finite G]

/-- `F(X) ≤ X`. -/
private lemma fitSub_le (X : Subgroup G) : Design.fitSub X ≤ X := Subgroup.map_subtype_le _

/-- `1 ∈ Kset D t`. -/
private lemma one_mem_Kset {H : Subgroup G} {t : G} :
    (1 : G) ∈ Kset (twoPoint H t) t := ⟨Subgroup.one_mem _, by simp⟩

/-! ## Glue: characteristic subgroups of `↥D` are invariant under `N_G(D)` -/

/-- A subgroup `Z ≤ ↥D` which is characteristic in `↥D` is invariant under `N_G(D)`
(conjugation by `e ∈ N_G(D)` restricts to an automorphism of `↥D`). -/
private lemma conj_map_subtype_of_characteristic {D : Subgroup G} {Z : Subgroup ↥D}
    (hZ : Z.Characteristic) {e : G} (he : e ∈ Subgroup.normalizer (D : Set G)) :
    (Z.map D.subtype).map (MulAut.conj e) = Z.map D.subtype := by
  have hD : D.map (MulAut.conj e).toMonoidHom = D := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      show e * y * e⁻¹ ∈ D
      exact (Subgroup.mem_normalizer_iff.mp he y).mp hy
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨e⁻¹ * x * e, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.mp he (e⁻¹ * x * e)).mpr ?_
        have h : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
        rw [h]; exact hx
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  let φ : ↥D ≃* ↥D :=
    (Subgroup.equivMapOfInjective D (MulAut.conj e).toMonoidHom (MulAut.conj e).injective).trans
      (MulEquiv.subgroupCongr hD)
  have hcomp : D.subtype.comp φ.toMonoidHom = (MulAut.conj e).toMonoidHom.comp D.subtype := by
    ext x
    rfl
  have key : Z.map φ.toMonoidHom = Z := (Subgroup.characteristic_iff_map_eq.mp hZ) φ
  calc (Z.map D.subtype).map (MulAut.conj e)
      = Z.map ((MulAut.conj e).toMonoidHom.comp D.subtype) := by
        rw [Subgroup.map_map]
        ext x
        rfl
    _ = Z.map (D.subtype.comp φ.toMonoidHom) := by rw [hcomp]
    _ = (Z.map φ.toMonoidHom).map D.subtype := by rw [Subgroup.map_map]
    _ = Z.map D.subtype := by rw [key]

/-- `N_G(X)` normalises `O_{p'}(F(X))`: the Fitting subgroup and its `p'`-core are
characteristic. -/
private lemma normalizer_le_normalizer_pPrimeCoreSub_fitSub {V X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hVX : V ≤ Subgroup.normalizer (X : Set G)) :
    V ≤ Subgroup.normalizer (pPrimeCoreSub p (Design.fitSub X) : Set G) := by
  intro v hv
  have h1 : v ∈ Subgroup.normalizer (Design.fitSub X : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa only [Design.fitSub] using
      conj_map_subtype_of_characteristic (D := X) (Z := Work.Fitting.fitting ↥X)
        (Work.Fitting.fitting_characteristic ↥X) (hVX hv)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa only [Work.NormalComplement.pPrimeCoreSub, Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    using conj_map_subtype_of_characteristic (D := Design.fitSub X)
      (Z := Work.Fitting.pPrimeCore p ↥(Design.fitSub X)) (inferInstance) h1

/-! ## A `p'`-subgroup of a finite nilpotent group lies in `O_{p'}` -/

/-- In a finite nilpotent group `N`, a subgroup `A` of order prime to `p` is contained in
`O_{p'}(N)`.  (`N = O_p(N) × O_{p'}(N)`; the `O_p`-component of an element of `A` has order
dividing the order of that element, hence is trivial.) -/
private lemma le_pPrimeCore_of_isNilpotent {N : Type} [Group N] [Finite N]
    (hN : Group.IsNilpotent N) {p : ℕ} (hp : p.Prime) {A : Subgroup N}
    (hA : ¬ p ∣ Nat.card A) : A ≤ Work.Fitting.pPrimeCore p N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hN
  set B : Subgroup N := Work.Fitting.pPrimeCore p N with hB
  set C : Subgroup N := Work.Fitting.pCore p N with hC
  have htop : C ⊔ B = ⊤ := by
    rw [hC, hB]
    exact Work.ZassenhausTwoGroup.pCore_sup_pPrimeCore_eq_top (G := N) hN p
  have hCnorm : C.Normal := inferInstance
  have hBnorm : B.Normal := inferInstance
  have hinf : C ⊓ B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have h1 : orderOf x ∣ Nat.card ↥C := by
      rw [← Nat.card_zpowers x]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx.1)
    have h2 : orderOf x ∣ Nat.card ↥B := by
      rw [← Nat.card_zpowers x]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx.2)
    have h3 : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥B) :=
      Work.Fitting.piCore_isPiNat N (fun q => q ≠ p)
    have h4 : ¬ p ∣ orderOf x := fun hd => h3 p hp (hd.trans h2) rfl
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Work.Fitting.isPGroup_pCore (G := N) hp)
    have h5 : orderOf x ∣ p ^ k := by rw [← hk]; exact h1
    have h6 : orderOf x = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h5
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero] at hj; exact hj
      · exact absurd (hj ▸ dvd_pow_self p hpos.ne') h4
    simpa using orderOf_eq_one_iff.mp h6
  have hcomm : ∀ x ∈ C, ∀ y ∈ B, Commute x y := fun x hx y hy =>
    Subgroup.commute_of_normal_of_disjoint C B hCnorm hBnorm (disjoint_iff.mpr hinf) x y hx hy
  have hcoe : ((C ⊔ B : Subgroup N) : Set N) = (C : Set N) * (B : Set N) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C B
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hBnorm]; exact le_top)
  have hBcop : Nat.Coprime (Nat.card ↥B) p :=
    (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp
      (Work.Fitting.piCore_isPiNat N (fun q => q ≠ p))
  intro a ha
  have ha' : a ∈ C ⊔ B := by rw [htop]; exact Subgroup.mem_top a
  change a ∈ ((C ⊔ B : Subgroup N) : Set N) at ha'
  rw [hcoe, Set.mem_mul] at ha'
  obtain ⟨x, hx, y, hy, hxy⟩ := ha'
  have hxy_comm : Commute x y := hcomm x hx y hy
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Work.Fitting.isPGroup_pCore (G := N) hp)
  have hx_dvd : orderOf x ∣ p ^ k := by
    rw [← hk, ← Nat.card_zpowers x]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
  have hx_cop : Nat.Coprime (orderOf x) (orderOf y) := by
    have hy_dvd : orderOf y ∣ Nat.card ↥B := by
      rw [← Nat.card_zpowers y]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy)
    have hp_not : ¬ p ∣ orderOf y := by
      intro hd
      have hd1 : p ∣ Nat.card ↥B := hd.trans hy_dvd
      have : p ∣ 1 := hBcop ▸ Nat.dvd_gcd hd1 (dvd_refl p)
      exact hp.not_dvd_one this
    have hp_cop : p.Coprime (orderOf y) := (hp.coprime_iff_not_dvd).mpr hp_not
    have hpk : (p ^ k).Coprime (orderOf y) := hp_cop.pow_left k
    exact hpk.coprime_dvd_left hx_dvd
  have hx_triv : x = 1 := by
    by_contra hx1
    have hx_ord_ne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hx_dvd
    have hj1 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero] at hj; exact absurd hj hx_ord_ne
      · exact hpos
    have hp_dvd : p ∣ orderOf x := by rw [hj]; exact dvd_pow_self p hj1.ne'
    have hpd : p ∣ orderOf a := by
      rw [← hxy, hxy_comm.orderOf_mul_eq_mul_orderOf_of_coprime hx_cop]
      exact dvd_mul_of_dvd_left hp_dvd _
    refine hA (hpd.trans ?_)
    rw [← Nat.card_zpowers a]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ha)
  rw [← hxy, hx_triv, one_mul]
  exact hy

/-! ## Self-normalizing subgroups of nilpotent groups -/

/-- If `Y ≤ R`, `R` is nilpotent, and `N_G(Y) ∩ R = Y`, then `R = Y` (the normalizer condition
inside the nilpotent group `↥R`). -/
private lemma eq_of_normalizer_inf_eq_of_isNilpotent {Y R : Subgroup G}
    (hR : Group.IsNilpotent ↥R) (hYR : Y ≤ R)
    (hN : Subgroup.normalizer (Y : Set G) ⊓ R = Y) : R = Y := by
  have hnc : NormalizerCondition ↥R := Group.normalizerCondition_of_isNilpotent
  have hnorm : Subgroup.normalizer ((Y.subgroupOf R : Set ↥R)) = Y.subgroupOf R := by
    rw [← Subgroup.subgroupOf_normalizer_eq hYR]
    conv_rhs => rw [← hN]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2, and_true]
  have htop : Y.subgroupOf R = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hnorm
  refine le_antisymm ?_ hYR
  intro r hr
  have : (⟨r, hr⟩ : ↥R) ∈ Y.subgroupOf R := by rw [htop]; trivial
  exact Subgroup.mem_subgroupOf.mp this

/-! ## Normalizer computations -/

/-- `Q ≤ N(Y)` implies `Q ≤ N(N(Y))` (a normalizer is self-normalizing). -/
private lemma le_normalizer_normalizer_of_le_normalizer {Y Q : Subgroup G}
    (h : Q ≤ Subgroup.normalizer (Y : Set G)) :
    Q ≤ Subgroup.normalizer (Subgroup.normalizer (Y : Set G) : Set G) :=
  h.trans (Subgroup.le_normalizer (H := Subgroup.normalizer (Y : Set G)))

/-- `Q ≤ N(X)` and `Q ≤ N(Y)` imply `Q ≤ N(X ∩ Y)`. -/
private lemma le_normalizer_inf_of_le_normalizer {X Y Q : Subgroup G}
    (hX : Q ≤ Subgroup.normalizer (X : Set G)) (hY : Q ≤ Subgroup.normalizer (Y : Set G)) :
    Q ≤ Subgroup.normalizer (X ⊓ Y : Subgroup G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨hzX, hzY⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hX hq) z).mp hzX,
      (Subgroup.mem_normalizer_iff.mp (hY hq) z).mp hzY⟩
  · intro hz
    obtain ⟨hzX, hzY⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hX hq) z).mpr hzX,
      (Subgroup.mem_normalizer_iff.mp (hY hq) z).mpr hzY⟩

/-- `Q ≤ N(Y)` implies `Q ≤ N(C_G(Y))`. -/
private lemma le_normalizer_centralizer_of_le_normalizer {Y Q : Subgroup G}
    (h : Q ≤ Subgroup.normalizer (Y : Set G)) :
    Q ≤ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have h1 : q⁻¹ * y * q ∈ Y := by
      refine (Subgroup.mem_normalizer_iff.mp (h hq) (q⁻¹ * y * q)).mpr ?_
      have : q * (q⁻¹ * y * q) * q⁻¹ = y := by group
      rw [this]; exact hy
    have h2 := hc (q⁻¹ * y * q) h1
    calc y * (q * c * q⁻¹) = q * ((q⁻¹ * y * q) * c) * q⁻¹ := by group
      _ = q * (c * (q⁻¹ * y * q)) * q⁻¹ := by rw [h2]
      _ = (q * c * q⁻¹) * y := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have h1 : q * y * q⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (h hq) y).mp hy
    have h2 := hc (q * y * q⁻¹) h1
    calc y * c = q⁻¹ * ((q * y * q⁻¹) * (q * c * q⁻¹)) * q := by group
      _ = q⁻¹ * ((q * c * q⁻¹) * (q * y * q⁻¹)) * q := by rw [h2]
      _ = c * y := by group

/-- Conjugating an element of `C_G(S)` by an element `p` with `p⁻¹ S p ⊆ S` stays in `C_G(S)`. -/
private lemma mem_centralizer_conj {S : Set G} {p c : G}
    (hc : c ∈ Subgroup.centralizer S) (h : ∀ z ∈ S, p⁻¹ * z * p ∈ S) :
    p * c * p⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro z hz
  have h1 := hc (p⁻¹ * z * p) (h z hz)
  calc z * (p * c * p⁻¹) = p * ((p⁻¹ * z * p) * c) * p⁻¹ := by group
    _ = p * (c * (p⁻¹ * z * p)) * p⁻¹ := by rw [h1]
    _ = (p * c * p⁻¹) * z := by group

/-! ## Elements of a `p`-subgroup and a `p'`-subgroup of a nilpotent group commute -/

private lemma key_centralizes {F Y P : Subgroup G}
    (hF : Group.IsNilpotent ↥F) (hYF : Y ≤ F) (hPF : P ≤ F) {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p P) (hYp : ¬ p ∣ Nat.card ↥Y) :
    ∀ a ∈ P, ∀ y ∈ Y, a * y = y * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hF
  intro a ha y hy
  have hcop : Nat.Coprime (orderOf (⟨a, hPF ha⟩ : ↥F)) (orderOf (⟨y, hYF hy⟩ : ↥F)) := by
    have h1 : orderOf (⟨a, hPF ha⟩ : ↥F) = orderOf a := (Subgroup.orderOf_coe _).symm
    have h2 : orderOf (⟨y, hYF hy⟩ : ↥F) = orderOf y := (Subgroup.orderOf_coe _).symm
    rw [h1, h2]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have ha_dvd : orderOf a ∣ p ^ k := by
      rw [← hk, ← Nat.card_zpowers a]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ha)
    have hy_dvd : orderOf y ∣ Nat.card ↥Y := by
      rw [← Nat.card_zpowers y]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy)
    have hp_not : ¬ p ∣ orderOf y := fun hd => hYp (hd.trans hy_dvd)
    have hp_cop : p.Coprime (orderOf y) := (hp.coprime_iff_not_dvd).mpr hp_not
    exact (hp_cop.pow_left k).coprime_dvd_left ha_dvd
  have hcomm := Group.IsNilpotent.commute_of_orderOf_coprime hcop
  exact congrArg Subtype.val hcomm.eq

/-! ## The nilpotent endgame of §3 Prop. 1 step 3 -/

private lemma key_nilpotent_endgame {F Y P : Subgroup G}
    {p : ℕ} (hF : Group.IsNilpotent ↥F) (hp : p.Prime) (hYF : Y ≤ F) (hPF : P ≤ F)
    (hPp : IsPGroup p P) (hYp : ¬ p ∣ Nat.card ↥Y)
    (hNP : P ≤ Subgroup.normalizer (Y : Set G))
    (hN : Subgroup.normalizer (Y : Set G) ⊓ F ≤ Y ⊔ P) :
    Y = pPrimeCoreSub p F := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `Y ≤ O_{p'}(F)`
  have hYQ : Y ≤ pPrimeCoreSub p F := by
    have h1 : (Y.subgroupOf F) ≤ Work.Fitting.pPrimeCore p ↥F := by
      refine le_pPrimeCore_of_isNilpotent (N := ↥F) hF hp ?_
      rw [show Nat.card ↥(Y.subgroupOf F) = Nat.card ↥Y from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYF).toEquiv]
      exact hYp
    have h2 := Subgroup.map_mono (f := F.subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hYF] at h2
    change Y ≤ (Submission.Blueprint.pPrimeCore p ↥F).map F.subtype
    rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    exact h2
  -- `P ⊓ O_{p'}(F) = ⊥`
  have hPQ : P ⊓ pPrimeCoreSub p F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hzP, hzQ⟩
    have h1 : orderOf z ∣ Nat.card ↥P := by
      rw [← Nat.card_zpowers z]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzP)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have h2 : orderOf z ∣ p ^ k := by rw [← hk]; exact h1
    have h3 : ¬ p ∣ Nat.card ↥(pPrimeCoreSub p F) := by
      change ¬ p ∣ Nat.card ↥((Submission.Blueprint.pPrimeCore p ↥F).map F.subtype)
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective F),
        Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
      intro hd
      exact (Work.Fitting.piCore_isPiNat ↥F (fun q => q ≠ p)) p hp hd rfl
    have h4 : ¬ p ∣ orderOf z := by
      intro hd
      refine h3 (hd.trans ?_)
      rw [← Nat.card_zpowers z]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzQ)
    have h5 : orderOf z = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h2
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero] at hj; exact hj
      · exact absurd (hj ▸ dvd_pow_self p hpos.ne') h4
    simpa using orderOf_eq_one_iff.mp h5
  -- `N_{O_{p'}(F)}(Y) = Y`
  have hNQ : Subgroup.normalizer (Y : Set G) ⊓ pPrimeCoreSub p F = Y := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hzF : z ∈ F := (Subgroup.map_subtype_le _ : pPrimeCoreSub p F ≤ F) hz.2
      have hzsup : z ∈ Y ⊔ P := hN ⟨hz.1, hzF⟩
      have hcoe : ((P ⊔ Y : Subgroup G) : Set G) = (P : Set G) * (Y : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right P Y hNP
      have hzsup' : z ∈ (P ⊔ Y : Subgroup G) := by rw [sup_comm]; exact hzsup
      change z ∈ ((P ⊔ Y : Subgroup G) : Set G) at hzsup'
      rw [hcoe, Set.mem_mul] at hzsup'
      obtain ⟨bb, hb, a, ha, hba⟩ := hzsup'
      have hbbQ : bb ∈ pPrimeCoreSub p F := by
        have : bb = z * a⁻¹ := by rw [← hba]; group
        rw [this]
        exact (pPrimeCoreSub p F).mul_mem hz.2 ((pPrimeCoreSub p F).inv_mem (hYQ ha))
      have hbb1 : bb = 1 := by
        have : bb ∈ P ⊓ pPrimeCoreSub p F := ⟨hb, hbbQ⟩
        rw [hPQ] at this
        exact Subgroup.mem_bot.mp this
      rw [← hba, hbb1, one_mul]
      exact ha
    · exact le_inf (Subgroup.le_normalizer (H := Y)) hYQ
  -- nilpotency of `O_{p'}(F)` and conclusion
  have hQnil : Group.IsNilpotent ↥(pPrimeCoreSub p F) := by
    change Group.IsNilpotent ↥((Submission.Blueprint.pPrimeCore p ↥F).map F.subtype)
    rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (Work.Fitting.pPrimeCore p ↥F) F.subtype
        (Subgroup.subtype_injective F))
  exact (eq_of_normalizer_inf_eq_of_isNilpotent hQnil hYQ hNQ).symm

/-! ## Hypothesis (D1): `p`-subgroups of `E` act fixed-point-freely on `K` -/

private lemma key_pgroup_fpf {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Design.Setup3 G H t W) {K : Subgroup G}
    (hK : (K : Set G) = Kset (twoPoint H t) t)
    (hKD : twoPoint H t ≤ Subgroup.normalizer (K : Set G))
    {p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ (Design.Ecomm H t W).relIndex (Design.Egrp H t W))
    {Q : Subgroup G} (hQE : Q ≤ Design.Egrp H t W) (hQp : IsPGroup p Q)
    {q : G} (hq : q ∈ Q) (hq1 : q ≠ 1) :
    ∀ k ∈ Kset (twoPoint H t) t, q * k * q⁻¹ = k → k = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀, hP₀syl, -, hP₀fpf, -⟩ :=
    h.d1 p hp (by simpa only [Design.Egrp, Design.Ecomm] using hpdvd)
  obtain ⟨R, hQR, hRsyl⟩ := aux_exists_isSylowIn_ge (p := p) hQE hQp
  obtain ⟨g, hgE, hg⟩ := aux_exists_conj_eq_of_isSylowIn_of_isSylowIn (p := p) hRsyl hP₀syl
  have hgD : g ∈ twoPoint H t := (Subgroup.mem_inf.mp hgE).2
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := hKD hgD
  intro k hk hconj
  have hkK : k ∈ K := by
    show k ∈ (K : Set G)
    rw [hK]
    exact hk
  have hk' : g * k * g⁻¹ ∈ Kset (twoPoint H t) t := by
    rw [← hK]
    exact (Subgroup.mem_normalizer_iff.mp hgN k).mp hkK
  have hqP₀ : g * q * g⁻¹ ∈ P₀ := by
    rw [← hg]
    refine Subgroup.mem_map.mpr ⟨q, hQR hq, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hqP₀ne : g * q * g⁻¹ ≠ 1 := by
    intro h1
    refine hq1 ?_
    have h2 : g⁻¹ * (g * q * g⁻¹) * g = q := by group
    rw [h1] at h2
    simpa using h2.symm
  have hconj' : (g * q * g⁻¹) * (g * k * g⁻¹) * (g * q * g⁻¹)⁻¹ = g * k * g⁻¹ := by
    have h1 : g * (q * k * q⁻¹) * g⁻¹ = g * k * g⁻¹ := by rw [hconj]
    calc (g * q * g⁻¹) * (g * k * g⁻¹) * (g * q * g⁻¹)⁻¹
        = g * (q * k * q⁻¹) * g⁻¹ := by group
      _ = g * k * g⁻¹ := h1
  have h1 : g * k * g⁻¹ = 1 := hP₀fpf _ hqP₀ hqP₀ne _ hk' hconj'
  have h2 : k = g⁻¹ * (g * k * g⁻¹) * g := by group
  rw [h1] at h2
  simpa using h2

/-! ## §3 Proposition 1, step 3 -/

theorem sec3_step3_v (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hV : Work.NormalComplement.AppVProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (hN : Work.NormalComplement.Design.NoCentralizedNormal H t)
    (hstep2 : ∀ p : ℕ, p.Prime →
      p ∣ (Work.NormalComplement.Design.Ecomm H t W).relIndex
            (Work.NormalComplement.Design.Egrp H t W) →
      p ∣ Nat.card ↥(Work.NormalComplement.Design.fitSub
            (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))) :
    Work.NormalComplement.Design.FpfOn
      (Work.NormalComplement.Design.fitSub
        (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))
      (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t) := by
  classical
  -- ## standing facts
  have ht : orderOf t = 2 := h.invol
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  obtain ⟨-, -, K, hKset, hKnc, -⟩ := sec3_step1 hFT h hN
  have hDnormK : twoPoint H t ≤ Subgroup.normalizer (K : Set G) := hKnc.2.1
  have hEodd : Odd (Nat.card ↥(Design.Egrp H t W)) :=
    Odd.of_dvd_nat hDodd
      (Subgroup.card_dvd_of_le (show Design.Egrp H t W ≤ twoPoint H t from inf_le_right))
  have hEsol : Group.IsSolvable ↥(Design.Egrp H t W) := hFT ↥(Design.Egrp H t W) hEodd
  haveI hFitNil : Group.IsNilpotent ↥(Work.Fitting.fitting
      ↥(Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)) :=
    Work.Fitting.fitting_isNilpotent ↥(Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)
  have hFnil : Group.IsNilpotent
      ↥(Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective
      (Work.Fitting.fitting ↥(Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))
      (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t).subtype (Subgroup.subtype_injective _))
  -- `V` normalises `E ⊓ V`
  have hVE : Submission.Blueprint.centD H t ≤ Subgroup.normalizer
      (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t : Subgroup G) := by
    have hVH : Submission.Blueprint.centD H t ≤ H := fun v hv =>
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).1).1
    have hVD : Submission.Blueprint.centD H t ≤ twoPoint H t := fun v hv =>
      (Subgroup.mem_inf.mp hv).1
    have h1 : Submission.Blueprint.centD H t ≤
        Subgroup.normalizer (W ⊓ twoPoint H t : Subgroup G) :=
      (le_inf (le_trans hVH h.normal)
        (hVD.trans (Subgroup.le_normalizer (H := twoPoint H t)))).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := W) (K := twoPoint H t))
    exact (le_inf h1 (Subgroup.le_normalizer (H := Submission.Blueprint.centD H t))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := W ⊓ twoPoint H t)
        (K := Submission.Blueprint.centD H t))
  -- ## the main claim: no nontrivial subgroup of `F` has a nontrivial `K`-centralizer
  have key : ∀ Z : Subgroup G,
      Z ≤ Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) →
      Design.CK H t Z ≠ {1} → Z = ⊥ := by
    intro Z hZF hZCK
    -- a prime `p | |E : E'|`
    have hEcomm_ne : Design.Ecomm H t W ≠ Design.Egrp H t W :=
      commutator_ne_of_solvable (Design.Egrp H t W) h.Ene hEsol
    have hrelne : (Design.Ecomm H t W).relIndex (Design.Egrp H t W) ≠ 1 := by
      intro h1
      exact hEcomm_ne
        (le_antisymm (Subgroup.commutator_le_self _) (Subgroup.relIndex_eq_one.mp h1))
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hrelne
    haveI : Fact p.Prime := ⟨hp⟩
    have hpF : p ∣ Nat.card ↥(Design.fitSub
        (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)) := hstep2 p hp hpdvd
    -- a subgroup `P` of order `p` of `F`
    obtain ⟨xF, hxF⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))) p hpF
    set P : Subgroup G := Subgroup.zpowers (xF : G) with hPdef
    have hPF : P ≤ Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) := by
      rw [hPdef]
      exact Subgroup.zpowers_le.mpr xF.2
    have hPcard : Nat.card ↥P = p := by
      rw [hPdef, Nat.card_zpowers, Subgroup.orderOf_coe, hxF]
    have hPp : IsPGroup p P := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [hPcard, pow_one]⟩
    have hPne : P ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥P = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hPcard] at h1
      exact hp.ne_one h1
    -- the maximal element of the family above `Z`
    obtain ⟨Y, hYF, hYCK, hZY, hYmax⟩ : ∃ Y : Subgroup G,
        Y ≤ Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) ∧
        Design.CK H t Y ≠ {1} ∧ Z ≤ Y ∧
        ∀ Z' : Subgroup G,
          Z' ≤ Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) →
          Design.CK H t Z' ≠ {1} → Z ≤ Z' → Nat.card ↥Z' ≤ Nat.card ↥Y := by
      haveI : Fintype G := Fintype.ofFinite G
      let T : Finset (Subgroup G) := Finset.univ.filter (fun Z' : Subgroup G =>
        Z' ≤ Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) ∧
          Design.CK H t Z' ≠ {1} ∧ Z ≤ Z')
      have hT : T.Nonempty := ⟨Z, by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hZF, hZCK, le_refl Z⟩⟩
      obtain ⟨Y, hYT, hYmax⟩ := Finset.exists_max_image T (fun Z' : Subgroup G => Nat.card ↥Z') hT
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hYT
      exact ⟨Y, hYT.1, hYT.2.1, hYT.2.2,
        fun Z' h1 h2 h3 => hYmax Z' (by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h1, h2, h3⟩)⟩
    by_cases hZbot : Z = ⊥
    · exact hZbot
    · exfalso
      have hYne : Y ≠ ⊥ := fun hY => hZbot (le_bot_iff.mp (hZY.trans (le_of_eq hY)))
      -- ## `p ∤ |Y|`
      have hpY : ¬ p ∣ Nat.card ↥Y := by
        intro hdvd
        obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hdvd
        have hyF : (y : G) ∈ Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) :=
          hYF y.2
        have hyE : (y : G) ∈ Design.Egrp H t W := (fitSub_le _ hyF).1
        have hyne_sub : y ≠ 1 := by
          intro h1
          rw [h1, orderOf_one] at hy
          exact hp.ne_one hy.symm
        have hyne : (y : G) ≠ 1 := fun h1 => hyne_sub (Subtype.ext h1)
        have hQp : IsPGroup p (Subgroup.zpowers (y : G)) := by
          rw [IsPGroup.iff_card]
          exact ⟨1, by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, pow_one]⟩
        have hfpf : ∀ k ∈ Kset (twoPoint H t) t, (y : G) * k * (y : G)⁻¹ = k → k = 1 :=
          key_pgroup_fpf h hKset hDnormK hp hpdvd
            (Subgroup.zpowers_le.mpr hyE) hQp (Subgroup.mem_zpowers _) hyne
        refine hYCK (Set.eq_singleton_iff_unique_mem.mpr
          ⟨⟨one_mem_Kset, Subgroup.one_mem _⟩, ?_⟩)
        intro k hk
        exact hfpf k hk.1 (by
          have h1 : (y : G) * k = k * (y : G) :=
            (Subgroup.mem_centralizer_iff.mp hk.2) (y : G) y.2
          have h2 : (y : G) * k * (y : G)⁻¹ = k := by rw [h1]; group
          exact h2)
      -- ## `P` normalises `Y`
      have hPY : P ≤ Subgroup.normalizer (Y : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro a ha b hb
        have h1 : a * b = b * a := key_centralizes hFnil hYF hPF hp hPp hpY a ha b hb
        have h2 : a * b * a⁻¹ = b := by rw [h1]; group
        rw [h2]
        exact hb
      -- ## §1 Lemma 3
      have hNK : ∃ k ∈ Design.NK H t Y, k ≠ 1 := by
        have hne : ∃ k ∈ Design.CK H t Y, k ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hYCK (Set.eq_singleton_iff_unique_mem.mpr
            ⟨⟨one_mem_Kset, Subgroup.one_mem _⟩, fun b hb => hcon b hb⟩)
        obtain ⟨k, hk, hkne⟩ := hne
        exact ⟨k, ⟨hk.1, Subgroup.centralizer_le_normalizer (Y : Set G) hk.2⟩, hkne⟩
      have hfpfNK : Design.FpfOn P (Design.NK H t Y) := by
        intro a ha ha1 k hk hconj
        exact key_pgroup_fpf h hKset hDnormK hp hpdvd
          ((hPF.trans (fitSub_le _)).trans inf_le_left) hPp ha ha1 k hk.1 hconj
      obtain ⟨-, -, -, -, hAinf, hAsup⟩ := sec1_lemma3 (hFT := hFT) (hC4 := hC4) (hMod := hMod)
        (hV := hV) h.sit h.se ht h.notMem hYne
        ((hYF.trans (fitSub_le _)).trans inf_le_right) hNK hPne
        ((hPF.trans (fitSub_le _)).trans inf_le_right) hPY hfpfNK
      set A : Subgroup G := Submission.Blueprint.centD H t ⊓
        Subgroup.normalizer (Y : Set G) ⊓ Subgroup.centralizer (Design.NK H t Y : Set G) with hA
      set V₁ : Subgroup G := Submission.Blueprint.centD H t ⊓
        Subgroup.normalizer (Y : Set G) with hV₁
      have hAinf' : A ⊓ P = ⊥ := by rw [hA]; exact hAinf
      have hAsup' : A ⊔ P = V₁ := by rw [hA, hV₁]; exact hAsup
      -- ## `P ≤ N(A)`
      have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
        ((hPF.trans (fitSub_le _)).trans inf_le_left |>.trans inf_le_right).trans hDnormK
      have hPNY : P ≤ Subgroup.normalizer (Subgroup.normalizer (Y : Set G) : Set G) :=
        le_normalizer_normalizer_of_le_normalizer hPY
      have hPCen : P ≤ Subgroup.normalizer
          (Subgroup.centralizer (Design.NK H t Y : Set G) : Set G) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro c
        constructor
        · intro hc
          refine mem_centralizer_conj hc ?_
          intro z hz
          refine ⟨?_, ?_⟩
          · rw [← hKset]
            simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPK ha)) z).mp
              (show z ∈ K from by
                show z ∈ (K : Set G)
                rw [hKset]
                exact hz.1)
          · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPNY ha)) z).mp hz.2
        · intro hc
          have hmem : ∀ z ∈ Design.NK H t Y, a * z * a⁻¹ ∈ Design.NK H t Y := by
            intro z hz
            refine ⟨?_, ?_⟩
            · rw [← hKset]
              simpa using (Subgroup.mem_normalizer_iff.mp (hPK ha) z).mp
                (show z ∈ K from by
                  show z ∈ (K : Set G)
                  rw [hKset]
                  exact hz.1)
            · simpa using (Subgroup.mem_normalizer_iff.mp (hPNY ha) z).mp hz.2
          have h3 := mem_centralizer_conj (S := Design.NK H t Y) (p := a⁻¹) hc (by
            intro z hz
            simpa using hmem z hz)
          have h4 : a⁻¹ * (a * c * a⁻¹) * (a⁻¹)⁻¹ = c := by group
          rwa [h4] at h3
      have hPN : P ≤ Subgroup.normalizer (A : Set G) := by
        rw [hA]
        refine le_normalizer_inf_of_le_normalizer ?_ hPCen
        exact le_normalizer_inf_of_le_normalizer
          ((hPF.trans (fitSub_le _)).trans inf_le_right |>.trans (Subgroup.le_normalizer))
          hPNY
      -- ## `N_F(Y) = Y ⊔ P`
      have hcoedecomp : ((P ⊔ A : Subgroup G) : Set G) = (P : Set G) * (A : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right P A hPN
      have hNF : Subgroup.normalizer (Y : Set G) ⊓
          Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) = Y ⊔ P := by
        refine le_antisymm ?_ ?_
        · intro y hy
          have hyV : y ∈ V₁ := ⟨(fitSub_le _ hy.2).2, hy.1⟩
          have hyAP : y ∈ A ⊔ P := by rw [hAsup']; exact hyV
          have hyPA : y ∈ P ⊔ A := by rw [sup_comm]; exact hyAP
          change y ∈ ((P ⊔ A : Subgroup G) : Set G) at hyPA
          rw [hcoedecomp, Set.mem_mul] at hyPA
          obtain ⟨pp, hppP, a, haA, hpa⟩ := hyPA
          have hppNF : pp ∈ Subgroup.normalizer (Y : Set G) ⊓
              Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) :=
            ⟨hPY hppP, hPF hppP⟩
          have haNF : a ∈ Subgroup.normalizer (Y : Set G) ⊓
              Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) := by
            have h1 : a = pp⁻¹ * y := by rw [← hpa]; group
            rw [h1]
            exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hppNF) hy
          have haY : a ∈ Y := by
            have hCK : Design.CK H t (Y ⊔ Subgroup.zpowers a) ≠ {1} := by
              intro hEq
              have h2 : Design.CK H t Y ⊆ Design.CK H t (Y ⊔ Subgroup.zpowers a) := by
                intro k hk
                refine ⟨hk.1, ?_⟩
                have hkNK : k ∈ Design.NK H t Y :=
                  ⟨hk.1, Subgroup.centralizer_le_normalizer (Y : Set G) hk.2⟩
                have hac : k * a = a * k := (Subgroup.mem_centralizer_iff.mp haA.2) k hkNK
                have hksub : k ∈ Subgroup.centralizer ((Y : Set G) ∪ {a}) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro b hb
                  rcases hb with hbY | hba
                  · exact (Subgroup.mem_centralizer_iff.mp hk.2) b hbY
                  · rw [Set.mem_singleton_iff] at hba
                    subst hba
                    exact hac.symm
                have hcl : Subgroup.closure ((Y : Set G) ∪ {a}) =
                    Y ⊔ Subgroup.closure {a} := by
                  rw [Subgroup.closure_union, Subgroup.closure_eq]
                have hzeq : (Y ⊔ Subgroup.zpowers a : Subgroup G) =
                    Subgroup.closure ((Y : Set G) ∪ {a}) := by
                  rw [Subgroup.zpowers_eq_closure, ← hcl]
                rw [hzeq, Subgroup.centralizer_closure]
                exact hksub
              rw [hEq] at h2
              refine hYCK (Set.eq_singleton_iff_unique_mem.mpr
                ⟨⟨one_mem_Kset, Subgroup.one_mem _⟩, ?_⟩)
              intro k hk
              exact Set.mem_singleton_iff.mp (h2 hk)
            have hle : Y ⊔ Subgroup.zpowers a ≤
                Design.fitSub (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) :=
              sup_le hYF (Subgroup.zpowers_le.mpr haNF.2)
            have hmax := hYmax (Y ⊔ Subgroup.zpowers a) hle hCK (le_sup_of_le_left hZY)
            have heq : Y ⊔ Subgroup.zpowers a = Y := by
              have h := Subgroup.eq_of_le_of_card_ge (H := Y) (K := Y ⊔ Subgroup.zpowers a)
                le_sup_left hmax
              exact h.symm
            rw [← heq]
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
          rw [← hpa]
          have := Subgroup.mul_mem_sup hppP haY
          rwa [sup_comm] at this
        · refine sup_le (le_inf (Subgroup.le_normalizer (H := Y)) hYF) ?_
          exact le_inf hPY hPF
      -- ## endgame
      have hYeq : Y = pPrimeCoreSub p (Design.fitSub
          (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)) :=
        key_nilpotent_endgame (F := Design.fitSub
            (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))
          hFnil hp hYF hPF hPp hpY hPY (le_of_eq hNF)
      have hVY : Submission.Blueprint.centD H t ≤ Subgroup.normalizer (Y : Set G) := by
        rw [hYeq]
        exact normalizer_le_normalizer_pPrimeCoreSub_fitSub hp hVE
      exact hYCK (hN Y hYne ((hYF.trans (fitSub_le _)).trans inf_le_right) hVY)
  -- ## conclude
  intro x hxF hx1 k hk hconv
  by_contra hk1
  have hX0F : Subgroup.zpowers x ≤ Design.fitSub
      (Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) := Subgroup.zpowers_le.mpr hxF
  have hX0CK : Design.CK H t (Subgroup.zpowers x) ≠ {1} := by
    intro hEq
    have hmem : k ∈ Design.CK H t (Subgroup.zpowers x) := by
      refine ⟨hk, ?_⟩
      show k ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hcomm : Commute x k := by
        rw [commute_iff_eq]
        calc x * k = (x * k * x⁻¹) * x := by group
          _ = k * x := by rw [hconv]
      exact (hcomm.zpow_left n).eq
    rw [hEq] at hmem
    exact hk1 (Set.mem_singleton_iff.mp hmem)
  have hbot := key (Subgroup.zpowers x) hX0F hX0CK
  have hxmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  rw [hbot] at hxmem
  exact hx1 (Subgroup.mem_bot.mp hxmem)

end Work.NormalComplement
