/-
# Peterfalvi I Ch. III §2 Lemma 1 (`Work.NormalComplement.sec2_one`)

This file proves `sec2_one`, Peterfalvi I Ch. III §2 Lemma 1 (p. 176), in the form used by the
`NormalComplement` area: with `D = twoPoint H t`, `E = W ⊓ D`, `V = centD H t`, under hypothesis
(D1) one has `Kset D t ⊆ E'`, `E^t = E`, and every element of `(E ⊓ V) ∖ E'` acts
fixed-point-freely on `K = Kset D t`.

The route is the source's:

* `D` has odd order (`IsStronglyEmbedded` at `t ∉ H`), so `E ≤ D` is odd; `hFT` makes `↥E`
  solvable, hence `E' = ⁅E,E⁆ < E` and there is a prime `p ∣ [E : E']`;
* (D1) provides a `p`-Sylow `P ≤ E ⊓ V` of `E` acting fixed-point-freely on `K`;
* **App. I (5)(d)** — in the corrected fixed-point-free form of `C_K(P) = 1`, proved in
  `Work.NormalComplement.appI_five_d_corrected` — with `X = D` gives `K ⊆ E'` and `E^t = E`;
* for `x ∈ (E ⊓ V) ∖ E'` one takes a prime `q ∣ orderOf x` with `q ∣ [E : E']` (the image of `x`
  in `E/E'` is nontrivial), a `q`-Sylow `Q ≤ E ⊓ V` of `E` fixed-point-free on `K` (D1), moves a
  `q`-power of `x` into a `V`-conjugate of `Q` (App. I (2), `appI_two`) and concludes `C_K(x) = 1`.
-/
import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_two
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.commutator_ne_of_solvable
import Submission.Work.NormalComplement.commutator_subgroupOf_eq_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ## Elementary helpers -/

lemma sq_eq_one_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [ht] at h
  simpa [pow_two] using h

/-- Powers of an element commuting (by conjugation) with `k` also commute with `k`. -/
lemma pow_conj_eq_of_conj_eq {x k : G} (h : x * k * x⁻¹ = k) :
    ∀ m : ℕ, x ^ m * k * (x ^ m)⁻¹ = k := by
  intro m
  induction m with
  | zero => simp
  | succ j ih =>
      have h1 : x ^ (j + 1) * k * (x ^ (j + 1))⁻¹ = x ^ j * (x * k * x⁻¹) * (x ^ j)⁻¹ := by
        rw [pow_succ]; group
      rw [h1, h, ih]

/-- `t` normalises `D = twoPoint H t` when `t` is an involution.  (Private: `sec4_P2d` exports a
public copy of this lemma; the two clash when both are imported.) -/
private lemma normalizedBy_twoPoint (H : Subgroup G) {t : G} (ht : orderOf t = 2) :
    NormalizedBy t (Submission.Blueprint.twoPoint H t) := by
  have ht2 : t * t = 1 := sq_eq_one_of_orderOf_eq_two ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro x hx
  rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf] at hx ⊢
  obtain ⟨hxH, hxHt⟩ := hx
  rw [Submission.Blueprint.conj, Subgroup.mem_map] at hxHt ⊢
  obtain ⟨h, hh, hxh⟩ := hxHt
  have hx_eq : x = t * h * t⁻¹ := by
    have := hxh.symm
    simpa [MulAut.conj_apply] using this
  constructor
  · have hkey : t * x * t⁻¹ = h := by
      rw [hx_eq, hti]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2]; group
    rw [hkey]; exact hh
  · exact ⟨x, hxH, by simp [MulAut.conj_apply]⟩

/-! ## A prime divisor of `[E : E']` dividing the order of a given element -/

/-- If `x ∈ E` is not in the commutator subgroup `⁅E,E⁆`, then some prime dividing `orderOf x`
also divides `[E : ⁅E,E⁆]`. -/
theorem exists_prime_dvd_relIndex_of_notMem_commutator {E : Subgroup G} {x : G} (hx : x ∈ E)
    (hxE' : x ∉ ((⁅E, E⁆ : Subgroup G) : Set G)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ orderOf x ∧ q ∣ (⁅E, E⁆).relIndex E := by
  haveI : Fintype ((↥E) ⧸ commutator ↥E) := Fintype.ofFinite _
  have hsub : (⁅E, E⁆).subgroupOf E = commutator ↥E := commutator_subgroupOf_eq_commutator E
  have hxE'' : (⟨x, hx⟩ : ↥E) ∉ commutator ↥E := by
    intro h
    exact hxE' (Subgroup.mem_subgroupOf.mp (hsub.symm ▸ h))
  let y : (↥E) ⧸ commutator ↥E := QuotientGroup.mk' (commutator ↥E) ⟨x, hx⟩
  have hyne : y ≠ 1 := by
    intro h
    have hker : (⟨x, hx⟩ : ↥E) ∈ (QuotientGroup.mk' (commutator ↥E)).ker :=
      MonoidHom.mem_ker.mpr h
    rw [QuotientGroup.ker_mk'] at hker
    exact hxE'' hker
  have hordne : orderOf y ≠ 1 := fun h => hyne (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqy⟩ := Nat.exists_prime_and_dvd hordne
  refine ⟨q, hq, ?_, ?_⟩
  · refine dvd_trans hqy ?_
    have h1 : orderOf y ∣ orderOf (⟨x, hx⟩ : ↥E) := orderOf_map_dvd _ _
    have h2 : orderOf (⟨x, hx⟩ : ↥E) = orderOf x :=
      (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥E)).symm
    rwa [h2] at h1
  · have h2 : orderOf y ∣ Nat.card ((↥E) ⧸ commutator ↥E) := by
      simpa using orderOf_dvd_card (x := y)
    have hqcard : q ∣ Nat.card ((↥E) ⧸ commutator ↥E) := dvd_trans hqy h2
    have hrel : (⁅E, E⁆).relIndex E = (commutator ↥E).index := by rw [← hsub]; rfl
    rw [hrel, Subgroup.index_eq_card]
    exact hqcard

/-! ## The fixed-point-free action of `(E ⊓ V) ∖ E'` on `K` -/

/-- **Local step of §2 Lemma 1.**  `x ∈ E`, `x` commutes with `t` and `q ∣ orderOf x`, where `q` is
a prime for which (D1) provides a `q`-Sylow `P ≤ E ⊓ V` of `E` acting fixed-point-freely on
`K = Kset D t`.  Then `x` acts fixed-point-freely on `K`. -/
theorem kset_centralizer_eq_one_of_isSylowIn {t : G} (ht : orderOf t = 2)
    {D E : Subgroup G} (hE : E ≤ D) (hEnorm : NormalizedBy t E) (hEodd : Odd (Nat.card E))
    {q : ℕ} (hq : q.Prime) {P : Subgroup G} (hPsyl : IsSylowIn q P E)
    (hPV : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ D)
    (hfpf : ∀ x ∈ P, x ≠ 1 → ∀ k ∈ Kset D t, x * k * x⁻¹ = k → k = 1)
    {x : G} (hxE : x ∈ E) (hxV : x ∈ Subgroup.centralizer ({t} : Set G)) (hxq : q ∣ orderOf x) :
    ∀ k ∈ Kset D t, x * k * x⁻¹ = k → k = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro k hk hkx
  obtain ⟨m, hm⟩ := hxq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact absurd hm (ne_of_gt (orderOf_pos x))
  -- the `q`-power `x ^ m` has order `q`
  have hxmne : x ^ m ≠ 1 := by
    intro h
    have h1 : orderOf x ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
    have h2 : m ∣ orderOf x := by rw [hm]; exact dvd_mul_left m q
    have h3 : orderOf x = m := Nat.dvd_antisymm h1 h2
    have h4 : q * m = m := by rw [← hm, h3]
    have h5 : q * m = 1 * m := by rw [one_mul, h4]
    exact hq.ne_one (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) h5)
  have hxmq : (x ^ m) ^ q = 1 := by
    calc (x ^ m) ^ q = x ^ (m * q) := (npow_mul x m q).symm
      _ = 1 := by rw [Nat.mul_comm, ← hm]; exact pow_orderOf_eq_one x
  have horder : orderOf (x ^ m) = q := by
    have hdvd : orderOf (x ^ m) ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hxmq
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hxmne
    · exact h1
  have hxmE : x ^ m ∈ E := by
    have hall : ∀ j : ℕ, x ^ j ∈ E := by
      intro j
      induction j with
      | zero => simp
      | succ i ih => rw [pow_succ]; exact E.mul_mem ih hxE
    exact hall m
  have hxt : (MulAut.conj t) x = x := by
    have h : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxV
    rw [MulAut.conj_apply]
    rw [← h]; group
  have hxmt : (MulAut.conj t) (x ^ m) = x ^ m := by rw [map_pow, hxt]
  have hzp : IsPGroup q (Subgroup.zpowers (x ^ m)) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, horder, pow_one]⟩
  have hzple : Subgroup.zpowers (x ^ m) ≤ E := Subgroup.zpowers_le.mpr hxmE
  have hzpnorm : NormalizedBy t (Subgroup.zpowers (x ^ m)) := by
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h2 : t * (x ^ m) ^ j * t⁻¹ = (x ^ m) ^ j := by
      rw [← MulAut.conj_apply, map_zpow, hxmt]
    rw [h2]
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩
  obtain ⟨-, hconj2, hge2⟩ := appI_two (d := 2) Nat.prime_two ht hEnorm
    (Nat.coprime_two_right.mpr hEodd) hq
  obtain ⟨Q, hQsyl, hQnorm, hQge⟩ := hge2 (Subgroup.zpowers (x ^ m)) hzp hzple hzpnorm
  have hPnorm : NormalizedBy t P := by
    intro u hu
    have h : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp (hPV hu).1
    rw [show t * u * t⁻¹ = u by rw [← h]; group]
    exact hu
  obtain ⟨v, hvC, hvP⟩ := hconj2 Q P hQsyl hQnorm hPsyl hPnorm
  have hyQ : x ^ m ∈ Q := hQge (Subgroup.mem_zpowers (x ^ m))
  have hvy : v * (x ^ m) * v⁻¹ ∈ P := by
    rw [hvP]
    exact ⟨x ^ m, hyQ, by simp [MulAut.conj_apply]⟩
  have hvyn : v * (x ^ m) * v⁻¹ ≠ 1 := by
    intro h
    apply hxmne
    have := congrArg (fun z => v⁻¹ * z * v) h
    simpa [mul_assoc] using this
  have hvD : v ∈ D := hE hvC.2
  have hvk : v * k * v⁻¹ ∈ Kset D t := by
    obtain ⟨hkD, hkinv⟩ := hk
    have hvt : t * v * t⁻¹ = v := by
      have h : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hvC.1
      rw [← h]; group
    refine ⟨D.mul_mem (D.mul_mem hvD hkD) (D.inv_mem hvD), ?_⟩
    have hvi : t * v⁻¹ * t⁻¹ = v⁻¹ := by
      calc t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ := by group
        _ = v⁻¹ := by rw [hvt]
    calc t * (v * k * v⁻¹) * t⁻¹ = (t * v * t⁻¹) * (t * k * t⁻¹) * (t * v⁻¹ * t⁻¹) := by group
      _ = v * k⁻¹ * v⁻¹ := by rw [hvt, hkinv, hvi]
      _ = (v * k * v⁻¹)⁻¹ := by group
  have hmain : (v * (x ^ m) * v⁻¹) * (v * k * v⁻¹) * (v * (x ^ m) * v⁻¹)⁻¹ = v * k * v⁻¹ := by
    have h1 : (x ^ m) * k * (x ^ m)⁻¹ = k := pow_conj_eq_of_conj_eq hkx m
    calc (v * (x ^ m) * v⁻¹) * (v * k * v⁻¹) * (v * (x ^ m) * v⁻¹)⁻¹
        = v * ((x ^ m) * k * (x ^ m)⁻¹) * v⁻¹ := by group
      _ = v * k * v⁻¹ := by rw [h1]
  have h1 := hfpf (v * (x ^ m) * v⁻¹) hvy hvyn (v * k * v⁻¹) hvk hmain
  have := congrArg (fun z => v⁻¹ * z * v) h1
  simpa [mul_assoc] using this

/-! ## Main theorem -/

set_option linter.unusedVariables false in
/-- **Peterfalvi I Ch. III §2 Lemma 1** (p.176), with the data unpacked (no `_design` structures):
under (D1) and `E = W ⊓ D ≠ 1`, one has `K ⊆ E'`, `E^t = E`, and every element of `(E ∩ V) ∖ E'`
acts fixed-point-freely on `K = J(D,t)`; here `D = twoPoint H t`, `E = W ⊓ D`, `E' = ⁅E,E⁆`,
`V = centD H t`.

Route: `E ≠ ⊥` is odd (`IsStronglyEmbedded` at `t ∉ H`), so `↥E` is solvable (`hFT`) and `E' < E`;
(D1) applies to any prime `p ∣ [E : E']` and gives a `p`-Sylow `P ≤ E ⊓ V` of `E` acting
fixed-point-freely on `K`; App. I (5)(d) — in the *corrected* form with `C_K(P) = 1` as
`∀ k ∈ K, (∀ q ∈ P, q*k*q⁻¹ = k) → k = 1` — with `X = D`, `d = 2`,
gives `K ⊆ E'` and `E^t = E`.  For `x ∈ (E ⊓ V) ∖ E'`, take a prime `q ∣ orderOf x` with
`q ∣ [E:E']` and the `q`-Sylow `P ≤ E ⊓ V` of `E` fixed-point-free on `K` (D1); `x` lies in a
`V`-conjugate of `P` (App. I (2), `Work.NormalComplement.appI_two`), so `C_K(x) = 1` follows from
fixed-point-freeness. -/
theorem sec2_one (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {W : Subgroup G} (hWH : W ≤ H)
    (hWn : H ≤ Subgroup.normalizer (W : Set G))
    (hWD : W ⊔ Submission.Blueprint.twoPoint H t = H)
    (hEne : W ⊓ Submission.Blueprint.twoPoint H t ≠ ⊥)
    (hD1 : Work.NormalComplement.IsD1 H t W) :
    Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ⊆
        ((⁅W ⊓ Submission.Blueprint.twoPoint H t,
           W ⊓ Submission.Blueprint.twoPoint H t⁆ : Subgroup G) : Set G) ∧
      (∀ e ∈ W ⊓ Submission.Blueprint.twoPoint H t,
        t * e * t⁻¹ ∈ W ⊓ Submission.Blueprint.twoPoint H t) ∧
      ∀ x ∈ (W ⊓ Submission.Blueprint.twoPoint H t) ⊓ Submission.Blueprint.centD H t,
        x ∉ ((⁅W ⊓ Submission.Blueprint.twoPoint H t,
              W ⊓ Submission.Blueprint.twoPoint H t⁆ : Subgroup G) : Set G) →
        ∀ k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t,
          x * k * x⁻¹ = k → k = 1 := by
  let D : Subgroup G := Submission.Blueprint.twoPoint H t
  let E : Subgroup G := W ⊓ D
  let V : Subgroup G := Submission.Blueprint.centD H t
  change Work.NormalComplement.Kset D t ⊆ ((⁅E, E⁆ : Subgroup G) : Set G) ∧
      (∀ e ∈ E, t * e * t⁻¹ ∈ E) ∧
      ∀ x ∈ E ⊓ V, x ∉ ((⁅E, E⁆ : Subgroup G) : Set G) →
        ∀ k ∈ Work.NormalComplement.Kset D t, x * k * x⁻¹ = k → k = 1
  have hDodd : Odd (Nat.card ↥D) := hH.2.2 t htH
  have hED : E ≤ D := by show W ⊓ D ≤ D; exact inf_le_right
  have hEodd : Odd (Nat.card ↥E) := Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hED)
  have hEsolv : Group.IsSolvable ↥E := hFT ↥E hEodd
  have hEne' : E ≠ ⊥ := hEne
  have hcommle : ⁅E, E⁆ ≤ E := Subgroup.commutator_le.mpr (fun a ha b hb =>
    E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb))
  have hE'ne : ⁅E, E⁆ ≠ E := commutator_ne_of_solvable E hEne' hEsolv
  have hrelne : (⁅E, E⁆).relIndex E ≠ 1 := by
    intro h1
    exact hE'ne (le_antisymm hcommle (Subgroup.relIndex_eq_one.mp h1))
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hrelne
  obtain ⟨P, hPsyl, hPVc, hPfpf, hPcyc⟩ := hD1 p hp hpdvd
  -- ### `E` is normal in `D`
  have hEnormD : ∀ x ∈ D, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hxD e heE
    have hxD' : x ∈ H ⊓ Submission.Blueprint.conj t H := hxD
    have hxW : x ∈ Subgroup.normalizer (W : Set G) := hWn hxD'.1
    have heE' : e ∈ W ∧ e ∈ D := Subgroup.mem_inf.mp heE
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hxW e).mp heE'.1,
        D.mul_mem (D.mul_mem hxD heE'.2) (D.inv_mem hxD)⟩
  -- ### `t` normalises `D`
  have htD : NormalizedBy t D := normalizedBy_twoPoint H ht
  have hcopD : Nat.Coprime (Nat.card ↥D) 2 := Nat.coprime_two_right.mpr hDodd
  have hDsolv : Group.IsSolvable ↥D := hFT ↥D hDodd
  have hKappKset : Kapp t D = Kset D t :=
    ((appI_one (d := 2) Nat.prime_two ht htD hcopD).2 rfl).1
  -- ### `C_K(P) = 1` in the fixed-point-free form
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hdivE : p ∣ Nat.card ↥E := dvd_trans hpdvd (Subgroup.relIndex_dvd_card _ _)
    have hcard : Nat.card ↥E = (P.subgroupOf E).index * Nat.card ↥P := by
      rw [← Subgroup.index_mul_card (P.subgroupOf E)]
      congr 1
      exact card_subgroupOf_eq_of_le hPsyl.2.1
    rw [hcard] at hdivE
    rcases hp.dvd_mul.mp hdivE with h | h
    · exact hPsyl.2.2 h
    · rw [(Subgroup.card_eq_one).mpr hbot] at h
      exact hp.not_dvd_one h
  have hCK : ∀ k ∈ Kapp t D, (∀ q ∈ P, q * k * q⁻¹ = k) → k = 1 := by
    intro k hk hfix
    have hkKset : k ∈ Kset D t := by rw [← hKappKset]; exact hk
    obtain ⟨z, hzP, hzne⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hPne
    exact hPfpf z hzP hzne k hkKset (hfix z hzP)
  have hPV' : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ D :=
    le_inf (fun u hu => (Subgroup.mem_inf.mp (hPVc hu)).2)
      (fun u hu => (Subgroup.mem_inf.mp (hPVc hu)).1)
  -- ### App. I (5)(d), corrected form
  obtain ⟨hKapp_sub, hEt⟩ :=
    appI_five_d_corrected ht htD hDodd hDsolv hED hEnormD hPsyl hPV' hp hCK
  refine ⟨?_, hEt, ?_⟩
  · rw [← hKappKset]
    exact hKapp_sub
  · intro x hx hxE' k hk hkx
    have hxE : x ∈ E := hx.1
    have hxV : x ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hx.2).2
    obtain ⟨q, hq, hqx, hqrel⟩ := exists_prime_dvd_relIndex_of_notMem_commutator hxE hxE'
    obtain ⟨Q, hQsyl, hQVc, hQfpf, hQcyc⟩ := hD1 q hq hqrel
    have hQPV : Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ D :=
      le_inf (fun u hu => (Subgroup.mem_inf.mp (hQVc hu)).2)
        (fun u hu => (Subgroup.mem_inf.mp (hQVc hu)).1)
    exact kset_centralizer_eq_one_of_isSylowIn ht hED hEt hEodd hq hQsyl hQPV hQfpf
      hxE hxV hqx k hk hkx

end Work.NormalComplement
