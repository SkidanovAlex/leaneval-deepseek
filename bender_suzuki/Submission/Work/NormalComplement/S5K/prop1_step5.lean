import Mathlib
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.appI_five_c_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.S5K

open Work.NormalComplement

/-! ## Auxiliary group theory: a `P`-invariant Sylow `r`-subgroup of `A` when `V = A ⋊ P` -/

/-- The image of an `r`-Sylow subgroup of `↥A` is an ambient `r`-Sylow subgroup of `A`. -/
theorem isSylowIn_map_subtype_of_sylow {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {A : Subgroup G} (Q : Sylow r ↥A) :
    IsSylowIn r (Q.1.map A.subtype) A := by
  refine ⟨Q.isPGroup'.map _, Subgroup.map_subtype_le _, ?_⟩
  have hsub : (Q.1.map A.subtype).subgroupOf A = Q.1 := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨q, hq, hqeq⟩
      have hq' : q = x := Subtype.ext hqeq
      rwa [hq'] at hq
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hsub]
  exact Sylow.not_dvd_index Q

/-- Every subgroup `A` of a finite group has an `r`-Sylow subgroup (in the ambient sense). -/
theorem exists_isSylowIn_of_prime {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (A : Subgroup G) : ∃ R : Subgroup G, IsSylowIn r R A := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r ↥A))
  exact ⟨Q.1.map A.subtype, isSylowIn_map_subtype_of_sylow Q⟩

/-- Conjugating a normalizer: the image of `N_G(R)` under conjugation by `v` is `N_G(R^v)`. -/
theorem map_conj_le_normalizer {G : Type*} [Group G] {R P₁ : Subgroup G} {v : G}
    (h : P₁ ≤ Subgroup.normalizer (R : Set G)) :
    P₁.map (MulAut.conj v).toMonoidHom ≤
      Subgroup.normalizer ((R.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) :=
  (Subgroup.map_mono h).trans
    (le_of_eq (Subgroup.map_normalizer_eq_of_bijective R (MulAut.conj v).bijective))

/-- **Existence of a `P`-invariant Sylow.**  Let `V = A ⋊ P` be a semidirect product inside a
finite group `G`: `A ⊔ P = V`, `A ⊓ P = ⊥`, `V ≤ N_G(A)`, `|P| = p` a prime and `p ∤ |A|`.  Then for
every prime `r ≠ p` there is an `r`-Sylow subgroup `R` of `A` normalised by `P`.

`|V| = |A|·p`, so `[V : A] = p` and the `p`-Sylow subgroups of `V` have order `p`.  Take
`R ∈ Syl_r(A)`; the Frattini argument in `V` (with `A ⊴ V`, `Work.NormalComplement.frattini_decomp`)
gives `V = A·N_V(R)`, whence `[N_V(R) : N_A(R)] = [V : A] = p`; so `N_V(R)` contains a subgroup of
order `p`, i.e. a `p`-Sylow of `V`, and conjugating it to `P` by Sylow's theorem in `V`
(`Work.NormalComplement.exists_conj_map_eq_of_isSylowIn`) produces a `P`-invariant conjugate of
`R`. -/
theorem exists_isSylowIn_normalizer {G : Type} [Group G] [Finite G]
    {A P V : Subgroup G} {p r : ℕ}
    (hsup : A ⊔ P = V) (hinf : A ⊓ P = ⊥) (hAV : V ≤ Subgroup.normalizer (A : Set G))
    (hp : p.Prime) (hPcard : Nat.card P = p) (hpdvd : ¬ p ∣ Nat.card ↥A)
    (hr : r.Prime) (hrp : r ≠ p) :
    ∃ R : Subgroup G, IsSylowIn r R A ∧ P ≤ Subgroup.normalizer (R : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hA_le_V : A ≤ V := hsup ▸ le_sup_left
  have hP_le_V : P ≤ V := hsup ▸ le_sup_right
  have hPV : P ≤ Subgroup.normalizer (A : Set G) := hP_le_V.trans hAV
  -- `|V| = |A| * p`
  have hVcard : Nat.card ↥V = Nat.card ↥A * p := by
    have h := card_sup_mul_card_inf (H := A) (K := P) hPV
    rw [hsup, hinf, Subgroup.card_bot, mul_one, hPcard] at h
    exact h
  -- a Sylow `r`-subgroup `R` of `A`
  obtain ⟨R, hR⟩ := exists_isSylowIn_of_prime hr A
  -- Frattini: `V = A ⊔ N_V(R)`
  have hnormA : ∀ y ∈ V, ∀ m ∈ A, y * m * y⁻¹ ∈ A :=
    fun y hy m hm => Subgroup.le_normalizer_iff.mp hAV y hy m hm
  have hV_eq : V = A ⊔ (Subgroup.normalizer (R : Set G) ⊓ V) := by
    refine le_antisymm ?_ (sup_le hA_le_V inf_le_right)
    intro y hy
    obtain ⟨m, hm, n, hn, hmn⟩ := frattini_decomp hr hA_le_V hnormA hR y hy
    rw [hmn]
    exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hn)
  have hN_le_normA : Subgroup.normalizer (R : Set G) ⊓ V ≤ Subgroup.normalizer (A : Set G) :=
    inf_le_right.trans hAV
  -- `|N_V(R)| = p * |A ⊓ N_V(R)|`
  have hNcard : Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ V) =
      p * Nat.card ↥(A ⊓ (Subgroup.normalizer (R : Set G) ⊓ V)) := by
    have hcard := card_sup_mul_card_inf (H := A)
      (K := Subgroup.normalizer (R : Set G) ⊓ V) hN_le_normA
    rw [← hV_eq] at hcard
    have h2 : Nat.card ↥A * (p * Nat.card ↥(A ⊓ (Subgroup.normalizer (R : Set G) ⊓ V))) =
        Nat.card ↥A * Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ V) := by
      rw [← hcard, hVcard]
      ring
    exact (Nat.mul_left_cancel (Nat.card_pos (α := ↥A)) h2).symm
  -- an element `x` of order `p` in `N_V(R)`
  obtain ⟨x, hxN, hxord⟩ : ∃ x ∈ Subgroup.normalizer (R : Set G) ⊓ V, orderOf x = p := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p
      (show p ∣ Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ V) from
        ⟨Nat.card ↥(A ⊓ (Subgroup.normalizer (R : Set G) ⊓ V)), hNcard⟩)
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  have hzNR : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr hxN.1
  have hzV : Subgroup.zpowers x ≤ V := Subgroup.zpowers_le.mpr hxN.2
  -- `⟨x⟩` and `P` are both `p`-Sylow subgroups of `V`
  have hzcard : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hzsyl : IsSylowIn p (Subgroup.zpowers x) V := by
    refine ⟨?_, hzV, ?_⟩
    · rw [IsPGroup.iff_card]
      exact ⟨1, by rw [pow_one, hzcard]⟩
    · intro hdvd
      have hrel := relIndex_mul_card_of_le' hzV
      rw [hzcard, hVcard] at hrel
      have : (Subgroup.zpowers x).relIndex V = Nat.card ↥A :=
        Nat.mul_right_cancel hp.pos hrel
      exact hpdvd (this ▸ hdvd)
  have hPsyl : IsSylowIn p P V := by
    refine ⟨?_, hP_le_V, ?_⟩
    · rw [IsPGroup.iff_card]
      exact ⟨1, by rw [pow_one, hPcard]⟩
    · intro hdvd
      have hrel := relIndex_mul_card_of_le' hP_le_V
      rw [hPcard, hVcard] at hrel
      have : P.relIndex V = Nat.card ↥A := Nat.mul_right_cancel hp.pos hrel
      exact hpdvd (this ▸ hdvd)
  -- Sylow conjugacy in `V`
  obtain ⟨v, hvV, hconj⟩ := exists_conj_map_eq_of_isSylowIn hp hzsyl hPsyl
  have hAv : A.map (MulAut.conj v).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAV hvV)
  refine ⟨R.map (MulAut.conj v).toMonoidHom, ?_, ?_⟩
  · have hR' := isSylowIn_map_conj hR v
    rwa [hAv] at hR'
  · intro q hq
    rw [← hconj] at hq
    exact map_conj_le_normalizer hzNR hq

/-! ## App. I (5)(a) in the setting of `Setup45A` -/

/-- **Peterfalvi I App. I (5)(a)** for `D = twoPoint H t`: with `K = Kset D t` and
`⟨K⟩ = Kgrp D t`, the prime divisors of `|⟨K⟩|` and of `|K|` coincide. -/
theorem prime_dvd_card_Kgrp_iff (hFT : Submission.Blueprint.FeitThompsonProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G} (h : Design.Setup45A G H t W p P A) (q : ℕ) (hq : q.Prime) :
    (q ∣ Nat.card ↥(Kgrp (twoPoint H t) t) ↔ q ∣ (Kset (twoPoint H t) t).ncard) := by
  have htD : NormalizedBy t (twoPoint H t) :=
    twoPoint_normalizedBy (twoPoint_mul_self h.invol)
  have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcop : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hodd
  have hsolv : Group.IsSolvable ↥(twoPoint H t) := hFT ↥(twoPoint H t) hodd
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcop).2 rfl).1
  have hKg : Kgrp (twoPoint H t) t = Subgroup.closure (Kapp t (twoPoint H t)) := by
    rw [Kgrp, hKappKset]
  rw [hKg, ← hKappKset]
  exact appI_five_a Nat.prime_two h.invol htD hcop hsolv q hq

/-- `p ∤ |⟨K⟩|`: `P` acts fixed-point-freely on `K = Kset D t`, so `p ∤ |K|`
(`Work.NormalComplement.not_dvd_ncard_Kapp`), and App. I (5)(a) transfers this to `⟨K⟩`. -/
theorem not_dvd_p_card_Kgrp (hFT : Submission.Blueprint.FeitThompsonProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G} (h : Design.Setup45A G H t W p P A) :
    ¬ p ∣ Nat.card ↥(Kgrp (twoPoint H t) t) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have htD : NormalizedBy t (twoPoint H t) :=
    twoPoint_normalizedBy (twoPoint_mul_self h.invol)
  have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcop : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hodd
  have hsolv : Group.IsSolvable ↥(twoPoint H t) := hFT ↥(twoPoint H t) hodd
  have hcen_comm : Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t = centD H t := by
    rw [centD, inf_comm]
  have hP_le_V : P ≤ centD H t := le_trans h.P_le inf_le_right
  have hPp : IsPGroup p ↥P := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [pow_one]; exact h.P_card⟩
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h.P_card] at h1
    exact h.prime.ne_one h1
  have hP_fixX : P ≤ fixX t (twoPoint H t) := by
    have : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := by
      rw [hcen_comm]; exact hP_le_V
    exact this
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcop).2 rfl).1
  have hKg : Kgrp (twoPoint H t) t = Subgroup.closure (Kapp t (twoPoint H t)) := by
    rw [Kgrp, hKappKset]
  have hfpfKapp : ∀ k ∈ Kapp t (twoPoint H t), (∀ u ∈ P, u * k * u⁻¹ = k) → k = 1 :=
    kapp_fixed_eq_one_of_fpf hP_ne_bot
      (fun u hu hu1 k hk hfix => by
        refine h.P_fpf u hu hu1 k ?_ hfix
        rwa [hKappKset] at hk)
  rw [hKg]
  exact not_dvd_card_closureKapp h.prime Nat.prime_two h.invol htD hcop hsolv
    hP_fixX hPp hfpfKapp

/-! ## The counting step -/

/-- **Counting step of §4 Prop. 1 step 5.**  Let `r` be a prime not dividing `p`, and let
`R ≤ C ≤ D`, `R` an `r`-Sylow subgroup of `A`, inside `D = (M ⊔ A) ⋊ P`: `D = (M ⊔ A) ⊔ P` with
`(M ⊔ A) ⊓ P = ⊥`, `|P| = p`, `A ≤ N_G(M)`, `P ≤ N_G(M ⊔ A)` and `r ∤ |M|`.  Then `r ∤ [D : C]`.

Indeed `|D| = |M ⊔ A|·p`, `|M ⊔ A|·|M ⊓ A| = |M|·|A|` and `|A| = [A:R]·|R|`, so
`|D| = |R|·m` with `r ∤ m`; on the other hand `|D| = [D:C]·[C:R]·|R|`.  Cancelling `|R|` gives
`[D:C]·[C:R] = m`, and `r ∤ m` forces `r ∤ [D:C]`. -/
theorem not_dvd_relIndex_of_sylow_le {G : Type} [Group G] [Finite G]
    {A C D M P R : Subgroup G} {p r : ℕ}
    (hr : r.Prime) (hrp : ¬ r ∣ p)
    (hR : IsSylowIn r R A)
    (hRC : R ≤ C) (hCD : C ≤ D)
    (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hPM : P ≤ Subgroup.normalizer ((M ⊔ A : Subgroup G) : Set G))
    (hD : D = (M ⊔ A) ⊔ P) (hinf : (M ⊔ A) ⊓ P = ⊥)
    (hPcard : Nat.card P = p) (hrM : ¬ r ∣ Nat.card ↥M) :
    ¬ r ∣ C.relIndex D := by
  classical
  -- `M`-side counting: `|M ⊔ A| = m₁ * |A|` with `r ∤ m₁`
  have hMA : Nat.card ↥(M ⊔ A) * Nat.card ↥(M ⊓ A) = Nat.card ↥M * Nat.card ↥A :=
    card_sup_mul_card_inf hAM
  have hMdvd : Nat.card ↥(M ⊓ A) ∣ Nat.card ↥M := Subgroup.card_dvd_of_le inf_le_left
  set m₁ : ℕ := Nat.card ↥M / Nat.card ↥(M ⊓ A) with hm₁
  have hm₁M : m₁ * Nat.card ↥(M ⊓ A) = Nat.card ↥M := Nat.div_mul_cancel hMdvd
  have hrM₁ : ¬ r ∣ m₁ := fun hd =>
    hrM (hm₁M ▸ dvd_mul_of_dvd_left hd _)
  have hMsup : Nat.card ↥(M ⊔ A) = m₁ * Nat.card ↥A := by
    have h2 : Nat.card ↥(M ⊔ A) * Nat.card ↥(M ⊓ A) =
        (m₁ * Nat.card ↥A) * Nat.card ↥(M ⊓ A) := by
      rw [hMA, ← hm₁M]
      ring
    exact Nat.mul_right_cancel Nat.card_pos h2
  -- `D`-side counting: `|D| = |M ⊔ A| * p`
  have hDcard : Nat.card ↥D = Nat.card ↥(M ⊔ A) * p := by
    have h := card_sup_mul_card_inf (H := M ⊔ A) (K := P) hPM
    rw [← hD, hinf, Subgroup.card_bot, mul_one, hPcard] at h
    exact h
  -- `|A| = [A:R] * |R|`
  have hAcard : Nat.card ↥A = R.relIndex A * Nat.card ↥R :=
    (relIndex_mul_card_of_le' hR.2.1).symm
  -- `r ∤ m₁ * [A:R] * p`
  have hrfree : ¬ r ∣ m₁ * R.relIndex A * p := by
    intro hd
    rcases hr.dvd_mul.mp hd with h | h
    · rcases hr.dvd_mul.mp h with h' | h'
      · exact hrM₁ h'
      · exact hR.2.2 h'
    · exact hrp h
  -- `|D| = |R| * (m₁ * [A:R] * p)`
  have hkey : Nat.card ↥D = Nat.card ↥R * (m₁ * R.relIndex A * p) := by
    rw [hDcard, hMsup, hAcard]
    ring
  -- `|D| = [D:C] * [C:R] * |R|`
  have hCcard : R.relIndex C * Nat.card ↥R = Nat.card ↥C := relIndex_mul_card_of_le' hRC
  have hfin : m₁ * R.relIndex A * p = R.relIndex C * C.relIndex D := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := ↥R))
    calc Nat.card ↥R * (m₁ * R.relIndex A * p)
        = Nat.card ↥D := hkey.symm
      _ = C.relIndex D * Nat.card ↥C := (relIndex_mul_card_of_le' hCD).symm
      _ = C.relIndex D * (R.relIndex C * Nat.card ↥R) := by rw [hCcard]
      _ = Nat.card ↥R * (R.relIndex C * C.relIndex D) := by ring
  intro hdvd
  exact hrfree (hfin ▸ dvd_mul_of_dvd_right hdvd _)

/-! ## §4 Prop. 1, step 5 -/

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 5** (p.180): the conclusion `Step5Conc H t p P A`
(`Submission/Work/NormalComplement/S5K/Defs.lean`): for `r ∈ π = Design.piSec4 H t p` (primes
`r ≠ p` of `|D|` with `r ∤ |K|`) one has `r ∤ |D : C_A(P)|`, i.e. `C_A(P)` is Hall in
`D = twoPoint H t`.

Route (the source's step 5, p.180):
* Let `r ∈ π` and let `R` be an `r`-Sylow of `A` normalised by `P` (orbit counting).
  By App. I (5)(a) (`Work.NormalComplement.appI_five_a`) `|⟨K⟩|` is prime to `|R P|`.
* By step 4 (`h4 : Step4Conc`) and §4 Lemma 1 (c) (`Work.NormalComplement.sec4_one_c`),
  `|C_D(P)|` is prime to `|K|`, hence to `|⟨K⟩|`; so `C_{⟨K⟩}(P) = 1`.
* App. VII (`hVII : Design.AppVIIProp`, applied with `K := ⟨K⟩ = Kgrp (twoPoint H t) t`,
  `Q := R`, `P := P`) then gives that `[R,P]` centralises `⟨K⟩`.  By (D2)
  (`h.d2 : IsD2 H t W`, whose second clause is `C_V(K) = 1`) `[R,P] = 1`, so `R ≤ C_A(P)`;
  hence `r ∤ |D : C_A(P)|`. -/
theorem prop1_step5 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (h4 : Work.NormalComplement.S5K.Step4Conc H t p P A) :
    Work.NormalComplement.S5K.Step5Conc H t p P A := by
  intro r hr
  obtain ⟨hrprime, _hrdvdD, hrne, hrK⟩ := hr
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact r.Prime := ⟨hrprime⟩
  -- ## Some standing facts
  have hP_le_V : P ≤ centD H t := le_trans h.P_le inf_le_right
  have hP_le_D : P ≤ twoPoint H t := hP_le_V.trans inf_le_left
  have hA_le_D : A ≤ twoPoint H t := h.A_le.trans inf_le_left
  have hC_le_D : A ⊓ Subgroup.centralizer (P : Set G) ≤ twoPoint H t :=
    inf_le_left.trans hA_le_D
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have htD : NormalizedBy t (twoPoint H t) :=
    twoPoint_normalizedBy (twoPoint_mul_self h.invol)
  have hcopD : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hoddD
  -- `D ≤ N_G(⟨K⟩)` (App. I (4))
  have hfour := appI_four (d := 2) Nat.prime_two h.invol htD hcopD
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcopD).2 rfl).1
  have hKg : Kgrp (twoPoint H t) t = Subgroup.closure (Kapp t (twoPoint H t)) := by
    rw [Kgrp, hKappKset]
  have hM_le_D : Kgrp (twoPoint H t) t ≤ twoPoint H t :=
    hKg ▸ (Subgroup.closure_le _).mpr (fun z hz => hfour.1 hz)
  have hD_le_NM : twoPoint H t ≤
      Subgroup.normalizer ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hyD k hk
    have hk' : k ∈ Subgroup.closure (Kapp t (twoPoint H t)) := by rw [← hKg]; exact hk
    have hh := hfour.2.2.1 y hyD k hk'
    rwa [hKg]
  -- ## `p ∤ |A|`
  have hpdvd : ¬ p ∣ Nat.card ↥A := by
    have hVcard : Nat.card ↥(centD H t) = Nat.card ↥A * p := by
      have hh := card_sup_mul_card_inf (H := A) (K := P) (hP_le_V.trans h.A_normal)
      rw [h.A_sup, h.A_inf, Subgroup.card_bot, mul_one, h.P_card] at hh
      exact hh
    have hrel : P.relIndex (centD H t) = Nat.card ↥A := by
      have hh := relIndex_mul_card_of_le' hP_le_V
      rw [h.P_card, hVcard] at hh
      exact Nat.mul_right_cancel h.prime.pos hh
    intro hd
    have h1 : p ∣ P.relIndex (centD H t) := by rw [hrel]; exact hd
    have h2 : p ∣ P.relIndex (twoPoint H t) := by
      rw [← Subgroup.relIndex_mul_relIndex P (centD H t) (twoPoint H t) hP_le_V inf_le_left]
      exact dvd_mul_of_dvd_left h1 _
    exact hPsyl.2.2 h2
  -- ## `r ∤ |⟨K⟩|` and `p ∤ |⟨K⟩|`
  have hrM : ¬ r ∣ Nat.card ↥(Kgrp (twoPoint H t) t) := fun hd =>
    hrK ((prime_dvd_card_Kgrp_iff hFT h r hrprime).mp hd)
  have hpM : ¬ p ∣ Nat.card ↥(Kgrp (twoPoint H t) t) := not_dvd_p_card_Kgrp hFT h
  have hcopMr : Nat.Coprime (Nat.card ↥(Kgrp (twoPoint H t) t)) r :=
    (hrprime.coprime_iff_not_dvd.mpr hrM).symm
  have hcopMp : Nat.Coprime (Nat.card ↥(Kgrp (twoPoint H t) t)) p :=
    (h.prime.coprime_iff_not_dvd.mpr hpM).symm
  -- ## `C_{⟨K⟩}(P) = 1`
  have hCPinf : (A ⊓ Subgroup.centralizer (P : Set G)) ⊓ P = ⊥ := by
    have h1 : (A ⊓ Subgroup.centralizer (P : Set G)) ⊓ P ≤ A ⊓ P :=
      inf_le_inf inf_le_left le_rfl
    rw [h.A_inf] at h1
    exact le_bot_iff.mp h1
  have hPnormC : P ≤ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (P : Set G)) : Set G) := by
    refine (Subgroup.le_normalizer_iff (H := P)
      (K := A ⊓ Subgroup.centralizer (P : Set G))).mpr ?_
    intro a ha x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.le_normalizer_iff.mp (hP_le_V.trans h.A_normal) a ha x hxA
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro q hq
      have hxq : q * x = x * q := Subgroup.mem_centralizer_iff.mp hxC q hq
      have hxp : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a ha
      have ha1 : a * x * a⁻¹ = x := by rw [hxp]; group
      rw [ha1]
      exact hxq
  have hcopMC : Nat.Coprime (Nat.card ↥(Kgrp (twoPoint H t) t))
      (Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))) := by
    by_contra hnc
    obtain ⟨q, hq, hqM, hqC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact (h4 q hq hqC).2.2.2 ((prime_dvd_card_Kgrp_iff hFT h q hq).mp hqM)
  have hcopMCP : Nat.Coprime (Nat.card ↥(Kgrp (twoPoint H t) t))
      (Nat.card ↥((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P)) := by
    have hcard : Nat.card ↥((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P) =
        Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) * p := by
      have hh := card_sup_mul_card_inf (H := A ⊓ Subgroup.centralizer (P : Set G)) (K := P)
        hPnormC
      rw [hCPinf, Subgroup.card_bot, mul_one, h.P_card] at hh
      exact hh
    rw [hcard]
    exact hcopMC.mul_right hcopMp
  have hM_inf_CP : Kgrp (twoPoint H t) t ⊓
      ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P) = ⊥ := by
    have h3 : Nat.card ↥(Kgrp (twoPoint H t) t ⊓
          ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P)) ∣
        Nat.gcd (Nat.card ↥(Kgrp (twoPoint H t) t))
          (Nat.card ↥((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P)) :=
      Nat.dvd_gcd (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcopMCP] at h3
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h3)
  have hM_inf_CG : Kgrp (twoPoint H t) t ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    have hDinf : twoPoint H t ⊓ Subgroup.normalizer (P : Set G) =
        (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := (sec4_one_c hFT h).1
    have h1 : Kgrp (twoPoint H t) t ⊓ Subgroup.centralizer (P : Set G) ≤
        Kgrp (twoPoint H t) t ⊓ ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P) := by
      refine le_inf inf_le_left ?_
      intro y hy
      obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyD : y ∈ twoPoint H t := hM_le_D hyM
      have hyN : y ∈ twoPoint H t ⊓ Subgroup.normalizer (P : Set G) :=
        Subgroup.mem_inf.mpr ⟨hyD, Subgroup.centralizer_le_normalizer (P : Set G) hyC⟩
      rwa [hDinf] at hyN
    rw [hM_inf_CP] at h1
    exact le_bot_iff.mp h1
  -- ## App. VII
  obtain ⟨R, hRsyl, hPR⟩ := exists_isSylowIn_normalizer h.A_sup h.A_inf h.A_normal
    h.prime h.P_card hpdvd hrprime hrne
  have hRPinf : R ⊓ P = ⊥ := by
    have h1 : R ⊓ P ≤ A ⊓ P := inf_le_inf hRsyl.2.1 le_rfl
    rw [h.A_inf] at h1
    exact le_bot_iff.mp h1
  have hcopMRP : Nat.Coprime (Nat.card ↥(Kgrp (twoPoint H t) t))
      (Nat.card ↥(R ⊔ P)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRsyl.1
    have hcard : Nat.card ↥(R ⊔ P) = Nat.card ↥R * p := by
      have hh := card_sup_mul_card_inf (H := R) (K := P) hPR
      rw [hRPinf, Subgroup.card_bot, mul_one, h.P_card] at hh
      exact hh
    rw [hcard, hk]
    exact (hcopMr.pow_right k).mul_right hcopMp
  have hoddR : Odd (Nat.card ↥(R ⊓ Subgroup.centralizer (P : Set G))) :=
    Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le
      (le_trans inf_le_left (le_trans hRsyl.2.1 hA_le_D)))
  have hpdvdR : ¬ Nat.card P ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRsyl.1
    rw [h.P_card, hk]
    intro hd
    exact hrne ((Nat.prime_dvd_prime_iff_eq h.prime hrprime).mp
      (h.prime.dvd_of_dvd_pow hd)).symm
  have hVIIapp : ⁅P, R⁆ ≤
      Subgroup.centralizer ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) :=
    hVII hFT G (Kgrp (twoPoint H t) t) R P
      (hRsyl.2.1.trans (hA_le_D.trans hD_le_NM))
      (hP_le_D.trans hD_le_NM)
      hPR (h.P_card ▸ h.prime) hpdvdR hoddR hcopMRP hM_inf_CG
  -- ## `[P,R] = 1`, hence `R ≤ C_A(P)`
  have hcomm_le : ⁅P, R⁆ ≤ centD H t ⊓
      Subgroup.centralizer (Kset (twoPoint H t) t : Set G) := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      show ⁅a, b⁆ ∈ centD H t
      rw [commutatorElement_def]
      have ha' : a ∈ centD H t := hP_le_V ha
      have hb' : b ∈ centD H t := (hRsyl.2.1.trans h.A_le) hb
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ ha' hb') (Subgroup.inv_mem _ ha')) (Subgroup.inv_mem _ hb')
    · refine hVIIapp.trans ?_
      exact Subgroup.centralizer_le (fun z hz => Subgroup.subset_closure hz)
  have hcomm_bot : ⁅P, R⁆ = ⊥ := by
    rw [h.d2.2.1] at hcomm_le
    exact le_bot_iff.mp hcomm_le
  have hR_le_CG : R ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : ⁅a, y⁆ = 1 :=
      Subgroup.mem_bot.mp ((Subgroup.commutator_le.mp (le_of_eq hcomm_bot)) a ha y hy)
    rw [commutatorElement_def] at h1
    have h2 : a * y * a⁻¹ = y := mul_inv_eq_one.mp h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hRC : R ≤ A ⊓ Subgroup.centralizer (P : Set G) := le_inf hRsyl.2.1 hR_le_CG
  -- ## Counting
  refine not_dvd_relIndex_of_sylow_le (A := A) (C := A ⊓ Subgroup.centralizer (P : Set G))
    (D := twoPoint H t) (M := Kgrp (twoPoint H t) t) (P := P) (R := R) (p := p) (r := r)
    hrprime (fun hd => ?_) hRsyl hRC hC_le_D (hA_le_D.trans hD_le_NM)
    (hP_le_D.trans (sec4_one_c hFT h).2.1) (sec4_one_c hFT h).2.2.2.symm
    (sec4_one_c hFT h).2.2.1 h.P_card hrM
  · rcases (Nat.dvd_prime h.prime).mp hd with h1 | h1
    · exact hrprime.ne_one h1
    · exact hrne h1

end Work.NormalComplement.S5K
