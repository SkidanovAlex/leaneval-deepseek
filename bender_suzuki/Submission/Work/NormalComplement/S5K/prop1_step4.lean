import Mathlib
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.appI_five_c_aux
import Submission.Work.Frobenius.Complement.ord_mod_eq_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise commutatorElement
open Submission.Blueprint

namespace Work.NormalComplement.S5K

variable {G : Type*} [Group G] [Finite G]

/-! ## Auxiliary lemmas -/

/-- **Orbit counting** for the conjugation action of a `p`-subgroup `R ≤ C_G(t) ⊓ X` on
`K = Kapp t X`: since the fixed points of the conjugation action are exactly
`K ∩ C_G(R) = K ∩ C_G(R)`, one has `p ∣ |K| → p ∣ |K ∩ C_G(R)|`. -/
theorem dvd_ncard_Kapp_centralizer {t : G} {X R : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hR : R ≤ Work.NormalComplement.fixX t X) (hRp : IsPGroup p R)
    (hdvd : p ∣ (Work.NormalComplement.Kapp t X).ncard) :
    p ∣ (Work.NormalComplement.Kapp t X ∩ (Subgroup.centralizer (R : Set G) : Set G)).ncard := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction R ↥(Work.NormalComplement.Kapp t X) := Work.NormalComplement.KappMulAction hR
  have hval : ∀ (u : R) (k : ↥(Work.NormalComplement.Kapp t X)),
      (u • k).1 = u.1 * k.1 * u.1⁻¹ :=
    fun u k => Work.NormalComplement.KappMulAction_val hR u k
  -- the fixed points of the action are `K ∩ C_G(R)`
  have hcard_fix : (MulAction.fixedPoints R ↥(Work.NormalComplement.Kapp t X)).ncard
      = (Work.NormalComplement.Kapp t X ∩ (Subgroup.centralizer (R : Set G) : Set G)).ncard := by
    rw [← Nat.card_coe_set_eq (MulAction.fixedPoints R ↥(Work.NormalComplement.Kapp t X)),
        ← Nat.card_coe_set_eq
          (Work.NormalComplement.Kapp t X ∩ (Subgroup.centralizer (R : Set G) : Set G))]
    apply Nat.card_congr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      refine ⟨a.1.1, a.1.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro u hu
      have hm := congrArg Subtype.val (a.2 ⟨u, hu⟩)
      rw [hval] at hm
      calc u * a.1.1 = (u * a.1.1 * u⁻¹) * u := by group
        _ = a.1.1 * u := by rw [hm]
    · intro b
      exact ⟨⟨b.1, b.2.1⟩, by
        intro m
        refine Subtype.ext ?_
        rw [hval]
        have hcomm := (Subgroup.mem_centralizer_iff.mp b.2.2) m.1 m.2
        rw [hcomm]; group⟩
    · intro a
      exact Subtype.ext (Subtype.ext rfl)
    · intro b
      exact Subtype.ext rfl
  have hmod : (Work.NormalComplement.Kapp t X).ncard ≡
      (Work.NormalComplement.Kapp t X ∩ (Subgroup.centralizer (R : Set G) : Set G)).ncard
        [MOD p] := by
    have h := hRp.card_modEq_card_fixedPoints ↥(Work.NormalComplement.Kapp t X)
    have h1 : Nat.card ↥(Work.NormalComplement.Kapp t X)
        = (Work.NormalComplement.Kapp t X).ncard := Nat.card_coe_set_eq _
    have h2 : Nat.card ↥(MulAction.fixedPoints R ↥(Work.NormalComplement.Kapp t X))
        = (Work.NormalComplement.Kapp t X ∩
            (Subgroup.centralizer (R : Set G) : Set G)).ncard :=
      (Nat.card_coe_set_eq _).trans hcard_fix
    rw [h1, h2] at h
    exact h
  exact (Nat.ModEq.dvd_iff hmod (dvd_refl p)).mp hdvd

/-- If a prime `r ≠ 2` divides `2 ^ p - 1` with `p` prime, then `p ∣ r - 1` (the multiplicative
order of `2` mod `r` is `p`, and it divides `r - 1`). -/
theorem p_dvd_sub_one_of_dvd_two_pow_sub_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hr2 : r ≠ 2) (hdvd : r ∣ 2 ^ p - 1) : p ∣ r - 1 := by
  have hr2dvd : ¬ r ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact hr.ne_one h1
    · exact hr2 h1
  have hcop : Nat.Coprime 2 r := ((hr.coprime_iff_not_dvd).mpr hr2dvd).symm
  have hfermat : 2 ^ (r - 1) ≡ 1 [MOD r] := Nat.ModEq.pow_card_sub_one_eq_one hr hcop
  have hdiv : r ∣ 2 ^ (r - 1) - 1 :=
    (Nat.modEq_iff_dvd' (n := r) (a := 1) (b := 2 ^ (r - 1)) Nat.one_le_two_pow).mp
      hfermat.symm
  refine Work.Frobenius.Complement.ord_mod_eq_prime hp hr hdvd ?_ hdiv
  rw [show (2 : ℕ) - 1 = 1 from rfl]
  exact hr.not_dvd_one

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 4** (p.180): the conclusion `Step4Conc H t p P A`
(`Submission/Work/NormalComplement/S5K/Defs.lean`): every prime divisor of `|C_A(P)|` lies in
`π = Design.piSec4 H t p` (the primes `r ≠ p` of `|D|` with `r ∤ |K|`), i.e. `C_A(P)` is a
`π`-group.  Here `D = twoPoint H t`, `V = centD H t`, `K = Kset D t`, `C_A(P) = A ⊓ C_G(P)`.

Route (the source's step 4, p.180):
* `p ∤ |C_A(P)|` is `Work.NormalComplement.S5K.not_dvd_p_card_CA` (`S5K/ca_coprime.lean`, proved)
  from `hPsyl`: `P` is a `p`-Sylow of `D`; so `r ≠ p`.
* `r ∣ |D|` because `C_A(P) ≤ A ≤ V ≤ D`.
* `r ∤ |K|`: suppose `r` is prime with `r ∣ |C_A(P)|` and `r ∣ |K|`.  Pick `x ∈ C_A(P)` of order `r`
  (Cauchy) and put `R = ⟨x⟩ ≤ A`; then `R ≠ ⊥`, `R ≤ A`, `P ≤ N_G(R)` (as `R ≤ C_G(P)`), so
  `Setup45A.A_B` gives `C_K(R) = C_K(A)`.  Orbit counting for the conjugation action of the
  `r`-group `R` on `K` (the action `KappMulAction` of `Work.NormalComplement.appI_five_c_aux`)
  gives `r ∣ |C_K(R)|` from `r ∣ |K|`.  Hence `r ∣ |C_K(A)| = 2^p - 1` (`Setup45A.A_CK`), so
  `ord_r 2 = p` (it divides the prime `p` and is not `1`), hence `p ∣ r - 1`, i.e. `p ≤ r - 1`.
* On the other hand `r ∣ |C_A(P)|` gives an `r`-Sylow `R₀ ≠ ⊥` of `C_A(P)`, and step 3
  (`h3 : Step3Conc`) gives `|R₀| ∣ p - 1`, hence `r ≤ p - 1`: contradiction. -/
theorem prop1_step4 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (h3 : Work.NormalComplement.S5K.Step3Conc H t p P A) :
    Work.NormalComplement.S5K.Step4Conc H t p P A := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  -- ## standing facts
  have hVleD : centD H t ≤ twoPoint H t := inf_le_left
  have hAleD : A ≤ twoPoint H t := h.A_le.trans hVleD
  have hCleD : A ⊓ Subgroup.centralizer (P : Set G) ≤ twoPoint H t := inf_le_left.trans hAleD
  have hOddD : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  intro r hr hrC
  haveI : Fact r.Prime := ⟨hr⟩
  refine ⟨hr, ?_, ?_, ?_⟩
  · -- `r ∣ |D|`
    exact dvd_trans hrC (Subgroup.card_dvd_of_le hCleD)
  · -- `r ≠ p`
    intro hrp
    exact not_dvd_p_card_CA h hPsyl (hrp ▸ hrC)
  · -- `r ∤ |K|`
    intro hrK
    -- `r` is odd, so `r ≠ 2`
    have hOddr : Odd r := Odd.of_dvd_nat hOddD (hrC.trans (Subgroup.card_dvd_of_le hCleD))
    have hr2 : r ≠ 2 := by
      intro h2
      exact hOddr.not_two_dvd_nat (h2.symm ▸ dvd_refl 2)
    -- ## Cauchy: an element `x ∈ C_A(P)` of order `r`
    haveI : Fintype ↥(A ⊓ Subgroup.centralizer (P : Set G)) := Fintype.ofFinite _
    have hcardC : r ∣ Fintype.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
      rw [← Nat.card_eq_fintype_card]; exact hrC
    obtain ⟨y, hyord⟩ :=
      exists_prime_orderOf_dvd_card (G := ↥(A ⊓ Subgroup.centralizer (P : Set G))) r hcardC
    set x : G := (y : G) with hxdef
    have hxC : x ∈ A ⊓ Subgroup.centralizer (P : Set G) := y.2
    have hxord : orderOf x = r := by rw [hxdef]; exact (Subgroup.orderOf_coe y).trans hyord
    have hxA : x ∈ A := (Subgroup.mem_inf.mp hxC).1
    have hxcen : x ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hxC).2
    -- ## `R = ⟨x⟩`
    set R : Subgroup G := Subgroup.zpowers x with hRdef
    have hRleV : R ≤ centD H t := by rw [hRdef]; exact Subgroup.zpowers_le.mpr (h.A_le hxA)
    have hRleD : R ≤ twoPoint H t := hRleV.trans hVleD
    have hRcen : R ≤ Subgroup.centralizer (P : Set G) := by
      rw [hRdef]; exact Subgroup.zpowers_le.mpr hxcen
    have hcent_le : centD H t ≤ Subgroup.centralizer ({t} : Set G) := inf_le_right
    have hRt : R ≤ Subgroup.centralizer ({t} : Set G) := hRleV.trans hcent_le
    have hRfix : R ≤ Work.NormalComplement.fixX t (twoPoint H t) :=
      fun z hz => ⟨hRt hz, hRleD hz⟩
    have hRne : R ≠ ⊥ := by
      intro hbot
      have hx1 : x = 1 := by
        have hmem : x ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact Subgroup.mem_zpowers x
        simpa using hmem
      rw [hx1, orderOf_one] at hxord
      exact hr.ne_one hxord.symm
    have hRleA : R ≤ A := by rw [hRdef]; exact Subgroup.zpowers_le.mpr hxA
    have hPN : P ≤ Subgroup.normalizer (R : Set G) :=
      (Subgroup.le_centralizer_iff.mp hRcen).trans
        (Subgroup.centralizer_le_normalizer (R : Set G))
    have hRp : IsPGroup r R := by
      rw [IsPGroup.iff_card]
      refine ⟨1, ?_⟩
      rw [pow_one, hRdef, Nat.card_zpowers]
      exact hxord
    -- ## `C_K(R) = C_K(A)`
    have hAB : Design.CK H t R = Design.CK H t A := h.A_B R hRne hRleA hPN
    -- ## orbit count: `r ∣ |C_K(R)|`
    have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
      ((appI_one (d := 2) Nat.prime_two h.invol (twoPoint_normalizedBy (twoPoint_mul_self h.invol))
        (Nat.coprime_two_right.mpr hOddD)).2 rfl).1
    have hdvdKapp : r ∣ (Kapp t (twoPoint H t)).ncard := by rw [hKappKset]; exact hrK
    have hcnt := dvd_ncard_Kapp_centralizer hr hRfix hRp hdvdKapp
    have hCK_R : (Kset (twoPoint H t) t ∩ (Subgroup.centralizer (R : Set G) : Set G)).ncard
        = 2 ^ p - 1 := by
      have h1 : (Design.CK H t R).ncard = (Design.CK H t A).ncard := congrArg Set.ncard hAB
      rw [h.A_CK] at h1
      exact h1
    have hr_dvd_2p : r ∣ 2 ^ p - 1 := by
      have h2 : r ∣ (Kset (twoPoint H t) t ∩ (Subgroup.centralizer (R : Set G) : Set G)).ncard := by
        rw [← hKappKset]; exact hcnt
      rwa [hCK_R] at h2
    -- ## number theory: `p ∣ r - 1`
    have hp_dvd : p ∣ r - 1 := p_dvd_sub_one_of_dvd_two_pow_sub_one h.prime hr hr2 hr_dvd_2p
    have hp_le : p ≤ r - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hr.one_lt) hp_dvd
    -- ## step 3 contradicts `p ∣ r - 1`
    obtain ⟨S⟩ := Sylow.nonempty (p := r) (G := ↥(A ⊓ Subgroup.centralizer (P : Set G)))
    set R₀ : Subgroup G :=
      S.toSubgroup.map (A ⊓ Subgroup.centralizer (P : Set G)).subtype with hR₀def
    have hR₀syl : IsSylowIn r R₀ (A ⊓ Subgroup.centralizer (P : Set G)) := by
      rw [hR₀def]; exact sylow_toSubgroup_isSylowIn S
    have hr_dvd_R₀ : r ∣ Nat.card R₀ := by
      have hrel : R₀.relIndex (A ⊓ Subgroup.centralizer (P : Set G)) * Nat.card R₀
          = Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
        relIndex_mul_card_of_le' hR₀syl.2.1
      have h2 : r ∣ R₀.relIndex (A ⊓ Subgroup.centralizer (P : Set G)) * Nat.card R₀ := by
        rw [hrel]; exact hrC
      rcases (hr.dvd_mul).mp h2 with hh | hh
      · exact absurd hh hR₀syl.2.2
      · exact hh
    have hr_le : r ≤ p - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt h.prime.one_lt)
        (dvd_trans hr_dvd_R₀ (h3 r R₀ hr hR₀syl))
    -- `p ≤ r - 1` and `r ≤ p - 1` are contradictory
    have hr_lt_p : r < p := (Nat.le_sub_one_iff_lt h.prime.pos).mp hr_le
    have hp_lt_r : p < r := (Nat.le_sub_one_iff_lt hr.pos).mp hp_le
    exact absurd hr_lt_p (not_lt.mpr hp_lt_r.le)

end Work.NormalComplement.S5K
