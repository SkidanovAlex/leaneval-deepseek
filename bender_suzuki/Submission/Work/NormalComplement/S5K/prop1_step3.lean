import Mathlib
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.sec4_prop1_star
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.DoubleTransitivity.App2.app2_5
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.S5K.prop1_step3_defs
import Submission.Work.NormalComplement.S5K.prop1_step3_aux
import Submission.Work.NormalComplement.S5K.prop1_step3_aux2
import Submission.Work.NormalComplement.S5K.prop1_step3_aux3
import Submission.Work.NormalComplement.S5K.prop1_step3_appIII

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open scoped Pointwise
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 3** (p.180): the conclusion `Step3Conc H t p P A`
(`Submission/Work/NormalComplement/S5K/Defs.lean`): every Sylow subgroup `R` of `C_A(P)` has order
dividing `p - 1`.

Route (the source's step 3, p.180):
* By step 1 (`h1 : Step1Conc`) there is a `p`-Sylow `P₁` of `N_H(P)` normalised by `R`
  (orbit counting for the action of the `p`-group `R` on the Sylow `p`-subgroups of `N_H(P)`).
  If `R = 1` the conclusion is trivial; otherwise `C_A(P) ≠ 1` and step 2 (`h2 : Step2Conc`) gives
  `P ⊊ P₁` (`exists_pSubgroup_normalized`).
* `fpf_on_P1modP` (formula (∗)) gives that `R` acts fixed-point-freely on `P₁/P`.
* `isCyclic_quotient_of_appIII` (Appendix III applied to `N_G(P)/KKP`) gives that `P₁/P` is cyclic.
* `exists_D_of_isCyclic_quotient` produces `D` with `P ≤ D ≤ P₁`, `|D| = p²` and
  `D = {z ∈ P₁ : z^p ∈ P}`; `card_dvd_sub_one_of_fpf` (free action of `R` on `D \ P`) gives
  `|R| ∣ p - 1`.

The proof must avoid the `sec2_one` world (do not import `Submission.Work.NormalComplement.sec2_lemma1`
or `sec2_one`); the `S5K` modules live in the `sec4_P2d` world. -/
theorem prop1_step3 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (h1 : Work.NormalComplement.S5K.Step1Conc H t p P A)
    (h2 : Work.NormalComplement.S5K.Step2Conc H t p P A) :
    Work.NormalComplement.S5K.Step3Conc H t p P A := by
  classical
  intro r R hr hRsyl
  by_cases hR : R = ⊥
  · rw [hR, Subgroup.card_bot]
    exact one_dvd _
  · haveI : Fact r.Prime := ⟨hr⟩
    haveI : Fact p.Prime := ⟨h.prime⟩
    -- ## the `R`-invariant `p`-Sylow `P₁ ⊋ P` of `N_H(P)`
    obtain ⟨P₁, hP₁p, hPP₁, hP₁W', hP₁R, hne'⟩ :=
      exists_pSubgroup_normalized h hPsyl h1 h2 hr hRsyl hR
    have hP₁N : P₁ ≤ Subgroup.normalizer (P : Set G) := fun x hx => (hP₁W' hx).2
    have hne : P₁ ≠ P := by
      intro heq
      obtain ⟨x, hx1, hx2⟩ := hne'
      rw [heq] at hx1
      exact hx2 hx1
    -- ## `P₁/P` is cyclic (Appendix III)
    obtain ⟨K, hKg, hKf, φ, hφsurj, hφker, hcyc, hk⟩ :=
      isCyclic_quotient_of_appIII hFT hC4 hIII h hPsyl hPP₁ hP₁W' hP₁p hne
    -- ## the subgroup `D` of order `p ^ 2`
    obtain ⟨D, hPD, hDle, hDcard, hDpow, hDgen⟩ :=
      exists_D_of_isCyclic_quotient h.prime hPP₁ hP₁N h.P_card hφsurj hφker hcyc hk
    have hRleC : R ≤ A ⊓ Subgroup.centralizer (P : Set G) := hRsyl.2.1
    have hRleCg : R ≤ Subgroup.centralizer (P : Set G) := hRleC.trans inf_le_right
    -- ## `R` normalises `D`
    have hstep : ∀ v ∈ R, ∀ y ∈ D, v * y * v⁻¹ ∈ D := by
      intro v hv y hy
      have hyP₁ : y ∈ P₁ := hDle hy
      have hyp : y ^ p ∈ P := hDpow y hy
      have hvc : v ∈ Subgroup.centralizer (P : Set G) := hRleCg hv
      refine hDgen _ ((Subgroup.mem_normalizer_iff.mp (hP₁R hv) y).mp hyP₁) ?_
      have h1 : (v * y * v⁻¹) ^ p = v * y ^ p * v⁻¹ := by
        have hp := map_pow (MulAut.conj v).toMonoidHom y p
        simpa [MulAut.conj_apply] using hp.symm
      rw [h1]
      have hcomm : y ^ p * v = v * y ^ p := (Subgroup.mem_centralizer_iff.mp hvc) (y ^ p) hyp
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hyp
    have hRD : R ≤ Subgroup.normalizer (D : Set G) := by
      intro v hv
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine le_antisymm ?_ ?_
      · rintro y ⟨z, hz, rfl⟩
        simpa [MulAut.conj_apply] using hstep v hv z hz
      · intro y hy
        refine ⟨v⁻¹ * y * v, ?_, ?_⟩
        · simpa using hstep v⁻¹ (Subgroup.inv_mem R hv) y hy
        · show v * (v⁻¹ * y * v) * v⁻¹ = y
          group
    -- ## `|R|` is prime to `p`
    have hpC : ¬ p ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
      not_dvd_p_card_CA h hPsyl
    have hcardR : Nat.card R ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
      Subgroup.card_dvd_of_le hRleC
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := r) (G := ↥R)).mp hRsyl.1
    have hkpos : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hR (Subgroup.card_eq_one.mp hk)
    have hrne : r ≠ p := by
      intro hrp
      rw [hrp] at hk
      exact hpC ((hk.symm ▸ dvd_pow_self p hkpos : p ∣ Nat.card ↥R).trans hcardR)
    have hcop : Nat.Coprime (Nat.card R) p := by
      rw [hk]
      refine ((Nat.Prime.coprime_iff_not_dvd hr).mpr ?_).pow_left k
      intro hd
      rcases (Nat.dvd_prime h.prime).mp hd with h1' | h1'
      · exact hr.ne_one h1'
      · exact hrne h1'
    -- ## fixed-point-freeness on `D`
    refine card_dvd_sub_one_of_fpf h.prime h.P_card hPD hDcard hRleCg hRD hcop ?_
    intro u hu hu1 y hyD hyu
    have hyP₁ : y ∈ P₁ := hDle hyD
    have hyH : y ∈ H := (hP₁W' hyP₁).1
    -- `y` and `u` commute (`u y u⁻¹ = y`)
    have hyu_comm : Commute y u := by
      have h : u * y = y * u := by
        have h2 : u * y * u⁻¹ * u = y * u := congrArg (fun z => z * u) hyu
        simpa [mul_assoc] using h2
      exact h.symm
    have hyu' : y * u * y⁻¹ = u := by
      rw [hyu_comm.eq, mul_assoc, mul_inv_cancel, mul_one]
    have hyu'' : y⁻¹ * u * y = u := by
      conv_lhs => rw [← hyu']
      group
    -- `y` normalises `⟨u⟩`
    have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [← hwz]
        have h1 : y * u ^ m * y⁻¹ = u ^ m := by
          rw [hyu_comm.zpow_right m, mul_assoc, mul_inv_cancel, mul_one]
        show y * u ^ m * y⁻¹ ∈ Subgroup.zpowers u
        rw [h1]
        exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
      · intro z hz
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        refine Subgroup.mem_map.mpr ⟨u ^ m, Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩, ?_⟩
        have h1 : y * u ^ m * y⁻¹ = u ^ m := by
          rw [hyu_comm.zpow_right m, mul_assoc, mul_inv_cancel, mul_one]
        exact h1
    -- `P` normalises `⟨u⟩`
    have hPN : P ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff.mpr
        (Subgroup.zpowers_le.mpr (hRleCg hu))).trans (Subgroup.centralizer_le_normalizer _)
    -- apply the group-theoretic criterion with `Q = ⟨y⟩ ⊔ P`
    have hQle : Subgroup.zpowers y ⊔ P ≤
        H ⊓ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
      sup_le (le_inf (Subgroup.zpowers_le.mpr hyH) (Subgroup.zpowers_le.mpr hyN))
        (le_inf (h.P_le.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))) hPN)
    have hQp : IsPGroup p ↥(Subgroup.zpowers y ⊔ P) :=
      IsPGroup.to_le hP₁p (sup_le (Subgroup.zpowers_le.mpr hyP₁) hPP₁)
    have hQeq := fpf_on_P1modP hFT hP3 h hPsyl (hRleC hu) hu1 hQle hQp le_sup_right
    exact hQeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end Work.NormalComplement.S5K
