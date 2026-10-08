import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_setup_invol
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.sec4_prop1_star
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.Sec5Fix.prop2b
import Submission.Work.NormalComplement.Sec5Fix.lemma1
import Submission.Work.NormalComplement.Sec5Fix.prop2d
import Submission.Work.NormalComplement.Sec5Fix.prop2a
import Submission.Work.NormalComplement.Sec5Fix.normFitting
import Submission.Work.NormalComplement.Sec5Fix.prop2c

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Peterfalvi I Ch. III §5 Proposition 3 and the final contradiction** (pp. 186–187): `Setup5`
is contradictory.  Assembled from §5 Prop. 2 (a)–(d) (`Sec5Fix.prop2a` … `Sec5Fix.prop2d`),
§5 Prop. 3 (`Sec5Fix.normFitting`) and §5 Lemma 1 (`Sec5Fix.lemma1`). -/
theorem sec5_final_clean (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) : False := by
  classical
  -- ## the §5 involution `u ∈ H` centralising `V = centD H t`
  obtain ⟨u, hu, -⟩ := sec5_setup_invol hFT hC4 hP3 h
  -- ## §5 Prop. 2 (a): `f = orderOf (u*t) ∈ {3,5}`
  have hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 :=
    Work.NormalComplement.Sec5Fix.prop2a hFT hC hC4 hP3 hIII hMF2 h u hu
  -- ## §5 Prop. 2 (b), (c), (d)
  obtain ⟨hBfix, hBcop, M, hMcarr, hMab⟩ :=
    Work.NormalComplement.Sec5Fix.prop2b hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu hf
  have hMc : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G) :=
    Work.NormalComplement.Sec5Fix.prop2c hFT hA hC hC4 hP3 hIII hMF2 hCor1 h u hu M hMcarr
  have hMd : Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
      Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G) :=
    Work.NormalComplement.Sec5Fix.prop2d hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu hf M hMcarr
  -- ## §5 Prop. 3: `N_H(P) ≤ N_H(F(V))`
  have hNormF : H ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t) : Subgroup G) : Set G) :=
    Work.NormalComplement.Sec5Fix.normFitting hFT hA hC hC4 hP3 hIII hVII hMF2 hCor1 hBC hBP
      h u hu hf ⟨hBfix, hBcop⟩ M hMcarr hMab hMc hMd
  -- ## the final contradiction
  -- `r ≠ p`: `r ∣ 2^p - 1`, but `2^p - 1 ≡ 1 (mod p)` (Fermat).
  have hrp : r ≠ p := by
    intro hrp
    have hp2 : p ∣ 2 ^ p - 1 := hrp ▸ h.r_dvd
    have hnot : ¬ p ∣ 2 ^ p - 1 := by
      haveI : Fact p.Prime := ⟨h.prime⟩
      intro hd
      have hzero : ((2 ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      have hle : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
      have hcast : ((2 ^ p - 1 : ℕ) : ZMod p) = (2 : ZMod p) ^ p - 1 := by
        rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      rw [hcast, ZMod.pow_card] at hzero
      norm_num at hzero
    exact hnot hp2
  -- the join `P ⊔ F(V)` and §5 Lemma 1
  have hPX : P ≤ P ⊔ Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) :=
    le_sup_left
  have hPV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hFV : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      Submission.Blueprint.centD H t := Subgroup.map_subtype_le _
  have hXV : P ⊔ Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      Submission.Blueprint.centD H t := sup_le hPV hFV
  have hN : H ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((P ⊔ Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t) : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨-, hxNP⟩ := Subgroup.mem_inf.mp hx
    exact sec4_star_normalizer_inf_le_normalizer_sup P _ (Subgroup.mem_inf.mpr ⟨hxNP, hNormF hx⟩)
  have hEq : P ⊔ Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) = P :=
    Work.NormalComplement.Sec5Fix.lemma1 hFT hP3 h
      (P ⊔ Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) hPX hXV hN
  have hFleP : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤ P := by
    rw [← hEq]; exact le_sup_right
  -- `F(V)` is a non-trivial `r`-group and a `p`-group, so `F(V) = ⊥`.
  have hFbot : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hFp : IsPGroup p ↥(Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t)) := h.P_syl.1.to_le hFleP
    have hFr : IsPGroup r ↥(Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t)) := h.fitV_syl.1
    obtain ⟨k, hk⟩ := hFp ⟨x, hx⟩
    obtain ⟨m, hm⟩ := hFr ⟨x, hx⟩
    have hkx : x ^ (p ^ k) = 1 := by
      have := congrArg (Subtype.val) hk; simpa using this
    have hmx : x ^ (r ^ m) = 1 := by
      have := congrArg (Subtype.val) hm; simpa using this
    have hd1 : orderOf x ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hkx
    have hd2 : orderOf x ∣ r ^ m := orderOf_dvd_iff_pow_eq_one.mpr hmx
    have hcop : Nat.Coprime (p ^ k) (r ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes h.prime h.r_prime).mpr hrp.symm)
    have hone : orderOf x ∣ 1 := by
      have hg : Nat.gcd (p ^ k) (r ^ m) = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
      rw [← hg]; exact Nat.dvd_gcd hd1 hd2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  exact h.fitV_ne hFbot

end Work.NormalComplement
