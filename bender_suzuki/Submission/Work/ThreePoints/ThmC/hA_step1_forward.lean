import Mathlib
import Submission.Work.ThreePoints.ThmC.hAprereq
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.app4
import Submission.Work.ThreePoints.ThmC.hAzj
import Submission.Work.ThreePoints.ThmC.hA_step2
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- **Peterfalvi I Ch. II §3, Step 1, forward inequality.**

Let `H` be strongly embedded in the finite group `G`, `t ∉ H`, `p` an odd prime, `P` a `p`-Sylow
of `D₃ = D ⊓ D^u`, where `D = twoPoint H t = H ⊓ H^t`, which is also a `p`-Sylow of
`P · (C_G(P) ⊓ D)`.  Then `O_{p'}(D₃) ≤ O_{p'}(D)`.

Proof.  `D` has odd order, hence is solvable (`hFT`).  Apply Peterfalvi Appendix IV (`happ4`) in the
group `↥D` to the `p`-subgroup `P` and the subgroup `X = O_{p'}(D₃) ≤ D₃ ≤ D`:

* every element of order `p` in `C_D(P)` lies in `P`, because `P` is a `p`-Sylow of
  `P · (C_G(P) ⊓ D)`;
* `X` is a `p'`-subgroup of `D`;
* `P ≤ D₃` and `O_{p'}(D₃)` is normal in `D₃`, so `P` normalises `X`.

Appendix IV then gives `X ≤ O_{p'}(D)`. -/
theorem hA_step1_forward (hFT : Submission.Blueprint.FeitThompsonProp)
    (happ4 : Work.ThreePoints.ThmC.App4Hyp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t u : G} (htH : t ∉ H)
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H t ⊓
      Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)))
    (hSylowPC : Work.ThreePoints.ThmC.IsSylowOf p P
      (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H t))) :
    Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)) ≤
      Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hDdef
  set Y : Subgroup G := D ⊓ Submission.Blueprint.conj u D with hYdef
  set X : Subgroup G := Work.ThreePoints.ThmC.pPrimeCoreSub p Y with hX
  -- `D` has odd order, hence is solvable by Feit–Thompson
  have hoddD : Odd (Nat.card ↥D) := IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hsol : Group.IsSolvable ↥D := hFT ↥D hoddD
  have hPp : IsPGroup p P := hP.2.1
  have hPY : P ≤ Y := hP.1
  have hYD : Y ≤ D := inf_le_left
  have hPD : P ≤ D := hPY.trans hYD
  have hPC : IsSylowOf p P (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ D)) := hSylowPC
  have hXD : X ≤ D := (pPrimeCoreSub_le p Y).trans hYD
  -- (i) every element of order `p` of `C_D(P)` lies in `P`
  have hcond : ∀ x : ↥D, x ∈ Subgroup.centralizer (P.subgroupOf D : Set ↥D) →
      orderOf x = p → x ∈ P.subgroupOf D := by
    intro x hx hxo
    have hxo' : orderOf (x : G) = p := (Subgroup.orderOf_mk (x : G) x.2).symm.trans hxo
    have hxG : (x : G) ∈ Subgroup.centralizer (P : Set G) ⊓ D := by
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, x.2⟩
      intro y hy
      have hyPD : (⟨y, hPD hy⟩ : ↥D) ∈ P.subgroupOf D := Subgroup.mem_subgroupOf.mpr hy
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨y, hPD hy⟩ hyPD)
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G) hxG.1
    have hzp : IsPGroup p (Subgroup.zpowers (x : G) : Subgroup G) := by
      refine IsPGroup.iff_card.mpr ⟨1, ?_⟩
      rw [Nat.card_zpowers, hxo', pow_one]
    have hzpN : Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hsup : IsPGroup p (P ⊔ Subgroup.zpowers (x : G) : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hPp hzp hzpN
    have hle : P ⊔ Subgroup.zpowers (x : G) ≤ P ⊔ (Subgroup.centralizer (P : Set G) ⊓ D) := by
      refine sup_le le_sup_left ?_
      exact (Subgroup.zpowers_le.mpr hxG).trans le_sup_right
    have hsupQ : P ⊔ Subgroup.zpowers (x : G) = P := hPC.2.2 _ le_sup_left hle hsup
    rw [Subgroup.mem_subgroupOf, ← hsupQ]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G))
  -- (ii) `X` is a `p'`-subgroup of `D`
  have hXcop : Nat.Coprime (Nat.card ↥(X.subgroupOf D)) p := by
    have h1 : Nat.card ↥(X.subgroupOf D) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXD).toEquiv
    have h3 : Nat.card ↥X = Nat.card ↥(Submission.Blueprint.pPrimeCore p ↥Y) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective
        (Submission.Blueprint.pPrimeCore p ↥Y) Y.subtype Y.subtype_injective).toEquiv).symm
    rw [h1, h3]
    exact coprime_card_pPrimeCore hp ↥Y
  -- (iii) `P` normalises `X`
  have hPN : P.subgroupOf D ≤ Subgroup.normalizer (X.subgroupOf D : Set ↥D) := by
    have h1 : P.subgroupOf D ≤ (Subgroup.normalizer (X : Set G)).subgroupOf D :=
      Subgroup.subgroupOf_mono D (hPY.trans (pPrimeCoreSub_le_normalizer hp Y))
    rwa [Subgroup.subgroupOf_normalizer_eq hXD] at h1
  have hPpD : IsPGroup p (P.subgroupOf D) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  have hmain : X.subgroupOf D ≤ Submission.Blueprint.pPrimeCore p ↥D :=
    happ4 ↥D hp hpodd hsol (P := P.subgroupOf D) (X := X.subgroupOf D) hPpD hcond hXcop hPN
  have hfinal : X ≤ pPrimeCoreSub p D := by
    have hmap := Subgroup.map_mono (f := D.subtype) hmain
    rw [Subgroup.map_subgroupOf_eq_of_le hXD] at hmap
    exact hmap
  exact hfinal

end Work.ThreePoints.ThmC
