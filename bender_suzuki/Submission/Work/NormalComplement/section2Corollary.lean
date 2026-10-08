import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.primes_of_abelianization
import Submission.Work.NormalComplement.pResidual_strategy
import Submission.Work.NormalComplement.commutator_ne_of_solvable
import Submission.Work.NormalComplement.BenderPrelimAux
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThmF.Bender.cardInvGeTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- `H` normalises `H ⊓ C_G(Inv(H))`: conjugation by an element of `H` permutes the involutions of
`H`, hence fixes their centraliser. -/
private theorem le_normalizer_inf_centralizer_involutions' {G : Type} [Group G]
    {H : Subgroup G} :
    H ≤ Subgroup.normalizer
      (((H ⊓ Subgroup.centralizer (involutions (H : Set G))) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxC' : ∀ u ∈ involutions (H : Set G), u * x = x * u :=
    Subgroup.mem_centralizer_iff.mp hxC
  refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨huH, hu2⟩ := Work.ThreePoints.mem_involutions.mp hu
  have hconj : h⁻¹ * u * h ∈ involutions (H : Set G) := by
    refine Work.ThreePoints.mem_involutions.mpr ⟨?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem hh) huH) hh
    · have e : h⁻¹ * u * h = (MulAut.conj h⁻¹) u := by
        rw [MulAut.conj_apply]; group
      rw [e, MulEquiv.orderOf_eq, hu2]
  have h2 := hxC' (h⁻¹ * u * h) hconj
  calc u * (h * x * h⁻¹) = h * ((h⁻¹ * u * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * u * h)) * h⁻¹ := by rw [h2]
    _ = (h * x * h⁻¹) * u := by group

/-- **The Corollary of Peterfalvi I Ch. III §2 Prop. 1** (p.176): if `H = C_H(Inv(H))·D`, where
`D = H ⊓ conj t H` and `Inv(H) = involutions (H : Set G)`, then `D` has a normal complement in `H`.

Route.  Let `W ⊴ H` be minimal with `W ≤ C_H(Inv H)` and `H = W·D` (nonempty: `C_H(Inv H)` itself).
Put `E = W ⊓ D`.  If `E ≠ ⊥`, then `E` is solvable (`hFT`, `|E|` odd) and some prime `p | [E : E']`
(`Work.NormalComplement.primes_of_abelianization`), and:
* alternative (b) of `hS2` is impossible: `P ≤ V ⊓ E ≤ D`, and `E ≤ W ≤ C_H(Inv H)`, so
  `P ≤ D ⊓ C(Inv H) ≤ C(K)` by `ChIIFourProp` **P4** (its conjunct
  `centD H t ⊓ Subgroup.centralizer (Kset D t) = D ⊓ Subgroup.centralizer (involutions (H:Set G))`);
  but `P` acts fixed-point-freely on `K = J(D,t)` and `K ≠ {1}` since `|K| = |Inv H| ≥ 2`
  (`BenderPrelimProp` + `ChIIFourProp` P2(a) + App. I (1)(a) — `Kset` contains the involutions of
  `H` under `k ↦ u^k`, `H` having even order);
* hence `E` is `p`-control in `W` by `hS2`; with `y ∈ E ∖ E'` a `p`-element, `hTrans` gives
  `y ∉ O^p(W)`, and the Strategy (`Work.NormalComplement.pResidual_strategy`, with `|W:E|` odd)
  produces a proper normal subgroup `W₁ ⊴ H` contained in `C_H(Inv H)` with `W₁ ⊔ D = H`,
  contradicting minimality of `W`.
So `E = ⊥` and `W` is the required normal complement. -/
theorem section2Corollary (hFT : Submission.Blueprint.FeitThompsonProp)
    (hTrans : Work.NormalComplement.TransferProp)
    (hX : Work.NormalComplement.AppXProp) (hS2 : Work.NormalComplement.Section2Prop)
    (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    Work.NormalComplement.Section2CorollaryProp := by
  classical
  intro G _ _ hSit H hH t ht2 htH hsup
  have hfour : HasFourGroup G := hSit.1.1
  have hDodd : Odd (Nat.card (twoPoint H t)) := hH.2.2 t htH
  -- The family of admissible subgroups.
  let S : Set (Subgroup G) :=
    {W | W ≤ H ⊓ Subgroup.centralizer (involutions (H : Set G)) ∧
      H ≤ Subgroup.normalizer (W : Set G) ∧ W ⊔ twoPoint H t = H}
  have hCinS : (H ⊓ Subgroup.centralizer (involutions (H : Set G))) ∈ S :=
    ⟨le_rfl, le_normalizer_inf_centralizer_involutions', hsup⟩
  have hex : ∃ k : ℕ, ∃ W : Subgroup G, W ∈ S ∧ Nat.card W = k := ⟨_, _, hCinS, rfl⟩
  obtain ⟨W, hWS, hWval⟩ := Nat.find_spec hex
  have hWmin : ∀ W' ∈ S, Nat.card W ≤ Nat.card W' := by
    intro W' hW'
    rw [hWval]
    exact Nat.find_min' hex ⟨W', hW', rfl⟩
  have hWleH : W ≤ H := hWS.1.trans inf_le_left
  have hWleC : W ≤ Subgroup.centralizer (involutions (H : Set G)) := hWS.1.trans inf_le_right
  have hHnW : H ≤ Subgroup.normalizer (W : Set G) := hWS.2.1
  have hWD : W ⊔ twoPoint H t = H := hWS.2.2
  -- `W` meets `D = twoPoint H t` trivially.
  have hWinf : W ⊓ twoPoint H t = ⊥ := by
    by_contra hne
    set E : Subgroup G := W ⊓ twoPoint H t with hE
    have hEne : E ≠ ⊥ := by rw [hE]; exact hne
    have hEodd : Odd (Nat.card E) :=
      Odd.of_dvd_nat hDodd
        (Subgroup.card_dvd_of_le (inf_le_right : W ⊓ twoPoint H t ≤ twoPoint H t))
    have hEsol : Group.IsSolvable ↥E := hFT ↥E hEodd
    have hE'ne : ⁅E, E⁆ ≠ E := commutator_ne_of_solvable E hEne hEsol
    have hE'lt : ⁅E, E⁆ < E := lt_of_le_of_ne (Subgroup.commutator_le_self E) hE'ne
    have hrel : (⁅E, E⁆).relIndex E ≠ 1 :=
      fun h1 => hE'lt.2 (Subgroup.relIndex_eq_one.mp h1)
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hrel
    haveI : Fact p.Prime := ⟨hpprime⟩
    have hpcardE : p ∣ Nat.card E :=
      dvd_trans hpdvd (Subgroup.relIndex_dvd_card ⁅E, E⁆ E)
    obtain ⟨y, hyE, hyE', k, hyord⟩ :=
      primes_of_abelianization G E hEne hEsol p hpprime hpdvd
    rcases hS2 G hSit H hH t ht2 htH W hWleH hHnW hWD (hX G hSit H hH t ht2 htH) p hpprime hpcardE with
      hpc | ⟨P, hPsyl, hPV, hPfree, _⟩
    · -- Case (a): `E` is `p`-control in `W`; the transfer and the Strategy contradict minimality.
      have hy1 : y ≠ 1 := by rintro rfl; exact hyE' (Subgroup.one_mem _)
      have hyW : y ∈ W := hpc.1 hyE
      have hyres : y ∉ Work.Grun.pResidual p W := hTrans G hpc hyE hy1 ⟨k, hyord⟩ hyE' hpdvd
      obtain ⟨W₁, hlt, hW₁H, hHn₁, hW₁D⟩ :=
        pResidual_strategy hpc.1 inf_le_right hpc.2.1 hWleH hHnW hWD hyW hyres
      have hW₁S : W₁ ∈ S := ⟨hlt.le.trans hWS.1, hHn₁, hW₁D⟩
      exact (not_lt.mpr (hWmin W₁ hW₁S)) (Subgroup.card_lt_of_lt hlt)
    · -- Case (b): a `p`-Sylow of `E` acting fixed-point-freely on `K = J(D,t)` is impossible.
      have hPleE : P ≤ E := hPsyl.2.1
      have hPleW : P ≤ W := hPleE.trans inf_le_left
      have hPleD : P ≤ twoPoint H t := hPleE.trans inf_le_right
      have hPleC : P ≤ Subgroup.centralizer (involutions (H : Set G)) := hPleW.trans hWleC
      have hPne : P ≠ ⊥ := by
        intro hbot
        have hcard : Nat.card ↥(P.subgroupOf E) = Nat.card ↥P :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleE).toEquiv
        have h1 : p ∣ Nat.card ↥(P.subgroupOf E) * (P.subgroupOf E).index := by
          rw [Subgroup.card_mul_index]; exact hpcardE
        have h2 : p ∣ Nat.card ↥(P.subgroupOf E) :=
          (hpprime.dvd_mul.mp h1).resolve_right hPsyl.2.2
        rw [hcard, hbot, Subgroup.card_bot] at h2
        exact hpprime.not_dvd_one h2
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
      have hxP : (x : G) ∈ P := x.2
      have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      -- `|K| = |Inv H| ≥ 2`, so `K` contains an element `≠ 1`.
      have hKcard : (Kset (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard := by
        show (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard
        exact (kapp_ncard_eq_invOfConj_ncard hH ht2 htH).trans
          (invOfConj_ncard_eq_involutions_ncard hH ht2 htH)
      have hK2 : 2 ≤ (Kset (twoPoint H t) t).ncard := by
        rw [hKcard]; exact Work.ThmF.Bender.cardInvGeTwo hH hfour
      obtain ⟨z, hzK, hz1⟩ : ∃ z ∈ Kset (twoPoint H t) t, z ≠ 1 := by
        by_contra h
        push_neg at h
        have hsub : (Kset (twoPoint H t) t) ⊆ ({1} : Set G) := fun z hz => by
          simpa using h z hz
        have hle := Set.ncard_le_ncard hsub
        rw [Set.ncard_singleton] at hle
        omega
      -- `P ≤ C(K)` by `ChIIFourProp` P4.
      have hP4 := (hC4 G hSit H hH t ht2 htH).2.2.2.2.1
      have hKcenter : P ≤ Subgroup.centralizer (Kset (twoPoint H t) t : Set G) := by
        intro q hq
        have h1 : q ∈ twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) :=
          ⟨hPleD hq, hPleC hq⟩
        rw [← hP4] at h1
        exact h1.2
      have hcomm : z * (x : G) = (x : G) * z :=
        (Subgroup.mem_centralizer_iff.mp (hKcenter hxP)) z hzK
      have hxz : (x : G) * z * (x : G)⁻¹ = z := by
        rw [← hcomm]; group
      exact hz1 (hPfree (x : G) hxP hx1' z hzK hxz)
  exact ⟨W, hWleH, hHnW, hWinf, hWD⟩

end Work.NormalComplement
