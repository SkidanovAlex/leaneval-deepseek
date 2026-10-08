import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement._design.Vocab
import Submission.Work.NormalComplement.commutator_ne_of_solvable

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

/-- **Entry of Peterfalvi I Ch. III §4** (p.179): from the data of `Section45Prop` (minimal `W`,
(D1), (D2)), choose a prime `p ∣ |E:E'|` and a subgroup `P ≤ E ⊓ V` of order `p` which acts
fixed-point-freely on `K = J(D,t)`, packaged as `Setup45 G H t W p P` (the design structure in
`Submission.Work.NormalComplement._design.Vocab`).

Route: `E = W ⊓ D ≠ 1` is odd (`IsStronglyEmbedded` applied to `t ∉ H`) hence solvable (`hFT`), so
`E' < E` and some prime `p ∣ (⁅E,E⁆).relIndex E`; (D1) applied to `p` gives a cyclic `P₀ ≤ E ⊓ V`
with `P₀` a `p`-Sylow of `E` acting fixed-point-freely on `K`; let `P` be the (unique) subgroup of
order `p` of `P₀` (`p ∣ |P₀|` since `p ∣ |E|` and `P₀` is Sylow), which inherits fixed-point-freeness;
`IsMinimalIn` supplies the first three `Setup3` fields. -/
theorem exists_setup45 (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G]
    [Finite G] (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {W : Subgroup G}
    (hmin : Work.NormalComplement.IsMinimalIn H (Submission.Blueprint.twoPoint H t) W)
    (hE : W ⊓ Submission.Blueprint.twoPoint H t ≠ ⊥)
    (hD1 : Work.NormalComplement.IsD1 H t W) (hD2 : Work.NormalComplement.IsD2 H t W) :
    ∃ (p : ℕ) (P : Subgroup G),
      Work.NormalComplement.Design.Setup45 G H t W p P := by
  classical
  -- `D = twoPoint H t` has odd order by strong embeddedness applied to `t ∉ H`.
  have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  -- `E = W ⊓ D`.
  let E : Subgroup G := W ⊓ Submission.Blueprint.twoPoint H t
  have hEne : E ≠ ⊥ := hE
  have hEodd : Odd (Nat.card ↥E) :=
    Odd.of_dvd_nat hDodd
      (Subgroup.card_dvd_of_le (show E ≤ Submission.Blueprint.twoPoint H t from inf_le_right))
  -- `E` is solvable (Feit–Thompson), hence not perfect: `E' < E`.
  have hEsol : Group.IsSolvable ↥E := hFT ↥E hEodd
  have hEcomm_ne : ⁅E, E⁆ ≠ E := commutator_ne_of_solvable E hEne hEsol
  have hEcomm_le : ⁅E, E⁆ ≤ E := Subgroup.commutator_le_self E
  -- Some prime `p` divides `[E : E']`.
  have hrelne : (⁅E, E⁆).relIndex E ≠ 1 := by
    intro h1
    have hle : E ≤ ⁅E, E⁆ := Subgroup.relIndex_eq_one.mp h1
    exact hEcomm_ne (le_antisymm hle hEcomm_le).symm
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hrelne
  -- (D1) gives a cyclic `p`-Sylow `P₀ ≤ E ⊓ V` acting fixed-point-freely on `K`.
  obtain ⟨P₀, hP₀syl, hP₀le, hP₀fpf, _hP₀cyc⟩ := hD1 p hp hpdvd
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p ∣ |E|` (via `[E:E'] ∣ |E|`), and `|E| = |P₀| · [E:P₀]` with `p ∤ [E:P₀]`, so `p ∣ |P₀|`.
  have hpE : p ∣ Nat.card ↥E := dvd_trans hpdvd (Subgroup.relIndex_dvd_card ⁅E, E⁆ E)
  have hcardP₀ : Nat.card ↥(P₀.subgroupOf E) = Nat.card ↥P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀syl.2.1).toEquiv
  have hcard : Nat.card ↥E = Nat.card ↥P₀ * (P₀).relIndex E := by
    have h := Subgroup.card_mul_index (P₀.subgroupOf E)
    rw [hcardP₀] at h
    exact h.symm
  have hnot : ¬ p ∣ (P₀).relIndex E := by
    simpa only [Subgroup.relIndex] using hP₀syl.2.2
  have hpP₀ : p ∣ Nat.card ↥P₀ := by
    have h : p ∣ Nat.card ↥P₀ * (P₀).relIndex E := by rw [← hcard]; exact hpE
    exact (Nat.Prime.dvd_mul hp).mp h |>.resolve_right hnot
  -- Cauchy gives `x ∈ P₀` of order `p`; `P = ⟨x⟩` is the subgroup of order `p`.
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) p hpP₀
  have hP_leP₀ : Subgroup.zpowers (x : G) ≤ P₀ := Subgroup.zpowers_le.mpr x.2
  refine ⟨p, Subgroup.zpowers (x : G), ?_⟩
  have hPcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hPle : Subgroup.zpowers (x : G) ≤
      Design.Egrp H t W ⊓ Submission.Blueprint.centD H t :=
    le_inf (hP_leP₀.trans (show P₀ ≤ Design.Egrp H t W from hP₀syl.2.1)) (hP_leP₀.trans hP₀le)
  have hPfpf : Design.FpfOn (Subgroup.zpowers (x : G))
      (Kset (Submission.Blueprint.twoPoint H t) t) := by
    intro y hy hyne k hk hconj
    exact hP₀fpf y (hP_leP₀ hy) hyne k hk hconj
  exact { toSetup3 := { sit := hS, se := hH, invol := ht, notMem := htH, le := hmin.1,
                        normal := hmin.2.1, sup := hmin.2.2.1, Ene := hE, d1 := hD1 },
          minW := hmin, d2 := hD2, prime := hp, dvd := hpdvd,
          P_le := hPle, P_card := hPcard, P_fpf := hPfpf }

end Work.NormalComplement
