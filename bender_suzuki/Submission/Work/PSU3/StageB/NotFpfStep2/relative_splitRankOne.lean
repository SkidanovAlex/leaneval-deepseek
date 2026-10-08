import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.three_le_fixedPts_of_centralizes
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.DoubleTransitivity.Sec5.inductionStep
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer
import Submission.Work.PSU3.StageB.NotFpfStep2.twoTransitive_centralizerOddResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.NotFpfStep2.relative_splitRankOne`

Peterfalvi II, Ch. VII §4, Step 2: for the prime-order `P ≤ V = centD H t` produced by
`Work.PSU3.StageB.exists_prime_order_le_centD_centralizing` (centralising some `y ∈ Q ∖ Q₀`),
the group `U = O^{2'}(C_G(P))` carries relative split rank-one data
`(H ⊓ U, Q ⊓ U, t ∈ U)`.

The ten fields of `Work.ThmF.IsSplitRankOneData ↥U ((H ⊓ U).subgroupOf U)
((Q ⊓ U).subgroupOf U) ⟨t, htU⟩` are assembled as follows.

* `ne_top`, `even_card`, `odd_inter`: `(H ⊓ U).subgroupOf U` is strongly embedded in `↥U`
  (`isStronglyEmbedded_centralizerOddResidual`).  This is Ch. II §4 Prop. 1 (b) of
  `ChIIFourProp` at `X = P`, `F = U`, `g = 1`: its side conditions are `3 ≤ #fixedPts H P`
  (Peterfalvi's "`P` fixes three points", from the element `y ∈ Q ∖ Q₀` centralised by `P`),
  `Inv C_G(P) ⊆ U` (an involution of `C_G(P)` lies in `O^{2'}(C_G(P))`), and `U ≤ N_G(P)`.
* `twoTransitive`: `Work.PSU3.StageB.NotFpfStep2.twoTransitive_centralizerOddResidual`
  (delegated): `↥U` is `2`-transitive on `↥U ⧸ (H ⊓ U)`.  Route: the Prop. 3 clause of
  `ChIIFourProp` at `X = P` gives an epimorphism `φ : ↥U ↠ Y` onto a simple Bender group with
  central kernel; `φ(H ⊓ U)` is strongly embedded in `Y`, and the `2`-transitivity of the
  Bender action of `Y` (`ModelData.isMultiplyPretransitive_two`) descends along `φ`.
* `invol`: `orderOf ⟨t, htU⟩ = orderOf t = 2`.
* `not_mem`: `t ∉ H`.
* `le`, `normal`, `inf_eq`: the elementary subgroup-of facts (`struct_centralizerOddResidual`),
  using `Q ⊓ twoPoint H t = ⊥`.
* `sup_eq`: for `x ∈ H ⊓ U` written `x = q d` with `q ∈ Q`, `d ∈ twoPoint H t`, the *uniqueness*
  of that decomposition (from `Q ⊓ twoPoint H t = ⊥`) shows that `p ∈ P ≤ centD H t` satisfies
  `p⁻¹ q p = q` and `p⁻¹ d p = d` (because `x` is centralised by `P`).  Hence `d ∈ C_G(P)` and
  `q = x d⁻¹ ∈ C_G(P) ∩ Q` has `2`-power order (as `Q` is a `2`-group), so `q ∈ U`; then also
  `d = q⁻¹ x ∈ U`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageB.NotFpfStep2

/-- `U = centralizerOddResidual P = O^{2'}(C_G(P))` lies in `C_G(P)`. -/
theorem centralizerOddResidual_le_centralizer {G : Type} [Group G] (P : Subgroup G) :
    Work.PSU3.StageB.centralizerOddResidual P ≤ Subgroup.centralizer (P : Set G) := by
  simp only [Work.PSU3.StageB.centralizerOddResidual]
  exact Subgroup.map_subtype_le _

/-- The two-point stabiliser computed inside `↥U` when `t ∈ U`:
`twoPoint ((H ⊓ U).subgroupOf U) t = (twoPoint H t ⊓ U).subgroupOf U`. -/
theorem twoPoint_subgroupOf_inf {G : Type} [Group G] [Finite G] {H U : Subgroup G} {t : G}
    (htU : t ∈ U) :
    Submission.Blueprint.twoPoint ((H ⊓ U).subgroupOf U) (⟨t, htU⟩ : ↥U)
      = (Submission.Blueprint.twoPoint H t ⊓ U).subgroupOf U := by
  have hconjU : U.map (MulAut.conj t).toMonoidHom = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      show t * y * t⁻¹ ∈ U
      exact U.mul_mem (U.mul_mem htU hy) (U.inv_mem htU)
    · intro hx
      refine Subgroup.mem_map.mpr ⟨t⁻¹ * x * t, U.mul_mem (U.mul_mem (U.inv_mem htU) hx) htU, ?_⟩
      show t * (t⁻¹ * x * t) * t⁻¹ = x
      group
  rw [Work.DoubleTransitivity.Sec5.twoPoint_subgroupOf htU]
  congr 1
  change (H ⊓ U) ⊓ (H ⊓ U).map (MulAut.conj t).toMonoidHom
      = (H ⊓ H.map (MulAut.conj t).toMonoidHom) ⊓ U
  rw [Subgroup.map_inf H U (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, hconjU]
  ext x; simp only [Subgroup.mem_inf]; tauto

/-- **Ch. II §4 Prop. 1 (b) at `X = P`, `F = U = O^{2'}(C_G(P))`, `g = 1`.**
`H ⊓ U` is strongly embedded in `↥U`. -/
theorem isStronglyEmbedded_centralizerOddResidual {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hSit : Submission.Blueprint.Situation G)
    (hSplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) {y : G}
    (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H) (hyc : ∀ p ∈ P, p⁻¹ * y * p = y) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)) := by
  have hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H := hSplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hSplit.invol
  have htH : t ∉ H := hSplit.not_mem
  have hP1b := (hC4 G hSit H hH t ht2 htH).1
  have hy1 : y ≠ 1 := fun h => hy0 (h ▸ Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H))
  -- `P` fixes at least three points of `Ω = G ⧸ H`
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard :=
    Work.PSU3.StageB.three_le_fixedPts_of_centralizes hSplit
      (hPV.trans (Work.ThmF.centD_le_twoPoint t)) hyQ hy1 hyc
  -- involutions of `C_G(P)` lie in `U = O^{2'}(C_G(P))`
  have hInv : Submission.Blueprint.involutions (Subgroup.centralizer (P : Set G) : Set G) ⊆
      Work.PSU3.StageB.centralizerOddResidual P := by
    intro x hx
    exact Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow
      (C := Subgroup.centralizer (P : Set G)) hx.1 (k := 1) (by rw [hx.2, pow_one])
  -- `U ≤ N_G(P)`
  have hFN : Work.PSU3.StageB.centralizerOddResidual P ≤ Subgroup.normalizer (P : Set G) :=
    (centralizerOddResidual_le_centralizer P).trans (Subgroup.centralizer_le_normalizer (P : Set G))
  -- `P ≤ H`, so `P` fixes the point `H`
  have hPH : P ≤ Submission.Blueprint.conj (1 : G) H := by
    rw [Work.DoubleTransitivity.conj_one]
    exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hPV hx)).1).1
  have hres := hP1b P (Work.PSU3.StageB.centralizerOddResidual P) hX3 hInv hFN 1 hPH
  rwa [Work.DoubleTransitivity.conj_one, inf_comm] at hres

/-- The three "easy" structural fields of the split rank-one data on `↥U`, `U = O^{2'}(C_G(P))`:
`Q ⊓ U ≤ H ⊓ U`, `H ⊓ U` normalises `Q ⊓ U`, and
`(Q ⊓ U) ⊓ twoPoint (H ⊓ U) t = ⊥`. -/
theorem struct_centralizerOddResidual {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hSplit : Submission.Blueprint.IsSplitRankOne H Q t)
    {P : Subgroup G} (htU : t ∈ Work.PSU3.StageB.centralizerOddResidual P) :
    (Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P) ≤
      (H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P) ∧
    (H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P) ≤
      Subgroup.normalizer
        ((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P) :
            Subgroup ↥(Work.PSU3.StageB.centralizerOddResidual P)) ∧
    (Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P) ⊓
      Submission.Blueprint.twoPoint
        ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P))
        (⟨t, htU⟩ : ↥(Work.PSU3.StageB.centralizerOddResidual P)) = ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.subgroupOf_mono _ (inf_le_inf_right _ hSplit.le)
  · rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨hxH, -⟩ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨hyQ, -⟩ := Subgroup.mem_subgroupOf.mp hy
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp hSplit.normal x hxH y hyQ)
    · exact (Work.PSU3.StageB.centralizerOddResidual P).mul_mem
        ((Work.PSU3.StageB.centralizerOddResidual P).mul_mem x.2 y.2)
        ((Work.PSU3.StageB.centralizerOddResidual P).inv_mem x.2)
  · rw [twoPoint_subgroupOf_inf htU, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxQ : (x : G) ∈ Q := (Subgroup.mem_subgroupOf.mp hx1).1
    have hxD : (x : G) ∈ Submission.Blueprint.twoPoint H t :=
      (Subgroup.mem_subgroupOf.mp hx2).1
    have hmem : (x : G) ∈ Q ⊓ Submission.Blueprint.twoPoint H t := ⟨hxQ, hxD⟩
    rw [hSplit.inf_eq, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem

/-- **The `sup_eq` field of the split rank-one data on `↥U`**, `U = O^{2'}(C_G(P))`:
`(Q ⊓ U) ⊔ twoPoint (H ⊓ U) t = H ⊓ U`.

Write `x ∈ H ⊓ U` as `x = q d` with `q ∈ Q`, `d ∈ D = twoPoint H t` (using `H = Q ⋊ D` and the
uniqueness of that decomposition from `Q ⊓ D = ⊥`).  For `p ∈ P ≤ D` one has `x^p = x`, and
`x^p = q^p d^p` with `q^p ∈ Q`, `d^p ∈ D`; uniqueness gives `d^p = d` and `q^p = q`.  So
`d ∈ C_G(P)` and `q = x d⁻¹ ∈ C_G(P) ∩ Q`; as `Q` is a `2`-group, `q` has `2`-power order and
therefore lies in `O^{2'}(C_G(P)) = U`, whence also `d = q⁻¹ x ∈ U`. -/
theorem supEq_centralizerOddResidual {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hSplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hTwo : IsPGroup 2 Q)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t)
    (htU : t ∈ Work.PSU3.StageB.centralizerOddResidual P) :
    (Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P) ⊔
      Submission.Blueprint.twoPoint
        ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P))
        (⟨t, htU⟩ : ↥(Work.PSU3.StageB.centralizerOddResidual P))
      = (H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P) := by
  set U : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P with hUdef
  have hUC : U ≤ Subgroup.centralizer (P : Set G) := centralizerOddResidual_le_centralizer P
  have hDle : Submission.Blueprint.twoPoint H t ≤ H :=
    Work.RankOneUniqueness.twoPoint_le_left H t
  have hDnorm : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    fun z hz => hSplit.normal (hDle hz)
  -- uniqueness of the decomposition `H = Q ⋊ D`
  have huniq : ∀ {q₁ q₂ d₁ d₂ : G}, q₁ ∈ Q → q₂ ∈ Q →
      d₁ ∈ Submission.Blueprint.twoPoint H t → d₂ ∈ Submission.Blueprint.twoPoint H t →
      q₁ * d₁ = q₂ * d₂ → q₁ = q₂ ∧ d₁ = d₂ := by
    intro q₁ q₂ d₁ d₂ hq₁ hq₂ hd₁ hd₂ heq
    have hmem : q₂⁻¹ * q₁ ∈ Q ⊓ Submission.Blueprint.twoPoint H t := by
      refine ⟨Q.mul_mem (Q.inv_mem hq₂) hq₁, ?_⟩
      have hthis : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
        calc q₂⁻¹ * q₁ = q₂⁻¹ * (q₁ * d₁) * d₁⁻¹ := by group
          _ = q₂⁻¹ * (q₂ * d₂) * d₁⁻¹ := by rw [heq]
          _ = d₂ * d₁⁻¹ := by group
      rw [hthis]
      exact (Submission.Blueprint.twoPoint H t).mul_mem hd₂
        ((Submission.Blueprint.twoPoint H t).inv_mem hd₁)
    rw [hSplit.inf_eq, Subgroup.mem_bot] at hmem
    have hq : q₁ = q₂ := by
      have h := congrArg (fun z => q₂ * z) hmem
      simpa using h
    have hd : d₁ = d₂ := by
      rw [hq] at heq
      exact mul_left_cancel heq
    exact ⟨hq, hd⟩
  -- pass to `G` via the subtype
  apply Subgroup.map_injective U.subtype_injective
  rw [Subgroup.map_sup, twoPoint_subgroupOf_inf htU,
    Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Q ⊓ U ≤ U),
    Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Submission.Blueprint.twoPoint H t ⊓ U ≤ U),
    Subgroup.map_subgroupOf_eq_of_le (inf_le_right : H ⊓ U ≤ U)]
  refine le_antisymm (sup_le (le_inf (inf_le_left.trans hSplit.le) inf_le_right)
    (le_inf (inf_le_left.trans hDle) inf_le_right)) ?_
  intro x hx
  obtain ⟨hxH, hxU⟩ := Subgroup.mem_inf.mp hx
  have hxC : x ∈ Subgroup.centralizer (P : Set G) := hUC hxU
  -- decompose `x = q * d`
  have hxsup : x ∈ Q ⊔ Submission.Blueprint.twoPoint H t := by
    rw [hSplit.sup_eq]; exact hxH
  obtain ⟨q, hqQ, d, hdD, hqd⟩ :=
    Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer Q
      (Submission.Blueprint.twoPoint H t) hDnorm hxsup
  -- `P` centralises `d`
  have hdx : ∀ p ∈ P, p⁻¹ * d * p = d := by
    intro p hp
    have hpD : p ∈ Submission.Blueprint.twoPoint H t := (Work.ThmF.centD_le_twoPoint t) (hPV hp)
    have hpq : p⁻¹ * q * p ∈ Q := by
      have h := Subgroup.le_normalizer_iff.mp hSplit.normal (p⁻¹) (H.inv_mem (hDle hpD)) q hqQ
      simpa using h
    have hpd : p⁻¹ * d * p ∈ Submission.Blueprint.twoPoint H t :=
      (Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).mul_mem
          ((Submission.Blueprint.twoPoint H t).inv_mem hpD) hdD) hpD
    have hpfix : p⁻¹ * (q * d) * p = q * d := by
      have h2 : p * x = x * p := Subgroup.mem_centralizer_iff.mp hxC p hp
      calc p⁻¹ * (q * d) * p = p⁻¹ * x * p := by rw [hqd]
        _ = p⁻¹ * (x * p) := by rw [mul_assoc]
        _ = p⁻¹ * (p * x) := by rw [← h2]
        _ = x := by group
        _ = q * d := hqd
    have heq : (p⁻¹ * q * p) * (p⁻¹ * d * p) = q * d := by
      calc (p⁻¹ * q * p) * (p⁻¹ * d * p) = p⁻¹ * (q * d) * p := by group
        _ = q * d := hpfix
    exact (huniq hpq hqQ hpd hdD heq).2
  have hdC : d ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h := hdx p hp
    calc p * d = p * (p⁻¹ * d * p) := by rw [h]
      _ = d * p := by group
  have hqeq : q = x * d⁻¹ := by rw [hqd]; group
  have hqC : q ∈ Subgroup.centralizer (P : Set G) :=
    hqeq ▸ (Subgroup.centralizer (P : Set G)).mul_mem hxC
      ((Subgroup.centralizer (P : Set G)).inv_mem hdC)
  -- `q ∈ U` (2-power order) and hence `d ∈ U`
  have hqU : q ∈ U := by
    obtain ⟨k, hk⟩ := Work.PSU3.StageA.exists_orderOf_eq_two_pow_of_mem_isPGroup hTwo hqQ
    exact Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow hqC hk
  have hdU : d ∈ U := by
    have h2 : d = q⁻¹ * x := by rw [hqd]; group
    rw [h2]
    exact U.mul_mem (U.inv_mem hqU) hxU
  rw [hqd]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hqQ, hqU⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hdD, hdU⟩))

theorem relative_splitRankOne {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hSit : Submission.Blueprint.Situation G)
    (hSplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hNotZ : ¬ Submission.Blueprint.IsZassenhaus H)
    (hB3 : ∀ P' : Subgroup G, P' ≤ Submission.Blueprint.centD H t → (Nat.card P').Prime →
      Submission.Blueprint.HasFourGroup (Subgroup.centralizer (P' : Set G)))
    (hTwo : IsPGroup 2 Q)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    (hQ3 : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) (hW : Work.ThmF.W H t ≠ ⊥)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    (hPne : P ≠ ⊥) {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y)
    (htU : t ∈ Work.PSU3.StageB.centralizerOddResidual P) :
    Work.ThmF.IsSplitRankOneData ↥(Work.PSU3.StageB.centralizerOddResidual P)
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P))
      ((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P))
      ⟨t, htU⟩
  := by
  have hStrong := isStronglyEmbedded_centralizerOddResidual hSit hSplit hC4 hPV hyQ hy0 hyc
  have hTwoT := twoTransitive_centralizerOddResidual hSit hSplit hC4 hB3 hPV hPp hPne hyQ hy0 hyc
    hStrong
  have hStruct := struct_centralizerOddResidual hSplit htU
  have hSup := supEq_centralizerOddResidual hSplit hTwo hPV htU
  refine ⟨hStrong.1, hStrong.2.1, hTwoT, hStrong.2.2, ?_, ?_,
    hStruct.1, hStruct.2.1, hStruct.2.2, hSup⟩
  · rw [Subgroup.orderOf_mk]; exact hSplit.invol
  · intro hmem
    exact hSplit.not_mem (Subgroup.mem_subgroupOf.mp hmem).1

end Work.PSU3.StageB.NotFpfStep2
