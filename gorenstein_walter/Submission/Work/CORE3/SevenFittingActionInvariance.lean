import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.J4U3V18Aux.KCentralizesFittingU
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.Case1bSetup
import Submission.Work.CORE3.VUInvSetTrivial

namespace Work.CORE3

open Subgroup
open Work.GW2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas for `SevenFittingActionInvariance` -/

/-- An element of order two satisfies `s * s = 1`. -/
private theorem seven_sq_eq_one {G : Type} [Group G] {s : G} (hs : orderOf s = 2) :
    s * s = 1 := by
  have h := pow_orderOf_eq_one s
  rw [hs] at h
  simpa [pow_two] using h

/-- The set of points on which conjugation by `s` and by `s'` agree is the carrier of a
subgroup: the equations `s * x * s⁻¹ = s' * x * s'⁻¹` are preserved by products and inverses. -/
theorem sevenConjEqSubgroup {G : Type} [Group G] (s s' : G) :
    ∃ T : Subgroup G, (T : Set G) = {x : G | s * x * s⁻¹ = s' * x * s'⁻¹} := by
  let S : Set G := {x : G | s * x * s⁻¹ = s' * x * s'⁻¹}
  have hmul : ∀ {a b : G}, a ∈ S → b ∈ S → a * b ∈ S := by
    intro a b ha hb
    show s * (a * b) * s⁻¹ = s' * (a * b) * s'⁻¹
    rw [show s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) by group,
        show s' * (a * b) * s'⁻¹ = (s' * a * s'⁻¹) * (s' * b * s'⁻¹) by group, ha, hb]
  have hone : (1 : G) ∈ S := by
    show s * 1 * s⁻¹ = s' * 1 * s'⁻¹
    simp
  have hinv : ∀ {a : G}, a ∈ S → a⁻¹ ∈ S := by
    intro a ha
    show s * a⁻¹ * s⁻¹ = s' * a⁻¹ * s'⁻¹
    rw [show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ by group,
        show s' * a⁻¹ * s'⁻¹ = (s' * a * s'⁻¹)⁻¹ by group, ha]
  exact ⟨⟨⟨⟨S, @hmul⟩, hone⟩, @hinv⟩, rfl⟩

/-- `Ĥ` normalizes `U = O(H)` (`O(Ĥ) = O(H) = U` by Theorem 2.6, and `O(Ĥ) ⊴ Ĥ`). -/
private theorem seven_Hhat_le_normalizer_U {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) :
    B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
  simpa [Work.GW2.oddCoreIn] using
    c1aLe_normalizer_map_subtype (K := B.Hhat) (N := Work.GW2.oddCore ↥B.Hhat)
      (Work.GW2.oddCore_normal ↥B.Hhat)

/-- `K = I_U(t)` is normal in `F(U)`: `K = I_U(t)` is normal in `U` (Bender 1.5(iii),
`I.T.c15`) and `K ≤ F(U)`. -/
private theorem seven_K_normal_in_fitting {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1bData B)
    {t : G} (ht : t ∈ B.Hhat) (ht2 : orderOf t = 2) (htV : t ∉ pCoreIn 2 B.Hhat) :
    (D.K.subgroupOf (fittingIn B.U)).Normal := by
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := seven_Hhat_le_normalizer_U I hBc B
  have htN : t ∈ Subgroup.normalizer (B.U : Set G) := hUnorm ht
  have hKset : (D.K : Set G) = invSet B.U t := D.inv t ht ht2 htV
  have hc15 := (I.T.c15 G I.T.ft B.U t ht2 (Work.CORE2A.bSetup_U_odd B) htN).2.2 D.K hKset
  have hnormU : (D.K.subgroupOf B.U).Normal := hc15.2.1
  have hKU : D.K ≤ B.U := le_trans D.hall.1 (c1aFittingIn_le B.U)
  have hnormK : B.U ≤ Subgroup.normalizer (D.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKU).mp hnormU
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer D.hall.1).mpr
    (le_trans (c1aFittingIn_le B.U) hnormK)

/-- The Hall dichotomy for `K`: since `K` is Hall in the nilpotent group `F(U)`, every prime
core `O_q(U)` is either contained in `K` or disjoint from it. -/
private theorem seven_pCore_le_K_or_disjoint {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1bData B)
    {t : G} (ht : t ∈ B.Hhat) (ht2 : orderOf t = 2) (htV : t ∉ pCoreIn 2 B.Hhat)
    {q : ℕ} (hq : q.Prime) :
    pCoreIn q B.U ≤ D.K ∨ pCoreIn q B.U ⊓ D.K = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact isPGroup_le_or_inf_eq_bot_of_isHallIn hq D.hall
    (seven_K_normal_in_fitting I hBc B D ht ht2 htV)
    (c1aPcoreIn_le_fittingIn q B.U) (c1aIsPGroup_pCoreIn q B.U)

/-- If `O_q(U) ≤ K = I_U(t)` then `t` inverts every element of `O_q(U)`, by definition of
`I_U(t)`. -/
private theorem seven_action_inv_of_le_K {G : Type} [Group G] [Finite G]
    (B : BenderSetup G) (D : Case1bData B)
    {t : G} (ht : t ∈ B.Hhat) (ht2 : orderOf t = 2) (htV : t ∉ pCoreIn 2 B.Hhat)
    {q : ℕ} (hle : pCoreIn q B.U ≤ D.K) :
    ∀ y ∈ pCoreIn q B.U, t * y * t⁻¹ = y⁻¹ := by
  have hKmem : ∀ y : G, y ∈ D.K ↔ y ∈ invSet B.U t := by
    intro y
    show y ∈ (D.K : Set G) ↔ y ∈ invSet B.U t
    rw [D.inv t ht ht2 htV]
  intro y hy
  exact (Work.CORE2A.mem_invSet.mp ((hKmem y).mp (hle hy))).2

/-- If `O_q(U)` is disjoint from `K = I_U(t)` then `t` fixes every element of `O_q(U)`:
`t` inverts no non-trivial element of `O_q(U)` (such an element would lie in
`I_U(t) ∩ O_q(U) = K ∩ O_q(U) = ⊥`), so `t` centralizes `O_q(U)`. -/
private theorem seven_action_id_of_disjoint_K {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1bData B)
    {t : G} (ht : t ∈ B.Hhat) (ht2 : orderOf t = 2) (htV : t ∉ pCoreIn 2 B.Hhat)
    {q : ℕ} (hq : q.Prime) (hdisj : pCoreIn q B.U ⊓ D.K = ⊥) :
    ∀ y ∈ pCoreIn q B.U, t * y * t⁻¹ = y := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := seven_Hhat_le_normalizer_U I hBc B
  have htN : t ∈ Subgroup.normalizer (B.U : Set G) := hUnorm ht
  have hKmem : ∀ y : G, y ∈ D.K ↔ y ∈ invSet B.U t := by
    intro y
    show y ∈ (D.K : Set G) ↔ y ∈ invSet B.U t
    rw [D.inv t ht ht2 htV]
  have hcen : pCoreIn q B.U ≤ Subgroup.centralizer ({t} : Set G) := by
    refine c1aCentralizer_of_no_inverted (Q := pCoreIn q B.U) (x := t)
      (seven_sq_eq_one ht2) (c1aLe_normalizer_pCoreIn q B.U htN) ?_
    intro y hy hyinv
    have hyK : y ∈ D.K := (hKmem y).mpr
      (Work.CORE2A.mem_invSet.mpr ⟨c1aPcoreIn_le_self q B.U hy, hyinv⟩)
    have hmem : y ∈ pCoreIn q B.U ⊓ D.K := ⟨hy, hyK⟩
    rw [hdisj] at hmem
    simpa using hmem
  intro y hy
  have hcomm : t * y = y * t := (Subgroup.mem_centralizer_iff.mp (hcen hy)) t (by simp)
  calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [hcomm]
    _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-- **The involutions of `Ĥ ∖ V` induce the same automorphism of `F(U)`** (Bender 1981, §3,
p. 223, the parenthetical "whence `[Ĥ,s]` centralizes `F(U)`").

Setting: a minimal counterexample `G` (`BenderCtx`), `B : BenderSetup`, `Case1 B`,
`V = O₂(Ĥ)` a four-group, `U = O(Ĥ) = O(H)`, `K = D.K` the Hall subgroup of `F(U)` with
`K = I_U(s) = invSet B.U s` for every involution `s ∈ Ĥ ∖ V` (`Case1bData.inv`), `K ≠ ⊥`.

Claim: for any two involutions `s, s' ∈ Ĥ ∖ V`, conjugation by `s` and by `s'` agree on
`F(U) = fittingIn B.U`.

Route (all ingredients in the tree, sorry-free):
* `F(U) = ⨆_p O_p(U)` is nilpotent (`c1aFittingIn_eq_iSup_pCoreIn`), `K` is its `π(K)`-Hall
  subgroup, `K ≤ Z(F(U))` (`KCentralizesFittingU`), and for `q ∉ π(K)` one has
  `[s, O_q(U)] ⊆ I_U(s) ∩ O_q(U) = K ∩ O_q(U) = ⊥`, so `s` centralises `O_q(U)`
  (use `I.T.c15`'s `invSet X s = {y | ∃ x ∈ X, y = x⁻¹ * (s * x * s⁻¹)}` to see
  `[s,u] ∈ I_U(s)^u ⊆ K`);
* for `p ∈ π(K)`, `O_p(U) ⊆ K` and `s` inverts all of `K`;

hence `s` and `s'` induce the same involution of `F(U)` (and therefore products of two elements
of `Ĥ ∖ V` act trivially on `F(U)`). -/
theorem SevenFittingActionInvariance (G : Type) [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {s s' : G} (hs : s ∈ B.Hhat) (hs2 : orderOf s = 2)
    (hsV : s ∉ Work.GW2.pCoreIn 2 B.Hhat)
    (hs' : s' ∈ B.Hhat) (hs'2 : orderOf s' = 2)
    (hs'V : s' ∉ Work.GW2.pCoreIn 2 B.Hhat) :
    ∀ x ∈ Work.GW2.fittingIn B.U, s * x * s⁻¹ = s' * x * s'⁻¹ := by
  classical
  obtain ⟨T, hT⟩ := sevenConjEqSubgroup s s'
  have hle : fittingIn B.U ≤ T := by
    rw [c1aFittingIn_eq_iSup_pCoreIn B.U]
    refine iSup_le fun p => ?_
    intro y hy
    have hgoal : s * y * s⁻¹ = s' * y * s'⁻¹ := by
      rcases seven_pCore_le_K_or_disjoint I hBc B D hs hs2 hsV p.2 with hK | hdisj
      · rw [seven_action_inv_of_le_K B D hs hs2 hsV hK y hy,
            seven_action_inv_of_le_K B D hs' hs'2 hs'V hK y hy]
      · rw [seven_action_id_of_disjoint_K I hBc B D hs hs2 hsV p.2 hdisj y hy,
            seven_action_id_of_disjoint_K I hBc B D hs' hs'2 hs'V p.2 hdisj y hy]
    exact (Set.ext_iff.mp hT y).mpr hgoal
  intro x hx
  exact (Set.ext_iff.mp hT x).mp (hle hx)

end Work.CORE3
