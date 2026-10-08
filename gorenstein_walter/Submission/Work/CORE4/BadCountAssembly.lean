/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the counting leaf assembled from TWO residuals at the best available level

`Work.CORE4.Case2CountImpl_of_pieces5` (in `PerXAssembly.lean`) already reduces the leaf
`Work.GW2.Case2CountImpl` to §4 (8) (`EightNuCtxProp`) plus the p. 227 per-`X` count.  Its second
input, however, went through `Work.CORE4.Case2PerXBound9'`'s `hBadBound`, which is **false**
(see `Submission/Work/CORE4/Case2PerXBound9Corrected.lean` and `NOTES_CASE2COUNTIMPL9C.md` §7):
`badSet P E X` ranges over *all* conjugates of `P`, whereas Bender counts only inside the copy
`X·E^g` containing `X`.

This module replaces that input by the *corrected* count and thereby assembles
`Work.GW2.Case2CountImpl` from exactly two residuals, each stated at the strongest level available
from `Case2Ctx` (`Case2PrePlus` and `Case2SevenFacts` are *proved* consequences of `Case2Ctx` —
`Case2PrePlusOfCtx`, `Case2SevenFacts_of_ctx` — so they are discharged here, not assumed):

* `Work.CORE4.EightNuCtxCore` — Bender §4 (8): `A ⊴ F(U)` and `u ≤ p`;
* `Work.CORE4.BadCountCtxProp I` (this file) — Bender p. 227, *copy-restricted*: for every
  conjugate `X = P^g ≠ P` of `P` inside `P ⊔ E(M)`, the number of conjugates `Y ∈ 𝓓^g` of `P`
  inside the copy `X·E^g` that commute with some second member of `𝓓` is at most
  `(p₁ − 1) + ((q − 1)/p) q`.

## What is proved here

* `Case2LB_of_badCount`: §4 (12) (`Case2LBImpl`) from `BadCountCtxProp`, using the proved
  §4 (11) (`Work.CORE4.Counting.Count11Ctx`), the proved disjoint-union count `perXCount_aux`,
  and the corrected per-`X` argument of `Case2PerXBound9Corrected.lean` (copied here in the shape
  `perXCount_aux` needs, which does not mention §4 (7)/(8) or `Case2EightAll`);
* `Case2CountImpl_of_pieces6`: the leaf from §4 (8) and the corrected count.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Arith
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Assembly3
import Submission.Work.CORE4.PerXAssembly
import Submission.Work.CORE4.Case2PerXBound9
import Submission.Work.CORE4.Case2PerXBound9Corrected
import Submission.Work.CORE4.Case2EightAllOfCtx
import Submission.Work.CORE4.Counting.Count11Ctx

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- **Bender 1981, §4, p. 227, the copy-restricted bad-`Y` count.**

For every conjugate `X = P^g ≠ P` of `P` inside `W := P ⊔ E(M)`, the number of conjugates `Y` of
`P` lying in the copy `𝓓^g = (conjSub g) '' 𝓓` (`𝓓 = {X ≤ W : X ~ P}`, of size `(p₁−1)qk' + 1`
by §4 (11)) that commute with some second member `Z ≠ P^g` of `𝓓` is at most
`(p₁ − 1) + ((q − 1)/p) q`.

The `(p₁ − 1)` is the `𝓓 ∩ 𝓓^g` part (always bad for `X`) and `((q − 1)/p) q` is Bender's
"`Q ≠ 1`" family.  This is the *corrected* form of `Work.CORE4.Case2PerXBound9'`'s `hBadBound`
(which is false): the `Y`'s are restricted to the copy containing `X`, exactly as in Bender's
sentence *"not more than `((q − 1)/p)q` conjugates `Y` of `P` lying in `X × E^g` but not in `M` …
satisfy `Q ≠ 1`"*. -/
def BadCountCtxProp (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G),
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Work.GW2.Case2EightObj h.D p P A →
      ∀ g : G, Work.GW2.conjSub g P ≠ P → Work.GW2.conjSub g P ≤ P ⊔ Work.GW2.layerIn h.D.M →
      {Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub g Z) ∧
            Y ≠ Work.GW2.conjSub g P ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
        (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p

/-- **§4 (12) from the copy-restricted count.** -/
theorem Case2LB_of_badCount (I : Work.GW2.C4Inputs) (hB : BadCountCtxProp I) :
    Case2LBImpl I := by
  intro G _ _ hbc B h k k' p P A p1 hkeven hk'odd hcases hkK hp hPF hPcard hAle hAcard hAexp
    hPAsub hAuniq hp1 hqodd hq7 hpK0 hrelMH
  have hObj : Work.GW2.Case2EightObj h.D p P A :=
    ⟨hp, hPF, hPcard, hAle, hAcard, hAexp, hPAsub, hAuniq⟩
  -- `p ∣ |K₀|`, as in §4 (8)
  have hpK0' : p ∣ Nat.card ↥h.D.K0 := by
    rw [← hPcard]
    exact (Subgroup.card_dvd_of_le hPF).trans (card_F_dvd_card_K0_of_ctx I hbc B h)
  -- §4 (11), at the `Case2LBImpl` interface
  have h11 := Work.CORE4.Counting.Count11Ctx I G hbc B h k k' p P A hkeven hk'odd hcases hkK hp
    hPF hPcard hObj hqodd hq7 hpK0' hrelMH
  have h11i : (inConjSet P (Work.GW2.layerIn h.D.M)).ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1 := h11
  -- the disjoint-union count, fed with the per-`X` bound proved inside
  have haux : ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
      (((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
          (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
        ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) := by
    refine perXCount_aux I h p P A hp hPF hPcard hObj h11 ?_
    intro X hXW hXne hXc
    obtain ⟨g, rfl⟩ := hXc
    -- ## Bender's p. 227 argument, restricted to the copy `𝓓^g` containing `X = P^g`
    set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
    set Ds : Set (Subgroup G) := inConjSet P (Work.GW2.layerIn h.D.M) with hDs
    set Dg : Set (Subgroup G) := Work.GW2.conjSub g '' Ds with hDg
    set badC : Set (Subgroup G) :=
      {Y : Subgroup G | (∃ Z ∈ Ds, Y = Work.GW2.conjSub g Z) ∧
        Y ≠ Work.GW2.conjSub g P ∧
        ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)} with hbadC
    have hDgcard : Dg.ncard = (Work.GW2.Case2EightP1 P A - 1) *
        (h.D.M ⊓ B.H).relIndex h.D.M + 1 := by
      rw [hDg, Set.ncard_image_of_injective Ds (conjSub_injective g)]
      rw [hDs, h11i]
    have hXmem : Work.GW2.conjSub g P ∈ Dg := by
      rw [hDg]
      refine ⟨P, ?_, rfl⟩
      rw [hDs]
      exact ⟨le_sup_left, ⟨1, (conjSub_one P).symm⟩⟩
    have hbadC_le : badC.ncard ≤
        (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p := by
      have hh : badC = {Y : Subgroup G |
          ((∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub g Z) ∧
            Y ≠ Work.GW2.conjSub g P ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Z ≠ Work.GW2.conjSub g P ∧
              Y ≤ Subgroup.centralizer (Z : Set G))} := by
        rw [hbadC, hDs]
      rw [hh]
      exact hB G hbc B h p P A hp hPF hPcard hObj g hXne hXW
    -- an element of the copy which is not bad has `X` as its only conjugate in `C_W(·)`
    have hsub : Dg \ {Work.GW2.conjSub g P} ⊆
        perXSet P E (Work.GW2.conjSub g P) ∪ badC := by
      intro Y hY
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hY
      obtain ⟨hYDg, hYne⟩ := hY
      rw [hDg, Set.mem_image] at hYDg
      obtain ⟨Z₀, hZ₀, hYZ₀⟩ := hYDg
      by_cases hbad : ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧
          Y ≤ Subgroup.centralizer (Z : Set G)
      · refine Or.inr ⟨?_, hYne, hbad⟩
        exact ⟨Z₀, hZ₀, hYZ₀.symm⟩
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · rw [hDs, inConjSet] at hZ₀
          obtain ⟨-, u, hu⟩ := hZ₀
          exact ⟨g * u, by rw [← hYZ₀, hu, conjSub_conjSub]⟩
        · rw [hDs, inConjSet] at hZ₀
          obtain ⟨hZ₀le, -⟩ := hZ₀
          have hZ₀P : Z₀ ≤ Subgroup.centralizer (P : Set G) :=
            hZ₀le.trans (sup_le_centralizer_P h hPF)
          have hPZ₀ : P ≤ Subgroup.centralizer (Z₀ : Set G) :=
            le_centralizer_comm.mp hZ₀P
          have := conjSub_le_centralizer g hPZ₀
          rwa [← hYZ₀]
        · intro Z hZle hZc hZY
          by_contra hZX
          exact hbad ⟨Z, by rw [hDs]; exact ⟨hZle, hZc⟩, hZX,
            le_centralizer_comm.mp hZY⟩
    -- counting
    have hcard_sdiff : (Dg \ {Work.GW2.conjSub g P}).ncard = Dg.ncard - 1 := by
      rw [Set.ncard_sdiff (s := {Work.GW2.conjSub g P}) (t := Dg)
        (by rw [Set.singleton_subset_iff]; exact hXmem), Set.ncard_singleton]
    have hle : (Dg \ {Work.GW2.conjSub g P}).ncard ≤
        (perXSet P E (Work.GW2.conjSub g P)).ncard + badC.ncard :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    -- the numerical bound, in `ℚ`
    have hp1 : (1 : ℕ) ≤ Work.GW2.Case2EightP1 P A :=
      Case2EightP1_pos (P := P) (A := A) hObj.2.2.2.2.2.2.1
    have hDgpos : (1 : ℕ) ≤ Dg.ncard :=
      Nat.succ_le_iff.mpr (Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hXmem⟩)
    have hdiffcast : (((Dg \ {Work.GW2.conjSub g P}).ncard : ℕ) : ℚ) = (Dg.ncard : ℚ) - 1 := by
      rw [hcard_sdiff, Nat.cast_sub hDgpos, Nat.cast_one]
    have hDgcast : (Dg.ncard : ℚ) =
        ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) + 1 := by
      rw [hDgcard, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
    have hunion : (((Dg \ {Work.GW2.conjSub g P}).ncard : ℕ) : ℚ) ≤
        (((perXSet P E (Work.GW2.conjSub g P)).ncard : ℕ) : ℚ) + ((badC.ncard : ℕ) : ℚ) := by
      exact_mod_cast hle
    have hbadcast : ((badC.ncard : ℕ) : ℚ) ≤
        ((Work.GW2.Case2EightP1 P A : ℚ) - 1) + ((((qOf h - 1) * qOf h) / p : ℕ) : ℚ) := by
      have h1 : ((badC.ncard : ℕ) : ℚ) ≤
          (((Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p : ℕ) : ℚ) := by
        exact_mod_cast hbadC_le
      rwa [Nat.cast_add, Nat.cast_sub hp1] at h1
    have htdiv : ((((qOf h - 1) * qOf h) / p : ℕ) : ℚ) ≤
        ((qOf h : ℚ) - 1) * (qOf h : ℚ) / (p : ℚ) := by
      have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
      rw [le_div_iff₀ hp0]
      have h1 : ((((qOf h - 1) * qOf h) / p : ℕ) : ℚ) * (p : ℚ) ≤
          (((qOf h - 1) * qOf h : ℕ) : ℚ) := by
        rw [← Nat.cast_mul]
        exact_mod_cast Nat.div_mul_le_self ((qOf h - 1) * qOf h) p
      have h2 : (((qOf h - 1) * qOf h : ℕ) : ℚ) = ((qOf h : ℚ) - 1) * (qOf h : ℚ) := by
        rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ qOf h by have := nineP_seven h; omega),
          Nat.cast_one]
      linarith [h1, h2.le, h2.ge]
    have hgoal : ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((qOf h : ℚ) - 1) * (qOf h : ℚ) / (p : ℚ) ≤
        ((perXSet P E (Work.GW2.conjSub g P)).ncard : ℚ) := by
      nlinarith [hunion, hdiffcast, hDgcast, hbadcast, htdiv]
    simpa using hgoal
  -- the last step: multiply `perXCount_aux` by `q k' = |M : M ⊓ H|`
  set r : ℚ := ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) with hrdef
  have hrval : r = (qOf h : ℚ) * k' := by
    rw [hrdef, hrelMH]; push_cast; ring
  have hrnn : (0 : ℚ) ≤ r := by rw [hrdef]; positivity
  have hmul := mul_le_mul_of_nonneg_right haux hrnn
  have hcast : ((qOf h * k' * h.D.M.index : ℕ) : ℚ) = (h.D.M.index : ℚ) * r := by
    rw [hrval]; push_cast; ring
  have hgoal : (((qOf h : ℚ) * k' * ((p1 : ℚ) - 1) * ((qOf h : ℚ) * k')) *
      (((p1 : ℚ) - 1) * ((qOf h : ℚ) * k' - 1) - ((qOf h : ℚ) - 1) * qOf h / p)) =
      (r * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (r - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p)) * r := by
    rw [hrval, hp1]
    simp only [Work.GW2.Case2EightP1]
    ring
  rw [hcast, hgoal]
  exact hmul

/-- **The counting leaf from §4 (8) and the copy-restricted p. 227 count.** -/
theorem Case2CountImpl_of_pieces6 (I : Work.GW2.C4Inputs)
    (hNu : EightNuCtxProp I) (hB : BadCountCtxProp I) :
    Work.GW2.Case2CountImpl I :=
  Case2CountImpl_of_pieces2 I hNu (Case2LB_of_badCount I hB)

end Work.CORE4
