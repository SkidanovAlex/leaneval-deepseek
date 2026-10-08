/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender's §4 (12) reduced to the p. 227 per-conjugate count

`Work.CORE4.Case2LowerBound9_of_perX` (proved in `Submission/Work/CORE4/Case2LowerBound9.lean`)
already carries out the disjoint-union count of Bender's p. 227, but takes two unused parameters
`h7 : Case2SevenFacts` and `h8 : Case2EightAll` (they occur only in its signature).  This module
copies its body without them (`perXCount_aux`, below) and reduces `Case2LBImpl` — hence the leaf
`Work.GW2.Case2CountImpl` — to

* `Count11CtxProp I` — Bender's (11) at the `Case2LBImpl` interface, and
* `PerXProp I` — **Bender's p. 227 per-conjugate count**: for *every* conjugate `X ≠ P` of `P`
  inside `P ⊔ E(M)` — including those inside `A` — at least
  `(p₁ − 1)(q k' − 1) − ((q − 1)/p)q` conjugates `Y` of `P` have `X` as the *only* conjugate of
  `P` inside `C_{P⊔E}(Y)`.

`PerXProp` is the amalgam analysis of `⟨E(M), E(M)^g⟩ ≤ G` on p. 227 (the displayed identities
`M^g ⊓ P·E = N_{P·E}(X) = P K S₀ = C_{P·E}(A)` and `M ⊓ X X^g E^g = X K^g S₀`, the normal
complement `Q` of `N_D(X)` in `D = C_{X X^g E^g}(Y)` with `|Q| ∣ q`, and the `L₂(q)` estimates
`I.l2torusNorm` / `I.l2normTwo`); it is the last genuinely missing piece of the leaf.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Assembly3
import Submission.Work.CORE4.Case2LowerBound9
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.L2NormTwoE
import Submission.Work.CORE4.L2TorusNormE
import Submission.Work.CORE4.Counting.XsetCount
import Submission.Work.CORE4.Counting.Count11Ctx
import Submission.Work.CORE4.ConjSubgroupCount

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- The disjoint-union count of Bender p. 227, with the unused `Case2SevenFacts` / `Case2EightAll`
parameters of `Work.CORE4.Case2LowerBound9_of_perX` removed. -/
theorem perXCount_aux (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hpp : p.Prime)
    (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
        ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1)
    (hPerX : ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
          (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
        ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
      ((Work.CORE4.perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ)) :
    ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤
      (h.D.M.index : ℚ) := by
  classical
  -- abbreviations for the two numerical ingredients
  set r : ℕ := (h.D.M ⊓ B.H).relIndex h.D.M with hr
  set p1 : ℕ := Work.GW2.Case2EightP1 P A with hp1def
  have hp1 : 1 ≤ p1 := by
    rw [hp1def]; exact Case2EightP1_pos hObj.2.2.2.2.2.2.1
  -- the index set `S := {X ≤ P ⊔ E : X ~ P}` and its difference with `{P}`
  have hSfin : (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}).Finite := Set.toFinite _
  set s : Finset (Subgroup G) := hSfin.toFinset with hs
  have hPmem : P ∈ conjSetIn P (Work.GW2.layerIn h.D.M) :=
    ⟨le_sup_left, ⟨1, (conjSub_one P).symm⟩⟩
  have hSncard : (conjSetIn P (Work.GW2.layerIn h.D.M)).ncard = (p1 - 1) * r + 1 :=
    hCount11
  have hsplit : conjSetIn P (Work.GW2.layerIn h.D.M) =
      (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}) ∪ ({P} : Set (Subgroup G)) := by
    ext X
    constructor
    · intro hX
      by_cases hXP : X = P
      · exact Or.inr (by simpa [hXP])
      · exact Or.inl ⟨hX, by simpa [hXP]⟩
    · rintro (hX | hX)
      · exact hX.1
      · rwa [Set.mem_singleton_iff.mp hX]
  have hs_card_nat : s.card = (p1 - 1) * r := by
    have h2 : (conjSetIn P (Work.GW2.layerIn h.D.M)).ncard =
        (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}).ncard + 1 := by
      conv_lhs => rw [hsplit]
      rw [Set.ncard_union_eq (by
        rw [Set.disjoint_left]
        intro x hx hxP
        exact hx.2 (Set.mem_singleton_iff.mp hxP)) (Set.toFinite _) (Set.toFinite _),
        Set.ncard_singleton]
    have h3 : (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}).ncard = s.card := by
      rw [hs]
      exact Set.ncard_eq_toFinset_card _ hSfin
    omega
  -- the counting core
  have hsub : ∀ X ∈ s, perXSet P (Work.GW2.layerIn h.D.M) X ⊆
      {Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} :=
    fun X _ => perXSet_subset P (Work.GW2.layerIn h.D.M) X
  have hdisj : ∀ X ∈ s, ∀ X' ∈ s, X ≠ X' →
      Disjoint (perXSet P (Work.GW2.layerIn h.D.M) X)
        (perXSet P (Work.GW2.layerIn h.D.M) X') := by
    intro X hX X' hX' hne
    have hXmem : X ∈ conjSetIn P (Work.GW2.layerIn h.D.M) \ {P} :=
      (Set.Finite.mem_toFinset hSfin).mp hX
    have hX'mem : X' ∈ conjSetIn P (Work.GW2.layerIn h.D.M) \ {P} :=
      (Set.Finite.mem_toFinset hSfin).mp hX'
    exact perXSet_disjoint hXmem.1.1 hX'mem.1.1 hXmem.1.2 hX'mem.1.2 hne
  have hcount := Finset.sum_ncard_le_ncard s (perXSet P (Work.GW2.layerIn h.D.M))
    {Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} hsub hdisj
  have hidxT : ({Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} : Set (Subgroup G)).ncard =
      h.D.M.index := conjSet_ncard_eq_index B h p hpp hPF hPcard
  have hcountQ : ∑ X ∈ s, ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) ≤
      (h.D.M.index : ℚ) := by
    have := hcount
    rw [hidxT] at this
    exact_mod_cast this
  -- the per-`X` lower bound, summed
  have hper : ∀ X ∈ s, ((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) := by
    intro X hX
    have hXmem : X ∈ conjSetIn P (Work.GW2.layerIn h.D.M) \ {P} :=
      (Set.Finite.mem_toFinset hSfin).mp hX
    exact hPerX X hXmem.1.1 hXmem.2 hXmem.1.2
  have hsumge : ∑ X ∈ s, (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤
      ∑ X ∈ s, ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) :=
    Finset.sum_le_sum hper
  have hconst : ∑ X ∈ s, (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) =
      (s.card : ℚ) * (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
        ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hkey : (s.card : ℚ) * (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) :=
    le_trans (le_of_eq hconst.symm) (le_trans hsumge hcountQ)
  have hscard : (s.card : ℚ) = (r : ℚ) * ((p1 : ℚ) - 1) := by
    rw [hs_card_nat, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
    ring
  rw [hscard] at hkey
  rw [hr, hp1def]
  exact hkey

/-- Bender's §4 (11) at the `Case2LBImpl` interface: `P ⊔ E(M)` contains
`(p₁ − 1) |M : M ⊓ H| + 1` conjugates of `P`, with `p₁ = Case2EightP1 P A`.
(Delegated as `Work.CORE4.Counting.Count11Ctx`.) -/
def Count11CtxProp (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
      (P A : Subgroup G),
      Even k → Odd k' →
      ((2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
        (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1)) →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      Work.GW2.Case2EightObj h.D p P A →
      Odd (qOf h) → 7 ≤ qOf h → p ∣ Nat.card ↥h.D.K0 →
      (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k' →
      {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
          ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
        (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1

/-- **Bender 1981, §4, p. 227, the per-conjugate count.**

For `E := layerIn h.D.M`, `P ≤ D.F` of order `p` and `A` the unique `(p,p)`-subgroup of `F ⊔ K`
containing `P`, and *every* conjugate `X ≠ P` of `P` inside `P ⊔ E` — including the `p₁ − 1`
conjugates lying inside `A` — at least `(p₁ − 1)(q k' − 1) − ((q − 1)/p)q` conjugates `Y` of `P`
have `X` as the *only* conjugate of `P` inside `C_{P⊔E}(Y)` (formally `Y ∈ perXSet P E X`).

The hypothesis list is the one needed to invoke Bender's (11) (`Work.CORE4.Counting.ElevenGW`,
`Work.CORE4.Counting.Count11Ctx`): `Odd (qOf h)`, `7 ≤ qOf h` for `I.l2primeCount`, and
`p ∣ Nat.card ↥h.D.K0` which produces `Kp ≤ K₀` of order `p` by Cauchy in the cyclic `K` and
identifies `A = P ⊔ Kp`.  It is the last genuinely missing piece of the leaf. -/
def PerXProp (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
      (P A : Subgroup G),
      Even k → Odd k' →
      ((2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
        (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1)) →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      Work.GW2.Case2EightObj h.D p P A →
      Odd (qOf h) → 7 ≤ qOf h → p ∣ Nat.card ↥h.D.K0 →
      (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k' →
      ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
        (∃ g : G, X = Work.GW2.conjSub g P) →
        ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
        ((Work.CORE4.perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ)

/-- **`Case2LBImpl` from (11) and the p. 227 per-conjugate count.** -/
theorem Case2LB_of_perX (I : Work.GW2.C4Inputs) (hC11 : Count11CtxProp I)
    (hPX : PerXProp I) : Case2LBImpl I := by
  intro G _ _ hbc B h k k' p P A p1 hkeven hk'odd hcases hkK hp hPF hPcard hAle hAcard hAexp
    hPAsub hAuniq hp1 hqodd hq7 hpK0 hrelMH
  have hObj : Work.GW2.Case2EightObj h.D p P A :=
    ⟨hp, hPF, hPcard, hAle, hAcard, hAexp, hPAsub, hAuniq⟩
  have h11 := hC11 G hbc B h k k' p P A hkeven hk'odd hcases hkK hp hPF hPcard hObj hqodd hq7
    hpK0 hrelMH
  have hPe : ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
          (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
        ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
      ((Work.CORE4.perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) :=
    hPX G hbc B h k k' p P A hkeven hk'odd hcases hkK hp hPF hPcard hObj hqodd hq7 hpK0 hrelMH
  have haux := perXCount_aux I h p P A hp hPF hPcard hObj h11 hPe
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


/-- **`Work.GW2.Case2CountImpl I` from §4 (8), (11) and the p. 227 per-conjugate count.** -/
theorem Case2CountImpl_of_pieces4 (I : Work.GW2.C4Inputs)
    (hNu : EightNuCtxProp I) (hC11 : Count11CtxProp I) (hPX : PerXProp I) :
    Work.GW2.Case2CountImpl I :=
  Case2CountImpl_of_pieces2 I hNu (Case2LB_of_perX I hC11 hPX)


/-- Bender's p. 227 per-conjugate count, `X ≤ A` case (delegated as
`Work.CORE4.Counting.PerXInA`). -/
def PerXInAProp (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
      (P A : Subgroup G),
      Even k → Odd k' →
      ((2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
        (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1)) →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      Work.GW2.Case2EightObj h.D p P A →
      Odd (qOf h) → 7 ≤ qOf h → p ∣ Nat.card ↥h.D.K0 →
      (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k' →
      ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P → X ≤ A →
        (∃ g : G, X = Work.GW2.conjSub g P) →
        ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
        ((Work.CORE4.perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ)

/-- Bender's p. 227 per-conjugate count, `X ≰ A` case (delegated as
`Work.CORE4.Counting.PerXNotA`). -/
def PerXNotAProp (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
      (P A : Subgroup G),
      Even k → Odd k' →
      ((2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
        (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1)) →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      Work.GW2.Case2EightObj h.D p P A →
      Odd (qOf h) → 7 ≤ qOf h → p ∣ Nat.card ↥h.D.K0 →
      (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k' →
      ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P → ¬ X ≤ A →
        (∃ g : G, X = Work.GW2.conjSub g P) →
        ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
        ((Work.CORE4.perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ)

/-- `PerXProp` from its two cases. -/
theorem PerXProp_of (I : Work.GW2.C4Inputs) (h1 : PerXInAProp I) (h2 : PerXNotAProp I) :
    PerXProp I := by
  intro G _ _ hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj hqodd hq7 hpK0
    hrelMH X hXE hXne hconj
  by_cases hXA : X ≤ A
  · exact h1 G hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj hqodd hq7 hpK0
      hrelMH X hXE hXne hXA hconj
  · exact h2 G hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj hqodd hq7 hpK0
      hrelMH X hXE hXne hXA hconj

/-- Bender's (11) at the `Case2LBImpl` interface, from the proved
`Work.CORE4.Counting.Count11Ctx`. -/
theorem Count11CtxProp_proof (I : Work.GW2.C4Inputs) : Count11CtxProp I :=
  fun G _ _ hbc B h k k' p P A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    Work.CORE4.Counting.Count11Ctx I G hbc B h k k' p P A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

/-- **`Work.GW2.Case2CountImpl I` from §4 (8) and the two cases of the p. 227 per-conjugate
count.** -/
theorem Case2CountImpl_of_pieces5 (I : Work.GW2.C4Inputs)
    (hNu : EightNuCtxProp I) (hIn : PerXInAProp I) (hNot : PerXNotAProp I) :
    Work.GW2.Case2CountImpl I :=
  Case2CountImpl_of_pieces4 I hNu (Count11CtxProp_proof I) (PerXProp_of I hIn hNot)

end Work.CORE4
