/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)
-/

import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2LowerBound9
import Submission.Work.CORE4.Case2CentA

/-!
# AREA CORE4 — Bender p. 227: the per-`X` count, reduced to ONE cardinality bound

This file carries the **assembly** of Bender's p. 227 per-`X` count, i.e. the hypothesis `hPerX` of
the proved `Work.CORE4.Case2LowerBound9_of_perX`, hence the whole of §4 (12).

## Notation

`E := layerIn h.D.M` (Bender's `E(M) ≅ L₂(q)`), `W := P ⊔ E` (an internal direct product),
`𝓒` the class of `G`-conjugates of `P`, `𝓓 := 𝓒 ∩ {subgroups of W}`, of size `(p₁ − 1) q k' + 1`
(§4 (11), proved in `Case2Count11`), and for `X ∈ 𝓓`, `X ≠ P`,

    good(X) := {Y ∈ 𝓒 : [Y,X] = 1 and no Z ∈ 𝓓 ∖ {X} commutes with Y}.

Bender's count is `#good(X) ≥ (p₁ − 1)(q k' − 1) − (q − 1)q/p` for **every** `X ∈ 𝓓 ∖ {P}`, and then
`Σ_X #good(X) ≤ #𝓒`, because a `Y` determines `X` (`perXSet_disjoint`).

## What is proved, and what is isolated

The file proves the assembly

    §4 (11)  +  #good(X) ≥ (p₁ − 1) q k' + 1 − (p₁ + (q − 1)q/p)  ⟹  §4 (12)  (hPerX),

i.e. it reduces (12) to the **single** cardinality bound

    #{Y ∈ 𝓒 : Y ≤ C_G(A)} ≤ p₁ + (q − 1)q/p.                        (CENT-BOUND)

`A` is the `(p,p)`-subgroup of §4 (8).  Of the conjugates of `P` centralizing `A`, exactly `p₁` are
the elements of `𝓓` inside `A`; the remaining `(q − 1)q/p` are Bender's "`Q ≠ 1`" conjugates.

Two structural inputs are hypotheses of the main theorem, so that everything here is *proved* and the
gap is isolated:

* `hBad` — the **bad criterion**: if `X ≠ Z ∈ 𝓓` both commute with `Y ∈ 𝓒`, then `Y` centralizes `P`.
  (This is the correct reading of the p. 227 display: the set `𝓓 ∩ C_W(Y)` is either a single
  conjugate, or it contains two elements lying in one `(p,p)`-group `P · Y₀ ∋ P`; in the latter case
  every element of `𝓓 ∩ C_W(Y)` centralizes `P`.)
* `hTwist` — the transport of (CENT-BOUND) from the copy `A = P ⊔ (A ⊓ K)` to the copy `⟨P,X⟩ ≤ W`,
  which uses the `E`-transitivity of the order-`p` subgroups of `E ≅ L₂(q)` (Dickson).
-/

namespace Work.CORE4

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## 1. The two sets -/

/-- The `G`-conjugates of `P` that centralize a given subgroup. -/
def centConjSet (P A : Subgroup G) : Set (Subgroup G) :=
  {Y : Subgroup G | (∃ g : G, Y = Work.GW2.conjSub g P) ∧
    Y ≤ Subgroup.centralizer (A : Set G)}

/-- The `G`-conjugates of `P` inside `P ⊔ E`. -/
def inConjSet (P E : Subgroup G) : Set (Subgroup G) :=
  {Y : Subgroup G | Y ≤ P ⊔ E ∧ ∃ g : G, Y = Work.GW2.conjSub g P}

/-- The `G`-conjugates of `P` commuting with `X`. -/
def commConjSet (P X : Subgroup G) : Set (Subgroup G) :=
  {Y : Subgroup G | (∃ g : G, Y = Work.GW2.conjSub g P) ∧
    Y ≤ Subgroup.centralizer (X : Set G)}

/-- The **bad** conjugates for `X`: conjugates `Y` of `P` commuting with `X` and with a *second*
conjugate `Z ∈ 𝓓 ∖ {X}` of `P` inside `P ⊔ E`.  `Y` is good (i.e. `X` is the unique conjugate of
`P` inside `C_{P⊔E}(Y)`) exactly when `Y ∈ commConjSet P X` and `Y ∉ badSet P E X`; hence

    perXSet P E X = commConjSet P X \ badSet P E X,

and Bender's p. 227 count is exactly the bound `#badSet ≤ p₁ + (q − 1)q/p`. -/
def badSet (P E X : Subgroup G) : Set (Subgroup G) :=
  {Y : Subgroup G | (∃ g : G, Y = Work.GW2.conjSub g P) ∧
    Y ≤ Subgroup.centralizer (X : Set G) ∧
    ∃ Z : Subgroup G, Z ≤ P ⊔ E ∧ (∃ g : G, Z = Work.GW2.conjSub g P) ∧ Z ≠ X ∧
      Y ≤ Subgroup.centralizer (Z : Set G)}

/-- Commutation of two subgroups is symmetric. -/
theorem le_centralizer_comm {X Y : Subgroup G} :
    (X ≤ Subgroup.centralizer (Y : Set G)) ↔ (Y ≤ Subgroup.centralizer (X : Set G)) := by
  constructor
  · intro h y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h hx) y hy).symm
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (h hy) x hx).symm

/-- `P` commutes with every element of `P ⊔ E(M)`. -/
theorem P_le_cent_sup {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {P : Subgroup G} (hPF : P ≤ h.D.F) :
    P ≤ Subgroup.centralizer ((P ⊔ Work.GW2.layerIn h.D.M : Subgroup G) : Set G) := by
  have hcomm : ∀ x ∈ P, ∀ y ∈ Work.GW2.layerIn h.D.M, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  have hLE : P ≤ Subgroup.normalizer (Work.GW2.layerIn h.D.M : Set G) :=
    fun z hz => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm z hz y hy).symm))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hmem : y ∈ ((P : Set G) * (Work.GW2.layerIn h.D.M : Set G)) := by
    have := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P (Work.GW2.layerIn h.D.M) hLE] at this
    exact this
  obtain ⟨q, hq, e, he, hqe⟩ := Set.mem_mul.mp hmem
  haveI : IsMulCommutative ↥h.D.F := h.F_cyclic.isMulCommutative
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.le_centralizer h.D.F (hPF ha)) b (hPF hb)).symm
  rw [← hqe]
  calc (q * e) * x = q * (e * x) := by rw [mul_assoc]
    _ = q * (x * e) := by rw [hcomm x hx e he]
    _ = (q * x) * e := by rw [mul_assoc]
    _ = (x * q) * e := by rw [hPab q hq x hx]
    _ = x * (q * e) := by rw [mul_assoc]

/-! ## 2. `perXSet` is a set difference -/

/-- **`perXSet` is a set difference.**  For `X ∈ 𝓓` with `X ≠ P`, the conjugates `Y` of `P` that
make `X` the unique conjugate of `P` inside `C_{P⊔E}(Y)` are exactly the conjugates of `P` commuting
with `X` but not with `P`.  The inclusion `⊇` is the bad criterion `hBad`; the reverse inclusion uses
`P ∈ 𝓓` (`P ≤ P ⊔ E` and `P = conjSub 1 P`). -/
theorem perXSet_eq_sdiff {P E X : Subgroup G}
    (hBad : ∀ X Z Y : Subgroup G, X ≤ P ⊔ E → Z ≤ P ⊔ E → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) → (∃ g : G, Z = Work.GW2.conjSub g P) →
      (∃ g : G, Y = Work.GW2.conjSub g P) → X ≠ Z →
      Y ≤ Subgroup.centralizer (X : Set G) → Y ≤ Subgroup.centralizer (Z : Set G) →
      Y ≤ Subgroup.centralizer (P : Set G))
    (hXW : X ≤ P ⊔ E) (hXne : X ≠ P) (hXc : ∃ g : G, X = Work.GW2.conjSub g P) :
    perXSet P E X = commConjSet P X \ centConjSet P P := by
  ext Y
  simp only [perXSet, Set.mem_ofPred_eq, Set.mem_sdiff, commConjSet, centConjSet]
  constructor
  · rintro ⟨hYc, hYX, huniq⟩
    refine ⟨⟨hYc, (le_centralizer_comm).mpr hYX⟩, fun hcon => ?_⟩
    obtain ⟨-, hYP⟩ := hcon
    have hPle : P ≤ Subgroup.centralizer (Y : Set G) := (le_centralizer_comm).mpr hYP
    have hPsup : P ≤ P ⊔ E := le_sup_left
    have hPconj : ∃ g : G, P = Work.GW2.conjSub g P := ⟨1, (conjSub_one' P).symm⟩
    exact hXne (huniq P hPsup hPconj hPle).symm
  · rintro ⟨⟨hYc, hYX⟩, hYnc⟩
    refine ⟨hYc, (le_centralizer_comm).mp hYX, fun Z hZle hZc hZY => ?_⟩
    by_contra hZX
    exact hYnc ⟨hYc,
      hBad X Z Y hXW hZle hXne hXc hZc hYc (fun h => hZX h.symm) hYX
        (le_centralizer_comm.mp hZY)⟩

/-! ## 3. The commuting set is at least as large as `𝓓` -/

/-- Conjugating by `g` maps `𝓓 = 𝓒 ∩ {subgroups of P ⊔ E}` onto the conjugates of `P` inside
`conjSub g (P ⊔ E)`, which all commute with `conjSub g P` (`P ≤ Z(P ⊔ E)`).  Hence

    (inConjSet P E).ncard ≤ #{Y ∈ 𝓒 : Y ≤ C_G(conjSub g P)}. -/
theorem inConjSet_card_le_commConjSet {B : Work.GW2.BenderSetup G} {P E X : Subgroup G}
    (hXc : ∃ g : G, X = Work.GW2.conjSub g P)
    (hPcent : P ≤ Subgroup.centralizer (((P ⊔ E : Subgroup G)) : Set G)) :
    (inConjSet P E).ncard ≤ (commConjSet P X).ncard := by
  obtain ⟨g, rfl⟩ := hXc
  have hcard : (Work.GW2.conjSub g '' inConjSet P E).ncard = (inConjSet P E).ncard :=
    Set.ncard_image_of_injective _ (fun K L h => Work.CORE4.conjSub_injective' g h)
  rw [← hcard]
  apply Set.ncard_le_ncard
  · rintro Y ⟨Z, ⟨hZW, hZc⟩, rfl⟩
    obtain ⟨h', rfl⟩ := hZc
    refine ⟨⟨g * h', ?_⟩, ?_⟩
    · rw [Work.CORE4.conjSub_mul']
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy hqx
      rw [← hzy, ← hqx]
      have hcomm' : q * z = z * q :=
        (Subgroup.mem_centralizer_iff.mp (hPcent hq) z (hZW hz)).symm
      calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
        _ = g * (z * q) * g⁻¹ := by rw [hcomm']
        _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  · exact Set.toFinite _

/-! ## 4. The assembly: §4 (12) from (CENT-BOUND) -/

/-- **Bender's p. 227 per-`X` count, assembled.**  From §4 (11) (`hCount11`), the bad criterion
(`hBad`), the transport of (CENT-BOUND) (`hTwist`) and the bound itself (`hCent`) follows Bender's
per-conjugate count, and hence — via the proved `Case2LowerBound9_of_perX` — the whole of §4 (12).

The counting is exact: `perXSet` is the set difference `commConjSet P X \ centConjSet P P`
(`perXSet_eq_sdiff`), the first set has at least `𝓓 = (p₁ − 1)qk' + 1` elements
(`inConjSet_card_le_commConjSet`), and the subtracted part is at most `p₁ + (q − 1)q/p`
(`hTwist` + `hCent`).  Since

    ((p₁ − 1)qk' + 1) − (p₁ + (q − 1)q/p) = (p₁ − 1)(qk' − 1) − (q − 1)q/p,

this is exactly Bender's per-`X` bound. -/
theorem Case2PerXBound9 (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B) (h : Work.GW2.Case2Ctx B)
    (hplus : Work.GW2.Case2PrePlus B h.D) (h7 : Work.GW2.Case2SevenFacts B h.D)
    (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : (inConjSet P (Work.GW2.layerIn h.D.M)).ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1)
    (hBad : ∀ X Z Y : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M →
      Z ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) → (∃ g : G, Z = Work.GW2.conjSub g P) →
      (∃ g : G, Y = Work.GW2.conjSub g P) → X ≠ Z →
      Y ≤ Subgroup.centralizer (X : Set G) → Y ≤ Subgroup.centralizer (Z : Set G) →
      Y ≤ Subgroup.centralizer (P : Set G))
    (hTwist : ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((commConjSet P X ∩ centConjSet P P).ncard : ℚ) ≤ ((centConjSet P A).ncard : ℚ))
    (hCent : ((centConjSet P A).ncard : ℚ) ≤ (Work.GW2.Case2EightP1 P A : ℚ) +
      ((Work.CORE4.qOf h : ℚ) - 1) * (Work.CORE4.qOf h : ℚ) / p) :
    ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) := by
  classical
  refine Case2LowerBound9_of_perX I hbc h2 h hplus h7 h8 p P A hpp hPF hPcard hObj hCount11 ?_
  intro X hXW hXne hXc
  set r : ℕ := (h.D.M ⊓ B.H).relIndex h.D.M
  have hPcent := P_le_cent_sup h hPF
  have hp1ge : (1 : ℕ) ≤ Work.GW2.Case2EightP1 P A :=
    Case2EightP1_pos (P := P) (A := A) hObj.2.2.2.2.2.2.1
  -- `perXSet P E X = commConjSet P X \ centConjSet P P`
  have hsplit := perXSet_eq_sdiff (P := P) (E := Work.GW2.layerIn h.D.M) (X := X) hBad hXW hXne hXc
  -- the number of conjugates of `P` commuting with `X` is at least `|𝓓|`
  have hAge : (Work.GW2.Case2EightP1 P A - 1) * r + 1 ≤ (commConjSet P X).ncard := by
    rw [← hCount11]
    exact inConjSet_card_le_commConjSet (B := B) hXc hPcent
  -- the difference, and the two bounds
  have hsub : commConjSet P X ∩ centConjSet P P ⊆ commConjSet P X := Set.inter_subset_left
  have hfine : (perXSet P (Work.GW2.layerIn h.D.M) X).ncard =
      (commConjSet P X).ncard - (commConjSet P X ∩ centConjSet P P).ncard := by
    rw [hsplit]
    have : commConjSet P X \ centConjSet P P =
        commConjSet P X \ (commConjSet P X ∩ centConjSet P P) := by
      ext Y
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [this, Set.ncard_sdiff hsub]
  have hle_nat : (commConjSet P X ∩ centConjSet P P).ncard ≤ (commConjSet P X).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  -- the numeric comparison
  have hcastA : (((Work.GW2.Case2EightP1 P A - 1) * r + 1 : ℕ) : ℚ) =
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (r : ℚ) + 1 := by
    have h1 : ((Work.GW2.Case2EightP1 P A - 1 : ℕ) : ℚ) =
        (Work.GW2.Case2EightP1 P A : ℚ) - 1 := by
      rw [Nat.cast_sub hp1ge]; norm_num
    push_cast
    rw [h1]
  have hmain : ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * (Work.CORE4.qOf h : ℚ) / p ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) := by
    have h1 : ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (r : ℚ) + 1 ≤
        ((commConjSet P X).ncard : ℚ) := by
      rw [← hcastA]; exact_mod_cast hAge
    have h2 : ((commConjSet P X ∩ centConjSet P P).ncard : ℚ) ≤
        (Work.GW2.Case2EightP1 P A : ℚ) +
          ((Work.CORE4.qOf h : ℚ) - 1) * (Work.CORE4.qOf h : ℚ) / p :=
      le_trans (hTwist X hXW hXne hXc) hCent
    have h3 : ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) =
        ((commConjSet P X).ncard : ℚ) -
          ((commConjSet P X ∩ centConjSet P P).ncard : ℚ) := by
      rw [hfine, Nat.cast_sub hle_nat]
    rw [h3]
    nlinarith [h1, h2]
  simpa using hmain

/-! ## 2'. `perXSet` is a set difference, unconditionally -/

/-- **`perXSet` is the set difference `commConjSet P X \ badSet P E X`** — with no extra hypothesis.

`⊆`: a `Y ∈ perXSet P E X` commutes with `X` and with no `Z ∈ 𝓓 ∖ {X}`, so it is not bad.
`⊇`: `Y ∈ commConjSet P X` commuting with no `Z ∈ 𝓓 ∖ {X}` satisfies the uniqueness condition of
`perXSet`, because `𝓓 ∩ C_{P⊔E}(Y)` is a set of conjugates of `P` inside `P ⊔ E` commuting with `Y`,
and the only candidate is `X` itself. -/
theorem perXSet_eq_sdiff' {P E X : Subgroup G} (hXW : X ≤ P ⊔ E)
    (hXc : ∃ g : G, X = Work.GW2.conjSub g P) :
    perXSet P E X = commConjSet P X \ badSet P E X := by
  ext Y
  constructor
  · intro hY
    simp only [perXSet, Set.mem_setOf_eq] at hY
    obtain ⟨hYc, hYX, huniq⟩ := hY
    refine ⟨⟨hYc, le_centralizer_comm.mpr hYX⟩, ?_⟩
    intro hbad
    simp only [badSet, Set.mem_setOf_eq] at hbad
    obtain ⟨-, -, Z, hZle, hZc, hZX, hZY⟩ := hbad
    exact hZX (huniq Z hZle hZc (le_centralizer_comm.mpr hZY))
  · intro hY
    rw [Set.mem_sdiff] at hY
    obtain ⟨hYcomm, hYbad⟩ := hY
    simp only [commConjSet, Set.mem_setOf_eq] at hYcomm
    obtain ⟨hYc, hYX⟩ := hYcomm
    refine ⟨hYc, le_centralizer_comm.mp hYX, ?_⟩
    intro Z hZle hZc hZY
    by_contra hZX
    exact hYbad (by
      simp only [badSet, Set.mem_setOf_eq]
      exact ⟨hYc, hYX, Z, hZle, hZc, hZX, le_centralizer_comm.mp hZY⟩)

/-! ## 4'. The assembly with a single hypothesis: the bad-`Y` count -/

/-- **Bender's p. 227 per-`X` count from ONE hypothesis.**  If the number of *bad* conjugates of `P`
for `X` (those commuting with `X` and with some second `Z ∈ 𝓓 ∖ {X}`) is at most
`p₁ + (q − 1)q/p` — which is verbatim Bender's "not more than `((q−1)/p)q` conjugates `Y` ... satisfy
`Q ≠ 1`", plus the `p₁` conjugates inside `A` — then §4 (12) follows.  The rest is proved here:
`perXSet P E X = commConjSet P X \ badSet P E X` (`perXSet_eq_sdiff'`) and
`#commConjSet P X ≥ |𝓓| = (p₁ − 1)qk' + 1` (`inConjSet_card_le_commConjSet`), so

    #perXSet ≥ ((p₁ − 1)qk' + 1) − (p₁ + (q − 1)q/p) = (p₁ − 1)(qk' − 1) − (q − 1)q/p. -/
theorem Case2PerXBound9' (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B) (h : Work.GW2.Case2Ctx B)
    (hplus : Work.GW2.Case2PrePlus B h.D) (h7 : Work.GW2.Case2SevenFacts B h.D)
    (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : (inConjSet P (Work.GW2.layerIn h.D.M)).ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1)
    (hBadBound : ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((badSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) ≤ (Work.GW2.Case2EightP1 P A : ℚ) +
        ((Work.CORE4.qOf h : ℚ) - 1) * (Work.CORE4.qOf h : ℚ) / p) :
    ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) := by
  classical
  refine Case2LowerBound9_of_perX I hbc h2 h hplus h7 h8 p P A hpp hPF hPcard hObj hCount11 ?_
  intro X hXW hXne hXc
  set r : ℕ := (h.D.M ⊓ B.H).relIndex h.D.M
  have hPcent := P_le_cent_sup h hPF
  have hp1ge : (1 : ℕ) ≤ Work.GW2.Case2EightP1 P A :=
    Case2EightP1_pos (P := P) (A := A) hObj.2.2.2.2.2.2.1
  have hsplit := perXSet_eq_sdiff' (P := P) (E := Work.GW2.layerIn h.D.M) (X := X) hXW hXc
  have hAge : (Work.GW2.Case2EightP1 P A - 1) * r + 1 ≤ (commConjSet P X).ncard := by
    rw [← hCount11]
    exact inConjSet_card_le_commConjSet (B := B) hXc hPcent
  -- `badSet ⊆ commConjSet`
  have hsub : badSet P (Work.GW2.layerIn h.D.M) X ⊆ commConjSet P X := by
    rintro Y ⟨hYc, hYX, -⟩
    exact ⟨hYc, hYX⟩
  have hle_nat : (badSet P (Work.GW2.layerIn h.D.M) X).ncard ≤ (commConjSet P X).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hfine : (perXSet P (Work.GW2.layerIn h.D.M) X).ncard =
      (commConjSet P X).ncard - (badSet P (Work.GW2.layerIn h.D.M) X).ncard := by
    rw [hsplit, Set.ncard_sdiff hsub]
  have hcastA : (((Work.GW2.Case2EightP1 P A - 1) * r + 1 : ℕ) : ℚ) =
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (r : ℚ) + 1 := by
    have h1 : ((Work.GW2.Case2EightP1 P A - 1 : ℕ) : ℚ) =
        (Work.GW2.Case2EightP1 P A : ℚ) - 1 := by
      rw [Nat.cast_sub hp1ge]; norm_num
    push_cast
    rw [h1]
  have hmain : ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * (Work.CORE4.qOf h : ℚ) / p ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) := by
    have h1 : ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (r : ℚ) + 1 ≤
        ((commConjSet P X).ncard : ℚ) := by
      rw [← hcastA]; exact_mod_cast hAge
    have h2 : ((badSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) ≤
        (Work.GW2.Case2EightP1 P A : ℚ) +
          ((Work.CORE4.qOf h : ℚ) - 1) * (Work.CORE4.qOf h : ℚ) / p :=
      hBadBound X hXW hXne hXc
    have h3 : ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) =
        ((commConjSet P X).ncard : ℚ) -
          ((badSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) := by
      rw [hfine, Nat.cast_sub hle_nat]
    rw [h3]
    nlinarith [h1, h2]
  simpa using hmain

end Work.CORE4
