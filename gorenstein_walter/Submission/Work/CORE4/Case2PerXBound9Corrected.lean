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
import Submission.Work.CORE4.Case2PerXBound9

/-!
# AREA CORE4 — the **corrected** per-`X` count of Bender p. 227 (pass 9, session 4)

## Why the existing reduction cannot be used

`Work.CORE4.Case2PerXBound9'` reduces §4 (12) to

    hBadBound :  ∀ X ∈ 𝓓 ∖ {P},  #{Y ∈ 𝓒 : Y ∈ badSet P E X} ≤ p₁ + (q − 1)q/p,

over **all** conjugates `Y ∈ 𝓒` of `P`.  That bound is *false*: for `X ∈ A ∖ {P}` (so that
`⟨P,X⟩ = A = P × K_p`) one has `{Y ∈ 𝓒 : Y ≤ C_G(A)} ⊆ badSet P E X`, and

    #{Y ∈ 𝓒 : Y ≤ C_G(A)} ≥ #{B ~ A : B ≤ C_G(P)} ≥ q k'

(the map `Y ↦ A^{h^{-1}}` for `P^h = Y` sends `{Y ~ P : Y ≤ C_G(A)}` onto a subset of
`{B ~ A : B ≤ C_G(P)}`, and the `q k'` subgroups `A^e = P × K_p^e`, `e ∈ E(M)`, are all
`≤ C_G(P)`).  Since `q k' ≈ q²/2` and `(q−1)q/p ≈ q²/p > p₁ + (q−1)q/p` for `p ≥ 3`, no such bound
can hold.  This is why every prover asked to supply `hBadBound`/`hCent` reported
"under-hypothesised".

## What Bender actually counts (and what is proved here)

Bender restricts the `Y`'s to the **copy containing `X`** (`X × E^g`), i.e. to
`𝓓^g := (conjSub g) '' 𝓓` for `X = P^g`: *"not more than ((q−1)/p)q conjugates Y of P lying in
X × E^g but not in M (i.e. not in A) satisfy Q ≠ 1"*.  The correct input is therefore

    ∀ g,  #{Y ∈ 𝓓^g : Y ≠ P^g, ∃ Z ∈ 𝓓 ∖ {P^g}, [Y,Z] = 1} ≤ (p₁ − 1) + (q − 1)q/p,   (CORRECT-BOUND)

and the theorem below proves that (CORRECT-BOUND) together with §4 (11) implies §4 (12) — by the
same disjointness argument as before (`Case2LowerBound9_of_perX`), with the counting done inside
`𝓓^g` instead of inside `𝓒`.

## The dictionary between the two counts

* `|𝓓^g| = |𝓓| = (p₁ − 1) q k' + 1` (conjugation is injective, §4 (11));
* `P^g = Z(W^g)` (since `P ≤ C_G(E)`), so **every** `Y ∈ 𝓓^g` commutes with `X = P^g`; hence
  `perXSet P E X ⊇ {Y ∈ 𝓓^g : Y ≠ X and no Z ∈ 𝓓∖{X} commutes with Y}`;
* the `(p₁ − 1)` in (CORRECT-BOUND) is the `𝓓 ∩ 𝓓^g` part (which is always bad for `X`), and the
  `(q−1)q/p` is Bender's "`Q ≠ 1`" family.
-/

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- Conjugation of subgroups is injective. -/
theorem conjSub_injective (g : G) : Function.Injective (Work.GW2.conjSub g) := by
  intro K L h
  exact Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _) h

/-- Conjugating twice is conjugating by the product. -/
theorem conjSub_conjSub (g u : G) (P : Subgroup G) :
    Work.GW2.conjSub g (Work.GW2.conjSub u P) = Work.GW2.conjSub (g * u) P := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- Conjugation carries centralizers into centralizers (the *right* way round: `K ≤ C(L)` gives
`K^g ≤ C(L^g)`). -/
theorem conjSub_le_centralizer (g : G) {K L : Subgroup G}
    (h : K ≤ Subgroup.centralizer (L : Set G)) :
    Work.GW2.conjSub g K ≤ Subgroup.centralizer ((Work.GW2.conjSub g L : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  simp only [Work.GW2.conjSub, SetLike.mem_coe, Subgroup.mem_map] at hx hy
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h hk) l hl]

/-- `P ⊔ E(M)` commutes with `P` (the `P`-part of `W = P ⊔ E(M)` is central in `W`). -/
theorem sup_le_centralizer_P {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {P : Subgroup G} (hPF : P ≤ h.D.F) :
    (P ⊔ Work.GW2.layerIn h.D.M : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (P_le_cent_sup h hPF hy) z hz).symm

/-- **The corrected per-`X` count of Bender p. 227.**  From §4 (11) and (CORRECT-BOUND) — the bad
conjugates counted *inside the copy* `𝓓^g = conjSub g '' 𝓓` — we obtain Bender's §4 (12). -/
theorem Case2PerXBound9_corrected (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B) (h : Work.GW2.Case2Ctx B)
    (hplus : Work.GW2.Case2PrePlus B h.D) (h7 : Work.GW2.Case2SevenFacts B h.D)
    (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : (inConjSet P (Work.GW2.layerIn h.D.M)).ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1)
    (hBadCount : ∀ g : G, Work.GW2.conjSub g P ≠ P →
      {Y : Subgroup G | (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
            Y = Work.GW2.conjSub g Z) ∧
          Y ≠ Work.GW2.conjSub g P ∧
          ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
            Z ≠ Work.GW2.conjSub g P ∧
              Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
        (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p) :
    ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((qOf h : ℚ) - 1) * qOf h / p) ≤ (h.D.M.index : ℚ) := by
  classical
  refine Case2LowerBound9_of_perX I hbc h2 h hplus h7 h8 p P A hpp hPF hPcard hObj hCount11 ?_
  intro X hXW hXne hXc
  obtain ⟨g, rfl⟩ := hXc
  -- abbreviations
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  set Ds : Set (Subgroup G) := inConjSet P E with hDs
  set Dg : Set (Subgroup G) := Work.GW2.conjSub g '' Ds with hDg
  set badC : Set (Subgroup G) :=
    {Y : Subgroup G | (∃ Z ∈ Ds, Y = Work.GW2.conjSub g Z) ∧
      Y ≠ Work.GW2.conjSub g P ∧
      ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)} with hbadC
  -- cardinality of the copy
  have hDgcard : Dg.ncard = (Work.GW2.Case2EightP1 P A - 1) *
      (h.D.M ⊓ B.H).relIndex h.D.M + 1 := by
    rw [hDg, Set.ncard_image_of_injective Ds (conjSub_injective g)]
    rw [hDs, hE, hCount11]
  have hXmem : Work.GW2.conjSub g P ∈ Dg := by
    rw [hDg]
    refine ⟨P, ?_, rfl⟩
    rw [hDs, hE]
    exact ⟨le_sup_left, ⟨1, (conjSub_one P).symm⟩⟩
  -- the bad set inside the copy is the one of `hBadCount`
  have hbadC_le : badC.ncard ≤ (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p := by
    have hh : badC = {Y : Subgroup G |
        ((∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub g Z) ∧
          Y ≠ Work.GW2.conjSub g P ∧
          ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Z ≠ Work.GW2.conjSub g P ∧
            Y ≤ Subgroup.centralizer (Z : Set G))} := by
      rw [hbadC, hDs, hE]
    rw [hh]
    exact hBadCount g hXne
  -- the dichotomy: an element of the copy which is not bad is good for `X`
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
      · -- `Y` is a conjugate of `P`
        rw [hDs, hE, inConjSet] at hZ₀
        obtain ⟨-, u, hu⟩ := hZ₀
        exact ⟨g * u, by rw [← hYZ₀, hu, conjSub_conjSub]⟩
      · -- `X` commutes with `Y`
        rw [hDs, hE, inConjSet] at hZ₀
        obtain ⟨hZ₀le, -⟩ := hZ₀
        have hZ₀P : Z₀ ≤ Subgroup.centralizer (P : Set G) :=
          hZ₀le.trans (sup_le_centralizer_P h hPF)
        have hPZ₀ : P ≤ Subgroup.centralizer (Z₀ : Set G) :=
          le_centralizer_comm.mp hZ₀P
        have := conjSub_le_centralizer g hPZ₀
        rwa [← hYZ₀]
      · -- uniqueness
        intro Z hZle hZc hZY
        by_contra hZX
        exact hbad ⟨Z, by rw [hDs, hE]; exact ⟨hZle, hZc⟩, hZX,
          le_centralizer_comm.mp hZY⟩
  -- counting
  have hcard_sdiff : (Dg \ {Work.GW2.conjSub g P}).ncard = Dg.ncard - 1 := by
    rw [Set.ncard_sdiff (s := {Work.GW2.conjSub g P}) (t := Dg)
      (by rw [Set.singleton_subset_iff]; exact hXmem), Set.ncard_singleton]
  have hle : (Dg \ {Work.GW2.conjSub g P}).ncard ≤
      (perXSet P E (Work.GW2.conjSub g P)).ncard + badC.ncard :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  -- the numerical bound, in ℚ
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
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hpp.pos
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

end Work.CORE4
