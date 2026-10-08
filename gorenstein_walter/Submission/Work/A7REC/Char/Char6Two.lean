/-
Area `A7REC`: **C1 assembled with the corrected C1e leaf** (`A7Y6Values2Prop`).

This file is the non-circular replacement of `Char/a7Char6_of_table.lean`, which took the
too-weak contracted leaf `A7Y6ValuesProp`.  It redoes the C1 assembly with `A7Y6Values2Prop`
in place of `A7Y6ValuesProp` (no other change: the degree-`6` package `deg6_package` does not use
the value lemma), and assembles C1 from the area's proved leaves and the caller's one-class
input:

`Work.A7REC.Char.a7Char6_two (hone) (a7Y6Values2) : A7Char6Prop`.

The proof of `a7Y6Values2 : A7Y6Values2Prop` itself lives in
`Submission/Work/A7REC/Char/Y6Values2.lean` (which imports the six proved pieces and the assembly
`a7Y6Values2_of_pieces` of `Char/Y6Main.lean`).
-/
import Submission.Work.A7REC.Char.a7Char6_of_table
import Submission.Work.A7REC.Char.Y6Main
import Submission.Work.A7REC.Char.a7TableLemma
import Submission.Work.A7REC.Char.a7C1b
import Submission.Work.A7REC.Char.a7Bridge
import Submission.Work.A7REC.Char.InvCounts2

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup OddOrder.RepresentationTheory

/-- **C1 assembled with the corrected value lemma.**  Identical to `a7Char6_of_table`, with
`A7Y6Values2Prop` in place of `A7Y6ValuesProp`; the one-class hypothesis is supplied by `hone`. -/
theorem a7Char6_of_table2
    (hone : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      Work.A7REC.A7RecHyps G S z U V → Work.A7REC.OneInvClass G)
    (hTab : Work.A7REC.A7TableLemmaProp) (hC1b : Work.A7REC.A7C1bProp)
    (hBr : Work.A7REC.A7BridgeProp) (hCnt : Work.A7REC.A7InvolutionCounts2Prop)
    (hY6 : Work.A7REC.A7Y6Values2Prop) : Work.A7REC.A7Char6Prop := by
  intro G instG instF S z U V hyps
  letI : Group G := instG
  letI : Finite G := instF
  haveI : Fintype G := Fintype.ofFinite G
  let ctx : A7RecCtx G := A7RecCtx.ofHyps hyps
  have honeG : OneInvClass G := hone G S z U V hyps
  have hU3 : Nat.card U = 3 := hyps.2.2.2.2.2.2.2.1
  have hCz : Subgroup.centralizer ({z} : Set G) = U ⊔ (S : Subgroup G) :=
    hyps.2.2.2.2.2.2.1
  -- a fixed non-identity element of `U`, used to produce the representation
  obtain ⟨σ, hσU, hσ1⟩ : ∃ σ : G, σ ∈ U ∧ σ ≠ 1 := by
    haveI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU3]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : U)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨W, hAC, hMod, hFD, ρ, hρirr, h6, hztr, hzσtr, huniq⟩ :=
    deg6_package hTab hC1b hBr hCnt S z U V hyps honeG hσU hσ1
  letI : AddCommGroup W := hAC
  letI : Module ℂ W := hMod
  letI : FiniteDimensional ℂ W := hFD
  -- a non-identity element of `U` has order `3` and commutes with `z`
  have horder : ∀ u ∈ U, u ≠ 1 → orderOf u = 3 := by
    intro u hu hu1
    have hdvd : orderOf u ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (α := G) (Subgroup.zpowers_le.mpr hu)
      rwa [Nat.card_zpowers, hU3] at h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h3
  have hcommute : ∀ u ∈ U, z * u = u * z := by
    intro u hu
    have hC : u ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [hCz]
      exact Subgroup.mem_sup_left hu
    exact Subgroup.mem_centralizer_iff.mp hC z (Set.mem_singleton z)
  -- the values at the order-`7` elements
  have horder7 : ∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1 := by
    exact (hY6 G S z U V hyps honeG σ W ρ hσU hσ1 (horder σ hσU hσ1) (hcommute σ hσU) hρirr h6
      hztr hzσtr huniq).2
  refine ⟨W, hAC, hMod, hFD, ρ, h6, hztr, ?_, horder7⟩
  -- the values on `U^#`: run the construction for `u` and transfer the value at `z * u`
  intro u hu hu1
  obtain ⟨Wu, hACu, hModu, hFDu, ρu, hρuirr, h6u, _hzu, hzutr, huniqu⟩ :=
    deg6_package hTab hC1b hBr hCnt S z U V hyps honeG hu hu1
  letI : AddCommGroup Wu := hACu
  letI : Module ℂ Wu := hModu
  letI : FiniteDimensional ℂ Wu := hFDu
  have hzu : LinearMap.trace ℂ W (ρ (z * u)) = -1 := by
    rw [← huniq Wu ρu hρuirr h6u (z * u)]
    exact hzutr
  exact (hY6 G S z U V hyps honeG u W ρ hu hu1 (horder u hu hu1) (hcommute u hu) hρirr h6 hztr
    hzu huniq).1

/-- **C1, non-circular**, from the area's proved leaves and `A7Y6Values2Prop`. -/
theorem a7Char6_two
    (hone : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      Work.A7REC.A7RecHyps G S z U V → Work.A7REC.OneInvClass G)
    (hY6 : Work.A7REC.A7Y6Values2Prop) : Work.A7REC.A7Char6Prop :=
  a7Char6_of_table2 hone a7TableLemma a7C1b a7Bridge Work.A7REC.c13_counts hY6

end Work.A7REC.Char
