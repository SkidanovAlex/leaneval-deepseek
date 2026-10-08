import Mathlib
import Submission.Work.BG.CharBridge
import Submission.Work.BG.singleCoincidence
import Submission.Work.BG.doubleCoincidence
import Submission.Work.BG.signedPairCoeffNeZero
import Submission.Work.BG.signOrthContra

/-!
# Area BG, Remark 1.5 of Bender–Glauberman (1981): disjointness of norm-`2` characters

**Remark 1.5** (Bender–Glauberman 1981, *Characters of finite groups with dihedral Sylow
2-subgroups*, J. Algebra 77, p. 202).  Let `δ` and `ε` be generalized (= virtual) characters
of a finite group `G` with `‖δ‖² = ‖ε‖² = 2`, `δ(1) = ε(1)` and `⟨δ, ε⟩ = 0`.  Then `δ` and
`ε` are *disjoint*: no irreducible character `χ` of `G` has both `⟨δ, χ⟩ ≠ 0` and
`⟨ε, χ⟩ ≠ 0`.

The formalization below proves exactly the disjointness conclusion for the library's
`ClassFunction.inner` pairing (normalized by `1/|G|`), namely

`ClassFunction.inner δ χ = 0 ∨ ClassFunction.inner ε χ = 0`.

## Proof

By `exists_signed_pair_of_mem_ZIrr_inner_self_eq_two` (the norm-`2` structure lemma, the
converse of Peterfalvi §3 `dirr_small_norm`) both virtual characters are signed sums of two
distinct irreducibles,

`δ = a·α + b·β`, `ε = c·γ + d·ζ`,   `a,b,c,d ∈ {±1}`, `α ≠ β`, `γ ≠ ζ`.

Suppose an irreducible `χ` has `⟨δ,χ⟩ ≠ 0` and `⟨ε,χ⟩ ≠ 0`.  Because `⟨α,χ⟩, ⟨β,χ⟩ ∈ {0,1}`
and `α ≠ β`, the first inequality forces `χ ∈ {α,β}`; likewise `χ ∈ {γ,ζ}`.  So `χ` lies in
both pairs and exactly one of four coincidences holds.  If exactly one of the four pairings
`α = γ`, `α = ζ`, `β = γ`, `β = ζ` occurs, then `⟨δ,ε⟩ = ±1 ≠ 0`, contradicting orthogonality
(`Work.BG.singleCoincidence`).  If both occur, i.e. `{α,β} = {γ,ζ}`, then orthogonality gives
`ac + bd = 0` while `δ(1) = ε(1)` gives a *second* relation between `α(1)` and `β(1)`; the two
together force `α(1) = 0` or `β(1) = 0`, impossible for an irreducible character
(`Work.BG.doubleCoincidence`).  Hence no such `χ` exists.

The pieces invoked here are elementary orthonormality computations (`⟨χ,ψ⟩ = δ_{χψ}`); the
whole content of the remark is the key observation above that orthogonality of the two
generalized characters forbids every common constituent.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Bender–Glauberman 1981, Remark 1.5.** Two virtual characters `δ`, `ε` with
`‖δ‖² = ‖ε‖² = 2`, `δ(1) = ε(1)` and `⟨δ,ε⟩ = 0` are disjoint: every irreducible character
`χ` satisfies `⟨δ,χ⟩ = 0` or `⟨ε,χ⟩ = 0`. -/
theorem remark15Disjoint {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {δ ε : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hδ : δ ∈ OddOrder.RepresentationTheory.ZIrr G)
    (hε : ε ∈ OddOrder.RepresentationTheory.ZIrr G)
    (hδ2 : OddOrder.RepresentationTheory.ClassFunction.inner δ δ = 2)
    (hε2 : OddOrder.RepresentationTheory.ClassFunction.inner ε ε = 2) (h1 : δ 1 = ε 1)
    (ho : OddOrder.RepresentationTheory.ClassFunction.inner δ ε = 0)
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) :
    OddOrder.RepresentationTheory.ClassFunction.inner δ
        (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) = 0 ∨
      OddOrder.RepresentationTheory.ClassFunction.inner ε
        (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) = 0 := by
  classical
  -- Norm-`2` structure: each virtual character is a signed sum of two distinct irreducibles.
  obtain ⟨α, β, a, b, hαirr, hβirr, hαβ, ha, hb, hδeq⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hδ hδ2
  obtain ⟨γ, ζ, c, d, hγirr, hζirr, hγζ, hc, hd, hεeq⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hε hε2
  have hαmem : α ∈ irreducibleCharacters G := hαirr
  have hβmem : β ∈ irreducibleCharacters G := hβirr
  have hγmem : γ ∈ irreducibleCharacters G := hγirr
  have hζmem : ζ ∈ irreducibleCharacters G := hζirr
  -- The two relations on the expanded signed sums, transported along the decompositions.
  have horth : ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β)
      ((c : ℂ) • γ + (d : ℂ) • ζ) = 0 := by
    rw [← hδeq, ← hεeq]; exact ho
  have hdegeq : ((a : ℂ) • α + (b : ℂ) • β) (1 : G) = ((c : ℂ) • γ + (d : ℂ) • ζ) (1 : G) := by
    rw [← hδeq, ← hεeq]; exact h1
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hδχ, hεχ⟩ := hcon
  -- Nonvanishing inner products with `χ` force `χ` into the support of each signed pair.
  have hχab : (χ : ClassFunction G ℂ) = α ∨ (χ : ClassFunction G ℂ) = β :=
    signedPairCoeffNeZero hαmem hβmem hαβ χ (by rwa [hδeq] at hδχ)
  have hχcd : (χ : ClassFunction G ℂ) = γ ∨ (χ : ClassFunction G ℂ) = ζ :=
    signedPairCoeffNeZero hγmem hζmem hγζ χ (by rwa [hεeq] at hεχ)
  rcases hχab with hχa | hχb
  · rcases hχcd with hχc | hχd
    · -- `χ = α = γ`
      have hαγ : α = γ := hχa.symm.trans hχc
      by_cases hβζ : β = ζ
      · exact doubleCoincidence ha hb hc hd hαirr hβirr hγirr hζirr hαβ hγζ
          (Or.inl ⟨hαγ, hβζ⟩) horth hdegeq
      · exact singleCoincidence ha hb hc hd hαmem hβmem hγmem hζmem hαβ hγζ
          (Or.inl ⟨hαγ, hβζ⟩) horth
    · -- `χ = α = ζ`
      have hαζ : α = ζ := hχa.symm.trans hχd
      by_cases hβγ : β = γ
      · exact doubleCoincidence ha hb hc hd hαirr hβirr hγirr hζirr hαβ hγζ
          (Or.inr ⟨hαζ, hβγ⟩) horth hdegeq
      · exact singleCoincidence ha hb hc hd hαmem hβmem hγmem hζmem hαβ hγζ
          (Or.inr (Or.inl ⟨hαζ, hβγ⟩)) horth
  · rcases hχcd with hχc | hχd
    · -- `χ = β = γ`
      have hβγ : β = γ := hχb.symm.trans hχc
      by_cases hαζ : α = ζ
      · exact doubleCoincidence ha hb hc hd hαirr hβirr hγirr hζirr hαβ hγζ
          (Or.inr ⟨hαζ, hβγ⟩) horth hdegeq
      · exact singleCoincidence ha hb hc hd hαmem hβmem hγmem hζmem hαβ hγζ
          (Or.inr (Or.inr (Or.inl ⟨hβγ, hαζ⟩))) horth
    · -- `χ = β = ζ`
      have hβζ : β = ζ := hχb.symm.trans hχd
      by_cases hαγ : α = γ
      · exact doubleCoincidence ha hb hc hd hαirr hβirr hγirr hζirr hαβ hγζ
          (Or.inl ⟨hαγ, hβζ⟩) horth hdegeq
      · exact singleCoincidence ha hb hc hd hαmem hβmem hγmem hζmem hαβ hγζ
          (Or.inr (Or.inr (Or.inr ⟨hβζ, hαγ⟩))) horth

end Work.BG
