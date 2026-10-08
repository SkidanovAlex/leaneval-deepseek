import Mathlib
import Submission.OddOrder.Algebra.AlgInt
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.CharBridge

/-!
# Area BG: the odd-order parity step of Lemma 4.2

`Work.BG.l42HatOdd` is the character-theoretic parity input of Bender–Glauberman 1981,
Lemma 4.2 (`Work.GW2.C23.Lemma42Prop`): on a group `K` of **odd** order, a virtual
character `φ ∈ ℤ[Irr K]` which is congruent to an irreducible character `θ` modulo `2`
(`AlgIntModTwo (φ k) (θ k)` for every `k`) has, for every irreducible `θ'`, an integer
multiplicity `m = (φ, θ')` in `φ`, and `m` is odd exactly for `θ' = θ`.

Proof.  Put `ψ := φ - θ ∈ ℤ[Irr K]`; the congruence says `ψ ≡ 0 (mod 2)` pointwise.
The Fourier expansion `ψ = Σ_χ (ψ, χ) • χ` (Mathlib/OddOrder:
`sum_inner_irreducibleCharacter_smul`) turns this into the pointwise congruence
`Σ_χ (ψ, χ) · χ(k) ≡ 0 (mod 2)`, and Lemma 1.8
(`Work.GW2.C23.ModTwoIndepProp`, proved in `Submission/Work/BG/modTwoIndep.lean`) — which
only needs `|K|` odd and that the `χ` are distinct irreducibles — gives that every
Fourier coefficient `(ψ, χ)` is even.  In particular `m₀ := (ψ, θ')` is an even integer,
and `(φ, θ') = m₀ + (1 if θ' = θ else 0)` by the orthonormality
`(θ, θ') = δ_{θ,θ'}`.  Hence `(φ, θ')` is odd iff `θ' = θ`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- An integer which is congruent to `0` modulo `2` in the algebraic integers (its difference
from `0` is twice an algebraic integer) is even: `m/2` is a rational algebraic integer, hence
an integer. -/
theorem even_of_algIntModTwo_intCast_zero {m : ℤ} (h : AlgIntModTwo (m : ℂ) 0) : Even m := by
  obtain ⟨c, hc, hceq⟩ := h
  have h2 : (m : ℂ) = 2 * c := by linear_combination hceq
  have hq : c = ((((m : ℚ) / 2 : ℚ)) : ℂ) := by
    rw [show c = (m : ℂ) / 2 by rw [h2]; ring]
    push_cast
    ring
  have hqint : IsIntegral ℤ ((m : ℚ) / 2) := IsIntegral.ratCast_iff.mp (hq ▸ hc)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨y, ?_⟩
  have hy' : (((y : ℤ)) : ℚ) = (m : ℚ) / 2 := hy
  have h4 : m = 2 * y := by
    have h5 : (m : ℚ) = ((2 * y : ℤ) : ℚ) := by
      push_cast
      rw [hy']
      ring
    exact_mod_cast h5
  omega

open OddOrder.RepresentationTheory in
theorem l42HatOdd {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (hodd : Odd (Nat.card K))
    (φ : ClassFunction K ℂ) (hφ : φ ∈ ZIrr K)
    (θ : ClassFunction K ℂ) (hθ : IsIrreducibleCharacter θ)
    (hcong : ∀ k : K, AlgIntModTwo (φ k) (θ k))
    (θ' : ClassFunction K ℂ) (hθ' : IsIrreducibleCharacter θ') :
    ∃ m : ℤ, ClassFunction.inner φ θ' = m ∧ (Odd m ↔ θ' = θ) := by
  classical
  haveI : Finite K := Finite.of_fintype K
  haveI : Fintype (IrreducibleCharacter K) := Fintype.ofFinite _
  -- `ψ := φ - θ` is a virtual character congruent to `0` modulo `2`
  set ψ : ClassFunction K ℂ := φ - θ with hψdef
  have hψ : ψ ∈ ZIrr K := by
    rw [hψdef]
    exact Submodule.sub_mem (p := ZIrr K) hφ (IsIrreducibleCharacter.mem_ZIrr hθ)
  have hψmod : ∀ g : K, AlgIntModTwo (ψ g) 0 := by
    intro g
    have h1 : ψ g = φ g - θ g := by rw [hψdef]; rfl
    rw [h1]
    obtain ⟨c, hc, hceq⟩ := hcong g
    exact ⟨c, hc, by simpa using hceq⟩
  -- the Fourier expansion of `ψ` at a point
  have hFourier : ∀ g : K,
      (∑ χ : IrreducibleCharacter K,
        ClassFunction.inner ψ (χ : ClassFunction K ℂ) * (χ : ClassFunction K ℂ) g) = ψ g := by
    intro g
    have h := congrArg (fun f : ClassFunction K ℂ => f g)
      (sum_inner_irreducibleCharacter_smul ψ)
    simpa [ClassFunction.smul_apply] using h
  -- Lemma 1.8: every Fourier coefficient of `ψ` is even
  have hcoeff : ∀ χ : IrreducibleCharacter K,
      AlgIntModTwo (ClassFunction.inner ψ (χ : ClassFunction K ℂ)) 0 := by
    refine modTwoIndep (K := K) hodd
      (β := fun χ : IrreducibleCharacter K => (χ : ClassFunction K ℂ))
      (fun χ => χ.isIrreducible) ?_ (fun χ => ClassFunction.inner ψ (χ : ClassFunction K ℂ)) ?_ ?_
    · intro a b hab
      exact Subtype.ext hab
    · intro χ
      obtain ⟨n, hn⟩ := mem_ZIrr_inner_int χ hψ
      rw [hn]
      exact isIntegral_intCast n
    · intro g
      rw [hFourier g]
      exact hψmod g
  -- the multiplicity of `θ'` in `ψ`, an even integer
  obtain ⟨m₀, hm₀⟩ := mem_ZIrr_inner_int (⟨θ', hθ'⟩ : IrreducibleCharacter K) hψ
  have hEven : Even m₀ := by
    refine even_of_algIntModTwo_intCast_zero ?_
    rw [← hm₀]
    exact hcoeff ⟨θ', hθ'⟩
  -- orthonormality: `(θ, θ') = 1` iff `θ' = θ`
  have hinnerθ : ClassFunction.inner θ θ' = (if θ' = θ then (1 : ℂ) else 0) := by
    rw [show ClassFunction.inner θ θ' =
        ClassFunction.inner ((⟨θ, hθ⟩ : IrreducibleCharacter K) : ClassFunction K ℂ)
          ((⟨θ', hθ'⟩ : IrreducibleCharacter K) : ClassFunction K ℂ) from rfl]
    rw [irreducibleCharacter_inner_eq_ite]
    by_cases h : θ' = θ
    · rw [if_pos (Subtype.ext h.symm), if_pos h]
    · rw [if_neg (fun hh => h (Subtype.ext_iff.mp hh).symm), if_neg h]
  have hinnerφ : ClassFunction.inner φ θ' = (m₀ : ℂ) + (if θ' = θ then 1 else 0) := by
    have hsum : φ = ψ + θ := by
      rw [hψdef]
      exact (sub_add_cancel φ θ).symm
    rw [hsum, ClassFunction.inner_add_left, hm₀, hinnerθ]
  by_cases h : θ' = θ
  · refine ⟨m₀ + 1, ?_, ?_⟩
    · rw [hinnerφ, if_pos h]
      push_cast
      ring
    · constructor
      · intro _; exact h
      · intro _
        obtain ⟨j, hj⟩ := hEven
        exact ⟨j, by omega⟩
  · refine ⟨m₀, ?_, ?_⟩
    · rw [hinnerφ, if_neg h, add_zero]
    · constructor
      · intro hodd
        obtain ⟨j, hj⟩ := hEven
        obtain ⟨k, hk⟩ := hodd
        omega
      · intro hh; exact absurd hh h

end Work.BG
