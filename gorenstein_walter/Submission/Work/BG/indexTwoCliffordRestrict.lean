import Mathlib
import Submission.Work.BG.indexTwoMackey
import Submission.Work.BG.indexTwoInduceIrreducible
import Submission.Work.BG.indexTwoEveryIrr
import Submission.Work.BG.indexTwoInduceNormTwo
import Submission.Work.BG.indexTwoInduceEqIff
import Submission.OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Parseval norm bound.** For a virtual character `φ ∈ ℤ[Irr G]` whose squared norm is `2`,
the Fourier coefficient at any irreducible `χ` — here given as a natural number `k` — is at most
`1`.

Indeed, writing `φ = ∑_{a ∈ s} (c a) • a` with integer coefficients `c` on irreducible `a`
(`mem_ZIrr_repr`), Parseval gives `⟨φ, φ⟩ = ∑_a (c a)^2 = 2`.  The Fourier coefficient at `χ` is
`c χ = k`, and `(c χ)^2 ≤ ∑_a (c a)^2 = 2`, so `k ≤ 1` (as `k ≥ 0`). -/
theorem le_one_of_inner_self_eq_two {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (χ : IrreducibleCharacter G) (k : ℕ)
    (hk : ClassFunction.inner φ (χ : ClassFunction G ℂ) = (k : ℂ))
    (hnorm : ClassFunction.inner φ φ = 2) : k ≤ 1 := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hcoeff := inner_eq_coeff_of_repr χ hsupp
  have hk' : ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) (χ : ClassFunction G ℂ)
      = (k : ℂ) := by
    rw [← hrepr]; exact hk
  have hcχ : (c (χ : ClassFunction G ℂ) : ℂ) = (k : ℂ) := by rw [← hcoeff, hk']
  have hcχi : c (χ : ClassFunction G ℂ) = (k : ℤ) := by exact_mod_cast hcχ
  have hsumC : (∑ a ∈ c.support, (c a : ℂ) ^ 2) = 2 := by rw [← hsq, hnorm]
  have hsumZ : (∑ a ∈ c.support, (c a) ^ 2) = 2 := by
    have h : ((∑ a ∈ c.support, (c a) ^ 2 : ℤ) : ℂ) = 2 := by
      rw [← hsumC]; push_cast; rfl
    exact_mod_cast h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · omega
  · have hmem : (χ : ClassFunction G ℂ) ∈ c.support := by
      rw [Finsupp.mem_support_iff, hcχi]
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hkpos)
    have hle : (c (χ : ClassFunction G ℂ)) ^ 2 ≤ ∑ a ∈ c.support, (c a) ^ 2 :=
      Finset.single_le_sum (fun a _ => sq_nonneg (c a)) hmem
    rw [hsumZ, hcχi] at hle
    have hnot : ¬ (2 ≤ k) := by
      intro h2
      have hk2 : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast h2
      nlinarith
    omega

set_option linter.style.haveILetI false in
open OddOrder.RepresentationTheory in
theorem indexTwoCliffordRestrict {K : Type} [Group K] [Finite K] [Fintype K]
    {H : Subgroup K} [H.Normal] (hind : H.index = 2) (s : K) (hs : s ∉ H)
    [Fintype ↥H] [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    (τ : IrreducibleCharacter ↥H) (χ : IrreducibleCharacter K)
    (hover : IrreducibleCharacter.LiesOver H χ τ) :
    ((ClassFunction.conjBy (G := K) (H := H) s (τ : ClassFunction ↥H ℂ) = (τ : ClassFunction ↥H ℂ)) →
        ClassFunction.restrict H (χ : ClassFunction K ℂ) = (τ : ClassFunction ↥H ℂ)) ∧
    ((ClassFunction.conjBy (G := K) (H := H) s (τ : ClassFunction ↥H ℂ) ≠ (τ : ClassFunction ↥H ℂ)) →
        ClassFunction.restrict H (χ : ClassFunction K ℂ)
          = (τ : ClassFunction ↥H ℂ)
            + ClassFunction.conjBy (G := K) (H := H) s (τ : ClassFunction ↥H ℂ)) := by
  classical
  -- `|Irr ↥H|` is finite, needed by the Clifford invariant-constituent theorem.
  haveI : Finite (IrreducibleCharacter ↥H) := finite_irreducibleCharacter (G := ↥H)
  constructor
  · -- **Case A: `τ` is `s`-invariant.**  Then `τ` is `K`-invariant, `Res_H χ = e • τ` with
    -- `e = ⟨Res χ, τ⟩ ∈ ℕ`, and `e² ≤ ⟨Ind_H^K τ, Ind_H^K τ⟩ = 2` forces `e = 1`.
    intro hinv
    have hinv_all : ∀ g : K, IrreducibleCharacter.conjBy g τ = τ := by
      intro g
      by_cases hg : g ∈ H
      · exact IrreducibleCharacter.ext (ClassFunction.conjBy_eq_self_of_mem hg _)
      · have hs' : s⁻¹ ∉ H := fun h => hs (by simpa using H.inv_mem h)
        have hg' : s⁻¹ * g ∈ H := by
          rw [Subgroup.mul_mem_iff_of_index_two hind]
          exact iff_of_false (fun h => hs' h) (fun h => hg h)
        have hconjs : IrreducibleCharacter.conjBy s τ = τ := IrreducibleCharacter.ext hinv
        have hgEq : g = s * (s⁻¹ * g) := by group
        rw [hgEq, IrreducibleCharacter.conjBy_mul, hconjs]
        exact IrreducibleCharacter.ext (ClassFunction.conjBy_eq_self_of_mem hg' _)
    have hres :=
      restrict_eq_restrictionMultiplicity_smul_of_invariant (G := K) (H := H) χ τ hover hinv_all
    obtain ⟨k, hk⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := H) χ τ
    -- `k ≥ 1` because `τ` occurs in `Res_H χ` with nonzero multiplicity (`hover`).
    have hkpos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        rw [h, Nat.cast_zero] at hk
        exact hover hk
      · exact h
    -- Frobenius reciprocity identifies `⟨Ind_H^K τ, χ⟩` with the restriction multiplicity `k`.
    have hinner : ClassFunction.inner (ClassFunction.induce H (τ : ClassFunction ↥H ℂ))
        (χ : ClassFunction K ℂ) = (k : ℂ) := by
      rw [ClassFunction.inner_induce_eq_inner_restrict]
      rw [inner_conj_symm (ClassFunction.restrict H (χ : ClassFunction K ℂ))
        (τ : ClassFunction ↥H ℂ)]
      rw [← ClassFunction.restrictionMultiplicity_def, hk, star_natCast]
    -- The index-two norm of the induced character is `2`.
    have hnorm : ClassFunction.inner (ClassFunction.induce H (τ : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (τ : ClassFunction ↥H ℂ)) = 2 :=
      indexTwoInduceNormTwo (H := K) H hind s hs τ hinv
    have hZIrr : ClassFunction.induce H (τ : ClassFunction ↥H ℂ) ∈ ZIrr K :=
      ClassFunction.induce_mem_ZIrr H τ.isIrreducible.mem_ZIrr
    have hk1 : k ≤ 1 := le_one_of_inner_self_eq_two hZIrr χ k hinner hnorm
    have hkEq : k = 1 := le_antisymm hk1 hkpos
    rw [hres, hk, hkEq, Nat.cast_one, one_smul]
  · -- **Case B: `τ` is not `s`-invariant.**  Then `Ind_H^K τ` is irreducible, so `χ = Ind_H^K τ`,
    -- and the index-two Mackey formula computes `Res_H χ = τ + τ^s`.
    intro hne
    have hind_irr : IsIrreducibleCharacter (ClassFunction.induce H (τ : ClassFunction ↥H ℂ)) :=
      indexTwoInduceIrreducible (H := K) H hind s hs τ hne
    have hcoe : (χ : ClassFunction K ℂ) = ClassFunction.induce H (τ : ClassFunction ↥H ℂ) :=
      coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce χ τ hind_irr hover
    rw [hcoe, indexTwoMackey (H := K) H hind s hs (τ : ClassFunction ↥H ℂ)]

end Work.BG
