import Mathlib
import Submission.Work.MotK.TwCensus.TrdegQuotientTwo
import Submission.Work.MotV.trdeg_fractionRing_mvPolynomial
import Submission.Work.MotK.TGen.CubTResidue

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.CensusBridge

set_option linter.style.haveILetI false

/-!
# Heights of primes of `K[X₀,X₁,X₂]` with two-dimensional residue field

If `p` is a prime of `K[X₀,X₁,X₂]` (for `K` a field) whose residue field
`Frac (K[X₀,X₁,X₂] ⧸ p)` has transcendence degree `2` over `K`, then `p` has height `1`.

This is the codimension-one case of the dimension formula
`height p = 3 - trdeg_K (Frac (R ⧸ p))` for the three-dimensional polynomial ring.

The proof is the one used for the residue field of the cubic link in
`Work.MotK.TGen.CubTResidue`: `trdeg ≥ 2` forces the quotient `A = R ⧸ p` to have two nested
primes `𝔭₁ < 𝔭₂` with `𝔭₁ ≠ ⊥` (Noether normalisation, `Work.MotK.TGen.two_primes_of_trdeg`).
Pulling them back along `R ↠ A` gives a chain `p < Q₁ < Q₂` in `R` of length two above `p`;
since `ringKrullDim R = 3`, we get `p.height + 2 ≤ 3`, i.e. `p.height ≤ 1`. Finally `p ≠ ⊥`
(the transcendence degree drops from `3` to `2` when passing from `R` to `R ⧸ p`), so
`p.height ≥ 1`.
-/

/-- A prime `p` of `K[X₀,X₁,X₂]` whose residue field has transcendence degree two over `K` has
height one. -/
theorem height_eq_one_of_trdeg_eq_two (K : Type) [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime]
    (htr : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ p)) = 2) :
    p.height = 1 := by
  classical
  -- The quotient is a finitely generated domain over `K`.
  haveI hdom : IsDomain (MvPolynomial (Fin 3) K ⧸ p) := Ideal.Quotient.isDomain p
  haveI hft : Algebra.FiniteType K (MvPolynomial (Fin 3) K ⧸ p) :=
    Algebra.FiniteType.quotient K p
  -- Two nested primes in the quotient `A = R ⧸ p`, the lower one non-zero.
  obtain ⟨𝔭₁, 𝔭₂, h𝔭₁, h𝔭₂, hlt, hne⟩ :=
    Work.MotK.TGen.two_primes_of_trdeg (A := MvPolynomial (Fin 3) K ⧸ p) (by rw [htr])
  haveI := h𝔭₁
  haveI := h𝔭₂
  -- Their pullbacks to `R`.
  have hQ₁prime : (𝔭₁.comap (Ideal.Quotient.mk p)).IsPrime := Ideal.comap_isPrime _ _
  have hQ₂prime : (𝔭₂.comap (Ideal.Quotient.mk p)).IsPrime := Ideal.comap_isPrime _ _
  haveI := hQ₁prime
  haveI := hQ₂prime
  have hPQ₁ : p ≤ 𝔭₁.comap (Ideal.Quotient.mk p) := by
    have h := Ideal.ker_le_comap (Ideal.Quotient.mk p) (K := 𝔭₁)
    rwa [Ideal.mk_ker] at h
  have hlt₁ : p < 𝔭₁.comap (Ideal.Quotient.mk p) := by
    refine lt_of_le_of_ne hPQ₁ fun heq => hne ?_
    have hm := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective 𝔭₁
    have hmap : Ideal.map (Ideal.Quotient.mk p) (Ideal.comap (Ideal.Quotient.mk p) 𝔭₁) = ⊥ := by
      rw [heq.symm, Ideal.map_quotient_self]
    exact hm.symm.trans hmap
  have hlt₂ : 𝔭₁.comap (Ideal.Quotient.mk p) < 𝔭₂.comap (Ideal.Quotient.mk p) := by
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => ?_
    have hA := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective 𝔭₁
    have hB := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective 𝔭₂
    have hAB : 𝔭₁ = 𝔭₂ := by rw [← hA, ← hB, heq]
    exact absurd hAB (ne_of_lt hlt)
  -- `ringKrullDim R = 3`, so a chain of length two above `p` gives `p.height ≤ 1`.
  have hdim : ringKrullDim (MvPolynomial (Fin 3) K) = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    norm_num
  have ha1 : p.height + 1 ≤ (𝔭₁.comap (Ideal.Quotient.mk p)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt₁
  have hb1 : (𝔭₁.comap (Ideal.Quotient.mk p)).height + 1
      ≤ (𝔭₂.comap (Ideal.Quotient.mk p)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt₂
  have hc2 : (𝔭₂.comap (Ideal.Quotient.mk p)).height ≤ 3 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔭₂.comap (Ideal.Quotient.mk p))
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hle : p.height ≤ 1 := by
    have key : p.height + (1 + 1) ≤ 1 + (1 + 1) := by
      calc p.height + (1 + 1) = (p.height + 1) + 1 := by rw [add_assoc]
        _ ≤ (𝔭₁.comap (Ideal.Quotient.mk p)).height + 1 := add_le_add ha1 le_rfl
        _ ≤ (𝔭₂.comap (Ideal.Quotient.mk p)).height := hb1
        _ ≤ 3 := hc2
        _ = 1 + (1 + 1) := by norm_num
    exact (ENat.add_le_add_iff_right (by norm_num : ((1 : ℕ∞) + 1) ≠ ⊤)).mp key
  -- `p ≠ ⊥`, since otherwise the residue field would have transcendence degree `3`.
  have hne_bot : p ≠ ⊥ := by
    intro hbot
    have hEq : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ p))
        = Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K)) := by
      rw [hbot]
      exact AlgEquiv.trdeg_eq (IsFractionRing.algEquivOfAlgEquiv
        (AlgEquiv.quotientBot K (MvPolynomial (Fin 3) K)))
    rw [htr, Work.MotV.trdeg_fractionRing_mvPolynomial K 3, Cardinal.mk_fin] at hEq
    norm_num at hEq
  have hge : (1 : ℕ∞) ≤ p.height := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact hne_bot (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  exact le_antisymm hle hge

end Work.MotK.CensusBridge
