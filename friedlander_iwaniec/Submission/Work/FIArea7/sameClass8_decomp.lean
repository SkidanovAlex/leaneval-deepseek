import Mathlib
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.GaussUnitClass
import Submission.Work.FIArea7.chiOf_eq_unitInd_mul
import Submission.Work.FIArea7.sum_addChar_mul_star

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The class map modulo eight and the character expansion of its indicator

We realise the (5.7) class condition `z ≡ z₀ (mod 8)` as a finite character sum over the dual of
`G = (ℤ[i]/8)^*`.  The characters are the `AddChar (Additive (GaussUnit 8)) ℂ` of the workspace's
coordinate model of the Gaussian unit group, and the extension by zero off the units is the
workspace's `chiOf 8`.  The only arithmetic input is that a primary Gaussian integer is odd, hence a
unit modulo eight. -/

/-- An enumeration of the dual of `G = (ℤ[i]/8)^*` by `Fin N`, `N` its cardinality.  The
characters `a_i` of the statement are indexed by this equivalence. -/
def cls8ChrIdx :
    Fin (Fintype.card (AddChar (Additive (GaussUnit 8)) ℂ)) ≃
      AddChar (Additive (GaussUnit 8)) ℂ :=
  (Fintype.equivFin (AddChar (Additive (GaussUnit 8)) ℂ)).symm

/-- `SameClass8` is exactly the equality of the reductions modulo eight. -/
lemma sameClass8_iff_phiCoord (z z0 : GaussianInt) :
    Work.FITop4.SameClass8 z z0 ↔ phiCoord 8 z = phiCoord 8 z0 :=
  Iff.rfl

/-- A primary Gaussian integer is odd, hence coprime to eight. -/
lemma isPrimary_coprime_eight {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Nat.Coprime (Work.FIPlan.gnorm z) 8 := by
  obtain ⟨hodd, heven, -⟩ := hz
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by
    rw [Zsqrtd.norm_def]; ring
  have hoddg : Odd (Work.FIPlan.gnorm z) := by
    show Odd (z.norm.natAbs)
    rw [hnorm]
    refine Int.natAbs_odd.mpr ?_
    rw [ha, hb]
    exact ⟨2 * a ^ 2 + 2 * a + 2 * b ^ 2, by ring⟩
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
  exact (Nat.coprime_pow_right_iff (by norm_num) (Work.FIPlan.gnorm z) 2).mpr
    (Nat.coprime_two_right.mpr hoddg)

/-- The class map `unitClassD 8` agrees, on the units, with the reduction `phiCoord 8`. -/
lemma unitClassD_fst_of_coprime (z : GaussianInt) (h : Nat.Coprime (Work.FIPlan.gnorm z) 8) :
    (unitClassD 8 z).1 = phiCoord 8 z := by
  rw [unitClassD_eq 8 z h, gaussUnitOf_val]
  rfl

/-- On the units, two classes agree iff their reductions modulo eight agree. -/
lemma unitClassD_eq_iff (z z0 : GaussianInt)
    (hz : Nat.Coprime (Work.FIPlan.gnorm z) 8) (hz0 : Nat.Coprime (Work.FIPlan.gnorm z0) 8) :
    unitClassD 8 z = unitClassD 8 z0 ↔ phiCoord 8 z = phiCoord 8 z0 := by
  rw [unitClassD_eq 8 z hz, unitClassD_eq 8 z0 hz0, gaussUnitOf_eq_iff 8 z z0 hz hz0]
  rfl

/-- Coprimality to eight transfers along a fixed class modulo eight. -/
lemma coprime_eight_of_sameClass8 {z z0 : GaussianInt}
    (hz : Nat.Coprime (Work.FIPlan.gnorm z) 8) (h : Work.FITop4.SameClass8 z z0) :
    Nat.Coprime (Work.FIPlan.gnorm z0) 8 := by
  have h0 : IsUnit (gaussNorm (phiCoord 8 z0)) := by
    rw [← (sameClass8_iff_phiCoord z z0).mp h, gaussNorm_phiCoord]
    exact (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z) 8).mpr hz
  rw [gaussNorm_phiCoord] at h0
  exact (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z0) 8).mp h0

/-- `chiOf` depends on `z` only through its reduction modulo eight. -/
lemma chiOf_phiCoord_congr (χ : AddChar (Additive (GaussUnit 8)) ℂ) {z w : GaussianInt}
    (hp : phiCoord 8 z = phiCoord 8 w) : chiOf 8 χ z = chiOf 8 χ w := by
  by_cases h : IsUnit (gaussNorm (phiCoord 8 w))
  · have hz : IsUnit (gaussNorm (phiCoord 8 z)) := by rwa [hp]
    simp only [chiOf]
    rw [dif_pos hz, dif_pos h]
    exact congrArg (fun u : GaussUnit 8 => χ (Additive.ofMul u)) (Subtype.ext hp)
  · have hz : ¬ IsUnit (gaussNorm (phiCoord 8 z)) := by rwa [hp]
    simp only [chiOf]
    rw [dif_neg hz, dif_neg h]

/-- **The (5.7) indicator as a character sum.**  For `z` coprime to eight, the average of
`χ(π z)·conj(χ(π z₀))` over the dual of `(ℤ[i]/8)^*` is the indicator of `z ≡ z₀ (mod 8)`. -/
lemma sum_star_chiOf_mul_eight (z z0 : GaussianInt)
    (hz : Nat.Coprime (Work.FIPlan.gnorm z) 8) :
    (∑ χ : AddChar (Additive (GaussUnit 8)) ℂ, star (chiOf 8 χ z0) * chiOf 8 χ z)
      = if Work.FITop4.SameClass8 z z0 then (Fintype.card (GaussUnit 8) : ℂ) else 0 := by
  classical
  by_cases hz0 : Nat.Coprime (Work.FIPlan.gnorm z0) 8
  · have hcomm : ∀ χ : AddChar (Additive (GaussUnit 8)) ℂ,
        star (chiOf 8 χ z0) * chiOf 8 χ z
          = χ (Additive.ofMul (unitClassD 8 z)) *
            star (χ (Additive.ofMul (unitClassD 8 z0))) := by
      intro χ
      rw [chiOf_eq_unitInd_mul 8 χ z0, chiOf_eq_unitInd_mul 8 χ z, unitInd, unitInd,
        if_pos hz0, if_pos hz, one_mul, one_mul, mul_comm]
    rw [Finset.sum_congr rfl (fun χ _ => hcomm χ), sum_addChar_mul_star]
    have hcond : (unitClassD 8 z = unitClassD 8 z0) ↔ Work.FITop4.SameClass8 z z0 :=
      (unitClassD_eq_iff z z0 hz hz0).trans (sameClass8_iff_phiCoord z z0).symm
    by_cases h : Work.FITop4.SameClass8 z z0
    · rw [if_pos (hcond.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  · have hns : ¬ Work.FITop4.SameClass8 z z0 :=
      fun h => hz0 (coprime_eight_of_sameClass8 hz h)
    have hχ0 : ∀ χ : AddChar (Additive (GaussUnit 8)) ℂ, chiOf 8 χ z0 = 0 :=
      fun χ => chiOf_eq_zero_of_not_coprime χ hz0
    have hzsum : (∑ χ : AddChar (Additive (GaussUnit 8)) ℂ,
        star (chiOf 8 χ z0) * chiOf 8 χ z) = 0 := by
      simp only [hχ0, star_zero, zero_mul, Finset.sum_const_zero]
    rw [hzsum, if_neg hns]

/-- The same sum, indexed by `Fin N` through the enumeration `cls8ChrIdx`. -/
lemma sum_cls8ChrIdx (z z0 : GaussianInt) :
    (∑ i : Fin (Fintype.card (AddChar (Additive (GaussUnit 8)) ℂ)),
        (1 / (Fintype.card (GaussUnit 8) : ℂ)) * star (chiOf 8 (cls8ChrIdx i) z0)
          * chiOf 8 (cls8ChrIdx i) z)
      = (1 / (Fintype.card (GaussUnit 8) : ℂ)) *
        ∑ χ : AddChar (Additive (GaussUnit 8)) ℂ, star (chiOf 8 χ z0) * chiOf 8 χ z := by
  rw [show (∑ i : Fin (Fintype.card (AddChar (Additive (GaussUnit 8)) ℂ)),
        (1 / (Fintype.card (GaussUnit 8) : ℂ)) * star (chiOf 8 (cls8ChrIdx i) z0)
          * chiOf 8 (cls8ChrIdx i) z)
      = ∑ i : Fin (Fintype.card (AddChar (Additive (GaussUnit 8)) ℂ)),
        (1 / (Fintype.card (GaussUnit 8) : ℂ)) * (star (chiOf 8 (cls8ChrIdx i) z0)
          * chiOf 8 (cls8ChrIdx i) z) from
        Finset.sum_congr rfl (fun i _ => by rw [mul_assoc])]
  rw [Finset.mul_sum]
  exact Equiv.sum_comp cls8ChrIdx (fun χ : AddChar (Additive (GaussUnit 8)) ℂ =>
    (1 / (Fintype.card (GaussUnit 8) : ℂ)) * (star (chiOf 8 χ z0) * chiOf 8 χ z))

/-- **The (5.7) class condition is a character condition** (*FI* p. 1009: "the congruence (5.7) can
be detected by characters to modulus eight so we can relax it by changing χ in ψ").

For primary `z` the class `z mod 8` runs over the subgroup `H = 1 + 2(1+i)ℤ[i]` of `(ℤ[i]/8)^*`
(order `8`), so the indicator of a fixed class is a finite combination of characters of `H`, and
each such character — extended by `0` off the units — is a bounded, `8`-periodic, *multiplicative*
function of `z` (finite-abelian-group Fourier inversion on `G = (ℤ[i]/8)^*`, `|G| = 32`,
`G`-characters extended by zero off the units, `c z0 i = (1/32)·χ_i(z0)^{-1}`):

    `1` if `SameClass8 z z0`, else `0`   =   `Σ_i (c z0 i)·(a_i z)`      for every *primary* `z`.

(The statement is split into the two implications so that no `Decidable` instance is needed.)

This is what lets the §17 bridge move the (5.7) restriction out of the support of `β` and into the
character `χ` of the deep input (`radBeta`/`SChiRad` of `Prop172Classical` carry no class
restriction; NOTES.md §61.5 (b)).  The `8`-periodicity is what makes the product with the character
of modulus `Q = 4be` a character of modulus `lcm(Q,8) ≤ 2Q`, i.e. harmless in the
Proposition-17.2 threshold `d(|m|+1) ≤ N^{δ₁}`. -/
theorem sameClass8_decomp :
    ∃ (N : ℕ) (a : Fin N → GaussianInt → ℂ) (c : GaussianInt → Fin N → ℂ),
      (∀ i, ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → a i (z1 * z2) = a i z1 * a i z2) ∧
      (∀ i, ∀ z : GaussianInt, ‖a i z‖ ≤ 1) ∧
      (∀ i, ∀ z : GaussianInt, a i (z + 8) = a i z) ∧
      (∀ i, ∀ z : GaussianInt, a i (⟨z.re, z.im + 8⟩ : GaussianInt) = a i z) ∧
      (∀ i, ∀ z0 : GaussianInt, ‖c z0 i‖ ≤ 1) ∧
      (∀ z z0 : GaussianInt, Work.FIPlan.IsPrimary z → Work.FITop4.SameClass8 z z0 →
        (1 : ℂ) = ∑ i, c z0 i * a i z) ∧
      (∀ z z0 : GaussianInt, Work.FIPlan.IsPrimary z → ¬ Work.FITop4.SameClass8 z z0 →
        (0 : ℂ) = ∑ i, c z0 i * a i z) := by
  classical
  haveI : Nonempty (GaussUnit 8) := ⟨1⟩
  have hcard_ne : (Fintype.card (GaussUnit 8) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard_ge : (1 : ℝ) ≤ (Fintype.card (GaussUnit 8) : ℝ) := by
    exact_mod_cast (show (1 : ℕ) ≤ Fintype.card (GaussUnit 8) from Fintype.card_pos)
  refine ⟨Fintype.card (AddChar (Additive (GaussUnit 8)) ℂ),
    fun i => chiOf 8 (cls8ChrIdx i),
    fun z0 i => (1 / (Fintype.card (GaussUnit 8) : ℂ)) * star (chiOf 8 (cls8ChrIdx i) z0),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i z1 z2 _
    exact chiOf_mul (cls8ChrIdx i) z1 z2
  · intro i z
    exact chiOf_norm_le (cls8ChrIdx i) z
  · intro i z
    exact chiOf_phiCoord_congr (cls8ChrIdx i) (by ext <;> simp [phiCoord] <;> decide)
  · intro i z
    exact chiOf_phiCoord_congr (cls8ChrIdx i) (by ext <;> simp [phiCoord] <;> decide)
  · intro i z0
    have h1 : ‖(1 / (Fintype.card (GaussUnit 8) : ℂ))‖ ≤ 1 := by
      rw [one_div, norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ hcard_ge
    calc ‖(1 / (Fintype.card (GaussUnit 8) : ℂ)) * star (chiOf 8 (cls8ChrIdx i) z0)‖
        ≤ ‖(1 / (Fintype.card (GaussUnit 8) : ℂ))‖ *
            ‖star (chiOf 8 (cls8ChrIdx i) z0)‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by
          refine mul_le_mul h1 ?_ (norm_nonneg _) (by norm_num)
          simpa using chiOf_norm_le (cls8ChrIdx i) z0
      _ = 1 := one_mul 1
  · intro z z0 hz hSame
    rw [sum_cls8ChrIdx z z0, sum_star_chiOf_mul_eight z z0 (isPrimary_coprime_eight hz),
      if_pos hSame, one_div, inv_mul_cancel₀ hcard_ne]
  · intro z z0 hz hNot
    rw [sum_cls8ChrIdx z z0, sum_star_chiOf_mul_eight z z0 (isPrimary_coprime_eight hz),
      if_neg hNot, mul_zero]

end

end Work.FIArea7
