import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum

open scoped BigOperators
open Finset Classical

/-!
# The character reduction for the Bombieri--Vinogradov theorem

This module sets up the first step of the classical proof of the
Bombieri--Vinogradov theorem (following R. C. Vaughan, *The Bombieri-Vinogradov
theorem*, §1): the reduction of the *residue-class* discrepancy of `ψ`

    ψ(y; q, a) − y/φ(q)

to a sum over Dirichlet characters,

    Σ_{q ≤ Q} max_{y ≤ x, (a,q)=1} |ψ(y; q, a) − y/φ(q)|
        ≤ Σ_{q ≤ Q} (1/φ(q)) Σ_{χ mod q} sup_{y ≤ x} |ψ(y, χ) − δ(χ) y|,

where `ψ(y,χ) = Σ_{n ≤ y} Λ(n) χ(n)` and `δ(χ) = 1` for the principal character
and `0` otherwise.

The character expansion of a residue-class sum is the commons lemma
`Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum`.
-/

namespace Submission.BV

noncomputable section

/-- `ψ(y,χ) = Σ_{n ≤ y} Λ(n) χ(n)`, the von Mangoldt character sum. -/
def psiChar {q : ℕ} (y : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)

/-- `ψ(y; q, a) = Σ_{n ≤ y, n ≡ a (mod q)} Λ(n)`, the von Mangoldt sum in a
residue class. -/
def psiAP (y q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (y + 1)).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n

/-- The principal-character correction `δ(χ) y`. -/
def deltaChar {q : ℕ} (y : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  if χ = 1 then (y : ℂ) else 0

/-- The character expansion of the residue-class sum, in the form used below. -/
theorem psiAP_char_expansion {q : ℕ} [NeZero q] (y a : ℕ) (ha : a.Coprime q) :
    ((psiAP y q a : ℝ) : ℂ) =
      ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * psiChar y χ := by
  have h := Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum q y a ha
  have hL : (∑ n ∈ (Finset.range (y + 1)).filter (fun n => n % q = a % q),
        (ArithmeticFunction.vonMangoldt n : ℂ)) =
      ((psiAP y q a : ℝ) : ℂ) := by
    simp only [psiAP, Complex.ofReal_sum]
  rw [hL] at h
  simp only [psiChar]
  rw [← h]

/-- The inverse of a natural number coprime to `q`, viewed in `ZMod q`, is a unit. -/
lemma isUnit_inv_natCast {q : ℕ} {a : ℕ} (ha : a.Coprime q) :
    IsUnit (((a : ZMod q))⁻¹) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
  refine ⟨u⁻¹, ?_⟩
  refine (ZMod.inv_eq_of_mul_eq_one q (a : ZMod q) ((u⁻¹ : (ZMod q)ˣ) : ZMod q) ?_).symm
  rw [← hu]
  simp

/-- `Σ_χ χ(a)⁻¹ δ(χ) y = y`: the principal character contributes the main term. -/
lemma sum_char_mul_deltaChar {q : ℕ} [NeZero q] (y a : ℕ) (ha : a.Coprime q) :
    ∑ χ : DirichletCharacter ℂ q, χ (((a : ZMod q))⁻¹) * deltaChar y χ = (y : ℂ) := by
  classical
  rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
  · rw [deltaChar, if_pos rfl, MulChar.one_apply (isUnit_inv_natCast ha), one_mul]
  · intro χ _ hχ
    rw [deltaChar, if_neg hχ, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The exact character identity behind the reduction:
`ψ(y;q,a) − y/φ(q) = φ(q)⁻¹ Σ_χ χ(a)⁻¹ (ψ(y,χ) − δ(χ) y)`. -/
lemma psiAP_sub_main_eq {q : ℕ} [NeZero q] (y a : ℕ) (ha : a.Coprime q) :
    ((psiAP y q a : ℝ) : ℂ) - (y : ℂ) / ((q.totient : ℕ) : ℂ) =
      (((q.totient : ℕ) : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * (psiChar y χ - deltaChar y χ) := by
  classical
  rw [psiAP_char_expansion (q := q) y a ha]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, sum_char_mul_deltaChar y a ha, div_eq_mul_inv, mul_sub]
  ring

/-- The pointwise discrepancy bound in terms of the character sums. -/
lemma abs_psiAP_sub_main_le {q : ℕ} [NeZero q] (y a : ℕ) (ha : a.Coprime q) :
    |psiAP y q a - (y : ℝ) / ((q.totient : ℕ) : ℝ)| ≤
      (((q.totient : ℕ) : ℝ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖psiChar y χ - deltaChar y χ‖ := by
  classical
  have key := psiAP_sub_main_eq (q := q) y a ha
  have hcast : Complex.ofReal (psiAP y q a - (y : ℝ) / ((q.totient : ℕ) : ℝ)) =
      ((psiAP y q a : ℝ) : ℂ) - (y : ℂ) / ((q.totient : ℕ) : ℂ) := by
    push_cast
    ring
  have hbound : ‖((psiAP y q a : ℝ) : ℂ) - (y : ℂ) / ((q.totient : ℕ) : ℂ)‖ ≤
      (((q.totient : ℕ) : ℝ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖psiChar y χ - deltaChar y χ‖ := by
    rw [key, norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (psiChar y χ - deltaChar y χ)‖
        ≤ ∑ χ : DirichletCharacter ℂ q,
            ‖χ ((a : ZMod q)⁻¹) * (psiChar y χ - deltaChar y χ)‖ := norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖psiChar y χ - deltaChar y χ‖ := by
          refine Finset.sum_le_sum (fun χ _ => ?_)
          rw [norm_mul]
          calc ‖χ ((a : ZMod q)⁻¹)‖ * ‖psiChar y χ - deltaChar y χ‖
              ≤ 1 * ‖psiChar y χ - deltaChar y χ‖ :=
                mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
            _ = ‖psiChar y χ - deltaChar y χ‖ := one_mul _
  calc |psiAP y q a - (y : ℝ) / ((q.totient : ℕ) : ℝ)|
      = ‖Complex.ofReal (psiAP y q a - (y : ℝ) / ((q.totient : ℕ) : ℝ))‖ :=
        (RCLike.norm_ofReal _).symm
    _ = ‖((psiAP y q a : ℝ) : ℂ) - (y : ℂ) / ((q.totient : ℕ) : ℂ)‖ := by rw [hcast]
    _ ≤ _ := hbound

/-- The maximal discrepancy of `ψ` in a primitive residue class, over all
classes `a` coprime to `q` and all truncation points `y ≤ x`. -/
noncomputable def discSupPsi (x q : ℕ) : ℝ :=
  sSup ((fun pa : ℕ × ℕ =>
      |psiAP pa.1 q pa.2 - (pa.1 : ℝ) / ((q.totient : ℕ) : ℝ)|)
    '' (Set.Icc 1 x ×ˢ {a : ℕ | a.Coprime q}))

/-- The maximal character sum `sup_{y ≤ x} ‖ψ(y,χ) − δ(χ) y‖`. -/
noncomputable def charSup {q : ℕ} (x : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup ((fun y : ℕ => ‖psiChar y χ - deltaChar y χ‖) '' Set.Icc 1 x)

lemma charSup_nonneg {q : ℕ} (x : ℕ) (χ : DirichletCharacter ℂ q) : 0 ≤ charSup x χ :=
  Real.sSup_nonneg (s := (fun y : ℕ => ‖psiChar y χ - deltaChar y χ‖) '' Set.Icc 1 x)
    (fun _ hv => by
      rcases hv with ⟨y, -, rfl⟩
      exact norm_nonneg _)

/-- **The character reduction.**  The maximal discrepancy of `ψ` over primitive
residue classes is bounded by the totient-weighted average of the maximal
character sums:
`max_{y ≤ x, (a,q)=1} |ψ(y;q,a) − y/φ(q)| ≤ φ(q)⁻¹ Σ_{χ mod q} sup_{y ≤ x} |ψ(y,χ) − δ(χ) y|`. -/
lemma discSupPsi_le_sum_charSup {q : ℕ} [NeZero q] (x : ℕ) :
    discSupPsi x q ≤ ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      charSup x χ := by
  classical
  have hφpos : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  refine Real.sSup_le (fun v hv => ?_)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => charSup_nonneg x χ)))
  rcases hv with ⟨pa, hpa, rfl⟩
  obtain ⟨⟨h1, h2⟩, hcop⟩ := hpa
  refine le_trans (abs_psiAP_sub_main_le pa.1 pa.2 hcop) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hφpos))
  refine Finset.sum_le_sum (fun χ _ => ?_)
  exact le_csSup ((Set.finite_Icc 1 x).image _ |>.bddAbove) ⟨pa.1, ⟨h1, h2⟩, rfl⟩

/-- The same reduction summed over the moduli `q ≤ Q`. -/
lemma sum_discSupPsi_le {Q : ℕ} {x : ℕ} :
    ∑ q ∈ Finset.Icc 1 Q, discSupPsi x q ≤
      ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        charSup x χ := by
  refine Finset.sum_le_sum (fun q hq => ?_)
  haveI : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact discSupPsi_le_sum_charSup x

/-- For a non-principal character the correction `δ(χ) y` vanishes. -/
lemma deltaChar_eq_zero {q : ℕ} (y : ℕ) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    deltaChar y χ = 0 := by
  rw [deltaChar, if_neg hχ]

/-- For a non-principal character, `charSup` is the supremum of the plain character sums. -/
lemma charSup_eq_of_ne_one {q : ℕ} (x : ℕ) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    charSup x χ = sSup ((fun y : ℕ => ‖psiChar y χ‖) '' Set.Icc 1 x) := by
  refine congrArg sSup (Set.image_congr (fun y _ => ?_))
  rw [deltaChar_eq_zero y hχ, sub_zero]

end
end Submission.BV
