import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup
import Submission.Commons.NumberTheory.BombieriVinogradov.dyadic_bilinear_char_large_sieve

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The dyadic maximal bilinear character large sieve

Combining `Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup`
with the dyadic conversion `Commons.NumberTheory.BombieriVinogradov.totient_inv_sum_le`,
we obtain the version used in the proof of `bRemCorrLevelOfDistribution`: over a dyadic block
`R < r ≤ 2R` of *conductors*, with the weight `1/φ(r)`,

`Σ_{R<r≤2R} (1/φ r) Σ*_{ψ} sSup_y ‖Σ_{m≤U}Σ_{n≤V} [mn≤y] a_m b_n ψ(mn)‖`

`  ≤ c R⁻¹ √((U + (2R)²) Σ‖a‖²) √((V + (2R)²) Σ‖b‖²) log(2UV+2)`.

The crucial feature is the factor `R⁻¹`: it is what beats the diagonal, and it is available
because the large sieve is stated with the `q/φ(q)` weight (converted by
`totient_inv_sum_le`).
-/

/-- The bilinear form (with hyperbola cut) that the large sieve applies to. -/
noncomputable def bilinForm (U V y : ℕ) (a b : ℕ → ℂ) (r : ℕ)
    (ψ : DirichletCharacter ℂ r) : ℂ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ n ∈ Finset.Icc 1 V,
    (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * ψ (((m * n : ℕ)) : ZMod r)

theorem bilinForm_eq (U V y : ℕ) (a b : ℕ → ℂ) (r : ℕ) (ψ : DirichletCharacter ℂ r) :
    bilinForm U V y a b r ψ
      = ∑ m ∈ Finset.Icc 1 U, ∑ n ∈ Finset.Icc 1 V,
          (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * ψ (((m * n : ℕ)) : ZMod r) := rfl

/-- **The dyadic maximal bilinear character large sieve.** -/
theorem BLodLargeSieve :
    ∃ c : ℝ, 0 < c ∧
      ∀ (U V R : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hR : 1 ≤ R) (a b : ℕ → ℂ),
        (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
            (∑ ψ ∈ (@Finset.filter (DirichletCharacter ℂ r) (fun ψ => ψ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
              sSup ((fun y : ℕ => ‖bilinForm U V y a b r ψ‖) '' Set.Icc 1 (U * V))))
          ≤ c * (R : ℝ)⁻¹ *
              Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
                * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2) *
              Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
                * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2) *
              Real.log (2 * (U : ℝ) * (V : ℝ) + 2) := by
  obtain ⟨c, hcpos, hc⟩ :=
    Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup
  refine ⟨c, hcpos, ?_⟩
  intro U V R hU hV hR a b
  classical
  set Z : ℕ → ℝ := fun r =>
    (∑ ψ ∈ (@Finset.filter (DirichletCharacter ℂ r) (fun ψ => ψ.IsPrimitive)
        (Classical.decPred _) Finset.univ),
      sSup ((fun y : ℕ => ‖bilinForm U V y a b r ψ‖) '' Set.Icc 1 (U * V))) with hZ
  have hZnn : ∀ r, 0 ≤ Z r := by
    intro r
    rw [hZ]
    refine Finset.sum_nonneg (fun ψ _ => ?_)
    have h1mem : (1 : ℕ) ∈ Set.Icc 1 (U * V) := by
      simp only [Set.mem_Icc]; exact ⟨le_rfl, by simpa using Nat.mul_le_mul hU hV⟩
    have hfin : ((fun y : ℕ => ‖bilinForm U V y a b r ψ‖) '' Set.Icc 1 (U * V)).Finite :=
      (Set.finite_Icc (1 : ℕ) (U * V)).image (fun y : ℕ => ‖bilinForm U V y a b r ψ‖)
    have hmem : ‖bilinForm U V 1 a b r ψ‖ ∈
        ((fun y : ℕ => ‖bilinForm U V y a b r ψ‖) '' Set.Icc 1 (U * V)) := ⟨1, h1mem, rfl⟩
    exact le_trans (norm_nonneg _) (le_csSup hfin.bddAbove hmem)
  have hglobal : (∑ q ∈ Finset.Icc 1 (2 * R), ((q : ℝ) / (q.totient : ℝ)) * Z q) ≤
      c * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2) *
        Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2) *
        Real.log (2 * (U : ℝ) * (V : ℝ) + 2) := by
    rw [hZ]
    have h := hc (2 * R) U V (by omega) hU hV a b
    simpa only [bilinForm] using h
  have hconv := Commons.NumberTheory.BombieriVinogradov.totient_inv_sum_le hR Z hZnn _ hglobal
  calc (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
        (∑ ψ ∈ (@Finset.filter (DirichletCharacter ℂ r) (fun ψ => ψ.IsPrimitive)
            (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖bilinForm U V y a b r ψ‖) '' Set.Icc 1 (U * V))))
      = ∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * Z r := rfl
    _ ≤ (R : ℝ)⁻¹ * (c * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2) *
        Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2) *
        Real.log (2 * (U : ℝ) * (V : ℝ) + 2)) := hconv
    _ = c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2) *
        Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2) *
        Real.log (2 * (U : ℝ) * (V : ℝ) + 2) := by ring

end Work.NumberTheory.Chen.BTermCount
