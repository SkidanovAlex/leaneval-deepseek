import Mathlib
import Submission.Vdw.FinalAssemblyM
import Submission.Vdw.CaseIIClasses
import Submission.Vdw.CaseIIFields
import Submission.Vdw.CaseIISmallDelta
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case II at the parameter threshold `2 + 4/M`

The region `SubcaseIM_P2 n M H` (`D_f ≤ H^(2+4/M)` inside the subcase-(i)
remainder `SubcaseIM`) is bounded by the *same* Abel-refined field-counting
input `CaseIICountBound n β` as the paper's Case II, but at the threshold
exponent `2 + 4/M` rather than `2 + 1/n`.

The point of the parameterisation is that with the Weyl choice
`M = weylM n = 4n·2^n` (`FinalAssemblyM`) the exponent `2 + 4/M` is
essentially `2`, so the *crude* field counting suffices for **every** degree
`n ≥ 3` — including `n = 4, 6`, where the paper's own threshold `2 + 1/n`
needs the finer (Weil-strength) per-discriminant input.  Concretely the
exponent condition is

  `1 + (2 + 4/M)·(β − 1/(n(n−1))) < n − 1`,

satisfied by `β = 1/2` (`n = 3`), `β = 1` (`n = 4, 5`) and
`β = (n+2)/4` (`n ≥ 6`) as soon as `M ≥ 4n·2^n`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **Case II at the threshold `2 + 4/M`, from the Abel-refined count bound.**
The region `SubcaseIM_P2 n M H` sits inside the `CaseIICountBound`-region
`SubcaseI_P2 n H` with discriminant at most `⌈H^(2+4/M)⌉`; the cumulative
bound evaluated at that modulus gives the exponent
`1 + (2 + 4/M)·(β − 1/(n(n−1)))`, and the logarithmic factor is absorbed by
the power saving. -/
theorem SubcaseIM_P2_isBigO_of_countBound (n M : ℕ) (β : ℝ) (hn : 3 ≤ n)
    (hM4 : 4 * n ≤ M)
    (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + 4 / (M : ℝ)) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1)
    (h : CaseIICountBound n β) :
    (fun H : ℕ => ((SubcaseIM_P2 n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  obtain ⟨C, hC, hCb⟩ := h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hn1pos
  set γ : ℝ := β - 1 / ((n : ℝ) * ((n : ℝ) - 1)) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  set κ : ℝ := 1 + (2 + 4 / (M : ℝ)) * γ with hκdef
  have hκ : κ < (n : ℝ) - 1 := by rw [hκdef, hγdef]; exact hexp
  set δ : ℝ := ((n : ℝ) - 1 - κ) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (H : ℝ)) ^ (n - 1) ≤ (H : ℝ) ^ δ := by
    have h1 := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
      (n - 1) 1 δ hδ
    filter_upwards [h1] with H hH
    simpa using hH
  have hXpow : ∀ (H X : ℕ), 1 ≤ H → (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 4 / (M : ℝ)) →
      (X : ℝ) ^ γ ≤ 2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) := by
    intro H X hH1 hXle
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    calc (X : ℝ) ^ γ ≤ (2 * (H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ γ :=
          Real.rpow_le_rpow (by positivity) hXle hγ.le
      _ = 2 ^ γ * ((H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ γ :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ = 2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) := by
          rw [Real.rpow_mul hHpos.le]
  have hbound : ∀ᶠ H : ℕ in atTop,
      ((SubcaseIM_P2 n M H).ncard : ℝ) ≤ C * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with H hlogH hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    -- the chosen modulus `X = ⌈H^(2+4/M)⌉`
    set X : ℕ := Nat.ceil ((H : ℝ) ^ (2 + 4 / (M : ℝ))) with hX
    have hX1 : 1 ≤ X := by
      rw [hX]
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      have h3 : (1 : ℝ) ≤ ((Nat.ceil ((H : ℝ) ^ (2 + 4 / (M : ℝ)))) : ℕ) :=
        le_trans h2 (Nat.le_ceil _)
      exact_mod_cast h3
    -- the inclusion `SubcaseIM_P2 ⊆ {f ∈ SubcaseI_P2 : disc ≤ X}`
    have hsub : SubcaseIM_P2 n M H ⊆ SubcaseI_P2 n H :=
      SubcaseIM_P2_subset_SubcaseI_P2 n M H hn hM4 hH1
    have hmem_le : ∀ (f : ℤ[X]) (hf : f ∈ SubcaseIM_P2 n M H),
        (subcaseI_P2_disc n H ⟨f, hsub hf⟩ : ℝ) ≤ (X : ℝ) := by
      intro f hf
      have hfmem := hf
      obtain ⟨-, h, hD⟩ := hf
      have heq : subcaseI_P2_disc n H ⟨f, hsub hfmem⟩ = fieldDiscExp f h := rfl
      rw [heq]
      calc (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) := hD
        _ ≤ (X : ℝ) := by rw [hX]; exact Nat.le_ceil _
    haveI hfinI : Fintype ↥(SubcaseI_P2 n H) :=
      ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
    have hcardle : (SubcaseIM_P2 n M H).ncard ≤
        Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_le_card_of_injective
        (fun f : ↥(SubcaseIM_P2 n M H) =>
          (⟨⟨f.1, hsub f.2⟩, hmem_le f.1 f.2⟩ :
            {g : ↥(SubcaseI_P2 n H) // (subcaseI_P2_disc n H g : ℝ) ≤ (X : ℝ)})) ?_
      intro a b hab
      exact Subtype.ext (congrArg (fun x => x.1.1) hab)
    have hcast : ((SubcaseIM_P2 n M H).ncard : ℝ) ≤
        ((Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ) := by
      exact_mod_cast hcardle
    have happly := hCb H X hX1
    -- `X ≤ 2·H^(2+4/M)`
    have hXle : (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 4 / (M : ℝ)) := by
      have h1 : (X : ℝ) < (H : ℝ) ^ (2 + 4 / (M : ℝ)) + 1 := by
        rw [hX]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      linarith
    have hXp := hXpow H X hH1 hXle
    have hlogle : (Real.log (H : ℝ)) ^ (n - 1) ≤ (1 + Real.log (H : ℝ)) ^ (n - 1) :=
      pow_le_pow_left₀ (Real.log_nonneg hH1R) (by linarith) (n - 1)
    have hκδ : κ + δ ≤ (n : ℝ) - 1 := by rw [hδdef]; linarith
    calc ((SubcaseIM_P2 n M H).ncard : ℝ)
        ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ :=
          le_trans hcast happly
      _ ≤ C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogle (by positivity))
            (by positivity)
      _ ≤ C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
            * (2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ)) :=
          mul_le_mul_of_nonneg_left hXp (by positivity)
      _ = C * 2 ^ γ * ((H : ℝ) ^ κ * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by
          have hrw1 : (H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) = (H : ℝ) ^ κ := by
            have h1 : (H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ)
                = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) := by
              rw [Real.rpow_one]
            rw [h1, (Real.rpow_add hHpos 1 _).symm]
          have hstep : C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
                * (2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
              = C * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
                * (1 + Real.log (H : ℝ)) ^ (n - 1) := by ring
          calc C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
                * (2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
              = C * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
                * (1 + Real.log (H : ℝ)) ^ (n - 1) := hstep
            _ = C * 2 ^ γ * ((H : ℝ) ^ κ * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by
                rw [hrw1]; ring
      _ ≤ C * 2 ^ γ * ((H : ℝ) ^ κ * (H : ℝ) ^ δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hlogH (by positivity)
      _ = C * 2 ^ γ * (H : ℝ) ^ (κ + δ) := by rw [← Real.rpow_add hHpos]
      _ ≤ C * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hH1R hκδ
  refine IsBigO.of_bound (C * 2 ^ γ) ?_
  filter_upwards [hbound] with H hH
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  rw [← Real.rpow_natCast (H : ℝ) (n - 1)]
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  exact hH

end

end Submission.Vdw
