import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_defs

/-!
# `Work.GM.Affine.Gfun_le_gSum` (GM §9, region II: the honest affine sum is dominated by `gSum`)

The Poisson summation of GM §9 region II produces the "honest" affine sum

`Gfun C₀ T M₂ f u = Σ_{m₂ ∈ R2 M₂} Σ_{m₂' ∈ R2 M₂} Σ_{|j| ≤ ⌊2C₀M₂⌋} f̃((m₂u + j)/m₂')`,

while the majorant that all the `L²` estimates are phrased for is

`gSum K M₁ M₂ M₃ g u = Σ_{m₁ ∈ R1 M₁} Σ_{m₂ ∈ R2 M₂} Σ_{m₃ ∈ R3ext K M₃}
                          ψ₁ K (m₃/M₃) · g((m₁u + m₃)/m₂)`.

This file proves the pointwise comparison at `M₁ = M₂`, `M₃ = r₃`, `g = smoothed psiSmooth T f`:

`Gfun C₀ T M₂ f u ≤ gSum K M₂ M₂ r₃ (smoothed psiSmooth T f) u`,   as soon as `r₃ ≥ (2C₀M₂+1)/K`,

i.e. as soon as the `m₃`-range `R3ext K r₃` covers the `j`-range `|j| ≤ ⌊2C₀M₂⌋`.  The three
elementary inputs are:

* `R2 M₂ ⊆ R1 M₂` (the positive half of the symmetric range `R1`);
* `Icc (-⌊2C₀M₂⌋) ⌊2C₀M₂⌋ ⊆ R3ext K r₃`, which follows from
  `⌊2C₀M₂⌋ ≤ 2C₀M₂ < (K+1)r₃ ≤ ⌈(K+1)r₃⌉` — here `r₃ > 0` because
  `r₃ ≥ (2C₀M₂+1)/K > 0`;
* on that range the bump equals one, `ψ₁ K (j/r₃) = 1` (because `|j| ≤ 2C₀M₂ < K r₃`),
  so multiplying by `ψ₁ K (j/r₃)` is free; all terms are non-negative since `f ≥ 0` and
  `psiSmooth ≥ 0` force `smoothed psiSmooth T f ≥ 0`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The smoothing `f̃ = smoothed psiSmooth T f` of a non-negative `f` (with `T > 0`) is
non-negative. -/
lemma smoothed_psiSmooth_nonneg {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u)
    (x : ℝ) : 0 ≤ smoothed psiSmooth T f x := by
  rw [smoothed]
  exact mul_nonneg hT.le
    (integral_nonneg (fun u' => mul_nonneg (psiSmooth_nonneg _) (hfnn _)))

/-- The positive half `R2 M₂` of the symmetric `m₁`-range `R1 M₂`. -/
lemma R2_subset_R1 {M₂ : ℝ} (hM₂ : 0 < M₂) : R2 M₂ ⊆ R1 M₂ := by
  intro m hm
  rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨h1, h2⟩, h3⟩ := hm
  rw [R1, Finset.mem_filter, Finset.mem_Icc]
  have hfl : (0 : ℤ) ≤ ⌊2 * M₂⌋ := Int.floor_nonneg.mpr (by linarith)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < m)
  refine ⟨⟨by omega, h2⟩, ?_⟩
  rw [abs_of_pos hmpos]
  exact h3

/-- The `j`-range of `Gfun` is contained in the enlarged `m₃`-range of `gSum`, provided
`(2C₀M₂ + 1)/K ≤ r₃`. -/
lemma Icc_subset_R3ext {K C₀ M₂ r₃ : ℝ} (hK : 0 < K) (hC₀ : 0 ≤ C₀) (hM₂ : 0 < M₂)
    (hr₃ : (2 * C₀ * M₂ + 1) / K ≤ r₃) :
    Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋ ⊆ R3ext K r₃ := by
  have hnum : 0 < 2 * C₀ * M₂ + 1 := by nlinarith
  have hr₃pos : 0 < r₃ := lt_of_lt_of_le (div_pos hnum hK) hr₃
  have hKr₃ : 2 * C₀ * M₂ + 1 ≤ K * r₃ := by
    have h := (div_le_iff₀ hK).mp hr₃
    linarith
  have hfloorceil : ⌊2 * C₀ * M₂⌋ ≤ ⌈(K + 1) * r₃⌉ := by
    have h1 := Int.floor_le (2 * C₀ * M₂)
    have h2 := Int.le_ceil ((K + 1) * r₃)
    have : ((⌊2 * C₀ * M₂⌋ : ℤ) : ℝ) ≤ ((⌈(K + 1) * r₃⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [R3ext, Finset.mem_Icc]
  exact ⟨by linarith, by linarith⟩

/-- On the `j`-range of `Gfun` the bump `ψ₁ K (·/r₃)` equals `1`. -/
lemma psi1_div_eq_one {K C₀ M₂ r₃ : ℝ} (hK : 0 < K) (hC₀ : 0 ≤ C₀) (hM₂ : 0 < M₂)
    (hr₃ : (2 * C₀ * M₂ + 1) / K ≤ r₃) {j : ℤ}
    (hj : j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋) :
    psi1 K ((j : ℝ) / r₃) = 1 := by
  have hnum : 0 < 2 * C₀ * M₂ + 1 := by nlinarith
  have hr₃pos : 0 < r₃ := lt_of_lt_of_le (div_pos hnum hK) hr₃
  have hKr₃ : 2 * C₀ * M₂ + 1 ≤ K * r₃ := by
    have h := (div_le_iff₀ hK).mp hr₃
    linarith
  rw [Finset.mem_Icc] at hj
  refine psi1_eq_one ?_
  have h1 : -(⌊2 * C₀ * M₂⌋ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have h2 : (j : ℝ) ≤ (⌊2 * C₀ * M₂⌋ : ℝ) := by exact_mod_cast hj.2
  have h3 : |(j : ℝ)| ≤ 2 * C₀ * M₂ :=
    le_trans (abs_le.mpr ⟨h1, h2⟩) (Int.floor_le _)
  rw [abs_div, abs_of_pos hr₃pos, div_le_iff₀ hr₃pos]
  linarith

/-- **The honest affine sum of GM §9 region II is dominated by `gSum`.**

With `M₁ = M₂`, `M₃ = r₃` and `g = smoothed psiSmooth T f`, the sum

`Gfun C₀ T M₂ f u = Σ_{m₂ ∈ R2 M₂} Σ_{m₂' ∈ R2 M₂} Σ_{|j| ≤ ⌊2C₀M₂⌋} f̃((m₂u + j)/m₂')`

is bounded by the `ψ₁`-weighted sum over the enlarged `m₃`-range:

`gSum K M₂ M₂ r₃ f̃ u = Σ_{m₁ ∈ R1 M₂} Σ_{m₂ ∈ R2 M₂} Σ_{m₃ ∈ R3ext K r₃}
                          ψ₁ K (m₃/r₃) · f̃((m₁u + m₃)/m₂)`,

the only requirement on `r₃` being `(2C₀M₂ + 1)/K ≤ r₃`, which makes `R3ext K r₃` cover the
`j`-range `|j| ≤ ⌊2C₀M₂⌋`. -/
theorem Gfun_le_gSum {K C₀ T M₂ r₃ : ℝ} (hK : 0 < K) (hC₀ : 0 ≤ C₀) (hT : 0 < T)
    (hM₂ : 0 < M₂) (hr₃ : (2 * C₀ * M₂ + 1) / K ≤ r₃) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u)
    (u : ℝ) :
    Gfun C₀ T M₂ f u ≤ gSum K M₂ M₂ r₃ (smoothed psiSmooth T f) u := by
  set F : ℝ → ℝ := smoothed psiSmooth T f with hFdef
  have hFnn : ∀ x, 0 ≤ F x := by
    intro x
    rw [hFdef]
    exact smoothed_psiSmooth_nonneg hT hfnn x
  have hR2R1 : R2 M₂ ⊆ R1 M₂ := R2_subset_R1 hM₂
  have hIccR3 : Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋ ⊆ R3ext K r₃ :=
    Icc_subset_R3ext hK hC₀ hM₂ hr₃
  rw [Gfun, gSum]
  calc ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
        ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
          F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))
      ≤ ∑ m₁ ∈ R1 M₂, ∑ m₂ ∈ R2 M₂,
        ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
          F (((m₁ : ℝ) * u + (j : ℝ)) / (m₂ : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hR2R1 ?_
        intro m _ _
        exact Finset.sum_nonneg (fun m' _ => Finset.sum_nonneg (fun j _ => hFnn _))
    _ ≤ ∑ m₁ ∈ R1 M₂, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K r₃,
          psi1 K ((m₃ : ℝ) / r₃) * F (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) := by
        refine Finset.sum_le_sum (fun m₁ _ => Finset.sum_le_sum (fun m₂ _ => ?_))
        have hcongr : (∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
              F (((m₁ : ℝ) * u + (j : ℝ)) / (m₂ : ℝ)))
            = ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
              psi1 K ((j : ℝ) / r₃) * F (((m₁ : ℝ) * u + (j : ℝ)) / (m₂ : ℝ)) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [psi1_div_eq_one hK hC₀ hM₂ hr₃ hj, one_mul]
        rw [hcongr]
        exact Finset.sum_le_sum_of_subset_of_nonneg hIccR3
          (fun m _ _ => mul_nonneg (psi1_nonneg _ _) (hFnn _))

end

end Work.GM.Affine
