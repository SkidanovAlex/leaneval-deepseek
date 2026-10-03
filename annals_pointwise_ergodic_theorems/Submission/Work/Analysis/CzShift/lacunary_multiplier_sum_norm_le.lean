import Mathlib
import Submission.Work.Analysis.CzShift.lacunary_sums

/-!
# Sum-of-norms bound for lacunary multipliers with a `min 1 |ξ|` symbol

Let `lam > 1`, `C > 0`.  Let `D` be a finite index set, `σ : ι → ℝ` a positive
`lam`-lacunary family of scales on `D` (`LacunaryFam lam D σ`), and let `ψ : ℝ → ℂ`
be supported in `|ξ| ≤ C` and obey the symbol bound `‖ψ ξ‖ ≤ C * min 1 |ξ|`.

Then `∑_{i ∈ D} ‖ψ(σ i * ξ)‖` is bounded uniformly in `D`, `σ`, `ψ` and `ξ`.  This
is the `ℓ¹`-in-the-scales companion of `lacunary_multiplier_sup_le`; it is the
statement actually needed to dominate the pointwise sum of the shifted kernels.

Indeed, fix `ξ ≠ 0` and put `x = |ξ|`.  A summand vanishes unless
`σ i * x ≤ C`.  Splitting the family at `σ i = 1/x`:

* if `σ i < 1/x` then `min 1 (σ i * x) = σ i * x`, so
  `∑_{σ i < 1/x} ‖ψ (σ i ξ)‖ ≤ C x ∑_{σ i < 1/x} σ i ≤ C x · (1/x) · 1/(1-λ⁻¹)`;
* if `1/x ≤ σ i` then `ψ (σ i ξ) = 0` unless `σ i * x ≤ C`, in which case
  `(1/x)/σ i ≥ 1/C` and `∑_{1/x ≤ σ i} ‖ψ (σ i ξ)‖ ≤ C² ∑_{1/x ≤ σ i} (1/x)/σ i
  ≤ C² · 1/(1-λ⁻¹)`,

by the geometric bounds of `lacunary_sums`.  The case `ξ = 0` is trivial since
`ψ 0 = 0`.
-/

namespace Work.Analysis.CzShift

theorem lacunary_multiplier_sum_norm_le {ι : Type*} (lam C : ℝ) (hlam : 1 < lam) (hC : 0 < C) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ (D : Finset ι) (σ : ι → ℝ) (ψ : ℝ → ℂ),
      LacunaryFam lam D σ →
      (∀ ξ : ℝ, C < |ξ| → ψ ξ = 0) →
      (∀ ξ : ℝ, ‖ψ ξ‖ ≤ C * min 1 |ξ|) →
      ∀ ξ : ℝ, ∑ i ∈ D, ‖ψ (σ i * ξ)‖ ≤ Cm := by
  have hden : 0 < 1 - lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam)
  refine ⟨(C + C ^ 2) * (1 / (1 - lam⁻¹)),
    mul_pos (add_pos hC (pow_pos hC 2)) (one_div_pos.mpr hden), ?_⟩
  intro D σ ψ hlac hsup hbd ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · -- `ξ = 0`: every summand vanishes
    have hψ0 : ψ 0 = 0 := norm_le_zero_iff.mp (by simpa using hbd 0)
    have hzero : ∑ i ∈ D, ‖ψ (σ i * (0 : ℝ))‖ = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [mul_zero, hψ0, norm_zero]
    rw [hzero]
    exact mul_nonneg (add_nonneg hC.le (sq_nonneg C)) (one_div_pos.mpr hden).le
  · set x := |ξ| with hx
    have hx0 : 0 < x := by rw [hx]; exact abs_pos.mpr hξ
    have hL : 0 < 1 / x := one_div_pos.mpr hx0
    obtain ⟨-, htail, hhead⟩ := lacunary_sums D σ hlam hlac
    -- ### pointwise bounds on the two pieces
    have key₁ : ∀ i ∈ D.filter (fun i => σ i < 1 / x),
        ‖ψ (σ i * ξ)‖ ≤ C * (σ i * x) := by
      intro i hi
      have hii : i ∈ D := Finset.mem_of_mem_filter i hi
      have hlt : σ i < 1 / x := (Finset.mem_filter.mp hi).2
      have hσ : 0 < σ i := hlac.1 i hii
      have hlt' : σ i * x < 1 := (lt_div_iff₀ hx0).mp hlt
      have habs : |σ i * ξ| = σ i * x := by rw [abs_mul, abs_of_pos hσ, hx]
      calc ‖ψ (σ i * ξ)‖ ≤ C * min 1 |σ i * ξ| := hbd _
        _ = C * (σ i * x) := by rw [habs, min_eq_right hlt'.le]
    have key₂ : ∀ i ∈ D.filter (fun i => 1 / x ≤ σ i),
        ‖ψ (σ i * ξ)‖ ≤ C ^ 2 * ((1 / x) / σ i) := by
      intro i hi
      have hii : i ∈ D := Finset.mem_of_mem_filter i hi
      have hge : 1 / x ≤ σ i := (Finset.mem_filter.mp hi).2
      have hσ : 0 < σ i := hlac.1 i hii
      have hge' : 1 ≤ σ i * x := (div_le_iff₀ hx0).mp hge
      have habs : |σ i * ξ| = σ i * x := by rw [abs_mul, abs_of_pos hσ, hx]
      by_cases hle : σ i * x ≤ C
      · have hCb : ‖ψ (σ i * ξ)‖ ≤ C := by
          calc ‖ψ (σ i * ξ)‖ ≤ C * min 1 |σ i * ξ| := hbd _
            _ = C * 1 := by rw [habs, min_eq_left hge']
            _ = C := mul_one C
        have hCc : C ≤ C ^ 2 * ((1 / x) / σ i) := by
          have hd : (1 / x) / σ i = 1 / (x * σ i) := by rw [div_div]
          rw [hd, mul_one_div, le_div_iff₀ (mul_pos hx0 hσ)]
          nlinarith [hC, hle, mul_le_mul_of_nonneg_left hle hC.le]
        linarith
      · have hgt : C < σ i * x := not_le.mp hle
        rw [hsup _ (by rw [habs]; exact hgt), norm_zero]
        exact mul_nonneg (sq_nonneg C) (div_pos (one_div_pos.mpr hx0) hσ).le
    -- ### the two sum bounds
    have hsum₁ : ∑ i ∈ D.filter (fun i => σ i < 1 / x), ‖ψ (σ i * ξ)‖
        ≤ C * (1 / (1 - lam⁻¹)) := by
      have hh := hhead (1 / x) hL
      have h1 : ∑ i ∈ D.filter (fun i => σ i < 1 / x), ‖ψ (σ i * ξ)‖
          ≤ C * ∑ i ∈ D.filter (fun i => σ i < 1 / x), σ i / (1 / x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hd : σ i / (1 / x) = σ i * x := by rw [one_div, div_inv_eq_mul]
        rw [hd]
        exact key₁ i hi
      exact le_trans h1 (mul_le_mul_of_nonneg_left hh hC.le)
    have hsum₂ : ∑ i ∈ D.filter (fun i => 1 / x ≤ σ i), ‖ψ (σ i * ξ)‖
        ≤ C ^ 2 * (1 / (1 - lam⁻¹)) := by
      have hh := htail (1 / x) hL
      have h1 : ∑ i ∈ D.filter (fun i => 1 / x ≤ σ i), ‖ψ (σ i * ξ)‖
          ≤ C ^ 2 * ∑ i ∈ D.filter (fun i => 1 / x ≤ σ i), (1 / x) / σ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum key₂
      exact le_trans h1 (mul_le_mul_of_nonneg_left hh (sq_nonneg C))
    -- ### assembly
    have hD₂ : D.filter (fun i => ¬ (σ i < 1 / x)) = D.filter (fun i => 1 / x ≤ σ i) :=
      Finset.filter_congr fun i _ => not_lt
    have hsplit := (Finset.sum_filter_add_sum_filter_not D (fun i => σ i < 1 / x)
      (fun i => ‖ψ (σ i * ξ)‖)).symm
    rw [hD₂] at hsplit
    calc ∑ i ∈ D, ‖ψ (σ i * ξ)‖
        = ∑ i ∈ D.filter (fun i => σ i < 1 / x), ‖ψ (σ i * ξ)‖
          + ∑ i ∈ D.filter (fun i => 1 / x ≤ σ i), ‖ψ (σ i * ξ)‖ := hsplit
      _ ≤ C * (1 / (1 - lam⁻¹)) + C ^ 2 * (1 / (1 - lam⁻¹)) := add_le_add hsum₁ hsum₂
      _ = (C + C ^ 2) * (1 / (1 - lam⁻¹)) := by ring

end Work.Analysis.CzShift
