import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB6Est.Regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — FS `thm:BogHamDiag`: the `𝒞`-sum bound `hkappa`

FS's §10 proof of `thm:BogHamDiag` needs the `𝒞`-sum of the quadratic Bogoliubov
Hamiltonian to be controlled by the *one* error term

  `(ρ_z − μ)² (ĝ(0)/2) ℓ³ (1 + C (μa³) R²/a²)`

(`eq:BogHamDiag`, FS's line following `eq:LowerBoundHBog`).  In scaled variables

  `𝒞_k = ℓ⁻³(ρ_z−μ)(8πa) χh(t_k) z`,  `𝒜_k + ℬ_k = ρ_z a(τ̃_k + 2β_k)`,

so wherever `𝒜_k + ℬ_k ≥ (16π − 2)ρ_z a = 2ρ_z a(8π − 1)` (FS's elementary
`𝒜(k)+ℬ(k) ≥ 2ρ_zŴ₁(0)(1 − C(μa³)R²/a²)`; at FS's data `β ≥ 8π − ηT ≥ 8π − 1`
on the support gives exactly this, which is the hypothesis of `kappaSum_le`)
one has

  `Σ_k 2𝒞_k²/(𝒜_k+ℬ_k) ≤ 2 (ℓ⁻³(ρ_z−μ)8πa z)² ((16π−2)ρ_z a)⁻¹ Σ_k χh(t_k)²`,

and the localisation normalisation `Σ_k χh(t_k)² ≤ ℓ³ chiM (1+δ)` (FS:
`(2π)⁻³∫|χ̂_Λ|²dk = ‖χ_Λ‖²_{L²} = chiM ≈ ℓ³`) turns this into `fsEkappa` (up to
the constant `2(8π−1)/(8π) < 2` absorbed by the `ℓ³ ≥ 3` slack).  `kappaSum_le`
below is this estimate in FS's form; it needs only the lower bound on
`𝒜_k + ℬ_k` on the support of `χh` (the modes with `χh = 0` contribute `0`) and
the normalisation of `χh`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6Est

local notation "ℝ³" => Fin 3 → ℝ

/-- **FS `thm:BogHamDiag`, the `𝒞`-sum bound (`hkappa`) at FS's coefficients.**

If `𝒜_k + ℬ_k ≥ (16π − 2)ρ_z a` on the support of `χh` (at FS's data:
`β ≥ 8π − 1` there), if the localisation satisfies
`Σ_k χh(t_k)² ≤ ℓ³ chiM (1+δ)` (its `L²` normalisation) and if `ℓ³ ≥ 3`, then

  `Σ_k 2𝒞_k²/(𝒜_k+ℬ_k) ≤ (ρ_z−μ)² (ĝ(0)/2) ℓ³ (1+δ)`,

i.e. FS's error term `(ρ_z−μ)²(ĝ(0)/2)ℓ³(1+C(μa³)R²/a²)` with
`ĝ(0) = Ŵ₁(0) z² chiM/(ρ_z ℓ³)` (`fsG0`) and `δ = C(μa³)R²/a²`. -/
theorem kappaSum_le {n : ℕ} {ρz a ℓ μ z chiM δ εT c1 c2 : ℝ} (K : FsKernel)
    (χh : ℝ³ → ℝ) (hρa : 0 < ρz * a) (hℓ : 0 < ℓ) (hchiM : 0 ≤ chiM)
    (hδ : 0 ≤ δ) (hℓ3 : 3 ≤ ℓ ^ 3)
    (hχ : chiSqSum n χh ≤ ℓ ^ 3 * chiM * (1 + δ))
    (hAB : ∀ k : modeIdx n, χh (modePos n k) ≠ 0 →
      (16 * Real.pi - 2) * (ρz * a) ≤ fsA ρz a K εT c1 c2 (modePos n k) + fsB ρz a K (modePos n k)) :
    kappaSum n ρz a ℓ μ z K εT c1 c2 χh ≤ fsEkappa ρz a ℓ μ z chiM δ := by
  set P : ℝ := (ℓ ^ 3)⁻¹ * (ρz - μ) * (8 * Real.pi * a) * z with hP
  set D : ℝ := (16 * Real.pi - 2) * (ρz * a) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    have : (0 : ℝ) < 16 * Real.pi - 2 := by nlinarith [Real.pi_gt_three]
    positivity
  -- termwise bound
  have hstep : ∀ k : modeIdx n,
      Work.BoseB6.bogKappaErr (fsA ρz a K εT c1 c2 (modePos n k)) (fsB ρz a K (modePos n k))
          (fsC ℓ ρz μ a z χh (modePos n k))
        ≤ 2 * (fsC ℓ ρz μ a z χh (modePos n k)) ^ 2 / D := by
    intro k
    by_cases hχ0 : χh (modePos n k) = 0
    · have h0 : (fsC ℓ ρz μ a z χh (modePos n k)) = 0 := by rw [fsC, hχ0]; ring
      rw [Work.BoseB6.bogKappaErr, h0]
      simp only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
      positivity
    · have hABk := hAB k hχ0
      rw [hDdef] at hD ⊢
      rw [Work.BoseB6.bogKappaErr]
      exact div_le_div_of_nonneg_left (by positivity) hD hABk
  refine le_trans (Finset.sum_le_sum fun k _ => hstep k) ?_
  -- the sum of the majorants
  have hsum : (∑ k : modeIdx n, 2 * (fsC ℓ ρz μ a z χh (modePos n k)) ^ 2 / D)
      = 2 * P ^ 2 / D * chiSqSum n χh := by
    rw [chiSqSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fsC, hP]
    ring
  rw [hsum]
  -- normalisation of the localisation
  have hχ' : chiSqSum n χh ≤ (8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 * chiM * (1 + δ) := by
    have hA : 0 ≤ chiM * (1 + δ) := mul_nonneg hchiM (by linarith)
    have h3 : ℓ ^ 3 ≤ (8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Real.pi)]
      have h6 : ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 := by ring
      have hx0 : 0 < ℓ ^ 3 := pow_pos hℓ 3
      have h7 : (8 * Real.pi - 1) * 3 ≥ 16 * Real.pi := by nlinarith [Real.pi_gt_three]
      have h8nn : (0 : ℝ) ≤ 8 * Real.pi - 1 := by nlinarith [Real.pi_gt_three]
      calc (8 * Real.pi - 1) * ℓ ^ 6 = (8 * Real.pi - 1) * (ℓ ^ 3 * ℓ ^ 3) := by rw [h6]
        _ ≥ (8 * Real.pi - 1) * (3 * ℓ ^ 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hℓ3 hx0.le) h8nn
        _ = (8 * Real.pi - 1) * 3 * ℓ ^ 3 := by ring
        _ ≥ 16 * Real.pi * ℓ ^ 3 := mul_le_mul_of_nonneg_right h7 hx0.le
        _ = ℓ ^ 3 * (16 * Real.pi) := by ring
    have h4 : ℓ ^ 3 * (chiM * (1 + δ))
        ≤ (8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 * (chiM * (1 + δ)) :=
      mul_le_mul_of_nonneg_right h3 hA
    have h5 : ℓ ^ 3 * chiM * (1 + δ) = ℓ ^ 3 * (chiM * (1 + δ)) := by ring
    have h6 : (8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 * chiM * (1 + δ)
        = (8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 * (chiM * (1 + δ)) := by ring
    linarith [hχ, h4, h5.ge, h5.le, h6.ge, h6.le]
  have hcoef : 0 ≤ 2 * P ^ 2 / D := by positivity
  have hfin : 2 * P ^ 2 / D * chiSqSum n χh
      ≤ (ρz - μ) ^ 2 * (8 * Real.pi * a * z ^ 2 * chiM / (ρz * ℓ ^ 3) / 2) * ℓ ^ 3 * (1 + δ) := by
    have h1 : 2 * P ^ 2 / D * chiSqSum n χh
        ≤ 2 * P ^ 2 / D * ((8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 * chiM * (1 + δ)) :=
      mul_le_mul_of_nonneg_left hχ' hcoef
    have h2 : 2 * P ^ 2 / D * ((8 * Real.pi - 1) / (16 * Real.pi) * ℓ ^ 6 * chiM * (1 + δ))
        = (ρz - μ) ^ 2 * (8 * Real.pi * a * z ^ 2 * chiM / (ρz * ℓ ^ 3) / 2) * ℓ ^ 3 * (1 + δ) := by
      rw [hP, hDdef]
      have h01 : (-2 + Real.pi * 16) ≠ 0 := by
        have : (0 : ℝ) < -2 + Real.pi * 16 := by nlinarith [Real.pi_gt_three]
        exact ne_of_gt this
      have h16 : ((16 * Real.pi - 2) * (ρz * a)) ≠ 0 := by
        have : (0 : ℝ) < 16 * Real.pi - 2 := by nlinarith [Real.pi_gt_three]
        positivity
      have h8 : (8 * Real.pi - 1) ≠ 0 := by
        have : (0 : ℝ) < 8 * Real.pi - 1 := by nlinarith [Real.pi_gt_three]
        exact ne_of_gt this
      have hρ : ρz ≠ 0 := fun h => (ne_of_gt hρa) (by rw [h]; ring)
      have ha : a ≠ 0 := fun h => (ne_of_gt hρa) (by rw [h]; ring)
      have hl : ℓ ≠ 0 := ne_of_gt hℓ
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring_nf
      field_simp [h01]
      ring
    linarith [h1, h2.le]
  rw [fsEkappa, fsG0]
  exact hfin

end Work.BoseB6Est
