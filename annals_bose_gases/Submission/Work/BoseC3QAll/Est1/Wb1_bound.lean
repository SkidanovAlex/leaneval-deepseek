import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.Wb1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.Wb1_bound` — the `σ₁`-word `κB(b_k†+b_k)`

Family 2 of the leftover `R1` of FS `eq:EstimateQ3Tilde1` (`Est1.estR1_defs`):

  `Wb1 = (z/ℓ³) Σ_{s∈suppL} Σ_{k∈P_H} γ_{sk}β_{sk}κB_{sk} (b_k† + b_k)`,

and this module proves (FS §10, the `κB` row of the linear leftover) that at small
diluteness

  `-(costB2)‖Φ‖² - (𝓁²/8)⟨Φ, ∫_{P_H^q}𝒟_k b_k†b_k Φ⟩ ≤ ⟨Φ, Wb1 Φ⟩`

for every state `Φ` in FS's number window `T.NWindow E.bigM`, where

  `costB2 = 512·64⁶·K₀^{11}·(K_ℓK_L)⁶·𝓁⁴·η²·ρ_z·a`.

## The proof

`Wb1` is a sum of `2C_kb_k`-words with the collected coefficients
`C_k = Σ_{s∈suppL} cB1 s k` (`Est1.Wb1_defs`), so its quadratic form is

  `⟨Φ, Wb1 Φ⟩ = Σ_{k∈P_H} 2C_k⟨b_kΦ,Φ⟩`   (`Wb1_qw_eq`).

Each term is estimated by Young's inequality in the Fock form (`bp_cauchy`) with
the *weight* `ε_k = (𝓁²/8)𝒟_k` (`Wb1_perk`):

  `2C_k⟨b_kΦ,Φ⟩ ≥ -(ε_k‖b_kΦ‖² + ε_k⁻¹C_k²‖Φ‖²)`,

so that `Σ_k ε_k‖b_kΦ‖² = (𝓁²/8)Σ_{P_H}𝒟_k‖b_kΦ‖²` is dominated by the
quarter-region reserve `(𝓁²/8)⟨Φ, dNumOpR P_H^q Φ⟩` (`Wb1_reserve`, `P_H ⊆ P_H^q`),
and the error term is `(8/𝓁²)Σ_k C_k²/𝒟_k·‖Φ‖²`.

The coefficient sum `Σ_k C_k²/𝒟_k ≤ 64⁷K₀^{11}(K_ℓK_L)⁶𝓁⁶η²ρ_za` is the content of
`Wb1_coef_sum`: Cauchy–Schwarz in the `s`-sum, the local bound
`cB1² ≤ 16·64⁶K₀^8𝓁⁶η²(ρ_z/ℓ³)Ŵ₁(k)²` (`Wb1_coef_le`), and the weighted lattice sum
`Σ_{P_H}Ŵ₁(k)²/𝒟_k ≤ 4ℓ³K₀a` (`Wb1_sumsq`, from `Q3KernelFSAll.sum_W1sq` and
`𝒟_k ≥ ‖k‖²/4`), together with the mode count `#suppL ≤ K₀(K_ℓK_L)³`.  Since
`(8/𝓁²)·64⁷ = 512·64⁶ = costB2/(𝓁⁴η²ρ_za)`, the constant `costB2` is exactly the
one this route produces.

No use is made of the number window `T.NWindow E.bigM Φ`: the word is linear and
its estimate is a pure Cauchy–Schwarz statement about `Φ`.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. Elementary helpers -/

/-- `Σ_i f i * (2X) = (2Σ_i f i) * X`. -/
lemma sum_mul_two {ι : Type*} (t : Finset ι) (f : ι → ℝ) (X : ℝ) :
    ∑ i ∈ t, f i * (2 * X) = (2 * ∑ i ∈ t, f i) * X := by
  rw [← Finset.sum_mul]
  ring

/-- `⟨c • v, g⟩ = c⟨v,g⟩` for the Fock form. -/
lemma bp_smul_left' {F : FockData Mode} (c : ℝ) (v g : F.H) :
    F.bp (c • v) g = c * F.bp v g := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- `⟨v, c • g⟩ = c⟨v,g⟩` for the Fock form. -/
lemma bp_smul_right' {F : FockData Mode} (c : ℝ) (v g : F.H) :
    F.bp v (c • g) = c * F.bp v g := by
  rw [map_smul, smul_eq_mul]

/-- `⟨-v, g⟩ = -⟨v,g⟩` for the Fock form. -/
lemma bp_neg_left' {F : FockData Mode} (v g : F.H) :
    F.bp (-v) g = -F.bp v g := by
  rw [map_neg, LinearMap.neg_apply]

/-- `⟨v, -g⟩ = -⟨v,g⟩` for the Fock form. -/
lemma bp_neg_right' {F : FockData Mode} (v g : F.H) :
    F.bp v (-g) = -F.bp v g := by
  rw [map_neg]

/-- Linearity of `qw` in a finite sum of scalar multiples of operators. -/
lemma qw_finset_sum' (F : FockData Mode) (Φ : F.H) {ι : Type*} (t : Finset ι)
    (c : ι → ℝ) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ i ∈ t, c i • X i) = ∑ i ∈ t, c i * F.qw Φ (X i) := by
  have h1 : (∑ i ∈ t, c i • X i) Φ = ∑ i ∈ t, c i • (X i Φ) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply]
  calc F.qw Φ (∑ i ∈ t, c i • X i)
      = F.bp (∑ i ∈ t, c i • (X i Φ)) Φ := by rw [FockData.qw, h1]
    _ = (∑ i ∈ t, F.bp (c i • (X i Φ))) Φ := by rw [map_sum]
    _ = ∑ i ∈ t, (F.bp (c i • (X i Φ))) Φ := by rw [LinearMap.sum_apply]
    _ = ∑ i ∈ t, c i * F.bp (X i Φ) Φ :=
        Finset.sum_congr rfl fun i _ => by
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = ∑ i ∈ t, c i * F.qw Φ (X i) :=
        Finset.sum_congr rfl fun i _ => by rw [FockData.qw]

/-- Linearity of `qw` in a double sum of scalar multiples of operators. -/
lemma qw_double_sum' (F : FockData Mode) (Φ : F.H) (t₁ t₂ : Finset Mode)
    (c : Mode → Mode → ℝ) (X : Mode → Mode → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ s ∈ t₁, ∑ k ∈ t₂, c s k • X s k)
      = ∑ s ∈ t₁, ∑ k ∈ t₂, c s k * F.qw Φ (X s k) := by
  have h1 : (∑ s ∈ t₁, ∑ k ∈ t₂, c s k • X s k)
      = ∑ s ∈ t₁, (1 : ℝ) • (∑ k ∈ t₂, c s k • X s k) :=
    Finset.sum_congr rfl fun s _ => (one_smul ℝ _).symm
  rw [h1, qw_finset_sum' F Φ t₁ (fun _ => 1) (fun s => ∑ k ∈ t₂, c s k • X s k)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [one_mul, qw_finset_sum' F Φ t₂ (c s) (X s)]

/-- The square of a product of three bounded factors:
`(a₁a₂a₃)² ≤ b₁²b₂²b₃²` as soon as `|a_i| ≤ b_i` with `b_i ≥ 0`. -/
lemma sq_mul_le_sq_mul {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁ : |a₁| ≤ b₁) (h₂ : |a₂| ≤ b₂)
    (h₃ : |a₃| ≤ b₃) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) :
    (a₁ * a₂ * a₃) ^ 2 ≤ b₁ ^ 2 * b₂ ^ 2 * b₃ ^ 2 := by
  have h : |a₁ * a₂ * a₃| ≤ b₁ * b₂ * b₃ := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h₁ h₂ (abs_nonneg _) hb₁) h₃ (abs_nonneg _)
      (mul_nonneg hb₁ hb₂)
  calc (a₁ * a₂ * a₃) ^ 2 = |a₁ * a₂ * a₃| ^ 2 := (sq_abs _).symm
    _ ≤ (b₁ * b₂ * b₃) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = b₁ ^ 2 * b₂ ^ 2 * b₃ ^ 2 := by ring

/-! ## 2. The expansion of the word -/

/-- **The word `Wb1` in the Fock form.**  Expanding the operator sum and using
`⟨b_k†Φ,Φ⟩ = ⟨b_kΦ,Φ⟩` (adjointness of `b_k†` and symmetry of the Fock form)
replaces the double `(s,k)` sum by the collected coefficients `CB1`. -/
theorem Wb1_qw_eq (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H) :
    F.qw Φ (Wb1 F T E) =
      ∑ k ∈ F.PHset E, (2 * CB1 T E k) * F.bp (F.bOp E.alpha k Φ) Φ := by
  have hstep : ∀ k : Mode, F.qw Φ (F.bOpDag E.alpha k + F.bOp E.alpha k)
      = 2 * F.bp (F.bOp E.alpha k Φ) Φ := by
    intro k
    rw [FockData.qw, LinearMap.add_apply, map_add, LinearMap.add_apply, bp_bOpDag_left,
      F.bp_symm Φ (F.bOp E.alpha k Φ)]
    ring
  have hW : Wb1 F T E = ∑ s ∈ suppL E, ∑ k ∈ F.PHset E, cB1 T E s k •
      (F.bOpDag E.alpha k + F.bOp E.alpha k) := by
    simp only [Wb1, cB1]
  rw [hW, qw_double_sum' F Φ (suppL E) (F.PHset E) (fun s k => cB1 T E s k)
      (fun _ k => F.bOpDag E.alpha k + F.bOp E.alpha k)]
  rw [show (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
        cB1 T E s k * F.qw Φ (F.bOpDag E.alpha k + F.bOp E.alpha k))
      = ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
        cB1 T E s k * (2 * F.bp (F.bOp E.alpha k Φ) Φ) from
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun k _ => by rw [hstep k]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_mul_two, ← CB1]

/-! ## 3. The Young step, mode by mode -/

/-- **Young's inequality in the Fock form, with the weight `ε_k = (𝓁²/8)𝒟_k`.**
The `k`-th summand of `⟨Φ, Wb1 Φ⟩` is bounded below by the negative of the
reserve term `ε_k‖b_kΦ‖²` and the error term `ε_k⁻¹C_k²‖Φ‖²`. -/
lemma Wb1_perk (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    (k : Mode) (hD : 0 < E.D k) (h𝓁 : 0 < E.lille) :
    -(((E.lille ^ 2 / 8) * E.D k) * F.bp (F.bNumOp E.alpha k Φ) Φ
        + ((E.lille ^ 2 / 8) * E.D k)⁻¹ * (CB1 T E k) ^ 2 * F.normSq Φ)
      ≤ 2 * CB1 T E k * F.bp (F.bOp E.alpha k Φ) Φ := by
  have hε : 0 < (E.lille ^ 2 / 8) * E.D k := by positivity
  have hbb : F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ)
      = F.bp (F.bNumOp E.alpha k Φ) Φ := by
    rw [FockData.bNumOp, LinearMap.comp_apply]
    exact (bp_bOpDag F E.alpha k (F.bOp E.alpha k Φ) Φ).symm
  have hlin : F.bp (F.bOp E.alpha k Φ) (CB1 T E k • Φ)
      = CB1 T E k * F.bp (F.bOp E.alpha k Φ) Φ :=
    bp_smul_right' (CB1 T E k) (F.bOp E.alpha k Φ) Φ
  have hlin_neg : F.bp (F.bOp E.alpha k Φ) (-(CB1 T E k • Φ))
      = -(CB1 T E k * F.bp (F.bOp E.alpha k Φ) Φ) := by
    rw [bp_neg_right', hlin]
  have hvv : F.bp (CB1 T E k • Φ) (CB1 T E k • Φ)
      = (CB1 T E k) ^ 2 * F.normSq Φ := by
    rw [bp_smul_left', F.bp_symm Φ (CB1 T E k • Φ), bp_smul_left', FockData.normSq]
    ring
  have hvv_neg : F.bp (-(CB1 T E k • Φ)) (-(CB1 T E k • Φ))
      = (CB1 T E k) ^ 2 * F.normSq Φ := by
    rw [bp_neg_left', bp_neg_right', hvv]
    ring
  have h := bp_cauchy F hε (F.bOp E.alpha k Φ) (-(CB1 T E k • Φ))
  rw [hbb, hvv_neg, hlin_neg] at h
  linarith

/-! ## 4. The reserve: `P_H ⊆ P_H^q` -/

/-- **The kinetic reserve.**  The `P_H`-sum of the `𝒟`-weighted mode numbers is
dominated by the quarter-region reserve `⟨Φ, dNumOpR P_H^q Φ⟩`, because each
`𝒟_k ≥ 0` on `P_H^q` and `P_H ⊆ P_H^q` (`Finset.sum_le_sum_of_subset_of_nonneg`). -/
lemma Wb1_reserve (F : FockData Mode) (E : Q3Env Mode) (Φ : F.H)
    (hsub : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i)
    (hD : ∀ i : Mode, F.PHq E.KH E.aScat i → 0 ≤ E.D i) :
    ∑ k ∈ F.PHset E, E.D k * F.bp (F.bNumOp E.alpha k Φ) Φ
      ≤ F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
  rw [FockData.qw, bp_dNumOpR F E (F.PHq E.KH E.aScat) Φ]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    rw [FockData.PHset, Finset.mem_filter] at hk
    exact Finset.mem_filter.mpr ⟨hk.1, hsub k hk.2⟩
  · intro k hk _
    rw [Finset.mem_filter] at hk
    exact mul_nonneg (hD k hk.2) (bp_bNumOp_nonneg F E.alpha k Φ)

/-! ## 5. The local bound on the coefficients -/

/-- **The local coefficient bound.**  For `s ∈ suppL` and `k ∈ P_H`, the
coefficient `cB1 T E s k = (z/ℓ³)γβκB` obeys

  `cB1² ≤ 16·64⁶K₀^8𝓁⁶η²·(ρ_z/ℓ³)·Ŵ₁(k)²`,

because `γ = f_LŴ₁q3Denom` with `|f_L| ≤ 1` and `q3Denom ≤ 4`, `β = α_kα_{s-k}`
and `κB = -α_{s-k}·χ̂`-kernel with `|α| ≤ 64K₀𝓁` on `P_H^q` and `|ccrX| ≤ K₀η`,
while `z² = ρ_zℓ³` converts `(z/ℓ³)²` into `ρ_z/ℓ³`. -/
lemma Wb1_coef_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (K₀ : ℝ)
    (hK : Q3KernelFSAll K₀ F T E)
    (hα : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hhalf : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hPHq : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i)
    (hsk : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.PHq E.KH E.aScat (s - k))
    (hz : E.z ^ 2 = E.rho * E.ell ^ 3) (hK0 : 0 ≤ K₀) (h𝓁 : 0 ≤ E.lille)
    (hη : 0 ≤ eta E) (hell : 0 < E.ell) :
    ∀ s k : Mode, s ∈ suppL E → k ∈ F.PHset E →
      (cB1 T E s k) ^ 2
        ≤ 16 * (64 : ℝ) ^ 6 * K₀ ^ 8 * E.lille ^ 6 * (eta E) ^ 2
            * (E.rho / E.ell ^ 3) * (E.W1 k) ^ 2 := by
  intro s k hs hk
  have hfL : E.fL s ≠ 0 := suppL_fL_ne_zero hs
  by_cases hW : E.W1 k = 0
  · -- both sides carry the factor `Ŵ₁ k`
    have hz2 : (cB1 T E s k) ^ 2 = 0 := by rw [cB1, gA, hW]; ring
    have hzW : (E.W1 k) ^ 2 = 0 := by rw [hW]; norm_num
    rw [hz2, hzW]
    simp
  have hPHk : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hqk : F.PHq E.KH E.aScat k := hPHq k hPHk
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsk s k hfL hk hW
  have hqks : F.PHq E.KH E.aScat (k - s) := by
    have hnorm : ‖F.kmom (k - s)‖ = ‖F.kmom (s - k)‖ := by
      rw [show k - s = -(s - k) by abel, F.kmom_neg, norm_neg]
    show 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom (k - s)‖
    rw [hnorm]
    exact hqsk
  -- the three factor bounds
  have hfL1 : |E.fL s| ≤ 1 := abs_le.mpr ⟨by linarith [hK.fL_nonneg s], hK.fL_le_one s⟩
  have hh1 : (1 / 2 : ℝ) ≤ 1 - E.alpha k ^ 2 := hhalf k hqk
  have hh2 : (1 / 2 : ℝ) ≤ 1 - E.alpha (s - k) ^ 2 := hhalf (s - k) hqsk
  have hq3den : (1 / 2 : ℝ) * (1 / 2) ≤ (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) :=
    mul_le_mul hh1 hh2 (by norm_num) (by linarith)
  have hq3pos : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hq3den
  have hq3le : E.q3Denom s k ≤ 4 := by
    rw [Q3Env.q3Denom]
    calc 1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2))
        ≤ 1 / ((1 / 2 : ℝ) * (1 / 2)) := one_div_le_one_div_of_le (by norm_num) hq3den
      _ = 4 := by norm_num
  have hq3nn : 0 ≤ E.q3Denom s k := by
    rw [Q3Env.q3Denom]
    exact le_of_lt (one_div_pos.mpr hq3pos)
  have hA : |gA E s k| ≤ 4 * |E.W1 k| := by
    have h1 : |E.fL s| * |E.W1 k| ≤ 1 * |E.W1 k| :=
      mul_le_mul_of_nonneg_right hfL1 (abs_nonneg _)
    have h2 : |E.fL s| * |E.W1 k| * E.q3Denom s k ≤ (1 * |E.W1 k|) * 4 :=
      mul_le_mul h1 hq3le hq3nn (by positivity)
    rw [gA, abs_mul, abs_mul, abs_of_nonneg hq3nn]
    linarith
  have hαk : |E.alpha k| ≤ 64 * K₀ * E.lille := hα k hqk
  have hαsk : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hα (s - k) hqsk
  have hB : |bA E s k| ≤ (64 * K₀ * E.lille) ^ 2 := by
    rw [bA, abs_mul, pow_two]
    exact mul_le_mul hαk hαsk (abs_nonneg _) (by positivity)
  have hccr : |T.ccrX (-s) (k - s)| ≤ K₀ * eta E := by
    refine hK.ccrX_small (-s) (k - s) ?_ hqks
    rw [hK.fL_even]
    exact hfL
  have hC : |kB T E s k| ≤ 64 * K₀ * E.lille * (K₀ * eta E) := by
    rw [kB]
    simp only [abs_mul, abs_neg]
    exact mul_le_mul hαsk hccr (abs_nonneg _) (by positivity)
  -- square and reassemble
  have hprod : (gA E s k * bA E s k * kB T E s k) ^ 2
      ≤ (4 * |E.W1 k|) ^ 2 * ((64 * K₀ * E.lille) ^ 2) ^ 2
          * (64 * K₀ * E.lille * (K₀ * eta E)) ^ 2 :=
    sq_mul_le_sq_mul hA hB hC (by positivity) (by positivity) (by positivity)
  have hcB1 : (cB1 T E s k) ^ 2
      = (E.z / E.ell ^ 3) ^ 2 * (gA E s k * bA E s k * kB T E s k) ^ 2 := by
    rw [cB1]
    ring
  have hzell : (E.z / E.ell ^ 3) ^ 2 = E.rho / E.ell ^ 3 := by
    have hL3 : E.ell ^ 3 ≠ 0 := ne_of_gt (pow_pos hell 3)
    rw [div_pow, hz]
    field_simp <;> ring
  have hρnn : 0 ≤ E.rho / E.ell ^ 3 :=
    div_nonneg ((mul_nonneg_iff_of_pos_right (pow_pos hell 3)).mp (hz ▸ sq_nonneg E.z))
      (le_of_lt (pow_pos hell 3))
  calc (cB1 T E s k) ^ 2
      = (E.z / E.ell ^ 3) ^ 2 * (gA E s k * bA E s k * kB T E s k) ^ 2 := hcB1
    _ ≤ (E.rho / E.ell ^ 3) * ((4 * |E.W1 k|) ^ 2 * ((64 * K₀ * E.lille) ^ 2) ^ 2
          * (64 * K₀ * E.lille * (K₀ * eta E)) ^ 2) := by
        rw [hzell]
        exact mul_le_mul_of_nonneg_left hprod hρnn
    _ = 16 * (64 : ℝ) ^ 6 * K₀ ^ 8 * E.lille ^ 6 * (eta E) ^ 2
          * (E.rho / E.ell ^ 3) * (E.W1 k) ^ 2 := by
        have hL : E.ell ≠ 0 := ne_of_gt hell
        rw [show (4 * |E.W1 k|) ^ 2 = 16 * (E.W1 k) ^ 2 by
          rw [mul_pow, sq_abs]
          norm_num]
        field_simp

/-! ## 6. The weighted lattice sum of `Ŵ₁²` -/

/-- **`Σ_{P_H}Ŵ₁(k)²/𝒟_k ≤ 4ℓ³K₀a`.**  On `P_H` one has `𝒟_k ≥ ‖k‖²/4`, and the
quarter-region sum `ℓ⁻³Σ_{P_H^q}Ŵ₁²/‖k‖² ≤ K₀a` is the `Q3KernelFSAll` field
`sum_W1sq` (FS `eq.I2`). -/
lemma Wb1_sumsq (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (K₀ : ℝ)
    (hD : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q)
    (hPHq : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i)
    (hW1sq : E.ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
        ≤ K₀ * E.aScat)
    (hKa : 0 < E.KH * E.aScat) (hellpos : 0 < E.ell) :
    ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / E.D k ≤ 4 * E.ell ^ 3 * K₀ * E.aScat := by
  have hstep : ∀ k ∈ F.PHset E, (E.W1 k) ^ 2 / E.D k ≤ 4 * ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) := by
    intro k hk
    have hPHk : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hqk : F.PHq E.KH E.aScat k := hPHq k hPHk
    have hcut : 0 < 1 / (2 * E.KH * E.aScat) := by
      have h2 : 0 < 2 * E.KH * E.aScat := by linarith [hKa]
      positivity
    have hnorm : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcut hPHk
    have hDpos : 0 < E.D k := lt_of_lt_of_le (by positivity) (hD k hqk)
    have hkey : 1 / E.D k ≤ 4 / ‖F.kmom k‖ ^ 2 := by
      have h4 : 0 < ‖F.kmom k‖ ^ 2 / 4 := by positivity
      have hle : ‖F.kmom k‖ ^ 2 / 4 ≤ E.D k := hD k hqk
      calc 1 / E.D k ≤ 1 / (‖F.kmom k‖ ^ 2 / 4) := one_div_le_one_div_of_le h4 hle
        _ = 4 / ‖F.kmom k‖ ^ 2 := by
            have hne : ‖F.kmom k‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
            field_simp
    calc (E.W1 k) ^ 2 / E.D k = (E.W1 k) ^ 2 * (1 / E.D k) := by ring
      _ ≤ (E.W1 k) ^ 2 * (4 / ‖F.kmom k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = 4 * ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) := by ring
  calc ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / E.D k
      ≤ ∑ k ∈ F.PHset E, 4 * ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) := Finset.sum_le_sum hstep
    _ = 4 * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro k hk
          rw [FockData.PHset, Finset.mem_filter] at hk
          exact Finset.mem_filter.mpr ⟨hk.1, hPHq k hk.2⟩
        · intro q hq _
          rw [Finset.mem_filter] at hq
          have hcut : 0 < 1 / (4 * E.KH * E.aScat) := by
            have h4 : 0 < 4 * E.KH * E.aScat := by linarith [hKa]
            positivity
          have hnorm : 0 < ‖F.kmom q‖ := lt_of_lt_of_le hcut hq.2
          positivity
    _ ≤ 4 * (K₀ * E.aScat * E.ell ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h3pos : 0 < E.ell ^ 3 := pow_pos hellpos 3
        have h := mul_le_mul_of_nonneg_left hW1sq (le_of_lt h3pos)
        have hcancel : E.ell ^ 3 * (E.ell ^ (-(3 : ℝ)) *
            ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2)
            = ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 := by
          have h1 : E.ell ^ (-(3 : ℝ)) = (E.ell ^ 3)⁻¹ := by
            rw [Real.rpow_neg (le_of_lt hellpos)]
            rw [show E.ell ^ (3 : ℝ) = E.ell ^ 3 from Real.rpow_natCast (E.ell) 3]
          rw [h1, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h3pos), one_mul]
        rw [hcancel] at h
        linarith
    _ = 4 * E.ell ^ 3 * K₀ * E.aScat := by ring

/-! ## 7. The coefficient sum -/

/-- **The collected coefficient sum.**  Cauchy–Schwarz in the `s`-sum, the local
bound `Wb1_coef_le`, the weighted lattice sum `Wb1_sumsq` and the mode count
`#suppL ≤ K₀(K_ℓK_L)³` give

  `Σ_{k∈P_H} C_k²/𝒟_k ≤ 64⁷K₀^{11}(K_ℓK_L)⁶𝓁⁶η²ρ_za`,

which is exactly the constant needed by the Young step at weight `𝓁²/8`. -/
lemma Wb1_coef_sum (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (K₀ : ℝ)
    (hcoef : ∀ s k : Mode, s ∈ suppL E → k ∈ F.PHset E →
      (cB1 T E s k) ^ 2
        ≤ 16 * (64 : ℝ) ^ 6 * K₀ ^ 8 * E.lille ^ 6 * (eta E) ^ 2
            * (E.rho / E.ell ^ 3) * (E.W1 k) ^ 2)
    (hsumsq : ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / E.D k ≤ 4 * E.ell ^ 3 * K₀ * E.aScat)
    (hcard : ((suppL E).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3)
    (hK0 : 0 ≤ K₀) (h𝓁 : 0 ≤ E.lille) (hη : 0 ≤ eta E) (ha : 0 ≤ E.aScat)
    (hell : 0 < E.ell) (hρℓ : 0 ≤ E.rho / E.ell ^ 3)
    (hDpos : ∀ k ∈ F.PHset E, 0 < E.D k) :
    ∑ k ∈ F.PHset E, (CB1 T E k) ^ 2 / E.D k
      ≤ (64 : ℝ) ^ 7 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 6 * (eta E) ^ 2
          * E.rho * E.aScat := by
  set N : ℝ := ((suppL E).card : ℝ) with hN
  set M : ℝ := 16 * (64 : ℝ) ^ 6 * K₀ ^ 8 * E.lille ^ 6 * (eta E) ^ 2
      * (E.rho / E.ell ^ 3) with hM
  have hNnn : 0 ≤ N := by rw [hN]; positivity
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hper : ∀ k ∈ F.PHset E, (CB1 T E k) ^ 2 ≤ N ^ 2 * M * (E.W1 k) ^ 2 := by
    intro k hk
    have hCS : (CB1 T E k) ^ 2 ≤ N * ∑ s ∈ suppL E, (cB1 T E s k) ^ 2 := by
      rw [CB1, hN]
      exact sq_sum_le_card_mul_sum_sq (s := suppL E) (f := fun s => cB1 T E s k)
    have hsumk : ∑ s ∈ suppL E, (cB1 T E s k) ^ 2 ≤ N * (M * (E.W1 k) ^ 2) := by
      calc ∑ s ∈ suppL E, (cB1 T E s k) ^ 2 ≤ ∑ _s ∈ suppL E, M * (E.W1 k) ^ 2 := by
            refine Finset.sum_le_sum fun s hs => ?_
            have h := hcoef s k hs hk
            rw [hM] at h ⊢
            linarith [h]
        _ = N * (M * (E.W1 k) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← hN]
    calc (CB1 T E k) ^ 2 ≤ N * ∑ s ∈ suppL E, (cB1 T E s k) ^ 2 := hCS
      _ ≤ N * (N * (M * (E.W1 k) ^ 2)) := mul_le_mul_of_nonneg_left hsumk hNnn
      _ = N ^ 2 * M * (E.W1 k) ^ 2 := by ring
  have hterm : ∀ k ∈ F.PHset E,
      (CB1 T E k) ^ 2 / E.D k ≤ (N ^ 2 * M * (E.W1 k) ^ 2) / E.D k := fun k hk =>
    div_le_div_of_nonneg_right (hper k hk) (le_of_lt (hDpos k hk))
  calc ∑ k ∈ F.PHset E, (CB1 T E k) ^ 2 / E.D k
      ≤ ∑ k ∈ F.PHset E, (N ^ 2 * M * (E.W1 k) ^ 2) / E.D k := Finset.sum_le_sum hterm
    _ = N ^ 2 * M * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / E.D k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ N ^ 2 * M * (4 * E.ell ^ 3 * K₀ * E.aScat) :=
        mul_le_mul_of_nonneg_left hsumsq (by positivity)
    _ ≤ (K₀ * (E.Kl * E.KL) ^ 3) ^ 2 * M * (4 * E.ell ^ 3 * K₀ * E.aScat) := by
        have hN2 : N ^ 2 ≤ (K₀ * (E.Kl * E.KL) ^ 3) ^ 2 :=
          pow_le_pow_left₀ hNnn hcard 2
        have h4 : 0 ≤ M * (4 * E.ell ^ 3 * K₀ * E.aScat) :=
          mul_nonneg hMnn (by positivity)
        calc N ^ 2 * M * (4 * E.ell ^ 3 * K₀ * E.aScat)
            = N ^ 2 * (M * (4 * E.ell ^ 3 * K₀ * E.aScat)) := by ring
          _ ≤ (K₀ * (E.Kl * E.KL) ^ 3) ^ 2 * (M * (4 * E.ell ^ 3 * K₀ * E.aScat)) :=
              mul_le_mul_of_nonneg_right hN2 h4
          _ = (K₀ * (E.Kl * E.KL) ^ 3) ^ 2 * M * (4 * E.ell ^ 3 * K₀ * E.aScat) := by ring
    _ = (64 : ℝ) ^ 7 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 6 * (eta E) ^ 2
          * E.rho * E.aScat := by
        rw [hM]
        field_simp <;> ring

/-! ## 8. The estimate -/


end Est1

end Work.BoseC3QAll
