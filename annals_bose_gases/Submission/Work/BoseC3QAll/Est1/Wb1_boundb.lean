import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseC3QAll.Est1.Wb1_bound
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
theorem Wb1_bound (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
        (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          - (Work.BoseC3QAll.Est1.costB2 K₀ E) * F.normSq Φ
              - (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
            ≤ F.qw Φ (Work.BoseC3QAll.Est1.Wb1 F T E) := by
  obtain ⟨t₁, ht₁, H₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, H₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK Φ hΦ
  have hle₁ : hv.t ≤ t₁ := le_trans htle (min_le_left _ _)
  have hle₂ : hv.t ≤ t₂ := le_trans htle (min_le_right _ _)
  obtain ⟨_hαeven, _hB2, hhalf, hα, hD⟩ := H₁ F T E hv hle₁ hb hK
  obtain ⟨hPHq, hsk, -⟩ := H₂ F T E hv hle₂ hb hK
  -- scalar facts of the parameter point
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hKa : 0 < E.KH * E.aScat := mul_pos hKH ha
  have hℓpos : 0 < E.ell := ell_pos E hv
  have hℓ3 : 0 < E.ell ^ 3 := pow_pos hℓpos 3
  have h𝓁pos : 0 < E.lille := lille_pos E hv
  have h𝓁nn : 0 ≤ E.lille := le_of_lt h𝓁pos
  have hηnn : 0 ≤ eta E := by
    rw [eta, Mt]
    refine Real.rpow_nonneg (mul_nonneg ?_ h𝓁nn) _
    exact Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hv.one_le_Kl)) _
  have hK0 : 0 ≤ K₀ := by
    by_contra hneg
    have hneg' : K₀ < 0 := not_le.mp hneg
    have hcp := hK.count_PL
    have hcard : (0 : ℝ) ≤ (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hKl : 0 < E.Kl := by linarith [hv.one_le_Kl]
    have hKL : 0 < E.KL := by linarith [hv.one_le_KL]
    have hpos : 0 < (E.Kl * E.KL) ^ 3 := pow_pos (mul_pos hKl hKL) 3
    nlinarith [hcp, hcard, mul_neg_of_neg_of_pos hneg' hpos]
  have hρnn : 0 ≤ E.rho := le_of_lt (rho_pos E hv)
  have hρℓ : 0 ≤ E.rho / E.ell ^ 3 := div_nonneg hρnn (le_of_lt hℓ3)
  have hann : 0 ≤ E.aScat := le_of_lt ha
  have hDnn : ∀ q : Mode, F.PHq E.KH E.aScat q → 0 ≤ E.D q := fun q hq =>
    le_trans (by positivity) (hD q hq)
  have hDpos : ∀ k ∈ F.PHset E, 0 < E.D k := by
    intro k hk
    have hPHk : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hcut : 0 < 1 / (2 * E.KH * E.aScat) := by positivity
    have hnorm : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcut hPHk
    have h1 : 0 < ‖F.kmom k‖ ^ 2 / 4 := by positivity
    have h2 := hD k (hPHq k hPHk)
    linarith
  -- the coefficient facts
  have hcoef := Wb1_coef_le F T E K₀ hK hα hhalf hPHq hsk (zsq_eq E hv) hK0 h𝓁nn hηnn hℓpos
  have hsumsq := Wb1_sumsq F T E K₀ hD hPHq hK.sum_W1sq hKa hℓpos
  have hcsum := Wb1_coef_sum F T E K₀ hcoef hsumsq hK.count_PL hK0 h𝓁nn hηnn hann
    hℓpos hρℓ hDpos
  have hres := Wb1_reserve F E Φ hPHq hDnn
  -- expand the word
  rw [Wb1_qw_eq F T E Φ]
  set A : ℝ := ∑ k ∈ F.PHset E, ((E.lille ^ 2 / 8) * E.D k) * F.bp (F.bNumOp E.alpha k Φ) Φ
    with hAdef
  set B : ℝ := ∑ k ∈ F.PHset E, ((E.lille ^ 2 / 8) * E.D k)⁻¹ * (CB1 T E k) ^ 2 with hBdef
  have hsplit : ∑ k ∈ F.PHset E, (((E.lille ^ 2 / 8) * E.D k) * F.bp (F.bNumOp E.alpha k Φ) Φ
        + ((E.lille ^ 2 / 8) * E.D k)⁻¹ * (CB1 T E k) ^ 2 * F.normSq Φ)
      = A + B * F.normSq Φ := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hAdef, hBdef]
  have hsum_ge : -(A + B * F.normSq Φ)
      ≤ ∑ k ∈ F.PHset E, (2 * CB1 T E k) * F.bp (F.bOp E.alpha k Φ) Φ := by
    rw [← hsplit, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun k hk => Wb1_perk F T E Φ k (hDpos k hk) h𝓁pos
  have hA_le : A ≤ (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
    have hAeq : A = (E.lille ^ 2 / 8) *
        (∑ k ∈ F.PHset E, E.D k * F.bp (F.bNumOp E.alpha k Φ) Φ) := by
      rw [hAdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hAeq]
    exact mul_le_mul_of_nonneg_left hres (by positivity)
  have hB_le : B ≤ costB2 K₀ E := by
    have hBeq : B = (8 / E.lille ^ 2) *
        (∑ k ∈ F.PHset E, (CB1 T E k) ^ 2 / E.D k) := by
      rw [hBdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hDk : E.D k ≠ 0 := ne_of_gt (hDpos k hk)
      have h𝓁ne : E.lille ≠ 0 := ne_of_gt h𝓁pos
      field_simp
    rw [hBeq, costB2]
    calc (8 / E.lille ^ 2) * (∑ k ∈ F.PHset E, (CB1 T E k) ^ 2 / E.D k)
        ≤ (8 / E.lille ^ 2) * ((64 : ℝ) ^ 7 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6
            * E.lille ^ 6 * (eta E) ^ 2 * E.rho * E.aScat) :=
          mul_le_mul_of_nonneg_left hcsum (by positivity)
      _ = 512 * (64 : ℝ) ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4
            * (eta E) ^ 2 * E.rho * E.aScat := by
          have h𝓁ne : E.lille ≠ 0 := ne_of_gt h𝓁pos
          field_simp
          ring
  have hmul : B * F.normSq Φ ≤ costB2 K₀ E * F.normSq Φ :=
    mul_le_mul_of_nonneg_right hB_le (F.normSq_nonneg Φ)
  linarith [hsum_ge, hA_le, hmul]

end Est1

end Work.BoseC3QAll
