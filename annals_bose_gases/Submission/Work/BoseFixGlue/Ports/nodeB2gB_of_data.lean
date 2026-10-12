import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Ports.nodeB2gB_of_data` — the §6 port of `Work.BoseBox.nodeB2g_of_data`

The proved BoseBox chapter reduces FS §6 (`lem:LocMatrices`) to two inputs:

    `B2GradingData v h J → B2AprioriWindow v h J' → NodeB2g v h J J'`
    (`Work.BoseBox.nodeB2g_of_data`),

the Lieb–Solovej matrix localisation `Work.UBBInputs3.ls_localisation_band2` doing the
linear algebra (`Mw ∈ [𝓜/4, 𝓜/2]` window, error `(100/Mw²)(|d₁|+4|d₂|) ≤ 8000Kμ²ℓ³𝓜⁻²`), the
recombination clause producing `Φ'`, and FS's placement argument
(`n₀ ≤ C₁·nPlusWindow ≤ 𝓜/2`) upgrading the spectral confinement to the full window `𝓜`.

This file **ports** that proof verbatim into the frozen vocabulary of `Work.BoseBoxFix`:

* `BoxState n (sideAt μ (a v))` (smooth, bosonic, no support condition) with the box-restricted
  word `wordB` and norm `normB` — the repair of the whole-space/box mismatch
  (`BOSE_BOXNODES_LEAD.md` §1);
* `Adm v ε₀ μ` in place of the three separate hypotheses `0 < μ`, `μa³ ≤ ε₀`, `ParamsOK`;
* the hypothesis `0 < normB v μ n Φ` carried explicitly by the corrected data, which is exactly
  the positivity the division by `‖Φ‖²` in the energy identity needs.

The one genuinely new ingredient is **negativity**.  The corrected `B2GradingDataB` demands the
replacement only for windows with `⟨φ,Aφ⟩ < 0` (FS's proof uses precisely that, and for
`⟨φ,Aφ⟩ ≥ 0` the old clause asked for an unrelated state).  So the Lieb–Solovej vector `φ` must
be *shown* to be negative:

    ⟨φ,Aφ⟩ ≤ ⟨ψ,Aψ⟩ + 8000Kμ²ℓ³𝓜⁻² ≤ ℓ³Θ(a v,J,μ) + ℓ³(Θ(a v,J',μ) − Θ(a v,J,μ)) = ℓ³Θ(a v,J',μ),

using the Lieb–Solovej error estimate `exists_lsError_paid` (the error is paid by the a-priori
threshold gap `J' − J`), FS's threshold identity `theta_gap`, and the strict negativity
`Θ(a v,J',μ) < 0` for small diluteness (`Theta_neg_of_small`).

Everything else — the error arithmetic `exists_lsError_paid`, `lsError_abs_le`,
`threshold_pays`, `theta_gap`, `exists_KB3_ge`, `exists_place_le_halfM` — is the *proved*
BoseBox arithmetic, reused unchanged (it is stated at general `(a, μ)` and only mentions
`paramsAt`, `sideAt`, `bigM`, `nPlusWindow`, which are the same objects in both vocabularies).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue.Ports

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The threshold is negative for small diluteness

`Theta A J ρ = −4πρ²A(1 − J√(ρA³))`, so at a positive parameter `J` it is strictly negative as
soon as `ρA³` is small enough that `J√(ρA³) < 1`.  This is the fact that turns the Lieb–Solovej
energy bound `⟨φ,Aφ⟩ ≤ ℓ³Θ(a,J',μ)` into the *strict* negativity `⟨φ,Aφ⟩ < 0` that the corrected
recombination clause of `B2GradingDataB` requires. -/

/-- **`Θ(a,J,μ) < 0` for small diluteness `μa³`** (`a > 0`, `J > 0`). -/
lemma Theta_neg_of_small {a J : ℝ} (ha : 0 < a) (hJ : 0 < J) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε → Theta a J μ < 0 := by
  have hJ2 : 0 < 4 * J ^ 2 := by positivity
  have hminpos : 0 < min (a ^ 3) 1 := lt_min (by positivity) one_pos
  have hprod : 0 < min (a ^ 3) 1 * (1 / (4 * J ^ 2)) :=
    mul_pos hminpos (one_div_pos.mpr hJ2)
  refine ⟨min 1 (min (a ^ 3) 1 * (1 / (4 * J ^ 2))), lt_min one_pos hprod, ?_⟩
  intro μ hμ hle
  have hden : 0 ≤ 1 / (4 * J ^ 2) := (one_div_pos.mpr hJ2).le
  have hkey : μ * a ^ 3 ≤ 1 / (4 * J ^ 2) := by
    refine le_trans hle (le_trans (min_le_right _ _) ?_)
    calc min (a ^ 3) 1 * (1 / (4 * J ^ 2))
        ≤ 1 * (1 / (4 * J ^ 2)) := mul_le_mul_of_nonneg_right (min_le_right _ _) hden
      _ = 1 / (4 * J ^ 2) := by ring
  have ht : 0 < μ * a ^ 3 := by positivity
  have hsq : μ * a ^ 3 ≤ (1 / (2 * J)) ^ 2 := by
    have h : (2 * J) ^ 2 = 4 * J ^ 2 := by ring
    rw [div_pow, one_pow, h]
    exact hkey
  have hsqrt : √(μ * a ^ 3) ≤ 1 / (2 * J) := by
    have h1 : √(μ * a ^ 3) ≤ √((1 / (2 * J)) ^ 2) := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hJs : J * √(μ * a ^ 3) ≤ 1 / 2 := by
    have h2 : J * √(μ * a ^ 3) ≤ J * (1 / (2 * J)) := mul_le_mul_of_nonneg_left hsqrt hJ.le
    have h3 : J * (1 / (2 * J)) = 1 / 2 := by field_simp
    linarith [h2, h3.le, h3.ge]
  have hcoef : 0 < 4 * π * μ ^ 2 * a := by positivity
  have hbr : 0 < 1 - J * √(μ * a ^ 3) := by linarith
  have hpos : 0 < 4 * π * μ ^ 2 * a * (1 - J * √(μ * a ^ 3)) := mul_pos hcoef hbr
  rw [Theta]
  linarith

/-! ## 2. The §6 reduction -/

theorem nodeB2gB_of_data {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {J J' : ℝ}
    (hav : 0 < BoseGases.a v) (hlhy : Work.UBB.lhyC ≤ J) (hJJ : J < J')
    (hg : Work.BoseBoxFix.B2GradingDataB v h J) (ha : Work.BoseBoxFix.B2AprioriWindowB v h J') :
    Work.BoseBoxFix.NodeB2gB v h J J' := by
  obtain ⟨Kg, εg, hKg, hεg, hgd⟩ := hg
  obtain ⟨C₁, εa, hC₁, hεa, haw⟩ := ha
  have hlhypos : 0 < lhyC := by
    dsimp [lhyC]
    positivity
  have hJpos : 0 < J := lt_of_lt_of_le hlhypos hlhy
  have hJ'pos : 0 < J' := lt_trans hJpos hJJ
  obtain ⟨εs, hεs, hpaid⟩ := exists_lsError_paid (a := a v) hav hKg hJJ
  obtain ⟨εw, hεw, hplace⟩ := exists_place_le_halfM (a := a v) hav hC₁
  obtain ⟨εk, hεk, hkb⟩ := exists_KB3_ge (a := a v) hav hJ'pos
  obtain ⟨εj, hεj, hjb⟩ := exists_KB3_ge (a := a v) hav hJpos
  obtain ⟨εθ, hεθ, hth⟩ := Theta_neg_of_small (a := a v) hav hJ'pos
  refine ⟨8000 * Kg,
    min (min εg εa) (min εs (min εw (min (min εk εj) (min 1 εθ)))), by positivity,
    lt_min (lt_min hεg hεa)
      (lt_min hεs (lt_min hεw (lt_min (lt_min hεk hεj) (lt_min one_pos hεθ)))), ?_⟩
  intro μ hAdm n Φ hnorm hlow
  obtain ⟨hμ, hsmall, hpar⟩ := hAdm
  have ht1 : μ * (a v) ^ 3 ≤ εg :=
    le_trans hsmall (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2 : μ * (a v) ^ 3 ≤ εa :=
    le_trans hsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht3 : μ * (a v) ^ 3 ≤ εs :=
    le_trans hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht4 : μ * (a v) ^ 3 ≤ εw :=
    le_trans hsmall (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have ht5 : μ * (a v) ^ 3 ≤ εk :=
    le_trans hsmall (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_left _ _)))))
  have ht6 : μ * (a v) ^ 3 ≤ εj :=
    le_trans hsmall (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _)))))
  have ht7 : μ * (a v) ^ 3 ≤ εθ :=
    le_trans hsmall (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))))
  obtain ⟨nn, A, ψv, Mw, hMw3, hMwlo, hMwhi, hMwnn, hAsupp, hAherm, hψsupp, hψnorm,
    hE, hband, hdv, hrec⟩ := hgd μ ⟨hμ, ht1, hpar⟩ (hjb μ hμ ht6) n Φ hnorm hlow
  obtain ⟨n₀, h0, h1, φ, hsupp, hφnorm, hineq⟩ :=
    ls_localisation_band2 A nn Mw ψv hMw3 hMwnn hAsupp hAherm hψsupp hψnorm hband
  -- (0) positivity of the box side, of the norm and of the matrix window
  have hℓpos : 0 < sideAt μ (a v) := sideAt_pos hμ hav
  have hMpos : 0 < bigM (paramsAt μ (a v)) (a v) μ := bigM_pos_of_params hμ hav
  have hN : 0 ≤ normB v μ n Φ := by
    simp only [normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg (fun x => sq_nonneg _)
  -- (1) the Lieb–Solovej error, absolute form
  have hdv5 : |dk A nn ψv 1| + 4 * |dk A nn ψv 2|
      ≤ 5 * (Kg * μ ^ 2 * sideAt μ (a v) ^ 3) :=
    by linarith [hdv, abs_nonneg (dk A nn ψv 1), abs_nonneg (dk A nn ψv 2)]
  have hlerr := lsError_abs_le (ℓ := sideAt μ (a v))
    (𝓜 := bigM (paramsAt μ (a v)) (a v) μ) hMpos hMwlo hdv5
  have hineq' : qform A (iRange nn) φ φ ≤ qform A (iRange nn) ψv ψv
      + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2 :=
    by linarith [hineq, hlerr]
  -- (2) the energy identity reads the lowness of `Φ` at the threshold `J`
  have hψle : qform A (iRange nn) ψv ψv ≤ sideAt μ (a v) ^ 3 * Theta (a v) J μ := by
    have hmul : qform A (iRange nn) ψv ψv * normB v μ n Φ
        ≤ sideAt μ (a v) ^ 3 * Theta (a v) J μ * normB v μ n Φ := by
      rw [hE]
      exact hlow
    exact le_of_mul_le_mul_right hmul hnorm
  -- (3) the threshold gap pays the Lieb–Solovej error, hence `⟨φ,Aφ⟩ < 0`
  have hpay : 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
      ≤ sideAt μ (a v) ^ 3 * 4 * π * μ ^ 2 * (a v) * (J' - J)
          * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    threshold_pays hμ.le hℓpos.le (hpaid μ hμ ht3)
  have hΘsplit : sideAt μ (a v) ^ 3 * Theta (a v) J' μ
      = sideAt μ (a v) ^ 3 * Theta (a v) J μ
        + sideAt μ (a v) ^ 3 * 4 * π * μ ^ 2 * (a v) * (J' - J)
            * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    by linarith [theta_gap (a v) (sideAt μ (a v)) μ J J']
  have hΘJ' : sideAt μ (a v) ^ 3 * Theta (a v) J' μ < 0 :=
    mul_neg_of_pos_of_neg (pow_pos hℓpos 3) (hth μ hμ ht7)
  have hφneg : qform A (iRange nn) φ φ < 0 := by
    have h2 : qform A (iRange nn) φ φ ≤ sideAt μ (a v) ^ 3 * Theta (a v) J' μ :=
      by linarith [hineq', hψle, hpay, hΘsplit]
    exact lt_of_le_of_lt h2 hΘJ'
  -- (4) the recombination at the (negative) Lieb–Solovej window vector
  obtain ⟨Φ', hnorm', hword', hspec', hlowwin'⟩ := hrec n₀ φ h0 h1 hsupp hφnorm hφneg
  -- (5) the word of the replacement, against `Φ`
  have hword : wordB v h μ n Φ' ≤ wordB v h μ n Φ
      + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
          * normB v μ n Φ := by
    have h1 := mul_le_mul_of_nonneg_right hineq' hN
    have h2 : (qform A (iRange nn) ψv ψv
          + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2)
          * normB v μ n Φ
        = wordB v h μ n Φ
          + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
              * normB v μ n Φ := by
      calc (qform A (iRange nn) ψv ψv
            + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2)
            * normB v μ n Φ
          = qform A (iRange nn) ψv ψv * normB v μ n Φ
            + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
                * normB v μ n Φ := by ring
        _ = wordB v h μ n Φ
            + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
                * normB v μ n Φ := by rw [hE]
    linarith [hword', h1, h2]
  -- (6) `Φ'` is low at the raised threshold `J'`
  have hlow' : IsLowB v h J' μ n Φ' := by
    have hgoal : wordB v h μ n Φ
          + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
              * normB v μ n Φ
        ≤ sideAt μ (a v) ^ 3 * Theta (a v) J' μ * normB v μ n Φ := by
      have h2 : 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
              * normB v μ n Φ
          ≤ (sideAt μ (a v) ^ 3 * Theta (a v) J' μ - sideAt μ (a v) ^ 3 * Theta (a v) J μ)
              * normB v μ n Φ := by
        rw [theta_gap (a v) (sideAt μ (a v)) μ J J']
        exact mul_le_mul_of_nonneg_right hpay hN
      nlinarith [hlow, h2]
    have hfinal : wordB v h μ n Φ'
        ≤ sideAt μ (a v) ^ 3 * Theta (a v) J' μ * normB v μ n Φ' := by
      rw [hnorm']
      linarith [hword, hgoal]
    exact hfinal
  -- (7) FS's placement of the Lieb–Solovej window
  have hNpos' : 0 < normB v μ n Φ' := by
    rw [hnorm']
    exact hnorm
  have hcn := haw μ ⟨hμ, ht2, hpar⟩ (hkb μ hμ ht5) n Φ' hNpos' hlow'
  have hinst : (n₀ : ℝ) * normB v μ n Φ'
      ≤ (C₁ * nPlusWindow (paramsAt μ (a v)) μ (a v)) * normB v μ n Φ' :=
    le_trans hlowwin' hcn
  have hn₀ : (n₀ : ℝ) ≤ C₁ * nPlusWindow (paramsAt μ (a v)) μ (a v) :=
    le_of_mul_le_mul_right hinst hNpos'
  have hplace' := hplace μ hμ ht4
  have hwin : (n₀ : ℝ) + (Mw : ℝ) ≤ bigM (paramsAt μ (a v)) (a v) μ := by
    linarith [hn₀, hplace', hMwhi]
  exact ⟨Φ', hlow', hnorm', hword, hspec' _ hwin⟩

end Work.BoseFixGlue.Ports
