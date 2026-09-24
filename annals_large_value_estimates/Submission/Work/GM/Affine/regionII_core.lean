import Mathlib
import Submission.Work.GM.Affine.regionII_to_winmass
import Submission.Work.GM.Affine.WinMass_core

/-!
# GM §9, region II: the core estimate (`Work.GM.Affine.regionII_core`)

`regionII_core` is the region-II part of GM's Lemma 9.2 / Proposition 9.1 (verbatim as
requested): for `f ≥ 0` continuous supported in `[1/C₀,C₀]`, with the §9 Fourier-decay
hypothesis and `Λ ≤ 16 c(2,1) T³ ∫f`, and for all `1 ≤ Mbig ≤ T⁴`, `M₃ ≤ C₃ Mbig`,
`M₁,M₂ ≤ Mbig`,

`∫_{T^η M₁/M₃ < |ξ| ≤ T⁶} ‖ĝ(ξ)‖² dξ ≤ C' T^δ ( Mbig⁶ (∫f)² + Mbig² ‖f‖₂(∫Gfun²)^{1/2} + Mbig⁴ ∫f² )`,

`η = min δ 1 / 2`.

## Proof (this file, complete modulo the imported theorem `WinMass_core`)

Two inputs, each applied with the exponent `δ/2` so that the two `T^{δ/2}` losses multiply
into the target's `T^δ`:

* `Work.GM.Affine.regionII_to_winmass` (**PROVED** in the workspace) — the region-II reduction
  (GM (9.6')): `∫_region ‖ĝ‖² ≤ C₁ T^{δ/2} (M₁+M₃) WinMass f M₂ M₃`.  The target's region
  (`η = min δ 1 / 2`) is contained in the one with `min (δ/2) 1 / 2`, which is what is used;
* `Work.GM.Affine.WinMass_core` — the window-mass bound (GM (9.7)–(9.8)),
  being finished by the project lead's direct route (`WINMASS_ROUTE.md`)
  `WinMass f M₂ M₃ ≤ C₂ T^{δ/2} (M₂ ‖f‖₂ (∫Gfun²)^{1/2} + M₂² M₃ ∫f²)`.

All that is left is arithmetic: with `Mbig ≥ 1`, `M₁,M₂ ≤ Mbig`, `M₃ ≤ C₃ Mbig` one has
`(M₁+M₃)(M₂S + M₂²M₃V) ≤ 2C₃²(Mbig²S + Mbig⁴V)`, which turns the product of the two inputs
into the target bracket; the extra non-negative term `Mbig⁶(∫f)²` is free.

**The one remaining input is exactly the window-mass bound `WinMass_core`** (whose remaining gap is the only one left in this module's dependency closure).  Note for whoever proves
it (see `NOTES_Mellin_route_regionII.md`, `NOTES_hprof_sq_dilate_bound_eps_FALSE.md`): the
route through the *decay-free* profile/dilate bound (`hprof_dilate_sq_eps`,
`Hprof_sq_dilate_bound`, `Hprof_sq_cheap`) is **DEAD** — those statements are FALSE
(resonant-boost counterexample, Kronecker).  `WinMass_core` is now being finished by the project lead's direct route
(`WINMASS_ROUTE.md`: two-sided smoothing + `‖f̃‖₂ ≤ ‖f‖₂`, no one-sided local-average crux);
my parallel Poisson-chain tiles (`hsum_window_to_Gfun`, `Hsum_le_C3_of_weighted_K_ge1`,
`WinMass_small_M2`, `winmass_core_of_tiles`) are proved but no longer needed for this.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ## Pure arithmetic of the assembly -/

private lemma regionII_core_sup_arith {M₁ M₃ Mbig M₂ C₃ S V : ℝ}
    (hMb1 : 1 ≤ Mbig) (hC₃1 : 1 ≤ C₃) (hM₃1 : 1 ≤ M₃) (hM₂0 : 0 < M₂)
    (hM₁ : M₁ ≤ Mbig) (hM₂ : M₂ ≤ Mbig) (hM₃ : M₃ ≤ C₃ * Mbig)
    (hM₁0 : 0 < M₁) (hS : 0 ≤ S) (hV : 0 ≤ V) :
    (M₁ + M₃) * (M₂ * S + M₂ ^ 2 * M₃ * V)
      ≤ 2 * C₃ ^ 2 * (Mbig ^ 2 * S + Mbig ^ 4 * V) := by
  have hMb0 : (0:ℝ) < Mbig := lt_of_lt_of_le zero_lt_one hMb1
  have hMb2nn : (0:ℝ) ≤ Mbig ^ 2 := sq_nonneg _
  have hsum : M₁ + M₃ ≤ (1 + C₃) * Mbig := by nlinarith
  have hcoef1 : (M₁ + M₃) * M₂ ≤ 2 * C₃ ^ 2 * Mbig ^ 2 := by
    have h3 : (M₁ + M₃) * M₂ ≤ (1 + C₃) * Mbig * Mbig :=
      mul_le_mul hsum hM₂ (le_of_lt hM₂0) (by positivity)
    have h5 : (1 + C₃) ≤ 2 * C₃ ^ 2 := by nlinarith
    have h4 : (1 + C₃) * (Mbig * Mbig) ≤ (2 * C₃ ^ 2) * (Mbig * Mbig) :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    linarith
  have hcoef2 : (M₁ + M₃) * M₂ ^ 2 * M₃ ≤ 2 * C₃ ^ 2 * Mbig ^ 4 := by
    have h2 : M₂ ^ 2 ≤ Mbig ^ 2 := by nlinarith
    have h3 : (M₁ + M₃) * M₂ ^ 2 ≤ ((1 + C₃) * Mbig) * Mbig ^ 2 :=
      mul_le_mul hsum h2 (sq_nonneg M₂) (by positivity)
    have h4 : (M₁ + M₃) * M₂ ^ 2 * M₃ ≤ (((1 + C₃) * Mbig) * Mbig ^ 2) * (C₃ * Mbig) :=
      mul_le_mul h3 hM₃ (le_of_lt (lt_of_lt_of_le (by norm_num) hM₃1)) (by positivity)
    have h5 : (1 + C₃) * C₃ ≤ 2 * C₃ ^ 2 := by nlinarith
    have h7 : (0:ℝ) ≤ Mbig ^ 4 := by positivity
    have h6 : ((1 + C₃) * C₃) * Mbig ^ 4 ≤ (2 * C₃ ^ 2) * Mbig ^ 4 :=
      mul_le_mul_of_nonneg_right h5 h7
    linarith
  have hexp : (M₁ + M₃) * (M₂ * S + M₂ ^ 2 * M₃ * V)
      = (M₁ + M₃) * M₂ * S + (M₁ + M₃) * M₂ ^ 2 * M₃ * V := by ring
  rw [hexp]
  have hA : (M₁ + M₃) * M₂ * S ≤ 2 * C₃ ^ 2 * Mbig ^ 2 * S :=
    mul_le_mul_of_nonneg_right hcoef1 hS
  have hB : (M₁ + M₃) * M₂ ^ 2 * M₃ * V ≤ 2 * C₃ ^ 2 * Mbig ^ 4 * V :=
    mul_le_mul_of_nonneg_right hcoef2 hV
  linarith

/-! ## Integrability helpers -/

/-- `‖ĝ‖²` is integrable on `[-T⁶,T⁶]` (a set of finite measure, `‖ĝ‖` bounded by `∫ gSum`). -/
private lemma integrableOn_ghat_sq_Icc {K M₁ M₂ M₃ T : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) :
    IntegrableOn (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) (Set.Icc (-(T ^ 6)) (T ^ 6)) := by
  have hcont : Continuous (fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ) :=
    continuous_ghat_of_SuppHyp hK hM₁ hM₂ hM₃ hf hcs
  have hfin : volume (Set.Icc (-(T ^ 6)) (T ^ 6)) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine IntegrableOn.of_bound hfin ?_ ((∫ u, gSum K M₁ M₂ M₃ f u) ^ 2) ?_
  · exact ((hcont.measurable.norm).pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ξ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_ghat_le_integral_gSum hfnn ξ) 2

/-- Set-integral monotonicity for a nonnegative integrand. -/
private lemma setIntegral_mono_of_subset_sup {g : ℝ → ℝ} (hnn : ∀ x, 0 ≤ g x)
    {s t : Set ℝ} (hst : s ⊆ t) (hint : IntegrableOn g t) :
    ∫ x in s, g x ≤ ∫ x in t, g x :=
  setIntegral_mono_set hint (Filter.Eventually.of_forall hnn)
    (Filter.Eventually.of_forall hst)

/-! ## The target -/

theorem regionII_core {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 +
            Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
  have hδ2 : (0:ℝ) < δ / 2 := by linarith
  obtain ⟨C₁, hC₁pos, hA⟩ := regionII_to_winmass hC₀ hK hT₀ hC₃ c (δ / 2) hδ2
  obtain ⟨C₂, hC₂pos, hB⟩ := WinMass_core hC₀ hT₀ hC₃ c (δ / 2) hδ2
  refine ⟨2 * C₁ * C₂ * C₃ ^ 2 + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hM₃0 : (0:ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  have hcs : HasCompactSupport f := hcs_of_SuppHyp hsupp
  set U : ℝ := ∫ u, f u with hU
  set V : ℝ := ∫ u, (f u) ^ 2 with hV
  set W : ℝ := ∫ u, (Gfun C₀ T M₂ f u) ^ 2 with hW
  set S : ℝ := (∫ u, (f u) ^ 2) ^ (1/2:ℝ) * (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) with hS
  have hUnn : 0 ≤ U := by rw [hU]; exact integral_nonneg hfnn
  have hVnn : 0 ≤ V := by rw [hV]; exact integral_nonneg (fun u => sq_nonneg _)
  have hWnn : 0 ≤ W := by rw [hW]; exact integral_nonneg (fun u => sq_nonneg _)
  have hSnn : 0 ≤ S := by
    rw [hS]; exact mul_nonneg (Real.rpow_nonneg hVnn _) (Real.rpow_nonneg hWnn _)
  have hWinn : 0 ≤ WinMass f M₂ M₃ := WinMass_nonneg f M₂ M₃
  have hA' := hA T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hB' := hB T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₂0 hM₂M
  -- region monotonicity: the target's region lies inside the region used by `hA'`
  have hmin : min (δ / 2) 1 ≤ min δ 1 := min_le_min (by linarith) le_rfl
  have hle : T ^ (min (δ / 2) 1 / 2) * M₁ / M₃ ≤ T ^ (min δ 1 / 2) * M₁ / M₃ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hM₃0)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) (le_of_lt hM₁0)
  have hsub : (Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃))
      ⊆ (Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ (min (δ / 2) 1 / 2) * M₁ / M₃))
            (T ^ (min (δ / 2) 1 / 2) * M₁ / M₃)) := by
    intro ξ hξ
    rw [Set.mem_sdiff] at hξ ⊢
    refine ⟨hξ.1, fun h => hξ.2 ?_⟩
    exact ⟨by linarith [h.1, hle], by linarith [h.2, hle]⟩
  have hint : IntegrableOn (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      (Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ (min (δ / 2) 1 / 2) * M₁ / M₃))
            (T ^ (min (δ / 2) 1 / 2) * M₁ / M₃)) :=
    (integrableOn_ghat_sq_Icc hK hM₁0 hM₂0 hM₃0 hf hcs hfnn).mono_set Set.sdiff_subset
  have hmono := setIntegral_mono_of_subset_sup (fun ξ => sq_nonneg _) hsub hint
  -- combine the two inputs
  have hTδeq : T ^ (δ / 2) * T ^ (δ / 2) = T ^ δ := by
    rw [← Real.rpow_add hTpos]; ring_nf
  have harith : (M₁ + M₃) * (M₂ * S + M₂ ^ 2 * M₃ * V)
      ≤ 2 * C₃ ^ 2 * (Mbig ^ 2 * S + Mbig ^ 4 * V) :=
    regionII_core_sup_arith hMb1 hC₃ hM₃1 hM₂0 hM₁M hM₂M hM₃M hM₁0 hSnn hVnn
  have hB'' : WinMass f M₂ M₃ ≤ C₂ * T ^ (δ / 2) * (M₂ * S + M₂ ^ 2 * M₃ * V) := by
    calc WinMass f M₂ M₃
        ≤ C₂ * T ^ (δ / 2) * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
            (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) + M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := hB'
      _ = C₂ * T ^ (δ / 2) * (M₂ * S + M₂ ^ 2 * M₃ * V) := by rw [hS, hV]; ring
  have hmain : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
        \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
        ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ (2 * C₁ * C₂ * C₃ ^ 2) * T ^ δ * (Mbig ^ 2 * S + Mbig ^ 4 * V) := by
    have h1 : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
          \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
          ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ C₁ * T ^ (δ / 2) * ((M₁ + M₃) * WinMass f M₂ M₃) := by
      have hA'' : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min (δ / 2) 1 / 2) * M₁ / M₃))
                (T ^ (min (δ / 2) 1 / 2) * M₁ / M₃)),
            ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          ≤ C₁ * T ^ (δ / 2) * ((M₁ + M₃) * WinMass f M₂ M₃) := by
        calc (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
              \ (Set.Icc (-(T ^ (min (δ / 2) 1 / 2) * M₁ / M₃))
                  (T ^ (min (δ / 2) 1 / 2) * M₁ / M₃)),
              ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
            ≤ C₁ * T ^ (δ / 2) * (M₁ + M₃) * WinMass f M₂ M₃ := hA'
          _ = C₁ * T ^ (δ / 2) * ((M₁ + M₃) * WinMass f M₂ M₃) := by ring
      linarith [hmono, hA'']
    have h2 : C₁ * T ^ (δ / 2) * ((M₁ + M₃) * WinMass f M₂ M₃)
        ≤ C₁ * T ^ (δ / 2) * ((M₁ + M₃) * (C₂ * T ^ (δ / 2) * (M₂ * S + M₂ ^ 2 * M₃ * V))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hB'' (by positivity : (0:ℝ) ≤ M₁ + M₃)
      · positivity
    calc (∫ ξ in _, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ C₁ * T ^ (δ / 2) * ((M₁ + M₃) * WinMass f M₂ M₃) := h1
      _ ≤ C₁ * T ^ (δ / 2) * ((M₁ + M₃) * (C₂ * T ^ (δ / 2) * (M₂ * S + M₂ ^ 2 * M₃ * V))) := h2
      _ = C₁ * C₂ * (T ^ (δ / 2) * T ^ (δ / 2)) *
            ((M₁ + M₃) * (M₂ * S + M₂ ^ 2 * M₃ * V)) := by ring
      _ ≤ C₁ * C₂ * (T ^ (δ / 2) * T ^ (δ / 2)) *
            (2 * C₃ ^ 2 * (Mbig ^ 2 * S + Mbig ^ 4 * V)) := by
          apply mul_le_mul_of_nonneg_left harith; positivity
      _ = (2 * C₁ * C₂ * C₃ ^ 2) * (T ^ (δ / 2) * T ^ (δ / 2)) * (Mbig ^ 2 * S + Mbig ^ 4 * V) := by
          ring
      _ = (2 * C₁ * C₂ * C₃ ^ 2) * T ^ δ * (Mbig ^ 2 * S + Mbig ^ 4 * V) := by rw [hTδeq]
  have hrest : (0:ℝ) ≤ Mbig ^ 6 * U ^ 2 := by positivity
  have hbase : (0:ℝ) ≤ Mbig ^ 2 * S + Mbig ^ 4 * V := by positivity
  have hTδnn : 0 ≤ T ^ δ := Real.rpow_nonneg (le_of_lt hTpos) δ
  have hfin : (2 * C₁ * C₂ * C₃ ^ 2) * T ^ δ * (Mbig ^ 2 * S + Mbig ^ 4 * V)
      ≤ (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ *
          (Mbig ^ 6 * U ^ 2 + Mbig ^ 2 * S + Mbig ^ 4 * V) := by
    have h1 : 2 * C₁ * C₂ * C₃ ^ 2 ≤ 2 * C₁ * C₂ * C₃ ^ 2 + 1 := by linarith
    have h2 : (2 * C₁ * C₂ * C₃ ^ 2) * T ^ δ ≤ (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ := by
      apply mul_le_mul_of_nonneg_right h1 hTδnn
    have h3 : (0:ℝ) ≤ (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ := by positivity
    calc (2 * C₁ * C₂ * C₃ ^ 2) * T ^ δ * (Mbig ^ 2 * S + Mbig ^ 4 * V)
        ≤ (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ * (Mbig ^ 2 * S + Mbig ^ 4 * V) :=
          mul_le_mul_of_nonneg_right h2 hbase
      _ ≤ (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ *
            (Mbig ^ 6 * U ^ 2 + Mbig ^ 2 * S + Mbig ^ 4 * V) := by
          apply mul_le_mul_of_nonneg_left _ h3
          linarith
  calc (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
        \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
        ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ * (Mbig ^ 6 * U ^ 2 + Mbig ^ 2 * S + Mbig ^ 4 * V) :=
        le_trans hmain hfin
    _ = (2 * C₁ * C₂ * C₃ ^ 2 + 1) * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 +
          Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
            (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
          Mbig ^ 4 * ∫ u, (f u) ^ 2) := by rw [hU, hV, hS]; ring

end

end Work.GM.Affine
