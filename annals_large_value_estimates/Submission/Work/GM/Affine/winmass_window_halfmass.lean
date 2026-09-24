import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.winmass_halfmass_core
import Submission.Work.GM.Affine.halfmass_le_profile_sq

/-!
# GM §9: the half-window mass of the periodisation is controlled by a `2/M₃`-window

For `f ≥ 0` continuous with `SuppHyp C₀ f` (`C₀ ≥ 1` fixed) and any `M₂ > 0`, `M₃ > 4`,

  `∫₀^{1/2} Σ'_ℓ ‖Bsum f M₂ (ℓ+u)‖² du ≤ c·M₃ · ∫₀^{2/M₃} Σ'_ℓ ‖Bsum f M₂ (ℓ+u)‖² du`

with `c` depending only on `C₀`.

The proof has two halves, both about `S(u) := Σ'_ℓ ‖Fhat h (ℓ+u)‖²` with
`h := Hprof f M₂ = Σ_{m₂ ∈ R2 M₂} f (·/m₂) ≥ 0` (and `Bsum f M₂ = Fhat h`, `Bsum_eq_Fhat_Hprof`):

* **upper half** (`halfmass_le_profile_sq`): `∫₀^{1/2} S ≤ ∫h²` — the periodisation over a full
  period integrates to `∫ ‖Fhat h‖² = ∫h²` (partition of `ℝ` into unit intervals + Plancherel);
* **lower half** (`winmass_halfmass_core`): `∫₀^{T} S ≥ θ·T·∫h²` for an absolute `θ > 0` and
  every `T ∈ (0,1/2]`, where `T = 2/M₃`; equivalently, the periodisation of `|Fhat h|²` puts a
  fixed fraction of its mass in every `2T`-neighbourhood of the integers, for `h ≥ 0`.

Combining: `∫₀^{1/2} S ≤ ∫h² ≤ (M₃/(2θ))·∫₀^{2/M₃} S`, whence `c = 1/(2θ)`, and the pointwise
identity `Bsum f M₂ = Fhat (Hprof f M₂)` converts `S` into the `Bsum`-sum of the statement.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem winmass_window_halfmass {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M₂ M₃ : ℝ}, 0 < M₂ → 4 < M₃ →
        ∀ {f : ℝ → ℝ}, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
          (∫ u in (0 : ℝ)..(1 / 2), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2) ≤
            c * M₃ * (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2) := by
  obtain ⟨θ, hθpos, hcore⟩ := winmass_halfmass_core
  refine ⟨1 / (2 * θ), by positivity, ?_⟩
  intro M₂ M₃ hM₂ hM₃ f hf hnn hsup
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hM₃pos : (0 : ℝ) < M₃ := by linarith
  set h : ℝ → ℝ := Hprof f M₂ with hhdef
  have hhcont : Continuous h := hhdef ▸ Hprof_continuous hf M₂
  have hhcs : HasCompactSupport h := hhdef ▸ Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hhnn : ∀ t, 0 ≤ h t := by
    intro t; rw [hhdef]; exact Finset.sum_nonneg (fun m _ => hnn _)
  have hBh : ∀ x, Bsum f M₂ x = Fhat h x := fun x => by
    rw [hhdef]; exact Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ x
  -- upper half: the half-window mass is at most `∫ h²`
  have hLHS : (∫ u in (0 : ℝ)..(1 / 2), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2)
      ≤ ∫ x, (h x) ^ 2 := by
    have h1 : (∫ u in (0 : ℝ)..(1 / 2), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2)
        = ∫ u in (0 : ℝ)..(1 / 2), ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      exact tsum_congr (fun ℓ => by rw [hBh])
    rw [h1]
    exact halfmass_le_profile_sq hhcont hhcs
  -- lower half: the `2/M₃`-window mass is at least `θ·(2/M₃)·∫h²`
  have hTpos : 0 < 2 / M₃ := by positivity
  have hTle : 2 / M₃ ≤ 1 / 2 := by
    rw [div_le_iff₀ hM₃pos]
    linarith
  have hcore' := hcore hhcont hhnn hhcs hTpos hTle
  have h3 : (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2)
      = ∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    exact tsum_congr (fun ℓ => by rw [hBh])
  have h2 : (∫ x, (h x) ^ 2) ≤ (M₃ / (2 * θ)) *
      (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2) := by
    rw [← h3]
    have ha : (0:ℝ) < θ * (2 / M₃) := by positivity
    have hdiv : (∫ x, (h x) ^ 2)
        ≤ (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2) / (θ * (2 / M₃)) :=
      (le_div_iff₀ ha).mpr (by
        calc (∫ x, (h x) ^ 2) * (θ * (2 / M₃)) = θ * (2 / M₃) * (∫ x, (h x) ^ 2) := by ring
          _ ≤ _ := hcore')
    have hcoefeq : (θ * (2 / M₃))⁻¹ = M₃ / (2 * θ) := by
      field_simp
    calc (∫ x, (h x) ^ 2)
        ≤ (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2) / (θ * (2 / M₃)) := hdiv
      _ = (M₃ / (2 * θ))
            * (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2) := by
          rw [div_eq_mul_inv, hcoefeq]
          ring
  calc (∫ u in (0 : ℝ)..(1 / 2), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2)
      ≤ ∫ x, (h x) ^ 2 := hLHS
    _ ≤ (M₃ / (2 * θ)) *
          (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2) := h2
    _ = (1 / (2 * θ)) * M₃ *
          (∫ u in (0 : ℝ)..(2 / M₃), ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2) := by
        ring

end

end Work.GM.Affine
