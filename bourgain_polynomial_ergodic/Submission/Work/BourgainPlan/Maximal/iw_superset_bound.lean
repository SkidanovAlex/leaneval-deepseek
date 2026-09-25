import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlin_multiplier_lift
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_star
import Submission.Work.BourgainPlan.Maximal.iwRangeBound_of_endpoint

/-!
# `IWSupersetBound`: the assembly

This module proves the two `Prop`s of `Submission.Work.BourgainPlan.Maximal.iw_superset`:

* `iwEndpoint2r` — directly from `Work.BourgainPlan.Maximal.main_narrow_taoSetS` (Tao's `main` at
  the endpoint exponent `2r` over `Σ_N`, obtained from `main_narrow_sigmaLe` by the arithmetic of
  `taoSetS_arith`, the flat bump `exists_flat_bump_uniform` and the goodness tools);
* `IWSupersetBound` — from `iwEndpoint2r` through `Work.BourgainPlan.Maximal.iwRangeBound_of_endpoint`
  (duality + Riesz–Thorin) with the Mikhlin conditions converted into the multiplier-norm
  hypotheses by `mikhlin_multiplier_lift` (for the symbol and, via `mikhlin_conditions_star`, for
  its conjugate).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The endpoint `p = 2r` of Tao's `main` over `Σ_N` holds**: the constant of
`main_narrow_taoSetS` is renamed to fit the shape `(C * A) ^ (2r)` of `iwEndpoint2r`. -/
theorem iwEndpoint2r_proof : iwEndpoint2r := by
  intro ρ hρ r hr
  obtain ⟨K, hKpos, N₁, hN⟩ := main_narrow_taoSetS ρ hρ r hr
  have hCpos : 0 < max 1 K := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨max 1 K, hCpos, N₁, fun N hNle => ?_⟩
  intro ε hε0 hεle ψ hψ hψsupp A hA hMult _ f hf
  have hmono : K * A ≤ max 1 K * A := mul_le_mul_of_nonneg_right (le_max_right _ _) hA
  have h1max : (0 : ℝ) ≤ max 1 K := le_trans zero_le_one (le_max_left _ _)
  have h2r1 : (1 : ℝ) ≤ 2 * (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (le_trans (by norm_num) hr)
    linarith
  have h := hN N hNle ε hε0 hεle ψ hψ hψsupp A hA hMult f hf
  refine h.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact Real.rpow_le_rpow (mul_nonneg hKpos.le hA) hmono (by positivity)

/-- **`IWSupersetBound` holds.**  Given `ρ > 0` and `p ∈ (1,∞)`, put `r := max 2 (iwR p)`, so that
`2r ≥ max (p, p/(p−1))` and hence `p ∈ [(2r)', 2r]`.  The Mikhlin conditions of the statement
produce — via `mikhlin_multiplier_lift` at the exponent `2r`, applied to `ψ` and (using
`mikhlin_conditions_star`) to `star ∘ ψ` — the two multiplier-norm hypotheses `IWMult r · (C_m A)`,
and the range form `iwRangeBound` of Tao's `main` then gives the `ℓᵖ`-bound over `Σ_N`. -/
theorem iwSupersetBound_proof : IWSupersetBound := by
  intro ρ hρ p hp
  set r : ℕ := max 2 (iwR p) with hrdef
  have hr2 : 2 ≤ r := le_max_left _ _
  have hr1 : (1 : ℝ) < 2 * (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (le_trans (by norm_num) hr2)
    linarith
  obtain ⟨Km, hKmpos, hmikh⟩ := mikhlin_multiplier_lift (2 * (r : ℝ)) hr1
  obtain ⟨K, hKpos, N₁, hN⟩ := iwRangeBound_of_endpoint iwEndpoint2r_proof ρ hρ r hr2
  refine ⟨K * Km, mul_pos hKpos hKmpos, N₁, fun N hNle => ?_⟩
  intro ε hε0 hεle ψ hψ hψsupp A hA hcont hbdd hderiv hderiv2 f hf
  have hm1 : IWMult r ψ (Km * A) := hmikh ψ A hA hcont hbdd hderiv hderiv2
  obtain ⟨hcont', hbdd', hderiv', hderiv2'⟩ :=
    mikhlin_conditions_star hA hcont hbdd hderiv hderiv2
  have hm2 : IWMult r (fun ξ => star (ψ ξ)) (Km * A) :=
    hmikh (fun ξ => star (ψ ξ)) A hA hcont' hbdd' hderiv' hderiv2'
  have hsupp' : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      ε < ‖ξ‖ → (fun ξ => star (ψ ξ)) ξ = 0 := by
    intro ξ hξ
    show star (ψ ξ) = 0
    rw [hψsupp ξ hξ, star_zero]
  -- the range conditions `(2r)' ≤ p ≤ 2r`
  have hp1 : 0 < p - 1 := by linarith
  have hRle : (iwR p : ℝ) ≤ (r : ℝ) := by
    rw [hrdef]
    exact_mod_cast le_max_right 2 (iwR p)
  have hCeil : (iwR p : ℝ) = ((max ⌈p / 2⌉₊ ⌈(p / (p - 1)) / 2⌉₊ : ℕ) : ℝ) := rfl
  have hp_hi : p ≤ 2 * (r : ℝ) := by
    have h2 : ((⌈p / 2⌉₊ : ℕ) : ℝ) ≤ (iwR p : ℝ) := by
      rw [hCeil]; exact_mod_cast le_max_left _ _
    have h3 : p / 2 ≤ ((⌈p / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  have hpp : p / (p - 1) ≤ 2 * (r : ℝ) := by
    have h2 : ((⌈(p / (p - 1)) / 2⌉₊ : ℕ) : ℝ) ≤ (iwR p : ℝ) := by
      rw [hCeil]; exact_mod_cast le_max_right _ _
    have h3 : (p / (p - 1)) / 2 ≤ ((⌈(p / (p - 1)) / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  have hp_lo : (2 * (r : ℝ)) / (2 * (r : ℝ) - 1) ≤ p := by
    have hden : (0 : ℝ) < 2 * (r : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (le_trans (by norm_num) hr2)
      linarith
    rw [div_le_iff₀ hden]
    have hle : p ≤ 2 * (r : ℝ) * (p - 1) := by
      calc p = (p / (p - 1)) * (p - 1) := (div_mul_cancel₀ p hp1.ne').symm
        _ ≤ (2 * (r : ℝ)) * (p - 1) := mul_le_mul_of_nonneg_right hpp hp1.le
    nlinarith [hle]
  have h := hN N hNle ε hε0 hεle ψ hψ hψsupp (Km * A) (mul_nonneg hKmpos.le hA) hm1 hm2
    p hp_lo hp_hi f hf
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have heq : K * (Km * A) = K * Km * A := by ring
  rw [heq]

end

end Work.BourgainPlan.Maximal
