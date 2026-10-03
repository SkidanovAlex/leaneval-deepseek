/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.KMTContract.Defs

/-!
# The real-valued Ionescu–Wainger symbol `σ_{l,k}`

The paper's symbol of height `≤ l` at scale `≤ k` is

`σ_{l,k} = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(· - α)`,
`η_{≤k}(θ) = η(θ / 2^k)`, the periodisation `periodize` being the mechanism that turns a function
on `ℝ` into a function on `ℝ/ℤ`.

In this workspace the symbol is
`iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) : Circle → ℂ`, and this file
provides its *real valued* version: `kmtEta` is the complexification of a `ContDiffBump`
`kmtBump : ℝ → ℝ` with `rIn = 1/2`, `rOut = 1`, so `η(θ/2^k)` is the complexification of
`bumpRescaled k θ = kmtBump (θ / 2^k)`, and the periodisation of a function supported in
`[-2^k, 2^k]` is the finite sum over the set `suppIdx (2^k)` of integers `j` with
`-⌊2^k⌋-2 ≤ j ≤ ⌊2^k⌋+1`.

## Main definitions

* `Work.KMTAreas.A4.suppIdx` — the finite index set of the periodisation;
* `Work.KMTAreas.A4.bumpRescaled` — the real cutoff `θ ↦ kmtBump (θ / 2^k)`;
* `Work.KMTAreas.A4.symReal` — the real valued symbol `σ_{l,k}`, expanded over `suppIdx R`
  (valid for `R ≥ 2^k`).

## Main results

* `periodize_eq_sum_of_support` — the periodisation of a function supported in `[-R, R]` is the
  finite sum over `suppIdx R`;
* `iwSymbolSet_eq_ofReal_symReal` — the complex symbol is the complexification of `symReal`.

Everything here is stated for the fixed cutoff `Work.KMTContract.kmtEta`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open MeasureTheory

open Work.Analysis.IonescuWainger

/-- The integers `j` for which the translate `x + j`, `x ∈ [0,1)`, can lie in `[-R, R]`. -/
noncomputable def suppIdx (R : ℝ) : Finset ℤ := Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)

/-- The paper's cutoff `η_{≤k} = η(· / 2^k)`, made real valued (against the real bump
`kmtBump` whose complexification is `kmtEta`). -/
noncomputable def bumpRescaled (k : ℤ) (θ : ℝ) : ℝ :=
  Work.KMTContract.kmtBump (θ / (2 : ℝ) ^ k)

/-- The real valued Ionescu–Wainger symbol `σ_{l,k} = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(· - α)`,
expanded over the periodisation index set `suppIdx R`; the identity with the complex symbol
`iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))` holds as soon as `2^k ≤ R`
(see `iwSymbolSet_eq_ofReal_symReal`). -/
noncomputable def symReal (ρ : ℝ) (l : ℕ) (k : ℤ) (R : ℝ) (ξ : Work.Analysis.IonescuWainger.Circle) : ℝ :=
  ∑ α ∈ iwArithFreqs ρ l, ∑ j ∈ suppIdx R,
    bumpRescaled k ((AddCircle.equivIco (1 : ℝ) 0 (ξ - α)).val + j)

/-! ## Elementary properties of the cutoff -/

theorem bumpRescaled_nonneg (k : ℤ) (θ : ℝ) : 0 ≤ bumpRescaled k θ :=
  ContDiffBump.nonneg Work.KMTContract.kmtBump

theorem bumpRescaled_le_one (k : ℤ) (θ : ℝ) : bumpRescaled k θ ≤ 1 :=
  ContDiffBump.le_one Work.KMTContract.kmtBump

/-- `etaCut kmtEta k` is the complexification of `bumpRescaled k`. -/
theorem etaCut_eq_ofReal (k : ℤ) (θ : ℝ) :
    etaCut Work.KMTContract.kmtEta k θ = ((bumpRescaled k θ : ℝ) : ℂ) := rfl

/-- `η_{≤k}` vanishes where `2^k < |θ|`. -/
theorem etaCut_eq_zero {k : ℤ} {θ : ℝ} (hθ : (2 : ℝ) ^ k < |θ|) :
    etaCut Work.KMTContract.kmtEta k θ = 0 := by
  rw [etaCut]
  refine Work.KMTContract.kmtEta_zero ?_
  rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  exact (one_le_div (zpow_pos (by norm_num : (0 : ℝ) < 2) k)).mpr hθ.le

/-! ## The periodisation as a finite sum -/

/-- The integers `k` contributing to the periodisation of a function supported in `[-R, R]`
evaluated at a point of `[0,1)` all lie in the fixed interval `[-(⌊R⌋+2), ⌊R⌋+1]`. -/
private lemma periodize_term_eq_zero {φ : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x, R < |x| → φ x = 0) (ξ : Work.Analysis.IonescuWainger.Circle) {k : ℤ}
    (hk : k ∉ suppIdx R) :
    φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) = 0 := by
  by_contra hne
  have hx := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop
  rw [Set.mem_Ico] at hx
  have hle : |(AddCircle.equivIco (1 : ℝ) 0 ξ).val + k| ≤ R := by
    by_contra h
    exact hne (hφ0 _ (lt_of_not_ge h))
  rw [abs_le] at hle
  have h1 : k ≤ ⌊R⌋ + 1 := by
    have hkx : (k : ℝ) ≤ R := by linarith [hle.2, hx.1]
    have := Int.le_floor.mpr hkx
    linarith
  have h2 : -(⌊R⌋ + 2) ≤ k := by
    have hk2 : ((-k - 2 : ℤ) : ℝ) ≤ R := by
      push_cast
      linarith [hle.1, hx.2, hR]
    have := Int.le_floor.mpr hk2
    linarith
  exact hk (by rw [suppIdx, Finset.mem_Icc]; exact ⟨h2, h1⟩)

/-- A function supported in `[-R, R]` has a periodisation which is the finite sum of its
translates over `suppIdx R`. -/
theorem periodize_eq_sum_of_support {φ : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x : ℝ, R < |x| → φ x = 0) (ξ : Work.Analysis.IonescuWainger.Circle) :
    periodize φ ξ = ∑ j ∈ suppIdx R, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) := by
  change (∑' j : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j)) = _
  exact tsum_eq_sum fun j hj => periodize_term_eq_zero hR hφ0 ξ hj

/-! ## Measurability -/

/-- The canonical representative `ℝ/ℤ → [0,1)` is measurable. -/
theorem measurable_equivIco_val :
    Measurable fun ξ : Work.Analysis.IonescuWainger.Circle => (AddCircle.equivIco (1 : ℝ) 0 ξ).val :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem measurable_bumpRescaled (k : ℤ) : Measurable (bumpRescaled k) :=
  (Work.KMTContract.kmtBump.contDiff (n := ⊤)).continuous.measurable |>.comp
    (measurable_id.div_const _)

theorem measurable_etaCut (k : ℤ) : Measurable (etaCut Work.KMTContract.kmtEta k) := by
  rw [funext fun θ => etaCut_eq_ofReal k θ]
  exact Complex.measurable_ofReal.comp (measurable_bumpRescaled k)

/-- The periodisation of a measurable function supported in `[-R, R]` is measurable. -/
theorem measurable_periodize_of_support {φ : ℝ → ℂ} {R : ℝ} (hφ : Measurable φ) (hR : 0 ≤ R)
    (hφ0 : ∀ x : ℝ, R < |x| → φ x = 0) : Measurable (periodize φ) := by
  rw [funext (periodize_eq_sum_of_support hR hφ0)]
  refine Finset.measurable_sum _ fun j _ => hφ.comp ?_
  exact measurable_equivIco_val.add measurable_const

/-! ## Elementary properties of the real symbol -/

theorem symReal_nonneg (ρ : ℝ) (l : ℕ) (k : ℤ) (R : ℝ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    0 ≤ symReal ρ l k R ξ := by
  unfold symReal
  exact Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun j _ => bumpRescaled_nonneg k _

/-- `ℂ`-valued quotient of two nonnegative reals with `a ≤ b` has norm `≤ 1`. -/
theorem norm_ofReal_div_le_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖((a : ℝ) : ℂ) / ((b : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha,
    Real.norm_of_nonneg (ha.trans hab)]
  exact div_le_one_of_le₀ hab (ha.trans hab)

end Work.KMTAreas.A4
