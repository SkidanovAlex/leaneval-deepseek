/-
# `Work.FTS.StrongPersist.AK6.Sharp6` — the sharp pointwise `ℋ⁶`-bound for `AK α`

`AK α z θ = (Γ(θ)/c α)·2z²/(1+z)³` is separable, and the `ℋ⁶`-integrand of a separable
datum factorises (`L6Aux.HkIntegrandSepLeGen`) into an angular block times a radial block.
The two factors are bounded here with *α-uniform* constants:

* angular block: `Γ²·sin(2θ)^{-η} + Σ_{1≤i≤6} (D_θ^iΓ)²·sin(2θ)^{-γ}`.  Since `Γ ≤ 1` and
  – crucially – `|D_θ^iΓ| ≤ α·10⁵·Γ` for `i ≥ 1` (the extra factor `α` coming from
  `dthU_iter_Gam_abs_bound`), the block is `≤ sin(2θ)^{-η} + 7·10¹⁰·α²·sin(2θ)^{2α/5-γ}`
  after `Γ² ≤ sin(2θ)^{2α/5}` (`Gam_le_sin_two_rpow`).  The exponent `2α/5` is what makes
  the `γ`-term integrable *uniformly* in `α` (the paper's `W^{2,∞} → ℋ⁶` route).
* radial block: `Σ_{q≤6} (D_z^q ρ · w)²` with `ρ = 2z²/(1+z)³`, bounded by `700·R/(1+z)²`
  from the jet bound `hrad` and `1/c α ≤ 10`.

This is the `ℋ⁶`-analogue of the pointwise estimate behind `NonlinRows.HkMem_AK`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow
import Submission.Work.FTS.LocData.hLoc_hk
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false

/-! ## The angular jets of `Γ`, with the `α`-factor -/

/-- **`|D_θ^i Γ| ≤ α·10⁵·Γ` on `Iθ` for `1 ≤ i ≤ 6`.**  The `α`-factor is the point: it
comes from `Spaces.dthU_iter_Gam_abs_bound` (the `i`-th angular jet of `Γ` is
`α·Tfun_{i-1}·Γ`), and it is what makes the `γ`-weighted angular integral of the `ℋ⁶`-norm
uniformly bounded as `α → 0⁺`. -/
theorem dthU_Gam_abs_le_alpha (i : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ| ≤ α * 100000 * Work.Spaces.Gam α θ := by
  intro θ hθ
  exact Work.Spaces.dthU_iter_Gam_abs_bound i hi α hα 100000
    (fun θ' _ => Work.FTS.LocData6.Tfun_abs_le5 (i - 1) (by omega) α hα hα1 θ') θ hθ

/-- **`Γ² ≤ sin(2θ)^{2α/5}` on `Iθ`** (square of `Gam_le_sin_two_rpow`). -/
theorem Gam_sq_le_sin_two_rpow (α : ℝ) (hα : 0 < α) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  have h := Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have h2 := pow_le_pow_left₀ (Work.Spaces.Gam_bounds α θ hα hθ).1 h 2
  have heq : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
    congr 1
    ring
  rwa [heq] at h2

/-- **`Γ²·sin(2θ)^{-γ} ≤ sin(2θ)^{2α/5-γ}` on `Iθ`.**  This is the `rpow` bookkeeping that
converts the `γ`-weighted square of `Γ` into the uniformly integrable exponent
`2α/5 - γ = 3α/10 - 1` of `Work.Elliptic.WtoH_Angular`. -/
theorem Gam_sq_mul_rpow_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  have hp : 2 * α / 5 + -(Work.Spaces.gam α) ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; nlinarith [hα, hα1]
  have hkey : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add' (x := Real.sin (2 * θ)) hs0 hp,
      show 2 * α / 5 - Work.Spaces.gam α = 2 * α / 5 + -(Work.Spaces.gam α) by ring]
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right (Gam_sq_le_sin_two_rpow α hα θ hθ)
          (Real.rpow_nonneg hs0 _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := hkey

/-! ## The sharp pointwise bound on the `ℋ⁶`-integrand of `AK α` -/

/-- **The pointwise `ℋ⁶`-bound for `AK α`.**  From the radial jet bound `hrad` (order `≤ 6`)
of `ρ = 2z²/(1+z)³` one gets, for every `0 < α ≤ 1` and every `(z,θ) ∈ Iz × Iθ`,

  `HkIntegrand α 6 (AK α) z θ ≤ (1+z)^{-2}·(700·R·sin(2θ)^{-η}
     + 49·10¹²·R·(α+sin 2θ)²·sin(2θ)^{2α/5-γ})`,

which is exactly the pointwise input of `WtoH_Angular`-type integration
(`AK6.hkSq_le_of_integrand_le6`). -/
theorem AK_integrand_le6 {R : ℝ} (hR : 0 ≤ R)
    (hrad : ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ),
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ),
      θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 6 (Work.Construction.AK α) z θ
        ≤ (1 / (1 + z) ^ 2) *
          (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
  intro α hα hα1 z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hc10 : (1 / Work.Spaces.c α) ≤ 10 := by rw [div_le_iff₀ hc0]; linarith
  have hcsq : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
    have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
    nlinarith [hc10, h1]
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  -- `AK α` is the separable datum `Γ(θ)·(2z²/(1+z)³/c α)`
  have hAK : Work.Construction.AK α
      = fun z' θ' => Work.Spaces.Gam α θ' * (2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) := by
    funext z' θ'
    rw [Work.Construction.AK]
    ring
  rw [hAK]
  have hmain := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
    (C := fun θ' : ℝ => Work.Spaces.Gam α θ')
    (B := fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) (z := z) (θ := θ) hθ
  -- ### the radial block
  have hBfun : (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
      = fun z' _ : ℝ => (1 / Work.Spaces.c α) * (2 * z' ^ 2 / (1 + z') ^ 3) := by
    funext z' θ'
    ring
  have hradq : ∀ q : ℕ, q ≤ 6 →
      (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
          z 0) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 100 * R / (1 + z) ^ 2 := by
    intro q hq
    have hDzB : Work.Spaces.DzIter q
          (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0
        = (1 / Work.Spaces.c α)
          * Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3) z 0 := by
      rw [hBfun, Work.FTS.LocDataExt.DzIter_const_mul]
    rw [hDzB]
    have h1 := hrad q hq z hz 0
    calc ((1 / Work.Spaces.c α)
            * Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (1 / Work.Spaces.c α) ^ 2
            * (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3) z 0
              * Work.Spaces.w z) ^ 2 := by ring
      _ ≤ 100 * (R / (1 + z) ^ 2) := mul_le_mul hcsq h1 (sq_nonneg _) (by norm_num)
      _ = 100 * R / (1 + z) ^ 2 := by ring
  have hradsum : (∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
            z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 700 * R / (1 + z) ^ 2 := by
    have h := Finset.sum_le_card_nsmul (Finset.range 7)
      (fun q => (Work.Spaces.DzIter q
          (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) (100 * R / (1 + z) ^ 2)
      (fun q hq => hradq q (by have := Finset.mem_range.mp hq; omega))
    calc (∑ q ∈ Finset.range 7, (Work.Spaces.DzIter q
            (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        ≤ (Finset.range 7).card • (100 * R / (1 + z) ^ 2) := h
      _ = 700 * R / (1 + z) ^ 2 := by simp; ring
  have hradsum0 : 0 ≤ ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
          z 0) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### the angular block
  have hang_term : ∀ i : ℕ, i ∈ Finset.range 7 →
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
        ≤ 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    intro i hi
    by_cases h1i : 1 ≤ i
    · rw [if_pos h1i]
      have hb := dthU_Gam_abs_le_alpha i h1i
        (by have := Finset.mem_range.mp hi; omega) α hα hα1 θ hθ
      have hb2 : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
          ≤ α ^ 2 * 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs] at h
        calc (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
            ≤ (α * 100000 * Work.Spaces.Gam α θ) ^ 2 := h
          _ = α ^ 2 * 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by ring
      calc (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (α ^ 2 * 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg hs0 _)
        _ = 10 ^ 10 * α ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ ≤ 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
            mul_le_mul_of_nonneg_left (Gam_sq_mul_rpow_le α hα hα1 θ hθ) (by positivity)
    · rw [if_neg h1i]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)
  have hang : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    have h1 : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have h2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG0, hG1]
      calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          ≤ 1 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hs0 _)
        _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
    have h2 : (∑ i ∈ Finset.range 7, (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        ≤ 7 * (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
      have h := Finset.sum_le_card_nsmul (Finset.range 7)
        (fun i => (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) hang_term
      calc _ ≤ (Finset.range 7).card
            • (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := h
        _ = _ := by simp
    calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 7 * (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
          add_le_add h1 h2
      _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by ring
  have hang0 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h : 1 ≤ i
    · rw [if_pos h]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · rw [if_neg h]
  -- ### assemble
  have hangb0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    refine add_nonneg (Real.rpow_nonneg hs0 _) ?_
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)
  calc Work.Spaces.HkIntegrand α 6
        (fun z' θ' => Work.Spaces.Gam α θ' * (2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)) z θ
      ≤ ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q
              (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) := hmain
    _ ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
        * (700 * R / (1 + z) ^ 2) := mul_le_mul hang hradsum hradsum0 hangb0
    _ = (1 / (1 + z) ^ 2) * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 700 * (7 * 10 ^ 10) * α ^ 2 * R
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by ring
    _ ≤ (1 / (1 + z) ^ 2) * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hle : α ^ 2 ≤ (α + Real.sin (2 * θ)) ^ 2 := by nlinarith [hα, hs0]
        have h3 : (0 : ℝ) ≤ 700 * (7 * 10 ^ 10) * R := by positivity
        have h4 : α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            ≤ (α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hs0 _)
        calc 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 700 * (7 * 10 ^ 10) * α ^ 2 * R
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            = 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 700 * (7 * 10 ^ 10) * R * (α ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by ring
          _ ≤ 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 700 * (7 * 10 ^ 10) * R * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
              add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h4 h3)
          _ = 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by ring

end Work.FTS.StrongPersist.AK6
