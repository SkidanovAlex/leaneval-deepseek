import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB1.w1MassB_le_w2MassB_localised
import Submission.Work.BoseFixB1S.sectorPassageB1Lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary `F`-weight facts (pointwise) -/

/-- **`F(t) ≤ μ²` for `0 ≤ t ≤ μ`.**  (`F(μ) = 0`; restated locally from
`Submission/Work/BoseFixB1/perSectorBoundG_holds.lean` so that this module is independent of the
per-sector cone.) -/
theorem psiWeight_one_le_mu_sq_of_le {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (htμ : t ≤ μ) :
    psiWeight 1 μ t ≤ μ ^ 2 := by
  have hF : psiWeight 1 μ t = (t - μ) ^ 2 / (1 + t * μ⁻¹) := by
    rw [psiWeight]; ring
  have hd : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
    linarith
  have hle : (t - μ) ^ 2 / (1 + t * μ⁻¹) ≤ (t - μ) ^ 2 := by
    rw [div_le_iff₀ hd]
    have hge : 1 ≤ 1 + t * μ⁻¹ := by
      have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
      linarith
    nlinarith [sq_nonneg (t - μ), hge]
  have h4 : (t - μ) ^ 2 ≤ μ ^ 2 := by nlinarith
  rw [hF]; linarith

/-- **`F(t) ≤ μt` for `μ ≤ 3t`.**  In that range FS's weight is dominated by its linear term.
The threshold is exactly `(t−μ)² ≤ t(t+μ)`. -/
theorem psiWeight_one_le_mu_mul_of_mu_le_three {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t)
    (h3 : μ ≤ 3 * t) : psiWeight 1 μ t ≤ μ * t := by
  have hF : psiWeight 1 μ t = (t - μ) ^ 2 / (1 + t * μ⁻¹) := by
    rw [psiWeight]; ring
  have hd : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
    linarith
  rw [hF, div_le_iff₀ hd]
  have h2 : μ * t * (1 + t * μ⁻¹) = t * (t + μ) := by
    field_simp
    ring
  rw [h2]
  have hmul : μ * μ ≤ μ * (3 * t) := by
    exact mul_le_mul_of_nonneg_left h3 hμ.le
  nlinarith [hmul]

/-! ## 2. Cauchy–Schwarz

The cutoff-count Cauchy–Schwarz `chiSum² ≤ N·n·scountB` (which makes the crude fibre bound
`fibSum ≤ K_av(a v)chiSum` usable — the product form vanishes with `scountB`, unlike the crude
`chiSum ≤ n·sup χ_B·N`) is dispatched as the separate lemma
`Work.BoseFixB1.flatCS_chiSum_sq_le` (see `FINDING_perBoxF_flat.md`). -/

/-! ## 3. The pure arithmetic of the flat branch -/

/-- **The mean-field square completion of the flat branch.**  For `0 ≤ W₁ ≤ W₂` and `μ, τ ≥ 0`,

    (1/4)W₁(μτ + μ²) + μW₁τ − (1/2)μ²W₁ ≤ (1/2)τ²W₂ + (17/32)μ²W₁ .

The difference between the right and left sides is `(W₁/2)(τ − 5μ/4)² + (1/2)τ²(W₂ − W₁) ≥ 0`. -/
theorem flatArith {μ W₁ W₂ τ : ℝ} (hμ : 0 ≤ μ) (hW₁ : 0 ≤ W₁) (hW₁W₂ : W₁ ≤ W₂)
    (hτ : 0 ≤ τ) :
    (1 / 4) * W₁ * (μ * τ + μ ^ 2) + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
      ≤ (1 / 2) * τ ^ 2 * W₂ + (17 / 32) * μ ^ 2 * W₁ := by
  have h1 : (1 / 2) * τ ^ 2 * W₂ + (17 / 32) * μ ^ 2 * W₁
      - ((1 / 4) * W₁ * (μ * τ + μ ^ 2) + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁)
      = ((1 / 2) * (τ - 5 * μ / 4) ^ 2) * W₁ + (1 / 2) * τ ^ 2 * (W₂ - W₁) := by
    ring
  have h2 : 0 ≤ ((1 / 2) * (τ - 5 * μ / 4) ^ 2) * W₁ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hW₁
  have h3 : 0 ≤ (1 / 2) * τ ^ 2 * (W₂ - W₁) := by
    have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg τ
    have hsub : 0 ≤ W₂ - W₁ := sub_nonneg.mpr hW₁W₂
    positivity
  linarith

/-! ## 4. The state functionals of the ledger (verbatim copies of `perBoxF_localised`)

These are definitionally equal to `Work.BoseFixB1.scountB`, `chiSum`, `fibSum`, `pairSum` and
`nPlus`; they are reproduced here only so that this module does not import the (heavy) module that
contains them together with the per-sector cone. -/

/-- `Work.BoseFixB1.scountB`. -/
noncomputable def flatScountB (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x

/-- `Work.BoseFixB1.chiSum`. -/
noncomputable def flatChiSum (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i)

/-- `Work.BoseFixB1.fibSum`. -/
noncomputable def flatFibSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 *
    ∑ i : Fin n, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y

/-- `Work.BoseFixB1.pairSum`. -/
noncomputable def flatPairSum (v : EuclideanSpace ℝ (Fin 3) → ℝ) (M : ℕ) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 *
    ((1 / 2) * ∑ p ∈ pairSet n, wSmallPair M ℓ d u v (x p.1) (x p.2))

/-- The `F`-weight integral `∫Φ²F(nCountB/κ)`. -/
noncomputable def flatFterm (M : ℕ) (ℓ d μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u)

/-- The state's mass `N = ∫_{abox n ℓ}Φ²`. -/
noncomputable def flatMass (ℓ : ℝ) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2

/-- The state's mean smooth density `τ = scountB/(κN)`. -/
noncomputable def flatTau (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  flatScountB M ℓ d u Φ / (chiMass M ℓ d u * flatMass ℓ Φ)

/-- The pair mass with the interaction numerator: `∬wSmallPair M ℓ d u v`. -/
noncomputable def flatPairMass (v : EuclideanSpace ℝ (Fin 3) → ℝ) (M : ℕ) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ x : ℝ³, ∫ y : ℝ³, wSmallPair M ℓ d u v x y

/-- The error bracket of `PerBoxF`. -/
noncomputable def flatErr (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R : ℝ) (M : ℕ) (ℓ d μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v)
      * ((R / (ℓ * d)) ^ 2 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      * chiMass M ℓ d u
    + μ * (_root_.BoseGases.a v)

/-! ## 5. Abbreviations for the FS parameter block -/

/-- The small-box particle-number parameter `M = (paramsAt μ (a v)).M`. -/
abbrev pM (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℕ :=
  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M

/-- The small-box side `ℓ = sideAt μ (a v)`. -/
abbrev pL (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBox.sideAt μ (_root_.BoseGases.a v)

/-- The small-box ratio `d = (paramsAt μ (a v)).d`. -/
abbrev pD (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d

/-! ## 6. The flat-branch ledger -/

/-- **The flat-branch ledger.**  At FS's parameters, five inputs

* `(F)`  `Fterm ≤ μτN + μ²N`  (the `F`-weight integral against the mean smooth count),
* `(fib)` `μ·fibSum ≤ μW₁τN + E_fib`  (`fibSum ≤ K_av(a v)chiSum` plus the Cauchy–Schwarz
  `chiSum² ≤ n·N·scountB`, so that the fibre loss is measured by the pair term),
* `(P)`  `(5/4)μW₁τN − (1/4)μ²W₁N ≤ pairSum + E_pair`  — the **analytic input** of the flat branch:
  the pair term pays the *linear* chemical-potential loss of the fibre,
* the budget `E_fib + E_pair ≤ C·flatErr·N`,

together with the proved split `sbPot = −μfibSum + pairSum`, `sbKin ≥ 0`, `0 ≤ W₁` and
`μ, τ, N ≥ 0`, imply `PerBoxF v h R (1/4) C μ n Φ u`.

**Why the pair input is *linear* and not the quadratic mean-field value.**  The first form of this
ledger asked for `pairSum ≥ ½τ²W₂N − E_pair` (the box-constant mean-field value).  That is
**FALSE**, and not repairable by a constant: the all-pairs-separated ("hard-core") state
`Φ = C·∏ᵢ1_A(xᵢ)·∏_{k<l}1_{|x_k−x_l|>R}` has `pairSum = 0` exactly (the interaction support is never
hit) while `τ = n/V` makes the quadratic demand `≍ n²W₂/V²` grow like `n²`, against an `n`-free
error bracket.  What `PerBoxF` actually needs is only that the pair term dominate the *linear*
fibre loss `μ·fibSum ≈ μW₁τN` (the chemical-potential term), which is exactly FS's structure: the
`F`-weight's linear part cancels against the chemical potential and the pair energy pays `μ×count`.
(`F(t) ≤ μt + μ²` is *tight* on the hard-core states, where `t = nCountB/κ ≈ τ ≪ μ` and
`F(τ) ≈ μ²`.) -/
theorem perBoxF_of_ledger {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R C μ : ℝ} {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (pL v μ)} {u : EuclideanSpace ℝ (Fin 3)}
    {Efib Epair : ℝ}
    (hμ : 0 ≤ μ) (hN : 0 ≤ normB v μ n (Φ : X n → ℝ))
    (hW1 : 0 ≤ w1MassB h (pM v μ) (pL v μ) (pD v μ) u)
    (hτ : 0 ≤ flatTau (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ))
    (hF : flatFterm (pM v μ) (pL v μ) (pD v μ) μ u (Φ : X n → ℝ)
      ≤ μ * flatTau (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ) * normB v μ n (Φ : X n → ℝ)
        + μ ^ 2 * normB v μ n (Φ : X n → ℝ))
    (hfib : μ * flatFibSum h (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ)
      ≤ μ * w1MassB h (pM v μ) (pL v μ) (pD v μ) u
          * flatTau (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ)
          * normB v μ n (Φ : X n → ℝ) + Efib)
    (hpair : (5 / 4) * μ * w1MassB h (pM v μ) (pL v μ) (pD v μ) u
          * flatTau (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ)
          * normB v μ n (Φ : X n → ℝ)
        - (1 / 4) * μ ^ 2 * w1MassB h (pM v μ) (pL v μ) (pD v μ) u
          * normB v μ n (Φ : X n → ℝ)
      ≤ flatPairSum v (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ) + Epair)
    (hsplit : sbPot h μ u (Φ : X n → ℝ)
      = -(μ * flatFibSum h (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ))
        + flatPairSum v (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ))
    (hkin : 0 ≤ sbKin (v := v) μ (pM v μ) u (Φ : X n → ℝ))
    (hbud : Efib + Epair
      ≤ C * flatErr v R (pM v μ) (pL v μ) (pD v μ) μ u * normB v μ n (Φ : X n → ℝ)) :
    PerBoxF v h R (1 / 4) C μ n Φ u := by
  have h1 : (1 / 4) * w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        * flatFterm (pM v μ) (pL v μ) (pD v μ) μ u (Φ : X n → ℝ)
      ≤ (1 / 4) * w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        * (μ * flatTau (pM v μ) (pL v μ) (pD v μ) u (Φ : X n → ℝ)
              * normB v μ n (Φ : X n → ℝ)
            + μ ^ 2 * normB v μ n (Φ : X n → ℝ)) :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  have hFb : (∫ (x : X n) in abox n (pL v μ),
        (Φ x) ^ 2 * psiWeight 1 μ (nCountB (pM v μ) (pL v μ) (pD v μ) u x
          / chiMass (pM v μ) (pL v μ) (pD v μ) u))
      = flatFterm (pM v μ) (pL v μ) (pD v μ) μ u (Φ : X n → ℝ) := rfl
  rw [PerBoxF, sbWord, hsplit, hFb]
  simp only [flatErr] at hbud
  ring_nf at h1 hfib hpair hbud hkin ⊢
  linarith [h1, hfib, hpair, hbud, hkin]

end Work.BoseFixB1
