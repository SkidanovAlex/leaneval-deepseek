import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.AeValue
import Submission.CentredSector
import Submission.Q0Chosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — the Q0-renormalized value in sector form (S-form)

Combine `AeValue.q0_expect_ae` with the chosen-kernel double integrals
(`Q0Chosen.w1c_acube_integral`, `w2c_acube_integral`,
`w2c_acube_integral_bounds`) and the sector counts `cS1`, `cS2`
(`CentredSector`) into the corpus-native *Q0 renormalized value* in the
chosen branch (`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`, `w₀` the
chosen witness, `g₀ := v(1−w₀)`, `g₂ := g₀(1+w₀)`):

    ⟨Φ, Q₀^ren Φ⟩ = ½ℓ⁻³·(∫g₂)·S₂ − 8πa v·μ·S₁                          (q0_chosen_expect)
    S₁ = cS1 ℓ Φ = Σ_i ∫(P_iΦ)² ,   S₂ = cS2 ℓ Φ = Σ_{i≠j} ∫(P_iP_jΦ)²

(all integrals over `abox N ℓ`), valid for every continuous Φ (no symmetry).
Using the mass bounds `8πa v ≤ ∫g₂ ≤ 16πa v` (`g2_integral_bounds`) and
`cS2 ≥ 0` (`CentredSector.cS2_nonneg`) gives the lower surrogate

    ⟨Q₀^ren Φ⟩ ≥ ½ℓ⁻³·(8πa v)·S₂ − 8πa v·μ·S₁                          (q0_chosen_lower)

and the upper surrogate with `16πa v`.

## Route notes (for the child)

`q0_expect_ae` (Submission.AeValue) gives the identity for abstract
integrable kernels `w1,w2` on `acube ℓ ×ˢ acube ℓ`.  Instantiate with
`w1 := wPairU ℓ (g0 v h)` and `w2 := wPairU ℓ (g2 v h)`, using the
integrability `integrableOn_w1c_acube` / `integrableOn_w2c_acube`
(`Q0Chosen`).  Then rewrite the two product-cube integrals by
`Q0Chosen.w1c_acube_integral` (`∬w₁ = ℓ³·8πa v`) and
`Q0Chosen.w2c_acube_integral` (`∬w₂ = ℓ³·∫g₂`) and the sums by the
definitions of `cS1`/`cS2` (`CentredSector`); ring/nlinarith finishes.
The surrogates use `g2_integral_bounds` (`ScatKernelChosen`:
`8πa v ≤ ∫g₂ ≤ 16πa v`) with `cS2_nonneg` (`CentredSector`) and `0 < ℓ`.

The full hypothesis block (standing for the chosen branch, matching
`Q0Chosen`/`ScatKernelChosen`): `(hR : 0 < R) (hv_nonneg : 0 ≤ v)
(hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0:ℝ³) R)
(h : ∃ w, IsRadial w ∧ IsScatteringSolution w v) (hℓ : 0 < ℓ)
(hRℓ : R ≤ ℓ * chiR0)` plus `(μ : ℝ)` and `(hΦc : Continuous Φ)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Q0-renormalized value (S-form)**: with the chosen kernels
`w₁ := wPairU(g₀)`, `w₂ := wPairU(g₂)` (χ-renormalized, `g₀ := v(1−w₀)`,
`g₂ := g₀(1+w₀)`),

`½Σ_{i≠j}∫(P_iP_jΦ)²·w₂(xᵢ,xⱼ) − μΣ_i∫(P_iΦ)²·(∫_y w₁(xᵢ,y))`
`= ½ℓ⁻³·(∫g₂)·S₂ − 8πa v·μ·S₁`

with `S₁ = cS1 ℓ Φ`, `S₂ = cS2 ℓ Φ`. -/
lemma q0_chosen_expect {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y)))
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g2 v h z) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
  have hw1i : IntegrableOn (wPairU ℓ (g0 v h)) (acube ℓ ×ˢ acube ℓ) :=
    integrableOn_w1c_acube hR hv_supp h hℓ hRℓ
  have hw2i : IntegrableOn (wPairU ℓ (g2 v h)) (acube ℓ ×ˢ acube ℓ) :=
    integrableOn_w2c_acube hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hw2v : (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) = ℓ ^ 3 * (∫ z : ℝ³, g2 v h z) :=
    w2c_acube_integral hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hw1v : (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p) = ℓ ^ 3 * (8 * π * a v) :=
    w1c_acube_integral hR hv_supp h hℓ hRℓ
  calc
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y)))
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) *
            (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
        - μ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p) *
            (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
      exact q0_expect_ae (N := N) (ℓ := ℓ) (μ := μ) (Φ := Φ) hℓ hΦc
        (w1 := wPairU ℓ (g0 v h)) (w2 := wPairU ℓ (g2 v h)) hw1i hw2i
    _ = (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g2 v h z) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
      rw [hw2v, hw1v]
      unfold cS1 cS2
      have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
      field_simp [hℓ3]

/-- Lower surrogate: `⟨Q₀^ren⟩ ≥ ½ℓ⁻³·(8πa v)·S₂ − 8πa v·μ·S₁`. -/
lemma q0_chosen_lower {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * cS2 ℓ Φ - (8 * π * a v) * μ * cS1 ℓ Φ
      ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y))) := by
  rw [q0_chosen_expect hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc]
  have hb : 8 * π * a v ≤ ∫ x : ℝ³, g2 v h x :=
    (g2_integral_bounds hR hv_nonneg hvrad hv_supp h).1
  have hk0 : 0 ≤ (1 / 2) * (ℓ ^ 3)⁻¹ := by positivity
  have hfac : (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v)
      ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, g2 v h x) :=
    mul_le_mul_of_nonneg_left hb hk0
  have hfin := mul_le_mul_of_nonneg_right hfac (cS2_nonneg : 0 ≤ cS2 ℓ Φ)
  nlinarith

/-- Upper surrogate: `⟨Q₀^ren⟩ ≤ ½ℓ⁻³·(16πa v)·S₂ − 8πa v·μ·S₁`. -/
lemma q0_chosen_upper {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y)))
      ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * (16 * π * a v) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
  rw [q0_chosen_expect hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc]
  have hb : (∫ x : ℝ³, g2 v h x) ≤ 16 * π * a v :=
    (g2_integral_bounds hR hv_nonneg hvrad hv_supp h).2
  have hk0 : 0 ≤ (1 / 2) * (ℓ ^ 3)⁻¹ := by positivity
  have hfac : (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, g2 v h x)
      ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * (16 * π * a v) :=
    mul_le_mul_of_nonneg_left hb hk0
  have hfin := mul_le_mul_of_nonneg_right hfac (cS2_nonneg : 0 ≤ cS2 ℓ Φ)
  nlinarith

end BoseGases

end Submission
