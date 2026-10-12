import ChallengeDeps
import Submission.PotChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# First per-state inequality of the FS §6–13 assembly (corpus centred box)

The first per-state lower bound for the sliding-box assembly, combining (at
fixed particle count `N`, for every continuous state `Φ` over the centred box
`abox N ℓ`):

  * `PotWords.potsplit` / `PotChosen.potsplit_chosen`  (FS lem:potsplit
    eq:potsplit): `qLHS = q0 + q1 + q2 + q3 + q4`;
  * `Q0Ren.q0_chosen_lower` (FS lem:QDecompSimpler eq:Q0n0): the condensate
    term `q0 ≥ ½ℓ⁻³·(8πa v)·S₂ − (8πa v)·μ·S₁` with the chosen kernels
    (`S₁ = cS1`, `S₂ = cS2` = condensate counts over the centred box);
  * `q4 ≥ 0` (`PotWords.q4_nonneg`, `wPairC_nonneg`): the positive 4Q square.

Result (`pot_q0_lower`): the potential word of the box Hamiltonian is bounded
below by the *renormalized Q0 value at the condensate counts* plus the three
lower `Q`-words `q1 + q2 + q3` and the positive `q4` — i.e. the per-state
form of FS's potential decomposition with the sharp Q0 term kept exactly and
the residual words left explicit (this is the entry inequality that the
cross-term bounds of `QCrossD` / one-body `OneBodyBound` / kinetic `centredGap`
will later dominate).  `pot_q0_lower_drop_q4` drops the (nonnegative) `q4`.

Hypothesis block (chosen branch): `0 ≤ v`, radial, `L¹`, support in
`ball 0 R`, `h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`, cell `ℓ` with
`0 < ℓ` and `R ≤ ℓ·chiR0`, chemical potential `0 ≤ μ`, state `Φ` continuous.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Q0-renormalized value at the condensate counts (FS eq:Q0n0 RHS with
`S₁ = cS1`, `S₂ = cS2`): `½ℓ⁻³(8πa v)S₂ − (8πa v)μS₁`. -/
noncomputable def q0RenVal {N : ℕ} {v : ℝ³ → ℝ} (ℓ μ : ℝ) (Φ : X N → ℝ) : ℝ :=
  (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * cS2 ℓ Φ - (8 * π * a v) * μ * cS1 ℓ Φ

/-- **First per-state inequality (fixed `N`)** — the potential word is at least
the renormalized-Q0 value plus the three lower words plus the positive Q4
square.  (Per-state form of FS `lem:potsplit` + `lem:QDecompSimpler`.) -/
theorem pot_q0_lower {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q0RenVal (N := N) (v := v) ℓ μ Φ
        + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  -- the chosen-kernel potential splitting qLHS = q0 + q1 + q2 + q3 + q4
  have hp := potsplit_chosen (N := N) (ℓ := ℓ) (μ := μ) hℓ
    (v := v) hv_nonneg hvrad hv_memL1 (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  -- the q0-chosen lower bound (kernels matched through wPairC/wPairU)
  have hl := q0_chosen_lower (N := N) (v := v) (R := R) (ℓ := ℓ) hR hv_nonneg hvrad hv_supp
    h hℓ hRℓ μ (Φ := Φ) hΦc
  have hq0eq : q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ =
      (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y))) := by
    rfl
  have hq0 : q0RenVal (N := N) (v := v) ℓ μ Φ ≤
      q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
    -- hl's expanded RHS is the compressed q0word (hq0eq); hl's LHS is q0RenVal.
    calc
      q0RenVal (N := N) (v := v) ℓ μ Φ
          ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
            - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
              (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y))) := by
              simpa [q0RenVal] using hl
      _ = q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
              exact hq0eq.symm
  -- qLHS = q0 + (q1+q2+q3+q4) and q0RenVal ≤ q0, so linarith closes
  rw [hp]
  linarith

/-- Dropping the (nonnegative) Q4 square: the potential word is at least the
renormalized-Q0 value plus the three lower words `q1 + q2 + q3`. -/
theorem pot_q0_lower_drop_q4 {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q0RenVal (N := N) (v := v) ℓ μ Φ
        + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hmain := pot_q0_lower (N := N) (ℓ := ℓ) (μ := μ) hℓ hv_nonneg hvrad hv_memL1
    (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hq4 : 0 ≤ q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ :=
    q4_nonneg (N := N) hℓ (wPairC_nonneg hv_nonneg ℓ)
  linarith

end BoseGases

end Submission
