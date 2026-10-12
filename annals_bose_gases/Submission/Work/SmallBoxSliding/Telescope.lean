import ChallengeDeps
import Submission.Work.SmallBoxSliding.Sliding
import Submission.Work.SmallBoxSliding.nBox_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The word-level telescoping of the sliding sum (FS `eq:appsliding`)

Integrating the localised per-box energy word `sboxEBWord` over ALL sliding
boxes `u` reproduces a *reference* word obtained by replacing the localised
kernels by their unrenormalised `u`-integrals.  The kernel-level identities
are the CLOSED `DLSmallKernels.chiSmallB_w_pair_uint_cancel` /
`chiSmallB_w1_pair_uint_cancel`; this module exposes the resulting
*reference words* and (with `Words.kinWordB_integral_u` and
`Telescope.qLHSwordB_integral_u`) the word-level identity

    ∫_u sboxEBWord h M ℓ d μ u Φ du = kinWordChi N M ℓ Φ + qLHSwordChi h M ℓ d μ Φ .

This is the structural half of FS `eq:appsliding`: it shows exactly what the
sliding sum telescopes to, so that the remaining input of the sliding-sum
identity is a *comparison of two explicit words*, not an operator statement.

## Why the comparison is NOT part of this module (recorded, see NOTES.md §7)

The reference word carries the factor `χ_M(x/ℓ)²`, whose peak is
`1/chiSmallNormSq M ≫ 1` (for `M = 8`: `≈ 132`), while the corpus global word
carries `chiScale ℓ` — so `kinWordChi` is a `χ_M²`-weighted average of the
Dirichlet energy and is *not* dominated by `kinWord` in general.  The
comparison therefore belongs to the SmallBoxA0 / FS error bookkeeping
(the `(R/λ₁)²`-type terms), not to a partition-of-unity identity.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- The reference kinetic word at the **repointed** layer: the `χ(·/ℓ)²`-weighted Dirichlet
energy — the `u`-integral of the localised kinetic word (`Words.kinWordB_integral_u`).  The
weight is the *corpus global* bump `chiScale ℓ`: after the repoint the `ℓ`-scale factor of
`chiSmallB` is `chiScale ℓ`, so the surviving weight is `χ(x/ℓ)²`, independent of `M`.  (The
argument `M` is kept for arity compatibility; it is unused.) -/
noncomputable def kinWordChi (N : ℕ) (M : ℕ) (ℓ : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N ℓ,
      (chiScale ℓ (x i)) ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-- The reference potential word: the corpus `qLHSword` at the *unrenormalised*
`χ_M`-localised kernels `χ_M(x/ℓ)h(x−y)χ_M(y/ℓ)` — the `u`-integral of the
localised potential word (`Telescope.qLHSwordB_integral_u`). -/
noncomputable def qLHSwordChi {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (Φ : X N → ℝ) : ℝ :=
  qLHSword (N := N) ℓ μ
    (fun x y => chiSmall M (ℓ⁻¹ • x) * v (x - y) * chiSmall M (ℓ⁻¹ • y))
    (fun x y => chiSmall M (ℓ⁻¹ • x) * g0 v h (x - y) * chiSmall M (ℓ⁻¹ • y))
    Φ

/-- The uncurried integrand of the localised potential word `qLHSwordB`
(so that `qLHSwordB h M ℓ d μ u Φ = ∫ x in abox N ℓ, qLHSBIntegrand … u x`). -/
noncomputable def qLHSBIntegrand {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (Φ : X N → ℝ) (u : ℝ³) (x : X N) : ℝ :=
  Φ x ^ 2 * (- μ * (∑ i : Fin N, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y)
    + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2)))

/-- The integrand of the reference potential word `qLHSwordChi`
(so that `qLHSwordChi h M ℓ d μ Φ = ∫ x in abox N ℓ, qLHSChiIntegrand … x`). -/
noncomputable def qLHSChiIntegrand {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (Φ : X N → ℝ) (x : X N) : ℝ :=
  Φ x ^ 2 * (- μ * (∑ i : Fin N, ∫ y in acube ℓ,
        chiSmall M (ℓ⁻¹ • (x i)) * g0 v h (x i - y) * chiSmall M (ℓ⁻¹ • y))
    + (1 / 2) * (∑ q ∈ pairSet N,
        chiSmall M (ℓ⁻¹ • (x q.1)) * v (x q.1 - x q.2) * chiSmall M (ℓ⁻¹ • (x q.2))))

/-- `qLHSwordB` is the `abox`-integral of `qLHSBIntegrand`. -/
theorem qLHSwordB_eq_integral {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) :
    qLHSwordB (N := N) h M ℓ d μ u Φ = ∫ x in abox N ℓ, qLHSBIntegrand h M ℓ d μ Φ u x := rfl

/-- `qLHSwordChi` is the `abox`-integral of `qLHSChiIntegrand`. -/
theorem qLHSwordChi_eq_integral {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (Φ : X N → ℝ) :
    qLHSwordChi (N := N) h M ℓ d μ Φ = ∫ x in abox N ℓ, qLHSChiIntegrand h M ℓ d μ Φ x := rfl

/-- The two halves of `sboxEBWord` sum as expected (definitional). -/
theorem sboxEBWord_eq_kin_add_pot {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) :
    sboxEBWord (N := N) h M ℓ d μ u Φ
      = kinWordB N M ℓ d u Φ + qLHSwordB (N := N) h M ℓ d μ u Φ := rfl


end Work.SmallBoxSliding
