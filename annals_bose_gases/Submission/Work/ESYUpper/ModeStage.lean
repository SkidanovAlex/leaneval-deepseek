import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.ESYUpper.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ESYUpper` — the named stage residual `ModeStage`

This module turns the roadmap of `NOTES.md` §3 into **Lean-level stage
residuals**, in the reducer pattern of the SecondOrder chapter: a single named
`Prop` (`Work.ESYUpper.ModeStage`) bundles the two remaining stages, and the
reductions from it down to the TrialState residual and the consumer's `hEgc` are
*proved*.

The two conjuncts of `ModeStage`, for a member `(ψ, wt, G)` of the pair-excited
family:

* **(stage E — the energy evaluation)** its energy word is the ESY mode
  functional
  `pairStateE = −4πaμN + esyQ s μ p2 V f + Ω₂ + Ω₄`
  for the box's mode data `(s, p2, V, f, Vsub, V2p, Λ, Vup)`, and its pairing
  kernel is `DiagonalKernel` — diagonal in an orthonormal box-mode family, which
  is the structural hypothesis under which the Wick/hafnian evaluation of the
  family (ESY's `lm:EM`) becomes the mode sum;
* **(stage Ω + L + N2 — the momentum-space inequality)**
  `−4πaμN + esyQ + Ω₂ + Ω₄ ≤ θ_C · pairStateZ`.

The Ω half of the second conjunct is already available: `AmplitudeBounds`
proves the ESY amplitude bounds and `Omega2Omega4_bound` converts them into the
`Ω₂ + Ω₄` estimate.  What the second conjunct still needs is stage **L** (the
mode-sum limit `esyQ → 4πaNϱ·(128/(15√π))(a³ϱ)^{1/2}`, whose *value* is proved
in `EsyQ_const`/`EsyQLimitValue`) and the norm identity `N2`.

`pairFamilyBound_of_modeStage` below proves `ModeStage → PairFamilyBound`
(via the same `s^{2N}`-scaling used in `pairFamilyBound_of_quadFormRayleigh`),
and `secondOrderUpperBound'_of_modeStage` /
`exists_hEgc_of_modeStage` reach the TrialState residual and `hEgc`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.ESYUpper

open Submission.BoseGases
open _root_.BoseGases
open Work.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The mode-diagonal structure of a pairing kernel** (stage E0).  `G` is
diagonal in an `L²(acube ℓ)`-orthonormal family of box modes: there are a finite
mode set, an orthonormal family `φ` and amplitudes `c` with
`G x y = Σ_k c_k φ_k(x) φ_k(y)`.  This is exactly the structure that makes the
Wick evaluation of the pair-excited state a *mode sum*. -/
def DiagonalKernel (ℓ : ℝ) (G : ℝ³ → ℝ³ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (s : Finset ι)
    (φ : ι → ℝ³ → ℝ) (c : ι → ℝ),
    (∀ k ∈ s, ∀ l ∈ s,
        (∫ x in acube ℓ, φ k x * φ l x) = if k = l then 1 else 0) ∧
      (∀ x y : ℝ³, G x y = ∑ k ∈ s, c k * φ k x * φ k y)

/-- **The named stage residual of the ESY upper-bound chapter.**  A member of the
pair-excited family with a mode-diagonal pairing kernel whose energy word *is*
the ESY mode functional (stage E), and whose mode functional satisfies the
momentum-space Rayleigh inequality (stages Ω + L + N2). -/
def ModeStage (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ (ψ : ℝ³ → ℝ) (wt : ℕ → ℝ) (G : ℝ³ → ℝ³ → ℝ) (s : Finset ℝ³) (Λ Vup : ℝ)
    (p2 V f : ℝ³ → ℝ) (Vsub : ℝ³ → ℝ³ → ℝ) (V2p : ℝ³ → ℝ),
    (∀ x y : ℝ³, G x y = G y x) ∧ Continuous (pairState N ψ wt G) ∧
      DiagonalKernel ℓ G ∧ 0 < pairStateZ N ℓ ψ wt G ∧ 0 < Λ ∧ Λ = ℓ ^ 3 ∧
      (∀ p ∈ s, p2 p = ‖p‖ ^ 2) ∧
      pairStateE N ℓ μ v h ψ wt G
        = - 4 * π * (a v) * μ * (N : ℝ)
          + esyQ s μ p2 V f + Omega2 s Vup Λ V (optAmp μ V f)
          + Omega4 s Vup Λ Vsub V2p (optAmp μ V f) ∧
      (- 4 * π * (a v) * μ * (N : ℝ)
          + esyQ s μ p2 V f + Omega2 s Vup Λ V (optAmp μ V f)
          + Omega4 s Vup Λ Vsub V2p (optAmp μ V f)
        ≤ (- 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * pairStateZ N ℓ ψ wt G)

/-- **`ModeStage` implies the family residual** (for `1 ≤ N`), by the same
`s^{2N}`-scaling that removes the normalisation conjunct: solve
`s^{2N} = Z⁻¹` and use that both sides of the two conjuncts scale by `s^{2N}`. -/
theorem pairFamilyBound_of_modeStage {N : ℕ} (hN : 1 ≤ N) {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hM : ModeStage N ℓ μ C v h) : PairFamilyBound N ℓ μ C v h := by
  obtain ⟨ψ, wt, G, s, Λ, Vup, p2, V, f, Vsub, V2p, hsym, hcont, hdiag, hZpos,
    hΛpos, hΛ, hp2, hid, hineq⟩ := hM
  obtain ⟨σ, hσ⟩ := Exists_pow_eq_inv hN hZpos
  have hcont' : Continuous (pairState N (fun y => σ * ψ y) wt G) := by
    rw [show pairState N (fun y => σ * ψ y) wt G
          = fun x : X N => σ ^ N * pairState N ψ wt G x from
        funext fun x => PairState_scale N σ ψ wt G x]
    exact hcont.const_mul _
  have hZ : pairStateZ N ℓ (fun y => σ * ψ y) wt G = 1 := by
    rw [PairStateZ_scale N ℓ σ ψ wt G, hσ, inv_mul_cancel₀ (ne_of_gt hZpos)]
  refine ⟨fun y => σ * ψ y, wt, G, hsym, hcont', hZ, ?_⟩
  rw [pairStateE_scale (N := N) ℓ μ σ v h ψ wt G, hid]
  have hsq : 0 ≤ σ ^ (2 * N) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg σ) N
  calc σ ^ (2 * N) * (- 4 * π * (a v) * μ * (N : ℝ)
        + esyQ s μ p2 V f + Omega2 s Vup Λ V (optAmp μ V f)
        + Omega4 s Vup Λ Vsub V2p (optAmp μ V f))
      ≤ σ ^ (2 * N) * ((- 4 * π * μ ^ 2 * (a v) * ℓ ^ 3
            * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * pairStateZ N ℓ ψ wt G) :=
        mul_le_mul_of_nonneg_left hineq hsq
    _ = (- 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * (σ ^ (2 * N) * pairStateZ N ℓ ψ wt G) := by ring
    _ = - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3
          * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
        rw [hσ, inv_mul_cancel₀ (ne_of_gt hZpos), mul_one]


/-- **`ModeStage` gives the corrected TrialState residual** in the dilute window. -/
theorem secondOrderUpperBound'_of_modeStage {N : ℕ} {ℓ μ C ε : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hM : ∀ _hN : 1 ≤ N, ∀ _hε : μ * (a v) ^ 3 ≤ ε, ModeStage N ℓ μ C v h) :
    SecondOrderUpperBound' N ℓ μ C ε v h :=
  fun hN hε =>
    secondOrderUpperBound_of_pairFamily (pairFamilyBound_of_modeStage hN (hM hN hε))

/-- **The consumer-facing theorem for the named stage residual.**  From
`ModeStage` one obtains the exact `hEgc` shape of `APrioriSkeleton.APrioriData`
for every `J ≥ C`. -/
theorem exists_hEgc_of_modeStage {N : ℕ} {ℓ μ C J ε : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hN : 1 ≤ N) (hε : μ * (a v) ^ 3 ≤ ε)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : 0 ≤ C) (hCJ : C ≤ J)
    (hM : ModeStage N ℓ μ C v h) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :=
  exists_hEgc_of_secondOrder' h hN hε hℓ hμ ha hC hCJ
    (secondOrderUpperBound'_of_modeStage (fun _ _ => hM))

end Work.ESYUpper
