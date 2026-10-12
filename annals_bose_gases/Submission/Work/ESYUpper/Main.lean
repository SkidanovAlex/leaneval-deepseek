import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.ESYUpper.Exists_pow_eq_inv
import Submission.Work.ESYUpper.KinWord_const_mul
import Submission.Work.ESYUpper.PairStateZ_scale
import Submission.Work.ESYUpper.QLHSword_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ESYUpper` — the Rayleigh reduction and the packaging

## 1. The normalisation conjunct is *free*

The residual `Work.SecondOrder.QuasiFreeBound` (and the TrialState residual
`SecondOrderUpperBound` behind it) asks for a **normalised** state of the family
`quasiFreeState N s c r hr ω`.  But `s` — the condensate amplitude — is a free
parameter of the family, and *both* the energy word `pairStateE` and the norm
square `pairStateZ` are homogeneous of degree `2` in the state:

    pairState N (y ↦ s · ψ y) wt G = sᴺ · pairState N ψ wt G        (`PairState_scale`)
    kinWord (s · Φ)  = s² · kinWord Φ ,  qLHSword (s · Φ) = s² · qLHSword Φ
    pairStateZ (s · ψ) = s^{2N} · pairStateZ ψ                      (`PairStateZ_scale`)

Consequently the *only* content of the normalisation conjunct is the
positivity of the box norm square: for `1 ≤ N` and `pairStateZ ≠ 0` one can
*solve* for `s` (`Exists_pow_eq_inv`: `s^{2N} = Z⁻¹`), and then

    ∫ (pairState(s))² = s^{2N} Z = 1 ,
    Rayleigh quotient ≤ θ  ⟺  pairStateE(s) ≤ θ .

This is why the chapter's residual `ESYRayleigh` is stated **without** the
normalisation conjunct and with the *Rayleigh-quotient* inequality
`pairStateE ≤ θ · pairStateZ`: no cluster/Wick *evaluation* of the double sum
`Σ_{p,q} w_p w_q ∫ pairComp_p pairComp_q` is needed for the norm — only its
positivity (`NOTES.md` §3).  The cluster machinery
(`Reduce.pairStateZ_eq_doubleSum`, `Reduce.pairState_eq_sum_components`) is
still what the *energy* stage uses.

## 2. The packaging

    ESYUpperBound'  ──quasiFreeBound'_of_ESYUpperBound'──▶  QuasiFreeBound'
        │                                                         │
        │                                       (SecondOrder/Main) ▼
        ▼                                                  PairFamilyBound'
    secondOrderUpperBound'_of_ESYUpperBound' ─────────────▶ SecondOrderUpperBound'
        │
        ▼
    exists_hEgc_of_ESYUpperBound'  ──▶  the consumer's `hEgc` shape (any `J ≥ C`)

## 3. The model integral

`Phi.lean` (via `PhiDefs`/`Phi_sub`/`Sub_integral`) proves ESY's
`Φ(0) = √512/15`, and `EsyQ_const` identifies
`(π/(2π)³)·(8π)^{5/2}·Φ(0) = 4π·(128/(15√π))`, i.e. the mode-sum limit of the
ESY `Q` is exactly `4πaNϱ·(128/(15√π))(a³ϱ)^{1/2}` — the sharp LHY second-order
term.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.ESYUpper

open Submission.BoseGases
open _root_.BoseGases
open Work.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Homogeneity of the energy word -/

/-- **Degree-2 homogeneity of the energy word.**  Scaling the condensate
orbital `ψ` by `s` scales `pairState` by `s^N`, hence both the kinetic word and
the potential word by `s^{2N}`, hence `pairStateE` by `s^{2N}`.  This is the
identity that makes the condensate amplitude `s` the normalisation degree of
freedom of the family. -/
theorem pairStateE_scale {N : ℕ} (ℓ μ s : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (ψ : ℝ³ → ℝ) (wt : ℕ → ℝ) (G : ℝ³ → ℝ³ → ℝ) :
    pairStateE N ℓ μ v h (fun y => s * ψ y) wt G
      = s ^ (2 * N) * pairStateE N ℓ μ v h ψ wt G := by
  have hfun : pairState N (fun y => s * ψ y) wt G
      = fun x : X N => s ^ N * pairState N ψ wt G x :=
    funext fun x => PairState_scale N s ψ wt G x
  have hp : s ^ (2 * N) = (s ^ N) ^ 2 := by
    rw [Nat.mul_comm 2 N, pow_mul]
  unfold pairStateE
  rw [hfun, KinWord_const_mul N ℓ (s ^ N) (pairState N ψ wt G),
    QLHSword_const_mul ℓ μ (s ^ N) _ _ (pairState N ψ wt G), ← hp]
  ring

/-! ## The Rayleigh reduction -/

/-- **`ESYRayleigh` reaches the normalised residual `QuasiFreeBound`.**  Given
the Rayleigh-quotient inequality for the *unnormalised* (`s = 1`) member of the
concrete squeezing family, one solves `s^{2N} = Z⁻¹` for the condensate
amplitude and obtains a member of the family that is box-normalised and whose
energy word meets the threshold. -/
theorem quasiFreeBound_of_rayleigh {N : ℕ} (hN : 1 ≤ N) {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hR : ESYRayleigh N ℓ μ C v h) : QuasiFreeBound N ℓ μ C v h := by
  obtain ⟨c, r, hr, hcont, hZpos, hE⟩ := hR
  set om : ℝ³ → ℝ := Classical.choose h with hom
  set wt : ℕ → ℝ := bogWeight c with hwt
  set G : ℝ³ → ℝ³ → ℝ := bogKernel r hr om with hG
  obtain ⟨s, hs⟩ := Exists_pow_eq_inv hN hZpos
  have h1 : TrialState.orbConst s = fun y => s * (TrialState.orbConst 1) y := by
    funext y; simp [TrialState.orbConst]
  have hscale : quasiFreeState N s c r hr om
      = fun x : X N => s ^ N * quasiFreeState N 1 c r hr om x := by
    funext x
    show pairState N (TrialState.orbConst s) wt G x
      = s ^ N * pairState N (TrialState.orbConst 1) wt G x
    rw [h1]
    exact PairState_scale N s (TrialState.orbConst 1) wt G x
  have hsq : 0 ≤ s ^ (2 * N) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg s) N
  have hZ : s ^ (2 * N) * pairStateZ N ℓ (TrialState.orbConst 1) wt G = 1 := by
    rw [hs, inv_mul_cancel₀ (ne_of_gt hZpos)]
  have hZs : pairStateZ N ℓ (TrialState.orbConst s) wt G
      = s ^ (2 * N) * pairStateZ N ℓ (TrialState.orbConst 1) wt G := by
    rw [h1]
    exact PairStateZ_scale N ℓ s (TrialState.orbConst 1) wt G
  have hEs : pairStateE N ℓ μ v h (TrialState.orbConst s) wt G
      = s ^ (2 * N) * pairStateE N ℓ μ v h (TrialState.orbConst 1) wt G := by
    rw [h1]
    exact pairStateE_scale (N := N) ℓ μ s v h (TrialState.orbConst 1) wt G
  refine ⟨s, c, r, hr, ?_, ?_, ?_⟩
  · rw [hscale]
    exact hcont.const_mul _
  · have hInt : (∫ x in abox N ℓ, (quasiFreeState N s c r hr om x) ^ 2)
        = pairStateZ N ℓ (TrialState.orbConst s) wt G := rfl
    rw [hInt, hZs, hZ]
  · have hkey : kinWord N ℓ (quasiFreeState N s c r hr om)
        + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h))
            (quasiFreeState N s c r hr om)
        = pairStateE N ℓ μ v h (TrialState.orbConst s) wt G := rfl
    rw [hkey, hEs]
    calc s ^ (2 * N) * pairStateE N ℓ μ v h (TrialState.orbConst 1) wt G
        ≤ s ^ (2 * N) * ((- 4 * π * μ ^ 2 * (a v) * ℓ ^ 3
              * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * pairStateZ N ℓ (TrialState.orbConst 1) wt G) :=
          mul_le_mul_of_nonneg_left hE hsq
      _ = (- 4 * π * μ ^ 2 * (a v) * ℓ ^ 3
              * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * (s ^ (2 * N) * pairStateZ N ℓ (TrialState.orbConst 1) wt G) := by ring
      _ = - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3
              * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by rw [hZ, mul_one]

/-! ## The chain to the consumers -/

/-- The dilute-window ESY residual gives the concrete quasi-free residual. -/
theorem quasiFreeBound'_of_ESYUpperBound' {N : ℕ} {ℓ μ C ε : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : ESYUpperBound' N ℓ μ C ε v h) : QuasiFreeBound' N ℓ μ C ε v h :=
  fun hN hε => quasiFreeBound_of_rayleigh hN (hb hN hε)

/-- **The chapter's packaging theorem.**  The ESY/Yau–Yin variational residual
(in Rayleigh form, in the dilute window) gives the corrected TrialState residual
`SecondOrderUpperBound'`, through the SecondOrder chapter's reducers. -/
theorem secondOrderUpperBound'_of_ESYUpperBound' {N : ℕ} {ℓ μ C ε : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : ESYUpperBound' N ℓ μ C ε v h) : SecondOrderUpperBound' N ℓ μ C ε v h :=
  secondOrderUpperBound'_of_pairFamilyBound'
    (pairFamilyBound'_of_quasiFreeBound' (quasiFreeBound'_of_ESYUpperBound' hb))

/-- **The consumer-facing theorem.**  From the ESY variational residual one
obtains the exact `hEgc` shape of `APrioriSkeleton.APrioriData`: a normalised
continuous box state whose `H_Λ(μ)`-energy is at most
`−4πμ²(a v)ℓ³(1 − J(μ(a v)³)^{1/2})`, for every `J ≥ C`. -/
theorem exists_hEgc_of_ESYUpperBound' {N : ℕ} {ℓ μ C J ε : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hN : 1 ≤ N) (hε : μ * (a v) ^ 3 ≤ ε)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : 0 ≤ C) (hCJ : C ≤ J)
    (hb : ESYUpperBound' N ℓ μ C ε v h) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :=
  exists_hEgc_of_quasiFreeBound' h hN hε hℓ hμ ha hC hCJ
    (quasiFreeBound'_of_ESYUpperBound' hb)

end Work.ESYUpper
