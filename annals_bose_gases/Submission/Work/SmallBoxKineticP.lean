import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.SmallBoxModeReal
import Submission.Work.SmallBoxPairAPairing
import Submission.Work.SmallBoxSharpMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-280 — the D1 p-space kinetic word

FS `lm:appbogolubov`'s kinetic term is `Σ_i Q_iχ_i[√−Δ_i − c]₊²χ_iQ_i`; its
faithful transcription in the corpus's mode language is the p-space integral

  `(2π)⁻³ ∫_p [|p|−c]₊² · (N_{u_p} + N_{v_p}) dp`,

where `g_p = Q_B(χ_B e^{−ipx}) = qMode s p` (`u_p = Re g_p`, `v_p = Im g_p`) and
`N_g` is the mode number operator.  Because the corpus's `b`-operators are
`bDag g = |B|⁻¹a†(g)a(1)`, `bAnn g = |B|⁻¹a†(1)a(g)`, the quadratic form of
`bDag g ∘ bAnn g` is `∫(boxOp 1 g Ψ)²`, i.e. `s³ ∫(τ_g Ψ)²`; this is exactly the
`P_g` of `bogoliubov_perP`.  Hence the per-`p` quadratic form of the D1 word is

  `F(p)·(P_{u_p} + P_{v_p})`

which is precisely the `A(P+Q)` of `tau_two_mode_bound`/`bogoliubov_perP`.

## Contents

* `boxOp_gg_integral_eq` — the slice decomposition `∫Ψ·(boxOp g g Ψ)
  = Σ_i ∫_r (∫_z g z·slice_r z dz)²` (no cross terms) — the identity that the
  proof of `SmallBoxTauComm.boxOp_gg_nonneg` actually establishes;
* `boxOp_one_sq_eq` — the bilinear adjoint form `∫(boxOp 1 g Ψ)²
  = ∫Ψ·(boxOp g 1 (boxOp 1 g Ψ))` (with the cross terms);
* `tauAnn_sq_integral` — `∫(τ_g Ψ)² = (s³)⁻¹∫(boxOp 1 g Ψ)²`;
* `modeP` and the D1 p-space kinetic word `kinWord`, with `kinWord_nonneg`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The slice decomposition of `∫Ψ·(boxOp g g Ψ)` -/

/-- **The slice (no cross term) decomposition of the `boxOp` quadratic form.**
`∫Ψ·(boxOp s g g Ψ) = Σ_i ∫_r (∫_z g z · Ψ(kcInsN i (z,r)) dz)²`. -/
lemma boxOp_gg_integral_eq {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x)
      = ∑ i : Fin (n + 1), ∫ r in abox n s,
          (∫ z in acube s, g z * Ψ (kcInsN n i (z, r))) ^ 2 := by
  haveI : IsFiniteMeasure (cubeMeas s) := isFiniteMeasure_cubeMeas hs
  have hcont : ∀ i : Fin (n + 1), Continuous fun p : X (n + 1) × ℝ³ =>
      (Ψ p.1 * g (p.1 i)) * (g p.2 * Ψ (Function.update p.1 i p.2)) := fun i =>
    ((hΨ.comp continuous_fst).mul (hg.comp ((continuous_apply i).comp continuous_fst))).mul
      ((hg.comp continuous_snd).mul (hΨ.comp (continuous_fst.update i continuous_snd)))
  have h1 : (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x)
      = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ∫ z in acube s,
          (Ψ x * g (x i)) * (g z * Ψ (Function.update x i z)) := by
    rw [show (fun x => Ψ x * boxOp s g g Ψ x) = fun x => ∑ i : Fin (n + 1),
        ∫ z in acube s, (Ψ x * g (x i)) * (g z * Ψ (Function.update x i z)) by
      funext x
      rw [boxOp, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (∫ z in acube s, (Ψ x * g (x i)) * (g z * Ψ (Function.update x i z)))
          = (Ψ x * g (x i)) * ∫ z in acube s, g z * Ψ (Function.update x i z) from
        integral_const_mul _ _]
      ring]
    exact integral_finsetSum _ (fun i _ => integrable_iterated (n := n) hs (hcont i))
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_peel_iterated hs i (hcont i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [kc_insN_apply_same, update_kcInsN]
  have hpt : (fun y : ℝ³ => ∫ z in acube s, (Ψ (kcInsN n i (y, r)) * g y) *
        (g z * Ψ (kcInsN n i (z, r))))
      = fun y => (g y * Ψ (kcInsN n i (y, r))) *
          (∫ z in acube s, g z * Ψ (kcInsN n i (z, r))) := by
    funext y
    rw [show (∫ z in acube s, (Ψ (kcInsN n i (y, r)) * g y) *
          (g z * Ψ (kcInsN n i (z, r))))
        = (Ψ (kcInsN n i (y, r)) * g y) * ∫ z in acube s, g z * Ψ (kcInsN n i (z, r)) from
      integral_const_mul _ _]
    ring
  rw [hpt, integral_mul_const]
  ring

/-! ## 2 The bilinear adjoint identity for `∫(boxOp 1 g Ψ)²` -/

/-- **`∫(boxOp s 1 g Ψ)² = ∫Ψ·(boxOp s g 1 (boxOp s 1 g Ψ))`** — the quadratic form of
`bDag g ∘ bAnn g` in the corpus's bilinear convention (`boxOp_adjoint`). -/
lemma boxOp_one_sq_eq {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s, Ψ x * boxOp s g (fun _ => (1 : ℝ))
          (boxOp s (fun _ => (1 : ℝ)) g Ψ) x := by
  have h := boxOp_adjoint (f := g) (h := fun _ => (1 : ℝ)) (Φ := Ψ)
    (Ψ := boxOp s (fun _ => (1 : ℝ)) g Ψ) hs hg continuous_const hΨ
    (continuous_boxOp hs continuous_const hg hΨ)
  calc (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) *
          (boxOp s (fun _ => (1 : ℝ)) g Ψ x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x in abox (n + 1) s, Ψ x * boxOp s g (fun _ => (1 : ℝ))
          (boxOp s (fun _ => (1 : ℝ)) g Ψ) x := h.symm

/-! ## 3 The `τ`-normalisation -/

/-- `∫(τ_g Ψ)² = (s³)⁻¹ ∫(boxOp s 1 g Ψ)²` (the `tauAnn_eq` normalisation). -/
lemma tauAnn_sq_integral {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      = (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 := by
  have hkey : ((Real.sqrt (s ^ 3))⁻¹) ^ 2 = (s ^ 3)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  calc (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s,
          (s ^ 3)⁻¹ * (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only []
          rw [tauAnn_eq hs g Ψ x, mul_pow, hkey])
    _ = (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]

/-! ## 4 The D1 p-space kinetic word -/

/-- The per-`p` mode content of a 1-particle state: `P_g = ∫(τ_g Ψ)²`, i.e.
`(s³)⁻¹∫(boxOp s 1 g Ψ)²` — the `P` of `bogoliubov_perP`. -/
noncomputable def modeP (s : ℝ) {n : ℕ} (g : ℝ³ → ℝ) (Ψ : X (n + 1) → ℝ) : ℝ :=
  (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2

lemma modeP_nonneg {s : ℝ} (hs : 0 < s) {n : ℕ} (g : ℝ³ → ℝ) (Ψ : X (n + 1) → ℝ) :
    0 ≤ modeP s g Ψ := by
  refine mul_nonneg (by positivity) ?_
  exact integral_nonneg fun x => sq_nonneg _


/-- **The bridge to `bogoliubov_perP`**: `modeP` IS the `P_g` of the per-`p` Bogoliubov
bound (`SmallBoxModeReal.bogoliubov_perP`), i.e. `∫(τ_gΨ)²`. -/
lemma modeP_eq_tauAnn_sq {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    modeP s g Ψ = ∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2 :=
  (tauAnn_sq_integral hs hg hΨ).symm

/-- **The D1 p-space kinetic word** `kinPWord` — FS's `Σ_i Q_iχ_i[√−Δ_i − c]₊²χ_iQ_i` transcribed
as `(2π)⁻³ ∫_p [|p|−c]₊² (P_{u_p} + P_{v_p}) dp` with `g_p = qMode s p = u_p + i v_p`. -/
noncomputable def kinPWord (s c : ℝ) {n : ℕ} (Φ : X (n + 1) → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ ^ 3 * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
    (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)

/-- the kinetic word is nonnegative (both factors are nonnegative pointwise). -/
lemma kinPWord_nonneg {s c : ℝ} (hs : 0 < s) {n : ℕ} (Φ : X (n + 1) → ℝ) :
    0 ≤ kinPWord s c Φ := by
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg fun p => ?_
  refine mul_nonneg (fsKinCoeff_nonneg c ‖p‖) ?_
  exact add_nonneg (modeP_nonneg hs _ Φ) (modeP_nonneg hs _ Φ)


/-! ## 5 The D1 target with the faithful (p-space) kinetic word -/

/-- **THE D1 TARGET** — FS `eq:refinedaprioribog` transcribed with the FAITHFUL
kinetic word `kinWord` (the p-space `(2π)⁻³∫[|p|−c]₊²(N_{u_p}+N_{v_p})dp`), i.e.
FS's `Σ_i Q_iχ_i[√−Δ_i − c]₊²χ_iQ_i`.

This SUPERSEDES `SmallBoxSharpMass.lm_appbogolubov_refined_concrete`, whose left-hand
side used the box-NEUMANN kinetic sum `kModeWord` (the eigenbasis of the small box):
that transcription is only the `O(R/s)`-approximation of FS's word, and — more
importantly — the Neumann basis has no `(p,−p)` pairing, so the Bogoliubov step cannot
be performed there (Sessions 272/278/279).  The slack is `(1 + C·R/s)`: the box-mode ⇄
continuum discrepancy is FIRST order in `R/s` (Session-268 numerical study: the box
Neumann Green function differs from the continuum one by `O(R/s)`, always with a
favourable sign), and `δ ≳ s` in the application (Session-269), so `R/δ ≤ C·R/s`.

The right-hand side is otherwise unchanged from the Session-269 statement: the sharp
mass `−½(1+C·R/s)(1+Cc₀(av))·g0w0Mass·(N̂+1)²/s³`, the log/`c₀³` error bracket and
the `n₊`-term.

SESSION-284 added four hypotheses, each an honest input of FS's context (see
`Submission/Work/SmallBoxD1Assembly.lean`):
* `hN : 1 ≤ N` — the pairing machinery is indexed by `X (p+2)` and the `(M−1)`-slack needs `M ≥ 2`;
* `hav : 0 < a v` — needed for the positivity of the coefficient `𝒜(q) = s³[‖q‖−c₀]₊²(M−1)/M + 2K_s·a v`
  at every `q` (the case `a v = 0`, i.e. `v = 0` a.e., is TRIVIAL: then `W₁ = 0`, `ℬ = 0`,
  `q4PairWord = 0`, `g0w0Mass = 0` and both sides vanish);
* `hdil : 2·c₀·(a v) ≤ 1` — the dilute regime, required by the exterior bracket
  `pBracket_inv_sub_sq_le` and by the log comparison;
* `hWfin` — the FINITENESS of the Newtonian energy `∬W₁(x)W₁(y)/‖x−y‖` (equivalently the
  integrability of `q ↦ Ŵ₁(q)²/‖q‖²`); without it the intermediate Bochner integrals are junk `0`
  and the chain silently loses the main term;
* `hNewton` — the M1 input `(2π)⁻³∫_q Ŵ₁(q)²/‖q‖² ≤ 2(1+6·C_t·(R/s)²)·g0w0Mass` (proved in
  `Submission/Work/SmallBoxD1Assembly.d1_M1_bound` from `mainMassCoeff_le_coarse` and the
  x-space finiteness; kept as a hypothesis so that the D1 chain does not have to carry the
  Taylor/`conv3 chi chi` bookkeeping). -/
def lm_appbogolubov_pWord {N : ℕ} {s c0 : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hsR : R ≤ s * chiR0) (hN : 1 ≤ N) (hav : 0 < a v) (hdil : 2 * c0 * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
            (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * g0w0Mass (v := v) h) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : X (N + 1) → ℝ) (hΦc : ContDiff ℝ ∞ Φ),
    (∫ x in abox (N + 1) s, (Φ x) ^ 2) = 1 →
    kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) ≥
      - (1 / 2 : ℝ) * (1 + C * (R / s)) * (1 + C * c0 * (a v))
          * g0w0Mass (v := v) h * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
      - C * ((a v) ^ 2 * c0 * Real.log ((c0 * (a v))⁻¹)
                * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
            + (a v) ^ 4 * (c0 ^ 3)⁻¹ * ((((N : ℝ) + 1) / s ^ 3) ^ 3) * (((N : ℝ) + 1) / s ^ 3) * s ^ 3
            + (a v) * c0 ^ 3 * (((N : ℝ) + 1) / s ^ 3) * s ^ 3)
      - C * (a v) * (((N : ℝ) + 1) / s ^ 3) * cnPlus s Φ


/-! ## 6 The D1 pairing word in the per-`p` parametrisation -/

/-- **The A₂-link re-parametrised to FS's momentum variable.**
`SmallBoxPairAPairing.q4PairWord_eq_tau_pairing` writes the corpus's pair word as
`∫_u 𝓕W₁(u)·G((2π)•u)du` with `G(p) = ∫Φ·(bDag (qMode (−p)))(bDag (qMode p) Φ)`.
Substituting `q = (2π)•u` (`MeasureTheory.integral_comp_smul`, the pointwise identity
`H((2π)u) = F(u)G((2π)u)` for `H(y) = F((2π)⁻¹y)G(y)`) gives the SAME integral in
FS's momentum variable `q`, with the weight `ℬ(q) = 𝓕W₁((2π)⁻¹•q)` — which is FS's
`\widehat{WS_1}(q) = ∫WS_1(x)e^{−i⟨q,x⟩}dx` (`ℬ(q) = \hat W₁(q)` since Mathlib's `𝓕`
uses `e^{−2πi⟨ξ,x⟩}`).  This is the form in which the pairing combines with the D1
kinetic word `kinPWord` (same `q`-parametrisation, same `qMode q` modes). -/
theorem q4PairWord_eq_pPairing {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ((q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) : ℝ) : ℂ)
      = (((2 * π : ℝ) ^ 3)⁻¹ : ℂ) *
          ∫ q, FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
                (((2 * π : ℝ)⁻¹) • q) *
            (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-q))
              (bDag ℓ (qMode ℓ q) (fun y => (Φ y : ℂ))) x) := by
  rw [q4PairWord_eq_tau_pairing hℓ hR hRℓ hv_supp h hΦ]
  have hpt : (fun u : ℝ³ =>
        FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
          (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-((2 * π : ℝ) • u)))
            (bDag ℓ (qMode ℓ ((2 * π : ℝ) • u)) (fun y => (Φ y : ℂ))) x))
      = fun u : ℝ³ => (fun q : ℝ³ =>
          FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
            (((2 * π : ℝ)⁻¹) • q) *
          (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-q))
            (bDag ℓ (qMode ℓ q) (fun y => (Φ y : ℂ))) x)) ((2 * π : ℝ) • u) := by
    funext u
    simp only []
    rw [show ((2 * π : ℝ)⁻¹) • ((2 * π : ℝ) • u) = u from by
      rw [smul_smul, inv_mul_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_smul]]
  rw [hpt]
  rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun q : ℝ³ => FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
      (((2 * π : ℝ)⁻¹) • q) *
      (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-q))
        (bDag ℓ (qMode ℓ q) (fun y => (Φ y : ℂ))) x)) (2 * π) (hR := by positivity)]
  rw [finrank_euclideanSpace, Fintype.card_fin]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]

end BoseGases
end Submission
