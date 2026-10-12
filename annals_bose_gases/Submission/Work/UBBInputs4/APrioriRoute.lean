import ChallengeDeps
import Submission.Work.UBBInputs4.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs4.APrioriRoute` — FS's own order of steps at the extended class

Round 2 (`Submission/Work/UBBInputs2/`) offered two routes to `hpres`: FS's *a-priori* route
(`thm:aprioriHLambda` for `eq:apriorinn+`, then §9–11 for the low windowed states,
i.e. `AprioriNPlusH + BogoliubovLowH`) and the `lem:LocMatrices` route
(`LocMatricesResidual + BogoliubovWindowedH`).  Round 3/4 refined the second route (the
localisation is *itself* decomposed by the Lieb–Solovej matrix theorem), and round 4 moved
both routes to the **extended (Neumann) class** that FS's own states live in.

`Residuals.lean` carries the `lem:LocMatrices` route.  This file carries FS's *a-priori*
route at the same class, so the lead can use whichever hypothesis list is closer to the
delivered corpus layers (the a-priori window is what the corpus's sliding/localisation
chapter `Work.SmallBoxSliding` supplies; the `lem:LocMatrices` window is what round 3's
`ls_localisation` supplies).

    AprioriNPlusNeu (FS eq:apriorinn+)  +  BogoliubovLowNeu (FS §9–11, low states)
        ──spectralInputNeu_of_apriori_bog──▶  SpectralInputNeu  ──▶  UBBNeu ──▶ UBB ──▶ hpres

Everything here is proved; the two inputs are named residuals of the same kind as the
`lem:LocMatrices` ones (see `README.md` §4).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **FS `eq:apriorinn+` (second conjunct) at the extended class**: a *low* state has at
most `W N L` excited particles, in the covariant normalisation
(`cnPlus L Φ ≤ W N L · aboxSq N L Φ`). -/
def AprioriNPlusNeu (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ → WindowNeu W N L Φ

/-- **FS §9–11 at the extended class, for *low* windowed states** (the form in which FS
apply it after the a-priori bounds). -/
def BogoliubovLowNeu (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CNeu N L, WindowNeu W N L Φ → LowStateNeu v N L J Φ →
        Lambda (a v) C η₀ (dens N L) * L ^ 3
          ≤ RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-- The *low-state* form of §9–11 follows from the windowed form (add a hypothesis: the
windowed form is the stronger statement, its hypothesis being weaker). -/
theorem bogoliubovLowNeu_of_windowed {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hB : BogoliubovWindowedNeu v h J W ε₀ η₀) :
    BogoliubovLowNeu v h J W ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  exact ⟨C, hC, fun L hL N hN Φ hwin _ => hB L hL N hN Φ hwin⟩

/-- **The per-state spectral input from the a-priori window and FS §9–11**: the a-priori
chapter produces exactly the window hypothesis that §9–11 consumes.  (The two forms of
§9–11 are *equivalent* as residuals, by the two lemmas above and
`lambda_shift_le`'s `K = 0` case.) -/
theorem spectralInputNeu_of_apriori_bog {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (ha1 : AprioriNPlusNeu v h J W ε₀)
    (ha2 : BogoliubovLowNeu v h J W ε₀ η₀) :
    SpectralInputNeu v J ε₀ η₀ := by
  rcases ha2 with ⟨C, hC, hlow⟩
  refine ⟨C, hC, fun L hL N hN Φ hΦ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlowH : LowStateNeu v N L J Φ := (lowStateNeu_iff_density hLpos Φ).mpr hΦ
  simpa using lambda_shift_le (A := a v) (C := C) (K := 0) (η₀ := η₀) (ρ := dens N L)
    (U := RaylNeu N L v Φ) (V := RaylNeu N L v Φ) hLpos
    (hlow L hL N hN Φ (ha1 L hL N hN Φ hlowH) hlowH) (by simp)

/-- **`UBBNeu` from FS's a-priori route at the extended class.** -/
theorem UBBNeu_of_HInputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (ha1 : AprioriNPlusNeu v h J W ε₀) (ha2 : BogoliubovLowNeu v h J W ε₀ η₀) :
    UBBNeu v η₀ :=
  UBBNeu_of_spectralNeu hv ha hε₀ hJ (spectralInputNeu_of_apriori_bog ha1 ha2)

/-- **The delivered `UBB` from FS's a-priori route at the extended class.** -/
theorem UBB_of_HInputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (ha : 0 ≤ a v)
    (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀) (ha1 : AprioriNPlusNeu v h J W ε₀)
    (ha2 : BogoliubovLowNeu v h J W ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_UBBNeu hv hv1 (UBBNeu_of_HInputs hv ha hJ hε₀ ha1 ha2)

/-- **The paper's `hpres` from FS's a-priori route at the extended class.** -/
theorem hpres_of_HInputs {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (ha1 : AprioriNPlusNeu v h J W ε₀) (ha2 : BogoliubovLowNeu v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBNeu hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBBNeu_of_HInputs hv (le_of_lt hav) hJ hε₀ ha1 ha2)

end Work.UBBInputs4
