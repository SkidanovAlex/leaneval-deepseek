import ChallengeDeps
import Submission.Work.UBB.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBB.Apriori` — wiring the a-priori window to the sibling chapter

`Defs.AprioriNPlus` is the a-priori `n₊` window of FS `thm:aprioriHLambda`
(`eq:apriorinn+`, second conjunct) for *low* states, for an abstract window
function `W` that this area's two sibling inputs share.  This module shows that
the input has a **proved arithmetic core** and that its *only* residual is the
per-state sliding localisation of the sibling chapter:

* `cnPlus_le_window_of_low` (proved) — from the low-state condition
  (`WordDens ≤ Theta`, this area's density form of FS `eq:aprioriPsi`) and the
  per-state sliding inequality

  ```
  R' + (b/(2L²))·cnPlus L Φ − 4πρ²(a v)L³(1 + K_B³(ρ(a v)³)^{1/2}) ≤ E(Φ)
  ```

  (`ρ := dens N L`, `E(Φ)` the shifted energy word of `Φ`), the excited count is
  bounded by `(2L²/b)·4πρ²(a v)L³(J+K_B³)(ρ(a v)³)^{1/2}` — the second
  conjunct of FS `eq:apriorinn+`, via the CLOSED corpus arithmetic
  `Work.SmallBoxSliding.cnPlus_and_R_le`.
* `nPlusWindow_rescale` (proved) — an FS-shaped window `nPlusWindow` absorbs a
  constant factor by the rescaling `K_ℓ ↦ K_ℓ·√C`.
* `aprioriNPlus_of_state` (proved) — assembling the two: **`AprioriNPlus` holds
  as soon as the per-state sliding inequality holds for every low state**, with
  the explicit window
  `W N L = (2L²/b)·4π·(dens N L)²·(a v)·L³·(J+K_B³)·(dens N L·(a v)³)^{1/2}`.

The per-state sliding inequality is FS `eq:BSsliding2`, cited by FS from
Bratteli–Solovej Theorem 3.10; in the corpus it is the named residual of
`Work.SmallBoxSliding` (`NOTES.md` §2 (H1), `Sliding.sliding_sum_identity`,
`sliing_sum_identity_of_telescope`) and it is supplied by
`Work.SmallBoxTBWord.Sliding.tBLocalisation` together with the per-box bound
(`Work.SmallBoxDLBound.smallbox_dl_energy_bound`) and the sliding sum
`Work.SmallBoxSliding.Sliding.sliding_sum_identity*`.  So from this area's
point of view the a-priori chapter has exactly ONE residual left.
-/

noncomputable section

open _root_.BoseGases
open Submission.BoseGases
set_option autoImplicit false
set_option linter.dupNamespace false

namespace Work.UBB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-- The shifted energy word of a box state (the corpus `sboxE` quotient, i.e.
the numerator of `WordDens` times `L³`). -/
def EnergyWord (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (Φ : CSBox N L) : ℝ :=
  (kinWord N L (Φ : X N → ℝ)
      + qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ))
    / (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)

/-- The low-state condition `WordDens ≤ Theta` is the energy condition
`EnergyWord ≤ Θ·L³` (FS `eq:aprioriPsi` in the corpus normalisation), with the
error term written in the corpus's `(μ a³)^{1/2}` form. -/
theorem energyWord_le_of_wordDens_le {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v}
    {J : ℝ} (hL : 0 < L) {Φ : CSBox N L}
    (hΦ : WordDens N L μ v h (Φ : X N → ℝ) ≤ Theta (a v) J μ) :
    EnergyWord N L μ v h Φ
      ≤ -4 * π * μ ^ 2 * (a v) * L ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  have hL3 : 0 < L ^ 3 := pow_pos hL 3
  have hrew : WordDens N L μ v h (Φ : X N → ℝ) = (EnergyWord N L μ v h Φ) / L ^ 3 := by
    unfold WordDens EnergyWord sboxE
    rw [div_div]
    congr 1
    ring
  rw [hrew, Theta] at hΦ
  rw [Real.sqrt_eq_rpow] at hΦ
  rw [div_le_iff₀ hL3] at hΦ
  have hkey : -(4 * π * μ ^ 2 * (a v) * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * L ^ 3
      = -4 * π * μ ^ 2 * (a v) * L ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    ring
  rwa [hkey] at hΦ

/-- **FS `eq:apriorinn+`, second conjunct, from the low-state condition** — the
proved core of `Defs.AprioriNPlus`, with the corpus's `Work.SmallBoxSliding`
arithmetic (`cnPlus_and_R_le`). -/
theorem cnPlus_le_window_of_low {N : ℕ} {L b : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v}
    {J K_B R' : ℝ} (hL : 0 < L) (hb : 0 < b) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    {Φ : CSBox N L}
    (hΦ : WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L))
    (hslide : R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
        - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
        ≤ EnergyWord N L (dens N L) v h Φ) :
    cnPlus L (Φ : X N → ℝ)
      ≤ (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
          * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  have hE := energyWord_le_of_wordDens_le (v := v) (h := h) (J := J) (hL := hL)
    (μ := dens N L) hΦ
  have hcn : 0 ≤ cnPlus L (Φ : X N → ℝ) := Work.SmallBoxSliding.cnPlus_nonneg L
  have hmain := Work.SmallBoxSliding.cnPlus_and_R_le (N := N) (ℓ := L) (μ := dens N L)
    (b := b) hL hb (a := a v) ha hR' hcn hE hslide
  have hne : (0 : ℝ) < 2 * L ^ 2 / b := by positivity
  have h1 : cnPlus L (Φ : X N → ℝ)
      ≤ (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
          * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    have h2 : (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
        ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
          * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
      linarith [hmain.1, hR']
    have := mul_le_mul_of_nonneg_left h2 hne.le
    have heq : (2 * L ^ 2 / b) * ((b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ))
        = cnPlus L (Φ : X N → ℝ) := by
      field_simp
    rwa [heq] at this
  exact h1

/-- An FS-shaped window `nPlusWindow` absorbs a constant factor by the
rescaling `K_ℓ ↦ K_ℓ·√C`. -/
theorem nPlusWindow_rescale {v : ℝ³ → ℝ} {K_B C : ℝ} (hC : 0 ≤ C)
    (Kℓ : ℕ → ℝ → ℝ) (N : ℕ) (L : ℝ) :
    nPlusWindow v K_B (fun N L => Kℓ N L * Real.sqrt C) N L
      = C * nPlusWindow v K_B Kℓ N L := by
  unfold nPlusWindow
  rw [mul_pow, Real.sq_sqrt hC]
  ring

/-- **`AprioriNPlus` from the per-state sliding inequality** (proved): if for
every low state of every box the sliding localisation inequality of FS
`eq:BSsliding2` holds, then the a-priori `n₊` window `AprioriNPlus` holds, with
the explicit window `W N L = (2L²/b)·4π·(dens N L)²·(a v)·L³·(J+K_B³)·(dens N L·(a v)³)^{1/2}`.
(`R'` is the free nonnegative a-priori remainder `R_Ψ`.) -/
theorem aprioriNPlus_of_state {v : ℝ³ → ℝ} {h : ScatSol v} {J b K_B ε₀ R' : ℝ}
    (hb : 0 < b) (_hKB : 0 < K_B) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    (hslide : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ,
      dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
      WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
      R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
        - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
        ≤ EnergyWord N L (dens N L) v h Φ) :
    AprioriNPlus v h J
      (fun N L => (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))) ε₀ := by
  intro L hL N hN Φ hΦ
  exact cnPlus_le_window_of_low (N := N) (L := L) (b := b) (v := v) (h := h)
    (J := J) (K_B := K_B) (R' := R') (lt_of_lt_of_le one_pos hL) hb ha hR' hΦ
    (hslide L hL N hN Φ hΦ)

end Work.UBB
