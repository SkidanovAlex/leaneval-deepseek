import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.LhyIntegral
import Submission.Work.UBBInputs5.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs6.Defs` — round 6: the carrier of the a-priori window

Round 5 (`Submission/Work/UBBInputs5/README.md`) closed the `GradedDatum`-based
residual lists as **unsatisfiable** (five findings) and left as "the only coherent list"

    Work.UBBInputs5.hpres_of_aprioriWindowNeu :
      AprioriNPlusNeu v h J W ε₀  +  BogoliubovWindowedNeu v h J W ε₀ η₀  ⟹  hpres .

Round 6 attacks the two inputs of that list.  The **first finding of round 6**
(`Work.UBBInputs6.aprioriNPlusNeu_false_of_window_lt_one`, `Correction.lean`) is that
round 4's `Work.UBBInputs4.AprioriNPlusNeu` is *false* in the dilute regime as soon as the
window is smaller than `1` at the smallest admissible box — and the FS window of
`eq:apriorinn+` *is* smaller than `1` there.  The reason is a **carrier mismatch**: round 4
measures

* the state's *energy* by `RaylNeu`, whose kinetic part `kinNeu N L Φ = ∫_{box N L} Σ (∂Φ)²`
  is an integral over the **Dirichlet box** `box N L = [0,L]³` (the corpus's canonical box),
* the state's *excited count* by `cnPlus L Φ = Σᵢ ∫_{abox N L} (QᵢΦ)²`, an integral over the
  **centred box** `abox N L = ∏ᵢ [-L/2,L/2]³` (FS's box `Λ`),

so a state may be invisible to `RaylNeu` (e.g. constant, hence of energy `0`, on `box N L`)
and yet carry a large excited count on `abox N L`.  The two boxes are *not nested*, and there
is no inequality relating the two normalisations.

The **corrected carrier** is the corpus's own (`Work.SmallBoxSliding`, `Work.UBB`): the
centred box `abox`, the kinetic word `kinWord` (`Submission.CentredGap`), the excited count
`cnPlus` (`Submission.CentredSector`), the localised potential words `qLHSwordB` and the
canonical per-box energy word `sboxE = kinWord + qLHSword` — i.e. *the region on which FS's
`H_Λ(μ)` is defined*.  Round 1 (`Work.UBBInputs.Defs`) already states the two inputs there:

* `AprioriNPlusCov v h J W ε₀` — FS `eq:apriorinn+` in its covariant form
  `cnPlus L Φ ≤ W N L · ‖Φ‖²_{abox}`, for the *low* states of FS `eq:aprioriPsi`
  (`WordDens ≤ Theta`);
* `BogoliubovLowCov v h J W ε₀ η₀` — FS §9–11 at the *same* window.

This file fixes the round-6 vocabulary:

| name | meaning |
|---|---|
| `fsWindowC v b J K_B` | the FS window `(2L²/b)·4πρ²(a v)L³(J+K_B³)√(ρ(a v)³)` produced by the sliding localisation at the corpus carrier |
| `fsWindowShape v b J K_B K_ℓ` | the *same* window in the FS `eq:apriorinn+` shape `K_B³ K_ℓ² ρ L³ (ρ(a v)³)^{1/2}` (so that the a-priori window and the §9–11 window are *literally* the same function) |
| `SlidingBundle v h b K_B R' J ε₀ d M R0` | the round-6 **a-priori residual bundle**: exactly the hypotheses of `Work.UBBInputs2.dlSlideCov_of_kinetic_and_kernel` — `KineticLocalisation d b` (BS Thm 3.10), the per-box energy fields of `BoxSumBoundKernel` (FS `thm:smallbox` / the ESY `hEgc` side), FS `lem:LocPotential` (`LocPotentialCorpus`), and the integrability bookkeeping |
| `BogoliubovWindowedCov v h J W ε₀ η₀` | FS §9–11 *under the window only* at the corpus carrier (the carrier-consistent analogue of round 4's `BogoliubovWindowedNeu`) |
| `SharpTwoTermCov v h J W ε₀ c₁` | the **sharp two-term Bogoliubov bound**: `−4πρ²(a v)L³ + 4πρ²(a v)L³·c₁·√(ρ(a v)³) ≤ E(Φ)` for windowed states — FS `thm:BogHamDiag` + `lem:BogIntegral` *without* the error-term bookkeeping |
| `lhyC_eq_modelIntegral` | the provenance of the sharp constant: `lhyC = 128/(15√π)` is the value of the corpus's delivered model integral `Submission.BoseGases.lhy_model_integral_fs` |

Everything here is `sorry`-free and axiom-clean; `README.md` carries the ledger and the
roadmaps.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs6

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2
open Work.UBBInputs4
open Work.UBBInputs5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The FS a-priori window at the corpus carrier -/

/-- **The window produced by the sliding localisation at the corpus (centred) carrier**:
FS `eq:apriorinn+`, second conjunct, with the constants the corpus chain actually produces
(`Work.UBBInputs.aprioriNPlusCov_of_dlSlideCov`, itself the arithmetic of
`Work.UBB.Apriori.cnPlus_le_window_of_low`):

    W N L = (2L²/b)·4πρ²(a v)L³(J + K_B³)·(ρ(a v)³)^{1/2} ,      ρ = N/L³ .

The kinetic gap `b` is the sliding parameter of BS Thm 3.10 (`b = 1/18` in the corpus
normalisation, `Work.SmallBoxSliding.kinetic_gap_18`), `K_B` the FS cutoff constant of
`eq:KBdefinition` and `J` the a-priori constant of `eq:aprioriPsi`. -/
noncomputable def fsWindowC (v : ℝ³ → ℝ) (b J K_B : ℝ) : ℕ → ℝ → ℝ :=
  fun N L => (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
    * (J + K_B ^ 3) * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))

@[simp] theorem fsWindowC_apply (v : ℝ³ → ℝ) (b J K_B : ℝ) (N : ℕ) (L : ℝ) :
    fsWindowC v b J K_B N L
      = (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) := rfl

/-- `fsWindowC` is nonnegative whenever `a v ≥ 0`, `b > 0`, `J + K_B³ ≥ 0` and `L ≥ 0`. -/
theorem fsWindowC_nonneg {v : ℝ³ → ℝ} {b J K_B : ℝ} (hb : 0 < b) (ha : 0 ≤ a v)
    (hJ : 0 ≤ J + K_B ^ 3) {N : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ fsWindowC v b J K_B N L := by
  rw [fsWindowC_apply]
  have hρ : 0 ≤ dens N L := by unfold dens; positivity
  have hpow : 0 ≤ (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hmain : 0 ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * π)
      (sq_nonneg (dens N L))) ha) (pow_nonneg hL 3)) hJ
  exact mul_nonneg (div_nonneg (by positivity) hb.le) (mul_nonneg hmain hpow)

/-- **The same window in the FS `eq:apriorinn+` shape** `K_B³ K_ℓ² ρ L³ (ρ(a v)³)^{1/2}`,
with the explicit

    K_ℓ² = (8πρ(a v)L²/b)·(J + K_B³)/K_B³ .

This is the *window reconciliation* of the a-priori route: the window the sliding localisation
produces is exactly the FS shape, so the a-priori input and the §9–11 input can be consumed at
one and the same window function (`Work.UBBInputs.spectralInput_of_cov`). -/
theorem fsWindowC_eq_shape {v : ℝ³ → ℝ} {b J K_B : ℝ} (hb : 0 < b) (hKB : 0 < K_B)
    (ha : 0 ≤ a v) (hJ : 0 ≤ J + K_B ^ 3) {N : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    fsWindowC v b J K_B N L
      = K_B ^ 3 * (Real.sqrt ((8 * π * dens N L * (a v) * L ^ 2 / b)
            * ((J + K_B ^ 3) / K_B ^ 3))) ^ 2
          * dens N L * L ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
  have hKB3 : (0 : ℝ) < K_B ^ 3 := by positivity
  have hρ : 0 ≤ dens N L := by unfold dens; positivity
  have hnum : 0 ≤ 8 * π * dens N L * (a v) * L ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * π) hρ) ha)
      (by positivity : (0 : ℝ) ≤ L ^ 2)
  have hrad : 0 ≤ (8 * π * dens N L * (a v) * L ^ 2 / b) * ((J + K_B ^ 3) / K_B ^ 3) :=
    mul_nonneg (div_nonneg hnum hb.le) (div_nonneg hJ hKB3.le)
  have hsq : (Real.sqrt ((8 * π * dens N L * (a v) * L ^ 2 / b)
        * ((J + K_B ^ 3) / K_B ^ 3))) ^ 2
      = (8 * π * dens N L * (a v) * L ^ 2 / b) * ((J + K_B ^ 3) / K_B ^ 3) :=
    Real.sq_sqrt hrad
  rw [hsq, fsWindowC_apply]
  field_simp
  ring

/-! ## 2. The round-6 a-priori residual bundle -/

/-- **The round-6 a-priori residual bundle** — exactly the hypothesis list of the delivered
`Work.UBBInputs2.dlSlideCov_of_kinetic_and_kernel`, bundled so that the round-6 ledger has a
single name.  Its members are, in FS's own reading:

* `hloc` — `KineticLocalisation d b`: FS `lem:LocKinEn`, *cited from* Bratteli–Solovej
  Theorem 3.10 (the corpus `Work.SmallBoxTBWord.tBLocalisation`).  This is the **one**
  genuinely external input of the sliding chapter (see
  `Submission/Work/SmallBoxTBWord/NOTES.md` §4, the no-substitute analysis);
* `hK` — `BoxSumBoundKernel`: the per-box energy fields.  Round 2's canonicalisation
  (`BoxSumBoundCanon` fixes the per-box energy word to `tBwordB u + qLHSwordB u`, so the
  `hbox` direction problem disappears and `Integrable chiMass` is discharged from
  `Work.SmallBoxSliding.integrable_chiSmallB_mass`), `hmass` is delivered by
  `Work.SmallBoxSliding.compl_mass_le` (+ `hmass_of_complMass`), and the remaining content is
  `hlow` (the per-box lower bound on the discarded boxes — FS `thm:smallbox`, sourced from the
  delivered `Submission.BoseGases.smallbox_dl_energy_bound`, i.e. the **trial-state/ESY
  upper** `hEgc` side of `Work.ESYRound7`) and `hsum` (the same per-box bound integrated over
  the good set: the count ↔ localised-density bookkeeping of
  `Work/UBBInputs2/README.md` §4(c));
* `hdRχ` — the repointing regime `R0 ≤ L·chiR0` (`L ≥ 1`), FS's own `a ≪ L` assumption: needed
  because after the repoint the `ℓ`-scale denominator `(χ⋆χ)(·/L) ≥ 1/2` on the support of `v`.
  (The round-6 field `hLP : LocPotentialCorpus` is **deleted**: the repointed telescoping
  `Work.SmallBoxSliding.qLHSwordB_integral_u` is an *identity*, so the `hpot` field is delivered
  by `Work.UBBInputs2.hpot_of_regime` with no word comparison.)
* `hint`, `hintRef` — the integrability bookkeeping (genuine at the corpus trial space
  `CSBox`, which admits non-decaying states; delivered for compactly supported states by
  `Work.UBBInputs2.integrable_qLHSBIntegrand` / `integrableOn_qLHSChiIntegrand`);
* the regime data `hM`, `hd`, `hv_supp`, `hR0`, `hdR` of the sliding geometry
  (`Work.SmallBoxSliding.compl_mass_le`). -/
structure SlidingBundle (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (d M : ℕ)
    (R0 : ℝ) : Prop where
  hM : 1 ≤ M
  hd : (0 : ℝ) < (d : ℝ)
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hR0 : 0 < R0
  hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16
  hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0
  hint : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      Integrable (fun p : ℝ³ × X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (dens N L) (Φ : X N → ℝ) p.1 p.2)
  hintRef : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      IntegrableOn (Work.SmallBoxSliding.qLHSChiIntegrand h M L (d : ℝ) (dens N L)
        (Φ : X N → ℝ)) (abox N L)
  hloc : KineticLocalisation (d : ℝ) b
  hK : BoxSumBoundKernel v h b K_B R' J ε₀ d M

/-! ## 3. FS §9–11 at the corpus carrier, under the window only -/

/-- **FS §9–11 under the window only, at the corpus (centred) carrier** — the
carrier-consistent analogue of round 4's `BogoliubovWindowedNeu`: every state whose excited
count is inside the window `W` has shifted energy density at least `Λ(a v) C η₀ ρ`.  The
normalisation is the corpus's: `‖Φ‖²_{abox} = sqNormN N L Φ` and the energy density is the
word density `WordDens` (= `sboxE/(L³‖Φ‖²)`), so the window hypothesis
`cnPlus L Φ ≤ W N L · sqNormN N L Φ` is *scale-invariant* (both sides are of degree two in
`Φ`) — the round-1 finding (B) (a scale-invariant hypothesis against a scale-quadratic
conclusion) is thereby avoided.

FS's chain (their §9–11): `prop:Hamilton2ndQuant` (the second quantisation of `H_Λ(μ)`),
`thm:Kafz` (the `c`-number substitution), `thm:BogHamDiag` + `lem:BogIntegral` (the
Bogoliubov diagonalisation and the model integral) and `thm:Control3Q` (the positive `4Q`
absorption). -/
def BogoliubovWindowedCov (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) →
        Lambda (a v) C η₀ (dens N L) ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ)

/-- The windowed form is *weaker* than the low-state form of round 1
(`BogoliubovLowCov`) — its hypothesis is weaker — so it implies it.  (The consumer
`Work.UBBInputs.spectralInput_of_cov` takes the low-state form; this lemma is what allows the
round-6 chain to be fed the windowed form, exactly as round 4's
`bogoliubovLowNeu_of_windowed` does at the other carrier.) -/
theorem bogoliubovLowCov_of_windowedCov {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hB : BogoliubovWindowedCov v h J W ε₀ η₀) :
    BogoliubovLowCov v h J W ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  exact ⟨C, hC, fun L hL N hN Φ hwin _ => hB L hL N hN Φ hwin⟩

/-! ## 4. The sharp two-term Bogoliubov bound (the §9–11 layer) -/

/-- **The sharp two-term Bogoliubov bound at the corpus carrier** — FS `thm:BogHamDiag` +
`lem:BogIntegral` read at a single windowed state, with the LHY constant `c₁` *exposed* and
**no error term**:

    −4πρ²(a v)L³ + 4πρ²(a v)L³·c₁·√(ρ(a v)³) ≤ E(Φ) := WordDens N L (dens N L) v h Φ · L³ .

The three delivered corpus layers that supply it are

* the `D1` diagonal component of the Bogoliubov diagonalisation with its explicit constant
  (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`: FS `lm:appbogolubov` at the per-small-box
  geometry, `Work.SmallBoxD1*`: `Submission/SmallBoxD1Final.lm_appbogolubov_pWord_holds`);
* the `w₂`-mass completion of the second-order term (`Work.FSKernelCompare.w2c_acube_integral_ge_w1c`,
  `Work.SmallBoxKernelMass`) — the corpus's version of FS `lem:BogIntegral`'s kernel mass;
* the sharp value of the model integral `c₁ = 128/(15√π)` (`Submission.LhyIntegral.lhy_model_integral_fs`).

What is **not** in the corpus is the passage from the per-small-box layers to this
box-level statement (FS §9–10 read at the box scale: the second-quantisation of `H_Λ(μ)`,
the `u`-averaging of the localised Bogoliubov Hamiltonians, the `Q₁`/`Q₂`/`Q₃`/`Q₄` peeling
and the `4Q` absorption `thm:Control3Q`).  That passage is the named residual
`Submission/Work/UBBInputs2/README.md` §5 ("the one undelivered layer"). -/
def SharpTwoTermCov (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ c₁ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CSBox N L,
      cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) →
      - (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3)
          + 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * c₁
              * Real.sqrt (dens N L * (a v) ^ 3)
        ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ) * L ^ 3

/-! ## 5. The provenance of the sharp constant -/

/-- **The sharp constant `lhyC = 128/(15√π)` is the value of the corpus's Bogoliubov model
integral** (FS `lem:BogIntegral`, evaluated in `Submission.LhyIntegral.lhy_model_integral_fs`):
the `LhyIntegral` chapter computes the `Bogoliubov model integral
`4π ∫_0^∞ (r⁴ + 8πr² − (8π)²/2 − r³√(r²+16π)) dr = −64π⁴·(128/(15√π))`, so the coefficient
that appears in `Λ` and in `bogLhy` is exactly the model's.  Recorded here so that the
round-6 layer `SharpTwoTermCov` is *pinned* to the model integral rather than merely named. -/
theorem lhyC_eq_modelIntegral :
    4 * π * (∫ r in Set.Ioi (0 : ℝ),
      (r ^ 4 + 8 * π * r ^ 2 - (8 * π) ^ 2 / 2 - r ^ 3 * Real.sqrt (r ^ 2 + 16 * π)))
      = -64 * π ^ 4 * lhyC := by
  rw [lhy_model_integral_fs]
  unfold lhyC
  ring

end Work.UBBInputs6
