import ChallengeDeps
import Submission.Work.UBBInputs2.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs2.Bogoliubov` — input (3) at the Hamiltonian: the two forms and
the non-vacuity certificate

`BogoliubovLowH` is FS §9–11 at the Hamiltonian (an energy `≥ Λ·L³` for a low
state inside the shared `n₊`-window).  This module provides:

* the **gain form** `BogoliubovGainH`, in which the sharp constant
  `lhyC = 128/(15√π)` appears *additively* over the free background
  `−4πρ²(a v)L³`; `bogoliubovLowH_iff_gainH` proves the two are the same
  statement (a `Lambda`-unfolding plus `Real.sqrt_eq_rpow`) — so the only
  non-free data are `lhyC` and the exponent `1/2 + η₀` (the coefficient is
  existential), exactly the rigidity the paper's theorem needs
  (`Work.UBB.LhyConstant` records the provenance of `lhyC` as the Bogoliubov
  model integral `Submission.LhyIntegral`);

* `spectralInputH_of_apriori_gainH` — the a-priori route with (3) in gain form;

* the non-vacuity certificate at the zero potential: the Hamiltonian-carrier
  Bogoliubov inputs are *proved* (not merely hypothesised) at `v ≡ 0`
  (`bogoliubovWindowedH_vZero`, `bogoliubovLowH_vZero`,
  `bogoliubovGainH_vZero`), via `Work.SmallBoxA0.a_vZero` and
  `Work.UBB.Rayl_nonneg`.

The irreducible content of (3) is the passage from the DELIVERED per-small-box
Bogoliubov layers (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`,
`Submission.BoseGases.lm_appbogolubov_pWord_holds`, the `w₂`-mass completion
`Work.SmallBoxKernelMass`/`Work.FSKernelCompare`, the sharp integral
`Submission.LhyIntegral`) to the box-level statement — FS §9–10 (`K(z)`,
`thm:Kafz`, `thm:BogHamDiag`, `thm:Control3Q`) read at the big box.  See
`README.md` §"Residual (3)".
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs2

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The two forms of FS §9–11 at the Hamiltonian -/

/-- **`BogoliubovGainH ⟹ BogoliubovLowH`**: the additive gain over the free
background is the same statement as the `Λ`-lower bound. -/
theorem bogoliubovLowH_of_gainH {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hg : BogoliubovGainH v h J W ε₀ η₀) :
    BogoliubovLowH v h J W ε₀ η₀ := by
  rcases hg with ⟨K, hK, hg⟩
  refine ⟨K, hK, fun L hL N hN Ψ hw hl => ?_⟩
  have hres := hg L hL N hN Ψ hw hl
  unfold Lambda
  rw [Real.sqrt_eq_rpow]
  linarith [hres]

/-- The converse direction. -/
theorem gainH_of_bogoliubovLowH {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hB : BogoliubovLowH v h J W ε₀ η₀) :
    BogoliubovGainH v h J W ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  refine ⟨C, hC, fun L hL N hN Ψ hw hl => ?_⟩
  have hres := hB L hL N hN Ψ hw hl
  unfold Lambda at hres
  rw [Real.sqrt_eq_rpow] at hres
  linarith [hres]

/-- **The two forms of FS §9–11 at the Hamiltonian are the same statement.** -/
theorem bogoliubovLowH_iff_gainH {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} :
    BogoliubovLowH v h J W ε₀ η₀ ↔ BogoliubovGainH v h J W ε₀ η₀ :=
  ⟨gainH_of_bogoliubovLowH, bogoliubovLowH_of_gainH⟩

/-- **The a-priori route with (3) in gain form**: `AprioriNPlusH` (FS
`eq:apriorinn+`, from the sliding inequality) together with the *gain* form of
FS §9–11 gives FS `eq:ToProve` at the Hamiltonian, hence `UBB` and `hpres`
through the delivered grand-canonical interface. -/
theorem spectralInputH_of_apriori_gainH {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (ha1 : AprioriNPlusH v h J W ε₀) (ha2 : BogoliubovGainH v h J W ε₀ η₀) :
    SpectralInputH v J ε₀ η₀ :=
  spectralInputH_of_apriori_bog ha1 (bogoliubovLowH_of_gainH ha2)

/-- **The window is a hypothesis**: the window-free Hamiltonian spectral input
`Work.UBB.SpectralInputH` (FS `eq:ToProve`) gives FS §9–11 under *any* window
(drop a hypothesis; the passage between the density and `Λ·L³` forms is
`Arith.lambda_le_div_iff`).  This is the H-analogue of round 1's
`Work.UBBInputs.bogoliubovLowCov_of_spectralInput`. -/
theorem bogoliubovLowH_of_spectralInputH {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ} (hS : SpectralInputH v J ε₀ η₀) :
    BogoliubovLowH v h J W ε₀ η₀ := by
  rcases hS with ⟨C, hC, hS⟩
  refine ⟨C, hC, fun L hL N hN Ψ _hw hlow => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hden := (lowStateH_iff_density hLpos Ψ).mp hlow
  have h1 : Lambda (a v) C η₀ (dens N L)
      ≤ (Rayl N L v Ψ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3) / L ^ 3 := by
    have h2 := hS L hL N hN Ψ hden
    rwa [div_sub_dens (a v) N hLpos (Rayl N L v Ψ)] at h2
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 3)).mp h1

/-- The same at the gain interface. -/
theorem bogoliubovGainH_of_spectralInputH {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ} (hS : SpectralInputH v J ε₀ η₀) :
    BogoliubovGainH v h J W ε₀ η₀ :=
  gainH_of_bogoliubovLowH (bogoliubovLowH_of_spectralInputH hS)

/-! ## 2. Non-vacuity at the zero potential -/

/-- At `v ≡ 0` the target vanishes: `Λ 0 C η₀ ρ = 0`. -/
theorem lambda_zero (C η₀ ρ : ℝ) : Lambda 0 C η₀ ρ = 0 := by
  unfold Lambda
  ring

/-- **FS §9–11 at the Hamiltonian, window only, is PROVED at the zero
potential**: there `a vZero = 0`, so `Λ = 0` and the conclusion is the
nonnegativity of the box Rayleigh quotient. -/
theorem bogoliubovWindowedH_vZero (J ε₀ η₀ : ℝ) (W : ℕ → ℝ → ℝ) :
    BogoliubovWindowedH Work.SmallBoxA0.vZero Work.SmallBoxA0.hZero J W ε₀ η₀ := by
  refine ⟨0, le_rfl, ?_⟩
  intro L hL N _hN Ψ _hw
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hray : (0 : ℝ) ≤ Rayl N L Work.SmallBoxA0.vZero Ψ :=
    Rayl_nonneg (v := Work.SmallBoxA0.vZero) hLpos (fun _ => le_refl 0) Ψ
  rw [Work.SmallBoxA0.a_vZero, lambda_zero]
  linarith [hray]

/-- The low-state form at the zero potential (drop the window hypothesis). -/
theorem bogoliubovLowH_vZero (J ε₀ η₀ : ℝ) (W : ℕ → ℝ → ℝ) :
    BogoliubovLowH Work.SmallBoxA0.vZero Work.SmallBoxA0.hZero J W ε₀ η₀ :=
  bogoliubovLowH_of_windowed (bogoliubovWindowedH_vZero J ε₀ η₀ W)

/-- **The gain form at the zero potential** (all terms carry `a vZero = 0`). -/
theorem bogoliubovGainH_vZero (J ε₀ η₀ : ℝ) (W : ℕ → ℝ → ℝ) :
    BogoliubovGainH Work.SmallBoxA0.vZero Work.SmallBoxA0.hZero J W ε₀ η₀ := by
  refine ⟨0, le_rfl, ?_⟩
  intro L hL N _hN Ψ _hw _hl
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hray : (0 : ℝ) ≤ Rayl N L Work.SmallBoxA0.vZero Ψ :=
    Rayl_nonneg (v := Work.SmallBoxA0.vZero) hLpos (fun _ => le_refl 0) Ψ
  rw [Work.SmallBoxA0.a_vZero]
  linarith [hray]

/-- **`SpectralInputH` at the zero potential, given the a-priori window** —
the Hamiltonian-carrier spectral input follows at `v ≡ 0` from the (window-only)
a-priori input and the PROVED zero-potential Bogoliubov bound.  (The a-priori
window itself is *not* free at `v ≡ 0`: it is a genuine statement about the
excited count, so it is carried as the hypothesis `ha1`.) -/
theorem spectralInputH_vZero_of_window (J ε₀ η₀ : ℝ) (W : ℕ → ℝ → ℝ)
    (ha1 : AprioriNPlusH Work.SmallBoxA0.vZero Work.SmallBoxA0.hZero J W ε₀) :
    SpectralInputH Work.SmallBoxA0.vZero J ε₀ η₀ :=
  spectralInputH_of_apriori_bog ha1 (bogoliubovLowH_vZero J ε₀ η₀ W)

end Work.UBBInputs2
