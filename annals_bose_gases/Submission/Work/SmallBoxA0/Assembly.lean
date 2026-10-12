import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed-`n` smallbox block bound — the CORRECTED final assembly
(Work.SmallBoxA0, step 4, Session-286)

This module replaces the (mis-signed) `Final.state_block_bound_of_inputs`
assembly.  The point of the correction is that the Bogoliubov input must be a
**single** lower bound on `kinWord + q4PairWord` whose right-hand side already
contains the kinetic gap `cnPlus/(36s²)` and the sharp mass term with a
**NEGATIVE** sign — that is what `SmallBoxD1Final.lm_appbogolubov_pWord` +
the kinetic bridge actually deliver.  The old `+½(1+η)·D·(N̂+1)²/s³`-form was
FALSE for `η ≥ 0` (the constant state `Φ ≡ c` has `kinWord = q4PairWord = 0`
and `cnPlus = 0`), which made the data bundle empty exactly in the intended
regime.

The derivation is a `linarith` over the five closed inputs:

* **(pot)** `Work.SmallBoxA0.pot_sharp_summary`:
  `qLHSword ≥ ¼-shape + ½s⁻³·D·cS2 + A₂ − PNC·n₊ − 36π(av)μ − 2s⁻³Corr`;
* **(slack)** `cs2_mass_slack`: the `∬w₂`-slack `½s⁻³D·cS2` dominates the
  mass term `½D(N̂+1)²s⁻³` up to `72π(av)μ·n₊ + 112π(av)μ`
  (`cS2 ≥ (N̂−n₊)²−(N̂−n₊)` and `D·N̂/s³ ≤ 9μD ≤ 72π(av)μ`, `D/s³ ≤ 8π(av)μ`);
* **(corr)** `2s⁻³Corr ≤ n₊/(72s²) + 36π(av)μ`;
* **(bog)** `−½(1+η)D(N̂+1)²s⁻³ + (1/(36s²) − BogErr)·n₊ − (88π+39)(av)μ
  ≤ kinWord + A₂` (`BogErr` a data scalar: the `cnPlus`-coefficient of the D1
  refined error that the gap does not already absorb);
* **(η)** `½|η|·8π(av)(N̂+1)²s⁻³ ≤ μ²(av)s³Γ + μ(av)`.

The `n₊`-coefficient telescopes to
`1/(36s²) − BogErr − 1/(72s²) − PNC − 72π(av)μ`, which is `≥ 0` exactly by
the regime condition `hreg : totNCoeff s μ v + BogErr ≤ 1/(36s²)`; the
constant coefficients telescope to the universal `272π + 40 ≤ C`.
`hC : 272 * π + 40 ≤ C` is the only constant comparison, and the universal
choice `C := 272π + 40` of `SmallBoxBlockBound` satisfies it by `le_refl`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The `∬w₂`-slack dominates the sharp mass term up to `n₊`/`(av)μ`-terms.**

    `½s⁻³·D·cS2 ≥ ½D(N̂+1)²s⁻³ − 72π(av)μ·n₊ − 112π(av)μ`

for `0 ≤ D ≤ 8π(av)`, `N̂/s³ ≤ 9μ`, `1 ≤ μs³`, `0 ≤ (av)`.  Proof: from
`cS2 ≥ cS1²−cS1` and `cS1 = N̂−n₊`,
`cS2 ≥ N̂² − 2N̂n₊ − N̂ = (N̂+1)² − 2N̂n₊ − 3N̂ − 1`. -/
lemma cs2_mass_slack {N : ℕ} {s μ D : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hDnn : 0 ≤ D) (hDle : D ≤ 8 * π * a v)
    (hav : 0 ≤ a v) (hμs : 1 ≤ μ * s ^ 3) (hwin : (N : ℝ) / s ^ 3 ≤ 9 * μ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    (1 / 2) * (s ^ 3)⁻¹ * D * cS2 s Φ
      ≥ (1 / 2) * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        - (72 * π * (a v) * μ) * cnPlus s Φ - 112 * π * (a v) * μ := by
  classical
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hs3i : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  have hμnn : (0 : ℝ) ≤ μ := le_of_lt hμ
  have hann : (0 : ℝ) ≤ a v := hav
  have hnn : (0 : ℝ) ≤ cnPlus s Φ := cnPlus_nonneg
  have hS2 := cS2_ge_sq_sub_self (N := N) (ℓ := s) hs hΦc hnorm
  have hS : cS1 s Φ = (N : ℝ) - cnPlus s Φ := cS1_eq_nat_sub_cnPlus hs hΦc hnorm
  have hcS2 : (N : ℝ) ^ 2 - 2 * (N : ℝ) * cnPlus s Φ - (N : ℝ) ≤ cS2 s Φ := by
    rw [hS] at hS2
    nlinarith [hS2, sq_nonneg (cnPlus s Φ), hnn]
  -- the window facts
  have hNr : (N : ℝ) * (s ^ 3)⁻¹ ≤ 9 * μ := by
    rw [div_eq_mul_inv] at hwin; exact hwin
  have hN1 : (0 : ℝ) ≤ (N : ℝ) * (s ^ 3)⁻¹ := by positivity
  have hDN : D * ((N : ℝ) * (s ^ 3)⁻¹) ≤ 9 * μ * D := by
    have := mul_le_mul_of_nonneg_right hNr hDnn; nlinarith [this]
  have hDN' : D * (N : ℝ) * (s ^ 3)⁻¹ ≤ 72 * π * a v * μ := by
    have h1 : 9 * μ * D ≤ 9 * μ * (8 * π * a v) := by
      have h2 := mul_le_mul_of_nonneg_left hDle (by nlinarith [hμnn] : (0 : ℝ) ≤ 9 * μ)
      nlinarith [h2]
    have h3 : D * (N : ℝ) * (s ^ 3)⁻¹ = D * ((N : ℝ) * (s ^ 3)⁻¹) := by ring
    nlinarith [hDN, h1, h3]
  have hs3inv_mu : (s ^ 3)⁻¹ ≤ μ := by
    have h3 : (s ^ 3)⁻¹ * 1 ≤ (s ^ 3)⁻¹ * (μ * s ^ 3) :=
      mul_le_mul_of_nonneg_left hμs hs3i
    have h4 : (s ^ 3)⁻¹ * (μ * s ^ 3) = μ := by field_simp [ne_of_gt hs3]
    linarith [h3, h4]
  have hDinv : D * (s ^ 3)⁻¹ ≤ 8 * π * a v * μ := by
    have h1 := mul_le_mul_of_nonneg_right hDle hs3i
    have h2 := mul_le_mul_of_nonneg_left hs3inv_mu (by positivity : (0 : ℝ) ≤ 8 * π * a v)
    nlinarith [h1, h2]
  -- multiply the cS2 bound by the nonneg coefficient `½s⁻³D`
  have hcoef : (0 : ℝ) ≤ (1 / 2) * (s ^ 3)⁻¹ * D := by positivity
  have hmul : (1 / 2) * (s ^ 3)⁻¹ * D * ((N : ℝ) ^ 2 - 2 * (N : ℝ) * cnPlus s Φ - (N : ℝ))
      ≤ (1 / 2) * (s ^ 3)⁻¹ * D * cS2 s Φ := mul_le_mul_of_nonneg_left hcS2 hcoef
  -- bound the three remainder blocks
  have hA : (1 / 2) * (s ^ 3)⁻¹ * D * (2 * (N : ℝ) * cnPlus s Φ)
      ≤ (72 * π * (a v) * μ) * cnPlus s Φ := by
    have h : (s ^ 3)⁻¹ * D * (N : ℝ) ≤ 72 * π * a v * μ := by
      have h3 : D * (N : ℝ) * (s ^ 3)⁻¹ ≤ 72 * π * a v * μ := hDN'
      nlinarith [h3]
    nlinarith [mul_le_mul_of_nonneg_right h hnn]
  have hB : (1 / 2) * (s ^ 3)⁻¹ * D * (N : ℝ) ≤ 54 * π * (a v) * μ := by
    nlinarith [hDN']
  have hC : (1 / 2) * (s ^ 3)⁻¹ * D ≤ 4 * π * a v * μ := by
    nlinarith [hDinv]
  have hkey : (1 / 2) * (s ^ 3)⁻¹ * D * ((N : ℝ) ^ 2 - 2 * (N : ℝ) * cnPlus s Φ - (N : ℝ))
      ≥ (1 / 2) * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        - (72 * π * (a v) * μ) * cnPlus s Φ - 112 * π * (a v) * μ := by
    have hsqn : (0 : ℝ) ≤ (s ^ 3)⁻¹ * D * (N : ℝ) ^ 2 := by positivity
    nlinarith [hA, hB, hC, hsqn]
  linarith [hmul, hkey]

/-- **The `η`-slack bound**: from `½|η|·8π(av)(N̂+1)²s⁻³ ≤ μ²(av)s³Γ + μ(av)` and
`D ≤ 8π(av)`,

    `−(1/2)η·D(N̂+1)²s⁻³ ≥ −(μ²(av)s³Γ + μ(av))`

(no sign hypothesis on `η`: the negative-`η` case is trivial because the
left-hand side is then nonnegative). -/
lemma eta_mass_le {N : ℕ} {s μ η D G : ℝ} {a : ℝ} (hs : 0 < s) (hDnn : 0 ≤ D)
    (hDle : D ≤ 8 * π * a)
    (hη : (1 / 2) * |η| * (8 * π * a) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ μ ^ 2 * a * s ^ 3 * G + μ * a) :
    -((1 / 2) * η * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹)
      ≥ -(μ ^ 2 * a * s ^ 3 * G + μ * a) := by
  have hN1 : (0 : ℝ) ≤ (((N : ℝ) + 1) ^ 2) := by positivity
  have h0 : (0 : ℝ) ≤ (1 / 2) * |η| * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by positivity
  have hle : (1 / 2) * |η| * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
      ≤ (1 / 2) * |η| * (8 * π * a) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hDle h0
    nlinarith [h]
  have hneg : -((1 / 2) * η * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹)
      ≥ -((1 / 2) * |η| * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹) := by
    have h1 : η ≤ |η| := le_abs_self η
    have h2 : (0 : ℝ) ≤ (1 / 2) * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    nlinarith [h3]
  linarith [hle, hneg, hη]

/-- **`eta_mass_le` at FS's OWN count `(N+1)·N`** (`eq:refinedaprioribog` has `(n+1)n`, not
`(n+1)²`): the same conclusion with the residual's mass coefficient `(N+1)N` instead of `(N+1)²`.
The regime hypothesis is kept at `(N+1)²` (stronger, hence safe). -/
lemma eta_mass_le_mul {N : ℕ} {s μ η D G : ℝ} {a : ℝ} (hs : 0 < s) (hDnn : 0 ≤ D)
    (hDle : D ≤ 8 * π * a)
    (hη : (1 / 2) * |η| * (8 * π * a) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ μ ^ 2 * a * s ^ 3 * G + μ * a) :
    -((1 / 2) * η * D * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹)
      ≥ -(μ ^ 2 * a * s ^ 3 * G + μ * a) := by
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hle : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hDmul : D * (((N : ℝ) + 1) * (N : ℝ)) ≤ D * (((N : ℝ) + 1) * ((N : ℝ) + 1)) := by
    have h1 : (((N : ℝ) + 1) * (N : ℝ)) ≤ (((N : ℝ) + 1) * ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ (N : ℝ) + 1)
    exact mul_le_mul_of_nonneg_left h1 hDnn
  have hM : D * (((N : ℝ) + 1) * ((N : ℝ) + 1)) = D * (((N : ℝ) + 1) ^ 2) := by ring
  rw [hM] at hDmul
  have h1 : -((1 / 2) * η * D * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹)
      ≥ -((1 / 2) * |η| * D * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹) := by
    have hηle : η ≤ |η| := le_abs_self η
    have hpos : (0 : ℝ) ≤ (1 / 2) * D * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ := by
      have : (0 : ℝ) ≤ (((N : ℝ) + 1) * (N : ℝ)) := mul_nonneg (by linarith) hNn
      positivity
    have := mul_le_mul_of_nonneg_right hηle hpos
    nlinarith [this]
  have h2 : -((1 / 2) * |η| * D * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹)
      ≥ -((1 / 2) * |η| * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹) := by
    have : (1 / 2) * |η| * D * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹
        ≤ (1 / 2) * |η| * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
      have hk : (0 : ℝ) ≤ (1 / 2) * |η| * (s ^ 3)⁻¹ := by positivity
      nlinarith [hDmul, hk]
    linarith [this]
  have h3 : -((1 / 2) * |η| * D * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹)
      ≥ -(μ ^ 2 * a * s ^ 3 * G + μ * a) := by
    have hη' : (1 / 2) * |(|η|)| * (8 * π * a) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ μ ^ 2 * a * s ^ 3 * G + μ * a := by simpa using hη
    exact eta_mass_le (N := N) (η := |η|) hs hDnn hDle hη'
  linarith [h1, h2, h3]

/-- **THE CORRECTED FINAL ASSEMBLY (per state).**  From the proved sharp
summary `pot_sharp_summary` (the potential side), the `∬w₂`-slack
(`cs2_mass_slack`), the `Corr` residue bound `hCorr`, the Bogoliubov input
`hBog` (the kinetic word plus the `A₂ = q4PairWord` pairing, with the sharp
mass term NEGATIVE, the kinetic gap `n₊/(36s²)` POSITIVE and the residual
coefficients `(88π+39)(av)μ`), the loss-factor regime `hη`, the gap regime
`hreg` (`totNCoeff ≤ 1/(36s²)`) and the universal-constant condition
`88π+39+184π ≤ C − 1`, the per-state block shape holds:

    sboxE(Φ) ≥ (¼(x−μ)² − ½μ²)·8π(av)s³ − C·μ²(av)s³·Γ − C·μ(av),

`x := N̂/s³`, `Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}`.  See the module header for
the `linarith` bookkeeping (the `n₊`-coefficient telescopes to zero by
`hreg : totNCoeff s μ v + BogErr ≤ 1/(36s²)`, and the constant coefficients
to the single comparison `272π+40 ≤ C`). -/
theorem state_block_bound_of_inputs_sharp {N : ℕ} {s μ R0 K_B η C BogErr : ℝ} {v : ℝ³ → ℝ}
    (hN : 1 ≤ N) (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0) (hKB : 0 < K_B)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwin : (N : ℝ) / s ^ 3 ≤ 9 * μ)
    (hSc1 : 0 < cS1 s Φ)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * a v)
    (hreg : totNCoeff s μ v + BogErr ≤ 1 / (36 * s ^ 2))
    (hη : (1 / 2) * |η| * (8 * π * (a v)) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ μ ^ 2 * (a v) * s ^ 3
            * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          + μ * (a v))
    (hC : 272 * π + 40 ≤ C)
    (hCorr : 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
    (hBog : -((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹)
          + (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ
        ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)) :
    (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
      - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
      - C * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      - C * μ * (a v)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  classical
  set G : ℝ := (R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hGdef
  have hav : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    g0w0Mass_nonneg (v := v) (R := R0) hR0 hv_nonneg hvrad hv_supp h
  have hnn : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hμnn : 0 ≤ μ := le_of_lt hμ
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
    exact Real.rpow_nonneg (by positivity) (1 / 2)
  -- (pot) the potential side
  have hsum := pot_sharp_summary (N := N) (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1
    hR0 hv_supp h hRs hΦc.continuous hnorm hwin hSc1
  have hpot : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (1 / 2) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ
        + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
        - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa [CorrWord] using hsum
  -- (slack) the `∬w₂`-slack dominates the sharp mass term
  have hslack := cs2_mass_slack (N := N) (s := s) (μ := μ)
    (D := g0w0Mass (v := v) h) (v := v) hs hμ hDnn hD hav hμs hwin hΦc.continuous hnorm
  -- (corr) the Corr residue
  have hcorr : -((1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
      ≤ -(2 * (s ^ 3)⁻¹ * CorrWord s h Φ) := by linarith [hCorr]
  -- (eta) the loss-factor regime
  have heta := eta_mass_le (N := N) (s := s) (μ := μ) (η := η)
    (D := g0w0Mass (v := v) h) (G := G) (a := a v) hs hDnn hD hη
  -- (reg) the gap regime: the expanded residual `n₊`-coefficient is nonnegative
  have hnf : 0 ≤ (1/(36*s^2) - BogErr) * cnPlus s Φ - (1/(72*s^2)) * cnPlus s Φ
      - potNCoeff μ (a v) * cnPlus s Φ - 72 * π * (a v) * μ * cnPlus s Φ := by
    have h0 : potNCoeff μ (a v) + 72 * π * (a v) * μ + 1 / (72 * s ^ 2) + BogErr ≤ 1 / (36 * s ^ 2) := by
      rw [totNCoeff] at hreg
      linarith [hreg]
    nlinarith [h0, hnn]
  have hX : 0 ≤ μ ^ 2 * (a v) * s ^ 3 * G := by
    have h1 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
    have h2 : (0 : ℝ) ≤ s ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hGnn
  have hY : 0 ≤ μ * (a v) := mul_nonneg hμnn hav
  have hC1 : (1 : ℝ) ≤ C := by linarith [hC, Real.pi_pos]
  have hDnn0 : (0 : ℝ) ≤ g0w0Mass (v := v) h := hDnn
  -- FS's own count `(N+1)·N` for the mass term: the slack and the `η`-budget at that count
  have hslackN : (1 / 2) * (s ^ 3)⁻¹ * g0w0Mass (v := v) h * cS2 s Φ
      ≥ (1 / 2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹
        - (72 * π * (a v) * μ) * cnPlus s Φ - 112 * π * (a v) * μ := by
    have h2 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hle' : (((N : ℝ) + 1) * (N : ℝ)) ≤ (((N : ℝ) + 1) ^ 2) := by nlinarith [h2]
    have hk : (0 : ℝ) ≤ (1 / 2) * g0w0Mass (v := v) h * (s ^ 3)⁻¹ := by positivity
    have hraw := mul_le_mul_of_nonneg_right hle' hk
    have hstep : (1 / 2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹
        ≤ (1 / 2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
      calc (1 / 2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹
          = (((N : ℝ) + 1) * (N : ℝ)) * ((1 / 2) * g0w0Mass (v := v) h * (s ^ 3)⁻¹) := by ring
        _ ≤ (((N : ℝ) + 1) ^ 2) * ((1 / 2) * g0w0Mass (v := v) h * (s ^ 3)⁻¹) := hraw
        _ = (1 / 2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by ring
    linarith [hstep, hslack]
  have hetaN := eta_mass_le_mul (N := N) (s := s) (μ := μ) (η := η)
    (D := g0w0Mass (v := v) h) (G := G) (a := a v) hs hDnn0 hD hη
  have step1 : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3) - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) + (1/2) * (s ^ 3)⁻¹ * g0w0Mass (v := v) h * cS2 s Φ - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ - (1/2) * (1 + η) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ + (1/(36*s^2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by linarith [hpot, hBog]
  have step2 : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3) - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) + ((1/2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ - 72 * π * (a v) * μ * cnPlus s Φ - 112 * π * (a v) * μ) - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ - (1/2) * (1 + η) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ + (1/(36*s^2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by linarith [step1, hslackN]
  have step3 : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3) - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) + ((1/2) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ - 72 * π * (a v) * μ * cnPlus s Φ - 112 * π * (a v) * μ) - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ - ((1/(72*s^2)) * cnPlus s Φ + 36 * π * (a v) * μ) - (1/2) * (1 + η) * g0w0Mass (v := v) h * (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ + (1/(36*s^2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by linarith [step2, hcorr]
  have step4 : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3) - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) - (72 * π * (a v) * μ * cnPlus s Φ + 112 * π * (a v) * μ)
        - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - ((1/(72*s^2)) * cnPlus s Φ + 36 * π * (a v) * μ) - (μ^2 * (a v) * s^3 * G + μ * (a v))
        + (1/(36*s^2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    linarith [step3, hetaN]
  have hmain : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3) - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) - μ ^ 2 * (a v) * s ^ 3 * G - (272 * π + 40) * (a v) * μ
      ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    linarith [step4, hnf]
  have hconst : -(C * μ ^ 2 * (a v) * s ^ 3 * G + C * (μ * (a v)))
      ≤ -(μ ^ 2 * (a v) * s ^ 3 * G + (272 * π + 40) * (μ * (a v))) := by
    nlinarith [hC, hC1, hX, hY]
  rw [show sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ
      = kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ from rfl]
  nlinarith [hmain, hconst]

end Work.SmallBoxA0
