import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.q4PairWord_cs_bound
import Submission.Work.SmallBoxA0.w1_L2_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SmallBoxA0` — the residual from a kernel-`L²` control of the pairing

SESSION-289.  `Work.SmallBoxA0.q4PairWord_cs_bound` (the honest Cauchy–Schwarz
bound on the pairing word) has the shape

    q4PairWord Φ  ≥  −N̂(N̂−1)·s⁻³·M ,    M := ‖w₁‖_{L²(acube s × acube s)} ,

with `w₁ = wPairC s (g0 v h)` the pairing kernel.  This module converts that
into the recorded residual field's content,

    −½(1+η)·D·(N̂+1)N̂·s⁻³ + (1/(36s²) − BogErr)·n₊ − (88π+39)(av)μ
        ≤ kinWord N s Φ + q4PairWord Φ ,

under the EXPLICIT state-free arithmetic condition

    N̂(N̂−1)·M·s⁻³ ≤ ½(1+η)·D·(N̂+1)N̂·s⁻³ + (88π+39)(av)μ .               (arith)

(The case `N = 2` is the reviewer's sharp case: `q4PairWord = 2c⟨g,w₁⟩` and
`M = ‖Q₁Q₂w₁‖_{L²}`; the `s`-dependence of `M` — `M ≍ (av)s^{3/2}/R^{3/2}` for
`v` spread out over its range `R`, but `M ≫ (av)` for concentrated `v` — is
exactly the missing input: see `README.md` §28.5.)

Proof: `kinWord ≥ n₊/(36s²)` (`KineticBound.kinWord_gap_cnPlus`, PROVED) and
`n₊ ≤ N̂` (`cS1 + n₊ = N̂` with `0 ≤ cS1`), so the Cauchy–Schwarz bound
`q4PairWord ≥ −N̂(N̂−1)M/s³` and (arith) telescope; the `BogErr·n₊` term is
nonnegative by `0 ≤ BogErr`, `0 ≤ n₊`.
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

/-- **The residual from a kernel-`L²` control of the pairing** (the honest
Cauchy–Schwarz bound, with the state-free arithmetic condition). -/
lemma residual_of_pairing_cs {N : ℕ} {s μ η BogErr M : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hAv : 0 ≤ a v) (hμ : 0 ≤ μ) (hBog0 : 0 ≤ BogErr)
    (hD : 0 ≤ g0w0Mass (v := v) h)
    (hCS : ∀ {Φ : X N → ℝ}, ContDiff ℝ ∞ Φ →
      (∫ x in abox N s, (Φ x) ^ 2) = 1 →
      -((N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ * M)
        ≤ q4PairWord (ℓ := s) (v := v) h (Φ := Φ))
    (harith : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ * M
        ≤ (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
            * (s ^ 3)⁻¹
          + (88 * π + 39) * (a v) * μ)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) (hcS1 : 0 < cS1 s Φ) :
    -((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
        * (s ^ 3)⁻¹)
      + (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ
    ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
  -- the kinetic gap (`n₊`-absorption) and the count identity `n₊ + cS1 = N̂`
  have hgap : (1 / (36 * s ^ 2)) * cnPlus s Φ ≤ kinWord N s Φ :=
    kinWord_gap_cnPlus (N := N) (ℓ := s) hs hΦ
  have hS := cS1_eq_nat_sub_cnPlus (N := N) (ℓ := s) hs hΦ.continuous hnorm
  have hcnnn : (0 : ℝ) ≤ cnPlus s Φ := cnPlus_nonneg
  have hcnN : cnPlus s Φ ≤ (N : ℝ) := by
    have := cS1_nonneg (ℓ := s) (Φ := Φ)
    linarith
  have hCS' := hCS hΦ hnorm
  -- the `BogErr·n₊` term is nonnegative, so (arith) transfers to the shape we need
  have hBe : (0 : ℝ) ≤ BogErr * cnPlus s Φ := mul_nonneg hBog0 hcnnn
  -- the cancellation identity, stated in the exact shapes used
  have hdist : (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ
      = (1 / (36 * s ^ 2)) * cnPlus s Φ - BogErr * cnPlus s Φ := by ring
  rw [hdist]
  linarith [hgap, hCS', harith, hBe]

end Work.SmallBoxA0

namespace Work.SmallBoxA0

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Discharging the residual field of `BlockBoxData` from a kernel-`L²`
bound.**  With the PROVED Cauchy–Schwarz bound
`Work.SmallBoxA0.q4PairWord_cs_bound`, a data-level `L²`-bound
`‖w₁‖_{L²(acube s × acube s)} ≤ M` (`hM`, together with `MemLp` so that the
Bochner integral is not degenerate) and the explicit state-free arithmetic
condition, the recorded residual field's content holds for every admissible
`Φ`.  This is the honest, STATE-INDEPENDENT replacement for the pairing-only
reduction of `BogReduction` (which is false, see `README.md` §28.5). -/
lemma hBogF_of_kernel_L2 {N : ℕ} {s μ η BogErr M R : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hRs : R ≤ s * chiR0)
    (hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2
      (volume.restrict (abox 2 s)))
    (hM : Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2) ≤ M)
    (hAv : 0 ≤ a v) (hμ : 0 ≤ μ) (hBog0 : 0 ≤ BogErr)
    (hD : 0 ≤ g0w0Mass (v := v) h)
    (harith : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ * M
        ≤ (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
            * (s ^ 3)⁻¹
          + (88 * π + 39) * (a v) * μ)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) (hcS1 : 0 < cS1 s Φ) :
    -((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
        * (s ^ 3)⁻¹)
      + (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ
    ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
  have hs3i : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  have hNN : (0 : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ := by
    have h2 : (0 : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0]; norm_num
      · have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h0
        nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
    exact mul_nonneg h2 hs3i
  have hcs := q4PairWord_cs_bound (N := N) (R := R) hs hR hv_nonneg hvrad hv_supp h hRs hW2 hΦ hnorm
  have hstep : -((N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ * M) ≤ q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
    have hmul : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ *
        Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
        ≤ (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ * M :=
      mul_le_mul_of_nonneg_left hM hNN
    linarith [hcs, hmul]
  exact residual_of_pairing_cs h hs hAv hμ hBog0 hD (fun {Ψ} hΨ hn => by
    have := q4PairWord_cs_bound (N := N) (R := R) hs hR hv_nonneg hvrad hv_supp h hRs hW2 hΨ hn
    have hmul : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ *
        Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
        ≤ (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ * M :=
      mul_le_mul_of_nonneg_left hM hNN
    linarith [this, hmul]) harith hΦ hnorm hcS1

end Work.SmallBoxA0

namespace Work.SmallBoxA0

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The residual from the sharpest explicit hypothesis on the pairing kernel**
(`M` eliminated).  With `MemLp w₁ 2` and the kernel bound

    ‖w₁‖_{L²(acube s × acube s)} ≤ ½(1+η)·g0w0Mass ,    w₁ = wPairC s (g0 v h),

together with `0 ≤ BogErr`, `0 ≤ μ`, `0 ≤ a v`, `0 ≤ D`, the recorded residual
field's content holds for every admissible `Φ`.

Indeed the mass budget on the right of the residual is `½(1+η)D(N̂+1)N̂s⁻³` and
the Cauchy–Schwarz bound consumes `N̂(N̂−1)s⁻³‖w₁‖_{L²}`, so the comparison is
`N̂(N̂−1) ≤ (N̂+1)N̂` after cancelling `½(1+η)D s⁻³` in the kernel bound — no
`N̂`-dependence survives.  (The corpus's `g0w0Mass ≤ 8π(a v)`
(`Final.g0w0Mass_le_av`) is an UPPER bound on `D`, so it does NOT replace the
hypothesis by an `(a v)`-only one: a lower bound on `g0w0Mass` is what a
data-only form would need.) -/
lemma hBogF_of_w1_sqrt_le {N : ℕ} {s μ η BogErr R : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hRs : R ≤ s * chiR0)
    (hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2
      (volume.restrict (abox 2 s)))
    (hM : Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
        ≤ (1 / 2) * (1 + η) * g0w0Mass (v := v) h)
    (hAv : 0 ≤ a v) (hμ : 0 ≤ μ) (hBog0 : 0 ≤ BogErr) (hη0 : 0 ≤ η)
    (hD : 0 ≤ g0w0Mass (v := v) h)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) (hcS1 : 0 < cS1 s Φ) :
    -((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
        * (s ^ 3)⁻¹)
      + (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ
    ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
  have hs3i : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹
      ≤ (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹ := by
    have h1 : (N : ℝ) * ((N : ℝ) - 1) ≤ ((N : ℝ) + 1) * (N : ℝ) := by nlinarith [hN0]
    exact mul_le_mul_of_nonneg_right h1 hs3i
  refine hBogF_of_kernel_L2 (M := (1 / 2) * (1 + η) * g0w0Mass (v := v) h)
    h hs hR hv_nonneg hvrad hv_supp hRs hW2 ?_ hAv hμ hBog0 hD ?_ hΦ hnorm hcS1
  · -- `M := ½(1+η)D` closes `√(...) ≤ M`
    exact hM
  · -- the arithmetic condition at `M = ½(1+η)D`
    have hhalf : (0 : ℝ) ≤ (1 / 2) * (1 + η) := by linarith
    have hstep : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹
          * ((1 / 2) * (1 + η) * g0w0Mass (v := v) h)
        ≤ (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹
          * ((1 / 2) * (1 + η) * g0w0Mass (v := v) h) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    calc (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹
          * ((1 / 2) * (1 + η) * g0w0Mass (v := v) h)
        ≤ (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹
          * ((1 / 2) * (1 + η) * g0w0Mass (v := v) h) := hstep
      _ = (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
            * (s ^ 3)⁻¹ := by ring
      _ ≤ (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
            * (s ^ 3)⁻¹ + (88 * π + 39) * (a v) * μ := by
          have hp : (0 : ℝ) < π := Real.pi_pos
          have hμav : (0 : ℝ) ≤ (88 * π + 39) * (a v) * μ := by positivity
          linarith

end Work.SmallBoxA0

namespace Work.SmallBoxA0

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The residual from the PRIMITIVE data-level condition** (kernel bound
eliminated).  Given `Integrable (g₀²)`, `MemLp w₁ 2`, the sign conditions, and the
pure-data comparison

    4·chiSup⁴·s³·∫g₀²  ≤  (½(1+η)·g0w0Mass)² ,

the recorded residual field's content holds.

(`‖w₁‖²_{L²(abox 2 s)} ≤ 4·chiSup⁴·s³·∫g₀²` is `Work.SmallBoxA0.w1_L2_sq_le`,
delegated and PROVED; the comparison above is then exactly `hL2` of
`Work.SmallBoxA0.KernelL2BoxData` after square roots.) -/
lemma hBogF_of_g0_L2 {N : ℕ} {s μ η BogErr R : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hRs : R ≤ s * chiR0)
    (hint : Integrable (fun z : ℝ³ => (g0 v h z) ^ 2))
    (hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2
      (volume.restrict (abox 2 s)))
    (hg0 : 4 * chiSup ^ 4 * s ^ 3 * (∫ z : ℝ³, (g0 v h z) ^ 2)
        ≤ ((1 / 2) * (1 + η) * g0w0Mass (v := v) h) ^ 2)
    (hAv : 0 ≤ a v) (hμ : 0 ≤ μ) (hBog0 : 0 ≤ BogErr) (hη0 : 0 ≤ η)
    (hD : 0 ≤ g0w0Mass (v := v) h)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) (hcS1 : 0 < cS1 s Φ) :
    -((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
        * (s ^ 3)⁻¹)
      + (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ
    ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
  have hD0 : (0 : ℝ) ≤ (1 / 2) * (1 + η) := by linarith
  have hDnn : (0 : ℝ) ≤ (1 / 2) * (1 + η) * g0w0Mass (v := v) h := mul_nonneg hD0 hD
  refine hBogF_of_w1_sqrt_le h hs hR hv_nonneg hvrad hv_supp hRs hW2 ?_ hAv hμ hBog0 hη0 hD hΦ hnorm hcS1
  have hI := w1_L2_sq_le (s := s) (R := R) hs hR hv_nonneg hvrad hv_supp hRs h hint
  have hsq : (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
      ≤ ((1 / 2) * (1 + η) * g0w0Mass (v := v) h) ^ 2 := le_trans hI hg0
  calc Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
      ≤ Real.sqrt (((1 / 2) * (1 + η) * g0w0Mass (v := v) h) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |(1 / 2) * (1 + η) * g0w0Mass (v := v) h| := Real.sqrt_sq_eq_abs _
    _ = (1 / 2) * (1 + η) * g0w0Mass (v := v) h := abs_of_nonneg hDnn

end Work.SmallBoxA0

namespace Work.SmallBoxA0

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The residual with the `N̂`-SHARPENED kernel rung.**  The required comparison
`N̂(N̂−1)·M ≤ ½(1+η)D(N̂+1)N̂` holds with EQUALITY for `M := ½(1+η)D·(N̂+1)/(N̂−1)`,
which is up to `3×` weaker than `M ≤ ½(1+η)D` at `N̂ = 2` and tends to `½(1+η)D`
as `N̂ → ∞`.  This is the form in which the kernel rung reaches deepest into FS's
regime (`s ≲ 46·R0` at `N̂ = 2`, against `s ≲ 5·R0` for the `M ≤ ½(1+η)D` form of
`Work.SmallBoxA0.hBogF_of_w1_sqrt_le`). -/
lemma hBogF_of_w1_sqrt_le_N {N : ℕ} {s μ η BogErr R : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hRs : R ≤ s * chiR0)
    (hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2
      (volume.restrict (abox 2 s)))
    (hN : 2 ≤ N)
    (hM : Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
        ≤ (1 / 2) * (1 + η) * g0w0Mass (v := v) h * (((N : ℝ) + 1) / ((N : ℝ) - 1)))
    (hAv : 0 ≤ a v) (hμ : 0 ≤ μ) (hBog0 : 0 ≤ BogErr) (hη0 : 0 ≤ η)
    (hD : 0 ≤ g0w0Mass (v := v) h)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) (hcS1 : 0 < cS1 s Φ) :
    -((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
        * (s ^ 3)⁻¹)
      + (1 / (36 * s ^ 2) - BogErr) * cnPlus s Φ - (88 * π + 39) * (a v) * μ
    ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN2 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  refine hBogF_of_kernel_L2 (M := (1 / 2) * (1 + η) * g0w0Mass (v := v) h
      * (((N : ℝ) + 1) / ((N : ℝ) - 1)))
    h hs hR hv_nonneg hvrad hv_supp hRs hW2 hM hAv hμ hBog0 hD ?_ hΦ hnorm hcS1
  have heq : (N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹
        * ((1 / 2) * (1 + η) * g0w0Mass (v := v) h * (((N : ℝ) + 1) / ((N : ℝ) - 1)))
      = (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) * (N : ℝ))
        * (s ^ 3)⁻¹ := by
    field_simp
    try ring
  rw [heq]
  have hp : (0 : ℝ) < π := Real.pi_pos
  have hμav : (0 : ℝ) ≤ (88 * π + 39) * (a v) * μ := by positivity
  linarith

end Work.SmallBoxA0
