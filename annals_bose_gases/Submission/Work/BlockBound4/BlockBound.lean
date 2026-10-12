import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BlockBound4.diagW_block_bound_of_D1
import Submission.Work.BlockBound4.diagW_lm_appbogolubov_explicitC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The FS-shaped faithful block bound, and its unconditional form

`diagW_block_bound_of_D1` is the `eB`-level block shape at the faithful word,
with the named rung `DiagWD1BoxData.hD1` (FS's `lm:appbogolubov`).  This module

* turns it into FS's `thm:smallbox` shape — the convex density term
  `c·(x−μ)²/(1+x/μ)` with `x = N̂/s³`, `c = 1/50`, via the PROVED
  `Submission.BoseGases.smallboxConvex_count` (`SmallBoxConvexity.lean`);
* discharges the rung from **R1**
  (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`), giving the unconditional
  faithful block bound: NO rung, NO kernel-`L²` input, NO `modeP`-comparison.

The count-split (`n = m·n′ + n″`, FS's grouping trick) is available at the
faithful word from the PROVED `Work.KinPSuperadd.diagKinPeBAt_group_superadd`
(`door4Superadd`): that is the piece the corpus's own `eB`-chain is missing
(see `SmallBoxA0/README.md` §30).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The FS `thm:smallbox` shape at the faithful word** (density term
`c(x−μ)²/(1+x/μ)`, `x = N̂/s³`, `c = 1/50`), over the D1 bundle. -/
theorem diagW_block_bound_FS :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : DiagWD1BoxData,
      (c * ((((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
            / (1 + ((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) / D.μ))
          - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ diagWeB D.n D.s D.μ D.v D.h D.c₀ D.cgap := by
  obtain ⟨C, hC0, hblk⟩ := diagW_block_bound_of_D1
  refine ⟨1 / 50, by norm_num, by norm_num, C, hC0, ?_⟩
  intro D
  have hav : 0 ≤ a D.v := le_of_lt D.hav
  have hμnn : 0 ≤ D.μ := le_of_lt D.hμ
  have hs3 : (0 : ℝ) ≤ D.s ^ 3 := pow_nonneg (le_of_lt D.hs) 3
  set x : ℝ := (((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3 with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    exact div_nonneg (by positivity) hs3
  have hconv := smallboxConvex_count (μ := D.μ) (x := x) (c := 1 / 50) D.hμ hx0
    (by norm_num) (by norm_num : (1 / 50 : ℝ) ≤ 1 / 4)
  have hcoef : (0 : ℝ) ≤ 8 * π * (a D.v) * D.s ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) hav) hs3
  have hmul := mul_le_mul_of_nonneg_right hconv hcoef
  have hblkD := hblk D
  have hstep : (1 / 50 * ((x - D.μ) ^ 2 / (1 + x / D.μ)) - (1 / 2 : ℝ) * D.μ ^ 2)
        * (8 * π * (a D.v) * D.s ^ 3)
      ≤ ((1 / 4 : ℝ) * (x - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
        * (8 * π * (a D.v) * D.s ^ 3) := by
    linarith [hmul]
  rw [hxdef] at hstep
  linarith [hstep, hblkD]

/-! ## The rung discharged: the unconditional faithful block bound -/

/-- **The Door-4 bundle with the rung DISCHARGED from R1**
(`diagW_lm_appbogolubov_explicitC`).  This is the one-line bridge from R1 to the
rung `DiagWD1BoxData.hD1`. -/
def toDiagWD1BoxData (D : DiagWBoxData) : DiagWD1BoxData :=
  { D with
    hD1 := by
      intro N hN Φ hΦc hnorm
      obtain ⟨C, hCeq, _hC0, hD1⟩ :=
        diagW_lm_appbogolubov_explicitC (N := N) (s := D.s) (c0 := D.c₀) (Ct := D.Ct)
          D.hs D.hc0 D.hv_nonneg D.hvrad D.hv_memL1 D.hR0 D.hv_supp D.h D.hRs hN
          D.hav D.hdil (by simpa only [one_div] using D.hWfin) D.hCt
          (by simpa only [one_div] using D.hNewton)
      have h := hD1 Φ hΦc hnorm
      rw [hCeq] at h
      simp only [d4MassCoeff, d4Eta, d4Bracket, d4BogErr, Work.SmallBoxA0.kinPeta,
        Work.SmallBoxA0.kinPBracket, Work.SmallBoxA0.kinPBogErr, Work.SmallBoxA0.d1C,
        one_div] at h ⊢
      ring_nf at h ⊢
      exact h }

/-- **The UNCONDITIONAL faithful block bound**: the block shape at the faithful
word, over the corpus's bundle, with NO rung (FS's `lm:appbogolubov` is supplied
by R1). -/
theorem diagW_block_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : DiagWBoxData,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ diagWeB D.n D.s D.μ D.v D.h D.c₀ D.cgap := by
  obtain ⟨C, hC0, h⟩ := diagW_block_bound_of_D1
  exact ⟨C, hC0, fun D => h (toDiagWD1BoxData D)⟩

/-- **The unconditional FS shape**: FS's `thm:smallbox` with the convex density
term, at the faithful word, with NO rung. -/
theorem diagW_block_bound_FS_uncond :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : DiagWBoxData,
      (c * ((((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
            / (1 + ((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) / D.μ))
          - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ diagWeB D.n D.s D.μ D.v D.h D.c₀ D.cgap := by
  obtain ⟨c, hc0, hc, C, hC0, h⟩ := diagW_block_bound_FS
  exact ⟨c, hc0, hc, C, hC0, fun D => h (toDiagWD1BoxData D)⟩

end Work.BlockBound4
