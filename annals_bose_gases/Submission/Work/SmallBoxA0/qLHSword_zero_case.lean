import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Pure real-arithmetic core of the `cS1 = 0` case.**  In the window
`x := N̂/s³ ≤ 9μ` and under the regime cap `μ(av)s²(1600 + 1850q) ≤ 1`
(`q ≥ 0`), the A₀-bracket is paid by the kinetic gap `N̂/(36s²)` minus the
crude one-body mean-field mass `μ·N̂·16πqa`:

    (¼(x−μ)² − ½μ²)·8πas³ ≤ N̂/(36s²) − μ·N̂·16πqa .

Equivalently, with `w := x/μ ∈ [0,9]`, the quadratic
`g(w) := 8π(¼(w−1)²−½) + 16πqw − w(1600+1850q)/36` satisfies `g ≤ 0` on
`[0,9]`, since it is convex and
`g(0) = −2π ≤ 0`, `g(9) = (124π−400) + (144π−462.5)q ≤ 0`
(using `124π ≤ 400` and `144π ≤ 462.5`, from `π < 3.15`). -/
lemma qZeroArith {N : ℕ} {s μ a q : ℝ} (hs : 0 < s) (hμ : 0 < μ) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (hwin : (N : ℝ) / s ^ 3 ≤ 9 * μ)
    (hgap : (μ * a * s ^ 2) * (1600 + 1850 * q) ≤ 1) :
    ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
        * (8 * π * a * s ^ 3)
      ≤ (N : ℝ) / (36 * s ^ 2) - μ * (N : ℝ) * (16 * π * q * a) := by
  set x : ℝ := (N : ℝ) / s ^ 3 with hx
  set A : ℝ := a * s ^ 2 with hA
  set M : ℝ := 1600 + 1850 * q with hM
  have hxnn : 0 ≤ x := by rw [hx]; positivity
  have hx9 : x ≤ 9 * μ := by rw [hx]; exact hwin
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hMpos : 0 < M := by rw [hM]; positivity
  have hxN : (N : ℝ) = x * s ^ 3 := by rw [hx]; field_simp
  -- the quadratic core, in the variable `w = x/μ`
  have hcore : ∀ w : ℝ, 0 ≤ w → w ≤ 9 →
      8 * π * ((1 / 4 : ℝ) * (w - 1) ^ 2 - (1 / 2)) + 16 * π * q * w ≤ w * M / 36 := by
    intro w hw0 hw9
    have hpi : π ≤ 3.15 := le_of_lt Real.pi_lt_d2
    have h1 : 124 * π ≤ 400 := by nlinarith [hpi]
    have h2 : 144 * π ≤ 462.5 := by nlinarith [hpi]
    have hb1 : 0 ≤ 400 - 124 * π := by linarith
    have hb2 : 0 ≤ 462.5 - 144 * π := by linarith
    have hid : w * M / 36
          - (8 * π * ((1 / 4 : ℝ) * (w - 1) ^ 2 - (1 / 2)) + 16 * π * q * w)
        = (1 - w / 9) * (2 * π)
          + (w / 9) * (400 - 124 * π + (462.5 - 144 * π) * q)
          + 2 * π * (w * (9 - w)) := by
      rw [hM]; ring
    have hA1 : 0 ≤ (1 - w / 9) * (2 * π) :=
      mul_nonneg (by linarith) (by positivity)
    have hA2 : 0 ≤ (w / 9) * (400 - 124 * π + (462.5 - 144 * π) * q) := by
      have hb3 : 0 ≤ 400 - 124 * π + (462.5 - 144 * π) * q := by
        have h := mul_nonneg hb2 hq
        linarith
      exact mul_nonneg (by positivity) hb3
    have hA3 : 0 ≤ 2 * π * (w * (9 - w)) :=
      mul_nonneg (by positivity) (mul_nonneg hw0 (by linarith))
    linarith [hid, hA1, hA2, hA3]
  -- multiply the core by `A ≤ 1/(μM)`
  have hkey : A * (8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2)
        + 16 * π * q * μ * x) ≤ x / 36 := by
    by_cases hc : 8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2)
        + 16 * π * q * μ * x ≤ 0
    · have h := mul_nonpos_of_nonneg_of_nonpos hAnn hc
      have hx36 : 0 ≤ x / 36 := by positivity
      linarith
    · push_neg at hc
      have hμM : 0 < μ * M := by positivity
      have hAM : A ≤ 1 / (μ * M) := by
        rw [le_div_iff₀ hμM]
        nlinarith [hgap, hA, hM]
      have hstep := mul_le_mul_of_nonneg_right hAM (le_of_lt hc)
      have hw0 : 0 ≤ x / μ := by positivity
      have hw9 : x / μ ≤ 9 := by
        rw [div_le_iff₀ hμ]
        linarith
      have hC := hcore (x / μ) hw0 hw9
      have hmul := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ μ ^ 2)
      have hf : μ ^ 2 * ((1 / 4 : ℝ) * (x / μ - 1) ^ 2 - (1 / 2))
          = (1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2 := by
        field_simp
      have hC' : 8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2)
            + 16 * π * q * μ * x ≤ μ * x * M / 36 := by
        have h1 : μ ^ 2 * (8 * π * ((1 / 4 : ℝ) * (x / μ - 1) ^ 2 - (1 / 2)))
            = 8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2) := by
          rw [← hf]; ring
        have h2 : μ ^ 2 * (16 * π * q * (x / μ)) = 16 * π * q * μ * x := by
          field_simp
        have h3 : μ ^ 2 * ((x / μ) * M / 36) = μ * x * M / 36 := by
          field_simp
        have hexp : μ ^ 2 * (8 * π * ((1 / 4 : ℝ) * (x / μ - 1) ^ 2 - (1 / 2))
              + 16 * π * q * (x / μ))
            = 8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2)
              + 16 * π * q * μ * x := by
          rw [mul_add, h1, h2]
        linarith [hmul, hexp, h3]
      have hgoal : (1 / (μ * M)) * (8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2)
            + 16 * π * q * μ * x) ≤ x / 36 := by
        have hm := mul_le_mul_of_nonneg_left hC'
          (show (0 : ℝ) ≤ 1 / (μ * M) by positivity)
        have he : (1 / (μ * M)) * (μ * x * M / 36) = x / 36 := by
          field_simp
        linarith [hm, he.le, he.symm.le]
      linarith [hstep, hgoal]
  -- convert back using `N̂ = x·s³` and `a·s³ = s·A`
  have hsnn : 0 ≤ s := le_of_lt hs
  have hmain : ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2) * (8 * π * a * s ^ 3)
      + μ * (x * s ^ 3) * (16 * π * q * a) ≤ x * s ^ 3 / (36 * s ^ 2) := by
    have heq : ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2) * (8 * π * a * s ^ 3)
        + μ * (x * s ^ 3) * (16 * π * q * a)
        = s * (A * (8 * π * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2) * μ ^ 2)
            + 16 * π * q * μ * x)) := by
      rw [hA]; ring
    have heq2 : x * s ^ 3 / (36 * s ^ 2) = s * (x / 36) := by
      field_simp
    rw [heq, heq2]
    exact mul_le_mul_of_nonneg_left hkey hsnn
  rw [hxN]
  linarith [hmain]

/-- **The `cS1 = 0` (fully excited) per-state case of the smallbox block
bound.**  With `cS1 s Φ = 0` every slice of `Φ` is mean-zero, so `aQᵢΦ = Φ`
and `qLHSword = −μ·qOneMass + q4word` with `q4word ≥ 0`; the kinetic energy
(`kinWord ≥ cnPlus/(36s²) = N̂/(36s²)`) plus the crude one-body bound
(`qOneMass ≤ 16π(av)n₊`) then pays the bracket.  Claimed at `C = 1` with the
`Γ`/`μ(av)` error terms dropped (they are additional non-negative losses, so
this form implies the recorded residual 3). -/
lemma qLHSword_zero_case {N : ℕ} {s μ R0 : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hz : cS1 s Φ = 0)
    (hwin : (N : ℝ) / s ^ 3 ≤ 9 * μ)
    (hgap : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1) :
    ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hav : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  -- the excited count equals the particle number
  have hcn : cnPlus s Φ = (N : ℝ) := by
    have h1 := cnPlus_add_cS1 hs hΦc.continuous
    rw [hnorm, mul_one] at h1
    linarith [h1, hz]
  -- kinetic gap
  have hkin : (N : ℝ) / (36 * s ^ 2) ≤ kinWord N s Φ := by
    have h1 := centredGap (ℓ := s) hs hΦc
    rw [hcn] at h1
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 36 * s ^ 2)]
    linarith [h1]
  -- crude one-body lower bound for the potential word
  have hpot : - (μ * (N : ℝ) * (16 * π * chiSup ^ 2 * (a v)))
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    have h1 := qLHSword_chosen_lower (N := N) (s := s) (R := R0) (μ := μ) (v := v)
      hR0 hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ.le hΦc
    rw [hnorm, mul_one] at h1
    have hsc : sboxC N μ v = μ * (N : ℝ) * (16 * π * chiSup ^ 2 * (a v)) := by
      rw [sboxC]; ring
    rw [hsc] at h1
    exact h1
  -- arithmetic
  have har := qZeroArith (N := N) (s := s) (μ := μ) (a := a v) (q := chiSup ^ 2)
    hs hμ hav (sq_nonneg chiSup) hwin hgap
  unfold sboxE
  linarith [har, hkin, hpot]

end Work.SmallBoxA0
