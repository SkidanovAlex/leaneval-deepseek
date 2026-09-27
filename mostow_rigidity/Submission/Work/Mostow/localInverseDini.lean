import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.diniResidual
import Submission.Work.Mostow.diniPhiBound
import Submission.Work.Mostow.diniGHBound
import Submission.Work.Mostow.diniCoshBound
import Submission.Work.Mostow.segfunHdist
import Submission.Work.Mostow.segfunSpeed

/-!
# The one-sided Dini estimate: `hdist (γ t) (γ (t+h)) ≤ h (1+ε)`

If `γ : ℝ → E n` is differentiable at `t` with `gH (γ t) v = 1` (i.e. `γ` has unit
hyperbolic speed at `t`), then for every `ε > 0` the hyperbolic distance from `γ t`
to `γ (t+h)` is at most `h (1+ε)` for all small positive `h`.

This is the chart (hyperboloid model) second-order expansion of
`cdist p q = cosh (hdist p q)` at `p = γ t`, done for the increment
`w = h • v + R` with `R = γ (t+h) - γ t - h • v = o(h)`:

* `diniPhiBound` : `cdist p (p + w) - 1 ≤ gH p w / 2 + ‖w‖³`;
* `diniGHBound`  : `gH p (h • v + R) ≤ h² gH p v + 4 h ‖v‖ ‖R‖ + ‖R‖²`;
* `diniResidual` : `‖γ (t + h) - γ t - h • v‖ ≤ η h` for `h` small.

With `gH p v = 1` these give `cdist (γ t) (γ (t+h)) - 1 ≤ h² ((1 + 4η‖v‖ + η²)/2 + h(‖v‖+η)³)`,
and choosing `η` and `h` small enough (elementary arithmetic in `localInverseDini_arith`)
makes this `≤ h² (1+ε)²/2 ≤ cosh (h(1+ε)) - 1` by the two-term Taylor bound `diniCoshBound`.
Since `x ↦ arccosh x` is increasing on `(0,∞)`, the claim follows.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- Cauchy–Schwarz in the chart: `cdist p q = cosh (hdist p q)` is `≥ 1`. -/
private theorem localInverseDini_cdist_ge_one (p q : E n) : 1 ≤ cdist p q := by
  rw [cdist]
  have h1 : inner ℝ p q ≤ ‖p‖ * ‖q‖ := real_inner_le_norm p q
  have hmain : 1 + ‖p‖ * ‖q‖ ≤ tpart p * tpart q := by
    have ht : tpart p * tpart q = Real.sqrt ((1 + ‖p‖ ^ 2) * (1 + ‖q‖ ^ 2)) := by
      rw [tpart, tpart, ← Real.sqrt_mul (by positivity)]
    rw [ht]
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr
      (by nlinarith [sq_nonneg (‖p‖ - ‖q‖)])
  linarith

/-- `cdist` is `cosh` of the hyperbolic distance. -/
private theorem localInverseDini_cosh_hdist (p q : E n) :
    Real.cosh (hdist p q) = cdist p q := by
  rw [hdist]
  exact Real.cosh_arcosh (localInverseDini_cdist_ge_one p q)

/-- The elementary `η`/`δ` bookkeeping: for a speed bound `K ≥ 0` and `ε > 0` there are
`0 < η ≤ 1` and `δ > 0` with `(1 + 4ηK + η²)/2 + δ (K+1)³ ≤ (1+ε)²/2`. -/
private theorem localInverseDini_arith {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ δ : ℝ, 0 < δ ∧
      (1 + 4 * η * K + η ^ 2) / 2 + δ * (K + 1) ^ 3 ≤ (1 + ε) ^ 2 / 2 := by
  have hK2 : (0 : ℝ) < K + 2 := by linarith
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  set η : ℝ := min 1 (ε / (8 * (K + 2))) with hηdef
  set δ : ℝ := ε / (16 * (K + 1) ^ 3) with hδdef
  have hηpos : 0 < η := by rw [hηdef]; exact lt_min one_pos (by positivity)
  have hηle1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
  have hηle : η ≤ ε / (8 * (K + 2)) := by rw [hηdef]; exact min_le_right _ _
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  refine ⟨η, hηpos, hηle1, δ, hδpos, ?_⟩
  have hden : (0 : ℝ) < 8 * (K + 2) := by positivity
  have hη8 : η * (8 * (K + 2)) ≤ ε := (le_div_iff₀ hden).mp hηle
  have h2ηK : 2 * η * K ≤ ε / 4 := by nlinarith [hη8, hηpos.le, hK]
  have hη16 : 16 * η ≤ ε := by nlinarith [hη8, hηpos.le, hK]
  have h2 : η ^ 2 / 2 ≤ ε / 16 := by nlinarith [hη16, hηle1, hηpos.le]
  have h3 : δ * (K + 1) ^ 3 ≤ ε / 16 := by
    rw [hδdef, div_mul_eq_mul_div]
    rw [mul_div_mul_right ε 16 (pow_ne_zero 3 (ne_of_gt hK1))]
  nlinarith [h2ηK, h2, h3, hε.le, sq_nonneg ε]

/-- **The Dini estimate.**  A curve of unit hyperbolic speed at `t` moves at most
`h (1+ε)` in hyperbolic distance over the parameter increment `h > 0`, for small `h`. -/
theorem localInverseDini {n : ℕ} (γ : ℝ → E n) (t : ℝ) (v : E n) (hv : HasDerivAt γ v t)
    (hsp : gH (γ t) v = 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Set.Ioo 0 δ, hdist (γ t) (γ (t + h)) ≤ h * (1 + ε) := by
  intro ε hε
  obtain ⟨η, hηpos, hηle1, δ₀, hδ₀pos, harith⟩ :=
    localInverseDini_arith (norm_nonneg v) hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := diniResidual γ t v hv η hηpos
  refine ⟨min δ₁ δ₀, lt_min hδ₁pos hδ₀pos, ?_⟩
  intro h hh
  rw [Set.mem_Ioo] at hh
  obtain ⟨hhpos, hhlt⟩ := hh
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhlt (min_le_left _ _)
  have hhδ₀ : h < δ₀ := lt_of_lt_of_le hhlt (min_le_right _ _)
  set R : E n := γ (t + h) - γ t - h • v with hRdef
  have hR : ‖R‖ ≤ η * h := by
    have h' := hδ₁ h ⟨hhpos, hhδ₁⟩
    rw [← hRdef] at h'
    exact h'
  have hq : γ t + (h • v + R) = γ (t + h) := by rw [hRdef]; abel
  have hw : ‖h • v + R‖ ≤ h * (‖v‖ + η) := by
    have h1 : ‖h • v‖ = h * ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg hhpos.le]
    calc ‖h • v + R‖ ≤ ‖h • v‖ + ‖R‖ := norm_add_le _ _
      _ ≤ h * ‖v‖ + η * h := by rw [h1]; linarith [hR]
      _ = h * (‖v‖ + η) := by ring
  have hgh : gH (γ t) (h • v + R) ≤ h ^ 2 + 4 * h * ‖v‖ * (η * h) + (η * h) ^ 2 := by
    have h1 := diniGHBound (γ t) v R h hhpos.le
    rw [hsp] at h1
    simp only [mul_one] at h1
    have hR2 : ‖R‖ ^ 2 ≤ (η * h) ^ 2 := pow_le_pow_left₀ (norm_nonneg R) hR 2
    have hcross : 4 * h * ‖v‖ * ‖R‖ ≤ 4 * h * ‖v‖ * (η * h) :=
      mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 4 * h * ‖v‖)
    linarith
  have hw3 : ‖h • v + R‖ ^ 3 ≤ h ^ 3 * (‖v‖ + η) ^ 3 := by
    calc ‖h • v + R‖ ^ 3 ≤ (h * (‖v‖ + η)) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hw 3
      _ = h ^ 3 * (‖v‖ + η) ^ 3 := by ring
  have hcdist : cdist (γ t) (γ (t + h)) - 1 ≤ h ^ 2 * (1 + ε) ^ 2 / 2 := by
    have hp := diniPhiBound (γ t) (h • v + R)
    rw [hq] at hp
    have hmain : cdist (γ t) (γ (t + h)) - 1 ≤
        h ^ 2 * ((1 + 4 * η * ‖v‖ + η ^ 2) / 2 + h * (‖v‖ + η) ^ 3) := by
      have hgH2 : gH (γ t) (h • v + R) / 2 ≤
          (h ^ 2 + 4 * h * ‖v‖ * (η * h) + (η * h) ^ 2) / 2 := by linarith [hgh]
      have hsum : (h ^ 2 + 4 * h * ‖v‖ * (η * h) + (η * h) ^ 2) / 2
          + (h * (‖v‖ + η)) ^ 3
          = h ^ 2 * ((1 + 4 * η * ‖v‖ + η ^ 2) / 2 + h * (‖v‖ + η) ^ 3) := by ring
      calc cdist (γ t) (γ (t + h)) - 1
          ≤ gH (γ t) (h • v + R) / 2 + ‖h • v + R‖ ^ 3 := hp
        _ ≤ (h ^ 2 + 4 * h * ‖v‖ * (η * h) + (η * h) ^ 2) / 2
              + (h * (‖v‖ + η)) ^ 3 := by linarith [hgH2, hw3]
        _ = h ^ 2 * ((1 + 4 * η * ‖v‖ + η ^ 2) / 2 + h * (‖v‖ + η) ^ 3) := hsum
    have hδ' : h * (‖v‖ + η) ^ 3 ≤ δ₀ * (‖v‖ + 1) ^ 3 := by
      have h1 : ‖v‖ + η ≤ ‖v‖ + 1 := by linarith [hηle1]
      have h2 : (‖v‖ + η) ^ 3 ≤ (‖v‖ + 1) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h1 3
      have h3 : h * (‖v‖ + η) ^ 3 ≤ δ₀ * (‖v‖ + η) ^ 3 :=
        mul_le_mul_of_nonneg_right hhδ₀.le (by positivity)
      have h4 : δ₀ * (‖v‖ + η) ^ 3 ≤ δ₀ * (‖v‖ + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left h2 hδ₀pos.le
      linarith
    have harith' : (1 + 4 * η * ‖v‖ + η ^ 2) / 2 + h * (‖v‖ + η) ^ 3 ≤
        (1 + ε) ^ 2 / 2 := by linarith [harith, hδ']
    have hmul := mul_le_mul_of_nonneg_left harith' (sq_nonneg h)
    linarith [hmain, hmul]
  have hcosh : cdist (γ t) (γ (t + h)) ≤ Real.cosh (h * (1 + ε)) := by
    have h2 := diniCoshBound (h * (1 + ε))
    have h1 : (h * (1 + ε)) ^ 2 = h ^ 2 * (1 + ε) ^ 2 := by ring
    rw [h1] at h2
    linarith
  have harg : 0 ≤ h * (1 + ε) := by positivity
  have hcd0 : 0 < cdist (γ t) (γ (t + h)) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (localInverseDini_cdist_ge_one (γ t) (γ (t + h)))
  have hstep : Real.arcosh (cdist (γ t) (γ (t + h))) ≤
      Real.arcosh (Real.cosh (h * (1 + ε))) :=
    (Real.arcosh_le_arcosh hcd0 (Real.cosh_pos _)).mpr hcosh
  rw [Real.arcosh_cosh harg] at hstep
  simpa [hdist, cdist] using hstep

end Work.Mostow
