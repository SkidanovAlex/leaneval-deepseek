import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.diniCoshBound
import Submission.Work.Mostow.diniResidual
import Submission.Work.Mostow.diniGHBound
import Submission.Work.Mostow.diniPhiBound

/-!
# The local Dini estimate for `1`-speed curves in ℍⁿ

If `γ : ℝ → ℍⁿ` is differentiable at `t` with `gH (γ t) v = 1` (unit hyperbolic speed),
then for every `ε > 0` and all small positive `h`

`hdist (γ t) (γ (t + h)) ≤ h * (1 + ε)`.

The proof collects the Taylor data of `cdist p q = cosh (hdist p q)` at `p = γ t`:

* `diniPhiBound` : `cdist p (p + w) - 1 ≤ gH p w / 2 + ‖w‖³`  (second-order expansion with cubic remainder);
* `diniGHBound`  : `gH p (h • v + R) ≤ h² * gH p v + 4h‖v‖‖R‖ + ‖R‖²`;
* `diniResidual` : `‖γ (t+h) - γ t - h • v‖ ≤ η h` for small `h`.

Writing `w = h • v + R` we get `gH p w ≤ h²(1 + 4η‖v‖ + η²) ≤ h²(1+ε)` and `‖w‖ ≤ h(‖v‖+η)`,
so `cosh (hdist (γ t) (γ (t+h))) = cdist ... ≤ 1 + h²(1+ε)²/2 ≤ cosh (h(1+ε))`, whence the claim
by monotonicity of `arcosh`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- `cdist p q = cosh (hdist p q) ≥ 1`, by Cauchy–Schwarz in the chart. -/
theorem diniOneLeCdist (p q : E n) : 1 ≤ cdist p q := by
  rw [cdist]
  have h1 : inner ℝ p q ≤ ‖p‖ * ‖q‖ := real_inner_le_norm p q
  have hmain : 1 + ‖p‖ * ‖q‖ ≤ tpart p * tpart q := by
    have ht : tpart p * tpart q = Real.sqrt ((1 + ‖p‖ ^ 2) * (1 + ‖q‖ ^ 2)) := by
      rw [tpart, tpart, ← Real.sqrt_mul (by positivity)]
    rw [ht]
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr
      (by nlinarith [sq_nonneg (‖p‖ - ‖q‖)])
  linarith

theorem diniEstimate {n : ℕ} (γ : ℝ → E n) (t : ℝ) (v : E n) (hv : HasDerivAt γ v t)
    (hsp : gH (γ t) v = 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Set.Ioo 0 δ, hdist (γ t) (γ (t + h)) ≤ h * (1 + ε) := by
  intro ε hε
  set η : ℝ := min 1 (ε / (8 * ‖v‖ + 2)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact lt_min one_pos (by positivity)
  have hηle1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
  have hηle : η ≤ ε / (8 * ‖v‖ + 2) := by rw [hηdef]; exact min_le_right _ _
  have hηbound : 4 * η * ‖v‖ + η ^ 2 ≤ ε := by
    have hden : (0 : ℝ) < 8 * ‖v‖ + 2 := by positivity
    have h1 : η * (8 * ‖v‖ + 2) ≤ ε := (le_div_iff₀ hden).mp hηle
    nlinarith [h1, hηle1, hηpos]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := diniResidual γ t v hv η hηpos
  set tm : ℝ := (ε + ε ^ 2) / (2 * (‖v‖ + η) ^ 3) with htmdef
  have htmpos : 0 < tm := by rw [htmdef]; positivity
  refine ⟨min δ₁ tm, lt_min hδ₁pos htmpos, ?_⟩
  intro h hh
  rw [Set.mem_Ioo] at hh
  obtain ⟨hhpos, hhlt⟩ := hh
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhlt (min_le_left _ _)
  have hhtm : h < tm := lt_of_lt_of_le hhlt (min_le_right _ _)
  set R : E n := γ (t + h) - γ t - h • v with hRdef
  have hR : ‖R‖ ≤ η * h := by
    have h' := hδ₁ h ⟨hhpos, hhδ₁⟩
    rw [← hRdef] at h'
    exact h'
  have hq : γ t + (h • v + R) = γ (t + h) := by
    rw [hRdef]; abel
  have hw : ‖h • v + R‖ ≤ h * (‖v‖ + η) := by
    have h1 : ‖h • v‖ = h * ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg hhpos.le]
    calc ‖h • v + R‖ ≤ ‖h • v‖ + ‖R‖ := norm_add_le _ _
      _ ≤ h * ‖v‖ + η * h := by rw [h1]; linarith [hR]
      _ = h * (‖v‖ + η) := by ring
  have hgh : gH (γ t) (h • v + R) ≤ h ^ 2 * (1 + ε) := by
    have h1 := diniGHBound (γ t) v R h hhpos.le
    rw [hsp] at h1
    have hR2 : ‖R‖ ^ 2 ≤ (η * h) ^ 2 := pow_le_pow_left₀ (norm_nonneg R) hR 2
    have hcross : 4 * h * ‖v‖ * ‖R‖ ≤ 4 * h * ‖v‖ * (η * h) :=
      mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 4 * h * ‖v‖)
    nlinarith [h1, hcross, hR2, hηbound, hηpos, hhpos]
  have hcdist : cdist (γ t) (γ (t + h)) - 1 ≤
      h ^ 2 * (1 + ε) / 2 + h ^ 3 * (‖v‖ + η) ^ 3 := by
    have hp := diniPhiBound (γ t) (h • v + R)
    rw [hq] at hp
    have hw3 : ‖h • v + R‖ ^ 3 ≤ h ^ 3 * (‖v‖ + η) ^ 3 := by
      calc ‖h • v + R‖ ^ 3 ≤ (h * (‖v‖ + η)) ^ 3 :=
            pow_le_pow_left₀ (norm_nonneg _) hw 3
        _ = h ^ 3 * (‖v‖ + η) ^ 3 := by ring
    nlinarith [hp, hgh, hw3]
  have hfinal : cdist (γ t) (γ (t + h)) - 1 ≤ h ^ 2 * (1 + ε) ^ 2 / 2 := by
    have htm2 : h * (‖v‖ + η) ^ 3 ≤ (ε + ε ^ 2) / 2 := by
      have h2D : (0 : ℝ) < 2 * (‖v‖ + η) ^ 3 := by positivity
      rw [htmdef] at hhtm
      rw [lt_div_iff₀ h2D] at hhtm
      linarith
    have htail : h ^ 3 * (‖v‖ + η) ^ 3 ≤ h ^ 2 * (ε + ε ^ 2) / 2 := by
      nlinarith [htm2, hhpos, hηpos.le, norm_nonneg v]
    nlinarith [hcdist, htail]
  have hcosh : cdist (γ t) (γ (t + h)) ≤ Real.cosh (h * (1 + ε)) := by
    have h2 := diniCoshBound (h * (1 + ε))
    have h1 : (h * (1 + ε)) ^ 2 = h ^ 2 * (1 + ε) ^ 2 := by ring
    rw [h1] at h2
    linarith
  have harg : 0 ≤ h * (1 + ε) := by positivity
  have hcd0 : 0 < cdist (γ t) (γ (t + h)) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (diniOneLeCdist (γ t) (γ (t + h)))
  have hstep : Real.arcosh (cdist (γ t) (γ (t + h))) ≤
      Real.arcosh (Real.cosh (h * (1 + ε))) :=
    (Real.arcosh_le_arcosh hcd0 (Real.cosh_pos _)).mpr hcosh
  rw [Real.arcosh_cosh harg] at hstep
  exact hstep

end Work.Mostow
