import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Backward iteration of a near-translation into the fundamental strip

Given a near-translation `F` on Shishikura's region `Qreg b₁ b₂` (so `‖F z - (z + 1)‖ ≤ 1/32`
on `Qreg b₁ b₂`), every point `z ∈ Qreg b₁ b₂` that is not to the left of the line `Re = x₀`
has an `F`-preimage in `Qreg b₁ b₂` with real part `≥ x₀`, unless `z` already lies in the
fundamental strip `fundStrip F (Qreg b₁ b₂) x₀`.  Iterating this dichotomy gives the lemma
below: every such `z` is reached from a point of the fundamental strip by forward iteration
which never leaves `Qreg b₁ b₂`.

The iteration terminates because every backward step decreases the real part by at least
`31/32`, while the real part stays `≥ x₀` as long as the dichotomy can be applied.  Note that
the hypotheses `Re b₁ + 1 < x₀`, `x₀ + 3 < Re b₂` (used for forward iteration) are *not*
needed here: if no preimage in `Qreg b₁ b₂` lies to the right of the line, `z` is in the
fundamental strip by definition, and this can happen well to the right of `x₀`.
-/

namespace Work.FatouCH

open MandelDim

/-- One step of a near-translation decreases the real part by at least `31/32`. -/
private lemma re_step_lower {F : ℂ → ℂ} {z w : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) (hw : F w = z) :
    w.re ≤ z.re - 31 / 32 := by
  have h1 : |(F w - (w + 1)).re| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_re_le_norm _) h
  have h2 : (F w - (w + 1)).re = z.re - w.re - 1 := by
    rw [hw]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have h3 : -(1 / 32 : ℝ) ≤ (F w - (w + 1)).re := (abs_le.mp h1).1
  rw [h2] at h3
  linarith

/-- The induction that drives the backward iteration: the number of steps is bounded by
`(z.re - x₀)/(31/32)`, so we induct on a natural number dominating that quantity. -/
private lemma backward_iterate_aux {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hF : NearTranslationOn F (Qreg b₁ b₂)) :
    ∀ n : ℕ, ∀ z : ℂ, z ∈ Qreg b₁ b₂ → x₀ ≤ z.re → z.re - x₀ < (n : ℝ) * (31 / 32) →
      ∃ k : ℕ, ∃ s ∈ fundStrip F (Qreg b₁ b₂) x₀,
        F^[k] s = z ∧ ∀ j ≤ k, F^[j] s ∈ Qreg b₁ b₂ := by
  intro n
  induction n with
  | zero =>
    intro z _ hzx hlt
    rw [Nat.cast_zero, zero_mul] at hlt
    linarith
  | succ n ih =>
    intro z hz hzx hlt
    by_cases hmem : z ∈ fundStrip F (Qreg b₁ b₂) x₀
    · refine ⟨0, z, hmem, by simp, ?_⟩
      intro j hj
      rw [Nat.le_zero.mp hj]
      simpa using hz
    · -- `z` is not in the fundamental strip: some preimage in `Q` is still right of the line
      have hnot : ¬ ∀ w : ℂ, w ∈ Qreg b₁ b₂ → F w = z → w.re < x₀ := by
        intro h
        exact hmem ⟨hz, hzx, h⟩
      obtain ⟨w, hwQ, hFw, hwx⟩ : ∃ w : ℂ, w ∈ Qreg b₁ b₂ ∧ F w = z ∧ x₀ ≤ w.re := by
        by_contra hc
        exact hnot fun w hwQ hFw => lt_of_not_ge fun hge => hc ⟨w, hwQ, hFw, hge⟩
      have hwlt : w.re - x₀ < (n : ℝ) * (31 / 32) := by
        have hstep : w.re ≤ z.re - 31 / 32 := re_step_lower ((hF.2 w hwQ).1) hFw
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hlt
        linarith
      obtain ⟨k, s, hs, hsk, hQ⟩ := ih w hwQ hwx hwlt
      refine ⟨k + 1, s, hs, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hsk, hFw]
      · intro j hj
        rcases Nat.lt_or_eq_of_le hj with hjk | hjk
        · exact hQ j (Nat.le_of_lt_succ hjk)
        · rw [hjk, Function.iterate_succ_apply', hsk, hFw]
          exact hz

open MandelDim in
/-- **Backward iteration reaches the fundamental strip.**  Every `z ∈ Qreg b₁ b₂` with
`x₀ ≤ Re z` is the `k`-th forward iterate of a point `s` of the fundamental strip, the orbit
in between staying inside `Qreg b₁ b₂`. -/
lemma backward_iterate {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hF : NearTranslationOn F (Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (hzx : x₀ ≤ z.re) :
    ∃ k : ℕ, ∃ s ∈ fundStrip F (Qreg b₁ b₂) x₀,
      F^[k] s = z ∧ ∀ j ≤ k, F^[j] s ∈ Qreg b₁ b₂ := by
  have hnonneg : 0 ≤ z.re - x₀ := by linarith
  refine backward_iterate_aux (x₀ := x₀) hF (Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀)) + 1)
    z hz hzx ?_
  have hle : (32 / 31 : ℝ) * (z.re - x₀) ≤ ((Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀))) : ℝ) :=
    Nat.le_ceil _
  have hcast : ((Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀)) + 1 : ℕ) : ℝ)
      = ((Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀))) : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hkey : z.re - x₀ = ((32 / 31 : ℝ) * (z.re - x₀)) * (31 / 32) := by ring
  have hmono : ((32 / 31 : ℝ) * (z.re - x₀)) * (31 / 32)
      ≤ ((Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀))) : ℝ) * (31 / 32) := by
    apply mul_le_mul_of_nonneg_right hle
    norm_num
  have hstrict : ((Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀))) : ℝ) * (31 / 32)
      < (((Nat.ceil ((32 / 31 : ℝ) * (z.re - x₀))) : ℝ) + 1) * (31 / 32) := by
    nlinarith
  linarith [hkey, hmono, hstrict]

end Work.FatouCH
