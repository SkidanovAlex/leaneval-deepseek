import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs

/-!
# B5: the two-sided decomposition of `lagPt` near `x = -√2`

`lagPt` is the collar `collarPt Γc Ac τ (sig x) t` for `x ≤ -√2` and the chord chart
`W τ t (rho τ x t)` for `-√2 ≤ x ≤ 0` (`sig x = x²/2 - 1 ≥ 0`).

Near `x = -√2` the level `sig x` is small and `rho` agrees with the level inverse
`ρh (sig ·)` on a two-sided neighbourhood (`LagData.hrhonearδ`), so the *chart* branch may be
written as `W τ t (ρh τ t (sig x))` — which is exactly the `σ ≤ 0` branch of the right-hand
side.  The collar branch `x < -√2` gives `sig x > 0` and matches the `else` branch verbatim; at
the junction `x = -√2` (`sig = 0`) the value matching is the order-`0` jet hypothesis
`LagData.σjet`.
-/

namespace Work.RPB.B5

/-- `sig (-√2) = 0`. -/
private lemma sig_neg_sqrt_two : sig (-Real.sqrt 2) = 0 := by
  simp only [sig, neg_sq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

/-- On the collar's range `x < -√2` the attached level `sig x = x²/2 - 1` is positive. -/
private lemma sig_pos_of_lt_neg_sqrt_two {x : ℝ} (hx : x < -Real.sqrt 2) : 0 < sig x := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : 2 < x ^ 2 := by nlinarith [hs, Real.sqrt_nonneg 2]
  simp only [sig]
  linarith

/-- For `-√2 < x < 0` the attached level `sig x` is negative. -/
private lemma sig_neg_of_lt {x : ℝ} (h1 : -Real.sqrt 2 < x) (h2 : x < 0) : sig x < 0 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : x ^ 2 < 2 := by nlinarith [hs, Real.sqrt_nonneg 2]
  simp only [sig]
  linarith

theorem lagPt_negSqrt2_decomp (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ x : ℝ,
      |x + Real.sqrt 2| < δ →
      Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t
        = (if Work.RPB.B5.sig x ≤ 0 then D.W τ t (D.ρh τ t (Work.RPB.B5.sig x))
            else Work.RPB.B5.collarPt D.Γc D.Ac τ (Work.RPB.B5.sig x) t) := by
  obtain ⟨δ, hδpos, hδ14, _hδκ, hnear, _hnear0⟩ := D.hrhonearδ
  refine ⟨δ, hδpos, by linarith, ?_⟩
  intro τ hτ t x hx
  have hab := abs_lt.mp hx
  have hxhi : x < -Real.sqrt 2 + δ := by linarith [hab.2]
  have hxlo : -Real.sqrt 2 - δ < x := by linarith [hab.1]
  have hxneg : x < 0 := by linarith [hxhi, hδ14, Real.one_lt_sqrt_two]
  -- unlock the two `if`s of `lagPt` and `basePt`, picking the `x ≤ 0` half
  unfold lagPt basePt
  rw [ite_eq_left (le_of_lt hxneg)]
  rcases lt_trichotomy x (-Real.sqrt 2) with hlt | heq | hgt
  · -- collar branch: `x < -√2`, so `sig x > 0` and both sides are `collarPt`
    rw [ite_eq_left (le_of_lt hlt), ite_eq_right (not_le.mpr (sig_pos_of_lt_neg_sqrt_two hlt))]
  · -- junction `x = -√2`: `sig (-√2) = 0`, value matching is the `0`-jet of `σjet`
    rw [heq, ite_eq_left le_rfl, sig_neg_sqrt_two, ite_eq_left le_rfl]
    have h0val : Work.RPV.levelPt (D.Γc τ 0 t) 0 (D.Ac τ 0 t) = D.W τ t (D.ρh τ t 0) := by
      have h := D.σjet τ hτ t 0 (by norm_num)
      simpa only [iteratedDerivWithin_zero, iteratedDeriv_zero] using h
    simpa only [collarPt] using h0val
  · -- chart branch: `-√2 < x`, `sig x < 0`, and `rho τ x t = ρh τ t (sig x)` near `-√2`
    rw [ite_eq_right (not_le.mpr hgt), ite_eq_left (le_of_lt (sig_neg_of_lt hgt hxneg))]
    rw [hnear τ hτ x ⟨hxlo, hxhi⟩ t]

end Work.RPB.B5
