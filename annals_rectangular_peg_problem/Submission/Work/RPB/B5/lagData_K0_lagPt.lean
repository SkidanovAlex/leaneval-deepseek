import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.K0_chordSurf_level
import Submission.Work.RPB.B5.chartW_eq_chordSurf_sqrt
import Submission.Work.RPB.Defs
import Submission.Work.RPV.V
import Submission.Work.RPV.VBasic

/-!
# `Work.RPB.B5.lagData_K0_lagPt`

The level `K₀` of the assembled family `ℓ = lagPt W Γc Ac rho` (`Submission/Work/RPB/B5/Defs.lean`):

* on the **collar region** `√2 ≤ |x|` the family is the collar point
  `levelPt (Γc τ σ t) σ (Ac τ σ t)` with `σ = sig x = x²/2 - 1` (for `x ≥ √2` the base half at
  `-x` is `τ_π`-conjugated); since `K₀ (levelPt u σ a) = -1 - σ` and `K₀` is invariant under `tau`,
  this gives `K₀ (ℓ τ x t) = -x²/2`;
* on the **chord-chart region** `|x| < √2` the family is the chord chart `W τ t (rho τ x t)` (or its
  `τ_π`-image for `x > 0`), where `rho τ x t ∈ (0, π²/4]`, so `r = √(rho τ x t) ∈ (0, π/2]` lies in
  the range on which `W τ t (r²) = chordSurf CI.c a τ t r`.  By the chord level identity
  `K₀ (chordSurf …) + 1 = r² ‖halfChord …‖²` and `halfChord ≠ 0` (the two ends `c τ (t+r)`,
  `c τ (t-r)` of a chord with `0 < 2r ≤ π` are distinct because `CI.c τ` is injective modulo `2π`),
  this gives `K₀ (ℓ τ x t) > -1`.

Hence the level `K₀ = -1` (equivalently the blown-up diagonal `Λ`) is attained exactly at
`|x| = √2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.RPB.B5

private lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

/-! ## Unfolding `lagPt` and `basePt` in the two half planes / the two regions -/

/-- On `x ≤ 0` the family is its base half. -/
private lemma lagPt_of_nonpos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = basePt W Γc Ac rho τ x t := by
  rw [lagPt, ite_eq_left hx]

/-- On `x > 0` the family is `τ_π` of the reflected base half. -/
private lemma lagPt_of_pos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : 0 < x) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.tau Real.pi (basePt W Γc Ac rho τ (-x) (t - Real.pi)) := by
  rw [lagPt, ite_eq_right (not_le.mpr hx)]

/-- Deep on the left, the base half is the collar. -/
private lemma basePt_of_le (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    basePt W Γc Ac rho τ x t = collarPt Γc Ac τ (sig x) t := by
  rw [basePt, ite_eq_left hx]

/-- On `-√2 < x`, the base half is the chord chart. -/
private lemma basePt_of_gt (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : -Real.sqrt 2 < x) :
    basePt W Γc Ac rho τ x t = W τ t (rho τ x t) := by
  rw [basePt, ite_eq_right (not_le.mpr hx)]

/-- Canonical collar form of `lagPt` for `x ≤ -√2`. -/
private lemma lagPt_collar_neg (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t) := by
  have hx0 : x ≤ 0 := by linarith [sqrt_two_pos]
  rw [lagPt_of_nonpos W Γc Ac rho hx0, basePt_of_le W Γc Ac rho hx, collarPt]

/-- Canonical collar form of `lagPt` for `√2 ≤ x`: here the family is `τ_π` of the collar at
`-x`, and `τ_π` of a `levelPt` is a `levelPt` of the same reduced coordinate and level. -/
private lemma lagPt_collar_pos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : Real.sqrt 2 ≤ x) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.tau Real.pi
        (Work.RPV.levelPt (Γc τ (sig x) (t - Real.pi)) (sig x)
          (Ac τ (sig x) (t - Real.pi))) := by
  have hx0 : 0 < x := lt_of_lt_of_le sqrt_two_pos hx
  have hnx : -x ≤ -Real.sqrt 2 := by linarith
  have hs : sig (-x) = sig x := by simp only [sig]; ring
  rw [lagPt_of_pos W Γc Ac rho hx0, basePt_of_le W Γc Ac rho hnx, collarPt, hs]

/-! ## The collar region `√2 ≤ |x|` -/

/-- On the collar region, `K₀ (ℓ (x,t)) = -x²/2`. -/
private lemma K0_lagPt_of_ge (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : Real.sqrt 2 ≤ |x|) :
    Work.RPV.K0 (lagPt W Γc Ac rho τ x t) = -x ^ 2 / 2 := by
  by_cases hx0 : x ≤ 0
  · have hxs : x ≤ -Real.sqrt 2 := by
      have h := hx; rw [abs_of_nonpos hx0] at h; linarith
    rw [lagPt_collar_neg W Γc Ac rho hxs, Work.RPV.K0_levelPt]
    simp only [sig]; ring
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hxs : Real.sqrt 2 ≤ x := by
      have h := hx; rw [abs_of_pos hxpos] at h; exact h
    rw [lagPt_collar_pos W Γc Ac rho hxs, Work.RPV.K0_tau, Work.RPV.K0_levelPt]
    simp only [sig]; ring

/-! ## The chord-chart region `|x| < √2` -/

/-- The half chord `(c τ (t+r) - c τ (t-r))/(2r)` of a curve isotopy is nonzero for
`0 < r ≤ π/2`: a vanishing half chord would make `c τ (t+r) = c τ (t-r)`, i.e. (by injectivity
modulo `2π`) `2r ∈ 2πℤ`, which is impossible since `0 < 2r ≤ π`. -/
private lemma halfChord_ne_zero (CI : Work.RPV.CurveIsotopy) {τ r : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr0 : 0 < r) (hrπ : r ≤ Real.pi / 2) (t : ℝ) :
    Work.RPB.halfChord CI.c τ t r ≠ 0 := by
  intro h0
  have hdiff : CI.c τ (t + r) - CI.c τ (t - r) = 0 := by
    rw [Work.RPB.halfChord, div_eq_zero_iff] at h0
    rcases h0 with h | h
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr0)))
  have heq : CI.c τ (t + r) = CI.c τ (t - r) := sub_eq_zero.mp hdiff
  obtain ⟨m, hm⟩ := CI.inj τ hτ (t + r) (t - r) heq
  have hr_eq : r = -Real.pi * (m : ℝ) := by
    have h' : 2 * r = -(2 * Real.pi * (m : ℝ)) := by linarith
    linarith
  have hm0 : m = 0 := by
    rcases lt_trichotomy (m : ℝ) 0 with h | h | h
    · have hle : ((m : ℝ)) ≤ -1 := by
        have : m ≤ -1 := by
          have hm_lt : m < 0 := by exact_mod_cast h
          omega
        exact_mod_cast this
      have hpi_le : Real.pi ≤ r := by
        rw [hr_eq]; nlinarith [Real.pi_pos, hle]
      linarith [Real.pi_pos]
    · exact_mod_cast h
    · have hge : (1 : ℝ) ≤ (m : ℝ) := by
        have : (1 : ℤ) ≤ m := by
          have hm_gt : (0 : ℤ) < m := by exact_mod_cast h
          omega
        exact_mod_cast this
      have hle : r ≤ -Real.pi := by
        rw [hr_eq]; nlinarith [Real.pi_pos, hge]
      linarith [Real.pi_pos, hr0]
  have hr0' : r = 0 := by
    rw [hm0] at hr_eq
    simpa using hr_eq
  linarith [hr0]

/-- On the chord-chart region `-√2 < x ≤ 0`, the chart point `W τ t (rho τ x t)` has `K₀ > -1`. -/
private lemma chartK0_gt (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      -1 < Work.RPV.K0 (D.W τ t (D.rho τ x t)) := by
  intro τ hτ x hx t
  -- `r = √(rho τ x t) ∈ (0, π/2]`, where the chart is the chord surface
  obtain ⟨hpos, hle⟩ := D.hrhoval τ hτ x hx t
  set r : ℝ := Real.sqrt (D.rho τ x t) with hr
  have hr_pos : 0 < r := Real.sqrt_pos_of_pos hpos
  have hr_sq : r ^ 2 = D.rho τ x t := Real.sq_sqrt hpos.le
  have hr_le : r ≤ Real.pi / 2 := by
    have hpi : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have h := Real.sqrt_le_sqrt hle
    rw [hpi, ← hr] at h
    exact h
  have hmem : r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := ⟨hr_pos, hr_le⟩
  have hW : D.W τ t (D.rho τ x t) = Work.RPB.chordSurf CI.c a τ t r := by
    rw [← hr_sq]
    exact D.hWchord τ hτ t r hmem
  rw [hW]
  -- the chord level identity and the nonvanishing of the half chord
  have hlev := K0_chordSurf_level CI.c a τ t r
  have hne : Work.RPB.halfChord CI.c τ t r ≠ 0 := halfChord_ne_zero CI hτ hr_pos hr_le t
  have hpos2 : 0 < r ^ 2 * ‖Work.RPB.halfChord CI.c τ t r‖ ^ 2 :=
    mul_pos (pow_pos hr_pos 2) (pow_pos (norm_pos_iff.mpr hne) 2)
  linarith

/-- On the chord-chart region, `K₀ (ℓ (x,t)) > -1`, given the chart bound `hK`. -/
private lemma one_lt_K0_lagPt_of_lt (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ)
    (hK : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      -1 < Work.RPV.K0 (W τ t (rho τ x t)))
    {τ x t : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hx : |x| < Real.sqrt 2) :
    -1 < Work.RPV.K0 (lagPt W Γc Ac rho τ x t) := by
  have hsp : (0 : ℝ) < Real.sqrt 2 := sqrt_two_pos
  by_cases hx0 : x ≤ 0
  · have hgt : -Real.sqrt 2 < x := by
      have h := hx; rw [abs_of_nonpos hx0] at h; linarith
    have hmem : x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hgt, hx0⟩
    rw [lagPt_of_nonpos W Γc Ac rho hx0, basePt_of_gt W Γc Ac rho hgt]
    exact hK τ hτ x hmem t
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hgt : -Real.sqrt 2 < -x := by
      have h := hx; rw [abs_of_pos hxpos] at h; linarith
    have hmem : -x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hgt, by linarith⟩
    rw [lagPt_of_pos W Γc Ac rho hxpos, basePt_of_gt W Γc Ac rho hgt, Work.RPV.K0_tau]
    exact hK τ hτ (-x) hmem (t - Real.pi)

/-! ## The assembled statement -/

theorem lagData_K0_lagPt (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t : ℝ, Real.sqrt 2 ≤ |x| →
      Work.RPV.K0 (Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t) = -x ^ 2 / 2) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t : ℝ, |x| < Real.sqrt 2 →
      -1 < Work.RPV.K0 (Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t)) := by
  refine ⟨?_, ?_⟩
  · intro τ hτ x t hx
    exact K0_lagPt_of_ge D.W D.Γc D.Ac D.rho hx
  · intro τ hτ x t hx
    exact one_lt_K0_lagPt_of_lt D.W D.Γc D.Ac D.rho (chartK0_gt CI a D) hτ hx

end Work.RPB.B5
