import Mathlib
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddEnvelope.Defs

/-!
# Basic regularity of the two-piece low-slope curve

`Work.OddCurve.LowSlope.lowSlopeCurveY R Y` is the two-piece chord-endpoint function of the
low-slope reconstruction: it is the radial parametrisation `σ ↦ R (arctan σ) * cos (arctan σ)`
for `σ < 3/4`, and the anchor's curve `Y` for `σ ≥ 3/4` (and symmetrically for the `X`/`r`
version).  This file proves the elementary regularity facts about it that the assembly of the
odd curve needs:

* it is `C^∞` on `(0, ∞)`;
* it has a positive limit as `σ → 0⁺` (namely `R 0`, resp. `r 0`);
* beyond the perturbation window `[1 - τ, ∞)` it agrees with the semicircle's chord function
  `profileX`.

The glue at `σ = 3/4` works because the two pieces *agree* on the closed window
`[3/4, 4/5]` (`hjunc`): the whole function coincides with the smooth radial parametrisation on
`(0, 4/5)` and with `Y` on `(3/4, ∞)`, a pair of open sets covering `(0, ∞)`.

Everything about `R` and `r` that is used is `C^∞`-ness on the closed interval `[0, π/2]`
together with the two-sided `ε`-bounds at `α = 0`, which give the positivity of the limits.
-/

namespace Work.OddCurve.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- The radial parametrisation `σ ↦ R (arctan σ) * cos (arctan σ)` is `C^∞` on `(0, ∞)` when `R`
is `C^∞` on `[0, π/2]`. -/
private lemma contDiffOn_radial_branch (R : ℝ → ℝ)
    (hRc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2))) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun σ : ℝ => R (Real.arctan σ) * Real.cos (Real.arctan σ)) (Set.Ioi 0) := by
  have hmap : Set.MapsTo Real.arctan (Set.Ioi (0 : ℝ)) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    intro σ hσ
    exact ⟨le_of_lt (Real.arctan_pos.mpr hσ), le_of_lt (Real.arctan_lt_pi_div_two σ)⟩
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => R (Real.arctan σ))
      (Set.Ioi 0) :=
    hRc.comp Real.contDiff_arctan.contDiffOn hmap
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => Real.cos (Real.arctan σ))
      (Set.Ioi 0) :=
    Real.contDiff_cos.contDiffOn.comp Real.contDiff_arctan.contDiffOn hmap
  exact h1.mul h2

/-- Gluing a two-piece function `σ ↦ if σ < c then G σ else F σ` of `C^∞` pieces along a
*common interval* `[c, d]` on which they agree.  Since `(0, d)` and `(c, ∞)` cover `(0, ∞)` when
`0 < c < d`, smoothness follows pointwise from `contDiffOn_of_locally_contDiffOn`. -/
private lemma contDiffOn_ite_glue {F G : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.Ioi 0))
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioi 0))
    (hagree : ∀ σ : ℝ, c ≤ σ → σ < d → G σ = F σ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => if σ < c then G σ else F σ)
      (Set.Ioi 0) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  rcases lt_or_ge x d with hlt | hge
  · refine ⟨Set.Iio d, isOpen_Iio, hlt, ?_⟩
    have heq : ∀ σ ∈ Set.Ioi (0 : ℝ) ∩ Set.Iio d,
        (if σ < c then G σ else F σ) = G σ := by
      rintro σ ⟨hσ0, hσd⟩
      rcases lt_or_ge σ c with h | h
      · rw [if_pos h]
      · rw [if_neg (not_lt.mpr h), hagree σ h hσd]
    exact (hG.mono (fun σ hσ => hσ.1)).congr heq
  · refine ⟨Set.Ioi c, isOpen_Ioi, lt_of_lt_of_le hcd hge, ?_⟩
    have heq : ∀ σ ∈ Set.Ioi (0 : ℝ) ∩ Set.Ioi c,
        (if σ < c then G σ else F σ) = F σ := by
      rintro σ ⟨hσ0, hσc⟩
      rw [if_neg (not_lt.mpr (le_of_lt hσc))]
    exact (hF.mono (fun σ hσ => lt_trans hc hσ.2)).congr heq

/-- The radial parametrisation `σ ↦ R (arctan σ) * cos (arctan σ)` is continuous at `0` within
`(0, ∞)`. -/
private lemma continuousWithinAt_radial_branch (R : ℝ → ℝ)
    (hRc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2))) :
    ContinuousWithinAt (fun σ : ℝ => R (Real.arctan σ) * Real.cos (Real.arctan σ))
      (Set.Ioi 0) 0 := by
  have hmap : Set.MapsTo Real.arctan (Set.Ioi (0 : ℝ)) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    intro σ hσ
    exact ⟨le_of_lt (Real.arctan_pos.mpr hσ), le_of_lt (Real.arctan_lt_pi_div_two σ)⟩
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_refl _, by positivity⟩
  have harc : ContinuousWithinAt Real.arctan (Set.Ioi 0) 0 :=
    Real.continuous_arctan.continuousWithinAt
  have hR0 : ContinuousWithinAt R (Set.Icc (0 : ℝ) (Real.pi / 2)) (Real.arctan 0) := by
    simpa using hRc.continuousOn.continuousWithinAt hmem
  have h1 : ContinuousWithinAt (fun σ : ℝ => R (Real.arctan σ)) (Set.Ioi 0) 0 :=
    hR0.comp harc hmap
  have h2 : ContinuousWithinAt (fun σ : ℝ => Real.cos (Real.arctan σ)) (Set.Ioi 0) 0 :=
    (Real.continuous_cos.continuousWithinAt (s := Set.Icc (0 : ℝ) (Real.pi / 2))
      (x := Real.arctan 0)).comp harc hmap
  exact h1.mul h2

/-- The two-piece function `σ ↦ if σ < c then G σ else F σ` tends to `G 0` as `σ → 0⁺`, because
the branch `G` is the active one on a right neighbourhood of `0`. -/
private lemma tendsto_ite_nhds_zero {F G : ℝ → ℝ} {c b : ℝ} (hc : 0 < c)
    (hG : ContinuousWithinAt G (Set.Ioi 0) 0) (hb : G 0 = b) :
    Tendsto (fun σ : ℝ => if σ < c then G σ else F σ) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  have hmem : Set.Iio c ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin.mpr ⟨Set.Iio c, isOpen_Iio, hc, fun x hx => hx.1⟩
  have hev : (fun σ : ℝ => if σ < c then G σ else F σ) =ᶠ[𝓝[>] (0 : ℝ)] G := by
    filter_upwards [hmem] with σ hσ
    exact if_pos hσ
  have h := Filter.Tendsto.congr' hev.symm hG.tendsto
  rwa [hb] at h

theorem lowSlopeCurveBasic (h X Y R r : ℝ → ℝ) {ε : ℝ} (hε : ε < 1)
    (hXY : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hRc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hrc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |R α - 1| ≤ ε)
    (hr0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |r α - 1| ≤ ε)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ) ∧
      X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) (Set.Ioi 0) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.lowSlopeCurveX r X) (Set.Ioi 0) ∧
    (∃ b : ℝ, 0 < b ∧ Filter.Tendsto (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b)) ∧
    (∃ a : ℝ, 0 < a ∧ Filter.Tendsto (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a)) ∧
    (∀ s : ℝ, 1 - Work.OddEnvelope.tau ≤ s →
      Work.OddCurve.LowSlope.lowSlopeCurveY R Y s = Work.OddEnvelope.profileX s) ∧
    (∀ s : ℝ, 1 - Work.OddEnvelope.tau ≤ s →
      Work.OddCurve.LowSlope.lowSlopeCurveX r X s = Work.OddEnvelope.profileX s) := by
  -- smoothness of the right-hand piece, gluing the radial parametrisation to the anchor's `Y`
  have hYc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) (Set.Ioi 0) :=
    contDiffOn_ite_glue (F := Y) (G := fun σ : ℝ => R (Real.arctan σ) * Real.cos (Real.arctan σ))
      (c := 3 / 4) (d := 4 / 5) (by norm_num) (by norm_num)
      (contDiffOn_radial_branch R hRc) hXY.smooth_y
      (fun σ hσ hσd => (hjunc σ hσ (le_of_lt hσd)).1.symm)
  -- the same for the left-hand piece
  have hXc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.lowSlopeCurveX r X) (Set.Ioi 0) :=
    contDiffOn_ite_glue (F := X) (G := fun σ : ℝ => r (Real.arctan σ) * Real.cos (Real.arctan σ))
      (c := 3 / 4) (d := 4 / 5) (by norm_num) (by norm_num)
      (contDiffOn_radial_branch r hrc) hXY.smooth_x
      (fun σ hσ hσd => (hjunc σ hσ (le_of_lt hσd)).2.symm)
  -- the right limit at `0⁺`, with positivity from the `ε`-bound at `α = 0`
  have hYlim : ∃ b : ℝ, 0 < b ∧ Tendsto (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)
      (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    have hG : ContinuousWithinAt (fun σ : ℝ => R (Real.arctan σ) * Real.cos (Real.arctan σ))
        (Set.Ioi 0) 0 := continuousWithinAt_radial_branch R hRc
    have htend : Tendsto
        (fun σ : ℝ => if σ < 3 / 4 then R (Real.arctan σ) * Real.cos (Real.arctan σ) else Y σ)
        (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) :=
      tendsto_ite_nhds_zero (F := Y) (c := 3 / 4) (b := R 0) (by norm_num) hG
        (by simp [Real.arctan_zero])
    have hb : 0 < R 0 := by
      have h := hR0 0 (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from ⟨le_refl _, by positivity⟩)
      rw [abs_le] at h
      linarith [h.1]
    exact ⟨R 0, hb, htend⟩
  -- the left limit at `0⁺`
  have hXlim : ∃ a : ℝ, 0 < a ∧ Tendsto (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hG : ContinuousWithinAt (fun σ : ℝ => r (Real.arctan σ) * Real.cos (Real.arctan σ))
        (Set.Ioi 0) 0 := continuousWithinAt_radial_branch r hrc
    have htend : Tendsto
        (fun σ : ℝ => if σ < 3 / 4 then r (Real.arctan σ) * Real.cos (Real.arctan σ) else X σ)
        (𝓝[>] (0 : ℝ)) (𝓝 (r 0)) :=
      tendsto_ite_nhds_zero (F := X) (c := 3 / 4) (b := r 0) (by norm_num) hG
        (by simp [Real.arctan_zero])
    have ha : 0 < r 0 := by
      have h := hr0 0 (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from ⟨le_refl _, by positivity⟩)
      rw [abs_le] at h
      linarith [h.1]
    exact ⟨r 0, ha, htend⟩
  refine ⟨hYc, hXc, hYlim, hXlim, ?_, ?_⟩
  · -- beyond the window the curve is the anchor's, hence the semicircle's chord function
    intro s hs
    have h34 : (3 : ℝ) / 4 ≤ s := le_trans (by norm_num [Work.OddEnvelope.tau]) hs
    rw [Work.OddCurve.LowSlope.lowSlopeCurveY_of_ge h34]
    exact hXY.y_tail s hs
  · intro s hs
    have h34 : (3 : ℝ) / 4 ≤ s := le_trans (by norm_num [Work.OddEnvelope.tau]) hs
    rw [Work.OddCurve.LowSlope.lowSlopeCurveX_of_ge h34]
    exact hXY.x_tail s hs

end

end Work.OddCurve.Free
