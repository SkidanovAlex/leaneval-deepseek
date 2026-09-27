import Mathlib
import Submission.Work.Drive.chordStrictWideDescent
import Submission.Work.Drive.exists_capAngle_periodic
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.bandData
import Submission.Work.Drive.capSide_capPiece
import Submission.Work.Drive.planePt
import Submission.Work.Drive.Neutral.stripTauData
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.planeWrapData
import Submission.Work.Drive.capLift_reflect
import Submission.Work.Drive.exists_capDatum_of_data
import Submission.Work.Drive.Neutral.stripDiskAntipodal
import Submission.Work.Drive.Neutral.stripDiskValueClause

namespace Work.Drive


/-- **The chart datum of the plane chart** (design `PLANE_CHART_LIFT_DESIGN.md` §5).

Produce, for a smooth Jordan curve avoiding the origin with `WrapData γ`:

* the descended chord data `M W : ℂ × ℝ → ℂ` and `c > 0` of
  `Work.Drive.chordStrictWideDescent` (value clauses on the unit circle for `τ ≥ 0`, the strict band
  `4|τ|‖W‖² < ‖M‖²` and `W ≠ 0` on `{1/4 ≤ ‖x‖ ≤ 2, -c ≤ τ < 0}`, and `M(·,0) ≠ 0`, `W(·,0) ≠ 0` on
  `{1/4 ≤ ‖x‖ ≤ 1}`), plus a band threshold `a` with `0 < a < 1/2`;
* a smooth positive radius `r` and a smooth nowhere-vanishing sphere lift `V` such that
  * on the annulus `1/2 < ‖z‖ ≤ 1` they are the honest chord data evaluated at
    `x z = wCollapse z`, `τ z = bandTau a z` (the **strip clause** interface), and
  * on the inner disk `‖z‖ < 1/2` the lift is in *cap form* `capProjVecOf w dc` with `w ≠ 0`,
    `‖dc‖ ≤ 1` (the **cap clause** interface, which by `Work.Drive.exists_capPiece_of_capForm'`
    puts the point in the cap solid torus).

Construction (design note §5; all inputs are in-tree and `sorry`-free; nothing here needs a lift, a
Whitney extension or degree theory):

* `chordStrictWideDescent` gives `M, W, c`; take `a` with `max (1/4) (1/2 - 2*c/π²) < a < 1/2`, so
  that `π²(1/2 - a)/2 ≤ c`;
* `X z := ‖wCollapse z‖ = profCut (1/4) (‖z‖²)` (radial, `= 1` iff `‖z‖ ≥ 1/2`), `τ z := bandTau a z`
  (`= π²/2 (‖z‖ - 1/2)` for `‖z‖ ≥ 1/2`, `= 0` for `‖z‖ ≤ a`, `|τ z| ≤ c` for `‖z‖ ≤ 1/2`);
* on `{X z ≥ 1/4}` (where `‖x z‖ ∈ [1/4, 1]`, `τ z ∈ [-c, 0]`, so all the descent clauses apply):
  `A z := ‖M (x z, τ z)‖² + τ z ‖W (x z, τ z)‖² > 0`, `D z := M (x z, τ z)/√(A z) ≠ 0`,
  `dc z := √2 (D z/‖D z‖) √(1 - ‖D z‖²/2)` with `1 ≤ ‖D z‖ < 2/√3`,
  `w z := (W (x z, τ z)/‖W (x z, τ z)‖) * conj (D z)/‖D z‖` (a smooth *unit* function);
* the anchor `a z := ε * exp (i * ϱ (‖z‖) * Θ (arg z))` from the `2π`-periodic `C^∞` cap angle `Θ` of
  `exists_capAngle_periodic` (`circleOf (Θ t) = symmE γ t 0 * (star (symmD γ t 0))^2`), with `ϱ`
  smooth, flat at `0`, `ϱ = 1/2` for `‖z‖ ≥ 1/4`, and `ε = ±1` the constant sign with
  `w z = ε * exp (i * Θ (arg z)/2)` on the seam circle `‖z‖ = 1/2` (its square follows from the value
  clauses + `Θ`'s defining property; the sign is constant because both sides are continuous on the
  connected circle);
* `w + a = 2w ≠ 0` **on the seam circle**, hence `w z + a z ≠ 0` on a neighbourhood of it; fix
  `X₀ > 1/4`, `X₁ ≤ 1` with the blend region `{X₀ ≤ X z ≤ X₁}` inside that neighbourhood, and put
  `λ z := 1 - pStep X₀ X₁ (X z)` (`1` for `X ≤ X₀`, `0` for `X ≥ X₁`, flat at both ends),
  `w̃ z := λ z * a z + (1 - λ z) * w z`, `dcb z := (1 - λ z) * dc z` (junk `0` for `X ≤ X₀`),
  `V z := capProjVecOf (w̃ z) (dcb z)`, `r z := λ z * 1 + (1 - λ z) * √(A z)`.

Clauses: `w̃ ≠ 0` (a cancellation would force `λ = 1/2` — both summands are unit — and `w = -a`,
excluded on the blend region); `‖dcb z‖ ≤ 1` (convex combination of `dc` and `0`); smoothness by
"flat bump `×` bounded"; on `1/2 < ‖z‖ ≤ 1` one has `λ = 0`, so `V z = capProjVecOf (w z) (dc z)`,
which equals `confProjVecOf (W/‖W‖) (M/√A)` by `capLift_reflect` — the required strip value. -/
theorem exists_planeChartDatum (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hW : Work.Drive.WrapData γ) :
    ∃ (M W : ℂ × ℝ → ℂ) (c a : ℝ) (r : ℂ → ℝ) (V : ℂ → Eucl 3),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧ 0 < c ∧ 0 < a ∧ a < 1 / 2 ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        M (x, τ) = Work.Drive.Neutral.dataMid γ x (Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        W (x, τ) = Work.Drive.Neutral.dchW γ (x, Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
        4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      (∀ z : ℂ, 0 < r z) ∧ (∀ z : ℂ, V z ≠ 0) ∧
      (∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
        r z = Real.sqrt (‖M (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2
              + Work.Drive.bandTau a z * ‖W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2) ∧
        V z = Work.Drive.confProjVecOf
          (W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)
            / ((‖W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ : ℝ) : ℂ))
          (M (Work.Drive.wCollapse z, Work.Drive.bandTau a z)
            / ((Real.sqrt (‖M (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2
                  + Work.Drive.bandTau a z
                    * ‖W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2) : ℝ) : ℂ))) ∧
      (∀ z : ℂ, ‖z‖ < 1 / 2 →
        ∃ w dc : ℂ, w ≠ 0 ∧ ‖dc‖ ≤ 1 ∧ V z = Work.Drive.capProjVecOf w dc) := by
  obtain ⟨M, W, c, hMsm, hWsm, hc, hMval, hWval, hband, hWne, hM0, hW0⟩ :=
    chordStrictWideDescent γ hγ hγne
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hlt : max (1 / 4) (1 / 2 - 2 * c / Real.pi ^ 2) < 1 / 2 := by
    refine max_lt (by norm_num) ?_
    have : 0 < 2 * c / Real.pi ^ 2 := by positivity
    linarith
  set a : ℝ := (max (1 / 4) (1 / 2 - 2 * c / Real.pi ^ 2) + 1 / 2) / 2 with ha
  have hag : max (1 / 4) (1 / 2 - 2 * c / Real.pi ^ 2) < a := by rw [ha]; linarith
  have ha2 : a < 1 / 2 := by rw [ha]; linarith
  have hpair := max_lt_iff.mp hag
  have hapos : 0 < a := lt_trans (by norm_num : (0:ℝ) < 1 / 4) hpair.1
  have ha_c : 1 / 2 - 2 * c / Real.pi ^ 2 < a := hpair.2
  have hτc : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → -c ≤ bandTau a z := by
    intro z hz
    rcases le_or_gt ‖z‖ a with h | h
    · have h1 : bandTau a z = 0 := bandProf_eq_zero ha2 h
      linarith [h1, hc]
    · have hX : Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2) ≤ 0 := by nlinarith
      have hp1 : pStep a (1 / 2) ‖z‖ ≤ 1 := pStep_le_one _ _ _
      have hmul : Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2)
          ≤ pStep a (1 / 2) ‖z‖ * (Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2)) := by
        have h1 : 0 ≤ 1 - pStep a (1 / 2) ‖z‖ := by linarith
        have h2 : 0 ≤ -(Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2)) := by linarith
        have := mul_nonneg h1 h2
        nlinarith [this]
      have h2 : -(2 * c / Real.pi ^ 2) < a - 1 / 2 := by linarith [ha_c]
      have h3 : Real.pi ^ 2 / 2 * (-(2 * c / Real.pi ^ 2)) < Real.pi ^ 2 / 2 * (a - 1 / 2) :=
        mul_lt_mul_of_pos_left h2 (by positivity)
      have h4 : Real.pi ^ 2 / 2 * (-(2 * c / Real.pi ^ 2)) = -c := by
        field_simp
      have hmono : Real.pi ^ 2 / 2 * (a - 1 / 2) ≤ Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hbd : bandTau a z
          = pStep a (1 / 2) ‖z‖ * (Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2)) := rfl
      linarith [h3, h4, hmul, hmono, hbd]
  obtain ⟨r, V, hrsm, hVsm, hrpos, hVne, hstrip, hcap⟩ :=
    exists_capDatum_of_data γ hU hW hγ hγne M W c a hMsm hWsm hc hapos ha2 hMval hWval hband
      hWne hM0 hW0 hτc
  exact ⟨M, W, c, a, r, V, hMsm, hWsm, hc, hapos, ha2, hMval, hWval, hband, hWne, hM0, hW0,
    hrsm, hVsm, hrpos, hVne, hstrip, hcap⟩

end Work.Drive
