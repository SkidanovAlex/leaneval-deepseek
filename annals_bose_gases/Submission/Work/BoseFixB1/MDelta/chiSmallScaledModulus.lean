import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseFixB1.MDelta.massUpper
import Submission.Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass
import Submission.Work.BoseFixB1S.wSmall1Pair_denom_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.MDelta.chiSmallScaledModulus` — the scaled `L²`-modulus of the cosine bump
`chiSmall`

The requested statement is the *scaled* `L²`-modulus of continuity of the small-box cutoff
`Submission.BoseGases.chiSmall M` at scale `c > 0`:

    ∫ x, (χ_M(c⁻¹•(x − w)) − χ_M(c⁻¹•(x − t − w)))²  ≤  C·c·‖t‖²      (0 < c).

**Route.**  `χ_M` is supported in the unit ball (`chiSmallBase_support_norm_le`) and is
`L`-Lipschitz (`Work.BoseFixB1S.chiSmall_lipschitz`).  Put `F x = χ_M(c⁻¹•(x−w))` and
`G x = χ_M(c⁻¹•(x−t−w))`; pointwise `c⁻¹•(x−t−w) = c⁻¹•(x−w) − c⁻¹•t`, so

* `(F x − G x)² ≤ (L·c⁻¹·‖t‖)²` for **every** `x` (Lipschitz, no support input);
* `F x ≠ 0` forces `‖x − w‖ ≤ c`, and `G x ≠ 0` forces `‖x − w − t‖ ≤ c` (support + scaling);

hence the integrand is pointwise dominated by `K = (L·c⁻¹‖t‖)²` times the indicator of the
**union of two balls of radius `c`**, whose volume is at most `2·c³·V` with
`V = volume (closedBall 0 1)` (`EuclideanSpace.volume_closedBall`, the `Γ(5/2)`-constant cancelling
against the same constant at radius `1`).  So

    ∫ (F−G)² ≤ K·2c³V = 2·V·L²·c·‖t‖²,

which is the claim with `C = 2·V·L²`.  Note that no case distinction in `‖t‖/c` is needed: the two
balls have volume `c³V` *each*, however far apart they are (for `‖t‖ ≫ c` the bound is simply
weak, while the sharp asymptotic `∫(F−G)² → 2c³` is still `≤ 2VL²c‖t‖²` for `‖t‖² ≥ 4c²/(L²V)`).
A dilation to the unit scale would give the same constant, the two routes being related by
`Measure.integral_comp_smul`.

This is the `hmod`-type input (`L²`-translate continuity) of the cutoff analysis, in the form the
`MΔ`-lane consumes it.
-/

namespace Work.BoseFixB1.MDelta

open MeasureTheory Metric

set_option maxHeartbeats 800000

/-- Volume of the unit ball of `ℝ³`, the normalisation constant of the modulus bound. -/
noncomputable def chiSmallUnitBallVol : ℝ :=
  (volume (Metric.closedBall (0 : ℝ³) 1)).toReal

lemma chiSmallUnitBallVol_nonneg : 0 ≤ chiSmallUnitBallVol := by
  rw [chiSmallUnitBallVol]
  exact ENNReal.toReal_nonneg

/-- **The volume of a ball in `ℝ³` in units of the unit ball**: `volume (closedBall w c) =
ofReal (c³·V)`, `V = chiSmallUnitBallVol`.  The two occurrences of the `Γ(3/2+1)`-constant of
`EuclideanSpace.volume_closedBall` (at radius `c` and at radius `1`) cancel, so no evaluation of
`Real.Gamma` is needed. -/
lemma volume_closedBall_eq_chiSmallUnitBallVol (w : ℝ³) {c : ℝ} (hc : 0 ≤ c) :
    volume (Metric.closedBall w c) = ENNReal.ofReal (c ^ 3 * chiSmallUnitBallVol) := by
  have h0 : volume (Metric.closedBall (0 : ℝ³) 1) = ENNReal.ofReal chiSmallUnitBallVol := by
    rw [chiSmallUnitBallVol, ENNReal.ofReal_toReal]
    exact (isCompact_closedBall (0 : ℝ³) 1).measure_lt_top.ne
  have hvol : volume (Metric.closedBall w c)
      = ENNReal.ofReal c ^ 3 * volume (Metric.closedBall (0 : ℝ³) 1) := by
    rw [EuclideanSpace.volume_closedBall (Fin 3) w c,
      EuclideanSpace.volume_closedBall (Fin 3) (0 : ℝ³) 1]
    simp
  rw [hvol, h0, ← ENNReal.ofReal_pow hc 3, ← ENNReal.ofReal_mul (pow_nonneg hc 3)]

/-- **The scaled `L²`-modulus bound** for a bump of Lipschitz constant `L` supported in the unit
ball: `∫ x, (χ(c⁻¹•(x−w)) − χ(c⁻¹•(x−t−w)))² ≤ 2·V·L²·c·‖t‖²`. -/
lemma chiSmall_scaled_diff_sq_le {M : ℕ} (hM : 1 ≤ M) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ y z : ℝ³, |Submission.BoseGases.chiSmall M y
        - Submission.BoseGases.chiSmall M (y - z)| ≤ L * ‖z‖)
    {c : ℝ} (hc : 0 < c) (w t : ℝ³) :
    ∫ x : ℝ³, (Submission.BoseGases.chiSmall M (c⁻¹ • (x - w))
        - Submission.BoseGases.chiSmall M (c⁻¹ • (x - t - w))) ^ 2
      ≤ 2 * chiSmallUnitBallVol * L ^ 2 * c * ‖t‖ ^ 2 := by
  set F : ℝ³ → ℝ := fun x => Submission.BoseGases.chiSmall M (c⁻¹ • (x - w)) with hF
  set G : ℝ³ → ℝ := fun x => Submission.BoseGases.chiSmall M (c⁻¹ • (x - t - w)) with hG
  set B : Set ℝ³ := Metric.closedBall w c ∪ Metric.closedBall (w + t) c with hB
  set K : ℝ := (L * c⁻¹ * ‖t‖) ^ 2 with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hcnn : 0 ≤ c ^ 3 * chiSmallUnitBallVol :=
    mul_nonneg (pow_nonneg (le_of_lt hc) 3) chiSmallUnitBallVol_nonneg
  have htwo : 0 ≤ 2 * (c ^ 3 * chiSmallUnitBallVol) := by linarith
  -- pointwise rewriting of `G` into `χ(c⁻¹•(x−w) − c⁻¹•t)`
  have hG_eq : ∀ x : ℝ³, G x
      = Submission.BoseGases.chiSmall M (c⁻¹ • (x - w) - c⁻¹ • t) := by
    intro x
    show Submission.BoseGases.chiSmall M (c⁻¹ • (x - t - w))
        = Submission.BoseGases.chiSmall M (c⁻¹ • (x - w) - c⁻¹ • t)
    congr 1
    rw [← smul_sub]
    congr 1
    abel
  -- the pointwise Lipschitz bound
  have hpt : ∀ x : ℝ³, (F x - G x) ^ 2 ≤ K := by
    intro x
    have hmain : |F x - G x| ≤ L * (c⁻¹ * ‖t‖) := by
      rw [hG_eq x, hF]
      have h := hLip (c⁻¹ • (x - w)) (c⁻¹ • t)
      have hn : ‖c⁻¹ • t‖ = c⁻¹ * ‖t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      rwa [hn] at h
    rw [hK]
    refine sq_le_sq.mpr ?_
    have habs : |L * c⁻¹ * ‖t‖| = L * (c⁻¹ * ‖t‖) := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hL (le_of_lt (inv_pos.mpr hc)))
        (norm_nonneg t))]
      ring
    rw [habs]
    exact hmain
  -- the support of the first factor lies in the ball of radius `c` about `w`
  have hFsupp : ∀ x : ℝ³, F x ≠ 0 → x ∈ Metric.closedBall w c := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hb : Submission.BoseGases.chiSmallBase M (c⁻¹ • (x - w)) ≠ 0 := by
      intro h0
      exact hx (by rw [hF]; simp [Submission.BoseGases.chiSmall, h0])
    have h1 := Submission.BoseGases.chiSmallBase_support_norm_le hM hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)] at h1
    have h2 : c * (c⁻¹ * ‖x - w‖) ≤ c * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
    have h3 : c * (c⁻¹ * ‖x - w‖) = ‖x - w‖ := by field_simp
    linarith
  -- and the support of the second in the ball of radius `c` about `w + t`
  have hGsupp : ∀ x : ℝ³, G x ≠ 0 → x ∈ Metric.closedBall (w + t) c := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hb : Submission.BoseGases.chiSmallBase M (c⁻¹ • (x - t - w)) ≠ 0 := by
      intro h0
      exact hx (by rw [hG]; simp [Submission.BoseGases.chiSmall, h0])
    have h1 := Submission.BoseGases.chiSmallBase_support_norm_le hM hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)] at h1
    have h2 : c * (c⁻¹ * ‖x - t - w‖) ≤ c * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
    have h3 : c * (c⁻¹ * ‖x - t - w‖) = ‖x - t - w‖ := by field_simp
    have h4 : x - (w + t) = x - t - w := by abel
    rw [h4]
    linarith
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact measurableSet_closedBall.union measurableSet_closedBall
  -- the volume of the union of the two balls
  have hBvol : (volume B).toReal ≤ 2 * (c ^ 3 * chiSmallUnitBallVol) := by
    have hle : volume B ≤ ENNReal.ofReal (2 * (c ^ 3 * chiSmallUnitBallVol)) := by
      rw [hB]
      calc volume (Metric.closedBall w c ∪ Metric.closedBall (w + t) c)
          ≤ volume (Metric.closedBall w c) + volume (Metric.closedBall (w + t) c) :=
            MeasureTheory.measure_union_le _ _
        _ = ENNReal.ofReal (c ^ 3 * chiSmallUnitBallVol)
              + ENNReal.ofReal (c ^ 3 * chiSmallUnitBallVol) := by
              rw [volume_closedBall_eq_chiSmallUnitBallVol w (le_of_lt hc),
                volume_closedBall_eq_chiSmallUnitBallVol (w + t) (le_of_lt hc)]
        _ = ENNReal.ofReal (2 * (c ^ 3 * chiSmallUnitBallVol)) := by
              rw [← ENNReal.ofReal_add hcnn hcnn]
              ring_nf
    calc (volume B).toReal ≤ (ENNReal.ofReal (2 * (c ^ 3 * chiSmallUnitBallVol))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 2 * (c ^ 3 * chiSmallUnitBallVol) := ENNReal.toReal_ofReal htwo
  -- the integrand is dominated by the indicator of `B`, times `K`
  have hpoint : ∀ x : ℝ³, (F x - G x) ^ 2 ≤ B.indicator (fun _ => K) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]; exact hpt x
    · rw [Set.indicator_of_notMem hx]
      have hF0 : F x = 0 := by
        by_contra hne
        exact hx (by rw [hB]; exact Or.inl (hFsupp x hne))
      have hG0 : G x = 0 := by
        by_contra hne
        exact hx (by rw [hB]; exact Or.inr (hGsupp x hne))
      rw [hF0, hG0]
      norm_num
  have hInt : Integrable (B.indicator (fun _ => K)) volume := by
    rw [MeasureTheory.integrable_indicator_iff hBmeas]
    exact MeasureTheory.integrableOn_const (C := K)
      (by exact (isCompact_closedBall w c |>.union (isCompact_closedBall (w + t) c)
        |>.measure_lt_top).ne) (by simp)
  have key : ∫ x : ℝ³, (F x - G x) ^ 2 ≤ 2 * chiSmallUnitBallVol * L ^ 2 * c * ‖t‖ ^ 2 := by
    calc ∫ x : ℝ³, (F x - G x) ^ 2 ≤ ∫ x : ℝ³, B.indicator (fun _ => K) x :=
          integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) hInt (ae_of_all _ hpoint)
      _ = (volume B).toReal * K := by
          rw [MeasureTheory.integral_indicator_const K hBmeas, MeasureTheory.measureReal_def]
          simp
      _ ≤ (2 * (c ^ 3 * chiSmallUnitBallVol)) * K := mul_le_mul_of_nonneg_right hBvol hKnn
      _ = 2 * chiSmallUnitBallVol * L ^ 2 * c * ‖t‖ ^ 2 := by
          rw [hK]
          field_simp
  simpa only [hF, hG] using key

theorem chiSmallScaledModulus {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (w t : EuclideanSpace ℝ (Fin 3)), 0 < c →
      ∫ x : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiSmall M (c⁻¹ • (x - w))
              - Submission.BoseGases.chiSmall M (c⁻¹ • (x - t - w))) ^ 2
        ≤ C * c * ‖t‖ ^ 2 := by
  obtain ⟨L, hL0, hLip⟩ := Work.BoseFixB1S.chiSmall_lipschitz hM
  refine ⟨2 * chiSmallUnitBallVol * L ^ 2, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) chiSmallUnitBallVol_nonneg) (sq_nonneg L)
  · intro c w t hc
    exact chiSmall_scaled_diff_sq_le hM hL0 hLip hc w t

end Work.BoseFixB1.MDelta
