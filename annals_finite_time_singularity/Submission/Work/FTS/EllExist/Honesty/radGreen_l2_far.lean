import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.radGreen_l2_near_zero
import Submission.Work.FTS.EllExist.Honesty.G1_far_bound
import Submission.Work.FTS.EllExist.Honesty.G1_far_measurable
import Submission.Work.FTS.EllExist.Honesty.G2_far_bound
import Submission.Work.FTS.EllExist.Honesty.G2_far_measurable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- On `[1, ∞)` the weight `w z = (1+z)^2 / z^2` of `Work.Spaces.w` satisfies
`w z ^ 2 ≤ 16` (indeed `w z ≤ (1 + 1/z)^2 ≤ 4`). -/
lemma w_sq_le_sixteen_of_one_le {z : ℝ} (hz : 1 ≤ z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have hz0 : 0 < z := by linarith
  have hw0 : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  have hw4 : Work.Spaces.w z ≤ 4 := by
    rw [Work.Spaces.w, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (show 1 - z ≤ 0 by linarith)
      (show 0 ≤ 1 + 3 * z by linarith)]
  have h := pow_le_pow_left₀ hw0 hw4 2
  norm_num at h
  exact h

/-- `(x * z ^ P) ^ 2 = x ^ 2 * z ^ (2 * P)` for `z > 0`. -/
lemma mul_rpow_sq {z x P : ℝ} (hz : 0 < z) : (x * z ^ P) ^ 2 = x ^ 2 * z ^ (2 * P) := by
  rw [mul_pow, pow_two (z ^ P), ← Real.rpow_add hz]
  rw [show P + P = 2 * P by ring]

-- The **far-field** half of the weighted `L²`-honesty of the mode-`m` Green function
-- `Work.FTS.PhiStar.Radial.radGreen α m c` (decaying solution of the mode-`m` radial Euler
-- equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, λ_m = 2m(2m+5)).  Companion of
-- `FTS/EllExist/Honesty/radGreen_l2_near_zero` (the `z → 0` half); together they give the full
-- `∫_{Iz} (radGreen α m c)² w² < ∞` that discharges the one-dimensional hypotheses `hza` of
-- `psiTrunc_hkMem_fts`/`psiTrunc_hkMem_third_slot`.
--
-- ROUTE (`s⁻ = -(2m+5)/α ≤ -20`, `s⁺ = 2m/α ≥ 8`, `K = 1/(α(4m+5))`; `w z = (1+z)²/z²`, so
-- `w(z)² = (1+1/z)⁴ ≤ 16` for `z ≥ 1`).  Write `radGreen = K(G₁ + G₂)` with
-- `G₁(z) = z^{s⁻}∫_0^zc t^{-1-s⁻}dt`, `G₂(z) = z^{s⁺}∫_z^∞c t^{-1-s⁺}dt`.
-- * `G₂`: `|G₂(z)| ≤ z^{s⁺}·M∫_z^∞t^{-s⁺-2}t^{-1-s⁺}dt = M z^{-s⁺-2}/(2s⁺+2)`, so
--   `G₂(z)² ≤ C z^{-2s⁺-4}` with `2s⁺+4 ≥ 20`.
-- * `G₁`: for `z ≥ 1` split `∫_0^z = ∫_0^1 + ∫_1^z` (`integral_add_adjacent_intervals`); on
--   `(1,z)` use `|c t| ≤ M t^{-s⁺-2}` and `-1-s⁻ = (2m+5)/α - 1` to get
--   `|∫_1^zc t^{-1-s⁻}dt| ≤ M∫_1^z t^{-s⁺-s⁻-3}dt ≤ M/(s⁺+s⁻+2)` (bounded); the `∫_0^1` piece is
--   bounded when `t ↦ c t·t^{-1-s⁻}` is interval-integrable on `[0,1]` (continuity gives it when
--   `c` is bounded there; otherwise Lean's `integral` is the junk value `0`, so one must case-split
--   on `IntervalIntegrable`).  So `|G₁(z)| ≤ C z^{s⁻}` **up to** the extra decaying contribution
--   `M z^{-s⁺-2}/(s⁺+s⁻+2)` of the `(1,z)` piece; both `z^{2s⁻}` (`≤ z^{-56}`) and `z^{-2s⁺-4}`
--   are integrable against `w² ≤ 16` on `(1,∞)`.  Use `(G₁+G₂)² ≤ 2G₁² + 2G₂²`.-
--
-- PROOF.  The four far-field ingredients are separate lemmas in this directory:
-- * `Work.FTS.EllExist.Honesty.G1_far_bound`, `G1_far_measurable` — the `z^{s⁻}` term,
--   `|G1 α m c z| ≤ A z^{s⁻} + B z^{-s⁺-2}` on `Ioi 1` with `A, B ≥ 0` (case-split on whether
--   `t ↦ c t t^{s⁻-1}` is integrable on `(0,1]`; when it is not, `G1` vanishes on `Ioi 1` by
--   `intervalIntegral.integral_undef`), and measurability of `G1` on `Ioi 1`;
-- * `Work.FTS.EllExist.Honesty.G2_far_bound`, `G2_far_measurable` — the `z^{s⁺}` term,
--   `|G2 α m c z| ≤ (M/(2s⁺+2)) z^{-s⁺-2}` on `Ioi 1`, and measurability of `G2` on `Ioi 1`.
-- Assembly (`radGreen_l2_far_assembly` below): `|radGreen|² w² = K² (G₁+G₂)² w²`, the pointwise
-- bound `|G₁+G₂| ≤ A z^{s⁻} + (B + M/(2s⁺+2)) z^{-s⁺-2}` gives
-- `(G₁+G₂)² ≤ 2(A² + (B + M/(2s⁺+2))²) z^{-2s⁺-4}` since `2s⁻ ≤ -2s⁺-4` (i.e. `s⁺ - s⁻ = 5/α ≥ 2`),
-- and `w² ≤ 16`; so `radGreen² w²` is dominated by a constant multiple of the integrable
-- `z^{-2s⁺-4}` (`2s⁺+4 ≥ 20 > 1`).  Measurability of `radGreen² w²` follows from that of `G₁`, `G₂`
-- and continuity of `w`.  Then `Integrable.mono'` finishes.
/-- Assembly of `radGreen_l2_far` from the four far-field ingredients. -/
theorem radGreen_l2_far_assembly (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ)
    {c : ℝ → ℝ} (M : ℝ) (hM : 0 ≤ M) (hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2))
    (hG2b : ∀ z ∈ Set.Ioi 1, |G2 α m c z| ≤ M / (2 * (2 * (m : ℝ) / α) + 2)
        * z ^ (-(2 * (m : ℝ) / α) - 2))
    (hG2m : AEStronglyMeasurable (fun z => G2 α m c z) (volume.restrict (Set.Ioi 1)))
    (hG1b : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ Set.Ioi 1,
        |G1 α m c z| ≤ A * z ^ (-((2 * (m : ℝ) + 5) / α))
          + B * z ^ (-(2 * (m : ℝ) / α) - 2))
    (hG1m : AEStronglyMeasurable (fun z => G1 α m c z) (volume.restrict (Set.Ioi 1))) :
    IntegrableOn (fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
      * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
  obtain ⟨A, B, hA0, hB0, hG1b'⟩ := hG1b
  have hB2nn : 0 ≤ M / (2 * (2 * (m : ℝ) / α) + 2) := div_nonneg hM (by positivity)
  have hq : -(2 * (2 * (m : ℝ) / α)) - 4 < -1 := by
    have : 0 ≤ 2 * (m : ℝ) / α := div_nonneg (by positivity) hα.le
    linarith
  have h2p : 2 * (-((2 * (m : ℝ) + 5) / α)) ≤ -(2 * (2 * (m : ℝ) / α)) - 4 := by
    have h5 : (2 : ℝ) ≤ 5 / α := by rw [le_div_iff₀ hα]; linarith
    have h10 : (4 : ℝ) ≤ 2 * (5 / α) := by linarith
    have hexp : (2 * (m : ℝ) + 5) / α = 2 * (m : ℝ) / α + 5 / α := add_div _ _ _
    rw [hexp]
    nlinarith [h10]
  -- the pointwise domination by a multiple of `z ^ (-2 s⁺ - 4)`
  have hmain : ∀ z ∈ Set.Ioi 1,
      ‖Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 * (Work.Spaces.w z) ^ 2‖
        ≤ ((1 / (α * (4 * (m : ℝ) + 5))) ^ 2 * 2
            * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2) * 16)
          * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) := by
    intro z hz
    have hz1 : 1 ≤ z := le_of_lt hz
    have hz0 : 0 < z := by linarith
    have hw16 : (Work.Spaces.w z) ^ 2 ≤ 16 := w_sq_le_sixteen_of_one_le hz1
    have hznn : 0 ≤ z ^ (-(2 * (m : ℝ) / α) - 2) := Real.rpow_nonneg hz0.le _
    have htri : |G1 α m c z + G2 α m c z| ≤ A * z ^ (-((2 * (m : ℝ) + 5) / α))
        + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) * z ^ (-(2 * (m : ℝ) / α) - 2) := by
      have h1 := hG1b' z hz
      have h2 := hG2b z hz
      have h3 : A * z ^ (-((2 * (m : ℝ) + 5) / α)) + B * z ^ (-(2 * (m : ℝ) / α) - 2)
          + M / (2 * (2 * (m : ℝ) / α) + 2) * z ^ (-(2 * (m : ℝ) / α) - 2)
          = A * z ^ (-((2 * (m : ℝ) + 5) / α))
            + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) * z ^ (-(2 * (m : ℝ) / α) - 2) := by
        ring
      have h4 := abs_add_le (G1 α m c z) (G2 α m c z)
      linarith
    have hsq1 : |G1 α m c z + G2 α m c z| ^ 2
        ≤ 2 * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2)
            * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) := by
      have hx0 : 0 ≤ A * z ^ (-((2 * (m : ℝ) + 5) / α)) :=
        mul_nonneg hA0 (Real.rpow_nonneg hz0.le _)
      have hy0 : 0 ≤ (B + M / (2 * (2 * (m : ℝ) / α) + 2))
          * z ^ (-(2 * (m : ℝ) / α) - 2) := mul_nonneg (add_nonneg hB0 hB2nn) hznn
      have hs : |G1 α m c z + G2 α m c z| ^ 2
          ≤ (A * z ^ (-((2 * (m : ℝ) + 5) / α))
              + (B + M / (2 * (2 * (m : ℝ) / α) + 2))
                * z ^ (-(2 * (m : ℝ) / α) - 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) htri 2
      have hxy : (A * z ^ (-((2 * (m : ℝ) + 5) / α))
              + (B + M / (2 * (2 * (m : ℝ) / α) + 2))
                * z ^ (-(2 * (m : ℝ) / α) - 2)) ^ 2
          ≤ 2 * (A * z ^ (-((2 * (m : ℝ) + 5) / α))) ^ 2
            + 2 * ((B + M / (2 * (2 * (m : ℝ) / α) + 2))
                * z ^ (-(2 * (m : ℝ) / α) - 2)) ^ 2 := by
        nlinarith [sq_nonneg (A * z ^ (-((2 * (m : ℝ) + 5) / α))
          - (B + M / (2 * (2 * (m : ℝ) / α) + 2)) * z ^ (-(2 * (m : ℝ) / α) - 2))]
      have hx2 : (A * z ^ (-((2 * (m : ℝ) + 5) / α))) ^ 2
          = A ^ 2 * z ^ (2 * (-((2 * (m : ℝ) + 5) / α))) := mul_rpow_sq hz0
      have hy2 : ((B + M / (2 * (2 * (m : ℝ) / α) + 2))
              * z ^ (-(2 * (m : ℝ) / α) - 2)) ^ 2
          = (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2
            * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) := by
        rw [mul_rpow_sq hz0,
          show 2 * (-(2 * (m : ℝ) / α) - 2) = -(2 * (2 * (m : ℝ) / α)) - 4 from by ring]
      have hle2 : A ^ 2 * z ^ (2 * (-((2 * (m : ℝ) + 5) / α)))
          ≤ A ^ 2 * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 h2p) (sq_nonneg A)
      calc |G1 α m c z + G2 α m c z| ^ 2
          ≤ (A * z ^ (-((2 * (m : ℝ) + 5) / α))
              + (B + M / (2 * (2 * (m : ℝ) / α) + 2))
                * z ^ (-(2 * (m : ℝ) / α) - 2)) ^ 2 := hs
        _ ≤ 2 * (A * z ^ (-((2 * (m : ℝ) + 5) / α))) ^ 2
            + 2 * ((B + M / (2 * (2 * (m : ℝ) / α) + 2))
                * z ^ (-(2 * (m : ℝ) / α) - 2)) ^ 2 := hxy
        _ = 2 * (A ^ 2 * z ^ (2 * (-((2 * (m : ℝ) + 5) / α))))
            + 2 * ((B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2
                * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4)) := by rw [hx2, hy2]
        _ ≤ 2 * (A ^ 2 * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4))
            + 2 * ((B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2
                * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4)) := by linarith
        _ = 2 * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2)
              * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) := by ring
    have hnn : 0 ≤ Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hkey : Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 * (Work.Spaces.w z) ^ 2
        = (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 * (G1 α m c z + G2 α m c z) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      rw [radGreen_eq_G1_add_G2]; ring
    rw [hkey]
    have hK2 : 0 ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 := sq_nonneg _
    have hsq2 : (G1 α m c z + G2 α m c z) ^ 2
        ≤ 2 * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2)
            * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) := by
      simpa using hsq1
    have hYZ : 0 ≤ 2 * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2)
        * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) :=
      mul_nonneg (by nlinarith [sq_nonneg A, sq_nonneg (B + M / (2 * (2 * (m : ℝ) / α) + 2))])
        (Real.rpow_nonneg hz0.le _)
    calc (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 * (G1 α m c z + G2 α m c z) ^ 2
            * (Work.Spaces.w z) ^ 2
        ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * (2 * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2)
                * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4)) * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq2 hK2) (sq_nonneg _)
      _ ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * (2 * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2)
                * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4)) * 16 :=
          mul_le_mul_of_nonneg_left hw16 (mul_nonneg hK2 hYZ)
      _ = ((1 / (α * (4 * (m : ℝ) + 5))) ^ 2 * 2
            * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2) * 16)
            * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4) := by ring
  -- measurability of `radGreen ^ 2 * w ^ 2` on `Ioi 1`
  have hwmeas : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro z hz
      have hz1 : (1 : ℝ) < z := Set.mem_Ioi.mp hz
      exact pow_ne_zero 2 (ne_of_gt (by linarith : (0 : ℝ) < z))
  have hRGmeas : AEStronglyMeasurable (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (volume.restrict (Set.Ioi 1)) := by
    have hsum : AEStronglyMeasurable (fun z => G1 α m c z + G2 α m c z)
        (volume.restrict (Set.Ioi 1)) := hG1m.add hG2m
    have hc1 := hsum.const_mul (1 / (α * (4 * (m : ℝ) + 5)))
    refine hc1.congr ?_
    filter_upwards with z
    rw [radGreen_eq_G1_add_G2]
  have hAE : AEStronglyMeasurable (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2
      * (Work.Spaces.w z) ^ 2) (volume.restrict (Set.Ioi 1)) :=
    (hRGmeas.pow 2).mul hwmeas
  -- the dominating function is integrable
  have hD : Integrable (fun z : ℝ => ((1 / (α * (4 * (m : ℝ) + 5))) ^ 2 * 2
        * (A ^ 2 + (B + M / (2 * (2 * (m : ℝ) / α) + 2)) ^ 2) * 16)
      * z ^ (-(2 * (2 * (m : ℝ) / α)) - 4)) (volume.restrict (Set.Ioi 1)) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt hq one_pos) _
  refine Integrable.mono' hD hAE ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ fun z hz => hmain z hz

theorem radGreen_l2_far (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (M : ℝ) (hM : 0 ≤ M) (hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2)) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
  refine radGreen_l2_far_assembly α hα hα4 m M hM hc hdec ?_ ?_ ?_ ?_
  · exact G2_far_bound α hα m M hM hc hdec
  · exact G2_far_measurable α hα m M hc hdec
  · exact G1_far_bound α hα hα4 m M hM hc hdec
  · exact G1_far_measurable α hα m hc

end Work.FTS.EllExist.Honesty
