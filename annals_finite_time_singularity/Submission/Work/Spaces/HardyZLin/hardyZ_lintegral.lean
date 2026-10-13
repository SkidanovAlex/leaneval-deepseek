import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces.HardyZLin

open MeasureTheory

/-- **The radial Hardy inequality of `HardyZ` in `ℝ≥0∞` form.**  The real-valued `HardyZ`
needs the hypothesis `IntegrableOn (fun s => (Dz g s θ)^2 * (w s)^2) Iz` for the *fixed* angle
`θ`, and that hypothesis is NOT available when `g` is only known to satisfy a *θ-integrated*
weighted `L²` bound (as in `HkMem`): the radial Hardy inequality must be applied θ-slice by
θ-slice without any per-slice integrability.  This ENNReal version needs no integrability at
all, and it is the form in which the Hardy inequality can be integrated over `θ`.

Route: split on whether `P := ∫⁻_s in Iz, ofReal ((Dz g s θ)^2 * (w s)^2)` is finite.  If
`P = ∞` the claim is trivial.  If `P < ∞`, then `(Dz g · θ)^2 w^2` is integrable on `Iz`
(measurability from `Work.Spaces.hardyZ_continuousOn_pz_slice`), so `HardyZ` applies directly
and `ofReal_toReal` identifies `P` with `ofReal` of the real integral.  This also covers
`z = 0` (continuity of the slice, as in `HardyZ`).  An alternative route that avoids the
finiteness split: for `B ≥ z` use `Work.Spaces.hardyZ_integral_pz_eq_sub`,
`Work.Spaces.hardyZ_mul_w_mul_psi`, the real Cauchy–Schwarz
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` and
`Work.Spaces.hardyZ_integral_psi_sq_le_one` to get
`|g z θ - g B θ| ≤ sqrt (∫_s in z..B, (Dz g s θ)^2 (w s)^2) ≤ sqrt P`, then let `B → ∞`
using the decay hypothesis and conclude with `ENNReal.ofReal_toReal_le`. -/
theorem hardyZ_lintegral (g : ℝ → ℝ → ℝ) (θ : ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hθ : θ ∈ Work.Spaces.Iθ) (hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ENNReal.ofReal ((g z θ) ^ 2) ≤
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => ENNReal.ofReal ((Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)) := by
  -- Measurability of the integrand: `pz g · θ` is continuous on `(-1,∞) ⊇ Iz`, and the
  -- weight is measurable everywhere (its only singularity is at the null set `{0}`).
  have hsub : Iz ⊆ Set.Ioi (-1) := fun x hx => by
    simp only [Iz, Set.mem_Ici] at hx; simp only [Set.mem_Ioi]; linarith
  have hDzcont : ContinuousOn (fun s => Dz g s θ) Iz := by
    have hpz : ContinuousOn (fun s => pz g s θ) (Set.Ioi (-1)) :=
      hardyZ_continuousOn_pz_slice g hsm hθ
    unfold Dz
    exact continuousOn_id.mul (hpz.mono hsub)
  have hw : Measurable w := by unfold w; fun_prop
  have hmeas : AEStronglyMeasurable
      (fun s => (Dz g s θ) ^ 2 * (w s) ^ 2) (volume.restrict Iz) :=
    ((hDzcont.pow 2).aestronglyMeasurable measurableSet_Ici).mul
      ((hw.pow_const (2 : ℕ)).aestronglyMeasurable)
  have hnn : 0 ≤ᵐ[volume.restrict Iz] (fun s => (Dz g s θ) ^ 2 * (w s) ^ 2) :=
    Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases htop : ∫⁻ s in Iz, ENNReal.ofReal ((Dz g s θ) ^ 2 * (w s) ^ 2) = ⊤
  · rw [htop]; exact le_top
  · have hint : IntegrableOn (fun s => (Dz g s θ) ^ 2 * (w s) ^ 2) Iz :=
      (lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp htop
    have hH : (g z θ) ^ 2 ≤ ∫ s in Iz, (Dz g s θ) ^ 2 * (w s) ^ 2 :=
      HardyZ g θ hsm hθ hdec hint z hz
    calc ENNReal.ofReal ((g z θ) ^ 2)
        ≤ ENNReal.ofReal (∫ s in Iz, (Dz g s θ) ^ 2 * (w s) ^ 2) :=
          ENNReal.ofReal_le_ofReal hH
      _ = ∫⁻ s in Iz, ENNReal.ofReal ((Dz g s θ) ^ 2 * (w s) ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal hint hnn

end Work.Spaces.HardyZLin
