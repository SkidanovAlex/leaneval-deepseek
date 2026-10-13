import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.Series.Deleg.hasDerivAt_pairGreen
import Submission.Work.FTS.PhiStar.Series.Deleg.rgiClearing
import Submission.Work.FTS.PhiStar.Series.Deleg.rgiIndicial
import Submission.Work.FTS.PhiStar.Series.Deleg.eulerCombination

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false

open Work.FTS.PhiStar.Series (rgiK rgiSn rgiSp rgiF1 rgiF2 rgiA rgiB rgiD1 rgiA_hasDerivAt
  rgiB_hasDerivAt hasDerivAt_radGreenI radGreenI_eq_rgi)

/-!
# `radGreenSolvesNoH0` — the mode-`m` radial Green's function solves the Euler equation

`Work.FTS.PhiStar.Radial.radGreen α m c` is the explicit decaying solution of the mode-`m`
radial Euler equation

  `-α² z² a'' - α(5+α) z a' + λ_m a = c`,      `λ_m = lamR m = 2m(2m+5)`,

written as a Green's function with the two indicial exponents `s⁻ = -(2m+5)/α` (decaying at
`∞`) and `s⁺ = 2m/α`, normalisation `K = 1/(α(4m+5))`.

The sibling `Work.FTS.PhiStar.Radial.radGreen_solves` proves this identity under the *extra*
hypothesis that `t ↦ c t · t^{-1-s⁺}` is integrable on `(0,1)`.  That hypothesis is **not
needed** for the pointwise identity: the tail integral `∫_z^∞` only ever needs local
integrability of `c t t^{-1-s⁺}` near `z`, which continuity of `c` on the compact interval
`[z/2, 1]` supplies (together with the global integrability on `(1,∞)` — precisely what the
public lemmas `Work.FTS.PhiStar.Series.rgiB_hasDerivAt` / `rgiA_hasDerivAt` use).

The computation is the standard one: with `A z = ∫_0^z c t t^{-1-s⁻} dt` and
`B z = ∫_z^∞ c t t^{-1-s⁺} dt`, the `c`-terms of `a'` cancel
(`z^{s⁻} · c z · z^{-1-s⁻} = c z / z = z^{s⁺} · c z · z^{-1-s⁺}`), and the indicial relations
`-α²s(s-1) - α(5+α)s + λ_m = 0` for `s = s⁻, s⁺` together with `α²K(s⁺-s⁻) = 1` leave `c z`.
-/

/-- **The second derivative of `radGreenI`.**  The explicit formula for
`deriv (deriv (radGreenI α m c)) z`: the `y`-differentiated version of
`Work.FTS.PhiStar.Series.rgiD1`. -/
def rgiD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m * (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
            + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
          + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))

/-- `rgiD1` is differentiable on `(0,∞)`, with the explicit second derivative `rgiD2`. -/
theorem hasDerivAt_rgiD1 {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiD1 α m c) (rgiD2 α m c z) z := by
  intro z hz
  have hA := rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz
  have hB := rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz
  have h := hasDerivAt_pairGreen (K := rgiK α m) (sn := rgiSn α m) (sp := rgiSp α m)
    (A := rgiA α m c) (B := rgiB α m c) (F1 := rgiF1 α m c) (F2 := rgiF2 α m c)
    hA hB (ne_of_gt hz)
  exact h.congr_deriv (by simp only [rgiD2])

/-- The six clearing identities at `z > 0`: the four elementary `rpow` identities for the two
indicial exponents and the two `c`-clearing identities `z² z^{s-1} · (c z z^{-1-s}) = c z`. -/
theorem rpow_clear {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    z * z ^ (rgiSn α m - 1) = z ^ (rgiSn α m) ∧
    z ^ 2 * z ^ (rgiSn α m - 2) = z ^ (rgiSn α m) ∧
    z * z ^ (rgiSp α m - 1) = z ^ (rgiSp α m) ∧
    z ^ 2 * z ^ (rgiSp α m - 2) = z ^ (rgiSp α m) ∧
    z ^ 2 * z ^ (rgiSn α m - 1) * rgiF1 α m c z = c z ∧
    z ^ 2 * z ^ (rgiSp α m - 1) * rgiF2 α m c z = c z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rgiClearing α m c
  exact ⟨h1 z hz, h2 z hz, h3 z hz, h4 z hz, h5 z hz, h6 z hz⟩

theorem radGreenSolvesNoH0 (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
        - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
        = c z := by
  have hmain : ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z
        - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) z
        + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreenI α m c z
        = c z := by
    intro z hz
    have hGreen1 : ∀ y ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (Work.FTS.PhiStar.Radial.radGreenI α m c) (rgiD1 α m c y) y :=
      fun y hy => hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf y hy
    have hD2 : HasDerivAt (rgiD1 α m c) (rgiD2 α m c z) z :=
      hasDerivAt_rgiD1 m hc h0 hinf z hz
    have hderivEq : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c :=
      eventually_of_mem (Ioi_mem_nhds hz) (fun y hy => (hGreen1 y hy).deriv)
    have hdd : deriv (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z = rgiD2 α m c z := by
      rw [hderivEq.deriv_eq, hD2.deriv]
    have hd1z : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) z = rgiD1 α m c z :=
      (hGreen1 z hz).deriv
    have hgz : Work.FTS.PhiStar.Radial.radGreenI α m c z
        = rgiK α m * (z ^ rgiSn α m * rgiA α m c z + z ^ rgiSp α m * rgiB α m c z) :=
      congrFun (radGreenI_eq_rgi α m c) z
    rw [hdd, hd1z, hgz]
    obtain ⟨hzs1, hzs2, hzp1, hzp2, hc1, hc2⟩ := rpow_clear (α := α) (m := m) (c := c) hz
    -- first derivative: `z * rgiD1 = K (s⁻ z^{s⁻} A + s⁺ z^{s⁺} B)`
    have hzA1 : z * rgiD1 α m c z
        = rgiK α m * (rgiSn α m * (z ^ rgiSn α m * rgiA α m c z)
          + rgiSp α m * (z ^ rgiSp α m * rgiB α m c z)) := by
      simp only [rgiD1]
      linear_combination (rgiK α m * rgiSn α m * rgiA α m c z) * hzs1
        + (rgiK α m * rgiSp α m * rgiB α m c z) * hzp1
    -- second derivative:
    -- `z² * rgiD2 = K (s⁻(s⁻-1) z^{s⁻} A + s⁺(s⁺-1) z^{s⁺} B + (s⁻-s⁺) c)`
    have hzA2 : z ^ 2 * rgiD2 α m c z
        = rgiK α m * (rgiSn α m * (rgiSn α m - 1) * (z ^ rgiSn α m * rgiA α m c z)
          + rgiSp α m * (rgiSp α m - 1) * (z ^ rgiSp α m * rgiB α m c z)
          + (rgiSn α m - rgiSp α m) * c z) := by
      simp only [rgiD2]
      linear_combination (rgiK α m * rgiSn α m * (rgiSn α m - 1) * rgiA α m c z) * hzs2
        + (rgiK α m * rgiSp α m * (rgiSp α m - 1) * rgiB α m c z) * hzp2
        + (rgiK α m * rgiSn α m) * hc1 - (rgiK α m * rgiSp α m) * hc2
    obtain ⟨hind1, hind2, hK⟩ := rgiIndicial α hα m
    have hEC := eulerCombination (α := α) (lam := Work.FTS.PhiStar.Radial.lamR m)
      (K := rgiK α m) (sn := rgiSn α m) (sp := rgiSp α m)
      (P := z ^ rgiSn α m * rgiA α m c z) (Q := z ^ rgiSp α m * rgiB α m c z)
      (cz := c z) (W1 := z * rgiD1 α m c z) (W2 := z ^ 2 * rgiD2 α m c z)
      hzA1 hzA2 hind1 hind2 hK
    linear_combination hEC
  intro z hz
  have hfun : Work.FTS.PhiStar.Radial.radGreen α m c
      = Work.FTS.PhiStar.Radial.radGreenI α m c := rfl
  simpa only [hfun] using hmain z hz

end Work.FTS.PhiStar.Series.Deleg
