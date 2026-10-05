import Mathlib
import Submission.Work.RPB.B5.contDiff_signedArea
import Submission.Work.RPA3.contDiff_param_intervalIntegral

/-!
# B5: smoothness of the signed area at `σ = 0` from a *local* hypothesis

`Work.RPB.B5.contDiffAt_signedArea_of_contDiffOn`: the signed area
`σ ↦ signedArea (V σ) = (1/2) ∫_0^{2π} ω_ℂ (V σ t, ∂_t V σ t) dt` is `C^n` at `σ = 0`
provided the joint family `(σ,t) ↦ V σ t` is `C^{n+1}` only on the *open* set
`(-1,1) × ℝ` (which is a neighbourhood of `{0} × ℝ`).

The global statement `Work.RPB.B5.contDiff_signedArea` needs the family to be `C^{n+1}`
*everywhere* (and, in its current interface, `2π`-periodic, which is not actually used).  To pass
from the local hypothesis to the global one, we compose `V` with a `C^∞` function `ψ : ℝ → ℝ`
that is the identity near `0` and whose range lies inside `(-1,1)` — such a `ψ` is built from a
`ContDiffBump`.  The resulting family `σ ↦ V (ψ σ)` is globally `C^{n+1}`, agrees with `V` in a
neighbourhood of `0`, and hence has the same germ of signed areas at `0`.

## Contents

* `contDiff_signedArea_noPer` — `contDiff_signedArea` with the periodicity hypothesis dropped
  (the two ingredients `contDiff_sliceDeriv` and `contDiff_omegaC` are imported);
* `exists_contDiff_eq_id_near_zero_mapsTo_Ioo` — the localising `ψ`;
* `contDiffAt_signedArea_of_contDiffOn` — the requested statement.
-/

open MeasureTheory intervalIntegral
open scoped Interval ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- `contDiff_signedArea` without the (unused) periodicity hypothesis: the signed area of a
globally `C^{k+1}` two-parameter family is `C^k` in the family parameter.

This is the proof of `Work.RPB.B5.contDiff_signedArea` with `hper` removed: the slice derivative
`(σ,t) ↦ ∂_t V σ t` is `C^k` (`contDiff_sliceDeriv`), the integrand is `C^k` (`contDiff_omegaC`),
and a parametric integral of a jointly `C^k` family is `C^k`
(`Work.RPA3.contDiff_param_intervalIntegral`). -/
theorem contDiff_signedArea_noPer (V : ℝ → ℝ → ℂ) (k : ℕ)
    (hV : ContDiff ℝ (k + 1) (fun z : ℝ × ℝ => V z.1 z.2)) :
    ContDiff ℝ k (fun σ => Work.RPB.signedArea (V σ)) := by
  have hWk : ContDiff ℝ k (fun z : ℝ × ℝ => V z.1 z.2) := hV.of_le (by norm_num)
  have hderivCont : ContDiff ℝ k (fun z : ℝ × ℝ => deriv (fun s => V z.1 s) z.2) :=
    contDiff_sliceDeriv V hV
  have hg : ContDiff ℝ k
      (fun z : ℝ × ℝ => Work.RPV.ωC (V z.1 z.2) (deriv (fun s => V z.1 s) z.2)) :=
    contDiff_omegaC hWk hderivCont
  have hint : ContDiff ℝ k
      (fun σ => ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V σ t) (deriv (fun s => V σ s) t)) :=
    Work.RPA3.contDiff_param_intervalIntegral (k : ℕ∞)
      (fun σ t => Work.RPV.ωC (V σ t) (deriv (fun s => V σ s) t)) hg 0 (2 * Real.pi)
  have h2 : ContDiff ℝ k
      (fun σ => (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V σ t) (deriv (fun s => V σ s) t)) :=
    ContDiff.const_smul (1 / 2 : ℝ) hint
  simpa only [Work.RPB.signedArea] using h2

/-- There is a `C^∞` function `ψ : ℝ → ℝ` that equals the identity in a neighbourhood of `0` and
sends all of `ℝ` into `(-1,1)`.

Explicitly `ψ σ = σ · b σ` where `b` is a `ContDiffBump` around `0` with `rIn = 1/4`,
`rOut = 1/2`; then `ψ σ = σ` for `|σ| ≤ 1/4` and `ψ σ = 0` for `|σ| ≥ 1/2`, so `|ψ σ| ≤ 1/2`. -/
theorem exists_contDiff_eq_id_near_zero_mapsTo_Ioo :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ ψ =ᶠ[𝓝 0] id ∧ ∀ σ, ψ σ ∈ Set.Ioo (-1:ℝ) 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  refine ⟨fun σ => σ * b σ, ?_, ?_, ?_⟩
  · exact contDiff_id.mul b.contDiff
  · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1/4)]
      with σ hσ
    simp only [id_eq]
    rw [ContDiffBump.one_of_mem_closedBall b hσ, mul_one]
  · intro σ
    rw [Set.mem_Ioo]
    have hb1 : b σ ≤ 1 := ContDiffBump.le_one b
    have hb0 : 0 ≤ b σ := ContDiffBump.nonneg b
    have key : |σ * b σ| ≤ 1/2 := by
      by_cases h : dist σ 0 ≤ 1/2
      · have hσ : |σ| ≤ 1/2 := by rwa [Real.dist_eq, sub_zero] at h
        calc |σ * b σ| = |σ| * b σ := by rw [abs_mul, abs_of_nonneg hb0]
          _ ≤ |σ| * 1 := by gcongr
          _ = |σ| := by rw [mul_one]
          _ ≤ 1/2 := hσ
      · have hlt : (1/2 : ℝ) < dist σ 0 := not_le.mp h
        have hz : b σ = 0 := ContDiffBump.zero_of_le_dist b (le_of_lt hlt)
        rw [hz, mul_zero, abs_zero]; norm_num
    have hlt1 : |σ * b σ| < 1 := lt_of_le_of_lt key (by norm_num)
    exact abs_lt.mp hlt1

theorem contDiffAt_signedArea_of_contDiffOn (V : ℝ → ℝ → ℂ) (n : ℕ)
    (hV : ContDiffOn ℝ (n + 1) (fun z : ℝ × ℝ => V z.1 z.2)
      (Set.Ioo (-1:ℝ) 1 ×ˢ Set.univ)) :
    ContDiffAt ℝ n (fun σ => Work.RPB.signedArea (V σ)) 0 := by
  obtain ⟨ψ, hψ_smooth, hψ_near, hψ_maps⟩ := exists_contDiff_eq_id_near_zero_mapsTo_Ioo
  -- the "reindexing" map `z ↦ (ψ z.1, z.2)` is globally `C^{n+1}` and lands in the open set
  have hg : ContDiff ℝ (n + 1) (fun z : ℝ × ℝ => (ψ z.1, z.2)) := by
    have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ψ z.1) := hψ_smooth.comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z.2) := contDiff_snd
    exact (h1.prodMk h2).of_le (by simp)
  have hmap : Set.MapsTo (fun z : ℝ × ℝ => (ψ z.1, z.2)) Set.univ
      (Set.Ioo (-1:ℝ) 1 ×ˢ Set.univ) := by
    intro z _
    exact ⟨hψ_maps z.1, trivial⟩
  -- the localised family is globally `C^{n+1}`
  have hW' : ContDiff ℝ (n + 1) (fun z : ℝ × ℝ => V (ψ z.1) z.2) := by
    have hcomp : ContDiffOn ℝ (n + 1)
        ((fun z : ℝ × ℝ => V z.1 z.2) ∘ (fun z : ℝ × ℝ => (ψ z.1, z.2))) Set.univ :=
      hV.comp hg.contDiffOn hmap
    rw [contDiffOn_univ] at hcomp
    exact hcomp
  have hmain : ContDiff ℝ n (fun σ => Work.RPB.signedArea (fun t => V (ψ σ) t)) :=
    contDiff_signedArea_noPer (fun σ t => V (ψ σ) t) n hW'
  -- it agrees with `V` near `σ = 0`, so the signed areas have the same germ at `0`
  refine hmain.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hψ_near] with σ hσ
  have heq : V σ = (fun t => V (ψ σ) t) := by
    funext t
    simp only [hσ, id_eq]
  rw [heq]

end Work.RPB.B5
