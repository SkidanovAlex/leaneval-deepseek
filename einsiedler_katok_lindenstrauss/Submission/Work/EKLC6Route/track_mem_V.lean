import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.gridIdx_ratio_mem_V
import Submission.Work.EKLC6Route.VtSet_mul_inv
import Submission.Work.EKLCompAux.flower_constants
import Submission.Work.EKLComp.inv_mem_V

namespace Work.EKLC6Route

open Work.EKLContract

/-- Members of `Uball U r` are `V r`-small entrywise displacements of the identity. -/
private lemma Uball_subset_V {U : Subgroup SL3} {r : ℝ} :
    Work.EKLComp.Uball U r ⊆ V r := fun _ hg => hg.2

/-- Numerical core of `track_mem_V`: with `4000 r ≤ δ`, `4000 ρ ≤ δ`, `s ≤ 100 ρ` and
`δ ≤ 1/100`, the product radius `A + 10 r + 3 A (10 r)` (where `A = r + s + 3 r s`) is `< δ`. -/
private lemma track_num {r ρ s δ : ℝ} (hr : 0 ≤ r) (hs0 : 0 ≤ s)
    (hs : s ≤ 100 * ρ) (hδ : 0 < δ) (hrδ : 4000 * r ≤ δ) (hρδ : 4000 * ρ ≤ δ)
    (hδ1 : δ ≤ 1 / 100) :
    (r + s + 3 * r * s) + 10 * r + 3 * (r + s + 3 * r * s) * (10 * r) < δ := by
  have hr' : r ≤ δ / 4000 := by linarith
  have hs' : s ≤ δ / 40 := by linarith
  have hδ2 : δ * δ ≤ δ / 100 := by nlinarith [hδ, hδ1]
  have hrs : r * s ≤ δ * δ / 160000 := by
    have h1 : r * s ≤ (δ / 4000) * (δ / 40) :=
      mul_le_mul hr' hs' hs0 (by linarith : (0 : ℝ) ≤ δ / 4000)
    nlinarith [h1]
  have hrs3 : 3 * r * s ≤ 3 * δ / 16000000 := by nlinarith [hrs, hδ2, hδ]
  have hA : r + s + 3 * r * s ≤ δ / 32 := by nlinarith [hr', hs', hrs3]
  have hA0 : 0 ≤ r + s + 3 * r * s := by nlinarith [hr, hs0, mul_nonneg hr hs0]
  have hrA : r * (r + s + 3 * r * s) ≤ (δ / 4000) * (δ / 32) :=
    mul_le_mul hr' hA hA0 (by positivity)
  have h30 : 3 * (r + s + 3 * r * s) * (10 * r) ≤ 3 * δ / 1280000 := by
    nlinarith [hrA, hδ2, hδ]
  linarith [hA, hr', h30]

theorem track_mem_V {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) {L : ℕ} {u u' k k' : Work.EKLContract.SL3}
    (hu : u ∈ Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) w.r)
    (hu' : u' ∈ Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) w.r)
    (hk : k ∈ Work.EKLC6Route.VtSet t ∩ Work.EKLContract.V w.ρ)
    (hk' : k' ∈ Work.EKLC6Route.VtSet t ∩ Work.EKLContract.V w.ρ)
    (hgrid : Work.EKLC6Route.gridIdx w.ρ L k = Work.EKLC6Route.gridIdx w.ρ L k') :
    u' * (k' * k⁻¹) * u⁻¹ ∈ Work.EKLContract.V w.δ := by
  have hr : 0 < w.r := w.hr
  have hρ : 0 < w.ρ := w.hρ
  have hδ : 0 < w.δ := w.hδ
  have hrδ : 4000 * w.r ≤ w.δ := w.hrδ
  have hρδ : 4000 * w.ρ ≤ w.δ := w.hρδ
  have hδ1 : w.δ ≤ 1 / 100 := w.hδ1
  have hρ1 : w.ρ ≤ 1 := by linarith
  have hr1 : w.r ≤ 1 := by linarith
  -- the tracked displacement `g = k' k⁻¹` is `100 (1/2)^L ρ`-small
  have hgV : k' * k⁻¹ ∈ V (100 * (1 / 2 : ℝ) ^ L * w.ρ) :=
    gridIdx_ratio_mem_V hρ hρ1 hk.2 hk'.2 hgrid
  have hu'V : u' ∈ V w.r := Uball_subset_V hu'
  have huV : u ∈ V w.r := Uball_subset_V hu
  have huinv : u⁻¹ ∈ V (10 * w.r) := Work.EKLComp.inv_mem_V hr hr1 huV
  -- the two product estimates
  have h1 : u' * (k' * k⁻¹) ∈
      V (w.r + 100 * (1 / 2 : ℝ) ^ L * w.ρ
        + 3 * w.r * (100 * (1 / 2 : ℝ) ^ L * w.ρ)) :=
    Work.EKLCompAux.mul_mem_V (by linarith) (by positivity) hu'V hgV
  have h2 : (u' * (k' * k⁻¹)) * u⁻¹ ∈
      V ((w.r + 100 * (1 / 2 : ℝ) ^ L * w.ρ
            + 3 * w.r * (100 * (1 / 2 : ℝ) ^ L * w.ρ))
          + 10 * w.r
          + 3 * (w.r + 100 * (1 / 2 : ℝ) ^ L * w.ρ
              + 3 * w.r * (100 * (1 / 2 : ℝ) ^ L * w.ρ)) * (10 * w.r)) :=
    Work.EKLCompAux.mul_mem_V (by positivity) (by positivity) h1 huinv
  -- numeric comparison
  have hhalf : (1 / 2 : ℝ) ^ L ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hsle : 100 * (1 / 2 : ℝ) ^ L * w.ρ ≤ 100 * w.ρ := by
    have := mul_le_mul_of_nonneg_right hhalf (le_of_lt hρ)
    nlinarith [this]
  have hnum := track_num (r := w.r) (ρ := w.ρ) (s := 100 * (1 / 2 : ℝ) ^ L * w.ρ)
    (le_of_lt hr) (by positivity) hsle hδ hrδ hρδ hδ1
  exact Work.EKLCompAux.V_mono (le_of_lt hnum) h2

end Work.EKLC6Route
