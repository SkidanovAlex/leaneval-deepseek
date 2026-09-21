import Mathlib
import Submission.Work.OddCurve.Inv.Defs
import Submission.Work.OddCurve.Inv.abelTrans_negHalf_eq_abelNu

/-!
# `T_{-1/2}` of the explicit Radon inverse

The assembly step of `PLAN_M2.md` §2, first half: with `γ = radonInvData n F` one has
`γ (√σ)/√σ = abelNuInv (abelDatumNu n F) σ` for `σ ≥ 0`; hence the substitution
`T_{-1/2} γ c = (1/2) J^{1/2} (γ ∘ √ / √) (c²)` and the Abel right inverse
`abelNu (abelNuInv G) = G` give

  `T_{-1/2} (radonInvData n F) c = abelDatum n F c`   (`c ∈ (0,1)`),

i.e. the `(n-1)`-fold reduction of `T_{n-3/2} (radonInvData n F)` is the reduction of the datum
`K c = (2|S^{2n-2}|)⁻¹ c^{2n-2} F c` — the input of the kernel lemma
`Inv.eq_of_abelReduceIter_eq_of_eqOn`.
-/

namespace Work.OddCurve.Inv

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-- The `√`-substitution of `radonInvData`. -/
theorem radonInvData_comp_sqrt (n : ℕ) (F : ℝ → ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    radonInvData n F (Real.sqrt σ) / Real.sqrt σ = abelNuInv (abelDatumNu n F) σ := by
  rcases eq_or_lt_of_le hσ with h | h
  · subst h
    simp [radonInvData, abelNuInv, abelNu]
  · have hs : 0 < Real.sqrt σ := Real.sqrt_pos.2 h
    have harg : (Real.sqrt σ) ^ 2 = σ := by rw [sq, Real.mul_self_sqrt hσ]
    simp only [radonInvData, harg]
    rw [abs_of_pos hs]
    field_simp

/-- **The reduction of the Radon inverse reproduces the Abel datum.** -/
theorem abelTrans_negHalf_radonInvData (n : ℕ) (hn : 1 ≤ n) {F : ℝ → ℝ}
    (habel : ∀ ν ∈ Set.Ioo (0 : ℝ) 1,
      abelNu (abelNuInv (abelDatumNu n F)) ν = abelDatumNu n F ν) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      Work.OddRadon.abelTrans (-(1 / 2)) (radonInvData n F) c = abelDatum n F c := by
  intro c hc
  have hc0 : 0 < c := hc.1
  have hc2 : c ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith [hc.2]⟩
  rw [abelTrans_negHalf_eq_abelNu (γ := radonInvData n F) c hc0]
  have habel' : (∫ σ in (0:ℝ)..(c^2),
        (Real.sqrt ((c^2) - σ))⁻¹ * abelNuInv (abelDatumNu n F) σ)
      = abelDatumNu n F (c^2) := by
    have h := habel (c^2) hc2
    rwa [abelNu] at h
  have hcongr : (∫ σ in (0:ℝ)..(c^2),
        (Real.sqrt ((c^2) - σ))⁻¹ * (radonInvData n F (Real.sqrt σ) / Real.sqrt σ))
      = ∫ σ in (0:ℝ)..(c^2),
        (Real.sqrt ((c^2) - σ))⁻¹ * abelNuInv (abelDatumNu n F) σ := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ c^2)] at hσ
    dsimp only
    rw [radonInvData_comp_sqrt n F hσ.1]
  simp only [abelNu]
  rw [hcongr, habel']
  simp only [abelDatumNu]
  rw [Real.sqrt_sq hc0.le]
  ring

end

end Work.OddCurve.Inv
