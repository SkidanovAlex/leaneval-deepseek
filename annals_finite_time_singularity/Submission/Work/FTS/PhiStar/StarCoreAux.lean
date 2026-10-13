import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Model

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.StarCoreInhabitant` — the analysis node `StarCore`

For every `0 < α ≤ 1/5` there is a stream function `Φ_* = Model α (GzProfile α) ψ + R` with

* `R = psiSeries α (RemSource α ψ)` the mode series solving the `O(α²)` remainder equation
  (`Series.psiSeries_solves_rem`),
* `Φ_*` presented in the zero-extension normal form (`ZeroOffWitness`) so that `PhiTs α Φ_*`
  vanishes off the open quadrant,
* and the flat bound `FlatW 7 (Ycheck α Φ_*) (Cs·α)` assembled from

  `Ycheck α Φ_* = ((z+1)/z)·Aprof α + α·(2/(1+z))·(ψ/sin 2θ) + ((z+1)/z)·R/sin 2θ`

  whose three pieces are bounded by `FlatW_aprof` (`O(α)`), `FlatW_psiDiv` transported along the
  radial factor `2/(1+z)` (`O(α)`), and `FlatW_psiSeries` (`O(α²)`) respectively
  (`FlatW_YcheckExpansion`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Classical

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `FlatW` is monotone in its constant. -/
theorem FlatW_mono {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') :
    Work.FTS.VocabO2.FlatW l f K' := by
  intro z θ hz hθ hθ2
  obtain ⟨h1, h2⟩ := h z θ hz hθ hθ2
  exact ⟨fun k hk => le_trans (h1 k hk) hle, fun k i hki => le_trans (h2 k i hki) hle⟩

/-- The explicit decomposition of `Ycheck`, as a definition. -/
def YcheckExpand (α : ℝ) (ψ : ℝ → ℝ) (R : Fn) : Fn :=
  fun z θ => (z + 1) / z * Aprof α z
    + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)
    + (z + 1) / z * R z θ / Work.Construction.s2 θ

/-- **The pointwise identity behind the flat bound**: on the open quadrant, `Ycheck` of the
assembled witness is the sum of the explicit flat part, the separable model part and the
remainder. -/
theorem Ycheck_eq_expand {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ψ : ℝ → ℝ} {R : Fn}
    {Φs : Fn}
    (hs : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Φs z θ = Model α (GzProfile α) ψ z θ + R z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      YcheckExpand α ψ R z θ = Work.FTS.VocabO2.Ycheck α Φs z θ := by
  intro z θ hz hθ hθ2
  have hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
  have hs2 : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos]))
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  have hphi : (z + 1) / z * Work.FTS.VocabO.phiR z = 2 / (1 + z) := by
    rw [Work.FTS.VocabO.phiR]
    field_simp
    ring
  have hkey : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      = Aprof α z * Work.Construction.s2 θ + α * Work.FTS.VocabO.phiR z * ψ θ + R z θ := by
    have hp : Φs z θ = Model α (GzProfile α) ψ z θ + R z θ := hs z θ hzp
    have hq : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        = Work.Construction.PhiTil α (Work.Construction.Fstar α)
            (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) z θ := by
      simp only [Work.Construction.PhiTil, hp]
    exact hq.trans (PhiTil_expansion_eq hα hα1 ψ R z θ (le_of_lt hz))
  show YcheckExpand α ψ R z θ = Work.FTS.VocabO2.Ycheck α Φs z θ
  unfold YcheckExpand Work.FTS.VocabO2.Ycheck
  rw [show Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ / Work.Construction.s2 θ
      = (Aprof α z * Work.Construction.s2 θ + α * Work.FTS.VocabO.phiR z * ψ θ + R z θ)
        / Work.Construction.s2 θ from by rw [hkey]]
  rw [← hphi]
  field_simp
  try ring

end Work.FTS.PhiStar
