import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.continuous_integral_tBamp_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open MeasureTheory
open scoped Topology

noncomputable section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The centred cube of side `a` is contained in the centred cube of side `max a 0`
(the nonnegative "radius" of `acube a`); the latter has finite measure unconditionally. -/
private lemma acube_subset_acube_max (a : ℝ) :
    Submission.BoseGases.acube a ⊆ Submission.BoseGases.acube (max a 0) := by
  intro z hz
  simp only [Submission.BoseGases.mem_acube_iff] at hz ⊢
  intro m
  obtain ⟨h1, h2⟩ := hz m
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    exact ⟨by linarith, by linarith⟩
  · rw [max_eq_left ha]
    exact ⟨h1, h2⟩

/-- Replacing one coordinate of a point of the ambient box by a point of a set
`A ⊆ acube a` keeps the configuration in the ambient box. -/
private lemma update_mem_abox {N : ℕ} {a : ℝ} {A : Set ℝ³} (hAsub : A ⊆ Submission.BoseGases.acube a)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N a) {z : ℝ³} (hz : z ∈ A)
    (i : Fin N) : Function.update x i z ∈ Submission.BoseGases.abox N a := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact hAsub hz
  · rw [Function.update_of_ne hj]; exact hx j

/-- **The uniform norm bound on the windowed amplitude.**  If the window `χ` is bounded by `Cχ`
on its (topological) support, if that support lies in the cube `acube a`, and if `Φ` is bounded by
`M` on the ambient box `abox N a`, then the amplitude of `Φ` at any box configuration is bounded
by `Cχ·M·|tsupport χ|`.  (No measurability or integrability hypothesis on `χ`, `Φ` is needed: the
integrand of `tBamp` vanishes off `tsupport χ`, where the norm bound is pointwise.) -/
theorem tBamp_norm_le_of_bound {N : ℕ} {a : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} {Cχ M : ℝ} (hCχ : 0 ≤ Cχ)
    (hχb : ∀ z ∈ tsupport χ, |χ z| ≤ Cχ)
    (hχsub : tsupport χ ⊆ Submission.BoseGases.acube a)
    (hΦb : ∀ y ∈ Submission.BoseGases.abox N a, |Φ y| ≤ M)
    (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N a) :
    ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖
      ≤ Cχ * M * MeasureTheory.volume.real (tsupport χ) := by
  -- `tsupport χ` has finite measure, being contained in the cube `acube (max a 0)`.
  have hfin : (volume : Measure ℝ³) (tsupport χ) < ⊤ :=
    lt_of_le_of_lt (measure_mono (hχsub.trans (acube_subset_acube_max a)))
      (Submission.BoseGases.acube_lt_top (max a 0) (le_max_right a 0))
  -- rewrite the amplitude as a set integral over `tsupport χ` (off which the integrand vanishes)
  rw [Work.SmallBoxTBWord.tBamp_eq_setIntegral_tsupport]
  refine norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³)) hfin ?_
  intro z hz
  have hexp : ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hΦz : |Φ (Function.update x i z)| ≤ M :=
    hΦb _ (update_mem_abox hχsub hx hz i)
  calc ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ)‖
      = |χ z| * |Φ (Function.update x i z)| := by
        rw [norm_mul, norm_mul, hexp, mul_one]
        simp
    _ ≤ Cχ * M := mul_le_mul (hχb z hz) hΦz (abs_nonneg _) hCχ

end

end Work.SmallBoxTBWord
