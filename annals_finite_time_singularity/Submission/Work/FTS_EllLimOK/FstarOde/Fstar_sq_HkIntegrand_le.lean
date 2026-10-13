import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.FstarOde

set_option autoImplicit false

/-! ## The level-`0` integrand and the pointwise weight bookkeeping

At level `k = 0` the `H^k`-integrand is a *single* square (`Work.Spaces.HkIntegrand` has the
one `D_z`-term `i = 0` and an empty mixed double sum),

`HkIntegrand α 0 F z θ = (F z θ · w(z) / sin(2θ)^{η/2})²`,  `w(z) = (1+z)²/z²`,

so that for `z > 0` the factor `z⁴` of the estimate below is exactly the reciprocal of the
angular weight of `F`:

`z⁴ · HkIntegrand α 0 F z θ = (F z θ · (1+z)² / sin(2θ)^{η/2})²`.

Since `(1+z)² ≥ 1` and `sin(2θ)^{η/2} ≤ 1` in the *interior* `θ ∈ (0,π/2)`, the bracket is at
least `1` there, and hence `F(z,θ)² ≤ z⁴ · HkIntegrand α 0 F z θ`.  This fails only at the two
endpoints `θ = 0, π/2` (where `sin(2θ) = 0` and the totalised division makes both `w/s^{η/2}`
and the integrand vanish) — a null set, which is why the comparison of the two integrals is
taken almost everywhere. -/

/-- At level `k = 0` the `H^k`-integrand is the single square
`(F z θ · w(z) / sin(2θ)^{η/2})²`. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **Pointwise weight bookkeeping.**  For `z > 0` and `θ ∈ (0,π/2)`,
`F(z,θ)² ≤ z⁴ · HkIntegrand α 0 F z θ`: the right hand side is
`(F(z,θ) · (1+z)²/sin(2θ)^{η/2})²` and the bracket is `≥ 1`. -/
private lemma fstar_sq_pointwise_le {α z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (δ : ℝ → ℝ → ℝ) :
    (δ z θ) ^ 2 ≤ z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hspow_pos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hspos _
  have hspow_le : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hspos.le (Real.sin_le_one _) (by linarith [Work.Spaces.eta_nonneg])
  have hge : 1 ≤ (1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspow_pos]
    have h1z : (1 : ℝ) ≤ (1 + z) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  -- the `z⁴`-weighted integrand is the square `(δ z θ · (1+z)²/sin(2θ)^{η/2})²`
  rw [HkIntegrand_zero_eq,
    show z ^ 4 = (z ^ 2) ^ 2 by ring, ← mul_pow,
    show z ^ 2 * (δ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        = δ z θ * ((z ^ 2 * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      from by ring,
    show z ^ 2 * Work.Spaces.w z = (1 + z) ^ 2 from by rw [Work.Spaces.w]; field_simp]
  -- whose bracket is at least `1`
  have hc2 : (1 : ℝ) ≤ ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    nlinarith [hge, sq_nonneg ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) - 1)]
  calc (δ z θ) ^ 2 = (δ z θ) ^ 2 * 1 := by ring
    _ ≤ (δ z θ) ^ 2 * ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
    _ = (δ z θ * ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring

/-- The pointwise comparison of the previous lemma holds almost everywhere on `Iθ`: the only
angles of `Iθ` at which `sin(2θ)` vanishes are the two endpoints `θ = 0, π/2` (in the interior
`sin(2θ) > 0`), a null set. -/
private lemma ae_fstar_sq_le_HkIntegrand {δ : ℝ → ℝ → ℝ} {α z : ℝ} (hz : 0 < z) :
    (fun θ : ℝ => (δ z θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsub : {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0}
      ⊆ ({0} ∪ {Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq] at hθ
    obtain ⟨hθI, hsin⟩ := hθ
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne0, hne2⟩ := hcon
    have hθ1 : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hne0)
    have hθ2 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 hne2
    have hpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith
  have hnull : volume {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0} = 0 :=
    measure_mono_null hsub (measure_union_null (measure_singleton (0 : ℝ)) (measure_singleton _))
  change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    (δ z θ) ^ 2 ≤ z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ
  rw [MeasureTheory.ae_restrict_iff' hIθ, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro θ hθ
  simp only [Set.mem_ofPred_eq] at hθ ⊢
  obtain ⟨hθI, hne⟩ := Classical.not_imp.mp hθ
  refine ⟨hθI, ?_⟩
  by_contra hsin
  have hθ1 : 0 < θ := lt_of_le_of_ne hθI.1 (fun h0 => hsin (by rw [← h0]; norm_num))
  have hθ2 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2
    (fun h2 => hsin (by rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]))
  exact (not_lt.mpr (fstar_sq_pointwise_le hz ⟨hθ1, hθ2⟩ δ)) (not_le.mp hne)

/-- **The angular-`L²` bound for the moment `F_*` against the level-`0` `H`-integrand.**

`BoxReg` makes the slices of `δ` continuous on the compact interval `Iθ`, so `θ ↦ δ(z,θ)²` is
integrable there and Cauchy–Schwarz in its discriminant form
(`Work.Elliptic.Fstar_sq_le`) gives

`F_*(z)² ≤ (π/2) ∫_θ δ(z,θ)² dθ`.

The pointwise weight bookkeeping (`ae_fstar_sq_le_HkIntegrand`) upgrades the right hand side
to the level-`0` `H`-integrand: `δ(z,θ)² ≤ z⁴ · HkIntegrand α 0 δ z θ` for a.e. `θ`, whence

`F_*(z)² ≤ (π/2) z⁴ ∫_θ HkIntegrand α 0 δ z θ`. -/
theorem Fstar_sq_HkIntegrand_le {α : ℝ} {δ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg δ)
    (hHk : Work.Spaces.HkMem α 0 δ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.Fstar δ z) ^ 2
        ≤ (π / 2) * z ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz0
  -- the slice of `δ` is continuous on the compact interval, so its square is integrable there
  have hslice : ContinuousOn (fun θ => δ z θ) (Set.Icc 0 (Real.pi / 2)) :=
    (hbox.slice hz).continuousOn
  have hIntδ : IntegrableOn (fun θ => (δ z θ) ^ 2) Work.Spaces.Iθ :=
    (hslice.pow 2).integrableOn_compact isCompact_Icc
  have hIntHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 δ z θ) Work.Spaces.Iθ :=
    hHk.1 z hzI
  -- comparison of the two slice integrals, almost everywhere
  have hmono : ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ :=
    integral_mono_ae hIntδ (hIntHk.const_mul (z ^ 4)) (ae_fstar_sq_le_HkIntegrand hz0)
  have hmono' : ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2
      ≤ z ^ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ := by
    calc ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ := hmono
      _ = z ^ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ :=
          MeasureTheory.integral_const_mul _ _
  -- Cauchy–Schwarz for the angular moment, then the weight bookkeeping
  have hCS := Work.Elliptic.Fstar_sq_le δ z hIntδ
  calc (Work.Elliptic.Fstar δ z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2 := hCS
    _ ≤ (π / 2) * (z ^ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) :=
        mul_le_mul_of_nonneg_left hmono' (by linarith [Real.pi_pos])
    _ = (π / 2) * z ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) := by ring

end Work.FTS_EllLimOK.FstarOde
