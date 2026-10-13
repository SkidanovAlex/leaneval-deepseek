import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist.Honesty

/-- A function continuous on `(0,∞)` which is integrable on `(1,∞)` is integrable on `(t,∞)`
for every `t > 0`: split `(t,∞) = (t,m] ∪ (m,∞)` with `m = max 1 t` and use compactness of
`[t,m]` together with monotonicity of the integral. -/
lemma integrableOn_Ioi_of_integrableOn_Ioi_one {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0)) (h1 : IntegrableOn f (Set.Ioi 1)) {t : ℝ} (ht : 0 < t) :
    IntegrableOn f (Set.Ioi t) := by
  have hta : t ≤ max 1 t := le_max_right 1 t
  have hIoc : IntegrableOn f (Set.Ioc t (max 1 t)) := by
    have hcu : ContinuousOn f (Set.uIcc t (max 1 t)) := by
      rw [Set.uIcc_of_le hta]
      exact hcont.mono (fun x hx => lt_of_lt_of_le ht hx.1)
    have hint : IntervalIntegrable f volume t (max 1 t) := hcu.intervalIntegrable
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hta] at hint
  have hIoi : IntegrableOn f (Set.Ioi (max 1 t)) :=
    h1.mono_set (Set.Ioi_subset_Ioi (le_max_left 1 t))
  have hunion : IntegrableOn f (Set.Ioc t (max 1 t) ∪ Set.Ioi (max 1 t)) := hIoc.union hIoi
  rwa [Set.Ioc_union_Ioi_eq_Ioi hta] at hunion

-- `radPsi α m c = fun z => ∫ u in Set.Ioi 1, c (z*u) * u^(-p-1)` with `p = radP α m = 2m/α ≥ 8`
-- (`Submission/Work/FTS/PhiStar/RadialWAux/Defs.lean`).  Claim: for `z > 0`,
--   `Ψ'(z) = (radP α m * Ψ(z) - c z) / z`, i.e. `z Ψ' = p Ψ - c`.
-- ROUTE: `Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow` (proved, in
-- `radGreen_eq_rescaled.lean`) gives `Ψ z = z^p * ∫ t in Set.Ioi z, c t * t^{-p-1}` (for any `c`,
-- `z > 0`).  Put `g t = c t * t^{-p-1}`, continuous on `(0,∞)` by `hc`.  For a fixed `z₀ > 0`
-- choose `a = max 1 (2*z₀)`; for `y < a`,
-- `∫ t in Ioi y, g t = ∫ t in Ioi a, g t + ∫ t in y..a, g t`
-- (split `Ioi y = Ioc y a ∪ Ioi a`; `IntegrableOn g (Ioi y)` follows from `hinf` on `Ioi 1`
-- together with continuity on `(y,1)`, via `IntegrableOn.union`).  The derivative at `y = z₀` of
-- `y ↦ ∫ t in y..a, g t` is `-g z₀` (`intervalIntegral.integral_hasDerivAt_left`), and the
-- displayed equality holds eventually near `z₀`, so `HasDerivAt (fun y => ∫ t in Ioi y, g t) (-g z₀) z₀`.
-- Finish with the product rule for `z ↦ z^p * A z` and the identity `z₀^p * g z₀ = c z₀ / z₀`
-- (`Real.rpow_add`, `z₀ > 0`).

theorem radPsi_hasDerivAt {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.FTS.PhiStar.RadialWAux.radPsi α m c)
        ((Work.FTS.PhiStar.RadialWAux.radP α m
            * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z) z := by
  intro z hz
  set p : ℝ := Work.FTS.PhiStar.RadialWAux.radP α m with hp
  set g : ℝ → ℝ := fun t => c t * t ^ (-p - 1) with hg
  have hpval : p = 2 * (m : ℝ) / α := by rw [hp]; rfl
  -- `g` is continuous on `(0,∞)`
  have hgcont : ContinuousOn g (Set.Ioi 0) := by
    rw [hg]
    exact hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  -- and integrable on `(1,∞)`, by comparison with the hypothesis `hinf`
  have hintegr : IntegrableOn g (Set.Ioi 1) := by
    have habs : IntegrableOn (fun t => |g t|) (Set.Ioi 1) := by
      refine hinf.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      simp only [hg, hpval]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi 1)) :=
      (hgcont.mono (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))).aestronglyMeasurable
        measurableSet_Ioi
    exact (integrable_norm_iff hmeas).mp
      (by simpa [Real.norm_eq_abs, IntegrableOn] using habs)
  -- the substitution identity `Ψ y = y^p · ∫_{Ioi y} g`
  have hsub : ∀ y : ℝ, 0 < y →
      Work.FTS.PhiStar.RadialWAux.radPsi α m c y = y ^ p * ∫ t in Set.Ioi y, g t := by
    intro y hy
    have h := Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow c
      (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1) hy
    show (∫ u in Set.Ioi (1 : ℝ),
        c (y * u) * u ^ (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1))
      = y ^ p * ∫ t in Set.Ioi y, g t
    rw [h, show -(-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1 + 1) = p from by rw [hp]; ring]
  -- the threshold `a = max 1 (2z)` and the splitting identity
  have h1a : (1 : ℝ) ≤ max 1 (2 * z) := le_max_left 1 (2 * z)
  have hza : z < max 1 (2 * z) := by
    have h2 : z < 2 * z := by linarith
    exact lt_of_lt_of_le h2 (le_max_right 1 (2 * z))
  have hza' : z ≤ max 1 (2 * z) := le_of_lt hza
  have hIa : IntegrableOn g (Set.Ioi (max 1 (2 * z))) :=
    hintegr.mono_set (Set.Ioi_subset_Ioi h1a)
  have hsplit : ∀ y : ℝ, 0 < y → y ≤ max 1 (2 * z) →
      (∫ t in Set.Ioi y, g t)
        = (∫ t in Set.Ioi (max 1 (2 * z)), g t) + ∫ t in y..(max 1 (2 * z)), g t := by
    intro y hy hya
    have hy' : IntegrableOn g (Set.Ioi y) :=
      integrableOn_Ioi_of_integrableOn_Ioi_one hgcont hintegr hy
    have h := intervalIntegral.integral_Ioi_sub_Ioi hy' hya
    rwa [sub_eq_iff_eq_add'] at h
  have hev : (fun y : ℝ => ∫ t in Set.Ioi y, g t)
      =ᶠ[𝓝 z] (fun y : ℝ => (∫ t in Set.Ioi (max 1 (2 * z)), g t)
        + ∫ t in y..(max 1 (2 * z)), g t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz, Iio_mem_nhds hza] with y hy hya
    exact hsplit y hy (le_of_lt hya)
  -- the derivative of `y ↦ ∫_{Ioi y} g` is `-g z`
  have hII : IntervalIntegrable g volume z (max 1 (2 * z)) := by
    have hcu : ContinuousOn g (Set.uIcc z (max 1 (2 * z))) := by
      rw [Set.uIcc_of_le hza']
      exact hgcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)
    exact hcu.intervalIntegrable
  have hmeas_z : StronglyMeasurableAtFilter g (𝓝 z) volume :=
    ContinuousOn.stronglyMeasurableAtFilter (f := g) (s := Set.Ioi 0) (μ := volume)
      isOpen_Ioi hgcont z hz
  have hcont_z : ContinuousAt g z := hgcont.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hleft : HasDerivAt (fun y : ℝ => ∫ t in y..(max 1 (2 * z)), g t) (-(g z)) z :=
    intervalIntegral.integral_hasDerivAt_left hII hmeas_z hcont_z
  have hfull : HasDerivAt
      (fun y : ℝ => (∫ t in Set.Ioi (max 1 (2 * z)), g t)
        + ∫ t in y..(max 1 (2 * z)), g t) (-(g z)) z :=
    hleft.const_add (∫ t in Set.Ioi (max 1 (2 * z)), g t)
  have hA : HasDerivAt (fun y : ℝ => ∫ t in Set.Ioi y, g t) (-(g z)) z :=
    hfull.congr_of_eventuallyEq hev
  -- product rule for `y ↦ y^p · ∫_{Ioi y} g`
  have hpow : HasDerivAt (fun y : ℝ => y ^ p) (p * z ^ (p - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl (ne_of_gt hz))
  have hprod : HasDerivAt (fun y : ℝ => y ^ p * ∫ t in Set.Ioi y, g t)
      (p * z ^ (p - 1) * (∫ t in Set.Ioi z, g t) + z ^ p * (-(g z))) z := hpow.mul hA
  -- the value of that derivative, rewritten in terms of `Ψ`
  have hval : p * z ^ (p - 1) * (∫ t in Set.Ioi z, g t) + z ^ p * (-(g z))
      = (Work.FTS.PhiStar.RadialWAux.radP α m
          * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z := by
    rw [hsub z hz]
    have hgz : g z = c z * z ^ (-p - 1) := by simp only [hg]
    have h1 : z ^ (p - 1) = z ^ p * z⁻¹ := by
      rw [show p - 1 = p + (-1) from by ring, Real.rpow_add hz, Real.rpow_neg_one]
    have h2 : z ^ p * z ^ (-p - 1) = z⁻¹ := by
      rw [← Real.rpow_add hz, show p + (-p - 1) = -1 from by ring, Real.rpow_neg_one]
    have h4 : z ^ p * (-(c z * z ^ (-p - 1))) = -(c z) * (z ^ p * z ^ (-p - 1)) := by ring
    rw [hgz, h1, h4, h2, div_eq_mul_inv, hp]
    ring
  rw [hval] at hprod
  exact hprod.congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact hsub y hy)

end Work.FTS.EllExist.Honesty
