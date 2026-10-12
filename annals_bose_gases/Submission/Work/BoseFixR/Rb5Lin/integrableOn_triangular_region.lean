import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.integrableOn_triangular_region`

If `r ↦ r ^ 2 * ψ r` is integrable on `(0, ∞)`, then the plane integrand
`p ↦ p.2 * ψ p.2 * cos (c * p.1)` is integrable on the triangular region
`{p : ℝ × ℝ | |p.1| < p.2}`.

Nothing is assumed about `ψ` itself — in particular no measurability.  The proof
is a Tonelli/Fubini computation on the horizontal fibres: for `y > 0` the fibre
`{x | |x| < y}` has length `2 * y`, so that

  `∫_{|x| < y} ‖y * ψ y * cos (c * x)‖ₑ dx ≤ 2 * y * ‖y * ψ y‖ₑ = 2 * ‖y ^ 2 * ψ y‖ₑ`,

and integrating the (finite) right hand side over `y > 0` is exactly the
hypothesis.  Because the hypothesis only gives a.e. measurability of
`r ↦ r ^ 2 * ψ r` on `(0, ∞)`, the argument first replaces it by an a.e. equal
*strongly measurable* representative `m` and works with
`p ↦ p.2⁻¹ * m p.2 * cos (c * p.1)`, which agrees with the original integrand
on the region (where `p.2 ≠ 0`), then transfers integrability back by a.e.
equality.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.Rb5Lin

/-- The triangular region `{|x| < y}` is open, hence measurable. -/
private lemma measurableSet_triangular_region :
    MeasurableSet {p : ℝ × ℝ | |p.1| < p.2} := by
  have h1 : Continuous (fun p : ℝ × ℝ => |p.1|) := by fun_prop
  have h2 : Continuous (fun p : ℝ × ℝ => p.2) := by fun_prop
  exact (isOpen_lt h1 h2).measurableSet

/-- **The Tonelli bound.**  For a measurable `m` and any `c`,
`∫⁻_{(x,y) : |x| < y} ‖y⁻¹ m y cos (c x)‖ₑ ≤ 2 ∫⁻_{y > 0} ‖m y‖ₑ`.

For a fixed `y > 0` the inner integral over `x` is at most
`‖y⁻¹ m y‖ₑ * vol (Ioo (-y) y) = ‖y⁻¹ m y‖ₑ * ofReal (2 y) = 2 ‖m y‖ₑ`,
and for `y ≤ 0` the fibre is empty. -/
private lemma lintegral_indicator_triangular_le_aux {m : ℝ → ℝ} {c : ℝ} (hm : Measurable m) :
    (∫⁻ p : ℝ × ℝ,
        ({p : ℝ × ℝ | |p.1| < p.2}.indicator
          (fun q : ℝ × ℝ => ‖q.2⁻¹ * m q.2 * Real.cos (c * q.1)‖ₑ) p))
      ≤ 2 * ∫⁻ y in Set.Ioi (0 : ℝ), ‖m y‖ₑ := by
  set A : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.1| < p.2} with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_triangular_region
  set g : ℝ × ℝ → ENNReal :=
    A.indicator (fun q : ℝ × ℝ => ‖q.2⁻¹ * m q.2 * Real.cos (c * q.1)‖ₑ) with hg
  have hgmeas : Measurable g := by
    rw [hg]
    apply Measurable.indicator _ hAmeas
    have h3 : Measurable (fun q : ℝ × ℝ => q.2⁻¹ * m q.2 * Real.cos (c * q.1)) := by
      refine ((measurable_snd.inv).mul ?_).mul ?_
      · exact hm.comp measurable_snd
      · fun_prop
    exact h3.enorm
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      MeasureTheory.lintegral_prod_symm (f := g) hgmeas.aemeasurable]
  have hpt : ∀ x y : ℝ, g (x, y) ≤ (Set.Ioo (-y) y).indicator (fun _ => ‖y⁻¹ * m y‖ₑ) x := by
    intro x y
    by_cases hx : |x| < y
    · have hmem : (x, y) ∈ A := by rw [hA]; exact hx
      have hxmem : x ∈ Set.Ioo (-y) y := Set.mem_Ioo.mpr (abs_lt.mp hx)
      rw [hg, Set.indicator_of_mem hmem, Set.indicator_of_mem hxmem]
      have : ‖y⁻¹ * m y * Real.cos (c * x)‖ₑ ≤ ‖y⁻¹ * m y‖ₑ := by
        calc ‖y⁻¹ * m y * Real.cos (c * x)‖ₑ
            = ‖y⁻¹ * m y‖ₑ * ‖Real.cos (c * x)‖ₑ := enorm_mul _ _
          _ ≤ ‖y⁻¹ * m y‖ₑ * 1 := by
              gcongr
              rw [Real.enorm_eq_ofReal_abs]
              exact (ENNReal.ofReal_le_one).mpr (Real.abs_cos_le_one _)
          _ = ‖y⁻¹ * m y‖ₑ := mul_one _
      simpa using this
    · have hmem : (x, y) ∉ A := by rw [hA]; exact hx
      have hxmem : x ∉ Set.Ioo (-y) y := fun h => hx (abs_lt.mpr (Set.mem_Ioo.mp h))
      rw [hg, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hxmem]
  have hinner : ∀ y : ℝ,
      (∫⁻ x, g (x, y)) ≤ (Set.Ioi (0 : ℝ)).indicator (fun y => 2 * ‖m y‖ₑ) y := by
    intro y
    calc ∫⁻ x, g (x, y)
        ≤ ∫⁻ x, (Set.Ioo (-y) y).indicator (fun _ => ‖y⁻¹ * m y‖ₑ) x :=
          lintegral_mono (fun x => hpt x y)
      _ = ‖y⁻¹ * m y‖ₑ * volume (Set.Ioo (-y) y) := lintegral_indicator_const measurableSet_Ioo _
      _ ≤ (Set.Ioi (0 : ℝ)).indicator (fun y => 2 * ‖m y‖ₑ) y := by
          rw [Real.volume_Ioo]
          by_cases hy : 0 < y
          · rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from hy)]
            have harith : ‖y⁻¹ * m y‖ₑ * ENNReal.ofReal (y - (-y)) = 2 * ‖m y‖ₑ := by
              have h1 : ‖y⁻¹ * m y‖ₑ = ENNReal.ofReal y⁻¹ * ‖m y‖ₑ := by
                rw [enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hy.le)]
              have h2 : y - (-y) = 2 * y := by ring
              rw [h2, h1, mul_assoc, mul_comm (‖m y‖ₑ) (ENNReal.ofReal (2 * y)), ← mul_assoc,
                ← ENNReal.ofReal_mul (inv_nonneg.mpr hy.le)]
              have hy0 : y ≠ 0 := ne_of_gt hy
              rw [show y⁻¹ * (2 * y) = 2 by
                    calc y⁻¹ * (2 * y) = 2 * (y⁻¹ * y) := by ring
                      _ = 2 * 1 := by rw [inv_mul_cancel₀ hy0]
                      _ = 2 := by ring]
              norm_num
            rw [harith]
          · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi (0 : ℝ) from hy)]
            have h2y : y - (-y) ≤ 0 := by linarith [not_lt.mp hy]
            rw [ENNReal.ofReal_eq_zero.mpr h2y, mul_zero]
  calc ∫⁻ y, ∫⁻ x, g (x, y)
      ≤ ∫⁻ y, (Set.Ioi (0 : ℝ)).indicator (fun y => 2 * ‖m y‖ₑ) y := lintegral_mono hinner
    _ = ∫⁻ y in Set.Ioi (0 : ℝ), 2 * ‖m y‖ₑ := lintegral_indicator measurableSet_Ioi _
    _ = 2 * ∫⁻ y in Set.Ioi (0 : ℝ), ‖m y‖ₑ := lintegral_const_mul 2 hm.enorm

/-- **The a.e. transfer.**  On the triangular region `{|x| < y}` (where always
`y ≠ 0`) the function `p ↦ p.2⁻¹ * m p.2 * cos (c * p.1)` agrees with
`p ↦ p.2 * ψ p.2 * cos (c * p.1)` as soon as `m` agrees with `r ↦ r ^ 2 * ψ r`
a.e. on `(0, ∞)`: the exceptional set is `A ∩ (ℝ × N)` with `N` a null subset
of `(0, ∞)`. -/
private lemma ae_eq_triangular_integrand_aux {ψ : ℝ → ℝ} {c : ℝ} {m : ℝ → ℝ}
    (hm : (fun r : ℝ => r ^ 2 * ψ r) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] m) :
    (fun p : ℝ × ℝ => p.2⁻¹ * m p.2 * Real.cos (c * p.1))
      =ᵐ[MeasureTheory.volume.restrict {p : ℝ × ℝ | |p.1| < p.2}]
      (fun p : ℝ × ℝ => p.2 * ψ p.2 * Real.cos (c * p.1)) := by
  set A : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.1| < p.2} with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_triangular_region
  let N : Set ℝ := {r : ℝ | m r ≠ (fun r : ℝ => r ^ 2 * ψ r) r}
  have hN : volume (N ∩ Set.Ioi (0 : ℝ)) = 0 := by
    have h := MeasureTheory.ae_iff.mp hm
    rw [Measure.restrict_apply' measurableSet_Ioi] at h
    rwa [show {r : ℝ | ¬ ((fun r : ℝ => r ^ 2 * ψ r) r = m r)} ∩ Set.Ioi (0 : ℝ)
          = N ∩ Set.Ioi (0 : ℝ) by
        congr 1
        ext r
        simp only [N, Set.mem_ofPred_eq, ne_eq, eq_comm]] at h
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  rw [Measure.restrict_apply' hAmeas]
  apply le_antisymm
  · calc volume ({p : ℝ × ℝ | ¬ ((fun p : ℝ × ℝ => p.2⁻¹ * m p.2 * Real.cos (c * p.1)) p
              = (fun p : ℝ × ℝ => p.2 * ψ p.2 * Real.cos (c * p.1)) p)} ∩ A)
        ≤ volume (Set.univ ×ˢ (N ∩ Set.Ioi (0 : ℝ))) := by
          apply measure_mono
          intro p hp
          obtain ⟨hpS, hpA⟩ := hp
          have hy0 : 0 < p.2 := lt_of_le_of_lt (abs_nonneg p.1) hpA
          refine ⟨trivial, ?_, hy0⟩
          intro hmm
          apply hpS
          have hy : p.2 ≠ 0 := ne_of_gt hy0
          have h1 : p.2⁻¹ * ((fun r : ℝ => r ^ 2 * ψ r) p.2) = p.2 * ψ p.2 := by
            calc p.2⁻¹ * ((fun r : ℝ => r ^ 2 * ψ r) p.2)
                = (p.2⁻¹ * p.2 ^ 2) * ψ p.2 := by ring
              _ = p.2 * ψ p.2 := by
                  rw [show p.2⁻¹ * p.2 ^ 2 = p.2 by
                        calc p.2⁻¹ * p.2 ^ 2 = (p.2⁻¹ * p.2) * p.2 := by ring
                          _ = 1 * p.2 := by rw [inv_mul_cancel₀ hy]
                          _ = p.2 := one_mul _]
          simp only []
          rw [hmm, h1]
      _ = volume Set.univ * volume (N ∩ Set.Ioi (0 : ℝ)) := Measure.prod_prod _ _
      _ = 0 := by rw [hN, mul_zero]
  · exact zero_le

theorem integrableOn_triangular_region {ψ : ℝ → ℝ} {c : ℝ}
    (h : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * ψ r) (Set.Ioi (0 : ℝ)) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.2 * ψ p.2 * Real.cos (c * p.1))
      {p : ℝ × ℝ | |p.1| < p.2} MeasureTheory.volume := by
  -- an a.e. equal strongly measurable representative of `r ↦ r ^ 2 * ψ r`
  obtain ⟨m, hm_strong, hm_ae⟩ := h.1
  have hm_meas : Measurable m := hm_strong.measurable
  have hA : MeasurableSet {p : ℝ × ℝ | |p.1| < p.2} := measurableSet_triangular_region
  -- the strongly measurable replacement of the integrand
  set F' : ℝ × ℝ → ℝ := fun p => p.2⁻¹ * m p.2 * Real.cos (c * p.1) with hF'def
  have hF'_strong : StronglyMeasurable F' := by
    rw [hF'def]
    have h1 : StronglyMeasurable (fun p : ℝ × ℝ => p.2⁻¹) :=
      (measurable_snd.inv).stronglyMeasurable
    have h2 : StronglyMeasurable (fun p : ℝ × ℝ => m p.2) :=
      hm_strong.comp_measurable measurable_snd
    have h3 : StronglyMeasurable (fun p : ℝ × ℝ => Real.cos (c * p.1)) := by
      have : Continuous (fun p : ℝ × ℝ => Real.cos (c * p.1)) := by fun_prop
      exact this.stronglyMeasurable
    exact (h1.mul h2).mul h3
  have hF'_aesm : AEStronglyMeasurable F' (volume.restrict {p : ℝ × ℝ | |p.1| < p.2}) :=
    hF'_strong.aestronglyMeasurable
  -- the finite integral bound
  have hP2' : (∫⁻ p, ‖F' p‖ₑ ∂(volume.restrict {p : ℝ × ℝ | |p.1| < p.2}))
      ≤ 2 * ∫⁻ y in Set.Ioi (0 : ℝ), ‖m y‖ₑ := by
    rw [← MeasureTheory.lintegral_indicator hA (fun p : ℝ × ℝ => ‖F' p‖ₑ)]
    show (∫⁻ p : ℝ × ℝ, ({p : ℝ × ℝ | |p.1| < p.2}.indicator
        (fun q : ℝ × ℝ => ‖q.2⁻¹ * m q.2 * Real.cos (c * q.1)‖ₑ) p)) ≤ _
    exact lintegral_indicator_triangular_le_aux hm_meas
  have hfin : HasFiniteIntegral F' (volume.restrict {p : ℝ × ℝ | |p.1| < p.2}) := by
    have hnorm : (fun y : ℝ => ‖m y‖ₑ) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun y : ℝ => ‖(fun r : ℝ => r ^ 2 * ψ r) y‖ₑ) := by
      filter_upwards [hm_ae] with y hy
      rw [hy]
    have h3 : (2 : ENNReal) * ∫⁻ y in Set.Ioi (0 : ℝ), ‖m y‖ₑ < ⊤ := by
      rw [MeasureTheory.lintegral_congr_ae hnorm]
      exact ENNReal.mul_lt_top (by norm_num) h.2
    exact lt_of_le_of_lt hP2' h3
  have hF'_int : Integrable F' (volume.restrict {p : ℝ × ℝ | |p.1| < p.2}) :=
    ⟨hF'_aesm, hfin⟩
  -- transfer back by a.e. equality
  have hae : F' =ᵐ[volume.restrict {p : ℝ × ℝ | |p.1| < p.2}]
      (fun p : ℝ × ℝ => p.2 * ψ p.2 * Real.cos (c * p.1)) :=
    ae_eq_triangular_integrand_aux hm_ae
  exact hF'_int.congr hae

end Work.BoseFixR.Rb5Lin
