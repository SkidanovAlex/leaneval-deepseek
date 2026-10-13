import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

/-- The interval integral `∫ x in a..b, g x` tends to the set integral over `[0, π/2]`
as `a → 0⁺` and `b → (π/2)⁻`, for any function `g` integrable on `Set.Icc 0 (π/2)`.

This is the absolute-continuity of the Lebesgue integral applied to the primitive
`y ↦ ∫ x in 0..y, g x`, which is continuous on `[0, π/2]` as soon as `g` is merely
integrable there (`intervalIntegral.continuousOn_primitive_interval`). -/
theorem IntervalIntegralTendstoSetIntegral {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, g x)
      (Filter.comap Prod.fst (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        ⊓ Filter.comap Prod.snd (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
      (nhds (∫ x in Set.Icc 0 (Real.pi / 2), g x)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by positivity
  -- the primitive `y ↦ ∫ x in 0..y, g x` is continuous on the closed interval
  have hcont : ContinuousOn (fun y : ℝ => ∫ x in (0 : ℝ)..y, g x) (Set.Icc 0 (Real.pi / 2)) := by
    have h2 : MeasureTheory.IntegrableOn g (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
      rwa [Set.uIcc_of_le hπ.le]
    have h3 := intervalIntegral.continuousOn_primitive_interval (f := g)
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2) h2
    rwa [Set.uIcc_of_le hπ.le] at h3
  -- the closed interval is a neighbourhood of `0` inside `Ioi 0`, and of `π/2` inside `Iio (π/2)`
  have hmem1 : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds hπ))
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hmem2 : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Iio (Real.pi / 2)) (Ioi_mem_nhds hπ))
      (fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩)
  -- consequently the two coordinates stay in `Icc 0 (π/2)` eventually
  have hev1 : ∀ᶠ p : ℝ × ℝ in
      Filter.comap Prod.fst (nhdsWithin (0 : ℝ) (Set.Ioi 0)), p.1 ∈ Set.Icc 0 (Real.pi / 2) :=
    (Filter.tendsto_comap (f := Prod.fst) (x := nhdsWithin (0 : ℝ) (Set.Ioi 0))).eventually hmem1
  have hev2 : ∀ᶠ p : ℝ × ℝ in
      Filter.comap Prod.snd (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))),
        p.2 ∈ Set.Icc 0 (Real.pi / 2) :=
    (Filter.tendsto_comap (f := Prod.snd) (x := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))).eventually
      hmem2
  -- the primitive tends to its values at the two endpoints
  have htend1 : Filter.Tendsto (fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..p.1, g x)
      (Filter.comap Prod.fst (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (∫ x in (0 : ℝ)..(0 : ℝ), g x)) :=
    (((hcont.continuousWithinAt (by exact ⟨le_refl _, hπ.le⟩)).tendsto).mono_left
        (nhdsWithin_le_of_mem hmem1)).comp
      (Filter.tendsto_comap (f := Prod.fst) (x := nhdsWithin (0 : ℝ) (Set.Ioi 0)))
  have htend2 : Filter.Tendsto (fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..p.2, g x)
      (Filter.comap Prod.snd (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
      (nhds (∫ x in (0 : ℝ)..(Real.pi / 2), g x)) :=
    (((hcont.continuousWithinAt (by exact ⟨hπ.le, le_refl _⟩)).tendsto).mono_left
        (nhdsWithin_le_of_mem hmem2)).comp
      (Filter.tendsto_comap (f := Prod.snd) (x := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
  have hA : Filter.Tendsto
      (fun p : ℝ × ℝ => (∫ x in (0 : ℝ)..p.2, g x) - (∫ x in (0 : ℝ)..p.1, g x))
      (Filter.comap Prod.fst (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        ⊓ Filter.comap Prod.snd (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
      (nhds ((∫ x in (0 : ℝ)..(Real.pi / 2), g x) - (∫ x in (0 : ℝ)..(0 : ℝ), g x))) :=
    (htend2.mono_left inf_le_right).sub (htend1.mono_left inf_le_left)
  have hlim : (∫ x in (0 : ℝ)..(Real.pi / 2), g x) - (∫ x in (0 : ℝ)..(0 : ℝ), g x)
      = ∫ x in Set.Icc 0 (Real.pi / 2), g x := by
    rw [intervalIntegral.integral_same, sub_zero]
    exact (intervalIntegral.integral_of_le hπ.le).trans
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
  -- eventually the signed interval integral equals the difference of the two primitives
  have hEq : (fun p : ℝ × ℝ => ∫ x in p.1..p.2, g x)
      =ᶠ[Filter.comap Prod.fst (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        ⊓ Filter.comap Prod.snd (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))]
      (fun p : ℝ × ℝ => (∫ x in (0 : ℝ)..p.2, g x) - (∫ x in (0 : ℝ)..p.1, g x)) := by
    filter_upwards [hev1.filter_mono inf_le_left, hev2.filter_mono inf_le_right] with p hp1 hp2
    have h1 : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) p.1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hp1.1).mpr
        (hg.mono_set (s := Set.Ioc 0 p.1) (t := Set.Icc 0 (Real.pi / 2))
          (fun x hx => ⟨le_of_lt hx.1, hx.2.trans hp1.2⟩))
    have h2 : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) p.2 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hp2.1).mpr
        (hg.mono_set (s := Set.Ioc 0 p.2) (t := Set.Icc 0 (Real.pi / 2))
          (fun x hx => ⟨le_of_lt hx.1, hx.2.trans hp2.2⟩))
    exact (intervalIntegral.integral_interval_sub_left h2 h1).symm
  rw [hlim] at hA
  exact hA.congr' hEq.symm

end Work.FTS.EllipticEst.Honest
