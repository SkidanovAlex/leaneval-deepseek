import Mathlib
import Submission.Work.Analysis.Poisson.poissonInt_tendsto_of_eventuallyEq

/-!
# The Bouligand datum, and its circle integrability (step 1 of 5)

This module starts the formalisation of the Bouligand globalization described in
`bouligandRecipe.lean` and in `NOTES_globalBarrier_reg_perron_route.md`.

Fix the chart `c` at `p` (`a := c p`) and a radius `ρ` with `Metric.closedBall a ρ ⊆ c.target`
(so that `c.symm` is genuine on the corresponding circle) and `ρ > 0`.  For a level `m > 0` the
**Bouligand datum** on the unit circle is

`bouligandDatum Ω u c a ρ m w = 1` if `c.symm (a + ρ w) ∈ Ω` and `u (c.symm (a + ρ w)) < m`, and
`0` otherwise.

It is the indicator of the "bad set" of the construction: the part of the collar whose chart
preimage lies in `Ω` and where the local barrier `u` is still below the level `m`.  Its three uses
(the recipe) are: its Poisson integral `h_m` is harmonic (needs *circle integrability* — this
module), `h_m(p) = ⨍ g_m` is small (the bad-set measure argument), and `h_m` is `≡ 1` (resp. `≡ 0`)
at the collar points with `u < m` (resp. `u > m`), which is what makes the clamped barrier glue.

The datum is *not* continuous on the circle (it jumps where the sphere leaves `Ω`), so it is not
circle integrable "by continuity".  It is however **bounded** (`0 ≤ g ≤ 1`) and **measurable**:
both defining conditions pull back to Borel sets, because the chart map
`w ↦ c.symm (a + ρ w)` is continuous on the unit sphere (its values lie in `c.target`) and `u` is
continuous on the open set `V` which contains the collar.
-/

open Filter Set MeasureTheory
open Classical
open scoped Topology

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The Bouligand datum** at level `m`: the indicator of the set of points `w` of the circle whose
chart preimage `c.symm (a + ρ w)` lies in `Ω` and satisfies `u < m`. -/
def bouligandDatum (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) :
    ℂ → ℝ :=
  fun w => if c.symm (a + ρ * w) ∈ Ω ∧ u (c.symm (a + ρ * w)) < m then 1 else 0

theorem bouligandDatum_apply (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ)
    (ρ m : ℝ) (w : ℂ) :
    bouligandDatum Ω u c a ρ m w
      = if c.symm (a + ρ * w) ∈ Ω ∧ u (c.symm (a + ρ * w)) < m then 1 else 0 := rfl

/-- The datum is nonnegative. -/
theorem bouligandDatum_nonneg (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ)
    (ρ m : ℝ) (w : ℂ) : 0 ≤ bouligandDatum Ω u c a ρ m w := by
  rw [bouligandDatum_apply]
  by_cases h : c.symm (a + ρ * w) ∈ Ω ∧ u (c.symm (a + ρ * w)) < m <;> simp [h]

/-- The datum is bounded by `1`. -/
theorem bouligandDatum_le_one (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ)
    (ρ m : ℝ) (w : ℂ) : bouligandDatum Ω u c a ρ m w ≤ 1 := by
  rw [bouligandDatum_apply]
  by_cases h : c.symm (a + ρ * w) ∈ Ω ∧ u (c.symm (a + ρ * w)) < m <;> simp [h]

/-- **Step 1 of the Bouligand construction.**  The datum is circle integrable on the unit circle:
it is bounded by `1` and measurable, because the chart map is continuous on the sphere and `u` is
continuous on the open set `V` containing the collar. -/
theorem circleIntegrable_bouligandDatum {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V)
    (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) :
    CircleIntegrable (fun w : ℂ => ((bouligandDatum Ω u c a ρ m w : ℝ) : ℂ)) 0 1 := by
  rw [CircleIntegrable, intervalIntegrable_iff]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc]
        exact ENNReal.ofReal_lt_top⟩
  -- the point map and its basic properties
  set b : ℝ → X := fun θ => c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) with hb
  have hsphere : ∀ θ : ℝ, circleMap (0 : ℂ) 1 θ ∈ Metric.sphere (0 : ℂ) 1 := fun θ =>
    circleMap_mem_sphere 0 zero_le_one θ
  have hnorm_one : ∀ θ : ℝ, ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
    intro θ
    have h := mem_sphere_iff_norm.mp (hsphere θ)
    simpa using h
  have hinner_tgt : ∀ θ : ℝ, a + ρ * circleMap (0 : ℂ) 1 θ ∈ c.target := by
    intro θ
    apply htgt
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit : a + ρ * circleMap (0 : ℂ) 1 θ - a = ρ • circleMap (0 : ℂ) 1 θ := by
      rw [Complex.real_smul]; ring
    rw [hsplit, norm_smul, Real.norm_of_nonneg hρ.le, hnorm_one θ, mul_one]
  have hbcont : Continuous b := by
    rw [continuous_iff_continuousAt]
    intro θ
    have h1 : ContinuousAt (fun w : ℂ => a + ρ * w) (circleMap (0 : ℂ) 1 θ) := by fun_prop
    have h2 : ContinuousAt c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) :=
      c.continuousAt_symm (hinner_tgt θ)
    have h3 := ContinuousAt.comp (x := circleMap (0 : ℂ) 1 θ) (g := c.symm)
      (f := fun w : ℂ => a + ρ * w) h2 h1
    have h4 := ContinuousAt.comp (x := θ) (g := fun w : ℂ => c.symm (a + ρ * w))
      (f := fun θ : ℝ => circleMap (0 : ℂ) 1 θ) h3 (by fun_prop)
    simpa [b, Function.comp_def] using h4
  have hbV : ∀ θ : ℝ, b θ ∈ V := fun θ => hV _ (hsphere θ)
  have hucont : Continuous fun θ : ℝ => u (b θ) := hcont.comp_continuous hbcont hbV
  -- the defining predicate is Borel
  have hP : MeasurableSet {θ : ℝ | b θ ∈ Ω ∧ u (b θ) < m} :=
    ((hΩo.preimage hbcont).inter (isOpen_Iio.preimage hucont)).measurableSet
  -- the datum along the circle, with the coercions pushed inside the `if`
  have hfun : (fun θ : ℝ => ((bouligandDatum Ω u c a ρ m (circleMap (0 : ℂ) 1 θ) : ℝ) : ℂ))
      = fun θ : ℝ => if b θ ∈ Ω ∧ u (b θ) < m then ((1 : ℝ) : ℂ) else 0 := by
    funext θ
    rw [bouligandDatum_apply]
    by_cases h : b θ ∈ Ω ∧ u (b θ) < m <;> simp [h, b]
  rw [hfun]
  refine MeasureTheory.Integrable.of_bound
    (Measurable.aestronglyMeasurable (Measurable.ite hP measurable_const measurable_const)) 1 ?_
  filter_upwards with θ
  split <;> simp


/-! ## Step 2: the bad set shrinks, so the mean of the datum tends to `0`

The mean of the datum at the centre is (by the Poisson mean-value formula `poissonInt_apply_zero`)
the circle average of the datum; the datum is the indicator of the **bad set** in the angle variable
(its points are the collar points in `Ω` where `u < m`), so its average is controlled by the
*measure* of that bad set.  Because `u > 0` on `Ω ∩ V` and the collar lies in `V`, the bad sets
decrease to the empty set as the level decreases along `m = 1/(n+1)`; by continuity from above of a
finite measure, the measures — hence the averages — tend to `0`. -/

/-- The point of the collar corresponding to the angle `θ` on the unit circle. -/
def collarPoint (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (θ : ℝ) : X :=
  c.symm (a + ρ * circleMap (0 : ℂ) 1 θ)

/-- The angle map `θ ↦ collarPoint c a ρ θ` is continuous, as soon as the collar lies in the chart
target (so that `c.symm` is always applied to genuine points). -/
theorem continuous_collarPoint (c : OpenPartialHomeomorph X ℂ) {a : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target) : Continuous (collarPoint c a ρ) := by
  rw [continuous_iff_continuousAt]
  intro θ
  show ContinuousAt (fun θ : ℝ => c.symm (a + ρ * circleMap (0 : ℂ) 1 θ)) θ
  have hnorm : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
    simpa using (mem_sphere_iff_norm.mp (circleMap_mem_sphere 0 zero_le_one θ))
  have hmem : a + ρ * circleMap (0 : ℂ) 1 θ ∈ c.target := by
    apply htgt
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit : a + ρ * circleMap (0 : ℂ) 1 θ - a = ρ • circleMap (0 : ℂ) 1 θ := by
      rw [Complex.real_smul]; ring
    rw [hsplit, norm_smul, Real.norm_of_nonneg hρ, hnorm, mul_one]
  have h1 : ContinuousAt (fun w : ℂ => a + ρ * w) (circleMap (0 : ℂ) 1 θ) := by fun_prop
  have h2 : ContinuousAt c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) := c.continuousAt_symm hmem
  have h3 := ContinuousAt.comp (x := circleMap (0 : ℂ) 1 θ) (g := c.symm)
    (f := fun w : ℂ => a + ρ * w) h2 h1
  have h4 := ContinuousAt.comp (x := θ) (g := fun w : ℂ => c.symm (a + ρ * w))
    (f := fun θ : ℝ => circleMap (0 : ℂ) 1 θ) h3 (by fun_prop)
  simpa [Function.comp_def] using h4

/-- The bad set in the angle variable: the angles whose collar point lies in `Ω` and satisfies
`u < m`. -/
def bouligandBadSet (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) :
    Set ℝ :=
  {θ : ℝ | collarPoint c a ρ θ ∈ Ω ∧ u (collarPoint c a ρ θ) < m}

theorem bouligandBadSet_eq (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ)
    (ρ m : ℝ) :
    bouligandBadSet Ω u c a ρ m
      = {θ : ℝ | c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) ∈ Ω ∧
          u (c.symm (a + ρ * circleMap (0 : ℂ) 1 θ)) < m} := rfl

theorem bouligandDatum_circleMap_eq_indicator (Ω : Set X) (u : X → ℝ)
    (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) (θ : ℝ) :
    bouligandDatum Ω u c a ρ m (circleMap (0 : ℂ) 1 θ)
      = (bouligandBadSet Ω u c a ρ m).indicator (fun _ => (1 : ℝ)) θ := by
  have hiff : (c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) ∈ Ω ∧
        u (c.symm (a + ρ * circleMap (0 : ℂ) 1 θ)) < m)
      ↔ θ ∈ bouligandBadSet Ω u c a ρ m := Iff.rfl
  rw [bouligandDatum_apply]
  by_cases h : θ ∈ bouligandBadSet Ω u c a ρ m
  · rw [if_pos (hiff.mpr h), Set.indicator_of_mem h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), Set.indicator_of_notMem h]

theorem bouligandBadSet_mono (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ)
    (a : ℂ) (ρ : ℝ) : Monotone (bouligandBadSet Ω u c a ρ) := by
  intro m m' hmm' θ hθ
  exact ⟨hθ.1, lt_of_lt_of_le hθ.2 hmm'⟩

theorem measurableSet_bouligandBadSet {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ : ℝ} (hΩo : IsOpen Ω) (hcont : ContinuousOn u V) (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) (m : ℝ) :
    MeasurableSet (bouligandBadSet Ω u c a ρ m) := by
  have hc := continuous_collarPoint c hρ htgt
  have hV' : ∀ θ : ℝ, collarPoint c a ρ θ ∈ V := fun θ =>
    hV _ (circleMap_mem_sphere 0 zero_le_one θ)
  have heq : bouligandBadSet Ω u c a ρ m
      = {θ : ℝ | collarPoint c a ρ θ ∈ Ω} ∩ {θ : ℝ | u (collarPoint c a ρ θ) < m} := rfl
  rw [heq]
  exact ((hΩo.preimage hc).inter (isOpen_Iio.preimage (hcont.comp_continuous hc hV'))).measurableSet

theorem bouligandBadSet_iInter_inter_ioc_eq_empty {Ω V : Set X} {u : X → ℝ}
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) :
    (⋂ n : ℕ, (bouligandBadSet Ω u c a ρ (1 / ((n : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi))) = ∅ := by
  refine Set.subset_empty_iff.mp (fun θ hθ => ?_)
  have h1 : ∀ n : ℕ, collarPoint c a ρ θ ∈ Ω ∧ u (collarPoint c a ρ θ) < 1 / ((n : ℝ) + 1) :=
    fun n => (Set.mem_iInter.mp hθ n).1
  have hΩ : collarPoint c a ρ θ ∈ Ω := (h1 0).1
  have hV' : collarPoint c a ρ θ ∈ V := hV _ (circleMap_mem_sphere 0 zero_le_one θ)
  have hu : 0 < u (collarPoint c a ρ θ) := hpos _ hΩ hV'
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hu
  exact absurd (h1 n).2 (not_lt.mpr hn.le)

theorem tendsto_volume_bouligandBadSet {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ : ℝ} (hΩo : IsOpen Ω) (hcont : ContinuousOn u V) (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x) :
    Filter.Tendsto
      (fun n : ℕ => volume (bouligandBadSet Ω u c a ρ (1 / ((n : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi)))
      Filter.atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ,
      NullMeasurableSet
        (bouligandBadSet Ω u c a ρ (1 / ((n : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi)) volume := fun n =>
    ((measurableSet_bouligandBadSet (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
      hΩo hcont hρ htgt hV _).inter measurableSet_Ioc).nullMeasurableSet
  have hanti : Antitone
      (fun n : ℕ => bouligandBadSet Ω u c a ρ (1 / ((n : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi)) := by
    intro n n' hnn' θ hθ
    have hlt : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : (n : ℝ) ≤ (n' : ℝ) := Nat.cast_le.mpr hnn'
      linarith
    exact ⟨(bouligandBadSet_mono Ω u c a ρ hlt) hθ.1, hθ.2⟩
  have hfin : ∃ n : ℕ,
      volume (bouligandBadSet Ω u c a ρ (1 / ((n : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi)) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun θ hθ => Set.mem_uIoc.mpr (Or.inl ⟨hθ.2.1, hθ.2.2⟩)))
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop hmeas hanti hfin
  have h0 : (⋂ n : ℕ, (bouligandBadSet Ω u c a ρ (1 / ((n : ℝ) + 1)) ∩
      Set.Ioc 0 (2 * Real.pi))) = ∅ := bouligandBadSet_iInter_inter_ioc_eq_empty hpos hV
  rw [h0, measure_empty] at hlim
  simpa [Function.comp_def] using hlim

/-- **The circle average of the datum is the measure of the bad set** (up to the normalisation
`2π`): the datum is the indicator of the bad set along the circle. -/
theorem circleAverage_bouligandDatum_eq {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ : ℝ} (hΩo : IsOpen Ω) (hcont : ContinuousOn u V) (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) (m : ℝ) :
    Real.circleAverage (fun w : ℂ => bouligandDatum Ω u c a ρ m w) 0 1
      = (2 * Real.pi)⁻¹ * (volume (bouligandBadSet Ω u c a ρ m ∩ Set.Ioc 0 (2 * Real.pi))).toReal := by
  have hcongr : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        bouligandDatum Ω u c a ρ m (circleMap (0 : ℂ) 1 θ))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (bouligandBadSet Ω u c a ρ m).indicator (fun _ => (1 : ℝ)) θ := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    exact bouligandDatum_circleMap_eq_indicator Ω u c a ρ m θ
  have hkey : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (bouligandBadSet Ω u c a ρ m).indicator (fun _ => (1 : ℝ)) θ)
      = (volume (bouligandBadSet Ω u c a ρ m ∩ Set.Ioc 0 (2 * Real.pi))).toReal := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      MeasureTheory.setIntegral_indicator
        (measurableSet_bouligandBadSet (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
          hΩo hcont hρ htgt hV m),
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm,
      MeasureTheory.measureReal_def]
  rw [Real.circleAverage, smul_eq_mul, hcongr, hkey]

/-- **Step 2 of the Bouligand construction.**  For every `η > 0` there is a level `m > 0` at which
the circle average of the datum — hence, by the Poisson mean-value formula, the value of its
harmonic extension at the centre `p` — is below `η`. -/
theorem exists_bouligandDatum_circleAverage_lt {Ω V : Set X} {u : X → ℝ}
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hΩo : IsOpen Ω) (hcont : ContinuousOn u V) (hρ : 0 < ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x) :
    ∀ η : ℝ, 0 < η → ∃ m : ℝ, 0 < m ∧
      Real.circleAverage (fun w : ℂ => bouligandDatum Ω u c a ρ m w) 0 1 < η := by
  intro η hη
  have hlim := tendsto_volume_bouligandBadSet (Ω := Ω) (V := V) (u := u) (c := c) (a := a)
    (ρ := ρ) hΩo hcont hρ.le htgt hV hpos
  have hto : (0 : ℝ) < 2 * Real.pi * η := by positivity
  have hev := hlim (isOpen_Iio.mem_nhds (ENNReal.ofReal_pos.mpr hto))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
  rw [circleAverage_bouligandDatum_eq hΩo hcont hρ.le htgt hV]
  have hne : volume (bouligandBadSet Ω u c a ρ (1 / ((N : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi))
      ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (fun θ hθ => Set.mem_uIoc.mpr (Or.inl ⟨hθ.2.1, hθ.2.2⟩)))
  have h1 : (volume (bouligandBadSet Ω u c a ρ (1 / ((N : ℝ) + 1)) ∩
      Set.Ioc 0 (2 * Real.pi))).toReal < 2 * Real.pi * η := by
    have h2 : volume (bouligandBadSet Ω u c a ρ (1 / ((N : ℝ) + 1)) ∩ Set.Ioc 0 (2 * Real.pi))
        < ENNReal.ofReal (2 * Real.pi * η) := hN N le_rfl
    rw [← ENNReal.toReal_ofReal hto.le]
    exact (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr h2
  calc (2 * Real.pi)⁻¹ * (volume (bouligandBadSet Ω u c a ρ (1 / ((N : ℝ) + 1)) ∩
        Set.Ioc 0 (2 * Real.pi))).toReal
      < (2 * Real.pi)⁻¹ * (2 * Real.pi * η) := mul_lt_mul_of_pos_left h1 (by positivity)
    _ = η := by field_simp


/-! ## Step 3: the collar behaviour of the harmonic glue

At a collar point whose corresponding point of `Ω` has `u < m`, the datum is locally the constant
`1` *in the sphere topology* — because the defining predicate `Φ z ∈ Ω ∧ u (Φ z) < m` is the
preimage under the (locally) continuous chart map `Φ` of an **open** subset of `X`.  No
sphere-topology (`arg`) argument is needed: the openness of `{y ∈ Ω : u y < m}` does all the work.
By `poissonInt_tendsto_of_eventuallyEq` the Poisson integral then tends to `1` at that collar point
from inside the disc; symmetrically it tends to `0` where `u > m`. -/

/-- The chart map `w ↦ c.symm (a + ρ w)` is continuous at every point of the unit circle. -/
theorem continuousAt_chartMap (c : OpenPartialHomeomorph X ℂ) {a : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target) (θ : ℝ) :
    ContinuousAt (fun w : ℂ => c.symm (a + ρ * w)) (circleMap (0 : ℂ) 1 θ) := by
  have hnorm : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
    simpa using (mem_sphere_iff_norm.mp (circleMap_mem_sphere 0 zero_le_one θ))
  have hmem : a + ρ * circleMap (0 : ℂ) 1 θ ∈ c.target := by
    apply htgt
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit : a + ρ * circleMap (0 : ℂ) 1 θ - a = ρ • circleMap (0 : ℂ) 1 θ := by
      rw [Complex.real_smul]; ring
    rw [hsplit, norm_smul, Real.norm_of_nonneg hρ, hnorm, mul_one]
  have h1 : ContinuousAt (fun w : ℂ => a + ρ * w) (circleMap (0 : ℂ) 1 θ) := by fun_prop
  exact ContinuousAt.comp (x := circleMap (0 : ℂ) 1 θ) (g := c.symm)
    (f := fun w : ℂ => a + ρ * w) (c.continuousAt_symm hmem) h1

/-- The set of points of `V` where `u < m` is open (only `Ω ∩ V` matters, but this is the form the
collar needs). -/
theorem isOpen_V_inter_lt {V : Set X} {u : X → ℝ} (hVo : IsOpen V) (hcont : ContinuousOn u V)
    (m : ℝ) : IsOpen (V ∩ u ⁻¹' Set.Iio m) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨hxV, hxm⟩ := hx
  exact Filter.inter_mem (hVo.mem_nhds hxV)
    ((hcont.continuousAt (hVo.mem_nhds hxV)).preimage_mem_nhds (isOpen_Iio.mem_nhds hxm))

theorem isOpen_V_inter_gt {V : Set X} {u : X → ℝ} (hVo : IsOpen V) (hcont : ContinuousOn u V)
    (m : ℝ) : IsOpen (V ∩ u ⁻¹' Set.Ioi m) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨hxV, hxm⟩ := hx
  exact Filter.inter_mem (hVo.mem_nhds hxV)
    ((hcont.continuousAt (hVo.mem_nhds hxV)).preimage_mem_nhds (isOpen_Ioi.mem_nhds hxm))

/-- **Collar, below the level**: where `u < m` the datum is eventually `1` in the sphere topology. -/
theorem bouligandDatum_eventually_one {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) (hlt : u (collarPoint c a ρ θ) < m) :
    ∀ᶠ z in 𝓝[Metric.sphere (0 : ℂ) 1] (circleMap (0 : ℂ) 1 θ),
      bouligandDatum Ω u c a ρ m z = 1 := by
  have hmem : c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) ∈
      Ω ∩ (V ∩ u ⁻¹' Set.Iio m) := ⟨hΩ, hV _ (circleMap_mem_sphere 0 zero_le_one θ), hlt⟩
  have hA : IsOpen (Ω ∩ (V ∩ u ⁻¹' Set.Iio m)) :=
    hΩo.inter (isOpen_V_inter_lt (u := u) hVo hcont m)
  have hnb : (fun w : ℂ => c.symm (a + ρ * w)) ⁻¹' (Ω ∩ (V ∩ u ⁻¹' Set.Iio m)) ∈
      𝓝 (circleMap (0 : ℂ) 1 θ) :=
    (continuousAt_chartMap c hρ htgt θ).preimage_mem_nhds (hA.mem_nhds hmem)
  filter_upwards [nhdsWithin_le_nhds hnb] with z hz
  rw [bouligandDatum_apply]
  exact if_pos ⟨hz.1, hz.2.2⟩

/-- **Collar, above the level**: where `u > m` the datum is eventually `0` in the sphere topology. -/
theorem bouligandDatum_eventually_zero {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) (hgt : m < u (collarPoint c a ρ θ)) :
    ∀ᶠ z in 𝓝[Metric.sphere (0 : ℂ) 1] (circleMap (0 : ℂ) 1 θ),
      bouligandDatum Ω u c a ρ m z = 0 := by
  have hmem : c.symm (a + ρ * circleMap (0 : ℂ) 1 θ) ∈
      Ω ∩ (V ∩ u ⁻¹' Set.Ioi m) := ⟨hΩ, hV _ (circleMap_mem_sphere 0 zero_le_one θ), hgt⟩
  have hA : IsOpen (Ω ∩ (V ∩ u ⁻¹' Set.Ioi m)) :=
    hΩo.inter (isOpen_V_inter_gt (u := u) hVo hcont m)
  have hnb : (fun w : ℂ => c.symm (a + ρ * w)) ⁻¹' (Ω ∩ (V ∩ u ⁻¹' Set.Ioi m)) ∈
      𝓝 (circleMap (0 : ℂ) 1 θ) :=
    (continuousAt_chartMap c hρ htgt θ).preimage_mem_nhds (hA.mem_nhds hmem)
  filter_upwards [nhdsWithin_le_nhds hnb] with z hz
  rw [bouligandDatum_apply]
  exact if_neg (fun hcon => absurd hcon.2 (not_lt.mpr hz.2.2.le))

/-- **Collar, below the level (Poisson form).**  At a collar point with `u < m` the Poisson integral
of the datum tends to `1` from inside the disc. -/
theorem poissonInt_bouligandDatum_tendsto_one {Ω V : Set X} {u : X → ℝ}
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V)
    (hcont : ContinuousOn u V) (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) (hlt : u (collarPoint c a ρ θ) < m) :
    Filter.Tendsto
      (fun w : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
        (fun z : ℂ => bouligandDatum Ω u c a ρ m z) 1 w)
      (𝓝[Metric.ball (0 : ℂ) 1] (circleMap (0 : ℂ) 1 θ)) (𝓝 1) := by
  have hx : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
    simpa using (mem_sphere_iff_norm.mp (circleMap_mem_sphere 0 zero_le_one θ))
  exact Work.Analysis.Poisson.poissonInt_tendsto_of_eventuallyEq (r := 1) one_pos
    (circleIntegrable_bouligandDatum (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
      (m := m) hΩo hVo hcont hρ htgt hV) hx
    (bouligandDatum_eventually_one hΩo hVo hcont hρ.le htgt hV hΩ hlt)

/-- **Collar, above the level (Poisson form).**  At a collar point with `u > m` the Poisson integral
of the datum tends to `0` from inside the disc. -/
theorem poissonInt_bouligandDatum_tendsto_zero {Ω V : Set X} {u : X → ℝ}
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V)
    (hcont : ContinuousOn u V) (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) (hgt : m < u (collarPoint c a ρ θ)) :
    Filter.Tendsto
      (fun w : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
        (fun z : ℂ => bouligandDatum Ω u c a ρ m z) 1 w)
      (𝓝[Metric.ball (0 : ℂ) 1] (circleMap (0 : ℂ) 1 θ)) (𝓝 0) := by
  have hx : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
    simpa using (mem_sphere_iff_norm.mp (circleMap_mem_sphere 0 zero_le_one θ))
  exact Work.Analysis.Poisson.poissonInt_tendsto_of_eventuallyEq (r := 1) one_pos
    (circleIntegrable_bouligandDatum (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
      (m := m) hΩo hVo hcont hρ htgt hV) hx
    (bouligandDatum_eventually_zero hΩo hVo hcont hρ.le htgt hV hΩ hgt)

/-! ## Step 4, first move: the chart transport of the collar limits

The harmonic glue of the construction, read on `X` through the chart at `p`, is
`harmonicGlue Ω u c a ρ m x = poissonInt g_m 1 ((c x - a)/ρ)`.  Pushing the ℂ-side limits of step 3
across the chart (`Tendsto.comp` with the chart coordinate, which is continuous at the collar point
and lands in the open unit disc along the chart ball) gives the collar limits for `harmonicGlue`. -/

/-- The harmonic glue on `X`: the Poisson integral of the Bouligand datum, evaluated at the chart
coordinate `(c x - a)/ρ`. -/
def harmonicGlue (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) :
    X → ℝ :=
  fun x => Commons.Analysis.Complex.Harmonic.poissonInt
    (fun z : ℂ => bouligandDatum Ω u c a ρ m z) 1 ((c x - a) / ρ)

/-- The collar point lies in the chart source. -/
theorem collarPoint_mem_source (c : OpenPartialHomeomorph X ℂ) {a : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target) (θ : ℝ) :
    collarPoint c a ρ θ ∈ c.source :=
  (c.symm).map_source (htgt (by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
      simpa using (mem_sphere_iff_norm.mp (circleMap_mem_sphere 0 zero_le_one θ))
    have hsplit : a + ρ * circleMap (0 : ℂ) 1 θ - a = ρ • circleMap (0 : ℂ) 1 θ := by
      rw [Complex.real_smul]; ring
    rw [hsplit, norm_smul, Real.norm_of_nonneg hρ, hnorm, mul_one]))

/-- The chart coordinate of the collar point is the corresponding point of the unit circle. -/
theorem chart_collarPoint (c : OpenPartialHomeomorph X ℂ) {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target) (θ : ℝ) :
    (c (collarPoint c a ρ θ) - a) / ρ = circleMap (0 : ℂ) 1 θ := by
  have hmem : a + ρ * circleMap (0 : ℂ) 1 θ ∈ c.target := by
    apply htgt
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by
      simpa using (mem_sphere_iff_norm.mp (circleMap_mem_sphere 0 zero_le_one θ))
    have hsplit : a + ρ * circleMap (0 : ℂ) 1 θ - a = ρ • circleMap (0 : ℂ) 1 θ := by
      rw [Complex.real_smul]; ring
    rw [hsplit, norm_smul, Real.norm_of_nonneg hρ.le, hnorm, mul_one]
  have h1 : c (collarPoint c a ρ θ) = a + ρ * circleMap (0 : ℂ) 1 θ := by
    show c (c.symm (a + ρ * circleMap (0 : ℂ) 1 θ)) = a + ρ * circleMap (0 : ℂ) 1 θ
    exact c.right_inv hmem
  rw [h1, add_sub_cancel_left]
  have hρne : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  field_simp

/-- The chart ball of radius `ρ` about `a` (a local copy of the workspace's `Submission.chartBall`,
so that this module stays independent of the `Submission` layer). -/
def chartBallC (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : Set X :=
  {x : X | x ∈ c.source ∧ ‖c x - a‖ < ρ}

/-- The chart coordinate `x ↦ (c x - a)/ρ` tends, along the chart ball, to the point of the unit
circle corresponding to the collar point. -/
theorem tendsto_chartCoord {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {ξ : X} (hξ : ξ ∈ c.source) {θ : ℝ} (hval : (c ξ - a) / ρ = circleMap (0 : ℂ) 1 θ) :
    Filter.Tendsto (fun x : X => (c x - a) / ρ) (𝓝[chartBallC c a ρ] ξ)
      (𝓝[Metric.ball (0 : ℂ) 1] (circleMap (0 : ℂ) 1 θ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h1 : ContinuousAt (fun x : X => (c x - a) / ρ) ξ :=
      ((c.continuousAt hξ).sub_const a).div_const ρ
    have hT : Filter.Tendsto (fun x : X => (c x - a) / ρ) (𝓝 ξ) (𝓝 ((c ξ - a) / ρ)) := h1.tendsto
    rw [hval] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : ‖c x - a‖ < ρ := hx.2
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hnorm : ‖(c x - a) / ρ‖ = ‖c x - a‖ / ρ := by
      rw [norm_div]
      have hρc : ‖((ρ : ℝ) : ℂ)‖ = ρ := by simp [abs_of_pos hρ]
      rw [hρc]
    rw [hnorm, div_lt_one hρ]
    exact hx'

/-- **Chart transport of the collar limit (below the level).**  Along `Ω` near the collar point,
the harmonic glue tends to `1`. -/
theorem harmonicGlue_tendsto_one {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 < ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) (hlt : u (collarPoint c a ρ θ) < m) :
    Filter.Tendsto (harmonicGlue Ω u c a ρ m) (𝓝[chartBallC c a ρ] (collarPoint c a ρ θ))
      (𝓝 1) := by
  have hlim := poissonInt_bouligandDatum_tendsto_one (Ω := Ω) (V := V) (u := u) (c := c) (a := a)
    (ρ := ρ) (m := m) hΩo hVo hcont hρ htgt hV hΩ hlt
  have htrans := tendsto_chartCoord (c := c) (a := a) (ρ := ρ) hρ
    (collarPoint_mem_source c hρ.le htgt θ) (chart_collarPoint c hρ htgt θ)
  exact hlim.comp htrans

/-- **Chart transport of the collar limit (above the level).**  Along `Ω` near the collar point,
the harmonic glue tends to `0`. -/
theorem harmonicGlue_tendsto_zero {Ω V : Set X} {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ m : ℝ} (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 < ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) (hgt : m < u (collarPoint c a ρ θ)) :
    Filter.Tendsto (harmonicGlue Ω u c a ρ m) (𝓝[chartBallC c a ρ] (collarPoint c a ρ θ))
      (𝓝 0) := by
  have hlim := poissonInt_bouligandDatum_tendsto_zero (Ω := Ω) (V := V) (u := u) (c := c) (a := a)
    (ρ := ρ) (m := m) hΩo hVo hcont hρ htgt hV hΩ hgt
  have htrans := tendsto_chartCoord (c := c) (a := a) (ρ := ρ) hρ
    (collarPoint_mem_source c hρ.le htgt θ) (chart_collarPoint c hρ htgt θ)
  exact hlim.comp htrans

/-- **Nonnegativity of the Poisson integral.**  A nonnegative circle-integrable datum has
nonnegative Poisson integral inside the disc (the kernel is nonnegative there). -/
theorem poissonInt_nonneg {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : CircleIntegrable g 0 r)
    (hg0 : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) |r| → 0 ≤ g z) {w : ℂ} (hw : ‖w‖ < r) :
    0 ≤ Commons.Analysis.Complex.Harmonic.poissonInt g r w := by
  rw [Commons.Analysis.Complex.Harmonic.poissonInt]
  have hzr : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) |r| → ‖z‖ = r := by
    intro z hz
    have h := mem_sphere_iff_norm.mp hz
    rwa [sub_zero, abs_of_pos hr] at h
  have hk : CircleIntegrable (fun z : ℂ => poissonKernel 0 w z * g z) 0 r :=
    hg.continuousOn_mul
      (Commons.Analysis.Complex.Harmonic.continuousOn_poissonKernel_sphere_r
        (by rwa [abs_of_pos hr] : ‖w‖ < |r|))
  have h0 : CircleIntegrable (fun _ : ℂ => (0 : ℝ)) 0 r :=
    (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) (Metric.sphere (0 : ℂ) |r|)).circleIntegrable'
  refine le_trans (le_of_eq (Real.circleAverage_const (0 : ℝ) 0 r).symm)
    (Real.circleAverage_mono h0 hk ?_)
  intro z hz
  exact mul_nonneg
    (Commons.Analysis.Complex.Harmonic.poissonKernel_pos_r hw (hzr z hz)) (hg0 z hz)

/-- **The collar inequality.**  With the *clamp* level `m` strictly below the *bad-set* level `δ`,
the glued function `u(·)/m + harmonicGlue` is `≥ 1` eventually near every collar point of `Ω`.
Three cases: `u ξ < δ` (the glue tends to `1`), `δ < u ξ` (the glue tends to `0` while `u ξ/m > 1`),
and `u ξ = δ` (`u ξ/m = δ/m > 1` while the glue is nonnegative). -/
theorem one_le_u_div_add_harmonicGlue {Ω V : Set X} {u : X → ℝ}
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ δ m : ℝ}
    (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 < ρ) (hm0 : 0 < m)
    (hmδ : m < δ) (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V)
    {θ : ℝ} (hΩ : collarPoint c a ρ θ ∈ Ω) :
    ∀ᶠ x in 𝓝[chartBallC c a ρ] (collarPoint c a ρ θ),
      1 ≤ u x / m + harmonicGlue Ω u c a ρ δ x := by
  set ξ := collarPoint c a ρ θ with hξdef
  have hξV : ξ ∈ V := hV _ (circleMap_mem_sphere 0 zero_le_one θ)
  have hξpos : 0 < u ξ := hpos ξ hΩ hξV
  have huclim : Filter.Tendsto u (𝓝[chartBallC c a ρ] ξ) (𝓝 (u ξ)) :=
    ((hcont.continuousAt (hVo.mem_nhds hξV)).tendsto).mono_left nhdsWithin_le_nhds
  rcases lt_trichotomy (u ξ) δ with hlt | heq | hgt
  · -- below the bad-set level: the glue tends to `1`
    have hglue := harmonicGlue_tendsto_one (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
      (m := δ) hΩo hVo hcont hρ htgt hV hΩ hlt
    have hsum : Filter.Tendsto (fun x : X => u x / m + harmonicGlue Ω u c a ρ δ x)
        (𝓝[chartBallC c a ρ] ξ) (𝓝 (u ξ / m + 1)) :=
      (huclim.div_const m).add hglue
    have h1 : 1 < u ξ / m + 1 := by
      have : 0 < u ξ / m := div_pos hξpos hm0
      linarith
    exact (hsum.eventually (isOpen_Ioi.mem_nhds h1)).mono (fun x hx => hx.le)
  · -- on the bad-set level: the glue is nonnegative and `u ξ/m = δ/m > 1`
    have hratio : 1 < u ξ / m := by
      rw [heq, lt_div_iff₀ hm0, one_mul]; exact hmδ
    have hucl : ∀ᶠ x in 𝓝[chartBallC c a ρ] ξ, 1 < u x / m :=
      (huclim.div_const m).eventually (isOpen_Ioi.mem_nhds hratio)
    have hnn : ∀ᶠ x in 𝓝[chartBallC c a ρ] ξ, 0 ≤ harmonicGlue Ω u c a ρ δ x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxw : ‖(c x - a) / ρ‖ < 1 := by
        have hnorm : ‖(c x - a) / ρ‖ = ‖c x - a‖ / ρ := by
          rw [norm_div]
          have hρc : ‖((ρ : ℝ) : ℂ)‖ = ρ := by simp [abs_of_pos hρ]
          rw [hρc]
        rw [hnorm, div_lt_one hρ]
        exact hx.2
      exact poissonInt_nonneg one_pos
        (Work.Analysis.Poisson.circleIntegrable_of_ofReal
          (circleIntegrable_bouligandDatum (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
            (m := δ) hΩo hVo hcont hρ htgt hV))
        (fun z _ => bouligandDatum_nonneg Ω u c a ρ δ z) hxw
    filter_upwards [hucl, hnn] with x h1 h2
    linarith
  · -- above the bad-set level: the glue tends to `0`
    have hglue := harmonicGlue_tendsto_zero (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ)
      (m := δ) hΩo hVo hcont hρ htgt hV hΩ hgt
    have hsum : Filter.Tendsto (fun x : X => u x / m + harmonicGlue Ω u c a ρ δ x)
        (𝓝[chartBallC c a ρ] ξ) (𝓝 (u ξ / m + 0)) := (huclim.div_const m).add hglue
    have h1 : 1 < u ξ / m + 0 := by
      rw [add_zero, lt_div_iff₀ hm0]
      simpa using lt_trans hmδ hgt
    exact (hsum.eventually (isOpen_Ioi.mem_nhds h1)).mono (fun x hx => hx.le)

/-- **The unit circle is the range of `circleMap 0 1`.**  Needed to identify an arbitrary point of
the collar `frontier (chartBallC c a ρ)` with some `collarPoint c a ρ θ` in the three-case assembly.
Proof: `θ := arg z` and `Complex.norm_mul_exp_arg_mul_I` with `‖z‖ = 1`. -/
theorem circleMap_eq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ : ℝ, circleMap (0 : ℂ) 1 θ = z := by
  refine ⟨Complex.arg z, ?_⟩
  have h : Complex.exp (Complex.arg z * Complex.I) = z := by
    have h1 := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at h1
    simpa using h1
  rw [circleMap, zero_add]
  simpa using h


end Work.SimplyConnected.ABS
