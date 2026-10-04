import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Man.Sect

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint measurability of the component family `(s, z) ↦ D.R i (vs s) a b z`

`Work.Diff.STE.Lead.aemeasurable_uncurry_R_vs` is the measurability input of
`Work.Diff.STE.Lead.norm_integral_mul_sub_le_of_hasDerivAt`: it says that the uncurried function
`(s, z) ↦ D.R i (vs s) a b z` is `AEMeasurable` for the product of the restriction of Lebesgue
measure to `[0, τ]` with the restriction of Lebesgue measure to the centred cube `(-1/2, 1/2]^n`.

## Route

Write `G(σ, z) := D.R i (u σ) a b z` and `F(σ, z) := D.R i (vs σ) a b z`.  The hypothesis `hode`
says that for every fixed `z` the function `σ ↦ G(σ, z)` has (one-sided) derivative `F(s, z)` at
every `s ∈ Icc 0 τ`.  Note that `vs` is *determined* by `u` through this derivative, so it carries
no regularity of its own: everything has to come from `hode` and from the spatial smoothness
`hCDu : ∀ t, ChartData (u t)`.

* For each fixed `t ∈ ℝ`, `hCDu t` together with `Work.Diff.STE.B3.R_contDiff_of_chartData` gives
  that `z ↦ G(t, z)` is `C^∞`, hence measurable.
* For each fixed `z`, `hode` gives that `σ ↦ G(σ, z)` is continuous on `Icc 0 τ` (a within
  derivative implies within continuity), hence continuous on all of `ℝ` after clamping `σ` to
  `Icc 0 τ` (the clamp is used only inside `u`, i.e. in the definition of the auxiliary function;
  on `Icc 0 τ` it is the identity, so nothing is lost in the difference quotients).

The classical Carathéodory lemma (`caratheodory_measurable_aux`, proved below from scratch) turns
"continuous in the first variable, measurable in the second" into joint measurability, so `G` is
jointly measurable.  The parameter derivative is then the a.e. limit of the measurable difference
quotients `n ↦ ((n : ℝ) + 1) * (G(s + 1 / ((n : ℝ) + 1), z) − G(s, z))` on `[0, τ] × Z`
(`aemeasurable_uncurry_of_hasDerivWithinAt_aux`): the exceptional set is `{τ}`, which is null for
the restricted Lebesgue measure on `[0, τ]`, and off it the difference quotients converge by
`HasDerivAt.tendsto_slope_zero`.

The two general lemmas above are independent of the Layer B3 vocabulary and are proved here, so
that the file is self-contained.
-/

noncomputable section

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 4000000

/-! ## Two general measurability lemmas -/

/-- The dyadic-rational approximation of the identity
`t ↦ ((⌊((n : ℝ) + 1) * t⌋ : ℤ) : ℝ) / ((n : ℝ) + 1)` (from below, with error `≤ 1/(n+1)`). -/
private def approxByFloor (n : ℕ) (t : ℝ) : ℝ :=
  ((⌊((n : ℝ) + 1) * t⌋ : ℤ) : ℝ) / ((n : ℝ) + 1)

/-- **Carathéodory's joint measurability lemma.**  A function of two variables which is continuous
in the first variable and measurable in the second is jointly measurable.  Here `f` is a function
`ℝ → Z → ℝ`: `ℝ` is second countable, which is what makes the argument work. -/
theorem caratheodory_measurable_aux {Z : Type*} [MeasurableSpace Z] {f : ℝ → Z → ℝ}
    (hc : ∀ z : Z, Continuous (fun t : ℝ => f t z))
    (hm : ∀ t : ℝ, Measurable (fun z : Z => f t z)) :
    Measurable (fun p : ℝ × Z => f p.1 p.2) := by
  -- the `ℤ`-indexed version: for a countable (discrete) index type, separate measurability of the
  -- sections gives joint measurability
  have key : ∀ (g : ℤ → Z → ℝ), (∀ k, Measurable (g k)) →
      Measurable (fun p : ℤ × Z => g p.1 p.2) := by
    intro g hg s hs
    have hEq : (fun p : ℤ × Z => g p.1 p.2) ⁻¹' s
        = ⋃ k : ℤ, ({k} : Set ℤ) ×ˢ (g k ⁻¹' s) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro hp; exact ⟨p.1, rfl, hp⟩
      · rintro ⟨k, hk, hp⟩; rw [hk]; exact hp
    rw [hEq]
    exact MeasurableSet.iUnion fun k =>
      MeasurableSet.prod (measurableSet_singleton k) (MeasurableSet.preimage hs (hg k))
  -- the lattice-rational step functions `approxByFloor n` are measurable and converge to the
  -- identity, so the measurable functions `p ↦ f (approxByFloor n p.1) p.2` converge pointwise
  have hstep : ∀ n : ℕ, Measurable (fun p : ℝ × Z => f (approxByFloor n p.1) p.2) := by
    intro n
    have hfloor : Measurable (fun p : ℝ × Z => (⌊((n : ℝ) + 1) * p.1⌋ : ℤ)) :=
      Int.measurable_floor.comp (measurable_const.mul measurable_fst)
    have hpair : Measurable (fun p : ℝ × Z => ((⌊((n : ℝ) + 1) * p.1⌋ : ℤ), p.2)) := by
      refine Measurable.prod ?_ measurable_snd
      exact hfloor
    have h3 : Measurable (fun q : ℤ × Z => f ((q.1 : ℝ) / ((n : ℝ) + 1)) q.2) :=
      key (fun k z => f ((k : ℝ) / ((n : ℝ) + 1)) z) (fun k => hm _)
    have h4 := h3.comp hpair
    have h4' : Measurable
        (fun p : ℝ × Z => f (((⌊((n : ℝ) + 1) * p.1⌋ : ℤ) : ℝ) / ((n : ℝ) + 1)) p.2) :=
      h4
    simpa only [approxByFloor] using h4'
  refine measurable_of_tendsto_metrizable (f := fun n p => f (approxByFloor n p.1) p.2) hstep ?_
  rw [tendsto_pi_nhds]
  intro p
  have hq : Filter.Tendsto (fun n : ℕ => approxByFloor n p.1) Filter.atTop (nhds p.1) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (g := fun n : ℕ => 1 / ((n : ℝ) + 1))
        (fun n => norm_nonneg (approxByFloor n p.1 - p.1)) (fun n => ?_) ?_)
    · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hfloorle := Int.floor_le (((n : ℝ) + 1) * p.1)
      have hfloorlt := Int.lt_floor_add_one (((n : ℝ) + 1) * p.1)
      have hle : approxByFloor n p.1 ≤ p.1 := by
        simp only [approxByFloor]
        rw [div_le_iff₀ hpos]
        calc ((⌊((n : ℝ) + 1) * p.1⌋ : ℤ) : ℝ) ≤ ((n : ℝ) + 1) * p.1 := hfloorle
          _ = p.1 * ((n : ℝ) + 1) := by ring
      have hlt : p.1 < approxByFloor n p.1 + 1 / ((n : ℝ) + 1) := by
        have h2 : p.1 * ((n : ℝ) + 1) < ((⌊((n : ℝ) + 1) * p.1⌋ : ℤ) : ℝ) + 1 := by
          calc p.1 * ((n : ℝ) + 1) = ((n : ℝ) + 1) * p.1 := by ring
            _ < ((⌊((n : ℝ) + 1) * p.1⌋ : ℤ) : ℝ) + 1 := hfloorlt
        rw [approxByFloor, ← add_div]
        rw [lt_div_iff₀ hpos]
        exact h2
      have h3 : approxByFloor n p.1 - p.1 ≤ 0 := by linarith
      rw [Real.norm_eq_abs, abs_of_nonpos h3]
      linarith
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp := (hc p.2).continuousAt.tendsto.comp hq
  simpa only [Function.comp_def] using hcomp

/-- **The parameter derivative is a.e. measurable.**  If `G : ℝ × Z → ℝ` is jointly measurable and
`F(s, z)` is the (two-sided, where it exists) derivative in the first variable of `G` at every
interior point of the interval `Icc a b`, then the uncurried `F` is `AEMeasurable` for the product
of the Lebesgue measure restricted to `Icc a b` with any s-finite measure.

The derivative is the a.e. limit of the measurable difference quotients
`((n : ℝ) + 1) * (G(s + 1/(n+1), z) − G(s, z))`, and the only points of `Icc a b` at which the
convergence may fail are the two endpoints, which are Lebesgue-null. -/
theorem aemeasurable_uncurry_of_hasDerivWithinAt_aux
    {Z : Type*} [MeasurableSpace Z] {μ : MeasureTheory.Measure Z} [MeasureTheory.SFinite μ]
    {a b : ℝ} {F : ℝ → Z → ℝ} {G : ℝ × Z → ℝ}
    (hG : Measurable G)
    (hd : ∀ s ∈ Set.Ioo a b, ∀ z : Z,
      HasDerivWithinAt (fun σ : ℝ => G (σ, z)) (F s z) (Set.Icc a b) s) :
    AEMeasurable (fun p : ℝ × Z => F p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod μ) := by
  -- the interval measure is concentrated on `Ioo a b`
  have haeb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc a b)), x ∈ Set.Ioo a b := by
    rw [MeasureTheory.ae_iff]
    show (MeasureTheory.volume.restrict (Set.Icc a b)) ((Set.Ioo a b)ᶜ) = 0
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton a) (MeasureTheory.measure_singleton b))
    intro x hx
    rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Ioo, Set.mem_Icc, not_and_or,
      not_lt, not_lt] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases hx1 with h | h
    · exact Or.inl (le_antisymm h hx2.1)
    · exact Or.inr (le_antisymm hx2.2 h)
  -- hence the same is true for the product measure (the `x`-sections of the complement vanish)
  have hS : MeasurableSet {p : ℝ × Z | ¬ p.1 ∈ Set.Ioo a b} :=
    (measurableSet_Ioo.compl).preimage measurable_fst
  have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc a b)).prod μ), p.1 ∈ Set.Ioo a b := by
    rw [MeasureTheory.ae_iff, ← nonpos_iff_eq_zero]
    refine (MeasureTheory.Measure.prod_apply_le (ν := μ) hS).trans ?_
    have hzero : (fun x : ℝ => μ (Prod.mk x ⁻¹' {p : ℝ × Z | ¬ p.1 ∈ Set.Ioo a b}))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)] 0 := by
      filter_upwards [haeb] with x hx
      have hpre : Prod.mk x ⁻¹' {p : ℝ × Z | ¬ p.1 ∈ Set.Ioo a b} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z hz
        rw [Set.mem_preimage] at hz
        exact hz hx
      rw [hpre, MeasureTheory.measure_empty]
      rfl
    rw [MeasureTheory.lintegral_congr_ae hzero]
    simp
  -- the difference quotients are measurable
  have hAmeas : ∀ n : ℕ, Measurable (fun p : ℝ × Z =>
      ((n : ℝ) + 1) * (G (p.1 + 1 / ((n : ℝ) + 1), p.2) - G p)) := by
    intro n
    have hshift : Measurable (fun p : ℝ × Z => (p.1 + 1 / ((n : ℝ) + 1), p.2)) := by
      refine Measurable.prod ?_ measurable_snd
      exact measurable_fst.add_const _
    exact ((hG.comp hshift).sub hG).const_mul _
  refine aemeasurable_of_tendsto_metrizable_ae Filter.atTop
    (fun n => (hAmeas n).aemeasurable) ?_
  filter_upwards [hae] with p hp
  -- and they converge on the interior of the interval
  have hda : HasDerivAt (fun σ : ℝ => G (σ, p.2)) (F p.1 p.2) p.1 :=
    (hd p.1 hp p.2).hasDerivAt (mem_interior_iff_mem_nhds.mp (by rw [interior_Icc]; exact hp))
  have hslope := hda.tendsto_slope_zero
  have hseq : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin (0 : ℝ) {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
  have hcomp := hslope.comp hseq
  simpa only [Function.comp_def, one_div, inv_inv, smul_eq_mul] using hcomp

/-! ## Finiteness of the measure on the centred cube -/

private lemma volume_centreCube_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ))
      (Work.Diff.STE.B3Data.centreCube (E := E)) = 1 := by
  rw [Work.Diff.STE.B3Data.centreCube, Real.volume_pi_Ioc]
  trans ∏ _i : Fin (Module.finrank ℝ E), (1 : ENNReal)
  · exact Finset.prod_congr rfl (fun i _ => by norm_num)
  · simp

private lemma sFinite_centreCube_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    MeasureTheory.SFinite
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ)).restrict
        (Work.Diff.STE.B3Data.centreCube (E := E))) := by
  have : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ)).restrict
        (Work.Diff.STE.B3Data.centreCube (E := E))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply_univ, volume_centreCube_aux]
      exact ENNReal.one_lt_top⟩
  exact inferInstance

/-! ## The target -/

theorem aemeasurable_uncurry_R_vs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {τ : ℝ}
    (u vs : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCDu : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (u t))
    (hode : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => u s x u₀ v) (vs t x u₀ v) (Set.Icc (0 : ℝ) τ) t)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    AEMeasurable (Function.uncurry (fun s : ℝ => fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.R i (vs s) a b z : ℝ) : ℂ)))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ)).restrict
          (Work.Diff.STE.B3Data.centreCube (E := E)))) := by
  by_cases hτ : τ ≤ 0
  · -- degenerate case: `Icc 0 τ` is contained in `{0}`, so the interval measure is zero
    have hν : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ) = 0 := by
      rw [MeasureTheory.Measure.restrict_eq_zero]
      refine MeasureTheory.measure_mono_null (fun x hx => ?_) (MeasureTheory.measure_singleton 0)
      exact le_antisymm (le_trans hx.2 hτ) hx.1
    rw [hν, MeasureTheory.Measure.zero_prod]
    exact ⟨fun _ => 0, measurable_const, by
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      simp only [MeasureTheory.Measure.coe_zero, Pi.zero_apply]⟩
  · push Not at hτ
    -- ## Step 1: `h ↦ D.R i h a b z` is linear in `h`, so continuity in `σ` for fixed `z`
    -- follows from `hode`, while `hCDu` gives measurability in `z` for fixed `σ`
    have hGmeas : Measurable (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        D.R i (u (min (max p.1 0) τ)) a b p.2) := by
      refine caratheodory_measurable_aux
        (f := fun σ z => D.R i (u (min (max σ 0) τ)) a b z) ?_ ?_
      · intro z
        have hwu : ContinuousOn
            (fun t : ℝ => u t (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z)))
            (Set.Icc (0 : ℝ) τ) :=
          fun t ht => (hode t ht (D.pt i z) (D.e i a (D.pt i z))
            (D.e i b (D.pt i z))).continuousWithinAt
        have hcm : Continuous (fun σ : ℝ => min (max σ 0) τ) :=
          (continuous_id.max continuous_const).min continuous_const
        have hmap : ∀ σ : ℝ, min (max σ 0) τ ∈ Set.Icc (0 : ℝ) τ :=
          fun σ => ⟨le_min (le_max_right _ _) hτ.le, min_le_right _ _⟩
        have hcomp := hwu.comp_continuous hcm hmap
        have h2 := hcomp.const_mul (D.psi i z * Real.sqrt (D.dens i z))
        simpa only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat,
          Function.comp_apply, mul_assoc] using h2
      · intro σ
        exact (Work.Diff.STE.B3.R_contDiff_of_chartData D (u (min (max σ 0) τ))
          (hCDu (min (max σ 0) τ)) i a b).continuous.measurable
    -- ## Step 2: the derivative of `σ ↦ D.R i (u σ) a b z` on `Icc 0 τ` is `D.R i (vs s) a b z`
    have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) τ, ∀ z : (Fin (Module.finrank ℝ E) → ℝ),
        HasDerivWithinAt (fun σ : ℝ => D.R i (u (min (max σ 0) τ)) a b z)
          (D.R i (vs s) a b z) (Set.Icc (0 : ℝ) τ) s := by
      intro s hs z
      have hs' : s ∈ Set.Icc (0 : ℝ) τ := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      have h1 : HasDerivWithinAt (fun σ : ℝ => D.R i (u σ) a b z)
          (D.R i (vs s) a b z) (Set.Icc (0 : ℝ) τ) s := by
        have h0 := hode s hs' (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z))
        have h2 := h0.const_mul (D.psi i z * Real.sqrt (D.dens i z))
        simpa only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat] using h2
      -- on `Icc 0 τ` the clamp is the identity
      refine h1.congr ?_ ?_
      · intro σ hσ
        simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
        rw [max_eq_left hσ.1, min_eq_left hσ.2]
      · simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
        rw [max_eq_left hs'.1, min_eq_left hs'.2]
    -- ## Step 3: assemble
    have := sFinite_centreCube_aux (E := E)
    have hB := aemeasurable_uncurry_of_hasDerivWithinAt_aux
      (Z := Fin (Module.finrank ℝ E) → ℝ)
      (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ)).restrict
        (Work.Diff.STE.B3Data.centreCube (E := E)))
      (a := 0) (b := τ)
      (G := fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        D.R i (u (min (max p.1 0) τ)) a b p.2)
      (F := fun s z => D.R i (vs s) a b z) hGmeas hderiv
    obtain ⟨g, hg, hfg⟩ := hB
    refine ⟨fun p => ((g p : ℝ) : ℂ), Complex.measurable_ofReal.comp hg, ?_⟩
    filter_upwards [hfg] with p hp
    simp only [Function.uncurry]
    rw [hp]

end Work.Diff.STE.Lead
