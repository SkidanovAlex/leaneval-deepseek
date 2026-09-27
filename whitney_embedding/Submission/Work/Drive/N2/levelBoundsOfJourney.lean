import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.levelRateOnChart
import Submission.Work.Drive.N2.hmono_of_chartODE
import Submission.Work.Drive.N2.norm_le_of_mem_closure_modelBall

/-!
# Level bounds along the journeys of a window datum

`Work.Drive.N2.levelBoundsOfJourney`: the value of `f` along a *backward* orbit of the
model-adapted flow of a `WindowDatum` is trapped between `f x + τ` and `f x`:

  `f x + τ ≤ f (D.Φ (τ, x)) ≤ f (D.Φ (0, x)) = f x`   for `τ ≤ 0`.

The mathematical content is the pair of bounds on the *rate* of the level along an orbit:

* where the orbit avoids the model balls the level law gives slope exactly `1`;
* where the orbit is inside the model ball of the chart `i` the chart ODE gives the rate
  `2 · chartMult (ρ i / 8) (‖φ i ·‖²) · ‖φ i ·‖² ∈ [0, 1]`.

Both are local statements, glued by the elementary fact that the set on which the increment bound
holds is clopen in the interval `[τ, 0]`; the local statement at a point of the *sphere* of a model
ball is obtained from the ODE on the chart region, which contains the whole ball of radius `ρ i`
(`WindowDatum.hCop`), hence a whole neighbourhood of every point of `closure (modelBall …)`.
-/

namespace Work.Drive.N2

open scoped Manifold Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-! ## The chart rate -/

/-- **The chart rate of the level is at most `1`**: the level of a chart-confined trace rises at
speed `2 · chartMult ε (‖u‖²) · ‖u‖² ≤ 1`. -/
lemma orbitRate_le_one {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N) (y : M)
    (τ : ℝ) :
    2 * chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (τ, y))‖ ^ 2) *
      ((D.φ i (D.Φ (τ, y)) 0) ^ 2 + (D.φ i (D.Φ (τ, y)) 1) ^ 2) ≤ 1 := by
  have h := two_mul_chartMult_mul_le_one (D.ρ i / 8) (‖D.φ i (D.Φ (τ, y))‖ ^ 2)
  rw [levelMono_coord_sq (D.φ i (D.Φ (τ, y)))]
  linarith

/-- **The orbit stays in the chart region near the closure of the model ball.**  The region `C i`
contains the whole chart ball of radius `ρ i` (`WindowDatum.hCop`) and that radius is strictly
larger than `ρ i / 8`, so every point of `closure (modelBall (φ i) (ρ i / 8))` is an interior point
of `C i`. -/
lemma mem_C_of_mem_closure_modelBall {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N)
    {y : M} {σ : ℝ} (h : D.Φ (σ, y) ∈ closure (modelBall (D.φ i) (D.ρ i / 8))) :
    ∃ δ > 0, ∀ ς : ℝ, |ς - σ| < δ → D.Φ (ς, y) ∈ D.C i := by
  have hγ : Continuous fun ς : ℝ => D.Φ (ς, y) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hsubsrc : closure (modelBall (D.φ i) (D.ρ i / 8)) ⊆ (D.φ i).source :=
    fun z hz => (D.hCcl i).2 (closure_mono (D.hCball i) hz)
  have hnorm : ‖D.φ i (D.Φ (σ, y))‖ ≤ D.ρ i / 8 :=
    norm_le_of_mem_closure_modelBall (D.φ i) (D.ρ i / 8) hsubsrc _ h
  have hsrc : D.Φ (σ, y) ∈ (D.φ i).source := hsubsrc h
  have hlt : ‖D.φ i (D.Φ (σ, y))‖ < D.ρ i := by
    have := D.hρ i
    linarith
  have hopen : IsOpen {z : M | z ∈ (D.φ i).source ∧ ‖D.φ i z‖ < D.ρ i} := by
    have h1 : {z : M | z ∈ (D.φ i).source ∧ ‖D.φ i z‖ < D.ρ i} =
        (D.φ i).source ∩ (D.φ i) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (D.ρ i) := by
      ext z
      simp [Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [h1]
    exact (D.φ i).isOpen_inter_preimage Metric.isOpen_ball
  have hnhds : (fun ς : ℝ => D.Φ (ς, y)) ⁻¹'
      {z : M | z ∈ (D.φ i).source ∧ ‖D.φ i z‖ < D.ρ i} ∈ 𝓝 σ :=
    hγ.continuousAt.preimage_mem_nhds (hopen.mem_nhds ⟨hsrc, hlt⟩)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδpos, fun ς hς => ?_⟩
  exact D.hCop i (hδ (by simpa [Metric.mem_ball, Real.dist_eq] using hς))

/-! ## The derivative of the orbit function on a chart-confined segment -/

/-- **The derivative of the orbit function at a point of a chart-confined segment** is the chart
rate: the restarted chart ODE (`ode_of_mem`) plus the chain rule for `chartQ`. -/
lemma orbit_hasDerivAt_of_confined {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N)
    {y : M} {τ₁ τ : ℝ} (hle : τ₁ ≤ τ)
    (hav : ∀ u ∈ Set.Icc τ₁ τ, D.Φ (u, y) ∈ D.C i) :
    HasDerivAt (fun σ : ℝ => f (D.Φ (σ, y)))
      (2 * chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (τ, y))‖ ^ 2) *
        ((D.φ i (D.Φ (τ, y)) 0) ^ 2 + (D.φ i (D.Φ (τ, y)) 1) ^ 2)) τ := by
  have hγ : Continuous fun ς : ℝ => D.Φ (ς, y) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hsrc : D.Φ (τ, y) ∈ (D.φ i).source := D.hCsub i (hav τ ⟨hle, le_rfl⟩)
  have hnhds : (fun ς : ℝ => D.Φ (ς, y)) ⁻¹' (D.φ i).source ∈ 𝓝 τ :=
    hγ.continuousAt.preimage_mem_nhds ((D.φ i).open_source.mem_nhds hsrc)
  obtain ⟨hd0, hd1⟩ := ode_of_mem (φ := D.φ) (s₁ := D.s₁) (s₂ := D.s₂)
    (β := fun i => chartMult (D.ρ i / 8)) (C := D.C) D.hΦcomp D.hODE hle i hav
  have hQ := levelMono_hasDerivAt_chartQ i D.φ D.s₁ D.s₂
    (chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (τ, y))‖ ^ 2)) (D.hsgn i) hd0 hd1
  have hev : (fun σ : ℝ => f (D.Φ (σ, y))) =ᶠ[𝓝 τ]
      (fun σ : ℝ => f (D.x i) + chartQ (D.φ i) (D.s₁ i) (D.s₂ i) (D.Φ (σ, y))) := by
    filter_upwards [hnhds] with σ hσ
    rw [D.hval i (D.Φ (σ, y)) hσ]
  exact (hQ.const_add (f (D.x i))).congr_of_eventuallyEq hev

/-! ## The local bounds -/

/-- **Off the model balls the level of the orbit is affine of slope `1`.** -/
lemma orbit_local_bound_off {f : M → ℝ} {p : M} (D : WindowDatum f p) (x : M) {σ : ℝ}
    (hav : ∀ i : Fin D.N, D.Φ (σ, x) ∉ closure (modelBall (D.φ i) (D.ρ i / 8))) :
    ∃ δ > 0, ∀ ς₁ ς₂ : ℝ, σ - δ ≤ ς₁ → ς₁ ≤ ς₂ → ς₂ ≤ σ + δ →
      f (D.Φ (ς₂, x)) ≤ f (D.Φ (ς₁, x)) + (ς₂ - ς₁) := by
  have hγ : Continuous fun ς : ℝ => D.Φ (ς, x) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  set K : Set M := ⋃ i : Fin D.N, closure (modelBall (D.φ i) (D.ρ i / 8)) with hK
  have hKcl : IsClosed K := by
    rw [hK]
    exact isClosed_iUnion_of_finite (fun i => isClosed_closure)
  have hσK : D.Φ (σ, x) ∉ K := by
    rw [hK]
    simp only [Set.mem_iUnion]
    rintro ⟨i, hi⟩
    exact hav i hi
  have hnhds : (fun ς : ℝ => D.Φ (ς, x)) ⁻¹' Kᶜ ∈ 𝓝 σ :=
    hγ.continuousAt.preimage_mem_nhds (hKcl.isOpen_compl.mem_nhds hσK)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ / 2, by linarith, fun ς₁ ς₂ h1 h2 h3 => ?_⟩
  have hav' : ∀ u ∈ Set.Icc ς₁ ς₂, ∀ i : Fin D.N,
      D.Φ (u, x) ∉ modelBall (D.φ i) (D.ρ i / 8) := by
    intro u hu i hmem
    have hd : dist u σ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, h1, h3]
    exact hδsub hd (by
      rw [hK]
      exact Set.mem_iUnion.mpr ⟨i, subset_closure hmem⟩)
  have hlaw := level_law_of_avoid D.hΦcomp D.φ (fun i : Fin D.N => D.ρ i / 8) D.hlevel h2 hav'
  linarith [hlaw]

/-- **On a neighbourhood of a point of `closure (modelBall …)` the orbit stays in the chart
region**, where the chart ODE bounds the level rate by `1`. -/
lemma orbit_local_bound_chart {f : M → ℝ} {p : M} (D : WindowDatum f p) (x : M) {σ : ℝ}
    {i : Fin D.N} (hi : D.Φ (σ, x) ∈ closure (modelBall (D.φ i) (D.ρ i / 8))) :
    ∃ δ > 0, ∀ ς₁ ς₂ : ℝ, σ - δ ≤ ς₁ → ς₁ ≤ ς₂ → ς₂ ≤ σ + δ →
      f (D.Φ (ς₂, x)) ≤ f (D.Φ (ς₁, x)) + (ς₂ - ς₁) := by
  obtain ⟨δ, hδpos, hδC⟩ := mem_C_of_mem_closure_modelBall D i hi
  refine ⟨δ / 2, by linarith, fun ς₁ ς₂ h1 h2 h3 => ?_⟩
  have hγ : Continuous fun ς : ℝ => D.Φ (ς, x) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hC : ∀ u ∈ Set.Icc ς₁ ς₂, D.Φ (u, x) ∈ D.C i := by
    intro u hu
    refine hδC u ?_
    rw [abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  have hseg : ∀ u ∈ Set.Icc ς₁ ς₂, D.Φ (u, x) ∈ D.C i := hC
  -- continuity of the orbit function on the interval, from the chart normal form
  have hcontf : ContinuousOn (fun s : ℝ => f (D.Φ (s, x))) (Set.Icc ς₁ ς₂) := by
    have hcompφ : ContinuousOn (fun s : ℝ => D.φ i (D.Φ (s, x))) (Set.Icc ς₁ ς₂) :=
      (D.φ i).continuousOn.comp hγ.continuousOn (fun s hs => D.hCsub i (hC s hs))
    have hcoord : ∀ j : Fin 2,
        ContinuousOn (fun s : ℝ => D.φ i (D.Φ (s, x)) j) (Set.Icc ς₁ ς₂) :=
      fun j => (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) j).continuousOn.comp
        hcompφ (fun _ _ => Set.mem_univ _)
    have hQ : ContinuousOn (fun s : ℝ =>
        chartQ (D.φ i) (D.s₁ i) (D.s₂ i) (D.Φ (s, x))) (Set.Icc ς₁ ς₂) :=
      (((hcoord 0).pow 2).const_mul (D.s₁ i)).add (((hcoord 1).pow 2).const_mul (D.s₂ i))
    exact (hQ.const_add (f (D.x i))).congr (fun s hs => D.hval i _ (D.hCsub i (hC s hs)))
  have hcont : ContinuousOn (fun s : ℝ => f (D.Φ (s, x)) - s) (Set.Icc ς₁ ς₂) :=
    hcontf.sub continuous_id.continuousOn
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => f (D.Φ (s, x)) - s)
      (interior (Set.Icc ς₁ ς₂)) := by
    intro s hs
    rw [interior_Icc] at hs
    have hs' : ∀ u ∈ Set.Icc ς₁ s, D.Φ (u, x) ∈ D.C i :=
      fun u hu => hC u ⟨hu.1, le_trans hu.2 (le_of_lt hs.2)⟩
    exact ((orbit_hasDerivAt_of_confined D i (le_of_lt hs.1) hs').sub
      (hasDerivAt_id s)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ interior (Set.Icc ς₁ ς₂),
      deriv (fun s : ℝ => f (D.Φ (s, x)) - s) s ≤ 0 := by
    intro s hs
    rw [interior_Icc] at hs
    have hs' : ∀ u ∈ Set.Icc ς₁ s, D.Φ (u, x) ∈ D.C i :=
      fun u hu => hC u ⟨hu.1, le_trans hu.2 (le_of_lt hs.2)⟩
    have hfun : (fun t : ℝ => f (D.Φ (t, x)) - t) = (fun σ : ℝ => f (D.Φ (σ, x))) - id := by
      funext t
      simp
    have hd : HasDerivAt (fun s : ℝ => f (D.Φ (s, x)) - s)
        (2 * chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (s, x))‖ ^ 2) *
          ((D.φ i (D.Φ (s, x)) 0) ^ 2 + (D.φ i (D.Φ (s, x)) 1) ^ 2) - 1) s := by
      rw [hfun]
      exact (orbit_hasDerivAt_of_confined D i (le_of_lt hs.1) hs').sub (hasDerivAt_id s)
    rw [hd.deriv]
    have hb := orbitRate_le_one D i x s
    linarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc ς₁ ς₂) hcont hdiff hderiv
  have h := hanti ⟨le_rfl, h2⟩ ⟨h2, le_rfl⟩ h2
  linarith

/-- **The local increment bound along the orbit, in both directions.** -/
lemma orbit_local_bound {f : M → ℝ} {p : M} (D : WindowDatum f p) (x : M) (σ : ℝ) :
    ∃ δ > 0, ∀ ς₁ ς₂ : ℝ, σ - δ ≤ ς₁ → ς₁ ≤ ς₂ → ς₂ ≤ σ + δ →
      f (D.Φ (ς₂, x)) ≤ f (D.Φ (ς₁, x)) + (ς₂ - ς₁) := by
  by_cases h : ∃ i : Fin D.N, D.Φ (σ, x) ∈ closure (modelBall (D.φ i) (D.ρ i / 8))
  · obtain ⟨i, hi⟩ := h
    exact orbit_local_bound_chart D x hi
  · push Not at h
    exact orbit_local_bound_off D x h

/-! ## The global bounds -/

/-- **The level increases at most at unit speed along the orbit.** -/
lemma orbit_pair_bound {f : M → ℝ} {p : M} (D : WindowDatum f p) (x : M) :
    ∀ ς₁ ς₂ : ℝ, ς₁ ≤ ς₂ → f (D.Φ (ς₂, x)) ≤ f (D.Φ (ς₁, x)) + (ς₂ - ς₁) := by
  intro ς₁ ς₂ h12
  set g : ℝ → ℝ := fun s => f (D.Φ (s, x)) with hg
  have hloc : ∀ s : ℝ, ∃ δ > 0, ∀ u v : ℝ, s - δ ≤ u → u ≤ v → v ≤ s + δ →
      g v ≤ g u + (v - u) := by
    intro s
    obtain ⟨δ, hδ, hb⟩ := orbit_local_bound D x s
    exact ⟨δ, hδ, fun u v hu huv hv => hb u v hu huv hv⟩
  set C : Set ℝ := {u | u ∈ Set.Icc ς₁ ς₂ ∧ ∀ w ∈ Set.Icc ς₁ u, g w ≤ g ς₁ + (w - ς₁)}
    with hCdef
  have h1C : ς₁ ∈ C := by
    refine ⟨⟨le_rfl, h12⟩, ?_⟩
    intro w hw
    rw [Set.mem_Icc] at hw
    have hw' : w = ς₁ := le_antisymm hw.2 hw.1
    rw [hw']
    simp
  have hCne : C.Nonempty := ⟨ς₁, h1C⟩
  have hCbdd : BddAbove C := ⟨ς₂, fun u hu => hu.1.2⟩
  set σs : ℝ := sSup C with hσs
  have hσs_ub : ∀ u ∈ C, u ≤ σs := fun u hu => le_csSup hCbdd hu
  have hσs_le : σs ≤ ς₂ := csSup_le hCne (fun u hu => hu.1.2)
  have h1le : ς₁ ≤ σs := hσs_ub ς₁ h1C
  -- the supremum belongs to `C`
  have hσsC : σs ∈ C := by
    refine ⟨⟨h1le, hσs_le⟩, ?_⟩
    intro w hw
    rw [Set.mem_Icc] at hw
    rcases lt_or_eq_of_le hw.2 with hlt | heq
    · obtain ⟨a, haC, hlt'⟩ := exists_lt_of_lt_csSup hCne hlt
      exact haC.2 w ⟨hw.1, le_of_lt hlt'⟩
    · -- leftward local bound at `σs`
      obtain ⟨δ, hδpos, hb⟩ := hloc σs
      obtain ⟨a, haC, ha_gt⟩ := exists_lt_of_lt_csSup hCne (show σs - δ < σs by linarith)
      have ha_le : a ≤ σs := hσs_ub a haC
      have hlocal := hb a σs (by linarith) ha_le (by linarith)
      have hCa := haC.2 a ⟨haC.1.1, le_rfl⟩
      have hw' : w = σs := heq
      rw [hw']
      linarith
  -- the supremum is the right end
  have hσs_eq : σs = ς₂ := by
    by_contra hne
    have hlt : σs < ς₂ := lt_of_le_of_ne hσs_le hne
    obtain ⟨δ, hδpos, hb⟩ := hloc σs
    have hu_gt : σs < min (σs + δ / 2) ς₂ := lt_min (by linarith) hlt
    have hu_le : min (σs + δ / 2) ς₂ ≤ ς₂ := min_le_right _ _
    have hu_close : min (σs + δ / 2) ς₂ ≤ σs + δ := by
      have h := min_le_left (σs + δ / 2) ς₂
      linarith
    have hu_mem : min (σs + δ / 2) ς₂ ∈ C := by
      refine ⟨⟨le_trans h1le hu_gt.le, hu_le⟩, ?_⟩
      intro w hw
      rw [Set.mem_Icc] at hw
      rcases le_total w σs with hw1 | hw1
      · exact hσsC.2 w ⟨hw.1, hw1⟩
      · have hlocal := hb σs w (by linarith) hw1 (by linarith [hw.2, hu_close])
        have hCs := hσsC.2 σs ⟨h1le, le_rfl⟩
        linarith
    exact absurd (hσs_ub _ hu_mem) (not_le.mpr hu_gt)
  rw [← hσs_eq]
  exact hσsC.2 σs ⟨h1le, le_rfl⟩

theorem levelBoundsOfJourney {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {x : M} {τ : ℝ} (hτ : τ ≤ 0) :
    f x + τ ≤ f (D.Φ (τ, x)) ∧ f (D.Φ (τ, x)) ≤ f x := by
  constructor
  · have h := orbit_pair_bound D x τ 0 hτ
    rw [D.hΦ0 x] at h
    linarith
  · have hmono := D.hmono (D.Φ (τ, x))
    have h := hmono (le_refl (0 : ℝ)) (show (0 : ℝ) ≤ -τ by linarith) (by linarith)
    simp only at h
    rw [D.hΦ0, D.hΦcomp (-τ) τ x, neg_add_cancel, D.hΦ0] at h
    exact h

end Work.Drive.N2
