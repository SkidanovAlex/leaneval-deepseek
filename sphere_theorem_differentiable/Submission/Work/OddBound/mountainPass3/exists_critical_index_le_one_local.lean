import Mathlib
import Submission.Work.OddBound.PolygonChart
import Submission.Work.OddBound.mountainPass.exists_critical_index_le_one
import Submission.Work.OddBound.design.Localisation
import Submission.Work.OddBound.design.MountainPassManifold2
import Submission.Work.OddBound.mountainPass3.exists_sublevel_near_of_negDefPlane_local
import Submission.Work.OddBound.mountainPass3.local_joinedIn_of_fderiv_ne_zero_ball
import Submission.Work.OddBound.mountainPass3.local_joinedIn_of_negDefPlane_ball
import Submission.Work.OddBound.mountainPass3.contDiffAt_chart_expression_of_mem_atlas
import Submission.Work.OddBound.mountainPass3.fderiv_chart_expression_eq_zero_of_isCriticalChart
import Submission.Work.OddBound.mountainPass3.isCriticalChart_of_isLocalMin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.mountainPass3

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-!
## Local structure lemmas, transported from the Euclidean (chart) versions

These three lemmas are the only places where the manifold structure is used: each is a
chart transport of one of the Euclidean structural lemmas proved in this directory.
-/

/-- **Sublevel points accumulate at a point with a negative definite plane.**
If `z` carries a negative-definite plane (in *some* atlas chart, which is smooth at `z`),
then every neighbourhood of `z` contains a point at which `f` is strictly smaller. -/
theorem hedge_of_hasNegDefPlane
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] [FiniteDimensional ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold (𝓘(ℝ, H')) 2 P]
    {f : P → ℝ} {z : P}
    (hsm : ∃ e : OpenPartialHomeomorph P H', e ∈ atlas H' P ∧ z ∈ e.source ∧
      ContDiffAt ℝ 2 (fun x : H' => f (e.symm x)) (e z))
    (hbad : Work.OddBound.HasNegDefPlane H' f z) :
    ∀ V : Set P, IsOpen V → z ∈ V → ∃ x ∈ V, f x < f z := by
  intro V hV hzV
  obtain ⟨e₂, he₂, hz₂, v, w, hv⟩ := hbad
  obtain ⟨e₀, he₀, hz₀, hs₀⟩ := hsm
  -- smoothness of the chart expression in the chart that exhibits the plane
  have hs₂ : ContDiffAt ℝ 2 (fun x : H' => f (e₂.symm x)) (e₂ z) :=
    contDiffAt_chart_expression_of_mem_atlas ⟨e₀, he₀, hz₀, hs₀⟩ e₂ he₂ hz₂
  -- a ball around `e₂ z` inside `e₂.target` whose inverse image lies in `V`
  have hnhds : (↑e₂.symm ⁻¹' V ∩ e₂.target) ∈ 𝓝 (e₂ z) :=
    Filter.inter_mem
      ((e₂.continuousAt_symm (e₂.mapsTo hz₂)).preimage_mem_nhds
        (hV.mem_nhds (by simpa [e₂.left_inv hz₂] using hzV)))
      (e₂.open_target.mem_nhds (e₂.mapsTo hz₂))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨x, hxdist, hxlt⟩ :=
    exists_sublevel_near_of_negDefPlane_local hs₂ ⟨v, w, hv⟩ ρ hρ
  have hxball : x ∈ Metric.ball (e₂ z) ρ := Metric.mem_ball.mpr hxdist
  have hxt : x ∈ e₂.target := (hρsub hxball).2
  have hxV : e₂.symm x ∈ V := (hρsub hxball).1
  exact ⟨e₂.symm x, hxV, by simpa only [e₂.left_inv hz₂] using hxlt⟩

/-- **At a critical point with a negative definite plane, nearby sublevel points are joined.**
This is the manifold version of `local_joinedIn_of_negDefPlane`; both the criticality and the
plane are transferred to a single chart. -/
theorem joinedIn_class_of_critical_hasNegDefPlane
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] [FiniteDimensional ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold (𝓘(ℝ, H')) 2 P]
    {f : P → ℝ} {z : P} {Λ : ℝ} (hz : f z = Λ)
    (hsm : ∃ e : OpenPartialHomeomorph P H', e ∈ atlas H' P ∧ z ∈ e.source ∧
      ContDiffAt ℝ 2 (fun x : H' => f (e.symm x)) (e z))
    (hcrit : Work.OddBound.IsCriticalChart H' f z)
    (hbad : Work.OddBound.HasNegDefPlane H' f z) :
    ∃ V : Set P, IsOpen V ∧ z ∈ V ∧ ∀ x ∈ V, ∀ y ∈ V, f x < Λ → f y < Λ →
      JoinedIn {w : P | f w < Λ} x y := by
  obtain ⟨e₂, he₂, hz₂, v, w, hv⟩ := hbad
  obtain ⟨e₀, he₀, hz₀, hs₀⟩ := hsm
  have hs₂ : ContDiffAt ℝ 2 (fun x : H' => f (e₂.symm x)) (e₂ z) :=
    contDiffAt_chart_expression_of_mem_atlas ⟨e₀, he₀, hz₀, hs₀⟩ e₂ he₂ hz₂
  -- the `C¹` structure on `P` in the form the `{n : ℕ}`-typed transfer lemmas expect
  haveI hI1 : IsManifold (𝓘(ℝ, H')) ((1 : ℕ) : ℕ∞ω) P :=
    inferInstanceAs (IsManifold (𝓘(ℝ, H')) (1 : ℕ∞ω) P)
  -- criticality in the chart `e₂`
  have hsmall : ∀ (e : OpenPartialHomeomorph P H'), e ∈ atlas H' P → z ∈ e.source →
      ContDiffAt ℝ 1 (fun x : H' => f (e.symm x)) (e z) := fun e he hez =>
    contDiffAt_chart_expression_of_mem_atlas ⟨e₀, he₀, hz₀, hs₀.of_le (m := 1) (by norm_num)⟩ e he hez
  have hcz₂ : fderiv ℝ (fun x : H' => f (e₂.symm x)) (e₂ z) = 0 :=
    fderiv_chart_expression_eq_zero_of_isCriticalChart hcrit hsmall e₂ he₂ hz₂
  -- a ball around `e₂ z` on which the chart expression is `C²`, inside `e₂.target`
  have hev₂ : ∀ᶠ y in 𝓝 (e₂ z), ContDiffAt ℝ 2 (fun x : H' => f (e₂.symm x)) y :=
    hs₂.eventually (by norm_num)
  obtain ⟨R₀, hR₀, hR₀ball⟩ := Metric.eventually_nhds_iff_ball.mp hev₂
  obtain ⟨r₁, hr₁, hr₁sub⟩ :=
    Metric.isOpen_iff.mp e₂.open_target (e₂ z) (e₂.mapsTo hz₂)
  set R : ℝ := min R₀ r₁
  have hRpos : 0 < R := lt_min hR₀ hr₁
  have hRsub : Metric.ball (e₂ z) R ⊆ e₂.target := fun y hy =>
    hr₁sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hC2 : ContDiffOn ℝ 2 (fun x : H' => f (e₂.symm x)) (Metric.ball (e₂ z) R) :=
    (Metric.isOpen_ball).contDiffOn_iff.mpr fun y hy =>
      hR₀ball y (Metric.ball_subset_ball (min_le_left _ _) hy)
  obtain ⟨ρ, hρ, hpath⟩ := local_joinedIn_of_negDefPlane_ball hRpos hC2 hcz₂ ⟨v, w, hv⟩
  refine ⟨e₂.source ∩ (↑e₂ : P → H') ⁻¹' Metric.ball (e₂ z) ρ,
    e₂.isOpen_inter_preimage Metric.isOpen_ball, ?_, ?_⟩
  · exact ⟨hz₂, Metric.mem_ball_self hρ⟩
  · intro x hx y hy hfx hfy
    obtain ⟨hxsrc, hxball⟩ := hx
    obtain ⟨hysrc, hyball⟩ := hy
    have hxlt : (fun y : H' => f (e₂.symm y)) (e₂ x) < (fun y : H' => f (e₂.symm y)) (e₂ z) := by
      have : f (e₂.symm (e₂ x)) < f (e₂.symm (e₂ z)) := by
        rw [e₂.left_inv hxsrc, e₂.left_inv hz₂]
        rw [hz]
        exact hfx
      exact this
    have hylt : (fun y : H' => f (e₂.symm y)) (e₂ y) < (fun y : H' => f (e₂.symm y)) (e₂ z) := by
      have : f (e₂.symm (e₂ y)) < f (e₂.symm (e₂ z)) := by
        rw [e₂.left_inv hysrc, e₂.left_inv hz₂]
        rw [hz]
        exact hfy
      exact this
    obtain ⟨γ, hγcont, hγ0, hγ1, hγlt, hγdist⟩ :=
      hpath (e₂ x) (e₂ y) hxball hyball hxlt hylt
    refine JoinedIn.ofLine (f := fun t : ℝ => e₂.symm (γ t)) ?_ ?_ ?_ ?_
    · exact (e₂.continuousOn_symm.comp hγcont) fun t ht => hRsub (hγdist t ht)
    · rw [hγ0, e₂.left_inv hxsrc]
    · rw [hγ1, e₂.left_inv hysrc]
    · rintro w' ⟨t, ht, rfl⟩
      have h1 : f (e₂.symm (γ t)) < f (e₂.symm (e₂ z)) := hγlt t ht
      rw [e₂.left_inv hz₂, hz] at h1
      exact h1

/-- **At a regular point the sublevel set is locally path connected.**
Manifold version of `local_joinedIn_of_fderiv_ne_zero`. -/
theorem joinedIn_class_of_fderiv_ne_zero
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    {f : P → ℝ} {z : P} {Λ : ℝ} (hz : f z = Λ)
    {e : OpenPartialHomeomorph P H'} (he : e ∈ atlas H' P) (hzsrc : z ∈ e.source)
    (hsm : ContDiffAt ℝ 1 (fun x : H' => f (e.symm x)) (e z))
    (hg : fderiv ℝ (fun x : H' => f (e.symm x)) (e z) ≠ 0) :
    ∃ V : Set P, IsOpen V ∧ z ∈ V ∧ ∀ x ∈ V, ∀ y ∈ V, f x < Λ → f y < Λ →
      JoinedIn {w : P | f w < Λ} x y := by
  have hev : ∀ᶠ y in 𝓝 (e z), ContDiffAt ℝ 1 (fun x : H' => f (e.symm x)) y :=
    hsm.eventually (by norm_num)
  obtain ⟨R₀, hR₀, hR₀ball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp e.open_target (e z) (e.mapsTo hzsrc)
  set R : ℝ := min R₀ r₁
  have hRpos : 0 < R := lt_min hR₀ hr₁
  have hRsub : Metric.ball (e z) R ⊆ e.target := fun y hy =>
    hr₁sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hC1 : ContDiffOn ℝ 1 (fun x : H' => f (e.symm x)) (Metric.ball (e z) R) :=
    (Metric.isOpen_ball).contDiffOn_iff.mpr fun y hy =>
      hR₀ball y (Metric.ball_subset_ball (min_le_left _ _) hy)
  obtain ⟨ρ, hρ, hpath⟩ := local_joinedIn_of_fderiv_ne_zero_ball hRpos hC1 hg
  refine ⟨e.source ∩ (↑e : P → H') ⁻¹' Metric.ball (e z) ρ,
    e.isOpen_inter_preimage Metric.isOpen_ball, ?_, ?_⟩
  · exact ⟨hzsrc, Metric.mem_ball_self hρ⟩
  · intro x hx y hy hfx hfy
    obtain ⟨hxsrc, hxball⟩ := hx
    obtain ⟨hysrc, hyball⟩ := hy
    have hxlt : (fun y : H' => f (e.symm y)) (e x) < (fun y : H' => f (e.symm y)) (e z) := by
      have : f (e.symm (e x)) < f (e.symm (e z)) := by
        rw [e.left_inv hxsrc, e.left_inv hzsrc]
        rw [hz]
        exact hfx
      exact this
    have hylt : (fun y : H' => f (e.symm y)) (e y) < (fun y : H' => f (e.symm y)) (e z) := by
      have : f (e.symm (e y)) < f (e.symm (e z)) := by
        rw [e.left_inv hysrc, e.left_inv hzsrc]
        rw [hz]
        exact hfy
      exact this
    obtain ⟨γ, hγcont, hγ0, hγ1, hγlt, hγdist⟩ :=
      hpath (e x) (e y) hxball hyball hxlt hylt
    refine JoinedIn.ofLine (f := fun t : ℝ => e.symm (γ t)) ?_ ?_ ?_ ?_
    · exact (e.continuousOn_symm.comp hγcont) fun t ht => hRsub (hγdist t ht)
    · rw [hγ0, e.left_inv hxsrc]
    · rw [hγ1, e.left_inv hysrc]
    · rintro w' ⟨t, ht, rfl⟩
      have h1 : f (e.symm (γ t)) < f (e.symm (e z)) := hγlt t ht
      rw [e.left_inv hzsrc, hz] at h1
      exact h1

/-!
## The mountain pass with the index bound, localised

The proof is a port of the proved Euclidean theorem
`Work.OddBound.mountainPass.exists_critical_index_le_one`; only the local structure lemmas
above change.
-/

/-- Path components of an open subset of a charted space over a normed space are open
(the manifold is locally path connected). -/
theorem isOpen_joinedIn_class' {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    {U : Set P} (hU : IsOpen U) {x : P} (hx : x ∈ U) :
    IsOpen {y : P | JoinedIn U x y} := by
  haveI : LocallyPathConnectedSpace P := ChartedSpace.locallyPathConnectedSpace H' P
  exact hU.pathComponentIn x

theorem exists_critical_index_le_one_local
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] [FiniteDimensional ℝ H']
    {P : Type*} [TopologicalSpace P] [T2Space P] [CompactSpace P]
    [ChartedSpace H' P] [IsManifold (𝓘(ℝ, H')) 2 P]
    {f : P → ℝ} (hf : Continuous f)
    {a b : P} (hpath : ∃ σ : ℝ → P, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b)
    {Λ : ℝ}
    (hΛ : Λ = sInf {m : ℝ | ∃ σ : ℝ → P, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, f (σ t) ≤ m})
    (hlt : max (f a) (f b) < Λ)
    {C : ℝ} (hC : Λ < C)
    (hsm : ∀ z : P, f z ≤ C → ∃ e : OpenPartialHomeomorph P H',
      e ∈ atlas H' P ∧ z ∈ e.source ∧
      ContDiffAt ℝ 2 (fun x : H' => f (e.symm x)) (e z)) :
    ∃ z : P, f z = Λ ∧ Work.OddBound.IsCriticalChart H' f z ∧
      ¬ Work.OddBound.HasNegDefPlane H' f z := by
  classical
  -- ## Step 1: the competitor set and basic order facts
  set S : Set ℝ := {m : ℝ | ∃ σ : ℝ → P, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, f (σ t) ≤ m} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨σ, hσc, hσ0, hσ1⟩ := hpath
    obtain ⟨t₀, ht₀, htmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
      ⟨0, left_mem_Icc.mpr zero_le_one⟩ (hf.comp_continuousOn hσc)
    exact ⟨f (σ t₀), σ, hσc, hσ0, hσ1, fun t ht => htmax ht⟩
  have hSle_a : ∀ m ∈ S, f a ≤ m := by
    intro m hm
    obtain ⟨σ, _, h0, _, hle⟩ := hm
    rw [← h0]
    exact hle 0 (left_mem_Icc.mpr zero_le_one)
  have hbdd : BddBelow S := ⟨f a, hSle_a⟩
  have hfa : f a ≤ Λ := by rw [hΛ]; exact le_csInf hSne hSle_a
  have hfb : f b ≤ Λ := by
    rw [hΛ]
    refine le_csInf hSne fun m hm => ?_
    obtain ⟨σ, _, _, h1, hle⟩ := hm
    rw [← h1]
    exact hle 1 (right_mem_Icc.mpr zero_le_one)
  have hfa' : f a < Λ := lt_of_le_of_lt (le_max_left _ _) hlt
  have hfb' : f b < Λ := lt_of_le_of_lt (le_max_right _ _) hlt
  have hmemS_of_gt : ∀ {c : ℝ}, Λ < c → c ∈ S := by
    intro c hc
    obtain ⟨m, hmS, hmc⟩ := (csInf_lt_iff hbdd hSne).mp (by rw [← hΛ]; exact hc)
    obtain ⟨σ, hσc, hσ0, hσ1, hle⟩ := hmS
    exact ⟨σ, hσc, hσ0, hσ1, fun t ht => le_trans (hle t ht) hmc.le⟩
  -- ## Step 2: `a` and `b` are not joined inside the strict sublevel set
  set U : Set P := {x : P | f x < Λ} with hUdef
  have hUopen : IsOpen U := isOpen_lt hf continuous_const
  have hnotJoined : ¬ JoinedIn U a b := by
    rintro ⟨γ, hγ⟩
    let σ : ℝ → P := fun t => γ (Set.projIcc 0 1 zero_le_one t)
    have hσc : ContinuousOn σ (Set.Icc (0 : ℝ) 1) :=
      (γ.continuous.comp continuous_projIcc).continuousOn
    have hσ0 : σ 0 = a := by
      simp only [σ, Set.projIcc_left]
      exact γ.source
    have hσ1 : σ 1 = b := by
      simp only [σ, Set.projIcc_right]
      exact γ.target
    obtain ⟨t₀, ht₀, htmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
      ⟨0, left_mem_Icc.mpr zero_le_one⟩ (hf.comp_continuousOn hσc)
    have hmS : f (σ t₀) ∈ S := ⟨σ, hσc, hσ0, hσ1, fun t ht => htmax ht⟩
    have hmlt : f (σ t₀) < Λ := hγ (Set.projIcc 0 1 zero_le_one t₀)
    have hle := csInf_le hbdd hmS
    rw [← hΛ] at hle
    linarith
  -- ## Step 3: the nested sublevel components and their intersection `Z`
  let lev : ℕ → Set P := fun n => {x : P | f x ≤ Λ + 1 / ((n : ℝ) + 1)}
  have hlev_closed : ∀ n, IsClosed (lev n) := fun n =>
    isClosed_le hf continuous_const
  have hlev_comp : ∀ n, IsCompact (lev n) := fun n => (hlev_closed n).isCompact
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hmem_lev : ∀ n, a ∈ lev n := fun n => by
    show f a ≤ Λ + 1 / ((n : ℝ) + 1)
    linarith [hfa', hpos n]
  have hlev_mono : ∀ n, lev (n + 1) ⊆ lev n := by
    intro n x hx
    have hx' : f x ≤ Λ + 1 / (((n + 1 : ℕ) : ℝ) + 1) := hx
    show f x ≤ Λ + 1 / ((n : ℝ) + 1)
    have h2 : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le <;> push_cast <;> linarith
    linarith
  let comp : ℕ → Set P := fun n => connectedComponentIn (lev n) a
  have hcomp_sub : ∀ n, comp n ⊆ lev n := fun n => connectedComponentIn_subset _ _
  have hcomp_ne : ∀ n, (comp n).Nonempty := fun n =>
    connectedComponentIn_nonempty_iff.mpr (hmem_lev n)
  have hcomp_conn : ∀ n, IsConnected (comp n) := fun n =>
    ⟨hcomp_ne n, isPreconnected_connectedComponentIn⟩
  have hcomp_closed : ∀ n, IsClosed (comp n) := by
    intro n
    rw [← closure_subset_iff_isClosed]
    refine IsPreconnected.subset_connectedComponentIn
      isPreconnected_connectedComponentIn.closure ?_ ?_
    · exact subset_closure (mem_connectedComponentIn (hmem_lev n))
    · calc closure (comp n) ⊆ closure (lev n) := closure_mono (hcomp_sub n)
        _ = lev n := (hlev_closed n).closure_eq
  have hcomp_compact : ∀ n, IsCompact (comp n) := fun n =>
    IsCompact.of_isClosed_subset (hlev_comp n) (hcomp_closed n) (hcomp_sub n)
  have hcomp_mono : ∀ n, comp (n + 1) ⊆ comp n := fun n =>
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn (hmem_lev (n + 1))) ((hcomp_sub (n + 1)).trans (hlev_mono n))
  set Z : Set P := ⋂ n, comp n with hZdef
  have hZconn : IsConnected Z :=
    Work.OddBound.mountainPass.isConnected_iInter_of_antitone hcomp_compact hcomp_conn hcomp_mono
  have haZ : a ∈ Z := mem_iInter.mpr fun n => mem_connectedComponentIn (hmem_lev n)
  have hbZ : b ∈ Z := by
    refine mem_iInter.mpr fun n => ?_
    have hltn : Λ < Λ + 1 / ((n : ℝ) + 1) := by linarith [hpos n]
    obtain ⟨σ, hσc, hσ0, hσ1, hle⟩ := hmemS_of_gt hltn
    have hpre : IsPreconnected (σ '' Set.Icc (0 : ℝ) 1) := isPreconnected_Icc.image σ hσc
    have hain : a ∈ σ '' Set.Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.mpr zero_le_one, hσ0⟩
    have hbin : b ∈ σ '' Set.Icc (0 : ℝ) 1 := ⟨1, right_mem_Icc.mpr zero_le_one, hσ1⟩
    have hsub : σ '' Set.Icc (0 : ℝ) 1 ⊆ lev n := by
      rintro y ⟨t, ht, rfl⟩
      show f (σ t) ≤ Λ + 1 / ((n : ℝ) + 1)
      exact hle t ht
    exact IsPreconnected.subset_connectedComponentIn hpre hain hsub hbin
  have hZle : Z ⊆ {x : P | f x ≤ Λ} := by
    intro z hz
    show f z ≤ Λ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have h1 : f z ≤ Λ + 1 / ((n : ℝ) + 1) := hcomp_sub n (mem_iInter.mp hz n)
    linarith
  -- ## Step 4: the final argument
  by_contra hcon
  have hall : ∀ z : P, f z = Λ → Work.OddBound.IsCriticalChart H' f z →
      Work.OddBound.HasNegDefPlane H' f z := by
    intro z hz hcrit
    by_contra hnb
    exact hcon ⟨z, hz, hcrit, hnb⟩
  -- (A) every point of `Z` lies in the closure of `U`
  have hZclU : Z ⊆ closure U := by
    intro z hz
    by_contra hzc
    rw [_root_.mem_closure_iff] at hzc
    have hex : ∃ o : Set P, IsOpen o ∧ z ∈ o ∧ ¬ (o ∩ U).Nonempty := by
      by_contra h
      refine hzc fun o hoo hzo => ?_
      by_contra hne
      exact h ⟨o, hoo, hzo, hne⟩
    obtain ⟨o, hoo, hzo, hoe⟩ := hex
    have hoe' : ∀ y : P, y ∈ o → y ∉ U := by
      intro y hyo hyU
      exact hoe ⟨y, hyo, hyU⟩
    have hzle : f z ≤ Λ := hZle hz
    have hzeq : f z = Λ := le_antisymm hzle (le_of_not_gt fun h => hoe' z hzo h)
    have hmin : IsLocalMin f z := by
      show ∀ᶠ y in 𝓝 z, f z ≤ f y
      filter_upwards [hoo.mem_nhds hzo] with y hy
      rw [hzeq]
      exact le_of_not_gt fun h => hoe' y hy h
    have hzC : f z ≤ C := by rw [hzeq]; exact hC.le
    obtain ⟨e, he, hzsrc, hsmooth⟩ := hsm z hzC
    have hcrit : Work.OddBound.IsCriticalChart H' f z :=
      isCriticalChart_of_isLocalMin hmin he hzsrc (hsmooth.of_le (m := 1) (by norm_num))
    have hbad : Work.OddBound.HasNegDefPlane H' f z := hall z hzeq hcrit
    obtain ⟨x, hxo, hxlt⟩ := hedge_of_hasNegDefPlane ⟨e, he, hzsrc, hsmooth⟩ hbad o hoo hzo
    exact hoe' x hxo (show f x < Λ from by rw [← hzeq]; exact hxlt)
  -- (B) local connectedness of the strict sublevel set near points of `Z`
  have hLocal : ∀ z ∈ Z, ∃ V : Set P, IsOpen V ∧ z ∈ V ∧ ∀ x ∈ V, ∀ y ∈ V,
      f x < Λ → f y < Λ → JoinedIn U x y := by
    intro z hz
    have hzle : f z ≤ Λ := hZle hz
    rcases lt_or_eq_of_le hzle with hlt' | heq
    · exact ⟨{y : P | JoinedIn U z y}, isOpen_joinedIn_class' (H' := H') hUopen hlt',
        JoinedIn.refl hlt', fun x hx y hy _ _ => (JoinedIn.symm hx).trans hy⟩
    · have hzC : f z ≤ C := by rw [heq]; exact hC.le
      obtain ⟨e, he, hzsrc, hsmooth⟩ := hsm z hzC
      by_cases hder : fderiv ℝ (fun x : H' => f (e.symm x)) (e z) = 0
      · have hcrit : Work.OddBound.IsCriticalChart H' f z := ⟨e, he, hzsrc, hder⟩
        exact joinedIn_class_of_critical_hasNegDefPlane heq ⟨e, he, hzsrc, hsmooth⟩ hcrit
          (hall z heq hcrit)
      · exact joinedIn_class_of_fderiv_ne_zero heq he hzsrc (hsmooth.of_le (m := 1) (by norm_num)) hder
  -- (C) the minimal closed separation
  set Comp : P → Set P := fun x => {y : P | JoinedIn U x y} with hCompdef
  have hComp_sub_U : ∀ x : P, Comp x ⊆ U := fun x y hy => JoinedIn.target_mem hy
  set TA : Set P := closure (Comp a) with hTAdef
  set TB : Set P := closure (U \ Comp a) with hTBdef
  have hZunion : Z ⊆ TA ∪ TB := by
    intro z hz
    have hzcl : z ∈ closure U := hZclU hz
    have hdecomp : U = Comp a ∪ (U \ Comp a) := by
      ext y
      constructor
      · intro hy
        by_cases h : y ∈ Comp a
        · exact Or.inl h
        · exact Or.inr ⟨hy, h⟩
      · rintro (h | h)
        · exact hComp_sub_U a h
        · exact h.1
    rw [hdecomp, closure_union] at hzcl
    exact hzcl
  have hZdisj : Z ∩ (TA ∩ TB) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzZ, hzTA, hzTB⟩
    obtain ⟨V, hVo, hzV, hloc⟩ := hLocal z hzZ
    obtain ⟨x₁, hx1V, hx1c⟩ := _root_.mem_closure_iff.mp hzTA V hVo hzV
    obtain ⟨x₂, hx2V, hx2⟩ := _root_.mem_closure_iff.mp hzTB V hVo hzV
    have hfx1 : f x₁ < Λ := hComp_sub_U a hx1c
    have hfx2 : f x₂ < Λ := hx2.1
    exact hx2.2 (hx1c.trans (hloc x₁ hx1V x₂ hx2V hfx1 hfx2))
  -- the dichotomy
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hZconn.isPreconnected) TA TB
      isClosed_closure isClosed_closure hZunion hZdisj with hTA | hTB
  · have hbTB : b ∈ TB := subset_closure ⟨hfb', hnotJoined⟩
    have hbTA : b ∈ TA := hTA hbZ
    have hmem : b ∈ Z ∩ (TA ∩ TB) := ⟨hbZ, hbTA, hbTB⟩
    rw [hZdisj] at hmem
    exact hmem
  · have haTA : a ∈ TA := subset_closure (JoinedIn.refl hfa')
    have haTB : a ∈ TB := hTB haZ
    have hmem : a ∈ Z ∩ (TA ∩ TB) := ⟨haZ, haTA, haTB⟩
    rw [hZdisj] at hmem
    exact hmem

end Work.OddBound.mountainPass3
