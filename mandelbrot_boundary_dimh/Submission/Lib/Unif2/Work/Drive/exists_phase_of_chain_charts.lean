import Mathlib
import Submission.Lib.Unif2.Work.Drive.chPhiProduct
import Submission.Lib.Unif2.Work.Drive.tendsto_chPhi_at_pivot
import Submission.Lib.Unif2.Work.Drive.tendsto_chPhi_mul_star_phase
import Submission.Lib.Unif2.Work.Drive.exists_phase_of_chain
import Submission.Lib.Unif2.Work.Drive.pair_chGadget_tendsto

/-!
# A chain of pivots with a chart family out of the maximal atlas produces a global phase

This is the **chart-family** version of `Work.Drive.exists_phase_of_chain`
(`Submission/Work/Drive/exists_phase_of_chain.lean`), which is the proof template: everywhere
`chartAt ℂ (a i)` is replaced by the chosen chart `c i` of the maximal atlas, `gPhi a ρ` by
`chPhi c a ρ`, `gadget a ρ i` by `chGadget c a ρ i`, and

* `Work.Drive.tendsto_gPhi_at_pivot` by `Work.Drive.tendsto_chPhi_at_pivot`
  (extra hypotheses `hca`, `hinj`, `hchain`);
* `Work.Drive.continuousAt_gPhi_of_notMem_range` by `Work.Drive.continuousAt_chPhi`;
* `Work.Drive.gPhi_ne_zero_of_notMem_range` by `Work.Drive.chPhi_ne_zero_of_notMem_range`;
* `Work.Drive.tendsto_gPhi_mul_star_phase` by `Work.Drive.tendsto_chPhi_mul_star_phase`
  (its hypotheses `ha0 hca hρ hinj hchain hwell hlf` are exactly the ones of the theorem below;
  this is the only genuinely new analytic input — the interaction of the *chosen* chart `c 0` at
  the base point with the chart `chartAt ℂ z₀` of the conclusion).

Everything else (`Work.Drive.exists_radialFactor`, the filled-in phase
`Θ = if x ∈ range a then limUnder (𝓝[≠] x) Ψ else Ψ x` with `Ψ = m · chPhi`,
`Work.Drive.mul_star_phase`, `Work.Drive.tendsto_nhds_ite_eq`,
`Work.Drive.continuousAt_ite_of_tendsto_nhdsNE`) is chart-independent.
-/

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The pivots of a chart-family chain are locally finite -/

/-- Every pivot lies in its own `chBall`. -/
lemma self_mem_chBall {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    (hsrc : ∀ i : ℕ, a i ∈ (c i).source) (hρ : ∀ i : ℕ, 0 < ρ i) (i : ℕ) :
    a i ∈ chBall c a ρ i := by
  rw [mem_chBall]
  refine ⟨hsrc i, ?_⟩
  rw [sub_self, norm_zero]
  linarith [hρ i]

/-- Local finiteness in the `K`/`F` witness form. -/
lemma exists_finset_forall_mem_chBall_of_mem {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X}
    {ρ : ℕ → ℝ} (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite)
    (p : X) :
    ∃ (K : Set X) (F : Finset ℕ), K ∈ 𝓝 p ∧ ∀ y ∈ K, ∀ i : ℕ, y ∈ chBall c a ρ i → i ∈ F := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨K, hKc, hKnhds⟩ := exists_compact_mem_nhds p
  exact ⟨K, (hlf K hKc).toFinset, hKnhds, fun y hy i hi => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨y, hy, hi⟩⟩

/-- The pivots of a chart-family chain form a locally finite set: every point has a neighbourhood
meeting the range of `a` only possibly at that point. -/
lemma exists_nhds_inter_range_subset_singleton_ch {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X}
    {ρ : ℕ → ℝ} (hsrc : ∀ i : ℕ, a i ∈ (c i).source) (hρ : ∀ i : ℕ, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite) (p : X) :
    ∃ W : Set X, W ∈ 𝓝 p ∧ W ∩ Set.range a ⊆ {p} := by
  obtain ⟨K, F, hK, hKF⟩ := exists_finset_forall_mem_chBall_of_mem hlf p
  set A : Set X := {q : X | ∃ i ∈ F, q = a i ∧ a i ≠ p} with hA
  have hAfin : A.Finite :=
    (F.finite_toSet).image a |>.subset (fun q hq => by
      obtain ⟨i, hiF, hqeq, -⟩ := hq
      exact ⟨i, hiF, hqeq.symm⟩)
  refine ⟨K ∩ Aᶜ, Filter.inter_mem hK ?_, ?_⟩
  · refine (hAfin.isClosed.isOpen_compl).mem_nhds ?_
    simp only [Set.mem_compl_iff, hA, Set.mem_setOf_eq, not_exists, not_and]
    intro i _ hp hne
    exact hne hp.symm
  · rintro z ⟨⟨hzK, hzA⟩, ⟨j, rfl⟩⟩
    have hjF : j ∈ F := hKF (a j) hzK j (self_mem_chBall hsrc hρ j)
    by_contra hne
    exact hzA ⟨j, hjF, rfl, hne⟩

/-! ## The main theorem -/

theorem exists_phase_of_chain_charts {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (z₀ : X) (a : ℕ → X) (c : ℕ → OpenPartialHomeomorph X ℂ) (ρ : ℕ → ℝ)
    (hca : ∀ i : ℕ, c i ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (ha0 : a 0 = z₀)
    (hρ : ∀ i : ℕ, 0 < ρ i)
    (hchain : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source ∧
      ‖(c i) (a (i + 1)) - (c i) (a i)‖ < ρ i)
    (hwell : ∀ i : ℕ, closure {x : X | x ∈ (c i).source ∧
      (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ {x : X | x ∈ (c i).source ∧
      (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}).Nonempty}.Finite)
    (hinj : Function.Injective a) :
    ∃ Θ : X → ℂ, Continuous Θ ∧ (∀ x : X, x ≠ z₀ → Θ x ≠ 0) ∧
      ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧ (∀ x ∈ V, u x ≠ 0) ∧
        ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x := by
  classical
  haveI : Nonempty X := ⟨z₀⟩
  haveI : Nontrivial X := ⟨a 0, a 1, fun h => Nat.zero_ne_one (hinj h)⟩
  haveI : PerfectSpace X := inferInstance
  -- the chain data in the form used by the `ch`-gadget lemmas
  have hsrc : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source :=
    fun i => ⟨(hchain i).1, (hchain i).2.1⟩
  have hsrc' : ∀ i : ℕ, a i ∈ (c i).source := fun i => (hchain i).1
  have hclose : ∀ i : ℕ, ‖chQ c a i - chP c a i‖ < 2 * ρ i := by
    intro i
    have h := (hchain i).2.2
    have hq : ‖chQ c a i - chP c a i‖ = ‖(c i) (a (i + 1)) - (c i) (a i)‖ := by
      simp [chQ, chP]
    rw [hq]
    linarith [hρ i]
  have hlf' : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite :=
    fun A hA => by simpa [chBall] using hlf A hA
  obtain ⟨m, hmcont, hmz0, hmpos, hmnear⟩ := exists_radialFactor (X := X) z₀
  have hmcontC : Continuous (fun x : X => (m x : ℂ)) := Complex.continuous_ofReal.comp hmcont
  set Ψ : X → ℂ := fun x => (m x : ℂ) * chPhi c a ρ x with hΨdef
  -- the limit of `Ψ` at the base point is zero
  have hΨz0 : Tendsto Ψ (𝓝[≠] z₀) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hm0 : Tendsto (fun x : X => m x) (𝓝[≠] z₀) (𝓝 0) := by
      have h := hmcont.tendsto z₀
      rw [hmz0] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨W, hWmem, hWsub⟩ := exists_nhds_inter_range_subset_singleton_ch hsrc' hρ hlf' z₀
    refine Tendsto.congr' ?_ hm0
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds hWmem]
      with x hxne hxW
    have hxr : x ∉ Set.range a := fun hyr => hxne (by simpa using hWsub ⟨hxW, hyr⟩)
    have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
    rw [hΨdef]
    simp only [norm_mul, norm_ofReal_complex,
      norm_chPhi_eq_one_of_notMem_range hρ hsrc hlf' hxnot, mul_one]
    exact (abs_of_nonneg (le_of_lt (hmpos x hxne))).symm
  -- the limit of `Ψ` at every pivot
  have hlimAt : ∀ p : X, p ∈ Set.range a → ∃ L : ℂ, Tendsto Ψ (𝓝[≠] p) (𝓝 L) := by
    intro p hp
    obtain ⟨j, rfl⟩ := hp
    rcases Nat.eq_zero_or_pos j with hj0 | hj
    · subst hj0
      rw [ha0]
      exact ⟨0, hΨz0⟩
    · obtain ⟨cst, hcne, hc⟩ :=
        tendsto_chPhi_at_pivot (c := c) (a := a) (ρ := ρ) hca hρ hinj hchain hwell hlf hj
      refine ⟨(m (a j) : ℂ) * cst, ?_⟩
      have hm : Tendsto (fun x : X => (m x : ℂ)) (𝓝[≠] (a j)) (𝓝 ((m (a j) : ℂ))) :=
        (hmcontC.tendsto (a j)).mono_left nhdsWithin_le_nhds
      simpa only [hΨdef] using hm.mul hc
  -- the global phase
  set Θ : X → ℂ := fun x => if h : x ∈ Set.range a then limUnder (𝓝[≠] x) Ψ else Ψ x with hΘdef
  have hΘpos : ∀ p : X, (hp : p ∈ Set.range a) → Θ p = limUnder (𝓝[≠] p) Ψ := by
    intro p hp
    change dite (p ∈ Set.range a) (fun _ => limUnder (𝓝[≠] p) Ψ) (fun _ => Ψ p) =
      limUnder (𝓝[≠] p) Ψ
    exact dif_pos hp
  have hΘneg : ∀ p : X, (hp : p ∉ Set.range a) → Θ p = Ψ p := by
    intro p hp
    change dite (p ∈ Set.range a) (fun _ => limUnder (𝓝[≠] p) Ψ) (fun _ => Ψ p) = Ψ p
    exact dif_neg hp
  have hΘcont : Continuous Θ := by
    rw [continuous_iff_continuousAt]
    intro p
    obtain ⟨W, hWmem, hWsub⟩ := exists_nhds_inter_range_subset_singleton_ch hsrc' hρ hlf' p
    have hWrange : ∀ y ∈ W, y ∈ Set.range a → y = p := fun y hy hyr => hWsub ⟨hy, hyr⟩
    by_cases hp : p ∈ Set.range a
    · obtain ⟨L, hL⟩ := hlimAt p hp
      have hΘp : Θ p = L := (hΘpos p hp).trans hL.limUnder_eq
      have heq : Θ =ᶠ[𝓝 p] fun y : X => if y = p then L else Ψ y := by
        filter_upwards [hWmem] with y hy
        by_cases hyp : y = p
        · have hyr : y ∈ Set.range a := by rw [hyp]; exact hp
          have h1 : Θ y = limUnder (𝓝[≠] p) Ψ := by rw [hΘpos y hyr, hyp]
          have h2 : limUnder (𝓝[≠] p) Ψ = L := (hΘpos p hp).symm.trans hΘp
          rw [h1, h2, hyp, if_pos rfl]
        · have hyr : y ∉ Set.range a := fun hh => hyp (hWrange y hy hh)
          rw [hΘneg y hyr, if_neg hyp]
      exact (continuousAt_ite_of_tendsto_nhdsNE hL).congr_of_eventuallyEq heq
    · have hΘeq : Θ =ᶠ[𝓝 p] Ψ := by
        filter_upwards [hWmem] with y hy
        have hyr : y ∉ Set.range a := by
          intro hh
          exact hp (by rw [← hWrange y hy hh]; exact hh)
        rw [hΘneg y hyr]
      have hΨcont : ContinuousAt Ψ p := by
        rw [hΨdef]
        exact (hmcontC.continuousAt).mul
          (continuousAt_chPhi hρ hsrc hclose hwell hlf (fun i hi => hp ⟨i, hi.symm⟩))
      exact hΨcont.congr_of_eventuallyEq hΘeq
  have hΘne : ∀ x : X, x ≠ z₀ → Θ x ≠ 0 := by
    intro x hx
    by_cases hxr : x ∈ Set.range a
    · obtain ⟨j, rfl⟩ := hxr
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · exact absurd (show a j = z₀ by rw [h]; exact ha0) hx
        · exact h
      obtain ⟨cst, hcne, hc⟩ :=
        tendsto_chPhi_at_pivot (c := c) (a := a) (ρ := ρ) hca hρ hinj hchain hwell hlf hj
      have hΨlim : Tendsto Ψ (𝓝[≠] (a j)) (𝓝 ((m (a j) : ℂ) * cst)) := by
        have hm : Tendsto (fun x : X => (m x : ℂ)) (𝓝[≠] (a j)) (𝓝 ((m (a j) : ℂ))) :=
          (hmcontC.tendsto (a j)).mono_left nhdsWithin_le_nhds
        simpa only [hΨdef] using hm.mul hc
      have hval : Θ (a j) = (m (a j) : ℂ) * cst :=
        (hΘpos (a j) ⟨j, rfl⟩).trans hΨlim.limUnder_eq
      rw [hval]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hmpos (a j) hx))) hcne
    · have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
      rw [hΘneg x hxr, hΨdef]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hmpos x hx)))
        (chPhi_ne_zero_of_notMem_range hρ hsrc hlf' hxnot)
  -- the local description at the base point
  obtain ⟨u₀, hu₀ne, hu₀⟩ := tendsto_chPhi_mul_star_phase (c := c) (a := a) (ρ := ρ)
    ha0 hca hρ hinj hchain hwell hlf
  set d : X → ℂ := fun x => (chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀ with hddef
  obtain ⟨W₀, hW₀mem, hW₀sub⟩ := exists_nhds_inter_range_subset_singleton_ch hsrc' hρ hlf' z₀
  have hW₀range : ∀ y ∈ W₀, y ∈ Set.range a → y = z₀ := fun y hy hyr => hW₀sub ⟨hy, hyr⟩
  set V : Set X := W₀ ∩ (chartAt ℂ z₀).source ∩ {x : X | m x = ‖d x‖} with hVdef
  set u : X → ℂ := fun x => if x = z₀ then u₀ else chPhi c a ρ x * star (phase (d x)) with hudef
  have hVmem : V ∈ 𝓝 z₀ := by
    rw [hVdef]
    refine Filter.inter_mem (Filter.inter_mem hW₀mem ?_) ?_
    · exact (chartAt ℂ z₀).open_source.mem_nhds (mem_chart_source ℂ z₀)
    · filter_upwards [hmnear] with x hx
      simpa only [hddef] using hx
  have hVsub : ∀ x ∈ V, x ∈ W₀ ∧ x ∈ (chartAt ℂ z₀).source ∧ m x = ‖d x‖ := by
    intro x hx
    rw [hVdef] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  have hcont_u : ContinuousOn u V := by
    intro x hxV
    obtain ⟨hxW₀, hxsrc, hxmd⟩ := hVsub x hxV
    by_cases hxz : x = z₀
    · subst hxz
      exact (continuousAt_ite_of_tendsto_nhdsNE hu₀).continuousWithinAt
    · have hxr : x ∉ Set.range a := fun hh => hxz (hW₀range x hxW₀ hh)
      have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
      have hcd : ContinuousAt d x := by
        rw [hddef]
        exact ((chartAt ℂ z₀).continuousAt hxsrc).sub continuousAt_const
      have hdx_ne : d x ≠ 0 := by
        rw [hddef]
        exact sub_ne_zero.mpr (fun h => hxz ((chartAt ℂ z₀).injOn hxsrc
          (mem_chart_source ℂ z₀) h))
      have hcontΦ : ContinuousAt (chPhi c a ρ) x :=
        continuousAt_chPhi hρ hsrc hclose hwell hlf hxnot
      have hcontphase : ContinuousAt (fun y : X => star (phase (d y))) x :=
        continuous_star.continuousAt.comp ((continuousAt_phase hdx_ne).comp hcd)
      refine ((hcontΦ.mul hcontphase).congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [eventually_ne_nhds hxz] with y hy
      rw [hudef]
      simp only [if_neg hy, Pi.mul_apply]
  have hne_u : ∀ x ∈ V, u x ≠ 0 := by
    intro x hxV
    obtain ⟨hxW₀, hxsrc, hxmd⟩ := hVsub x hxV
    by_cases hxz : x = z₀
    · simp only [hudef, if_pos hxz]
      exact hu₀ne
    · have hxr : x ∉ Set.range a := fun hh => hxz (hW₀range x hxW₀ hh)
      have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
      simp only [hudef, if_neg hxz]
      refine mul_ne_zero (chPhi_ne_zero_of_notMem_range hρ hsrc hlf' hxnot) ?_
      intro h
      have hdx_ne : d x ≠ 0 := by
        rw [hddef]
        exact sub_ne_zero.mpr (fun hh => hxz ((chartAt ℂ z₀).injOn hxsrc
          (mem_chart_source ℂ z₀) hh))
      refine phase_ne_zero hdx_ne ?_
      have := congrArg star h
      simpa using this
  have hform : ∀ x ∈ V, Θ x = d x * u x := by
    intro x hxV
    obtain ⟨hxW₀, hxsrc, hxmd⟩ := hVsub x hxV
    by_cases hxz : x = z₀
    · have hΘz : Θ z₀ = 0 := (hΘpos z₀ ⟨0, ha0⟩).trans hΨz0.limUnder_eq
      rw [hxz, hΘz, hudef, hddef]
      simp
    · have hxr : x ∉ Set.range a := fun hh => hxz (hW₀range x hxW₀ hh)
      have hΘx : Θ x = Ψ x := hΘneg x hxr
      rw [hΘx, hΨdef, hudef]
      simp only [if_neg hxz]
      rw [hxmd, ← mul_star_phase (d x)]
      ring
  exact ⟨Θ, hΘcont, hΘne, u, V, hVmem, hcont_u, hne_u, hform⟩

end Work.Drive
