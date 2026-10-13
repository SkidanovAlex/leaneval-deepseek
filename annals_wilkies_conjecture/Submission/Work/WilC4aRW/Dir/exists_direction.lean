import Mathlib
import Submission.Work.WilC4aRW.Defs

set_option autoImplicit false

namespace Work.WilC4aRW.Dir

open Filter Topology
open scoped Topology

/-- From a real-analytic function at `0`, obtain an extended ball around `0` on which it is
analytic at every point. -/
lemma exists_ball_analyticOnNhd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ r : ENNReal, 0 < r ∧ AnalyticOnNhd ℝ f (Metric.eball 0 r) := by
  rcases hf with ⟨p, r, hr⟩
  exact ⟨r, hr.r_pos, hr.analyticOnNhd⟩

/-- If `f` is analytic on the ball `eball 0 r`, then along any direction `x` at which `f` is
nonzero, the one-variable function `t ↦ f (t • x)` is not eventually zero at `0`. -/
lemma not_eventuallyEq_zero_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {r : ENNReal} (hr : 0 < r)
    (hf : AnalyticOnNhd ℝ f (Metric.eball 0 r)) {x : E}
    (hx : x ∈ Metric.eball 0 r) (hxz : f x ≠ 0) :
    ¬ ((fun t : ℝ => f (t • x)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0)) := by
  intro hg
  set u : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ x with hu
  have hU : IsPreconnected (⇑u ⁻¹' Metric.eball (0 : E) r) :=
    ((convex_eball (0 : E) r).linear_preimage u.toLinearMap).isPreconnected
  have h0U : (0 : ℝ) ∈ ⇑u ⁻¹' Metric.eball (0 : E) r := by
    simp only [Set.mem_preimage, map_zero]
    exact Metric.mem_eball_self hr
  have h1U : (1 : ℝ) ∈ ⇑u ⁻¹' Metric.eball (0 : E) r := by
    simp only [Set.mem_preimage, hu, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    exact hx
  have han : AnalyticOnNhd ℝ (fun t : ℝ => f (t • x)) (⇑u ⁻¹' Metric.eball (0 : E) r) := by
    have h := hf.compContinuousLinearMap (u := u)
    simpa [hu, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using h
  have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero han hU h0U hg
  have h1 := hzero h1U
  simp only [Pi.zero_apply] at h1
  exact hxz (by simpa using h1)

theorem exists_direction {n k : ℕ} (h : Fin k → (Fin (n + 1) → ℝ) → ℝ)
    (hA : ∀ i, AnalyticAt ℝ (h i) 0) (h0 : ∀ i, h i 0 = 0)
    (hNZ : ∀ i, ¬ (h i =ᶠ[nhds (0 : Fin (n + 1) → ℝ)] fun _ => 0)) :
    ∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧
      ∀ i, ¬ ((fun t : ℝ => h i (t • v)) =ᶠ[nhds (0 : ℝ)] fun _ => 0) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨Pi.single (0 : Fin (n + 1)) (1 : ℝ), ?_, ?_⟩
    · intro hcon
      have hthis := congrFun hcon 0
      rw [Pi.single_eq_same] at hthis
      exact one_ne_zero hthis
    · intro i
      exact i.elim0
  · have hch : ∀ i, ∃ r : ENNReal, 0 < r ∧ AnalyticOnNhd ℝ (h i) (Metric.eball 0 r) :=
      fun i => exists_ball_analyticOnNhd (hA i)
    choose r hrpos hran using hch
    have hnbh : (⋂ i, Metric.eball (0 : Fin (n + 1) → ℝ) (r i)) ∈ 𝓝 (0 : Fin (n + 1) → ℝ) := by
      rw [Filter.iInter_mem]
      intro i
      exact Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self (hrpos i))
    obtain ⟨R, hRpos, hRsub⟩ := Metric.mem_nhds_iff.mp hnbh
    have hRsub' : ∀ i, Metric.ball (0 : Fin (n + 1) → ℝ) R ⊆ Metric.eball 0 (r i) :=
      fun i x hx => Set.mem_iInter.mp (hRsub hx) i
    have hcont : ∀ i, ContinuousOn (h i) (Metric.ball (0 : Fin (n + 1) → ℝ) R) :=
      fun i => ((hran i).mono (hRsub' i)).continuousOn
    -- A single analytic non-flat function is nonzero somewhere in every nonempty open subset
    -- of the ball.
    have key : ∀ i, ∀ S : Set (Fin (n + 1) → ℝ), IsOpen S → S.Nonempty →
        S ⊆ Metric.ball (0 : Fin (n + 1) → ℝ) R → ∃ x ∈ S, h i x ≠ 0 := by
      intro i S hSop hSne hSsub
      by_contra hcon
      push_neg at hcon
      obtain ⟨x₀, hx₀S⟩ := hSne
      have hx₀ : x₀ ∈ Metric.ball (0 : Fin (n + 1) → ℝ) R := hSsub hx₀S
      have hev : h i =ᶠ[𝓝 x₀] 0 := by
        filter_upwards [hSop.mem_nhds hx₀S] with y hy
        exact hcon y hy
      have hanaly : AnalyticOnNhd ℝ (h i) (Metric.ball (0 : Fin (n + 1) → ℝ) R) :=
        (hran i).mono (hRsub' i)
      have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hanaly
        Metric.isPreconnected_ball hx₀ hev
      have hgerm : h i =ᶠ[𝓝 (0 : Fin (n + 1) → ℝ)] 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : Fin (n + 1) → ℝ) hRpos] with y hy
        exact hzero hy
      exact (hNZ i) hgerm
    -- Shrinking the open set successively avoids the finitely many zero sets.
    have key2 : ∀ (s : Finset (Fin k)), ∀ S : Set (Fin (n + 1) → ℝ), IsOpen S → S.Nonempty →
        S ⊆ Metric.ball (0 : Fin (n + 1) → ℝ) R → ∃ x ∈ S, ∀ i ∈ s, h i x ≠ 0 := by
      intro s
      induction s using Finset.induction with
      | empty =>
          intro S hSop hSne hSsub
          obtain ⟨x, hx⟩ := hSne
          exact ⟨x, hx, by simp⟩
      | insert a s has ih =>
          intro S hSop hSne hSsub
          have hWopen : IsOpen (Metric.ball (0 : Fin (n + 1) → ℝ) R ∩ {y | h a y ≠ 0}) :=
            (hcont a).isOpen_inter_preimage Metric.isOpen_ball (isOpen_ne (x := (0 : ℝ)))
          have hSne' :
              (S ∩ (Metric.ball (0 : Fin (n + 1) → ℝ) R ∩ {y | h a y ≠ 0})).Nonempty := by
            obtain ⟨x, hx, hxh⟩ := key a S hSop hSne hSsub
            exact ⟨x, hx, hSsub hx, hxh⟩
          have hSsub' : S ∩ (Metric.ball (0 : Fin (n + 1) → ℝ) R ∩ {y | h a y ≠ 0}) ⊆
              Metric.ball (0 : Fin (n + 1) → ℝ) R := fun y hy => hy.2.1
          obtain ⟨x, hxS, hxH⟩ :=
            ih (S ∩ (Metric.ball (0 : Fin (n + 1) → ℝ) R ∩ {y | h a y ≠ 0}))
              (hSop.inter hWopen) hSne' hSsub'
          refine ⟨x, hxS.1, ?_⟩
          intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · exact hxS.2.2
          · exact hxH i hi
    have hbne : (Metric.ball (0 : Fin (n + 1) → ℝ) R).Nonempty :=
      ⟨0, Metric.mem_ball_self hRpos⟩
    obtain ⟨v, hvball, hvne⟩ := key2 Finset.univ (Metric.ball (0 : Fin (n + 1) → ℝ) R)
      Metric.isOpen_ball hbne (fun _ hx => hx)
    have hvne' : ∀ i, h i v ≠ 0 := fun i => hvne i (Finset.mem_univ i)
    have hv0 : v ≠ 0 := by
      intro hv
      have h1 : h ⟨0, hk⟩ v = 0 := by rw [hv, h0 ⟨0, hk⟩]
      exact hvne' ⟨0, hk⟩ h1
    exact ⟨v, hv0,
      fun i => not_eventuallyEq_zero_smul (hrpos i) (hran i) (hRsub' i hvball) (hvne' i)⟩

end Work.WilC4aRW.Dir
