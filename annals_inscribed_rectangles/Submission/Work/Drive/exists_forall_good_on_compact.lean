import Mathlib
import Submission.Work.Drive.generic_regularization_gen

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

/-- **Parametric Sard on a compact parameter set.**  The local form of the workspace's parametric-Sard result (whose parameter set is the unit box): for a smooth family, if at every zero lying in a compact set `K` the parameter-derivative is surjective, then for parameters of arbitrarily small norm the `z`-derivative is surjective at every zero lying in `K`.

The two relaxations with respect to the box form are what a *local* application needs: when the family is only smooth on a chart region, the zeros outside that region are artefacts of the junk extension of the chart, and neither their transversality nor the surjectivity of the parameter-derivative at them should be required.

Everything the box proof of `Work.Drive.generic_regularization_gen` uses is available in the localized setting: the local lemma `Work.Drive.Gen.exists_local_good_gen` (which consumes the parameter-surjectivity hypothesis only at the bad zero itself, hence is supplied by the `K`-restricted hypothesis here), the compactness of `Metric.closedBall 0 k ×ˢ K` together with the closedness of `{Φ = 0}` and of the set where the `z`-derivative fails to be surjective, and the Baire step `Work.Sard.wp.interior_eq_empty_iUnion_isClosed`.  The helper `exists_norm_lt_notMem_of_interior_eq_empty` converts `interior Bad = ∅` into the existence of `p` with `‖p‖ < ε`.

Non-vacuous: taking `K` to be `Submission.Drive.unitBox n` recovers the box form a fortiori; the hypothesis is weakest when `K` is small. -/
theorem exists_forall_good_on_compact (m n : ℕ) (K : Set (Work.Drive.Amb n)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε)
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), z ∈ K → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      ∀ z ∈ K, Φ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z) := by
  classical
  -- The set of parameters at which some zero in `K` fails to be `z`-regular.
  set Bad : Set (EuclideanSpace ℝ (Fin m)) :=
    {p | ∃ z ∈ K, Φ (p, z) = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z)} with hBad
  -- The `z`-derivative depends continuously on the base point.
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n =>
      (fderiv ℝ Φ x).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Work.Drive.Amb n))) := by
    have h1 : Continuous (fun T : (EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n) →L[ℝ]
        Work.Drive.Tgt n =>
        T.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Work.Drive.Amb n))) := by
      have h := (ContinuousLinearMap.compL ℝ (Work.Drive.Amb n)
          (EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n) (Work.Drive.Tgt n)).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n) →L[ℝ] Work.Drive.Tgt n =>
            ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Work.Drive.Amb n)))
      simpa using h
    exact h1.comp (hΦ.continuous_fderiv (by simp))
  -- The bad set has empty interior.
  have hBad_int : interior Bad = ∅ := by
    by_contra hne
    obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨ε', hε'pos, hε'sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp₀)
    have hBsub : Metric.closedBall p₀ (ε' / 2) ⊆ Bad := by
      intro p hp
      refine interior_subset (hε'sub ?_)
      rw [Metric.mem_ball]
      have h := Metric.mem_closedBall.mp hp
      linarith [hε'pos]
    have hBint : (interior (Metric.closedBall p₀ (ε' / 2))).Nonempty :=
      ⟨p₀, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
        (Metric.mem_ball_self (by linarith [hε'pos]))⟩
    -- the compact set of bad zeros over the closed ball
    set Kp : Set (EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n) :=
      {x | x.1 ∈ Metric.closedBall p₀ (ε' / 2) ∧ x.2 ∈ K ∧ Φ x = 0 ∧
        ¬ Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (x.1, z')) x.2)}
      with hKp
    have hKp_eq : Kp = ((Metric.closedBall p₀ (ε' / 2) ×ˢ K) ∩
        {x : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n | Φ x = 0}) ∩
        {x : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n | ¬ Function.Surjective
          ((fderiv ℝ Φ x).comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m))
            (Work.Drive.Amb n)))} := by
      rw [hKp]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
      rw [← Work.MetricSquare.fd_comp_inr Φ hΦ x.1 x.2]
      tauto
    have hKp_compact : IsCompact Kp := by
      rw [hKp_eq]
      have hc1 : IsClosed ((Metric.closedBall p₀ (ε' / 2) ×ˢ K) ∩
          {x : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n | Φ x = 0}) :=
        ((isCompact_closedBall p₀ (ε' / 2)).isClosed.prod hK.isClosed).inter
          (isClosed_eq hΦ.continuous continuous_const)
      have hc2 : IsClosed {x : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n |
          ¬ Function.Surjective ((fderiv ℝ Φ x).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Work.Drive.Amb n)))} :=
        Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
      exact IsCompact.of_isClosed_subset
        ((isCompact_closedBall p₀ (ε' / 2)).prod hK)
        (hc1.inter hc2) (fun x hx => hx.1.1)
    -- the local neighbourhoods of the bad zeros
    have hchoice : ∀ x : Kp,
        ∃ U : Set (EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n),
          IsOpen U ∧ (x.1 : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n) ∈ U ∧
          ∃ A : Set (EuclideanSpace ℝ (Fin m)), IsCompact A ∧ interior A = ∅ ∧
            (∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), (p, z) ∈ U →
              Function.Surjective
                (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p) →
              Φ (p, z) = 0 →
              ¬ Function.Surjective
                (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z) → p ∈ A) :=
      fun x => Gen.exists_local_good_gen m n Φ hΦ x.1.1 x.1.2 x.2.2.2.1
        (hsurj x.1.1 x.1.2 x.2.2.1 x.2.2.2.1)
    choose U hU using hchoice
    obtain ⟨s, hs⟩ := hKp_compact.elim_finite_subcover U (fun x => (hU x).1)
      (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩)
    have hBsub2 : Metric.closedBall p₀ (ε' / 2) ⊆ ⋃ y : s, (hU (y : Kp)).2.2.choose := by
      intro p hp
      have hpBad : p ∈ Bad := hBsub hp
      obtain ⟨z, hzK, hΦz, hbadz⟩ := hpBad
      have hxK : (p, z) ∈ Kp := ⟨hp, hzK, hΦz, hbadz⟩
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxK)
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hU (y : Kp)).2.2.choose_spec.2.2 p z hxy
        (hsurj p z hzK hΦz) hΦz hbadz⟩
    have hclosedA : ∀ y : s, IsClosed ((hU (y : Kp)).2.2.choose) :=
      fun y => (hU (y : Kp)).2.2.choose_spec.1.isClosed
    have hemptyA : ∀ y : s, interior ((hU (y : Kp)).2.2.choose) = ∅ :=
      fun y => (hU (y : Kp)).2.2.choose_spec.2.1
    have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hclosedA hemptyA
    have hsubInt : interior (Metric.closedBall p₀ (ε' / 2)) ⊆
        interior (⋃ y : s, (hU (y : Kp)).2.2.choose) := interior_mono hBsub2
    rw [hBaire] at hsubInt
    exact hBint.ne_empty (Set.Subset.antisymm hsubInt (Set.empty_subset _))
  obtain ⟨p, hpball, hp⟩ :=
    Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty Bad hBad_int hε
  refine ⟨p, hpball, ?_⟩
  intro z hz h0
  by_contra hbad
  exact hp ⟨z, hz, h0, hbad⟩

end

end Work.Drive
