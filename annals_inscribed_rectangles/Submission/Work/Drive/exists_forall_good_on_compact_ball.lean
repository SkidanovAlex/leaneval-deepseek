import Mathlib
import Submission.Work.Drive.exists_forall_good_on_compact
import Submission.Work.Drive.Interfaces

/-!
# Parametric Sard on a compact set, with the parameter hypothesis localised to a ball

`Work.Drive.exists_forall_good_on_compact` proves: for a smooth family `Φ : ℝ^m × ℝ^{n+1} → ℝ^n`
whose parameter-derivative is surjective at every zero lying in a compact set `K`, there are
parameters of arbitrarily small norm at which the `z`-derivative is surjective at every zero in `K`.

Here we need the *lokalised hypothesis* form: the parameter-derivative is only assumed surjective at
zeros whose parameter already lies in the closed ball of radius `ε₀`.  This is the form that a
*local* application of the Sard argument needs: when the family is only smooth (or only transverse)
on a chart region, the surjectivity of the parameter-derivative should not be required for
parameters outside that region.

The proof is verbatim the Baire argument of the sibling, with the bad parameter set intersected with
the closed ball `‖p‖ ≤ ε₀`: if that set had interior, a bad parameter `p₀` together with a ball
`B (p₀, ε') ⊆ Bad` would give a compact set of bad zeros over `closedBall p₀ (ε'/2) ×ˢ K`.  Since
`Bad ⊆ closedBall 0 ε₀`, every parameter arising there satisfies `‖p‖ ≤ ε₀`, so the `K`-localised
surjectivity hypothesis applies at every bad zero, and the local Sard lemma
`Work.Drive.Gen.exists_local_good_gen` produces, for each bad zero, a compact set of empty interior
containing all offending parameters nearby.  Finitely many of these cover `closedBall p₀ (ε'/2)`,
contradicting Baire.  Then `Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty` yields
`p` with `‖p‖ < ε` outside `Bad`; since `ε < ε₀` such a `p` lies in the ball, so `p ∉ Bad` is
exactly the required conclusion.

Non-vacuity: `K := Submission.Drive.unitBox n` and `ε₀ > ε` arbitrary recovers
`Work.Drive.exists_forall_good_on_compact` in the special case where the hypothesis happens to hold
on all of `ℝ^m`; and the hypothesis is genuinely weaker than the sibling's, e.g. it allows the
family to be transverse only near the origin.
-/

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

/-- **Parametric Sard on a compact set with a localised parameter hypothesis.**  Let
`Φ : ℝ^m × ℝ^{n+1} → ℝ^n` be smooth and suppose that at every zero of `Φ` lying in the compact set
`K` whose parameter satisfies `‖p‖ ≤ ε₀`, the parameter-derivative `p ↦ Φ (p, z)` is surjective.
Then for some parameter `p` with `‖p‖ < ε` (`ε < ε₀`), the `z`-derivative of `Φ (p, ·)` is
surjective at *every* zero lying in `K`. -/
theorem exists_forall_good_on_compact_ball (m n : ℕ) (K : Set (Work.Drive.Amb n))
    (hK : IsCompact K) (ε₀ ε : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), ‖p‖ ≤ ε₀ → z ∈ K →
      Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      ∀ z ∈ K, Φ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z) := by
  classical
  -- The set of parameters inside the ball at which some zero in `K` fails to be `z`-regular.
  set Bad : Set (EuclideanSpace ℝ (Fin m)) :=
    {p | ‖p‖ ≤ ε₀ ∧ ∃ z ∈ K, Φ (p, z) = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z)} with hBad
  -- Every element of `Bad` lies in the ball on which the hypothesis is available.
  have hnorm : ∀ p ∈ Bad, ‖p‖ ≤ ε₀ := by
    intro p hp
    simpa only [hBad, Set.mem_ofPred_eq] using hp.1
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
      fun x => by
        obtain ⟨hball, hzK, hΦz, hbadz⟩ := x.2
        exact Gen.exists_local_good_gen m n Φ hΦ x.1.1 x.1.2 hΦz
          (hsurj x.1.1 x.1.2 (hnorm x.1.1 (hBsub hball)) hzK hΦz)
    choose U hU using hchoice
    obtain ⟨s, hs⟩ := hKp_compact.elim_finite_subcover U (fun x => (hU x).1)
      (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩)
    have hBsub2 : Metric.closedBall p₀ (ε' / 2) ⊆ ⋃ y : s, (hU (y : Kp)).2.2.choose := by
      intro p hp
      have hpBad : p ∈ Bad := hBsub hp
      obtain ⟨hpnorm, z, hzK, hΦz, hbadz⟩ := hpBad
      have hxK : (p, z) ∈ Kp := ⟨hp, hzK, hΦz, hbadz⟩
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxK)
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hU (y : Kp)).2.2.choose_spec.2.2 p z hxy
        (hsurj p z hpnorm hzK hΦz) hΦz hbadz⟩
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
  exact hp ⟨le_of_lt (lt_trans hpball hεε₀), z, hz, h0, hbad⟩

end

end Work.Drive
