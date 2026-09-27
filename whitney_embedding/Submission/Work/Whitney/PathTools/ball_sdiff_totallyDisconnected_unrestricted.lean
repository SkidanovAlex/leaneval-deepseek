import Mathlib
import Submission.Work.Whitney.PathTools.exists_isometry_plane_through
import Submission.Work.Whitney.PathTools.planar_ball_sdiff_totallyDisconnected

namespace Work.Whitney.PathTools

open Set Metric Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A path in the ball avoiding a closed set is the same as a path avoiding the closed set
together with the boundary sphere** (the endpoints being inside the ball). -/
lemma joinedIn_ball_sdiff_iff_compl_union_sphere {K : Set E} {c : E} {r : ℝ} {X Y : E}
    (hX : X ∈ Metric.ball c r) (_hY : Y ∈ Metric.ball c r) :
    JoinedIn (Metric.ball c r \ K) X Y ↔
      JoinedIn ((K ∪ Metric.sphere c r)ᶜ : Set E) X Y := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, fun t => ?_⟩
    obtain ⟨hb, hK⟩ := hγ t
    simp only [mem_compl_iff, mem_union, not_or]
    exact ⟨hK, fun hsphere =>
      ne_of_lt (Metric.mem_ball.mp hb) (Metric.mem_sphere.mp hsphere)⟩
  · rintro ⟨γ, hγ⟩
    have hγ' : ∀ t, γ t ∉ K ∧ γ t ∉ Metric.sphere c r := by
      intro t; simpa only [mem_compl_iff, mem_union, not_or] using hγ t
    refine ⟨γ, fun t => ?_⟩
    have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
    have hsub : Set.range γ ⊆ Metric.ball c r ∪ (Metric.closedBall c r)ᶜ := by
      rintro _ ⟨s, rfl⟩
      by_cases hlt : dist (γ s) c < r
      · exact Or.inl (Metric.mem_ball.mpr hlt)
      · refine Or.inr ?_
        simp only [mem_compl_iff, Metric.mem_closedBall, not_le]
        exact lt_of_le_of_ne (le_of_not_gt hlt)
          (fun h => (hγ' s).2 (Metric.mem_sphere.mpr h.symm))
    have hdisj : Set.range γ ∩ (Metric.ball c r ∩ (Metric.closedBall c r)ᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro _ ⟨-, hb, hc⟩
      exact hc (Metric.ball_subset_closedBall hb)
    rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) (Metric.ball c r)
        ((Metric.closedBall c r)ᶜ) Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl
        hsub hdisj with h | h
    · exact ⟨h ⟨t, rfl⟩, (hγ' t).1⟩
    · exact absurd (h ⟨0, γ.source⟩) (by
        simp only [mem_compl_iff, Metric.mem_closedBall, not_le]
        exact not_lt.mpr (le_of_lt (Metric.mem_ball.mp hX)))

variable [FiniteDimensional ℝ E]

/-- The ball minus a compact totally disconnected set is nonempty. -/
lemma ball_sdiff_nonempty_of_isTotallyDisconnected (hm : 2 ≤ Module.finrank ℝ E)
    {K : Set E} (htd : IsTotallyDisconnected K) {c : E} {r : ℝ} (hr : 0 < r) :
    (Metric.ball c r \ K).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : Metric.ball c r ⊆ K := Set.sdiff_eq_empty.mp h
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  have hsing : (Metric.ball c r).Subsingleton := htd _ hsub Metric.isPreconnected_ball
  obtain ⟨u, hu⟩ : ∃ u : E, u ≠ 0 := exists_ne 0
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hmem : c + (r / (2 * ‖u‖)) • u ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    rw [show r / (2 * ‖u‖) * ‖u‖ = r / 2 by field_simp]
    linarith
  have hne : c + (r / (2 * ‖u‖)) • u ≠ c := by
    intro hcon
    have h1 : (r / (2 * ‖u‖)) • u = 0 := by
      have h2 := congrArg (fun w : E => w - c) hcon
      simpa using h2
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact (by positivity : r / (2 * ‖u‖) ≠ 0) h2
    · exact hu h2
  exact hne (hsing (Metric.mem_ball_self hr) hmem).symm

/-- **Transport of the planar ball theorem along an isometry of a plane.**  If the planar statement
is available and `f : ℝ² → E` is an isometry hitting the centre and the two given points, then the
ball theorem holds at `X`, `Y`. -/
lemma joinedIn_ball_sdiff_of_isometry {K : Set E} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) {c : E} {r : ℝ} (hr : 0 < r) {X Y : E}
    (hX : X ∈ Metric.ball c r \ K) (hY : Y ∈ Metric.ball c r \ K)
    (f : EuclideanSpace ℝ (Fin 2) → E) (hiso : Isometry f) (hcont : Continuous f)
    (hf0 : f 0 = c) (pX pY : EuclideanSpace ℝ (Fin 2)) (hpX : f pX = X) (hpY : f pY = Y)
    (hplanar : ∀ {K' : Set (EuclideanSpace ℝ (Fin 2))}, IsCompact K' →
      IsTotallyDisconnected K' → ∀ {c' : EuclideanSpace ℝ (Fin 2)} {r' : ℝ}, 0 < r' →
      ∀ {X' Y' : EuclideanSpace ℝ (Fin 2)}, X' ∈ Metric.ball c' r' \ K' →
      Y' ∈ Metric.ball c' r' \ K' → JoinedIn (Metric.ball c' r' \ K') X' Y') :
    JoinedIn (Metric.ball c r \ K) X Y := by
  subst hpX
  subst hpY
  set K' : Set (EuclideanSpace ℝ (Fin 2)) := f ⁻¹' K with hK'def
  have hinj : Function.Injective f := hiso.injective
  have hK'closed : IsClosed K' := hK.isClosed.preimage hcont
  have hK'bdd : Bornology.IsBounded K' := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (f pX)).mp hK.isBounded
    refine (Metric.isBounded_iff_subset_closedBall pX).mpr ⟨R, ?_⟩
    intro p hp
    rw [Metric.mem_closedBall]
    have h1 : f p ∈ Metric.closedBall (f pX) R := hR hp
    rw [Metric.mem_closedBall] at h1
    rwa [hiso.dist_eq p pX] at h1
  have hK'cpt : IsCompact K' := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK'closed, hK'bdd⟩
  have hK'td : IsTotallyDisconnected K' := by
    intro S hSK hSpre
    have himg : IsPreconnected (f '' S) := hSpre.image f hcont.continuousOn
    have hsub : f '' S ⊆ K := fun z ⟨p, hp, hzp⟩ => hzp ▸ hSK hp
    have hsing : (f '' S).Subsingleton := htd _ hsub himg
    intro a ha b hb
    exact hinj (hsing ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  have hpre : ∀ p : EuclideanSpace ℝ (Fin 2),
      f p ∈ Metric.ball c r ↔ p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
    intro p
    rw [Metric.mem_ball, Metric.mem_ball, ← hf0, hiso.dist_eq]
  have hpX' : pX ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r \ K' := by
    refine ⟨(hpre pX).mp hX.1, hX.2⟩
  have hpY' : pY ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r \ K' := by
    refine ⟨(hpre pY).mp hY.1, hY.2⟩
  obtain ⟨γ, hγ⟩ := hplanar hK'cpt hK'td hr hpX' hpY'
  refine ⟨γ.map hcont, fun t => ?_⟩
  have h1 := hγ t
  exact ⟨(hpre (γ t)).mpr h1.1, fun hmem => h1.2 hmem⟩

/-- **The target statement, assuming the planar case.** -/
theorem ball_sdiff_totallyDisconnected_unrestricted_of_planar
    (hm : 2 ≤ Module.finrank ℝ E)
    (hplanar : ∀ {K : Set (EuclideanSpace ℝ (Fin 2))}, IsCompact K → IsTotallyDisconnected K →
      ∀ {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}, 0 < r →
      ∀ {X Y : EuclideanSpace ℝ (Fin 2)}, X ∈ Metric.ball c r \ K →
      Y ∈ Metric.ball c r \ K → JoinedIn (Metric.ball c r \ K) X Y)
    {c : E} {r : ℝ} (hr : 0 < r) {K : Set E} (hK : IsCompact K) (htd : IsTotallyDisconnected K) :
    IsPathConnected (Metric.ball c r \ K) := by
  refine isPathConnected_iff.mpr
    ⟨ball_sdiff_nonempty_of_isTotallyDisconnected hm htd hr, fun X hX Y hY => ?_⟩
  by_cases hXY : X = Y
  · subst hXY; exact JoinedIn.refl hX
  · obtain ⟨f, hiso, hcont, hf0, ⟨pX, hpX⟩, ⟨pY, hpY⟩⟩ := exists_isometry_plane_through hm c X Y
    exact joinedIn_ball_sdiff_of_isometry hK htd hr hX hY f hiso hcont hf0 pX pY hpX hpY hplanar

/-- In a finite dimensional real inner product space of dimension `≥ 2`, an open ball minus a
compact totally disconnected set is path connected (no hypothesis that the set lie in the ball). -/
theorem ball_sdiff_totallyDisconnected_unrestricted {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hm : 2 ≤ Module.finrank ℝ E)
    {c : E} {r : ℝ} (hr : 0 < r)
    {K : Set E} (hK : IsCompact K) (htd : IsTotallyDisconnected K) :
    IsPathConnected (Metric.ball c r \ K) :=
  ball_sdiff_totallyDisconnected_unrestricted_of_planar (E := E) hm
    (fun {K'} hK' htd' {c'} {r'} hr' {X'} {Y'} hX' hY' =>
      planar_ball_sdiff_totallyDisconnected hK' htd' hr' hX' hY') hr hK htd

end Work.Whitney.PathTools
