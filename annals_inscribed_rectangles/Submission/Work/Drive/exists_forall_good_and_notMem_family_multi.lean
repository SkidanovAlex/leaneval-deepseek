import Mathlib
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family
import Submission.Work.Drive.BoxParityDefs

/-!
# One parameter for the Sard clauses of a *finite family* of maps and the avoidance clauses

`Work.Drive.exists_forall_good_face_and_notMem_family` merges, at a single parameter `p`, the two
generic conclusions (parametric Sard on a compact set and avoidance of parametrised
lower-dimensional pieces) for **one** family `Φ`.  Here the same merge is performed for a finite
family `Φ i` (`i : Fin r`) of families, each with its own compact set `K i` carrying the Sard clause
and its own finite family of parametrised pieces `B i j '' K₀ i j` (`j : ι i`) carrying the
avoidance clause.

The proof is the one-step Baire argument of the sibling: the bad parameter set is the union of the
bad Sard sets `badSetK m n (K i) (Φ i)` and the bad avoidance sets
`{p | ∃ i j y ∈ K₀ i j, Φ i (p, B i j y) = 0}`; it is truncated at the ball of radius `ε/2` so that
the norm-restricted hypothesis `hsurj` applies at every base point of the local analyses.  The local
pieces of `Gen.exists_local_good_gen` (attached to the bad zeros of the Sard clauses) and of
`AvoidLowDim.exists_local_avoid_gen` (attached to the zeros over the parametrised pieces) are
closed sets of empty interior, finitely many of which cover the truncated bad set; Baire then
contradicts the nonemptiness of the interior of the truncated ball, and
`Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty` extracts the parameter. -/

set_option maxHeartbeats 1000000

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

theorem exists_forall_good_and_notMem_family_multi (m n r : ℕ)
    (K : Fin r → Set (Work.Drive.Amb n)) (hK : ∀ i, IsCompact (K i))
    (ι : Fin r → Type*) [∀ i, Fintype (ι i)]
    (X : ∀ i, ι i → Type*) [∀ i j, NormedAddCommGroup (X i j)] [∀ i j, NormedSpace ℝ (X i j)]
    [∀ i j, FiniteDimensional ℝ (X i j)] (hX : ∀ i j, Module.finrank ℝ (X i j) < n)
    (B : ∀ i, (j : ι i) → X i j → Work.Drive.Amb n)
    (hB : ∀ i j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i j))
    (K₀ : ∀ i, (j : ι i) → Set (X i j)) (hK₀ : ∀ i j, IsCompact (K₀ i j))
    (Φ : Fin r → EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ i))
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (i : Fin r) (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), ‖p‖ < ε →
      (z ∈ K i ∨ ∃ j, z ∈ B i j '' K₀ i j) → Φ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ (i : Fin r) (z : Work.Drive.Amb n), z ∈ K i → Φ i (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ i (p, z')) z)) ∧
      (∀ (i : Fin r) (j : ι i), ∀ y ∈ K₀ i j, Φ i (p, B i j y) ≠ 0) := by
  classical
  -- the truncation radius
  set R : ℝ := ε / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRlt : R < ε := by rw [hRdef]; linarith
  -- ## the bad sets
  set BadGood : Set (EuclideanSpace ℝ (Fin m)) :=
    ⋃ i : Fin r, badSetK m n (K i) (Φ i) with hBadGood
  set BadAvoid : Set (EuclideanSpace ℝ (Fin m)) :=
    {p | ∃ (i : Fin r) (j : ι i), ∃ y ∈ K₀ i j, Φ i (p, B i j y) = 0} with hBadAvoid
  set Bad : Set (EuclideanSpace ℝ (Fin m)) := BadGood ∪ BadAvoid with hBad
  -- ## the truncated bad set has empty interior
  have hBadR : interior (Bad ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R) = ∅ := by
    by_contra hne
    obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp₀)
    have hsub : Metric.closedBall p₀ (ρ / 2) ⊆ Bad ∩ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin m)) R := by
      intro p hp
      refine interior_subset (hρsub ?_)
      rw [Metric.mem_ball]
      have h2 := Metric.mem_closedBall.mp hp
      linarith
    have hnorm : ∀ p ∈ Metric.closedBall p₀ (ρ / 2), ‖p‖ < ε := by
      intro p hp
      have h1 := (hsub hp).2
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      linarith
    -- ## the local pieces of the Sard clauses
    have hgood : ∀ i : Fin r,
        ∃ (s : Finset ↥(goodBadPt m n p₀ (ρ / 2) (K i) (Φ i)))
          (A : ↥(goodBadPt m n p₀ (ρ / 2) (K i) (Φ i)) →
            Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        (∀ p ∈ Metric.closedBall p₀ (ρ / 2),
          p ∈ badSetK m n (K i) (Φ i) → ∃ x ∈ s, p ∈ A x) := by
      intro i
      have hloc : ∀ x : ↥(goodBadPt m n p₀ (ρ / 2) (K i) (Φ i)),
          ∃ (U : Set (EuclideanSpace ℝ (Fin m) × Amb n))
            (A : Set (EuclideanSpace ℝ (Fin m))),
            IsOpen U ∧ (x.1 : EuclideanSpace ℝ (Fin m) × Amb n) ∈ U ∧
              IsCompact A ∧ interior A = ∅ ∧
            ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Amb n), (p, z) ∈ U →
              Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
                Φ i (p', z)) p) →
              Φ i (p, z) = 0 →
              ¬ Function.Surjective
                (fderiv ℝ (fun z' : Amb n => Φ i (p, z')) z) → p ∈ A := by
        intro x
        obtain ⟨hx1, hx2, hx3, hx4⟩ := x.2
        obtain ⟨U, hU1, hU2, A, hA1, hA2, hA3⟩ :=
          Gen.exists_local_good_gen m n (Φ i) (hΦ i) x.1.1 x.1.2 hx3
            (hsurj i x.1.1 x.1.2 (hnorm x.1.1 hx1) (Or.inl hx2) hx3)
        exact ⟨U, A, hU1, hU2, hA1, hA2, hA3⟩
      choose U A hUopen hxU hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ :=
        (goodBadPt_isCompact m n p₀ (ρ / 2) (K i) (hK i) (Φ i) (hΦ i)).elim_finite_subcover
          (fun x => U x) (fun x => hUopen x)
          (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
      exact ⟨s, A, (fun x _ => ⟨hAcomp x, hAint x⟩), (fun p hp hbad => by
        obtain ⟨z, hz, hz0, hzsurj⟩ := hbad
        have hxZ : (p, z) ∈ goodBadPt m n p₀ (ρ / 2) (K i) (Φ i) := ⟨hp, hz, hz0, hzsurj⟩
        obtain ⟨x, hxs, hxU'⟩ := Set.mem_iUnion₂.mp (hs hxZ)
        exact ⟨x, hxs, hAprop x p z hxU' (hsurj i p z (hnorm p hp) (Or.inl hz) hz0) hz0
          hzsurj⟩)⟩
    -- ## the local pieces of the avoidance clauses
    have havoid : ∀ (i : Fin r) (j : ι i),
        ∃ (s : Finset ↥(avoidBadPt m n p₀ (ρ / 2) (X i j) (B i j) (K₀ i j) (Φ i)))
          (A : ↥(avoidBadPt m n p₀ (ρ / 2) (X i j) (B i j) (K₀ i j) (Φ i)) →
            Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        (∀ p ∈ Metric.closedBall p₀ (ρ / 2), ∀ y ∈ K₀ i j,
          Φ i (p, B i j y) = 0 → ∃ x ∈ s, p ∈ A x) := by
      intro i j
      have hloc : ∀ x : ↥(avoidBadPt m n p₀ (ρ / 2) (X i j) (B i j) (K₀ i j) (Φ i)),
          ∃ (W : Set (EuclideanSpace ℝ (Fin m) × X i j))
            (A : Set (EuclideanSpace ℝ (Fin m))),
            IsOpen W ∧ (x.1 : EuclideanSpace ℝ (Fin m) × X i j) ∈ W ∧
              IsCompact A ∧ interior A = ∅ ∧
            ∀ (p : EuclideanSpace ℝ (Fin m)) (y : X i j),
              (p, y) ∈ W → Φ i (p, B i j y) = 0 → p ∈ A := by
        intro x
        obtain ⟨hx1, hx2, hx3⟩ := x.2
        obtain ⟨W, hW1, hW2, A, hA1, hA2, hA3⟩ :=
          AvoidLowDim.exists_local_avoid_gen m n (hX i j) (Φ i) (hΦ i) (B i j) (hB i j)
            x.1.1 x.1.2 hx3 (hsurj i x.1.1 (B i j x.1.2) (hnorm x.1.1 hx1)
              (Or.inr ⟨j, x.1.2, hx2, rfl⟩) hx3)
        exact ⟨W, A, hW1, hW2, hA1, hA2, hA3⟩
      choose W A hWopen hxW hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ :=
        (avoidBadPt_isCompact m n p₀ (ρ / 2) (B i j) (K₀ i j) (hK₀ i j) (Φ i) (hΦ i)
          (hB i j)).elim_finite_subcover (fun x => W x) (fun x => hWopen x)
          (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
      exact ⟨s, A, (fun x _ => ⟨hAcomp x, hAint x⟩), (fun p hp y hy hzero => by
        have hxZ : (p, y) ∈ avoidBadPt m n p₀ (ρ / 2) (X i j) (B i j) (K₀ i j) (Φ i) :=
          ⟨hp, hy, hzero⟩
        obtain ⟨x, hxs, hxW'⟩ := Set.mem_iUnion₂.mp (hs hxZ)
        exact ⟨x, hxs, hAprop x p y hxW' hzero⟩)⟩
    -- ## the Baire step over the finite union of all pieces
    choose sG AG hAG using hgood
    choose sV AV hAV using havoid
    let F : (Σ i : Fin r, ↥(sG i)) ⊕ (Σ e : (Σ i : Fin r, ι i), ↥(sV e.1 e.2)) →
        Set (EuclideanSpace ℝ (Fin m)) :=
      fun q => q.elim (fun qo => AG qo.1 qo.2) (fun qi => AV qi.1.1 qi.1.2 qi.2)
    have hFclosed : ∀ q, IsClosed (F q) := by
      rintro (⟨i, x⟩ | ⟨⟨i, j⟩, x⟩)
      · exact ((hAG i).1 x x.2).1.isClosed
      · exact ((hAV i j).1 x x.2).1.isClosed
    have hFempty : ∀ q, interior (F q) = ∅ := by
      rintro (⟨i, x⟩ | ⟨⟨i, j⟩, x⟩)
      · exact ((hAG i).1 x x.2).2
      · exact ((hAV i j).1 x x.2).2
    have hbaire : interior (⋃ q, F q) = ∅ :=
      Work.Sard.wp.interior_eq_empty_iUnion_isClosed hFclosed hFempty
    have hcover : Metric.closedBall p₀ (ρ / 2) ⊆ ⋃ q, F q := by
      intro p hp
      have hpBad : p ∈ Bad := (hsub hp).1
      rw [hBad] at hpBad
      rcases hpBad with hpG | hpV
      · rw [hBadGood] at hpG
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpG
        obtain ⟨x, hxs, hpx⟩ := (hAG i).2 p hp hi
        exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i, ⟨x, hxs⟩⟩, hpx⟩
      · rw [hBadAvoid] at hpV
        obtain ⟨i, j, y, hy, hzero⟩ := hpV
        obtain ⟨x, hxs, hpx⟩ := (hAV i j).2 p hp y hy hzero
        exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨⟨i, j⟩, ⟨x, hxs⟩⟩, hpx⟩
    have hcontra : interior (Metric.closedBall p₀ (ρ / 2)) ⊆ interior (⋃ q, F q) :=
      interior_mono hcover
    rw [hbaire] at hcontra
    have hne' : (interior (Metric.closedBall p₀ (ρ / 2))).Nonempty :=
      ⟨p₀, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
        (Metric.mem_ball_self (by linarith))⟩
    exact hne'.ne_empty (Set.Subset.antisymm hcontra (Set.empty_subset _))
  -- ## extraction
  obtain ⟨p, hpnorm, hpmem⟩ :=
    Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty
      (Bad ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R) hBadR hRpos
  have hpR : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hpnorm
  have hnotBad : p ∉ Bad := fun hb => hpmem ⟨hb, hpR⟩
  have hpGood : p ∉ BadGood := fun h => hnotBad (by rw [hBad]; exact Or.inl h)
  have hpAvoid : ∀ (i : Fin r) (j : ι i), ∀ y ∈ K₀ i j, Φ i (p, B i j y) ≠ 0 := by
    intro i j y hy h0
    exact hnotBad (by rw [hBad]; exact Or.inr (by
      rw [hBadAvoid]; exact ⟨i, j, y, hy, h0⟩))
  refine ⟨p, by linarith, ?_, hpAvoid⟩
  · intro i z hz h0
    by_contra hbadz
    refine hpGood ?_
    rw [hBadGood]
    exact Set.mem_iUnion.mpr ⟨i, ⟨z, hz, h0, hbadz⟩⟩

end

end Work.Drive
