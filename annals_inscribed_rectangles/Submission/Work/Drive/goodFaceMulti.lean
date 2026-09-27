import Mathlib
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family

/-!
# One parameter for a *finite family* of maps carrying the Sard, face and avoidance clauses

`Work.Drive.exists_forall_good_and_notMem_family_multi` merges, at a single parameter, the two generic
conclusions (parametric Sard on each of the compact sets `K i` and avoidance of the parametrised
lower-dimensional pieces `B i j '' K₀ i j`) for a finite family of families `Φ i`.

`Work.Drive.exists_forall_good_face_and_notMem_family` adds, for **one** family, the *face* clause:
at a zero lying on a box face `z j ∈ {0,1}`, the restriction of the `z`-derivative to the
coordinate hyperplane `{v | v j = 0}` is onto.

This file performs the two merges at once: a single parameter `p` of norm `< ε` such that, for every
`i`,

* the `z`-derivative of `Φ i (p, ·)` is onto at every zero lying in `K i`
  (parametric Sard on the compact set `K i`);
* at every such zero with `z j ∈ {0,1}`, its restriction to `{v | v j = 0}` is onto;
* `Φ i (p, B i j y) ≠ 0` for every `j` and every `y ∈ K₀ i j`.

The proof is the one-step Baire argument of the two parents, run over the finite union of three
families of closed sets of empty interior: the local pieces of `Gen.exists_local_good_gen` attached
to the bad zeros of the augmented family `(q : Fin r × Option (Fin (n + 1) × Bool)) ↦ Φ q.1` on the
compact set `faceK n (K q.1) q.2` (whose `q.2 = none` component gives the plain Sard clause and whose
`q.2 = some (j, b)` component gives the face clause, see `Gen.mapFam`), and the local pieces of
`AvoidLowDim.exists_local_avoid_gen` attached to the zeros over the parametrised pieces.  The bad set
is truncated at the ball of radius `ε/2` so that the norm-restricted hypothesis `hsurj` applies at
every base point of the local analyses. -/

set_option maxHeartbeats 1000000

namespace Work.Drive

noncomputable section

theorem goodFaceMulti (m n r : ℕ)
    (K : Fin r → Set (Work.Drive.Amb n)) (hK : ∀ i, IsCompact (K i))
    (ι : Fin r → Type*) [∀ i, Fintype (ι i)]
    (X : ∀ i, ι i → Type*) [∀ i j, NormedAddCommGroup (X i j)] [∀ i j, NormedSpace ℝ (X i j)]
    [∀ i j, FiniteDimensional ℝ (X i j)] (hX : ∀ i j, Module.finrank ℝ (X i j) < n)
    (B : ∀ i, (j : ι i) → X i j → Work.Drive.Amb n)
    (hB : ∀ i j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i j))
    (K₀ : ∀ i, (j : ι i) → Set (X i j)) (hK₀ : ∀ i j, IsCompact (K₀ i j))
    (Φ : Fin r → Work.Drive.Gen.Pm m × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ i))
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (i : Fin r) (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n),
      ‖p‖ < ε → (z ∈ K i ∨ ∃ j, z ∈ B i j '' K₀ i j) → Φ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ (i : Fin r) (z : Work.Drive.Amb n), z ∈ K i → Φ i (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ i (p, z')) z)) ∧
      (∀ (i : Fin r) (j : Fin (n + 1)) (z : Work.Drive.Amb n), z ∈ K i → Φ i (p, z) = 0 →
        (z j = 0 ∨ z j = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb n // v j = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb n => Φ i (p, z')) z v.1)) ∧
      (∀ (i : Fin r) (j : ι i) (y : X i j), y ∈ K₀ i j → Φ i (p, B i j y) ≠ 0) := by
  classical
  -- ## the truncation radius
  set R : ℝ := ε / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  -- ## the augmented family of good clauses: the plain maps and their face maps
  have hqsmooth : ∀ q : Fin r × Option (Fin (n + 1) × Bool),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gen.mapFam (Φ q.1) q.2) := by
    intro q
    obtain ⟨i, o⟩ := q
    cases o with
    | none => simpa only [Gen.mapFam_none] using hΦ i
    | some jb =>
      obtain ⟨j, b⟩ := jb
      simpa only [Gen.mapFam_some] using Gen.PhiIc_contDiff (Φ i) (hΦ i) j (Gen.cval b)
  have hqcompact : ∀ q : Fin r × Option (Fin (n + 1) × Bool), IsCompact (faceK n (K q.1) q.2) := by
    intro q
    obtain ⟨i, o⟩ := q
    cases o with
    | none => simpa only [faceK_none] using hK i
    | some jb =>
      obtain ⟨j, b⟩ := jb
      rw [faceK_some]
      exact IsCompact.of_isClosed_subset (hK i)
        ((hK i).isClosed.inter (isClosed_eq (by fun_prop) continuous_const))
        Set.inter_subset_left
  have hqsurj : ∀ (q : Fin r × Option (Fin (n + 1) × Bool)) (p : Gen.Pm m) (z : Amb n),
      ‖p‖ < ε → z ∈ faceK n (K q.1) q.2 → Gen.mapFam (Φ q.1) q.2 (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Gen.mapFam (Φ q.1) q.2 (p', z)) p) := by
    intro q
    obtain ⟨i, o⟩ := q
    cases o with
    | none =>
      intro p z hp hz h0
      exact hsurj i p z hp (Or.inl hz) h0
    | some jb =>
      obtain ⟨j, b⟩ := jb
      intro p z hp hz h0
      rw [faceK_some] at hz
      have hzK : z ∈ K i := hz.1
      have hzj : z j = Gen.cval b := hz.2
      have h0' : Φ i (p, z) = 0 := by
        have h := h0
        simp only [Gen.mapFam_some, Gen.PhiIc] at h
        rwa [← hzj, Gen.faceMap_self] at h
      have h := hsurj i p z hp (Or.inl hzK) h0'
      simpa only [Gen.mapFam_some, Gen.PhiIc, ← hzj, Gen.faceMap_self] using h
  -- ## the bad sets
  set BadGood : Set (EuclideanSpace ℝ (Fin m)) :=
    ⋃ q : Fin r × Option (Fin (n + 1) × Bool),
      badSetK m n (faceK n (K q.1) q.2) (Gen.mapFam (Φ q.1) q.2) with hBadGood
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
    -- ## the local pieces of the augmented good clauses
    have hgood : ∀ q : Fin r × Option (Fin (n + 1) × Bool),
        ∃ (s : Finset ↥(goodBadPt m n p₀ (ρ / 2) (faceK n (K q.1) q.2)
            (Gen.mapFam (Φ q.1) q.2)))
          (A : ↥(goodBadPt m n p₀ (ρ / 2) (faceK n (K q.1) q.2)
            (Gen.mapFam (Φ q.1) q.2)) → Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        (∀ p ∈ Metric.closedBall p₀ (ρ / 2),
          p ∈ badSetK m n (faceK n (K q.1) q.2) (Gen.mapFam (Φ q.1) q.2) →
          ∃ x ∈ s, p ∈ A x) := by
      intro q
      have hloc : ∀ x : ↥(goodBadPt m n p₀ (ρ / 2) (faceK n (K q.1) q.2)
            (Gen.mapFam (Φ q.1) q.2)),
          ∃ (U : Set (EuclideanSpace ℝ (Fin m) × Amb n))
            (A : Set (EuclideanSpace ℝ (Fin m))),
            IsOpen U ∧ (x.1 : EuclideanSpace ℝ (Fin m) × Amb n) ∈ U ∧
              IsCompact A ∧ interior A = ∅ ∧
            ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Amb n), (p, z) ∈ U →
              Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
                Gen.mapFam (Φ q.1) q.2 (p', z)) p) →
              Gen.mapFam (Φ q.1) q.2 (p, z) = 0 →
              ¬ Function.Surjective
                (fderiv ℝ (fun z' : Amb n => Gen.mapFam (Φ q.1) q.2 (p, z')) z) → p ∈ A := by
        intro x
        obtain ⟨hx1, hx2, hx3, hx4⟩ := x.2
        obtain ⟨U, hU1, hU2, A, hA1, hA2, hA3⟩ :=
          Gen.exists_local_good_gen m n (Gen.mapFam (Φ q.1) q.2) (hqsmooth q)
            x.1.1 x.1.2 hx3 (hqsurj q x.1.1 x.1.2 (hnorm x.1.1 hx1) hx2 hx3)
        exact ⟨U, A, hU1, hU2, hA1, hA2, hA3⟩
      choose U A hUopen hxU hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ :=
        (goodBadPt_isCompact m n p₀ (ρ / 2) (faceK n (K q.1) q.2) (hqcompact q)
          (Gen.mapFam (Φ q.1) q.2) (hqsmooth q)).elim_finite_subcover
          (fun x => U x) (fun x => hUopen x)
          (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
      exact ⟨s, A, (fun x _ => ⟨hAcomp x, hAint x⟩), (fun p hp hbad => by
        obtain ⟨z, hz, hz0, hzsurj⟩ := hbad
        have hxZ : (p, z) ∈ goodBadPt m n p₀ (ρ / 2) (faceK n (K q.1) q.2)
            (Gen.mapFam (Φ q.1) q.2) := ⟨hp, hz, hz0, hzsurj⟩
        obtain ⟨x, hxs, hxU'⟩ := Set.mem_iUnion₂.mp (hs hxZ)
        exact ⟨x, hxs, hAprop x p z hxU' (hqsurj q p z (hnorm p hp) hz hz0) hz0 hzsurj⟩)⟩
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
    let F : (Σ q : Fin r × Option (Fin (n + 1) × Bool), ↥(sG q)) ⊕
        (Σ e : (Σ i : Fin r, ι i), ↥(sV e.1 e.2)) → Set (EuclideanSpace ℝ (Fin m)) :=
      fun q => q.elim (fun qo => AG qo.1 qo.2) (fun qi => AV qi.1.1 qi.1.2 qi.2)
    have hFclosed : ∀ q, IsClosed (F q) := by
      rintro (⟨q, x⟩ | ⟨⟨i, j⟩, x⟩)
      · exact ((hAG q).1 x x.2).1.isClosed
      · exact ((hAV i j).1 x x.2).1.isClosed
    have hFempty : ∀ q, interior (F q) = ∅ := by
      rintro (⟨q, x⟩ | ⟨⟨i, j⟩, x⟩)
      · exact ((hAG q).1 x x.2).2
      · exact ((hAV i j).1 x x.2).2
    have hbaire : interior (⋃ q, F q) = ∅ :=
      Work.Sard.wp.interior_eq_empty_iUnion_isClosed hFclosed hFempty
    have hcover : Metric.closedBall p₀ (ρ / 2) ⊆ ⋃ q, F q := by
      intro p hp
      have hpBad : p ∈ Bad := (hsub hp).1
      rw [hBad] at hpBad
      rcases hpBad with hpG | hpV
      · rw [hBadGood] at hpG
        obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hpG
        obtain ⟨x, hxs, hpx⟩ := (hAG q).2 p hp hq
        exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨q, ⟨x, hxs⟩⟩, hpx⟩
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
  refine ⟨p, by linarith, ?_, ?_, hpAvoid⟩
  · intro i z hz h0
    by_contra hbadz
    refine hpGood ?_
    rw [hBadGood]
    exact Set.mem_iUnion.mpr ⟨(i, none), by
      show p ∈ badSetK m n (K i) (Φ i)
      exact ⟨z, hz, h0, hbadz⟩⟩
  · intro i j z hzK h0 hzj
    set b : Bool := Gen.boolOf (z j) with hb
    have hcb : Gen.cval b = z j := Gen.cval_boolOf hzj
    have hzface : z ∈ faceK n (K i) (some (j, b)) := by
      rw [faceK_some]
      exact ⟨hzK, hcb.symm⟩
    have h0face : Gen.mapFam (Φ i) (some (j, b)) (p, z) = 0 := by
      rw [Gen.mapFam_some]
      show Φ i (p, Gen.faceMap j (Gen.cval b) z) = 0
      rw [hcb, Gen.faceMap_self]
      exact h0
    have hsurjz : Function.Surjective
        (fderiv ℝ (fun z' : Amb n => Gen.mapFam (Φ i) (some (j, b)) (p, z')) z) := by
      by_contra hbadz
      refine hpGood ?_
      rw [hBadGood]
      exact Set.mem_iUnion.mpr ⟨(i, some (j, b)), by
        show p ∈ badSetK m n (faceK n (K i) (some (j, b)))
          (Gen.mapFam (Φ i) (some (j, b)))
        exact ⟨z, hzface, h0face, hbadz⟩⟩
    have h1 : fderiv ℝ (fun z' : Amb n => Gen.mapFam (Φ i) (some (j, b)) (p, z')) z
        = (fderiv ℝ (fun w : Amb n => Φ i (p, w)) z).comp (Gen.faceLin j) := by
      have hfaceb : Gen.faceMap j (Gen.cval b) z = z := by rw [hcb, Gen.faceMap_self]
      have h := Gen.fderiv_PhiIc (Φ i) (hΦ i) j (Gen.cval b) p z
      rw [hfaceb] at h
      exact h
    have hD : Function.Surjective
        ((fderiv ℝ (fun w : Amb n => Φ i (p, w)) z).comp (Gen.faceLin j)) := by
      rw [← h1]
      exact hsurjz
    exact (Gen.surjective_comp_faceLin_iff _ j).mp hD

end

end Work.Drive
