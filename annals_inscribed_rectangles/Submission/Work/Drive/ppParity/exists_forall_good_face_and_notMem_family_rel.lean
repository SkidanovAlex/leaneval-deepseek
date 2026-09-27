import Mathlib
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family

/-!
# One parameter for the Sard clauses on a prescribed subset and the avoidance clause

`Work.Drive.exists_forall_good_face_and_notMem_family` merges the parametric Sard clauses and the
avoidance clause at a single small parameter, under the hypothesis that the parameter-derivative of
`Φ` is onto at *every* zero over the compact set `K` or over the parametrised pieces
`B i '' K₀ i`.

This file proves the *relative* form used by the residency plan: the parameter-surjectivity
hypothesis is only available on a prescribed subset `S` of the ambient space `ℝ^{n+1}`, while off
`S` the regularity of the `z`-derivative (and, at a zero on a box face, of its restriction to the
coordinate hyperplane) is a *hypothesis* `hregOff`, and the avoidance clause off `S` is
`havoid`.

The proof is the Baire argument of the absolute form, with one extra observation recorded in
`hS_of_bad`: a **bad** zero at a parameter with `‖p‖ < ε` never lies off `S`.  For a zero in `K`
this is the first conjunct of `hregOff`; for a zero on a face `z j ∈ {0,1}` it is the second
conjunct of `hregOff`, converted through `Gen.surjective_comp_faceLin_iff`; for a zero over a
parametrised piece `B i '' K₀ i` it is `havoid`.  Hence the parameter-surjectivity hypothesis of
the absolute argument is available (in its `S`-relative form) at every bad point, and the Baire
step is otherwise unchanged.
-/

set_option maxHeartbeats 1000000

namespace Work.Drive.ppParity

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

theorem exists_forall_good_face_and_notMem_family_rel (m n : ℕ)
    (K : Set (Work.Drive.Amb n)) (hK : IsCompact K)
    (ι : Type*) [Fintype ι]
    (X : ι → Type*) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)] (hX : ∀ i, Module.finrank ℝ (X i) < n)
    (B : ∀ i, X i → Work.Drive.Amb n) (hB : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i))
    (K₀ : ∀ i, Set (X i)) (hK₀ : ∀ i, IsCompact (K₀ i))
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (S : Set (Work.Drive.Amb n))
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), ‖p‖ < ε →
      (z ∈ K ∨ ∃ i, z ∈ B i '' K₀ i) → Φ (p, z) = 0 → z ∈ S →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p))
    (hregOff : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), ‖p‖ < ε →
      (z ∈ K ∨ ∃ i, z ∈ B i '' K₀ i) → Φ (p, z) = 0 → z ∉ S →
      Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z) ∧
      (∀ j : Fin (n + 1), (z j = 0 ∨ z j = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb n // v j = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z v.1)))
    (havoid : ∀ (p : EuclideanSpace ℝ (Fin m)) (i : ι) (y : X i), ‖p‖ < ε → y ∈ K₀ i →
      B i y ∉ S → Φ (p, B i y) ≠ 0) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ z ∈ K, Φ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z)) ∧
      (∀ (j : Fin (n + 1)) (z : Work.Drive.Amb n), z ∈ K → Φ (p, z) = 0 →
        (z j = 0 ∨ z j = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb n // v j = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z v.1)) ∧
      (∀ i, ∀ y ∈ K₀ i, Φ (p, B i y) ≠ 0) := by
  classical
  -- the truncation radius
  set R : ℝ := ε / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRlt : R < ε := by rw [hRdef]; linarith
  -- ## the auxiliary family of the good clauses
  have hfam_smooth : ∀ o : Option (Fin (n + 1) × Bool),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gen.mapFam Φ o) := by
    intro o
    cases o with
    | none => simpa only [Gen.mapFam_none] using hΦ
    | some jb =>
      obtain ⟨j, b⟩ := jb
      simpa only [Gen.mapFam_some] using Gen.PhiIc_contDiff Φ hΦ j (Gen.cval b)
  have hfam_compact : ∀ o : Option (Fin (n + 1) × Bool), IsCompact (faceK n K o) := by
    intro o
    cases o with
    | none => rwa [faceK_none]
    | some jb =>
      obtain ⟨j, b⟩ := jb
      rw [faceK_some]
      exact IsCompact.of_isClosed_subset hK
        (hK.isClosed.inter (isClosed_eq (by fun_prop) continuous_const)) Set.inter_subset_left
  -- ## membership in `S` is forced at a bad zero
  have hS_of_bad : ∀ (o : Option (Fin (n + 1) × Bool)) (p : Gen.Pm m) (z : Amb n),
      ‖p‖ < ε → z ∈ faceK n K o → Gen.mapFam Φ o (p, z) = 0 →
      ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Gen.mapFam Φ o (p, z')) z) →
      z ∈ S := by
    intro o
    cases o with
    | none =>
      intro p z hp hz h0 hbad
      by_contra hzS
      exact hbad (hregOff p z hp (Or.inl hz) h0 hzS).1
    | some jb =>
      obtain ⟨j, b⟩ := jb
      intro p z hp hz h0 hbad
      rw [faceK_some] at hz
      have hzK : z ∈ K := hz.1
      have hzj : z j = Gen.cval b := hz.2
      have h0' : Φ (p, z) = 0 := by
        have h := h0
        simp only [Gen.mapFam_some, Gen.PhiIc] at h
        rwa [← hzj, Gen.faceMap_self] at h
      by_contra hzS
      have hreg := hregOff p z hp (Or.inl hzK) h0' hzS
      have hzj01 : z j = 0 ∨ z j = 1 := by
        rw [hzj]; cases b <;> simp [Gen.cval]
      have hface := hreg.2 j hzj01
      have hD : Function.Surjective
          ((fderiv ℝ (fun w : Amb n => Φ (p, w)) z).comp (Gen.faceLin j)) :=
        (Gen.surjective_comp_faceLin_iff _ j).mpr hface
      have h1 := Gen.fderiv_PhiIc Φ hΦ j (Gen.cval b) p z
      have hfaceb : Gen.faceMap j (Gen.cval b) z = z := by rw [← hzj, Gen.faceMap_self]
      rw [hfaceb] at h1
      have hbad' : ¬ Function.Surjective
          (fderiv ℝ (fun z' : Amb n => Gen.PhiIc Φ j (Gen.cval b) (p, z')) z) := by
        simpa only [Gen.mapFam_some] using hbad
      exact hbad' (by rw [h1]; exact hD)
  -- ## the parameter-surjectivity of the auxiliary family, given `z ∈ S`
  have hfam_surj : ∀ (o : Option (Fin (n + 1) × Bool)) (p : Gen.Pm m) (z : Amb n),
      ‖p‖ < ε → z ∈ faceK n K o → Gen.mapFam Φ o (p, z) = 0 → z ∈ S →
      Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Gen.mapFam Φ o (p', z)) p) := by
    intro o
    cases o with
    | none =>
      intro p z hp hz h0 hzS
      exact hsurj p z hp (Or.inl hz) h0 hzS
    | some jb =>
      obtain ⟨j, b⟩ := jb
      intro p z hp hz h0 hzS
      rw [faceK_some] at hz
      have hzK : z ∈ K := hz.1
      have hzj : z j = Gen.cval b := hz.2
      have h0' : Φ (p, z) = 0 := by
        have h := h0
        simp only [Gen.mapFam_some, Gen.PhiIc] at h
        rwa [← hzj, Gen.faceMap_self] at h
      have h := hsurj p z hp (Or.inl hzK) h0' hzS
      simpa only [Gen.mapFam_some, Gen.PhiIc, ← hzj, Gen.faceMap_self] using h
  -- ## the bad set
  set BadGood : Set (EuclideanSpace ℝ (Fin m)) :=
    ⋃ o : Option (Fin (n + 1) × Bool), badSetK m n (faceK n K o) (Gen.mapFam Φ o) with hBadGood
  set BadAvoid : Set (EuclideanSpace ℝ (Fin m)) :=
    {p : EuclideanSpace ℝ (Fin m) | ∃ i, ∃ y ∈ K₀ i, B i y ∈ S ∧ Φ (p, B i y) = 0} with hBadAvoid
  set Bad : Set (EuclideanSpace ℝ (Fin m)) := BadGood ∪ BadAvoid with hBad
  -- ## the bad set is contained in a finite union of closed sets of empty interior
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
    -- the local pieces of the good clauses
    have hgood : ∀ o : Option (Fin (n + 1) × Bool),
        ∃ (s : Finset ↥(goodBadPt m n p₀ (ρ / 2) (faceK n K o) (Gen.mapFam Φ o)))
          (A : ↥(goodBadPt m n p₀ (ρ / 2) (faceK n K o) (Gen.mapFam Φ o)) →
            Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        (∀ p ∈ Metric.closedBall p₀ (ρ / 2),
          p ∈ badSetK m n (faceK n K o) (Gen.mapFam Φ o) → ∃ x ∈ s, p ∈ A x) := by
      intro o
      have hloc : ∀ x : ↥(goodBadPt m n p₀ (ρ / 2) (faceK n K o) (Gen.mapFam Φ o)),
          ∃ (U : Set (EuclideanSpace ℝ (Fin m) × Amb n))
            (A : Set (EuclideanSpace ℝ (Fin m))),
            IsOpen U ∧ (x.1 : EuclideanSpace ℝ (Fin m) × Amb n) ∈ U ∧
              IsCompact A ∧ interior A = ∅ ∧
            ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Amb n), (p, z) ∈ U →
              Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Gen.mapFam Φ o (p', z)) p) →
              Gen.mapFam Φ o (p, z) = 0 →
              ¬ Function.Surjective
                (fderiv ℝ (fun z' : Amb n => Gen.mapFam Φ o (p, z')) z) → p ∈ A := by
        intro x
        obtain ⟨hx1, hx2, hx3, hx4⟩ := x.2
        obtain ⟨U, hU1, hU2, A, hA1, hA2, hA3⟩ :=
          Gen.exists_local_good_gen m n (Gen.mapFam Φ o) (hfam_smooth o) x.1.1 x.1.2 hx3
            (hfam_surj o x.1.1 x.1.2 (hnorm x.1.1 hx1) hx2 hx3
              (hS_of_bad o x.1.1 x.1.2 (hnorm x.1.1 hx1) hx2 hx3 hx4))
        exact ⟨U, A, hU1, hU2, hA1, hA2, hA3⟩
      choose U A hUopen hxU hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ :=
        (goodBadPt_isCompact m n p₀ (ρ / 2) (faceK n K o) (hfam_compact o) (Gen.mapFam Φ o)
          (hfam_smooth o)).elim_finite_subcover (fun x => U x) (fun x => hUopen x)
          (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
      exact ⟨s, A, (fun x _ => ⟨hAcomp x, hAint x⟩), (fun p hp hbad => by
        obtain ⟨z, hz, hz0, hzsurj⟩ := hbad
        have hxZ : (p, z) ∈ goodBadPt m n p₀ (ρ / 2) (faceK n K o) (Gen.mapFam Φ o) :=
          ⟨hp, hz, hz0, hzsurj⟩
        obtain ⟨x, hxs, hxU'⟩ := Set.mem_iUnion₂.mp (hs hxZ)
        exact ⟨x, hxs, hAprop x p z hxU'
          (hfam_surj o p z (hnorm p hp) hz hz0 (hS_of_bad o p z (hnorm p hp) hz hz0 hzsurj))
          hz0 hzsurj⟩)⟩
    -- the local pieces of the avoidance clauses
    have havoid' : ∀ i : ι,
        ∃ (s : Finset ↥(avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ))
          (A : ↥(avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ) →
            Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        (∀ p ∈ Metric.closedBall p₀ (ρ / 2), ∀ y ∈ K₀ i, B i y ∈ S →
          Φ (p, B i y) = 0 → ∃ x ∈ s, p ∈ A x) := by
      intro i
      have hloc : ∀ x : ↥(avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ),
          ∃ (W : Set (EuclideanSpace ℝ (Fin m) × X i))
            (A : Set (EuclideanSpace ℝ (Fin m))),
            IsOpen W ∧ (x.1 : EuclideanSpace ℝ (Fin m) × X i) ∈ W ∧
              IsCompact A ∧ interior A = ∅ ∧
            ∀ (p : EuclideanSpace ℝ (Fin m)) (y : X i),
              (p, y) ∈ W → Φ (p, B i y) = 0 → p ∈ A := by
        intro x
        obtain ⟨hx1, hx2, hx3⟩ := x.2
        have hxS : B i x.1.2 ∈ S := by
          by_contra hxS
          exact havoid x.1.1 i x.1.2 (hnorm x.1.1 hx1) hx2 hxS hx3
        obtain ⟨W, hW1, hW2, A, hA1, hA2, hA3⟩ :=
          AvoidLowDim.exists_local_avoid_gen m n (hX i) Φ hΦ (B i) (hB i) x.1.1 x.1.2 hx3
            (hsurj x.1.1 (B i x.1.2) (hnorm x.1.1 hx1) (Or.inr ⟨i, x.1.2, hx2, rfl⟩) hx3 hxS)
        exact ⟨W, A, hW1, hW2, hA1, hA2, hA3⟩
      choose W A hWopen hxW hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ :=
        (avoidBadPt_isCompact m n p₀ (ρ / 2) (B i) (K₀ i) (hK₀ i) Φ hΦ (hB i)).elim_finite_subcover
          (fun x => W x) (fun x => hWopen x)
          (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
      exact ⟨s, A, (fun x _ => ⟨hAcomp x, hAint x⟩), (fun p hp y hy hyS hzero => by
        have hxZ : (p, y) ∈ avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ := ⟨hp, hy, hzero⟩
        obtain ⟨x, hxs, hxW'⟩ := Set.mem_iUnion₂.mp (hs hxZ)
        exact ⟨x, hxs, hAprop x p y hxW' hzero⟩)⟩
    -- the Baire step over the finite union of all pieces
    choose sG AG hAG using hgood
    choose sV AV hAV using havoid'
    let F : (Σ o : Option (Fin (n + 1) × Bool), ↥(sG o)) ⊕ (Σ i : ι, ↥(sV i)) →
        Set (EuclideanSpace ℝ (Fin m)) :=
      fun q => q.elim (fun qo => AG qo.1 qo.2) (fun qi => AV qi.1 qi.2)
    have hFclosed : ∀ q, IsClosed (F q) := by
      rintro (⟨o, x⟩ | ⟨i, x⟩)
      · exact ((hAG o).1 x x.2).1.isClosed
      · exact ((hAV i).1 x x.2).1.isClosed
    have hFempty : ∀ q, interior (F q) = ∅ := by
      rintro (⟨o, x⟩ | ⟨i, x⟩)
      · exact ((hAG o).1 x x.2).2
      · exact ((hAV i).1 x x.2).2
    have hbaire : interior (⋃ q, F q) = ∅ :=
      Work.Sard.wp.interior_eq_empty_iUnion_isClosed hFclosed hFempty
    have hcover : Metric.closedBall p₀ (ρ / 2) ⊆ ⋃ q, F q := by
      intro p hp
      have hpBad : p ∈ Bad := (hsub hp).1
      rw [hBad] at hpBad
      rcases hpBad with hpG | hpV
      · rw [hBadGood] at hpG
        obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hpG
        obtain ⟨x, hxs, hpx⟩ := (hAG o).2 p hp ho
        exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨o, ⟨x, hxs⟩⟩, hpx⟩
      · rw [hBadAvoid] at hpV
        obtain ⟨i, y, hy, hyS, hzero⟩ := hpV
        obtain ⟨x, hxs, hpx⟩ := (hAV i).2 p hp y hy hyS hzero
        exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨i, ⟨x, hxs⟩⟩, hpx⟩
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
  have hple : ‖p‖ < ε := by linarith
  have hpAvoid : ∀ i, ∀ y ∈ K₀ i, Φ (p, B i y) ≠ 0 := by
    intro i y hy h0
    by_cases hyS : B i y ∈ S
    · have hmem : p ∈ BadAvoid := by
        rw [hBadAvoid]
        exact ⟨i, y, hy, hyS, h0⟩
      exact hnotBad (by rw [hBad]; exact Or.inr hmem)
    · exact havoid p i y hple hy hyS h0
  refine ⟨p, hple, ?_, ?_, hpAvoid⟩
  · intro z hz h0
    by_cases hzS : z ∈ S
    · by_contra hbadz
      refine hpGood ?_
      rw [hBadGood]
      exact Set.mem_iUnion.mpr ⟨none, by rw [faceK_none, Gen.mapFam_none]; exact ⟨z, hz, h0, hbadz⟩⟩
    · exact (hregOff p z hple (Or.inl hz) h0 hzS).1
  · intro j z hzK h0 hzj
    by_cases hzS : z ∈ S
    · set b : Bool := Gen.boolOf (z j) with hb
      have hcb : Gen.cval b = z j := Gen.cval_boolOf hzj
      have hzface : z ∈ faceK n K (some (j, b)) := by
        rw [faceK_some]
        exact ⟨hzK, hcb.symm⟩
      have h0face : Gen.mapFam Φ (some (j, b)) (p, z) = 0 := by
        rw [Gen.mapFam_some]
        show Φ (p, Gen.faceMap j (Gen.cval b) z) = 0
        rw [hcb, Gen.faceMap_self]
        exact h0
      have hsurjz : Function.Surjective
          (fderiv ℝ (fun z' : Amb n => Gen.mapFam Φ (some (j, b)) (p, z')) z) := by
        by_contra hbadz
        refine hpGood ?_
        rw [hBadGood]
        exact Set.mem_iUnion.mpr ⟨some (j, b), ⟨z, hzface, h0face, hbadz⟩⟩
      have h1 : fderiv ℝ (fun z' : Amb n => Gen.PhiIc Φ j (Gen.cval b) (p, z')) z
          = (fderiv ℝ (fun w : Amb n => Φ (p, w)) z).comp (Gen.faceLin j) := by
        have hfaceb : Gen.faceMap j (Gen.cval b) z = z := by rw [hcb, Gen.faceMap_self]
        have h := Gen.fderiv_PhiIc Φ hΦ j (Gen.cval b) p z
        rw [hfaceb] at h
        exact h
      have hD : Function.Surjective
          ((fderiv ℝ (fun w : Amb n => Φ (p, w)) z).comp (Gen.faceLin j)) := by
        rw [← h1]
        exact hsurjz
      exact (Gen.surjective_comp_faceLin_iff _ j).mp hD
    · exact (hregOff p z hple (Or.inl hzK) h0 hzS).2 j hzj

end

end Work.Drive.ppParity
