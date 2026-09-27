import Mathlib
import Submission.Work.Drive.avoidLowDim
import Submission.Work.Drive.exists_forall_good_on_compact_face

/-!
# One parameter for the Sard clauses and the avoidance clause

`Work.Drive.exists_forall_good_on_compact_face` proves, for a smooth family
`Φ : ℝ^m × ℝ^{n+1} → ℝ^n` with an everywhere parameter-derivative onto over a compact set `K`, that
some small parameter `p` makes the `z`-derivative of `Φ (p, ·)` surjective at every zero in `K`,
*and* makes its restriction to every coordinate hyperplane `{v | v j = 0}` surjective at every zero
of `K` lying on the face `z j ∈ {0,1}`.

`Work.Drive.AvoidLowDim.exists_forall_notMem_family` proves, for a finite family of smooth
parametrisations `B i : X i → ℝ^{n+1}` of pieces of dimension `< n`, that some small parameter `p`
makes `Φ (p, B i y) ≠ 0` for every `y ∈ K₀ i`.

Here the two conclusions are merged at a **single** parameter.  The bad control on the parameter is
weaker than in the two parents: the parameter-surjectivity hypothesis is available only for
`‖p‖ < ε`.  Both conclusions are nevertheless instances of the same Baire argument: the set of
"bad" parameters inside the ball `‖p‖ < ε` is contained in a finite union of closed sets with empty
interior.  The proof below runs one Baire step over the finite union of the two families of closed
sets — the local pieces of `Gen.exists_local_good_gen` attached to the bad zeros of the good clauses
and the local pieces of `AvoidLowDim.exists_local_avoid_gen` attached to the zeros over the
parametrised pieces — and then extracts `p` from the complement of the bad set inside the ball of
radius `ε/2`.

The truncation at the ball of radius `ε/2 < ε` is what lets the norm-restricted hypothesis `hsurj`
be used at every base point entering the local analysis. -/

set_option maxHeartbeats 1000000

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

/-- The base bad set of a good clause, relative to the closed ball of radius `r` about `p₀`: the
pairs `(p, z)` with `p` in that ball, `z ∈ K`, `Ψ (p, z) = 0` and the `z`-derivative of `Ψ (p, ·)`
at `z` not surjective. -/
def goodBadPt (m n : ℕ) (p₀ : EuclideanSpace ℝ (Fin m)) (r : ℝ) (K : Set (Amb n))
    (Ψ : EuclideanSpace ℝ (Fin m) × Amb n → Tgt n) :
    Set (EuclideanSpace ℝ (Fin m) × Amb n) :=
  {x | x.1 ∈ Metric.closedBall p₀ r ∧ x.2 ∈ K ∧ Ψ x = 0 ∧
    ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (x.1, z')) x.2)}

/-- The base bad set of the avoidance argument, relative to the closed ball of radius `r` about
`p₀`: the pairs `(p, y)` with `p` in that ball, `y ∈ K₀` and `Φ (p, B y) = 0`. -/
def avoidBadPt (m n : ℕ) (p₀ : EuclideanSpace ℝ (Fin m)) (r : ℝ) (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X → Amb n) (K₀ : Set X) (Φ : EuclideanSpace ℝ (Fin m) × Amb n → Tgt n) :
    Set (EuclideanSpace ℝ (Fin m) × X) :=
  {x | x.1 ∈ Metric.closedBall p₀ r ∧ x.2 ∈ K₀ ∧ Φ (x.1, B x.2) = 0}

lemma goodBadPt_isCompact (m n : ℕ) (p₀ : EuclideanSpace ℝ (Fin m)) (r : ℝ)
    (K : Set (Amb n)) (hK : IsCompact K) (Ψ : EuclideanSpace ℝ (Fin m) × Amb n → Tgt n)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) :
    IsCompact (goodBadPt m n p₀ r K Ψ) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin m) × Amb n =>
      (fderiv ℝ Ψ x).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Amb n))) := by
    have h1 : Continuous (fun T : (EuclideanSpace ℝ (Fin m) × Amb n) →L[ℝ] Tgt n =>
        T.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Amb n))) := by
      have h := (ContinuousLinearMap.compL ℝ (Amb n) (EuclideanSpace ℝ (Fin m) × Amb n)
        (Tgt n)).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (EuclideanSpace ℝ (Fin m) × Amb n) →L[ℝ] Tgt n =>
            ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Amb n)))
      simpa using h
    exact h1.comp (hΨ.continuous_fderiv (by simp))
  have hset : goodBadPt m n p₀ r K Ψ =
      ((Metric.closedBall p₀ r ×ˢ K) ∩
          {x : EuclideanSpace ℝ (Fin m) × Amb n | Ψ x = 0}) ∩
        {x : EuclideanSpace ℝ (Fin m) × Amb n | ¬ Function.Surjective
          ((fderiv ℝ Ψ x).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Amb n)))} := by
    ext x
    simp only [goodBadPt, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
    rw [← Work.MetricSquare.fd_comp_inr Ψ hΨ x.1 x.2]
    tauto
  rw [hset]
  exact IsCompact.of_isClosed_subset ((isCompact_closedBall p₀ r).prod hK)
    (((isCompact_closedBall p₀ r).isClosed.prod hK.isClosed).inter
      (isClosed_eq hΨ.continuous continuous_const) |>.inter
      (Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont))
    (fun x hx => hx.1.1)

lemma avoidBadPt_isCompact (m n : ℕ) (p₀ : EuclideanSpace ℝ (Fin m)) (r : ℝ) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (B : X → Amb n) (K₀ : Set X)
    (hK₀ : IsCompact K₀) (Φ : EuclideanSpace ℝ (Fin m) × Amb n → Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    IsCompact (avoidBadPt m n p₀ r X B K₀ Φ) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin m) × X => Φ (x.1, B x.2)) :=
    hΦ.continuous.comp (continuous_fst.prodMk (hB.continuous.comp continuous_snd))
  have hset : avoidBadPt m n p₀ r X B K₀ Φ =
      (Metric.closedBall p₀ r ×ˢ K₀) ∩
        {x : EuclideanSpace ℝ (Fin m) × X | Φ (x.1, B x.2) = 0} := by
    ext x
    simp only [avoidBadPt, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
    tauto
  rw [hset]
  exact IsCompact.of_isClosed_subset
    ((isCompact_closedBall p₀ r).prod hK₀)
    (((isCompact_closedBall p₀ r).isClosed.prod hK₀.isClosed).inter
      (isClosed_eq hcont continuous_const))
    Set.inter_subset_left

theorem exists_forall_good_face_and_notMem_family (m n : ℕ) (K : Set (Work.Drive.Amb n)) (hK : IsCompact K)
    (ι : Type*) [Fintype ι]
    (X : ι → Type*) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)] (hX : ∀ i, Module.finrank ℝ (X i) < n)
    (B : ∀ i, X i → Work.Drive.Amb n) (hB : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i))
    (K₀ : ∀ i, Set (X i)) (hK₀ : ∀ i, IsCompact (K₀ i))
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), ‖p‖ < ε →
      (z ∈ K ∨ ∃ i, z ∈ B i '' K₀ i) → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
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
  -- ## the auxiliary family of the good clauses (as in `exists_forall_good_on_compact_face`)
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
  have hfam_surj : ∀ (o : Option (Fin (n + 1) × Bool)) (p : Gen.Pm m) (z : Amb n),
      ‖p‖ < ε → z ∈ faceK n K o → Gen.mapFam Φ o (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Gen.mapFam Φ o (p', z)) p) := by
    intro o
    cases o with
    | none =>
      intro p z hp hz h0
      exact hsurj p z hp (Or.inl hz) h0
    | some jb =>
      obtain ⟨j, b⟩ := jb
      intro p z hp hz h0
      rw [faceK_some] at hz
      have hzK : z ∈ K := hz.1
      have hzj : z j = Gen.cval b := hz.2
      have h0' : Φ (p, z) = 0 := by
        have h := h0
        simp only [Gen.mapFam_some, Gen.PhiIc] at h
        rwa [← hzj, Gen.faceMap_self] at h
      have h := hsurj p z hp (Or.inl hzK) h0'
      simpa only [Gen.mapFam_some, Gen.PhiIc, ← hzj, Gen.faceMap_self] using h
  -- ## the bad set
  set BadGood : Set (EuclideanSpace ℝ (Fin m)) :=
    ⋃ o : Option (Fin (n + 1) × Bool), badSetK m n (faceK n K o) (Gen.mapFam Φ o) with hBadGood
  set BadAvoid : Set (EuclideanSpace ℝ (Fin m)) :=
    {p : EuclideanSpace ℝ (Fin m) | ∃ i, ∃ y ∈ K₀ i, Φ (p, B i y) = 0} with hBadAvoid
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
            (hfam_surj o x.1.1 x.1.2 (hnorm x.1.1 hx1) hx2 hx3)
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
        exact ⟨x, hxs, hAprop x p z hxU' (hfam_surj o p z (hnorm p hp) hz hz0) hz0 hzsurj⟩)⟩
    -- the local pieces of the avoidance clauses
    have havoid : ∀ i : ι,
        ∃ (s : Finset ↥(avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ))
          (A : ↥(avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ) →
            Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        (∀ p ∈ Metric.closedBall p₀ (ρ / 2), ∀ y ∈ K₀ i,
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
        obtain ⟨W, hW1, hW2, A, hA1, hA2, hA3⟩ :=
          AvoidLowDim.exists_local_avoid_gen m n (hX i) Φ hΦ (B i) (hB i) x.1.1 x.1.2 hx3
            (hsurj x.1.1 (B i x.1.2) (hnorm x.1.1 hx1) (Or.inr ⟨i, x.1.2, hx2, rfl⟩) hx3)
        exact ⟨W, A, hW1, hW2, hA1, hA2, hA3⟩
      choose W A hWopen hxW hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ :=
        (avoidBadPt_isCompact m n p₀ (ρ / 2) (B i) (K₀ i) (hK₀ i) Φ hΦ (hB i)).elim_finite_subcover
          (fun x => W x) (fun x => hWopen x)
          (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
      exact ⟨s, A, (fun x _ => ⟨hAcomp x, hAint x⟩), (fun p hp y hy hzero => by
        have hxZ : (p, y) ∈ avoidBadPt m n p₀ (ρ / 2) (X i) (B i) (K₀ i) Φ := ⟨hp, hy, hzero⟩
        obtain ⟨x, hxs, hxW'⟩ := Set.mem_iUnion₂.mp (hs hxZ)
        exact ⟨x, hxs, hAprop x p y hxW' hzero⟩)⟩
    -- the Baire step over the finite union of all pieces
    choose sG AG hAG using hgood
    choose sV AV hAV using havoid
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
        obtain ⟨i, y, hy, hzero⟩ := hpV
        obtain ⟨x, hxs, hpx⟩ := (hAV i).2 p hp y hy hzero
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
  have hpAvoid : ∀ i, ∀ y ∈ K₀ i, Φ (p, B i y) ≠ 0 := by
    intro i y hy h0
    exact hnotBad (by rw [hBad]; exact Or.inr (by rw [hBadAvoid]; exact ⟨i, y, hy, h0⟩))
  refine ⟨p, by linarith, ?_, ?_, hpAvoid⟩
  · intro z hz h0
    by_contra hbadz
    refine hpGood ?_
    rw [hBadGood]
    exact Set.mem_iUnion.mpr ⟨none, by rw [faceK_none, Gen.mapFam_none]; exact ⟨z, hz, h0, hbadz⟩⟩
  · intro j z hzK h0 hzj
    set b : Bool := Gen.boolOf (z j) with hb
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

end

end Work.Drive
