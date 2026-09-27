import Mathlib
import Submission.Work.Drive.generic_regularization_gen
import Submission.Work.Drive.exists_forall_good_on_compact

set_option maxHeartbeats 1000000

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

/-- The set of parameters `p` at which `Ψ (p, ·)` has a zero lying in the set `K` at which the
`z`-derivative fails to be surjective.  This is `Gen.badSetGen` with the unit box replaced by an
arbitrary prescribed set `K`. -/
def badSetK (m n : ℕ) (K : Set (Amb n)) (Ψ : Gen.Pm m × Amb n → Tgt n) : Set (Gen.Pm m) :=
  {p | ∃ z ∈ K, Ψ (p, z) = 0 ∧
    ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (p, z')) z)}

/-- **The bad set of a compact family is meagre.**  For a smooth `Ψ` whose parameter-derivative is
surjective at every zero lying in the compact set `K`, the set of parameters `p` at which `Ψ (p, ·)`
has a zero in `K` with non-surjective `z`-derivative has empty interior. -/
lemma interior_badSetK_eq_empty (m n : ℕ) (K : Set (Amb n)) (hK : IsCompact K)
    (Ψ : Gen.Pm m × Amb n → Tgt n) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsurj : ∀ (p : Gen.Pm m) (z : Amb n), z ∈ K → Ψ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Ψ (p', z)) p)) :
    interior (badSetK m n K Ψ) = ∅ := by
  classical
  by_contra hne
  obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε', hε'pos, hε'sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp₀)
  have hBsub : Metric.closedBall p₀ (ε' / 2) ⊆ badSetK m n K Ψ := by
    intro p hp
    refine interior_subset (hε'sub ?_)
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hp
    linarith [hε'pos]
  have hBint : (interior (Metric.closedBall p₀ (ε' / 2))).Nonempty :=
    ⟨p₀, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith [hε'pos]))⟩
  -- the compact set of bad points over the closed ball
  set Kp : Set (Gen.Pm m × Amb n) :=
    {x | x.1 ∈ Metric.closedBall p₀ (ε' / 2) ∧ x.2 ∈ K ∧ Ψ x = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (x.1, z')) x.2)} with hKp
  have hcont : Continuous (fun x : Gen.Pm m × Amb n =>
      (fderiv ℝ Ψ x).comp
        (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n))) := by
    have h1 : Continuous (fun T : (Gen.Pm m × Amb n) →L[ℝ] Tgt n =>
        T.comp (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n))) := by
      have h := (ContinuousLinearMap.compL ℝ (Amb n) (Gen.Pm m × Amb n) (Tgt n)).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (Gen.Pm m × Amb n) →L[ℝ] Tgt n =>
            ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n)))
      simpa using h
    exact h1.comp (hΨ.continuous_fderiv (by simp))
  have hKp_eq : Kp = ((Metric.closedBall p₀ (ε' / 2) ×ˢ K) ∩
      {x : Gen.Pm m × Amb n | Ψ x = 0}) ∩
      {x : Gen.Pm m × Amb n | ¬ Function.Surjective
        ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n)))} := by
    rw [hKp]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
    rw [← Work.MetricSquare.fd_comp_inr Ψ hΨ x.1 x.2]
    tauto
  have hKp_compact : IsCompact Kp := by
    rw [hKp_eq]
    have hc1 : IsClosed ((Metric.closedBall p₀ (ε' / 2) ×ˢ K) ∩
        {x : Gen.Pm m × Amb n | Ψ x = 0}) :=
      ((isCompact_closedBall p₀ (ε' / 2)).isClosed.prod hK.isClosed).inter
        (isClosed_eq hΨ.continuous continuous_const)
    have hc2 : IsClosed {x : Gen.Pm m × Amb n |
        ¬ Function.Surjective ((fderiv ℝ Ψ x).comp
          (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n)))} :=
      Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
    exact IsCompact.of_isClosed_subset
      ((isCompact_closedBall p₀ (ε' / 2)).prod hK)
      (hc1.inter hc2) (fun x hx => hx.1.1)
  -- the local neighbourhoods of the bad zeros
  have hchoice : ∀ x : Kp,
      ∃ U : Set (Gen.Pm m × Amb n),
        IsOpen U ∧ (x.1 : Gen.Pm m × Amb n) ∈ U ∧
        ∃ A : Set (Gen.Pm m), IsCompact A ∧ interior A = ∅ ∧
          (∀ (p : Gen.Pm m) (z : Amb n), (p, z) ∈ U →
            Function.Surjective
              (fderiv ℝ (fun p' : Gen.Pm m => Ψ (p', z)) p) →
            Ψ (p, z) = 0 →
            ¬ Function.Surjective
              (fderiv ℝ (fun z' : Amb n => Ψ (p, z')) z) → p ∈ A) :=
    fun x => Gen.exists_local_good_gen m n Ψ hΨ x.1.1 x.1.2 x.2.2.2.1
      (hsurj x.1.1 x.1.2 x.2.2.1 x.2.2.2.1)
  choose U hU using hchoice
  obtain ⟨s, hs⟩ := hKp_compact.elim_finite_subcover U (fun x => (hU x).1)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩)
  have hBsub2 : Metric.closedBall p₀ (ε' / 2) ⊆ ⋃ y : s, (hU (y : Kp)).2.2.choose := by
    intro p hp
    have hpBad : p ∈ badSetK m n K Ψ := hBsub hp
    obtain ⟨z, hzK, hΨz, hbadz⟩ := hpBad
    have hxK : (p, z) ∈ Kp := ⟨hp, hzK, hΨz, hbadz⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxK)
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hU (y : Kp)).2.2.choose_spec.2.2 p z hxy
      (hsurj p z hzK hΨz) hΨz hbadz⟩
  have hclosedA : ∀ y : s, IsClosed ((hU (y : Kp)).2.2.choose) :=
    fun y => (hU (y : Kp)).2.2.choose_spec.1.isClosed
  have hemptyA : ∀ y : s, interior ((hU (y : Kp)).2.2.choose) = ∅ :=
    fun y => (hU (y : Kp)).2.2.choose_spec.2.1
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hclosedA hemptyA
  have hsubInt : interior (Metric.closedBall p₀ (ε' / 2)) ⊆
      interior (⋃ y : s, (hU (y : Kp)).2.2.choose) := interior_mono hBsub2
  rw [hBaire] at hsubInt
  exact hBint.ne_empty (Set.Subset.antisymm hsubInt (Set.empty_subset _))

/-- The bad set of a compact family, cut down to a ball, is compact: it is the image under the first
projection of a closed subset of a product of compact sets. -/
lemma isCompact_badSetK_inter_closedBall (m n : ℕ) (K : Set (Amb n)) (hK : IsCompact K)
    (Ψ : Gen.Pm m × Amb n → Tgt n) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (k : ℕ) :
    IsCompact (badSetK m n K Ψ ∩ Metric.closedBall (0 : Gen.Pm m) k) := by
  have hcont : Continuous (fun x : Gen.Pm m × Amb n =>
      (fderiv ℝ Ψ x).comp
        (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n))) := by
    have h1 : Continuous (fun T : (Gen.Pm m × Amb n) →L[ℝ] Tgt n =>
        T.comp (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n))) := by
      have h := (ContinuousLinearMap.compL ℝ (Amb n) (Gen.Pm m × Amb n) (Tgt n)).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (Gen.Pm m × Amb n) →L[ℝ] Tgt n =>
            ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n)))
      simpa using h
    exact h1.comp (hΨ.continuous_fderiv (by simp))
  set Kx : Set (Gen.Pm m × Amb n) :=
    ((Metric.closedBall (0 : Gen.Pm m) k ×ˢ K) ∩ {x : Gen.Pm m × Amb n | Ψ x = 0})
      ∩ {x : Gen.Pm m × Amb n | ¬ Function.Surjective
          ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n)))} with hKx
  have hKcompact : IsCompact Kx := by
    rw [hKx]
    have hc1 : IsClosed ((Metric.closedBall (0 : Gen.Pm m) k ×ˢ K)
        ∩ {x : Gen.Pm m × Amb n | Ψ x = 0}) :=
      ((isCompact_closedBall (0 : Gen.Pm m) k).isClosed.prod hK.isClosed).inter
        (isClosed_eq hΨ.continuous continuous_const)
    have hc2 : IsClosed {x : Gen.Pm m × Amb n | ¬ Function.Surjective
        ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Gen.Pm m) (Amb n)))} :=
      Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
    exact IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : Gen.Pm m) k).prod hK)
      (hc1.inter hc2) (fun x hx => hx.1.1)
  have himg : Prod.fst '' Kx = badSetK m n K Ψ ∩ Metric.closedBall (0 : Gen.Pm m) k := by
    rw [hKx]
    ext p
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, badSetK]
    constructor
    · rintro ⟨x, ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩, rfl⟩
      exact ⟨⟨x.2, hx2, hx3, fun hc =>
        hx4 (by rwa [← Work.MetricSquare.fd_comp_inr Ψ hΨ x.1 x.2] at hc)⟩, hx1⟩
    · rintro ⟨⟨z, hz, hz0, hzbad⟩, hp⟩
      exact ⟨(p, z), ⟨⟨⟨hp, hz⟩, hz0⟩,
        by rwa [Work.MetricSquare.fd_comp_inr Ψ hΨ p z]⟩, rfl⟩
  rw [← himg]
  exact hKcompact.image continuous_fst

/-- **Finitely many compact bad sets are jointly meagre.**  For a finite family `Ψ i` of smooth maps
whose parameter-derivative is surjective at every zero lying in the compact set `K i`, the union of
the bad parameter sets has empty interior. -/
lemma interior_iUnion_badSetK_eq_empty {m n : ℕ} {ι : Type*} [Fintype ι]
    (K : ι → Set (Amb n)) (hK : ∀ i, IsCompact (K i))
    (Ψ : ι → Gen.Pm m × Amb n → Tgt n)
    (hΨ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ i))
    (hsurj : ∀ (i : ι) (p : Gen.Pm m) (z : Amb n), z ∈ K i → Ψ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Ψ i (p', z)) p)) :
    interior (⋃ i : ι, badSetK m n (K i) (Ψ i)) = ∅ := by
  have hFclosed : ∀ k : ι × ℕ,
      IsClosed (badSetK m n (K k.1) (Ψ k.1) ∩ Metric.closedBall (0 : Gen.Pm m) k.2) :=
    fun k => (isCompact_badSetK_inter_closedBall m n (K k.1) (hK k.1) (Ψ k.1)
      (hΨ k.1) k.2).isClosed
  have hFempty : ∀ k : ι × ℕ,
      interior (badSetK m n (K k.1) (Ψ k.1) ∩ Metric.closedBall (0 : Gen.Pm m) k.2) = ∅ :=
    fun k => subset_eq_empty (interior_mono Set.inter_subset_left)
      (interior_badSetK_eq_empty m n (K k.1) (hK k.1) (Ψ k.1) (hΨ k.1) (hsurj k.1))
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hFclosed hFempty
  have hunion : (⋃ k : ι × ℕ,
        badSetK m n (K k.1) (Ψ k.1) ∩ Metric.closedBall (0 : Gen.Pm m) k.2)
      = ⋃ i : ι, badSetK m n (K i) (Ψ i) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, badSetK]
    constructor
    · rintro ⟨k, ⟨z, hz, hz0, hz1⟩, -⟩
      exact ⟨k.1, z, hz, hz0, hz1⟩
    · rintro ⟨i, z, hz, hz0, hz1⟩
      obtain ⟨N, hN⟩ := exists_nat_ge ‖p‖
      exact ⟨(i, N), ⟨z, hz, hz0, hz1⟩,
        Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hN)⟩
  rw [← hunion]
  exact hBaire

/-- The domains of the auxiliary family attached to a compact set `K` and its faces: `K` itself and,
for each coordinate `j` and each `c ∈ {0,1}`, the slice `K ∩ {z | z j = c}`. -/
def faceK (n : ℕ) (K : Set (Amb n)) : Option (Fin (n + 1) × Bool) → Set (Amb n) :=
  fun o => o.elim K (fun jb => K ∩ {z : Amb n | z jb.1 = Gen.cval jb.2})

lemma faceK_none {n : ℕ} (K : Set (Amb n)) : faceK n K none = K := rfl

lemma faceK_some {n : ℕ} (K : Set (Amb n)) (j : Fin (n + 1)) (b : Bool) :
    faceK n K (some (j, b)) = K ∩ {z : Amb n | z j = Gen.cval b} := rfl

/-- **Parametric Sard on a compact parameter set, with the boundary-face refinement.**  The local form of the workspace's parametric-Sard result, including its second clause: for a smooth family, if at every zero lying in a compact set `K` the parameter-derivative is surjective, then for parameters of arbitrarily small norm the `z`-derivative is surjective at every zero lying in `K`, *and* at every such zero that lies on a box face `z j ∈ {0,1}` its restriction to the coordinate hyperplane `{v | v j = 0}` is surjective.

Compared with the box form (`Work.Drive.generic_regularization_gen`), the two relaxations are: the compact set `K` replaces `Submission.Drive.unitBox n`, and the parameter-surjectivity hypothesis is required only at the zeros in `K`.  This is what a *local* application needs: when the family is only smooth on a chart region (where the zeros are the geometric ones), the zeros outside that region are artefacts of the junk extension of the chart and must not enter the hypotheses.  Taking `K` to be the unit box recovers the box form a fortiori.

Proof sketch.  Clause 1 is the sibling `Work.Drive.exists_forall_good_on_compact`.  For the face clause, do **not** apply the box argument to all of `K` through the auxiliary face maps `Gen.PhiIc` — on `K ∖ {z j = c}` the map `faceMap j c` moves points and the box's own `Gen.PhiIc_hsurj` (which needs `hsurj` on the whole unit box) is unavailable.  Instead, for each `j` and `c ∈ {0,1}` restrict to the compact set `K ∩ {z j = c}`, on which `faceMap j c = id`, so that `Gen.PhiIc Φ j c` agrees there with `Φ` in both value and parameter-derivative (hence the `K`-hypothesis of `hsurj` supplies what `Gen.exists_local_good_gen` consumes at a bad point), and kill each of the finitely many bad sets with `Gen.exists_local_good_gen` + `Work.Sard.wp.interior_eq_empty_iUnion_isClosed`.  Finally `exists_norm_lt_notMem_of_interior_eq_empty` turns `interior Bad = ∅` into a parameter of norm `< ε` that is good for all clauses simultaneously. -/
theorem exists_forall_good_on_compact_face (m n : ℕ) (K : Set (Work.Drive.Amb n)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε)
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), z ∈ K → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ z ∈ K, Φ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z)) ∧
      (∀ (j : Fin (n + 1)) (z : Work.Drive.Amb n), z ∈ K → Φ (p, z) = 0 →
        (z j = 0 ∨ z j = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb n // v j = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb n => Φ (p, z')) z v.1)) := by
  classical
  -- the finite family of maps: `Φ` and its face maps, restricted to `K` and its faces
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
      z ∈ faceK n K o → Gen.mapFam Φ o (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Gen.Pm m => Gen.mapFam Φ o (p', z)) p) := by
    intro o
    cases o with
    | none =>
      intro p z hz h0
      exact hsurj p z hz h0
    | some jb =>
      obtain ⟨j, b⟩ := jb
      intro p z hz h0
      rw [faceK_some] at hz
      have hzK : z ∈ K := hz.1
      have hzj : z j = Gen.cval b := hz.2
      have h0' : Φ (p, z) = 0 := by
        have h := h0
        simp only [Gen.mapFam_some, Gen.PhiIc] at h
        rwa [← hzj, Gen.faceMap_self] at h
      have h := hsurj p z hzK h0'
      simpa only [Gen.mapFam_some, Gen.PhiIc, ← hzj, Gen.faceMap_self] using h
  have hbad := interior_iUnion_badSetK_eq_empty (m := m) (n := n)
    (K := faceK n K) hfam_compact (Gen.mapFam Φ) hfam_smooth hfam_surj
  obtain ⟨p, hpball, hp⟩ :=
    Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty _ hbad hε
  refine ⟨p, hpball, ?_, ?_⟩
  · intro z hz h0
    by_contra hbadz
    refine hp (Set.mem_iUnion.mpr ⟨none, ?_⟩)
    rw [faceK_none, Gen.mapFam_none]
    exact ⟨z, hz, h0, hbadz⟩
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
      exact hp (Set.mem_iUnion.mpr ⟨some (j, b), ⟨z, hzface, h0face, hbadz⟩⟩)
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
