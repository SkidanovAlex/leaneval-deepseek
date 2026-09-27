import Mathlib
import Submission.Work.MetricSquare.generic_regularization_of_family
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.boxParity

/-!
# Generic regularization on the faces of the box

`Work.MetricSquare.generic_regularization_of_family` produces a parameter `p` at which the
`z`-derivative of `Φ (p, ·)` is surjective at every zero inside the unit box.  For the mod-2
boundary parity argument (`Submission.Drive.ParityProp`) one additionally needs, at every zero `z`
of `Φ (p, ·)` lying on a *face* `z i = 0` or `z i = 1` of the box, that the restriction of the
`z`-derivative to the coordinate hyperplane `{v // v i = 0}` is surjective.

This file supplies that generic statement.  The proof is a Baire argument on the *finite* family
of auxiliary maps

`Φ_{i,c}(p, z) = Φ (p, z with the i-th coordinate replaced by c)`,   `c ∈ {0,1}`,

whose `z`-derivative at `(p,z)` is the `z`-derivative of `Φ` at `(p,z)` composed with the
projection `ℝ⁷ → {v // v i = 0}`.  The bad parameter sets of these finitely many maps have empty
interior by `bad_interior_empty`, and each of them is a countable union of compact (hence closed)
sets, so a countable union of closed sets with empty interior — Baire — is meagreness of the total
bad set.
-/

set_option maxHeartbeats 2000000

namespace Work.MetricSquare

open scoped ContDiff Topology
open Set Metric

noncomputable section

/-! ## The bad parameter sets -/

/-- The set of parameters `p` at which `Ψ (p, ·)` has a zero in the unit box at which the
`z`-derivative fails to be surjective. -/
def badSet (m : ℕ) (Ψ : Pm m × Cz → Tw) : Set (Pm m) :=
  {p | ∃ z ∈ Submission.Drive.unitBox 6, Ψ (p, z) = 0 ∧
    ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Ψ (p, z')) z)}

/-- `Work.MetricSquare.bad_interior_empty`, restated for `badSet`. -/
lemma interior_badSet_eq_empty (m : ℕ) (Ψ : Pm m × Cz → Tw)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsurj : ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → Ψ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => Ψ (p', z)) p)) :
    interior (badSet m Ψ) = ∅ := by
  simpa only [badSet] using bad_interior_empty m Ψ hΨ hsurj

/-- **The bad set is a countable union of compact sets.**  The intersection of `badSet Ψ` with a
closed ball is the image under the first projection of a compact set. -/
lemma isCompact_badSet_inter_closedBall (m : ℕ) (Ψ : Pm m × Cz → Tw)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (n : ℕ) :
    IsCompact (badSet m Ψ ∩ Metric.closedBall (0 : Pm m) n) := by
  have hcont : Continuous (fun x : Pm m × Cz =>
      (fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz)) := by
    have h1 : Continuous (fun T : (Pm m × Cz) →L[ℝ] Tw =>
        T.comp (ContinuousLinearMap.inr ℝ (Pm m) Cz)) := by
      have h := (ContinuousLinearMap.compL ℝ Cz (Pm m × Cz) Tw).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (Pm m × Cz) →L[ℝ] Tw => ContinuousLinearMap.inr ℝ (Pm m) Cz))
      simpa using h
    exact h1.comp (hΨ.continuous_fderiv (by simp))
  set K : Set (Pm m × Cz) := ((Metric.closedBall (0 : Pm m) n ×ˢ Submission.Drive.unitBox 6)
      ∩ {x : Pm m × Cz | Ψ x = 0})
      ∩ {x : Pm m × Cz | ¬ Function.Surjective
          ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz))} with hK
  have hKcompact : IsCompact K := by
    rw [hK]
    have hc1 : IsClosed ((Metric.closedBall (0 : Pm m) n ×ˢ Submission.Drive.unitBox 6)
        ∩ {x : Pm m × Cz | Ψ x = 0}) :=
      ((isCompact_closedBall (0 : Pm m) n).isClosed.prod (Work.Drive.isClosed_unitBox 6)).inter
        (isClosed_eq hΨ.continuous continuous_const)
    have hc2 : IsClosed {x : Pm m × Cz | ¬ Function.Surjective
        ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz))} :=
      Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
    exact IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : Pm m) n).prod (Work.Drive.isCompact_unitBox 6))
      (hc1.inter hc2) (fun x hx => hx.1.1)
  have himg : Prod.fst '' K = badSet m Ψ ∩ Metric.closedBall (0 : Pm m) n := by
    rw [hK]
    ext p
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, badSet]
    constructor
    · rintro ⟨x, ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩, rfl⟩
      exact ⟨⟨x.2, hx2, hx3, fun hc => hx4 (by rwa [← fd_comp_inr Ψ hΨ x.1 x.2] at hc)⟩, hx1⟩
    · rintro ⟨⟨z, hz, hz0, hzbad⟩, hp⟩
      exact ⟨(p, z), ⟨⟨⟨hp, hz⟩, hz0⟩, by rwa [fd_comp_inr Ψ hΨ p z]⟩, rfl⟩
  rw [← himg]
  exact hKcompact.image continuous_fst

/-- The bad set is the union over `n` of its intersections with the closed balls. -/
lemma badSet_eq_iUnion_closedBall (m : ℕ) (Ψ : Pm m × Cz → Tw) :
    badSet m Ψ = ⋃ n : ℕ, badSet m Ψ ∩ Metric.closedBall (0 : Pm m) n := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := exists_nat_ge ‖p‖
    exact Set.mem_iUnion.mpr ⟨n, hp, Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hn)⟩
  · intro hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact hn.1

/-! ## The linear projection onto a coordinate hyperplane and the face maps -/

/-- The orthogonal projection of `ℝ⁷` onto the coordinate hyperplane `{v | v i = 0}`. -/
def faceLin (i : Fin 7) : Cz →L[ℝ] Cz :=
  ContinuousLinearMap.id ℝ Cz -
    (PiLp.proj 2 (fun _ : Fin 7 => ℝ) i).smulRight (EuclideanSpace.single i 1)

/-- `z ↦ z` with the `i`-th coordinate replaced by `c`. -/
def faceMap (i : Fin 7) (c : ℝ) : Cz → Cz :=
  fun z => faceLin i z + c • EuclideanSpace.single i 1

lemma faceLin_coord (i : Fin 7) (z : Cz) (j : Fin 7) :
    (faceLin i z) j = if j = i then 0 else z j := by
  simp only [faceLin]
  split_ifs with h <;> simp [h]

lemma faceLin_self (i : Fin 7) (z : Cz) : (faceLin i z) i = 0 := by
  rw [faceLin_coord, if_pos rfl]

lemma faceLin_eq_self_of {i : Fin 7} {z : Cz} (hz : z i = 0) : faceLin i z = z := by
  apply WithLp.ofLp_injective 2
  funext j
  rw [faceLin_coord]
  split_ifs with h
  · rw [h]; exact hz.symm
  · rfl

lemma faceMap_coord (i : Fin 7) (c : ℝ) (z : Cz) (j : Fin 7) :
    (faceMap i c z) j = if j = i then c else z j := by
  simp only [faceMap, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, faceLin_coord]
  split_ifs with h <;> ring

lemma faceMap_self (i : Fin 7) (z : Cz) : faceMap i (z i) z = z := by
  apply WithLp.ofLp_injective 2
  funext j
  rw [faceMap_coord]
  split_ifs with h
  · rw [h]
  · rfl

lemma faceMap_mem_unitBox {i : Fin 7} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {z : Cz}
    (hz : z ∈ Submission.Drive.unitBox 6) : faceMap i c z ∈ Submission.Drive.unitBox 6 := by
  intro j
  rw [faceMap_coord]
  split_ifs with h
  · exact ⟨hc0, hc1⟩
  · exact hz j

lemma hasFDerivAt_faceMap (i : Fin 7) (c : ℝ) (z : Cz) :
    HasFDerivAt (faceMap i c) (faceLin i) z := by
  have h : HasFDerivAt (⇑(faceLin i)) (faceLin i) z := ContinuousLinearMap.hasFDerivAt (faceLin i)
  exact h.add_const (c • EuclideanSpace.single i 1)

/-- Surjectivity of `D ∘ faceLin i` is surjectivity of the restriction of `D` to the coordinate
hyperplane `{v | v i = 0}`. -/
lemma surjective_comp_faceLin_iff (D : Cz →L[ℝ] Tw) (i : Fin 7) :
    Function.Surjective (D.comp (faceLin i)) ↔
      Function.Surjective (fun v : {v : Cz // v i = 0} => D v.1) := by
  constructor
  · intro h w
    obtain ⟨u, hu⟩ := h w
    exact ⟨⟨faceLin i u, faceLin_self i u⟩, hu⟩
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨v.1, by rw [ContinuousLinearMap.comp_apply, faceLin_eq_self_of v.2]; exact hv⟩

/-! ## The auxiliary maps `Φ_{i,c}` -/

/-- `Φ` with the `i`-th coordinate of the `z`-variable replaced by `c`. -/
def PhiIc {m : ℕ} (Φ : Pm m × Cz → Tw) (i : Fin 7) (c : ℝ) : Pm m × Cz → Tw :=
  fun x => Φ (x.1, faceMap i c x.2)

lemma PhiIc_contDiff {m : ℕ} (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (i : Fin 7) (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PhiIc Φ i c) := by
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (faceMap i c) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(faceLin i)) :=
      ContinuousLinearMap.contDiff (faceLin i)
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : Cz => c • EuclideanSpace.single i (1 : ℝ)) := contDiff_const
    exact h.add hc
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Pm m × Cz => (x.1, faceMap i c x.2)) :=
    contDiff_fst.prodMk (h2.comp contDiff_snd)
  exact hΦ.comp hpair

/-- The `z`-derivative of `Φ_{i,c}`. -/
lemma fderiv_PhiIc {m : ℕ} (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (i : Fin 7) (c : ℝ) (p : Pm m) (z : Cz) :
    fderiv ℝ (fun z' : Cz => PhiIc Φ i c (p, z')) z
      = (fderiv ℝ (fun w : Cz => Φ (p, w)) (faceMap i c z)).comp (faceLin i) := by
  have hlin : HasFDerivAt (faceMap i c) (faceLin i) z := hasFDerivAt_faceMap i c z
  have hinner : HasFDerivAt (fun w : Cz => (p, w)) (ContinuousLinearMap.inr ℝ (Pm m) Cz)
      (faceMap i c z) := by
    simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ (Pm m) Cz)).const_add (p, 0)
  have hd : DifferentiableAt ℝ Φ (p, faceMap i c z) :=
    (hΦ.differentiable (by simp)).differentiableAt
  have hcomp1 : HasFDerivAt (fun w : Cz => Φ (p, w))
      ((fderiv ℝ Φ (p, faceMap i c z)).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz))
      (faceMap i c z) :=
    hd.hasFDerivAt.comp (faceMap i c z) hinner
  have hcomp2 : HasFDerivAt (fun z' : Cz => PhiIc Φ i c (p, z'))
      (((fderiv ℝ Φ (p, faceMap i c z)).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz)).comp
        (faceLin i)) z :=
    hcomp1.comp z hlin
  have hgoal : fderiv ℝ (fun z' : Cz => PhiIc Φ i c (p, z')) z
      = ((fderiv ℝ Φ (p, faceMap i c z)).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz)).comp
          (faceLin i) := hcomp2.fderiv
  rw [hgoal, fd_comp_inr Φ hΦ p (faceMap i c z)]

/-- The parameter-derivative of `Φ_{i,c}` is surjective at every zero in the box. -/
lemma PhiIc_hsurj {m : ℕ} (Φ : Pm m × Cz → Tw) (i : Fin 7) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsurj : ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p)) :
    ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → PhiIc Φ i c (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => PhiIc Φ i c (p', z)) p) := by
  intro p z hz h0
  have hz' : faceMap i c z ∈ Submission.Drive.unitBox 6 := faceMap_mem_unitBox hc0 hc1 hz
  have h0' : Φ (p, faceMap i c z) = 0 := h0
  have h := hsurj p (faceMap i c z) hz' h0'
  change Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', faceMap i c z)) p)
  exact h

/-! ## The two-valued index -/

/-- `false ↦ 0`, `true ↦ 1`. -/
def cval (b : Bool) : ℝ := if b then 1 else 0

/-- The Bool with value `1` exactly when `x = 1`. -/
def boolOf (x : ℝ) : Bool := if x = 1 then true else false

lemma cval_boolOf {x : ℝ} (h : x = 0 ∨ x = 1) : cval (boolOf x) = x := by
  rcases h with rfl | rfl
  · simp [boolOf, cval]
  · simp [boolOf, cval]

lemma cval_nonneg (b : Bool) : 0 ≤ cval b := by
  cases b <;> simp [cval]

lemma cval_le_one (b : Bool) : cval b ≤ 1 := by
  cases b <;> simp [cval]

/-- The finite family of maps: `Φ` itself and the face maps `Φ_{i,c}`. -/
def mapFam {m : ℕ} (Φ : Pm m × Cz → Tw) : Option (Fin 7 × Bool) → Pm m × Cz → Tw :=
  fun o => Option.elim o Φ (fun jb => PhiIc Φ jb.1 (cval jb.2))

lemma mapFam_none {m : ℕ} (Φ : Pm m × Cz → Tw) : mapFam Φ none = Φ := rfl

lemma mapFam_some {m : ℕ} (Φ : Pm m × Cz → Tw) (i : Fin 7) (b : Bool) :
    mapFam Φ (some (i, b)) = PhiIc Φ i (cval b) := rfl

/-! ## The main theorem -/

theorem generic_regularization_of_family_face (m : ℕ)
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 6 → Work.Drive.Tgt 6)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb 6),
      z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m),
      (∀ z ∈ Submission.Drive.unitBox 6, Φ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb 6 => Φ (p, z')) z)) ∧
      (∀ (i : Fin 7) (z : Work.Drive.Amb 6), z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
        (z i = 0 ∨ z i = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb 6 // v i = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb 6 => Φ (p, z')) z v.1)) := by
  classical
  have hmap_smooth : ∀ o : Option (Fin 7 × Bool),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mapFam Φ o) := by
    intro o
    cases o with
    | none => exact hΦ
    | some jb =>
      obtain ⟨i, b⟩ := jb
      exact PhiIc_contDiff Φ hΦ i (cval b)
  have hmap_hsurj : ∀ o : Option (Fin 7 × Bool),
      ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → mapFam Φ o (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun p' : Pm m => mapFam Φ o (p', z)) p) := by
    intro o
    cases o with
    | none => exact hsurj
    | some jb =>
      obtain ⟨i, b⟩ := jb
      exact PhiIc_hsurj Φ i (cval b) (cval_nonneg b) (cval_le_one b) hsurj
  have hFclosed : ∀ k : Option (Fin 7 × Bool) × ℕ,
      IsClosed (badSet m (mapFam Φ k.1) ∩ Metric.closedBall (0 : Pm m) k.2) :=
    fun k => (isCompact_badSet_inter_closedBall m (mapFam Φ k.1) (hmap_smooth k.1) k.2).isClosed
  have hFempty : ∀ k : Option (Fin 7 × Bool) × ℕ,
      interior (badSet m (mapFam Φ k.1) ∩ Metric.closedBall (0 : Pm m) k.2) = ∅ := by
    intro k
    exact subset_eq_empty (interior_mono Set.inter_subset_left)
      (interior_badSet_eq_empty m (mapFam Φ k.1) (hmap_smooth k.1) (hmap_hsurj k.1))
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hFclosed hFempty
  have hunion : (⋃ k : Option (Fin 7 × Bool) × ℕ,
        badSet m (mapFam Φ k.1) ∩ Metric.closedBall (0 : Pm m) k.2)
      = ⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, badSet]
    constructor
    · rintro ⟨k, ⟨z, hz, hz0, hz1⟩, -⟩
      exact ⟨k.1, z, hz, hz0, hz1⟩
    · rintro ⟨o, z, hz, hz0, hz1⟩
      obtain ⟨n, hn⟩ := exists_nat_ge ‖p‖
      exact ⟨(o, n), ⟨z, hz, hz0, hz1⟩,
        Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hn)⟩
  have hBempty : interior (⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o)) = ∅ := by
    rw [← hunion]
    exact hBaire
  have hnotall : (⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o)) ≠ Set.univ := by
    intro h
    have h1 : interior (⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o)) = Set.univ := by
      rw [h]; exact interior_univ
    rw [hBempty] at h1
    have : (0 : Pm m) ∈ (∅ : Set (Pm m)) := by
      rw [h1]
      exact Set.mem_univ 0
    exact this
  obtain ⟨p, hp⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnotall
  refine ⟨p, ?_, ?_⟩
  · intro z hz h0
    by_contra hbad
    refine hp (Set.mem_iUnion.mpr ⟨none, ?_⟩)
    show p ∈ badSet m Φ
    exact ⟨z, hz, h0, hbad⟩
  · intro i z hz h0 hzi
    by_contra hbad
    have hpface : p ∈ badSet m (PhiIc Φ i (z i)) := by
      refine ⟨z, hz, ?_, ?_⟩
      · show PhiIc Φ i (z i) (p, z) = 0
        rw [PhiIc, faceMap_self i z]
        exact h0
      · intro hD
        have hD' : Function.Surjective
            ((fderiv ℝ (fun w : Cz => Φ (p, w)) z).comp (faceLin i)) := by
          have h1 := fderiv_PhiIc Φ hΦ i (z i) p z
          rw [faceMap_self i z] at h1
          rw [← h1]
          exact hD
        exact hbad ((surjective_comp_faceLin_iff _ i).mp hD')
    refine hp (Set.mem_iUnion.mpr ⟨some (i, boolOf (z i)), ?_⟩)
    have hval : cval (boolOf (z i)) = z i := cval_boolOf hzi
    show p ∈ badSet m (PhiIc Φ i (cval (boolOf (z i))))
    rw [hval]
    exact hpface

end

end Work.MetricSquare
