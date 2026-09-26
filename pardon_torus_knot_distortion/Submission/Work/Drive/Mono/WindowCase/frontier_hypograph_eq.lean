import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs

namespace Work.Drive.Mono.WindowCase

open Set

noncomputable section

/-! # The frontier of the solid under a graph over a compact plane set

This file computes the frontier of the solid

`hypo K g = {P : ℝ³ | cproj P ∈ K ∧ 0 ≤ clast P ≤ g (cproj P)}`

over a compact plane set `K` under a continuous nonnegative height `g`: it is the union of the
bottom disc `{clast = 0}`, the top graph `{clast = g}`, and the side wall over `frontier K`.

The two ingredients are

* `hypo K g` is closed (`hypo_isClosed`), because on the closed set `cproj ⁻¹' K` the function
  `clast - g ∘ cproj` is continuous; and
* `interior (hypo K g) = {P | cproj P ∈ interior K ∧ 0 < clast P < g (cproj P)}`
  (`interior_hypo_eq`).

Neither `closure (interior K) = K` nor the strict positivity `hgpos` of `g` on `interior K` is
needed for this computation; they are carried along for the consumer.
-/

/-- The solid under the graph of `g` over `K`: the "hypograph" region of the statement. -/
def hypo (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | Work.Drive.Mono.cproj P ∈ K ∧ 0 ≤ Work.Drive.Mono.clast P ∧
    Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)}

/-- The bottom disc of the solid. -/
def hypoBot (K : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | Work.Drive.Mono.cproj P ∈ K ∧ Work.Drive.Mono.clast P = 0}

/-- The top graph of the solid. -/
def hypoTop (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | Work.Drive.Mono.cproj P ∈ K ∧ Work.Drive.Mono.clast P = g (Work.Drive.Mono.cproj P)}

/-- The side wall of the solid, over the frontier of `K`. -/
def hypoWall (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | Work.Drive.Mono.cproj P ∈ frontier K ∧ 0 ≤ Work.Drive.Mono.clast P ∧
    Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)}

/-! ## Two metric normal forms for `cmk` -/

theorem norm_cmk_zero (y : ℝ) :
    ‖Work.Drive.Mono.cmk (0 : EuclideanSpace ℝ (Fin 2)) y‖ = |y| := by
  have h2 : ‖Work.Drive.Mono.cmk (0 : EuclideanSpace ℝ (Fin 2)) y‖ ^ 2 = y ^ 2 := by
    rw [Work.Drive.Mono.norm_sq_cmk]
    simp
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq_eq_abs]

theorem norm_cmk_zero_left (x : EuclideanSpace ℝ (Fin 2)) :
    ‖Work.Drive.Mono.cmk x 0‖ = ‖x‖ := by
  have h2 : ‖Work.Drive.Mono.cmk x 0‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Work.Drive.Mono.norm_sq_cmk]
    simp
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq (norm_nonneg x)]

/-- Distances in `ℝ³` between two points with the same plane projection. -/
theorem dist_cmk_same_proj (x : EuclideanSpace ℝ (Fin 2)) (y y' : ℝ) :
    dist (Work.Drive.Mono.cmk x y) (Work.Drive.Mono.cmk x y') = |y - y'| := by
  rw [dist_eq_norm, Work.Drive.Mono.cmk_sub, sub_self x, norm_cmk_zero]

/-- Distances in `ℝ³` between two points with the same `clast`. -/
theorem dist_cmk_same_last (x x' : EuclideanSpace ℝ (Fin 2)) (y : ℝ) :
    dist (Work.Drive.Mono.cmk x y) (Work.Drive.Mono.cmk x' y) = dist x x' := by
  rw [dist_eq_norm, dist_eq_norm, Work.Drive.Mono.cmk_sub, sub_self y, norm_cmk_zero_left]

/-! ## The intermediate open region -/

/-- The interior of the solid, in coordinates. -/
def hypoInt (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | Work.Drive.Mono.cproj P ∈ interior K ∧ 0 < Work.Drive.Mono.clast P ∧
    Work.Drive.Mono.clast P < g (Work.Drive.Mono.cproj P)}

open scoped Classical in
/-- The solid `hypo K g` is closed. -/
theorem hypo_isClosed {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hKcomp : IsCompact K) (hgc : ContinuousOn g K) : IsClosed (hypo K g) := by
  have hKclosed : IsClosed K := hKcomp.isClosed
  have hT : IsClosed ((K ×ˢ Set.Ici (0 : ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - g q.1) ⁻¹' Set.Iic (0 : ℝ)) := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hKclosed.prod isClosed_Ici) isClosed_Iic
    show ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - g q.1) (K ×ˢ Set.Ici (0 : ℝ))
    have h1 : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => g q.1) (K ×ˢ Set.Ici (0:ℝ)) :=
      hgc.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have h2 : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2) (K ×ˢ Set.Ici (0:ℝ)) :=
      continuous_snd.continuousOn
    exact h2.sub h1
  have hmap : Continuous (fun P : EuclideanSpace ℝ (Fin 3) =>
      (Work.Drive.Mono.cproj P, Work.Drive.Mono.clast P)) :=
    Work.Drive.Mono.continuous_cproj.prodMk Work.Drive.Mono.continuous_clast
  have heq : hypo K g = (fun P : EuclideanSpace ℝ (Fin 3) =>
      (Work.Drive.Mono.cproj P, Work.Drive.Mono.clast P)) ⁻¹'
      ((K ×ˢ Set.Ici (0 : ℝ)) ∩
        (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - g q.1) ⁻¹' Set.Iic (0 : ℝ)) := by
    ext P
    simp only [hypo, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ici,
      Set.mem_Iic, Set.mem_ofPred_eq, sub_nonpos]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  rw [heq]
  exact hT.preimage hmap

/-- The intermediate region is open. -/
theorem isOpen_hypoInt {K : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hgc : ContinuousOn g K) :
    IsOpen (hypoInt K g) := by
  rw [isOpen_iff_mem_nhds]
  intro P hP
  simp only [hypoInt, Set.mem_ofPred_eq] at hP
  obtain ⟨hPK, hPc0, hPcg⟩ := hP
  have hPK' : Work.Drive.Mono.cproj P ∈ K := interior_subset hPK
  set c := Work.Drive.Mono.clast P with hc
  set g0 := g (Work.Drive.Mono.cproj P) with hg0
  have hη : 0 < (g0 - c) / 2 := by rw [hc, hg0]; linarith
  obtain ⟨δ1, hδ1pos, hδ1⟩ :=
    Metric.continuousWithinAt_iff.mp (hgc _ hPK') ((g0 - c) / 2) hη
  obtain ⟨δ2, hδ2pos, hδ2⟩ :=
    Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hPK)
  set δ := min δ1 (min δ2 (min (c / 2) ((g0 - c) / 2))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min hδ1pos (lt_min hδ2pos (lt_min (by linarith) hη))
  have hδδ1 : δ ≤ δ1 := by rw [hδ]; exact min_le_left _ _
  have hδδ2 : δ ≤ δ2 := by
    rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδc : δ ≤ c / 2 := by
    rw [hδ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδη : δ ≤ (g0 - c) / 2 := by
    rw [hδ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδpos, fun Q hQ => ?_⟩
  rw [Metric.mem_ball] at hQ
  have hproj : dist (Work.Drive.Mono.cproj Q) (Work.Drive.Mono.cproj P) ≤ dist Q P := by
    rw [dist_eq_norm, dist_eq_norm, ← Work.Drive.Mono.cproj_sub]
    exact Work.Drive.Mono.norm_cproj_le (Q - P)
  have hlast : |Work.Drive.Mono.clast Q - Work.Drive.Mono.clast P| ≤ dist Q P := by
    rw [dist_eq_norm, ← Work.Drive.Mono.clast_sub]
    exact Work.Drive.Mono.abs_clast_le (Q - P)
  have hQK : Work.Drive.Mono.cproj Q ∈ K :=
    interior_subset (hδ2 (Metric.mem_ball.mpr
      (lt_of_le_of_lt hproj (lt_of_lt_of_le hQ hδδ2))))
  have hQproj : dist (Work.Drive.Mono.cproj Q) (Work.Drive.Mono.cproj P) < δ1 :=
    lt_of_le_of_lt hproj (lt_of_lt_of_le hQ hδδ1)
  have hgQ : dist (g (Work.Drive.Mono.cproj Q)) g0 < (g0 - c) / 2 := by
    have := hδ1 hQK hQproj
    rwa [← hg0] at this
  simp only [hypoInt, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact hδ2 (Metric.mem_ball.mpr (lt_of_le_of_lt hproj (lt_of_lt_of_le hQ hδδ2)))
  · have := neg_abs_le (Work.Drive.Mono.clast Q - Work.Drive.Mono.clast P)
    rw [← hc] at this
    linarith
  · have h4 : Work.Drive.Mono.clast Q < c + (g0 - c) / 2 := by
      have := le_abs_self (Work.Drive.Mono.clast Q - Work.Drive.Mono.clast P)
      rw [← hc] at this
      linarith
    have h5 : g0 - (g0 - c) / 2 < g (Work.Drive.Mono.cproj Q) := by
      have habs : |g (Work.Drive.Mono.cproj Q) - g0| < (g0 - c) / 2 := by
        rw [← Real.dist_eq]; exact hgQ
      have := (abs_lt.mp habs).1
      linarith
    linarith

/-- The intermediate region sits in the solid. -/
theorem hypoInt_subset {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ} :
    hypoInt K g ⊆ hypo K g := by
  intro P hP
  simp only [hypoInt, Set.mem_ofPred_eq] at hP
  exact ⟨interior_subset hP.1, le_of_lt hP.2.1, le_of_lt hP.2.2⟩

/-- **The interior of the solid, in coordinates.**  Only continuity of `g` on `K` is used; in
particular the description is correct without any strict positivity of `g`. -/
theorem interior_hypo_eq {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgc : ContinuousOn g K) :
    interior (hypo K g) = hypoInt K g := by
  refine Subset.antisymm ?_ (interior_maximal hypoInt_subset (isOpen_hypoInt hgc))
  intro P hP
  rw [mem_interior_iff_mem_nhds] at hP
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hP
  have hPH : P ∈ hypo K g := hδsub (Metric.mem_ball_self hδpos)
  simp only [hypo, Set.mem_ofPred_eq] at hPH
  obtain ⟨hPK, hPc0, hPcg⟩ := hPH
  have hP' : P = Work.Drive.Mono.cmk (Work.Drive.Mono.cproj P) (Work.Drive.Mono.clast P) :=
    (Work.Drive.Mono.cmk_cproj_clast P).symm
  simp only [hypoInt, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have hcl : Work.Drive.Mono.cproj P ∈ closure (Kᶜ) := by
      rw [closure_compl]; exact h
    obtain ⟨x, hxK, hxd⟩ := Metric.mem_closure_iff.mp hcl δ hδpos
    have hdist : dist (Work.Drive.Mono.cmk x (Work.Drive.Mono.clast P)) P < δ := by
      rw [hP']
      simp only [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
      rw [dist_cmk_same_last, dist_comm]
      exact hxd
    have hmem : Work.Drive.Mono.cmk x (Work.Drive.Mono.clast P) ∈ hypo K g :=
      hδsub (Metric.mem_ball.mpr hdist)
    simp only [hypo, Set.mem_ofPred_eq, Work.Drive.Mono.cproj_cmk] at hmem
    exact hxK hmem.1
  · by_contra h
    rw [not_lt] at h
    have hc0 : Work.Drive.Mono.clast P = 0 := le_antisymm h hPc0
    have hdist : dist (Work.Drive.Mono.cmk (Work.Drive.Mono.cproj P) (-(δ / 2))) P < δ := by
      rw [hP']
      simp only [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
      rw [dist_cmk_same_proj, hc0]
      rw [abs_lt]
      constructor <;> linarith
    have hmem : Work.Drive.Mono.cmk (Work.Drive.Mono.cproj P) (-(δ / 2)) ∈ hypo K g :=
      hδsub (Metric.mem_ball.mpr hdist)
    simp only [hypo, Set.mem_ofPred_eq, Work.Drive.Mono.clast_cmk] at hmem
    linarith [hmem.2.1]
  · by_contra h
    rw [not_lt] at h
    have heq : Work.Drive.Mono.clast P = g (Work.Drive.Mono.cproj P) := le_antisymm hPcg h
    have hdist :
        dist (Work.Drive.Mono.cmk (Work.Drive.Mono.cproj P) (Work.Drive.Mono.clast P + δ / 2)) P < δ := by
      rw [hP']
      simp only [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
      rw [dist_cmk_same_proj]
      rw [abs_lt]
      constructor <;> linarith
    have hmem : Work.Drive.Mono.cmk (Work.Drive.Mono.cproj P) (Work.Drive.Mono.clast P + δ / 2)
        ∈ hypo K g := hδsub (Metric.mem_ball.mpr hdist)
    simp only [hypo, Set.mem_ofPred_eq, Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
      at hmem
    rw [heq] at hmem
    linarith [hmem.2.2]

/-- **The frontier of the solid**, in the three pieces. -/
theorem hypo_frontier_eq {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hKcomp : IsCompact K) (hKcl : closure (interior K) = K)
    (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (hgpos : ∀ x ∈ interior K, 0 < g x) :
    frontier (hypo K g) = hypoBot K ∪ hypoTop K g ∪ hypoWall K g := by
  have hKclosed : IsClosed K := hKcomp.isClosed
  have hcl := hypo_isClosed hKcomp hgc
  have hint := interior_hypo_eq hgc
  have hfront : frontier (hypo K g) = hypo K g \ hypoInt K g := by
    unfold frontier
    rw [hcl.closure_eq, hint]
  rw [hfront]
  ext P
  constructor
  · intro hP
    rw [Set.mem_sdiff] at hP
    obtain ⟨hPH, hPni⟩ := hP
    simp only [hypo, Set.mem_ofPred_eq] at hPH
    obtain ⟨hPK, hPc0, hPcg⟩ := hPH
    by_cases hPKi : Work.Drive.Mono.cproj P ∈ interior K
    · have hnot : ¬ (0 < Work.Drive.Mono.clast P ∧
          Work.Drive.Mono.clast P < g (Work.Drive.Mono.cproj P)) := by
        intro hcon
        exact hPni (by
          simp only [hypoInt, Set.mem_ofPred_eq]
          exact ⟨hPKi, hcon.1, hcon.2⟩)
      rcases not_and_or.mp hnot with h | h
      · left; left
        exact ⟨interior_subset hPKi, le_antisymm (not_lt.mp h) hPc0⟩
      · left; right
        exact ⟨hPK, le_antisymm hPcg (not_lt.mp h)⟩
    · right
      refine ⟨?_, hPc0, hPcg⟩
      unfold frontier
      rw [hKclosed.closure_eq]
      exact ⟨hPK, hPKi⟩
  · intro hP
    rw [Set.mem_sdiff]
    rcases hP with (h1 | h2) | h3
    · -- the bottom disc
      simp only [hypoBot, Set.mem_ofPred_eq] at h1
      obtain ⟨hPK, hcz⟩ := h1
      refine ⟨?_, ?_⟩
      · simp only [hypo, Set.mem_ofPred_eq]
        refine ⟨hPK, ?_, ?_⟩
        · rw [hcz]
        · rw [hcz]
          exact hg0 _ hPK
      · intro hPI
        simp only [hypoInt, Set.mem_ofPred_eq] at hPI
        linarith [hPI.2.1, hcz]
    · -- the top graph
      simp only [hypoTop, Set.mem_ofPred_eq] at h2
      obtain ⟨hPK, hceq⟩ := h2
      refine ⟨?_, ?_⟩
      · simp only [hypo, Set.mem_ofPred_eq]
        exact ⟨hPK, by rw [hceq]; exact hg0 _ hPK, by rw [hceq]⟩
      · intro hPI
        simp only [hypoInt, Set.mem_ofPred_eq] at hPI
        linarith [hPI.2.2, hceq]
    · -- the side wall
      simp only [hypoWall, Set.mem_ofPred_eq] at h3
      refine ⟨?_, ?_⟩
      · simp only [hypo, Set.mem_ofPred_eq]
        refine ⟨?_, h3.2.1, h3.2.2⟩
        have h := h3.1.1
        rwa [hKclosed.closure_eq] at h
      · intro hPI
        simp only [hypoInt, Set.mem_ofPred_eq] at hPI
        exact h3.1.2 hPI.1

/-- PROOF HINT: put `K` closed (compact) and `R = {P | cproj P ∈ K ∧ 0 ≤ clast P ∧ clast P ≤ g (cproj P)}`,
so `frontier R = R \ interior R`, and show `interior R = {P | cproj P ∈ interior K ∧ 0 < clast P ∧
clast P < g (cproj P)}`.  Then split `K` as `interior K ∪ frontier K` and `0 ≤ clast P ≤ g (cproj P)`
into `clast P = 0`, `clast P = g (cproj P)` and the rest.  `hgpos` is what makes the interior
description correct at points of `interior K`; `hg0` makes the three displayed pieces subsets of `R`. -/
theorem frontier_hypograph_eq
    {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hKcomp : IsCompact K) (hKcl : closure (interior K) = K)
    (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (hgpos : ∀ x ∈ interior K, 0 < g x) :
    frontier {P : EuclideanSpace ℝ (Fin 3) |
        Work.Drive.Mono.cproj P ∈ K ∧ 0 ≤ Work.Drive.Mono.clast P ∧
        Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)} =
      {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ K ∧
        Work.Drive.Mono.clast P = 0} ∪
      {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ K ∧
        Work.Drive.Mono.clast P = g (Work.Drive.Mono.cproj P)} ∪
      {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ frontier K ∧
        0 ≤ Work.Drive.Mono.clast P ∧ Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)} := by
  show frontier (hypo K g) = hypoBot K ∪ hypoTop K g ∪ hypoWall K g
  exact hypo_frontier_eq hKcomp hKcl hgc hg0 hgpos

end

end Work.Drive.Mono.WindowCase
