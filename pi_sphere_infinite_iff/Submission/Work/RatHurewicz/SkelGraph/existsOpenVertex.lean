import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.goodDefs

namespace Work.RatHurewicz.SkelGraph

/- Please state and prove this as `Work.RatHurewicz.SkelGraph.existsOpenVertex`, i.e. inside `namespace Work.RatHurewicz.SkelGraph`, in the file `Submission/Work/RatHurewicz/SkelGraph/existsOpenVertex.lean` (it must import `Submission.Work.RatHurewicz.SkelGraph.goodDefs`).  Prefix any helper lemmas you add with `existsOpenVertex_`.

**A neighbourhood of a vertex of the model consisting of "good" points.**

`Work.RatHurewicz.SkelGraph.GoodAux.good D U` is the set of low dimensional raw points whose
canonical graph data `Work.RatHurewicz.SkelGraph.wOf` lies in `U`, and
`Work.RatHurewicz.SkelGraph.GoodAux.Sat D U` says that `U` is a union of classes of the graph
relation on `V D ⊕ (E D × I)`.

Plan.  Take `N` to be a ball (in the sup metric of the copy `Δ^{n+2}`) around the vertex
`stdSimplex.vertex p`, of radius `δ > 0` smaller than `1` and smaller than the (finitely many)
thresholds supplied by `GoodAux.exists_nhds_pair` below.  A low dimensional `y' = Sum.inl ⟨i, x'⟩`
in `N` has support either `{p}` (then `x' = stdSimplex.vertex p` by `GoodAux.eq_vertex_of_supp`,
so the graph data is `Sum.inl (vCl D (Sum.inl ⟨i,p⟩)) ∈ U` by `GoodAux.wOf_vertex` and the
hypothesis) or `{p, r}` for a single `r ≠ p`: then by `GoodAux.exists_sdPt_of_supp` one has
`x' = sdPt (min p r) (max p r) s` with `s` the coordinate at the larger index, and
`GoodAux.wOf_sdPt` gives that the graph data of `y'` is `Sum.inr (eCl D (Sum.inl ⟨i,{(min,max)}⟩), s)`.
* If `p < r` then `s = x' r < δ`, while `a D (eCl D (Sum.inl ⟨i, (⟨(p,r),_⟩ : EdgeRaw D)⟩)) =
  vCl D (Sum.inl ⟨i,p⟩) = a` and `GoodAux.Sat.mem_zero` gives `Sum.inr (e, 0) ∈ U`; since `U` is
  open there is `ε > 0` with `(e, t) ∈ U` for all `t < ε` (`GoodAux.exists_nhds_pair`), and
  `δ ≤ ε` gives the claim.
* If `r < p` then `s = x' p > 1 - δ`; use `b D`, `GoodAux.b_eCl_inl`, `GoodAux.Sat.mem_one` and
  the threshold near `1` in the same way.
The finitely many cases `r ≠ p` are handled by taking `δ` smaller than all the thresholds. -/

open scoped Topology Simplicial unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## Auxiliary lemmas -/

/-- The coordinate bound coming from the sup-metric distance to a vertex of the standard
simplex. -/
theorem existsOpenVertex_coord {m : ℕ} {δ : ℝ} {p : Fin m} {x : stdSimplex ℝ (Fin m)}
    (h : dist x (stdSimplex.vertex p) < δ) (k : Fin m) :
    |(x : Fin m → ℝ) k - (stdSimplex.vertex p : Fin m → ℝ) k| < δ := by
  have h1 : dist (x : Fin m → ℝ) (stdSimplex.vertex p : Fin m → ℝ) < δ := by
    rwa [Subtype.dist_eq] at h
  have h2 : dist ((x : Fin m → ℝ) k) ((stdSimplex.vertex p : Fin m → ℝ) k)
      ≤ dist (x : Fin m → ℝ) (stdSimplex.vertex p : Fin m → ℝ) := dist_le_pi_dist _ _ k
  have h3 : dist ((x : Fin m → ℝ) k) ((stdSimplex.vertex p : Fin m → ℝ) k) < δ :=
    lt_of_le_of_lt h2 h1
  rwa [Real.dist_eq] at h3

/-- The coordinates of a vertex of the standard simplex. -/
theorem existsOpenVertex_vertex_apply {m : ℕ} (p k : Fin m) :
    (stdSimplex.vertex p : Fin m → ℝ) k = if k = p then 1 else 0 := by
  rw [stdSimplex.vertex_coe, Pi.single_apply]

/-- A window of parameters near `0` on an edge whose initial vertex lies in `U`. -/
theorem existsOpenVertex_window_zero {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))}
    (hU : IsOpen U) (hSat : GoodAux.Sat D U) {e : E D} {v : V D}
    (he : a D e = v) (hv : Sum.inl v ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : I, (t : ℝ) < ε → Sum.inr (e, t) ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := GoodAux.exists_nhds_pair (D := D) hU (hSat.mem_zero he hv)
  refine ⟨ε, hε, fun t ht => hsub t ?_⟩
  rw [show ((0 : I) : ℝ) = 0 from rfl, sub_zero, abs_of_nonneg t.2.1]
  exact ht

/-- A window of parameters near `1` on an edge whose terminal vertex lies in `U`. -/
theorem existsOpenVertex_window_one {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))}
    (hU : IsOpen U) (hSat : GoodAux.Sat D U) {e : E D} {v : V D}
    (he : b D e = v) (hv : Sum.inl v ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : I, 1 - (t : ℝ) < ε → Sum.inr (e, t) ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := GoodAux.exists_nhds_pair (D := D) hU (hSat.mem_one he hv)
  refine ⟨ε, hε, fun t ht => hsub t ?_⟩
  rw [show ((1 : I) : ℝ) = 1 from rfl, abs_of_nonpos (by linarith [t.2.2])]
  linarith

/-- The edge of the copy `i` linking the vertex `p` to the vertex `r`, as an ordered pair. -/
def existsOpenVertex_edgeOf (D : MData X n x₀) (i : D.Idx) {p : Fin (n + 2)}
    (t : {r : Fin (n + 2) // r ≠ p}) : E D :=
  eCl D (Sum.inl ⟨i, (⟨(min p t.1, max p t.1), (min_lt_max).mpr (Ne.symm t.2)⟩ :
    {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩)

/-- The end point of the edge `existsOpenVertex_edgeOf D i t` at which the vertex `p` sits. -/
def existsOpenVertex_u {p : Fin (n + 2)} (t : {r : Fin (n + 2) // r ≠ p}) : I :=
  if p < t.1 then 0 else 1

theorem existsOpenVertex {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀)
    {U : Set (Work.RatHurewicz.SkelGraph.V D ⊕
      (Work.RatHurewicz.SkelGraph.E D × unitInterval))}
    (hU : IsOpen U) (hSat : Work.RatHurewicz.SkelGraph.GoodAux.Sat D U)
    {i : D.Idx} {p : Fin (n + 2)}
    (hmem : Sum.inl (Work.RatHurewicz.SkelGraph.vCl D (Sum.inl ⟨i, p⟩)) ∈ U) :
    ∃ N : Set (Work.RatHurewicz.Raw D), IsOpen N ∧
      (Sum.inl (⟨i, stdSimplex.vertex p⟩ :
        Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) : Work.RatHurewicz.Raw D) ∈ N ∧
      ∀ y' ∈ N, Work.RatHurewicz.isLowDim D y' →
        y' ∈ Work.RatHurewicz.SkelGraph.GoodAux.good D U := by
  classical
  have hcard : 1 < Fintype.card (Fin (n + 2)) := by
    rw [Fintype.card_fin]; omega
  haveI : Nonempty {r : Fin (n + 2) // r ≠ p} := by
    obtain ⟨r, hr⟩ := Fintype.exists_ne_of_one_lt_card hcard p
    exact ⟨⟨r, hr⟩⟩
  -- the finitely many thresholds, one for each neighbour `r ≠ p` of `p`
  have hthr : ∀ t : {r : Fin (n + 2) // r ≠ p}, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : I, |(s : ℝ) - (existsOpenVertex_u t : ℝ)| < ε →
        Sum.inr (existsOpenVertex_edgeOf D i t, s) ∈ U := by
    intro t
    by_cases hlt : p < t.1
    · have hEt : existsOpenVertex_edgeOf D i t
          = eCl D (Sum.inl ⟨i, (⟨(p, t.1), hlt⟩ :
            {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩) := by
        simp only [existsOpenVertex_edgeOf, min_eq_left hlt.le, max_eq_right hlt.le]
      have he : a D (existsOpenVertex_edgeOf D i t) = vCl D (Sum.inl ⟨i, p⟩) := by
        rw [hEt]; exact GoodAux.a_eCl_inl (D := D) i p t.1 hlt
      obtain ⟨ε, hε, hsub⟩ := existsOpenVertex_window_zero (D := D) hU hSat he hmem
      refine ⟨ε, hε, fun s hs => hsub s ?_⟩
      have hu0 : existsOpenVertex_u t = 0 := by
        simp only [existsOpenVertex_u, if_pos hlt]
      rw [hu0] at hs
      rw [show ((0 : I) : ℝ) = 0 from rfl, sub_zero, abs_of_nonneg s.2.1] at hs
      exact hs
    · have hrp : t.1 < p := lt_of_le_of_ne (le_of_not_gt hlt) t.2
      have hEt : existsOpenVertex_edgeOf D i t
          = eCl D (Sum.inl ⟨i, (⟨(t.1, p), hrp⟩ :
            {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩) := by
        simp only [existsOpenVertex_edgeOf, min_eq_right hrp.le, max_eq_left hrp.le]
      have he : b D (existsOpenVertex_edgeOf D i t) = vCl D (Sum.inl ⟨i, p⟩) := by
        rw [hEt]; exact GoodAux.b_eCl_inl (D := D) i t.1 p hrp
      obtain ⟨ε, hε, hsub⟩ := existsOpenVertex_window_one (D := D) hU hSat he hmem
      refine ⟨ε, hε, fun s hs => hsub s ?_⟩
      have hu1 : existsOpenVertex_u t = 1 := by
        simp only [existsOpenVertex_u, if_neg hlt]
      rw [hu1] at hs
      rw [show ((1 : I) : ℝ) = 1 from rfl,
        abs_of_nonpos (by linarith [s.2.2])] at hs
      linarith
  -- combine the finitely many thresholds into one radius
  set vals : Finset ℝ := insert (1 / 2 : ℝ)
    ((Finset.univ : Finset {r : Fin (n + 2) // r ≠ p}).image
      (fun t => Classical.choose (hthr t))) with hvals
  have hvals_pos : ∀ v ∈ vals, 0 < v := by
    intro v hv
    rw [hvals] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · norm_num
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hv
      exact (Classical.choose_spec (hthr t)).1
  have hvals_ne : vals.Nonempty := by
    rw [hvals]; exact Finset.insert_nonempty _ _
  set δ : ℝ := vals.min' hvals_ne with hδdef
  have hδmem : δ ∈ vals := by rw [hδdef]; exact Finset.min'_mem vals hvals_ne
  have hδle : ∀ v ∈ vals, δ ≤ v := by
    intro v hv; rw [hδdef]; exact Finset.min'_le vals v hv
  have hδpos : 0 < δ := hvals_pos δ hδmem
  have hδlt : δ < 1 :=
    lt_of_le_of_lt (hδle (1 / 2) (by rw [hvals]; exact Finset.mem_insert_self _ _))
      (by norm_num)
  have hδthr : ∀ t : {r : Fin (n + 2) // r ≠ p}, δ ≤ Classical.choose (hthr t) := by
    intro t
    refine hδle _ ?_
    rw [hvals]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  -- the neighbourhood
  set B : Set (stdSimplex ℝ (Fin (n + 2))) := {x | dist x (stdSimplex.vertex p) < δ} with hB
  set P : Set (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) :=
    (fun x : stdSimplex ℝ (Fin (n + 2)) =>
      (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) '' B with hP
  set N : Set (Raw D) := Sum.inl '' P with hN
  have hBopen : IsOpen B := by
    rw [hB]; exact Metric.isOpen_ball
  have hPopen : IsOpen P := by
    rw [hP, isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · rw [hji]
      have : Sigma.mk i ⁻¹' ((fun x : stdSimplex ℝ (Fin (n + 2)) =>
          (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) '' B) = B := by
        ext x
        rw [Set.mem_preimage, Set.mem_image]
        constructor
        · rintro ⟨y, hy, hyx⟩
          have hyx' : y = x := eq_of_heq (Sigma.mk.inj_iff.mp hyx).2
          rwa [← hyx']
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [this]; exact hBopen
    · have hnil : Sigma.mk j ⁻¹' ((fun x : stdSimplex ℝ (Fin (n + 2)) =>
          (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) '' B) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨y, hy, hyx⟩
        exact hji (Sigma.mk.inj_iff.mp hyx).1.symm
      rw [hnil]; exact isOpen_empty
  have hNopen : IsOpen N := by
    rw [hN, isOpen_sum_iff]
    constructor
    · rwa [Set.preimage_image_eq _ Sum.inl_injective]
    · have : Sum.inr ⁻¹' (Sum.inl '' P : Set (Raw D)) = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨z, hz, hzy⟩
        exact Sum.inr_ne_inl hzy.symm
      rw [this]; exact isOpen_empty
  have hmemN : (Sum.inl (⟨i, stdSimplex.vertex p⟩ :
      Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) : Raw D) ∈ N := by
    rw [hN]
    refine ⟨⟨i, stdSimplex.vertex p⟩, ?_, rfl⟩
    rw [hP]
    refine ⟨stdSimplex.vertex p, ?_, rfl⟩
    rw [hB, Set.mem_ofPred_eq]
    simpa [dist_self] using hδpos
  refine ⟨N, hNopen, hmemN, ?_⟩
  intro y' hy'N hlow
  rw [hN] at hy'N
  obtain ⟨z, hzP, rfl⟩ := hy'N
  rw [hP] at hzP
  obtain ⟨x', hxB, rfl⟩ := hzP
  rw [hB, Set.mem_ofPred_eq] at hxB
  have hcoord : ∀ k : Fin (n + 2),
      |(x' : Fin (n + 2) → ℝ) k - (stdSimplex.vertex p : Fin (n + 2) → ℝ) k| < δ :=
    fun k => existsOpenVertex_coord hxB k
  have hp_pos : 0 < (x' : Fin (n + 2) → ℝ) p := by
    have h := hcoord p
    rw [existsOpenVertex_vertex_apply p p, if_pos rfl] at h
    have h' := abs_lt.mp h
    linarith [h'.1, hδlt]
  have hp_mem : p ∈ supp x' := by
    rw [mem_supp]; exact ne_of_gt hp_pos
  have hcard2 : (supp x').card ≤ 2 := hlow
  by_cases hcard_one : (supp x').card = 1
  · have hsupp : supp x' = {p} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard_one
      have hpa : p = a := by
        have hm := hp_mem
        rw [ha] at hm
        simpa using hm
      rw [ha, hpa]
    have hxv : x' = stdSimplex.vertex p := GoodAux.eq_vertex_of_supp hsupp
    refine ⟨hlow, ?_⟩
    subst hxv
    rw [GoodAux.wOf_vertex (D := D) i p hlow]
    exact hmem
  · have hcard_eq2 : (supp x').card = 2 := by
      have hpos : 0 < (supp x').card := Finset.card_pos.mpr (supp_nonempty x')
      omega
    obtain ⟨a, b, hab, hsuppab⟩ := Finset.card_eq_two.mp hcard_eq2
    have hpab : p = a ∨ p = b := by
      have hm := hp_mem
      rw [hsuppab] at hm
      simpa using hm
    have key : ∀ (r : Fin (n + 2)) (hr : r ≠ p), supp x' = {p, r} →
        Sum.inl (⟨i, x'⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) ∈ GoodAux.good D U := by
      intro r hr hsupp
      rcases lt_or_gt_of_ne hr with hrp | hpr
      · -- r < p : the relevant end point of the edge is `1`
        have hsupp' : supp x' = {r, p} := by rw [hsupp]; exact Finset.pair_comm p r
        obtain ⟨s, hsx, hsv, hs0, hs1⟩ := GoodAux.exists_sdPt_of_supp hrp hsupp'
        have hsr : (x' : Fin (n + 2) → ℝ) r < δ := by
          have h := hcoord r
          rw [existsOpenVertex_vertex_apply p r, if_neg hr, sub_zero] at h
          exact (abs_lt.mp h).2
        have h1s : 1 - (s : ℝ) < δ := by
          have hxr : (x' : Fin (n + 2) → ℝ) r = 1 - (s : ℝ) := by
            rw [hsx, sdPt_apply_left hrp.ne]
          linarith [hsr, hxr]
        refine ⟨hlow, ?_⟩
        have hwEc : wOf D ⟨Sum.inl (⟨i, x'⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), hlow⟩
            = Sum.inr (eCl D (Sum.inl ⟨i, (⟨(r, p), hrp⟩ :
                {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩), s) := by
          cases hsx
          exact GoodAux.wOf_sdPt (D := D) (p := r) (q := p) (s := s) hrp hs0 hs1 hlow
        rw [hwEc]
        have hEt : existsOpenVertex_edgeOf D i (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p})
            = eCl D (Sum.inl ⟨i, (⟨(r, p), hrp⟩ :
                {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩) := by
          simp only [existsOpenVertex_edgeOf, min_eq_right hrp.le, max_eq_left hrp.le]
        have hu1 : existsOpenVertex_u (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p}) = 1 := by
          simp only [existsOpenVertex_u, if_neg (not_lt.mpr hrp.le)]
        have hcond : |(s : ℝ) - (existsOpenVertex_u (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p}) : ℝ)|
            < Classical.choose (hthr ⟨r, hr⟩) := by
          have h1 : |(s : ℝ) - (existsOpenVertex_u (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p}) : ℝ)|
              = 1 - (s : ℝ) := by
            rw [hu1, show ((1 : I) : ℝ) = 1 from rfl,
              abs_of_nonpos (by linarith [hs1])]
            ring
          rw [h1]
          exact lt_of_lt_of_le h1s (hδthr ⟨r, hr⟩)
        have hmemU := (Classical.choose_spec (hthr ⟨r, hr⟩)).2 s hcond
        rw [hEt] at hmemU
        exact hmemU
      · -- p < r : the relevant end point of the edge is `0`
        obtain ⟨s, hsx, hsv, hs0, hs1⟩ := GoodAux.exists_sdPt_of_supp hpr hsupp
        have hsr : (x' : Fin (n + 2) → ℝ) r < δ := by
          have h := hcoord r
          rw [existsOpenVertex_vertex_apply p r, if_neg hr, sub_zero] at h
          exact (abs_lt.mp h).2
        have hsδ : (s : ℝ) < δ := by
          have hxr : (x' : Fin (n + 2) → ℝ) r = (s : ℝ) := by
            rw [hsx, sdPt_apply_right hpr.ne]
          linarith [hsr, hxr]
        refine ⟨hlow, ?_⟩
        have hwEc : wOf D ⟨Sum.inl (⟨i, x'⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), hlow⟩
            = Sum.inr (eCl D (Sum.inl ⟨i, (⟨(p, r), hpr⟩ :
                {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩), s) := by
          cases hsx
          exact GoodAux.wOf_sdPt (D := D) (p := p) (q := r) (s := s) hpr hs0 hs1 hlow
        rw [hwEc]
        have hEt : existsOpenVertex_edgeOf D i (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p})
            = eCl D (Sum.inl ⟨i, (⟨(p, r), hpr⟩ :
                {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩) := by
          simp only [existsOpenVertex_edgeOf, min_eq_left hpr.le, max_eq_right hpr.le]
        have hu0 : existsOpenVertex_u (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p}) = 0 := by
          simp only [existsOpenVertex_u, if_pos hpr]
        have hcond : |(s : ℝ) - (existsOpenVertex_u (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p}) : ℝ)|
            < Classical.choose (hthr ⟨r, hr⟩) := by
          have h1 : |(s : ℝ) - (existsOpenVertex_u (⟨r, hr⟩ : {q : Fin (n + 2) // q ≠ p}) : ℝ)|
              = (s : ℝ) := by
            rw [hu0, show ((0 : I) : ℝ) = 0 from rfl, sub_zero, abs_of_nonneg s.2.1]
          rw [h1]
          exact lt_of_lt_of_le hsδ (hδthr ⟨r, hr⟩)
        have hmemU := (Classical.choose_spec (hthr ⟨r, hr⟩)).2 s hcond
        rw [hEt] at hmemU
        exact hmemU
    rcases hpab with hpa | hpb
    · exact key b (by rw [hpa]; exact Ne.symm hab) (by rw [hsuppab, hpa])
    · exact key a (by rw [hpb]; exact hab) (by rw [hsuppab, hpb]; exact Finset.pair_comm a b)

end

end Work.RatHurewicz.SkelGraph
