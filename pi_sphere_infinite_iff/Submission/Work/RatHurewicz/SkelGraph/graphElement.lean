import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.points
import Submission.Work.RatHurewicz.SkelGraph.graphElementDefs
import Submission.Work.RatHurewicz.SkelGraph.graphElementAux
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.finiteGraphDefs

/-!
# The `1`-skeleton of the cycle model as the finite graph `GraphX (a D) (b D)`

See `Submission/Work/RatHurewicz/SkelGraph/` (`defs.lean`, `graphMap.lean`, `points.lean`): the
`1`-skeleton `Work.RatHurewicz.skeleton D` of the cycle model is the finite graph
`Work.RatHurewicz.GraphX (a D) (b D)`.  This file builds the inverse `f` of the map `Phi`, at the
level of the low dimensional points of `Raw D`: it is `y ↦ gq (wOf y)`, where `wOf` is the
canonical graph datum of a low dimensional point.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The graph datum of a raw point of the model (no low-dimensionality assumption). -/
def ge_wRaw (D : MData X n x₀) (y : Raw D) : V D ⊕ (E D × I) :=
  match y with
  | Sum.inl ⟨i, x⟩ => wSimp D i x
  | Sum.inr ⟨i, s⟩ => Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s)

theorem ge_wOf_eq_wRaw (D : MData X n x₀) (y : {y : Raw D // isLowDim D y}) :
    wOf D y = ge_wRaw D y.1 := by
  obtain ⟨y, h⟩ := y
  rcases y with ⟨i, x⟩ | ⟨i, s⟩ <;> rfl

theorem ge_wRaw_inl (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2)))
    (p : Fin (n + 2)) (hp : decomp x = Sum.inl p) :
    ge_wRaw D (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
      = Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) := by
  rw [ge_wRaw, wSimp, hp]

theorem ge_wRaw_inr (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2)))
    (e : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2}) (s : I)
    (hp : decomp x = Sum.inr (e, s)) :
    ge_wRaw D (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
      = Sum.inr (eCl D (Sum.inl ⟨i, e⟩), s) := by
  rw [ge_wRaw, wSimp, hp]

theorem ge_wRaw_inr_arc (D : MData X n x₀) (i : D.Idx) (s : I) :
    ge_wRaw D (Sum.inr (⟨i, s⟩ : Σ _ : D.Idx, I))
      = Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s) := rfl

theorem ge_wOf_inl (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2)))
    (h : isLowDim D (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))) :
    wOf D ⟨Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩ = wSimp D i x := by
  rw [ge_wOf_eq_wRaw]; rfl

theorem ge_wOf_inr (D : MData X n x₀) (i : D.Idx) (s : I)
    (h : isLowDim D (Sum.inr (⟨i, s⟩ : Σ _ : D.Idx, I))) :
    wOf D ⟨Sum.inr (⟨i, s⟩ : Σ _ : D.Idx, I), h⟩
      = Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s) := by
  rw [ge_wOf_eq_wRaw]; rfl

theorem ge_vertSk_vCl (D : MData X n x₀) (r : VertRaw D) :
    vertSk D (vCl D r) = (⟨vertM D r, mem_skeleton_vertM D r⟩ : ↥(skeleton D)) := rfl

theorem ge_edgeParam_eCl (D : MData X n x₀) (e : EdgeRaw D) (s : I) :
    edgeParam D (eCl D e) s = (⟨edgeM D e s, mem_skeleton_edgeM D e s⟩ : ↥(skeleton D)) := rfl

/-! ## The first conjunct: `Phi` inverts `wOf` -/

theorem ge_Phi_wOf (D : MData X n x₀) (y : {y : Raw D // isLowDim D y}) :
    Phi D (gq (a D) (b D) (wOf D y)) = toSkeleton D y := by
  obtain ⟨y, h⟩ := y
  rcases y with ⟨i, x⟩ | ⟨i, s⟩
  · rcases hd : decomp x with p | ⟨e, t⟩
    · have hw : wOf D ⟨Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩
          = Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) := by
        rw [ge_wOf_eq_wRaw]
        exact ge_wRaw_inl D i x p hd
      have hx : x = stdSimplex.vertex p := ge_eq_vertex_of_decomp_inl hd
      rw [hw, Phi_apply]
      change vertSk D (vCl D (Sum.inl ⟨i, p⟩))
        = toSkeleton D ⟨Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩
      rw [ge_vertSk_vCl]
      apply Subtype.ext
      show Quotient.mk'' (Sum.inl (⟨i, stdSimplex.vertex p⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
        = Quotient.mk'' (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
      rw [← hx]
    · have hx2 : (supp x).card ≤ 2 := h
      obtain ⟨hx, -, -⟩ := ge_eq_sdPt_of_decomp_inr hd hx2
      have hw : wOf D ⟨Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩
          = Sum.inr (eCl D (Sum.inl ⟨i, e⟩), t) := by
        rw [ge_wOf_eq_wRaw]
        exact ge_wRaw_inr D i x e t hd
      rw [hw, Phi_apply]
      change edgeParam D (eCl D (Sum.inl ⟨i, e⟩)) t
        = toSkeleton D ⟨Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩
      rw [ge_edgeParam_eCl]
      apply Subtype.ext
      show Quotient.mk'' (Sum.inl (⟨i, sdPt e.1.1 e.1.2 t⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
        = Quotient.mk'' (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
      rw [← hx]
  · have hw : wOf D ⟨Sum.inr (⟨i, s⟩ : Σ _ : D.Idx, I), h⟩
        = Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s) := by
      rw [ge_wOf_eq_wRaw]
      rfl
    rw [hw, Phi_apply]
    change edgeParam D (eCl D (Sum.inr ⟨i, PUnit.unit⟩)) s
      = toSkeleton D ⟨Sum.inr (⟨i, s⟩ : Σ _ : D.Idx, I), h⟩
    rw [ge_edgeParam_eCl]
    apply Subtype.ext
    rfl

/-! ## The second conjunct, reduced to `rawOf` -/

theorem ge_gq_rawOf_wOf (D : MData X n x₀) (w : V D ⊕ (E D × I)) :
    gq (a D) (b D) (wOf D (rawOf D w)) = gq (a D) (b D) w := by
  rw [ge_wOf_eq_wRaw]
  rcases w with v | ⟨e, s⟩
  · change gq (a D) (b D) (ge_wRaw D (vertPt D (Quotient.out v)))
      = gq (a D) (b D) (Sum.inl v)
    generalize hq : Quotient.out v = r
    rcases r with ⟨i, p⟩ | ⟨i, k⟩
    · have hv : vCl D (Sum.inl ⟨i, p⟩) = v := by rw [← hq]; exact Quotient.out_eq v
      change gq (a D) (b D) (wSimp D i (stdSimplex.vertex p)) = gq (a D) (b D) (Sum.inl v)
      rw [show wSimp D i (stdSimplex.vertex p) = Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) from by
        rw [wSimp, ge_decomp_vertex], hv]
    · have hv : vCl D (Sum.inr ⟨i, k⟩) = v := by rw [← hq]; exact Quotient.out_eq v
      change gq (a D) (b D) (Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), arcEnd k))
        = gq (a D) (b D) (Sum.inl v)
      rw [hv.symm]
      have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      rcases hk with hk | hk
      · rw [hk]
        simp only [arcEnd_zero]
        exact rel_ae (a D) (b D) (eCl D (Sum.inr ⟨i, PUnit.unit⟩))
      · rw [hk]
        simp only [arcEnd_one]
        exact rel_be (a D) (b D) (eCl D (Sum.inr ⟨i, PUnit.unit⟩))
  · change gq (a D) (b D) (ge_wRaw D (edgePt D (Quotient.out e) s))
      = gq (a D) (b D) (Sum.inr (e, s))
    generalize he : Quotient.out e = r
    rcases r with ⟨i, pq⟩ | ⟨i, u⟩
    · obtain ⟨⟨p, q⟩, hpq⟩ := pq
      have hev : eCl D (Sum.inl ⟨i, ⟨(p, q), hpq⟩⟩) = e := by rw [← he]; exact Quotient.out_eq e
      by_cases hs0 : (s : ℝ) = 0
      · have hss : s = (0 : I) := Subtype.ext hs0
        change gq (a D) (b D) (wSimp D i (sdPt p q s)) = gq (a D) (b D) (Sum.inr (e, s))
        rw [show wSimp D i (sdPt p q s) = Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) from by
          rw [hss, sdPt_zero, wSimp, ge_decomp_vertex], hss, ← hev]
        exact (rel_ae (a D) (b D) (eCl D (Sum.inl ⟨i, ⟨(p, q), hpq⟩⟩))).symm
      · by_cases hs1 : (s : ℝ) = 1
        · have hss : s = (1 : I) := Subtype.ext hs1
          change gq (a D) (b D) (wSimp D i (sdPt p q s)) = gq (a D) (b D) (Sum.inr (e, s))
          rw [show wSimp D i (sdPt p q s) = Sum.inl (vCl D (Sum.inl ⟨i, q⟩)) from by
            rw [hss, sdPt_one, wSimp, ge_decomp_vertex], hss, ← hev]
          exact (rel_be (a D) (b D) (eCl D (Sum.inl ⟨i, ⟨(p, q), hpq⟩⟩))).symm
        · have hs0' : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
          have hs1' : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 (fun h => hs1 h)
          change gq (a D) (b D) (wSimp D i (sdPt p q s)) = gq (a D) (b D) (Sum.inr (e, s))
          rw [show wSimp D i (sdPt p q s)
              = Sum.inr (eCl D (Sum.inl ⟨i, ⟨(p, q), hpq⟩⟩), s) from by
            rw [wSimp, ge_decomp_sdPt hpq hs0' hs1'], ← hev]
    · cases u
      have hev : eCl D (Sum.inr ⟨i, PUnit.unit⟩) = e := by rw [← he]; exact Quotient.out_eq e
      change gq (a D) (b D) (Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s))
        = gq (a D) (b D) (Sum.inr (e, s))
      rw [hev]

/-! ## The third conjunct: constancy on the gluing relation -/

theorem ge_wOf_rel (D : MData X n x₀) {a₀ b₀ : Raw D} (hab : modelRel D a₀ b₀) :
    ∀ (ha : isLowDim D a₀) (hb : isLowDim D b₀),
      gq (a D) (b D) (wOf D ⟨a₀, ha⟩) = gq (a D) (b D) (wOf D ⟨b₀, hb⟩) := by
  rcases hab with ⟨i, j, r, r', x, rfl, rfl, h3⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
  · intro ha hb
    have hx2 : (supp x).card ≤ 2 :=
      le_trans (ge_card_supp_le_card_supp_facept (m := n + 1) r x) ha
    rcases hd : decomp x with u | ⟨e, t⟩
    · have hx : x = stdSimplex.vertex u := ge_eq_vertex_of_decomp_inl hd
      have hfx : facept (n + 1) r x = stdSimplex.vertex (r.succAbove u) := by
        rw [hx]; exact ge_facept_vertex r u
      have hfx' : facept (n + 1) r' x = stdSimplex.vertex (r'.succAbove u) := by
        rw [hx]; exact ge_facept_vertex r' u
      have hwA : wOf D ⟨Sum.inl (⟨i, facept (n + 1) r x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), ha⟩
          = Sum.inl (vCl D (Sum.inl ⟨i, r.succAbove u⟩)) := by
        rw [ge_wOf_inl]
        rw [show wSimp D i (facept (n + 1) r x) = Sum.inl (vCl D (Sum.inl ⟨i, r.succAbove u⟩)) from by
          rw [hfx, wSimp, ge_decomp_vertex]]
      have hwB : wOf D ⟨Sum.inl (⟨j, facept (n + 1) r' x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), hb⟩
          = Sum.inl (vCl D (Sum.inl ⟨j, r'.succAbove u⟩)) := by
        rw [ge_wOf_inl]
        rw [show wSimp D j (facept (n + 1) r' x) = Sum.inl (vCl D (Sum.inl ⟨j, r'.succAbove u⟩)) from by
          rw [hfx', wSimp, ge_decomp_vertex]]
      rw [hwA, hwB]
      have hv : vCl D (Sum.inl ⟨i, r.succAbove u⟩) = vCl D (Sum.inl ⟨j, r'.succAbove u⟩) :=
        vCl_eq_of_vertM_eq D (by
          have h1 : vertM D (Sum.inl ⟨i, r.succAbove u⟩) =
              Quotient.mk'' (Sum.inl (⟨i, facept (n + 1) r x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) := by
            change Quotient.mk'' (Sum.inl (⟨i, stdSimplex.vertex (r.succAbove u)⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
              = Quotient.mk'' (Sum.inl (⟨i, facept (n + 1) r x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
            rw [← hfx]
          have h2 : vertM D (Sum.inl ⟨j, r'.succAbove u⟩) =
              Quotient.mk'' (Sum.inl (⟨j, facept (n + 1) r' x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) := by
            change Quotient.mk'' (Sum.inl (⟨j, stdSimplex.vertex (r'.succAbove u)⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
              = Quotient.mk'' (Sum.inl (⟨j, facept (n + 1) r' x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
            rw [← hfx']
          rw [h1, h2]
          exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl ⟨i, j, r, r', x, rfl, rfl, h3⟩)))
      rw [hv]
    · obtain ⟨hx, ht0, ht1⟩ := ge_eq_sdPt_of_decomp_inr hd hx2
      have hP : r.succAbove e.1.1 < r.succAbove e.1.2 :=
        (Fin.succAbove_lt_succAbove_iff (p := r)).mpr e.2
      have hQ : r'.succAbove e.1.1 < r'.succAbove e.1.2 :=
        (Fin.succAbove_lt_succAbove_iff (p := r')).mpr e.2
      have hfA : facept (n + 1) r x = sdPt (r.succAbove e.1.1) (r.succAbove e.1.2) t := by
        rw [hx]; exact facept_sdPt r e.1.1 e.1.2 t
      have hfB : facept (n + 1) r' x = sdPt (r'.succAbove e.1.1) (r'.succAbove e.1.2) t := by
        rw [hx]; exact facept_sdPt r' e.1.1 e.1.2 t
      have hdA : decomp (facept (n + 1) r x) =
          Sum.inr (⟨(r.succAbove e.1.1, r.succAbove e.1.2), hP⟩, t) := by
        rw [hfA]; exact ge_decomp_sdPt hP ht0 ht1
      have hdB : decomp (facept (n + 1) r' x) =
          Sum.inr (⟨(r'.succAbove e.1.1, r'.succAbove e.1.2), hQ⟩, t) := by
        rw [hfB]; exact ge_decomp_sdPt hQ ht0 ht1
      have hwA : wOf D ⟨Sum.inl (⟨i, facept (n + 1) r x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), ha⟩
          = Sum.inr (eCl D (Sum.inl ⟨i, ⟨(r.succAbove e.1.1, r.succAbove e.1.2), hP⟩⟩), t) := by
        rw [ge_wOf_inl]
        rw [show wSimp D i (facept (n + 1) r x)
            = Sum.inr (eCl D (Sum.inl ⟨i, ⟨(r.succAbove e.1.1, r.succAbove e.1.2), hP⟩⟩), t) from by
          rw [wSimp, hdA]]
      have hwB : wOf D ⟨Sum.inl (⟨j, facept (n + 1) r' x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), hb⟩
          = Sum.inr (eCl D (Sum.inl ⟨j, ⟨(r'.succAbove e.1.1, r'.succAbove e.1.2), hQ⟩⟩), t) := by
        rw [ge_wOf_inl]
        rw [show wSimp D j (facept (n + 1) r' x)
            = Sum.inr (eCl D (Sum.inl ⟨j, ⟨(r'.succAbove e.1.1, r'.succAbove e.1.2), hQ⟩⟩), t) from by
          rw [wSimp, hdB]]
      have heq : eCl D (Sum.inl ⟨i, ⟨(r.succAbove e.1.1, r.succAbove e.1.2), hP⟩⟩)
          = eCl D (Sum.inl ⟨j, ⟨(r'.succAbove e.1.1, r'.succAbove e.1.2), hQ⟩⟩) := by
        apply Quotient.sound
        intro s
        change Quotient.mk'' (Sum.inl (⟨i, sdPt (r.succAbove e.1.1) (r.succAbove e.1.2) s⟩ :
            Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
          = Quotient.mk'' (Sum.inl (⟨j, sdPt (r'.succAbove e.1.1) (r'.succAbove e.1.2) s⟩ :
            Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
        rw [← facept_sdPt r e.1.1 e.1.2 s, ← facept_sdPt r' e.1.1 e.1.2 s]
        exact Quotient.sound (Relation.EqvGen.rel _ _
          (Or.inl ⟨i, j, r, r', sdPt e.1.1 e.1.2 s, rfl, rfl, h3⟩))
      rw [hwA, hwB, heq]
  · intro ha hb
    have hwA : wOf D ⟨Sum.inl (⟨i, stdSimplex.vertex (0 : Fin (n + 2))⟩ :
        Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), ha⟩
        = Sum.inl (vCl D (Sum.inl ⟨i, (0 : Fin (n + 2))⟩)) := by
      rw [ge_wOf_inl]
      rw [show wSimp D i (stdSimplex.vertex (0 : Fin (n + 2)))
          = Sum.inl (vCl D (Sum.inl ⟨i, (0 : Fin (n + 2))⟩)) from by
        rw [wSimp, ge_decomp_vertex]]
    have hwB : wOf D ⟨Sum.inr (⟨i, (0 : I)⟩ : Σ _ : D.Idx, I), hb⟩
        = Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), (0 : I)) := ge_wOf_inr D i 0 hb
    rw [hwA, hwB]
    have h1 : vCl D (Sum.inl ⟨i, (0 : Fin (n + 2))⟩) = vCl D (Sum.inr ⟨i, (0 : Fin 2)⟩) := by
      apply vCl_eq_of_vertM_eq
      change Quotient.mk'' (Sum.inl (⟨i, stdSimplex.vertex (0 : Fin (n + 2))⟩ :
          Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
        = Quotient.mk'' (Sum.inr (⟨i, arcEnd (0 : Fin 2)⟩ : Σ _ : D.Idx, I))
      rw [arcEnd_zero]
      exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨i, rfl, rfl⟩)))
    have h2 : vCl D (Sum.inl ⟨i, (0 : Fin (n + 2))⟩) = a D (eCl D (Sum.inr ⟨i, PUnit.unit⟩)) := h1
    rw [rel_ae (a D) (b D) (eCl D (Sum.inr ⟨i, PUnit.unit⟩)), h2]
  · intro ha hb
    have hwA : wOf D ⟨Sum.inr (⟨i, (1 : I)⟩ : Σ _ : D.Idx, I), ha⟩
        = Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), (1 : I)) := ge_wOf_inr D i 1 ha
    have hwB : wOf D ⟨Sum.inr (⟨j, (1 : I)⟩ : Σ _ : D.Idx, I), hb⟩
        = Sum.inr (eCl D (Sum.inr ⟨j, PUnit.unit⟩), (1 : I)) := ge_wOf_inr D j 1 hb
    rw [hwA, hwB]
    have hv : b D (eCl D (Sum.inr ⟨i, PUnit.unit⟩)) = b D (eCl D (Sum.inr ⟨j, PUnit.unit⟩)) := by
      have h1 : b D (eCl D (Sum.inr ⟨i, PUnit.unit⟩)) = vCl D (Sum.inr ⟨i, (1 : Fin 2)⟩) := rfl
      have h2 : b D (eCl D (Sum.inr ⟨j, PUnit.unit⟩)) = vCl D (Sum.inr ⟨j, (1 : Fin 2)⟩) := rfl
      rw [h1, h2]
      apply vCl_eq_of_vertM_eq
      change Quotient.mk'' (Sum.inr (⟨i, arcEnd (1 : Fin 2)⟩ : Σ _ : D.Idx, I))
        = Quotient.mk'' (Sum.inr (⟨j, arcEnd (1 : Fin 2)⟩ : Σ _ : D.Idx, I))
      rw [arcEnd_one]
      exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨i, j, rfl, rfl⟩)))
    rw [rel_be (a D) (b D) (eCl D (Sum.inr ⟨i, PUnit.unit⟩)),
      rel_be (a D) (b D) (eCl D (Sum.inr ⟨j, PUnit.unit⟩)), hv]

theorem ge_wOf_const (D : MData X n x₀) (a₀ b₀ : Raw D)
    (h : Relation.EqvGen (modelRel D) a₀ b₀) :
    ∀ (ha : isLowDim D a₀) (hb : isLowDim D b₀),
      gq (a D) (b D) (wOf D ⟨a₀, ha⟩) = gq (a D) (b D) (wOf D ⟨b₀, hb⟩) := by
  induction h with
  | rel x y hxy => exact ge_wOf_rel D hxy
  | refl x =>
    intro ha hb
    exact congrArg (fun z => gq (a D) (b D) (wOf D z)) (Subtype.ext rfl)
  | symm x y hxy ih => intro ha hb; exact (ih hb ha).symm
  | trans x y z hxy hyz ih1 ih2 =>
    intro ha hc
    have hy : isLowDim D y := (ge_isLowDim_eqvGen hxy).mp ha
    exact (ih1 ha hy).trans (ih2 hy hc)

/-
See `Submission/Work/RatHurewicz/SkelGraph/` (`defs.lean`, `graphMap.lean`, `points.lean`): the
`1`-skeleton `Work.RatHurewicz.skeleton D` of the cycle model is the finite graph
`Work.RatHurewicz.GraphX (a D) (b D)`.  The map `f` below is `y ↦ gq (a D) (b D) (wOf D y)`.
-/
theorem graphElement {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) :
    ∃ f : {y : Work.RatHurewicz.Raw D // Work.RatHurewicz.isLowDim D y} →
        Work.RatHurewicz.GraphX (Work.RatHurewicz.SkelGraph.a D)
          (Work.RatHurewicz.SkelGraph.b D),
      (∀ y, Work.RatHurewicz.SkelGraph.Phi D (f y)
          = Work.RatHurewicz.SkelGraph.toSkeleton D y) ∧
      (∀ (y : {y : Work.RatHurewicz.Raw D // Work.RatHurewicz.isLowDim D y})
         (w : Work.RatHurewicz.SkelGraph.V D ⊕ (Work.RatHurewicz.SkelGraph.E D × unitInterval)),
          Work.RatHurewicz.SkelGraph.psi D w = Work.RatHurewicz.SkelGraph.toSkeleton D y →
          f y = Work.RatHurewicz.gq (Work.RatHurewicz.SkelGraph.a D)
            (Work.RatHurewicz.SkelGraph.b D) w) ∧
      (∀ y y', Relation.EqvGen (Work.RatHurewicz.modelRel D) y.1 y'.1 → f y = f y') := by
  refine ⟨fun y => gq (a D) (b D) (wOf D y), ?_, ?_, ?_⟩
  · intro y
    exact ge_Phi_wOf D y
  · intro y w hw
    change gq (a D) (b D) (wOf D y) = gq (a D) (b D) w
    have h1 : toSkeleton D (rawOf D w) = toSkeleton D y := by
      rw [← psi_rawOf D w]
      exact hw
    have h2 : Relation.EqvGen (modelRel D) (rawOf D w).1 y.1 := by
      have hq := congrArg Subtype.val h1
      exact Quotient.eq.mp hq
    have h3 : gq (a D) (b D) (wOf D (rawOf D w)) = gq (a D) (b D) (wOf D y) :=
      ge_wOf_const D (rawOf D w).1 y.1 h2 (rawOf D w).2 y.2
    exact h3.symm.trans (ge_gq_rawOf_wOf D w)
  · intro y y' h
    exact ge_wOf_const D y.1 y'.1 h y.2 y'.2

end

end Work.RatHurewicz.SkelGraph
