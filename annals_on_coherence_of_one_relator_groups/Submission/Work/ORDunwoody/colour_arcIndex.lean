import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Piece
import Submission.Work.ORDunwoody.Dunwoody.Pattern
import Submission.Work.ORDunwoody.colour_walk_defs
import Submission.Work.ORDunwoody.colour_collapsed
import Submission.Work.ORDunwoody.faceWalk_getLast
import Submission.Work.ORDunwoody.faceWalk_chain
import Submission.Work.ORDunwoody.edgeTailPos_head_old
import Submission.Work.ORDunwoody.edgeTailNeg_head_old
import Submission.Work.ORDunwoody.edgeTailPos_chain_oldRel
import Submission.Work.ORDunwoody.edgeTailNeg_chain_oldRel

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

namespace Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The arc index of an old vertex -/

theorem arcIndexAux_cons_inl (u : BaseV D) (rest : List (Vertex D)) (k : ℕ) :
    arcIndexAux (Sum.inl u :: rest) k = (u, k) :: arcIndexAux rest k := rfl

theorem arcIndexAux_cons_inr (m : MidV D) (rest : List (Vertex D)) (k : ℕ) :
    arcIndexAux (Sum.inr m :: rest) k = arcIndexAux rest (k + 1) := rfl

/-- Every arc index occurring in `arcIndexAux l k` is at least `k`. -/
theorem arcIndexAux_snd_ge : ∀ (l : List (Vertex D)) (k : ℕ) (p : BaseV D × ℕ),
    p ∈ arcIndexAux l k → k ≤ p.2 := by
  intro l
  induction l with
  | nil => intro k p hp; simp at hp
  | cons w rest ih =>
      intro k p hp
      cases w with
      | inl u =>
          rw [arcIndexAux_cons_inl, List.mem_cons] at hp
          rcases hp with hp | hp
          · rw [hp]
          · exact le_trans (le_refl k) (ih k p hp)
      | inr m =>
          rw [arcIndexAux_cons_inr] at hp
          exact le_trans (Nat.le_succ k) (ih (k + 1) p hp)

/-- The entries of `arcIndexAux l k` whose second component is `k` are exactly the old vertices
of the initial run `initOlds l`. -/
theorem mem_arcIndexAux_self : ∀ (l : List (Vertex D)) (k : ℕ) (v : BaseV D),
    (v, k) ∈ arcIndexAux l k → v ∈ initOlds l := by
  intro l
  induction l with
  | nil => intro k v hv; simp at hv
  | cons w rest ih =>
      intro k v hv
      cases w with
      | inl u =>
          rw [arcIndexAux_cons_inl, List.mem_cons] at hv
          rcases hv with hv | hv
          · rw [Prod.mk.injEq] at hv
            rw [hv.1, initOlds_inl]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih k v hv)
      | inr m =>
          rw [arcIndexAux_cons_inr] at hv
          have hge := arcIndexAux_snd_ge rest (k + 1) (v, k) hv
          exact absurd hge (by omega)

/-! ## The initial run has a constant colour -/

/-- If the consecutive old vertices of `Sum.inl u :: rest` have equal colour, then `u` has the
same colour as every old vertex of the initial run of `rest`. -/
theorem head_firstRun_const : ∀ (rest : List (Vertex D)) (u : BaseV D),
    (Sum.inl u :: rest).IsChain (oldRel D) → ∀ v ∈ initOlds rest, colour D u = colour D v := by
  intro rest
  induction rest with
  | nil => intro u h v hv; simp at hv
  | cons w rest ih =>
      intro u h v hv
      cases w with
      | inr m => simp at hv
      | inl w₀ =>
          rw [List.isChain_cons_cons] at h
          obtain ⟨huw, hrest⟩ := h
          rw [initOlds_inl, List.mem_cons] at hv
          rcases hv with hv | hv
          · rw [hv]; exact oldRel_inl_inl.mp huw
          · exact (oldRel_inl_inl.mp huw).trans (ih w₀ hrest v hv)

/-- All the old vertices of the initial run of `l` have the same colour, provided the
consecutive old vertices of `l` have equal colour. -/
theorem firstRun_const : ∀ (l : List (Vertex D)), l.IsChain (oldRel D) →
    ∀ (u v : BaseV D), u ∈ initOlds l → v ∈ initOlds l → colour D u = colour D v := by
  intro l
  induction l with
  | nil => intro h u v hu hv; simp at hu
  | cons w rest ih =>
      intro h u v hu hv
      cases w with
      | inr m => simp at hu
      | inl u₀ =>
          rw [List.isChain_cons] at h
          obtain ⟨hhead, hrest⟩ := h
          have hchain : (Sum.inl u₀ :: rest).IsChain (oldRel D) := List.IsChain.cons hrest hhead
          rw [initOlds_inl, List.mem_cons] at hu hv
          rcases hu with hu | hu
          · rw [hu]
            rcases hv with hv | hv
            · rw [hv]
            · exact head_firstRun_const rest u₀ hchain v hv
          · rcases hv with hv | hv
            · rw [hv]
              exact (head_firstRun_const rest u₀ hchain u hu).symm
            · exact ih hrest u v hu hv

/-- Old vertices of a walk that are at the same arc index have the same colour, provided
consecutive old vertices of the walk have equal colour. -/
theorem isChain_arcIndexAux : ∀ (l : List (Vertex D)), l.IsChain (oldRel D) →
    ∀ (k i : ℕ) (u v : BaseV D), (u, i) ∈ arcIndexAux l k → (v, i) ∈ arcIndexAux l k →
      colour D u = colour D v := by
  intro l
  induction l with
  | nil => intro h k i u v hu hv; simp at hu
  | cons w rest ih =>
      intro h k i u v hu hv
      cases w with
      | inr m =>
          rw [List.isChain_cons] at h
          obtain ⟨-, hrest⟩ := h
          rw [arcIndexAux_cons_inr] at hu hv
          exact ih hrest (k + 1) i u v hu hv
      | inl u₀ =>
          rw [List.isChain_cons] at h
          obtain ⟨hhead, hrest⟩ := h
          have hchain : (Sum.inl u₀ :: rest).IsChain (oldRel D) := List.IsChain.cons hrest hhead
          rw [arcIndexAux_cons_inl, List.mem_cons] at hu hv
          rcases hu with hu | hu
          · injection hu with hu1 hu2
            rw [hu1]
            rw [hu2] at hv
            rcases hv with hv | hv
            · injection hv with hv1 _
              rw [hv1]
            · exact firstRun_const (Sum.inl u₀ :: rest) hchain u₀ v List.mem_cons_self
                (List.mem_cons_of_mem _ (mem_arcIndexAux_self rest k v hv))
          · rcases hv with hv | hv
            · injection hv with hv1 hv2
              rw [hv2] at hu
              rw [hv1]
              exact (firstRun_const (Sum.inl u₀ :: rest) hchain u₀ u List.mem_cons_self
                (List.mem_cons_of_mem _ (mem_arcIndexAux_self rest k u hu))).symm
            · exact ih hrest k i u v hu hv

/-! ## The boundary walk of a face is a chain for the colour relation -/

theorem edgeTailPos_ne_nil (a : G) (j : Fin P.n) : edgeTailPos D a j ≠ [] := by
  by_cases h : D.L (j, true) = 0
  · simp only [edgeTailPos, if_pos h]; simp
  · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
    rw [edgeTailPos, if_neg h]
    have hmem : (Sum.inr (⟨a, ⟨j, ⟨0, hpos⟩⟩⟩ : MidV D) : Vertex D) ∈
        (List.finRange (D.L (j, true))).flatMap
          (fun k => [Sum.inr (⟨a, ⟨j, k⟩⟩ : MidV D), Sum.inl (pos D a j (k + 1))]) := by
      rw [List.mem_flatMap]
      exact ⟨⟨0, hpos⟩, List.mem_finRange _, by simp⟩
    intro hnil
    rw [hnil] at hmem
    simp at hmem

theorem edgeTailNeg_ne_nil (a : G) (j : Fin P.n) : edgeTailNeg D a j ≠ [] := by
  by_cases h : D.L (j, true) = 0
  · simp only [edgeTailNeg, if_pos h]; simp
  · have hpos : 0 < D.L (j, true) := Nat.pos_of_ne_zero h
    rw [edgeTailNeg, if_neg h]
    have hmem : (Sum.inr (⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, ⟨0, hpos⟩⟩⟩ : MidV D) : Vertex D) ∈
        ((List.finRange (D.L (j, true))).reverse).flatMap
          (fun k => [Sum.inr (⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩ : MidV D),
            Sum.inl (pos D (a * (CayV.genE P (j, true))⁻¹) j k)]) := by
      rw [List.mem_flatMap]
      exact ⟨⟨0, hpos⟩, List.mem_reverse.mpr (List.mem_finRange _), by simp⟩
    intro hnil
    rw [hnil] at hmem
    simp at hmem

/-- If the tail of the boundary walk of `w` read at `a` starts with an old vertex `b`, then
`colour a = colour b`. -/
theorem faceAux_head_old : ∀ (a : G) (w : List (Fin P.n × Bool)) (b : BaseV D),
    (faceAux D a w).head? = some (Sum.inl b : Vertex D) →
      colour D (a, (Sum.inl () : BaseV₀ D)) = colour D b := by
  intro a w
  induction w generalizing a with
  | nil => intro b h; simp [faceAux] at h
  | cons x w ih =>
      intro b h
      obtain ⟨j, s⟩ := x
      cases s with
      | true =>
          rw [faceAux_true] at h
          rw [List.head?_append_of_ne_nil (edgeTailPos D a j) (edgeTailPos_ne_nil a j)] at h
          exact edgeTailPos_head_old a j b h
      | false =>
          rw [faceAux_false] at h
          rw [List.head?_append_of_ne_nil (edgeTailNeg D a j) (edgeTailNeg_ne_nil a j)] at h
          exact edgeTailNeg_head_old a j b h

/-- The boundary walk of a face, starting at `a`, is a chain for the colour relation. -/
theorem isChain_faceAux : ∀ (a : G) (w : List (Fin P.n × Bool)),
    (Sum.inl (a, (Sum.inl () : BaseV₀ D)) :: faceAux D a w : List (Vertex D)).IsChain
      (oldRel D) := by
  intro a w
  induction w generalizing a with
  | nil => exact List.isChain_singleton _
  | cons x w ih =>
      obtain ⟨j, s⟩ := x
      cases s with
      | true =>
          rw [faceAux_true, ← List.cons_append]
          refine List.IsChain.append (List.IsChain.cons (edgeTailPos_chain_oldRel a j) ?_)
            (List.IsChain.tail (ih (a * CayV.genE P (j, true)))) ?_
          · intro y hy b c h1 h2
            rw [← Sum.inl.inj h1]
            exact edgeTailPos_head_old a j c (by rw [← h2]; exact hy)
          · intro y hy z hz b c h1 h2
            have hy' : y = (Sum.inl (a * CayV.genE P (j, true),
                (Sum.inl () : BaseV₀ D)) : Vertex D) := by
              rw [List.getLast?_cons_of_ne_nil (edgeTailPos_ne_nil a j),
                edgeTailPos_getLast] at hy
              exact (Option.mem_some_iff.mp hy).symm
            have hb : b = (a * CayV.genE P (j, true), (Sum.inl () : BaseV₀ D)) := by
              rw [hy'] at h1
              exact (Sum.inl.inj h1).symm
            rw [hb]
            exact faceAux_head_old (a * CayV.genE P (j, true)) w c (by rw [← h2]; exact hz)
      | false =>
          rw [faceAux_false, ← List.cons_append]
          refine List.IsChain.append (List.IsChain.cons (edgeTailNeg_chain_oldRel a j) ?_)
            (List.IsChain.tail (ih (a * (CayV.genE P (j, true))⁻¹))) ?_
          · intro y hy b c h1 h2
            rw [← Sum.inl.inj h1]
            exact edgeTailNeg_head_old a j c (by rw [← h2]; exact hy)
          · intro y hy z hz b c h1 h2
            have hy' : y = (Sum.inl (a * (CayV.genE P (j, true))⁻¹,
                (Sum.inl () : BaseV₀ D)) : Vertex D) := by
              rw [List.getLast?_cons_of_ne_nil (edgeTailNeg_ne_nil a j),
                edgeTailNeg_getLast] at hy
              exact (Option.mem_some_iff.mp hy).symm
            have hb : b = (a * (CayV.genE P (j, true))⁻¹, (Sum.inl () : BaseV₀ D)) := by
              rw [hy'] at h1
              exact (Sum.inl.inj h1).symm
            rw [hb]
            exact faceAux_head_old (a * (CayV.genE P (j, true))⁻¹) w c (by rw [← h2]; exact hz)

end Dunwoody

/-- **The colour is constant on the arc of a visit.** Two old vertices of the boundary walk of a
face that occur with the same arc index have the same colour. -/
theorem colour_arcIndex {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool))
    {i : ℕ} {u v : Work.ORDunwoody.Dunwoody.BaseV D}
    (hu : (u, i) ∈ Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w))
    (hv : (v, i) ∈ Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w)) :
    Work.ORDunwoody.Dunwoody.colour D u = Work.ORDunwoody.Dunwoody.colour D v := by
  have hchain : (Work.ORDunwoody.Dunwoody.faceWalk D c w).IsChain
      (Work.ORDunwoody.Dunwoody.oldRel D) := by
    rw [Work.ORDunwoody.Dunwoody.faceWalk_eq]
    exact Work.ORDunwoody.Dunwoody.isChain_faceAux c w
  exact Work.ORDunwoody.Dunwoody.isChain_arcIndexAux (Work.ORDunwoody.Dunwoody.faceWalk D c w)
    hchain 0 i u v hu hv

end Work.ORDunwoody
