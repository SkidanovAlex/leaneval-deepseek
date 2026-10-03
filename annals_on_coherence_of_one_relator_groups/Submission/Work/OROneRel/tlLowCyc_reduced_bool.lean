import Mathlib
import Submission.Work.OROneRel.tlLowCycStep

/-!
# A reduced word of the low window is monochromatic in the sign

The low window `[0, p+q-1]` of the two-letter band with weight `tlW p q` (`a = 0 ↦ q`,
`b = 1 ↦ -p`) is a cycle: every level carries exactly one outgoing `a`- or `b`-edge.  The
statement proved here is that a *reduced* word `L` all of whose decorated edges lie in the window
cannot switch the sign of its letters: either all its letters are positive or all are negative.

The proof is the argument of `Submission/Work/OROneRel/halfPlane_sameBool.lean`, generalised from
`tlW 2 3` and the strip `[0,4]` to `tlW p q` and the window `[0, p+q-1]`:

* the running levels of the walk of `L` are the entries of `running (tlW p q) v L`, and the
  hypothesis `hwin` (the decorated edges lie in the window) says exactly that all of them lie in
  `[0, p+q-1]` (`tlrc_running_in_window`);
* two consecutive letters `X`, `Y` of a reduced word with opposite signs satisfy `X.1 = Y.1`
  (otherwise they cancel, contradicting reducedness — `X.1 ≠ Y.1` would force
  `letterW X + letterW Y = ±(p+q)`), so their weights sum to `±(p+q)`
  (`tlrc_letterW_tlW_pair`).  A level of the window shifted by `±(p+q)` leaves the window
  (`tlrc_step_out`), so the sign never switches (`tlrc_mono_running`).
-/

namespace Work.OROneRel

/-! ## The endpoints of a window edge are in the window -/

/-- If the (undirected) edge of a decorated letter lies in the window, then the *source* level of
the decorated letter lies in the window. -/
theorem tlrc_coverSrc_mem_winE {α : Type*} {c : α → ℤ} {lo hi : ℤ} {e : (α × ℤ) × Bool}
    (h : coverEdge e ∈ winE c lo hi) : lo ≤ coverSrc c e ∧ coverSrc c e ≤ hi := by
  obtain ⟨⟨a, i⟩, b⟩ := e
  rw [mem_winE] at h
  cases b <;> simp only [coverSrc, Bool.false_eq_true, if_false, if_true] <;>
    [exact ⟨h.2.2.1, h.2.2.2⟩; exact ⟨h.1, h.2.1⟩]

/-- If the (undirected) edge of a decorated letter lies in the window, then the *target* level of
the decorated letter lies in the window. -/
theorem tlrc_coverTgt_mem_winE {α : Type*} {c : α → ℤ} {lo hi : ℤ} {e : (α × ℤ) × Bool}
    (h : coverEdge e ∈ winE c lo hi) : lo ≤ coverTgt c e ∧ coverTgt c e ≤ hi := by
  obtain ⟨⟨a, i⟩, b⟩ := e
  rw [mem_winE] at h
  cases b <;> simp only [coverTgt, Bool.false_eq_true, if_false, if_true] <;>
    [exact ⟨h.1, h.2.1⟩; exact ⟨h.2.2.1, h.2.2.2⟩]

/-- The level increment `linc` of a letter is its `letterW`. -/
theorem tlrc_linc_eq_letterW {α : Type*} (c : α → ℤ) (p : α × Bool) :
    linc c p = letterW c p := rfl

/-! ## The weight of a pair of letters with opposite signs -/

/-- Two consecutive letters with distinct generators and opposite signs weigh `±(p+q)` in total:
one of them is `a` and the other `b`, and the sign of each is forced by the sign difference, so the
sum is `q + p` or `-q - p`. -/
theorem tlrc_letterW_tlW_pair (p q : ℕ) (X Y : Fin 2 × Bool)
    (hx : X.1 ≠ Y.1) (hb : X.2 ≠ Y.2) :
    letterW (tlW p q) X + letterW (tlW p q) Y = (p : ℤ) + (q : ℤ) ∨
    letterW (tlW p q) X + letterW (tlW p q) Y = -((p : ℤ) + (q : ℤ)) := by
  obtain ⟨a, ba⟩ := X
  obtain ⟨a', b'⟩ := Y
  fin_cases a <;> fin_cases a' <;> cases ba <;> cases b' <;>
    simp_all [letterW, tlW, add_comm]

/-- A shift by `±(p+q)` from a level of the window `[0, p+q-1]` leaves the window. -/
theorem tlrc_step_out (p q : ℕ) (u : ℤ) (X Y : Fin 2 × Bool)
    (hx : X.1 ≠ Y.1) (hb : X.2 ≠ Y.2)
    (hu : 0 ≤ u ∧ u ≤ (p : ℤ) + (q : ℤ) - 1) :
    ¬ (0 ≤ u + letterW (tlW p q) X + letterW (tlW p q) Y ∧
        u + letterW (tlW p q) X + letterW (tlW p q) Y ≤ (p : ℤ) + (q : ℤ) - 1) := by
  rintro ⟨h1, h2⟩
  rcases tlrc_letterW_tlW_pair p q X Y hx hb with h | h <;> omega

/-! ## The running levels of a walk -/

/-- Reading a letter at a level updates the level by the weight of that letter. -/
theorem tlrc_running_cons (c : Fin 2 → ℤ) (v : ℤ) (X : Fin 2 × Bool)
    (rest : List (Fin 2 × Bool)) :
    running c v (X :: rest) = v :: running c (v + letterW c X) rest := by
  obtain ⟨a, b⟩ := X
  cases b
  · simp only [running, letterW, Bool.false_eq_true, if_false]
    rw [sub_eq_add_neg]
  · simp [running, letterW]

/-- The starting level is one of the levels of the walk. -/
theorem tlrc_running_head (c : Fin 2 → ℤ) (v : ℤ) (L : List (Fin 2 × Bool)) :
    v ∈ running c v L := by
  cases L with
  | nil => simp [running]
  | cons p L => obtain ⟨a, b⟩ := p; cases b <;> simp [running]

/-! ## The window interior of a decorated word -/

/-- If the decorated edges of `L` read from a level `v` all lie in the window, and `v` is itself in
the window, then every running level of the walk is in the window. -/
theorem tlrc_running_in_window (p q : ℕ) (v : ℤ) (L : List (Fin 2 × Bool))
    (hv : 0 ≤ v ∧ v ≤ (p : ℤ) + (q : ℤ) - 1)
    (hwin : ∀ e ∈ decor (tlW p q) v L, coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1)) :
    ∀ x ∈ running (tlW p q) v L, 0 ≤ x ∧ x ≤ (p : ℤ) + (q : ℤ) - 1 := by
  induction L generalizing v with
  | nil => intro x hx; simp [running] at hx; subst hx; exact hv
  | cons X rest ih =>
    intro x hx
    rw [tlrc_running_cons] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · have heX_mem : ((X.1, if X.2 then v else v - tlW p q X.1), X.2) ∈
          decor (tlW p q) v (X :: rest) := by
        rw [decor_cons_l]; exact List.mem_cons_self
      have hT := tlrc_coverTgt_mem_winE (c := tlW p q) (hwin _ heX_mem)
      have ht : coverTgt (tlW p q) ((X.1, if X.2 then v else v - tlW p q X.1), X.2)
          = v + linc (tlW p q) X := coverTgt_head_l (tlW p q) v X
      have hv' : 0 ≤ v + letterW (tlW p q) X ∧
          v + letterW (tlW p q) X ≤ (p : ℤ) + (q : ℤ) - 1 := by
        rw [← tlrc_linc_eq_letterW (tlW p q) X, ← ht]; exact hT
      have hwin' : ∀ e ∈ decor (tlW p q) (v + letterW (tlW p q) X) rest,
          coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) := by
        intro e he
        apply hwin
        rw [decor_cons_l]
        exact List.mem_cons_of_mem _ he
      exact ih (v + letterW (tlW p q) X) hv' hwin' x hx

/-! ## Monochromaticity of a reduced window word -/

/-- A reduced word whose whole walk stays in the window `[0, p+q-1]` is monochromatic in the
sign of its letters. -/
theorem tlrc_mono_running (p q : ℕ) (v : ℤ) (L : List (Fin 2 × Bool))
    (hred : FreeGroup.IsReduced L)
    (hrun : ∀ x ∈ running (tlW p q) v L, 0 ≤ x ∧ x ≤ (p : ℤ) + (q : ℤ) - 1) :
    ∃ b : Bool, ∀ a ∈ L, a.2 = b := by
  induction L generalizing v with
  | nil => exact ⟨true, by simp⟩
  | cons X rest ih =>
    rcases rest with _ | ⟨Y, rest''⟩
    · refine ⟨X.2, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | h
      · rfl
      · exact absurd h (List.not_mem_nil)
    · obtain ⟨hXYred, hred'⟩ := FreeGroup.isReduced_cons_cons.mp hred
      have hstep1 : running (tlW p q) v (X :: Y :: rest'')
          = v :: running (tlW p q) (v + letterW (tlW p q) X) (Y :: rest'') :=
        tlrc_running_cons _ _ _ _
      have hstep2 : running (tlW p q) (v + letterW (tlW p q) X) (Y :: rest'')
          = (v + letterW (tlW p q) X) ::
              running (tlW p q) (v + letterW (tlW p q) X + letterW (tlW p q) Y) rest'' :=
        tlrc_running_cons _ _ _ _
      have hrun' : ∀ x ∈ running (tlW p q) (v + letterW (tlW p q) X) (Y :: rest''),
          0 ≤ x ∧ x ≤ (p : ℤ) + (q : ℤ) - 1 := by
        intro x hx
        exact hrun x (by rw [hstep1]; exact List.mem_cons_of_mem _ hx)
      obtain ⟨b', hb'⟩ := ih (v + letterW (tlW p q) X) hred' hrun'
      have hY : Y.2 = b' := hb' Y (by simp)
      have hXY : X.2 = Y.2 := by
        by_contra hne
        have hx1 : X.1 ≠ Y.1 := fun h => hne (hXYred h)
        have hu : 0 ≤ v ∧ v ≤ (p : ℤ) + (q : ℤ) - 1 := hrun v (by rw [hstep1]; simp)
        have hu2 : 0 ≤ v + letterW (tlW p q) X + letterW (tlW p q) Y ∧
            v + letterW (tlW p q) X + letterW (tlW p q) Y ≤ (p : ℤ) + (q : ℤ) - 1 :=
          hrun _ (by
            rw [hstep1, hstep2]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (tlrc_running_head _ _ _)))
        exact tlrc_step_out p q v X Y hx1 hne hu hu2
      refine ⟨b', ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hXY, hY]
      · exact hb' a ha

/-! ## The requested statement -/

theorem tlLowCyc_reduced_bool (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ)
    (L : List (Fin 2 × Bool))
    (hred : FreeGroup.IsReduced L)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) (Work.OROneRel.cycLevel p q k) L,
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) + (q : ℤ) - 1)) :
    (∀ l ∈ L, l.2 = true) ∨ (∀ l ∈ L, l.2 = false) := by
  have hb := cycLevel_bounds p q hp k
  have hb' : cycLevel p q k ≤ (p : ℤ) + (q : ℤ) - 1 := by
    have h := hb.2
    simp only [tlN] at h
    linarith
  have hrun := tlrc_running_in_window p q (cycLevel p q k) L ⟨hb.1, hb'⟩ hwin
  obtain ⟨b, hb0⟩ := tlrc_mono_running p q (cycLevel p q k) L hred hrun
  cases b
  · right; intro l hl; exact hb0 l hl
  · left; intro l hl; exact hb0 l hl

end Work.OROneRel
