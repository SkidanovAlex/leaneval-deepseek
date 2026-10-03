import Mathlib
import Submission.Work.ORDunwoody.even_visits_defs

namespace Work.ORDunwoody

universe u

/-! ## Auxiliary list lemmas

`negSteps D a j` traverses the cells of the generator edge `(j,true)` in reverse order, i.e. it is
`(List.finRange L).reverse.map F` for the length `L = D.L (j,true)`.  The lemmas below compute the
head and the last element of that list (they are the images of the last, resp. the first, index of
`Fin L`) and show that it is a chain for the relation `tgt _ = src _` of two consecutive steps. -/

/-- The last index of `Fin L`, for `L ≠ 0`. -/
private def lastFinIdx (L : ℕ) (h : L ≠ 0) : Fin L :=
  ⟨L - 1, Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one⟩

/-- The first index of `Fin L`, for `L ≠ 0`. -/
private def firstFinIdx (L : ℕ) (h : L ≠ 0) : Fin L := ⟨0, Nat.pos_of_ne_zero h⟩

@[simp] private lemma lastFinIdx_val (L : ℕ) (h : L ≠ 0) : (lastFinIdx L h).val = L - 1 := rfl

@[simp] private lemma firstFinIdx_val (L : ℕ) (h : L ≠ 0) : (firstFinIdx L h).val = 0 := rfl

private lemma head?_finRange_reverse_map {α : Type*} {L : ℕ} (hL : L ≠ 0) (F : Fin L → α) :
    ((List.finRange L).reverse.map F).head? = some (F (lastFinIdx L hL)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
  rw [List.head?_map, List.head?_reverse, List.finRange_succ_last,
      List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton, Option.map_some]
  congr 1

private lemma getLast?_finRange_reverse_map {α : Type*} {L : ℕ} (hL : L ≠ 0) (F : Fin L → α) :
    ((List.finRange L).reverse.map F).getLast? = some (F (firstFinIdx L hL)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
  rw [List.getLast?_map, List.getLast?_reverse, List.finRange_succ, List.head?_cons,
      Option.map_some]
  congr 1

/-- A list enumerated in decreasing index order is a chain, provided the `k`-th element starts
where the `(k+1)`-st ends. -/
private theorem isChain_reverse_map {α X : Type*} (s t : α → X) (p : ℕ → X) :
    ∀ (n : ℕ) (G : Fin n → α),
      (∀ k, s (G k) = p (k.val + 1)) → (∀ k, t (G k) = p k.val) →
      List.IsChain (fun a b => t a = s b) ((List.finRange n).reverse.map G) := by
  intro n
  induction n with
  | zero => intro G _ _; rw [List.finRange_zero]; simp
  | succ m ih =>
      intro G hs ht
      have hdec : (List.finRange (m + 1)).reverse.map G =
          G (Fin.last m) :: (List.finRange m).reverse.map (fun k => G (Fin.castSucc k)) := by
        rw [List.finRange_succ_last, List.reverse_append, ← List.map_reverse,
          List.reverse_singleton, List.map_append, List.map_map]
        rfl
      rw [hdec, List.isChain_cons]
      refine ⟨?_, ih (fun k => G (Fin.castSucc k))
          (fun k => by rw [hs]; simp)
          (fun k => by rw [ht]; simp)⟩
      intro y hy
      rw [List.head?_map] at hy
      cases m with
      | zero => simp at hy
      | succ m' =>
          rw [List.head?_reverse, List.finRange_succ_last,
            List.getLast?_append_of_ne_nil _ (by simp)] at hy
          simp only [List.getLast?_singleton, Option.map_some, Option.mem_some_iff] at hy
          rw [← hy]
          rw [ht (Fin.last (m'+1)), hs (Fin.castSucc (Fin.last m'))]
          congr 1

/-- The source of a backwards step through the `k`-th cell is the position `k+1` of the
generator edge. -/
private lemma src_bwd_cell {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a' : G) (j : Fin P.n)
    (k : Fin (D.L (j, true))) :
    Work.ORDunwoody.Dunwoody.DStep.src (Work.ORDunwoody.Dunwoody.DStep.bwd
        (⟨a', j, k⟩ : Work.ORDunwoody.Dunwoody.Cell D)) =
      Work.ORDunwoody.Dunwoody.pos D a' j (k.val + 1) := rfl

/-- The target of a backwards step through the `k`-th cell is the position `k` of the generator
edge. -/
private lemma tgt_bwd_cell {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a' : G) (j : Fin P.n)
    (k : Fin (D.L (j, true))) :
    Work.ORDunwoody.Dunwoody.DStep.tgt (Work.ORDunwoody.Dunwoody.DStep.bwd
        (⟨a', j, k⟩ : Work.ORDunwoody.Dunwoody.Cell D)) =
      Work.ORDunwoody.Dunwoody.pos D a' j k.val := rfl

theorem negSteps_facts {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n) :
    (∀ s, (Work.ORDunwoody.Dunwoody.negSteps D a j).head? = some s →
        Work.ORDunwoody.Dunwoody.DStep.src s = (a, Sum.inl ())) ∧
    (∀ s, (Work.ORDunwoody.Dunwoody.negSteps D a j).getLast? = some s →
        Work.ORDunwoody.Dunwoody.DStep.tgt s =
          (a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹, Sum.inl ())) ∧
    (Work.ORDunwoody.Dunwoody.negSteps D a j).IsChain
      (fun s s' => Work.ORDunwoody.Dunwoody.DStep.tgt s =
        Work.ORDunwoody.Dunwoody.DStep.src s') ∧
    Work.ORDunwoody.Dunwoody.negSteps D a j ≠ [] := by
  by_cases h : D.L (j, true) = 0
  · -- a collapsed generator edge: `negSteps` is the single skipped step
    have hlist : Work.ORDunwoody.Dunwoody.negSteps D a j =
        [Work.ORDunwoody.Dunwoody.DStep.skip ((a, Sum.inl ()) : Work.ORDunwoody.Dunwoody.BaseV D)
          (((a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹), Sum.inl ()) :
            Work.ORDunwoody.Dunwoody.BaseV D)] := by
      rw [Work.ORDunwoody.Dunwoody.negSteps]
      simp only [h, dif_pos]
    rw [hlist]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.head?_singleton, Option.some.injEq] at hs
      rw [← hs]; rfl
    · intro s hs
      simp only [List.getLast?_singleton, Option.some.injEq] at hs
      rw [← hs]; rfl
    · exact List.isChain_singleton _
    · simp
  · -- a genuine generator edge: `negSteps` is the reversed list of backwards steps
    have hlist : Work.ORDunwoody.Dunwoody.negSteps D a j =
        (List.finRange (D.L (j, true))).reverse.map (fun k =>
          Work.ORDunwoody.Dunwoody.DStep.bwd
            (⟨a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹, j, k⟩ :
              Work.ORDunwoody.Dunwoody.Cell D)) := by
      rw [Work.ORDunwoody.Dunwoody.negSteps]
      simp only [h, dif_neg, not_false_eq_true]
    rw [hlist]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [head?_finRange_reverse_map (L := D.L (j, true)) h
        (fun k => Work.ORDunwoody.Dunwoody.DStep.bwd
          (⟨a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹, j, k⟩ :
            Work.ORDunwoody.Dunwoody.Cell D))] at hs
      simp only [Option.some.injEq] at hs
      rw [← hs, src_bwd_cell,
          Work.ORDunwoody.Dunwoody.pos_succ_of_not_lt D
            (a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹) j
            (i := (lastFinIdx (D.L (j, true)) h).val) (by rw [lastFinIdx_val]; omega)]
      simp [mul_assoc]
    · intro s hs
      rw [getLast?_finRange_reverse_map (L := D.L (j, true)) h
        (fun k => Work.ORDunwoody.Dunwoody.DStep.bwd
          (⟨a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹, j, k⟩ :
            Work.ORDunwoody.Dunwoody.Cell D))] at hs
      simp only [Option.some.injEq] at hs
      rw [← hs, tgt_bwd_cell]
      simp [firstFinIdx_val]
    · refine isChain_reverse_map Work.ORDunwoody.Dunwoody.DStep.src
        Work.ORDunwoody.Dunwoody.DStep.tgt
        (fun i => Work.ORDunwoody.Dunwoody.pos D
          (a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹) j i)
        (D.L (j, true))
        (fun k => Work.ORDunwoody.Dunwoody.DStep.bwd
          (⟨a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹, j, k⟩ :
            Work.ORDunwoody.Dunwoody.Cell D)) ?_ ?_
      · intro k; rw [src_bwd_cell]
      · intro k; rw [tgt_bwd_cell]
    · intro hnil
      have hg := getLast?_finRange_reverse_map (L := D.L (j, true)) h
        (fun k => Work.ORDunwoody.Dunwoody.DStep.bwd
          (⟨a * (Work.ORDunwoody.Cayley.CayV.genE P (j, true))⁻¹, j, k⟩ :
            Work.ORDunwoody.Dunwoody.Cell D))
      rw [hnil] at hg
      simp at hg

end Work.ORDunwoody
