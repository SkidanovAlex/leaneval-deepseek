import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.SortSpecs
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.drainValsEv
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.mrgPushSize
import Submission.Work.Layout.mrgUpdSize
import Submission.Work.Layout.merge_readFlag
import Submission.Work.Layout.merge_cleanStack
import Submission.Work.Layout.merge_updSizeSkip
import Submission.Work.Layout.merge_cmpCost
import Submission.Work.Layout.merge_drainQ
import Submission.Work.Layout.merge_drainP
import Submission.Work.Layout.merge_mrgCost_le
import Submission.Work.Layout.mrgMergeStep

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# `Work.Layout.mergePair_ev`: the crux of the `sortByKey` development

`mergePair pLt pSize SX SY T D SA SB F1 F2 t d` merges the two top runs `P` of `SX` and `Q` of `SY`
onto `D` as the `gMark`-terminated run `merge2 P Q`, comparing the cached key sizes on `SA`/`SB`
(and the keys themselves only when the sizes agree), in cost linear in the total size of the two runs.
-/

namespace Work.Layout

open HvdH Work.Layout.Sk

/-! ## helper lemmas for the loop and the final assembly -/

/-- **membership in `merge2`** -/
theorem merge2_mem : ∀ P Q : List Val, ∀ v ∈ merge2 P Q, v ∈ P ++ Q := by
  intro P
  induction P with
  | nil =>
      intro Q v hv
      rw [merge2_nil_left] at hv
      simpa using hv
  | cons p ps ihp =>
      intro Q
      induction Q with
      | nil =>
          intro v hv
          rw [merge2_nil_right] at hv
          simpa using hv
      | cons q qs ihq =>
          intro v hv
          by_cases h : pairKey q < pairKey p
          · rw [merge2_cons_of_lt h] at hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact List.mem_append.mpr (Or.inr (by simp))
            · rcases List.mem_append.mp (ihq v hv') with h1 | h1
              · exact List.mem_append.mpr (Or.inl h1)
              · exact List.mem_append.mpr (Or.inr (by simp [h1]))
          · rw [merge2_cons_of_ge h] at hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact List.mem_append.mpr (Or.inl (by simp))
            · rcases List.mem_append.mp (ihp (q :: qs) v hv') with h1 | h1
              · exact List.mem_append.mpr (Or.inl (by simp [h1]))
              · exact List.mem_append.mpr (Or.inr h1)

/-- **the cache move identity**: moving the front `v` of a run `v :: vs` to the "done" part `L`
together with the update of the cached key size of the newly exposed front. -/
theorem mrg_cache_move (L : List Val) (v : Val) (vs : List Val) (B : List Glyph) :
    (if vs = [] then encs (cache L (v :: vs)) ++ B
     else (Val.int ((keyOf (vs.headD Val.nil)).size : ℤ)).enc ++
          (encs (cache L (v :: vs)) ++ B))
      = encs (cache (L ++ [v]) vs) ++ B := by
  cases vs with
  | nil =>
      rw [ite_eq_left rfl, cache_append_nil]
  | cons w ws =>
      rw [ite_eq_right (by simp), cache_cons, cache_cons, List.headD_cons]
      simp only [encs, List.map_cons, List.map_nil, List.map_append, List.flatten_cons,
        List.flatten_nil, List.flatten_append, List.reverse_cons, List.reverse_nil,
        List.reverse_append, List.reverse_singleton, List.nil_append, List.singleton_append,
        List.append_assoc, ksv, keyOf]

/-- **peeling a frame**: a frame off `{a,b,c,e,f}` together with explicit equalities on `c,e,f`
gives a frame off `{a,b}`. -/
theorem frame_peel3 {X Y : Stk → List Glyph} {a b c e f : Stk}
    (h : ∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ e → k ≠ f → Y k = X k)
    (hc : Y c = X c) (he : Y e = X e) (hf : Y f = X f) :
    ∀ k, k ≠ a → k ≠ b → Y k = X k := by
  intro k ha hb
  by_cases h1 : k = c
  · subst h1; exact hc
  by_cases h2 : k = e
  · subst h2; exact he
  by_cases h3 : k = f
  · subst h3; exact hf
  exact h k ha hb h1 h2 h3

/-- **peeling a frame** off `{a,b,c,e}` with equalities on `c,e` gives a frame off `{a,b}`. -/
theorem frame_peel4 {X Y : Stk → List Glyph} {a b c e : Stk}
    (h : ∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ e → Y k = X k)
    (hc : Y c = X c) (he : Y e = X e) : ∀ k, k ≠ a → k ≠ b → Y k = X k := by
  intro k ha hb
  by_cases h1 : k = c
  · subst h1; exact hc
  by_cases h2 : k = e
  · subst h2; exact he
  exact h k ha hb h1 h2

theorem ne_of_notMem {a y : Stk} {l : List Stk} (h : a ∉ l) (hy : y ∈ l) : a ≠ y :=
  fun hay => h (hay ▸ hy)

theorem mem_cons_insert_mid {α : Type} {x a : α} {l₁ l₂ : List α} (h : x ∈ l₁ ++ l₂) :
    x ∈ l₁ ++ (a :: l₂) := by
  rw [List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by simp [h])

/-- the individual `∉`-facts carried by the pairwise distinctness of the eleven stacks -/
theorem hdis11_peel {SX SY T D SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, D, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    (SX ∉ ([SY, T, D, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SY ∉ ([T, D, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (T ∉ ([D, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (D ∉ ([SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SA ∉ ([SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SB ∉ ([F1, F2, t, d, 0] : List Stk)) ∧
    (F1 ∉ ([F2, t, d, 0] : List Stk)) ∧
    (F2 ∉ ([t, d, 0] : List Stk)) ∧
    (t ∉ ([d, 0] : List Stk)) ∧
    (d ∉ ([0] : List Stk)) := by
  rw [List.nodup_cons] at hdis; obtain ⟨h1, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h2, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h3, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h4, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h5, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h6, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h7, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h8, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h9, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h10, -⟩ := hdis
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- the ten-element pairwise distinctness is a consequence of the eleven-element one -/
theorem hdis10_of_hdis11 {SX SY T D SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, D, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hdis11_peel hdis
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hx; exact h1 (mem_cons_insert_mid (l₁ := [SY, T]) (a := D) hx)
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hx; exact h2 (mem_cons_insert_mid (l₁ := [T]) (a := D) hx)
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hx; exact h3 (mem_cons_insert_mid (l₁ := ([] : List Stk)) (a := D) hx)
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · exact h5
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · exact h6
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · exact h7
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · exact h8
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · exact h9
  rw [List.nodup_cons]
  exact ⟨h10, by simp⟩

/-- transferring distinctness of `pairKey` to distinctness of `keyOf` -/
theorem mrg_keyOf_nodup {P Q : List Val}
    (hrec : ∀ v ∈ P ++ Q, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v')
    (h : ((P ++ Q).map pairKey).Nodup) : ((P ++ Q).map keyOf).Nodup := by
  have hkey : (P ++ Q).map keyOf = ((P ++ Q).map pairKey).map Int.toNat := by
    rw [List.map_map]
    rfl
  rw [hkey]
  refine h.map_on ?_
  intro x hx y hy hxy
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
  obtain ⟨kv, vv, rfl⟩ := hrec v hv
  obtain ⟨kw, ww, rfl⟩ := hrec w hw
  rw [pairKey_record, pairKey_record] at hxy ⊢
  simp only [Int.toNat_natCast] at hxy
  exact_mod_cast hxy

/-- the cost of `pushSize` for a record is covered by the `cExp` term of `mrgStep` -/
theorem pushSizeCost_le_cExp' (KSz k : ℕ) (v' : Val) :
    40 * (isz (k : ℤ) + 1) + KSz * isz (k : ℤ) + 16 * (isz (k.size : ℤ) + 1) + 8
      ≤ cExp KSz * (vsz (Val.cons (Val.int (k : ℤ)) v') + 2) := by
  rw [cExp, vsz_record, isz_natCast, isz_ksv]
  have h1 := size_le_self k.size
  have h2 := one_le_vsz v'
  nlinarith

theorem le_sum_map_of_mem : ∀ (l : List Val) (v : Val), v ∈ l → vsz v ≤ (l.map vsz).sum := by
  intro l
  induction l with
  | nil => intro v h; exact absurd h (by simp)
  | cons a t ih =>
      intro v h
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have h' := ih v h
        simp only [List.map_cons, List.sum_cons]
        omega

theorem sum_append_right_le (l₁ l₂ : List Val) : (l₂.map vsz).sum ≤ ((l₁ ++ l₂).map vsz).sum := by
  rw [List.map_append, List.sum_append]
  omega

/-- the sharp size bound on a cache: every cached key size is smaller than its record -/
theorem cache_sum_le (P₁ P₂ : List Val)
    (hrec : ∀ v ∈ P₁ ++ P₂, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') :
    ((cache P₁ P₂).map vsz).sum ≤ ((P₁ ++ P₂).map vsz).sum := by
  simp only [cache_take1, List.map_append, List.sum_append]
  have hA : ((((P₂.take 1).map ksv).reverse).map vsz).sum ≤ (P₂.map vsz).sum := by
    rw [List.map_reverse, List.sum_reverse, List.map_map]
    refine (sum_map_le_of_pointwise (fun v hv => ?_)).trans (sum_take_one_le P₂ vsz)
    obtain ⟨k, v', rfl⟩ := hrec v (List.mem_append_right _ (List.mem_of_mem_take hv))
    exact vsz_ksv_le_record k v'
  have hB : (((P₁.map ksv).reverse).map vsz).sum ≤ (P₁.map vsz).sum := by
    rw [List.map_reverse, List.sum_reverse, List.map_map]
    exact sum_map_le_of_pointwise (fun v hv => by
      obtain ⟨k, v', rfl⟩ := hrec v (List.mem_append_left _ hv)
      exact vsz_ksv_le_record k v')
  omega

theorem sum_append_left_le (l₁ l₂ : List Val) : (l₁.map vsz).sum ≤ ((l₁ ++ l₂).map vsz).sum := by
  rw [List.map_append, List.sum_append]
  omega

theorem length_append_left_le (l₁ l₂ : List Val) : l₁.length ≤ (l₁ ++ l₂).length := by
  rw [List.length_append]
  omega

theorem length_append_right_le (l₁ l₂ : List Val) : l₂.length ≤ (l₁ ++ l₂).length := by
  rw [List.length_append]
  omega

/-- the peel facts for the ten-element list `[SX,SY,T,SA,SB,F1,F2,t,d,0]` (without `D`) -/
theorem hdis10_peel {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    (SX ∉ ([SY, T, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SY ∉ ([T, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (T ∉ ([SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SA ∉ ([SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SB ∉ ([F1, F2, t, d, 0] : List Stk)) ∧
    (F1 ∉ ([F2, t, d, 0] : List Stk)) ∧
    (F2 ∉ ([t, d, 0] : List Stk)) ∧
    (t ∉ ([d, 0] : List Stk)) ∧
    (d ∉ ([0] : List Stk)) := by
  rw [List.nodup_cons] at hdis; obtain ⟨h1, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h2, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h3, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h4, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h5, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h6, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h7, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h8, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h9, -⟩ := hdis
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-! ## decomposition of a record's encoding -/

theorem encs_front_record (k : ℕ) (v' : Val) (ps : List Val) (A : List Glyph) :
    encs (Val.cons (Val.int (k : ℤ)) v' :: ps) ++ A =
      Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ A))) := by
  simp only [encs, List.map_cons, List.flatten_cons, Val.enc, List.cons_append,
    List.append_assoc]

theorem headD_encs_ps (ps : List Val) (A : List Glyph)
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'') :
    (encs ps ++ gMark :: A).headD Glyph.eos = (if ps = [] then gMark else Glyph.cons) := by
  cases ps with
  | nil => rw [headD_encs_nil]; rfl
  | cons v vs =>
      obtain ⟨k', v'', rfl⟩ := hps v (by simp)
      rw [mrgHeadD_encs_cons]
      simp [Val.enc]

theorem merge_loopRuns_eval_pre {main : Cmd} {rf : Reg} {c : Glyph} {body : Cmd} :
    ∀ {k : ℕ} {s s' s'' : State} {C₁ C₂ : ℕ}, loopRuns main rf c body k s s' C₁ →
      Ev main (.loop rf c body) s' s'' C₂ → Ev main (.loop rf c body) s s'' (C₁ + C₂ + 1) := by
  intro k
  induction k with
  | zero =>
      intro s s' s'' C₁ C₂ h h₂
      obtain ⟨hs, hC⟩ := h
      subst hs; subst hC
      exact h₂.mono (by omega)
  | succ k ih =>
      intro s s' s'' C₁ C₂ h h₂
      obtain ⟨hrf, s₁, D₁, D₂, hb, hr, hle⟩ := h
      have h' := Ev.loopT hrf hb (ih hr h₂)
      exact h'.mono (by omega)

/-! ## one comparison step of the loop, `keyOf q < keyOf p` (the front of `SY` moves) -/

theorem mBody_pairL {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True)
      (fun a => (a.natAbs.size : ℤ)) (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph}
    {p q : Val} {ps qs : List Val} {k l : ℕ} {v' w' : Val}
    {A B' Tc R Sc Sc' : List Glyph} {Tk : List Val} {S : Stk → List Glyph}
    (hp : p = Val.cons (Val.int (k : ℤ)) v') (hq : q = Val.cons (Val.int (l : ℤ)) w')
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hlt : l < k)
    (hSX : X SX = encs (p :: ps) ++ gMark :: A)
    (hSY : X SY = encs (q :: qs) ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = encs Tk ++ gMark :: Tc)
    (h0 : X 0 = R)
    (hF1 : X F1 = S F1) (hF2 : X F2 = S F2) (ht : X t = S t) (hd : X d = S d)
    (hfr : ∀ k', k' ∉ loopTouched SX SY T SA SB → X k' = S k') :
    ∃ s' n, Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStep KLt KSz p ps q qs ∧
      s'.reg Sk.rF = Glyph.cons ∧ s'.stk 0 = R ∧ s'.stk SX = X SX ∧
      s'.stk SY = encs qs ++ gMark :: B' ∧ s'.stk SA = X SA ∧
      s'.stk SB = (if qs = [] then X SB
                   else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ X SB) ∧
      s'.stk T = q.enc ++ encs Tk ++ gMark :: Tc ∧
      (∀ k', k' ∉ loopTouched SX SY T SA SB → s'.stk k' = S k') := by
  have hSXm : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A := by
    rw [hSX, hp]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hSYm : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B' := by
    rw [hSY, hq]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hSXd : X SX = Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A))) := by
    rw [hSXm]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  have hSYd : X SY = Glyph.cons :: ((Val.int (l : ℤ)).enc ++ (w'.enc ++ (encs qs ++ gMark :: B'))) := by
    rw [hSYm]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  have hkey : keyOf p = k := by rw [hp, keyOf_record]
  have hkeyq : keyOf q = l := by rw [hq, keyOf_record]
  have h1 : (X SX).headD Glyph.eos = Glyph.cons := by rw [hSXd]; rfl
  have h2 : (X SY).headD Glyph.eos = Glyph.cons := by rw [hSYd]; rfl
  have e1 : Ev main (.peek SX rH) ⟨g, X⟩ ⟨Function.update g rH Glyph.cons, X⟩ 1 := by
    have hp' := ev_peek' main SX rH g X
    rw [h1] at hp'
    exact hp'
  have e2 : Ev main (.peek SY rI) ⟨Function.update g rH Glyph.cons, X⟩
      ⟨Function.update (Function.update g rH Glyph.cons) rI Glyph.cons, X⟩ 1 := by
    have hp' := ev_peek' main SY rI (Function.update g rH Glyph.cons) X
    rw [h2] at hp'
    exact hp'
  obtain ⟨s3, M, e3, hM, h03, hT3, hSX3, hSY3, hSA3, hSB3, hF13, hF23, ht3, hd3, hfr3⟩ :=
    mrgMergeStep (main := main) (pLt := pLt) (pSize := pSize) hLt hSz hdis hps hqs
      (SX := SX) (SY := SY) (SA := SA) (SB := SB) (T := T) (F1 := F1) (F2 := F2) (t := t) (d := d)
      (g := Function.update (Function.update g rH Glyph.cons) rI Glyph.cons) (X := X)
      (k := k) (l := l) (v' := v') (w' := w') (ps := ps) (qs := qs) (A := A) (B' := B')
      (Tc := encs Tk ++ gMark :: Tc) (R := R) (Sc := Sc) (Sc' := Sc') hSXm hSYm hSA hSB hT h0
  rw [ite_eq_left hlt] at hT3 hSX3 hSY3 hSA3 hSB3
  have hSX3' : s3.stk SX = X SX := by rw [hSX3, hSXm]
  have hT3' : s3.stk T = q.enc ++ encs Tk ++ gMark :: Tc := by
    rw [← hq] at hT3
    rw [hT3, List.append_assoc]
  have hSB3' : s3.stk SB = (if qs = [] then X SB
      else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ X SB) := by
    rw [hSB3]
    by_cases hqs' : qs = []
    · rw [ite_eq_left hqs', ite_eq_left hqs']
    · rw [ite_eq_right hqs', ite_eq_right hqs', List.append_assoc]
      rw [← hSB]
  have h4 : (s3.stk SX).headD Glyph.eos = Glyph.cons := by
    rw [hSX3', hSXd]
    rfl
  have e4 : Ev main (.peek SX rF) s3 ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 1 := by
    have hp' := ev_peek' main SX rF s3.reg s3.stk
    rw [h4] at hp'
    exact hp'
  have e5 : Ev main (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF))
      ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩
      ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 2 := by
    have hsk : Ev main .skip ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩
        ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 1 := ev_skip main _
    exact Ev.iteT (C := 1) (by simp) hsk
  have eflag : Ev main (.seq (.peek SX Sk.rF) (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)))
      s3 ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 3 := Ev.seq' e4 e5 (by omega)
  have eite : Ev main
      (.ite Sk.rH Glyph.cons
        (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
          (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
        (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip)))
      ⟨Function.update g rH Glyph.cons, X⟩ s3 (M + 3) :=
    Ev.iteT (C := M + 2) (by simp)
      (Ev.seq' (C := M + 2) e2 (Ev.iteT (C := M) (by simp) e3) (by omega))
  have epre1 : Ev main
      (.seq (.peek SX Sk.rH)
        (.ite Sk.rH Glyph.cons
          (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
            (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
          (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))))
      ⟨g, X⟩ s3 (M + 4) := Ev.seq' (C := M + 4) e1 eite (by omega)
  have epre : Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩
      ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ (M + 7) := by
    unfold Sk.mBody
    exact Ev.seq' (C := M + 7) epre1 eflag (by omega)
  refine ⟨⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩, M + 7, epre, ?_, ?_, h03, hSX3',
    hSY3, hSA3, hSB3', hT3', ?_⟩
  · have hb : M + 7 ≤ mrgStep KLt KSz p ps q qs := by
      have h1 := le_mrgStep KLt KSz p ps q qs
      rw [hp, hq]
      rw [hp, hq] at h1
      simp only [mrgStepCore] at hM
      omega
    exact hb
  · show Function.update s3.reg rF Glyph.cons rF = Glyph.cons
    rw [Function.update_self]
  · intro k' hk
    have h1' : s3.stk k' = X k' := by
      by_cases hm : k' ∈ ({F1, F2, t, d, 0} : Finset Stk)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        · exact hF13
        · exact hF23
        · exact ht3
        · exact hd3
        · rw [h03, h0]
      · have hm' : k' ≠ F1 ∧ k' ≠ F2 ∧ k' ≠ t ∧ k' ≠ d ∧ k' ≠ 0 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          tauto
        exact hfr3 k' (stepTouched_of_not_mem hk hm'.1 hm'.2.1 hm'.2.2.1 hm'.2.2.2.1
          hm'.2.2.2.2)
    rw [h1']
    exact hfr k' hk

/-! ## one comparison step of the loop, `keyOf p ≤ keyOf q` (the front of `SX` moves) -/

theorem mBody_pairR {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True)
      (fun a => (a.natAbs.size : ℤ)) (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph}
    {p q : Val} {ps qs : List Val} {k l : ℕ} {v' w' : Val}
    {A B' Tc R Sc Sc' : List Glyph} {Tk : List Val} {S : Stk → List Glyph}
    (hp : p = Val.cons (Val.int (k : ℤ)) v') (hq : q = Val.cons (Val.int (l : ℤ)) w')
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hge : ¬ (l < k))
    (hSX : X SX = encs (p :: ps) ++ gMark :: A)
    (hSY : X SY = encs (q :: qs) ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = encs Tk ++ gMark :: Tc)
    (h0 : X 0 = R)
    (hF1 : X F1 = S F1) (hF2 : X F2 = S F2) (ht : X t = S t) (hd : X d = S d)
    (hfr : ∀ k', k' ∉ loopTouched SX SY T SA SB → X k' = S k') :
    ∃ s' n, Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStep KLt KSz p ps q qs ∧
      s'.reg Sk.rF = Glyph.cons ∧ s'.stk 0 = R ∧
      s'.stk SX = encs ps ++ gMark :: A ∧ s'.stk SY = X SY ∧
      s'.stk SA = (if ps = [] then X SA
                   else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ X SA) ∧
      s'.stk SB = X SB ∧ s'.stk T = p.enc ++ encs Tk ++ gMark :: Tc ∧
      (∀ k', k' ∉ loopTouched SX SY T SA SB → s'.stk k' = S k') := by
  have hSXm : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A := by
    rw [hSX, hp]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hSYm : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B' := by
    rw [hSY, hq]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hkey : keyOf p = k := by rw [hp, keyOf_record]
  have hkeyq : keyOf q = l := by rw [hq, keyOf_record]
  have hSXd : X SX = Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A))) := by
    rw [hSXm]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  have hSYd : X SY = Glyph.cons :: ((Val.int (l : ℤ)).enc ++ (w'.enc ++ (encs qs ++ gMark :: B'))) := by
    rw [hSYm]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  have h1 : (X SX).headD Glyph.eos = Glyph.cons := by rw [hSXd]; rfl
  have h2 : (X SY).headD Glyph.eos = Glyph.cons := by rw [hSYd]; rfl
  have e1 : Ev main (.peek SX rH) ⟨g, X⟩ ⟨Function.update g rH Glyph.cons, X⟩ 1 := by
    have hp' := ev_peek' main SX rH g X
    rw [h1] at hp'
    exact hp'
  have e2 : Ev main (.peek SY rI) ⟨Function.update g rH Glyph.cons, X⟩
      ⟨Function.update (Function.update g rH Glyph.cons) rI Glyph.cons, X⟩ 1 := by
    have hp' := ev_peek' main SY rI (Function.update g rH Glyph.cons) X
    rw [h2] at hp'
    exact hp'
  obtain ⟨s3, M, e3, hM, h03, hT3, hSX3, hSY3, hSA3, hSB3, hF13, hF23, ht3, hd3, hfr3⟩ :=
    mrgMergeStep (main := main) (pLt := pLt) (pSize := pSize) hLt hSz hdis hps hqs
      (SX := SX) (SY := SY) (SA := SA) (SB := SB) (T := T) (F1 := F1) (F2 := F2) (t := t) (d := d)
      (g := Function.update (Function.update g rH Glyph.cons) rI Glyph.cons) (X := X)
      (k := k) (l := l) (v' := v') (w' := w') (ps := ps) (qs := qs) (A := A) (B' := B')
      (Tc := encs Tk ++ gMark :: Tc) (R := R) (Sc := Sc) (Sc' := Sc') hSXm hSYm hSA hSB hT h0
  rw [ite_eq_right hge] at hT3 hSX3 hSY3 hSA3 hSB3
  have hSY3' : s3.stk SY = X SY := by rw [hSY3, hSYm]
  have hSA3'' : s3.stk SA = (if ps = [] then X SA
      else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ X SA) := by
    rw [hSA3]
    by_cases hps0 : ps = []
    · rw [ite_eq_left hps0, ite_eq_left hps0]
    · rw [ite_eq_right hps0, ite_eq_right hps0, List.append_assoc]
      rw [← hSA]
  have hT3' : s3.stk T = p.enc ++ encs Tk ++ gMark :: Tc := by
    rw [← hp] at hT3
    rw [hT3, List.append_assoc]
  have hflag : ∃ s5 : State,
      Ev main (.seq (.peek SX Sk.rF) (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF))) s3 s5 3 ∧
      s5.reg Sk.rF = Glyph.cons ∧ s5.stk = s3.stk := by
    have h4 : (s3.stk SX).headD Glyph.eos = (if ps = [] then gMark else Glyph.cons) := by
      rw [hSX3]
      exact headD_encs_ps ps A hps
    by_cases hps' : ps = []
    · have h5 : (s3.stk SX).headD Glyph.eos = gMark := by rw [h4, ite_eq_left hps']
      have e4 : Ev main (.peek SX rF) s3 ⟨Function.update s3.reg rF gMark, s3.stk⟩ 1 := by
        have hp' := ev_peek' main SX rF s3.reg s3.stk
        rw [h5] at hp'
        exact hp'
      have h6 : (s3.stk SY).headD Glyph.eos = Glyph.cons := by
        rw [hSY3]
        simp only [Val.enc, List.cons_append, List.append_assoc, List.headD_cons]
      refine ⟨⟨Function.update (Function.update s3.reg rF gMark) rF Glyph.cons, s3.stk⟩, ?_,
        by simp, rfl⟩
      have hne : (Function.update s3.reg rF gMark) rF ≠ Glyph.cons := by
        rw [Function.update_self]
        exact gMark_ne_cons
      have e5 : Ev main (.peek SY rF) ⟨Function.update s3.reg rF gMark, s3.stk⟩
          ⟨Function.update (Function.update s3.reg rF gMark) rF Glyph.cons, s3.stk⟩ 1 := by
        have hp' := ev_peek' main SY rF (Function.update s3.reg rF gMark) s3.stk
        rw [h6] at hp'
        exact hp'
      have e6 : Ev main (.ite rF Glyph.cons .skip (.peek SY rF))
          ⟨Function.update s3.reg rF gMark, s3.stk⟩
          ⟨Function.update (Function.update s3.reg rF gMark) rF Glyph.cons, s3.stk⟩ 2 :=
        Ev.iteF (C := 1) hne e5
      exact Ev.seq' (C := 3) e4 e6 (by omega)
    · have h5 : (s3.stk SX).headD Glyph.eos = Glyph.cons := by rw [h4, ite_eq_right hps']
      have e4 : Ev main (.peek SX rF) s3 ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 1 := by
        have hp' := ev_peek' main SX rF s3.reg s3.stk
        rw [h5] at hp'
        exact hp'
      refine ⟨⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩, ?_, by simp, rfl⟩
      have e6 : Ev main (.ite rF Glyph.cons .skip (.peek SY rF))
          ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩
          ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 2 := by
        have hsk : Ev main .skip ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩
            ⟨Function.update s3.reg rF Glyph.cons, s3.stk⟩ 1 := ev_skip main _
        exact Ev.iteT (C := 1) (by simp) hsk
      exact Ev.seq' (C := 3) e4 e6 (by omega)
  obtain ⟨s5, eflag, hrF5, hstk5⟩ := hflag
  have eite : Ev main
      (.ite Sk.rH Glyph.cons
        (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
          (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
        (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip)))
      ⟨Function.update g rH Glyph.cons, X⟩ s3 (M + 3) :=
    Ev.iteT (C := M + 2) (by simp)
      (Ev.seq' (C := M + 2) e2 (Ev.iteT (C := M) (by simp) e3) (by omega))
  have epre1 : Ev main
      (.seq (.peek SX Sk.rH)
        (.ite Sk.rH Glyph.cons
          (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
            (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
          (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))))
      ⟨g, X⟩ s3 (M + 4) := Ev.seq' (C := M + 4) e1 eite (by omega)
  have epre : Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s5 (M + 7) := by
    unfold Sk.mBody
    exact Ev.seq' (C := M + 7) epre1 eflag (by omega)
  refine ⟨s5, M + 7, epre, ?_, hrF5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : M + 7 ≤ mrgStep KLt KSz p ps q qs := by
      have h1 := le_mrgStep KLt KSz p ps q qs
      rw [hp, hq]
      rw [hp, hq] at h1
      simp only [mrgStepCore] at hM
      omega
    exact hb
  · rw [hstk5]; exact h03
  · rw [hstk5]; exact hSX3
  · rw [hstk5]; exact hSY3'
  · rw [hstk5]; exact hSA3''
  · rw [hstk5]; exact hSB3
  · rw [hstk5]; exact hT3' 
  · intro k' hk
    have h1' : s3.stk k' = X k' := by
      by_cases hm : k' ∈ ({F1, F2, t, d, 0} : Finset Stk)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        · exact hF13
        · exact hF23
        · exact ht3
        · exact hd3
        · rw [h03, h0]
      · have hm' : k' ≠ F1 ∧ k' ≠ F2 ∧ k' ≠ t ∧ k' ≠ d ∧ k' ≠ 0 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          tauto
        exact hfr3 k' (stepTouched_of_not_mem hk hm'.1 hm'.2.1 hm'.2.2.1 hm'.2.2.2.1
          hm'.2.2.2.2)
    rw [hstk5, h1']
    exact hfr k' hk

/-! ## the comparison phase of the loop

From a state satisfying the loop invariant with both runs nonempty, the loop keeps comparing until one
of the two runs is exhausted.  The bookkeeping is the `merge2` invariant
`merge2 P Q = Tk.reverse ++ merge2 P₂ Q₂` together with the two run/cache splits. -/

set_option maxHeartbeats 4000000 in
theorem merge_loopCmp {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True)
      (fun a => (a.natAbs.size : ℤ)) (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {S : Stk → List Glyph}
    {A B' Tc R Sc Sc' : List Glyph} {P Q P₁ P₂ Q₁ Q₂ Tk : List Val}
    (hrec : ∀ v ∈ P ++ Q, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v')
    (hP : P = P₁ ++ P₂) (hQ : Q = Q₁ ++ Q₂)
    (hm : merge2 P Q = Tk.reverse ++ merge2 P₂ Q₂)
    (hSX : X SX = encs P₂ ++ gMark :: A) (hSY : X SY = encs Q₂ ++ gMark :: B')
    (hT : X T = encs Tk ++ gMark :: Tc)
    (hSA : X SA = encs (cache P₁ P₂) ++ gMark :: Sc)
    (hSB : X SB = encs (cache Q₁ Q₂) ++ gMark :: Sc')
    (h0 : X 0 = R)
    (hfr : ∀ k', k' ∉ loopTouched SX SY T SA SB → X k' = S k')
    (hg : g Sk.rF = Glyph.cons) :
    ∃ (k : ℕ) (P₁' P₂' Q₁' Q₂' Tk' : List Val) (s' : State) (n : ℕ),
      loopRuns main Sk.rF Glyph.cons (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) k ⟨g, X⟩ s' n ∧
      n ≤ mrgCost KLt KSz P₂ Q₂ + (P₂.length + Q₂.length) ∧
      (P₂' = [] ∨ Q₂' = []) ∧ s'.reg Sk.rF = Glyph.cons ∧
      P = P₁' ++ P₂' ∧ Q = Q₁' ++ Q₂' ∧
      merge2 P Q = Tk'.reverse ++ merge2 P₂' Q₂' ∧
      s'.stk SX = encs P₂' ++ gMark :: A ∧ s'.stk SY = encs Q₂' ++ gMark :: B' ∧
      s'.stk T = encs Tk' ++ gMark :: Tc ∧
      s'.stk SA = encs (cache P₁' P₂') ++ gMark :: Sc ∧
      s'.stk SB = encs (cache Q₁' Q₂') ++ gMark :: Sc' ∧
      s'.stk 0 = R ∧
      (∀ k', k' ∉ loopTouched SX SY T SA SB → s'.stk k' = S k') := by
  obtain ⟨hdF1, hdF2, hdt, hdd, hd0⟩ := hdis_notMem hdis
  have aux : ∀ (m : ℕ) (P Q P₁ P₂ Q₁ Q₂ : List Val) (Tk : List Val)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      P₂.length + Q₂.length = m →
      (∀ v ∈ P ++ Q, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') →
      P = P₁ ++ P₂ → Q = Q₁ ++ Q₂ → merge2 P Q = Tk.reverse ++ merge2 P₂ Q₂ →
      X SX = encs P₂ ++ gMark :: A → X SY = encs Q₂ ++ gMark :: B' →
      X T = encs Tk ++ gMark :: Tc → X SA = encs (cache P₁ P₂) ++ gMark :: Sc →
      X SB = encs (cache Q₁ Q₂) ++ gMark :: Sc' → X 0 = R →
      (∀ k', k' ∉ loopTouched SX SY T SA SB → X k' = S k') → g Sk.rF = Glyph.cons →
      ∃ (k : ℕ) (P₁' P₂' Q₁' Q₂' Tk' : List Val) (s' : State) (n : ℕ),
        loopRuns main Sk.rF Glyph.cons (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) k ⟨g, X⟩ s' n ∧
        n ≤ mrgCost KLt KSz P₂ Q₂ + (P₂.length + Q₂.length) ∧
        (P₂' = [] ∨ Q₂' = []) ∧ s'.reg Sk.rF = Glyph.cons ∧
        P = P₁' ++ P₂' ∧ Q = Q₁' ++ Q₂' ∧
        merge2 P Q = Tk'.reverse ++ merge2 P₂' Q₂' ∧
        s'.stk SX = encs P₂' ++ gMark :: A ∧ s'.stk SY = encs Q₂' ++ gMark :: B' ∧
        s'.stk T = encs Tk' ++ gMark :: Tc ∧
        s'.stk SA = encs (cache P₁' P₂') ++ gMark :: Sc ∧
        s'.stk SB = encs (cache Q₁' Q₂') ++ gMark :: Sc' ∧
        s'.stk 0 = R ∧
        (∀ k', k' ∉ loopTouched SX SY T SA SB → s'.stk k' = S k') := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro P Q P₁ P₂ Q₁ Q₂ Tk g X hlen hrec hP hQ hm hSX hSY hT hSA hSB h0 hfr hg
      rcases P₂ with _ | ⟨p, ps⟩
      · refine ⟨0, P₁, [], Q₁, Q₂, Tk, ⟨g, X⟩, 0, loopRuns.zero, ?_, Or.inl rfl, hg, hP, hQ,
          hm, hSX, hSY, hT, hSA, hSB, h0, hfr⟩
        rw [mmc_cost_nil_left]
        simp
      · rcases Q₂ with _ | ⟨q, qs⟩
        · refine ⟨0, P₁, p :: ps, Q₁, [], Tk, ⟨g, X⟩, 0, loopRuns.zero, ?_, Or.inr rfl, hg, hP,
            hQ, hm, hSX, hSY, hT, hSA, hSB, h0, hfr⟩
          rw [mmc_cost_nil_right]
          simp
        · have hp_mem : p ∈ P ++ Q := by rw [hP]; simp
          have hq_mem : q ∈ P ++ Q := by rw [hQ]; simp
          obtain ⟨k, v', hp⟩ := hrec p hp_mem
          obtain ⟨l, w', hq⟩ := hrec q hq_mem
          have hps : ∀ v ∈ ps, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
            intro v hv
            exact hrec v (by rw [hP]; simp [hv])
          have hqs : ∀ v ∈ qs, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
            intro v hv
            exact hrec v (by rw [hQ]; simp [hv])
          have hkeyp : keyOf p = k := by rw [hp, keyOf_record]
          have hkeyq : keyOf q = l := by rw [hq, keyOf_record]
          have hF1 : X F1 = S F1 := hfr F1 hdF1
          have hF2 : X F2 = S F2 := hfr F2 hdF2
          have htm : X t = S t := hfr t hdt
          have hdm : X d = S d := hfr d hdd
          have hSA' : X SA = (Val.int (k.size : ℤ)).enc ++
              (encs ((P₁.map ksv).reverse) ++ gMark :: Sc) := by
            rw [hSA, cache_cons, hp, ksv_record]
            simp only [encs, List.map_cons, List.flatten_cons, List.cons_append, List.append_assoc]
          have hSB' : X SB = (Val.int (l.size : ℤ)).enc ++
              (encs ((Q₁.map ksv).reverse) ++ gMark :: Sc') := by
            rw [hSB, cache_cons, hq, ksv_record]
            simp only [encs, List.map_cons, List.flatten_cons, List.cons_append, List.append_assoc]
          by_cases hlt : keyOf q < keyOf p
          · have hltk : l < k := by rw [hkeyp, hkeyq] at hlt; exact hlt
            have hplt : pairKey q < pairKey p := by
              rw [hq, hp]
              show (l : ℤ) < (k : ℤ)
              exact_mod_cast hltk
            obtain ⟨s', n, hev, hcost, hF', h0', hSXm, hSYm, hSAm, hSBm, hTm, hfrm⟩ :=
              mBody_pairL (main := main) (pLt := pLt) (pSize := pSize) hLt hSz hdis
                (p := p) (ps := ps) (k := k) (v' := v') (q := q) (qs := qs) (l := l) (w' := w')
                (hp := hp) (hq := hq) (hps := hps) (hqs := hqs) (hlt := hltk)
                (hSX := hSX) (hSY := hSY) (hSA := hSA') (hSB := hSB') (hT := hT) (h0 := h0)
                (hF1 := hF1) (hF2 := hF2) (ht := htm) (hd := hdm) (hfr := hfr)
            have hrun₁ : loopRuns main Sk.rF Glyph.cons
                (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) 1 ⟨g, X⟩ s' (n + 1) :=
              loopRuns.succ' hg hev loopRuns.zero (by omega)
            have hQeq : Q = (Q₁ ++ [q]) ++ qs := by
              rw [hQ, List.append_assoc, List.singleton_append]
            have hMeq : merge2 P Q = (q :: Tk).reverse ++ merge2 (p :: ps) qs := by
              rw [hm, merge2_cons_of_lt hplt, List.reverse_cons]
              simp only [List.singleton_append, List.append_assoc]
            have hTm₂ : s'.stk T = encs (q :: Tk) ++ gMark :: Tc := by
              rw [hTm]; rfl
            have hSAm₂ : s'.stk SA = encs (cache P₁ (p :: ps)) ++ gMark :: Sc := by
              rw [hSAm, hSA]
            have hSBm₂ : s'.stk SB = encs (cache (Q₁ ++ [q]) qs) ++ gMark :: Sc' := by
              rw [hSBm, hSB]
              exact mrg_cache_move Q₁ q qs (gMark :: Sc')
            have hSXm₂ : s'.stk SX = encs (p :: ps) ++ gMark :: A := by
              rw [hSXm, hSX]
            obtain ⟨k₂, P₁₂, P₂₂, Q₁₂, Q₂₂, Tk₂, s₂, n₂, hrun₂, hcost₂, hnil₂, hrF₂, hPeq₂,
              hQeq₂, hMeq₂, hSX₂, hSY₂, hT₂, hSA₂, hSB₂, h0₂, hfr₂⟩ :=
              ih ((p :: ps).length + qs.length) (by simp only [List.length_cons] at hlen ⊢; omega)
                P Q P₁ (p :: ps) (Q₁ ++ [q]) qs (q :: Tk) s'.reg s'.stk rfl hrec hP hQeq hMeq
                hSXm₂ hSYm hTm₂ hSAm₂ hSBm₂ h0' hfrm hF'
            refine ⟨1 + k₂, P₁₂, P₂₂, Q₁₂, Q₂₂, Tk₂, s₂, (n + 1) + n₂,
              loopRuns.concat k₂ hrun₁ hrun₂, ?_, hnil₂, hrF₂, hPeq₂, hQeq₂, hMeq₂, hSX₂,
              hSY₂, hT₂, hSA₂, hSB₂, h0₂, hfr₂⟩
            rw [mmc_cost_cons, ite_eq_left hlt]
            simp only [List.length_cons] at hcost hcost₂ ⊢
            omega
          · have hgek : ¬ (l < k) := by rw [hkeyp, hkeyq] at hlt; exact hlt
            have hpge : ¬ (pairKey q < pairKey p) := by
              intro hcon
              have hcon' : (l : ℤ) < (k : ℤ) := by
                rw [hq, hp] at hcon
                exact hcon
              exact hgek (by exact_mod_cast hcon')
            obtain ⟨s', n, hev, hcost, hF', h0', hSXm, hSYm, hSAm, hSBm, hTm, hfrm⟩ :=
              mBody_pairR (main := main) (pLt := pLt) (pSize := pSize) hLt hSz hdis
                (p := p) (ps := ps) (k := k) (v' := v') (q := q) (qs := qs) (l := l) (w' := w')
                (hp := hp) (hq := hq) (hps := hps) (hqs := hqs) (hge := hgek)
                (hSX := hSX) (hSY := hSY) (hSA := hSA') (hSB := hSB') (hT := hT) (h0 := h0)
                (hF1 := hF1) (hF2 := hF2) (ht := htm) (hd := hdm) (hfr := hfr)
            have hrun₁ : loopRuns main Sk.rF Glyph.cons
                (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) 1 ⟨g, X⟩ s' (n + 1) :=
              loopRuns.succ' hg hev loopRuns.zero (by omega)
            have hPeq : P = (P₁ ++ [p]) ++ ps := by
              rw [hP, List.append_assoc, List.singleton_append]
            have hMeq : merge2 P Q = (p :: Tk).reverse ++ merge2 ps (q :: qs) := by
              rw [hm, merge2_cons_of_ge hpge, List.reverse_cons]
              simp only [List.singleton_append, List.append_assoc]
            have hTm₂ : s'.stk T = encs (p :: Tk) ++ gMark :: Tc := by
              rw [hTm]; rfl
            have hSAm₂ : s'.stk SA = encs (cache (P₁ ++ [p]) ps) ++ gMark :: Sc := by
              rw [hSAm, hSA]
              exact mrg_cache_move P₁ p ps (gMark :: Sc)
            have hSBm₂ : s'.stk SB = encs (cache Q₁ (q :: qs)) ++ gMark :: Sc' := by
              rw [hSBm, hSB]
            have hSYm₂ : s'.stk SY = encs (q :: qs) ++ gMark :: B' := by
              rw [hSYm, hSY]
            obtain ⟨k₂, P₁₂, P₂₂, Q₁₂, Q₂₂, Tk₂, s₂, n₂, hrun₂, hcost₂, hnil₂, hrF₂, hPeq₂,
              hQeq₂, hMeq₂, hSX₂, hSY₂, hT₂, hSA₂, hSB₂, h0₂, hfr₂⟩ :=
              ih (ps.length + (q :: qs).length) (by simp only [List.length_cons] at hlen ⊢; omega)
                P Q (P₁ ++ [p]) ps Q₁ (q :: qs) (p :: Tk) s'.reg s'.stk rfl hrec hPeq hQ hMeq
                hSXm hSYm₂ hTm₂ hSAm₂ hSBm₂ h0' hfrm hF'
            refine ⟨1 + k₂, P₁₂, P₂₂, Q₁₂, Q₂₂, Tk₂, s₂, (n + 1) + n₂,
              loopRuns.concat k₂ hrun₁ hrun₂, ?_, hnil₂, hrF₂, hPeq₂, hQeq₂, hMeq₂, hSX₂,
              hSY₂, hT₂, hSA₂, hSB₂, h0₂, hfr₂⟩
            rw [mmc_cost_cons, ite_eq_right hlt]
            simp only [List.length_cons] at hcost hcost₂ ⊢
            omega
  exact aux (P₂.length + Q₂.length) P Q P₁ P₂ Q₁ Q₂ Tk g X rfl hrec hP hQ hm hSX hSY hT hSA hSB
    h0 hfr hg

/-- **the tail of `mergePair`**: the two `pop`s that drop the boundary markers of the two runs, the
`outRun` that pushes the merged run onto `D`, and the two `cleanStack`s that remove the caches. -/
theorem merge_pair_tail {main pLt pSize : Cmd} {SX SY T D SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, D, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {S : Stk → List Glyph}
    {A B' Tc Dc Sc Sc' : List Glyph} {vals CLA CLB : List Val} {BdA BdB BdV : ℕ}
    (hSX : X SX = gMark :: A) (hSY : X SY = gMark :: B')
    (hT : X T = encs vals ++ gMark :: Tc) (hD : X D = Dc)
    (hSA : X SA = encs CLA ++ gMark :: Sc) (hSB : X SB = encs CLB ++ gMark :: Sc')
    (hrec : ∀ v ∈ vals, ∃ a b : Val, v = Val.cons a b)
    (hSAv : (CLA.map vsz).sum ≤ BdA) (hSBv : (CLB.map vsz).sum ≤ BdB)
    (hVv : (vals.map vsz).sum + vals.length ≤ BdV)
    (hfr : ∀ k', k' ≠ SX → k' ≠ SY → k' ≠ T → k' ≠ D → k' ≠ SA → k' ≠ SB → X k' = S k') :
    ∃ s' n, Ev main (seqs [.pop SX rJ, .pop SY rJ, Sk.outRun T D t d, Sk.cleanStack SA,
        Sk.cleanStack SB]) ⟨g, X⟩ s' n ∧
      n ≤ 5 + 20 * (BdV + 1) + 5 * BdA + 5 * BdB + 24 ∧
      s'.stk SX = A ∧ s'.stk SY = B' ∧ s'.stk T = Tc ∧
      s'.stk D = encs vals.reverse ++ gMark :: Dc ∧
      s'.stk SA = Sc ∧ s'.stk SB = Sc' ∧
      (∀ k', k' ≠ SX → k' ≠ SY → k' ≠ T → k' ≠ D → k' ≠ SA → k' ≠ SB → s'.stk k' = S k') := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := hdis11_peel hdis
  have hSXSY : SX ≠ SY := ne_of_notMem i1 (by simp)
  have hSXT : SX ≠ T := ne_of_notMem i1 (by simp)
  have hSXD : SX ≠ D := ne_of_notMem i1 (by simp)
  have hSXA : SX ≠ SA := ne_of_notMem i1 (by simp)
  have hSXB : SX ≠ SB := ne_of_notMem i1 (by simp)
  have hSYT : SY ≠ T := ne_of_notMem i2 (by simp)
  have hSYD : SY ≠ D := ne_of_notMem i2 (by simp)
  have hSYA : SY ≠ SA := ne_of_notMem i2 (by simp)
  have hSYB : SY ≠ SB := ne_of_notMem i2 (by simp)
  have hTD : T ≠ D := ne_of_notMem i3 (by simp)
  have hTA : T ≠ SA := ne_of_notMem i3 (by simp)
  have hTB : T ≠ SB := ne_of_notMem i3 (by simp)
  have hTt : T ≠ t := ne_of_notMem i3 (by simp)
  have hTd : T ≠ d := ne_of_notMem i3 (by simp)
  have hDA : D ≠ SA := ne_of_notMem i4 (by simp)
  have hDB : D ≠ SB := ne_of_notMem i4 (by simp)
  have hDt : D ≠ t := ne_of_notMem i4 (by simp)
  have hDd : D ≠ d := ne_of_notMem i4 (by simp)
  have hAB : SA ≠ SB := ne_of_notMem i5 (by simp)
  have hAt : SA ≠ t := ne_of_notMem i5 (by simp)
  have hAd : SA ≠ d := ne_of_notMem i5 (by simp)
  have hBt : SB ≠ t := ne_of_notMem i6 (by simp)
  have hBd : SB ≠ d := ne_of_notMem i6 (by simp)
  have htd : t ≠ d := ne_of_notMem i9 (by simp)
  -- (i) `pop SX rJ`
  obtain ⟨s1, e1, h1SX, hfr1⟩ : ∃ s1 : State, Ev main (.pop SX rJ) ⟨g, X⟩ s1 1 ∧
      s1.stk SX = A ∧ (∀ k', k' ≠ SX → s1.stk k' = X k') := by
    refine ⟨⟨Function.update g rJ ((X SX).headD Glyph.eos), Function.update X SX (X SX).tail⟩,
      ev_pop' main SX rJ g X, ?_, ?_⟩
    · show (Function.update X SX (X SX).tail) SX = A
      rw [Function.update_self, hSX]
      rfl
    · intro k' hk
      simp [Function.update_of_ne hk]
  have h1SY : s1.stk SY = gMark :: B' := by rw [hfr1 SY hSXSY.symm, hSY]
  have h1T : s1.stk T = encs vals ++ gMark :: Tc := by rw [hfr1 T hSXT.symm, hT]
  have h1D : s1.stk D = Dc := by rw [hfr1 D hSXD.symm, hD]
  have h1A : s1.stk SA = encs CLA ++ gMark :: Sc := by rw [hfr1 SA hSXA.symm, hSA]
  have h1B : s1.stk SB = encs CLB ++ gMark :: Sc' := by rw [hfr1 SB hSXB.symm, hSB]
  -- (ii) `pop SY rJ`
  obtain ⟨s2, e2, h2SY, hfr2⟩ : ∃ s2 : State, Ev main (.pop SY rJ) s1 s2 1 ∧
      s2.stk SY = B' ∧ (∀ k', k' ≠ SY → s2.stk k' = s1.stk k') := by
    refine ⟨⟨Function.update s1.reg rJ ((s1.stk SY).headD Glyph.eos),
      Function.update s1.stk SY (s1.stk SY).tail⟩, ev_pop' main SY rJ s1.reg s1.stk, ?_, ?_⟩
    · show (Function.update s1.stk SY (s1.stk SY).tail) SY = B'
      rw [Function.update_self, h1SY]
      rfl
    · intro k' hk
      simp [Function.update_of_ne hk]
  have h2T : s2.stk T = encs vals ++ gMark :: Tc := by rw [hfr2 T hSYT.symm, h1T]
  have h2D : s2.stk D = Dc := by rw [hfr2 D hSYD.symm, h1D]
  have h2A : s2.stk SA = encs CLA ++ gMark :: Sc := by rw [hfr2 SA hSYA.symm, h1A]
  have h2B : s2.stk SB = encs CLB ++ gMark :: Sc' := by rw [hfr2 SB hSYB.symm, h1B]
  -- (iii) `outRun T D t d`
  obtain ⟨s3, n3, e3, hn3, h3D, hfr3, -, -⟩ :=
    pushConst_ev (main := main) (k := D) (cst := gMark) (g := s2.reg) (X := s2.stk)
  have h3Dc : s3.stk D = gMark :: Dc := by rw [h3D, h2D]
  have h3T : s3.stk T = encs vals ++ gMark :: Tc := by rw [hfr3 T hTD, h2T]
  obtain ⟨s4, n4, e4, hn4, h4T, h4D, h4t, h4d, hfr4⟩ :=
    drainValsEv (main := main) (S := T) (T := D) (t := t) (d := d) hTD hTt hTd hDt hDd htd
      (g := s3.reg) (X := s3.stk) hrec h3T h3Dc
  obtain ⟨s5, e5, h5T, hfr5⟩ : ∃ s5 : State, Ev main (.pop T rJ) s4 s5 1 ∧
      s5.stk T = Tc ∧ (∀ k', k' ≠ T → s5.stk k' = s4.stk k') := by
    refine ⟨⟨Function.update s4.reg rJ ((s4.stk T).headD Glyph.eos),
      Function.update s4.stk T (s4.stk T).tail⟩, ev_pop' main T rJ s4.reg s4.stk, ?_, ?_⟩
    · show (Function.update s4.stk T (s4.stk T).tail) T = Tc
      rw [Function.update_self, h4T]
      rfl
    · intro k' hk
      simp [Function.update_of_ne hk]
  have eout : Ev main (Sk.outRun T D t d) s2 s5 (2 + n4 + 1) := by
    unfold Sk.outRun
    exact Ev.seq' (C := 2 + n4 + 1) (e3.mono hn3)
      (Ev.seq' (C := n4 + 1) e4 e5 (by omega)) (by omega)
  have h4A : s4.stk SA = encs CLA ++ gMark :: Sc := by
    rw [frame_peel4 hfr4 h4t h4d SA hTA.symm hDA.symm, hfr3 SA hDA.symm, h2A]
  have h4B : s4.stk SB = encs CLB ++ gMark :: Sc' := by
    rw [frame_peel4 hfr4 h4t h4d SB hTB.symm hDB.symm, hfr3 SB hDB.symm, h2B]
  have h5A : s5.stk SA = encs CLA ++ gMark :: Sc := by rw [hfr5 SA hTA.symm, h4A]
  have h5B : s5.stk SB = encs CLB ++ gMark :: Sc' := by rw [hfr5 SB hTB.symm, h4B]
  -- (iv) the two `cleanStack`s
  obtain ⟨s6, n6, e6, hn6, h6A, hfr6⟩ :=
    merge_cleanStack (main := main) (SA := SA) (CL := CLA) (Sc := Sc) (g := s5.reg)
      (X := s5.stk) h5A
  have h6B : s6.stk SB = encs CLB ++ gMark :: Sc' := by rw [hfr6 SB hAB.symm, h5B]
  obtain ⟨s7, n7, e7, hn7, h7B, hfr7⟩ :=
    merge_cleanStack (main := main) (SA := SB) (CL := CLB) (Sc := Sc') (g := s6.reg)
      (X := s6.stk) h6B
  have htail : Ev main (seqs [.pop SX rJ, .pop SY rJ, Sk.outRun T D t d, Sk.cleanStack SA,
      Sk.cleanStack SB]) ⟨g, X⟩ s7 (1 + 1 + (2 + n4 + 1) + n6 + n7) := by
    simp only [seqs]
    exact Ev.seq' (C := 1 + 1 + (2 + n4 + 1) + n6 + n7) e1
      (Ev.seq' (C := 1 + (2 + n4 + 1) + n6 + n7) e2
      (Ev.seq' (C := (2 + n4 + 1) + n6 + n7) eout
      (Ev.seq' (C := n6 + n7) e6 e7 (by omega)) (by omega)) (by omega)) (by omega)
  refine ⟨s7, 1 + 1 + (2 + n4 + 1) + n6 + n7, htail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h4' : n4 ≤ 20 * (BdV + 1) := by omega
    have h6' : n6 ≤ 5 * BdA + 12 := by
      have h := hn6
      rw [encs_length] at h
      omega
    have h7' : n7 ≤ 5 * BdB + 12 := by
      have h := hn7
      rw [encs_length] at h
      omega
    omega
  · rw [hfr7 SX hSXB, hfr6 SX hSXA, hfr5 SX hSXT,
      frame_peel4 hfr4 h4t h4d SX hSXT hSXD, hfr3 SX hSXD, hfr2 SX hSXSY, h1SX]
  · rw [hfr7 SY hSYB, hfr6 SY hSYA, hfr5 SY hSYT,
      frame_peel4 hfr4 h4t h4d SY hSYT hSYD, hfr3 SY hSYD, h2SY]
  · rw [hfr7 T hTB, hfr6 T hTA, h5T]
  · rw [hfr7 D hDB, hfr6 D hDA, hfr5 D hTD.symm, h4D]
  · rw [hfr7 SA hAB, h6A]
  · rw [h7B]
  · intro k h1 h2 h3 h4 h5 h6
    rw [hfr7 k h6, hfr6 k h5, hfr5 k h3, frame_peel4 hfr4 h4t h4d k h3 h4, hfr3 k h4,
      hfr2 k h2, hfr1 k h1]
    exact hfr k h1 h2 h3 h4 h5 h6

/-- **THE CRUX**: the `mergePair` word merges the two runs of `SX`,`SY` onto `D`. -/
theorem mergePair_ev {main pLt pSz : HvdH.Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : HvdH.Cmd, HvdH.BinOp main pLt (fun _ _ => True)
      (fun a b => if a < b then 1 else 0) (fun a b => KLt * (HvdH.isz a + HvdH.isz b)))
    (hSz : ∀ main : HvdH.Cmd, HvdH.UnOp main pSz (fun _ => True)
      (fun a => (a.natAbs.size : ℤ)) (fun a => KSz * HvdH.isz a))
    {SX SY T D SA SB F1 F2 t d : HvdH.Stk}
    (hdis : ([SX, SY, T, D, SA, SB, F1, F2, t, d, 0] : List HvdH.Stk).Nodup) :
    Work.Layout.Sk.MergePairSpec main pLt pSz SX SY T D SA SB F1 F2 t d KLt KSz := by
  intro P Q A B' Tc Dc Sc Sc' g S hSX hSY hT hD hSA hSB hP hQ hrecP hrecQ hsP hsQ hnd
  obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil hP
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hQ
  obtain ⟨kp, vp, hp⟩ := hrecP p (by simp)
  obtain ⟨lq, wq, hq⟩ := hrecQ q (by simp)
  have hrecAll : ∀ v ∈ (p :: ps) ++ (q :: qs),
      ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
    intro v hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hrecP v h1
    · exact hrecQ v h1
  set Tt : ℕ := (((p :: ps) ++ (q :: qs)).map vsz).sum + ((p :: ps) ++ (q :: qs)).length + 2
    with hTt
  have hTt2 : 2 ≤ Tt := by rw [hTt]; omega
  -- the pairwise distinctness
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hdis11_peel hdis
  have hdis10 : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup := hdis10_of_hdis11 hdis
  obtain ⟨hdF1, hdF2, hdt, hdd, hd0⟩ := hdis_notMem hdis10
  have hSX_SY : SX ≠ SY := ne_of_notMem h1 (by simp)
  have hSX_T : SX ≠ T := ne_of_notMem h1 (by simp)
  have hSX_D : SX ≠ D := ne_of_notMem h1 (by simp)
  have hSX_SA : SX ≠ SA := ne_of_notMem h1 (by simp)
  have hSX_SB : SX ≠ SB := ne_of_notMem h1 (by simp)
  have hSX_0 : SX ≠ 0 := ne_of_notMem h1 (by simp)
  have hSX_t : SX ≠ t := ne_of_notMem h1 (by simp)
  have hSX_d : SX ≠ d := ne_of_notMem h1 (by simp)
  have hSY_T : SY ≠ T := ne_of_notMem h2 (by simp)
  have hSY_D : SY ≠ D := ne_of_notMem h2 (by simp)
  have hSY_SA : SY ≠ SA := ne_of_notMem h2 (by simp)
  have hSY_SB : SY ≠ SB := ne_of_notMem h2 (by simp)
  have hSY_0 : SY ≠ 0 := ne_of_notMem h2 (by simp)
  have hSY_t : SY ≠ t := ne_of_notMem h2 (by simp)
  have hSY_d : SY ≠ d := ne_of_notMem h2 (by simp)
  have hT_D : T ≠ D := ne_of_notMem h3 (by simp)
  have hT_SA : T ≠ SA := ne_of_notMem h3 (by simp)
  have hT_SB : T ≠ SB := ne_of_notMem h3 (by simp)
  have hT_0 : T ≠ 0 := ne_of_notMem h3 (by simp)
  have hT_t : T ≠ t := ne_of_notMem h3 (by simp)
  have hT_d : T ≠ d := ne_of_notMem h3 (by simp)
  have hD_SA : D ≠ SA := ne_of_notMem h4 (by simp)
  have hD_SB : D ≠ SB := ne_of_notMem h4 (by simp)
  have hD_0 : D ≠ 0 := ne_of_notMem h4 (by simp)
  have hD_t : D ≠ t := ne_of_notMem h4 (by simp)
  have hD_d : D ≠ d := ne_of_notMem h4 (by simp)
  have hSA_SB : SA ≠ SB := ne_of_notMem h5 (by simp)
  have hSA_0 : SA ≠ 0 := ne_of_notMem h5 (by simp)
  have hSA_t : SA ≠ t := ne_of_notMem h5 (by simp)
  have hSA_d : SA ≠ d := ne_of_notMem h5 (by simp)
  have hSB_0 : SB ≠ 0 := ne_of_notMem h6 (by simp)
  have hSB_t : SB ≠ t := ne_of_notMem h6 (by simp)
  have hSB_d : SB ≠ d := ne_of_notMem h6 (by simp)
  have h0_t : (0 : Stk) ≠ t := (ne_of_notMem h9 (by simp)).symm
  have h0_d : (0 : Stk) ≠ d := (ne_of_notMem h10 (by simp)).symm
  have ht_d : t ≠ d := ne_of_notMem h9 (by simp)
  have hSA_T : SA ≠ T := hT_SA.symm
  have hSB_T : SB ≠ T := hT_SB.symm
  have hSA_D : SA ≠ D := hD_SA.symm
  have hSB_D : SB ≠ D := hD_SB.symm
  have hSA_SY : SA ≠ SY := hSY_SA.symm
  have hSB_SY : SB ≠ SY := hSY_SB.symm
  have hSA_SX : SA ≠ SX := hSX_SA.symm
  have hSB_SX : SB ≠ SX := hSX_SB.symm
  have hSY_SX : SY ≠ SX := hSX_SY.symm
  have hT_SY : T ≠ SY := hSY_T.symm
  have hT_SX : T ≠ SX := hSX_T.symm
  -- (1)-(3): the three boundary markers
  obtain ⟨s1, n1, e1, hn1, hs1T, hfr1, -, -⟩ :=
    pushConst_ev (main := main) (k := T) (cst := gMark) (g := g) (X := S)
  have hT1 : s1.stk T = gMark :: Tc := by rw [hs1T, hT]
  obtain ⟨s2, n2, e2, hn2, hs2SA, hfr2, -, -⟩ :=
    pushConst_ev (main := main) (k := SA) (cst := gMark) (g := s1.reg) (X := s1.stk)
  have hSA2 : s2.stk SA = gMark :: Sc := by rw [hs2SA, hfr1 SA hSA_T, hSA]
  obtain ⟨s3, n3, e3, hn3, hs3SB, hfr3, -, -⟩ :=
    pushConst_ev (main := main) (k := SB) (cst := gMark) (g := s2.reg) (X := s2.stk)
  have hSB3 : s3.stk SB = gMark :: Sc' := by rw [hs3SB, hfr2 SB hSA_SB.symm, hfr1 SB hSB_T, hSB]
  have hSX3 : s3.stk SX = (Val.cons (Val.int (kp : ℤ)) vp).enc ++ (encs ps ++ gMark :: A) := by
    rw [hfr3 SX hSX_SB, hfr2 SX hSX_SA, hfr1 SX hSX_T, hSX, hp]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hSY3 : s3.stk SY = (Val.cons (Val.int (lq : ℤ)) wq).enc ++ (encs qs ++ gMark :: B') := by
    rw [hfr3 SY hSY_SB, hfr2 SY hSY_SA, hfr1 SY hSY_T, hSY, hq]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hSA3 : s3.stk SA = gMark :: Sc := by rw [hfr3 SA hSA_SB, hSA2]
  -- (4) `pushSize SX SA`
  obtain ⟨s4, n4, e4, hn4, hs4SX, hs4SA, hs40, hs4t, hs4d, hfr4⟩ :=
    mrgPushSize (main := main) (pSize := pSz) (KSz := KSz) (hSz := hSz) (S := SX) (SA := SA)
      (t := t) (d := d) (hSSA := hSX_SA) (hS0 := hSX_0) (hSt := hSX_t) (hSd := hSX_d)
      (hSA0 := hSA_0) (hSAt := hSA_t) (hSAd := hSA_d) (h0t := h0_t) (h0d := h0_d)
      (htd := ht_d) (g := s3.reg) (X := s3.stk) (k := kp) (v' := vp)
      (A := encs ps ++ gMark :: A) (Sc := gMark :: Sc) (hS := hSX3) (hSA := hSA3)
  have hSAc4 : s4.stk SA = encs (cache ([] : List Val) (p :: ps)) ++ gMark :: Sc := by
    rw [hs4SA, hp, cache_cons, ksv_record]
    simp only [encs, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.reverse_nil, List.nil_append, List.append_assoc]
  -- (5) `pushSize SY SB`
  have hSB4 : s4.stk SB = gMark :: Sc' := by
    rw [hfr4 SB hSB_SX hSA_SB.symm hSB_0 hSB_t hSB_d, hSB3]
  have hSY4 : s4.stk SY = (Val.cons (Val.int (lq : ℤ)) wq).enc ++ (encs qs ++ gMark :: B') := by
    rw [hfr4 SY hSY_SX hSY_SA hSY_0 hSY_t hSY_d, hSY3]
  obtain ⟨s5, n5, e5, hn5, hs5SY, hs5SB, hs50, hs5t, hs5d, hfr5⟩ :=
    mrgPushSize (main := main) (pSize := pSz) (KSz := KSz) (hSz := hSz) (S := SY) (SA := SB)
      (t := t) (d := d) (hSSA := hSY_SB) (hS0 := hSY_0) (hSt := hSY_t) (hSd := hSY_d)
      (hSA0 := hSB_0) (hSAt := hSB_t) (hSAd := hSB_d) (h0t := h0_t) (h0d := h0_d)
      (htd := ht_d) (g := s4.reg) (X := s4.stk) (k := lq) (v' := wq)
      (A := encs qs ++ gMark :: B') (Sc := gMark :: Sc') (hS := hSY4) (hSA := hSB4)
  have hSBc5 : s5.stk SB = encs (cache ([] : List Val) (q :: qs)) ++ gMark :: Sc' := by
    rw [hs5SB, hq, cache_cons, ksv_record]
    simp only [encs, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.reverse_nil, List.nil_append, List.append_assoc]
  -- (6) arm the loop flag
  obtain ⟨s6, e6, hs6stk, hs6reg⟩ : ∃ s6 : State, Ev main (.set Sk.rF Glyph.cons) s5 s6 1 ∧
      s6.stk = s5.stk ∧ s6.reg Sk.rF = Glyph.cons :=
    ⟨⟨Function.update s5.reg Sk.rF Glyph.cons, s5.stk⟩,
      ev_set' main Sk.rF Glyph.cons s5.reg s5.stk, rfl, by simp⟩
  have hpeel5 : ∀ k, k ≠ SY → k ≠ SB → s5.stk k = s4.stk k := frame_peel3 hfr5 hs50 hs5t hs5d
  have hpeel4 : ∀ k, k ≠ SX → k ≠ SA → s4.stk k = s3.stk k := frame_peel3 hfr4 hs40 hs4t hs4d
  have hpeel3 : ∀ k, k ≠ SB → s3.stk k = s2.stk k := hfr3
  have hpeel2 : ∀ k, k ≠ SA → s2.stk k = s1.stk k := hfr2
  have hpeel1 : ∀ k, k ≠ T → s1.stk k = S k := hfr1
  have hSX6 : s6.stk SX = encs (p :: ps) ++ gMark :: A := by
    rw [hs6stk, hpeel5 SX hSX_SY hSX_SB, hs4SX, hpeel3 SX hSX_SB,
      hpeel2 SX hSX_SA, hpeel1 SX hSX_T, hSX]
  have hSY6 : s6.stk SY = encs (q :: qs) ++ gMark :: B' := by
    rw [hs6stk, hs5SY, hSY4, ← hq]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hT6 : s6.stk T = encs ([] : List Val) ++ gMark :: Tc := by
    rw [hs6stk, hpeel5 T hT_SY hT_SB, hpeel4 T hT_SX hT_SA, hpeel3 T hT_SB,
      hpeel2 T hT_SA, hT1]
    simp only [encs, List.map_nil, List.flatten_nil, List.nil_append]
  have hSA6 : s6.stk SA = encs (cache ([] : List Val) (p :: ps)) ++ gMark :: Sc := by
    rw [hs6stk, hpeel5 SA hSA_SY hSA_SB, hSAc4]
  have hSB6 : s6.stk SB = encs (cache ([] : List Val) (q :: qs)) ++ gMark :: Sc' := by
    rw [hs6stk]
    exact hSBc5
  have h06 : s6.stk 0 = S 0 := by
    rw [hs6stk, hs50, hs40, hpeel3 0 hSB_0.symm, hpeel2 0 hSA_0.symm, hpeel1 0 hT_0.symm]
  have hfr6S : ∀ k', k' ∉ loopTouched SX SY T SA SB → s6.stk k' = S k' := by
    intro k hk
    obtain ⟨e1, e2, e3, e4, e5⟩ := not_mem_loopTouched hk
    rw [hs6stk, hpeel5 k e2 e5, hpeel4 k e1 e4, hpeel3 k e5, hpeel2 k e4, hpeel1 k e3]
  -- (7) the comparison phase
  obtain ⟨k7, P₁7, P₂7, Q₁7, Q₂7, Tk7, s7, n7, hrun7, hcost7, hnil7, hrF7, hP7, hQ7, hM7,
    hSX7, hSY7, hT7, hSA7, hSB7, h07, hfr7⟩ :=
    merge_loopCmp (main := main) (pLt := pLt) (pSize := pSz) (hLt := hLt) (hSz := hSz)
      (hdis := hdis10) (g := s6.reg) (X := s6.stk) (S := S) (P := p :: ps) (Q := q :: qs)
      (P₁ := ([] : List Val)) (P₂ := p :: ps) (Q₁ := ([] : List Val)) (Q₂ := q :: qs)
      (Tk := ([] : List Val)) (hrec := hrecAll) (hP := by simp) (hQ := by simp) (hm := by simp)
      (hSX := hSX6) (hSY := hSY6) (hT := hT6) (hSA := hSA6) (hSB := hSB6) (h0 := h06)
      (hfr := hfr6S) (hg := hs6reg)
  -- the cost of the comparison phase
  have hcmp : ∀ ks ls : List ℕ, (ks ++ ls).Nodup →
      cmpCost ks ls ≤ 20 * (((ks ++ ls).map (fun k => k.size + 2)).sum + ks.length +
        ls.length + 2) := fun ks ls h => merge_cmpCost ks ls h
  have hkeynd : (((p :: ps) ++ (q :: qs)).map keyOf).Nodup :=
    mrg_keyOf_nodup (P := p :: ps) (Q := q :: qs) hrecAll hnd
  have hmrc : mrgCost KLt KSz (p :: ps) (q :: qs) ≤ MRC KLt KSz * Tt := by
    rw [hTt]
    exact merge_mrgCost_le KLt KSz (p :: ps) (q :: qs) hcmp hrecAll hkeynd
  have hkeyp' : vsz (Val.cons (Val.int (kp : ℤ)) vp) + 2 ≤ Tt := by
    have hmem : p ∈ (p :: ps) ++ (q :: qs) := by simp
    have h1 : vsz p ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum :=
      le_sum_map_of_mem _ p hmem
    have h2 : vsz (Val.cons (Val.int (kp : ℤ)) vp) ≤
        (((p :: ps) ++ (q :: qs)).map vsz).sum := by
      rw [← hp]
      exact h1
    rw [hTt]
    omega
  have hkeyq' : vsz (Val.cons (Val.int (lq : ℤ)) wq) + 2 ≤ Tt := by
    have hmem : q ∈ (p :: ps) ++ (q :: qs) := by simp
    have h1 : vsz q ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum :=
      le_sum_map_of_mem _ q hmem
    have h2 : vsz (Val.cons (Val.int (lq : ℤ)) wq) ≤
        (((p :: ps) ++ (q :: qs)).map vsz).sum := by
      rw [← hq]
      exact h1
    rw [hTt]
    omega
  have h4c : n4 ≤ cExp KSz * Tt :=
    le_trans hn4 (le_trans (pushSizeCost_le_cExp' KSz kp vp)
      (Nat.mul_le_mul_left _ hkeyp'))
  have h5c : n5 ≤ cExp KSz * Tt :=
    le_trans hn5 (le_trans (pushSizeCost_le_cExp' KSz lq wq)
      (Nat.mul_le_mul_left _ hkeyq'))
  have h7c : n7 ≤ (MRC KLt KSz + 1) * Tt := by
    have hlen2 : (((p :: ps) ++ (q :: qs))).length ≤ Tt := by rw [hTt]; omega
    have hlen3 : (p :: ps).length + (q :: qs).length ≤ Tt := by
      rw [← List.length_append]
      exact hlen2
    have hexp : (MRC KLt KSz + 1) * Tt = MRC KLt KSz * Tt + Tt := by ring
    rw [hexp]
    omega
  -- (8) the drain phase and the tail
  have hAconv : cache ([] : List Val) (p :: ps) = [ksv p] := by
    rw [cache_cons]; simp
  have hBconv : cache ([] : List Val) (q :: qs) = [ksv q] := by
    rw [cache_cons]; simp
  rcases hnil7 with hP27 | hQ27
  · -- `P₂7 = []`: drain `Q₂7`
    have hrecQ2 : ∀ v ∈ Q₂7, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
      intro v hv
      exact hrecQ v (by rw [hQ7]; exact List.mem_append.mpr (Or.inr hv))
    have hSX7' : s7.stk SX = gMark :: A := by rw [hSX7, hP27]; rfl
    obtain ⟨s8, n8, e8, hn8, h8SX, h8SY, h8T, h8SA, h80, hrF8, hfr8⟩ :=
      merge_drainQ (main := main) (pLt := pLt) (pSize := pSz) (SX := SX) (SY := SY) (T := T)
        (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t) (d := d) (hdis := hdis10)
        (g := s7.reg) (X := s7.stk) (A := A) (B' := B') (Tc := Tc) (R := S 0) (Sc := Sc)
        (CLA := cache P₁7 P₂7) (Tk := Tk7) (Qs := Q₂7) (hrec := hrecQ2) (hg := hrF7)
        (hSX := hSX7') (hSY := hSY7) (hT := hT7) (hSA := hSA7) (h0 := h07)
    have h8SB : s8.stk SB = encs (cache Q₁7 Q₂7) ++ gMark :: Sc' := by
      have hk : SB ∉ ({SX, SY, T} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact hSX_SB h.symm
        · exact hSY_SB h.symm
        · exact hT_SB h.symm
      rw [hfr8 SB hk, hSB7]
    have h8D : s8.stk D = Dc := by
      have hk : D ∉ ({SX, SY, T} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact hSX_D h.symm
        · exact hSY_D h.symm
        · exact hT_D h.symm
      rw [hfr8 D hk,
        hfr7 D (not_mem_loopTouched_of hSX_D.symm hSY_D.symm hT_D.symm hD_SA hD_SB), hD]
    have hloop8 : Ev main (.loop Sk.rF Glyph.cons
        (Sk.mBody pLt pSz SX SY SA SB T F1 F2 t d)) ⟨s6.reg, s6.stk⟩ s8 (n7 + n8 + 1) :=
      merge_loopRuns_eval_pre hrun7 e8
    have hvals : (Q₂7.reverse ++ Tk7).reverse = merge2 (p :: ps) (q :: qs) := by
      rw [List.reverse_append, List.reverse_reverse, hM7, hP27, merge2_nil_left]
    have h8sum : (Q₂7.map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum := by
      have h1 : (Q₂7.map vsz).sum ≤ ((q :: qs).map vsz).sum := by
        have h := sum_append_right_le (l₁ := Q₁7) (l₂ := Q₂7)
        rwa [← hQ7] at h
      have h2 : ((q :: qs).map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum :=
        sum_append_right_le (l₁ := p :: ps) (l₂ := q :: qs)
      omega
    have h8len : Q₂7.length ≤ ((p :: ps) ++ (q :: qs)).length := by
      have h1 : Q₂7.length ≤ (q :: qs).length := by
        have h := length_append_right_le (l₁ := Q₁7) (l₂ := Q₂7)
        rwa [← hQ7] at h
      have h2 : (q :: qs).length ≤ ((p :: ps) ++ (q :: qs)).length :=
        length_append_right_le (l₁ := p :: ps) (l₂ := q :: qs)
      omega
    have h8c : n8 ≤ 30 * Tt := by
      refine le_trans hn8 (Nat.mul_le_mul_left 30 ?_)
      rw [hTt]
      omega
    have hrecV : ∀ v ∈ Q₂7.reverse ++ Tk7, ∃ a b : Val, v = Val.cons a b := by
      intro v hv
      rcases List.mem_append.mp hv with hv1 | hv1
      · obtain ⟨kk, vv, hk⟩ := hrecQ2 v (List.mem_reverse.mp hv1)
        exact ⟨_, _, hk⟩
      · have hv2 : v ∈ merge2 (p :: ps) (q :: qs) := by
          rw [← hvals]
          exact List.mem_reverse.mpr (List.mem_append.mpr (Or.inr hv1))
        obtain ⟨kk, vv, hk⟩ := hrecAll v (merge2_mem (p :: ps) (q :: qs) v hv2)
        exact ⟨_, _, hk⟩
    have hfr8S : ∀ k', k' ≠ SX → k' ≠ SY → k' ≠ T → k' ≠ D → k' ≠ SA → k' ≠ SB →
        s8.stk k' = S k' := by
      intro k i1 i2 i3 i4 i5 i6
      have hk : k ∉ ({SX, SY, T} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hfr8 k hk]
      exact hfr7 k (not_mem_loopTouched_of i1 i2 i3 i5 i6)
    have h8A : ((cache P₁7 P₂7).map vsz).sum ≤ Tt := by
      have hp2 : ∀ v ∈ P₁7 ++ P₂7, ∃ (k : ℕ) (v' : Val),
          v = Val.cons (Val.int (k : ℤ)) v' := by
        intro v hv
        exact hrecAll v (by rw [hP7]; exact List.mem_append.mpr (Or.inl hv))
      have h1 := cache_sum_le P₁7 P₂7 hp2
      have h2 : ((P₁7 ++ P₂7).map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum := by
        rw [← hP7]
        exact sum_append_left_le (l₁ := p :: ps) (l₂ := q :: qs)
      rw [hTt]
      omega
    have h8B : ((cache Q₁7 Q₂7).map vsz).sum ≤ Tt := by
      have hq2 : ∀ v ∈ Q₁7 ++ Q₂7, ∃ (k : ℕ) (v' : Val),
          v = Val.cons (Val.int (k : ℤ)) v' := by
        intro v hv
        exact hrecAll v (by rw [hQ7]; exact List.mem_append.mpr (Or.inr hv))
      have h1 := cache_sum_le Q₁7 Q₂7 hq2
      have h2 : ((Q₁7 ++ Q₂7).map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum := by
        rw [← hQ7]
        exact sum_append_right_le (l₁ := p :: ps) (l₂ := q :: qs)
      rw [hTt]
      omega
    have h8V : ((Q₂7.reverse ++ Tk7).map vsz).sum + (Q₂7.reverse ++ Tk7).length ≤ Tt := by
      have hrev : Q₂7.reverse ++ Tk7 = (merge2 (p :: ps) (q :: qs)).reverse := by
        rw [← hvals, List.reverse_reverse]
      rw [hrev, sum_map_reverse, List.length_reverse, merge2_sum_vsz, mrgMerge2_length, hTt]
      omega
    obtain ⟨s9, n9, e9, hn9, h9SX, h9SY, h9T, h9D, h9SA, h9SB, hfr9⟩ :=
      merge_pair_tail (main := main) (pLt := pLt) (pSize := pSz) (hdis := hdis)
        (g := s8.reg) (X := s8.stk) (S := S) (A := A) (B' := B') (Tc := Tc) (Dc := Dc)
        (Sc := Sc) (Sc' := Sc') (vals := Q₂7.reverse ++ Tk7) (CLA := cache P₁7 P₂7)
        (CLB := cache Q₁7 Q₂7) (BdA := Tt) (BdB := Tt) (BdV := Tt) (hSX := h8SX) (hSY := h8SY)
        (hT := h8T) (hD := h8D) (hSA := h8SA) (hSB := h8SB) (hrec := hrecV) (hSAv := h8A)
        (hSBv := h8B) (hVv := h8V) (hfr := hfr8S)
    have h9c : n9 ≤ 30 * Tt + 49 := by
      have hexp : 5 + 20 * (Tt + 1) + 5 * Tt + 5 * Tt + 24 = 30 * Tt + 49 := by ring
      rw [← hexp]
      exact hn9
    have hcostfin : 2 + 2 + 2 + n4 + n5 + 1 + (n7 + n8 + 1) + n9 ≤ MPc KLt KSz * Tt := by
      have hcoef : 2 * cExp KSz + (MRC KLt KSz + 1) + 30 + 30 + 100 ≤ MPc KLt KSz := by
        simp only [MPc, MRC, cExp, cCmp, cMov, cK]
        omega
      have hA : 2 + 2 + 2 + n4 + n5 + 1 + (n7 + n8 + 1) + n9
          ≤ (2 * cExp KSz + (MRC KLt KSz + 1) + 30 + 30 + 100) * Tt := by
        have hdiff : (2 * cExp KSz + (MRC KLt KSz + 1) + 30 + 30 + 100) * Tt
            = cExp KSz * Tt + cExp KSz * Tt + (MRC KLt KSz + 1) * Tt + 30 * Tt + 30 * Tt
              + 100 * Tt := by ring
        rw [hdiff]
        omega
      exact le_trans hA (Nat.mul_le_mul_right Tt hcoef)
    have hmain0 : Ev main (Sk.mergePair pLt pSz SX SY T D SA SB F1 F2 t d) ⟨g, S⟩ s9
        (2 + (2 + (2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9))))))) := by
      unfold Sk.mergePair
      exact Ev.seq' (C := 2 + (2 + (2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9))))))) (e1.mono (C' := 2) hn1) (Ev.seq' (C := 2 + (2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9)))))) (e2.mono (C' := 2) hn2) (Ev.seq' (C := 2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9))))) (e3.mono (C' := 2) hn3) (Ev.seq' (C := n4 + (n5 + (1 + ((n7 + n8 + 1) + n9)))) e4 (Ev.seq' (C := n5 + (1 + ((n7 + n8 + 1) + n9))) e5 (Ev.seq' (C := 1 + ((n7 + n8 + 1) + n9)) (e6.mono (C' := 1) (by omega)) (Ev.seq' (C := (n7 + n8 + 1) + n9) hloop8 e9 (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)
    have hmain : Ev main (Sk.mergePair pLt pSz SX SY T D SA SB F1 F2 t d) ⟨g, S⟩ s9
        (2 + 2 + 2 + n4 + n5 + 1 + (n7 + n8 + 1) + n9) := hmain0.mono (by omega)
    have h9D' : s9.stk D = encs (merge2 (p :: ps) (q :: qs)) ++ gMark :: Dc := by
      rw [h9D, hvals]
    exact ⟨s9, _, hmain, hcostfin, h9SX, h9SY, h9T, h9D', h9SA, h9SB, hfr9⟩
  · -- `Q₂7 = []`: drain `P₂7`
    have hrecP2 : ∀ v ∈ P₂7, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
      intro v hv
      exact hrecP v (by rw [hP7]; exact List.mem_append.mpr (Or.inr hv))
    have hSY7' : s7.stk SY = gMark :: B' := by rw [hSY7, hQ27]; rfl
    obtain ⟨s8, n8, e8, hn8, h8SX, h8SY, h8T, h8SA, h80, hrF8, hfr8⟩ :=
      merge_drainP (main := main) (pLt := pLt) (pSize := pSz) (SX := SX) (SY := SY) (T := T)
        (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t) (d := d) (hdis := hdis10)
        (g := s7.reg) (X := s7.stk) (A := A) (B' := B') (Tc := Tc) (R := S 0) (Sc := Sc)
        (CLA := cache P₁7 P₂7) (Tk := Tk7) (Ps := P₂7) (hrec := hrecP2) (hg := hrF7)
        (hSX := hSX7) (hSY := hSY7') (hT := hT7) (hSA := hSA7) (h0 := h07)
    have h8SB : s8.stk SB = encs (cache Q₁7 Q₂7) ++ gMark :: Sc' := by
      have hk : SB ∉ ({SX, SY, T} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact hSX_SB h.symm
        · exact hSY_SB h.symm
        · exact hT_SB h.symm
      rw [hfr8 SB hk, hSB7]
    have h8D : s8.stk D = Dc := by
      have hk : D ∉ ({SX, SY, T} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact hSX_D h.symm
        · exact hSY_D h.symm
        · exact hT_D h.symm
      rw [hfr8 D hk,
        hfr7 D (not_mem_loopTouched_of hSX_D.symm hSY_D.symm hT_D.symm hD_SA hD_SB), hD]
    have hloop8 : Ev main (.loop Sk.rF Glyph.cons
        (Sk.mBody pLt pSz SX SY SA SB T F1 F2 t d)) ⟨s6.reg, s6.stk⟩ s8 (n7 + n8 + 1) :=
      merge_loopRuns_eval_pre hrun7 e8
    have hvals : (P₂7.reverse ++ Tk7).reverse = merge2 (p :: ps) (q :: qs) := by
      rw [List.reverse_append, List.reverse_reverse, hM7, hQ27, merge2_nil_right]
    have h8sum : (P₂7.map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum := by
      have h1 : (P₂7.map vsz).sum ≤ ((p :: ps).map vsz).sum := by
        have h := sum_append_right_le (l₁ := P₁7) (l₂ := P₂7)
        rwa [← hP7] at h
      have h2 : ((p :: ps).map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum :=
        sum_append_left_le (l₁ := p :: ps) (l₂ := q :: qs)
      omega
    have h8len : P₂7.length ≤ ((p :: ps) ++ (q :: qs)).length := by
      have h1 : P₂7.length ≤ (p :: ps).length := by
        have h := length_append_right_le (l₁ := P₁7) (l₂ := P₂7)
        rwa [← hP7] at h
      have h2 : (p :: ps).length ≤ ((p :: ps) ++ (q :: qs)).length :=
        length_append_left_le (l₁ := p :: ps) (l₂ := q :: qs)
      omega
    have h8c : n8 ≤ 30 * Tt := by
      refine le_trans hn8 (Nat.mul_le_mul_left 30 ?_)
      rw [hTt]
      omega
    have hrecV : ∀ v ∈ P₂7.reverse ++ Tk7, ∃ a b : Val, v = Val.cons a b := by
      intro v hv
      rcases List.mem_append.mp hv with hv1 | hv1
      · obtain ⟨kk, vv, hk⟩ := hrecP2 v (List.mem_reverse.mp hv1)
        exact ⟨_, _, hk⟩
      · have hv2 : v ∈ merge2 (p :: ps) (q :: qs) := by
          rw [← hvals]
          exact List.mem_reverse.mpr (List.mem_append.mpr (Or.inr hv1))
        obtain ⟨kk, vv, hk⟩ := hrecAll v (merge2_mem (p :: ps) (q :: qs) v hv2)
        exact ⟨_, _, hk⟩
    have hfr8S : ∀ k', k' ≠ SX → k' ≠ SY → k' ≠ T → k' ≠ D → k' ≠ SA → k' ≠ SB →
        s8.stk k' = S k' := by
      intro k i1 i2 i3 i4 i5 i6
      have hk : k ∉ ({SX, SY, T} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hfr8 k hk]
      exact hfr7 k (not_mem_loopTouched_of i1 i2 i3 i5 i6)
    have h8A : ((cache P₁7 P₂7).map vsz).sum ≤ Tt := by
      have hp2 : ∀ v ∈ P₁7 ++ P₂7, ∃ (k : ℕ) (v' : Val),
          v = Val.cons (Val.int (k : ℤ)) v' := by
        intro v hv
        exact hrecAll v (by rw [hP7]; exact List.mem_append.mpr (Or.inl hv))
      have h1 := cache_sum_le P₁7 P₂7 hp2
      have h2 : ((P₁7 ++ P₂7).map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum := by
        rw [← hP7]
        exact sum_append_left_le (l₁ := p :: ps) (l₂ := q :: qs)
      rw [hTt]
      omega
    have h8B : ((cache Q₁7 Q₂7).map vsz).sum ≤ Tt := by
      have hq2 : ∀ v ∈ Q₁7 ++ Q₂7, ∃ (k : ℕ) (v' : Val),
          v = Val.cons (Val.int (k : ℤ)) v' := by
        intro v hv
        exact hrecAll v (by rw [hQ7]; exact List.mem_append.mpr (Or.inr hv))
      have h1 := cache_sum_le Q₁7 Q₂7 hq2
      have h2 : ((Q₁7 ++ Q₂7).map vsz).sum ≤ (((p :: ps) ++ (q :: qs)).map vsz).sum := by
        rw [← hQ7]
        exact sum_append_right_le (l₁ := p :: ps) (l₂ := q :: qs)
      rw [hTt]
      omega
    have h8V : ((P₂7.reverse ++ Tk7).map vsz).sum + (P₂7.reverse ++ Tk7).length ≤ Tt := by
      have hrev : P₂7.reverse ++ Tk7 = (merge2 (p :: ps) (q :: qs)).reverse := by
        rw [← hvals, List.reverse_reverse]
      rw [hrev, sum_map_reverse, List.length_reverse, merge2_sum_vsz, mrgMerge2_length, hTt]
      omega
    obtain ⟨s9, n9, e9, hn9, h9SX, h9SY, h9T, h9D, h9SA, h9SB, hfr9⟩ :=
      merge_pair_tail (main := main) (pLt := pLt) (pSize := pSz) (hdis := hdis)
        (g := s8.reg) (X := s8.stk) (S := S) (A := A) (B' := B') (Tc := Tc) (Dc := Dc)
        (Sc := Sc) (Sc' := Sc') (vals := P₂7.reverse ++ Tk7) (CLA := cache P₁7 P₂7)
        (CLB := cache Q₁7 Q₂7) (BdA := Tt) (BdB := Tt) (BdV := Tt) (hSX := h8SX) (hSY := h8SY)
        (hT := h8T) (hD := h8D) (hSA := h8SA) (hSB := h8SB) (hrec := hrecV) (hSAv := h8A)
        (hSBv := h8B) (hVv := h8V) (hfr := hfr8S)
    have h9c : n9 ≤ 30 * Tt + 49 := by
      have hexp : 5 + 20 * (Tt + 1) + 5 * Tt + 5 * Tt + 24 = 30 * Tt + 49 := by ring
      rw [← hexp]
      exact hn9
    have hcostfin : 2 + 2 + 2 + n4 + n5 + 1 + (n7 + n8 + 1) + n9 ≤ MPc KLt KSz * Tt := by
      have hcoef : 2 * cExp KSz + (MRC KLt KSz + 1) + 30 + 30 + 100 ≤ MPc KLt KSz := by
        simp only [MPc, MRC, cExp, cCmp, cMov, cK]
        omega
      have hA : 2 + 2 + 2 + n4 + n5 + 1 + (n7 + n8 + 1) + n9
          ≤ (2 * cExp KSz + (MRC KLt KSz + 1) + 30 + 30 + 100) * Tt := by
        have hdiff : (2 * cExp KSz + (MRC KLt KSz + 1) + 30 + 30 + 100) * Tt
            = cExp KSz * Tt + cExp KSz * Tt + (MRC KLt KSz + 1) * Tt + 30 * Tt + 30 * Tt
              + 100 * Tt := by ring
        rw [hdiff]
        omega
      exact le_trans hA (Nat.mul_le_mul_right Tt hcoef)
    have hmain0 : Ev main (Sk.mergePair pLt pSz SX SY T D SA SB F1 F2 t d) ⟨g, S⟩ s9
        (2 + (2 + (2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9))))))) := by
      unfold Sk.mergePair
      exact Ev.seq' (C := 2 + (2 + (2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9))))))) (e1.mono (C' := 2) hn1) (Ev.seq' (C := 2 + (2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9)))))) (e2.mono (C' := 2) hn2) (Ev.seq' (C := 2 + (n4 + (n5 + (1 + ((n7 + n8 + 1) + n9))))) (e3.mono (C' := 2) hn3) (Ev.seq' (C := n4 + (n5 + (1 + ((n7 + n8 + 1) + n9)))) e4 (Ev.seq' (C := n5 + (1 + ((n7 + n8 + 1) + n9))) e5 (Ev.seq' (C := 1 + ((n7 + n8 + 1) + n9)) (e6.mono (C' := 1) (by omega)) (Ev.seq' (C := (n7 + n8 + 1) + n9) hloop8 e9 (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)
    have hmain : Ev main (Sk.mergePair pLt pSz SX SY T D SA SB F1 F2 t d) ⟨g, S⟩ s9
        (2 + 2 + 2 + n4 + n5 + 1 + (n7 + n8 + 1) + n9) := hmain0.mono (by omega)
    have h9D' : s9.stk D = encs (merge2 (p :: ps) (q :: qs)) ++ gMark :: Dc := by
      rw [h9D, hvals]
    exact ⟨s9, _, hmain, hcostfin, h9SX, h9SY, h9T, h9D', h9SA, h9SB, hfr9⟩


end Work.Layout
