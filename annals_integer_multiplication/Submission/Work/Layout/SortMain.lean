import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.SortSpecs
import Submission.Work.Layout.SortLoop
import Submission.Work.Layout.Move

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The sorting program: main assembly

`sortProg pLt pSz` = push the boundary markers on stacks 1,2,3,4; `distribute 1 2 7 8`; the two-pass
loop with the `rF` flag (`loopBody`); `assemble 1 9 7 8`; pop the boundaries of 2,3,4.

`sortMain` proves the `WordR` statement from the `Prop`s `ListsSpec`, `DistSpec`, `AsmSpec`,
`Pass2Spec` (which itself only needs the generic merge lemma `MergePairAll`) plus three elementary
list facts (`sortListAux`).  The final file `sortByKeyWord.lean` instantiates all of them with the
corresponding proved lemmas.

Stack indices: `X=1`, `Y=2`, `C=3`, `D=4`, `T1=5`, `T2=6`, `t=7`, `d=8`, `Z=9`, `SA=10`, `SB=11`,
`F1=12`, `F2=13`.
-/

namespace Work.Layout
namespace Sk

open HvdH

/-! ## pure helpers -/

theorem vsz_ofList' (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      have h : ofList (x :: xs) = Val.cons x (ofList xs) := rfl
      rw [h]
      simp only [vsz, Val.enc, List.length_cons, List.length_append]
      rw [show (ofList xs).enc.length = vsz (ofList xs) from rfl, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons, vsz]
      ring

theorem le_four_pow_size (n : ℕ) : n ≤ 4 ^ n.size := by
  have h : n < 2 ^ n.size := Nat.lt_size_self n
  have h2 : 4 ^ n.size = 2 ^ n.size * 2 ^ n.size := by
    rw [show (4:ℕ) = 2 * 2 by norm_num, mul_pow]
  have h3 : 0 < 2 ^ n.size := pow_pos (by norm_num) _
  rw [h2]; nlinarith

theorem totR_append (rs rs' : List (List Val)) : totR (rs ++ rs') = totR rs + totR rs' := by
  simp only [totR, List.flatten_append, List.map_append, List.sum_append, List.length_append]
  omega

theorem totR_cfg_eq (c : Cfg) :
    totR c.1 + totR c.2 = ((c.1 ++ c.2).flatten.map vsz).sum + (c.1 ++ c.2).flatten.length := by
  simp only [totR, List.flatten_append, List.map_append, List.sum_append, List.length_append]
  omega

theorem totR_perm {l l' : List Val} (h : l.Perm l') :
    (l.map vsz).sum + l.length = (l'.map vsz).sum + l'.length := by
  rw [(h.map vsz).sum_eq, h.length_eq]

theorem length_le_flatten_length :
    ∀ (rs : List (List Val)), (∀ r ∈ rs, r ≠ []) → rs.length ≤ rs.flatten.length
  | [] => by simp
  | r :: rs => by
      intro h
      have h1 : 1 ≤ r.length := List.length_pos_iff.mpr (h r (List.mem_cons_self ..))
      have h2 : rs.length ≤ rs.flatten.length :=
        length_le_flatten_length rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

theorem runLen_le_totR (rs : List (List Val)) (h : ∀ r ∈ rs, r ≠ []) : rs.length ≤ totR rs := by
  have h1 := length_le_flatten_length rs h
  simp only [totR]
  omega

/-- a list of length `≤ 1` is `Pairwise` for any relation -/
theorem pairwise_of_length_le_one {l : List Val} (h : l.length ≤ 1) :
    l.Pairwise (fun a b => pairKey a < pairKey b) := by
  match l with
  | [] => simp
  | [_] => simp
  | _ :: _ :: _ => simp at h

/-- flattening a list of at most one run -/
theorem pairwise_flatten_of_length_le_one {rs : List (List Val)}
    (h : ∀ r ∈ rs, r.Pairwise (fun a b => pairKey a < pairKey b)) (hlen : rs.length ≤ 1) :
    rs.flatten.Pairwise (fun a b => pairKey a < pairKey b) := by
  rcases rs with _ | ⟨r, rs'⟩
  · simp
  · rcases rs' with _ | ⟨b, t⟩
    · simpa using h r (by simp)
    · simp at hlen

/-- the arithmetic step of the run-count halving -/
theorem div_halve (N : ℕ) : ((N + 1) / 2 + 1) / 2 ≤ (N + 3) / 4 := by
  have h1 : 2 * ((N + 1) / 2 + 1) ≤ N + 3 := by
    have := Nat.div_mul_le_self (N + 1) 2
    omega
  refine (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr ?_
  calc (((N + 1) / 2 + 1) / 2) * 4 = 2 * (2 * (((N + 1) / 2 + 1) / 2)) := by ring
    _ ≤ 2 * ((N + 1) / 2 + 1) := by
        have := Nat.div_mul_le_self ((N + 1) / 2 + 1) 2
        omega
    _ ≤ N + 3 := h1

/-- the final cost arithmetic of the loop -/
theorem cost_final (P n1 n2 n3 n4 n5 X n8 nF A B : ℕ)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B)
    (h1 : n1 ≤ 2) (h2 : n2 ≤ 2) (h3 : n3 ≤ 2) (h4 : n4 ≤ 2)
    (h5 : n5 ≤ 60 * A) (hX : X ≤ (15 * P + 6) * (A * B))
    (h8 : n8 ≤ 160 * A) (hF : nF ≤ 3) :
    n1 + (n2 + (n3 + (n4 + (n5 + (1 + (X + (n8 + nF))))))) ≤ (20 * P + 2000) * A * B := by
  have hnp : n1 + (n2 + (n3 + n4)) ≤ 8 := by omega
  have hAB1 : 1 ≤ A * B := by have := Nat.mul_le_mul hA1 hB1; simpa using this
  have hAAB : A ≤ A * B := by have := Nat.mul_le_mul_left A hB1; omega
  have h1' : n1 + (n2 + (n3 + n4)) ≤ 8 * (A * B) := by
    have := Nat.mul_le_mul_left 8 hAB1; omega
  have h5' : n5 ≤ 60 * (A * B) := le_trans h5 (Nat.mul_le_mul_left 60 hAAB)
  have h8' : n8 ≤ 160 * (A * B) := le_trans h8 (Nat.mul_le_mul_left 160 hAAB)
  have hF' : nF ≤ 3 * (A * B) := by have := Nat.mul_le_mul_left 3 hAB1; omega
  have hone : 1 ≤ A * B := hAB1
  have hkey : (8:ℕ) * (A * B) + (60 * (A * B) + (1 * (A * B) +
      ((15 * P + 6) * (A * B) + (160 * (A * B) + 3 * (A * B))))) =
      (15 * P + 238) * (A * B) := by ring
  have hmono : (15 * P + 238) * (A * B) ≤ (20 * P + 2000) * (A * B) :=
    Nat.mul_le_mul_right _ (by omega)
  have hassoc : (20 * P + 2000) * (A * B) = (20 * P + 2000) * A * B := by ring
  omega

/-! ## the boundary pushes and the trailing pops -/

/-- push the boundary marker `gBnd` on stacks 1,2,3,4 -/
theorem pushBnds_ev (main : Cmd) (g : Reg → Glyph) (S : Stk → List Glyph) :
    ∃ s' n, Ev main (.seq (pushConst 1 gBnd)
        (.seq (pushConst 2 gBnd) (.seq (pushConst 3 gBnd) (pushConst 4 gBnd)))) ⟨g, S⟩ s' n ∧
      n ≤ 8 ∧ s'.stk 1 = gBnd :: S 1 ∧ s'.stk 2 = gBnd :: S 2 ∧
      s'.stk 3 = gBnd :: S 3 ∧ s'.stk 4 = gBnd :: S 4 ∧
      (∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → s'.stk k = S k) := by
  obtain ⟨s1, n1, h1, hn1, p1, o1, -, -⟩ := pushConst_ev (main := main) (k := 1) (cst := gBnd) (g := g) (X := S)
  obtain ⟨s2, n2, h2, hn2, p2, o2, -, -⟩ := pushConst_ev (main := main) (k := 2) (cst := gBnd) (g := s1.reg) (X := s1.stk)
  obtain ⟨s3, n3, h3, hn3, p3, o3, -, -⟩ := pushConst_ev (main := main) (k := 3) (cst := gBnd) (g := s2.reg) (X := s2.stk)
  obtain ⟨s4, n4, h4, hn4, p4, o4, -, -⟩ := pushConst_ev (main := main) (k := 4) (cst := gBnd) (g := s3.reg) (X := s3.stk)
  refine ⟨s4, n1 + (n2 + (n3 + n4)), ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ev.seq h1 (Ev.seq h2 (Ev.seq h3 h4))
  · rw [o4 1 (by decide), o3 1 (by decide), o2 1 (by decide), p1]
  · rw [o4 2 (by decide), o3 2 (by decide), p2, o1 2 (by decide)]
  · rw [o4 3 (by decide), p3, o2 3 (by decide), o1 3 (by decide)]
  · rw [p4, o3 4 (by decide), o2 4 (by decide), o1 4 (by decide)]
  · intro k hk1 hk2 hk3 hk4
    rw [o4 k hk4, o3 k hk3, o2 k hk2, o1 k hk1]

/-- pop the boundary markers off stacks 2,3,4 -/
theorem popBnds_ev (main : Cmd) {g : Reg → Glyph} {S : Stk → List Glyph} {a b c0 : List Glyph}
    (h2 : S 2 = gBnd :: a) (h3 : S 3 = gBnd :: b) (h4 : S 4 = gBnd :: c0) :
    ∃ s' n, Ev main (.seq (.pop 2 rJ) (.seq (.pop 3 rJ) (.pop 4 rJ))) ⟨g, S⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 2 = a ∧ s'.stk 3 = b ∧ s'.stk 4 = c0 ∧
      (∀ k : Stk, k ≠ 2 → k ≠ 3 → k ≠ 4 → s'.stk k = S k) := by
  have hp2 : Ev main (.pop 2 rJ) ⟨g, S⟩
      ⟨Function.update g rJ gBnd, Function.update S 2 a⟩ 1 := by
    have h := ev_pop main (2 : Stk) rJ (⟨g, S⟩ : State)
    have e : (⟨Function.update g rJ ((S 2).headD Glyph.eos), Function.update S 2 (S 2).tail⟩ : State) =
        ⟨Function.update g rJ gBnd, Function.update S 2 a⟩ := by simp [h2]
    rwa [e] at h
  have hp3 : Ev main (.pop 3 rJ) ⟨Function.update g rJ gBnd, Function.update S 2 a⟩
      ⟨Function.update (Function.update g rJ gBnd) rJ gBnd,
        Function.update (Function.update S 2 a) 3 b⟩ 1 := by
    have h := ev_pop main (3 : Stk) rJ (⟨Function.update g rJ gBnd, Function.update S 2 a⟩ : State)
    have h3' : (Function.update S 2 a) 3 = gBnd :: b := by
      rw [Function.update_of_ne (by decide : (3 : Stk) ≠ 2), h3]
    have e : (⟨Function.update (Function.update g rJ gBnd) rJ (((Function.update S 2 a) 3).headD Glyph.eos),
          Function.update (Function.update S 2 a) 3 ((Function.update S 2 a) 3).tail⟩ : State) =
        ⟨Function.update (Function.update g rJ gBnd) rJ gBnd,
          Function.update (Function.update S 2 a) 3 b⟩ := by simp [h3]
    rwa [e] at h
  have hp4 : Ev main (.pop 4 rJ) ⟨Function.update (Function.update g rJ gBnd) rJ gBnd,
        Function.update (Function.update S 2 a) 3 b⟩
      ⟨Function.update (Function.update (Function.update g rJ gBnd) rJ gBnd) rJ gBnd,
        Function.update (Function.update (Function.update S 2 a) 3 b) 4 c0⟩ 1 := by
    have h := ev_pop main (4 : Stk) rJ
      (⟨Function.update (Function.update g rJ gBnd) rJ gBnd,
        Function.update (Function.update S 2 a) 3 b⟩ : State)
    have h4' : (Function.update (Function.update S 2 a) 3 b) 4 = gBnd :: c0 := by
      rw [Function.update_of_ne (by decide : (4 : Stk) ≠ 3),
        Function.update_of_ne (by decide : (4 : Stk) ≠ 2), h4]
    have e : (⟨Function.update (Function.update (Function.update g rJ gBnd) rJ gBnd) rJ
            (((Function.update (Function.update S 2 a) 3 b) 4).headD Glyph.eos),
          Function.update (Function.update (Function.update S 2 a) 3 b) 4
            ((Function.update (Function.update S 2 a) 3 b) 4).tail⟩ : State) =
        ⟨Function.update (Function.update (Function.update g rJ gBnd) rJ gBnd) rJ gBnd,
          Function.update (Function.update (Function.update S 2 a) 3 b) 4 c0⟩ := by simp [h4]
    rwa [e] at h
  refine ⟨_, 3, Ev.seq hp2 (Ev.seq hp3 hp4), le_rfl, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_self, Function.update_of_ne (by decide : (2 : Stk) ≠ 3),
      Function.update_of_ne (by decide : (2 : Stk) ≠ 4)]
  · simp [Function.update_self, Function.update_of_ne (by decide : (3 : Stk) ≠ 2),
      Function.update_of_ne (by decide : (3 : Stk) ≠ 4)]
  · simp [Function.update_self, Function.update_of_ne (by decide : (4 : Stk) ≠ 2),
      Function.update_of_ne (by decide : (4 : Stk) ≠ 3)]
  · intro k hk2 hk3 hk4
    simp [Function.update_of_ne hk4, Function.update_of_ne hk3, Function.update_of_ne hk2]

/-! ## the loop step -/

/-- the loop step, derived from `Pass2Spec` (this is where `pass2_ev2` is used) -/
theorem loopStep_of_pass2 {main : Cmd} {pLt pSz : Cmd} {KLt KSz : ℕ}
    (hPs2 : Pass2Spec main pLt pSz KLt KSz) (hMPall : MergePairAll main pLt pSz KLt KSz)
    {J1 J2 J3 J4 : List Glyph} {S : Stk → List Glyph}
    (hS3 : S 3 = runEncB ([] : List (List Val)) ++ J3)
    (hS4 : S 4 = runEncB ([] : List (List Val)) ++ J4)
    (hHead : ∀ (rs : List (List Val)) (J : List Glyph), (∀ r ∈ rs, r ≠ []) →
      (∀ v ∈ rs.flatten, ∃ (a b : Val), v = Val.cons a b) →
      ((runEncB rs ++ J).headD Glyph.eos = Glyph.cons ↔ rs ≠ [])) :
    ∀ (L0 : List Val) (c : Cfg) (s : State),
      CfgAll L0 c → LoopInv 1 2 J1 J2 S s c → 2 ≤ cntC c →
      ∃ s', Ev main (loopBody pLt pSz 1 2 3 4 5 6 10 11 12 13 7 8) s s'
          (3 * P2c KLt KSz * (totR c.1 + totR c.2 + 4) + 4) ∧
        LoopInv 1 2 J1 J2 S s' (pass2P c) ∧ CfgAll L0 (pass2P c) := by
  intro L0 c s hok hinv h2
  obtain ⟨ps, qs⟩ := c
  have hinv1 : s.stk 1 = runEncB ps ++ J1 := hinv.1
  have hinv2 : s.stk 2 = runEncB qs ++ J2 := hinv.2.1
  have hfr : ∀ k : Stk, k ≠ 1 → k ≠ 2 → s.stk k = S k := hinv.2.2.2
  have hlen : ps.length = qs.length ∨ ps.length = qs.length + 1 := hok.1.2.2.2.2
  have hne : ∀ r ∈ ps ++ qs, r ≠ [] := hok.1.1
  have hrec : ∀ v ∈ (ps ++ qs).flatten, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
    hok.1.2.1
  have hsort : ∀ r ∈ ps ++ qs, r.Pairwise (fun a b => pairKey a < pairKey b) := hok.1.2.2.1
  have hnd : (((ps ++ qs).flatten).map pairKey).Nodup := hok.1.2.2.2.1
  have hs3 : s.stk 3 = runEncB ([] : List (List Val)) ++ J3 := by
    rw [hfr 3 (by decide) (by decide), hS3]
  have hs4 : s.stk 4 = runEncB ([] : List (List Val)) ++ J4 := by
    rw [hfr 4 (by decide) (by decide), hS4]
  obtain ⟨s1, n1, hev1, hn1, hX1, hY1, hC1, hD1, hfr1, hne1, hperm1, hlen1, hsort1⟩ :=
    hPs2 hMPall (X := 1) (Y := 2) (C := 3) (D := 4) (T1 := 5) (T2 := 6) (SA := 10) (SB := 11)
      (F1 := 12) (F2 := 13) (t := 7) (d := 8) (by decide) (g := s.reg) (S := s.stk)
      (ps := ps) (qs := qs) (JX := J1) (JY := J2) (JC := J3) (JD := J4)
      hinv1 hinv2 hs3 hs4 hlen hne hrec hsort hnd
  have h3 : s1.stk 3 = S 3 := by rw [hC1, hS3]
  have h4 : s1.stk 4 = S 4 := by rw [hD1, hS4]
  have hpeek : Ev main (.peek 2 rF) s1
      ⟨Function.update s1.reg rF ((s1.stk 2).headD Glyph.eos), s1.stk⟩ 1 :=
    ev_peek' main 2 rF s1.reg s1.stk
  have hbody : Ev main (loopBody pLt pSz 1 2 3 4 5 6 10 11 12 13 7 8) s
      ⟨Function.update s1.reg rF ((s1.stk 2).headD Glyph.eos), s1.stk⟩ (n1 + 1) := by
    unfold loopBody
    exact Ev.seq hev1 hpeek
  -- the nonemptiness and record facts of the result
  have hne1' : ∀ r ∈ (pass2R ps qs).1 ++ (pass2R ps qs).2, r ≠ [] := by
    intro r hr
    exact hne1 r hr
  have hrec1 : ∀ v ∈ ((pass2R ps qs).1 ++ (pass2R ps qs).2).flatten,
      ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
    intro v hv
    have hv' : v ∈ (ps ++ qs).flatten := hperm1.mem_iff.mp hv
    exact hrec v hv'
  have hrec1' : ∀ v ∈ ((pass2R ps qs).1 ++ (pass2R ps qs).2).flatten,
      ∃ (a b : Val), v = Val.cons a b := by
    intro v hv
    obtain ⟨k, v', hvk⟩ := hrec1 v hv
    exact ⟨Val.int (k : ℤ), v', hvk⟩
  have hhead1 : ((runEncB (pass2R ps qs).2 ++ J2).headD Glyph.eos = Glyph.cons ↔
      (pass2R ps qs).2 ≠ []) :=
    hHead (pass2R ps qs).2 J2
      (fun r hr => hne1' r (List.mem_append.mpr (Or.inr hr)))
      (fun v hv => hrec1' v (by rw [List.flatten_append]; exact List.mem_append.mpr (Or.inr hv)))
  refine ⟨_, hbody.mono ?_, ?_, ?_⟩
  · -- cost
    have hT : ((ps ++ qs).flatten.map vsz).sum + (ps ++ qs).flatten.length = totR ps + totR qs := by
      rw [← totR_append ps qs]
      rfl
    have hcnt : ps.length + qs.length ≤ totR ps + totR qs := by
      have h1 := runLen_le_totR ps (fun r hr => hne r (List.mem_append.mpr (Or.inl hr)))
      have h2 := runLen_le_totR qs (fun r hr => hne r (List.mem_append.mpr (Or.inr hr)))
      omega
    have := hn1
    rw [hT] at this
    have key : n1 + 1 ≤ 3 * P2c KLt KSz * (totR ps + totR qs + 4) + 4 := by
      have hp : 0 ≤ P2c KLt KSz := Nat.zero_le _
      nlinarith [this, hcnt, hp]
    omega
  · -- LoopInv
    refine ⟨hX1, hY1, ?_, ?_⟩
    · show (Function.update s1.reg rF ((s1.stk 2).headD Glyph.eos)) rF = Glyph.cons ↔
        (pass2R ps qs).2 ≠ []
      rw [Function.update_self, hY1]
      exact hhead1
    · intro k hk1 hk2
      show s1.stk k = S k
      by_cases hk3 : k = 3
      · rw [hk3]; exact h3
      by_cases hk4 : k = 4
      · rw [hk4]; exact h4
      rw [hfr1 k hk1 hk2 hk3 hk4]
      exact hfr k hk1 hk2
  · -- CfgAll
    refine ⟨⟨hne1', hrec1, hsort1, ?_, hlen1⟩, ?_⟩
    · -- CfgNd
      have hp : ((((pass2R ps qs).1 ++ (pass2R ps qs).2).flatten).map pairKey).Perm
          (((ps ++ qs).flatten).map pairKey) := hperm1.map pairKey
      exact hp.nodup_iff.mpr hnd
    · -- Perm of the L0 element list
      exact hperm1.trans hok.2

/-- the loop's count halves (four-fold) every iteration: `pass2_ev`'s length formula -/
theorem hdec_of_lists (hLists : ListsSpec) :
    ∀ c : Cfg, CfgOk c → cntC (pass2P c) ≤ (cntC c + 3) / 4 := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12,
    h13, h14, h15, h16, h17, h18, h19, h20⟩ := hLists
  intro c hok
  obtain ⟨ps, qs⟩ := c
  have hlen : ps.length = qs.length ∨ ps.length = qs.length + 1 := hok.2.2.2.2
  have h := h13 ps qs hlen
  have hcnt2 : cntC (pass2P (ps, qs)) = (pass2R ps qs).1.length + (pass2R ps qs).2.length := rfl
  have hcnt : cntC (ps, qs) = ps.length + qs.length := rfl
  rw [hcnt, hcnt2, h]
  exact div_halve (ps.length + qs.length)

/-! ## the main assembly -/

/-- **the main assembly**: the sorting program is a `WordR` that sorts -/
theorem sortMain (pLt pSz : Cmd) (KLt KSz : ℕ) (hLists : ListsSpec)
    (hDist : ∀ main : Cmd, DistSpec main) (hAsm : ∀ main : Cmd, AsmSpec main)
    (hPs2 : ∀ main : Cmd, Pass2Spec main pLt pSz KLt KSz)
    (hMPall : ∀ main : Cmd, MergePairAll main pLt pSz KLt KSz)
    (hTot : ∀ xs : List Val, totR (altSplit xs).1 + totR (altSplit xs).2 ≤ vsz (ofList xs))
    (hFin : ∀ (xs : List Val) (ps qs : List (List Val)), (ps ++ qs).flatten.Perm xs →
      (ps.flatten.map vsz).sum + ps.flatten.length ≤ (xs.map vsz).sum + xs.length)
    (hHead : ∀ (rs : List (List Val)) (J : List Glyph), (∀ r ∈ rs, r ≠ []) →
      (∀ v ∈ rs.flatten, ∃ (a b : Val), v = Val.cons a b) →
      ((runEncB rs ++ J).headD Glyph.eos = Glyph.cons ↔ rs ≠ [])) :
    ∃ K : ℕ, ∀ (main : Cmd) (xs : List Val),
      (∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = Val.cons (Val.int (k : ℤ)) v) →
      (xs.map pairKey).Nodup →
      WordR main (sortProg pLt pSz)
        (fun vs => ∃ rest, vs = ofList xs :: rest)
        (fun vs out => ∃ rest ys, vs = ofList xs :: rest ∧ out = ofList ys :: rest ∧ ys.Perm xs ∧
          ys.Pairwise fun a b => pairKey a < pairKey b)
        (fun _ => K * (vsz (ofList xs) + 1) * (xs.length.size + 1)) := by
  have hLists' : ListsSpec := hLists
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12,
    h13, h14, h15, h16, h17, h18, h19, h20⟩ := hLists
  refine ⟨20 * P2c KLt KSz + 2000, ?_⟩
  intro main xs hrec hnd
  intro vs hpre s R hstk0
  obtain ⟨rest, rfl⟩ := hpre
  have hstk0' : s.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [hstk0]; simp [encs]
  -- ## the boundary pushes (as four separate words, so that the composite matches `sortProg`)
  obtain ⟨s1, n1, hev1, hn1, p1, o1, -, -⟩ :=
    pushConst_ev (main := main) (k := 1) (cst := gBnd) (g := s.reg) (X := s.stk)
  obtain ⟨s2, n2, hev2, hn2, p2, o2, -, -⟩ :=
    pushConst_ev (main := main) (k := 2) (cst := gBnd) (g := s1.reg) (X := s1.stk)
  obtain ⟨s3, n3, hev3, hn3, p3, o3, -, -⟩ :=
    pushConst_ev (main := main) (k := 3) (cst := gBnd) (g := s2.reg) (X := s2.stk)
  obtain ⟨s4, n4, hev4, hn4, p4, o4, -, -⟩ :=
    pushConst_ev (main := main) (k := 4) (cst := gBnd) (g := s3.reg) (X := s3.stk)
  have hs4_0 : s4.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [o4 0 (by decide), o3 0 (by decide), o2 0 (by decide), o1 0 (by decide)]
    exact hstk0'
  have hs4_1 : s4.stk 1 = runEncB ([] : List (List Val)) ++ s.stk 1 := by
    rw [o4 1 (by decide), o3 1 (by decide), o2 1 (by decide), p1]; rfl
  have hs4_2 : s4.stk 2 = runEncB ([] : List (List Val)) ++ s.stk 2 := by
    rw [o4 2 (by decide), o3 2 (by decide), p2, o1 2 (by decide)]; rfl
  -- ## distribute
  obtain ⟨s5, n5, hev5, hn5, h5_0, h5_1, h5_2, h5_oth⟩ :=
    hDist main (X := 1) (Y := 2) (t := 7) (d := 8) (by decide)
      (g := s4.reg) (S := s4.stk) (xs := xs) (A := encs rest ++ R)
      (J1 := s.stk 1) (J2 := s.stk 2) hs4_0 hs4_1 hs4_2
  -- stacks 3 and 4 keep their boundary form
  have h5_3 : s5.stk 3 = gBnd :: s.stk 3 := by
    rw [h5_oth 3 (by decide) (by decide) (by decide), o4 3 (by decide), p3, o2 3 (by decide),
      o1 3 (by decide)]
  have h5_4 : s5.stk 4 = gBnd :: s.stk 4 := by
    rw [h5_oth 4 (by decide) (by decide) (by decide), p4, o3 4 (by decide), o2 4 (by decide),
      o1 4 (by decide)]
  have hS3 : s5.stk 3 = runEncB ([] : List (List Val)) ++ s.stk 3 := by rw [h5_3]; rfl
  have hS4 : s5.stk 4 = runEncB ([] : List (List Val)) ++ s.stk 4 := by rw [h5_4]; rfl
  -- ## the loop flag
  have hev6 : Ev main (.peek 2 rF) ⟨s5.reg, s5.stk⟩
      ⟨Function.update s5.reg rF ((s5.stk 2).headD Glyph.eos), s5.stk⟩ 1 :=
    ev_peek' main 2 rF s5.reg s5.stk
  -- ## membership helpers
  have memL : ∀ {v : Val}, v ∈ (altSplit xs).1.flatten →
      v ∈ ((altSplit xs).1 ++ (altSplit xs).2).flatten := by
    intro v hv
    rw [List.flatten_append]
    exact List.mem_append.mpr (Or.inl hv)
  have memR : ∀ {v : Val}, v ∈ (altSplit xs).2.flatten →
      v ∈ ((altSplit xs).1 ++ (altSplit xs).2).flatten := by
    intro v hv
    rw [List.flatten_append]
    exact List.mem_append.mpr (Or.inr hv)
  -- ## the initial configuration
  have hsplit_nil : ∀ r ∈ (altSplit xs).1 ++ (altSplit xs).2, r ≠ [] := by
    intro r hr
    have h := h20 xs r hr
    cases r with
    | nil => simp at h
    | cons a t => simp
  have hsplit_rec : ∀ v ∈ ((altSplit xs).1 ++ (altSplit xs).2).flatten,
      ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
    intro v hv
    have hv' : v ∈ xs := (h19 xs).mem_iff.mp hv
    obtain ⟨k, v', hvk⟩ := hrec v hv'
    exact ⟨k, v', hvk⟩
  have hsplit_len : cntC (altSplit xs) = xs.length := by
    show (altSplit xs).1.length + (altSplit xs).2.length = xs.length
    exact h17 xs
  have hc0ok : CfgAll xs (altSplit xs) := by
    refine ⟨⟨hsplit_nil, hsplit_rec, ?_, ?_, h18 xs⟩, h19 xs⟩
    · intro r hr
      exact pairwise_of_length_le_one (by rw [h20 xs r hr])
    · have hp : ((((altSplit xs).1 ++ (altSplit xs).2).flatten).map pairKey).Perm
          ((xs.map pairKey)) := (h19 xs).map pairKey
      exact hp.nodup_iff.mpr hnd
  -- ## the loop invariant at the loop entry
  have hhead0 : ((runEncB (altSplit xs).2 ++ s.stk 2).headD Glyph.eos = Glyph.cons ↔
      (altSplit xs).2 ≠ []) :=
    hHead (altSplit xs).2 (s.stk 2)
      (fun r hr => hsplit_nil r (List.mem_append.mpr (Or.inr hr)))
      (fun v hv => by
        obtain ⟨k, v', hvk⟩ := hsplit_rec v (memR hv)
        exact ⟨Val.int (k : ℤ), v', hvk⟩)
  have hinve : LoopInv 1 2 (s.stk 1) (s.stk 2) s5.stk
      ⟨Function.update s5.reg rF ((s5.stk 2).headD Glyph.eos), s5.stk⟩ (altSplit xs) := by
    refine ⟨h5_1, h5_2, ?_, ?_⟩
    · show (Function.update s5.reg rF ((s5.stk 2).headD Glyph.eos)) rF = Glyph.cons ↔
        (altSplit xs).2 ≠ []
      rw [Function.update_self, h5_2]
      exact hhead0
    · intro k hk1 hk2
      rfl
  -- ## the loop
  set CB : ℕ := 3 * P2c KLt KSz * (totR (altSplit xs).1 + totR (altSplit xs).2 + 4) + 4 with hCB
  have hVstep : ∀ c : Cfg, CfgAll xs c → totR c.1 + totR c.2 ≤
      totR (altSplit xs).1 + totR (altSplit xs).2 := by
    intro c hok
    have h1 := totR_cfg_eq c
    have h2 := totR_perm hok.2
    have h3 := totR_cfg_eq (altSplit xs)
    have h4 := totR_perm (h19 xs)
    omega
  have hstep : ∀ (c : Cfg) (st : State), CfgAll xs c →
      LoopInv 1 2 (s.stk 1) (s.stk 2) s5.stk st c → 2 ≤ cntC c →
      ∃ s', Ev main (loopBody pLt pSz 1 2 3 4 5 6 10 11 12 13 7 8) st s' CB ∧
        LoopInv 1 2 (s.stk 1) (s.stk 2) s5.stk s' (pass2P c) ∧ CfgAll xs (pass2P c) := by
    intro c st hok hinv h2
    obtain ⟨s', hev', hinv', hok'⟩ :=
      loopStep_of_pass2 (hPs2 main) (hMPall main) hS3 hS4 hHead xs c st hok hinv h2
    have hV := hVstep c hok
    have hb : 3 * P2c KLt KSz * (totR c.1 + totR c.2 + 4) + 4 ≤ CB := by
      rw [hCB]
      have h3 : totR c.1 + totR c.2 + 4 ≤ totR (altSplit xs).1 + totR (altSplit xs).2 + 4 := by
        omega
      have h4 := Nat.mul_le_mul_left (3 * P2c KLt KSz) h3
      omega
    exact ⟨s', hev'.mono hb, hinv', hok'⟩
  have hdec := hdec_of_lists hLists'
  obtain ⟨it, s7, hit, hrun, hinv7, hok7, hcnt7, hrf7⟩ :=
    loop_le (main := main) (pLt := pLt) (pSz := pSz) (X := 1) (Y := 2) (C := 3) (D := 4)
      (T1 := 5) (T2 := 6) (SA := 10) (SB := 11) (F1 := 12) (F2 := 13) (t := 7) (d := 8)
      (JX := s.stk 1) (JY := s.stk 2) (S := s5.stk) (CB := CB) (L0 := xs)
      hstep hdec (xs.length.size) (altSplit xs)
      ⟨Function.update s5.reg rF ((s5.stk 2).headD Glyph.eos), s5.stk⟩ hc0ok hinve (by
        rw [hsplit_len]; exact le_four_pow_size xs.length)
  have hevLoop : Ev main (.loop rF Glyph.cons (loopBody pLt pSz 1 2 3 4 5 6 10 11 12 13 7 8))
      ⟨Function.update s5.reg rF ((s5.stk 2).headD Glyph.eos), s5.stk⟩ s7 (it * (CB + 1) + 1) :=
    loopRuns.eval hrun hrf7
  -- ## assemble
  have hqs_nil : (cfgI (altSplit xs) it).2 = [] :=
    CfgOk.nil_of_cnt_le_one hok7.1 hcnt7
  have hrs_le : (cfgI (altSplit xs) it).1.length ≤ 1 := by
    have hcnt7' : cntC (cfgI (altSplit xs) it) =
        (cfgI (altSplit xs) it).1.length + (cfgI (altSplit xs) it).2.length := rfl
    rw [hcnt7', hqs_nil] at hcnt7
    omega
  have h7_0 : s7.stk 0 = encs rest ++ R := by
    rw [hinv7.2.2.2 0 (by decide) (by decide)]
    exact h5_0
  have h7_1 : s7.stk 1 = runEncB (cfgI (altSplit xs) it).1 ++ s.stk 1 := hinv7.1
  have h7_2 : s7.stk 2 = gBnd :: s.stk 2 := by
    rw [hinv7.2.1, hqs_nil]; rfl
  have hps_ne : ∀ r ∈ (cfgI (altSplit xs) it).1, r ≠ [] := by
    intro r hr
    exact hok7.1.1 r (by simpa [hqs_nil] using hr)
  have hps_rec : ∀ v ∈ (cfgI (altSplit xs) it).1.flatten, ∃ (a b : Val), v = Val.cons a b := by
    intro v hv
    obtain ⟨k, v', hvk⟩ := hok7.1.2.1 v (by simpa [hqs_nil] using hv)
    exact ⟨Val.int (k : ℤ), v', hvk⟩
  obtain ⟨s8, n8, hev8, hn8, h8_0, h8_1, h8_oth⟩ :=
    hAsm main (X := 1) (Z := 9) (t := 7) (d := 8) (by decide)
      (g := s7.reg) (S := s7.stk) (rs := (cfgI (altSplit xs) it).1) (J := s.stk 1)
      (R := encs rest ++ R) h7_1 hrs_le hps_rec hps_ne h7_0
  have h8_2 : s8.stk 2 = gBnd :: s.stk 2 := by
    rw [h8_oth 2 (by decide) (by decide), h7_2]
  have h8_3 : s8.stk 3 = gBnd :: s.stk 3 := by
    rw [h8_oth 3 (by decide) (by decide), hinv7.2.2.2 3 (by decide) (by decide), hS3]
    rfl
  have h8_4 : s8.stk 4 = gBnd :: s.stk 4 := by
    rw [h8_oth 4 (by decide) (by decide), hinv7.2.2.2 4 (by decide) (by decide), hS4]
    rfl
  -- ## the trailing pops
  obtain ⟨sF, nF, hevF, hnF, hF_2, hF_3, hF_4, hF_oth⟩ :=
    popBnds_ev main (g := s8.reg) (S := s8.stk) h8_2 h8_3 h8_4
  -- ## the composite evaluation
  have hevAll : Ev main (sortProg pLt pSz) s sF
      (n1 + (n2 + (n3 + (n4 + (n5 + (1 + ((it * (CB + 1) + 1) + (n8 + nF)))))))) :=
    Ev.seq hev1 (Ev.seq hev2 (Ev.seq hev3 (Ev.seq hev4
      (Ev.seq hev5 (Ev.seq hev6 (Ev.seq hevLoop (Ev.seq hev8 hevF)))))))
  obtain ⟨n, heval, hcost⟩ := hevAll
  -- ## cost bookkeeping
  have hV : totR (altSplit xs).1 + totR (altSplit xs).2 ≤ vsz (ofList xs) := hTot xs
  have hsum : ((cfgI (altSplit xs) it).1.flatten.map vsz).sum +
      (cfgI (altSplit xs) it).1.flatten.length ≤ (xs.map vsz).sum + xs.length := by
    have hp : ((cfgI (altSplit xs) it).1 ++ (cfgI (altSplit xs) it).2).flatten.Perm xs := hok7.2
    rw [hqs_nil] at hp
    exact hFin xs (cfgI (altSplit xs) it).1 [] (by simpa using hp)
  have hcost' : n ≤ (20 * P2c KLt KSz + 2000) * (vsz (ofList xs) + 1) * (xs.length.size + 1) := by
    have hA1 : 1 ≤ vsz (ofList xs) + 1 := by
      have := one_le_vsz (ofList xs); omega
    have hB1 : 1 ≤ xs.length.size + 1 := by omega
    have hT4 : totR (altSplit xs).1 + totR (altSplit xs).2 + 4 ≤ 5 * (vsz (ofList xs) + 1) := by
      have := hV; omega
    have hCB2 : CB + 2 ≤ (15 * P2c KLt KSz + 6) * (vsz (ofList xs) + 1) := by
      rw [hCB]
      have h1 := Nat.mul_le_mul_left (3 * P2c KLt KSz) hT4
      have h2 : (6 : ℕ) ≤ 6 * (vsz (ofList xs) + 1) := by
        have := Nat.mul_le_mul_left 6 hA1; omega
      have h3 : 3 * P2c KLt KSz * (5 * (vsz (ofList xs) + 1)) + 6 * (vsz (ofList xs) + 1) =
          (15 * P2c KLt KSz + 6) * (vsz (ofList xs) + 1) := by ring
      omega
    have hitB : it ≤ xs.length.size + 1 := by omega
    have hloop : it * (CB + 1) + 1 ≤ (15 * P2c KLt KSz + 6) *
        ((vsz (ofList xs) + 1) * (xs.length.size + 1)) := by
      have e1 := Nat.mul_le_mul_right (CB + 1) hitB
      have e2 : (xs.length.size + 1) * (CB + 1) + (xs.length.size + 1) =
          (xs.length.size + 1) * (CB + 2) := by ring
      have e3 := Nat.mul_le_mul_left (xs.length.size + 1) hCB2
      have e4 : (xs.length.size + 1) * ((15 * P2c KLt KSz + 6) * (vsz (ofList xs) + 1)) =
          (15 * P2c KLt KSz + 6) * ((vsz (ofList xs) + 1) * (xs.length.size + 1)) := by ring
      omega
    have h8' : n8 ≤ 160 * (vsz (ofList xs) + 1) := by
      have h1 : ((cfgI (altSplit xs) it).1.flatten.map vsz).sum +
          (cfgI (altSplit xs) it).1.flatten.length + 2 ≤ vsz (ofList xs) + 1 := by
        have hv := vsz_ofList' xs
        omega
      have := hn8
      omega
    exact le_trans hcost (cost_final (P2c KLt KSz) n1 n2 n3 n4 n5 (it * (CB + 1) + 1) n8 nF
      (vsz (ofList xs) + 1) (xs.length.size + 1) hA1 hB1 hn1 hn2 hn3 hn4 hn5 hloop h8' hnF)
  -- ## the final state facts
  have hsp : (cfgI (altSplit xs) it).1.flatten.Pairwise (fun a b => pairKey a < pairKey b) :=
    pairwise_flatten_of_length_le_one
      (fun r hr => hok7.1.2.2.1 r (by simpa [hqs_nil] using hr)) hrs_le
  have hsperm : (cfgI (altSplit xs) it).1.flatten.Perm xs := by
    have hp : ((cfgI (altSplit xs) it).1 ++ (cfgI (altSplit xs) it).2).flatten.Perm xs := hok7.2
    rw [hqs_nil] at hp
    simpa using hp
  refine ⟨ofList ((cfgI (altSplit xs) it).1.flatten) :: rest, sF, n,
    ⟨rest, (cfgI (altSplit xs) it).1.flatten, rfl, rfl, hsperm, hsp⟩, heval, hcost', ?_, ?_⟩
  · -- stack 0
    rw [hF_oth 0 (by decide) (by decide) (by decide), h8_0]
    simp [encs]
  · -- the frame
    intro k hk0
    by_cases hk1 : k = 1
    · rw [hk1, hF_oth 1 (by decide) (by decide) (by decide), h8_1]
    by_cases hk2 : k = 2
    · rw [hk2, hF_2]
    by_cases hk3 : k = 3
    · rw [hk3, hF_3]
    by_cases hk4 : k = 4
    · rw [hk4, hF_4]
    · rw [hF_oth k hk2 hk3 hk4, h8_oth k hk1 hk0,
        hinv7.2.2.2 k hk1 hk2,
        h5_oth k hk0 hk1 hk2,
        o4 k hk4, o3 k hk3, o2 k hk2, o1 k hk1]

end Sk
end Work.Layout
