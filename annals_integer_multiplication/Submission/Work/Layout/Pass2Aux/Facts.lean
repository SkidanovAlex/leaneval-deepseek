import Mathlib
import Submission.Work.Layout.Pass2Aux
import Submission.Work.Layout.drainValsEv
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Facts about `merge2`, the `moveRun` word, and the `pass` potential

* `mergeFacts` : the pure list theory of `Sk.merge2` (permutation, length, nonemptiness, sortedness,
  distinct keys, and its effect on `runsz`);
* `moveRunEv` : `Sk.moveRun` moves the top run of a stack onto another stack, at cost
  `≤ 50 * (runsz r + 1)`;
* `passWBound` : the potential `passW` is bounded by the target expression (with a factor `50 * K`).
-/

namespace Work.Layout

open HvdH
open scoped List

/-! ## `Sk.merge2` -/

theorem merge2_perm : ∀ P Q : List Val, (Sk.merge2 P Q).Perm (P ++ Q) := by
  intro P
  induction P with
  | nil => intro Q; simp [Sk.merge2]
  | cons p ps ihP =>
    intro Q
    induction Q with
    | nil => simp [Sk.merge2]
    | cons q qs ihQ =>
      by_cases hc : pairKey q < pairKey p
      · simp only [Sk.merge2, if_pos hc]
        exact List.perm_cons_append_cons q ihQ
      · simp only [Sk.merge2, if_neg hc]
        exact List.Perm.cons p (ihP (q :: qs))

theorem merge2_length : ∀ P Q : List Val, (Sk.merge2 P Q).length = P.length + Q.length := by
  intro P
  induction P with
  | nil => intro Q; simp [Sk.merge2]
  | cons p ps ihP =>
    intro Q
    induction Q with
    | nil => simp [Sk.merge2]
    | cons q qs ihQ =>
      by_cases hc : pairKey q < pairKey p
      · simp only [Sk.merge2, if_pos hc, List.length_cons, ihQ]
        omega
      · simp only [Sk.merge2, if_neg hc, List.length_cons, ihP]
        omega

theorem merge2_ne_nil (P Q : List Val) (h : P ≠ []) : Sk.merge2 P Q ≠ [] := by
  intro hnil
  have hlen := merge2_length P Q
  rw [hnil] at hlen
  simp only [List.length_nil] at hlen
  rcases P with _ | ⟨p, ps⟩
  · exact absurd rfl h
  · simp only [List.length_cons, Nat.add_eq_zero_iff] at hlen
    omega

theorem merge2_sorted : ∀ P Q : List Val,
    P.Pairwise (fun a b => pairKey a < pairKey b) →
    Q.Pairwise (fun a b => pairKey a < pairKey b) →
    ((P ++ Q).map pairKey).Nodup →
    (Sk.merge2 P Q).Pairwise (fun a b => pairKey a < pairKey b) := by
  intro P
  induction P with
  | nil => intro Q _ hq _; simpa [Sk.merge2] using hq
  | cons p ps ihP =>
    intro Q
    induction Q with
    | nil => intro hp _ _; simpa [Sk.merge2] using hp
    | cons q qs ihQ =>
      intro hp hq hnd
      obtain ⟨hp1, hp2⟩ := List.pairwise_cons.mp hp
      obtain ⟨hq1, hq2⟩ := List.pairwise_cons.mp hq
      have hndA : (pairKey p :: (ps ++ q :: qs).map pairKey).Nodup := by
        simpa only [List.cons_append, List.map_cons] using hnd
      obtain ⟨hp_nmem, hnd_rest⟩ := List.nodup_cons.mp hndA
      have hpq_ne : pairKey p ≠ pairKey q := by
        intro h
        refine hp_nmem (h ▸ List.mem_map_of_mem (f := pairKey)
          (List.mem_append_right ps (List.mem_cons_self (a := q))))
      by_cases hc : pairKey q < pairKey p
      · simp only [Sk.merge2, if_pos hc]
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro x hx
          have hx' : x ∈ (p :: ps) ++ qs := (merge2_perm (p :: ps) qs).mem_iff.mp hx
          rcases List.mem_append.mp hx' with hx'' | hx''
          · rcases List.mem_cons.mp hx'' with hpx | hmem
            · rw [hpx]; exact hc
            · exact lt_trans hc (hp1 x hmem)
          · exact hq1 x hx''
        · have hsub : ((p :: ps) ++ qs).Sublist ((p :: ps) ++ (q :: qs)) :=
            List.cons_sublist_cons.mpr
              (List.Sublist.append_left (List.sublist_cons_self q qs) ps)
          have hnd' : (((p :: ps) ++ qs).map pairKey).Nodup :=
            List.Sublist.nodup (hsub.map pairKey) hnd
          exact ihQ hp hq2 hnd'
      · have hpq_lt : pairKey p < pairKey q := by omega
        simp only [Sk.merge2, if_neg hc]
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro x hx
          have hx' : x ∈ ps ++ (q :: qs) := (merge2_perm ps (q :: qs)).mem_iff.mp hx
          rcases List.mem_append.mp hx' with hx'' | hx''
          · exact hp1 x hx''
          · rcases List.mem_cons.mp hx'' with hqx | hmem
            · rw [hqx]; exact hpq_lt
            · exact lt_trans hpq_lt (hq1 x hmem)
        · exact ihP (q :: qs) hp2 hq hnd_rest

theorem merge2_nodup (P Q : List Val) (h : ((P ++ Q).map pairKey).Nodup) :
    ((Sk.merge2 P Q).map pairKey).Nodup :=
  ((merge2_perm P Q).map pairKey).nodup_iff.mpr h

theorem merge2_runsz (P Q : List Val) : runsz (Sk.merge2 P Q) = runsz P + runsz Q := by
  have h1 := merge2_perm P Q
  have h2 : (Sk.merge2 P Q).length = P.length + Q.length := merge2_length P Q
  have h3 : ((Sk.merge2 P Q).map vsz).sum = ((P ++ Q).map vsz).sum := (h1.map vsz).sum_eq
  simp only [runsz, List.map_append, List.sum_append, List.length_append] at h2 h3 ⊢
  omega

/-- the pure list theory of `Sk.merge2` -/
theorem mergeFacts :
    (∀ P Q : List Val, (Sk.merge2 P Q).Perm (P ++ Q)) ∧
    (∀ P Q : List Val, (Sk.merge2 P Q).length = P.length + Q.length) ∧
    (∀ P Q : List Val, P ≠ [] → Sk.merge2 P Q ≠ []) ∧
    (∀ P Q : List Val,
      P.Pairwise (fun a b => pairKey a < pairKey b) →
      Q.Pairwise (fun a b => pairKey a < pairKey b) →
      ((P ++ Q).map pairKey).Nodup →
      (Sk.merge2 P Q).Pairwise (fun a b => pairKey a < pairKey b)) ∧
    (∀ P Q : List Val, ((P ++ Q).map pairKey).Nodup →
      ((Sk.merge2 P Q).map pairKey).Nodup) ∧
    (∀ P Q : List Val, runsz (Sk.merge2 P Q) = runsz P + runsz Q) :=
  ⟨merge2_perm, merge2_length, merge2_ne_nil, merge2_sorted, merge2_nodup, merge2_runsz⟩

/-! ## The potential `passW` -/

theorem runsz_reverse (r : List Val) : runsz r.reverse = runsz r := by
  have h1 : (r.reverse.map vsz).sum = (r.map vsz).sum :=
    ((List.reverse_perm r).map vsz).sum_eq
  have h2 : r.reverse.length = r.length := List.length_reverse
  simp only [runsz, h1, h2]

theorem runsz_pos (r : List Val) : 1 ≤ runsz r + 1 := by omega

theorem mergeW_bound (ps qs : List (List Val)) :
    mergeW ps qs ≤ totL ps + totL qs + 2 * (ps.length + qs.length) := by
  induction ps generalizing qs with
  | nil => simp [mergeW]
  | cons p ps ih =>
    cases qs with
    | nil => simp [mergeW]
    | cons q qs =>
      have h1 : mergeW (p :: ps) (q :: qs) = mergeCost p q + mergeW ps qs := by simp [mergeW]
      have h2 : mergeCost p q = runsz p + runsz q + 2 := by simp
      have h3 := ih qs
      have h4 : totL (p :: ps) = runsz p + totL ps := totL_cons p ps
      have h5 : totL (q :: qs) = runsz q + totL qs := totL_cons q qs
      rw [h1, h2, h4, h5, List.length_cons, List.length_cons]
      omega

theorem leftW_bound (ps qs : List (List Val)) : leftW ps qs ≤ totL ps + ps.length := by
  induction ps generalizing qs with
  | nil => simp [leftW]
  | cons p ps ih =>
    cases qs with
    | nil =>
      rw [leftW_cons_nil, totL_cons, List.length_cons]
      have h := ih ([] : List (List Val))
      omega
    | cons q qs =>
      rw [leftW_cons_cons, totL_cons, List.length_cons]
      have h := ih qs
      omega

theorem passWBound {K : ℕ} (hK : 4000 ≤ K) (ps qs : List (List Val)) :
    passW K ps qs ≤ 50 * K * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) := by
  have h1 : mergeW ps qs ≤ totL (ps ++ qs) + 2 * (ps.length + qs.length) := by
    have h := mergeW_bound ps qs
    rw [← totL_append] at h
    omega
  have h2 : leftW ps qs ≤ totL (ps ++ qs) + (ps.length + qs.length) := by
    have h := leftW_bound ps qs
    have h3 : totL ps ≤ totL (ps ++ qs) := by rw [totL_append]; omega
    omega
  have hm : K * mergeW ps qs ≤ K * (totL (ps ++ qs) + 2 * (ps.length + qs.length)) :=
    Nat.mul_le_mul_left K h1
  have hl : 60 * leftW ps qs ≤ 60 * (totL (ps ++ qs) + (ps.length + qs.length)) :=
    Nat.mul_le_mul_left 60 h2
  have hq : 60 * (qs.length + 1) + 60 ≤ 60 * (ps.length + qs.length + 2) := by
    have hle : qs.length + 2 ≤ ps.length + qs.length + 2 := by omega
    have heq : 60 * (qs.length + 1) + 60 = 60 * (qs.length + 2) := by ring
    rw [heq]
    exact Nat.mul_le_mul_left 60 hle
  have key : passW K ps qs
      ≤ K * (totL (ps ++ qs) + 2 * (ps.length + qs.length))
        + 60 * (totL (ps ++ qs) + (ps.length + qs.length))
        + 60 * (ps.length + qs.length + 2) := by
    unfold passW
    nlinarith [hm, hl, hq]
  have hfin : K * (totL (ps ++ qs) + 2 * (ps.length + qs.length))
      + 60 * (totL (ps ++ qs) + (ps.length + qs.length))
      + 60 * (ps.length + qs.length + 2)
      ≤ 50 * K * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) := by
    nlinarith [hK]
  exact le_trans key hfin

/-! ## `Sk.moveRun` -/

/-- `Sk.moveRun S D T t d` moves the top run of `S` (which must be nonempty and made of `cons`-values)
onto `D`, restoring `T`, `t` and `d`, at cost `≤ 50 * (runsz r + 1)`. -/
theorem moveRunEv {main : Cmd} {S D T t d : Stk} (hSD : S ≠ D) (hST : S ≠ T)
    (hSt : S ≠ t) (hSd : S ≠ d) (hDT : D ≠ T) (hDt : D ≠ t) (hDd : D ≠ d) (hTt : T ≠ t)
    (hTd : T ≠ d) (htd : t ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph} {r : List Val}
    {JS JD : List Glyph} (hne : r ≠ [])
    (hcons : ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b)
    (hS : X S = encs r ++ gMark :: JS) (hD : X D = JD) :
    ∃ s' n, Ev main (Sk.moveRun S D T t d) ⟨g, X⟩ s' n ∧ n ≤ 50 * (runsz r + 1) ∧
      s'.stk S = JS ∧ s'.stk D = encs r ++ gMark :: JD ∧
      s'.stk T = X T ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ S → k ≠ D → k ≠ T → k ≠ t → k ≠ d → s'.stk k = X k) := by
  -- step 1: push the boundary marker on `T`
  obtain ⟨s1, n1, hev1, hn1, hT1, hfr1, -, -⟩ :=
    pushConst_ev (main := main) (k := T) (cst := gMark) (g := g) (X := X)
  have ht1 : s1.stk t = X t := hfr1 t hTt.symm
  have hd1 : s1.stk d = X d := hfr1 d hTd.symm
  have hS1 : s1.stk S = encs r ++ gMark :: JS := by rw [hfr1 S hST]; exact hS
  have hD1 : s1.stk D = JD := by rw [hfr1 D hDT]; exact hD
  -- step 2: drain `S` onto `T`
  obtain ⟨s2, n2, hev2, hn2, hS2, hT2, ht2, hd2, hfr2⟩ :=
    drainValsEv (main := main) (S := S) (T := T) (t := t) (d := d) hST hSt hSd hTt hTd htd
      hcons hS1 hT1
  -- step 3: remove the run marker of `S`
  set s3 : State := ⟨Function.update s2.reg Sk.rJ ((s2.stk S).headD Glyph.eos),
      Function.update s2.stk S (s2.stk S).tail⟩ with hs3
  have hpop1 : Ev main (.pop S Sk.rJ) s2 s3 1 := by
    rw [hs3]; exact ev_pop main S Sk.rJ s2
  have hS3 : s3.stk S = JS := by
    show (Function.update s2.stk S (s2.stk S).tail) S = JS
    rw [Function.update_self, hS2]
    rfl
  have hT3 : s3.stk T = encs r.reverse ++ gMark :: X T := by
    show (Function.update s2.stk S (s2.stk S).tail) T = encs r.reverse ++ gMark :: X T
    rw [Function.update_of_ne hST.symm, hT2]
  have ht3 : s3.stk t = X t := by
    show (Function.update s2.stk S (s2.stk S).tail) t = X t
    rw [Function.update_of_ne hSt.symm, ht2, ht1]
  have hd3 : s3.stk d = X d := by
    show (Function.update s2.stk S (s2.stk S).tail) d = X d
    rw [Function.update_of_ne hSd.symm, hd2, hd1]
  have hD3 : s3.stk D = JD := by
    show (Function.update s2.stk S (s2.stk S).tail) D = JD
    rw [Function.update_of_ne hSD.symm, hfr2 D hSD.symm hDT hDt hDd, hD1]
  have hfr3 : ∀ k : Stk, k ≠ S → s3.stk k = s2.stk k := by
    intro k hk
    show (Function.update s2.stk S (s2.stk S).tail) k = s2.stk k
    rw [Function.update_of_ne hk]
  -- step 4: push the boundary marker on `D`
  obtain ⟨s4, n4, hev4, hn4, hD4, hfr4, -, -⟩ :=
    pushConst_ev (main := main) (k := D) (cst := gMark) (g := s3.reg) (X := s3.stk)
  have hT4 : s4.stk T = encs r.reverse ++ gMark :: X T := by
    rw [hfr4 T hDT.symm, hT3]
  have hD4' : s4.stk D = gMark :: JD := by rw [hD4, hD3]
  have ht4 : s4.stk t = X t := by rw [hfr4 t hDt.symm, ht3]
  have hd4 : s4.stk d = X d := by rw [hfr4 d hDd.symm, hd3]
  -- step 5: drain `T` onto `D`
  have hconsR : ∀ v ∈ r.reverse, ∃ a b : Val, v = Val.cons a b :=
    fun v hv => hcons v (List.mem_reverse.mp hv)
  obtain ⟨s5, n5, hev5, hn5, hT5, hD5, ht5, hd5, hfr5⟩ :=
    drainValsEv (main := main) (S := T) (T := D) (t := t) (d := d) hDT.symm hTt hTd hDt hDd htd
      hconsR hT4 hD4'
  have ht5' : s5.stk t = X t := ht5.trans ht4
  have hd5' : s5.stk d = X d := hd5.trans hd4
  -- step 6: remove the accumulator marker of `T`
  set s6 : State := ⟨Function.update s5.reg Sk.rJ ((s5.stk T).headD Glyph.eos),
      Function.update s5.stk T (s5.stk T).tail⟩ with hs6
  have hpop2 : Ev main (.pop T Sk.rJ) s5 s6 1 := by
    rw [hs6]; exact ev_pop main T Sk.rJ s5
  have hT6 : s6.stk T = X T := by
    show (Function.update s5.stk T (s5.stk T).tail) T = X T
    rw [Function.update_self, hT5]
    rfl
  have hfr6 : ∀ k : Stk, k ≠ T → s6.stk k = s5.stk k := by
    intro k hk
    show (Function.update s5.stk T (s5.stk T).tail) k = s5.stk k
    rw [Function.update_of_ne hk]
  -- assemble
  have hmain : Ev main (Sk.moveRun S D T t d) ⟨g, X⟩ s6
      (n1 + (n2 + (1 + (n4 + (n5 + 1))))) := by
    unfold Sk.moveRun Sk.outRun
    exact Ev.seq hev1 (Ev.seq hev2 (Ev.seq hpop1 (Ev.seq hev4 (Ev.seq hev5 hpop2))))
  refine ⟨s6, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have h1 : n1 ≤ 2 := hn1
    have h2 : n2 ≤ 20 * ((r.map vsz).sum + r.length + 1) := hn2
    have h4 : n4 ≤ 2 := hn4
    have h5 : n5 ≤ 20 * ((r.reverse.map vsz).sum + r.reverse.length + 1) := hn5
    have hr0 : (r.map vsz).sum + r.length = runsz r := rfl
    have hr : (r.reverse.map vsz).sum + r.reverse.length = runsz r := by
      rw [← runsz_reverse r]; rfl
    omega
  · -- `S`
    rw [hfr6 S hST, hfr5 S hST hSD hSt hSd, hfr4 S hSD, hS3]
  · -- `D`
    rw [hfr6 D hDT, hD5, List.reverse_reverse]
  · exact hT6
  · rw [hfr6 t hTt.symm, ht5']
  · rw [hfr6 d hTd.symm, hd5']
  · -- frame
    intro k hkS hkD hkT hkt hkd
    rw [hfr6 k hkT, hfr5 k hkT hkD hkt hkd, hfr4 k hkD, hfr3 k hkS, hfr2 k hkS hkT hkt hkd,
      hfr1 k hkT]

/-- the cost of the mark comparison in the small cases -/
theorem passW_single_nil (K : ℕ) (p : List Val) : passW K [p] [] = 60 * (runsz p + 1) + 120 := by
  have h1 : mergeW [p] ([] : List (List Val)) = 0 := by simp [mergeW]
  have h2 : leftW [p] ([] : List (List Val)) = runsz p + 1 := by simp [leftW]
  simp only [passW, h1, h2, List.length_nil]
  ring

theorem passW_single_single (K : ℕ) (p q : List Val) :
    passW K [p] [q] = K * mergeCost p q + 180 := by
  have h1 : mergeW [p] [q] = mergeCost p q := by simp [mergeW]
  have h2 : leftW [p] [q] = 0 := by simp [leftW]
  simp only [passW, h1, h2, List.length_cons, List.length_nil]

theorem passW_two_single (K : ℕ) (p p' q : List Val) :
    passW K [p, p'] [q] = K * mergeCost p q + 60 * (runsz p' + 1) + 180 := by
  have h1 : mergeW [p, p'] [q] = mergeCost p q := by simp [mergeW]
  have h2 : leftW [p, p'] [q] = runsz p' + 1 := by simp [leftW]
  simp only [passW, h1, h2, List.length_cons, List.length_nil]

theorem passW_two_two (K : ℕ) (p p' q q' : List Val) :
    passW K [p, p'] [q, q'] = K * (mergeCost p q + mergeCost p' q') + 240 := by
  have h := passW_step K p p' ([] : List (List Val)) q q' ([] : List (List Val))
  rw [h, passW_nil_nil]

theorem passW_three_two (K : ℕ) (p p' p'' q q' : List Val) :
    passW K [p, p', p''] [q, q']
      = K * (mergeCost p q + mergeCost p' q') + 60 * (runsz p'' + 1) + 240 := by
  have h := passW_step K p p' [p''] q q' ([] : List (List Val))
  rw [h, passW_single_nil]
  ring

/-- the top glyph of an `encs`-prefixed list whose first run is nonempty with `cons`-values -/
theorem headD_encs_cons_p2 {r : List Val} {J : List Glyph} (hne : r ≠ [])
    (hc : ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b) :
    (encs r ++ J).headD Glyph.eos = Glyph.cons := by
  rcases r with _ | ⟨v, t⟩
  · exact absurd rfl hne
  obtain ⟨a, b, hb⟩ := hc v (List.mem_cons_self ..)
  subst hb
  rw [encs_cons_p2, List.append_assoc]
  exact headD_enc_cons

/-- a run list that is a tail of another -/
theorem sublist_drop_two (p p' : List Val) (ps : List (List Val)) :
    ps <+ (p :: p' :: ps) :=
  (List.sublist_cons_self p' ps).trans (List.sublist_cons_self p (p' :: ps))

end Work.Layout
