import Mathlib
import Submission.Work.Layout.Pass2Aux
import Submission.Work.Layout.Pass2Aux.Facts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The pure list-level facts about `Sk.passGo` / `Sk.passR` / `Sk.pass2R`

`RunsNe rs`/`RunsRec rs`/`RunsSort rs` say that every run of `rs` is nonempty / made of `cons`-values
of natural key / strictly increasing; `PairKeys ps qs` says that the keys of any two runs, one from
each list, are distinct.
-/

namespace Work.Layout

open HvdH
open scoped List

/-! ## Predicates on run lists -/

def RunsNe (rs : List (List Val)) : Prop := ∀ r ∈ rs, r ≠ []

def RunsRec (rs : List (List Val)) : Prop :=
  ∀ r ∈ rs, ∀ v ∈ r, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v'

def RunsSort (rs : List (List Val)) : Prop :=
  ∀ r ∈ rs, r.Pairwise (fun a b => pairKey a < pairKey b)

def PairKeys (ps qs : List (List Val)) : Prop :=
  ∀ r ∈ ps, ∀ r' ∈ qs, ((r ++ r').map pairKey).Nodup

theorem RunsNe.sublist {rs rs' : List (List Val)} (h : RunsNe rs) (hs : rs' <+ rs) : RunsNe rs' :=
  fun r hr => h r (hs.subset hr)

theorem RunsSort.sublist {rs rs' : List (List Val)} (h : RunsSort rs) (hs : rs' <+ rs) : RunsSort rs' :=
  fun r hr => h r (hs.subset hr)

theorem RunsRec.sublist {rs rs' : List (List Val)} (h : RunsRec rs) (hs : rs' <+ rs) : RunsRec rs' :=
  fun r hr => h r (hs.subset hr)

theorem PairKeys.sublist {ps ps' qs qs' : List (List Val)} (h : PairKeys ps qs)
    (h1 : ps' <+ ps) (h2 : qs' <+ qs) : PairKeys ps' qs' :=
  fun r hr r' hr' => h r (h1.subset hr) r' (h2.subset hr')

/-- prepending a nonempty run to `ac` keeps all runs nonempty -/
theorem RunsNe.prepend {p : List Val} {ac ad : List (List Val)} (hp : p ≠ [])
    (h : RunsNe (ac ++ ad)) : RunsNe ((p :: ac) ++ ad) := by
  intro r hr
  rw [List.cons_append, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact hp
  · exact h r hr

/-- appending a nonempty run to `ad` keeps all runs nonempty -/
theorem RunsNe.append_cons {p : List Val} {ac ad : List (List Val)} (hp : p ≠ [])
    (h : RunsNe (ac ++ ad)) : RunsNe (ac ++ (p :: ad)) := by
  intro r hr
  rw [List.mem_append] at hr
  rcases hr with hr | hr
  · exact h r (List.mem_append_left ad hr)
  · rw [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hp
    · exact h r (List.mem_append_right ac hr)

/-- prepending a sorted run to `ac` keeps all runs sorted -/
theorem RunsSort.prepend {p : List Val} {ac ad : List (List Val)}
    (hp : p.Pairwise (fun a b => pairKey a < pairKey b)) (h : RunsSort (ac ++ ad)) :
    RunsSort ((p :: ac) ++ ad) := by
  intro r hr
  rw [List.cons_append, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact hp
  · exact h r hr

/-- appending a sorted run to `ad` keeps all runs sorted -/
theorem RunsSort.append_cons {p : List Val} {ac ad : List (List Val)}
    (hp : p.Pairwise (fun a b => pairKey a < pairKey b)) (h : RunsSort (ac ++ ad)) :
    RunsSort (ac ++ (p :: ad)) := by
  intro r hr
  rw [List.mem_append] at hr
  rcases hr with hr | hr
  · exact h r (List.mem_append_left ad hr)
  · rw [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hp
    · exact h r (List.mem_append_right ac hr)

/-- inserting an element into a list -/
theorem sublist_insert {α : Type} (ps qs : List α) (q : α) : (ps ++ qs) <+ (ps ++ q :: qs) :=
  (List.sublist_cons_self q qs).append_left ps

/-- dropping the head runs of both lists -/
theorem sublist_tails (p : List Val) (ps qs : List (List Val)) (q : List Val) :
    (ps ++ qs) <+ ((p :: ps) ++ (q :: qs)) :=
  ((sublist_insert ps qs q).trans (List.sublist_cons_self p (ps ++ q :: qs)))

/-- dropping the head of a run list -/
theorem sublist_head_left (p : List Val) (ps qs : List (List Val)) :
    (ps ++ qs) <+ ((p :: ps) ++ qs) :=
  (List.sublist_cons_self p ps).append_right qs

/-- a member run is a sublist of the flattened run list -/
theorem run_sublist_flatten {r : List Val} {rs : List (List Val)} (h : r ∈ rs) :
    r <+ rs.flatten := by
  induction rs with
  | nil => exact absurd h List.not_mem_nil
  | cons a as ih =>
    rw [List.flatten_cons]
    rcases List.mem_cons.mp h with h1 | h2
    · rw [h1]
      exact List.sublist_append_left a as.flatten
    · exact (ih h2).trans (List.sublist_append_right a as.flatten)

/-- the `PairKeys` condition follows from the global distinctness of the keys -/
theorem PairKeys.of_flat_nodup {ps qs : List (List Val)}
    (h : (((ps ++ qs).flatten).map pairKey).Nodup) : PairKeys ps qs := by
  intro r hr r' hr'
  have h1 : r <+ ps.flatten := run_sublist_flatten hr
  have h2 : r' <+ qs.flatten := run_sublist_flatten hr'
  have h3 : (r ++ r') <+ (ps.flatten ++ qs.flatten) := h1.append h2
  rw [← List.flatten_append] at h3
  exact List.Sublist.nodup (h3.map pairKey) h

theorem RunsRec.of_flat {rs : List (List Val)}
    (h : ∀ v ∈ rs.flatten, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') :
    RunsRec rs := by
  intro r hr v hv
  exact h v (List.mem_flatten.mpr ⟨r, hr, hv⟩)

/-! ## Unfolding `Sk.passGo` -/

theorem passGo_nil (toC : Bool) (qs ac ad : List (List Val)) :
    Sk.passGo toC [] qs ac ad = (ac, ad) := by simp only [Sk.passGo]

theorem passGo_true_nil (p : List Val) (ps : List (List Val)) (ac ad : List (List Val)) :
    Sk.passGo true (p :: ps) [] ac ad = (p :: ac, ad) := by simp only [Sk.passGo]

theorem passGo_false_nil (p : List Val) (ps : List (List Val)) (ac ad : List (List Val)) :
    Sk.passGo false (p :: ps) [] ac ad = (ac, p :: ad) := by simp only [Sk.passGo]

theorem passGo_true_cons (p : List Val) (ps : List (List Val)) (q : List Val)
    (qs : List (List Val)) (ac ad : List (List Val)) :
    Sk.passGo true (p :: ps) (q :: qs) ac ad
      = Sk.passGo false ps qs (Sk.merge2 p q :: ac) ad := by simp only [Sk.passGo]

theorem passGo_false_cons (p : List Val) (ps : List (List Val)) (q : List Val)
    (qs : List (List Val)) (ac ad : List (List Val)) :
    Sk.passGo false (p :: ps) (q :: qs) ac ad
      = Sk.passGo true ps qs ac (Sk.merge2 p q :: ad) := by simp only [Sk.passGo]

/-! ## Permutation of the concatenated outputs -/

theorem passGo_count (a : Val) :
    ∀ (ps qs ac ad : List (List Val)),
      ps.length = qs.length ∨ ps.length = qs.length + 1 →
      ∀ toC : Bool,
      List.count a ((Sk.passGo toC ps qs ac ad).1 ++ (Sk.passGo toC ps qs ac ad).2).flatten
        = List.count a ((ps ++ qs).flatten) + List.count a ((ac ++ ad).flatten) := by
  intro ps
  induction ps with
  | nil =>
    intro qs ac ad hlen toC
    have hq : qs = [] := by
      rcases hlen with h | h
      · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h; omega)
      · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h; omega)
    subst hq
    rw [passGo_nil]
    simp
  | cons p ps ih =>
    intro qs ac ad hlen toC
    cases qs with
    | nil =>
      have hps : ps = [] := by
        rcases hlen with h | h
        · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons, List.length_nil] at h; omega)
        · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons, List.length_nil] at h; omega)
      subst hps
      cases toC with
      | true =>
        rw [passGo_true_nil]
        simp only [List.singleton_append, List.nil_append, List.flatten_cons, List.flatten_nil,
          List.flatten_append, List.count_append, List.count_nil, List.cons_append, add_zero,
          zero_add] <;> try omega
      | false =>
        rw [passGo_false_nil]
        simp only [List.singleton_append, List.nil_append, List.flatten_cons, List.flatten_nil,
          List.flatten_append, List.count_append, List.count_nil, List.cons_append, add_zero,
          zero_add] <;> try omega
    | cons q qs =>
      have hlen' : ps.length = qs.length ∨ ps.length = qs.length + 1 := by
        rcases hlen with h | h <;> simp only [List.length_cons] at h <;> omega
      have hm : List.count a (Sk.merge2 p q) = List.count a p + List.count a q := by
        rw [(merge2_perm p q).count a, List.count_append]
      cases toC with
      | true =>
        rw [passGo_true_cons, ih qs (Sk.merge2 p q :: ac) ad hlen' false]
        simp only [List.cons_append, List.flatten_cons, List.flatten_append, List.count_append,
          hm] <;> try omega
      | false =>
        rw [passGo_false_cons, ih qs ac (Sk.merge2 p q :: ad) hlen' true]
        simp only [List.cons_append, List.flatten_cons, List.flatten_append, List.count_append,
          hm] <;> try omega

theorem passR_count (a : Val) (ps qs : List (List Val))
    (hlen : ps.length = qs.length ∨ ps.length = qs.length + 1) :
    List.count a ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2).flatten
      = List.count a ((ps ++ qs).flatten) := by
  have h := passGo_count a ps qs [] [] hlen true
  simpa only [Sk.passR, List.nil_append, List.flatten_nil, List.count_nil, add_zero] using h

theorem passR_perm (ps qs : List (List Val))
    (hlen : ps.length = qs.length ∨ ps.length = qs.length + 1) :
    ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2).flatten.Perm ((ps ++ qs).flatten) :=
  List.perm_iff_count.mpr (fun a => passR_count a ps qs hlen)

/-! ## Lengths of the outputs -/

theorem passGo_len_eq :
    ∀ (ps qs ac ad : List (List Val)),
      ps.length = qs.length ∨ ps.length = qs.length + 1 →
      ∀ toC : Bool,
      (Sk.passGo toC ps qs ac ad).1.length + (Sk.passGo toC ps qs ac ad).2.length
        = ac.length + ad.length + qs.length + (if ps.length = qs.length then 0 else 1) := by
  intro ps
  induction ps with
  | nil =>
    intro qs ac ad hlen toC
    have hq : qs = [] := by
      rcases hlen with h | h
      · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h; omega)
      · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h; omega)
    subst hq
    rw [passGo_nil]
    simp only [List.length_nil]
    simp
  | cons p ps ih =>
    intro qs ac ad hlen toC
    cases qs with
    | nil =>
      have hps : ps = [] := by
        rcases hlen with h | h
        · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons, List.length_nil] at h; omega)
        · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons, List.length_nil] at h; omega)
      subst hps
      have hif : ¬ ((p :: ([] : List (List Val))).length = ([] : List (List Val)).length) := by
        simp only [List.length_cons, List.length_nil]
        omega
      cases toC with
      | true =>
        rw [passGo_true_nil, if_neg hif]
        simp only [List.length_cons, List.length_nil]
        omega
      | false =>
        rw [passGo_false_nil, if_neg hif]
        simp only [List.length_cons, List.length_nil]
        omega
    | cons q qs =>
      have hlen' : ps.length = qs.length ∨ ps.length = qs.length + 1 := by
        rcases hlen with h | h <;> simp only [List.length_cons] at h <;> omega
      cases toC with
      | true =>
        rw [passGo_true_cons]
        have h := ih qs (Sk.merge2 p q :: ac) ad hlen' false
        rw [h]
        by_cases hc : ps.length = qs.length
        · have hc2 : (p :: ps).length = (q :: qs).length := by
            simp only [List.length_cons]; omega
          rw [if_pos hc, if_pos hc2]
          simp only [List.length_cons]
          omega
        · have hc2 : ¬ ((p :: ps).length = (q :: qs).length) := by
            simp only [List.length_cons]; omega
          rw [if_neg hc, if_neg hc2]
          simp only [List.length_cons]
          omega
      | false =>
        rw [passGo_false_cons]
        have h := ih qs ac (Sk.merge2 p q :: ad) hlen' true
        rw [h]
        by_cases hc : ps.length = qs.length
        · have hc2 : (p :: ps).length = (q :: qs).length := by
            simp only [List.length_cons]; omega
          rw [if_pos hc, if_pos hc2]
          simp only [List.length_cons]
          omega
        · have hc2 : ¬ ((p :: ps).length = (q :: qs).length) := by
            simp only [List.length_cons]; omega
          rw [if_neg hc, if_neg hc2]
          simp only [List.length_cons]
          omega

theorem passR_len_le (ps qs : List (List Val))
    (hlen : ps.length = qs.length ∨ ps.length = qs.length + 1) :
    (Sk.passR ps qs).1.length + (Sk.passR ps qs).2.length ≤ ps.length + qs.length := by
  show (Sk.passGo true ps qs [] []).1.length + (Sk.passGo true ps qs [] []).2.length
      ≤ ps.length + qs.length
  have h := passGo_len_eq ps qs [] [] hlen true
  by_cases hc : ps.length = qs.length
  · rw [if_pos hc] at h
    simp only [List.length_nil, add_zero] at h
    omega
  · rw [if_neg hc] at h
    simp only [List.length_nil, add_zero] at h
    rcases hlen with hh | hh <;> omega

theorem passGo_len_inv :
    ∀ (ps qs ac ad : List (List Val)),
      ps.length = qs.length ∨ ps.length = qs.length + 1 →
      ((Sk.passGo true ps qs ac ad).1.length + ad.length
          ≤ (Sk.passGo true ps qs ac ad).2.length + ac.length + 1 ∧
        (Sk.passGo true ps qs ac ad).2.length + ac.length
          ≤ (Sk.passGo true ps qs ac ad).1.length + ad.length) ∧
      ((Sk.passGo false ps qs ac ad).1.length + ad.length
          ≤ (Sk.passGo false ps qs ac ad).2.length + ac.length ∧
        (Sk.passGo false ps qs ac ad).2.length + ac.length
          ≤ (Sk.passGo false ps qs ac ad).1.length + ad.length + 1) := by
  intro ps
  induction ps with
  | nil =>
    intro qs ac ad hlen
    have hq : qs = [] := by
      rcases hlen with h | h
      · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h; omega)
      · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h; omega)
    subst hq
    have h1 : (Sk.passGo true ([] : List (List Val)) ([] : List (List Val)) ac ad).1 = ac := by
      rw [passGo_nil]
    have h2 : (Sk.passGo true ([] : List (List Val)) ([] : List (List Val)) ac ad).2 = ad := by
      rw [passGo_nil]
    have h3 : (Sk.passGo false ([] : List (List Val)) ([] : List (List Val)) ac ad).1 = ac := by
      rw [passGo_nil]
    have h4 : (Sk.passGo false ([] : List (List Val)) ([] : List (List Val)) ac ad).2 = ad := by
      rw [passGo_nil]
    rw [h1, h2, h3, h4]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
  | cons p ps ih =>
    intro qs ac ad hlen
    cases qs with
    | nil =>
      have hps : ps = [] := by
        rcases hlen with h | h
        · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons, List.length_nil] at h; omega)
        · exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons, List.length_nil] at h; omega)
      subst hps
      have e1 : (Sk.passGo true (p :: []) [] ac ad).1 = p :: ac := by rw [passGo_true_nil]
      have e2 : (Sk.passGo true (p :: []) [] ac ad).2 = ad := by rw [passGo_true_nil]
      have e3 : (Sk.passGo false (p :: []) [] ac ad).1 = ac := by rw [passGo_false_nil]
      have e4 : (Sk.passGo false (p :: []) [] ac ad).2 = p :: ad := by rw [passGo_false_nil]
      rw [e1, e2, e3, e4]
      simp only [List.length_cons]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
    | cons q qs =>
      have hlen' : ps.length = qs.length ∨ ps.length = qs.length + 1 := by
        rcases hlen with h | h <;> simp only [List.length_cons] at h <;> omega
      obtain ⟨h1, h2⟩ := ih qs (Sk.merge2 p q :: ac) ad hlen'
      obtain ⟨h3, h4⟩ := ih qs ac (Sk.merge2 p q :: ad) hlen'
      rw [passGo_true_cons, passGo_false_cons]
      simp only [List.length_cons] at h1 h2 h3 h4 ⊢
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem passR_len_inv (ps qs : List (List Val))
    (hlen : ps.length = qs.length ∨ ps.length = qs.length + 1) :
    (Sk.passR ps qs).1.length = (Sk.passR ps qs).2.length ∨
      (Sk.passR ps qs).1.length = (Sk.passR ps qs).2.length + 1 := by
  show (Sk.passGo true ps qs [] []).1.length = (Sk.passGo true ps qs [] []).2.length ∨
    (Sk.passGo true ps qs [] []).1.length = (Sk.passGo true ps qs [] []).2.length + 1
  obtain ⟨⟨h1, h2⟩, _⟩ := passGo_len_inv ps qs [] [] hlen
  simp only [List.length_nil, add_zero] at h1 h2
  omega

/-! ## Nonemptiness and sortedness of the outputs -/

theorem passGo_ne_nil :
    ∀ (ps qs ac ad : List (List Val)),
      RunsNe (ac ++ ad) → RunsNe (ps ++ qs) → ∀ toC : Bool,
      RunsNe ((Sk.passGo toC ps qs ac ad).1 ++ (Sk.passGo toC ps qs ac ad).2) := by
  intro ps
  induction ps with
  | nil =>
    intro qs ac ad hac _ toC
    rw [passGo_nil]
    exact hac
  | cons p ps ih =>
    intro qs ac ad hac hpq toC
    have htail : RunsNe (ps ++ qs) := hpq.sublist ((List.sublist_cons_self p ps).append_right qs)
    cases qs with
    | nil =>
      have hp : p ≠ [] := hpq p (List.mem_append_left [] (List.mem_cons_self (a := p)))
      cases toC with
      | true =>
        rw [passGo_true_nil]
        exact RunsNe.prepend hp hac
      | false =>
        rw [passGo_false_nil]
        exact RunsNe.append_cons hp hac
    | cons q qs =>
      have hp : p ≠ [] := hpq p (List.mem_append_left (q :: qs) (List.mem_cons_self (a := p)))
      have htail2 : RunsNe (ps ++ qs) :=
        htail.sublist ((List.sublist_cons_self q qs).append_left ps)
      have hm : Sk.merge2 p q ≠ [] := merge2_ne_nil p q hp
      cases toC with
      | true =>
        rw [passGo_true_cons]
        exact ih qs (Sk.merge2 p q :: ac) ad (RunsNe.prepend hm hac) htail2 false
      | false =>
        rw [passGo_false_cons]
        exact ih qs ac (Sk.merge2 p q :: ad) (RunsNe.append_cons hm hac) htail2 true

theorem passR_ne_nil (ps qs : List (List Val)) (hne : RunsNe (ps ++ qs)) :
    RunsNe ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) :=
  passGo_ne_nil ps qs [] [] (by simp [RunsNe]) hne true

theorem passGo_sorted :
    ∀ (ps qs ac ad : List (List Val)),
      RunsSort (ac ++ ad) → RunsSort (ps ++ qs) → PairKeys ps qs → ∀ toC : Bool,
      RunsSort ((Sk.passGo toC ps qs ac ad).1 ++ (Sk.passGo toC ps qs ac ad).2) := by
  intro ps
  induction ps with
  | nil =>
    intro qs ac ad hac _ _ toC
    rw [passGo_nil]
    exact hac
  | cons p ps ih =>
    intro qs ac ad hac hpq hkeys toC
    have htail : RunsSort (ps ++ qs) := hpq.sublist ((List.sublist_cons_self p ps).append_right qs)
    cases qs with
    | nil =>
      have hp : p.Pairwise (fun a b => pairKey a < pairKey b) :=
        hpq p (List.mem_append_left [] (List.mem_cons_self (a := p)))
      cases toC with
      | true =>
        rw [passGo_true_nil]
        exact RunsSort.prepend hp hac
      | false =>
        rw [passGo_false_nil]
        exact RunsSort.append_cons hp hac
    | cons q qs =>
      have hp : p.Pairwise (fun a b => pairKey a < pairKey b) :=
        hpq p (List.mem_append_left (q :: qs) (List.mem_cons_self (a := p)))
      have hq : q.Pairwise (fun a b => pairKey a < pairKey b) :=
        hpq q (List.mem_append_right (p :: ps) (List.mem_cons_self (a := q)))
      have htail2 : RunsSort (ps ++ qs) :=
        htail.sublist ((List.sublist_cons_self q qs).append_left ps)
      have hkeys' : PairKeys ps qs :=
        hkeys.sublist (List.sublist_cons_self p ps) (List.sublist_cons_self q qs)
      have hnd : ((p ++ q).map pairKey).Nodup :=
        hkeys p (List.mem_cons_self (a := p)) q (List.mem_cons_self (a := q))
      have hm : (Sk.merge2 p q).Pairwise (fun a b => pairKey a < pairKey b) :=
        merge2_sorted p q hp hq hnd
      cases toC with
      | true =>
        rw [passGo_true_cons]
        exact ih qs (Sk.merge2 p q :: ac) ad (RunsSort.prepend hm hac) htail2 hkeys' false
      | false =>
        rw [passGo_false_cons]
        exact ih qs ac (Sk.merge2 p q :: ad) (RunsSort.append_cons hm hac) htail2 hkeys' true

theorem passR_sorted (ps qs : List (List Val)) (hs : RunsSort (ps ++ qs)) (hk : PairKeys ps qs) :
    RunsSort ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) :=
  passGo_sorted ps qs [] [] (by simp [RunsSort]) hs hk true

end Work.Layout
