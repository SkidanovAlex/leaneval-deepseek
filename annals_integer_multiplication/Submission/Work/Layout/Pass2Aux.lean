import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.SortSpecs
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.drainValsEv

set_option autoImplicit false

/-!
# Auxiliaries for the two-pass lemma `Work.Layout.pass2_ev2`

This file only contains definitions and elementary lemmas (all `sorry`-free) that other files use:

* `runsz r` — `Σ (vsz + 1)` over the elements of a run, the "size" of a run;
* `mergeCost P Q` — the cost factor of merging `P` and `Q`, matching the bound of
  `Work.Layout.Sk.MergePairSpec`;
* `mergeW ps qs` — the total cost factor of the merges that a single `pass` still has to perform at the
  loop-test state where `X` holds the runs `ps` and `Y` the runs `qs` (the merges pair `ps[i]` with
  `qs[i]`);
* `totL rs` — `Σ vsz + Σ length` over all elements of the run list `rs`;
* `passW K ps qs` — an upper bound for the cost of `passLoopCmd ; passPostCmd` from that state;
* `passLoopCmd` / `passPostCmd` — the loop of `Sk.pass` and the leftover-run move that follows it.
-/

namespace Work.Layout

open HvdH

/-! ## Sizes and costs -/

/-- `Σ (vsz + 1)` over the elements of a run: the size of the run. -/
def runsz (r : List Val) : ℕ := (r.map vsz).sum + r.length

/-- The cost factor of merging the runs `P` and `Q`: exactly the expression appearing in the bound of
`Work.Layout.Sk.MergePairSpec`. -/
def mergeCost (P Q : List Val) : ℕ := ((P ++ Q).map vsz).sum + (P ++ Q).length + 2

/-- The total cost factor of the merges remaining in a `pass` at the loop-test state `(ps,qs)`: the
merges pair the runs `ps[i]` and `qs[i]`, so `List.zipWith` (which truncates at the shorter list)
describes them. -/
def mergeW (ps qs : List (List Val)) : ℕ := (ps.zipWith mergeCost qs).sum

/-- Total size of the elements of a list of runs: `Σ vsz + Σ length`. -/
def totL (rs : List (List Val)) : ℕ := (rs.flatten.map vsz).sum + rs.flatten.length

/-- The size contribution of the runs of `ps` that are *not* merged with a run of `qs` (the leftover
runs of a `pass`, at most one of them under the length invariant). -/
def leftW : List (List Val) → List (List Val) → ℕ
  | [], _ => 0
  | r :: rs, [] => (runsz r + 1) + leftW rs []
  | _ :: rs, _ :: qs => leftW rs qs

/-- An upper bound for the cost of `passLoopCmd ; passPostCmd` from the loop-test state `(ps,qs)`:
`K` units per `mergeCost` unit of the remaining merges (`K = Sk.MPc KLt KSz`), plus the leftover-run
move, plus a constant per loop iteration. -/
def passW (K : ℕ) (ps qs : List (List Val)) : ℕ :=
  K * mergeW ps qs + 60 * leftW ps qs + 60 * (qs.length + 1) + 60

/-! ## Elementary facts -/

@[simp] theorem runsz_nil : runsz ([] : List Val) = 0 := rfl

theorem runsz_append (r r' : List Val) : runsz (r ++ r') = runsz r + runsz r' := by
  simp only [runsz, List.map_append, List.sum_append, List.length_append]
  omega

@[simp] theorem mergeCost_eq (P Q : List Val) : mergeCost P Q = runsz P + runsz Q + 2 := by
  simp only [mergeCost, runsz, List.map_append, List.sum_append, List.length_append]
  omega

@[simp] theorem totL_nil : totL ([] : List (List Val)) = 0 := rfl

theorem totL_cons (r : List Val) (rs : List (List Val)) : totL (r :: rs) = runsz r + totL rs := by
  simp only [totL, List.flatten_cons, List.map_append, List.sum_append, List.length_append, runsz]
  omega

theorem totL_append (rs rs' : List (List Val)) : totL (rs ++ rs') = totL rs + totL rs' := by
  simp only [totL, List.flatten_append, List.map_append, List.sum_append, List.length_append]
  omega

@[simp] theorem mergeW_cons (p : List Val) (ps : List (List Val)) (q : List Val)
    (qs : List (List Val)) : mergeW (p :: ps) (q :: qs) = mergeCost p q + mergeW ps qs := by
  simp [mergeW]

@[simp] theorem mergeW_nil_left (qs : List (List Val)) : mergeW [] qs = 0 := by
  simp [mergeW]

@[simp] theorem mergeW_nil_right (ps : List (List Val)) : mergeW ps [] = 0 := by
  cases ps <;> simp [mergeW]

@[simp] theorem leftW_nil_left (qs : List (List Val)) : leftW [] qs = 0 := rfl

@[simp] theorem leftW_cons_cons (r : List Val) (rs : List (List Val)) (q : List Val)
    (qs : List (List Val)) : leftW (r :: rs) (q :: qs) = leftW rs qs := rfl

@[simp] theorem leftW_cons_nil (r : List Val) (rs : List (List Val)) :
    leftW (r :: rs) [] = (runsz r + 1) + leftW rs [] := rfl

@[simp] theorem passW_nil_nil (K : ℕ) : passW K [] ([] : List (List Val)) = 120 := by
  simp [passW]

/-- one iteration of the `pass` loop removes the two first merge pairs from the potential -/
theorem passW_step (K : ℕ) (p p' : List Val) (ps : List (List Val)) (q q' : List Val)
    (qs : List (List Val)) :
    passW K (p :: p' :: ps) (q :: q' :: qs)
      = K * (mergeCost p q + mergeCost p' q') + passW K ps qs + 120 := by
  simp only [passW, mergeW, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
    leftW_cons_cons]
  ring

/-! ## The two pieces of `Sk.pass` -/

/-- the loop of `Sk.pass` -/
def passLoopCmd (pLt pSz : Cmd) (X Y C D T1 T2 SA SB F1 F2 t d : Stk) : Cmd :=
  .loop Sk.rF Glyph.cons (Sk.passBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d)

/-- the leftover-run move of `Sk.pass`, executed after the loop -/
def passPostCmd (pLt pSz : Cmd) (X Y C D T1 T2 SA SB F1 F2 t d : Stk) : Cmd :=
  .seq (.peek X Sk.rH) (.ite Sk.rH Glyph.cons (Sk.moveRun X C T1 t d) .skip)

theorem pass_eq (pLt pSz : Cmd) (X Y C D T1 T2 SA SB F1 F2 t d : Stk) :
    Sk.pass pLt pSz X Y C D T1 T2 SA SB F1 F2 t d
      = .seq (.peek Y Sk.rF)
          (.seq (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d)
            (passPostCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d)) := rfl

/-! ## Unfolding the run encodings -/

theorem runEncB_cons_raw (r : List Val) (rs : List (List Val)) :
    Sk.runEncB (r :: rs) = ((encs r ++ [gMark]) ++ Sk.runEnc rs) ++ [Sk.gBnd] := rfl

@[simp] theorem runEncB_cons (r : List Val) (rs : List (List Val)) :
    Sk.runEncB (r :: rs) = encs r ++ gMark :: Sk.runEncB rs := by
  rw [runEncB_cons_raw]
  simp only [Sk.runEncB, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append]

@[simp] theorem runEncB_nil : Sk.runEncB ([] : List (List Val)) = [Sk.gBnd] := rfl

@[simp] theorem runEncB_append (rs rs' : List (List Val)) :
    Sk.runEncB (rs ++ rs') = Sk.runEnc rs ++ Sk.runEncB rs' := by
  simp [Sk.runEncB, Sk.runEnc]

theorem runEncB_eq_nil (rs : List (List Val)) : Sk.runEncB rs = Sk.runEnc rs ++ [Sk.gBnd] := rfl

/-! ## Encodings -/

@[simp] theorem encs_cons_p2 (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

@[simp] theorem encs_nil : encs ([] : List Val) = [] := rfl

theorem encs_append_p2 (l₁ l₂ : List Val) : encs (l₁ ++ l₂) = encs l₁ ++ encs l₂ := by
  simp [encs, List.map_append, List.flatten_append]

/-- every value's encoding is nonempty -/
theorem enc_ne_nil (v : Val) : v.enc ≠ [] := by
  intro h
  have h2 : v.enc.length = 0 := by rw [h]; rfl
  have h1 : 1 ≤ v.enc.length := one_le_vsz v
  omega

/-- the encoding of a nonempty value list is nonempty -/
theorem encs_ne_nil {q : List Val} (h : q ≠ []) : encs q ≠ [] := by
  rcases q with _ | ⟨v, t⟩
  · exact absurd rfl h
  intro hc
  have h1 : 1 ≤ v.enc.length := one_le_vsz v
  have h2 : (encs (v :: t)).length = 0 := by rw [hc]; rfl
  rw [encs_cons_p2, List.length_append] at h2
  omega

/-- `headD` of an append with a nonempty left part -/
theorem headD_append (l l' : List Glyph) (h : l ≠ []) :
    (l ++ l').headD Glyph.eos = l.headD Glyph.eos := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- the encoding of a `cons`-value starts with `Glyph.cons` -/
theorem headD_enc_cons {a b : Val} {l : List Glyph} :
    ((Val.cons a b).enc ++ l).headD Glyph.eos = Glyph.cons := rfl

theorem gBnd_ne_cons : Sk.gBnd ≠ Glyph.cons := by decide

/-- the top glyph of a stack holding a nonempty run of `cons`-values is `Glyph.cons` -/
theorem headD_runEncB_cons {r : List Val} {rs : List (List Val)} {J : List Glyph}
    (hne : r ≠ []) (hc : ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b) :
    (Sk.runEncB (r :: rs) ++ J).headD Glyph.eos = Glyph.cons := by
  rw [runEncB_cons, List.append_assoc, headD_append (encs r) _ (encs_ne_nil hne)]
  rcases r with _ | ⟨v, t⟩
  · exact absurd rfl hne
  obtain ⟨a, b, hb⟩ := hc v (List.mem_cons_self ..)
  subst hb
  rw [encs_cons_p2, headD_append (Val.enc (Val.cons a b)) _ (enc_ne_nil _)]
  rfl

/-- the top glyph of a stack whose run area is empty is the boundary marker -/
theorem headD_runEncB_nil (J : List Glyph) :
    (Sk.runEncB ([] : List (List Val)) ++ J).headD Glyph.eos = Sk.gBnd := rfl

/-- `Ev` of a `peek` whose result is known -/
theorem ev_peek_at {main : Cmd} {k : Stk} {r : Reg} {c : Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (h : (X k).headD Glyph.eos = c) :
    Ev main (.peek k r) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 := by
  rw [← h]; exact ev_peek' main k r g X

theorem ev_set_at {main : Cmd} {r : Reg} {c : Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} : Ev main (.set r c) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 :=
  ev_set' main r c g X

/-- every run of a `cons`-valued run list has a `cons` at the head -/
theorem headD_runEncB_pos {ps : List (List Val)} {J : List Glyph}
    (hne : ∀ r ∈ ps, r ≠ [])
    (hc : ∀ v ∈ ps.flatten, ∃ a b : Val, v = Val.cons a b) :
    ps ≠ [] → (Sk.runEncB ps ++ J).headD Glyph.eos = Glyph.cons := by
  intro hps
  rcases ps with _ | ⟨r, rs⟩
  · exact absurd rfl hps
  exact headD_runEncB_cons (hne r (List.mem_cons_self ..))
    (fun v hv => hc v (by simp only [List.flatten_cons]; exact List.mem_append_left _ hv))

end Work.Layout
