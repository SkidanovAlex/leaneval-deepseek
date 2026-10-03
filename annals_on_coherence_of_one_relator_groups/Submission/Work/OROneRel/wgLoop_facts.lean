/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The loop of a step of the `ℤ`-cover walk

For a walk with levels `vs` (of length `n + 1`) and labels `lbl` (of length `n`), the *loop* of its
`j`-th step is

  `wgLoop vs lbl j = wgTp vs lbl (wgSig vs j) ++ [(j, true)] ++ wgRev (wgTp vs lbl (wgTau vs j))`,

that is: down the first-arrival tree to the source level of the step, across the step, and back up
the tree from its target level.  This file records the four facts about these loops that the
immersion argument needs:

* `wgLoop vs lbl j` is a closed walk at the base level;
* it only uses edges of the walk (`p.1 < lbl.length`);
* its image in the target free group is the loop class `stepWord (walkGauge vs lbl)` of the step;
* for a non-tree step its image in the fundamental group of the domain is the corresponding
  generator.

Everything is proved here from `wgImmersionDefs` (and hence `gauge_levels_bound`) alone.  The
toolkit below is deliberately self-contained:

* `wglE_wgTpAux_succ`, `wglE_wgTpAux_mem` -- the recursion equation of the first-arrival path and
  the fact that all of its traversals are forward tree edges;
* `wglE_wgTpAux_path` -- the first-arrival path to a visited level is a walk;
* `wglE_wgPath_append` -- walks concatenate;
* `wglE_wgMu_tree` -- a walk through the tree dies in the fundamental group of the domain;
* `wglE_TpAux_word` -- the word of the first-arrival path to a level is exactly the entry of the
  first-arrival state machine at that level, so that `wgWord` of a loop is the loop class of the
  step under the first-arrival gauge `walkGauge`.
-/
import Mathlib
import Submission.Work.OROneRel.wgImmersionDefs

set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {α : Type u}

attribute [local instance] Classical.propDecidable

/-! ## The recursion equation of the first-arrival path -/

/-- One unfolding of the first-arrival path: if step `k` arrives at a new level, it is appended to
the path to the source of the step, and otherwise nothing happens. -/
theorem wglE_wgTpAux_succ (vs : List ℤ) (k : ℕ) (v : ℤ) :
    wgTpAux vs (k + 1) v =
      (if wgTree vs k ∧ wgTau vs k = v then wgTpAux vs k (wgSig vs k) ++ [(k, true)]
        else wgTpAux vs k v) := rfl

/-! ## List plumbing -/

/-- A prefix of length `k + 1` is the prefix of length `k` followed by the `k`-th entry. -/
theorem wglE_take_succ_getElem {β : Type*} (l : List β) {k : ℕ} (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]

/-- The only element of a one-element prefix is the head. -/
theorem wglE_mem_take_one {l : List ℤ} {x : ℤ} (h : x ∈ l.take 1) : x = l.headD 0 := by
  cases l with
  | nil => simp at h
  | cons a t => simpa using h

/-- A prefix of length `n + 2` is a prefix of length `n + 1` plus at most the `(n+1)`-st entry. -/
theorem wglE_mem_take_succ {l : List ℤ} {n : ℕ} {x : ℤ} (h : x ∈ l.take (n + 2)) :
    x ∈ l.take (n + 1) ∨ x = l.getD (n + 1) 0 := by
  rw [List.mem_take_iff_getElem] at h
  obtain ⟨j, hj, hjx⟩ := h
  have hjle : j ≤ n + 1 := by
    have : j < n + 2 := lt_of_lt_of_le hj (Nat.min_le_left (n + 2) l.length)
    omega
  rcases lt_or_eq_of_le hjle with hlt | heq
  · left
    rw [List.mem_take_iff_getElem]
    exact ⟨j, lt_min hlt (lt_of_lt_of_le hj (Nat.min_le_right (n + 2) l.length)), hjx⟩
  · right
    have hjl : j < l.length := lt_of_lt_of_le hj (Nat.min_le_right (n + 2) l.length)
    have hgd : l.getD j 0 = x := by
      rw [List.getD_eq_getElem l 0 hjl]
      exact hjx
    rw [heq] at hgd
    exact hgd.symm

/-! ## Traversals of a first-arrival path -/

/-- Every traversal of `wgTpAux vs k v` is a forward traversal (`p.2 = true`) of a tree edge
(`wgTree vs p.1`) occurring before step `k`. -/
theorem wglE_wgTpAux_mem (vs : List ℤ) :
    ∀ (k : ℕ) (v : ℤ) (p : ℕ × Bool), p ∈ wgTpAux vs k v →
      p.2 = true ∧ p.1 < k ∧ wgTree vs p.1 := by
  intro k
  induction k with
  | zero =>
    intro v p hp
    simp [wgTpAux] at hp
  | succ k ih =>
    intro v p hp
    rw [wglE_wgTpAux_succ] at hp
    by_cases h : wgTree vs k ∧ wgTau vs k = v
    · rw [if_pos h, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | hp
      · obtain ⟨h2, h1, h3⟩ := ih (wgSig vs k) p hp
        exact ⟨h2, by omega, h3⟩
      · subst hp
        exact ⟨rfl, by omega, h.1⟩
    · rw [if_neg h] at hp
      obtain ⟨h2, h1, h3⟩ := ih v p hp
      exact ⟨h2, by omega, h3⟩

/-- Walks concatenate (explicit-argument form, the recursion is on `γ`). -/
private theorem wglE_wgPath_append_aux {vs : List ℤ} :
    ∀ (u v w : ℤ) (γ δ : List (ℕ × Bool)),
      wgPath vs u γ v → wgPath vs v δ w → wgPath vs u (γ ++ δ) w := by
  intro u v w γ
  induction γ generalizing u with
  | nil =>
    intro δ h1 h2
    rw [wgPath_nil] at h1
    rw [h1]
    simpa using h2
  | cons p ps ih =>
    intro δ h1 h2
    exact ⟨h1.1, ih (wgHead vs p) δ h1.2 h2⟩

/-- Walks concatenate. -/
theorem wglE_wgPath_append {vs : List ℤ} {u v w : ℤ} {γ δ : List (ℕ × Bool)}
    (h1 : wgPath vs u γ v) (h2 : wgPath vs v δ w) : wgPath vs u (γ ++ δ) w :=
  wglE_wgPath_append_aux u v w γ δ h1 h2

/-- **The first-arrival path to a visited level is a walk.**  If `v` is a level visited during the
first `k` steps of the walk, then `wgTpAux vs k v` is a walk from the base level to `v`. -/
theorem wglE_wgTpAux_path (vs : List ℤ) (lbl : List (FreeGroup α))
    (hlen : vs.length = lbl.length + 1) :
    ∀ (k : ℕ) (v : ℤ), k ≤ lbl.length → v ∈ vs.take (k + 1) →
      wgPath vs (vs.headD 0) (wgTpAux vs k v) v := by
  intro k
  induction k with
  | zero =>
    intro v _ hv
    rw [show wgTpAux vs 0 v = ([] : List (ℕ × Bool)) from rfl, wgPath_nil]
    exact (wglE_mem_take_one hv).symm
  | succ k ih =>
    intro v hk hv
    have hk' : k ≤ lbl.length := by omega
    by_cases h : wgTree vs k ∧ wgTau vs k = v
    · have hsig : wgSig vs k ∈ vs.take (k + 1) := by
        have hklt : k < vs.length := by omega
        refine List.mem_take_iff_getElem.mpr ⟨k, lt_min (by omega) hklt, ?_⟩
        simp only [wgSig, List.getD_eq_getElem vs 0 hklt]
      rw [wglE_wgTpAux_succ, if_pos h]
      exact wglE_wgPath_append (ih (wgSig vs k) hk' hsig) ⟨rfl, h.2⟩
    · have hv' : v ∈ vs.take (k + 1) := by
        rcases wglE_mem_take_succ (n := k) hv with hmem | heq
        · exact hmem
        · have hwt : wgTau vs k ∈ vs.take (k + 1) := by
            by_contra hc
            exact h ⟨hc, heq.symm⟩
          rw [heq]
          exact hwt
      rw [wglE_wgTpAux_succ, if_neg h]
      exact ih v hk' hv'

/-! ## Walks through the tree die in the fundamental group of the domain -/

/-- The loop class of a non-tree step, at its single generator. -/
theorem wglE_wgMuGen_of_not_tree (vs : List ℤ) (lbl : List (FreeGroup α)) {j : ℕ}
    (hj : j < lbl.length) (h : ¬ wgTree vs j) :
    wgMuGen vs lbl j = FreeGroup.of ⟨j, hj, h⟩ := by
  simp only [wgMuGen]
  rw [dif_pos ⟨hj, h⟩]

/-- The loop class of a tree step is trivial. -/
theorem wglE_wgMuGen_of_tree (vs : List ℤ) (lbl : List (FreeGroup α)) {j : ℕ}
    (h : wgTree vs j) : wgMuGen vs lbl j = 1 := by
  simp only [wgMuGen]
  rw [dif_neg]
  rintro ⟨-, hnt⟩
  exact hnt h

/-- A walk all of whose traversals are forward tree edges is trivial in the fundamental group of
the domain. -/
theorem wglE_wgMu_tree (vs : List ℤ) (lbl : List (FreeGroup α)) :
    ∀ {γ : List (ℕ × Bool)}, (∀ p ∈ γ, p.2 = true ∧ wgTree vs p.1) → wgMu vs lbl γ = 1 := by
  intro γ
  induction γ with
  | nil =>
    intro _
    rfl
  | cons p ps ih =>
    intro h
    have hp : p.2 = true ∧ wgTree vs p.1 := h p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.2 = true ∧ wgTree vs q.1 :=
      fun q hq => h q (List.mem_cons_of_mem p hq)
    rw [show (p :: ps : List (ℕ × Bool)) = [p] ++ ps from rfl, wgMu_append, wgMu_singleton,
      ih hps, mul_one]
    simp [wglE_wgMuGen_of_tree vs lbl hp.2, hp.1]

/-- The label of a forward traversal is the label of its step. -/
theorem wglE_wgLblP_true (lbl : List (FreeGroup α)) (j : ℕ) :
    wgLblP lbl (j, true) = wgLbl lbl j := rfl

/-- A single forward traversal of a non-tree step has, in the fundamental group of the domain, the
class of the corresponding generator. -/
theorem wglE_wgMu_single (vs : List ℤ) (lbl : List (FreeGroup α)) {j : ℕ}
    (hj : j < lbl.length) (htree : ¬ wgTree vs j) :
    wgMu vs lbl [(j, true)] = FreeGroup.of ⟨j, hj, htree⟩ := by
  simp [wgMu_singleton, wglE_wgMuGen_of_not_tree vs lbl hj htree]

/-! ## The first-arrival machine -/

/-- The state of the first-arrival machine after all the steps is the first-arrival gauge. -/
theorem wglE_wgState_eq_walkGauge (vs : List ℤ) (lbl : List (FreeGroup α))
    (hlen : vs.length = lbl.length + 1) (v : ℤ) :
    (wgState vs lbl lbl.length v).getD 1 = walkGauge vs lbl v := by
  simp only [wgState, walkGauge, ← mkSteps_length vs lbl hlen, List.take_length]

/-- The state of the first-arrival machine before any step. -/
theorem wglE_wgState_zero (vs : List ℤ) (lbl : List (FreeGroup α)) (v : ℤ) :
    (wgState vs lbl 0 v).getD 1 = 1 := by
  simp only [wgState, runSteps, List.take_zero, List.foldl_nil, initState]
  split <;> rfl

/-- One step of the first-arrival machine, in terms of the `k`-th step of the walk. -/
theorem wglE_wgState_succ (vs : List ℤ) (lbl : List (FreeGroup α)) {k : ℕ}
    (hk : k < (mkSteps vs lbl).length) :
    ∀ v, wgState vs lbl (k + 1) v
      = stepUpd (wgState vs lbl k) ((mkSteps vs lbl).getD k (defaultStep α)) v := by
  intro v
  have hsplit : (wgState vs lbl (k + 1)) v
      = stepUpd (wgState vs lbl k) (wgStep vs lbl k) v := by
    have hfun : wgState vs lbl (k + 1) = runSteps (wgState vs lbl k) [wgStep vs lbl k] := by
      simp only [wgState, wgStep, wglE_take_succ_getElem (mkSteps vs lbl) hk, runSteps_append,
        ← List.getD_eq_getElem (mkSteps vs lbl) (defaultStep α) hk]
    have hval : runSteps (wgState vs lbl k) [wgStep vs lbl k] v
        = stepUpd (wgState vs lbl k) (wgStep vs lbl k) v := by
      simp only [runSteps, List.foldl_cons, List.foldl_nil]
    simp only [hfun, hval]
  simpa only [wgStep] using hsplit

/-- **The first-arrival path and the first-arrival machine compute the same word.**  The image in
`FreeGroup α` of the tree path `wgTpAux vs k v` is the word the state machine has attached to the
level `v` after `k` steps. -/
theorem wglE_TpAux_word (vs : List ℤ) (lbl : List (FreeGroup α))
    (hlen : vs.length = lbl.length + 1) :
    ∀ (k : ℕ) (v : ℤ), k ≤ lbl.length →
      wgWord vs lbl (wgTpAux vs k v) = (wgState vs lbl k v).getD 1 := by
  classical
  intro k
  induction k with
  | zero =>
    intro v _
    rw [show wgTpAux vs 0 v = ([] : List (ℕ × Bool)) from rfl, wgWord_nil]
    exact (wglE_wgState_zero vs lbl v).symm
  | succ k ih =>
    intro v hk
    have hk' : k ≤ lbl.length := by omega
    have hklt : k < lbl.length := by omega
    have hklen : k < (mkSteps vs lbl).length := by
      rw [mkSteps_length vs lbl hlen]; exact hklt
    have hsplit : (wgState vs lbl (k + 1)) v
        = stepUpd (wgState vs lbl k) (wgStep vs lbl k) v := by
      rw [wglE_wgState_succ vs lbl hklen v]
      simp only [wgStep]
    by_cases h : wgTree vs k ∧ wgTau vs k = v
    · -- the step discovers the level `v`: the machine multiplies in the label
      have htgt : (wgStep vs lbl k).tgt = v := by
        rw [wgStep, mkSteps_getD_tgt vs lbl hlen k hklt]
        exact h.2
      have hnone : (wgState vs lbl k) v = none := by
        simp only [wgState]
        rw [← not_ne_iff, prefixState_ne_none vs lbl hlen k hk', ← h.2]
        exact h.1
      have hupd : stepUpd (wgState vs lbl k) (wgStep vs lbl k) v
          = some (((wgState vs lbl k) (wgSig vs k)).getD 1 * wgLbl lbl k) := by
        simp only [stepUpd]
        rw [if_pos ⟨htgt.symm, by rw [htgt]; exact hnone⟩]
        simp only [wgStep, mkSteps_getD_src vs lbl hlen k hklt,
          mkSteps_getD_lbl vs lbl hlen k hklt, wgSig, wgLbl]
      simp only [wglE_wgTpAux_succ, if_pos h, wgWord_append, wgWord_singleton,
        ih (wgSig vs k) hk', hsplit, hupd, Option.getD_some, wglE_wgLblP_true]
    · -- the step does not discover the level `v`: the machine does not move at `v`
      have hstep_eq : stepUpd (wgState vs lbl k) (wgStep vs lbl k) v
          = (wgState vs lbl k) v := by
        simp only [stepUpd]
        have hcond : ¬ (v = (wgStep vs lbl k).tgt ∧
            (wgState vs lbl k) (wgStep vs lbl k).tgt = none) := by
          rintro ⟨hvt, hnone⟩
          have htgt : (wgStep vs lbl k).tgt = wgTau vs k := by
            simp only [wgStep, mkSteps_getD_tgt vs lbl hlen k hklt, wgTau]
          have hmem : wgTau vs k ∈ vs.take (k + 1) := by
            by_contra hc
            exact h ⟨hc, (hvt.trans htgt).symm⟩
          have hne : (wgState vs lbl k) (wgTau vs k) ≠ none := by
            simp only [wgState]
            rw [prefixState_ne_none vs lbl hlen k hk']
            exact hmem
          rw [htgt] at hnone
          exact hne hnone
        rw [if_neg hcond]
      simp only [wglE_wgTpAux_succ, if_neg h, ih v hk', hsplit, hstep_eq]

/-! ## The loop facts -/

theorem wgLoop_facts {α : Type u} (vs : List ℤ) (lbl : List (FreeGroup α))
    (hlen : vs.length = lbl.length + 1) :
    (∀ (j : ℕ) (hj : j < lbl.length), wgPath vs (vs.headD 0) (wgLoop vs lbl j) (vs.headD 0)) ∧
    (∀ (j : ℕ) (hj : j < lbl.length), ∀ p ∈ wgLoop vs lbl j, p.1 < lbl.length) ∧
    (∀ (j : ℕ) (hj : j < lbl.length),
      wgWord vs lbl (wgLoop vs lbl j) = stepWord (walkGauge vs lbl) (wgStep vs lbl j)) ∧
    (∀ (j : ℕ) (hj : j < lbl.length) (htree : ¬ wgTree vs j),
      wgMu vs lbl (wgLoop vs lbl j) = FreeGroup.of ⟨j, hj, htree⟩) := by
  classical
  -- the two endpoints of the `j`-th step are levels of the walk
  have hmem_sig : ∀ j : ℕ, j < lbl.length → wgSig vs j ∈ vs.take (lbl.length + 1) := by
    intro j hj
    rw [← hlen, List.take_length]
    refine List.mem_iff_getElem.mpr ⟨j, by omega, ?_⟩
    simp only [wgSig, List.getD_eq_getElem (n := j) vs 0 (by omega)]
  have hmem_tau : ∀ j : ℕ, j < lbl.length → wgTau vs j ∈ vs.take (lbl.length + 1) := by
    intro j hj
    rw [← hlen, List.take_length]
    refine List.mem_iff_getElem.mpr ⟨j + 1, by omega, ?_⟩
    simp only [wgTau, List.getD_eq_getElem (n := j + 1) vs 0 (by omega)]
  -- the state machine after all the steps is the first-arrival gauge
  have hwalk : ∀ v : ℤ, (wgState vs lbl lbl.length v).getD 1 = walkGauge vs lbl v :=
    wglE_wgState_eq_walkGauge vs lbl hlen
  -- a first-arrival path only uses forward tree edges
  have htree : ∀ (v : ℤ) (p : ℕ × Bool), p ∈ wgTpAux vs lbl.length v →
      p.2 = true ∧ wgTree vs p.1 := by
    intro v p hp
    exact ⟨(wglE_wgTpAux_mem vs lbl.length v p hp).1,
      (wglE_wgTpAux_mem vs lbl.length v p hp).2.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the loop is a closed walk at the base level
    intro j hj
    have hp : wgPath vs (vs.headD 0) (wgTpAux vs lbl.length (wgSig vs j)) (wgSig vs j) :=
      wglE_wgTpAux_path vs lbl hlen lbl.length (wgSig vs j) le_rfl (hmem_sig j hj)
    have hq : wgPath vs (wgSig vs j) [(j, true)] (wgTau vs j) := by
      rw [wgPath_cons]
      exact ⟨rfl, rfl⟩
    have hr : wgPath vs (wgTau vs j) (wgRev (wgTpAux vs lbl.length (wgTau vs j))) (vs.headD 0) :=
      wgPath_rev (wglE_wgTpAux_path vs lbl hlen lbl.length (wgTau vs j) le_rfl (hmem_tau j hj))
    have h1 : wgPath vs (vs.headD 0)
        (wgTpAux vs lbl.length (wgSig vs j) ++ [(j, true)]) (wgTau vs j) :=
      wglE_wgPath_append hp hq
    have h2 : wgPath vs (vs.headD 0)
        (wgTpAux vs lbl.length (wgSig vs j) ++ [(j, true)] ++
          wgRev (wgTpAux vs lbl.length (wgTau vs j))) (vs.headD 0) :=
      wglE_wgPath_append h1 hr
    simpa [wgLoop, wgTp] using h2
  · -- the loop only uses edges of the walk
    intro j hj p hp
    simp only [wgLoop, wgTp, List.mem_append, List.mem_singleton, wgRev, List.mem_map,
      List.mem_reverse] at hp
    rcases hp with (hp | hp) | hp
    · exact (wglE_wgTpAux_mem vs lbl.length (wgSig vs j) p hp).2.1
    · rw [hp]
      exact hj
    · obtain ⟨a, ha, hap⟩ := hp
      have hlt := (wglE_wgTpAux_mem vs lbl.length (wgTau vs j) a ha).2.1
      rw [← hap]
      simpa [wgFlip] using hlt
  · -- the image of the loop in the target free group is the loop class of the step
    intro j hj
    have hsrc : wgWord vs lbl (wgTp vs lbl (wgSig vs j)) = walkGauge vs lbl (wgSig vs j) := by
      simp only [wgTp]
      rw [wglE_TpAux_word vs lbl hlen lbl.length (wgSig vs j) le_rfl, hwalk]
    have htau : wgWord vs lbl (wgTp vs lbl (wgTau vs j)) = walkGauge vs lbl (wgTau vs j) := by
      simp only [wgTp]
      rw [wglE_TpAux_word vs lbl hlen lbl.length (wgTau vs j) le_rfl, hwalk]
    simp only [wgLoop]
    rw [wgWord_append, wgWord_append, hsrc, wgWord_singleton, wgWord_rev, htau]
    simp only [stepWord, wgStep, mkSteps_getD_src vs lbl hlen j hj,
      mkSteps_getD_lbl vs lbl hlen j hj, mkSteps_getD_tgt vs lbl hlen j hj,
      wglE_wgLblP_true, wgSig, wgTau, wgLbl]
  · -- the image of a non-tree loop in the fundamental group of the domain is its generator
    intro j hj htree'
    have hsrc : wgMu vs lbl (wgTp vs lbl (wgSig vs j)) = 1 :=
      wglE_wgMu_tree vs lbl (fun p hp => by
        simp only [wgTp] at hp
        exact htree (wgSig vs j) p hp)
    have htau : wgMu vs lbl (wgTp vs lbl (wgTau vs j)) = 1 :=
      wglE_wgMu_tree vs lbl (fun p hp => by
        simp only [wgTp] at hp
        exact htree (wgTau vs j) p hp)
    simp only [wgLoop]
    rw [wgMu_append, wgMu_append, hsrc, wglE_wgMu_single vs lbl hj htree', wgMu_rev, htau]
    simp only [one_mul, inv_one, mul_one]

end Work.OROneRel
