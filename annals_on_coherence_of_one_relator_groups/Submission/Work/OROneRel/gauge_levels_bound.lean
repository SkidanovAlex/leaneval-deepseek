import Mathlib
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs

/-!
# The gauge bound on the number of levels

Let `c : α → ℤ` be a weight function and `u : FreeGroup α` a word.  The decorated word
`decor c 0 (wordOf u)` is a walk on the levels `ℤ`: the `j`-th decorated letter runs from the level
`coverSrc c ·` to the level `coverTgt c ·`.  The *first-arrival gauge* `walkGauge vs lbl` assigns to
each level the word obtained by multiplying the labels along the chain of steps that first discovered
that level.  Every step whose target is discovered by the step itself is then *trivial*, i.e. its
loop class `W (source) * label * (W (target))⁻¹` is `1`.  Since exactly `V - 1` steps are
discovering ones (`V` the number of distinct levels visited), at most `N - (V - 1)` of the `N` steps
can have non-trivial loop class.

This file proves the resulting bound `Work.OROneRel.gauge_levels_bound` for the decorated word of an
arbitrary element `u`, with `V` the number of levels spanned by the decorated letters of `u`.
-/

set_option linter.unusedVariables false

namespace Work.OROneRel

universe u v

variable {α : Type u} {β : Type v}

/-! ## Steps and their loop classes -/

/-- The loop class of a step under a gauge. -/
noncomputable def stepWord (W : ℤ → FreeGroup β) (s : WalkStep β) : FreeGroup β :=
  W s.src * s.lbl * (W s.tgt)⁻¹

/-- A default step, used to extend `List.getD` to all indices. -/
def defaultStep (β : Type v) : WalkStep β := ⟨0, 1, 0⟩

/-- The step carried by a decorated letter.  By `gauge_letter` its loop class under the gauge `W` is
the image of the decorated letter under `gaugeMap W c`. -/
def toStep (c : α → ℤ) (p : (α × ℤ) × Bool) : WalkStep α :=
  ⟨coverSrc c p, coverLetter p, coverTgt c p⟩

theorem decor_map_toStep (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (decor c i L).map (toStep c) =
      mkSteps (running c i L) ((decor c i L).map coverLetter) := by
  induction L generalizing i with
  | nil => simp [decor, running, mkSteps]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [show decor c i ((a, false) :: L) = ((a, i - c a), false) :: decor c (i - c a) L from rfl,
        show running c i ((a, false) :: L) = i :: running c (i - c a) L from rfl]
      rw [List.map_cons, List.map_cons, ih (i - c a)]
      rw [← running_eq_cons_tail c (i - c a) L]
      rw [show mkSteps (i :: (i - c a) :: (running c (i - c a) L).tail)
            (coverLetter ((a, i - c a), false) :: (decor c (i - c a) L).map coverLetter)
          = ⟨i, coverLetter ((a, i - c a), false), i - c a⟩ ::
              mkSteps ((i - c a) :: (running c (i - c a) L).tail)
                ((decor c (i - c a) L).map coverLetter) from rfl]
      rw [← running_eq_cons_tail c (i - c a) L]
      simp only [toStep, coverSrc, coverTgt, Bool.false_eq_true, if_false]
      simp
    · rw [show decor c i ((a, true) :: L) = ((a, i), true) :: decor c (i + c a) L from rfl,
        show running c i ((a, true) :: L) = i :: running c (i + c a) L from rfl]
      rw [List.map_cons, List.map_cons, ih (i + c a)]
      rw [← running_eq_cons_tail c (i + c a) L]
      rw [show mkSteps (i :: (i + c a) :: (running c (i + c a) L).tail)
            (coverLetter ((a, i), true) :: (decor c (i + c a) L).map coverLetter)
          = ⟨i, coverLetter ((a, i), true), i + c a⟩ ::
              mkSteps ((i + c a) :: (running c (i + c a) L).tail)
                ((decor c (i + c a) L).map coverLetter) from rfl]
      rw [← running_eq_cons_tail c (i + c a) L]
      simp only [toStep, coverSrc, coverTgt, if_true]

/-- The step at index `k` of the walk of a decorated word is the step of the `k`-th decorated
letter.  The `getD` formulation avoids any dependent index. -/
theorem getD_map_toStep (c : α → ℤ) (D : List ((α × ℤ) × Bool)) (vs : List ℤ)
    (lbl : List (FreeGroup α)) (hmap : D.map (toStep c) = mkSteps vs lbl)
    (k : ℕ) (hk : k < D.length) :
    (mkSteps vs lbl).getD k (defaultStep α) = toStep c (D[k]'hk) := by
  rw [← hmap, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]

/-! ## The first component of the steps of `mkSteps` -/

theorem running_headD_zero (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (running c i L).headD 0 = i := by
  have h := running_eq_cons_tail c i L
  cases hL : running c i L with
  | nil => exact absurd hL (running_ne_nil c i L)
  | cons x xs =>
    rw [hL, List.tail_cons] at h
    rw [List.headD_cons]
    exact ((List.cons.inj h).1).symm

theorem mkSteps_getD_src (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) (j : ℕ) (hj : j < lbl.length) :
    ((mkSteps vs lbl).getD j (defaultStep β)).src = vs.getD j 0 := by
  rw [← List.getD_map (f := fun s : WalkStep β => s.src)]
  rw [mkSteps_map_src vs lbl hlen]
  simp only [defaultStep]
  rw [List.getD_eq_getElem?_getD, List.getElem?_dropLast, if_pos (by omega),
    ← List.getD_eq_getElem?_getD]

theorem mkSteps_getD_lbl (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) (j : ℕ) (hj : j < lbl.length) :
    ((mkSteps vs lbl).getD j (defaultStep β)).lbl = lbl.getD j 1 := by
  rw [← List.getD_map (f := fun s : WalkStep β => s.lbl)]
  rw [mkSteps_map_lbl vs lbl hlen]
  simp only [defaultStep]

theorem mkSteps_getD_tgt (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) (j : ℕ) (hj : j < lbl.length) :
    ((mkSteps vs lbl).getD j (defaultStep β)).tgt = vs.getD (j + 1) 0 := by
  rw [← List.getD_map (f := fun s : WalkStep β => s.tgt)]
  rw [mkSteps_map_tgt vs lbl hlen]
  simp only [defaultStep]
  rw [List.getD_eq_getElem?_getD, List.getElem?_tail, ← List.getD_eq_getElem?_getD]

/-! ## The state machine of the first-arrival gauge -/

theorem runSteps_cons (acc : ℤ → Option (FreeGroup β)) (s : WalkStep β) (rest : List (WalkStep β)) :
    runSteps acc (s :: rest) = runSteps (stepUpd acc s) rest := by
  simp only [runSteps, List.foldl_cons]

theorem runSteps_append (acc : ℤ → Option (FreeGroup β)) (s t : List (WalkStep β)) :
    runSteps acc (s ++ t) = runSteps (runSteps acc s) t := by
  simp only [runSteps, List.foldl_append]

theorem stepUpd_mono (acc : ℤ → Option (FreeGroup β)) (s : WalkStep β) {x : ℤ}
    {y : FreeGroup β} (h : acc x = some y) : stepUpd acc s x = some y := by
  have hc : ¬ (x = s.tgt ∧ acc s.tgt = none) := by
    rintro ⟨hxt, hst⟩
    rw [hxt] at h
    rw [hst] at h
    exact absurd h (by simp)
  rw [show stepUpd acc s x = acc x from by simp only [stepUpd]; rw [if_neg hc]]
  exact h

theorem runSteps_mono (acc : ℤ → Option (FreeGroup β)) (steps : List (WalkStep β)) {x : ℤ}
    {y : FreeGroup β} (h : acc x = some y) : runSteps acc steps x = some y := by
  induction steps generalizing acc with
  | nil => simpa only [runSteps, List.foldl_nil] using h
  | cons s rest ih => rw [runSteps_cons]; exact ih _ (stepUpd_mono acc s h)

theorem stepUpd_ne_none (acc : ℤ → Option (FreeGroup β)) (s : WalkStep β) (x : ℤ) :
    stepUpd acc s x ≠ none ↔ acc x ≠ none ∨ x = s.tgt := by
  by_cases hx : x = s.tgt
  · rw [hx]
    by_cases hc : acc s.tgt = none
    · simp [stepUpd, hc]
    · simp [stepUpd, hc]
  · simp only [stepUpd]
    rw [if_neg (by rintro ⟨h, -⟩; exact hx h)]
    simp only [ne_eq]
    exact ⟨fun h => Or.inl h, fun h => h.elim id (fun h => absurd h hx)⟩

theorem runSteps_ne_none (acc : ℤ → Option (FreeGroup β)) (steps : List (WalkStep β)) (x : ℤ) :
    runSteps acc steps x ≠ none ↔ acc x ≠ none ∨ ∃ s ∈ steps, s.tgt = x := by
  induction steps generalizing acc with
  | nil => simp only [runSteps, List.foldl_nil]; simp
  | cons s rest ih =>
    rw [runSteps_cons, ih (stepUpd acc s), stepUpd_ne_none]
    constructor
    · rintro ((h | hx) | ⟨t, ht, htx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, List.mem_cons_self .., hx.symm⟩
      · exact Or.inr ⟨t, List.mem_cons_of_mem s ht, htx⟩
    · rintro (h | ⟨t, ht, htx⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp ht with rfl | ht'
        · exact Or.inl (Or.inr htx.symm)
        · exact Or.inr ⟨t, ht', htx⟩

theorem runSteps_triv_step (acc : ℤ → Option (FreeGroup β)) (s : WalkStep β)
    (rest : List (WalkStep β)) (hsrc : acc s.src ≠ none) (htgt : acc s.tgt = none) :
    (runSteps acc (s :: rest) s.src).getD 1 * s.lbl *
        ((runSteps acc (s :: rest) s.tgt).getD 1)⁻¹ = 1 := by
  have hne : s.src ≠ s.tgt := by
    intro h
    rw [h, htgt] at hsrc
    exact hsrc rfl
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hsrc
  have hsrc' : stepUpd acc s s.src = some y := by
    have hc : ¬ (s.src = s.tgt ∧ acc s.tgt = none) := fun h => hne h.1
    rw [show stepUpd acc s s.src = acc s.src from by simp only [stepUpd]; rw [if_neg hc]]
    exact hy.symm
  have htgt' : stepUpd acc s s.tgt = some (y * s.lbl) := by
    rw [show stepUpd acc s s.tgt = some ((acc s.src).getD 1 * s.lbl) from by
      simp [stepUpd, htgt]]
    rw [← hy]
    simp
  rw [runSteps_cons]
  rw [runSteps_mono (stepUpd acc s) rest hsrc', runSteps_mono (stepUpd acc s) rest htgt']
  simp

theorem runSteps_triv_at (acc : ℤ → Option (FreeGroup β)) (steps : List (WalkStep β)) (j : ℕ)
    (hj : j < steps.length)
    (hsrc : (runSteps acc (steps.take j)) ((steps.getD j (defaultStep β)).src) ≠ none)
    (htgt : (runSteps acc (steps.take j)) ((steps.getD j (defaultStep β)).tgt) = none) :
    (runSteps acc steps ((steps.getD j (defaultStep β)).src)).getD 1 *
        ((steps.getD j (defaultStep β)).lbl) *
        ((runSteps acc steps ((steps.getD j (defaultStep β)).tgt)).getD 1)⁻¹ = 1 := by
  have hsrc' : (runSteps acc (steps.take j)) (steps[j]'hj).src ≠ none := by
    rwa [List.getD_eq_getElem _ _ hj] at hsrc
  have htgt' : (runSteps acc (steps.take j)) (steps[j]'hj).tgt = none := by
    rwa [List.getD_eq_getElem _ _ hj] at htgt
  have hdrop : steps.drop j = steps[j] :: steps.drop (j + 1) := List.drop_eq_getElem_cons hj
  have hfun : runSteps acc steps = runSteps (runSteps acc (steps.take j)) (steps.drop j) := by
    conv_lhs => rw [← List.take_append_drop j steps]
    rw [runSteps_append]
  rw [hfun, hdrop]
  rw [show (steps.getD j (defaultStep β)) = steps[j] from List.getD_eq_getElem _ _ hj]
  exact runSteps_triv_step _ _ _ hsrc' htgt'

/-! ## The state after a prefix is exactly the set of levels of the prefix -/

theorem tail_take_eq_take_succ_tail {γ : Type*} (l : List γ) (j : ℕ) :
    l.tail.take j = (l.take (j + 1)).tail := by
  cases l with
  | nil => simp
  | cons a t => rw [List.tail_cons, List.take_succ_cons, List.tail_cons]

theorem mkSteps_take_map_tgt (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) (j : ℕ) :
    ((mkSteps vs lbl).take j).map (fun s => s.tgt) = (vs.take (j + 1)).tail := by
  rw [List.map_take, mkSteps_map_tgt vs lbl hlen, tail_take_eq_take_succ_tail]

theorem prefixState_ne_none (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) (j : ℕ) (hj : j ≤ lbl.length) (x : ℤ) :
    (runSteps (initState (vs.headD 0)) ((mkSteps vs lbl).take j)) x ≠ none ↔
      x ∈ vs.take (j + 1) := by
  rw [runSteps_ne_none]
  have hinit : ((initState (vs.headD 0) : ℤ → Option (FreeGroup β)) x ≠ none) ↔
      x = vs.headD 0 := by simp [initState]
  rw [hinit, ← List.mem_map, mkSteps_take_map_tgt vs lbl hlen]
  have hvne : vs ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hcons : vs.take (j + 1) = vs.headD 0 :: (vs.take (j + 1)).tail := by
    cases vs with
    | nil => exact absurd rfl hvne
    | cons a t => simp [List.take_succ_cons]
  conv_rhs => rw [hcons]
  constructor
  · rintro (h | h)
    · rw [h]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h
  · intro hx
    rcases List.mem_cons.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr h

/-! ## The first-arrival gauge -/

theorem walkGauge_headD (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) : walkGauge vs lbl (vs.headD 0) = 1 := by
  have h : (initState (vs.headD 0) : ℤ → Option (FreeGroup β)) (vs.headD 0) = some 1 := by
    simp [initState]
  have h' : (runSteps (initState (vs.headD 0) : ℤ → Option (FreeGroup β)) (mkSteps vs lbl)
      (vs.headD 0)).getD (1 : FreeGroup β) = 1 := by
    rw [runSteps_mono _ (mkSteps vs lbl) h]
    simp
  rw [walkGauge]
  exact h'

theorem walkGauge_triv (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) (j : ℕ) (hj : j < lbl.length)
    (hnew : vs.getD (j + 1) 0 ∉ vs.take (j + 1)) :
    stepWord (walkGauge vs lbl) ((mkSteps vs lbl).getD j (defaultStep β)) = 1 := by
  have hjsteps : j < (mkSteps vs lbl).length := by rw [mkSteps_length vs lbl hlen]; exact hj
  have hsrc : (runSteps (initState (vs.headD 0)) ((mkSteps vs lbl).take j))
      (((mkSteps vs lbl).getD j (defaultStep β)).src) ≠ none := by
    rw [prefixState_ne_none vs lbl hlen j (le_of_lt hj),
      mkSteps_getD_src vs lbl hlen j hj]
    exact List.mem_take_iff_getElem.mpr ⟨j, by omega,
      (List.getD_eq_getElem vs 0 (by omega)).symm⟩
  have htgt : (runSteps (initState (vs.headD 0)) ((mkSteps vs lbl).take j))
      (((mkSteps vs lbl).getD j (defaultStep β)).tgt) = none := by
    rw [← not_ne_iff, prefixState_ne_none vs lbl hlen j (le_of_lt hj),
      mkSteps_getD_tgt vs lbl hlen j hj]
    exact hnew
  have key := runSteps_triv_at (initState (vs.headD 0)) (mkSteps vs lbl) j hjsteps hsrc htgt
  rw [stepWord, walkGauge]
  exact key

/-! ## Combinatorial inputs (proved separately) -/

/-- **First occurrences exist.**  A value of a list which differs from the first entry occurs at
some index `j + 1 ≥ 1` at which it is *new*, i.e. does not occur in the prefix `l.take (j + 1)`. -/
theorem firstOcc_exists {l : List ℤ} {v : ℤ} (hv : v ∈ l) (hne : v ≠ l.getD 0 0) :
    ∃ j, j + 1 < l.length ∧ l.getD (j + 1) 0 = v ∧ l.getD (j + 1) 0 ∉ l.take (j + 1) := by
  classical
  set P : ℕ → Prop := fun k => k < l.length ∧ l.getD k 0 = v with hP
  have hex : ∃ k, P k := by
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hv
    exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk, hkv]⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀v : l.getD k₀ 0 = v := (Nat.find_spec hex).2
  have hk₀len : k₀ < l.length := (Nat.find_spec hex).1
  have hk₀ne : k₀ ≠ 0 := by
    intro hh
    rw [hh] at hk₀v
    exact hne hk₀v.symm
  refine ⟨k₀ - 1, by omega, by rw [show k₀ - 1 + 1 = k₀ by omega]; exact hk₀v, ?_⟩
  rw [show k₀ - 1 + 1 = k₀ by omega]
  intro hmem
  rw [hk₀v] at hmem
  obtain ⟨m, hm, hmv⟩ := List.mem_take_iff_getElem.mp hmem
  have hmlen : m < l.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
  have hmk : m < k₀ := lt_of_lt_of_le hm (Nat.min_le_left _ _)
  exact Nat.find_min hex hmk ⟨hmlen, by rw [List.getD_eq_getElem _ _ hmlen, hmv]⟩

/-- The number of positions at which a list displays a value not seen before is the number of
distinct values minus one. -/
theorem list_new_steps_card_local (l : List ℤ) (h : l ≠ []) :
    ((Finset.range (l.length - 1)).filter (fun j => l.getD (j + 1) 0 ∉ l.take (j + 1))).card =
      l.toFinset.card - 1 := by
  classical
  have hpos : 0 < l.length := List.length_pos_iff.mpr h
  set S := (Finset.range (l.length - 1)).filter
    (fun j => l.getD (j + 1) 0 ∉ l.take (j + 1)) with hS
  set f : ℕ → ℤ := fun j => l.getD (j + 1) 0 with hf
  have hmemS : ∀ j, j ∈ S ↔ j < l.length - 1 ∧ f j ∉ l.take (j + 1) := by
    intro j
    rw [hS]
    simp only [Finset.mem_filter, Finset.mem_range, hf]
  -- the map `j ↦ l[j+1]` is injective on the set of new positions
  have hinj : Set.InjOn f ↑S := by
    intro j1 h1 j2 h2 heq
    have h1' := (hmemS j1).mp h1
    have h2' := (hmemS j2).mp h2
    rcases lt_trichotomy j1 j2 with hlt | heq' | hgt
    · exfalso
      have hlen1 : j1 + 1 < l.length := by omega
      have hlen2 : j2 + 1 < l.length := by omega
      have hm : f j2 ∈ l.take (j2 + 1) := by
        rw [← heq]
        show l.getD (j1 + 1) 0 ∈ l.take (j2 + 1)
        rw [List.getD_eq_getElem _ _ hlen1]
        exact List.mem_take_iff_getElem.mpr ⟨j1 + 1, by omega, rfl⟩
      exact h2'.2 hm
    · exact heq'
    · exfalso
      have hlen1 : j1 + 1 < l.length := by omega
      have hlen2 : j2 + 1 < l.length := by omega
      have hm : f j1 ∈ l.take (j1 + 1) := by
        rw [heq]
        show l.getD (j2 + 1) 0 ∈ l.take (j1 + 1)
        rw [List.getD_eq_getElem _ _ hlen2]
        exact List.mem_take_iff_getElem.mpr ⟨j2 + 1, by omega, rfl⟩
      exact h1'.2 hm
  -- the image is the set of values of `l` other than the first one
  have himg : f '' ↑S = (↑(l.toFinset \ {l.getD 0 0}) : Set ℤ) := by
    ext v
    constructor
    · rintro ⟨j, hjS, rfl⟩
      have hj' := (hmemS j).mp hjS
      have hlen : j + 1 < l.length := by omega
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
      · exact List.mem_toFinset.mpr (List.mem_iff_getElem.mpr
          ⟨j + 1, hlen, (List.getD_eq_getElem _ _ hlen).symm⟩)
      · simp only [Finset.mem_singleton]
        intro hc
        exact hj'.2 (by
          show l.getD (j + 1) 0 ∈ l.take (j + 1)
          rw [show l.getD (j + 1) 0 = l.getD 0 0 from hc, List.getD_eq_getElem l 0 hpos]
          exact List.mem_take_iff_getElem.mpr ⟨0, by omega, rfl⟩)
    · rintro hv
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hv
      obtain ⟨hv, hne⟩ := hv
      rw [List.mem_toFinset] at hv
      obtain ⟨j, hjlen, hjv, hjnew⟩ := firstOcc_exists hv hne
      exact ⟨j, (hmemS j).mpr ⟨by omega, hjnew⟩, hjv⟩
  have hsub : ({l.getD 0 0} : Finset ℤ) ⊆ l.toFinset := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact List.mem_toFinset.mpr (List.mem_iff_getElem.mpr
      ⟨0, hpos, (List.getD_eq_getElem l 0 hpos).symm⟩)
  calc S.card = (↑S : Set ℕ).ncard := (Set.ncard_coe_finset S).symm
    _ = (f '' ↑S).ncard := (Set.InjOn.ncard_image hinj).symm
    _ = (↑(l.toFinset \ {l.getD 0 0}) : Set ℤ).ncard := by rw [himg]
    _ = (l.toFinset \ {l.getD 0 0}).card := Set.ncard_coe_finset _
    _ = l.toFinset.card - 1 := by
        rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton]

/-! ## The counting argument -/

/-- **The first-arrival gauge bound.**  For a walk with levels `vs` and labels `lbl` there is a
gauge `W` with `W (vs.headD 0) = 1` such that at most `N - (V - 1)` of the `N` steps have
non-trivial loop class, where `V` is the number of distinct levels visited. -/
theorem exists_walk_gauge (vs : List ℤ) (lbl : List (FreeGroup β))
    (hlen : vs.length = lbl.length + 1) :
    ∃ W : ℤ → FreeGroup β, W (vs.headD 0) = 1 ∧
      {j : ℕ | j < lbl.length ∧
        stepWord W ((mkSteps vs lbl).getD j (defaultStep β)) ≠ 1}.ncard ≤
        lbl.length - (vs.toFinset.card - 1) := by
  classical
  set New := (Finset.range lbl.length).filter
    (fun j => vs.getD (j + 1) 0 ∉ vs.take (j + 1)) with hNew
  have hNewcard : New.card = vs.toFinset.card - 1 := by
    rw [hNew, ← list_new_steps_card_local vs (by intro h; rw [h] at hlen; simp at hlen)]
    rw [show vs.length - 1 = lbl.length by omega]
  set G : Finset ℕ := Finset.range lbl.length \ New with hG
  have hsub : {j : ℕ | j < lbl.length ∧
        stepWord (walkGauge vs lbl) ((mkSteps vs lbl).getD j (defaultStep β)) ≠ 1}
      ⊆ ↑G := by
    intro j hj
    obtain ⟨hjl, hjnt⟩ := hj
    have hmem : j ∈ (Finset.range lbl.length : Finset ℕ) := Finset.mem_range.mpr hjl
    have hnot : j ∉ New := by
      rw [hNew]
      simp only [Finset.mem_filter, Finset.mem_range]
      rintro ⟨-, hmiss⟩
      exact hjnt (walkGauge_triv vs lbl hlen j hjl hmiss)
    show j ∈ ↑G
    rw [hG]
    exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hmem, hnot⟩)
  refine ⟨walkGauge vs lbl, walkGauge_headD vs lbl hlen, ?_⟩
  calc {j : ℕ | j < lbl.length ∧
          stepWord (walkGauge vs lbl) ((mkSteps vs lbl).getD j (defaultStep β)) ≠ 1}.ncard
      ≤ (↑G : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet G)
    _ = G.card := by simp
    _ = (Finset.range lbl.length \ New).card := by rw [hG]
    _ = (Finset.range lbl.length).card - New.card :=
        Finset.card_sdiff_of_subset (by rw [hNew]; exact Finset.filter_subset _ _)
    _ = lbl.length - New.card := by rw [Finset.card_range]
    _ = lbl.length - (vs.toFinset.card - 1) := by rw [hNewcard]

/-! ## The bound for the decorated word of an element -/

theorem gauge_levels_bound {α : Type u} (c : α → ℤ) (u : FreeGroup α) :
    ∃ W : ℤ → FreeGroup α, W 0 = 1 ∧
      {p : (α × ℤ) × Bool | p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u) ∧
        Work.OROneRel.gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1}.ncard
      ≤ (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u)).length
        - (({i : ℤ | ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u), Work.OROneRel.coverSrc c p = i}
            ∪ {i : ℤ | ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u), Work.OROneRel.coverTgt c p = i}).ncard - 1) := by
  classical
  set D := decor c 0 (wordOf u) with hD
  set vs := running c 0 (wordOf u) with hvs
  set lbl := D.map coverLetter with hlbl
  have hlen : vs.length = lbl.length + 1 := by
    rw [hvs, hlbl, hD, List.length_map, decor_length, running_length]
  obtain ⟨W, hW, hbound⟩ := exists_walk_gauge vs lbl hlen
  refine ⟨W, ?_, ?_⟩
  · rw [hvs, running_headD_zero c 0 (wordOf u)] at hW
    exact hW
  · have hmap : D.map (toStep c) = mkSteps vs lbl := by
      rw [hvs, hlbl, hD]
      exact decor_map_toStep c 0 (wordOf u)
    have hDlen : D.length = lbl.length := by rw [hlbl, List.length_map]
    -- the indices of the steps with non-trivial loop class
    set T : Finset ℕ := (Finset.range lbl.length).filter
      (fun j => stepWord W ((mkSteps vs lbl).getD j (defaultStep α)) ≠ 1) with hT
    have hTcard : T.card ≤ lbl.length - (vs.toFinset.card - 1) := by
      have hset : (↑T : Set ℕ) = {j : ℕ | j < lbl.length ∧
          stepWord W ((mkSteps vs lbl).getD j (defaultStep α)) ≠ 1} := by
        ext j
        rw [hT]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
      have h1 : (↑T : Set ℕ).ncard = T.card := by simp
      rw [← h1, hset]
      exact hbound
    have hg : ∀ j ∈ T, j < D.length := by
      intro j hj
      rw [hT] at hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      omega
    -- the decorated letters of non-trivial loop class sit at such an index
    set F : Finset ((α × ℤ) × Bool) := T.attach.image (fun j => D[j.1]'(hg j.1 j.2)) with hF
    have hsub : {p : (α × ℤ) × Bool | p ∈ decor c 0 (wordOf u) ∧
        gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1} ⊆ ↑F := by
      rintro p ⟨hpD, hpbad⟩
      rw [← hD] at hpD
      obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hpD
      have hkT : k ∈ T := by
        rw [hT]
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [getD_map_toStep c D vs lbl hmap k hk]
        exact fun hcon => hpbad (by rw [gauge_letter W c p, ← hkp]; exact hcon)
      rw [hF]
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨k, hkT⟩, ?_, ?_⟩)
      · exact Finset.mem_attach T ⟨k, hkT⟩
      · show D[k]'(hg k hkT) = p
        rw [hkp]
    calc {p : (α × ℤ) × Bool | p ∈ decor c 0 (wordOf u) ∧
            gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1}.ncard
        ≤ (↑F : Set ((α × ℤ) × Bool)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet F)
      _ = F.card := by simp
      _ ≤ T.attach.card := by rw [hF]; exact Finset.card_image_le
      _ = T.card := Finset.card_attach
      _ ≤ lbl.length - (vs.toFinset.card - 1) := hTcard
      _ ≤ (decor c 0 (wordOf u)).length -
            (({i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i}
              ∪ {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i}).ncard - 1) := by
          have hlev : ({i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i} ∪
              {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i}) ⊆ ↑vs.toFinset := by
            rintro i (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
            · have hmem : coverSrc c p ∈ (decor c 0 (wordOf u)).map (coverSrc c) :=
                List.mem_map_of_mem hp
              rw [decor_map_coverSrc, ← hvs] at hmem
              exact List.mem_toFinset.mpr (List.mem_of_mem_dropLast hmem)
            · have hmem : coverTgt c p ∈ (decor c 0 (wordOf u)).map (coverTgt c) :=
                List.mem_map_of_mem hp
              rw [decor_map_coverTgt, ← hvs] at hmem
              exact List.mem_toFinset.mpr (List.mem_of_mem_tail hmem)
          have hle : ({i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i} ∪
              {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i}).ncard
              ≤ vs.toFinset.card := by
            have h := Set.ncard_le_ncard hlev (Finset.finite_toSet vs.toFinset)
            rw [Set.ncard_coe_finset] at h
            exact h
          rw [hlbl, List.length_map]
          exact Nat.sub_le_sub_left (Nat.sub_le_sub_right hle 1) _

end Work.OROneRel
