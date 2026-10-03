import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.rhoC_injective_range
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.range_presentedGroupMap
/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The weighted Magnus rewriting: definitions

Definitions of the *weighted* Magnus--Moldavanskii step used by
`Submission.Work.OROneRel.magnusStepCase2_of_weight`.  The symbol `(x,i)` (`x ≠ t`) of the base group
stands for the conjugate `t ^ i * x * t ^ (-i - c x)` (`wrho`), the loop class of the edge `(x,i)` of
the `ℤ`-cover induced by the integer weight `c` (with `c t = 1`); the `t`-symbols have trivial loop
class and are deleted (`wvListAux`).  `wDecs`, `wLo`, `wHi`, `wDecSet`, `wBeta`, `wBetaOf`, `wWL`,
`wW`, `wTA`, `wTB`, `wA`, `wB`, `wTshift`, `wIsoA`, `wIsoB`, `wPhi`, `wBaseHom`, `wK`, `wThetaFun`
are the weighted analogues of the combinatorics of the classical (`eps t`) Magnus rewriting
(`Submission.Work.OROneRel.mmStepData_of_expsum_zero`).

Definitions and proven basic lemmas only (no `sorry`), so that lemma requests may import it.
-/
namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The weighted Magnus map -/

/-- The generating type of the base group of the weighted Magnus step: the symbols `(x,i)` with
`x ≠ t`. -/
abbrev WgtBeta (t : α) : Type u := {x : α // x ≠ t} × ℤ

/-- The weighted Magnus map `F(WgtBeta t) →* F α` sending the symbol `(x,i)` to the conjugate
`t ^ i * x * t ^ (-i - c x)`. -/
noncomputable def wrho (t : α) (c : α → ℤ) : FreeGroup (WgtBeta t) →* FreeGroup α :=
  (rhoC (FreeGroup.of t) c).comp (FreeGroup.map fun p : WgtBeta t => ((p.1 : α), p.2))

theorem wrho_of (t : α) (c : α → ℤ) (p : WgtBeta t) :
    wrho t c (FreeGroup.of p) =
      FreeGroup.of t ^ p.2 * FreeGroup.of (p.1 : α) * FreeGroup.of t ^ (-(p.2) - c p.1) := by
  rw [wrho, MonoidHom.comp_apply, FreeGroup.map.of]
  exact rhoC_of (FreeGroup.of t) c ((p.1 : α), p.2)

/-- **Injectivity and range of the weighted Magnus map.**  This is `rhoC_injective_range` read in the
vocabulary of `wrho`. -/
theorem wrho_injective_range (t : α) (c : α → ℤ) (hc : c t = 1) :
    Function.Injective (wrho (α := α) t c) ∧
      (wrho (α := α) t c).range = (cohom c).ker :=
  rhoC_injective_range t c hc

/-! ## The decorated word with the `t`-symbols deleted -/

/-- `decor` with the `t`-symbols deleted, over the generating type `WgtBeta t`. -/
noncomputable def wvListAux [DecidableEq α] (c : α → ℤ) (t : α) :
    ℤ → List (α × Bool) → List (WgtBeta t × Bool)
  | _, [] => []
  | i, (a, true) :: L =>
      (if h : a = t then [] else [((⟨a, h⟩, i), true)]) ++ wvListAux c t (i + c a) L
  | i, (a, false) :: L =>
      (if h : a = t then [] else [((⟨a, h⟩, i - c a), false)]) ++ wvListAux c t (i - c a) L

/-- The rooted relator of the weighted Magnus step: the decorated word of `u` with the `t`-symbols
deleted. -/
noncomputable def wv [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) :
    FreeGroup (WgtBeta t) :=
  FreeGroup.mk (wvListAux c t 0 (wordOf u))

private theorem mk_nil {β : Type*} : FreeGroup.mk ([] : List (β × Bool)) = 1 := rfl

private theorem mk_cons_true {β : Type*} (q : β) (L : List (β × Bool)) :
    FreeGroup.mk ((q, true) :: L) = FreeGroup.of q * FreeGroup.mk L := by
  rw [FreeGroup.of, FreeGroup.mul_mk]; rfl

private theorem mk_cons_false {β : Type*} (q : β) (L : List (β × Bool)) :
    FreeGroup.mk ((q, false) :: L) = (FreeGroup.of q)⁻¹ * FreeGroup.mk L := by
  rw [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk]; rfl

/-- **The telescoping identity of the weighted rewriting.**  The images under `wrho` of the deformed
word (with the `t`-symbols deleted) and the images under `gaugeMap` of the full decorated word agree:
the deleted `t`-symbols have trivial image because `c t = 1`. -/
theorem wrho_mk_wvListAux [DecidableEq α] (c : α → ℤ) (t : α) (hct : c t = 1) (i : ℤ)
    (L : List (α × Bool)) :
    wrho t c (FreeGroup.mk (wvListAux c t i L))
      = gaugeMap (fun m : ℤ => FreeGroup.of t ^ m) c (FreeGroup.mk (decor c i L)) := by
  have hkeyT : ∀ j : ℤ,
      gaugeMap (fun m : ℤ => FreeGroup.of t ^ m) c (FreeGroup.of ((t, j) : α × ℤ)) = 1 := by
    intro j
    rw [gaugeMap_of, show (j : ℤ) + c t = j + 1 from by rw [hct]]
    group
  have hkeyTinv : ∀ j : ℤ,
      gaugeMap (fun m : ℤ => FreeGroup.of t ^ m) c ((FreeGroup.of ((t, j) : α × ℤ))⁻¹) = 1 := by
    intro j
    rw [map_inv, hkeyT j, inv_one]
  induction L generalizing i with
  | nil =>
      rw [show wvListAux c t i ([] : List (α × Bool)) = [] from rfl,
        show decor c i ([] : List (α × Bool)) = [] from rfl, mk_nil, mk_nil, map_one, map_one]
  | cons p L ih =>
      obtain ⟨a, b⟩ := p
      cases b
      · -- inverse letter
        rw [show wvListAux c t i ((a, false) :: L) =
              (if h : a = t then [] else [(((⟨a, h⟩, i - c a) : WgtBeta t), false)])
                ++ wvListAux c t (i - c a) L from rfl]
        rw [show decor c i ((a, false) :: L) = ((a, i - c a), false) :: decor c (i - c a) L from rfl]
        by_cases ha : a = t
        · rw [ha, dif_pos rfl, List.nil_append, ih (i - c t), mk_cons_false, map_mul,
            hkeyTinv (i - c t), one_mul]
        · rw [dif_neg ha, List.singleton_append, mk_cons_false, map_mul, map_inv, wrho_of,
            ih (i - c a), mk_cons_false, map_mul, map_inv, gaugeMap_of]
          group
      · -- direct letter
        rw [show wvListAux c t i ((a, true) :: L) =
              (if h : a = t then [] else [(((⟨a, h⟩, i) : WgtBeta t), true)])
                ++ wvListAux c t (i + c a) L from rfl]
        rw [show decor c i ((a, true) :: L) = ((a, i), true) :: decor c (i + c a) L from rfl]
        by_cases ha : a = t
        · rw [ha, dif_pos rfl, List.nil_append, ih (i + c t), mk_cons_true, map_mul,
            hkeyT i, one_mul]
        · rw [dif_neg ha, List.singleton_append, mk_cons_true, map_mul, wrho_of, ih (i + c a),
            mk_cons_true, map_mul, gaugeMap_of]
          group

/-- **The rooted relator maps to `u`.**  This is the weighted counterpart of the telescoping identity
`gauge_decor_zero`. -/
theorem wrho_wv [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) (hct : c t = 1)
    (hu : cohom c u = 1) :
    wrho t c (wv c t u) = u := by
  rw [wv, wrho_mk_wvListAux c t hct 0 (wordOf u)]
  exact gauge_decor_zero (fun m : ℤ => FreeGroup.of t ^ m) (zpow_zero _) hu

/-! ## The norm of the rooted relator -/

theorem wvListAux_length_le [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ) (L : List (α × Bool)) :
    (wvListAux c t i L).length ≤ L.length := by
  induction L generalizing i with
  | nil => simp [wvListAux]
  | cons p L ih =>
      obtain ⟨a, b⟩ := p
      cases b
      · rw [show wvListAux c t i ((a, false) :: L) =
            (if h : a = t then [] else [(((⟨a, h⟩, i - c a) : WgtBeta t), false)])
              ++ wvListAux c t (i - c a) L from rfl]
        by_cases ha : a = t
        · rw [dif_pos ha, List.nil_append, List.length_cons]
          exact Nat.le_succ_of_le (ih (i - c a))
        · rw [dif_neg ha, List.singleton_append, List.length_cons, List.length_cons]
          exact Nat.succ_le_succ (ih (i - c a))
      · rw [show wvListAux c t i ((a, true) :: L) =
            (if h : a = t then [] else [(((⟨a, h⟩, i) : WgtBeta t), true)])
              ++ wvListAux c t (i + c a) L from rfl]
        by_cases ha : a = t
        · rw [dif_pos ha, List.nil_append, List.length_cons]
          exact Nat.le_succ_of_le (ih (i + c a))
        · rw [dif_neg ha, List.singleton_append, List.length_cons, List.length_cons]
          exact Nat.succ_le_succ (ih (i + c a))

theorem wvListAux_length_lt [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ) (L : List (α × Bool))
    (h : ∃ b, (t, b) ∈ L) : (wvListAux c t i L).length < L.length := by
  induction L generalizing i with
  | nil => obtain ⟨b, hb⟩ := h; simp at hb
  | cons p L ih =>
      obtain ⟨a, b'⟩ := p
      obtain ⟨b, hb⟩ := h
      cases b'
      · rw [show wvListAux c t i ((a, false) :: L) =
            (if h : a = t then [] else [(((⟨a, h⟩, i - c a) : WgtBeta t), false)])
              ++ wvListAux c t (i - c a) L from rfl]
        by_cases ha : a = t
        · rw [dif_pos ha, List.nil_append, List.length_cons]
          exact Nat.lt_succ_of_le (wvListAux_length_le c t (i - c a) L)
        · rw [dif_neg ha, List.singleton_append, List.length_cons, List.length_cons]
          rcases List.mem_cons.mp hb with hb | hb
          · rw [Prod.mk.injEq] at hb
            exact absurd hb.1.symm ha
          · exact Nat.succ_lt_succ (ih (i - c a) ⟨b, hb⟩)
      · rw [show wvListAux c t i ((a, true) :: L) =
            (if h : a = t then [] else [(((⟨a, h⟩, i) : WgtBeta t), true)])
              ++ wvListAux c t (i + c a) L from rfl]
        by_cases ha : a = t
        · rw [dif_pos ha, List.nil_append, List.length_cons]
          exact Nat.lt_succ_of_le (wvListAux_length_le c t (i + c a) L)
        · rw [dif_neg ha, List.singleton_append, List.length_cons, List.length_cons]
          rcases List.mem_cons.mp hb with hb | hb
          · rw [Prod.mk.injEq] at hb
            exact absurd hb.1.symm ha
          · exact Nat.succ_lt_succ (ih (i + c a) ⟨b, hb⟩)

/-- **The rooted relator is strictly shorter than `u`.** -/
theorem relatorNorm_wv_lt [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (ht : t ∈ relatorLetters u) :
    relatorNorm (wv c t u) < relatorNorm u := by
  classical
  have hb' : ∃ b, (t, b) ∈ wordOf u := by
    rw [relatorLetters] at ht
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, by simpa [wordOf] using hb⟩
  have hnorm : relatorNorm (wv c t u) ≤ (wvListAux c t 0 (wordOf u)).length := by
    rw [wv, relatorNorm]
    exact @FreeGroup.norm_mk_le (WgtBeta t) (wvListAux c t 0 (wordOf u)) (Classical.decEq _)
  have hlt : (wvListAux c t 0 (wordOf u)).length < (wordOf u).length :=
    wvListAux_length_lt c t 0 (wordOf u) hb'
  have hword : (wordOf u).length = relatorNorm u := by rw [relatorNorm, wordOf]; rfl
  exact lt_of_le_of_lt hnorm (hword ▸ hlt)

/-- **The rooted relator is not a proper power.** -/
theorem not_isProperPower_wv [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) (hct : c t = 1)
    (hu : cohom c u = 1) (hpp : ¬ IsProperPower u) :
    ¬ IsProperPower (wv c t u) := by
  rintro ⟨z, k, hk, hzk⟩
  refine hpp ⟨wrho t c z, k, hk, ?_⟩
  rw [← wrho_wv c t u hct hu, hzk, map_pow]

/-! ## The weighted Magnus rewriting -/

variable (c : α → ℤ) (t : α) (u : FreeGroup α)

/-- The (finitely many) weights at which the letter `x` occurs in the deformed word of `u`. -/
noncomputable def wDecs [DecidableEq α] (x : {x : α // x ≠ t}) : Finset ℤ := by
  classical
  exact ((wvListAux c t 0 (wordOf u)).filterMap
    (fun p => if p.1.1 = x then some p.1.2 else none)).toFinset

theorem mem_wDecs_iff [DecidableEq α] (x : {x : α // x ≠ t}) (k : ℤ) :
    k ∈ wDecs c t u x ↔ ∃ b : Bool, ((x, k), b) ∈ wvListAux c t 0 (wordOf u) := by
  classical
  rw [wDecs, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hpx⟩
    by_cases hq : p.1.1 = x
    · rw [if_pos hq] at hpx
      have hk : p.1.2 = k := Option.some.inj hpx
      have hp' : p.1 = (x, k) := Prod.ext hq hk
      refine ⟨p.2, ?_⟩
      rw [← hp']; exact hp
    · rw [if_neg hq] at hpx
      exact absurd hpx (by simp)
  · rintro ⟨b, hb⟩
    exact ⟨((x, k), b), hb, by simp⟩

/-- The lowest weight at which `x` occurs (`0` if `x` does not occur). -/
noncomputable def wLo [DecidableEq α] (x : {x : α // x ≠ t}) : ℤ := by
  classical
  exact if h : (wDecs c t u x).Nonempty then (wDecs c t u x).min' h else 0

/-- The highest weight at which `x` occurs (`0` if `x` does not occur). -/
noncomputable def wHi [DecidableEq α] (x : {x : α // x ≠ t}) : ℤ := by
  classical
  exact if h : (wDecs c t u x).Nonempty then (wDecs c t u x).max' h else 0

/-- The interval closure of the occurring weights of `x`. -/
noncomputable def wDecSet [DecidableEq α] : Set (WgtBeta t) :=
  {p | wLo c t u p.1 ≤ p.2 ∧ p.2 ≤ wHi c t u p.1}

/-- The generating type of the base of the weighted Magnus step: the symbols `(x,i)` with `x ≠ t`
and `i` in the interval closure of the occurring weights. -/
abbrev wBeta [DecidableEq α] : Type u := {p : WgtBeta t // p ∈ wDecSet c t u}

noncomputable instance wBetaDecEq [DecidableEq α] : DecidableEq (wBeta c t u) := Classical.decEq _

theorem wLo_le_hi [DecidableEq α] (x : {x : α // x ≠ t}) : wLo c t u x ≤ wHi c t u x := by
  classical
  rw [wLo, wHi]
  by_cases h : (wDecs c t u x).Nonempty
  · simp only [dif_pos h]
    exact Finset.min'_le _ _ (Finset.max'_mem _ h)
  · simp only [dif_neg h]
    exact le_refl 0

theorem wLo_mem_decSet [DecidableEq α] (x : {x : α // x ≠ t}) :
    (x, wLo c t u x) ∈ wDecSet c t u :=
  ⟨le_refl _, wLo_le_hi c t u x⟩

theorem wHi_mem_decSet [DecidableEq α] (x : {x : α // x ≠ t}) :
    (x, wHi c t u x) ∈ wDecSet c t u :=
  ⟨wLo_le_hi c t u x, le_refl _⟩

theorem wDecSet_def [DecidableEq α] {p : WgtBeta t} :
    p ∈ wDecSet c t u ↔ wLo c t u p.1 ≤ p.2 ∧ p.2 ≤ wHi c t u p.1 := Iff.rfl

/-- The symbol of the interval closure associated with a weight-decorated letter. -/
noncomputable def wBetaOf [DecidableEq α] (p : WgtBeta t) : wBeta c t u := by
  classical
  exact if h : p ∈ wDecSet c t u then ⟨p, h⟩
    else ⟨(p.1, wLo c t u p.1), wLo_mem_decSet c t u p.1⟩

theorem wBetaOf_val [DecidableEq α] {p : WgtBeta t} (hp : p ∈ wDecSet c t u) :
    (wBetaOf c t u p).1 = p := by
  classical
  rw [wBetaOf]; simp only [dif_pos hp]

theorem wList_mem_decSet [DecidableEq α] {p : WgtBeta t} {b : Bool}
    (h : (p, b) ∈ wvListAux c t 0 (wordOf u)) : p ∈ wDecSet c t u := by
  classical
  have hk : p.2 ∈ wDecs c t u p.1 := (mem_wDecs_iff c t u p.1 p.2).mpr ⟨b, h⟩
  have hne : (wDecs c t u p.1).Nonempty := ⟨p.2, hk⟩
  constructor
  · rw [wLo, dif_pos hne]
    exact Finset.min'_le _ _ hk
  · rw [wHi, dif_pos hne]
    exact Finset.le_max' _ _ hk

/-- The decorated word of `u`, viewed in the interval-closed symbol type. -/
noncomputable def wWL [DecidableEq α] : List (wBeta c t u × Bool) := by
  classical
  exact (wvListAux c t 0 (wordOf u)).map (fun p => (wBetaOf c t u p.1, p.2))

/-- The rooted relator of the weighted Magnus step. -/
noncomputable def wW [DecidableEq α] : FreeGroup (wBeta c t u) :=
  FreeGroup.mk (wWL c t u)

theorem wWL_map_val [DecidableEq α] :
    (wWL c t u).map (fun q => ((q.1.1 : WgtBeta t), q.2)) = wvListAux c t 0 (wordOf u) := by
  classical
  rw [wWL, List.map_map]
  trans (wvListAux c t 0 (wordOf u)).map id
  · apply List.map_congr_left
    intro p hp
    exact Prod.ext (wBetaOf_val c t u (wList_mem_decSet c t u hp)) rfl
  · exact List.map_id _

theorem wW_map_val [DecidableEq α] :
    FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (wW c t u)
      = FreeGroup.mk (wvListAux c t 0 (wordOf u)) := by
  classical
  rw [wW, FreeGroup.map.mk]
  congr 1
  exact wWL_map_val c t u

/-- The expansion of the base word is `u`. -/
theorem wrho_wW [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1) :
    wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (wW c t u)) = u := by
  rw [wW_map_val]
  exact wrho_wv c t u hct hu

/-- The first associated generating set: the symbols whose shift is still a symbol. -/
abbrev wTA [DecidableEq α] : Set (wBeta c t u) :=
  {e | (((e.1.1 : {x : α // x ≠ t}), e.1.2 + 1) : WgtBeta t) ∈ wDecSet c t u}

/-- The second associated generating set. -/
abbrev wTB [DecidableEq α] : Set (wBeta c t u) :=
  {e | (((e.1.1 : {x : α // x ≠ t}), e.1.2 - 1) : WgtBeta t) ∈ wDecSet c t u}

noncomputable def wA [DecidableEq α] :
    Subgroup (PresentedGroup ({wW c t u} : Set (FreeGroup (wBeta c t u)))) :=
  magnusSubgroupOf (wW c t u) (wTA c t u)

noncomputable def wB [DecidableEq α] :
    Subgroup (PresentedGroup ({wW c t u} : Set (FreeGroup (wBeta c t u)))) :=
  magnusSubgroupOf (wW c t u) (wTB c t u)

/-- The shift of the decorations, an equivalence `wTA ≃ wTB`. -/
noncomputable def wTshift [DecidableEq α] : wTA c t u ≃ wTB c t u where
  toFun e :=
    ⟨⟨(e.1.1.1, e.1.1.2 + 1), by
        simpa only [wTA, wDecSet, Set.mem_ofPred_eq] using e.2⟩, by
      show ((e.1.1.1, e.1.1.2 + 1 - 1) : WgtBeta t) ∈ wDecSet c t u
      rw [show ((e.1.1.1, e.1.1.2 + 1 - 1) : WgtBeta t) = (e.1.1.1, e.1.1.2) from by simp]
      simpa only [wDecSet, Set.mem_ofPred_eq] using e.1.2⟩
  invFun e :=
    ⟨⟨(e.1.1.1, e.1.1.2 - 1), by
        simpa only [wTB, wDecSet, Set.mem_ofPred_eq] using e.2⟩, by
      show ((e.1.1.1, e.1.1.2 - 1 + 1) : WgtBeta t) ∈ wDecSet c t u
      rw [show ((e.1.1.1, e.1.1.2 - 1 + 1) : WgtBeta t) = (e.1.1.1, e.1.1.2) from by simp]
      simpa only [wDecSet, Set.mem_ofPred_eq] using e.1.2⟩
  left_inv e := by ext <;> simp
  right_inv e := by ext <;> simp


/-! ## The associated subgroups, the base homomorphism and the two maps -/

section Phi

variable {c : α → ℤ} {t : α} {u : FreeGroup α}

/-- The isomorphism from the free group on the decorations of `wTA` onto the Magnus subgroup
`wA`, induced by the canonical map `F(T) →* ⟨β | w⟩` (injective by the Freiheitssatz). -/
noncomputable def wIsoA [DecidableEq α]
    (hFw : FreiheitssatzAt (wW c t u))
    (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u)) :
    FreeGroup (wTA c t u) ≃* wA c t u :=
  (MonoidHom.ofInjective (f := presentedGroupMap (wW c t u) (wTA c t u))
      (hFw hc (wTA c t u) hA)).trans
    (MulEquiv.subgroupCongr (range_presentedGroupMap (wW c t u) (wTA c t u)))

noncomputable def wIsoB [DecidableEq α]
    (hFw : FreiheitssatzAt (wW c t u))
    (hc : IsCyclicallyReducedRelator (wW c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) :
    FreeGroup (wTB c t u) ≃* wB c t u :=
  (MonoidHom.ofInjective (f := presentedGroupMap (wW c t u) (wTB c t u))
      (hFw hc (wTB c t u) hB)).trans
    (MulEquiv.subgroupCongr (range_presentedGroupMap (wW c t u) (wTB c t u)))

noncomputable def wGA [DecidableEq α] (e : wTA c t u) : wA c t u :=
  ⟨PresentedGroup.of (e : wBeta c t u), Subgroup.subset_closure ⟨e, rfl⟩⟩

noncomputable def wGB [DecidableEq α] (e : wTB c t u) : wB c t u :=
  ⟨PresentedGroup.of (e : wBeta c t u), Subgroup.subset_closure ⟨e, rfl⟩⟩

/-- The isomorphism between the two associated Magnus subgroups induced by the shift of the
decorations. -/
noncomputable def wPhi [DecidableEq α]
    (hFw : FreiheitssatzAt (wW c t u))
    (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) :
    wA c t u ≃* wB c t u :=
  (wIsoA (c := c) (t := t) (u := u) hFw hc hA).symm.trans
    ((FreeGroup.freeGroupCongr (wTshift c t u)).trans (wIsoB (c := c) (t := t) (u := u) hFw hc hB))

end Phi

section BaseHom

variable {c : α → ℤ} {t : α} {u : FreeGroup α}

/-- The canonical map `⟨β | w⟩ →* ⟨α | u⟩` sending the decoration `(x,k)` to the conjugate
`t ^ k * x * t ^ (-k - c x)`. -/
noncomputable def wBaseHom [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1) :
    PresentedGroup ({wW c t u} : Set (FreeGroup (wBeta c t u))) →*
      PresentedGroup ({u} : Set (FreeGroup α)) :=
  PresentedGroup.toGroup (f := fun p : wBeta c t u =>
    PresentedGroup.mk ({u} : Set (FreeGroup α))
      (wrho t c (FreeGroup.of (p.1 : WgtBeta t)))) (by
      intro rel hrel
      rw [Set.mem_singleton_iff] at hrel
      subst hrel
      have hcomp : FreeGroup.lift (fun p : wBeta c t u =>
          PresentedGroup.mk ({u} : Set (FreeGroup α))
            (wrho t c (FreeGroup.of (p.1 : WgtBeta t)))) =
          (PresentedGroup.mk ({u} : Set (FreeGroup α))).comp
            ((wrho t c).comp (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)))) := by
        refine FreeGroup.ext_hom _ _ fun p => ?_
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, FreeGroup.map.of,
          FreeGroup.lift_apply_of]
      rw [hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply, wW_map_val,
        show FreeGroup.mk (wvListAux c t 0 (wordOf u)) = wv c t u from rfl,
        wrho_wv c t u hct hu]
      exact PresentedGroup.one_of_mem (Set.mem_singleton u))

theorem wBaseHom_gen [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1) (p : wBeta c t u) :
    wBaseHom (c := c) (t := t) (u := u) hct hu (PresentedGroup.of p) =
      (PresentedGroup.of t : PresentedGroup ({u} : Set (FreeGroup α))) ^ (p.1.2) *
        (PresentedGroup.of (p.1.1 : α)) *
        (PresentedGroup.of t : PresentedGroup ({u} : Set (FreeGroup α))) ^ (-(p.1.2) - c (p.1.1 : α)) := by
  rw [wBaseHom, PresentedGroup.toGroup.of, wrho_of]
  simp only [PresentedGroup.of, map_mul, map_zpow]

end BaseHom

/-- The base group `⟨β | w⟩` of the weighted Magnus rewriting. -/
abbrev wH [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) : Type u :=
  PresentedGroup ({wW c t u} : Set (FreeGroup (wBeta c t u)))

/-- The one-relator group `⟨α | u⟩`. -/
abbrev wG (u : FreeGroup α) : Type u := PresentedGroup ({u} : Set (FreeGroup α))

/-- The HNN extension in which `⟨α | u⟩` embeds. -/
noncomputable abbrev wK [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u))
    (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) : Type u :=
  HNNExtension (wH c t u) (wA c t u) (wB c t u) (wPhi (c := c) (t := t) (u := u) hFw hc hA hB)


/-- The images of the generators of `⟨α | u⟩` under the map to the HNN extension: the generator `t`
goes to the stable letter, and `y ≠ t` to the loop class of the lowest `y`-symbol, corrected by the
weight twist `t ^ (c y)`. -/
noncomputable def wThetaFun [DecidableEq α] (hFw : FreiheitssatzAt (wW c t u))
    (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) :
    α → wK c t u hFw hc hA hB := by
  classical
  exact fun y => if hy : y = t then (HNNExtension.t : wK c t u hFw hc hA hB)
    else (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(wLo c t u ⟨y, hy⟩)) *
      HNNExtension.of (PresentedGroup.of
        (wBetaOf c t u ((⟨y, hy⟩, wLo c t u ⟨y, hy⟩) : WgtBeta t))) *
      (HNNExtension.t : wK c t u hFw hc hA hB) ^ (wLo c t u ⟨y, hy⟩ + c y)

/-- The map `⟨α | u⟩ →* wK` induced by `wThetaFun`, well defined because the relator maps to `1`. -/
noncomputable def wTheta [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hrel : FreeGroup.lift (wThetaFun c t u hFw hc hA hB) u = 1) :
    wG u →* wK c t u hFw hc hA hB :=
  PresentedGroup.toGroup (f := wThetaFun c t u hFw hc hA hB) (by
    intro rel hrel'
    rw [Set.mem_singleton_iff] at hrel'
    subst hrel'
    exact hrel)

/-- The canonical map `wK →* ⟨α | u⟩`, the inverse of `wTheta`. -/
noncomputable def wPsi [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hcompat : ∀ a : wA c t u,
      (PresentedGroup.of t : wG u) * wBaseHom (c := c) (t := t) (u := u) hct hu (a : wH c t u)
        = wBaseHom (c := c) (t := t) (u := u) hct hu
            ((wPhi (c := c) (t := t) (u := u) hFw hc hA hB a : wB c t u) : wH c t u) *
          (PresentedGroup.of t : wG u)) :
    wK c t u hFw hc hA hB →* wG u :=
  HNNExtension.lift (wBaseHom (c := c) (t := t) (u := u) hct hu) (PresentedGroup.of t) hcompat

/-- The iterated-conjugation ("chain") statement in the HNN extension `wK`. -/
abbrev wChainHyp [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) : Prop :=
  ∀ (x : {x : α // x ≠ t}) (i : ℤ) (hi : ((x, i) : WgtBeta t) ∈ wDecSet c t u),
    ∀ (m : ℕ), (∀ s : ℕ, s < m → ((x, i + s + 1) : WgtBeta t) ∈ wDecSet c t u) →
      (HNNExtension.t : wK c t u hFw hc hA hB) ^ (m : ℤ) *
          HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i) : WgtBeta t))) *
          (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(m : ℤ))
        = HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i + m) : WgtBeta t)))

/-- The value of `wPhi` on the generator attached to a symbol of `wTA`. -/
abbrev wPhiOfHyp [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) : Prop :=
  ∀ (p : wBeta c t u) (hy : PresentedGroup.of p ∈ wA c t u) (hp : p ∈ wTA c t u),
    ((wPhi (c := c) (t := t) (u := u) hFw hc hA hB ⟨PresentedGroup.of p, hy⟩ : wB c t u) : wH c t u)
      = PresentedGroup.of (wBetaOf c t u ((p.1.1, p.1.2 + 1) : WgtBeta t))

/-- The compatibility of the base map with the HNN relation. -/
abbrev wCompatHyp [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) (hct : c t = 1)
    (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) : Prop :=
  ∀ a : wA c t u,
    (PresentedGroup.of t : wG u) * wBaseHom (c := c) (t := t) (u := u) hct hu (a : wH c t u)
      = wBaseHom (c := c) (t := t) (u := u) hct hu
          ((wPhi (c := c) (t := t) (u := u) hFw hc hA hB a : wB c t u) : wH c t u) *
        (PresentedGroup.of t : wG u)

theorem wTheta_of [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hrel : FreeGroup.lift (wThetaFun c t u hFw hc hA hB) u = 1) (y : α) :
    wTheta c t u hFw hc hA hB hrel (PresentedGroup.of y) = wThetaFun c t u hFw hc hA hB y := by
  rw [wTheta, PresentedGroup.toGroup.of]

end Work.OROneRel
