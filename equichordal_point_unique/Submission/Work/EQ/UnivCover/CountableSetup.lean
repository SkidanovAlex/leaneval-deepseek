import Mathlib
import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Cover

set_option autoImplicit false
open _root_.Topology
open scoped Topology unitInterval
open Classical

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X]

section Step

/-- A single "move" of the combinatorial description of the universal cover: from the point `e`
(lying over `U n`), append a path inside the disc-like set `U n` to reach the point over `y`.
Falls back to `e` when the hypotheses fail (junk value). -/
noncomputable def step (U : ℕ → Set X) (hU : DiscCover U) {x₀ : X} (e : UC x₀) (n : ℕ) (y : X) :
    UC x₀ :=
  if h : e.pt ∈ U n ∧ y ∈ U n then sectOf (U n) (hU.1 n) e h.1 y h.2 else e

theorem step_of_mem {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} {e : UC x₀} {n : ℕ} {y : X}
    (h : e.pt ∈ U n ∧ y ∈ U n) :
    step U hU e n y = sectOf (U n) (hU.1 n) e h.1 y h.2 :=
  dif_pos h

theorem step_pt {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} {e : UC x₀} {n : ℕ} {y : X}
    (h : e.pt ∈ U n ∧ y ∈ U n) : (step U hU e n y).pt = y := by
  rw [step_of_mem h]

theorem step_of_not_mem {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} {e : UC x₀} {n : ℕ} {y : X}
    (h : ¬ (e.pt ∈ U n ∧ y ∈ U n)) : step U hU e n y = e :=
  dif_neg h

/-- Two consecutive steps, where the middle point is moved within a single path component of the
intersection `U n ∩ U m`, give the same result. -/
theorem step_two {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} {e : UC x₀} {n m : ℕ} {y y' z : X}
    (hjoin : JoinedIn (U n ∩ U m) y y') (hz : z ∈ U m) :
    step U hU (step U hU e n y) m z = step U hU (step U hU e n y') m z := by
  obtain ⟨hy, hym⟩ : y ∈ U n ∧ y ∈ U m := hjoin.mem.1
  obtain ⟨hy', hy'm⟩ : y' ∈ U n ∧ y' ∈ U m := hjoin.mem.2
  by_cases he : e.pt ∈ U n
  · rw [step_of_mem (e := e) (n := n) (y := y) ⟨he, hy⟩,
        step_of_mem (e := e) (n := n) (y := y') ⟨he, hy'⟩,
        step_of_mem (e := sectOf (U n) (hU.1 n) e he y hy) (n := m) (y := z) ⟨hym, hz⟩,
        step_of_mem (e := sectOf (U n) (hU.1 n) e he y' hy') (n := m) (y := z) ⟨hy'm, hz⟩]
    apply congrArg (fun q : Path.Homotopic.Quotient x₀ z => (⟨z, q⟩ : UC x₀))
    simp only [sectOf]
    set q : Path y y' := hjoin.somePath with hq
    have hqmem : ∀ t, q t ∈ U n ∩ U m := hjoin.somePath_mem
    have hδ : Path.Homotopic.Quotient.mk
          (discPath (U n) (hU.1 n) e.pt he y' hy')
        = (Path.Homotopic.Quotient.mk (discPath (U n) (hU.1 n) e.pt he y hy)).trans
            (Path.Homotopic.Quotient.mk q) := by
      rw [← Path.Homotopic.Quotient.mk_trans]
      refine mk_eq_mk_of_isDiscLike (hU.1 n) _ _
        (discPath_mem (U n) (hU.1 n) e.pt he y' hy') (fun t => ?_)
      have ht : ((discPath (U n) (hU.1 n) e.pt he y hy).trans q) t ∈
          Set.range ((discPath (U n) (hU.1 n) e.pt he y hy).trans q) := ⟨t, rfl⟩
      rw [Path.trans_range, Set.mem_union] at ht
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [← hs]; exact discPath_mem (U n) (hU.1 n) e.pt he y hy s
      · rw [← hs]; exact (hqmem s).1
    have hη : Path.Homotopic.Quotient.mk (discPath (U m) (hU.1 m) y hym z hz)
        = (Path.Homotopic.Quotient.mk q).trans
            (Path.Homotopic.Quotient.mk (discPath (U m) (hU.1 m) y' hy'm z hz)) := by
      rw [← Path.Homotopic.Quotient.mk_trans]
      refine mk_eq_mk_of_isDiscLike (hU.1 m) _ _
        (discPath_mem (U m) (hU.1 m) y hym z hz) (fun t => ?_)
      have ht : (q.trans (discPath (U m) (hU.1 m) y' hy'm z hz)) t ∈
          Set.range (q.trans (discPath (U m) (hU.1 m) y' hy'm z hz)) := ⟨t, rfl⟩
      rw [Path.trans_range, Set.mem_union] at ht
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [← hs]; exact (hqmem s).2
      · rw [← hs]; exact discPath_mem (U m) (hU.1 m) y' hy'm z hz s
    rw [hδ, hη]
    simp only [Path.Homotopic.Quotient.trans_assoc]
  · rw [step_of_not_mem (e := e) (n := n) (y := y) (fun h => he h.1),
        step_of_not_mem (e := e) (n := n) (y := y') (fun h => he h.1)]

end Step

section Chain

/-- The result of performing the moves listed in `L`, starting from `e`. -/
noncomputable def chainPt (U : ℕ → Set X) (hU : DiscCover U) (L : List (ℕ × X)) {x₀ : X}
    (e : UC x₀) : UC x₀ :=
  L.foldl (fun e p => step U hU e p.1 p.2) e

@[simp] theorem chainPt_nil {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} (e : UC x₀) :
    chainPt U hU [] e = e := rfl

@[simp] theorem chainPt_cons {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} (p : ℕ × X)
    (L : List (ℕ × X)) (e : UC x₀) :
    chainPt U hU (p :: L) e = chainPt U hU L (step U hU e p.1 p.2) := rfl

theorem chainPt_append {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} (L₁ L₂ : List (ℕ × X))
    (e : UC x₀) :
    chainPt U hU (L₁ ++ L₂) e = chainPt U hU L₂ (chainPt U hU L₁ e) := by
  simp only [chainPt, List.foldl_append]

/-- One of the two consecutive moves of a chain may be redirected through any point of the same
path component of `U n ∩ U m`. -/
theorem chainPt_swap {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} (L₁ L₂ : List (ℕ × X))
    (e : UC x₀) {n m : ℕ} {y y' z : X} (hjoin : JoinedIn (U n ∩ U m) y y') (hz : z ∈ U m) :
    chainPt U hU (L₁ ++ [(n, y), (m, z)] ++ L₂) e
      = chainPt U hU (L₁ ++ [(n, y'), (m, z)] ++ L₂) e := by
  simp only [chainPt, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [step_two hjoin hz]

/-- The list `L` is a legitimate list of moves starting from `e`. -/
def Valid (U : ℕ → Set X) (hU : DiscCover U) {x₀ : X} : UC x₀ → List (ℕ × X) → Prop
  | e, [] => True
  | e, (n, y) :: L => e.pt ∈ U n ∧ y ∈ U n ∧ Valid U hU (step U hU e n y) L

@[simp] theorem valid_nil {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} (e : UC x₀) :
    Valid U hU e [] := trivial

theorem valid_cons {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} {e : UC x₀} {n : ℕ} {y : X}
    {L : List (ℕ × X)} :
    Valid U hU e ((n, y) :: L) ↔
      e.pt ∈ U n ∧ y ∈ U n ∧ Valid U hU (step U hU e n y) L := Iff.rfl

theorem valid_append {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} (L₁ L₂ : List (ℕ × X))
    (e : UC x₀) :
    Valid U hU e (L₁ ++ L₂) ↔
      Valid U hU e L₁ ∧ Valid U hU (chainPt U hU L₁ e) L₂ := by
  induction L₁ generalizing e with
  | nil => simp [Valid, chainPt]
  | cons p L₁ ih =>
      obtain ⟨n, y⟩ := p
      simp only [List.cons_append, valid_cons, chainPt_cons, ih]
      tauto

/-- The point reached by a valid chain sits over the last point listed. -/
theorem chainPt_pt {U : ℕ → Set X} {hU : DiscCover U} {x₀ : X} {e : UC x₀} {L : List (ℕ × X)}
    (h : Valid U hU e L) :
    (chainPt U hU L e).pt = (L.getLast?.map Prod.snd).getD e.pt := by
  induction L generalizing e with
  | nil => simp [chainPt]
  | cons p L ih =>
      obtain ⟨n, y⟩ := p
      rw [valid_cons] at h
      obtain ⟨h1, h2, h3⟩ := h
      rw [chainPt_cons, ih h3, step_pt ⟨h1, h2⟩, List.getLast?_cons]
      cases L.getLast? with
      | none => rfl
      | some q => simp

end Chain

section Res

/-- The index `(1 - u) * s + u * t` of the point of `[s,t]` at parameter `u`. -/
noncomputable def segIdx (s t u : I) : I :=
  ⟨(1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ), by
    obtain ⟨hu0, hu1⟩ := u.2
    obtain ⟨hs0, hs1⟩ := s.2
    obtain ⟨ht0, ht1⟩ := t.2
    constructor <;> nlinarith⟩

@[simp] theorem segIdx_coe (s t u : I) :
    (segIdx s t u : ℝ) = (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ) := rfl

theorem segIdx_zero (s t : I) : segIdx s t 0 = s := by
  refine Subtype.ext ?_
  simp

theorem segIdx_one (s t : I) : segIdx s t 1 = t := by
  refine Subtype.ext ?_
  simp

theorem le_segIdx {s t u : I} (hst : s ≤ t) : s ≤ segIdx s t u := by
  have h : (s : ℝ) ≤ (t : ℝ) := hst
  obtain ⟨hu0, hu1⟩ := u.2
  obtain ⟨hs0, hs1⟩ := s.2
  obtain ⟨ht0, ht1⟩ := t.2
  show (s : ℝ) ≤ (segIdx s t u : ℝ)
  rw [segIdx_coe]
  nlinarith

theorem segIdx_le {s t u : I} (hst : s ≤ t) : segIdx s t u ≤ t := by
  have h : (s : ℝ) ≤ (t : ℝ) := hst
  obtain ⟨hu0, hu1⟩ := u.2
  obtain ⟨hs0, hs1⟩ := s.2
  obtain ⟨ht0, ht1⟩ := t.2
  show (segIdx s t u : ℝ) ≤ (t : ℝ)
  rw [segIdx_coe]
  nlinarith

theorem continuous_segIdx (s t : I) : Continuous (segIdx s t) :=
  Continuous.subtype_mk (by fun_prop) (fun u => (segIdx s t u).2)

/-- The restriction of a path `γ` to the subinterval `[s,t]`, as a path from `γ s` to `γ t`. -/
noncomputable def res {x₀ x : X} (γ : Path x₀ x) (s t : I) : Path (γ s) (γ t) where
  toFun u := γ (segIdx s t u)
  continuous_toFun := γ.continuous.comp (continuous_segIdx s t)
  source' := by
    refine congrArg γ ?_
    rw [segIdx_zero]
  target' := by
    refine congrArg γ ?_
    rw [segIdx_one]

@[simp] theorem res_apply {x₀ x : X} (γ : Path x₀ x) (s t : I) (u : I) :
    res γ s t u = γ (segIdx s t u) := rfl

theorem res_mem {U : ℕ → Set X} {x₀ x : X} (γ : Path x₀ x) {n : ℕ} {s t : I} (hst : s ≤ t)
    (hn : ∀ u ∈ Set.Icc s t, γ u ∈ U n) : ∀ u, res γ s t u ∈ U n := by
  intro u
  rw [res_apply]
  exact hn _ (Set.mem_Icc.mpr ⟨le_segIdx hst, segIdx_le hst⟩)

theorem res_apply_segTo {x₀ x : X} (γ : Path x₀ x) (t : I) (u : I) :
    res γ 0 t u = segTo γ t u := by
  rw [res_apply]
  show γ (segIdx 0 t u) = γ (u * t)
  refine congrArg γ (Subtype.ext ?_)
  rw [segIdx_coe]
  push_cast
  ring

end Res
