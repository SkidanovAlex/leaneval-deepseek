/-
# Labellings with non-zero path sum on a simple cycle

This file provides the combinatorial input needed by Howie's proof (`Case 1` of his Theorem 3.1):
on a *simple* closed reduced path `p` — one whose vertex list, with the last vertex removed, has no
repetition — there is a balanced `ℤ`-labelling `L` of the arrows with `pathSum L p ≠ 0`.

The construction is elementary: a simple reduced closed path has an arrow `e` whose *reverse* does
not occur in the path (`exists_arrow_reverse_notMem_arrowList`), and for such an `e` the labelling
which is `1` on `e`, `-1` on `e⁻¹` and `0` elsewhere has path sum `1` on `p`
(`pathSum_labellingOfArrow_ne_zero`).

The only combinatorial fact used is `arrowList_map_left` (`Howie/ArrowVertex.lean`): the sources of
the arrows of a path are the vertices of the path without its last vertex.  Since the latter list is
assumed to have no repetitions, the source map is injective on the arrow list
(`eq_of_left_eq_of_mem_arrowList`).  Consequently the reverse of the *first* arrow of `p`, if it
occurred in `p`, would have to be the *second* arrow — and two consecutive arrows of a path are
never mutually inverse in a reduced path.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.ArrowVertex
import Submission.Work.ORLocInd.Howie.span_noSelfLoop

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLocInd.Howie

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Two elementary lemmas about `ℤ`-valued sums of indicator functions on a list -/

/-- The sum of a difference of two `ℤ`-valued functions is the difference of the sums. -/
theorem sum_map_sub_fun {α : Type*} (l : List α) (f g : α → ℤ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- The sum of a constant multiple of an indicator function of a `Bool`-valued predicate. -/
theorem sum_map_ite_eq_countP {α : Type*} (l : List α) (p : α → Bool) (c : ℤ) :
    (l.map (fun x => if p x then c else 0)).sum = c * (l.countP p : ℤ) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih]
    by_cases hx : p x = true
    · rw [if_pos hx, List.countP_cons_of_pos hx]; push_cast; ring
    · rw [if_neg hx, List.countP_cons_of_neg hx]; ring

/-! ## The labelling carried by a distinguished arrow -/

/-- The balanced labelling of `Γ` which takes the value `1` on a distinguished arrow `e`, the
value `-1` on its reverse, and the value `0` on every other arrow. -/
noncomputable def labellingOfArrow (e : Quiver.Total V) : Labelling V := by
  classical
  exact
  { toFun := fun f => (if decide (f = e) then (1 : ℤ) else 0)
      - (if decide (f = Quiver.totalReverse e) then (1 : ℤ) else 0)
    balanced := by
      intro f
      have h1 : (Quiver.totalReverse f = e) ↔ (f = Quiver.totalReverse e) := by
        constructor
        · intro h; rw [← h, Quiver.totalReverse_involutive]
        · intro h; rw [h, Quiver.totalReverse_involutive]
      have h2 : (Quiver.totalReverse f = Quiver.totalReverse e) ↔ (f = e) :=
        Quiver.totalReverse_injective.eq_iff
      simp only [decide_eq_true_eq]
      rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]
      ring }

/-- If the distinguished arrow `e` occurs in the reduced path `p` but its reverse does not, then the
path sum of the labelling `labellingOfArrow e` is non-zero.  Indeed it is the number of occurrences
of `e` in `p`, which is at least one. -/
theorem pathSum_labellingOfArrow_ne_zero {a : V} (p : Quiver.Path a a) (e : Quiver.Total V)
    (he : e ∈ p.arrowList) (ht : Quiver.totalReverse e ∉ p.arrowList) :
    pathSum (labellingOfArrow e).toFun p ≠ 0 := by
  classical
  have hfun : (labellingOfArrow e).toFun = fun f =>
      (if decide (f = e) then (1 : ℤ) else 0)
        - (if decide (f = Quiver.totalReverse e) then (1 : ℤ) else 0) := by
    funext f; simp only [labellingOfArrow]
  rw [pathSum, hfun]
  have hkey : (p.arrowList.map (fun f =>
        (if decide (f = e) then (1 : ℤ) else 0)
          - (if decide (f = Quiver.totalReverse e) then (1 : ℤ) else 0))).sum
      = (p.arrowList.countP (fun f => decide (f = e)) : ℤ)
        - (p.arrowList.countP (fun f => decide (f = Quiver.totalReverse e)) : ℤ) := by
    rw [sum_map_sub_fun (p.arrowList) (fun x => if decide (x = e) then (1 : ℤ) else 0)
      (fun x => if decide (x = Quiver.totalReverse e) then (1 : ℤ) else 0)]
    rw [sum_map_ite_eq_countP, sum_map_ite_eq_countP]
    ring
  rw [hkey]
  have hz : p.arrowList.countP (fun f => decide (f = Quiver.totalReverse e)) = 0 := by
    rw [List.countP_eq_zero]
    intro f hf hft
    rw [decide_eq_true_eq] at hft
    exact ht (hft ▸ hf)
  have hpos : p.arrowList.countP (fun f => decide (f = e)) ≠ 0 := by
    intro h0
    rw [List.countP_eq_zero] at h0
    exact h0 e he (decide_eq_true_eq.mpr rfl)
  have hge : (1 : ℤ) ≤ (p.arrowList.countP (fun f => decide (f = e)) : ℤ) := by
    have h1 : 1 ≤ p.arrowList.countP (fun f => decide (f = e)) := Nat.one_le_iff_ne_zero.mpr hpos
    omega
  rw [hz]
  omega

/-! ## The distinguished arrow -/

/-- Two arrows occurring in the arrow list of a path whose vertices (with the last removed) are
pairwise distinct are equal as soon as they have the same source. -/
theorem eq_of_left_eq_of_mem_arrowList {a b : V} {p : Quiver.Path a b}
    (h : p.vertices.dropLast.Nodup) {f g : Quiver.Total V}
    (hf : f ∈ p.arrowList) (hg : g ∈ p.arrowList) (hfg : f.left = g.left) : f = g :=
  List.inj_on_of_nodup_map (by rw [arrowList_map_left]; exact h) hf hg hfg

/-- A simple (vertex-repeat free) reduced closed path contains an arrow whose reverse does not occur
in the path.

Proof: the sources of the arrows of `p` are the vertices of `p` without the last one, a list without
repetitions (`arrowList_map_left`, `hnodup`).  Hence two arrows of `p` with the same source coincide
(`eq_of_left_eq_of_mem_arrowList`).  Let `f₁ : a ⟶ c` be the first arrow of `p` and `e := a → c` the
corresponding total arrow; its reverse `e⁻¹ : c ⟶ a` has source `c`, the target of `f₁`.  If `e⁻¹`
occurred in `p` and `p` had length at least two, then — the second arrow `f₂ : c ⟶ v` also having
source `c` — the injectivity of the source would force `e⁻¹ = f₂`, so that `f₂ = f₁⁻¹`: two
consecutive mutually inverse arrows, contradicting reducedness.  If `p` has length one then `p` is a
single arrow and the hypothesis that no self-loop is its own inverse rules out that the reverse of
that arrow coincides with it. -/
theorem exists_arrow_reverse_notMem_arrowList {a : V}
    (hns : ∀ (v : V) (e : v ⟶ v), Quiver.reverse e ≠ e)
    (p : Quiver.Path a a) (hp : p.IsReduced) (hne : p.length ≠ 0)
    (hnodup : p.vertices.dropLast.Nodup) :
    ∃ e ∈ p.arrowList, Quiver.totalReverse e ∉ p.arrowList := by
  by_cases hlen1 : p.length = 1
  · -- `p` consists of a single arrow
    obtain ⟨c, f, q, hqlen, hp_eq⟩ :=
      Quiver.Path.eq_toPath_comp_of_length_eq_succ p (n := 0) (by omega)
    have hqnil : q.arrowList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Quiver.Path.arrowList_length_eq, hqlen]
    refine ⟨Quiver.Total.mk a c f, ?_, ?_⟩
    · rw [hp_eq, Quiver.Path.arrowList_comp', Quiver.Path.arrowList_toPath']
      exact List.mem_append_left _ (List.mem_singleton_self _)
    · rw [hp_eq, Quiver.Path.arrowList_comp', Quiver.Path.arrowList_toPath', hqnil]
      simp only [List.singleton_append, List.mem_singleton]
      intro h
      exact totalReverse_ne_self hns (Quiver.Total.mk a c f) h
  · have hlen2 : 2 ≤ p.length := by omega
    obtain ⟨v, p₁, p₂, hp_eq, hp₁_len⟩ := Quiver.Path.exists_eq_comp_of_le_length p hlen2
    -- `p₁` has length two: `p₁ = f₁.toPath.comp f₂.toPath`
    obtain ⟨c, f₁, r, hr_len, hp₁_eq⟩ :=
      Quiver.Path.eq_toPath_comp_of_length_eq_succ p₁ (n := 1) (by omega)
    obtain ⟨d, f₂, s, hs_len, hr_eq⟩ :=
      Quiver.Path.eq_toPath_comp_of_length_eq_succ r (n := 0) (by omega)
    have hdv : d = v := Quiver.Path.eq_of_length_zero s hs_len
    subst d
    have hs_nil : s = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero s hs_len
    refine ⟨Quiver.Total.mk a c f₁, ?_, ?_⟩
    · rw [hp_eq, hp₁_eq, hr_eq, hs_nil, Quiver.Path.comp_nil,
        Quiver.Path.arrowList_comp', Quiver.Path.arrowList_comp',
        Quiver.Path.arrowList_toPath', Quiver.Path.arrowList_toPath']
      simp
    · intro hmem
      have hmem_t : Quiver.Total.mk c a (Quiver.reverse f₁) ∈ p.arrowList := by
        simpa using hmem
      have hmem_f₂ : Quiver.Total.mk c v f₂ ∈ p.arrowList := by
        rw [hp_eq, hp₁_eq, hr_eq, hs_nil, Quiver.Path.comp_nil,
          Quiver.Path.arrowList_comp', Quiver.Path.arrowList_comp',
          Quiver.Path.arrowList_toPath', Quiver.Path.arrowList_toPath']
        simp
      -- the reverse of the first arrow is the second arrow
      have heq : Quiver.Total.mk c a (Quiver.reverse f₁) = Quiver.Total.mk c v f₂ :=
        eq_of_left_eq_of_mem_arrowList hnodup hmem_t hmem_f₂ rfl
      rw [Quiver.Total.mk.injEq] at heq
      obtain ⟨-, hav, hheq⟩ := heq
      subst v
      have hf₂ : f₂ = Quiver.reverse f₁ := (eq_of_heq hheq).symm
      have hp₁_red : p₁.IsReduced := Quiver.Path.IsReduced.of_comp (q := p₂) (hp_eq ▸ hp)
      have hdb : Quiver.Path.DeleteBacktrack p₁ (Quiver.Path.nil : Quiver.Path a a) := by
        have hbase := Quiver.Path.DeleteBacktrack.intro (Quiver.Path.nil : Quiver.Path a a) f₁
          (Quiver.Path.nil : Quiver.Path a a)
        rw [Quiver.Path.nil_comp, Quiver.Path.comp_nil] at hbase
        have hp₁_eq' : p₁ = f₁.toPath.comp (Quiver.reverse f₁).toPath := by
          rw [hp₁_eq, hr_eq, hs_nil, Quiver.Path.comp_nil, hf₂]
        rwa [← hp₁_eq'] at hbase
      exact absurd hdb (hp₁_red Quiver.Path.nil)

/-! ## The main statement -/

theorem exists_labelling_of_simpleCycle {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hns : ∀ (a : V) (e : a ⟶ a), Quiver.reverse e ≠ e)
    {a : V} (p : Quiver.Path a a) (hp : p.IsReduced) (hne : p.length ≠ 0)
    (hnodup : p.vertices.dropLast.Nodup) :
    ∃ L : Work.ORLocInd.Howie.Labelling V, Work.ORLocInd.Howie.pathSum L.toFun p ≠ 0 := by
  obtain ⟨e, he, ht⟩ := exists_arrow_reverse_notMem_arrowList hns p hp hne hnodup
  exact ⟨labellingOfArrow e, pathSum_labellingOfArrow_ne_zero p e he ht⟩

end Work.ORLocInd.Howie
