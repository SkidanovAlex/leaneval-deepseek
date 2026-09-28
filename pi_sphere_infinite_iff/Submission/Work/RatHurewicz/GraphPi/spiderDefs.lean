import Mathlib
import Submission.Work.RatHurewicz.finiteGraphDefs

/-!
# The spine of the spider: the two germs and the shrink map

For a finite graph `GraphX a b = (V ⊕ (E × I)) / ~` (see `finiteGraphDefs`), the *spider*
(`Work.RatHurewicz.spider a b v`) of a vertex `v` is the vertex together with a short open germ of
every incident edge end.  This file sets up the material needed to prove that the spider is
contractible by shrinking every point towards the vertex.

The crucial trick is that the shrink can be written with a **single continuous formula**: let
`θ : I → ℝ` be `0` on `[0, 1/3]` and `1` on `[2/3, 1]` (affine in between).  Then

* on the `a`-germ (`s < 1/3`, `θ s = 0`) the parameter moves by `s ↦ s + t (θ s - s) = (1 - t) s`,
* on the `b`-germ (`2/3 < s`, `θ s = 1`) it moves by `s ↦ s + t (θ s - s) = 1 - (1 - t)(1 - s)`,

so the *same* real function `sShrinkVal t s = s + t (θ s - s)` interpolates between the two
branches.  Because `θ` is continuous, the resulting map

`shrinkRaw : (V ⊕ (E × I)) × I → V ⊕ (E × I)`, `Sum.inl w ↦ Sum.inl w`,
`Sum.inr (e, s) ↦ Sum.inr (e, sShrink t s)`

is continuous *everywhere* (the domain is the coproduct over `V ⊕ E` of `I`-families), and no
piecewise/gluing argument is needed for continuity.
-/

namespace Work.RatHurewicz.GraphPi

open scoped unitInterval Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V]

noncomputable section

/-! ## The two germs of the spider -/

/-- The `a`-germ of the spider at `v`: the vertex together with the initial segment `s < 1/3` of
every edge end whose `a`-endpoint is `v`. -/
def spiderA (a : E → V) (v : V) : Set (V ⊕ (E × I)) :=
  {Sum.inl v} ∪ {p | ∃ (e : E) (s : I), a e = v ∧ (s : ℝ) < 1/3 ∧ p = Sum.inr (e, s)}

/-- The `b`-germ of the spider at `v`: the vertex together with the final segment `2/3 < s` of
every edge end whose `b`-endpoint is `v`. -/
def spiderB (b : E → V) (v : V) : Set (V ⊕ (E × I)) :=
  {Sum.inl v} ∪ {p | ∃ (e : E) (s : I), b e = v ∧ 2/3 < (s : ℝ) ∧ p = Sum.inr (e, s)}

theorem mem_spiderA {a : E → V} {v : V} {p : V ⊕ (E × I)} :
    p ∈ spiderA a v ↔
      p = Sum.inl v ∨ ∃ (e : E) (s : I), a e = v ∧ (s : ℝ) < 1/3 ∧ p = Sum.inr (e, s) := by
  simp [spiderA]

theorem mem_spiderB {b : E → V} {v : V} {p : V ⊕ (E × I)} :
    p ∈ spiderB b v ↔
      p = Sum.inl v ∨ ∃ (e : E) (s : I), b e = v ∧ 2/3 < (s : ℝ) ∧ p = Sum.inr (e, s) := by
  simp [spiderB]

theorem sum_inl_mem_spiderA (a : E → V) (v : V) : (Sum.inl v : V ⊕ (E × I)) ∈ spiderA a v :=
  Or.inl rfl

theorem sum_inl_mem_spiderB (b : E → V) (v : V) : (Sum.inl v : V ⊕ (E × I)) ∈ spiderB b v :=
  Or.inl rfl

theorem sum_inr_mem_spiderA {a : E → V} {v : V} {e : E} {s : I} (h : a e = v)
    (hs : (s : ℝ) < 1/3) : (Sum.inr (e, s) : V ⊕ (E × I)) ∈ spiderA a v :=
  Or.inr ⟨e, s, h, hs, rfl⟩

theorem sum_inr_mem_spiderB {b : E → V} {v : V} {e : E} {s : I} (h : b e = v)
    (hs : 2/3 < (s : ℝ)) : (Sum.inr (e, s) : V ⊕ (E × I)) ∈ spiderB b v :=
  Or.inr ⟨e, s, h, hs, rfl⟩

/-! ## The interpolation profile and the shrinking of the parameter -/

/-- The profile function: `0` on `[0, 1/3]`, `1` on `[2/3, 1]`, affine in between. -/
def thetaVal (s : I) : ℝ := max 0 (min 1 (3 * (s : ℝ) - 1))

theorem continuous_thetaVal : Continuous thetaVal := by
  unfold thetaVal
  exact continuous_const.max (continuous_const.min (by fun_prop))

theorem thetaVal_nonneg (s : I) : 0 ≤ thetaVal s := le_max_left _ _

theorem thetaVal_le_one (s : I) : thetaVal s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem thetaVal_eq_zero {s : I} (h : (s : ℝ) ≤ 1/3) : thetaVal s = 0 := by
  have h1 : 3 * (s : ℝ) - 1 ≤ 0 := by linarith
  rw [thetaVal, min_eq_right (by linarith : 3 * (s : ℝ) - 1 ≤ 1), max_eq_left h1]

theorem thetaVal_eq_one {s : I} (h : 2/3 ≤ (s : ℝ)) : thetaVal s = 1 := by
  have h1 : 1 ≤ 3 * (s : ℝ) - 1 := by linarith
  rw [thetaVal, min_eq_left h1, max_eq_right zero_le_one]

/-- The shrunk edge parameter, as a real number: `s + t (θ s - s)`. -/
def sShrinkVal (t s : I) : ℝ := (s : ℝ) + (t : ℝ) * (thetaVal s - (s : ℝ))

theorem sShrinkVal_nonneg (t s : I) : 0 ≤ sShrinkVal t s := by
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have hθ : (0 : ℝ) ≤ thetaVal s := thetaVal_nonneg s
  have h : sShrinkVal t s = (s : ℝ) * (1 - (t : ℝ)) + (t : ℝ) * thetaVal s := by
    unfold sShrinkVal; ring
  rw [h]
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr ht1), mul_nonneg ht0 hθ]

theorem sShrinkVal_le_one (t s : I) : sShrinkVal t s ≤ 1 := by
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have hθ : thetaVal s ≤ 1 := thetaVal_le_one s
  have h : sShrinkVal t s = (s : ℝ) * (1 - (t : ℝ)) + (t : ℝ) * thetaVal s := by
    unfold sShrinkVal; ring
  rw [h]
  nlinarith [mul_le_mul_of_nonneg_right hs1 (sub_nonneg.mpr ht1),
    mul_le_mul_of_nonneg_left hθ ht0]

theorem sShrinkVal_mem (t s : I) : sShrinkVal t s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sShrinkVal_nonneg t s, sShrinkVal_le_one t s⟩

/-- The shrunk edge parameter, as an element of the unit interval. -/
def sShrink (t s : I) : I := ⟨sShrinkVal t s, sShrinkVal_mem t s⟩

theorem sShrink_zero_val (s : I) : sShrink 0 s = s := by
  apply Subtype.ext
  simp [sShrink, sShrinkVal]

theorem sShrink_left_zero (t : I) : sShrink t 0 = 0 := by
  apply Subtype.ext
  have h : thetaVal (0 : I) = 0 := thetaVal_eq_zero (by norm_num)
  simp [sShrink, sShrinkVal, h]

theorem sShrink_right_one (t : I) : sShrink t 1 = 1 := by
  apply Subtype.ext
  have h : thetaVal (1 : I) = 1 := thetaVal_eq_one (by norm_num)
  simp [sShrink, sShrinkVal, h]

theorem sShrink_coe (t s : I) : ((sShrink t s : I) : ℝ) = sShrinkVal t s := rfl

theorem sShrink_le_of_le_third {t s : I} (h : (s : ℝ) ≤ 1/3) : (sShrink t s : ℝ) ≤ (s : ℝ) := by
  have hθ : thetaVal s = 0 := thetaVal_eq_zero h
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have h' : (sShrink t s : ℝ) = (s : ℝ) * (1 - (t : ℝ)) := by
    rw [sShrink_coe]; unfold sShrinkVal; rw [hθ]; ring
  rw [h']
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr t.2.2), mul_nonneg hs0 t.2.1]

theorem le_sShrink_of_two_thirds_le {t s : I} (h : 2/3 ≤ (s : ℝ)) : (s : ℝ) ≤ (sShrink t s : ℝ) := by
  have hθ : thetaVal s = 1 := thetaVal_eq_one h
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have h' : (sShrink t s : ℝ) = (s : ℝ) + (t : ℝ) * (1 - (s : ℝ)) := by
    rw [sShrink_coe]; unfold sShrinkVal; rw [hθ]
  rw [h']
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hs1)]

/-! ## The raw shrink map -/

/-- The "shrink toward the vertex" map on representatives: the vertex summand is fixed, and the
edge parameter is pushed by `sShrink`. -/
def shrinkRaw : (V ⊕ (E × I)) × I → V ⊕ (E × I) :=
  fun p => match p.1 with
    | Sum.inl w => Sum.inl w
    | Sum.inr (e, s) => Sum.inr (e, sShrink p.2 s)

/-- `sShrink` as a continuous map of two variables. -/
def sShrinkC : C(I × I, I) :=
  ⟨fun p => sShrink p.1 p.2,
    Continuous.subtype_mk (f := fun p : I × I => sShrinkVal p.1 p.2)
      (by
        unfold sShrinkVal
        refine Continuous.add ?_ ?_
        · exact continuous_subtype_val.comp continuous_snd
        · refine Continuous.mul ?_ ?_
          · exact continuous_subtype_val.comp continuous_fst
          · refine Continuous.sub ?_ ?_
            · exact continuous_thetaVal.comp continuous_snd
            · exact continuous_subtype_val.comp continuous_snd)
      (fun p => sShrinkVal_mem p.1 p.2)⟩

@[simp] theorem sShrinkC_apply (t s : I) : sShrinkC (t, s) = sShrink t s := rfl

theorem continuous_shrinkRaw : Continuous (shrinkRaw (E := E) (V := V)) := by
  have hsum : Continuous fun y : V × I ⊕ (E × I) × I =>
      Sum.elim (fun w : V × I => (Sum.inl w.1 : V ⊕ (E × I)))
        (fun q : (E × I) × I => (Sum.inr (q.1.1, sShrink q.2 q.1.2) : V ⊕ (E × I))) y := by
    refine Continuous.sumElim ?_ ?_
    · exact continuous_inl.comp continuous_fst
    · exact continuous_inr.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (sShrinkC.continuous.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))))
  have h : shrinkRaw (E := E) (V := V) =
      (fun y : V × I ⊕ (E × I) × I =>
        Sum.elim (fun w : V × I => (Sum.inl w.1 : V ⊕ (E × I)))
          (fun q : (E × I) × I => (Sum.inr (q.1.1, sShrink q.2 q.1.2) : V ⊕ (E × I))) y)
        ∘ (Homeomorph.sumProdDistrib (X := V) (Y := E × I) (Z := I)) := by
    funext p
    obtain ⟨q, t⟩ := p
    rcases q with w | ⟨e, s⟩ <;> rfl
  rw [h]
  exact hsum.comp (Homeomorph.sumProdDistrib (X := V) (Y := E × I) (Z := I)).continuous

theorem shrinkRaw_inl (t : I) (w : V) : shrinkRaw ((Sum.inl w : V ⊕ (E × I)), t) = Sum.inl w := rfl

theorem shrinkRaw_inr (t s : I) (e : E) :
    shrinkRaw ((Sum.inr (e, s) : V ⊕ (E × I)), t) = Sum.inr (e, sShrink t s) := rfl

theorem shrinkRaw_zero (p : V ⊕ (E × I)) : shrinkRaw (p, 0) = p := by
  rcases p with w | ⟨e, s⟩
  · rfl
  · show Sum.inr (e, sShrink 0 s) = Sum.inr (e, s)
    rw [sShrink_zero_val]

theorem shrinkRaw_one_inl (w : V) : shrinkRaw ((Sum.inl w : V ⊕ (E × I)), 1) = Sum.inl w := rfl

theorem shrinkRaw_one_inr (s : I) (e : E) :
    shrinkRaw ((Sum.inr (e, s) : V ⊕ (E × I)), 1) = Sum.inr (e, sShrink 1 s) := rfl

end

end Work.RatHurewicz.GraphPi
