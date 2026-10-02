import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

open scoped unitInterval

/-- The point of `ℝ¹ = EuclideanSpace ℝ (Fin 1)` whose single coordinate is `c`. -/
private abbrev pt (c : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => c)

/-- `pt c` is nonzero when `c` is. -/
private lemma pt_ne_zero (c : ℝ) (hc : c ≠ 0) : pt c ≠ (0 : EuclideanSpace ℝ (Fin 1)) := by
  intro h
  have hc' : c = 0 := by
    have hh := congrArg (fun w : EuclideanSpace ℝ (Fin 1) => w (0 : Fin 1)) h
    simpa [pt] using hh
  exact hc hc'

/-- The open half space of `ℝ¹` with positive coordinate is convex. -/
private lemma convex_pos : Convex ℝ {w : EuclideanSpace ℝ (Fin 1) | (0 : ℝ) < w (0 : Fin 1)} := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_setOf_eq] at hx hy ⊢
  have key : (a • x + b • y) (0 : Fin 1) = a * x 0 + b * y 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  rw [key]
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    rw [hb1]; simpa using hy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : 0 < a * x 0 := mul_pos hapos hx
    have h2 : 0 ≤ b * y 0 := mul_nonneg hb (le_of_lt hy)
    linarith

/-- The open half space of `ℝ¹` with negative coordinate is convex. -/
private lemma convex_neg : Convex ℝ {w : EuclideanSpace ℝ (Fin 1) | w (0 : Fin 1) < (0 : ℝ)} := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_setOf_eq] at hx hy ⊢
  have key : (a • x + b • y) (0 : Fin 1) = a * x 0 + b * y 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  rw [key]
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    rw [hb1]; simpa using hy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : a * x 0 < 0 := mul_neg_of_pos_of_neg hapos hx
    have h2 : b * y 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hy)
    linarith

/-- A point of `ℝ¹` with positive coordinate is joined, inside the punctured line, to `pt 1`. -/
private lemma joinedIn_pos {v : EuclideanSpace ℝ (Fin 1)} (hv : (0 : ℝ) < v (0 : Fin 1)) :
    JoinedIn {w : EuclideanSpace ℝ (Fin 1) | w ≠ 0} v (pt 1) := by
  have hvS : v ∈ {w : EuclideanSpace ℝ (Fin 1) | (0 : ℝ) < w (0 : Fin 1)} := hv
  have haS : pt 1 ∈ {w : EuclideanSpace ℝ (Fin 1) | (0 : ℝ) < w (0 : Fin 1)} := by
    rw [Set.mem_setOf_eq]; simp
  refine (JoinedIn.of_segment_subset (convex_pos.segment_subset hvS haS)).mono ?_
  intro w hw hw0
  rw [hw0] at hw
  simpa using hw

/-- A point of `ℝ¹` with negative coordinate is joined, inside the punctured line, to `pt (-1)`. -/
private lemma joinedIn_neg {v : EuclideanSpace ℝ (Fin 1)} (hv : v (0 : Fin 1) < (0 : ℝ)) :
    JoinedIn {w : EuclideanSpace ℝ (Fin 1) | w ≠ 0} v (pt (-1)) := by
  have hvS : v ∈ {w : EuclideanSpace ℝ (Fin 1) | w (0 : Fin 1) < (0 : ℝ)} := hv
  have haS : pt (-1) ∈ {w : EuclideanSpace ℝ (Fin 1) | w (0 : Fin 1) < (0 : ℝ)} := by
    rw [Set.mem_setOf_eq]; simp
  refine (JoinedIn.of_segment_subset (convex_neg.segment_subset hvS haS)).mono ?_
  intro w hw hw0
  rw [hw0] at hw
  simpa using hw

/-- In the punctured line, any point with positive coordinate is joined to `pt 1`. -/
private lemma joined_posPt {v : EuclideanSpace ℝ (Fin 1)} (hv : v ≠ 0)
    (h : (0 : ℝ) < v (0 : Fin 1)) :
    Joined (⟨v, hv⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0})
      (⟨pt 1, pt_ne_zero 1 one_ne_zero⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0}) := by
  have hji := joinedIn_pos h
  have hj := hji.joined_subtype
  have e1 : (⟨v, hji.source_mem⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0}) = ⟨v, hv⟩ :=
    Subtype.ext rfl
  have e2 : (⟨pt 1, hji.target_mem⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0})
      = ⟨pt 1, pt_ne_zero 1 one_ne_zero⟩ := Subtype.ext rfl
  rw [e1, e2] at hj
  exact hj

/-- In the punctured line, any point with negative coordinate is joined to `pt (-1)`. -/
private lemma joined_negPt {v : EuclideanSpace ℝ (Fin 1)} (hv : v ≠ 0)
    (h : v (0 : Fin 1) < (0 : ℝ)) :
    Joined (⟨v, hv⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0})
      (⟨pt (-1), pt_ne_zero (-1) (by norm_num)⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0}) := by
  have hji := joinedIn_neg h
  have hj := hji.joined_subtype
  have e1 : (⟨v, hji.source_mem⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0}) = ⟨v, hv⟩ :=
    Subtype.ext rfl
  have e2 : (⟨pt (-1), hji.target_mem⟩ : {w : EuclideanSpace ℝ (Fin 1) // w ≠ 0})
      = ⟨pt (-1), pt_ne_zero (-1) (by norm_num)⟩ := Subtype.ext rfl
  rw [e1, e2] at hj
  exact hj

/-- The punctured real line `ℝ¹ ∖ {0}` (realized as `EuclideanSpace ℝ (Fin 1)` with the origin
removed) has exactly two path components: there are two points `a b` such that every point is
joinable to `a` or to `b`, while `a` and `b` are not joinable to each other. -/
theorem twoComponents_puncturedOne :
    ∃ a b : {v : EuclideanSpace ℝ (Fin 1) // v ≠ 0},
      (∀ z, Joined z a ∨ Joined z b) ∧ ¬ Joined a b := by
  refine ⟨⟨pt 1, pt_ne_zero 1 one_ne_zero⟩, ⟨pt (-1), pt_ne_zero (-1) (by norm_num)⟩, ?_, ?_⟩
  · intro z
    obtain ⟨v, hv⟩ := z
    have hv0 : v (0 : Fin 1) ≠ 0 := by
      intro h
      exact hv (PiLp.ext fun i => by fin_cases i; simpa using h)
    rcases lt_trichotomy (v (0 : Fin 1)) 0 with h | h | h
    · exact Or.inr (joined_negPt hv h)
    · exact absurd h hv0
    · exact Or.inl (joined_posPt hv h)
  · rintro ⟨γ⟩
    have hcont : Continuous (fun t : unitInterval =>
        (γ t : EuclideanSpace ℝ (Fin 1)) (0 : Fin 1)) := by fun_prop
    have h0 : (γ 0 : EuclideanSpace ℝ (Fin 1)) (0 : Fin 1) = 1 := by simp [pt]
    have h1 : (γ 1 : EuclideanSpace ℝ (Fin 1)) (0 : Fin 1) = -1 := by simp [pt]
    obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge (c := (0 : ℝ)) hcont
      ⟨1, by rw [h1]; norm_num⟩ ⟨0, by rw [h0]; norm_num⟩
    exact (γ t).2 (PiLp.ext fun i => by fin_cases i; simpa using ht)

end Work.Thom
