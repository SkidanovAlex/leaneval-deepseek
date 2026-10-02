import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.notInArc_midNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

open Work.EL

/-!
# `Work.ELTop.notInArc_window_midNear`

For an admissible ray polygon `ps`, a whole *window* — an interval of positive radius about
the reference angle `midNear ps` — consists of angles `θ` which

* lie in none of the arcs `(P.a, P.b)`, `P ∈ ps`, and
* are congruent to none of the angles `P.a`, `P.b` modulo `ℤ`.

The reference angle `midNear ps` is the midpoint of the first "gap" of the near arcs: with
`ps = P₀ :: rest` and `fl = ps.flatMap (fun P => [P.a, P.b])` the strictly increasing list of
the `2m` angles (all lying in `[P₀.a, P₀.a + 1)`),

* `ps = [P₀]`: `midNear ps = (P₀.a + P₀.b + 1)/2` is the midpoint of the gap
  `(P₀.b, P₀.a + 1)`;
* `ps = P₀ :: Q :: tl`: `midNear ps = (P₀.b + Q.a)/2` is the midpoint of the gap
  `(P₀.b, Q.a)`.

The window of half-width the half-length of that gap is therefore contained in the gap, and
the two conclusions follow from the elementary facts that (a) an angle in a gap between
consecutive angles of the polygon lies outside every arc (`neitherInArc`), and (b) all the
angles lie in the fundamental interval `[P₀.a, P₀.a + 1)`, so an angle of the gap can only be
congruent to a polygon angle if it *equals* it.
-/

/-! ## An integer-shift helper -/

/-- A real number distinct from `x` but within distance `< 1` of `x` is not congruent to `x`
modulo `ℤ`. -/
theorem ne_add_int_of_abs_lt_one {x θ : ℝ} (hxθ : θ ≠ x) (h : |θ - x| < 1) (k : ℤ) :
    θ ≠ x + (k : ℝ) := by
  intro hc
  have hk : (k : ℝ) = θ - x := by linarith [hc]
  have habs : |(k : ℝ)| < 1 := by rw [hk]; exact h
  have hlt := abs_lt.mp habs
  have h1 : (-1 : ℤ) < k := by exact_mod_cast hlt.1
  have h2 : k < (1 : ℤ) := by exact_mod_cast hlt.2
  have hk0 : k = 0 := by omega
  rw [hk0] at hc
  simp only [Int.cast_zero, add_zero] at hc
  exact hxθ hc

/-! ## The main statement -/

theorem notInArc_window_midNear {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) :
    ∃ δ > 0, ∀ θ : ℝ, |θ - Work.EL.midNear ps| < δ →
      (∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) ∧
      (∀ P ∈ ps, ∀ k : ℤ, θ ≠ P.a + k ∧ θ ≠ P.b + k) := by
  cases ps with
  | nil => exact absurd rfl hA.ne
  | cons P₀ rest =>
    cases rest with
    | nil =>
      -- `ps = [P₀]`: the gap is `(P₀.b, P₀.a + 1)`.
      have hpair : ([P₀.a, P₀.b] : List ℝ).Pairwise (· < ·) := hA.cyc.2.1
      have hhead : ([P₀.a, P₀.b] : List ℝ).headD 0 = P₀.a := rfl
      have hab0 : P₀.a < P₀.b := List.rel_of_pairwise_cons hpair (by simp)
      have hupper : ∀ x ∈ ([P₀.a, P₀.b] : List ℝ),
          x < ([P₀.a, P₀.b] : List ℝ).headD 0 + 1 := hA.cyc.2.2
      have hb_lt : P₀.b < P₀.a + 1 := by
        have := hupper P₀.b (by simp)
        rwa [hhead] at this
      have hf_eq : Int.fract (P₀.a + 1 - P₀.b) = P₀.a + 1 - P₀.b :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hmval : Work.EL.midNear [P₀] = (P₀.a + P₀.b + 1) / 2 := by
        rw [Work.EL.midNear.eq_2, hf_eq]; ring
      refine ⟨(P₀.a + 1 - P₀.b) / 2, by linarith, ?_⟩
      intro θ hθ
      have hθ_gt : P₀.b < θ := by
        have := (abs_lt.mp hθ).1; rw [hmval] at this; linarith
      have hθ_lt : θ < P₀.a + 1 := by
        have := (abs_lt.mp hθ).2; rw [hmval] at this; linarith
      constructor
      · intro P hP
        have hPP₀ : P = P₀ := by simpa using hP
        rw [hPP₀]
        exact midNear_notInArc_of_gt (le_of_lt hab0) hθ_gt hθ_lt
      · intro P hP k
        have hPP₀ : P = P₀ := by simpa using hP
        rw [hPP₀]
        refine ⟨ne_add_int_of_abs_lt_one (by linarith) ?_ k,
                ne_add_int_of_abs_lt_one (by linarith) ?_ k⟩
        · rw [abs_lt]; exact ⟨by linarith, by linarith⟩
        · rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    | cons Q tl =>
      -- `ps = P₀ :: Q :: tl`: the gap is `(P₀.b, Q.a)`.
      have hpair : (P₀.a :: P₀.b :: (Q :: tl).flatMap (fun P => [P.a, P.b])).Pairwise
          (· < ·) := hA.cyc.2.1
      have hpair1 := List.pairwise_cons.mp hpair
      have hpair2 := List.pairwise_cons.mp hpair1.2
      have hpairQ : ((Q :: tl).flatMap (fun P => [P.a, P.b])).Pairwise (· < ·) := hpair2.2
      have hab0 : P₀.a < P₀.b := hpair1.1 P₀.b (by simp)
      have hP0b_lt_Qa : P₀.b < Q.a := hpair2.1 Q.a (List.mem_flatMap.mpr ⟨Q, by simp, by simp⟩)
      have hupper : ∀ x ∈ (P₀ :: Q :: tl).flatMap (fun P => [P.a, P.b]), x < P₀.a + 1 := by
        intro x hx
        have hh := hA.cyc.2.2 x hx
        have hhd : ((P₀ :: Q :: tl).flatMap (fun P => [P.a, P.b])).headD 0 = P₀.a := by
          simp [List.flatMap_cons]
        rwa [hhd] at hh
      have hQa_bd : Q.a < P₀.a + 1 :=
        hupper Q.a (List.mem_flatMap.mpr ⟨Q, by simp, by simp⟩)
      have hf_eq : Int.fract (Q.a - P₀.b) = Q.a - P₀.b :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hmval : Work.EL.midNear (P₀ :: Q :: tl) = (P₀.b + Q.a) / 2 := by
        rw [Work.EL.midNear.eq_1, hf_eq]; ring
      refine ⟨(Q.a - P₀.b) / 2, by linarith, ?_⟩
      intro θ hθ
      have hθ_gt : P₀.b < θ := by
        have := (abs_lt.mp hθ).1; rw [hmval] at this; linarith
      have hθ_lt : θ < Q.a := by
        have := (abs_lt.mp hθ).2; rw [hmval] at this; linarith
      have hθ_gt_a0 : P₀.a < θ := by linarith
      have hθ_lt_a0 : θ < P₀.a + 1 := by linarith
      constructor
      · intro P hP
        rcases List.mem_cons.mp hP with rfl | hPtl
        · -- `P = P₀`: `θ` lies just above the arc `(P₀.a, P₀.b)`.
          exact midNear_notInArc_of_gt (le_of_lt hab0) hθ_gt hθ_lt_a0
        · -- `P ∈ Q :: tl`: `θ` lies just below the arc `(P.a, P.b)`.
          have hQle : Q.a ≤ P.a :=
            midNear_head_le_of_pairwise_flatMap Q tl (fun P => P.a) (fun P => P.b)
              hpairQ P hPtl
          have hPab : P.a < P.b :=
            midNear_a_lt_b_of_pairwise (Q :: tl) (fun P => P.a) (fun P => P.b) hpairQ P hPtl
          have hPb_bd : P.b < P₀.a + 1 :=
            hupper P.b (List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem P₀ hPtl, by simp⟩)
          exact midNear_notInArc_of_lt (le_of_lt hPab) (by linarith) (by linarith)
      · intro P hP k
        rcases List.mem_cons.mp hP with rfl | hPtl
        · -- `P = P₀`
          refine ⟨ne_add_int_of_abs_lt_one (by linarith) ?_ k,
                  ne_add_int_of_abs_lt_one (by linarith) ?_ k⟩
          · rw [abs_lt]; exact ⟨by linarith, by linarith⟩
          · rw [abs_lt]; exact ⟨by linarith, by linarith⟩
        · -- `P ∈ Q :: tl`: both `P.a` and `P.b` lie in `[P₀.a, P₀.a + 1)`.
          have hQle : Q.a ≤ P.a :=
            midNear_head_le_of_pairwise_flatMap Q tl (fun P => P.a) (fun P => P.b)
              hpairQ P hPtl
          have hPab : P.a < P.b :=
            midNear_a_lt_b_of_pairwise (Q :: tl) (fun P => P.a) (fun P => P.b) hpairQ P hPtl
          have hPa_bd : P.a < P₀.a + 1 :=
            hupper P.a (List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem P₀ hPtl, by simp⟩)
          have hPb_bd : P.b < P₀.a + 1 :=
            hupper P.b (List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem P₀ hPtl, by simp⟩)
          refine ⟨ne_add_int_of_abs_lt_one (by linarith) ?_ k,
                  ne_add_int_of_abs_lt_one (by linarith) ?_ k⟩
          · rw [abs_lt]; exact ⟨by linarith, by linarith⟩
          · rw [abs_lt]; exact ⟨by linarith, by linarith⟩

end Work.ELTop
