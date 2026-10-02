import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

open Work.EL

/-!
# `Work.ELTop.notInArc_midNear`

The reference angle `midNear ps` of an admissible ray polygon `ps` (the midpoint of the
"near arc" following the first pair) lies in no arc `(P.a, P.b)`, `P ∈ ps`.

The argument is purely about the cyclic order of the `2m` angles of `ps`: the flattened list
`ps.flatMap (fun P => [P.a, P.b])` is strictly increasing and all of its entries lie in
`[a₀, a₀ + 1)`, where `a₀` is the first angle.  Hence `midNear ps` — which lies strictly
between the first two "gaps", i.e. in `(b₀, a₀ + 1)` — is cyclically outside every arc of the
polygon.
-/

/-! ## Real-arithmetic helpers -/

/-- `Int.fract y ≤ y` for `y ≥ 0`. -/
theorem midNear_fract_le_self {y : ℝ} (hy : 0 ≤ y) : Int.fract y ≤ y := by
  rcases lt_or_ge y 1 with h | h
  · exact le_of_eq (Int.fract_eq_self.mpr ⟨hy, h⟩)
  · linarith [Int.fract_lt_one y]

/-- `InArc x a b` (with `a ≤ b`) forces some integer translate of `x` into the interval
`(a, b)`. -/
theorem midNear_InArc_exists_int {x a b : ℝ} (hab : a ≤ b) (h : InArc x a b) :
    ∃ z : ℤ, a < x - z ∧ x - z < b := by
  have key : x - (⌊x - a⌋ : ℝ) = a + Int.fract (x - a) := by
    have := Int.floor_add_fract (x - a); linarith
  have h2' : Int.fract (x - a) < Int.fract (b - a) := h.2
  have hle : Int.fract (b - a) ≤ b - a := midNear_fract_le_self (by linarith)
  exact ⟨⌊x - a⌋, by rw [key]; linarith [h.1], by rw [key]; linarith [h2', hle]⟩

/-- If `x` lies just below an arc `(a, b)` of length `< 1`, it is not in that arc. -/
theorem midNear_notInArc_of_lt {x a b : ℝ} (hab : a ≤ b) (hxa : x < a) (hxb : b < x + 1) :
    ¬ InArc x a b := by
  intro h
  obtain ⟨z, h1, h2⟩ := midNear_InArc_exists_int hab h
  have hzle : z ≤ -1 := by
    have : (z : ℝ) < 0 := by linarith
    have : z < 0 := by exact_mod_cast this
    omega
  have hzle' : (z : ℝ) ≤ -1 := by exact_mod_cast hzle
  linarith

/-- If `x` lies just above an arc `(a, b)` of length `< 1`, it is not in that arc. -/
theorem midNear_notInArc_of_gt {x a b : ℝ} (hab : a ≤ b) (hxb : b < x) (hxa : x < a + 1) :
    ¬ InArc x a b := by
  intro h
  obtain ⟨z, h1, h2⟩ := midNear_InArc_exists_int hab h
  have hz1 : (1 : ℤ) ≤ z := by
    have : (0 : ℝ) < (z : ℝ) := by linarith
    have : (0 : ℤ) < z := by exact_mod_cast this
    omega
  have hz1' : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  linarith

/-! ## List helpers -/

/-- In the strictly increasing flattened angle list of a polygon, the first angle of each pair
is strictly below its second angle. -/
theorem midNear_a_lt_b_of_pairwise {α : Type*} (ps : List α) (a b : α → ℝ)
    (h : (ps.flatMap (fun P => [a P, b P])).Pairwise (· < ·)) :
    ∀ P ∈ ps, a P < b P := by
  induction ps with
  | nil => intro P hP; exact absurd hP (by simp)
  | cons P tl ih =>
    intro R hR
    have hcons : (a P :: b P :: tl.flatMap (fun S => [a S, b S])).Pairwise (· < ·) := by
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append] using h
    rcases List.mem_cons.mp hR with rfl | hRtl
    · exact List.rel_of_pairwise_cons hcons (by simp)
    · have h2 : (b P :: tl.flatMap (fun S => [a S, b S])).Pairwise (· < ·) := by
        rw [List.pairwise_cons] at hcons; exact hcons.2
      rw [List.pairwise_cons] at h2
      exact ih h2.2 R hRtl

/-- The head `a Q` of the flattened angle list of `Q :: tl` is the least first-angle of the
pairs of `Q :: tl`. -/
theorem midNear_head_le_of_pairwise_flatMap {α : Type*} (Q : α) (tl : List α) (a b : α → ℝ)
    (h : ((Q :: tl).flatMap (fun P => [a P, b P])).Pairwise (· < ·)) :
    ∀ P ∈ Q :: tl, a Q ≤ a P := by
  intro P hP
  have hcons : (a Q :: b Q :: tl.flatMap (fun S => [a S, b S])).Pairwise (· < ·) := by
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append] using h
  rw [List.pairwise_cons] at hcons
  rcases List.mem_cons.mp hP with rfl | hPtl
  · exact le_refl _
  · exact le_of_lt (hcons.1 (a P)
      (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨P, hPtl, by simp⟩)))

/-! ## The main statement -/

theorem notInArc_midNear {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) :
    ∀ P ∈ ps, ¬ Work.EL.InArc (Work.EL.midNear ps) P.a P.b := by
  intro P hP
  rcases ps with _ | ⟨P₀, ps'⟩
  · exact absurd rfl hA.ne
  rcases ps' with _ | ⟨Q, tl⟩
  · -- `ps = [P₀]`
    have hPP₀ : P = P₀ := by simpa using hP
    rw [hPP₀]
    have hcyc := hA.cyc
    have hpair : ([P₀.a, P₀.b] : List ℝ).Pairwise (· < ·) := hcyc.2.1
    have hhead : ([P₀.a, P₀.b] : List ℝ).headD 0 = P₀.a := rfl
    have hupper : ∀ x ∈ ([P₀.a, P₀.b] : List ℝ),
        x < ([P₀.a, P₀.b] : List ℝ).headD 0 + 1 := hcyc.2.2
    have hab : P₀.a < P₀.b := List.rel_of_pairwise_cons hpair (by simp)
    have hb_lt : P₀.b < P₀.a + 1 := by
      have := hupper P₀.b (by simp); rwa [hhead] at this
    have hf_eq : Int.fract (P₀.a + 1 - P₀.b) = P₀.a + 1 - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hx_gt : P₀.b < P₀.b + Int.fract (P₀.a + 1 - P₀.b) / 2 := by
      rw [hf_eq]; linarith
    have hx_lt : P₀.b + Int.fract (P₀.a + 1 - P₀.b) / 2 < P₀.a + 1 := by
      rw [hf_eq]; linarith
    exact midNear_notInArc_of_gt (le_of_lt hab) hx_gt hx_lt
  · -- `ps = P₀ :: Q :: tl`
    let tail : List ℝ := tl.flatMap (fun R => [R.a, R.b])
    have hm : (P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b])
        = P₀.a :: P₀.b :: Q.a :: Q.b :: tail := rfl
    have hpair : ((P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b])).Pairwise (· < ·) :=
      hA.cyc.2.1
    rw [hm] at hpair
    have hp1 : (∀ y ∈ P₀.b :: Q.a :: Q.b :: tail, P₀.a < y) ∧
        (P₀.b :: Q.a :: Q.b :: tail).Pairwise (· < ·) := List.pairwise_cons.mp hpair
    have hp2 : (∀ y ∈ Q.a :: Q.b :: tail, P₀.b < y) ∧
        (Q.a :: Q.b :: tail).Pairwise (· < ·) := List.pairwise_cons.mp hp1.2
    have hupper : ∀ x ∈ (P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b]), x < P₀.a + 1 := by
      intro x hx
      have hh := hA.cyc.2.2 x hx
      rwa [hm, List.headD_cons] at hh
    have hAB : ∀ R ∈ P₀ :: Q :: tl, R.a < R.b :=
      midNear_a_lt_b_of_pairwise (P₀ :: Q :: tl) (fun R => R.a) (fun R => R.b) hA.cyc.2.1
    have hpairQ : ((Q :: tl).flatMap (fun R => [R.a, R.b])).Pairwise (· < ·) := hp2.2
    have hmin : ∀ R ∈ Q :: tl, Q.a ≤ R.a :=
      midNear_head_le_of_pairwise_flatMap Q tl (fun R => R.a) (fun R => R.b) hpairQ
    have hab0 : P₀.a < P₀.b := hp1.1 P₀.b (by simp)
    have hba : P₀.b < Q.a := hp2.1 Q.a (by simp)
    have hQam : Q.a ∈ (P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b]) :=
      List.mem_flatMap.mpr ⟨Q, by simp, by simp⟩
    have hQa_lt : Q.a < P₀.a + 1 := hupper Q.a hQam
    have hf_eq : Int.fract (Q.a - P₀.b) = Q.a - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hx_gt0 : P₀.b < P₀.b + Int.fract (Q.a - P₀.b) / 2 := by
      rw [hf_eq]; linarith
    have hx_lt_Qa : P₀.b + Int.fract (Q.a - P₀.b) / 2 < Q.a := by
      rw [hf_eq]; linarith
    have hx_lt_a0 : P₀.b + Int.fract (Q.a - P₀.b) / 2 < P₀.a + 1 := by linarith
    rcases List.mem_cons.mp hP with rfl | hPtl
    · exact midNear_notInArc_of_gt (le_of_lt hab0) hx_gt0 hx_lt_a0
    · have hPmem : P ∈ P₀ :: Q :: tl := List.mem_cons_of_mem P₀ hPtl
      have hx_lt_Pa : P₀.b + Int.fract (Q.a - P₀.b) / 2 < P.a := by
        have := hmin P hPtl
        linarith
      have hPb_lt : P.b < P₀.b + Int.fract (Q.a - P₀.b) / 2 + 1 := by
        have hPbm : P.b ∈ (P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b]) :=
          List.mem_flatMap.mpr ⟨P, hPmem, by simp⟩
        have := hupper P.b hPbm
        linarith
      have habP : P.a ≤ P.b := le_of_lt (hAB P hPmem)
      exact midNear_notInArc_of_lt habP hx_lt_Pa hPb_lt

end Work.ELTop
