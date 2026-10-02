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
# `Work.ELTop.exists_midNear_add_int_mem_Ioo`

The reference angle `midNear ps` of an admissible ray polygon `ps` lies, modulo `ℤ`, strictly
inside the **near arc** `(P.b, P.a + 1)` of *every* pair `P ∈ ps`.

The angles of `ps` are the strictly increasing list `a₀ < b₀ < a₁ < b₁ < ⋯ < a_{m-1} < b_{m-1}`
of the flattened angle list, all lying in `[a₀, a₀ + 1)`, where `a₀ = P₀.a` is the first angle.
`midNear ps` is the midpoint of the first gap of the near arcs, i.e. `(b₀ + a₁)/2` when
`ps = P₀ :: Q :: _` and `(b₀ + a₀ + 1)/2` when `ps = [P₀]`.

The argument is then elementary:
* for `P = P₀` the angle `midNear ps` itself lies in `(b₀, a₀ + 1) = (P₀.b, P₀.a + 1)`;
* for every other `P`, the translate `midNear ps + 1` lies in `(P.b, P.a + 1)`, because
  `midNear ps > a₀` gives `P.b < a₀ + 1 < midNear ps + 1`, while `midNear ps < a₁ ≤ P.a`
  gives `midNear ps + 1 < P.a + 1`.
-/

theorem exists_midNear_add_int_mem_Ioo {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    (P : Work.EL.CoPair hN) (hP : P ∈ ps) :
    ∃ k : ℤ, Work.EL.midNear ps + (k : ℝ) ∈ Set.Ioo P.b (P.a + 1) := by
  rcases ps with _ | ⟨P₀, ps'⟩
  · exact absurd rfl hA.ne
  rcases ps' with _ | ⟨Q, tl⟩
  · -- `ps = [P₀]`: the reference angle is the midpoint of the near arc of `P₀` itself.
    have hPP₀ : P = P₀ := by simpa using hP
    rw [hPP₀]
    have hcyc := hA.cyc
    have hpair : ([P₀.a, P₀.b] : List ℝ).Pairwise (· < ·) := hcyc.2.1
    have hab : P₀.a < P₀.b := List.rel_of_pairwise_cons hpair (by simp)
    have hb_lt : P₀.b < P₀.a + 1 := by
      have := hcyc.2.2 P₀.b (by simp)
      simpa using this
    have hf_eq : Int.fract (P₀.a + 1 - P₀.b) = P₀.a + 1 - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmval : Work.EL.midNear [P₀] = P₀.b + (P₀.a + 1 - P₀.b) / 2 := by
      rw [Work.EL.midNear.eq_2, hf_eq]
    refine ⟨0, ?_⟩
    rw [hmval]
    simp only [Int.cast_zero, add_zero, Set.mem_Ioo]
    constructor <;> linarith
  · -- `ps = P₀ :: Q :: tl`: the reference angle lies in the gap `(P₀.b, Q.a)`.
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
    have hab0 : P₀.a < P₀.b := hp1.1 P₀.b (by simp)
    have hba : P₀.b < Q.a := hp2.1 Q.a (by simp)
    have hQam : Q.a ∈ (P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b]) :=
      List.mem_flatMap.mpr ⟨Q, by simp, by simp⟩
    have hQa_lt : Q.a < P₀.a + 1 := hupper Q.a hQam
    have hf_eq : Int.fract (Q.a - P₀.b) = Q.a - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmval : Work.EL.midNear (P₀ :: Q :: tl) = P₀.b + (Q.a - P₀.b) / 2 := by
      rw [Work.EL.midNear.eq_1, hf_eq]
    have hx_gt0 : P₀.b < P₀.b + (Q.a - P₀.b) / 2 := by linarith
    have hx_lt_Qa : P₀.b + (Q.a - P₀.b) / 2 < Q.a := by linarith
    have hx_lt_a0 : P₀.b + (Q.a - P₀.b) / 2 < P₀.a + 1 := by linarith
    have hpairQ : ((Q :: tl).flatMap (fun R => [R.a, R.b])).Pairwise (· < ·) := hp2.2
    have hmin : ∀ R ∈ Q :: tl, Q.a ≤ R.a :=
      midNear_head_le_of_pairwise_flatMap Q tl (fun R => R.a) (fun R => R.b) hpairQ
    rcases List.mem_cons.mp hP with rfl | hPtl
    · -- `P = P₀`
      refine ⟨0, ?_⟩
      rw [hmval]
      simp only [Int.cast_zero, add_zero, Set.mem_Ioo]
      exact ⟨hx_gt0, hx_lt_a0⟩
    · -- `P ∈ Q :: tl`: the translate `midNear ps + 1` lies in `(P.b, P.a + 1)`.
      have hPmem : P ∈ P₀ :: Q :: tl := List.mem_cons_of_mem P₀ hPtl
      have hx_lt_Pa : P₀.b + (Q.a - P₀.b) / 2 < P.a := by
        have := hmin P hPtl
        linarith
      have hPb_lt : P.b < P₀.b + (Q.a - P₀.b) / 2 + 1 := by
        have hPbm : P.b ∈ (P₀ :: Q :: tl).flatMap (fun R => [R.a, R.b]) :=
          List.mem_flatMap.mpr ⟨P, hPmem, by simp⟩
        have := hupper P.b hPbm
        linarith
      refine ⟨1, ?_⟩
      rw [hmval]
      simp only [Int.cast_one, Set.mem_Ioo]
      exact ⟨hPb_lt, by linarith⟩

end Work.ELTop
