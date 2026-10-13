import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4b.posPoly_mem

/-!
  Area G4b / MeasBound: the sub- and super-level sets of a definable function of one variable
  are `Ω`-sets, with format and degree bounds that are *uniform* in the level `y`.

  Given an `Ω`-set `Γ = graphOf G ⊆ ℝ²` of format `F` and degree `D`, and reals `c, d`, we
  produce `K` and `p` with

      `{x : ℝ¹ | x 0 ∈ (c,d) ∧ y < G (x 0)}`  and  `{x : ℝ¹ | x 0 ∈ (c,d) ∧ G (x 0) < y}`

  in `Ω (F+K) (p.eval D) 1` for every real `y`.

  The mechanism: cut `Γ` by the horizontal half-plane `{z | y < z 1}`, which costs only a
  numeral format and degree (`ltSet_mem`, `gtSet_mem`), and project out the value coordinate.
  Projecting the intersection removes the value, but the graph already forces that value to be
  `G` of the first coordinate, so the projection is exactly the super-level set of `G`.  A
  final intersection with the numeral-bounded interval `(c,d)` in `ℝ¹`, and a monotonicity
  step, give the stated bounds (`K = 50`, `p = X + 40`).
-/

set_option autoImplicit false

namespace Work.WilG4b.MeasBound

open WilkiesDesign WilkiesConjecture

/-! ## 0. Evaluation of `Fin.snoc` in `Fin 2 → ℝ` -/

/-- The value appended by `Fin.snoc`, evaluated at the last index. -/
theorem snoc_two_last (x : Fin 1 → ℝ) (t : ℝ) :
    (Fin.snoc x t : Fin 2 → ℝ) (Fin.last 1) = t :=
  @Fin.snoc_last 1 (fun _ => ℝ) t x

/-- The value appended by `Fin.snoc`, evaluated at the index `1`. -/
theorem snoc_two_one (x : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc x t : Fin 2 → ℝ) 1 = t := by
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, snoc_two_last]

/-- `Fin.snoc` does not change the first coordinate. -/
theorem snoc_two_zero (x : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc x t : Fin 2 → ℝ) 0 = x 0 :=
  @Fin.snoc_castSucc 1 (fun _ => ℝ) t x 0

/-- `Fin.init` discards the value appended by `Fin.snoc`. -/
theorem init_snoc_two (x : Fin 1 → ℝ) (t : ℝ) : Fin.init (Fin.snoc x t : Fin 2 → ℝ) = x :=
  @Fin.init_snoc 1 (fun _ => ℝ) t x

/-! ## 1. Membership in the graph of a function of one variable -/

/-- A point of `ℝ²` lies on the graph of `G` exactly when its second coordinate is the value
of `G` at its first coordinate. -/
theorem mem_graphOf_one (G : ℝ → ℝ) (u : Fin 2 → ℝ) :
    u ∈ graphOf (fun x : Fin 1 → ℝ => G (x 0)) ↔ u 1 = G (u 0) := by
  rw [graphOf, Set.mem_ofPred_eq]
  have h : Fin.init u = fun _ => u 0 := by
    funext i
    fin_cases i
    rfl
  rw [h]
  rfl

/-! ## 2. Cutting the graph by a horizontal half-plane and projecting -/

/-- Projecting the graph cut by the upper half-plane `{y < z 1}` recovers the super-level set
of `G`, because the graph pins the value coordinate to `G` of the first coordinate. -/
theorem projLast_graph_gt (G : ℝ → ℝ) (y : ℝ) :
    projLast (graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∩ {z : Fin 2 → ℝ | y < z 1}) =
      {x : Fin 1 → ℝ | y < G (x 0)} := by
  ext x
  simp only [projLast, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨t, hmem, hy⟩
    rw [mem_graphOf_one (G := G) (u := Fin.snoc x t)] at hmem
    rw [snoc_two_one x t, snoc_two_zero x t] at hmem
    rw [snoc_two_one x t] at hy
    rw [← hmem]
    exact hy
  · intro hy
    refine ⟨G (x 0), ?_, ?_⟩
    · rw [mem_graphOf_one (G := G) (u := Fin.snoc x (G (x 0))), snoc_two_one x (G (x 0)),
        snoc_two_zero x (G (x 0))]
    · rw [snoc_two_one x (G (x 0))]
      exact hy

/-- Projecting the graph cut by the lower half-plane `{z 1 < y}` recovers the sub-level set
of `G`. -/
theorem projLast_graph_lt (G : ℝ → ℝ) (y : ℝ) :
    projLast (graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∩ {z : Fin 2 → ℝ | z 1 < y}) =
      {x : Fin 1 → ℝ | G (x 0) < y} := by
  ext x
  simp only [projLast, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨t, hmem, hy⟩
    rw [mem_graphOf_one (G := G) (u := Fin.snoc x t)] at hmem
    rw [snoc_two_one x t, snoc_two_zero x t] at hmem
    rw [snoc_two_one x t] at hy
    rw [← hmem]
    exact hy
  · intro hy
    refine ⟨G (x 0), ?_, ?_⟩
    · rw [mem_graphOf_one (G := G) (u := Fin.snoc x (G (x 0))), snoc_two_one x (G (x 0)),
        snoc_two_zero x (G (x 0))]
    · rw [snoc_two_one x (G (x 0))]
      exact hy

/-! ## 3. The interval `(c,d)` in `ℝ¹` -/

/-- The interval `(c,d)` is an `Ω`-subset of `ℝ¹` with numeral format and degree. -/
theorem interval_mem (S : WilkiesDesign.SOMin) (c d : ℝ) :
    {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d} ∈ S.Ω 25 16 1 := by
  have h1 : {x : Fin 1 → ℝ | c < x 0} ∈ S.Ω 24 ((Polynomial.C 8).eval 0) 1 := by
    rw [Polynomial.eval_C]
    exact Work.WilG5.ltSet_mem (S := S) (n := 1) (0 : Fin 1) c
  have h2 : {x : Fin 1 → ℝ | x 0 < d} ∈ S.Ω 24 ((Polynomial.C 8).eval 0) 1 := by
    rw [Polynomial.eval_C]
    exact Work.WilG5.gtSet_mem (S := S) (n := 1) (0 : Fin 1) d
  have h := Work.WilG1.Omega.inter₂ (S := S) h1 h2
  have hset : {x : Fin 1 → ℝ | c < x 0} ∩ {x : Fin 1 → ℝ | x 0 < d}
      = {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo]
  rw [hset] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  omega

/-! ## 4. The level sets -/

theorem levelSet_mem (S : WilkiesDesign.SOMin) {F D : ℕ} (G : ℝ → ℝ) (c d : ℝ)
    (hG : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ y : ℝ,
      {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d ∧ y < G (x 0)} ∈ S.Ω (F + K) (p.eval D) 1 ∧
      {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d ∧ G (x 0) < y} ∈ S.Ω (F + K) (p.eval D) 1 := by
  have hI : {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d} ∈ S.Ω 25 16 1 := interval_mem S c d
  -- the graph, at the common format `F + 28` and with degree written as `X.eval D`
  have hΓ : graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω (F + 28) ((Polynomial.X).eval D) 2 := by
    rw [Polynomial.eval_X]
    exact Work.WilG5.mem_monoF hG 28
  refine ⟨31, Polynomial.X + Polynomial.C 8 + Polynomial.C 16, fun y => ⟨?_, ?_⟩⟩
  · -- the super-level set `{y < G}`
    have hH : {z : Fin 2 → ℝ | y < z 1} ∈ S.Ω (F + 28) ((Polynomial.C 8).eval D) 2 := by
      rw [Polynomial.eval_C]
      exact Work.WilG1.Omega.mono (Work.WilG5.ltSet_mem (S := S) (n := 2) (1 : Fin 2) y)
        (by omega) le_rfl
    have hInt : graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∩ {z : Fin 2 → ℝ | y < z 1} ∈
        S.Ω (max (F + 28) (F + 28) + 1) ((Polynomial.X + Polynomial.C 8).eval D) 2 :=
      Work.WilG1.Omega.inter₂ (S := S) hΓ hH
    have hProj : projLast (graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∩ {z : Fin 2 → ℝ | y < z 1}) ∈
        S.Ω (max (F + 28) (F + 28) + 2) ((Polynomial.X + Polynomial.C 8).eval D) 1 :=
      S.proj hInt
    rw [projLast_graph_gt G y] at hProj
    have hI' : {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d} ∈
        S.Ω (max (F + 28) (F + 28) + 2) ((Polynomial.C 16).eval D) 1 := by
      rw [Polynomial.eval_C]
      exact Work.WilG1.Omega.mono hI (by omega) le_rfl
    have hRes := Work.WilG1.Omega.inter₂ (S := S) hProj hI'
    have hset : {x : Fin 1 → ℝ | y < G (x 0)} ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d}
        = {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d ∧ y < G (x 0)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset] at hRes
    exact Work.WilG1.Omega.mono hRes (by omega) le_rfl
  · -- the sub-level set `{G < y}`
    have hH : {z : Fin 2 → ℝ | z 1 < y} ∈ S.Ω (F + 28) ((Polynomial.C 8).eval D) 2 := by
      rw [Polynomial.eval_C]
      exact Work.WilG1.Omega.mono (Work.WilG5.gtSet_mem (S := S) (n := 2) (1 : Fin 2) y)
        (by omega) le_rfl
    have hInt : graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∩ {z : Fin 2 → ℝ | z 1 < y} ∈
        S.Ω (max (F + 28) (F + 28) + 1) ((Polynomial.X + Polynomial.C 8).eval D) 2 :=
      Work.WilG1.Omega.inter₂ (S := S) hΓ hH
    have hProj : projLast (graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∩ {z : Fin 2 → ℝ | z 1 < y}) ∈
        S.Ω (max (F + 28) (F + 28) + 2) ((Polynomial.X + Polynomial.C 8).eval D) 1 :=
      S.proj hInt
    rw [projLast_graph_lt G y] at hProj
    have hI' : {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d} ∈
        S.Ω (max (F + 28) (F + 28) + 2) ((Polynomial.C 16).eval D) 1 := by
      rw [Polynomial.eval_C]
      exact Work.WilG1.Omega.mono hI (by omega) le_rfl
    have hRes := Work.WilG1.Omega.inter₂ (S := S) hProj hI'
    have hset : {x : Fin 1 → ℝ | G (x 0) < y} ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d}
        = {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d ∧ G (x 0) < y} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset] at hRes
    exact Work.WilG1.Omega.mono hRes (by omega) le_rfl

end Work.WilG4b.MeasBound
