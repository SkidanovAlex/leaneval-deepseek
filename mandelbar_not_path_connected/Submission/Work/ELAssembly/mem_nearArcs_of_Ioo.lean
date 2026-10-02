import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## Two elementary facts about `Int.fract` on the interval `(-1, 1)` -/

/-- `Int.fract` fixes the interval `[0, 1)`. -/
theorem fract_eq_self_of_mem_Ico {y : ℝ} (h1 : 0 ≤ y) (h2 : y < 1) : Int.fract y = y :=
  Int.fract_eq_self.mpr ⟨h1, h2⟩

/-- `Int.fract` of a number in `(-1, 0)` is `y + 1`. -/
theorem fract_eq_add_one_of_mem_Ioo {y : ℝ} (h1 : -1 < y) (h2 : y < 0) : Int.fract y = y + 1 := by
  have hfloor : ⌊y⌋ = (-1 : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  rw [← Int.self_sub_floor y, hfloor]
  norm_num

/-- The four consecutive strict inequalities encoded by `CyclicStrict` on a four-element list. -/
theorem cycStrict_four_data {a b c d : ℝ} (h : Work.EL.CyclicStrict [a, b, c, d]) :
    a < b ∧ b < c ∧ c < d ∧ d < a + 1 := by
  obtain ⟨-, hpair, hhead⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hpair.rel_get_of_lt (show (⟨0, by simp⟩ : Fin 4) < (⟨1, by simp⟩ : Fin 4) by simp)
    simpa using this
  · have := hpair.rel_get_of_lt (show (⟨1, by simp⟩ : Fin 4) < (⟨2, by simp⟩ : Fin 4) by simp)
    simpa using this
  · have := hpair.rel_get_of_lt (show (⟨2, by simp⟩ : Fin 4) < (⟨3, by simp⟩ : Fin 4) by simp)
    simpa using this
  · have := hhead d (by simp)
    simpa using this

/-- **The two intervals `(P0.b, β'_{n+1})` and `(β_{n+1} + 1, P0.a + 1)` lie in the near arcs of
the level-`(n+1)` polygon.**  Assume `[P0, N.Qp k]` admissible for every `k`.  If `x` lies in
either of the two intervals then `x` lies in no closed far arc of the level-`(n+1)` polygon
`[P0, N.Qp (n+1)]`.

Admissibility at level `n+1` gives `P0.a < P0.b < β'_{n+1} < β_{n+1} + 1 < P0.a + 1` (with
`β'_{n+1} = (N.Qp (n+1)).a` and `β_{n+1} + 1 = (N.Qp (n+1)).b`).

* For `x ∈ (P0.b, β'_{n+1})`: `Int.fract (x - P0.a) = x - P0.a > P0.b - P0.a = arcLen P0.a P0.b`
  (using `x < β'_{n+1} < P0.a + 1`), and `x - β'_{n+1} ∈ (-1, 0)` with
  `Int.fract (x - β'_{n+1}) = x - β'_{n+1} + 1 > β_{n+1} + 1 - β'_{n+1}` (using `x > P0.b > P0.a > β_{n+1}`).
* For `x ∈ (β_{n+1} + 1, P0.a + 1)`: `x - P0.a ∈ (0,1)` and `x - P0.a > P0.b - P0.a` (using
  `x > β_{n+1} + 1 > β'_{n+1} > P0.b`), and `x - β'_{n+1} ∈ (0,1)` with
  `Int.fract (x - β'_{n+1}) = x - β'_{n+1} > β_{n+1} + 1 - β'_{n+1}`.

Both are `arcLen`s of the corresponding closed far arcs `[P0.a, P0.b]` and
`[β'_{n+1}, β_{n+1}+1]`, so `InClosedArc` fails in both cases. -/
theorem mem_nearArcs_of_Ioo {c : ℂ} {d : Work.EL.RootParabolic c}
    {P0 : Work.EL.CoPair d.hN} {N : Work.ELAssembly.NestPairs d}
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) {n : ℕ} {x : ℝ}
    (h : (P0.b < x ∧ x < Work.ELNest.bAng' (n + 1)) ∨
      (Work.ELNest.bAng (n + 1) + 1 < x ∧ x < P0.a + 1)) :
    ∀ P ∈ [P0, N.Qp (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b := by
  -- The four angles of the level-`(n+1)` polygon, in strict cyclic order.
  obtain ⟨-, hcyc, -⟩ := hadm (n + 1)
  have hflat : ([P0, N.Qp (n + 1)].flatMap fun P => [P.a, P.b]) =
      [P0.a, P0.b, (N.Qp (n + 1)).a, (N.Qp (n + 1)).b] := rfl
  rw [hflat] at hcyc
  obtain ⟨hAB, hBQa, hQaQb, hQbA⟩ := cycStrict_four_data hcyc
  simp only [N.Qpa (n + 1), N.Qpb (n + 1)] at hBQa hQaQb hQbA
  -- The two far arcs `[P0.a, P0.b]` and `[β'_{n+1}, β_{n+1}+1]` have lengths `P0.b - P0.a`
  -- and `β_{n+1} + 1 - β'_{n+1}` (both differences lie in `[0,1)`).
  have hBA : Int.fract (P0.b - P0.a) = P0.b - P0.a :=
    fract_eq_self_of_mem_Ico (by linarith) (by linarith)
  have hQQ : Int.fract (Work.ELNest.bAng (n + 1) + 1 - Work.ELNest.bAng' (n + 1)) =
      Work.ELNest.bAng (n + 1) + 1 - Work.ELNest.bAng' (n + 1) :=
    fract_eq_self_of_mem_Ico (by linarith) (by linarith)
  have hP0 : ¬ Work.EL.InClosedArc x P0.a P0.b := by
    intro hc
    have h2 : Int.fract (x - P0.a) ≤ Int.fract (P0.b - P0.a) := hc.2
    rcases h with ⟨hxl, hxr⟩ | ⟨hxl, hxr⟩
    · -- `x ∈ (P0.b, β'_{n+1})`
      have hfx : Int.fract (x - P0.a) = x - P0.a :=
        fract_eq_self_of_mem_Ico (by linarith) (by linarith)
      rw [hfx, hBA] at h2
      linarith
    · -- `x ∈ (β_{n+1} + 1, P0.a + 1)`
      have hfx : Int.fract (x - P0.a) = x - P0.a :=
        fract_eq_self_of_mem_Ico (by linarith) (by linarith)
      rw [hfx, hBA] at h2
      linarith
  have hQ : ¬ Work.EL.InClosedArc x (N.Qp (n + 1)).a (N.Qp (n + 1)).b := by
    rw [N.Qpa (n + 1), N.Qpb (n + 1)]
    intro hc
    have h2 : Int.fract (x - Work.ELNest.bAng' (n + 1)) ≤
        Int.fract (Work.ELNest.bAng (n + 1) + 1 - Work.ELNest.bAng' (n + 1)) := hc.2
    rcases h with ⟨hxl, hxr⟩ | ⟨hxl, hxr⟩
    · -- `x ∈ (P0.b, β'_{n+1})`: `x - β'_{n+1} ∈ (-1, 0)`
      have hfx := fract_eq_add_one_of_mem_Ioo
        (y := x - Work.ELNest.bAng' (n + 1)) (by linarith) (by linarith)
      rw [hfx, hQQ] at h2
      linarith
    · -- `x ∈ (β_{n+1} + 1, P0.a + 1)`: `x - β'_{n+1} ∈ (0, 1)`
      have hfx := fract_eq_self_of_mem_Ico
        (y := x - Work.ELNest.bAng' (n + 1)) (by linarith) (by linarith)
      rw [hfx, hQQ] at h2
      linarith
  intro P hP
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with h' | h'
  · rw [h']; exact hP0
  · rw [h']; exact hQ

end Work.ELAssembly
