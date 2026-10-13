import Mathlib
import Submission.Work.WilC4.badScale_aux

namespace Work.WilC4.BSpieces

open Work.WilC4 Work.WilC4.BSAux

/-- Membership in the deepness *body* (all quantified variables free): the tuple
`(u 0, c, ...)` lies in the breakpoint family `B`, the quotient `u 1` is `x/(2M)`, and
`x/(2M) ≤ u 0 ≤ 2 M x` — where the parameters `c`, `M`, `x` are read off from `g`. -/
theorem mem_BSDeepBody_iff {k : ℕ} (B : Set (Fin (k + 1) → ℝ)) (g : BSAux.BSI k → ℝ)
    (u : Fin 2 → ℝ) :
    Sum.elim g u ∈ BSAux.BSDeepBody B ↔
      (Fin.cons (u 0) (fun i : Fin k => g (BSAux.sc i)) ∈ B ∧
       IsDivR (g BSAux.sx) (2 * g BSAux.sM) (u 1) ∧
       u 1 ≤ u 0 ∧ u 0 ≤ 2 * g BSAux.sM * g BSAux.sx) := by
  simp only [BSAux.BSDeepBody, Set.mem_ofPred_eq, GrSub1, Sum.elim_inl, Sum.elim_inr]
  rw [show Sum.elim g u ∘ BSAux.bEmb k = fun i : Fin k => g (BSAux.sc i) from by
    funext i; simp [BSAux.bEmb]]

theorem mem_BSDeep_iff {k : ℕ} (B : Set (Fin (k + 1) → ℝ)) (g : Work.WilC4.BSAux.BSI k → ℝ) :
    g ∈ Work.WilC4.BSAux.BSDeep B ↔
      Work.WilC4.IsDeepR B (fun i : Fin k => g (Work.WilC4.BSAux.sc i))
        (g Work.WilC4.BSAux.sM) (g Work.WilC4.BSAux.sx) := by
  constructor
  · -- `BSDeep` ⟹ `IsDeepR`: realise the counterexample `(b, x/(2M))` as a tuple `u`.
    intro h b hb hbc
    set q : ℝ := g BSAux.sx / (2 * g BSAux.sM) with hq
    set u : Fin 2 → ℝ := fun j => if j = 0 then b else q with hu
    have hu0 : u 0 = b := by simp [hu]
    have hu1 : u 1 = q := by simp [hu]
    have hdiv : IsDivR (g BSAux.sx) (2 * g BSAux.sM) (u 1) := by
      rw [hu1, hq, isDivR_iff]
    exact h u ((mem_BSDeepBody_iff B g u).mpr
      ⟨by rwa [hu0], hdiv, by rw [hu1, hq]; exact hbc.1, by rw [hu0]; exact hbc.2⟩)
  · -- `IsDeepR` ⟹ `BSDeep`: the quotient `u 1` is forced to be `x/(2M)` by `IsDivR`.
    intro h u hu
    obtain ⟨hb, hdiv, hle, hub⟩ := (mem_BSDeepBody_iff B g u).mp hu
    have hq : g BSAux.sx / (2 * g BSAux.sM) = u 1 := (isDivR_iff _ _ _).mp hdiv
    exact h (u 0) hb ⟨by rw [hq]; exact hle, hub⟩

end Work.WilC4.BSpieces
