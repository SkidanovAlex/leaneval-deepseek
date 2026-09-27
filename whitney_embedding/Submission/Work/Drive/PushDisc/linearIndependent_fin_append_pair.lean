import Mathlib

namespace Work.Drive.PushDisc

open scoped Matrix

/-- Linear independence of the family obtained by prepending the pair `(a, η)` to `V`, in the
situation where `a = b + (2 * x) • η`, `b` lies outside the span of `V`, and `η` lies outside the
span of `b` together with `V`.

The proof works by transporting the coefficients of the "first two" positions: writing
`G = Fin.cons η (Fin.cons b V)` (an independent family, by `LinearIndependent.finCons` applied
twice), a relation `∑ g i • (Fin.append ![a, η] V) i = 0` produces a relation
`∑ d i • G i = 0` with `d 0 = g 0 * (2 * x) + g 1`, `d 1 = g 0` and `d i = g i` for `i ≥ 2`;
since `(g 0 * (2 * x) + g 1) • η + g 0 • b = g 0 • a + g 1 • η`, the two relations have the same
content. -/
theorem linearIndependent_fin_append_pair {E : Type*} [AddCommGroup E] [Module ℝ E]
    {k : ℕ} {V : Fin k → E} {a b η : E} {x : ℝ}
    (hV : LinearIndependent ℝ V)
    (hbV : b ∉ Submodule.span ℝ (Set.range V))
    (hη : η ∉ Submodule.span ℝ (Set.range (Fin.cons b V)))
    (ha : a = b + (2 * x) • η) :
    LinearIndependent ℝ (Fin.append ![a, η] V) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- the family `(η, b, V)` is independent
  have h2 : LinearIndependent ℝ (Fin.cons η (Fin.cons b V)) :=
    LinearIndependent.finCons (LinearIndependent.finCons hV hbV) hη
  show ∀ i, g i = 0
  -- decompose the relation `∑ i, g i • (Fin.append ![a, η] V) i = 0`
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  -- `hg : g c₀ • a + g c₁ • η + (∑ j, g j' • V j) = 0`; substituting `a = b + 2x • η` gives the
  -- corresponding relation for the family `(η, b, V)`
  have hrel : (g (Fin.castAdd k 0) * (2 * x) + g (Fin.castAdd k 1)) • η
      + g (Fin.castAdd k 0) • b + ∑ j : Fin k, g (Fin.natAdd 2 j) • V j = 0 := by
    rw [← hg, ha, smul_add, smul_smul, add_smul]
    abel
  -- the coefficient vector of this relation in the basis-free family `(η, b, V)`
  let d : Fin (k + 1 + 1) → ℝ := Fin.cons (g (Fin.castAdd k 0) * (2 * x) + g (Fin.castAdd k 1))
    (Fin.cons (g (Fin.castAdd k 0)) (fun j : Fin k => g (Fin.natAdd 2 j)))
  have hd : (∑ i : Fin (k + 1 + 1),
      d i • (Fin.cons η (Fin.cons b V) : Fin (k + 1 + 1) → E) i) = 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [d, Fin.cons_zero, Fin.cons_succ]
    rw [← hrel]
    abel
  have hzero : ∀ i : Fin (k + 1 + 1), d i = 0 := (Fintype.linearIndependent_iff.mp h2) d hd
  -- extract the values of `g` on the three groups of positions
  have hc0 : g (Fin.castAdd k 0) = 0 := by
    have h := hzero (Fin.succ (0 : Fin (k + 1)))
    simpa only [d, Fin.cons_zero, Fin.cons_succ] using h
  have hc1 : g (Fin.castAdd k 1) = 0 := by
    have h0 := hzero (0 : Fin (k + 1 + 1))
    simp only [d, Fin.cons_zero, hc0, zero_mul, zero_add] at h0
    exact h0
  have hgj : ∀ j : Fin k, g (Fin.natAdd 2 j) = 0 := by
    intro j
    have h := hzero (Fin.succ (Fin.succ j))
    simpa only [d, Fin.cons_succ] using h
  intro i
  induction i using Fin.addCases with
  | left i' => fin_cases i' <;> simp [hc0, hc1]
  | right j => exact hgj j

end Work.Drive.PushDisc
