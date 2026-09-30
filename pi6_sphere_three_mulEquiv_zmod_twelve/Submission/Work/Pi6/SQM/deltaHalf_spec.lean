import Mathlib
import Submission.Work.Pi6.SQM.SqOneDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The half-coboundary identity `δ(ỹ) = 2 · deltaHalf x`

For a mod-2 `2`-cocycle `x` with `0/1` lift `x̃ = liftZ X 2 x`, the integral coboundary `δx̃` is
even and equals twice the cochain `deltaHalf x` of `SqOneDefs`.  Pointwise on a `3`-simplex `σ`,
writing `a_i = genEval ℤ X (liftZ X 2 x) (X.δ i σ) ∈ {0,1}` (`i = 0,1,2,3`),

`(δx̃)(σ) = a₀ - a₁ + a₂ - a₃`  and  `2 · (deltaHalf x)(σ) = 2 (a₀a₂ - a₃a₁)`,

so the statement is the elementary identity `a₀ - a₁ + a₂ - a₃ = 2 (a₀a₂ - a₃a₁)` for `{0,1}`-valued
`a_i` whose total sum is even (evenness being exactly the mod-2 cocycle condition `δx = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff genEval_ext genEval_smul genEval_add)

/-- The `0/1` section `valZ` of `ℤ → 𝔽₂` only takes the values `0` and `1`. -/
theorem valZ_eq_zero_or_one (a : F2) : valZ a = 0 ∨ valZ a = 1 := by
  have h : a.val < 2 := ZMod.val_lt a
  have h2 : a.val = 0 ∨ a.val = 1 := by omega
  rcases h2 with h3 | h3 <;> simp [valZ, h3]

/-- **The elementary half-coboundary identity.**  For `{0,1}`-valued integers `a b c d` whose sum is
even, `a - b + c - d = 2 (a c - d b)`. -/
theorem deltaHalf_arith (a b c d : ℤ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (h : (2 : ℤ) ∣ a + b + c + d) :
    a - b + c - d = 2 * (a * c - d * b) := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rcases hc with h3 | h3 <;>
    rcases hd with h4 | h4
  all_goals (rw [h1, h2, h3, h4] at h ⊢; obtain ⟨k, hk⟩ := h; omega)

theorem deltaHalf_spec (X : SSet) (x : Work.Cohomology.Cochain (ZMod 2) X 2)
    (hx : Work.Cohomology.cochainDiff (ZMod 2) X x = 0) :
    Work.Cohomology.cochainDiff ℤ X (Work.Pi6.SQM.liftZ X 2 x)
      = (2 : ℤ) • Work.Pi6.SQM.deltaHalf X x := by
  apply genEval_ext
  intro σ
  -- the mod-2 cocycle condition, evaluated at `σ`, gives the parity of the four `0/1` values
  have hzero : genEval F2 X (cochainDiff F2 X x) σ = 0 := by rw [hx]; rfl
  rw [Work.Cohomology.genEval_cochainDiff] at hzero
  have hb : genEval F2 X x (X.δ 0 σ) + genEval F2 X x (X.δ 1 σ) + genEval F2 X x (X.δ 2 σ)
      + genEval F2 X x (X.δ 3 σ) = 0 := by
    have hneg : (-1 : F2) = 1 := by decide
    rw [Fin.sum_univ_four] at hzero
    simpa only [hneg, one_pow, one_mul] using hzero
  have hdiv : (2 : ℤ) ∣ valZ (genEval F2 X x (X.δ 0 σ)) + valZ (genEval F2 X x (X.δ 1 σ))
      + valZ (genEval F2 X x (X.δ 2 σ)) + valZ (genEval F2 X x (X.δ 3 σ)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    push_cast
    rw [intCast_valZ, intCast_valZ, intCast_valZ, intCast_valZ]
    exact hb
  rw [Work.Cohomology.genEval_cochainDiff, genEval_smul, genEval_deltaHalf, Fin.sum_univ_four]
  simp only [genEval_liftZ]
  norm_num
  exact deltaHalf_arith _ _ _ _ (valZ_eq_zero_or_one _) (valZ_eq_zero_or_one _)
    (valZ_eq_zero_or_one _) (valZ_eq_zero_or_one _) hdiv

end

end Work.Pi6.SQM
