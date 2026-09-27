import Mathlib
import Submission.Work.KT.Fund.kl_wh_defs

/-!
# `Work.KT.Fund.klWh_slice0` — the `t = 0` slice of the homotopy of the "outside" factor

The straight-line homotopy

  `klWh X n b E = klSZ • (1 - E) + (1 - E) b + E`,
  `klSZ (x, t, z) = t z`,

of `Work.KT.Fund.kl_wh_defs` deforms the `z`-dependent matrix `klW X n b E` (its `t = 1` slice)
to the `z`-independent matrix `E + (1 - E) b`.  This file records the `t = 0` end: pulling `klWh`
back along `incl0 X : (x, z) ↦ ((x, 0), z)` kills the scalar `klSZ` (since `t = 0`), leaving the
pull-back to `X × S¹` of the matrix `E + (1 - E) b` over `C(X, ℂ)`:

  `klWh_slice0 : (klWh X n b E).map (fun f => f.comp (incl0 X)) = pullMat X (E + (1 - E) * b)`.

The proof is a direct computation of the entries of the two matrices at a point `(x, z)`:
`klWh` is expanded entrywise (the `t = 0` value of each entry), the scalar `klSZ ((x,0),z)`
vanishes, and what is left is exactly the pullback of `E + (1 - E) * b`.
-/

namespace Work.KT.Fund

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The inclusion of the `t = 0` slice, on points. -/
private lemma klWh_slice0_incl0_apply (p : X × Sph ℂ) :
    incl0 X p = ((p.1, (0 : unitInterval)), p.2) := rfl

/-- **The entries of the homotopy matrix `klWh`.**  At a point `y = ((x, t), z)` the `(i, j)` entry
of `klWh` is `(t z) * ((1 - E) i j)(x) + ((1 - E) b) i j (x) + E i j (x)`, written out with the
elementary matrices and the multiplication of `C(X, ℂ)`. -/
private lemma klWh_slice0_apply (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (y : (X × unitInterval) × Sph ℂ) :
    klWh X n b E i j y
      = (klSZ X y) * ((if i = j then (1 : ℂ) else 0) - E i j y.1.1)
        + (∑ k, ((if i = k then (1 : ℂ) else 0) - E i k y.1.1) * b k j y.1.1)
        + E i j y.1.1 := by
  simp only [klWh, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.one_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.one_apply, ContinuousMap.zero_apply,
    DFunLike.ite_apply, klSZ_apply, klProj_apply, smul_eq_mul, ContinuousMap.comp_apply,
    ContinuousMap.coe_sum, Finset.sum_apply]

theorem klWh_slice0 (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Work.KT.Fund.klWh X n b E).map (fun f => f.comp (Work.KT.Fund.incl0 X))
      = Work.KT.Fund.pullMat X (E + (1 - E) * b) := by
  ext i j p
  change klWh X n b E i j (incl0 X p) = (E + (1 - E) * b) i j p.1
  rw [klWh_slice0_apply]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, ContinuousMap.zero_apply, DFunLike.ite_apply,
    ContinuousMap.coe_sum, Finset.sum_apply, klSZ_apply, klWh_slice0_incl0_apply,
    show (((0 : unitInterval) : ℝ) : ℂ) = 0 from rfl, zero_mul, zero_add]
  ring

end

end Work.KT.Fund
