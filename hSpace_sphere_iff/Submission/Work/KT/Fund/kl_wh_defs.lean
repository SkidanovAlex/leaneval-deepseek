import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs

/-!
# `Work.KT.Fund.kl_wh_defs` — the straight-line homotopy of the "outside" factor `klW`

The matrix `klW X n b E = E + z (1 - E) + (1 - E) b` of `Work.KT.Fund.kl_defs` is the `t = 1`
end of the straight-line homotopy

  `H_t = E + (1 - E) b + t z (1 - E)`   (`t ∈ [0,1]`, `z ∈ S¹`),

whose `t = 0` end is the `z`-independent (hence pulled back from `X`) matrix `E + (1 - E) b`.
Under the invertibility hypothesis `hout` (that `t z (1 - E) + (1 - E) b + E` is pointwise
invertible for `t ∈ [0,1]`, `‖z‖ = 1`) this homotopy runs through units, so `kappa` of `klW` is
`kappa` of the pulled-back unit `E + (1 - E) b`, which is `[1_n]` by `Work.KT.Fund.kappa_const`.

This file provides

* `klProj`, `klSZ` — the projection `(X × [0,1]) × S¹ → X` and the scalar `(x,t,z) ↦ t·z`;
* `klWh X n b E` — the matrix `H` of the homotopy, over `C((X × [0,1]) × S¹, ℂ)`;
* `klWh_eval` — its value at a point `((x,t),z)`, which is exactly the matrix appearing in `hout`.

The comparable statements about `klWh` (`klWh_slice0`, `klWh_slice1`, `klWh_isUnit`) and the unit
`E + (1-E) b` are proved in the sibling modules requested by `kl_w_cls`.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The projection `(X × [0,1]) × S¹ → X`, forgetting the interval and circle coordinates. -/
def klProj : C((X × unitInterval) × Sph ℂ, X) := ⟨fun q => q.1.1, by fun_prop⟩

/-- The scalar `(x, t, z) ↦ t · z` on `(X × [0,1]) × S¹`. -/
def klSZ : C((X × unitInterval) × Sph ℂ, ℂ) :=
  ⟨fun q => ((q.1.2 : ℝ) : ℂ) * (q.2 : ℂ), by fun_prop⟩

@[simp] lemma klProj_apply (q : (X × unitInterval) × Sph ℂ) : klProj X q = q.1.1 := rfl

@[simp] lemma klSZ_apply (q : (X × unitInterval) × Sph ℂ) :
    klSZ X q = ((q.1.2 : ℝ) : ℂ) * (q.2 : ℂ) := rfl

/-- The matrix of the straight-line homotopy `H_t = t z (1 - E) + (1 - E) b + E`, over
`C((X × [0,1]) × S¹, ℂ)`.  Its `t = 0` slice is `(1 - E) b + E` and its `t = 1` slice is
`klW X n b E`. -/
def klWh (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
  klSZ X • (1 - E.map (fun f => f.comp (klProj X)))
    + (1 - E.map (fun f => f.comp (klProj X))) * (b.map (fun f => f.comp (klProj X)))
    + E.map (fun f => f.comp (klProj X))

/-- **The value of the homotopy matrix at a point.**  At `((x, t), z)` the matrix `klWh` is exactly
the matrix whose pointwise invertibility is the hypothesis `hout`. -/
lemma klWh_eval (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) (s : unitInterval)
    (z : Sph ℂ) :
    (klWh X n b E).map (fun g => g ((x, s), z))
      = ((((s : ℝ) : ℂ) * (z : ℂ)) • (1 - E) + (1 - E) * b + E).map (fun f => f x) := by
  ext i j
  simp only [klWh, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, klSZ_apply, klProj_apply, smul_eq_mul,
    ContinuousMap.coe_sum, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.comp_apply,
    ContinuousMap.smul_apply, Finset.sum_apply, ContinuousMap.zero_apply,
    DFunLike.ite_apply]

end

end Work.KT.Fund
