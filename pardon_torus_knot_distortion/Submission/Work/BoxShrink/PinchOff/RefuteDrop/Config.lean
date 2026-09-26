import Submission.Work.BoxShrink.PinchOff.CollarPair

/-!
# The counterexample to `DropCase`: the configuration

This directory machine-checks the refutation of the honest residual of the pinch (`DropCase`,
`Drop.lean`; equivalently `KeyTameClosed`, equivalently the parent chapter's `PinchNoJump` under the
general position of the cutting plane): there is a configuration of the challenge's family with

* `TransverseSlice` (the cutting plane transverse to the surface inside the box),
* `TameClosedSlice` (the closed slice a finite union of arcs and circles),
* the box-sphere trace inessential (`hS`) and the slice inessential (`hZ`),
* both closed halves inessential (`W(Halves) = ⊥`),

at which nevertheless `W(Ω) = ⊤`, so the conclusion `finrank W(Ω) ≤ 1` fails.  The configuration is

* `ψ = dropDiffeo`, the linear diffeomorphism of `ℝ³` with the rational matrix `dropA`
  (`det dropA = 617827/1000000`),
* `s = dropS = 7/5`, `c = dropC = 0`, `σ = dropCyc` (the transposition `0 ↔ 2`) and `u = dropU = 0`,

so that the box carries the sides `7/5`, `(7/5)·2^{1/3}`, `(7/5)·2^{2/3}` in the coordinates
`σ 0 = 2` (i.e. `z`), `σ 1 = 1` (i.e. `y`) and `σ 2 = 0` (i.e. `x`), and the cutting plane is
`{x = 0}`.

The refutation is assembled in `RefuteDrop/Main.lean`; `README.md` §41 records the numerical
certificate, together with the scripts of this directory that reproduce it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## The distortion -/

/-- The matrix of the counterexample's linear distortion. -/
def dropA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-2/25 : ℝ), (-39/100 : ℝ), (97/100 : ℝ);
     (81/100 : ℝ), (53/50 : ℝ), (-3/25 : ℝ);
     (49/100 : ℝ), (31/25 : ℝ), (59/100 : ℝ)]

/-- Its inverse (computed from the adjugate; `det dropA = 617827/1000000`). -/
def dropB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(774200/617827 : ℝ), (204700/88261 : ℝ), (-140200/88261 : ℝ);
     (-536700/617827 : ℝ), (-522500/617827 : ℝ), (776100/617827 : ℝ);
     (485000/617827 : ℝ), (-91900/617827 : ℝ), (231100/617827 : ℝ)]

/-- The forward map, as a linear map. -/
noncomputable def dropLM : R3 →ₗ[ℝ] R3 where
  toFun x := WithLp.toLp 2 (fun i : Fin 3 => ∑ j : Fin 3, dropA i j * x j)
  map_add' x y := by
    ext i
    simp only [WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp only [WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The inverse map, as a linear map. -/
noncomputable def dropLMInv : R3 →ₗ[ℝ] R3 where
  toFun x := WithLp.toLp 2 (fun i : Fin 3 => ∑ j : Fin 3, dropB i j * x j)
  map_add' x y := by
    ext i
    simp only [WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp only [WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The forward map, as a continuous linear map. -/
noncomputable def dropVec : R3 →L[ℝ] R3 := dropLM.toContinuousLinearMap

/-- The inverse map, as a continuous linear map. -/
noncomputable def dropVecInv : R3 →L[ℝ] R3 := dropLMInv.toContinuousLinearMap

theorem dropVec_apply (x : R3) (i : Fin 3) : dropVec x i = ∑ j : Fin 3, dropA i j * x j := by
  simp [dropVec, dropLM]

theorem dropVecInv_apply (x : R3) (i : Fin 3) :
    dropVecInv x i = ∑ j : Fin 3, dropB i j * x j := by
  simp [dropVecInv, dropLMInv]

/-- The entrywise product identity `dropB * dropA = 1`. -/
theorem dropB_mul_dropA (i j : Fin 3) :
    (∑ k : Fin 3, dropB i k * dropA k j) = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, dropA, dropB] <;> norm_num

/-- The entrywise product identity `dropA * dropB = 1`. -/
theorem dropA_mul_dropB (i j : Fin 3) :
    (∑ k : Fin 3, dropA i k * dropB k j) = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, dropA, dropB] <;> norm_num

theorem dropVecInv_dropVec (x : R3) : dropVecInv (dropVec x) = x := by
  ext i
  have h : ∀ j : Fin 3, (dropVec x).ofLp j = ∑ k : Fin 3, dropA j k * (x.ofLp k) :=
    fun j => dropVec_apply x j
  rw [dropVecInv_apply]
  simp only [h, Fin.sum_univ_three]
  fin_cases i <;>
    (simp [Fin.sum_univ_three, dropA, dropB]; ring_nf)

theorem dropVec_dropVecInv (x : R3) : dropVec (dropVecInv x) = x := by
  ext i
  have h : ∀ j : Fin 3, (dropVecInv x).ofLp j = ∑ k : Fin 3, dropB j k * (x.ofLp k) :=
    fun j => dropVecInv_apply x j
  rw [dropVec_apply]
  simp only [h, Fin.sum_univ_three]
  fin_cases i <;>
    (simp [Fin.sum_univ_three, dropA, dropB]; ring_nf)

/-- **The linear diffeomorphism of the counterexample.** -/
noncomputable def dropDiffeo : Submission.Diffeo where
  toFun := dropVec
  invFun := dropVecInv
  smooth_toFun := dropVec.contDiff
  smooth_invFun := dropVecInv.contDiff
  left_inv := dropVecInv_dropVec
  right_inv := dropVec_dropVecInv

theorem dropDiffeo_apply (x : R3) : dropDiffeo x = dropVec x := rfl

theorem dropDiffeo_inv_apply (x : R3) : dropDiffeo.invFun x = dropVecInv x := rfl

/-- The parametrisation of the counterexample's surface. -/
theorem param_dropDiffeo (θ φ : ℝ) :
    Work.Smooth.Morse.param dropDiffeo (θ, φ) = dropVec (Work.Core.torusMap θ φ) := rfl

/-! ## The numbers of the configuration -/

/-- The radius of the box. -/
def dropS : ℝ := 7/5

/-- The centre of the box. -/
def dropC : R3 := 0

/-- The coordinate permutation: `x` (coordinate `0`) and `z` (coordinate `2`) are interchanged, so
that the box sides `boxSide 0 · s = s`, `boxSide 1 · s`, `boxSide 2 · s` sit on `z`, `y`, `x`. -/
def dropCyc : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- The offset of the cutting plane: the plane is `{x = 0}`. -/
def dropU : ℝ := 0

end

end Work.BoxShrink.PinchOff.RefuteDrop
