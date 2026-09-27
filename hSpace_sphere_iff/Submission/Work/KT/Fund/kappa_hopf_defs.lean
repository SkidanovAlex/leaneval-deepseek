import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_indep
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.hopf_trace_det
import Submission.Work.KT.Fund.twoByTwo_idem_of_trace_det

/-!
# `Work.KT.Fund.kappa_hopf_defs` — setup for `kappa_hopf`

The target `Work.KT.Fund.kappa_hopf` states

  `κ(z) = snd^*(cls hopfIdem)`   in `K0 C(X × S², ℂ)`,

where `κ(z)` is the clutched class of the coordinate unit `z` over the circle
(`Work.KT.Fund.kappa X 1 (zUnitMat X)`) and `snd^*(cls hopfIdem)` is the pull-back of the Hopf
line bundle (`Work.KT.Fund.gamma X`).

Both sides are the class of a rank-one idempotent over `X × S²`; after transporting along the
two-disc decomposition `glueEquiv` they become `2 × 2` matrices over the fibre product
`pullAlg2 X`, glued from a pair of disc matrices.  The clutched idempotent is built from the
orthogonal projection onto the graph of a lift `F₀` of `z` (upper disc) and onto the reciprocal
graph of a lift `G₀ = star F₀` of `z⁻¹` (lower disc).  This file fixes

* the explicit lifts `F₀ = !![g]`, `G₀ = !![star g]` with `g = c/(1+s)`, `c` the disc
  coordinate and `s = √(1-‖c‖²)` the height;
* the abstract `1 × 1` formulas `graphProj_one`, `recipProj_one` for the orthogonal projections
  (`orthProj`/`graphProj` are defined through `Ring.inverse`, so the formulas are the only
  practical way to compute them) together with the function identities that instantiate them;
* a clean `Fin 2` copy `hopfMat` of the Hopf idempotent matrix, `hopfIdem_eq : hopfIdem = ⟨2, hopfMat⟩`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

/-! ## The abstract `1 × 1` formulas for `graphProj`/`recipProj` -/

/-- `graphProj` of a single-entry matrix, in closed form.  If `w` is a two-sided inverse of
`1 + (star f) f` then the projection onto the graph of `f` is
`[[w, w f̄],[f w, f w f̄]]`. -/
theorem graphProj_one {R : Type} [CommRing R] [StarRing R] (f w : R)
    (h1 : (1 + star f * f) * w = 1) (h2 : w * (1 + star f * f) = 1) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (graphProj R !![f]) =
      !![w, w * star f; f * w, f * w * star f] := by
  have hBB : (graphB R !![f]).conjTranspose * graphB R !![f] = !![1 + star f * f] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [graphB, Matrix.mul_apply]
  have hu1 : (!![1 + star f * f] : Matrix (Fin 1) (Fin 1) R) * !![w] = 1 := by
    ext i j; fin_cases i; fin_cases j
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h1
  have hu2 : (!![w] : Matrix (Fin 1) (Fin 1) R) * !![1 + star f * f] = 1 := by
    ext i j; fin_cases i; fin_cases j
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h2
  let u : (Matrix (Fin 1) (Fin 1) R)ˣ :=
    { val := !![1 + star f * f], inv := !![w], val_inv := hu1, inv_val := hu2 }
  have hinv : Ring.inverse ((graphB R !![f]).conjTranspose * graphB R !![f]) = !![w] := by
    rw [hBB, Ring.inverse_unit u]; rfl
  unfold graphProj orthProj
  rw [hinv]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  · show (graphB R (!![f]) * !![w] * (graphB R (!![f])).conjTranspose) (Sum.inl 0) (Sum.inl 0) = w
    simp [graphB, Matrix.mul_apply]
  · show (graphB R (!![f]) * !![w] * (graphB R (!![f])).conjTranspose) (Sum.inl 0) (Sum.inr 0) = w * star f
    simp [graphB, Matrix.mul_apply]
  · show (graphB R (!![f]) * !![w] * (graphB R (!![f])).conjTranspose) (Sum.inr 0) (Sum.inl 0) = f * w
    simp [graphB, Matrix.mul_apply]
  · show (graphB R (!![f]) * !![w] * (graphB R (!![f])).conjTranspose) (Sum.inr 0) (Sum.inr 0) = f * w * star f
    simp [graphB, Matrix.mul_apply]

/-- `recipProj` of a single-entry matrix, in closed form.  If `w` is a two-sided inverse of
`1 + (star g) g` then the projection onto the reciprocal graph of `g` is
`[[g w ḡ, g w],[w ḡ, w]]`. -/
theorem recipProj_one {R : Type} [CommRing R] [StarRing R] (g w : R)
    (h1 : (1 + star g * g) * w = 1) (h2 : w * (1 + star g * g) = 1) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (recipProj R !![g]) =
      !![g * w * star g, g * w; w * star g, w] := by
  have hBB : (recipB R !![g]).conjTranspose * recipB R !![g] = !![1 + star g * g] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [recipB, Matrix.mul_apply, add_comm]
  have hu1 : (!![1 + star g * g] : Matrix (Fin 1) (Fin 1) R) * !![w] = 1 := by
    ext i j; fin_cases i; fin_cases j
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h1
  have hu2 : (!![w] : Matrix (Fin 1) (Fin 1) R) * !![1 + star g * g] = 1 := by
    ext i j; fin_cases i; fin_cases j
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h2
  let u : (Matrix (Fin 1) (Fin 1) R)ˣ :=
    { val := !![1 + star g * g], inv := !![w], val_inv := hu1, inv_val := hu2 }
  have hinv : Ring.inverse ((recipB R !![g]).conjTranspose * recipB R !![g]) = !![w] := by
    rw [hBB, Ring.inverse_unit u]; rfl
  unfold recipProj orthProj
  rw [hinv]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  · show (recipB R (!![g]) * !![w] * (recipB R (!![g])).conjTranspose) (Sum.inl 0) (Sum.inl 0) = g * w * star g
    simp [recipB, Matrix.mul_apply]
  · show (recipB R (!![g]) * !![w] * (recipB R (!![g])).conjTranspose) (Sum.inl 0) (Sum.inr 0) = g * w
    simp [recipB, Matrix.mul_apply]
  · show (recipB R (!![g]) * !![w] * (recipB R (!![g])).conjTranspose) (Sum.inr 0) (Sum.inl 0) = w * star g
    simp [recipB, Matrix.mul_apply]
  · show (recipB R (!![g]) * !![w] * (recipB R (!![g])).conjTranspose) (Sum.inr 0) (Sum.inr 0) = w
    simp [recipB, Matrix.mul_apply]

/-! ## The explicit lifts over the disc -/

variable (X : Type) [TopologicalSpace X]

/-- The coordinate function `p ↦ (p.2 : ℂ)` on `X × D`. -/
def cCoord : C(X × Ball ℂ, ℂ) :=
  ⟨fun p => ((p.2 : Ball ℂ) : ℂ), by fun_prop⟩

/-- The height `p ↦ √(1 - ‖p.2‖²)`, complexified. -/
def cHeight : C(X × Ball ℂ, ℂ) :=
  ⟨fun p => (Real.sqrt (1 - ‖(((p.2 : Ball ℂ) : ℂ))‖ ^ 2) : ℂ), by fun_prop⟩

lemma one_add_cHeight_ne_zero (p : X × Ball ℂ) : (1 + cHeight X) p ≠ 0 := by
  rw [ContinuousMap.add_apply, ContinuousMap.one_apply, cHeight]
  change (1 : ℂ) + ↑(Real.sqrt (1 - ‖(((p.2 : Ball ℂ) : ℂ))‖ ^ 2)) ≠ 0
  rw [← Complex.ofReal_one, ← Complex.ofReal_add]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

/-- `1 + cHeight`, as a unit of `C(X × D, ℂ)`. -/
def hUnit : (C(X × Ball ℂ, ℂ))ˣ :=
  ((ContinuousMap.isUnit_iff_forall_ne_zero (1 + cHeight X)).mpr
    (one_add_cHeight_ne_zero X)).unit

/-- The continuous inverse of `1 + cHeight`. -/
def cHeightInv : C(X × Ball ℂ, ℂ) := ↑(hUnit X)⁻¹

lemma hUnit_val : (hUnit X : C(X × Ball ℂ, ℂ)) = 1 + cHeight X := IsUnit.unit_spec _

lemma hUnit_mul : (1 + cHeight X) * cHeightInv X = 1 := by
  have h := (hUnit X).val_inv
  rw [hUnit_val X] at h
  exact h

lemma hUnit_inv_mul : cHeightInv X * (1 + cHeight X) = 1 := by
  have h := (hUnit X).inv_val
  rw [hUnit_val X] at h
  exact h

/-- The constant function `1/2`. -/
def halfC : C(X × Ball ℂ, ℂ) := ⟨fun _ => (1/2 : ℂ), by fun_prop⟩

lemma two_mul_halfC : (2 : C(X × Ball ℂ, ℂ)) * halfC X = 1 := by
  ext p
  change (2 : ℂ) * (1 / 2 : ℂ) = 1
  norm_num

/-- The lift `g = c/(1+s)` of the coordinate `z` to the disc. -/
def gFun : C(X × Ball ℂ, ℂ) := cCoord X * cHeightInv X

/-- The lift of the coordinate `z` used on the upper disc. -/
def F0 : Matrix (Fin 1) (Fin 1) C(X × Ball ℂ, ℂ) := !![gFun X]

/-- The lift of `z⁻¹` used on the lower disc. -/
def G0 : Matrix (Fin 1) (Fin 1) C(X × Ball ℂ, ℂ) := !![star (gFun X)]

lemma star_cHeightInv : star (cHeightInv X) = cHeightInv X := by
  ext p
  have h : (1 + cHeight X) p * cHeightInv X p = 1 := by
    have hh := congrFun (congrArg DFunLike.coe (hUnit X).val_inv) p
    rwa [hUnit_val X] at hh
  have hval : cHeightInv X p = (((1 + cHeight X) p))⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [ContinuousMap.star_apply, hval]
  rw [ContinuousMap.add_apply, ContinuousMap.one_apply]
  simp [cHeight]

lemma star_cCoord_mul_cCoord : star (cCoord X) * cCoord X = 1 - cHeight X * cHeight X := by
  ext p
  simp only [ContinuousMap.star_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, cCoord, cHeight, ContinuousMap.coe_mk]
  have hnorm : ‖(((p.2 : Ball ℂ) : ℂ))‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2.2
  have h1 : star (((p.2 : Ball ℂ) : ℂ)) = (starRingEnd ℂ) (((p.2 : Ball ℂ) : ℂ)) := rfl
  rw [h1, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by
    nlinarith [hnorm, norm_nonneg (((p.2 : Ball ℂ) : ℂ))])]
  push_cast
  ring

lemma star_gFun : star (gFun X) = star (cCoord X) * cHeightInv X := by
  rw [gFun, star_mul, star_cHeightInv X, mul_comm]

lemma F0_gram : 1 + star (gFun X) * gFun X = 2 * cHeightInv X := by
  rw [star_gFun X, gFun]
  rw [show star (cCoord X) * cHeightInv X * (cCoord X * cHeightInv X)
      = (star (cCoord X) * cCoord X) * (cHeightInv X * cHeightInv X) from by ring]
  rw [star_cCoord_mul_cCoord X]
  rw [show (1 : C(X × Ball ℂ, ℂ)) - cHeight X * cHeight X
      = (1 - cHeight X) * (1 + cHeight X) from by ring]
  rw [show (1 - cHeight X) * (1 + cHeight X) * (cHeightInv X * cHeightInv X)
      = (1 - cHeight X) * cHeightInv X * ((1 + cHeight X) * cHeightInv X) from by ring]
  rw [hUnit_mul X, mul_one]
  calc (1 : C(X × Ball ℂ, ℂ)) + (1 - cHeight X) * cHeightInv X
      = (1 + cHeight X) * cHeightInv X + (1 - cHeight X) * cHeightInv X := by rw [hUnit_mul X]
    _ = 2 * cHeightInv X := by ring

/-! ## A clean `Fin 2` copy of the Hopf idempotent -/

/-- The Hopf idempotent matrix, with explicit `Fin 2` indices. -/
def hopfMat : Matrix (Fin 2) (Fin 2) C(S2, ℂ) :=
  (algebraMap ℂ C(S2, ℂ)) (1 / 2) •
    !![1 + coordC 3 2, coordC 3 0 - (algebraMap ℂ C(S2, ℂ)) Complex.I * coordC 3 1;
       coordC 3 0 + (algebraMap ℂ C(S2, ℂ)) Complex.I * coordC 3 1, 1 - coordC 3 2]

lemma hopfIdem_eq : hopfIdem = ⟨2, hopfMat⟩ := rfl

lemma hopfIdem_isIdem : hopfIdem.IsIdem :=
  twoByTwo_idem_of_trace_det hopfIdem.2 hopf_trace_det.1 hopf_trace_det.2

end

end Work.KT.Fund
