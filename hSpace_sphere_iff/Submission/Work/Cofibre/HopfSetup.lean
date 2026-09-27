/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Set-up for the Hopf construction

Given a continuous multiplication `μ : S^d × S^d → S^d` with a unit (an `HSpace` structure on
`S^d`) the **Hopf construction** produces a continuous map

`μ̂ : S^{2d+1} = S^d * S^d ⟶ Σ S^d = S^{d+1}`

of Hopf invariant `1`.  Concretely, on the join `S^d * S^d`, written in coordinates
`(x, s, y)` with `s ∈ [0,1]`,

`μ̂(x, s, y) = (√(4s(1-s)) · μ(x,y), 2s - 1) ∈ ℝ^{d+1} ⊕ ℝ`,

which is well defined because at `s = 0` and `s = 1` the first coordinate vanishes.  Dropping the
join coordinate (`‖u‖² = 1 - s`, `‖v‖² = s`) this is

`μ̂(u, v) = (2 ‖u‖ ‖v‖ · μ(u/‖u‖, v/‖v‖), ‖v‖² - ‖u‖²)`,

a point of the `ℓ²`-sphere of `ℝ^{d+1} ⊕ ℝ`, since `4‖u‖²‖v‖² + (‖v‖²-‖u‖²)² = (‖u‖²+‖v‖²)² = 1`
on the unit sphere of `ℝ^{d+1} ⊕ ℝ^{d+1}`.

This file contains the *definitions*: the two linear isometry equivalences splitting the source and
the target euclidean spaces as `ℓ²`-products, the normalisation `sphVec` of a vector to a point of
the unit sphere (with an arbitrary junk value at the origin), and the raw formula `hopfRaw`.  The
two mathematical properties — that `hopfRaw` lands in the unit sphere and that it is continuous —
are proved in the companion files.
-/
import Mathlib
import Submission.Work.Sphere.Basic
import Submission.Work.Cofibre.Basic

open scoped Topology

open Submission.Sphere

namespace Submission.Cofibre

noncomputable section

/-- The euclidean space `ℝ^{d+1}`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- `ℝ^{2(d+1)}`, identified with the `ℓ²`-product `ℝ^{d+1} × ℝ^{d+1}`.  Both sides are real inner
product spaces of dimension `2(d+1)`, so the identification is an isometry. -/
def euclideanSplitSrc (d : ℕ) :
    EuclideanSpace ℝ (Fin (2 * (d + 1))) ≃ₗᵢ[ℝ] WithLp 2 (Euc d × Euc d) := by
  have hdim : Module.finrank ℝ (WithLp 2 (Euc d × Euc d)) = 2 * (d + 1) := by
    rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (Euc d × Euc d)), Module.finrank_prod,
      finrank_euclideanSpace_fin]
    ring
  exact (((stdOrthonormalBasis ℝ (WithLp 2 (Euc d × Euc d))).reindex
    (finCongr hdim)).repr).symm

/-- `ℝ^{d+2}`, identified with the `ℓ²`-product `ℝ^{d+1} × ℝ`. -/
def euclideanSplitTgt (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 2)) ≃ₗᵢ[ℝ] WithLp 2 (Euc d × ℝ) := by
  have hdim : Module.finrank ℝ (WithLp 2 (Euc d × ℝ)) = d + 2 := by
    rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (Euc d × ℝ)), Module.finrank_prod,
      finrank_euclideanSpace_fin, Module.finrank_self]
  exact (((stdOrthonormalBasis ℝ (WithLp 2 (Euc d × ℝ))).reindex
    (finCongr hdim)).repr).symm

/-- The normalisation `v ↦ ‖v‖⁻¹ • v` of a vector.  At `v = 0` this is `0`, which is not a unit
vector; `sphVec` supplies a junk value there. -/
def unitVec (d : ℕ) (v : Euc d) : Euc d := ‖v‖⁻¹ • v

lemma norm_unitVec (d : ℕ) {v : Euc d} (hv : v ≠ 0) : ‖unitVec d v‖ = 1 := by
  rw [unitVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- A vector, regarded as a point of the unit sphere: normalise it, with the fixed junk value
`pole d` at the origin.  The choice at the origin is irrelevant for the Hopf construction, since
the formula multiplies the resulting sphere point by `‖v‖` (times something bounded). -/
def sphVec (d : ℕ) (v : Euc d) : ↥(Metric.sphere (0 : Euc d) 1) :=
  if hv : v = 0 then ⟨pole d, pole_mem_sphere d⟩
  else ⟨unitVec d v, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_unitVec d hv⟩

/-- The sphere point `μ(x, y)`, after normalising the two arguments. -/
def muSph (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    (x : WithLp 2 (Euc d × Euc d)) : ↥(Metric.sphere (0 : Euc d) 1) :=
  μ (sphVec d x.fst, sphVec d x.snd)

/-- The first (`ℝ^{d+1}`-valued) coordinate of the Hopf construction. -/
def hopfFst (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    (x : WithLp 2 (Euc d × Euc d)) : Euc d :=
  (2 * ‖x.fst‖ * ‖x.snd‖) • (muSph d μ x : Euc d)

/-- The second (`ℝ`-valued) coordinate of the Hopf construction. -/
def hopfSnd (d : ℕ) (x : WithLp 2 (Euc d × Euc d)) : ℝ := ‖x.snd‖ ^ 2 - ‖x.fst‖ ^ 2

/-- **The Hopf construction**, as a raw formula on `ℝ^{d+1} ⊕ ℝ^{d+1}` — on the unit sphere this
lands on the unit sphere of `ℝ^{d+1} ⊕ ℝ` (see `norm_hopfRaw`), and it is continuous
(see `continuous_hopfRaw`). -/
def hopfRaw (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    (x : WithLp 2 (Euc d × Euc d)) : WithLp 2 (Euc d × ℝ) :=
  WithLp.toLp 2 (hopfFst d μ x, hopfSnd d x)

/-- The underlying vector of `μSph` has norm one: `μ` takes values in the unit sphere. -/
lemma norm_muSph (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    (x : WithLp 2 (Euc d × Euc d)) : ‖(muSph d μ x : Euc d)‖ = 1 :=
  by
    have h := Metric.mem_sphere.mp (muSph d μ x).2
    rwa [dist_eq_norm, sub_zero] at h

/-- On the unit sphere of the split source, the Hopf construction lands on the unit sphere of the
split target. -/
theorem norm_hopfRaw (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    {x : WithLp 2 (Euc d × Euc d)} (hx : ‖x‖ = 1) : ‖hopfRaw d μ x‖ = 1 := by
  have hsplit : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 x
    rw [hx] at h
    norm_num at h
    linarith
  have h1 : ‖hopfFst d μ x‖ = 2 * ‖x.fst‖ * ‖x.snd‖ := by
    rw [hopfFst, norm_smul, norm_muSph d μ x, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hnorm : ‖hopfRaw d μ x‖ ^ 2 = 1 := by
    rw [hopfRaw, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, h1, hopfSnd, Real.norm_eq_abs, sq_abs]
    nlinarith [hsplit]
  nlinarith [norm_nonneg (hopfRaw d μ x)]

/-- On the whole disk, the raw Hopf-construction formula is *radial*: its norm is the square of
the norm of the argument.  In particular it maps the closed disk of radius `1` into the cone on the
target sphere, with the boundary going to the boundary. -/
theorem norm_hopfRaw_general (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    (x : WithLp 2 (Euc d × Euc d)) : ‖hopfRaw d μ x‖ = ‖x‖ ^ 2 := by
  have h1 : ‖hopfFst d μ x‖ = 2 * ‖x.fst‖ * ‖x.snd‖ := by
    rw [hopfFst, norm_smul, norm_muSph d μ x, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hsplit : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 x
  have hnorm : ‖hopfRaw d μ x‖ ^ 2 = (‖x‖ ^ 2) ^ 2 := by
    rw [hopfRaw, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, h1, hopfSnd, Real.norm_eq_abs, sq_abs]
    nlinarith [hsplit, sq_nonneg ‖x.fst‖, sq_nonneg ‖x.snd‖]
  nlinarith [norm_nonneg (hopfRaw d μ x), norm_nonneg x]

/-- At the "south" degenerate locus `x.snd = 0` the Hopf construction is the point `(0,-1)`. -/
theorem hopfRaw_snd_zero (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    {x : WithLp 2 (Euc d × Euc d)} (hx : x.snd = 0) (h1 : ‖x.fst‖ = 1) :
    hopfRaw d μ x = WithLp.toLp 2 ((0 : Euc d), (-1 : ℝ)) := by
  have hf : hopfFst d μ x = 0 := by
    rw [hopfFst, hx, norm_zero]
    simp
  have hs : hopfSnd d x = -1 := by
    rw [hopfSnd, hx, norm_zero, h1]; norm_num
  rw [hopfRaw, hf, hs]

/-- At the "north" degenerate locus `x.fst = 0` the Hopf construction is the point `(0,1)`. -/
theorem hopfRaw_fst_zero (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d))
    {x : WithLp 2 (Euc d × Euc d)} (hx : x.fst = 0) (h1 : ‖x.snd‖ = 1) :
    hopfRaw d μ x = WithLp.toLp 2 ((0 : Euc d), (1 : ℝ)) := by
  have hf : hopfFst d μ x = 0 := by
    rw [hopfFst, hx, norm_zero]
    simp
  have hs : hopfSnd d x = 1 := by
    rw [hopfSnd, hx, norm_zero, h1]; norm_num
  rw [hopfRaw, hf, hs]

end

end Submission.Cofibre
