import Mathlib
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The complex and the real direct-sum splitting agree on the real part

`Work.Whitney.sumFibreC k₁ k₂` and `Work.Whitney.sumFibreR k₁ k₂` are, by definition, the *same*
coordinate shuffle `EuclideanSpace.finAddEquivProd.symm` (only the coefficient field differs).  The
shuffle acts on the *labels* `Fin (k₁ + k₂) ≅ Fin k₁ ⊕ Fin k₂` of the coordinates and is therefore
insensitive to the field: it commutes with the inclusion `Work.Thom.cxOfReal` of `ℝ^k` into `ℂ^k` as
the real part.  That is the statement of this file.

The computation is reduced to the coordinate formulae for the shuffle, recorded below as the local
lemmas `finAddEquivProd_symm_ofLp_castAdd` / `finAddEquivProd_symm_ofLp_natAdd` (the `inl`/`inr`
coordinates of the shuffle are those of the two summands).  The same coordinate formulae in the
`finSumFinEquiv` form are `Work.Thom.finAddEquivProd_symm_apply_inl` /
`Work.Thom.finAddEquivProd_symm_apply_inr`; we state them in the `Fin.castAdd` / `Fin.natAdd` form
because that is what `Fin.addCases` produces when splitting an index of `Fin (k₁ + k₂)`.

This is the coordinate lemma underlying `Work.Whitney.complexificationCore_whitneySumR`
(via `Work.Whitney.sumFibreC_cxRePart`).
-/

namespace Work.Whitney

noncomputable section

/-- Coordinate formula for the inclusion `cxOfReal` of the real part: on the `i`-th coordinate it is
the embedding `ℝ → ℂ`. -/
private lemma cxOfReal_ofLp_apply {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    (Work.Thom.cxOfReal u).ofLp i = ((u.ofLp i : ℝ) : ℂ) := rfl

/-- First coordinate of `EuclideanSpace.finAddEquivProd`: the first `n` coordinates of
`x : 𝕜^{n+m}`. -/
private lemma finAddEquivProd_fst_ofLp {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (x : EuclideanSpace 𝕜 (Fin (n + m))) (i : Fin n) :
    (EuclideanSpace.finAddEquivProd x).1.ofLp i = x.ofLp (Fin.castAdd m i) := by
  simp only [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  simp

/-- Second coordinate of `EuclideanSpace.finAddEquivProd`: the last `m` coordinates of
`x : 𝕜^{n+m}`. -/
private lemma finAddEquivProd_snd_ofLp {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (x : EuclideanSpace 𝕜 (Fin (n + m))) (j : Fin m) :
    (EuclideanSpace.finAddEquivProd x).2.ofLp j = x.ofLp (Fin.natAdd n j) := by
  simp only [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  simp

/-- The coordinate shuffle `EuclideanSpace.finAddEquivProd.symm`, on the coordinates of the first
summand. -/
private lemma finAddEquivProd_symm_ofLp_castAdd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (a : EuclideanSpace 𝕜 (Fin n)) (b : EuclideanSpace 𝕜 (Fin m)) (i : Fin n) :
    (EuclideanSpace.finAddEquivProd.symm (a, b)).ofLp (Fin.castAdd m i) = a.ofLp i := by
  have h := finAddEquivProd_fst_ofLp (𝕜 := 𝕜)
    (x := EuclideanSpace.finAddEquivProd.symm (a, b)) i
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The coordinate shuffle `EuclideanSpace.finAddEquivProd.symm`, on the coordinates of the second
summand. -/
private lemma finAddEquivProd_symm_ofLp_natAdd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (a : EuclideanSpace 𝕜 (Fin n)) (b : EuclideanSpace 𝕜 (Fin m)) (j : Fin m) :
    (EuclideanSpace.finAddEquivProd.symm (a, b)).ofLp (Fin.natAdd n j) = b.ofLp j := by
  have h := finAddEquivProd_snd_ofLp (𝕜 := 𝕜)
    (x := EuclideanSpace.finAddEquivProd.symm (a, b)) j
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The complex splitting and the real splitting agree on the real part**: the coordinate shuffle
is insensitive to the coefficient field, so `sumFibreC` commutes with `cxOfReal`. -/
theorem sumFibreC_cxOfReal (k₁ k₂ : ℕ)
    (u : EuclideanSpace ℝ (Fin k₁)) (v : EuclideanSpace ℝ (Fin k₂)) :
    Work.Whitney.sumFibreC k₁ k₂ (Work.Thom.cxOfReal u, Work.Thom.cxOfReal v) =
      Work.Thom.cxOfReal (Work.Whitney.sumFibreR k₁ k₂ (u, v)) := by
  simp only [Work.Whitney.sumFibreC, Work.Whitney.sumFibreR]
  apply PiLp.ext
  intro i
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
  · simp only [cxOfReal_ofLp_apply, finAddEquivProd_symm_ofLp_castAdd]
  · simp only [cxOfReal_ofLp_apply, finAddEquivProd_symm_ofLp_natAdd]

end

end Work.Whitney
