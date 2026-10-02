import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The coordinate reading of a nonzero normal fibre vector is nonzero

This file proves `Work.ThomBordism.nfRead_ne_zero`, the membership obligation that makes the
oriented fibre generator `Work.ThomBordism.nfGen` of `Submission/Work/ThomBordism/orientedFibreGen.lean`
*unconditional*.

`nfRead E ND x` reads a point of the fibre `ν_x` of the normal bundle in the σ-corrected orthonormal
frame `Gauss.gframe E ND (ND.D.indexAt x) x` of `ν_x` (`readFrame`), hence is a continuous map
`ν_x → ℝ^k`.  The claim is that it does not vanish on a *nonzero* fibre vector.  The mathematics is
exactly this: the frame spans `ν_x` (`span_orthFrame`; the corrected frame `gframe` spans the same
space as `orthFrame`, the gauge being diagonal with entries `±1`), and a vector of a subspace which
is orthogonal to a spanning family is zero.

The two ingredients are `Work.Tubular.span_orthFrame` (already proved in the tree, used through the
definitional identity `gframe = gauge • orthFrame`) and the orthogonality form
`Work.ThomBordism.readFrame_eq_zero_iff`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism

/-! ## Linear algebra: a vector of a subspace orthogonal to a spanning family is zero -/

/-- **A vector of a subspace which is orthogonal to a spanning family vanishes.** -/
theorem eq_zero_of_mem_span_of_inner_eq_zero {N k : ℕ} (f : Fin k → Work.Tubular.Euc N)
    (v : Work.Tubular.Euc N) (hmem : v ∈ Submodule.span ℝ (Set.range f))
    (horth : ∀ j, inner ℝ (f j) v = 0) : v = 0 := by
  have hspan : ∀ w ∈ Submodule.span ℝ (Set.range f), inner ℝ w v = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact horth j
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  exact inner_self_eq_zero.mp (hspan v hmem)

/-! ## The fibre of the normal bundle as a subspace of the normal space at `x` -/

/-- The fibre vector of a point of the fibre `nfSet E x` is a vector of the normal space at `x`. -/
theorem vec_mem_normalSpace_of_mem_nfSet {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {x : V.pt}
    (p : ↥(nfSet E x)) : Work.Tubular.NormalTotal.vec p.1 ∈ Work.Tubular.normalSpace E x := by
  have h := Work.Tubular.NormalTotal.vec_mem p.1
  have hx : Work.Tubular.NormalTotal.proj p.1 = x := p.2
  rwa [hx] at h

/-! ## The membership obligation -/

theorem nfRead_ne_zero {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    ∀ p ∈ nfPunct E x, nfRead E ND x p ≠ 0 := by
  intro p hp h
  have hmem : Work.Tubular.NormalTotal.vec p.1 ∈ Work.Tubular.normalSpace E x :=
    vec_mem_normalSpace_of_mem_nfSet E p
  have hg : ∀ j, inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j)
      (Work.Tubular.NormalTotal.vec p.1) = 0 := by
    have h' : readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
        (Work.Tubular.NormalTotal.vec p.1) = 0 := h
    exact (readFrame_eq_zero_iff _ _).mp h'
  have horth : ∀ j, inner ℝ (Work.Tubular.orthFrame E ND (ND.D.indexAt x) x j)
      (Work.Tubular.NormalTotal.vec p.1) = 0 := by
    intro j
    have hgj := hg j
    rw [Gauss.gframe_apply] at hgj
    have hc : (if (j : ℕ) = 0 then Gauss.sigma E ND (ND.D.indexAt x) x else 1) ≠ 0 := by
      by_cases hj : (j : ℕ) = 0
      · rw [if_pos hj]
        rcases Gauss.sigma_eq_one_or E ND (ND.D.indexAt x) x with hs | hs <;>
          rw [hs] <;> norm_num
      · rw [if_neg hj]
        norm_num
    rw [inner_smul_left] at hgj
    exact (mul_eq_zero.mp hgj).resolve_left (by simpa using hc)
  have hspan := Work.Tubular.span_orthFrame E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)
  have hzero : Work.Tubular.NormalTotal.vec p.1 = 0 :=
    eq_zero_of_mem_span_of_inner_eq_zero _ _ (by rw [hspan]; exact hmem) horth
  exact hp hzero

end Work.ThomBordism
