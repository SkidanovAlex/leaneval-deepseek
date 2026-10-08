import Mathlib
import Submission.Work.Hering.GL32.AppIXM4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: the equivariance of the map `theta : W → M₄`

`theta f = Σ_p f p • ThetaF p` where `ThetaF p` is the trace-zero matrix of the rank-one map
`x ↦ det(a,b,x) • (a+b)` attached to a pair `p = {a,b}`.  Conjugation by `g : GL(3,2)` acts on
`M₄` and the permutation action `actW g` on `W` corresponds to it:

`theta (actW g f) = conjMat g (theta f)`.

The proof is the basis case `ThetaF (pairPerm g p) = conjMat g (ThetaF p)`, which follows from
`endoOf (g a) (g b) = g ∘ endoOf a b ∘ g⁻¹` (`det3_mul`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Hering.GL32

/-! ## Linearity of `conjMat` -/

lemma conjMat_zero (g : GL32) : conjMat g 0 = 0 := by simp [conjMat]

lemma conjMat_add (g : GL32) (A B : Mat3) : conjMat g (A + B) = conjMat g A + conjMat g B := by
  simp only [conjMat, Matrix.mul_add, Matrix.add_mul]

lemma conjMat_smul (g : GL32) (c : ZMod 2) (A : Mat3) : conjMat g (c • A) = c • conjMat g A := by
  simp only [conjMat, Matrix.smul_mul, Matrix.mul_smul]

lemma conjMat_sum_smul (g : GL32) {ι : Type*} (s : Finset ι) (c : ι → ZMod 2) (F : ι → Mat3) :
    conjMat g (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • conjMat g (F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [conjMat_zero]
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, conjMat_add, conjMat_smul, ih]

/-! ## The basis case -/

/-- `endoOf (g a) (g b) = g ∘ endoOf a b ∘ g⁻¹`. -/
lemma endoOf_comp (g : GL32) (a b : F2v) :
    endoOf (g a) (g b) =
      ((g : F2v →ₗ[ZMod 2] F2v) * (endoOf a b)) * ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v) := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, Module.End.mul_apply, endoOf_apply, endoOf_apply, map_smul, map_add]
  congr 1
  have h := det3_mul g a b (((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v) x)
  rwa [show g (((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v) x) = x from
        LinearEquiv.apply_symm_apply (g : F2v ≃ₗ[ZMod 2] F2v) x] at h

lemma ThetaFun_mul (g : GL32) (a b : F2v) :
    ThetaFun (g a) (g b) = conjMat g (ThetaFun a b) := by
  show LinearMap.toMatrix' (endoOf (g a) (g b)) = conjMat g (LinearMap.toMatrix' (endoOf a b))
  rw [endoOf_comp g a b, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, conjMat]

/-- Conjugation equivariance of `ThetaF` on pairs. -/
lemma ThetaF_pairPerm (g : GL32) (p : Pair) :
    ((ThetaF (pairPerm g p) : M4) : Mat3) = conjMat g ((ThetaF p : M4) : Mat3) := by
  obtain ⟨s, hs⟩ := p
  induction s using Sym2.ind with
  | h a b =>
      have h1 : (pairPerm g ⟨Sym2.mk a b, hs⟩).1 = Sym2.mk (ptPerm g a) (ptPerm g b) := by
        show Sym2.map (ptPerm g) (Sym2.mk a b) = _
        rw [Sym2.map_mk]
      rw [show pairPerm g ⟨Sym2.mk a b, hs⟩ =
            ⟨Sym2.mk (ptPerm g a) (ptPerm g b),
              by rw [← h1]; exact (pairPerm g ⟨Sym2.mk a b, hs⟩).2⟩
          from Subtype.ext h1]
      show ThetaFun (ptPerm g a).1 (ptPerm g b).1 = conjMat g (ThetaFun a.1 b.1)
      exact ThetaFun_mul g a.1 b.1

/-- `theta`, viewed as a map into all `3 × 3` matrices through the inclusion of `M₄`. -/
theorem thetaMat_actW (g : GL32) (f : W) :
    (M4.subtype.comp theta) (actW g f) = conjMat g ((M4.subtype.comp theta) f) := by
  conv_lhs => rw [eq_sum_smul_single f]
  conv_rhs => rw [eq_sum_smul_single f]
  simp only [map_sum, map_smul, actW_single, LinearMap.comp_apply, theta_single,
    Submodule.subtype_apply]
  rw [conjMat_sum_smul]
  exact Finset.sum_congr rfl (fun p _ => by rw [ThetaF_pairPerm g p])

/-- **Equivariance of `theta`**: the permutation action on `W` corresponds to conjugation
on the trace-zero matrices `M₄`. -/
theorem theta_actW (g : GL32) (f : W) :
    ((theta (actW g f) : M4) : Mat3) = conjMat g ((theta f : M4) : Mat3) :=
  thetaMat_actW g f

end Work.Hering.GL32
