import Mathlib
import Submission.Work.Hering.GL32.AppIXPair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: the `M₄`-component of the permutation module

`M₄` is the space of trace-zero `3 × 3` matrices over `F₂`, a `GL(3,2)`-module of dimension `8`
under conjugation (simplicity is `Work.Hering.GL32.rad_irreducible`).  We construct the natural
map `theta : W → M₄` (`f ↦ Σ f(p) • (x ↦ det(a,b,x) • (a+b))`) and its equivariance.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Hering.GL32

/-- `3 × 3` matrices over `F₂`. -/
abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

/-- The trace as a linear map. -/
noncomputable def traceLin : Mat3 →ₗ[ZMod 2] ZMod 2 :=
  Matrix.traceLinearMap (Fin 3) (ZMod 2) (ZMod 2)

lemma traceLin_apply (A : Mat3) : traceLin A = A.trace := rfl

/-- The space of trace-zero matrices, the `8`-dimensional module `M₄`. -/
noncomputable def M4 : Submodule (ZMod 2) Mat3 := LinearMap.ker traceLin

lemma mem_M4_iff (A : Mat3) : A ∈ M4 ↔ A.trace = 0 := Iff.rfl

/-- The linear functional `x ↦ det(a,b,x)` for arbitrary vectors `a b`. -/
noncomputable def det3LinV (a b : F2v) : Module.Dual (ZMod 2) F2v where
  toFun x := det3 a b x
  map_add' x y := by
    simp only [det3, Matrix.det_fin_three, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Pi.add_apply]
    ring
  map_smul' c x := by
    simp only [det3, Matrix.det_fin_three, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma det3LinV_apply (a b x : F2v) : det3LinV a b x = det3 a b x := rfl

lemma det3LinV_swap (a b : F2v) : det3LinV b a = det3LinV a b := by
  apply LinearMap.ext
  intro x
  show det3 b a x = det3 a b x
  exact (det3_swap b a x).symm

/-- The trace-zero endomorphism `x ↦ det(a,b,x) • (a+b)` attached to an ordered pair. -/
noncomputable def endoOf (a b : F2v) : F2v →ₗ[ZMod 2] F2v :=
  (det3LinV a b).smulRight (a + b)

lemma endoOf_apply (a b x : F2v) : endoOf a b x = det3 a b x • (a + b) := by
  rw [endoOf, LinearMap.smulRight_apply]
  rfl

/-- The matrix of `endoOf a b`. -/
noncomputable def ThetaFun (a b : F2v) : Mat3 := LinearMap.toMatrix' (endoOf a b)

lemma ThetaFun_swap (a b : F2v) : ThetaFun b a = ThetaFun a b := by
  show LinearMap.toMatrix' (endoOf b a) = LinearMap.toMatrix' (endoOf a b)
  congr 1
  apply LinearMap.ext
  intro x
  rw [endoOf_apply, endoOf_apply]
  rw [show det3 b a x = det3 a b x from (det3_swap b a x).symm, add_comm b a]

/-- The trace of `endoOf a b` is `0`. -/
lemma trace_ThetaFun (a b : F2v) : (ThetaFun a b).trace = 0 := by
  revert a b
  decide

/-- The trace-zero matrix attached to a pair. -/
noncomputable def ThetaF : Pair → M4 :=
  fun p => Sym2.lift
    ⟨fun a b : Pt => ⟨ThetaFun a.1 b.1, by rw [mem_M4_iff]; exact trace_ThetaFun a.1 b.1⟩,
      fun a b => Subtype.ext (ThetaFun_swap a.1 b.1).symm⟩ p.1

/-- The natural map `W → M₄`. -/
noncomputable def theta : W →ₗ[ZMod 2] M4 where
  toFun f := ∑ p : Pair, f p • ThetaF p
  map_add' f h := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

lemma theta_single (p : Pair) : theta (Pi.single p (1 : ZMod 2)) = ThetaF p := by
  simp [theta]

lemma ThetaF_coe (p : Pair) : ((ThetaF p : M4) : Mat3).trace = 0 := (ThetaF p).2

lemma theta_coe_trace (f : W) : ((theta f : M4) : Mat3).trace = 0 := (theta f).2

/-- Conjugation of matrices by `g`. -/
noncomputable def conjMat (g : GL32) (A : Mat3) : Mat3 :=
  LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v) * A *
    LinearMap.toMatrix' ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v)

lemma conjMat_trace (g : GL32) (A : Mat3) : (conjMat g A).trace = A.trace := by
  rw [conjMat, Matrix.trace_mul_cycle]
  rw [show LinearMap.toMatrix' ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v) *
      LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v) = 1 from by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    ext v
    simp]
  rw [Matrix.one_mul]

/-- The combined map `W → k × V × V* × M₄`. -/
noncomputable def combinedMap :
    W →ₗ[ZMod 2] (ZMod 2 × F2v × Module.Dual (ZMod 2) F2v × M4) :=
  aug.prod (phi.prod (psi.prod theta))

/-- `K₄`, the common kernel of the four natural maps. -/
noncomputable def K4 : Submodule (ZMod 2) W := LinearMap.ker combinedMap

end Work.Hering.GL32
