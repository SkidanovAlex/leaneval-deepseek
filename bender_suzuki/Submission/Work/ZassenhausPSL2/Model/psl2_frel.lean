import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSL2Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `f`-relation of the `PSL(2, 2ⁿ)` model: the Zassenhaus (Bruhat) relation

For `b ≠ 0` in a field `K` of characteristic two let `u(b) = !![1, b; 0, 1]` be the unipotent
element and `w = !![0, 1; -1, 0]` the Weyl element of `PSL(2, K)`.  This file proves the
matrix identity

`w · u(b) · w = d(b⁻¹) · u(b) · w · u(b⁻¹)`,   with `d(a) = diag(a, a⁻¹)`,

which in the projective group `PSL(2, K)` exhibits the element `m = d(b⁻¹) · u(b)` of the Borel
subgroup `B = Stab(⟨e₀⟩)` in the "`f`-relation" `w u(b) w = m w u(b⁻¹)` of the rank-one
`(B, N)`-pair with `f(b) = b⁻¹`.  This is the model datum `M1b` of the Zassenhaus/PSL2 core.

The proof is the elementary computation

`!![0,1;1,0] · !![1,b;0,1] · !![0,1;1,0] = !![1,0;b,1] = !![b⁻¹,1;0,b] · !![0,1;1,b⁻¹]`
-/

namespace Work.ZassenhausPSL2.Model

open Matrix

/-- **The elementary matrix identity behind the `f`-relation.**  In a field `K` of characteristic
two, for a unit `u` with `c = ↑u`,

`w · u(c) · w = (d(u⁻¹) · u(c)) · w · u(c⁻¹)`,

where `w = !![0,1;-1,0]`, `u(t) = !![1,t;0,1]` and `d(a) = !![a,0;0,a⁻¹]`, as elements of
`SL(2, K)`.  (Both sides equal `!![-1,0;c,-1]`; characteristic two makes `-c = c`.) -/
lemma weylSL_mul_transvectionSL_mul_weylSL {K : Type*} [Field K] [CharP K 2] (u : Kˣ) :
    Submission.PSL2.weylSL K * Commons.GroupTheory.SL2.transvectionSL K (u : K) *
        Submission.PSL2.weylSL K =
      (Submission.PSL2.diagSL u⁻¹ * Commons.GroupTheory.SL2.transvectionSL K (u : K)) *
        Submission.PSL2.weylSL K * Commons.GroupTheory.SL2.transvectionSL K ((u⁻¹ : Kˣ) : K) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Submission.PSL2.weylSL_coe,
    Submission.PSL2.transvectionSL_coe, Submission.PSL2.diagSL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

/-- **The `f`-relation of the `PSL(2, K)` model** (`K` of characteristic two), at the level of the
projective group: for `c ≠ 0`,

`w · u(c) · w = (d(c⁻¹) · u(c)) · w · u(c⁻¹)` in `PSL(2, K)`

with `w = weylPSL K`, `u = unipotentPSLHom K ∘ ofAdd` and `d = diagPSLHom K`.  Since `K` has
characteristic two the centre of `SL(2, K)` is trivial, so the `SL(2, K)` identity of
`weylSL_mul_transvectionSL_mul_weylSL` descends to the quotient. -/
lemma weylPSL_mul_unipotentPSLHom_mul_weylPSL {K : Type*} [Field K] [CharP K 2] (c : K)
    (hc : c ≠ 0) :
    Submission.PSL2.weylPSL K * Commons.GroupTheory.SL2.unipotentPSLHom K (Multiplicative.ofAdd c) *
        Submission.PSL2.weylPSL K =
      (Submission.PSL2.diagPSLHom K (Units.mk0 c hc)⁻¹ *
          Commons.GroupTheory.SL2.unipotentPSLHom K (Multiplicative.ofAdd c)) *
        Submission.PSL2.weylPSL K *
        Commons.GroupTheory.SL2.unipotentPSLHom K (Multiplicative.ofAdd c⁻¹) := by
  have h := weylSL_mul_transvectionSL_mul_weylSL (K := K) (Units.mk0 c hc)
  have h' := congrArg (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) h
  simp only [map_mul] at h'
  exact h'

/-- **The `f`-relation of the `PSL(2, 2ⁿ)` Bender pair**: for `b ≠ 0` there is an element
`m = d(b⁻¹) · u(b)` of the Borel subgroup `B = Stab(⟨e₀⟩) = U ⋊ T` with

`w · u(b) · w = m · w · u(b⁻¹)`.

This is the model datum `M1b` for the Zassenhaus/PSL2 core (`f(b) = b⁻¹` on the additive group of
the field, transported along `c ↦ u(c)`). -/
theorem psl2_frel (n : ℕ) (hn : 2 ≤ n) (b : GaloisField 2 n) (hb : b ≠ 0) :
    ∃ m ∈ (Submission.PSL2.pSL2BenderPair n hn).B,
      Submission.PSL2.weylPSL (GaloisField 2 n) *
          Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n) (Multiplicative.ofAdd b) *
          Submission.PSL2.weylPSL (GaloisField 2 n) =
        m * Submission.PSL2.weylPSL (GaloisField 2 n) *
          Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
            (Multiplicative.ofAdd b⁻¹) := by
  refine ⟨Submission.PSL2.diagPSLHom (GaloisField 2 n) (Units.mk0 b hb)⁻¹ *
      Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n) (Multiplicative.ofAdd b),
    ?_, ?_⟩
  · -- `d(b⁻¹)` is in the torus `T ≤ B` and `u(b)` in the unipotent subgroup `U ≤ B`.
    show _ ∈ MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (Submission.PSL2.pt0 (GaloisField 2 n))
    exact Subgroup.mul_mem _
      (Submission.PSL2.diag_range_le_stabilizer_pt0 (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
      (Submission.PSL2.unipotent_range_le_stabilizer_pt0 (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
  · exact weylPSL_mul_unipotentPSLHom_mul_weylPSL (K := GaloisField 2 n) b hb

end Work.ZassenhausPSL2.Model
