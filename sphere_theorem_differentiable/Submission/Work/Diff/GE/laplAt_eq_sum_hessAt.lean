import Mathlib
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Δu` is the trace of the Hessian in any orthonormal frame

The frozen interface fixes the Laplacian at a point `x` by choosing a `Classical.epsilon` frame:
`laplAt g u x = ∑ i, hessAt g u x (onFrame g x i) (onFrame g x i)`.  This file proves that the
expression is *frame independent*: for **any** `g`-orthonormal frame `e` of `TₓM` we have

`laplAt g u x = ∑ i, hessAt g u x (e i) (e i)`,

as soon as `hessAt g u x` is symmetric (`hsym`).  The point is that the definition of `hessAt`
is manifestly linear in its *first* argument, so symmetry makes it a symmetric bilinear form, and
the trace of a symmetric bilinear form does not see the orthonormal frame.

The proof of the frame independence is the standard one, phrased through the trace of the
`ℝ`-linear map `T u = ∑ i, A u (e i) • e i` representing the form `A = hessAt g u x` via the
inner product (`LinearMap.trace_eq_sum_inner`): the trace is a function of the operator alone.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Diff

namespace Work.Diff.GE

section Trace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Frame independence of the trace of a symmetric bilinear form.**

Let `A : V → V → ℝ` be linear in its first argument (`hadd`, `hsmul`) and symmetric (`hsym`).
Then for any two orthonormal frames `e`, `f` of the finite dimensional real inner product space
`V`, indexed by `Fin (finrank ℝ V)`, the sums of the diagonal values agree.  (When
`finrank ℝ V = 0` the index type is empty and both sums vanish.) -/
theorem sum_bilin_eq_of_orthonormal (A : V → V → ℝ)
    (hadd : ∀ u₁ u₂ w : V, A (u₁ + u₂) w = A u₁ w + A u₂ w)
    (hsmul : ∀ (a : ℝ) (u w : V), A (a • u) w = a * A u w)
    (hsym : ∀ u w : V, A u w = A w u)
    (e f : Fin (Module.finrank ℝ V) → V) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    ∑ i, A (e i) (e i) = ∑ i, A (f i) (f i) := by
  classical
  -- linearity in the second argument, from symmetry and linearity in the first
  have hadd₂ : ∀ u w₁ w₂ : V, A u (w₁ + w₂) = A u w₁ + A u w₂ := by
    intro u w₁ w₂
    rw [hsym u (w₁ + w₂), hadd w₁ w₂ u, hsym w₁ u, hsym w₂ u]
  have hsmul₂ : ∀ (a : ℝ) (u w : V), A u (a • w) = a * A u w := by
    intro a u w
    rw [hsym u (a • w), hsmul a w u, hsym w u]
  -- `A` as a bundled bilinear form
  let φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun u => { toFun := fun w => A u w
                          map_add' := fun w₁ w₂ => hadd₂ u w₁ w₂
                          map_smul' := fun a w => hsmul₂ a u w }
      map_add' := fun u₁ u₂ => by ext w; exact hadd u₁ u₂ w
      map_smul' := fun a u => by ext w; exact hsmul a u w }
  have hφ : ∀ u w : V, φ u w = A u w := fun u w => rfl
  by_cases hn : 0 < Module.finrank ℝ V
  · haveI : Nonempty (Fin (Module.finrank ℝ V)) := Fin.pos_iff_nonempty.mp hn
    have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Module.finrank ℝ V := by
      rw [Fintype.card_fin]
    -- both frames are orthonormal bases
    let be : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V :=
      (basisOfOrthonormalOfCardEqFinrank he hcard).toOrthonormalBasis (by
        rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact he)
    let bf : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V :=
      (basisOfOrthonormalOfCardEqFinrank hf hcard).toOrthonormalBasis (by
        rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hf)
    have hbe : (be : Fin (Module.finrank ℝ V) → V) = e := by simp [be]
    have hbf : (bf : Fin (Module.finrank ℝ V) → V) = f := by simp [bf]
    -- expansion of a vector in the frame `e`
    have hexp : ∀ w : V, ∑ i, inner ℝ (e i) w • e i = w := by
      intro w
      simpa only [hbe] using OrthonormalBasis.sum_repr' be w
    -- the operator representing `A`
    let T : V →ₗ[ℝ] V :=
      { toFun := fun u => ∑ i, φ u (e i) • e i
        map_add' := fun u₁ u₂ => by
          show (∑ i, φ (u₁ + u₂) (e i) • e i) =
            (∑ i, φ u₁ (e i) • e i) + ∑ i, φ u₂ (e i) • e i
          simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun a u => by
          show (∑ i, φ (a • u) (e i) • e i) = a • ∑ i, φ u (e i) • e i
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul] }
    have hTu : ∀ u : V, T u = ∑ i, φ u (e i) • e i := fun u => rfl
    -- `T` represents `A`: `⟪T u, w⟫ = A u w`
    have hT : ∀ u w : V, inner ℝ (T u) w = A u w := by
      intro u w
      rw [hTu u, sum_inner]
      simp only [real_inner_smul_left]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (φ u (e i)) (inner ℝ (e i) w))]
      have hstep : ∑ i, inner ℝ (e i) w * (φ u) (e i) =
          φ u (∑ i, inner ℝ (e i) w • e i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul]
      rw [hstep, hexp, hφ]
    -- the trace in the two frames
    have htr : ∑ i, A (e i) (e i) = T.trace ℝ V := by
      rw [LinearMap.trace_eq_sum_inner T be]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hbi : be i = e i := congrFun hbe i
      rw [hbi, real_inner_comm, hT]
    have htr' : ∑ i, A (f i) (f i) = T.trace ℝ V := by
      rw [LinearMap.trace_eq_sum_inner T bf]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hbi : bf i = f i := congrFun hbf i
      rw [hbi, real_inner_comm, hT]
    exact htr.trans htr'.symm
  · -- `finrank ℝ V = 0`: the index type is empty and both sums vanish
    have h0 : Module.finrank ℝ V = 0 := Nat.eq_zero_of_not_pos hn
    haveI : IsEmpty (Fin (Module.finrank ℝ V)) := by rw [h0]; exact Fin.isEmpty
    simp

end Trace

/-- **`Δu` is the sum of the Hessian in any orthonormal frame.**

`laplAt g u x` is defined through the `Classical.epsilon`-chosen frame `onFrame g x`; this lemma
shows that the same value is obtained from an arbitrary `g`-orthonormal frame `e` of `TₓM`, the only
extra input being the symmetry of `hessAt g u x` in its two arguments (`hsym`). -/
theorem laplAt_eq_sum_hessAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (u : M → ℝ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e)
    (hsym : ∀ v w : TangentSpace I x,
      Submission.Diff.hessAt g u x v w = Submission.Diff.hessAt g u x w v) :
    Submission.Diff.laplAt g u x = ∑ i, Submission.Diff.hessAt g u x (e i) (e i) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- `hessAt g u x` is linear in its first argument, by definition ...
  have hadd : ∀ v₁ v₂ w : TangentSpace I x,
      hessAt g u x (v₁ + v₂) w = hessAt g u x v₁ w + hessAt g u x v₂ w := by
    intro v₁ v₂ w
    simp only [hessAt, map_add]
    ring
  have hsmul : ∀ (a : ℝ) (v w : TangentSpace I x),
      hessAt g u x (a • v) w = a * hessAt g u x v w := by
    intro a v w
    simp only [hessAt, map_smul, smul_eq_mul]
    ring
  -- ... so with `hsym` it is a symmetric bilinear form, and its trace is frame independent.
  have hON : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact isONFrame_onFrame g x i j
  have heON : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact he i j
  show ∑ i, hessAt g u x (onFrame g x i) (onFrame g x i)
      = ∑ i, hessAt g u x (e i) (e i)
  exact sum_bilin_eq_of_orthonormal (V := TangentSpace I x) (fun v w => hessAt g u x v w)
    hadd hsmul hsym (onFrame g x) e hON heON

end Work.Diff.GE
