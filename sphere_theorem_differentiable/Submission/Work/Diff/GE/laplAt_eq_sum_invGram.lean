import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.hessAt_comm
import Submission.Work.Diff.GE.laplAt_eq_sum_hessAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Δu` is the contraction of the Hessian with the inverse Gram matrix

`laplAt g u x` is defined in the frozen interface as the sum `∑ i, hessAt g u x (eᵢ) (eᵢ)` over a
`Classical.epsilon`-chosen `g`-orthonormal frame `onFrame g x` of `TₓM`.  This file shows that the
same number is obtained from the Hessian in an *arbitrary* basis `e₁,…,eₙ` of `TₓM`, by contracting
the two Hessian slots with the inverse `Γ⁻¹` of the Gram matrix `Γᵢⱼ = g(eᵢ,eⱼ)`:

  `laplAt g u x = ∑ i, ∑ j, (Γ⁻¹) i j * hessAt g u x (eᵢ) (eⱼ)`.

There are three ingredients.

* `Work.Diff.GE.hessAt_comm` — the Hessian of a `C²` function is symmetric (`LCSmooth`).
* `Work.Diff.GE.laplAt_eq_sum_hessAt` — the Hessian trace is the same in every orthonormal frame.
* `Work.Diff.GE.sum_invGram_mul_eq_sum_orthonormal` (proved below, self-contained linear algebra) —
  for a symmetric bilinear form `A` on a finite dimensional real inner product space `V`, a family
  `e` spanning `V` with Gram matrix `Γ`, and an orthonormal family `f` of `finrank ℝ V` vectors,
  `∑ᵢⱼ (Γ⁻¹)ᵢⱼ A(eᵢ,eⱼ) = ∑ᵢ A(fᵢ,fᵢ)`.

The last statement is the usual "trace of a bilinear form in a basis": if `T` is the operator with
`⟪T u, w⟫ = A u w`, then `∑ᵢ A(fᵢ,fᵢ) = tr T`, while writing `T` in the basis `e`,
`(Γ⁻¹)ᵢⱼ A(eᵢ,eⱼ)` is exactly the `(i,i)`-entry of `Γ⁻¹ Nᵀ = M`, the matrix of `T` in that basis
(the `B`-dual basis of `e` is `dᵢ = ∑ⱼ (Γ⁻¹)ᵢⱼ eⱼ`, and `Mᵢⱼ = ⟪T eⱼ, dᵢ⟫`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

open scoped InnerProductSpace in
/-- **Trace of a symmetric bilinear form in a general basis.**

Let `V` be a finite dimensional real inner product space, `A : V → V → ℝ` linear in its first
argument (`hadd`, `hsmul`) and symmetric (`hsym`), let `e : Fin (finrank ℝ V) → V` span `V` with
Gram matrix `Γᵢⱼ = ⟪eᵢ,eⱼ⟫`, and let `f` be an orthonormal family of `finrank ℝ V` vectors.  Then the
contraction of `A` with `Γ⁻¹` equals the trace of `A` in the orthonormal frame `f`:

  `∑ᵢⱼ (Γ⁻¹)ᵢⱼ A(eᵢ,eⱼ) = ∑ᵢ A(fᵢ,fᵢ)`.

(The degenerate case `finrank ℝ V = 0` is included: `Fin 0` is empty and both sides vanish.) -/
theorem sum_invGram_mul_eq_sum_orthonormal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : V → V → ℝ)
    (hadd : ∀ u₁ u₂ w : V, A (u₁ + u₂) w = A u₁ w + A u₂ w)
    (hsmul : ∀ (a : ℝ) (u w : V), A (a • u) w = a * A u w)
    (hsym : ∀ u w : V, A u w = A w u)
    (e f : Fin (Module.finrank ℝ V) → V)
    (he : Submodule.span ℝ (Set.range e) = ⊤)
    (hf : Orthonormal ℝ f)
    (Γ : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ)
    (hΓ : ∀ i j, Γ i j = inner ℝ (e i) (e j)) :
    (∑ i, ∑ j, (Γ⁻¹) i j * A (e i) (e j)) = ∑ i, A (f i) (f i) := by
  classical
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Module.finrank ℝ V := Fintype.card_fin _
  -- `e` is a basis, being a spanning family of `finrank ℝ V` vectors.
  have hli : LinearIndependent ℝ e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank he.ge hcard
  let be : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    basisOfLinearIndependentOfCardEqFinrank' e hli hcard
  have hbe : ⇑be = e := coe_basisOfLinearIndependentOfCardEqFinrank' e hli hcard
  -- `Γ` is the Gram matrix of `e`, hence positive definite and invertible.
  have hΓeq : Γ = Matrix.gram ℝ e := Matrix.ext (fun i j => by rw [hΓ, Matrix.gram_apply])
  have hpd : Γ.PosDef := hΓeq ▸ (Matrix.posDef_gram_of_linearIndependent hli)
  have hunit : IsUnit Γ.det := (Matrix.isUnit_iff_isUnit_det Γ).mp hpd.isUnit
  have hinv_mul : Γ⁻¹ * Γ = 1 := Matrix.nonsing_inv_mul Γ hunit
  have hΓsym2 : ∀ i j, Γ i j = Γ j i := fun i j => by
    rw [hΓ i j, hΓ j i]; exact real_inner_comm _ _
  -- linearity of `A` in the second argument, from symmetry
  have hadd₂ : ∀ u w₁ w₂ : V, A u (w₁ + w₂) = A u w₁ + A u w₂ := by
    intro u w₁ w₂; rw [hsym u (w₁ + w₂), hadd w₁ w₂ u, hsym w₁ u, hsym w₂ u]
  have hsmul₂ : ∀ (a : ℝ) (u w : V), A u (a • w) = a * A u w := by
    intro a u w; rw [hsym u (a • w), hsmul a w u, hsym w u]
  -- `A` bundled as a bilinear form
  let φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun u => { toFun := fun w => A u w
                          map_add' := fun w₁ w₂ => hadd₂ u w₁ w₂
                          map_smul' := fun a w => hsmul₂ a u w }
      map_add' := fun u₁ u₂ => by ext w; exact hadd u₁ u₂ w
      map_smul' := fun a u => by ext w; exact hsmul a u w }
  have hφapp : ∀ u w, φ u w = A u w := fun u w => rfl
  -- the operator representing `A`
  let T : V →ₗ[ℝ] V :=
    { toFun := fun u => ∑ k, A u (f k) • f k
      map_add' := fun u₁ u₂ => by
        show (∑ k, A (u₁ + u₂) (f k) • f k)
            = (∑ k, A u₁ (f k) • f k) + ∑ k, A u₂ (f k) • f k
        simp only [hadd u₁ u₂, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a u => by
        show (∑ k, A (a • u) (f k) • f k) = a • ∑ k, A u (f k) • f k
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsmul a u (f k), mul_smul] }
  have hTu : ∀ u : V, T u = ∑ k, A u (f k) • f k := fun u => rfl
  -- `f` is an orthonormal basis
  let bf : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    basisOfLinearIndependentOfCardEqFinrank' f hf.linearIndependent hcard
  have hbf : ⇑bf = f := coe_basisOfLinearIndependentOfCardEqFinrank' f hf.linearIndependent hcard
  have hbfON : Orthonormal ℝ (⇑bf) := by rw [hbf]; exact hf
  let B : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := bf.toOrthonormalBasis hbfON
  have hB : ⇑B = f := by rw [Module.Basis.coe_toOrthonormalBasis, hbf]
  have hrepr : ∀ w : V, ∑ k, inner ℝ (f k) w • f k = w := by
    intro w
    have := B.sum_repr' w
    simpa only [hB] using this
  -- `T` represents `A`
  have hTuw : ∀ u w : V, inner ℝ (T u) w = A u w := by
    intro u w
    have h1 : inner ℝ (T u) w = ∑ k, A u (f k) * inner ℝ (f k) w := by
      rw [hTu u, sum_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_left]
    have h4 : φ u w = ∑ k, A u (f k) * inner ℝ (f k) w := by
      conv_lhs => rw [← hrepr w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hφapp, smul_eq_mul, mul_comm]
    have h2 : A u w = ∑ k, A u (f k) * inner ℝ (f k) w := by
      rw [← hφapp u w, h4]
    rw [h1, h2]
  -- the `Γ`-dual basis: `⟪e k, ∑ j, (Γ⁻¹) i j • e j⟫ = δ k i`
  have hd : ∀ k i, inner ℝ (e k) (∑ j, Γ⁻¹ i j • e j) = if k = i then 1 else 0 := by
    intro k i
    rw [inner_sum]
    simp only [real_inner_smul_right]
    have h1 : ∑ j, Γ⁻¹ i j * inner ℝ (e k) (e j) = ∑ j, Γ⁻¹ i j * Γ j k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show inner ℝ (e k) (e j) = Γ j k from (hΓ k j).symm.trans (hΓsym2 k j)]
    rw [h1, ← Matrix.mul_apply, hinv_mul, Matrix.one_apply]
    by_cases h : k = i
    · rw [h]
    · have hne : ¬ (i = k) := fun hik => h hik.symm
      simp only [h, hne, ite_false]
  -- expansion of `T (e j)` in the basis `e`
  have hrepr2 : ∀ j, T (e j) = ∑ k, (be.repr (T (e j))) k • e k := by
    intro j
    conv_lhs => rw [← be.sum_repr (T (e j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [congrFun hbe k]
  -- the matrix entries of `T` in the basis `e`
  have hMij : ∀ i j, (T.toMatrix be be) i j = inner ℝ (T (e j)) (∑ k, Γ⁻¹ i k • e k) := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    rw [congrFun hbe j]
    have hkey : inner ℝ (T (e j)) (∑ k, Γ⁻¹ i k • e k) = (be.repr (T (e j))) i := by
      conv_lhs => rw [hrepr2 j]
      rw [sum_inner]
      simp only [real_inner_smul_left]
      rw [Finset.sum_eq_single i]
      · rw [hd i i]; simp
      · intro k _ hk
        rw [hd k i]; simp [hk]
      · intro hmem; exact absurd (Finset.mem_univ i) hmem
    exact hkey.symm
  -- evaluation of a diagonal matrix entry
  have hMii : ∀ i, (T.toMatrix be be) i i = ∑ j, Γ⁻¹ i j * A (e i) (e j) := by
    intro i
    rw [hMij i i]
    rw [hTuw (e i) (∑ j, Γ⁻¹ i j • e j)]
    conv_lhs => rw [← hφapp (e i) (∑ j, Γ⁻¹ i j • e j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφapp, smul_eq_mul]
  -- the two trace computations
  have htr1 : (∑ i, A (f i) (f i)) = T.trace ℝ V := by
    rw [LinearMap.trace_eq_sum_inner T B]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show B i = f i from congrFun hB i]
    rw [real_inner_comm (T (f i)) (f i)]
    exact (hTuw (f i) (f i)).symm
  have htr2 : T.trace ℝ V = (T.toMatrix be be).trace := LinearMap.trace_eq_matrix_trace ℝ be T
  calc (∑ i, ∑ j, (Γ⁻¹) i j * A (e i) (e j))
      = ∑ i, (T.toMatrix be be) i i := Finset.sum_congr rfl (fun i _ => (hMii i).symm)
    _ = (T.toMatrix be be).trace := by
        rw [Matrix.trace]
        exact Finset.sum_congr rfl (fun i _ => (Matrix.diag_apply _ i).symm)
    _ = T.trace ℝ V := htr2.symm
    _ = ∑ i, A (f i) (f i) := htr1.symm

/-- **The Laplacian is the inverse-Gram contraction of the Hessian.**

For a `C²` function `u` (here `CMDiff ∞ u`), a smooth metric `g`, a point `x`, and *any* basis
`e₁,…,eₙ` of `TₓM` with Gram matrix `Γᵢⱼ = g(x)(eᵢ,eⱼ)` (i.e. `span (range e) = ⊤`, so that there are
`finrank ℝ E` of them), the Laplacian of `u` at `x` is obtained by contracting the Hessian with
`Γ⁻¹`.  This is `laplAt_eq_sum_hessAt` (frame independence of the Hessian trace) combined with the
trace formula `sum_invGram_mul_eq_sum_orthonormal`. -/
theorem laplAt_eq_sum_invGram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] (hLC : LCSmooth I M)
    (g : SMet I M) (u : M → ℝ) (x : M) (hu : CMDiff ∞ u)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    laplAt g u x = ∑ i, ∑ j, (Γ⁻¹) i j * hessAt g u x (e i) (e j) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- `u` is `C²`, hence its Hessian is symmetric
  have hu2 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2 u x :=
    (hu.contMDiffAt).of_le (by simp)
  have hsym : ∀ v w : TangentSpace I x, hessAt g u x v w = hessAt g u x w v :=
    fun v w => hessAt_comm hLC g u x hu2 v w
  -- `laplAt` is the Hessian trace in the orthonormal frame `onFrame g x`
  have hlap : laplAt g u x = ∑ i, hessAt g u x (onFrame g x i) (onFrame g x i) :=
    laplAt_eq_sum_hessAt g u x (onFrame g x) (isONFrame_onFrame g x) hsym
  rw [hlap]
  -- `onFrame g x` is orthonormal for the instance inner product
  have hON : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact isONFrame_onFrame g x i j
  -- `hessAt g u x` is linear in its first slot
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
  -- `Γ` is the Gram matrix of `e`
  have hΓeq : Γ = Matrix.gram ℝ e := by
    ext i j
    rw [hΓ i j, Matrix.gram_apply]
    rfl
  rw [hΓeq]
  exact (sum_invGram_mul_eq_sum_orthonormal (V := TangentSpace I x)
    (fun v w => hessAt g u x v w) hadd hsmul hsym e (onFrame g x) hb hON
    (Matrix.gram ℝ e) (fun i j => rfl)).symm

end Work.Diff.GE
