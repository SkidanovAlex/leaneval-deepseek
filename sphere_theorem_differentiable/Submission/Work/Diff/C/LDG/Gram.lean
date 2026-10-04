import Submission.Work.Diff.C.LDG.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gram/linear-algebra core of `local_diffeo_of_gram`
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology EuclideanSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.LDG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

theorem eq_zero_of_gram
    {F : Idx E → M → ℝ} {ε₂ : ℝ} (hε₂ : 0 ≤ ε₂) (hε₂1 : ε₂ < 1)
    (hgram : ∀ (x : M) (c : Idx E → ℝ),
        |(∑ i, ∑ j, c i * c j * gp (I := I) (M := M) (F i) (F j) x) - (∑ i, c i ^ 2)|
          ≤ ε₂ * (∑ i, c i ^ 2))
    (x : M) {v : TangentSpace I x} {μ : ℝ}
    (h : ∀ i, Inner.inner ℝ (rgrad (I := I) (M := M) (F i) x) v = μ * F i x) :
    v = 0 := by
  set a : Idx E → TangentSpace I x := fun i => rgrad (I := I) (M := M) (F i) x with ha
  set f : Idx E → ℝ := fun i => F i x with hf
  have hgp : ∀ i j : Idx E, gp (I := I) (M := M) (F i) (F j) x
      = Inner.inner ℝ (a i) (a j) + f i * f j := by
    intro i j
    simp only [gp, ha, hf]
  -- the linear map `T c = (∑ cᵢ aᵢ, ∑ cᵢ fᵢ)`
  let T : (Idx E → ℝ) →ₗ[ℝ] (TangentSpace I x × ℝ) :=
    { toFun := fun c => (∑ i, c i • a i, ∑ i, c i * f i)
      map_add' := by
        intro c d
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, add_mul,
          Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        have h1 : (∑ i, (r • c) i • a i) = r • ∑ i, c i • a i := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by
            simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
        have h2 : (∑ i, (r • c) i * f i) = r * ∑ i, c i * f i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by
            simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        simp only [h1, h2, RingHom.id_apply, Prod.smul_mk, smul_eq_mul] }
  have hT1 : ∀ c : Idx E → ℝ, (T c).1 = ∑ i, c i • a i := fun c => rfl
  have hT2 : ∀ c : Idx E → ℝ, (T c).2 = ∑ i, c i * f i := fun c => rfl
  -- the quadratic identity
  have hQ : ∀ c : Idx E → ℝ, Inner.inner ℝ (T c).1 (T c).1 + (T c).2 ^ 2
      = ∑ i, ∑ j, c i * c j * gp (I := I) (M := M) (F i) (F j) x := by
    intro c
    have hinner : Inner.inner ℝ (∑ i, c i • a i) (∑ i, c i • a i)
        = ∑ i, ∑ j, c i * c j * Inner.inner ℝ (a i) (a j) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left, inner_smul_right]
      ring
    have hsq : (∑ i, c i * f i) * (∑ i, c i * f i)
        = ∑ i, ∑ j, c i * c j * (f i * f j) := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hT1 c, hT2 c, pow_two, hinner, hsq]
    simp only [hgp, mul_add, Finset.sum_add_distrib]
  -- `T` has trivial kernel
  have hnull : ∀ c : Idx E → ℝ, T c = 0 → c = 0 := by
    intro c hc
    have h0 : Inner.inner ℝ (T c).1 (T c).1 + (T c).2 ^ 2 = 0 := by
      rw [hc]; simp
    have hb := hgram x c
    rw [← hQ c, h0] at hb
    have hSnn : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg (c i)
    have hS : ∑ i, c i ^ 2 = 0 := by
      have h1 := (abs_le.mp hb).1
      have h3 : (∑ i, c i ^ 2) * (1 - ε₂) ≤ 0 := by nlinarith [h1]
      have h4 : (∑ i, c i ^ 2) ≤ 0 := by
        rcases mul_nonpos_iff.mp h3 with ⟨_, hε0⟩ | ⟨hS0, _⟩
        · exact absurd hε0 (not_le.mpr (by linarith : (0 : ℝ) < 1 - ε₂))
        · exact hS0
      linarith
    funext i
    have hi : c i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => _root_.sq_nonneg (c i))).mp hS i
        (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
  have hinj : Function.Injective T := by
    intro c d hcd
    have hcd' : T (c - d) = 0 := by rw [map_sub, hcd, sub_self]
    have hcd0 : c - d = 0 := hnull (c - d) hcd'
    exact sub_eq_zero.mp hcd0
  -- dimension count
  have hrank : Module.finrank ℝ (Idx E → ℝ) = Module.finrank ℝ (TangentSpace I x × ℝ) := by
    rw [Module.finrank_pi, Module.finrank_prod, Module.finrank_self,
      show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from
        (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq]
    simp [Idx]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := Idx E → ℝ)
      (V₂ := TangentSpace I x × ℝ) hrank (f := T)).mp hinj
  obtain ⟨c, hc⟩ := hsurj (v, -μ)
  -- the pairing
  have hkey : Inner.inner ℝ (T c).1 v + (T c).2 * (-μ) = 0 := by
    rw [hT1 c, hT2 c, sum_inner]
    have hstep : (∑ i, Inner.inner ℝ (c i • a i) v) = ∑ i, c i * (μ * f i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, h i]
    rw [hstep, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  rw [hc] at hkey
  have hμ : Inner.inner ℝ v v + μ ^ 2 = 0 := by nlinarith [hkey]
  have hv0 : Inner.inner ℝ v v = 0 := by
    have h2 : 0 ≤ Inner.inner ℝ v v := by simpa using inner_self_nonneg (𝕜 := ℝ) (x := v)
    nlinarith [h2, _root_.sq_nonneg μ]
  exact inner_self_eq_zero.mp hv0

end Work.Diff.C.LDG
