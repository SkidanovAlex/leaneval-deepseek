/-
# The concrete operator family of Savin's theorem

Savin's small perturbation theorem ([S], CPDE 32 (2007) 557--578) applies to an operator
`F(M, p, z, x)` which is monotone, uniformly elliptic near the origin and satisfies `F(0,·) = 0`.
In the application of Shankar--Yuan (Section 5) the relevant operator is

  `F(M) = σ₂(A + M) - σ₂(A)`  with `A = D²Q` the Hessian of a fixed quadratic solution `Q`
  of `σ₂(D²Q) = 1` on the positive branch,

i.e. `F(M) = tr(cof(A) ∘ M) + σ₂(M)` where `cof(A) = tr(A) • 1 - A` is positive definite.
After the rescalings of Savin's Section 4 the operator becomes `tr(C ∘ M) + ε σ₂(M)` with the
same positive definite `C` and a factor `ε ∈ (0,1]` in front of the quadratic term.

This file sets up that family (`Fop`), together with the *quadratic* (coordinate) model `s2` of
`σ₂`, and proves the two facts which the measure estimates need:

* the expansion `s2 (A + M) = s2 A + s2 M + tr(cof(A) ∘ M)`;
* the **contact point bound**: if `M ⪰ -a • 1` (a touching condition) and `Fop C ε M = 0`
  (the equation), then `M ⪯ K a • 1` with `K` depending only on `C` (and not on `a`, `ε`).
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Basic
import Submission.Commons.Analysis.Sigma2.coord_minor_add_expansion
import Submission.Commons.Analysis.Sigma2.coord_minor_mixed_eq_trace
import Submission.Commons.Analysis.Sigma2.coord_minor_sub_smul_one
import Submission.Commons.Analysis.Sigma2.coord_minor_nonneg_of_quadform_nonneg
import Submission.Commons.Analysis.Trace.trace_comp_ge_of_quadform_bounds
import Submission.Commons.Analysis.Trace.trace_comp_le_of_quadform_bounds
import Submission.Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_head

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The standard orthonormal basis of `ℝ⁴`. -/
noncomputable def stdB4 : OrthonormalBasis (Fin 4) ℝ ℝ⁴ := EuclideanSpace.basisFun (Fin 4) ℝ

theorem stdB4_apply (i : Fin 4) : stdB4 i = EuclideanSpace.single i (1 : ℝ) := by
  simp [stdB4, EuclideanSpace.basisFun_apply]

/-- The **quadratic model** of `σ₂`: for an operator `T` on `ℝ⁴` we set
`s2 T = ∑_{i<j} (T_{ii} T_{jj} - T_{ij}²)` where `T_{ij} = ⟪T bᵢ, bⱼ⟫` are the coordinates in the
standard basis.  For symmetric `T` this is `σ₂ T` (see `s2_eq_sigma2`). -/
noncomputable def s2 (T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ :=
  ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
    (⟪T (stdB4 i), stdB4 i⟫ * ⟪T (stdB4 j), stdB4 j⟫ - ⟪T (stdB4 i), stdB4 j⟫ ^ 2) else 0

/-- The trace of an operator on `ℝ⁴`. -/
noncomputable def trOp (T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ := LinearMap.trace ℝ ℝ⁴ T.toLinearMap

/-- The Hilbert--Schmidt pairing `tr(S ∘ M) = ∑ᵢ ⟪S(M bᵢ), bᵢ⟫` of two operators on `ℝ⁴`. -/
noncomputable def pairOp (S M : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ :=
  ∑ i : Fin 4, ⟪S (M (stdB4 i)), stdB4 i⟫

/-- The cofactor operator `cof(T) = tr(T) • 1 - T`.  For symmetric `T` with `σ₂ T = 1` and
positive trace it is positive definite. -/
noncomputable def cofOp (S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ := trOp S • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - S

/-- The concrete operator family of Savin's theorem: `F(M) = tr(C ∘ M) + ε σ₂(M)`. -/
noncomputable def Fop (S : ℝ⁴ →L[ℝ] ℝ⁴) (ε : ℝ) (M : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ :=
  pairOp S M + ε * s2 M

theorem trOp_eq_sum (T : ℝ⁴ →L[ℝ] ℝ⁴) :
    trOp T = ∑ i : Fin 4, ⟪T (stdB4 i), stdB4 i⟫ := by
  unfold trOp
  rw [LinearMap.trace_eq_sum_inner T.toLinearMap stdB4]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem pairOp_eq_trace (S M : ℝ⁴ →L[ℝ] ℝ⁴) :
    pairOp S M = LinearMap.trace ℝ ℝ⁴ (S.toLinearMap ∘ₗ M.toLinearMap) := by
  unfold pairOp
  rw [LinearMap.trace_eq_sum_inner (S.toLinearMap ∘ₗ M.toLinearMap) stdB4]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem pairOp_add (S M₁ M₂ : ℝ⁴ →L[ℝ] ℝ⁴) :
    pairOp S (M₁ + M₂) = pairOp S M₁ + pairOp S M₂ := by
  unfold pairOp
  simp only [add_apply, map_add, inner_add_left, Finset.sum_add_distrib]

theorem pairOp_smul (S M : ℝ⁴ →L[ℝ] ℝ⁴) (a : ℝ) :
    pairOp S (a • M) = a * pairOp S M := by
  unfold pairOp
  simp only [smul_apply, map_smul, real_inner_smul_left, Finset.mul_sum]

theorem pairOp_one (S : ℝ⁴ →L[ℝ] ℝ⁴) : pairOp S (1 : ℝ⁴ →L[ℝ] ℝ⁴) = trOp S := by
  unfold pairOp trOp
  rw [LinearMap.trace_eq_sum_inner S.toLinearMap stdB4]
  exact Finset.sum_congr rfl fun i _ => by simp [real_inner_comm]

theorem pairOp_sub (S M₁ M₂ : ℝ⁴ →L[ℝ] ℝ⁴) :
    pairOp S (M₁ - M₂) = pairOp S M₁ - pairOp S M₂ := by
  unfold pairOp
  simp only [sub_apply, map_sub, inner_sub_left, Finset.sum_sub_distrib]

/-- **Expansion of the quadratic model of `σ₂`.**  For symmetric `A`, `M`:
`σ₂(A + M) = σ₂(A) + σ₂(M) + tr(cof(A) ∘ M)`. -/
theorem s2_add_expansion {A M : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hM : M.IsSymmetric) :
    s2 (A + M) = s2 A + s2 M + pairOp (cofOp A) M := by
  have h1 := Commons.Analysis.Sigma2.coord_minor_add_expansion stdB4 hA hM
  have h2 := Commons.Analysis.Sigma2.coord_minor_mixed_eq_trace stdB4 hA hM
  have h3 : LinearMap.trace ℝ ℝ⁴
      (((LinearMap.trace ℝ ℝ⁴ (A : ℝ⁴ →ₗ[ℝ] ℝ⁴) • (1 : ℝ⁴ →ₗ[ℝ] ℝ⁴)
        - (A : ℝ⁴ →ₗ[ℝ] ℝ⁴))).comp ((M : ℝ⁴ →ₗ[ℝ] ℝ⁴)))
      = pairOp (cofOp A) M := by
    rw [pairOp_eq_trace]
    simp only [cofOp, trOp, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]
  unfold s2
  rw [h1, h2]
  exact congrArg _ h3


/-- `σ₂(N - a • 1) = σ₂(N) - 3 a tr(N) + 6 a²`: the effect of shifting an operator by a multiple of
the identity on the quadratic model of `σ₂` in dimension four. -/
theorem s2_sub_smul_one (a : ℝ) (N : ℝ⁴ →L[ℝ] ℝ⁴) :
    s2 (N - a • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) = s2 N - 3 * a * trOp N + 6 * a ^ 2 := by
  unfold s2 trOp
  rw [Commons.Analysis.Sigma2.coord_minor_sub_smul_one stdB4 a N]

/-- `σ₂ ≥ 0` for positive semidefinite operators: the quadratic model is a sum of principal
`2 × 2` minors of a positive semidefinite matrix. -/
theorem s2_nonneg_of_quadform_nonneg {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric)
    (h : ∀ v : ℝ⁴, 0 ≤ ⟪N v, v⟫) : 0 ≤ s2 N :=
  Commons.Analysis.Sigma2.coord_minor_nonneg_of_quadform_nonneg stdB4 hN h

theorem trOp_one : trOp (1 : ℝ⁴ →L[ℝ] ℝ⁴) = 4 := by
  rw [trOp_eq_sum]
  have h1 : ∀ i : Fin 4, ⟪(1 : ℝ⁴ →L[ℝ] ℝ⁴) (stdB4 i), stdB4 i⟫ = (1 : ℝ) := by
    intro i
    rw [ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq, stdB4.orthonormal.1 i]
    norm_num
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- A positive semidefinite symmetric operator satisfies `⟪N v, v⟫ ≤ trOp N * ‖v‖²`. -/
theorem quadform_le_trace_of_nonneg {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric)
    (h : ∀ v : ℝ⁴, 0 ≤ ⟪N v, v⟫) (v : ℝ⁴) : ⟪N v, v⟫ ≤ trOp N * ‖v‖ ^ 2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖(‖v‖⁻¹) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀]
    exact ne_of_gt hnorm
  obtain ⟨b, hb0⟩ := Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_head (E := ℝ⁴)
    (n := 3) (e := (‖v‖⁻¹) • v) (by simp : Module.finrank ℝ ℝ⁴ = 3 + 1) hunit
  have htr : trOp N = ∑ i : Fin 4, ⟪N (b i), b i⟫ := by
    unfold trOp
    rw [LinearMap.trace_eq_sum_inner N.toLinearMap b]
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  have hsplit : (∑ i : Fin 4, ⟪N (b i), b i⟫)
      = ⟪N (b 0), b 0⟫ + ∑ i ∈ Finset.univ.erase (0 : Fin 4), ⟪N (b i), b i⟫ :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 4))).symm
  have hnonneg : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 4), ⟪N (b i), b i⟫ :=
    Finset.sum_nonneg fun i _ => h _
  have hb0v : b 0 = (‖v‖⁻¹) • v := hb0
  have hkey : ⟪N (b 0), b 0⟫ = (‖v‖⁻¹) ^ 2 * ⟪N v, v⟫ := by
    rw [hb0v]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have h1 : (‖v‖⁻¹) ^ 2 * ⟪N v, v⟫ ≤ trOp N := by
    rw [htr, hsplit, hkey]
    have := hnonneg
    linarith
  have h2 : (‖v‖⁻¹) ^ 2 = (‖v‖ ^ 2)⁻¹ := by rw [inv_pow]
  rw [h2, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < ‖v‖ ^ 2)] at h1
  simpa only [mul_comm] using h1

/-- **Contact point bound.**  Let `C` be positive definite (`c ‖v‖² ≤ ⟪C v, v⟫`) and let `M` be a
symmetric operator satisfying the *touching* condition `M ⪰ -a • 1` together with the *equation*
`Fop C ε M = 0`.  If `a` is small compared with `ε` and with the ellipticity constant of `C`, then
`M ⪯ K a • 1` with `K` independent of `a` and `ε`.

This is the substitute for Savin's inequality (7) (the bound of the Hessian at a contact point of a
sliding paraboloid) in the classical, concrete case; it is what makes the map
`x ↦ x + Dφ(x)/a` of the sliding paraboloid argument have bounded Jacobian. -/
theorem contact_bound {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (haε : 3 * ε * a ≤ c / 2) {M : ℝ⁴ →L[ℝ] ℝ⁴} (hM : M.IsSymmetric)
    (hquad : ∀ v : ℝ⁴, -a * ‖v‖ ^ 2 ≤ ⟪M v, v⟫) (heq : Fop C ε M = 0) :
    ∀ v : ℝ⁴, ⟪M v, v⟫ ≤ (2 * trOp C / c + 3) * a * ‖v‖ ^ 2 := by
  set N : ℝ⁴ →L[ℝ] ℝ⁴ := M + a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) with hNdef
  have hMN : M = N - a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by rw [hNdef]; abel
  have hNsym : N.IsSymmetric := by
    intro x y
    have hx : N x = M x + a • x := by rw [hNdef]; simp
    have hy : N y = M y + a • y := by rw [hNdef]; simp
    change ⟪N x, y⟫ = ⟪x, N y⟫
    have hMxy : ⟪M x, y⟫ = ⟪x, M y⟫ := hM x y
    rw [hx, hy, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hMxy]
  have hNpos : ∀ v : ℝ⁴, 0 ≤ ⟪N v, v⟫ := by
    intro v
    have h1 := hquad v
    have hv : N v = M v + a • v := by rw [hNdef]; simp
    rw [hv, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [h1]
  -- The equation, rewritten in terms of `N`.
  have heq' : pairOp C N - a * trOp C + ε * (s2 N - 3 * a * trOp N + 6 * a ^ 2) = 0 := by
    have h1 : Fop C ε M = pairOp C M + ε * s2 M := rfl
    rw [h1, hMN, pairOp_sub, pairOp_smul, pairOp_one, s2_sub_smul_one] at heq
    exact heq
  -- The two lower bounds which make the equation strong.
  have hpairN : c * trOp N ≤ pairOp C N := by
    have h := Commons.Analysis.Trace.trace_comp_ge_of_quadform_bounds hC hNsym hcq hNpos
    rw [pairOp_eq_trace]
    exact h
  have hs2N : 0 ≤ s2 N := s2_nonneg_of_quadform_nonneg hNsym hNpos
  have htrN : 0 ≤ trOp N := by
    rw [trOp_eq_sum]; exact Finset.sum_nonneg fun i _ => hNpos _
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h := hcq (stdB4 i)
    have h2 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h2] at h
    nlinarith [h]
  have hcomb : (c - 3 * ε * a) * trOp N - a * trOp C ≤ 0 := by
    nlinarith [heq', hpairN, hs2N, htrN, hε, ha]
  -- Hence `trOp N ≤ 2 a trOp C / c`.
  have htrNle : trOp N ≤ 2 * a * trOp C / c := by
    have h2 : c / 2 * trOp N ≤ a * trOp C := by nlinarith
    rw [le_div_iff₀ hc]
    nlinarith
  have htrM : trOp M = trOp N - 4 * a := by
    have h1 : trOp M = trOp (N - a • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) := by rw [hMN]
    rw [h1, show trOp (N - a • (1 : ℝ⁴ →L[ℝ] ℝ⁴))
      = trOp N - a * trOp (1 : ℝ⁴ →L[ℝ] ℝ⁴) from by
        unfold trOp
        simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul]
        rw [map_sub, map_smul, smul_eq_mul], trOp_one]
    ring
  -- Convert into a bound on the quadratic form.
  intro v
  have hquadM : ⟪M v, v⟫ ≤ (trOp M + 3 * a) * ‖v‖ ^ 2 := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunit : ‖((‖v‖)⁻¹) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀]
      exact ne_of_gt hnorm
    obtain ⟨b, hb0⟩ := Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_head (E := ℝ⁴)
      (n := 3) (e := ((‖v‖)⁻¹) • v) (by simp : Module.finrank ℝ ℝ⁴ = 3 + 1) hunit
    have htr : trOp M = ∑ i : Fin 4, ⟪M (b i), b i⟫ := by
      unfold trOp
      rw [LinearMap.trace_eq_sum_inner M.toLinearMap b]
      exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
    have hsplit : (∑ i : Fin 4, ⟪M (b i), b i⟫)
        = ⟪M (b 0), b 0⟫ + ∑ i ∈ Finset.univ.erase (0 : Fin 4), ⟪M (b i), b i⟫ :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 4))).symm
    have hdiag : ∀ i ∈ Finset.univ.erase (0 : Fin 4), ⟪M (b i), b i⟫ ≥ -a := by
      intro i _
      have h1 := hquad (b i)
      have h2 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [h2] at h1
      nlinarith [h1]
    have hsum : ∑ i ∈ Finset.univ.erase (0 : Fin 4), ⟪M (b i), b i⟫ ≥ -3 * a := by
      have hcard : (Finset.univ.erase (0 : Fin 4)).card = 3 := by decide
      calc ∑ i ∈ Finset.univ.erase (0 : Fin 4), ⟪M (b i), b i⟫
          ≥ ∑ _i ∈ Finset.univ.erase (0 : Fin 4), (-a) := Finset.sum_le_sum hdiag
        _ = -3 * a := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
    have hb0v : b 0 = ((‖v‖)⁻¹) • v := hb0
    have hkey : ⟪M (b 0), b 0⟫ = ((‖v‖)⁻¹) ^ 2 * ⟪M v, v⟫ := by
      rw [hb0v]
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    have h1 : ((‖v‖)⁻¹) ^ 2 * ⟪M v, v⟫ - 3 * a ≤ trOp M := by
      rw [htr, hsplit, hkey]
      have := hsum
      linarith
    have h2 : ((‖v‖)⁻¹) ^ 2 = (‖v‖ ^ 2)⁻¹ := by rw [inv_pow]
    have h1' : (‖v‖ ^ 2)⁻¹ * ⟪M v, v⟫ ≤ trOp M + 3 * a := by
      rw [h2] at h1; linarith
    rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < ‖v‖ ^ 2)] at h1'
    linarith [h1']
  have hfinal : trOp M + 3 * a ≤ (2 * trOp C / c + 3) * a := by
    have hK : trOp N ≤ (2 * trOp C / c) * a := by
      calc trOp N ≤ 2 * a * trOp C / c := htrNle
        _ = (2 * trOp C / c) * a := by ring
    rw [htrM]
    nlinarith [hK, ha]
  nlinarith [hquadM, hfinal, sq_nonneg ‖v‖]

theorem s2_neg (M : ℝ⁴ →L[ℝ] ℝ⁴) : s2 (-M) = s2 M := by
  unfold s2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i < j
  · simp only [h, if_true, neg_apply, inner_neg_left, inner_neg_right]
    ring
  · simp only [h, if_false]

theorem pairOp_neg_left (C M : ℝ⁴ →L[ℝ] ℝ⁴) : pairOp (-C) M = -pairOp C M := by
  unfold pairOp
  simp only [neg_apply, inner_neg_left, Finset.sum_neg_distrib]

theorem pairOp_const_smul_left (C M : ℝ⁴ →L[ℝ] ℝ⁴) (k : ℝ) :
    pairOp (k • C) M = k * pairOp C M := by
  unfold pairOp
  simp only [smul_apply, real_inner_smul_left, Finset.mul_sum]

/-- **Dual contact point bound.**  This is the contact bound for the *negated* operator
`M ↦ -tr(C ∘ M) + ε σ₂(M)` (equivalently: for the function `-φ`), i.e. the case of paraboloids
touching the graph from *above*.  If `M ⪯ a • 1` and `-tr(C∘M) + ε σ₂(M) = 0` then
`M ⪰ -(2 tr C / c + 3) a • 1`, with the bound independent of `a` and `ε`. -/
theorem contact_bound_above {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (haε : 3 * ε * a ≤ c / 2) {M : ℝ⁴ →L[ℝ] ℝ⁴} (hM : M.IsSymmetric)
    (hquad : ∀ v : ℝ⁴, ⟪M v, v⟫ ≤ a * ‖v‖ ^ 2)
    (heq : -pairOp C M + ε * s2 M = 0) :
    ∀ v : ℝ⁴, -(2 * trOp C / c + 3) * a * ‖v‖ ^ 2 ≤ ⟪M v, v⟫ := by
  set P : ℝ⁴ →L[ℝ] ℝ⁴ := a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - M with hPdef
  have hPpos : ∀ v : ℝ⁴, 0 ≤ ⟪P v, v⟫ := by
    intro v
    have h1 := hquad v
    have hv : P v = a • v - M v := by rw [hPdef]; simp
    rw [hv, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [h1]
  have hPsym : P.IsSymmetric := by
    intro x y
    have hx : P x = a • x - M x := by rw [hPdef]; simp
    have hy : P y = a • y - M y := by rw [hPdef]; simp
    have hMxy : ⟪M x, y⟫ = ⟪x, M y⟫ := hM x y
    change ⟪P x, y⟫ = ⟪x, P y⟫
    rw [hx, hy, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hMxy]
  have hMP : M = a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - P := by rw [hPdef]; abel
  have heq' : -a * trOp C + pairOp C P + ε * (s2 P - 3 * a * trOp P + 6 * a ^ 2) = 0 := by
    have h1 : M = a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - P := hMP
    rw [h1, pairOp_sub, pairOp_smul, pairOp_one] at heq
    have h2 : a • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - P = -(P - a • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) := by abel
    rw [h2, s2_neg, s2_sub_smul_one] at heq
    have h3 := heq
    ring_nf at h3 ⊢
    exact h3
  have hpairP : c * trOp P ≤ pairOp C P := by
    have h := Commons.Analysis.Trace.trace_comp_ge_of_quadform_bounds hC hPsym hcq hPpos
    rw [pairOp_eq_trace]
    exact h
  have hs2P : 0 ≤ s2 P := s2_nonneg_of_quadform_nonneg hPsym hPpos
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h := hcq (stdB4 i)
    have h2 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h2] at h
    nlinarith [h]
  have htrP : 0 ≤ trOp P := by
    rw [trOp_eq_sum]; exact Finset.sum_nonneg fun i _ => hPpos _
  have htrPle : trOp P ≤ 2 * a * trOp C / c := by
    have h1 : a * trOp C ≥ (c - 3 * ε * a) * trOp P := by nlinarith [heq', hpairP, hs2P, hε, ha]
    have h2 : c / 2 ≤ c - 3 * ε * a := by linarith
    have h3 : c / 2 * trOp P ≤ a * trOp C := by nlinarith [h1, h2, htrP]
    rw [le_div_iff₀ hc]
    nlinarith
  intro v
  have hPv : ⟪P v, v⟫ ≤ trOp P * ‖v‖ ^ 2 := quadform_le_trace_of_nonneg hPsym hPpos v
  have hMv : ⟪M v, v⟫ = a * ‖v‖ ^ 2 - ⟪P v, v⟫ := by
    have hv : M v = a • v - P v := by rw [hMP]; simp
    rw [hv, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have htrM : trOp P ≤ 2 * trOp C / c * a := by
    calc trOp P ≤ 2 * a * trOp C / c := htrPle
      _ = 2 * trOp C / c * a := by ring
  nlinarith [hMv, hPv, htrM, sq_nonneg ‖v‖]

end

end Submission
