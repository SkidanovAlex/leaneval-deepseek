import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

open Matrix

namespace Commons.LinearAlgebra.Matrix

theorem log_one_add_taylor3 (t : ℝ) (ht : -1 < t) :
    Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  let k : ℝ → ℝ := fun s => s - s ^ 2 / 2 + s ^ 3 / 3 - Real.log (1 + s)
  have hk0 : k 0 = 0 := by simp [k]
  have hdpoly : ∀ x : ℝ, deriv (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) x = 1 - x + x ^ 2 := by
    intro x
    rw [show (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) =
        ((fun y : ℝ => y) - (fun y : ℝ => y ^ 2 / 2)) + (fun y : ℝ => y ^ 3 / 3) from rfl]
    rw [deriv_add (by fun_prop) (by fun_prop),
        deriv_sub (by fun_prop) (by fun_prop),
        deriv_div_const, deriv_div_const]
    rw [deriv_fun_pow (f := fun y : ℝ => y) (x := x) (n := 2) differentiableAt_id]
    rw [deriv_fun_pow (f := fun y : ℝ => y) (x := x) (n := 3) differentiableAt_id]
    rw [deriv_id'']
    ring
  have hdlog : ∀ x : ℝ, (1:ℝ) + x ≠ 0 → deriv (fun y : ℝ => Real.log (1 + y)) x = (1 + x)⁻¹ := by
    intro x h1
    change deriv (Real.log ∘ (fun y : ℝ => 1 + y)) x = (1 + x)⁻¹
    rw [deriv_comp x (Real.differentiableAt_log h1)
        (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => 1 + y) x)]
    rw [Real.deriv_log]
    have h2 : deriv (fun y : ℝ => 1 + y) x = 1 := by
      rw [show (fun y : ℝ => 1 + y) = (fun _ : ℝ => (1:ℝ)) + (fun y : ℝ => y) from rfl]
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_id'']
      simp
    rw [h2, mul_one]
  have hderiv : ∀ x ∈ Set.Ioi (-1), deriv k x = x ^ 3 / (1 + x) := by
    intro x hx
    have h1 : (1 : ℝ) + x ≠ 0 := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    have hp : DifferentiableAt ℝ (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) x := by fun_prop
    have hl : DifferentiableAt ℝ (fun y : ℝ => Real.log (1 + y)) x :=
      (differentiableAt_id.const_add 1).log h1
    have hsub : deriv k x = deriv (fun y : ℝ => y - y^2/2 + y^3/3) x
        - deriv (fun y : ℝ => Real.log (1 + y)) x := by
      rw [show k = (fun y : ℝ => y - y^2/2 + y^3/3) - (fun y : ℝ => Real.log (1 + y)) from rfl]
      exact deriv_sub hp hl
    rw [hsub, hdpoly x, hdlog x h1]
    rw [show (1:ℝ) - x + x^2 - (1+x)⁻¹ = x^3/(1+x) by field_simp; ring]
  have hcont_poly : ContinuousOn (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3) (Set.Ici (0:ℝ)) := by fun_prop
  have hcont_poly2 : ContinuousOn (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3) (Set.Ioc (-1:ℝ) 0) := by fun_prop
  by_cases ht0 : 0 ≤ t
  · have hcont_log : ContinuousOn (fun s : ℝ => Real.log (1 + s)) (Set.Ici (0:ℝ)) := by
      refine ContinuousOn.log (by fun_prop) ?_
      intro s hs; have := hs; simp only [Set.mem_Ici] at this; linarith
    have hdiff : DifferentiableOn ℝ k (interior (Set.Ici (0:ℝ))) := by
      intro x hx
      rw [interior_Ici] at hx
      have h1 : (1:ℝ) + x ≠ 0 := by have := hx; simp only [Set.mem_Ioi] at this; linarith
      exact ((show DifferentiableAt ℝ ((fun y : ℝ => y - y^2/2 + y^3/3)
          - (fun y : ℝ => Real.log (1 + y))) x from
          (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y - y^2/2 + y^3/3) x).sub
            ((differentiableAt_id.const_add 1).log h1))).differentiableWithinAt
    have hmono : MonotoneOn k (Set.Ici (0:ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ hdiff ?_
      · exact hcont_poly.sub hcont_log
      · intro x hx
        rw [interior_Ici] at hx
        rw [hderiv x (by simp only [Set.mem_Ioi]; have := hx; simp only [Set.mem_Ioi] at this; linarith)]
        have : (0:ℝ) < x := hx
        positivity
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
    rw [hk0] at this
    simp only [k] at this
    linarith
  · have ht0' : t < 0 := lt_of_not_ge ht0
    have hcont_log : ContinuousOn (fun s : ℝ => Real.log (1 + s)) (Set.Ioc (-1:ℝ) 0) := by
      refine ContinuousOn.log (by fun_prop) ?_
      intro s hs; have := hs; simp only [Set.mem_Ioc] at this; linarith [this.1]
    have hdiff : DifferentiableOn ℝ k (interior (Set.Ioc (-1:ℝ) 0)) := by
      intro x hx
      rw [interior_Ioc] at hx
      have h1 : (1:ℝ) + x ≠ 0 := by have := hx; simp only [Set.mem_Ioo] at this; linarith [this.1]
      exact ((show DifferentiableAt ℝ ((fun y : ℝ => y - y^2/2 + y^3/3)
          - (fun y : ℝ => Real.log (1 + y))) x from
          (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y - y^2/2 + y^3/3) x).sub
            ((differentiableAt_id.const_add 1).log h1))).differentiableWithinAt
    have hanti : AntitoneOn k (Set.Ioc (-1:ℝ) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc (-1) 0) ?_ hdiff ?_
      · exact hcont_poly2.sub hcont_log
      · intro x hx
        rw [interior_Ioc] at hx
        have hxm : x ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; have := hx; simp only [Set.mem_Ioo] at this; linarith [this.1]
        rw [hderiv x hxm]
        have hneg : x ^ 3 ≤ 0 := by have := hx; simp only [Set.mem_Ioo] at this; nlinarith [sq_nonneg x, this.2]
        have hpos : (0:ℝ) < 1 + x := by have := hx; simp only [Set.mem_Ioo] at this; linarith [this.1]
        exact div_nonpos_of_nonpos_of_nonneg hneg hpos.le
    have := hanti (Set.mem_Ioc.mpr ⟨ht, le_of_lt ht0'⟩) (Set.mem_Ioc.mpr ⟨by norm_num, le_rfl⟩) (le_of_lt ht0')
    rw [hk0] at this
    simp only [k] at this
    linarith

theorem sum_cube_le_rpow_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∑ i, a i ^ 3 ≤ (∑ i, a i ^ 2) ^ (3 / 2 : ℝ) := by
  set S : ℝ := ∑ i, a i ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  have step1 : ∑ i, a i ^ 3 ≤ ∑ i, |a i| ^ 3 := by
    apply Finset.sum_le_sum; intro i _
    calc a i ^ 3 ≤ |a i ^ 3| := le_abs_self _
      _ = |a i| ^ 3 := by rw [abs_pow]
  have step2 : ∑ i, |a i| ^ 3 ≤ Real.sqrt S * S := by
    have hterm : ∀ i, |a i| ^ 3 ≤ Real.sqrt S * a i ^ 2 := by
      intro i
      have hai : |a i| ≤ Real.sqrt S := by
        have h1 : a i ^ 2 ≤ S := by
          rw [hS]; exact Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt h1
      have h3 : |a i| ^ 3 = |a i| * a i ^ 2 := by
        rw [show (3:ℕ) = 1 + 2 from rfl, pow_add, pow_one, sq_abs]
      rw [h3]
      exact mul_le_mul_of_nonneg_right hai (sq_nonneg _)
    calc ∑ i, |a i| ^ 3 ≤ ∑ i, Real.sqrt S * a i ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
      _ = Real.sqrt S * S := by rw [← Finset.mul_sum, ← hS]
  have step3 : Real.sqrt S * S = S ^ (3/2 : ℝ) := by
    rcases eq_or_lt_of_le hSnn with h | h
    · rw [← h, Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0)]; simp
    · rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add h, Real.rpow_one, Real.sqrt_eq_rpow]
      ring
  linarith [step1, step2, step3.le]



theorem log_det_one_add_smul_le_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {ε : ℝ} (hε : 0 ≤ ε)
    (hpos : ∀ x : E, x ≠ 0 → 0 < inner ℝ ((1 + ε • T) x) x) :
    Real.log (LinearMap.det (1 + ε • T))
      ≤ ε * LinearMap.trace ℝ E T - (ε ^ 2 / 2) * LinearMap.trace ℝ E (T ∘ₗ T)
        + (ε ^ 3 / 3) * (LinearMap.trace ℝ E (T ∘ₗ T)) ^ (3 / 2 : ℝ) := by
  classical
  let lam : Fin (Module.finrank ℝ E) → ℝ := hT.eigenvalues rfl
  let hb : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := hT.eigenvectorBasis rfl
  have hmat : (LinearMap.toMatrix hb.toBasis hb.toBasis) T = Matrix.diagonal lam := by
    simpa [lam, hb] using hT.toMatrix_eigenvectorBasis rfl
  have htr : LinearMap.trace ℝ E T = ∑ i, lam i := by
    rw [LinearMap.trace_eq_matrix_trace ℝ hb.toBasis, hmat, Matrix.trace_diagonal]
  have htr2 : LinearMap.trace ℝ E (T ∘ₗ T) = ∑ i, lam i ^ 2 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ hb.toBasis,
      LinearMap.toMatrix_comp hb.toBasis hb.toBasis hb.toBasis, hmat,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [pow_two]
  have hdet : LinearMap.det (1 + ε • T) = ∏ i, (1 + ε * lam i) := by
    rw [← LinearMap.det_toMatrix hb.toBasis, map_add, map_smul, LinearMap.toMatrix_one, hmat,
      ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add, Matrix.det_diagonal]
    apply Finset.prod_congr rfl
    intro i _
    simp [Pi.smul_apply, smul_eq_mul]
  have hposi : ∀ i, -1 < ε * lam i := by
    intro i
    have hne : hb i ≠ 0 := by
      intro h; have := hb.orthonormal.1 i
      rw [h] at this; simpa using this
    have h1 : (1 + ε • T) (hb i) = (1 + ε * lam i) • hb i := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        show T (hb i) = lam i • hb i by simpa [lam, hb] using hT.apply_eigenvectorBasis rfl i]
      rw [smul_smul, add_smul, one_smul]
    have h2 : inner ℝ ((1 + ε • T) (hb i)) (hb i) = 1 + ε * lam i := by
      rw [h1, real_inner_smul_left, real_inner_self_eq_norm_sq, hb.orthonormal.1 i]
      norm_num
    have := hpos (hb i) hne
    rw [h2] at this
    linarith
  have hlog : Real.log (LinearMap.det (1 + ε • T)) = ∑ i, Real.log (1 + ε * lam i) := by
    rw [hdet, Real.log_prod]
    intro i _
    have := hposi i
    linarith
  have hsumle : ∑ i, Real.log (1 + ε * lam i)
      ≤ ε * (∑ i, lam i) - (ε ^ 2 / 2) * (∑ i, lam i ^ 2) + (ε ^ 3 / 3) * (∑ i, lam i ^ 3) := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        Real.log (1 + ε * lam i) ≤ ε * lam i - (ε * lam i)^2/2 + (ε * lam i)^3/3 :=
      fun i _ => log_one_add_taylor3 (ε * lam i) (hposi i)
    refine (Finset.sum_le_sum h1).trans ?_
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        ε * lam i - (ε * lam i)^2/2 + (ε * lam i)^3/3
          = ε * lam i - (ε^2/2) * lam i^2 + (ε^3/3) * lam i^3 := fun i _ => by ring
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hcube : (ε ^ 3 / 3) * (∑ i, lam i ^ 3) ≤ (ε ^ 3 / 3) * (∑ i, lam i ^ 2) ^ (3 / 2 : ℝ) := by
    have hnn : 0 ≤ ε ^ 3 / 3 := by positivity
    exact mul_le_mul_of_nonneg_left (sum_cube_le_rpow_sum_sq lam) hnn
  rw [hlog, htr, htr2]
  linarith [hsumle, hcube]


theorem log_det_add_smul_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (hB : B.IsSymm) {ε : ℝ} (hε : 0 ≤ ε) (hpos : (A + ε • B).PosDef) :
    Real.log (A + ε • B).det
      ≤ Real.log A.det + ε * (A⁻¹ * B).trace
        - (ε ^ 2 / 2) * (A⁻¹ * B * A⁻¹ * B).trace
        + (ε ^ 3 / 3) * ((A⁻¹ * B * A⁻¹ * B).trace) ^ (3 / 2 : ℝ) := by
  classical
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hAsym : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hA'A : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
  let M : Matrix (Fin d) (Fin d) ℝ := A⁻¹ * B
  have hMM : M * M = A⁻¹ * B * A⁻¹ * B := by
    show (A⁻¹ * B) * (A⁻¹ * B) = A⁻¹ * B * A⁻¹ * B
    rw [← Matrix.mul_assoc]
  have hMfact : 1 + ε • M = A⁻¹ * (A + ε • B) := by
    rw [Matrix.mul_add, Matrix.mul_smul, hA'A]
  have hAM' : A * M = B := by
    show A * (A⁻¹ * B) = B
    rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hfact : A * (1 + ε • M) = A + ε • B := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hAM']
  have hposM : 0 < (1 + ε • M).det := by
    rw [hMfact, Matrix.det_mul]
    exact mul_pos hA.inv.det_pos hpos.det_pos
  -- weighted inner product space
  letI : SeminormedAddCommGroup (Fin d → ℝ) := Matrix.toSeminormedAddCommGroup A hA.posSemidef
  letI : NormedAddCommGroup (Fin d → ℝ) := Matrix.toNormedAddCommGroup A hA
  letI : InnerProductSpace ℝ (Fin d → ℝ) := Matrix.toInnerProductSpace A hA.posSemidef
  let T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Matrix.toLin' M
  have hdot : ∀ (C : Matrix (Fin d) (Fin d) ℝ) (u z : Fin d → ℝ),
      (C *ᵥ u) ⬝ᵥ z = u ⬝ᵥ (Cᵀ *ᵥ z) := by
    intro C u z
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  have hAM : Aᵀ * M = B := by
    show Aᵀ * (A⁻¹ * B) = B
    rw [← Matrix.mul_assoc, hAsym, hAA, Matrix.one_mul]
  have hTsymm : T.IsSymmetric := by
    intro x y
    show (A *ᵥ y) ⬝ᵥ (T x) = (A *ᵥ (T y)) ⬝ᵥ x
    have hTx : T x = M *ᵥ x := rfl
    have hTy : T y = M *ᵥ y := rfl
    rw [hTx, hTy]
    have e1 : (A *ᵥ y) ⬝ᵥ (M *ᵥ x) = y ⬝ᵥ (B *ᵥ x) := by
      rw [hdot A y (M *ᵥ x), Matrix.mulVec_mulVec, hAM]
    have e2 : (A *ᵥ (M *ᵥ y)) ⬝ᵥ x = y ⬝ᵥ (B *ᵥ x) := by
      rw [hdot A (M *ᵥ y) x, hdot M y (Aᵀ *ᵥ x), Matrix.mulVec_mulVec]
      have h2 : Mᵀ * Aᵀ = B := by rw [← Matrix.transpose_mul, hAM', hB]
      rw [h2]
    rw [e1, e2]
  have hTapply : ∀ x : Fin d → ℝ, (1 + ε • T) x = (1 + ε • M) *ᵥ x := by
    intro x
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    show x + ε • (Matrix.toLin' M x) = (1 + ε • M) *ᵥ x
    rw [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hinner : ∀ x : Fin d → ℝ, inner ℝ ((1 + ε • T) x) x = x ⬝ᵥ ((A + ε • B) *ᵥ x) := by
    intro x
    have e1 : Aᵀ * (1 + ε • M) = A + ε • B := by rw [hAsym, hfact]
    show (A *ᵥ x) ⬝ᵥ ((1 + ε • T) x) = x ⬝ᵥ ((A + ε • B) *ᵥ x)
    rw [hTapply x, hdot A x ((1 + ε • M) *ᵥ x), Matrix.mulVec_mulVec, e1]
  have hTpos : ∀ x : Fin d → ℝ, x ≠ 0 → 0 < inner ℝ ((1 + ε • T) x) x := by
    intro x hx
    rw [hinner x]
    simpa using Matrix.PosDef.dotProduct_mulVec_pos hpos hx
  have hop := log_det_one_add_smul_le_operator T hTsymm hε hTpos
  have hdtr : LinearMap.det (1 + ε • T) = (1 + ε • M).det := by
    have h1 : Matrix.toLin' (1 + ε • M) = 1 + ε • Matrix.toLin' M := by
      rw [map_add, map_smul, Matrix.toLin'_one]
      rfl
    rw [show (1 : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) + ε • T = Matrix.toLin' (1 + ε • M) from by
      rw [h1]]
    rw [LinearMap.det_toLin']
  have htr1 : LinearMap.trace ℝ (Fin d → ℝ) T = M.trace := by
    rw [show T = Matrix.toLin' M from rfl, Matrix.trace_toLin'_eq]
  have htr2 : LinearMap.trace ℝ (Fin d → ℝ) (T ∘ₗ T) = (M * M).trace := by
    rw [show T ∘ₗ T = (Matrix.toLin' M) ∘ₗ (Matrix.toLin' M) from rfl,
      ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq]
  have hlog_fact : Real.log (A + ε • B).det = Real.log A.det + Real.log (1 + ε • M).det := by
    rw [← hfact, Matrix.det_mul, Real.log_mul (ne_of_gt hA.det_pos) (ne_of_gt hposM)]
  calc Real.log (A + ε • B).det
      = Real.log A.det + Real.log (1 + ε • M).det := hlog_fact
    _ = Real.log A.det + Real.log (LinearMap.det (1 + ε • T)) := by rw [hdtr]
    _ ≤ Real.log A.det + (ε * LinearMap.trace ℝ (Fin d → ℝ) T
          - (ε ^ 2 / 2) * LinearMap.trace ℝ (Fin d → ℝ) (T ∘ₗ T)
          + (ε ^ 3 / 3) * (LinearMap.trace ℝ (Fin d → ℝ) (T ∘ₗ T)) ^ (3 / 2 : ℝ)) := by
        linarith [hop]
    _ = Real.log A.det + (ε * M.trace - (ε ^ 2 / 2) * (M * M).trace
          + (ε ^ 3 / 3) * ((M * M).trace) ^ (3 / 2 : ℝ)) := by rw [htr1, htr2]
    _ = Real.log A.det + ε * (A⁻¹ * B).trace - (ε ^ 2 / 2) * (A⁻¹ * B * A⁻¹ * B).trace
          + (ε ^ 3 / 3) * ((A⁻¹ * B * A⁻¹ * B).trace) ^ (3 / 2 : ℝ) := by
        rw [hMM, show M = A⁻¹ * B from rfl]
        ring

end Commons.LinearAlgebra.Matrix