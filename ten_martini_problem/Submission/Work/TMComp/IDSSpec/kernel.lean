import Mathlib
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# `kernel`: finitely supported approximate eigenvectors of the almost Mathieu operator

The statement (`Work.TMComp.IDSSpec.kernel`) is the Weyl-criterion input used by the
proof of AJ (2.11) (`P_IDSSpectrum`): every real point `E` of the spectrum of an almost
Mathieu operator `H = H_{α,λ,0}` admits unit, finitely supported vectors `φ` with
`‖(H - E) φ‖ ≤ ε` in `ℓ²(ℤ)`.

The mathematical content is the classical fact that *the spectrum of a self-adjoint
operator is contained in its approximate point spectrum*.  The proof splits into

* `selfAdjoint_of_coeffs`: a Jacobi operator with real, bounded coefficients is
  self-adjoint — proved by comparing the two sides of `⟪H x, y⟫ = ⟪x, H y⟫` through the
  shift-plus-diagonal decomposition `H x = S₊ x + S₋ x + D x` and `lp.inner_eq_tsum`;
* `amo_selfAdjoint`: specialisation to `IsAlmostMathieuOperator α λ 0`;
* `Work.TMC7Core.Scale.fs_approx` (already in the workspace): a self-adjoint operator has
  finitely supported approximate eigenvectors at every real spectral point;
* the assembly below: normalising the approximate eigenvector, which preserves finite
  support, and rewriting the `ℓ²`-norm of `(H - E) u` as the coordinate sum in the
  statement.
-/

open scoped BigOperators
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.IDSSpec

/-! ## 1. Shifts on `ℓ²(ℤ)` and their membership in `ℓ²` -/

lemma memℓp_shiftZ (x : EllTwo) (k : ℤ) : Memℓp (fun n : ℤ => x (n + k)) 2 := by
  have hx : Summable (fun n : ℤ => ‖x n‖ ^ ((2 : ENNReal).toReal)) :=
    (lp.memℓp x).summable (by norm_num)
  refine memℓp_gen ?_
  have h := (Equiv.summable_iff (Equiv.addRight k)).2 hx
  simpa only [Function.comp_def, Equiv.coe_addRight] using h

/-- The backward shift `(S₊ x) n = x (n+1)`. -/
noncomputable def shF (x : EllTwo) : EllTwo :=
  ⟨fun n : ℤ => x (n + 1), memℓp_shiftZ x 1⟩

/-- The forward shift `(S₋ x) n = x (n-1)`. -/
noncomputable def shB (x : EllTwo) : EllTwo :=
  ⟨fun n : ℤ => x (n + (-1)), memℓp_shiftZ x (-1)⟩

lemma shF_apply (x : EllTwo) (n : ℤ) : shF x n = x (n + 1) := rfl

lemma shB_apply (x : EllTwo) (n : ℤ) : shB x n = x (n - 1) := by
  show x (n + -1) = x (n - 1)
  rw [sub_eq_add_neg]

/-! ## 2. Jacobi operators with real coefficients are self-adjoint -/

/-- A bounded operator on `ℓ²(ℤ)` given by a shift-plus-diagonal coordinate formula
with *real* bounded coefficients is self-adjoint. -/
theorem selfAdjoint_of_coeffs {c : ℤ → ℂ} (hstar : ∀ n, star (c n) = c n)
    (K : ℝ) (hK : ∀ n, ‖c n‖ ≤ K)
    {H : EllTwo →L[ℂ] EllTwo}
    (hH : ∀ (u : EllTwo) (n : ℤ), H u n = u (n + 1) + u (n - 1) + c n * u n) :
    IsSelfAdjoint H := by
  have hmemd : ∀ x : EllTwo, Memℓp (fun n : ℤ => c n * x n) 2 := by
    intro x
    have hK' : Memℓp (fun n : ℤ => K * ‖x n‖) 2 := (lp.memℓp x).norm.const_mul K
    refine Memℓp.mono hK' (fun n => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _)
  let D : EllTwo → EllTwo := fun x => ⟨fun n => c n * x n, hmemd x⟩
  have hD : ∀ x n, D x n = c n * x n := fun x n => rfl
  have hdecomp : ∀ x : EllTwo, H x = shF x + shB x + D x := by
    intro x
    apply lp.ext
    funext n
    rw [lp.coeFn_add, lp.coeFn_add, Pi.add_apply, Pi.add_apply, hH x n,
      shF_apply, shB_apply, hD]
  have key : ∀ x y : EllTwo, inner ℂ (H x) y = inner ℂ x (H y) := by
    intro x y
    have e1 : inner ℂ (shF x) y = inner ℂ x (shB y) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      simp_rw [shF_apply, shB_apply]
      rw [← Equiv.tsum_eq (Equiv.addRight (1:ℤ)) (fun m : ℤ => inner ℂ (x m) (y (m-1)))]
      simp only [Equiv.coe_addRight]
      simp
    have e2 : inner ℂ (shB x) y = inner ℂ x (shF y) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      simp_rw [shF_apply, shB_apply]
      rw [← Equiv.tsum_eq (Equiv.addRight (1:ℤ)) (fun m : ℤ => inner ℂ (x (m-1)) (y m))]
      simp only [Equiv.coe_addRight]
      simp
    have e3 : inner ℂ (D x) y = inner ℂ x (D y) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      simp_rw [hD]
      apply tsum_congr
      intro n
      have h1 : inner ℂ (c n * x n) (y n) = star (c n) * inner ℂ (x n) (y n) :=
        inner_smul_left (x n) (y n) (c n)
      have h2 : inner ℂ (x n) (c n * y n) = c n * inner ℂ (x n) (y n) :=
        inner_smul_right (x n) (y n) (c n)
      rw [h1, h2, hstar n]
    rw [hdecomp x, hdecomp y, inner_add_left, inner_add_left, inner_add_right, inner_add_right]
    rw [e1, e2, e3]
    ring
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (key x y).symm

/-- The almost Mathieu operator with real coupling and phase `0` is self-adjoint. -/
theorem amo_selfAdjoint (α lam : ℝ) {H : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam 0 H) : IsSelfAdjoint H := by
  refine selfAdjoint_of_coeffs (c := fun n : ℤ =>
      ((2 * lam * Real.cos (2 * Real.pi * (0 + (n:ℝ) * α)) : ℝ) : ℂ)) ?_ (2 * |lam|) ?_ ?_
  · intro n
    show star ((↑(2 * lam * Real.cos (2 * Real.pi * (0 + (n:ℝ) * α))) : ℂ)) = _
    rw [Complex.star_def, Complex.conj_ofReal]
  · intro n
    have h1 : |Real.cos (2 * Real.pi * (0 + (n:ℝ) * α))| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |2 * lam * Real.cos (2 * Real.pi * (0 + (n:ℝ) * α))|
        = 2 * |lam| * |Real.cos (2 * Real.pi * (0 + (n:ℝ) * α))| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [Complex.norm_real, Real.norm_eq_abs, h2]
    nlinarith [abs_nonneg lam, h1]
  · intro u n
    simpa using hH u n

/-- `amoAct` is linear in its sequence argument. -/
lemma amoAct_smul (α lam : ℝ) (c : ℂ) (f : ℤ → ℂ) (n : ℤ) :
    Work.TMContract.amoAct α lam 0 (fun k => c * f k) n
      = c * Work.TMContract.amoAct α lam 0 f n := by
  simp only [Work.TMContract.amoAct, Work.TMContract.amoPot]
  ring

/-! ## 3. The `kernel` statement -/

theorem kernel (α lam : ℝ) (H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)
    (hH : LeanEval.Analysis.TenMartini.IsAlmostMathieuOperator α lam 0 H)
    (E : ℝ) (hE : (E : ℂ) ∈ spectrum ℂ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∃ φ : ℤ → ℂ, (∀ m : ℤ, R ≤ m.natAbs → φ m = 0) ∧
      (∑' m : ℤ, ‖φ m‖ ^ 2) = 1 ∧
      (∑' m : ℤ, ‖Work.TMContract.amoAct α lam 0 φ m - (E : ℂ) * φ m‖ ^ 2) ≤ ε ^ 2 := by
  have hsa : IsSelfAdjoint H := amo_selfAdjoint α lam hH
  obtain ⟨u, hu_ne, ⟨s, hs⟩, hu_approx⟩ :=
    Work.TMC7Core.Scale.fs_approx H hsa E hE (δ := ε) hε
  set φf : ℤ → ℂ := fun m => ((‖u‖)⁻¹ : ℂ) * (u : ℤ → ℂ) m with hφf
  -- `ℓ²`-norm of a sequence as the sum of squares of its coordinates
  have norm_sq_eq (w : EllTwo) : ‖w‖ ^ 2 = ∑' m : ℤ, ‖(w : ℤ → ℂ) m‖ ^ 2 := by
    have hp : (0:ℝ) < (2:ENNReal).toReal := by norm_num
    have hto : (2:ENNReal).toReal = 2 := by norm_num
    have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) hp w
    rw [hto] at h
    simp_rw [Real.rpow_two] at h
    exact h
  set v : EllTwo := (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u with hv
  have hvnorm : ‖v‖ < ε * ‖u‖ := by rw [hv]; exact hu_approx
  -- coordinates of `(H - E) u`
  have hvs : ∀ m : ℤ, v m =
      Work.TMContract.amoAct α lam 0 (fun k => (u : ℤ → ℂ) k) m - (E:ℂ) * (u:ℤ→ℂ) m := by
    intro m
    rw [hv, sub_apply, ContinuousLinearMap.algebraMap_apply]
    rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [show (H u) m = Work.TMContract.amoAct α lam 0 (fun k => (u : ℤ → ℂ) k) m from
      (Work.TMContract.isAMO_iff α lam 0 H).1 hH u m]
  -- scaling of the eigenvalue equation
  have hpt : ∀ m : ℤ, Work.TMContract.amoAct α lam 0 φf m - (E:ℂ) * φf m
      = ((‖u‖)⁻¹ : ℂ) * v m := by
    intro m
    have h1 : Work.TMContract.amoAct α lam 0 φf m
        = ((‖u‖)⁻¹ : ℂ) * Work.TMContract.amoAct α lam 0 (fun k => (u : ℤ → ℂ) k) m := by
      rw [hφf]
      exact amoAct_smul α lam _ _ m
    rw [h1, hvs m]
    rw [hφf]
    ring
  have hφnorm : ∑' m : ℤ, ‖φf m‖ ^ 2 = 1 := by
    have hstep : ∀ m : ℤ, ‖φf m‖ ^ 2 = (‖u‖⁻¹)^2 * ‖(u : ℤ → ℂ) m‖ ^ 2 := by
      intro m
      simp only [hφf]
      rw [norm_mul]
      have hc : ‖(((‖u‖ : ℝ) : ℂ))⁻¹‖ = ‖u‖⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rw [hc, mul_pow]
    simp_rw [hstep]
    rw [tsum_mul_left, ← norm_sq_eq u, ← mul_pow,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu_ne), one_pow]
  have herr : ∑' m : ℤ, ‖Work.TMContract.amoAct α lam 0 φf m - (E : ℂ) * φf m‖ ^ 2
      = (‖u‖⁻¹)^2 * ‖v‖ ^ 2 := by
    simp_rw [hpt]
    have hstep : ∀ m : ℤ, ‖((‖u‖)⁻¹ : ℂ) * v m‖ ^ 2 = (‖u‖⁻¹)^2 * ‖v m‖ ^ 2 := by
      intro m
      rw [norm_mul]
      have hc : ‖(((‖u‖ : ℝ) : ℂ))⁻¹‖ = ‖u‖⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rw [hc, mul_pow]
    simp_rw [hstep]
    rw [tsum_mul_left, ← norm_sq_eq v]
  refine ⟨s.sup (fun i : ℤ => i.natAbs) + 1, φf, ?_, hφnorm, ?_⟩
  · intro m hm
    simp only [hφf]
    have hms : m ∉ s := by
      intro hmem
      have h1 : m.natAbs ≤ s.sup (fun i : ℤ => i.natAbs) := Finset.le_sup hmem
      omega
    rw [hs m hms, mul_zero]
  · rw [herr]
    calc (‖u‖⁻¹)^2 * ‖v‖ ^ 2 ≤ (‖u‖⁻¹)^2 * (ε * ‖u‖) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) hvnorm.le 2
      _ = ε ^ 2 := by
          rw [mul_pow, ← mul_assoc, inv_pow]
          field_simp

end Work.TMComp.IDSSpec
