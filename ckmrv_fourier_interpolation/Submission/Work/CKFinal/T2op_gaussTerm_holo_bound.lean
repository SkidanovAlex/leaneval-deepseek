import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Asymptotics.abs_pow_mul_exp_le
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.CKFinal.differentiable_gaussPoly_eval
import Submission.Work.CKFinal.iteratedDeriv_gaussTerm_scale_bound

noncomputable section
open scoped Manifold Topology

namespace Work.CKFinal

/-- Entire functions of the form `τ ↦ G (τ : ℂ)` are holomorphic on `ℍ`. -/
lemma t2gb_mdiff_coe_comp {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => G (τ : ℂ)) :=
  hG.mdifferentiable.comp UpperHalfPlane.mdifferentiable_coe

/-- `s ↦ gaussTerm σ s` is `C^∞`. -/
lemma t2gb_contDiff_gaussTerm (σ : UpperHalfPlane) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun s : ℝ => Work.Kernels.gaussTerm σ s) := by
  have h1 : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun s : ℝ => ((s : ℂ)) ^ 2) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : WithTop ℕ∞))).pow 2
  have h2 : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun s : ℝ => Real.pi * Complex.I * ((σ : ℂ)) * (s : ℂ) ^ 2) :=
    contDiff_const.mul h1
  exact Complex.contDiff_exp.comp (by simpa only [Work.Kernels.gaussTerm] using h2)

/-- The linearity decomposition of `∂_r^l` of the `(T-I)²`-defect of the Gaussian. -/
lemma t2gb_eq (l : ℕ) (τ : UpperHalfPlane) (r : ℝ) :
    iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ) r
      = iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s) r
        - 2 * iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r
        + iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r := by
  have hA : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s) r :=
    (t2gb_contDiff_gaussTerm ((2 : ℝ) +ᵥ τ)).contDiffAt.of_le le_top
  have hB : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r :=
    (t2gb_contDiff_gaussTerm ((1 : ℝ) +ᵥ τ)).contDiffAt.of_le le_top
  have hC : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => Work.Kernels.gaussTerm τ s) r :=
    (t2gb_contDiff_gaussTerm τ).contDiffAt.of_le le_top
  have hBB : ContDiffAt ℝ (l : ℕ∞)
      (fun s : ℝ => 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r :=
    (contDiff_const (c := (2 : ℂ))).contDiffAt.mul hB
  have hfun : (fun s : ℝ =>
        Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ)
      = (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s
          - 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s + Work.Kernels.gaussTerm τ s) := by
    funext s; rfl
  have step1 : iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s
        - 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s + Work.Kernels.gaussTerm τ s) r
      = iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s
          - 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r
        + iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r :=
    iteratedDeriv_add
      (f := fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s
        - 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s)
      (g := fun s : ℝ => Work.Kernels.gaussTerm τ s) (x := r) (hA.sub hBB) hC
  have step2 : iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s
          - 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r
      = iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s) r
        - iteratedDeriv l (fun s : ℝ => 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r :=
    iteratedDeriv_sub (f := fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s)
      (g := fun s : ℝ => 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) (x := r) hA hBB
  have step3 : iteratedDeriv l (fun s : ℝ => 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r
      = 2 * iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r :=
    iteratedDeriv_const_mul (f := fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s)
      (n := l) (x := r) 2 hB
  rw [hfun, step1, step2, step3]

/-- Holomorphy in `τ` of `∂_r^l e^{πi(τ+c)r²}`. -/
lemma t2gb_mdiff_gterm_vadd
    (hP : ∀ (l : ℕ) (y : ℂ), Differentiable ℂ (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).eval y))
    (l : ℕ) (c : ℝ) (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm (c +ᵥ τ) s) r) := by
  have hfun : ∀ τ : UpperHalfPlane, (fun s : ℝ => Work.Kernels.gaussTerm (c +ᵥ τ) s)
      = (fun s : ℝ =>
          Complex.exp (-((-(Real.pi * Complex.I * ((c : ℂ) + (τ : ℂ)))) * (s : ℂ) ^ 2))) := by
    intro τ
    funext s
    simp only [Work.Kernels.gaussTerm, UpperHalfPlane.coe_vadd]
    congr 1
    ring
  have key : (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm (c +ᵥ τ) s) r)
      = fun τ : UpperHalfPlane =>
          (Work.Asymptotics.gaussPoly (-(Real.pi * Complex.I * ((c : ℂ) + (τ : ℂ)))) l).eval (r : ℂ)
            * Complex.exp (Real.pi * Complex.I * ((c : ℂ) + (τ : ℂ)) * (r : ℂ) ^ 2) := by
    funext τ
    rw [hfun τ, Work.Asymptotics.iteratedDeriv_gaussPoly]
    beta_reduce
    rw [show -(-(Real.pi * Complex.I * ((c : ℂ) + (τ : ℂ))) * (r : ℂ) ^ 2)
        = Real.pi * Complex.I * ((c : ℂ) + (τ : ℂ)) * (r : ℂ) ^ 2 from by ring]
  rw [key]
  have hφ : Differentiable ℂ (fun z : ℂ => -((Real.pi * Complex.I) * ((c : ℂ) + z))) := by
    have h : Differentiable ℂ (fun z : ℂ => (Real.pi * Complex.I) * ((c : ℂ) + z)) :=
      ((differentiable_const (c := (c : ℂ))).add differentiable_id).const_mul (Real.pi * Complex.I)
    exact h.neg
  have h1 : Differentiable ℂ (fun z : ℂ =>
      (Work.Asymptotics.gaussPoly (-((Real.pi * Complex.I) * ((c : ℂ) + z))) l).eval (r : ℂ)) :=
    (hP l (r : ℂ)).comp hφ
  have h2 : Differentiable ℂ (fun z : ℂ =>
      Complex.exp (Real.pi * Complex.I * ((c : ℂ) + z) * (r : ℂ) ^ 2)) := by fun_prop
  exact t2gb_mdiff_coe_comp (G := fun z : ℂ =>
    (Work.Asymptotics.gaussPoly (-((Real.pi * Complex.I) * ((c : ℂ) + z))) l).eval (r : ℂ)
      * Complex.exp (Real.pi * Complex.I * ((c : ℂ) + z) * (r : ℂ) ^ 2)) (h1.mul h2)

/-- First conjunct of the target, given the polynomial crux. -/
lemma t2gb_holo
    (hP : ∀ (l : ℕ) (y : ℂ), Differentiable ℂ (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).eval y))
    (l : ℕ) (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ) r) := by
  have heq : (fun τ : UpperHalfPlane => iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ) r)
      = fun τ : UpperHalfPlane => iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s) r
          - 2 * iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r
          + iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r := by
    funext τ; exact t2gb_eq l τ r
  rw [heq]
  have hA := t2gb_mdiff_gterm_vadd hP l 2 r
  have hB := t2gb_mdiff_gterm_vadd hP l 1 r
  have hC0 := t2gb_mdiff_gterm_vadd hP l 0 r
  have hCe : (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((0 : ℝ) +ᵥ τ) s) r)
      = fun τ : UpperHalfPlane => iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r := by
    funext τ
    congr 1
    funext s
    rw [zero_vadd]
  rw [hCe] at hC0
  show MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
    ((fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s) r)
      - (2 : ℂ) • (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r)
      + (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r))
  exact (hA.sub (hB.const_smul 2)).add hC0

/-- The scale of a translate is controlled by the scale. -/
lemma t2gb_scale_vadd_le (c : ℝ) (τ : UpperHalfPlane) :
    Work.Kernels.scale (c +ᵥ τ) ≤ (1 + |c|) * Work.Kernels.scale τ := by
  have h1 : ((c +ᵥ τ : UpperHalfPlane) : ℂ) = (c : ℂ) + (τ : ℂ) := UpperHalfPlane.coe_vadd c τ
  have h2 : (c +ᵥ τ : UpperHalfPlane).im = τ.im := UpperHalfPlane.vadd_im c τ
  simp only [Work.Kernels.scale, h2, h1]
  have h3 : ‖(c : ℂ) + (τ : ℂ)‖ ≤ ‖(τ : ℂ)‖ + |c| := by
    have h4 : ‖(c : ℂ) + (τ : ℂ)‖ ≤ ‖(c : ℂ)‖ + ‖(τ : ℂ)‖ := norm_add_le _ _
    have h5 : ‖(c : ℂ)‖ = |c| := by simp
    linarith
  have hs : (1 : ℝ) ≤ 1 + τ.im⁻¹ + ‖(τ : ℂ)‖ := by
    have h6 := inv_nonneg.mpr τ.im_pos.le
    have h7 := norm_nonneg (τ : ℂ)
    linarith
  nlinarith [h3, hs, abs_nonneg c, inv_nonneg.mpr τ.im_pos.le, norm_nonneg (τ : ℂ)]

/-- Second conjunct of the target, given the bound for the plain Gaussian. -/
lemma t2gb_bnd
    (hBnd : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N)
    (k l : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := hBnd k l
  refine ⟨C * (3 ^ N + 2 * 2 ^ N + 1), N, ?_, hN, fun τ r => ?_⟩
  · have h3N : (0 : ℝ) ≤ (3 : ℝ) ^ N := Real.rpow_nonneg (by norm_num) N
    have h2N : (0 : ℝ) ≤ (2 : ℝ) ^ N := Real.rpow_nonneg (by norm_num) N
    nlinarith [hC, h3N, h2N]
  · have e1 := hb ((2 : ℝ) +ᵥ τ) r
    have e2 := hb ((1 : ℝ) +ᵥ τ) r
    have e3 := hb τ r
    have s1 : (Work.Kernels.scale ((2 : ℝ) +ᵥ τ)) ^ N
        ≤ (3 : ℝ) ^ N * (Work.Kernels.scale τ) ^ N := by
      have h := t2gb_scale_vadd_le 2 τ
      rw [show (1 : ℝ) + |(2 : ℝ)| = 3 by norm_num] at h
      refine le_trans (Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos _)) h hN) ?_
      rw [Real.mul_rpow (by norm_num) (le_of_lt (Work.Kernels.scale_pos τ))]
    have s2 : (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N
        ≤ (2 : ℝ) ^ N * (Work.Kernels.scale τ) ^ N := by
      have h := t2gb_scale_vadd_le 1 τ
      rw [show (1 : ℝ) + |(1 : ℝ)| = 2 by norm_num] at h
      refine le_trans (Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos _)) h hN) ?_
      rw [Real.mul_rpow (by norm_num) (le_of_lt (Work.Kernels.scale_pos τ))]
    have hA : (0 : ℝ) ≤ |r| ^ k := pow_nonneg (abs_nonneg r) k
    rw [t2gb_eq l τ r]
    set X := iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) s) r with hX
    set Y := iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) s) r with hY
    set Z := iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r with hZ
    set S := (Work.Kernels.scale τ) ^ N with hS
    have hX' : |r| ^ k * ‖X‖ ≤ C * (3 ^ N * S) :=
      le_trans e1 (mul_le_mul_of_nonneg_left s1 hC)
    have hY' : |r| ^ k * ‖Y‖ ≤ C * (2 ^ N * S) :=
      le_trans e2 (mul_le_mul_of_nonneg_left s2 hC)
    have hZ' : |r| ^ k * ‖Z‖ ≤ C * S := e3
    have hnorm : ‖X - 2 * Y + Z‖ ≤ ‖X‖ + 2 * ‖Y‖ + ‖Z‖ := by
      have ha : ‖X - 2 * Y + Z‖ ≤ ‖X - 2 * Y‖ + ‖Z‖ := norm_add_le _ _
      have hb2 : ‖X - 2 * Y‖ ≤ ‖X‖ + ‖2 * Y‖ := norm_sub_le _ _
      have hc : ‖(2 : ℂ) * Y‖ = 2 * ‖Y‖ := by rw [norm_mul]; norm_num
      linarith
    calc |r| ^ k * ‖X - 2 * Y + Z‖
        ≤ |r| ^ k * (‖X‖ + 2 * ‖Y‖ + ‖Z‖) := mul_le_mul_of_nonneg_left hnorm hA
      _ = |r| ^ k * ‖X‖ + 2 * (|r| ^ k * ‖Y‖) + |r| ^ k * ‖Z‖ := by ring
      _ ≤ C * (3 ^ N * S) + 2 * (C * (2 ^ N * S)) + C * S := by linarith
      _ = C * (3 ^ N + 2 * 2 ^ N + 1) * S := by ring

/-- The target statement, conditional on the two delegated pieces. -/
theorem T2op_gaussTerm_holo_bound_cond
    (hP : ∀ (l : ℕ) (y : ℂ), Differentiable ℂ (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).eval y))
    (hBnd : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N) :
    (∀ l : ℕ, ∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ s) τ) r)) ∧
    (∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ s) τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N) :=
  ⟨fun l r => t2gb_holo hP l r, fun k l => t2gb_bnd hBnd k l⟩

/-- **The `(T-I)²`-defect of the Gaussian, holomorphic in `τ` and of moderate growth.**

Written in the paper's notation: for every order `l` in the radial variable `r`, the function
`τ ↦ ∂_r^l [T2op(gaussTerm · r)](τ)` is holomorphic on `ℍ`; and for every pair of orders `k l`
there are constants `0 ≤ C`, `0 ≤ N` with
`|r|^k ‖∂_r^l [T2op(gaussTerm · r)](τ)‖ ≤ C (scale τ)^N` for all `τ : ℍ`, `r : ℝ`. -/
theorem T2op_gaussTerm_holo_bound :
    (∀ l : ℕ, ∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ => Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ s) τ) r)) ∧
    (∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ s) τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N) :=
  T2op_gaussTerm_holo_bound_cond Work.CKFinal.differentiable_gaussPoly_eval
    Work.CKFinal.iteratedDeriv_gaussTerm_scale_bound

end Work.CKFinal
