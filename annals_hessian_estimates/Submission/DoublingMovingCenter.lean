/-
Corollary 2.5 of Shankar--Yuan: the doubling inequality with *moving centres*.

From Proposition 2.4 (the doubling inequality centred at the origin) and the rescalings
`x ↦ a • u (b • x + y)` with `a * b^2 = 1` we obtain, uniformly in the centre `y ∈ ball 0 (1/3)`
and in the radius `r ∈ (0, 4/3)`,

  `sup_{ball 0 2} Δu ≤ C * sup_{ball y r} Δu`.

The proof follows the paper: iterate the doubling inequality along the radii
`r_k = (4/3) (4/5)^k`, using that `ball 0 1 ⊆ ball 0 (4/3)` is mapped into any ball
`ball y (4/3)` (for `‖y‖ < 1/3`) and `ball y (5/3) ⊆ ball 0 2`.
-/
import Submission.Prop24Assembly
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_affine_apply
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_affine_apply
import Submission.Commons.Analysis.Sigma2.sigma2_sum_eq_coord_minor_sum
import Submission.Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Sigma2
open Commons.Analysis.InnerProductSpace
open Laplacian Metric
open scoped BigOperators RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- A fixed orthonormal basis of `ℝ⁴`, indexed by `Fin 4`. -/
noncomputable def stdB : OrthonormalBasis (Fin 4) ℝ ℝ⁴ :=
  (stdOrthonormalBasis ℝ ℝ⁴).reindex (finCongr (by simp))

/-! ## `σ₂` in terms of the coordinate minors -/

private theorem sum_lt_eq_sum_ite {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ i < j, f i) = ∑ i : Fin n, (if i < j then f i else 0) := by
  show ∑ i ∈ Finset.Iio j, f i = _
  rw [show Finset.Iio j = Finset.univ.filter (fun x => x < j) from by
        ext x; simp [Finset.mem_Iio], Finset.sum_filter]

/-- `σ₂` of a symmetric operator is the sum of the `2 × 2` coordinate minors in any
orthonormal basis. -/
theorem sigma2_eq_coord_minor (T : ℝ⁴ →L[ℝ] ℝ⁴) (hT : T.IsSymmetric)
    (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) :
    σ₂ T = ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ - ⟪T (v i), v j⟫ ^ 2) else 0 := by
  rw [HessianEstimates.σ₂, dif_pos hT]
  rw [show (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i < j,
        hT.eigenvalues rfl i * hT.eigenvalues rfl j)
      = (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
          if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) from
        Finset.sum_congr rfl (fun j _ => sum_lt_eq_sum_ite _ j)]
  rw [sigma2_eigen_eq_trace_invariants hT, coord_minor_sum_eq_trace_invariants hT v]

/-! ## Scaling identities for the rescaled function -/

/-- The affine substitution `x ↦ b • x + y` preserves `C^n`. -/
theorem contDiffOn_affine_comp {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {b : ℝ} {y : ℝ⁴}
    (hu : ContDiffOn ℝ 4 u s) :
    ContDiffOn ℝ 4 (fun x => u (b • x + y)) {x | b • x + y ∈ s} := by
  have h1 : ContDiffOn ℝ 4 (fun w => u w) s := hu
  have h2 : ContDiffOn ℝ 4 (fun x : ℝ⁴ => b • x + y) {x | b • x + y ∈ s} :=
    (((b • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).contDiff).add contDiff_const).contDiffOn
  exact h1.comp h2 (fun x hx => hx)

theorem contDiffOn_rescale {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {a b : ℝ} {y : ℝ⁴}
    (hu : ContDiffOn ℝ 4 u s) :
    ContDiffOn ℝ 4 (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} := by
  have h1 : ContDiffOn ℝ 4 (fun w => a * u w) s := hu.const_smul a
  have h2 : ContDiffOn ℝ 4 (fun x : ℝ⁴ => b • x + y) {x | b • x + y ∈ s} :=
    (((b • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).contDiff).add contDiff_const).contDiffOn
  exact h1.comp h2 (fun x hx => hx)

theorem fderiv_rescale {u : ℝ⁴ → ℝ} {a b : ℝ} {y z : ℝ⁴}
    (h : DifferentiableAt ℝ u (b • z + y)) :
    fderiv ℝ (fun x => a * u (b • x + y)) z = (a * b) • fderiv ℝ u (b • z + y) := by
  simpa using fderiv_affine_apply (u := u) (a := a) (b := b) (y := y) (x := z) h

theorem iteratedFDeriv_two_rescale {u : ℝ⁴ → ℝ} {a b : ℝ} {y z : ℝ⁴}
    (hu : ContDiffAt ℝ 2 u (b • z + y)) (m : Fin 2 → ℝ⁴) :
    (iteratedFDeriv ℝ 2 (fun x => a * u (b • x + y)) z) m
      = a * b ^ 2 * (iteratedFDeriv ℝ 2 u (b • z + y)) m :=
  iteratedFDeriv_two_affine_apply (u := u) (a := a) (b := b) (y := y) (x := z) hu m

/-- The Laplacian under the rescaling `x ↦ a * u (b • x + y)`. -/
theorem laplacian_rescale {u : ℝ⁴ → ℝ} {a b : ℝ} {y z : ℝ⁴}
    (hu : ContDiffAt ℝ 2 u (b • z + y)) :
    (Δ fun x => a * u (b • x + y)) z = a * b ^ 2 * (Δ u) (b • z + y) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (fun x => a * u (b • x + y)) (stdOrthonormalBasis ℝ ℝ⁴),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u (stdOrthonormalBasis ℝ ℝ⁴)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [iteratedFDeriv_two_rescale hu]



/-- The `σ₂` of the Hessian is invariant under the rescaling `x ↦ a • u (b • x + y)` when
`a * b^2 = 1` (which is exactly the normalisation under which `Δ` is preserved). -/
theorem sigma2_rescale {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {a b : ℝ} {y z : ℝ⁴}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 2 u s) (hzy : b • z + y ∈ s) (hab : a * b ^ 2 = 1) :
    σ₂ (H (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} z) = σ₂ (H u s (b • z + y)) := by
  have hs' : IsOpen {x | b • x + y ∈ s} :=
    hs.preimage (((b • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).continuous).add continuous_const)
  have hz' : z ∈ {x | b • x + y ∈ s} := hzy
  have hv : ContDiffOn ℝ 2 (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} :=
    (hu.const_smul a).comp
      ((((b • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).contDiff).add contDiff_const).contDiffOn)
      (fun x hx => hx)
  have huAt : ContDiffAt ℝ 2 u (b • z + y) := hu.contDiffAt (hs.mem_nhds hzy)
  have hcoord : ∀ i j : Fin 4,
      ⟪H (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} z (stdB i), stdB j⟫
        = ⟪H u s (b • z + y) (stdB i), stdB j⟫ := by
    intro i j
    simp only [HessianEstimates.H]
    rw [hessianWithin_apply_second_partial stdB hs' hz' hv i j,
      hessianWithin_apply_second_partial stdB hs hzy hu i j]
    change (iteratedFDeriv ℝ 2 (fun x => a * u (b • x + y)) z) ![stdB i, stdB j]
      = (iteratedFDeriv ℝ 2 u (b • z + y)) ![stdB i, stdB j]
    rw [iteratedFDeriv_two_rescale (a := a) (b := b) (y := y) huAt, hab, one_mul]
  have hHv : (H (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} z).IsSymmetric :=
    isSymmetric_hessianWithin hs' hz' hv
  have hHu : (H u s (b • z + y)).IsSymmetric := isSymmetric_hessianWithin hs hzy hu
  have hsum_eq : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪H (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} z (stdB i), stdB i⟫
            * ⟪H (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} z (stdB j), stdB j⟫
          - ⟪H (fun x => a * u (b • x + y)) {x | b • x + y ∈ s} z (stdB i), stdB j⟫ ^ 2)
        else 0)
      = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪H u s (b • z + y) (stdB i), stdB i⟫ * ⟪H u s (b • z + y) (stdB j), stdB j⟫
          - ⟪H u s (b • z + y) (stdB i), stdB j⟫ ^ 2) else 0) := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij, hcoord i i, hcoord j j, hcoord i j]
    · rw [if_neg hij, if_neg hij]
  rw [sigma2_eq_coord_minor _ hHv stdB, hsum_eq,
    ← sigma2_eq_coord_minor _ hHu stdB]

/- ## Auxiliary order facts for `sSup` -/

theorem sSup_image_mono {f : ℝ⁴ → ℝ} {A B : Set ℝ⁴} (hAB : A ⊆ B) (hne : A.Nonempty)
    (hBdd : BddAbove (f '' B)) : sSup (f '' A) ≤ sSup (f '' B) := by
  refine csSup_le (hne.image f) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact le_csSup hBdd ⟨a, hAB ha, rfl⟩

theorem image_affine_ball {f : ℝ⁴ → ℝ} {b : ℝ} (hb : 0 < b) (y : ℝ⁴) (R : ℝ) :
    (fun z => f (b • z + y)) '' ball 0 R = f '' ball y (b * R) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨b • z + y, ?_, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [sub_zero] at hz
    have h1 : ‖b • z + y - y‖ = b * ‖z‖ := by
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    rw [h1]; nlinarith
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(1 / b) • (u - y), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
      rw [sub_zero]
      have h1 : ‖(1 / b) • (u - y)‖ = (1 / b) * ‖u - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [h1]
      have h2 : (1 / b) * ‖u - y‖ < (1 / b) * (b * R) := mul_lt_mul_of_pos_left hu (by positivity)
      have h3 : (1 / b) * (b * R) = R := by field_simp
      linarith
    · show f (b • ((1 / b) • (u - y)) + y) = f u
      congr 1
      rw [smul_smul, mul_one_div_cancel (ne_of_gt hb), one_smul, sub_add_cancel]

/-! ## Corollary 2.5: the doubling inequality with moving centres -/

theorem doubling_step {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hsub : closedBall 0 3 ⊆ s)
    (hu : ContDiffOn ℝ 4 u s) (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {Γ : ℝ} (hΓ : 4 ≤ Γ)
    (huΓ : ∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4)
    (hdΓ : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4)
    {b : ℝ} (hb0 : 0 < b) (hb45 : b ≤ 4 / 5) {y : ℝ⁴} (hy : ‖y‖ < 1 / 3) {Γb : ℝ}
    (hΓb : max 4 ((1 / b ^ 2) * (Γ - 4) + 4) ≤ Γb) :
    sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (5 / 3 * b))
      ≤ doublingConst * Real.exp (doublingConst * Γb ^ 2)
        * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3 * b)) := by
  have hble8 : b ≤ 8 / 9 := by linarith
  have hdcpos : 0 < doublingConst := by rw [doublingConst]; positivity
  -- the rescaled function
  let a : ℝ := 1 / b ^ 2
  have hab : a * b ^ 2 = 1 := by
    simp only [a]; field_simp
  let v : ℝ⁴ → ℝ := fun x => a * u (b • x + y)
  let s' : Set ℝ⁴ := {x | b • x + y ∈ s}
  have hs' : IsOpen s' := hs.preimage (((b • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).continuous).add continuous_const)
  have hvsmooth : ContDiffOn ℝ 4 v s' := contDiffOn_rescale (u := u) (a := a) (b := b) (y := y) hu
  have hs'c : closedBall 0 3 ⊆ s' := by
    intro x hx
    have hx3 : ‖x‖ ≤ 3 := by rw [mem_closedBall] at hx; simpa [dist_zero_right] using hx
    have : ‖b • x + y‖ ≤ 3 := by
      have h1 : ‖b • x + y‖ ≤ b * ‖x‖ + ‖y‖ := by
        calc ‖b • x + y‖ ≤ ‖b • x‖ + ‖y‖ := norm_add_le _ _
          _ = b * ‖x‖ + ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
      nlinarith
    exact hsub (by rwa [mem_closedBall, dist_zero_right])
  -- the rescaled function solves the same equation
  have hσ2v : ∀ z ∈ s', σ₂ (H v s' z) = 1 := by
    intro z hz
    have hzmem : b • z + y ∈ s := hz
    have huAt : ContDiffAt ℝ 2 u (b • z + y) :=
      (hu.of_le (by norm_num)).contDiffAt (hs.mem_nhds hzmem)
    have hHv : (H v s' z).IsSymmetric :=
      isSymmetric_hessianWithin hs' hz (hvsmooth.of_le (by norm_num))
    have hHu : (H u s (b • z + y)).IsSymmetric :=
      isSymmetric_hessianWithin hs hzmem (hu.of_le (by norm_num))
    have hcoord : ∀ i j : Fin 4, ⟪H v s' z (stdB i), stdB j⟫ = ⟪H u s (b • z + y) (stdB i), stdB j⟫ := by
      intro i j
      simp only [HessianEstimates.H]
      rw [hessianWithin_apply_second_partial stdB hs' hz (hvsmooth.of_le (by norm_num)) i j,
        hessianWithin_apply_second_partial stdB hs hzmem (hu.of_le (by norm_num)) i j]
      change (iteratedFDeriv ℝ 2 (fun x => a * u (b • x + y)) z) ![stdB i, stdB j]
        = (iteratedFDeriv ℝ 2 u (b • z + y)) ![stdB i, stdB j]
      rw [iteratedFDeriv_two_rescale huAt, hab, one_mul]
    have hsum_eq : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          (⟪H v s' z (stdB i), stdB i⟫ * ⟪H v s' z (stdB j), stdB j⟫
            - ⟪H v s' z (stdB i), stdB j⟫ ^ 2) else 0)
        = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          (⟪H u s (b • z + y) (stdB i), stdB i⟫ * ⟪H u s (b • z + y) (stdB j), stdB j⟫
            - ⟪H u s (b • z + y) (stdB i), stdB j⟫ ^ 2) else 0) := by
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
      by_cases hij : i < j
      · rw [if_pos hij, if_pos hij, hcoord i i, hcoord j j, hcoord i j]
      · rw [if_neg hij, if_neg hij]
    rw [sigma2_eq_coord_minor (H v s' z) hHv stdB, hsum_eq,
      ← sigma2_eq_coord_minor (H u s (b • z + y)) hHu stdB]
    exact hσ2 _ hzmem
  have hΔv : ∀ z ∈ s', 0 < (Δ v) z := by
    intro z hz
    have hzmem : b • z + y ∈ s := hz
    have huAt : ContDiffAt ℝ 2 u (b • z + y) :=
      (hu.of_le (by norm_num)).contDiffAt (hs.mem_nhds hzmem)
    have h := laplacian_rescale (u := u) (a := a) (b := b) (y := y) (z := z) huAt
    change (Δ fun x => a * u (b • x + y)) z = a * b ^ 2 * (Δ u) (b • z + y) at h
    rw [show v = fun x => a * u (b • x + y) from rfl, h, hab, one_mul]
    exact hΔ _ hzmem
  -- Gamma bounds for the rescaled function
  have hΓb4 : 4 ≤ Γb := le_trans (le_max_left _ _) hΓb
  have haeq : a * (Γ - 4) ≤ Γb - 4 := by
    have h1 : a * (Γ - 4) + 4 ≤ Γb := le_trans (le_max_right _ _) hΓb
    linarith
  have huΓv : ∀ z ∈ closedBall 0 3, |v z| ≤ Γb - 4 := by
    intro z hz
    have hzm : b • z + y ∈ s := hs'c hz
    have hzmem : b • z + y ∈ closedBall 0 3 := by
      have hx3 : ‖z‖ ≤ 3 := by rw [mem_closedBall] at hz; simpa [dist_zero_right] using hz
      have : ‖b • z + y‖ ≤ 3 := by
        have h1 : ‖b • z + y‖ ≤ b * ‖z‖ + ‖y‖ := by
          calc ‖b • z + y‖ ≤ ‖b • z‖ + ‖y‖ := norm_add_le _ _
            _ = b * ‖z‖ + ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
        nlinarith
      rwa [mem_closedBall, dist_zero_right]
    have h1 : |v z| = a * |u (b • z + y)| := by
      simp only [v, abs_mul, abs_of_pos (by positivity : (0:ℝ) < a)]
    rw [h1]
    have h2 : |u (b • z + y)| ≤ Γ - 4 := huΓ _ hzmem
    have h3 : a * (Γ - 4) ≤ Γb - 4 := haeq
    calc a * |u (b • z + y)| ≤ a * (Γ - 4) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Γb - 4 := h3
  have hdΓv : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ v z‖ ≤ Γb - 4 := by
    intro z hz
    have hzmem : b • z + y ∈ closedBall 0 3 := by
      have hx3 : ‖z‖ ≤ 3 := by rw [mem_closedBall] at hz; simpa [dist_zero_right] using hz
      have h1 : ‖b • z + y‖ ≤ b * ‖z‖ + ‖y‖ := by
        calc ‖b • z + y‖ ≤ ‖b • z‖ + ‖y‖ := norm_add_le _ _
          _ = b * ‖z‖ + ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
      rw [mem_closedBall, dist_zero_right]
      nlinarith
    have huAt : DifferentiableAt ℝ u (b • z + y) :=
      (hu.contDiffAt (hs.mem_nhds (hs'c hz))).differentiableAt (by norm_num)
    have h := fderiv_rescale (u := u) (a := a) (b := b) (y := y) (z := z) huAt
    change fderiv ℝ v z = (a * b) • fderiv ℝ u (b • z + y) at h
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < a * b)]
    have h2 : ‖fderiv ℝ u (b • z + y)‖ ≤ Γ - 4 := hdΓ _ hzmem
    have h4 : a * b * (Γ - 4) ≤ Γb - 4 := by
      have : a * b ≤ a := by
        have : b ≤ 1 := by linarith
        nlinarith [show (0:ℝ) < a by positivity]
      nlinarith [h2, show (0:ℝ) ≤ Γ - 4 by linarith]
    calc a * b * ‖fderiv ℝ u (b • z + y)‖ ≤ a * b * (Γ - 4) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Γb - 4 := h4
  -- apply the doubling inequality to the rescaled function
  have hdbl := doubling_inequality_const (u := v) (s := s') hs' hs'c hvsmooth hσ2v hΔv hΓb4 huΓv hdΓv
  -- convert to statements about `u`
  have hΔv_eq : ∀ z ∈ closedBall 0 3, (Δ v) z = (Δ u) (b • z + y) := by
    intro z hz
    have hzmem : b • z + y ∈ s := hs'c hz
    have huAt : ContDiffAt ℝ 2 u (b • z + y) :=
      (hu.of_le (by norm_num)).contDiffAt (hs.mem_nhds hzmem)
    have h := laplacian_rescale (u := u) (a := a) (b := b) (y := y) (z := z) huAt
    change (Δ fun x => a * u (b • x + y)) z = a * b ^ 2 * (Δ u) (b • z + y) at h
    rw [show v = fun x => a * u (b • x + y) from rfl, h, hab, one_mul]
  have hsub23 : ball (0:ℝ⁴) 2 ⊆ closedBall 0 3 := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hsub13 : ball (0:ℝ⁴) 1 ⊆ closedBall 0 3 := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hset2 : (fun z : ℝ⁴ => (Δ v) z) '' ball 0 2 = (fun z : ℝ⁴ => (Δ u) (b • z + y)) '' ball 0 2 :=
    Set.image_congr (fun z hz => hΔv_eq z (hsub23 hz))
  have hset1 : (fun z : ℝ⁴ => (Δ v) z) '' ball 0 1 = (fun z : ℝ⁴ => (Δ u) (b • z + y)) '' ball 0 1 :=
    Set.image_congr (fun z hz => hΔv_eq z (hsub13 hz))
  have himg2 : (fun z : ℝ⁴ => (Δ v) z) '' ball 0 2 = (fun z : ℝ⁴ => (Δ u) z) '' ball y (b * 2) := by
    rw [hset2]; exact image_affine_ball (f := fun w => (Δ u) w) hb0 y 2
  have himg1 : (fun z : ℝ⁴ => (Δ v) z) '' ball 0 1 = (fun z : ℝ⁴ => (Δ u) z) '' ball y (b * 1) := by
    rw [hset1]; exact image_affine_ball (f := fun w => (Δ u) w) hb0 y 1
  have hBdd : BddAbove ((fun z : ℝ⁴ => (Δ u) z) '' closedBall 0 3) :=
    (isCompact_closedBall (0:ℝ⁴) 3).bddAbove_image
      ((Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian hs
        (hu.of_le (by norm_num))).mono hsub)
  -- ball inclusions inside `closedBall 0 3`
  have hball2 : ball y (2 * b) ⊆ closedBall 0 3 := by
    intro w hw
    rw [mem_ball] at hw
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
      calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
    have h2 : ‖w - y‖ < 2 * b := by rwa [dist_eq_norm] at hw
    nlinarith
  have hball3 : ball y (4 / 3 * b) ⊆ closedBall 0 3 := by
    intro w hw
    rw [mem_ball] at hw
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
      calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
    have h2 : ‖w - y‖ < 4 / 3 * b := by rwa [dist_eq_norm] at hw
    nlinarith
  have hle2 : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (5 / 3 * b))
      ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (2 * b)) :=
    sSup_image_mono (fun w hw => by
        rw [mem_ball] at hw ⊢; nlinarith)
      ⟨y, by simp [mem_ball, hb0]⟩ (hBdd.mono (Set.image_mono hball2))
  have hsup2 : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (2 * b))
      ≤ doublingConst * Real.exp (doublingConst * Γb ^ 2)
        * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (b * 1)) := by
    have h5 : (fun z : ℝ⁴ => (Δ u) z) '' ball y (2 * b) = (fun z : ℝ⁴ => (Δ u) z) '' ball y (b * 2) := by
      rw [mul_comm]
    rw [h5, ← himg2, ← himg1]
    refine csSup_le ⟨(Δ v) 0, 0, by simp [mem_ball], rfl⟩ ?_
    rintro w ⟨z, hz, rfl⟩
    exact hdbl z hz
  have hle3 : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (b * 1))
      ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3 * b)) :=
    sSup_image_mono (fun w hw => by
        rw [mem_ball] at hw ⊢; nlinarith)
      ⟨y, by simp [mem_ball]; positivity⟩ (hBdd.mono (Set.image_mono hball3))
  have hle3' : doublingConst * Real.exp (doublingConst * Γb ^ 2)
        * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (b * 1))
      ≤ doublingConst * Real.exp (doublingConst * Γb ^ 2)
        * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3 * b)) :=
    mul_le_mul_of_nonneg_left hle3 (mul_nonneg (le_of_lt hdcpos) (le_of_lt (Real.exp_pos _)))
  linarith [hle2, hsup2, hle3']


theorem doubling_moving_center_const {Γ : ℝ} (hΓ : 4 ≤ Γ) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴), IsOpen s → closedBall 0 3 ⊆ s → ContDiffOn ℝ 4 u s →
        (∀ y ∈ s, σ₂ (H u s y) = 1) → (∀ y ∈ s, 0 < (Δ u) y) →
        (∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4) →
        (∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4) →
        ∀ y ∈ (ball 0 (1 / 3) : Set ℝ⁴),
        ∀ r : ℝ, δ ≤ r → r < 4 / 3 →
        ∀ z ∈ ball 0 2, (Δ u) z ≤ C * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y r) := by
  intro δ hδ
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 4 / 3 * (4 / 5 : ℝ) ^ K ≤ δ := by
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ * 3 / 4 by positivity)
      (by norm_num : (4 / 5 : ℝ) < 1)
    exact ⟨K, by linarith⟩
  have hdcpos : 0 < doublingConst := by rw [doublingConst]; positivity
  set A : ℝ := (5 / 4 : ℝ) ^ (2 * (K + 1)) with hAdef
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; exact one_le_pow₀ (by norm_num)
  set ΓK : ℝ := max 4 (A * (Γ - 4) + 4) with hΓKdef
  have hΓle : Γ ≤ ΓK := by
    rw [hΓKdef]
    have h : Γ ≤ A * (Γ - 4) + 4 := by nlinarith
    exact le_trans h (le_max_right _ _)
  set D : ℝ := doublingConst * Real.exp (doublingConst * ΓK ^ 2) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact mul_pos hdcpos (Real.exp_pos _)
  set Cc : ℝ := D ^ (K + 1) with hCcdef
  have hCcpos : 0 < Cc := by rw [hCcdef]; positivity
  refine ⟨Cc, hCcpos, ?_⟩
  intro u s hs hsub hu hσ2 hΔ huΓ hdΓ y hy r hrδ hr43 z hz
  have hBdd : BddAbove ((fun z : ℝ⁴ => (Δ u) z) '' closedBall 0 3) :=
    (isCompact_closedBall (0:ℝ⁴) 3).bddAbove_image
      ((Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian hs
        (hu.of_le (by norm_num))).mono hsub)
  have hy' : ‖y‖ < 1 / 3 := by simpa [mem_ball, dist_zero_right] using hy
  -- balls around `y` stay inside `closedBall 0 3`
  have hball_sub : ∀ R : ℝ, R ≤ 8 / 5 → ball y R ⊆ closedBall 0 3 := by
    intro R hR w hw
    rw [mem_ball] at hw
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
      calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
    have h2 : ‖w - y‖ < R := by rwa [dist_eq_norm] at hw
    nlinarith [norm_nonneg (w - y)]
  -- the single doubling step at a general radius
  have hstep : ∀ n : ℕ, (5 / 4 : ℝ) ^ (2 * (n + 1)) ≤ A →
      sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ n))
        ≤ D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ (n + 1))) := by
    intro n hAn
    have hb0 : (0 : ℝ) < (4 / 5 : ℝ) ^ (n + 1) := by positivity
    have hb45 : (4 / 5 : ℝ) ^ (n + 1) ≤ 4 / 5 := by
      rw [pow_succ]
      have h1 : (4 / 5 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hb2 : (1 : ℝ) / ((4 / 5 : ℝ) ^ (n + 1)) ^ 2 = ((5 / 4 : ℝ) ^ (n + 1)) ^ 2 := by
      rw [one_div, ← inv_pow, ← inv_pow, show (4 / 5 : ℝ)⁻¹ = 5 / 4 by norm_num]
    have hb3 : ((5 / 4 : ℝ) ^ (n + 1)) ^ 2 = (5 / 4 : ℝ) ^ (2 * (n + 1)) := by
      rw [← pow_mul]; ring_nf
    have hΓb : max 4 ((1 / ((4 / 5 : ℝ) ^ (n + 1)) ^ 2) * (Γ - 4) + 4) ≤ ΓK := by
      rw [hΓKdef, hb2, hb3]
      refine max_le (le_max_left _ _) ?_
      refine le_trans ?_ (le_max_right _ _)
      have h2 : (5 / 4 : ℝ) ^ (2 * (n + 1)) * (Γ - 4) ≤ A * (Γ - 4) :=
        mul_le_mul_of_nonneg_right hAn (by linarith)
      linarith
    have h := doubling_step (u := u) (s := s) (Γ := Γ) (b := (4 / 5 : ℝ) ^ (n + 1))
      (y := y) (Γb := ΓK) hs hsub hu hσ2 hΔ hΓ huΓ hdΓ hb0 hb45 hy' hΓb
    rw [show (5 / 3 : ℝ) * (4 / 5) ^ (n + 1) = (4 / 3) * (4 / 5) ^ n from by
      rw [pow_succ]; ring] at h
    rw [hDdef]
    exact h
  -- the chain of steps
  have hchain : ∀ k : ℕ, k ≤ K →
      sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3))
        ≤ D ^ k * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ k)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n ≤ K := Nat.le_of_succ_le hn
      have h1 := ih hn'
      have hAn : (5 / 4 : ℝ) ^ (2 * (n + 1)) ≤ A := by
        rw [hAdef]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5 / 4) (by omega)
      have h2 := hstep n hAn
      have h3 : D ^ n * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ n))
          ≤ D ^ n * (D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ (n + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (le_of_lt hDpos) n)
      calc sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3))
          ≤ D ^ n * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ n)) := h1
        _ ≤ D ^ n * (D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ (n + 1)))) := h3
        _ = D ^ (n + 1) * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ (n + 1))) := by ring
  -- the base step
  have hbase : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 2)
      ≤ D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3)) := by
    have hdbl := doubling_inequality_const hs hsub hu hσ2 hΔ hΓ huΓ hdΓ
    have h1 : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 2)
        ≤ doublingConst * Real.exp (doublingConst * Γ ^ 2)
          * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 1) := by
      refine csSup_le ⟨(Δ u) 0, 0, by simp [mem_ball], rfl⟩ ?_
      rintro w ⟨z', hz', rfl⟩
      exact hdbl z' hz'
    have h2 : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 1)
        ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3)) :=
      sSup_image_mono (fun w hw => by
          rw [mem_ball, dist_zero_right] at hw
          rw [mem_ball]
          have h3 := dist_triangle w 0 y
          rw [dist_zero_right, dist_zero_left] at h3
          linarith) ⟨0, by simp [mem_ball]⟩
        (hBdd.mono (Set.image_mono (hball_sub (4 / 3) (by norm_num))))
    have h4 : doublingConst * Real.exp (doublingConst * Γ ^ 2) ≤ D := by
      rw [hDdef]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt hdcpos)
      have h1 : Γ ^ 2 ≤ ΓK ^ 2 := by nlinarith [hΓle, hΓ]
      nlinarith [hdcpos, h1]
    have h5 : (0 : ℝ) ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 1) :=
      le_trans (le_of_lt (hΔ 0 (hsub (by simp [mem_closedBall]))))
        (le_csSup (hBdd.mono (Set.image_mono (fun w hw => by
            rw [mem_ball, dist_zero_right] at hw
            rw [mem_closedBall, dist_zero_right]
            linarith)))
          ⟨0, by simp [mem_ball], rfl⟩)
    calc sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 2)
        ≤ doublingConst * Real.exp (doublingConst * Γ ^ 2)
          * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 1) := h1
      _ ≤ D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 1) := mul_le_mul_of_nonneg_right h4 h5
      _ ≤ D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3)) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hDpos)
  have hchainK := hchain K le_rfl
  have hfin : sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ K))
      ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y r) := by
    have hKr : (4 / 3) * (4 / 5) ^ K ≤ r := le_trans hK hrδ
    refine sSup_image_mono (fun w hw => ?_) ⟨y, ?_⟩
      (hBdd.mono (Set.image_mono (hball_sub r (by linarith))))
    · exact mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw) hKr)
    · exact mem_ball.mpr (by rw [dist_self]; positivity)
  have hzz : (Δ u) z ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 2) :=
    le_csSup (hBdd.mono (Set.image_mono (fun w hw => by
        rw [mem_ball, dist_zero_right] at hw
        rw [mem_closedBall, dist_zero_right]
        linarith))) ⟨z, hz, rfl⟩
  calc (Δ u) z ≤ sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball 0 2) := hzz
    _ ≤ D * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y (4 / 3)) := hbase
    _ ≤ D * (D ^ K * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y ((4 / 3) * (4 / 5) ^ K))) :=
        mul_le_mul_of_nonneg_left hchainK (le_of_lt hDpos)
    _ ≤ D * (D ^ K * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y r)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfin (pow_nonneg (le_of_lt hDpos) K)) (le_of_lt hDpos)
    _ = Cc * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y r) := by rw [hCcdef]; ring

/-- **Corollary 2.5 (moving centres)**, stated with the sequence of solutions and domains
quantified inside: for `‖y‖ < 1/3` and `r ∈ [δ, 4/3)`,
`sup_{ball 0 2} Δu ≤ C * sup_{ball y r} Δu`. -/
theorem doubling_moving_center {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hsub : closedBall 0 3 ⊆ s) (hu : ContDiffOn ℝ 4 u s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {Γ : ℝ} (hΓ : 4 ≤ Γ)
    (huΓ : ∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4)
    (hdΓ : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ y ∈ (ball 0 (1 / 3) : Set ℝ⁴),
      ∀ r : ℝ, δ ≤ r → r < 4 / 3 →
      ∀ z ∈ ball 0 2, (Δ u) z ≤ C * sSup ((fun z : ℝ⁴ => (Δ u) z) '' ball y r) := by
  intro δ hδ
  obtain ⟨C, hC, h⟩ := doubling_moving_center_const (Γ := Γ) hΓ δ hδ
  exact ⟨C, hC, h u s hs hsub hu hσ2 hΔ huΓ hdΓ⟩

end Submission
