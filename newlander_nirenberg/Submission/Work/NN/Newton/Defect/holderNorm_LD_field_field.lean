import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds

/-!
# `C^{0,α}`-bound for the coordinate of `(DA_z X_z)(Y_z)`

Let `A : ℂⁿ → (ℂⁿ →L[ℝ] ℂⁿ)` be a `C¹`-field of `ℝ`-linear maps on a set `P`, whose coefficient
functions `z ↦ A z w j` (`‖w‖ ≤ 1`) have `C^{1,α}`-norm at most `a` (`CVBound`), and let
`X, Y` be vector fields of `C^{0,α}`-norm at most `a` (`VecHolder`).  This file proves that the
scalar field

  `z ↦ λ_l ((fderiv ℝ A z (X z)) (Y z))`

has `C^{0,α}`-norm at most `4 a²` on `P`.  The `4` is `1 + 3`: the pointwise bound is `a²`
(the derivative of the coefficient is bounded by `a`, and `‖Y z‖ ≤ a`), while the Hölder
seminorm is bounded by `2 a² + a³ ≤ 3 a²`.

The main technical device is the continuous linear functional
`Psi A l z w : v ↦ λ_l ((fderiv ℝ A z v) w)`, which is linear in `w` (so that differences of
the frozen coefficient direction can be pushed inside) and which equals
`fderiv ℝ (fun z' => A z' w l) z` (so that the `CVBound` hypotheses, which are stated for the
coefficient functions, apply to it).
-/

namespace Work.NN.Newton.Defect

open scoped NNReal ENNReal
open Set

noncomputable section

/-- The functional `v ↦ λ_l ((fderiv ℝ A z v) w)`, i.e. the `l`-th coordinate of the second
argument of the derivative of `A` at `z` evaluated at `v`, with the evaluation point `w` held
fixed.  It is defined through the continuous linear structure so that it is manifestly linear
in `w`. -/
def Psi {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l : Fin n)
    (z w : Work.NN.Core.Cn n) : Work.NN.Core.Cn n →L[ℝ] ℂ :=
  (Work.NN.Newton.lamC l).comp
    ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w).comp (fderiv ℝ A z))

@[simp] lemma Psi_apply {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (z w v : Work.NN.Core.Cn n) :
    Psi A l z w v = Work.NN.Newton.lamC l ((fderiv ℝ A z v) w) := by
  simp only [Psi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

lemma Psi_smul {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (z : Work.NN.Core.Cn n) (c : ℝ) (w : Work.NN.Core.Cn n) :
    Psi A l z (c • w) = c • Psi A l z w := by
  simp only [Psi]
  rw [map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

lemma Psi_add {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (z : Work.NN.Core.Cn n) (w₁ w₂ : Work.NN.Core.Cn n) :
    Psi A l z (w₁ + w₂) = Psi A l z w₁ + Psi A l z w₂ := by
  simp only [Psi]
  rw [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

lemma Psi_neg {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (z w : Work.NN.Core.Cn n) : Psi A l z (-w) = -Psi A l z w := by
  simp only [Psi]
  rw [map_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg]

lemma Psi_sub {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (z : Work.NN.Core.Cn n) (w₁ w₂ : Work.NN.Core.Cn n) :
    Psi A l z (w₁ - w₂) = Psi A l z w₁ - Psi A l z w₂ := by
  rw [sub_eq_add_neg, Psi_add, Psi_neg, sub_eq_add_neg]

/-- `Psi A l z w` is the derivative of the coefficient function `z' ↦ A z' w l`. -/
lemma Psi_eq_fderiv {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) {z : Work.NN.Core.Cn n} (h : DifferentiableAt ℝ A z) (w : Work.NN.Core.Cn n) :
    Psi A l z w = fderiv ℝ (fun z' => A z' w l) z := by
  have h1 : HasFDerivAt (fun z' => A z' w)
      ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w).comp (fderiv ℝ A z)) z :=
    (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w).hasFDerivAt.comp z h.hasFDerivAt
  have h3 := (Work.NN.Newton.lamC l).hasFDerivAt.comp z h1
  have hfun : (fun z' => A z' w l) = (⇑(Work.NN.Newton.lamC l) ∘ fun z' => A z' w) := by
    funext z'
    simp only [Function.comp_apply, Work.NN.Newton.lamC_apply]
  rw [hfun, h3.fderiv]
  rfl

/-- **The `C^{0,α}` bound.**  Under `CVBound` for `A` and `VecHolder` for `X` and `Y`, the
scalar field `z ↦ λ_l ((fderiv ℝ A z (X z)) (Y z))` has `C^{0,α}`-norm at most `4 a²`. -/
theorem holderNorm_zero_vecHolder_LD {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a : ℝ} (hα0 : 0 < α) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {P : Set (Work.NN.Core.Cn n)} (hPopen : IsOpen P)
    (hAc : ContDiffOn ℝ 1 A P)
    (hA : Work.NN.Newton.CVBound A α a P)
    {X Y : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hX : Work.NN.Final.VecHolder X α a P) (hY : Work.NN.Final.VecHolder Y α a P) (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) (Y z))) P
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
  -- `A` is differentiable at every point of the open set `P`
  have hAdiff : ∀ z ∈ P, DifferentiableAt ℝ A z := by
    intro z hz
    exact (hAc.contDiffAt (hPopen.mem_nhds hz)).differentiableAt (by simp)
  -- the `CVBound` hypothesis, specialised to the coordinate `l`
  have hP : ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 →
      Work.CR.Flat.holderNorm 1 α (fun z => A z w l) P ≤ ENNReal.ofReal a :=
    fun w hw => hA w hw l
  -- unit-ball bound for `Psi`
  have hPsi_unit : ∀ z ∈ P, ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ‖Psi A l z w‖ ≤ a := by
    intro z hz w hw
    rw [Psi_eq_fderiv A l (hAdiff z hz) w]
    have hb := hP w hw
    have h1 : ‖iteratedFDerivWithin ℝ 1 (fun z' => A z' w l) P z‖ ≤ a :=
      Work.NN.Newton.norm_iteratedFDerivWithin_le_of_holderNorm_le ha0 hb le_rfl hz
    have hz1 : iteratedFDerivWithin ℝ 1 (fun z' => A z' w l) P z
        = iteratedFDeriv ℝ 1 (fun z' => A z' w l) z :=
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := P) 1 hPopen hz
    rw [hz1, norm_iteratedFDeriv_one] at h1
    exact h1
  -- homogeneous form (linearity in `w` plus the unit-ball bound)
  have hPsi_le : ∀ z ∈ P, ∀ w : Work.NN.Core.Cn n, ‖Psi A l z w‖ ≤ a * ‖w‖ := by
    intro z hz w
    rcases eq_or_ne w 0 with hw | hw
    · subst hw
      have h0 : Psi A l z 0 = 0 := by
        ext v
        simp
      rw [h0]; simp
    · have hw' : w = (‖w‖ : ℝ) • ((‖w‖)⁻¹ • w) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
      have hnorm : ‖(‖w‖)⁻¹ • w‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
      have hstep : Psi A l z w = (‖w‖ : ℝ) • Psi A l z ((‖w‖)⁻¹ • w) := by
        rw [← Psi_smul, ← hw']
      calc ‖Psi A l z w‖
          = ‖(‖w‖ : ℝ) • Psi A l z ((‖w‖)⁻¹ • w)‖ := by rw [hstep]
        _ = ‖w‖ * ‖Psi A l z ((‖w‖)⁻¹ • w)‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]
        _ ≤ ‖w‖ * a :=
              mul_le_mul_of_nonneg_left (hPsi_unit z hz _ (le_of_eq hnorm)) (norm_nonneg w)
        _ = a * ‖w‖ := by ring
  -- Hölder bound for `Psi` in the base point, uniformly in the frozen direction
  have hPsi_hold : ∀ x ∈ P, ∀ y ∈ P, ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 →
      ‖Psi A l x w - Psi A l y w‖ ≤ a * ‖x - y‖ ^ α := by
    intro x hx y hy w hw
    rw [Psi_eq_fderiv A l (hAdiff x hx) w, Psi_eq_fderiv A l (hAdiff y hy) w]
    have hb := hP w hw
    have h1 : ‖iteratedFDerivWithin ℝ 1 (fun z' => A z' w l) P x
        - iteratedFDerivWithin ℝ 1 (fun z' => A z' w l) P y‖ ≤ a * ‖x - y‖ ^ α :=
      Work.NN.Newton.norm_sub_iteratedFDerivWithin_le_of_holderNorm_le hα0 ha0 hb le_rfl hx hy
    rwa [Work.NN.Core.Lev.norm_iteratedFDerivWithin_one_sub_eq hPopen (fun z' => A z' w l)
      hx hy] at h1
  -- replace the goal function by `z ↦ Psi A l z (Y z) (X z)`
  have hg : (fun z => Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) (Y z)))
      = (fun z => Psi A l z (Y z) (X z)) := by
    funext z
    rw [Psi_apply]
  rw [hg]
  -- sup bound
  have hsup : Work.CR.Flat.iterDerivNorm 0 (fun z => Psi A l z (Y z) (X z)) P
      ≤ ENNReal.ofReal (a ^ 2) := by
    refine iSup₂_le fun z hz => ?_
    rw [norm_iteratedFDerivWithin_zero]
    refine ENNReal.ofReal_le_ofReal ?_
    have hXz : ‖X z‖ ≤ a := hX.1 z hz
    have hYz : ‖Y z‖ ≤ 1 := le_trans (hY.1 z hz) ha1
    calc ‖Psi A l z (Y z) (X z)‖ ≤ ‖Psi A l z (Y z)‖ * ‖X z‖ :=
          (Psi A l z (Y z)).le_opNorm (X z)
      _ ≤ a * a := mul_le_mul (hPsi_unit z hz (Y z) hYz) hXz (norm_nonneg _) ha0
      _ = a ^ 2 := by ring
  -- Hölder seminorm
  have hsem : Work.CR.Flat.holderSeminorm 0 α (fun z => Psi A l z (Y z) (X z)) P
      ≤ ENNReal.ofReal (3 * a ^ 2) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.Lev.norm_iteratedFDerivWithin_zero_sub_eq
      (fun z => Psi A l z (Y z) (X z)) P x y]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
    rw [div_le_iff₀ hdαpos]
    have hXx : ‖X x‖ ≤ a := hX.1 x hx
    have hYx : ‖Y x‖ ≤ 1 := le_trans (hY.1 x hx) ha1
    have hYy1 : ‖Y y‖ ≤ 1 := le_trans (hY.1 y hy) ha1
    have ht : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hdec : Psi A l x (Y x) (X x) - Psi A l y (Y y) (X y)
        = ((Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)
            + ((Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x)))
          + ((Psi A l y (Y y)) (X x) - (Psi A l y (Y y)) (X y)) := by
      abel
    have h1 : ‖(Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)‖
        ≤ a ^ 2 * ‖x - y‖ ^ α := by
      rw [← sub_apply]
      calc ‖(Psi A l x (Y x) - Psi A l y (Y x)) (X x)‖
          ≤ ‖Psi A l x (Y x) - Psi A l y (Y x)‖ * ‖X x‖ :=
            (Psi A l x (Y x) - Psi A l y (Y x)).le_opNorm (X x)
        _ ≤ (a * ‖x - y‖ ^ α) * a :=
              mul_le_mul (hPsi_hold x hx y hy (Y x) hYx) hXx (norm_nonneg _) (mul_nonneg ha0 ht)
        _ = a ^ 2 * ‖x - y‖ ^ α := by ring
    have h2 : ‖(Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x)‖
        ≤ a ^ 3 * ‖x - y‖ ^ α := by
      have hmid : (Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x)
          = Psi A l y (Y x - Y y) (X x) := by
        rw [← sub_apply, Psi_sub]
      rw [hmid]
      calc ‖Psi A l y (Y x - Y y) (X x)‖
          ≤ ‖Psi A l y (Y x - Y y)‖ * ‖X x‖ := (Psi A l y (Y x - Y y)).le_opNorm (X x)
        _ ≤ (a * ‖Y x - Y y‖) * a :=
              mul_le_mul (hPsi_le y hy (Y x - Y y)) hXx (norm_nonneg _)
                (mul_nonneg ha0 (norm_nonneg _))
        _ ≤ (a * (a * ‖x - y‖ ^ α)) * a :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hY.2 x hx y hy) ha0) ha0
        _ = a ^ 3 * ‖x - y‖ ^ α := by ring
    have h3 : ‖(Psi A l y (Y y)) (X x) - (Psi A l y (Y y)) (X y)‖
        ≤ a ^ 2 * ‖x - y‖ ^ α := by
      rw [← ContinuousLinearMap.map_sub]
      calc ‖Psi A l y (Y y) (X x - X y)‖
          ≤ ‖Psi A l y (Y y)‖ * ‖X x - X y‖ := (Psi A l y (Y y)).le_opNorm (X x - X y)
        _ ≤ a * (a * ‖x - y‖ ^ α) :=
              mul_le_mul (hPsi_unit y hy (Y y) hYy1) (hX.2 x hx y hy) (norm_nonneg _) ha0
        _ = a ^ 2 * ‖x - y‖ ^ α := by ring
    have h3le : a ^ 3 ≤ a ^ 2 := by nlinarith [ha0, ha1, sq_nonneg a]
    have hAB : ‖(Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)
          + ((Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x))‖
        ≤ (a ^ 2 + a ^ 3) * ‖x - y‖ ^ α := by
      calc ‖(Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)
              + ((Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x))‖
          ≤ ‖(Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)‖
              + ‖(Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x)‖ := norm_add_le _ _
        _ ≤ a ^ 2 * ‖x - y‖ ^ α + a ^ 3 * ‖x - y‖ ^ α := add_le_add h1 h2
        _ = (a ^ 2 + a ^ 3) * ‖x - y‖ ^ α := by ring
    rw [hdec]
    calc ‖(Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)
              + ((Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x))
            + ((Psi A l y (Y y)) (X x) - (Psi A l y (Y y)) (X y))‖
        ≤ ‖(Psi A l x (Y x)) (X x) - (Psi A l y (Y x)) (X x)
              + ((Psi A l y (Y x)) (X x) - (Psi A l y (Y y)) (X x))‖
            + ‖(Psi A l y (Y y)) (X x) - (Psi A l y (Y y)) (X y)‖ := norm_add_le _ _
      _ ≤ (a ^ 2 + a ^ 3) * ‖x - y‖ ^ α + a ^ 2 * ‖x - y‖ ^ α := add_le_add hAB h3
      _ = (2 * a ^ 2 + a ^ 3) * ‖x - y‖ ^ α := by ring
      _ ≤ 3 * a ^ 2 * ‖x - y‖ ^ α := by
            apply mul_le_mul_of_nonneg_right _ ht
            linarith
  -- assemble the two pieces
  have hsum : Work.CR.Flat.holderNorm 0 α (fun z => Psi A l z (Y z) (X z)) P
      = Work.CR.Flat.iterDerivNorm 0 (fun z => Psi A l z (Y z) (X z)) P
        + Work.CR.Flat.holderSeminorm 0 α (fun z => Psi A l z (Y z) (X z)) P := by
    simp [Work.CR.Flat.holderNorm]
  rw [hsum]
  refine le_trans (add_le_add hsup hsem) (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem holderNorm_LD_field_field {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r))
    {X Y : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hX : Work.NN.Final.VecHolder X α a (Work.NN.Newton.polydiscR n r))
    (hY : Work.NN.Final.VecHolder Y α a (Work.NN.Newton.polydiscR n r)) (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) (Y z)))
        (Work.NN.Newton.polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
  holderNorm_zero_vecHolder_LD (P := Work.NN.Newton.polydiscR n r) A hα0 ha0 ha1
    (Work.NN.Newton.isOpen_polydiscR n r) hAc hA hX hY l

end

end Work.NN.Newton.Defect
