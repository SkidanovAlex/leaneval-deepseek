import Submission.FUP.LocalizeCell
import Submission.FUP.LensChange

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The per-cell localisation in the frequency plane (Han–Schlag `prop:locddim`, one cell)

This module assembles `Submission.FUP.cell_cartan_exp` (the Cartan two-constants estimate on the
unit polydisc) with the geometry of the lens map (`Submission.FUP.LensChange`) to obtain the
**per-cell** estimate

`∫_C ‖g‖² ≤ C₀ · S^{2(1-κ)} · (∫_I ‖g‖²)^κ`

where `C = c + [-1,1]^d` is a cell of the `2ℤ^d` grid, `I ⊆ C` the localisation cube, `g` is
band-limited (with entire extension `F`), `S := sup_{𝔻̄^d} |F(c + η·Φ(w))|` and `κ = (1+L)^{-d}`,
`L = 2δ⁻³log(2/δ) + δ⁻²log(2e/H)`.

The two change-of-variables steps are:

* (i) `∫_{c+ηΦ(mid)} ‖g‖² ≤ (ηλmax)^d ∫_{mid} ‖g(c+ηΦ(w))‖² dw`  (`λmax = 4q/(πε)`), with
  `mid = [-τ,τ]^d`, `τ = 1-3δ`; this is the *upper* bound for the cell (the cell is contained in
  the image of the mid box, which is why `ηφ(τ) ≥ 1`);
* (ii) `∫_E ‖g(c+ηΦ(w))‖²dw ≤ (λmin η)^{-d} ∫_{(I-c)/η} ‖g(c+ηz)‖²dz` with `λmin = (1-ε)q/π`,
  where `E := Φ⁻¹((I-c)/η)`; this is the *upper* bound for the localisation cube.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The real per-cell lens map `w ↦ c + η • Φ(w)`. -/
noncomputable def PsiR (q ε η : ℝ) (c : Fin d → ℝ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun j => c j + η * phiLens q ε (w j)

/-- The complex per-cell lens map (the one for which `G_n(w) = g(PsiCLens … w)` is holomorphic). -/
noncomputable def PsiCLens (q ε η : ℝ) (c : Fin d → ℝ) (w : Fin d → ℂ) : Fin d → ℂ :=
  fun j => (c j : ℂ) + (η : ℂ) * lensMap q ε (w j)

/-- On real points inside `(-1,1)^d` the two per-cell maps agree. -/
lemma PsiC_ofReal {q ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {c : Fin d → ℝ} {w : Fin d → ℝ}
    (hw : ∀ j, |w j| < 1) :
    PsiCLens (d := d) q ε η c (fun j => (w j : ℂ)) = fun j => (PsiR q ε η c w j : ℂ) := by
  funext j
  simp only [PsiCLens, PsiR, lensMap_ofReal_eq q ε (w j) (hw j) (le_of_lt hε0) hε1]
  push_cast
  ring

/-- The complex per-cell map composed with an entire `g` is holomorphic on the closed polydisc. -/
lemma analyticOnNhd_PsiC_comp {q ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {g : (Fin d → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) (c : Fin d → ℝ) :
    AnalyticOnNhd ℂ (fun w : Fin d → ℂ => g (PsiCLens (d := d) q ε η c w))
      (Metric.closedBall 0 1) := by
  have h := analyticOnNhd_lensComp (d := d) (q := q) (ε := ε) hε0 hε1 (g := g) hg
    (c := fun j : Fin d => (c j : ℂ)) (η := ((η : ℝ) : ℂ))
  have hfun : (fun w : Fin d → ℂ => g (PsiCLens (d := d) q ε η c w))
      = fun w : Fin d → ℂ => g (fun j => (c j : ℂ) + (η : ℂ) * lensMap q ε (w j)) := by
    funext w
    rfl
  rw [hfun]
  exact h

/-- The complex per-cell map applied to a real point in `(-1,1)^d` is the real one. -/
lemma PsiC_apply_ofReal {q ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {c : Fin d → ℝ}
    {w : Fin d → ℝ} (hw : ∀ j, |w j| < 1) (j : Fin d) :
    PsiCLens (d := d) q ε η c (fun j => (w j : ℂ)) j = (PsiR q ε η c w j : ℂ) := by
  simp only [PsiCLens, PsiR, lensMap_ofReal_eq q ε (w j) (hw j) (le_of_lt hε0) hε1]
  push_cast
  ring

/-! ### Elementary properties of the real lens map -/

lemma phiLens_zero (q ε : ℝ) : phiLens q ε 0 = 0 := by
  simp [phiLens]

lemma phiLens_deriv_nonneg {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 ≤ (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(0:ℝ))^2)) := by
  have h : 0 < (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(0:ℝ))^2)) :=
    phiLens_deriv_pos hq hε0 hε1 (by norm_num)
  exact le_of_lt h

/-- The real lens map is odd on `(-1,1)`. -/
lemma phiLens_neg {q ε x : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hx : |x| < 1) :
    phiLens q ε (-x) = -phiLens q ε x := by
  rw [phiLens, phiLens]
  have hlt := abs_lt.mp hx
  have h1 : (1 - (1-ε) * x) ≠ 0 := by
    intro h; nlinarith [hlt.1, hlt.2, hε0, hε1, h]
  have h2 : (1 + (1-ε) * x) ≠ 0 := by
    intro h; nlinarith [hlt.1, hlt.2, hε0, hε1, h]
  have h : (1 + (1-ε) * (-x)) / (1 - (1-ε) * (-x))
      = ((1 + (1-ε) * x) / (1 - (1-ε) * x))⁻¹ := by
    rw [inv_div]
    ring_nf
  rw [h, Real.log_inv]
  ring

/-- `phiLens q ε` is continuous on every interval strictly inside `(-1,1)`. -/
lemma continuousOn_phiLens {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ContinuousOn (phiLens q ε) (Set.Icc a b) := by
  intro x hx
  refine ((hasDerivAt_phiLens hq hε0 hε1 ?_).continuousAt).continuousWithinAt
  rw [abs_lt]
  exact ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩

/-- The image of an interval under the real lens map. -/
lemma image_phiLens_Icc {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    phiLens q ε '' Set.Icc a b = Set.Icc (phiLens q ε a) (phiLens q ε b) := by
  refine ContinuousOn.image_Icc_of_monotoneOn hab (continuousOn_phiLens hq hε0 hε1 ha hb) ?_
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (phiLens_strictMonoOn hq hε0 hε1
      ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩
      ⟨by linarith [hy.1, ha], by linarith [hy.2, hb]⟩ hlt)

/-- **Surjectivity of the real lens map on the interval.**  Every `z` with `|z| ≤ φ(τ)` is the
image of some `w ∈ [-τ,τ]` (`0 ≤ τ < 1`). -/
lemma exists_phiLens_eq {q ε τ z : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hz : |z| ≤ phiLens q ε τ) :
    ∃ w ∈ Set.Icc (-τ) τ, phiLens q ε w = z := by
  have hne : phiLens q ε (-τ) = -phiLens q ε τ :=
    phiLens_neg hε0 hε1 (by rw [abs_of_nonneg hτ0]; linarith)
  have himg := image_phiLens_Icc (q := q) (ε := ε) hq hε0 hε1 (a := -τ) (b := τ)
    (by linarith) (by linarith) (by linarith)
  rw [hne] at himg
  have hz' : z ∈ Set.Icc (-(phiLens q ε τ)) (phiLens q ε τ) := by
    rw [Set.mem_Icc, ← abs_le]
    exact hz
  rw [← himg] at hz'
  exact hz'

/-! ### The Fréchet derivative of the per-cell lens map -/

/-- The derivative of `PsiR q ε η c` (a `def` so that it can be mentioned in statements). -/
noncomputable def dPsiR (q ε η : ℝ) (c : Fin d → ℝ) (x : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  (η • ContinuousLinearMap.id ℝ (Fin d → ℝ)).comp (dPhiLens q ε x)

lemma hasFDerivAt_PsiR {q ε η : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {c x : Fin d → ℝ} (hx : ∀ j, |x j| < 1) :
    HasFDerivAt (PsiR (d := d) q ε η c) (dPsiR (d := d) q ε η c x) x := by
  have h1 : HasFDerivAt (fun y : Fin d → ℝ => fun j => phiLens q ε (y j))
      (dPhiLens (d := d) q ε x) x := hasFDerivAt_PhiLens hq hε0 hε1 hx
  have h2 : HasFDerivAt (fun z : Fin d → ℝ => c + η • z)
      (η • ContinuousLinearMap.id ℝ (Fin d → ℝ)) (fun j => phiLens q ε (x j)) :=
    (ContinuousLinearMap.hasFDerivAt (η • ContinuousLinearMap.id ℝ (Fin d → ℝ))).const_add c
  have h := h2.comp x h1
  have hfun : PsiR (d := d) q ε η c
      = (fun z : Fin d → ℝ => c + η • z) ∘ (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) := by
    funext w
    rfl
  rw [hfun, dPsiR]
  exact h

lemma det_dPsiR (q ε η : ℝ) (c x : Fin d → ℝ) :
    (dPsiR (d := d) q ε η c x).det
      = η^d * ∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) := by
  change LinearMap.det ((dPsiR (d := d) q ε η c x) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = _
  rw [dPsiR]
  rw [show (((η • ContinuousLinearMap.id ℝ (Fin d → ℝ)).comp (dPhiLens q ε x)) :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      = ((η • ContinuousLinearMap.id ℝ (Fin d → ℝ)) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) ∘ₗ
        (dPhiLens q ε x : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) from rfl]
  rw [LinearMap.det_comp,
    show LinearMap.det ((dPhiLens q ε x) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      = (dPhiLens q ε x).det from rfl, det_dPhiLens]
  congr 1
  change LinearMap.det ((η • ContinuousLinearMap.id ℝ (Fin d → ℝ)) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = η ^ d
  rw [show ((η • ContinuousLinearMap.id ℝ (Fin d → ℝ)) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      = η • (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) from rfl]
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma PsiR_injOn {q ε η : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    {c : Fin d → ℝ} {E : Set (Fin d → ℝ)} (hEsub : ∀ x ∈ E, ∀ j, |x j| < 1) :
    InjOn (PsiR (d := d) q ε η c) E := by
  intro x hx y hy hxy
  have hPhi : (fun j => phiLens q ε (x j)) = (fun j => phiLens q ε (y j)) := by
    funext j
    have := congrFun hxy j
    simp only [PsiR, Pi.add_apply] at this
    exact mul_left_cancel₀ (ne_of_gt hη) (add_left_cancel this)
  funext j
  have hx1 := abs_lt.mp (hEsub x hx j)
  have hy1 := abs_lt.mp (hEsub y hy j)
  exact phiLens_injOn hq hε0 hε1 ⟨le_of_lt hx1.1, le_of_lt hx1.2⟩
    ⟨le_of_lt hy1.1, le_of_lt hy1.2⟩ (congrFun hPhi j)

/-- **The upper change-of-variables bound for the per-cell lens map.** -/
theorem integral_image_PsiR_le {q ε η : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hη : 0 < η) {c : Fin d → ℝ} {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-1 : ℝ) 1))
    {G : (Fin d → ℝ) → ℝ} (hG : ∀ x, 0 ≤ G x)
    (hint : IntegrableOn (fun w : Fin d → ℝ => G (PsiR q ε η c w)) E volume) :
    ∫ y in PsiR (d := d) q ε η c '' E, G y
      ≤ (η * (4*q/(Real.pi*ε)))^d * ∫ w in E, G (PsiR q ε η c w) := by
  have hlt : ∀ x ∈ E, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hEsub hx j (Set.mem_univ j)
    rw [Set.mem_Ioo] at h
    rw [abs_lt]
    exact ⟨h.1, h.2⟩
  have hderiv : ∀ x ∈ E, HasFDerivWithinAt (PsiR (d := d) q ε η c) (dPsiR q ε η c x) E x :=
    fun x hx => (hasFDerivAt_PsiR hq hε0 (by linarith) (hlt x hx)).hasFDerivWithinAt
  have hinj : InjOn (PsiR (d := d) q ε η c) E :=
    PsiR_injOn hq hε0 (by linarith) hη hlt
  have hkey : ∀ x ∈ E, |(dPsiR (d := d) q ε η c x).det| • G (PsiR q ε η c x)
      ≤ ((η * (4*q/(Real.pi*ε)))^d) * G (PsiR q ε η c x) := by
    intro x hx
    have hc : ∀ j : Fin d, 0 ≤ (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
      fun j => le_of_lt (phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j))
    have hc' : ∀ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) ≤ 4*q/(Real.pi*ε) :=
      fun j => (phiLens_deriv_bounds hq hε0 hε1 (hlt x hx j)).2
    have hprod : (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))))
        ≤ (4*q/(Real.pi*ε))^d := by
      calc (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))))
          ≤ ∏ _j : Fin d, (4*q/(Real.pi*ε)) :=
            Finset.prod_le_prod (fun j _ => hc j) (fun j _ => hc' j)
        _ = (4*q/(Real.pi*ε))^d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hdet : |(dPsiR (d := d) q ε η c x).det| ≤ (η * (4*q/(Real.pi*ε)))^d := by
      rw [det_dPsiR, abs_of_nonneg (mul_nonneg (by positivity)
        (Finset.prod_nonneg (fun j _ => hc j)))]
      calc η^d * (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))))
          ≤ η^d * (4*q/(Real.pi*ε))^d := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (η * (4*q/(Real.pi*ε)))^d := by rw [mul_pow]
    rw [smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hdet (hG _)
  calc ∫ y in PsiR (d := d) q ε η c '' E, G y
      = ∫ x in E, |(dPsiR (d := d) q ε η c x).det| • G (PsiR q ε η c x) :=
        integral_image_eq_integral_abs_det_fderiv_smul volume hE hderiv hinj G
    _ ≤ ∫ x in E, ((η * (4*q/(Real.pi*ε)))^d) * G (PsiR q ε η c x) :=
        setIntegral_mono_of_nonneg (fun x _ => mul_nonneg (abs_nonneg _) (hG _))
          (fun x hx => hkey x hx) (hint.const_mul _)
    _ = (η * (4*q/(Real.pi*ε)))^d * ∫ x in E, G (PsiR q ε η c x) :=
        integral_const_mul _ _

/-- **The `λmin` change-of-variables bound for the per-cell lens map** (`λmin = (1-ε)q/π`):
the pull-back integral is at most `(ηλmin)^{-d}` times the integral over the image. -/
theorem integral_image_PsiR_ge {q ε η : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hη : 0 < η) {c : Fin d → ℝ} {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-1 : ℝ) 1))
    {G : (Fin d → ℝ) → ℝ} (hG : ∀ x, 0 ≤ G x)
    (hint : IntegrableOn (fun w : Fin d → ℝ =>
      |(dPsiR (d := d) q ε η c w).det| • G (PsiR q ε η c w)) E volume)
    (hint2 : IntegrableOn (fun w : Fin d → ℝ => G (PsiR q ε η c w)) E volume) :
    (η * ((1-ε)*q/Real.pi))^d * ∫ w in E, G (PsiR q ε η c w)
      ≤ ∫ y in PsiR (d := d) q ε η c '' E, G y := by
  have hlt : ∀ x ∈ E, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hEsub hx j (Set.mem_univ j)
    rw [Set.mem_Ioo] at h
    rw [abs_lt]
    exact ⟨h.1, h.2⟩
  have hderiv : ∀ x ∈ E, HasFDerivWithinAt (PsiR (d := d) q ε η c) (dPsiR q ε η c x) E x :=
    fun x hx => (hasFDerivAt_PsiR hq hε0 (by linarith) (hlt x hx)).hasFDerivWithinAt
  have hinj : InjOn (PsiR (d := d) q ε η c) E :=
    PsiR_injOn hq hε0 (by linarith) hη hlt
  have hbase : 0 < (1-ε)*q/Real.pi := by
    have h1 : (0:ℝ) < 1 - ε := by linarith
    exact mul_pos (mul_pos h1 hq) (by positivity)
  have hηl : 0 < η * ((1-ε)*q/Real.pi) := mul_pos hη hbase
  have hkey : ∀ x ∈ E, (η * ((1-ε)*q/Real.pi))^d * G (PsiR q ε η c x)
      ≤ |(dPsiR (d := d) q ε η c x).det| • G (PsiR q ε η c x) := by
    intro x hx
    have hc : ∀ j : Fin d, (1-ε)*q/Real.pi ≤
        (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
      fun j => (phiLens_deriv_bounds hq hε0 hε1 (hlt x hx j)).1
    have hprod : ((1-ε)*q/Real.pi)^d ≤
        ∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) := by
      calc ((1-ε)*q/Real.pi)^d = ∏ _j : Fin d, ((1-ε)*q/Real.pi) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) :=
            Finset.prod_le_prod (fun j _ => le_of_lt hbase) (fun j _ => hc j)
    have hdet : (η * ((1-ε)*q/Real.pi))^d ≤ |(dPsiR (d := d) q ε η c x).det| := by
      rw [det_dPsiR]
      have hnn : 0 ≤ ∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) :=
        Finset.prod_nonneg (fun j _ => le_of_lt (phiLens_deriv_pos hq hε0 (by linarith)
          (hlt x hx j)))
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hη) d) hnn)]
      calc (η * ((1-ε)*q/Real.pi))^d = η^d * ((1-ε)*q/Real.pi)^d := by rw [mul_pow]
        _ ≤ η^d * (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)))) :=
            mul_le_mul_of_nonneg_left hprod (pow_nonneg (le_of_lt hη) d)
    rw [smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hdet (hG _)
  have hInt : IntegrableOn (fun x : Fin d → ℝ =>
      ((η * ((1-ε)*q/Real.pi))^d) * G (PsiR q ε η c x)) E volume :=
    hint2.const_mul _
  calc (η * ((1-ε)*q/Real.pi))^d * ∫ w in E, G (PsiR q ε η c w)
      = ∫ x in E, ((η * ((1-ε)*q/Real.pi))^d) * G (PsiR q ε η c x) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ x in E, |(dPsiR (d := d) q ε η c x).det| • G (PsiR q ε η c x) :=
        setIntegral_mono_of_nonneg
          (fun x _ => mul_nonneg (pow_nonneg (le_of_lt hηl) d) (hG _))
          (fun x hx => hkey x hx) hint
    _ = ∫ y in PsiR (d := d) q ε η c '' E, G y :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hE hderiv hinj G).symm


/-! ### Bounded multiplicity of the localisation lattice -/

/-- **At most three integers per coordinate.**  If a finset `T ⊆ ℤ` lies in the set where
`|z - (2k + γ + 1)| ≤ 2` (for two fixed reals `z`, `γ`), then `T` has at most `3` elements. -/
lemma card_le_three_of_abs_le (z γ : ℝ) (T : Finset ℤ)
    (hT : ∀ k ∈ T, |z - (2 * (k : ℝ) + γ + 1)| ≤ 2) : T.card ≤ 3 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  set m := T.min' hne with hm
  have hm' := hT m (T.min'_mem hne)
  rw [abs_le] at hm'
  have hsub : ∀ k ∈ T, k = m ∨ k = m + 1 ∨ k = m + 2 := by
    intro k hk
    have h1 : m ≤ k := T.min'_le _ hk
    have h2 := hT k hk
    rw [abs_le] at h2
    have h3 : (k : ℝ) ≤ (m : ℝ) + 2 := by linarith [hm'.1, h2.2]
    have h4 : k ≤ m + 2 := by exact_mod_cast h3
    omega
  have hsub' : T ⊆ ({m, m + 1, m + 2} : Finset ℤ) := by
    intro k hk
    rcases hsub k hk with h | h | h <;> simp [h]
  calc T.card ≤ ({m, m + 1, m + 2} : Finset ℤ).card := Finset.card_le_card hsub'
    _ = 3 := by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
          Finset.card_singleton]

/-- **Bounded multiplicity of the localisation lattice.** -/
theorem card_filter_abs_le_three_pow {d : ℕ} (z γ : Fin d → ℝ) (s : Finset (Fin d → ℤ))
    (hs : ∀ n ∈ s, ∀ i : Fin d, |z i - (2 * (n i : ℝ) + γ i + 1)| ≤ 2) :
    s.card ≤ 3 ^ d := by
  set A : Fin d → Finset ℤ := fun i => s.image (fun n => n i) with hA
  have hcard3 : ∀ i : Fin d, (A i).card ≤ 3 := by
    intro i
    refine card_le_three_of_abs_le (z i) (γ i) (A i) ?_
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact hs n hn i
  have hmaps : Set.MapsTo (fun n : Fin d → ℤ => fun i (_ : i ∈ Finset.univ) => n i)
      (↑s : Set (Fin d → ℤ)) (↑(Finset.univ.pi A) : Set ((i : Fin d) → i ∈ Finset.univ → ℤ)) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_pi]
    intro i _
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hinj : (↑s : Set (Fin d → ℤ)).InjOn
      (fun n : Fin d → ℤ => fun i (_ : i ∈ Finset.univ) => n i) := by
    intro n _ n' _ h
    funext i
    exact congrFun (congrFun h i) (Finset.mem_univ i)
  have h1 : s.card ≤ (Finset.univ.pi A).card := Finset.card_le_card_of_injOn _ hmaps hinj
  have h2 : (Finset.univ.pi A).card = ∏ i : Fin d, (A i).card := by
    show Multiset.card (Finset.univ.pi A).1 = _
    rw [Finset.pi_val, Multiset.card_pi, ← Finset.prod_eq_multiset_prod]
    exact Finset.prod_congr rfl (fun i _ => (Finset.card_def (A i)).symm)
  rw [h2] at h1
  calc s.card ≤ ∏ i : Fin d, (A i).card := h1
    _ ≤ ∏ _i : Fin d, 3 := Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hcard3 i)
    _ = 3 ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Submission.FUP
