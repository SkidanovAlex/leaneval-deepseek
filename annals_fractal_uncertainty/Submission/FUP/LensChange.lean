import Submission.FUP.LensReal

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The coordinatewise lens map and (to come) the change of variables

`Submission/FUP/LensReal.lean` gives the real lens map `phiLens q ε`, an increasing bijection
`(-1,1) → ℝ` with explicit derivative bounds.  Here we record the `d`-dimensional coordinatewise
version `PhiLens`, its (candidate) Fréchet derivative `dPhiLens`, and the injectivity on boxes.

**Status.**  `PhiLens`, `dPhiLens` and `PhiLens_injOn` are proved.  The statement
`HasFDerivAt (fun y j => phiLens q ε (y j)) (dPhiLens q ε x) x` is *not* yet proved: it runs into
a Lean elaboration issue — `ContinuousLinearMap.pi` over the constant family `fun _ : Fin d => ℝ`
leaves the `Module`/`NormedSpace` instances for the family as metavariables as soon as the term
occurs in a *statement* (inside a `def` the expected type pins them down, which is why `dPhiLens`
itself elaborates).  Suggested workarounds for the next session:

* build the derivative as a `LinearMap` first (`LinearMap.pi`) and promote with
  `LinearMap.mkContinuous` / `LinearMap.toContinuousLinearMap` (Mathlib has
  `LinearMap.det_pi`, `LinearMap.det_ring` at `Mathlib/LinearAlgebra/Determinant.lean:383,393`,
  which is what the determinant computation needs);
* or state the derivative with the family named by a top-level `def`
  `lensDiagFamily (q ε x) : Fin d → (Fin d → ℝ) →L[ℝ] ℝ := fun j => _ • proj j`
  and then `ContinuousLinearMap.pi (lensDiagFamily q ε x)`;
* or avoid `HasFDerivAt` and use `fderiv` + `fderiv_pi` + `HasFDerivAt.fderiv`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The coordinatewise real lens map. -/
noncomputable def PhiLens (q ε : ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun j => phiLens q ε (x j)

/-- The diagonal family of derivatives of `PhiLens`. -/
noncomputable def lensDiag (q ε : ℝ) (x : Fin d → ℝ) : Fin d → (Fin d → ℝ) →L[ℝ] ℝ :=
  fun j => (ContinuousLinearMap.toSpanSingleton ℝ
    ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)))).comp (ContinuousLinearMap.proj j)

/-- The Fréchet derivative of the coordinatewise lens map (as a `ContinuousLinearMap`). -/
noncomputable def dPhiLens (q ε : ℝ) (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (lensDiag q ε x)

lemma lensDiag_apply (q ε : ℝ) (x v : Fin d → ℝ) (j : Fin d) :
    lensDiag q ε x j v = ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) * v j := by
  simp only [lensDiag, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

lemma dPhiLens_apply (q ε : ℝ) (x v : Fin d → ℝ) :
    dPhiLens q ε x v = fun j => ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) * v j := by
  funext j
  rw [dPhiLens, ContinuousLinearMap.pi_apply, lensDiag_apply]

/-- **The Fréchet derivative of the coordinatewise lens map.**  (The explicit `φ`, `φ'`
arguments to `hasFDerivAt_pi` are essential: leaving them implicit makes the family's
`Module`/`NormedSpace` instances stuck.) -/
lemma hasFDerivAt_PhiLens {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {x : Fin d → ℝ} (hx : ∀ j, |x j| < 1) :
    HasFDerivAt (fun y j => phiLens q ε (y j)) (dPhiLens (d := d) q ε x) x := by
  set A : Fin d → (Fin d → ℝ) → ℝ := fun j y => phiLens q ε (y j) with hA
  set B : Fin d → (Fin d → ℝ) →L[ℝ] ℝ := lensDiag q ε x with hB
  refine (hasFDerivAt_pi (φ := A) (φ' := B)).2 fun j => ?_
  have h1 : HasFDerivAt (fun y : Fin d → ℝ => y j) (ContinuousLinearMap.proj j) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d => ℝ) j x
  have h2 : HasDerivAt (phiLens q ε)
      ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) (x j) :=
    hasDerivAt_phiLens hq hε0 hε1 (hx j)
  exact HasFDerivAt.comp (𝕜 := ℝ) (f := fun y : Fin d → ℝ => y j) (g := phiLens q ε) x
    (HasDerivAt.hasFDerivAt h2) h1

/-- **The determinant of the derivative of `PhiLens`** is the product of the one-dimensional
derivatives. -/
lemma det_dPhiLens (q ε : ℝ) (x : Fin d → ℝ) :
    (dPhiLens (d := d) q ε x).det
      = ∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) := by
  rw [dPhiLens]
  change LinearMap.det (ContinuousLinearMap.pi (lensDiag q ε x) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = _
  rw [ContinuousLinearMap.coe_pi]
  have h : (LinearMap.pi fun i : Fin d => ↑(lensDiag q ε x i)) =
      LinearMap.pi (fun i : Fin d => ((ContinuousLinearMap.toSpanSingleton ℝ
        ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x i))^2))) : ℝ →L[ℝ] ℝ) :
          ℝ →ₗ[ℝ] ℝ) ∘ₗ LinearMap.proj i) := rfl
  rw [h, LinearMap.det_pi]
  congr 1
  funext i
  rw [LinearMap.det_ring]
  simp

/-- `PhiLens` is injective on boxes inside `(-1,1)^d` (per-coordinate bounds). -/
lemma PhiLens_injOn {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {a b : Fin d → ℝ} (ha : ∀ j, -1 ≤ a j) (hb : ∀ j, b j ≤ 1) :
    InjOn (PhiLens (d := d) q ε) (Set.pi Set.univ (fun j : Fin d => Set.Icc (a j) (b j))) := by
  intro x hx y hy hxy
  funext j
  have hxj : x j ∈ Set.Icc (-1) 1 := ⟨le_trans (ha j) (hx j (Set.mem_univ j)).1,
    le_trans (hx j (Set.mem_univ j)).2 (hb j)⟩
  have hyj : y j ∈ Set.Icc (-1) 1 := ⟨le_trans (ha j) (hy j (Set.mem_univ j)).1,
    le_trans (hy j (Set.mem_univ j)).2 (hb j)⟩
  exact phiLens_injOn hq hε0 hε1 hxj hyj (by simpa [PhiLens] using congrFun hxy j)

/-- **Change of variables for the coordinatewise lens map** (on an open box inside `(-1,1)^d`;
the endpoints of `[-1,1]` are deliberately avoided because both `hasFDerivAt_PhiLens` and
`phiLens_deriv_bounds` need `|x| < 1`).  Per-coordinate bounds. -/
theorem integral_image_PhiLens {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    {a b : Fin d → ℝ} (ha : ∀ j, -1 < a j) (hb : ∀ j, b j < 1) (F : (Fin d → ℝ) → ℝ) :
    ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) ''
        (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))), F z
      = ∫ x in Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)),
          (∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) *
            F (fun j => phiLens q ε (x j)) := by
  set J : Set (Fin d → ℝ) := Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)) with hJ
  have hmeas : MeasurableSet J := by
    rw [hJ, show Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))
        = ⋂ j, (fun x : Fin d → ℝ => x j) ⁻¹' (Set.Ioo (a j) (b j)) from by ext x; simp]
    exact MeasurableSet.iInter fun j =>
      measurableSet_Ioo.preimage (continuous_apply j).measurable
  have hlt : ∀ x ∈ J, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hx j (Set.mem_univ j)
    rw [abs_lt]
    exact ⟨by linarith [h.1, ha j], by linarith [h.2, hb j]⟩
  have hderiv : ∀ x ∈ J,
      HasFDerivWithinAt (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) (dPhiLens q ε x) J x :=
    fun x hx => (hasFDerivAt_PhiLens hq hε0 (by linarith) (hlt x hx)).hasFDerivWithinAt
  have hinj : InjOn (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) J := by
    refine Set.InjOn.mono ?_ (PhiLens_injOn hq hε0 (by linarith) (fun j => le_of_lt (ha j))
      (fun j => le_of_lt (hb j)))
    intro x hx j _
    have h := hx j (Set.mem_univ j)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hmeas hderiv hinj F]
  refine setIntegral_congr_fun hmeas fun x hx => ?_
  have hc : ∀ j : Fin d, 0 < (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
    fun j => phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j)
  have hprodpos : 0 < ∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
    Finset.prod_pos fun j _ => hc j
  rw [det_dPhiLens, abs_of_pos hprodpos]
  exact smul_eq_mul _ _

/-- **The volume of `Φ(J)` is at most `λmax^d · |J|`** on an open box inside `(-1,1)^d`. -/
theorem volume_image_PhiLens_le {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    {a b : Fin d → ℝ} (ha : ∀ j, -1 < a j) (hb : ∀ j, b j < 1) :
    volume ((fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) ''
        (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))))
      ≤ ENNReal.ofReal ((4*q/(Real.pi*ε))^d) *
          volume (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))) := by
  set J : Set (Fin d → ℝ) := Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)) with hJ
  have hmeas : MeasurableSet J := by
    rw [hJ, show Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))
        = ⋂ j, (fun x : Fin d → ℝ => x j) ⁻¹' (Set.Ioo (a j) (b j)) from by ext x; simp]
    exact MeasurableSet.iInter fun j =>
      measurableSet_Ioo.preimage (continuous_apply j).measurable
  have hlt : ∀ x ∈ J, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hx j (Set.mem_univ j)
    rw [abs_lt]
    exact ⟨by linarith [h.1, ha j], by linarith [h.2, hb j]⟩
  have hderiv : ∀ x ∈ J,
      HasFDerivWithinAt (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) (dPhiLens q ε x) J x :=
    fun x hx => (hasFDerivAt_PhiLens hq hε0 (by linarith) (hlt x hx)).hasFDerivWithinAt
  have hinj : InjOn (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) J := by
    refine Set.InjOn.mono ?_ (PhiLens_injOn hq hε0 (by linarith) (fun j => le_of_lt (ha j))
      (fun j => le_of_lt (hb j)))
    intro x hx j _
    have h := hx j (Set.mem_univ j)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas hderiv hinj
    (fun _ : Fin d → ℝ => (1 : ℝ≥0∞))
  rw [← MeasureTheory.setLIntegral_one (μ := volume)
      (s := (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' J), h]
  simp only [mul_one]
  refine le_trans (setLIntegral_mono measurable_const (fun x hx => ?_))
    (le_of_eq (setLIntegral_const J _))
  refine ENNReal.ofReal_le_ofReal ?_
  rw [det_dPhiLens, abs_of_pos (Finset.prod_pos fun j _ =>
    phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j))]
  have hc : ∀ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))
      ≤ 4*q/(Real.pi*ε) :=
    fun j => (phiLens_deriv_bounds hq hε0 hε1 (hlt x hx j)).2
  have hc0 : ∀ j : Fin d, 0 ≤ (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
    fun j => le_of_lt (phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j))
  calc ∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))
      ≤ ∏ _j : Fin d, (4*q/(Real.pi*ε)) :=
        Finset.prod_le_prod (fun j _ => hc0 j) (fun j _ => hc j)
    _ = (4*q/(Real.pi*ε))^d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The `L²` change-of-variables inequality** for the coordinatewise lens map: the pull-back
integral is at most `λmin^{-1}` times the integral over the image, with
`λmin = ((1-ε)q/π)^d`.  (`hint` is the integrability of the weighted pull-back; it holds in the
application because `G = ‖g‖²` is continuous and `∏ φ'` is bounded on the box.) -/
theorem integral_comp_PhiLens_le {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    {a b : Fin d → ℝ} (ha : ∀ j, -1 < a j) (hb : ∀ j, b j < 1)
    {G : (Fin d → ℝ) → ℝ} (hG : ∀ x, 0 ≤ G x)
    (hint : IntegrableOn (fun x : Fin d → ℝ =>
      (∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) *
        G (fun j => phiLens q ε (x j)))
      (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))) volume) :
    ∫ x in Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)),
        G (fun j => phiLens q ε (x j))
      ≤ ((1-ε)*q/Real.pi)^(-(d:ℝ)) *
          ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) ''
            (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))), G z := by
  have hbase : 0 < (1-ε)*q/Real.pi := by
    have h1 : (0:ℝ) < 1 - ε := by linarith
    positivity
  have hlam : 0 < ((1-ε)*q/Real.pi)^d := pow_pos hbase d
  have hlt : ∀ x ∈ Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)), ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hx j (Set.mem_univ j)
    rw [abs_lt]
    exact ⟨by linarith [h.1, ha j], by linarith [h.2, hb j]⟩
  have hpt : ∀ x ∈ Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)),
      ((1-ε)*q/Real.pi)^d * G (fun j => phiLens q ε (x j))
      ≤ (∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) *
        G (fun j => phiLens q ε (x j)) := by
    intro x hx
    refine mul_le_mul_of_nonneg_right ?_ (hG _)
    calc ((1-ε)*q/Real.pi)^d = ∏ _j : Fin d, ((1-ε)*q/Real.pi) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
          Finset.prod_le_prod (fun j _ => le_of_lt hbase)
            (fun j _ => (phiLens_deriv_bounds hq hε0 hε1 (hlt x hx j)).1)
  have h1 : ((1-ε)*q/Real.pi)^d *
        (∫ x in Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)),
          G (fun j => phiLens q ε (x j)))
      ≤ ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) ''
          (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))), G z := by
    rw [← integral_const_mul, integral_image_PhiLens (d := d) hq hε0 hε1 ha hb G]
    exact setIntegral_mono_of_nonneg (fun x _ => mul_nonneg (le_of_lt hlam) (hG _))
      (fun x hx => hpt x hx) hint
  calc ∫ x in Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)),
        G (fun j => phiLens q ε (x j))
      = (((1-ε)*q/Real.pi)^d)⁻¹ * (((1-ε)*q/Real.pi)^d *
          ∫ x in Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j)),
            G (fun j => phiLens q ε (x j))) :=
        (inv_mul_cancel_left₀ (ne_of_gt hlam) _).symm
    _ ≤ (((1-ε)*q/Real.pi)^d)⁻¹ *
          ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) ''
            (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))), G z :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((1-ε)*q/Real.pi)^(-(d:ℝ)) *
          ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) ''
            (Set.pi Set.univ (fun j : Fin d => Set.Ioo (a j) (b j))), G z := by
        congr 1
        rw [Real.rpow_neg (le_of_lt hbase) (d:ℝ), Real.rpow_natCast]

/-- **Change of variables for the coordinatewise lens map, arbitrary measurable set inside the
open unit cube.**  (Same content as `integral_image_PhiLens`, but the domain is an arbitrary
measurable subset of `(-1,1)^d`; this is what the localisation cell needs, since the cell preimage
is not a product of intervals with explicit endpoints.) -/
theorem integral_image_PhiLens_set {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-1 : ℝ) 1))
    (F : (Fin d → ℝ) → ℝ) :
    ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E, F z
      = ∫ x in E,
          (∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) *
            F (fun j => phiLens q ε (x j)) := by
  have hlt : ∀ x ∈ E, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hEsub hx j (Set.mem_univ j)
    rw [abs_lt]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hderiv : ∀ x ∈ E,
      HasFDerivWithinAt (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) (dPhiLens q ε x) E x :=
    fun x hx => (hasFDerivAt_PhiLens hq hε0 (by linarith) (hlt x hx)).hasFDerivWithinAt
  have hinj : InjOn (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) E := by
    refine Set.InjOn.mono ?_ (PhiLens_injOn hq hε0 (by linarith)
      (fun j => le_refl (-1:ℝ)) (fun j => le_refl (1:ℝ)))
    intro x hx j _
    have h := hEsub hx j (Set.mem_univ j)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hE hderiv hinj F]
  refine setIntegral_congr_fun hE fun x hx => ?_
  have hc : ∀ j : Fin d, 0 < (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
    fun j => phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j)
  have hprodpos : 0 < ∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
    Finset.prod_pos fun j _ => hc j
  rw [det_dPhiLens, abs_of_pos hprodpos]
  exact smul_eq_mul _ _

/-- **The `L²` change-of-variables inequality, arbitrary measurable set.** -/
theorem integral_comp_PhiLens_le_set {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-1 : ℝ) 1))
    {G : (Fin d → ℝ) → ℝ} (hG : ∀ x, 0 ≤ G x)
    (hint : IntegrableOn (fun x : Fin d → ℝ =>
      (∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) *
        G (fun j => phiLens q ε (x j))) E volume) :
    ∫ x in E, G (fun j => phiLens q ε (x j))
      ≤ ((1-ε)*q/Real.pi)^(-(d:ℝ)) *
          ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E, G z := by
  have hbase : 0 < (1-ε)*q/Real.pi := by
    have h1 : (0:ℝ) < 1 - ε := by linarith
    positivity
  have hlam : 0 < ((1-ε)*q/Real.pi)^d := pow_pos hbase d
  have hlt : ∀ x ∈ E, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hEsub hx j (Set.mem_univ j)
    rw [abs_lt]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hpt : ∀ x ∈ E, ((1-ε)*q/Real.pi)^d * G (fun j => phiLens q ε (x j))
      ≤ (∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))) *
        G (fun j => phiLens q ε (x j)) := by
    intro x hx
    refine mul_le_mul_of_nonneg_right ?_ (hG _)
    calc ((1-ε)*q/Real.pi)^d = ∏ _j : Fin d, ((1-ε)*q/Real.pi) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
          Finset.prod_le_prod (fun j _ => le_of_lt hbase)
            (fun j _ => (phiLens_deriv_bounds hq hε0 hε1 (hlt x hx j)).1)
  have h1 : ((1-ε)*q/Real.pi)^d * (∫ x in E, G (fun j => phiLens q ε (x j)))
      ≤ ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E, G z := by
    rw [← integral_const_mul, integral_image_PhiLens_set (d := d) hq hε0 hε1 hE hEsub G]
    exact setIntegral_mono_of_nonneg (fun x _ => mul_nonneg (le_of_lt hlam) (hG _))
      (fun x hx => hpt x hx) hint
  calc ∫ x in E, G (fun j => phiLens q ε (x j))
      = (((1-ε)*q/Real.pi)^d)⁻¹ * (((1-ε)*q/Real.pi)^d *
          ∫ x in E, G (fun j => phiLens q ε (x j))) :=
        (inv_mul_cancel_left₀ (ne_of_gt hlam) _).symm
    _ ≤ (((1-ε)*q/Real.pi)^d)⁻¹ *
          ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E, G z :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((1-ε)*q/Real.pi)^(-(d:ℝ)) *
          ∫ z in (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E, G z := by
        congr 1
        rw [Real.rpow_neg (le_of_lt hbase) (d:ℝ), Real.rpow_natCast]

/-- **`|Φ(E)| ≤ λmax^d |E|`, arbitrary measurable set.** -/
theorem volume_image_PhiLens_le_set {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-1 : ℝ) 1)) :
    volume ((fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E)
      ≤ ENNReal.ofReal ((4*q/(Real.pi*ε))^d) * volume E := by
  have hlt : ∀ x ∈ E, ∀ j, |x j| < 1 := by
    intro x hx j
    have h := hEsub hx j (Set.mem_univ j)
    rw [abs_lt]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hderiv : ∀ x ∈ E,
      HasFDerivWithinAt (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) (dPhiLens q ε x) E x :=
    fun x hx => (hasFDerivAt_PhiLens hq hε0 (by linarith) (hlt x hx)).hasFDerivWithinAt
  have hinj : InjOn (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) E := by
    refine Set.InjOn.mono ?_ (PhiLens_injOn hq hε0 (by linarith)
      (fun j => le_refl (-1:ℝ)) (fun j => le_refl (1:ℝ)))
    intro x hx j _
    have h := hEsub hx j (Set.mem_univ j)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE hderiv hinj
    (fun _ : Fin d → ℝ => (1 : ℝ≥0∞))
  rw [← MeasureTheory.setLIntegral_one (μ := volume)
      (s := (fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E), h]
  simp only [mul_one]
  refine le_trans (setLIntegral_mono measurable_const (fun x hx => ?_))
    (le_of_eq (setLIntegral_const E _))
  refine ENNReal.ofReal_le_ofReal ?_
  rw [det_dPhiLens, abs_of_pos (Finset.prod_pos fun j _ =>
    phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j))]
  have hc : ∀ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) ≤ 4*q/(Real.pi*ε) :=
    fun j => (phiLens_deriv_bounds hq hε0 hε1 (hlt x hx j)).2
  have hc0 : ∀ j : Fin d, 0 ≤ (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2)) :=
    fun j => le_of_lt (phiLens_deriv_pos hq hε0 (by linarith) (hlt x hx j))
  calc ∏ j : Fin d, (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(x j))^2))
      ≤ ∏ _j : Fin d, (4*q/(Real.pi*ε)) :=
        Finset.prod_le_prod (fun j _ => hc0 j) (fun j _ => hc j)
    _ = (4*q/(Real.pi*ε))^d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
