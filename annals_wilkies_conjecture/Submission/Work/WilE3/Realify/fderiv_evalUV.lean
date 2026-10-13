import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Realify

open WilkiesDesign.E

set_option autoImplicit false
noncomputable section

/-!
## The real derivative of `evalUV`

`evalUV c P w = eaEvalC c P (zOf w)` is the complexified EA system read on `ℝ^{2k}` through
`zOf w = w_u + i w_v`.  Since `eaEvalC c P` is complex differentiable with complex derivative
`dEvalC c P z = ∑ i, eaEvalC c (eaD c i P) z ∂_{z_i}` (`API.eaEvalC_fderiv_analytic`), and since
`zOf` is real linear, the real derivative of `evalUV c P` is the realification of the complex one:
the `u_j`-derivative is `∂_{z_j}` and the `v_j`-derivative is `i ∂_{z_j}`.  This file computes the
four entries of the real Jacobian block `[[Re, -Im], [Im, Re]]`.

The proof is pure calculus: `zOf` is a continuous linear map (`zOfCLM`), so its derivative is
itself, and `HasFDerivAt.comp` plus `Complex.reCLM`/`Complex.imCLM` give the two real components.
-/

/-! ## §1. `zOf` as a continuous linear map -/

/-- The real-linear continuous map underlying `zOf`: `w ↦ (i ↦ w (castAdd k i) + i · w (natAdd k i))`. -/
def zOfCLM (k : ℕ) : (Fin (k + k) → ℝ) →L[ℝ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + k) => ℝ)
        (Fin.castAdd k i)).smulRight (1 : ℂ)
      + (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + k) => ℝ)
        (Fin.natAdd k i)).smulRight Complex.I

theorem zOfCLM_apply' (k : ℕ) (d : Fin (k + k) → ℝ) :
    zOfCLM k d = fun i => d (Fin.castAdd k i) • (1 : ℂ) + d (Fin.natAdd k i) • Complex.I := by
  funext i
  simp only [zOfCLM, ContinuousLinearMap.pi_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- `zOf` is the continuous linear map `zOfCLM`. -/
theorem hasFDerivAt_zOf (k : ℕ) (w : Fin (k + k) → ℝ) :
    HasFDerivAt (zOf (k := k)) (zOfCLM k) w := by
  have h : (zOf (k := k)) = ⇑(zOfCLM k) := by
    funext w i
    simp only [zOfCLM, ContinuousLinearMap.pi_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, zOf,
      Complex.real_smul, mul_one]
  rw [h]
  exact (zOfCLM k).hasFDerivAt

/-! ## §2. The two basis directions -/

theorem castAdd_ne_natAdd (k : ℕ) (j i : Fin k) : Fin.castAdd k j ≠ Fin.natAdd k i := by
  intro h
  simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h
  omega

theorem natAdd_ne_castAdd (k : ℕ) (i j : Fin k) : Fin.natAdd k i ≠ Fin.castAdd k j :=
  (castAdd_ne_natAdd k j i).symm

theorem natAdd_injective (k : ℕ) : Function.Injective (Fin.natAdd (m := k) k) := by
  intro i j h
  simp only [Fin.ext_iff, Fin.val_natAdd] at h
  omega

/-- The `u_j`-direction maps to `∂_{z_j}`. -/
theorem zOfCLM_single_castAdd (k : ℕ) (j : Fin k) :
    zOfCLM k (Pi.single (Fin.castAdd k j) (1 : ℝ)) = Pi.single j (1 : ℂ) := by
  funext i
  simp only [zOfCLM_apply']
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (natAdd_ne_castAdd k i i)]
    simp
  · rw [Pi.single_eq_of_ne (fun hc => h (Fin.castAdd_inj.mp hc)),
      Pi.single_eq_of_ne (natAdd_ne_castAdd k i j), Pi.single_eq_of_ne h]
    simp

/-- The `v_j`-direction maps to `i ∂_{z_j}`. -/
theorem zOfCLM_single_natAdd (k : ℕ) (j : Fin k) :
    zOfCLM k (Pi.single (Fin.natAdd k j) (1 : ℝ)) = Pi.single j (Complex.I) := by
  funext i
  simp only [zOfCLM_apply']
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_of_ne (castAdd_ne_natAdd k i i), Pi.single_eq_same]
    simp
  · rw [Pi.single_eq_of_ne (castAdd_ne_natAdd k i j),
      Pi.single_eq_of_ne (fun hc => h (natAdd_injective k hc)), Pi.single_eq_of_ne h]
    simp

/-! ## §3. The complex derivative along a coordinate direction -/

theorem dEvalC_piSingle {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (z : Fin k → ℂ)
    (j : Fin k) (a : ℂ) :
    Work.WilE3.API.dEvalC c Q z (Pi.single j a)
      = Work.WilE3.eaEvalC c (eaD c j Q) z * a := by
  simp only [Work.WilE3.API.dEvalC, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, smul_eq_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Evaluating the `ℝ`-restriction of a complex-linear functional. -/
theorem restrictScalars_apply_eq {k : ℕ} (f : (Fin k → ℂ) →L[ℂ] ℂ) (y : Fin k → ℂ) :
    (ContinuousLinearMap.restrictScalars ℝ f) y = f y := rfl

/-! ## §4. The Jacobian of `evalUV` -/

theorem fderiv_evalUV {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (P : WilkiesDesign.E.EAPoly k r)
    (w : Fin (k + k) → ℝ) (j : Fin k) :
    fderiv ℝ (fun w' : Fin (k + k) → ℝ => (Work.WilE3.Realify.evalUV c P w').re) w
        (Pi.single (Fin.castAdd k j) 1)
        = (Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j P) (Work.WilE3.Realify.zOf w)).re
      ∧ fderiv ℝ (fun w' : Fin (k + k) → ℝ => (Work.WilE3.Realify.evalUV c P w').re) w
        (Pi.single (Fin.natAdd k j) 1)
        = -(Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j P) (Work.WilE3.Realify.zOf w)).im
      ∧ fderiv ℝ (fun w' : Fin (k + k) → ℝ => (Work.WilE3.Realify.evalUV c P w').im) w
        (Pi.single (Fin.castAdd k j) 1)
        = (Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j P) (Work.WilE3.Realify.zOf w)).im
      ∧ fderiv ℝ (fun w' : Fin (k + k) → ℝ => (Work.WilE3.Realify.evalUV c P w').im) w
        (Pi.single (Fin.natAdd k j) 1)
        = (Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j P) (Work.WilE3.Realify.zOf w)).re := by
  -- the chain rule: `evalUV c P = eaEvalC c P ∘ zOf`
  have hz : HasFDerivAt (zOf (k := k)) (zOfCLM k) w := hasFDerivAt_zOf k w
  have hC : HasFDerivAt (Work.WilE3.eaEvalC c P)
      ((Work.WilE3.API.dEvalC c P (zOf w)).restrictScalars ℝ) (zOf w) :=
    HasFDerivAt.restrictScalars ℝ
      (Work.WilE3.API.eaEvalC_fderiv_analytic c P (zOf w)).2
  have hF : HasFDerivAt (fun w' : Fin (k + k) → ℝ => evalUV c P w')
      ((ContinuousLinearMap.restrictScalars ℝ (Work.WilE3.API.dEvalC c P (zOf w))) ∘SL
        (zOfCLM k)) w := by
    have h := HasFDerivAt.comp w hC hz
    simpa only [evalUV, Function.comp_def] using h
  have hre : HasFDerivAt (fun w' : Fin (k + k) → ℝ => (evalUV c P w').re)
      (Complex.reCLM.comp ((ContinuousLinearMap.restrictScalars ℝ
        (Work.WilE3.API.dEvalC c P (zOf w))) ∘SL (zOfCLM k))) w :=
    HasFDerivAt.comp w (Complex.reCLM.hasFDerivAt (x := evalUV c P w)) hF
  have him : HasFDerivAt (fun w' : Fin (k + k) → ℝ => (evalUV c P w').im)
      (Complex.imCLM.comp ((ContinuousLinearMap.restrictScalars ℝ
        (Work.WilE3.API.dEvalC c P (zOf w))) ∘SL (zOfCLM k))) w :=
    HasFDerivAt.comp w (Complex.imCLM.hasFDerivAt (x := evalUV c P w)) hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre.fderiv]
    simp only [ContinuousLinearMap.comp_apply, restrictScalars_apply_eq,
      zOfCLM_single_castAdd, dEvalC_piSingle, Complex.reCLM_apply, mul_one]
  · rw [hre.fderiv]
    simp only [ContinuousLinearMap.comp_apply, restrictScalars_apply_eq,
      zOfCLM_single_natAdd, dEvalC_piSingle, Complex.reCLM_apply, Complex.mul_I_re]
  · rw [him.fderiv]
    simp only [ContinuousLinearMap.comp_apply, restrictScalars_apply_eq,
      zOfCLM_single_castAdd, dEvalC_piSingle, Complex.imCLM_apply, mul_one]
  · rw [him.fderiv]
    simp only [ContinuousLinearMap.comp_apply, restrictScalars_apply_eq,
      zOfCLM_single_natAdd, dEvalC_piSingle, Complex.imCLM_apply, Complex.mul_I_im]

end

end Work.WilE3.Realify
