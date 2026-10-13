import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §1. Auxiliary lemmas: open neighbourhoods, the projection `uCoord`, and `PhiC` -/

/-- **An eventual statement gives an open neighbourhood.** -/
theorem exists_isOpen_forall_of_eventually {α : Type*} [TopologicalSpace α] {x : α} {P : α → Prop}
    (h : ∀ᶠ y in 𝓝 x, P y) : ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, P y := by
  obtain ⟨s, hs, hPs⟩ := Filter.eventually_iff_exists_mem.mp h
  exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
    fun y hy => hPs y (interior_subset hy)⟩

/-- The projection `uCoord k ι` to the `ι`-complement coordinates, as a continuous linear map. -/
def uCoordL (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) : (Fin k → ℂ) →L[ℂ] (U k ι → ℂ) :=
  ContinuousLinearMap.pi fun i : U k ι =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1

theorem uCoordL_apply (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) (z : Fin k → ℂ) :
    uCoordL k ι z = uCoord k ι z := rfl

theorem hasFDerivAt_uCoord (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) (u : Fin k → ℂ) :
    HasFDerivAt (uCoord k ι) (uCoordL k ι) u :=
  (uCoordL k ι).hasFDerivAt

theorem continuous_uCoord (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) :
    Continuous (uCoord k ι) := by
  have hfn : (uCoord k ι : (Fin k → ℂ) → (U k ι → ℂ)) = ⇑(uCoordL k ι) :=
    funext fun z => uCoordL_apply k ι z
  rw [hfn]
  exact (uCoordL k ι).continuous

/-- The projection of an ambient basis vector: for `l ∉ range ι` the direction `e_l` of the ambient
space is the direction `e_{⟨l,_⟩}` of the parameter space. -/
theorem uCoordL_single (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) {l : Fin k} (hl : l ∉ Set.range ι) :
    uCoordL k ι (Pi.single l (1 : ℂ)) = (Pi.single ⟨l, hl⟩ (1 : ℂ) : U k ι → ℂ) := by
  ext i
  rw [uCoordL_apply]
  change (Pi.single l (1 : ℂ) : Fin k → ℂ) (i : Fin k)
    = (Pi.single ⟨l, hl⟩ (1 : ℂ) : U k ι → ℂ) i
  by_cases h : (i : Fin k) = l
  · have hs1 : i = ⟨l, hl⟩ := Subtype.ext h
    rw [hs1]
    show (Pi.single l (1 : ℂ) : Fin k → ℂ) l
      = (Pi.single ⟨l, hl⟩ (1 : ℂ) : U k ι → ℂ) ⟨l, hl⟩
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h,
      Pi.single_eq_of_ne (show i ≠ (⟨l, hl⟩ : U k ι) from fun hc => h (congrArg Subtype.val hc))]

/-- The coordinate map `PhiC` is complex differentiable, with derivative `DPhiC`. -/
theorem hasFDerivAt_PhiC' (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) : HasFDerivAt (PhiC c h ι) (DPhiC c h ι z) z := by
  have h1 : HasFDerivAt (fun z : Fin k → ℂ => uCoord k ι z)
      (ContinuousLinearMap.pi fun i : U k ι =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1) z :=
    (ContinuousLinearMap.pi (fun i : U k ι =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1)).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Fin k → ℂ => fun a : Fin j => eaEvalC c (h a) z)
      (ContinuousLinearMap.pi fun a : Fin j =>
        ∑ i : Fin k, (eaEvalC c (eaD c i (h a)) z) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i) z := by
    rw [hasFDerivAt_pi]
    intro a
    exact (Work.WilE3.API.eaEvalC_fderiv_analytic c (h a) z).2
  exact h1.prodMk h2

/-! ## §2. Analyticity of the frame coefficients

The frame field `VcoefC c h ι l z` is computed from the adjugate of the `ι`-Jacobian by Cramer's
rule.  Rather than analysing the adjugate of a matrix of analytic functions, we observe that
`jacMatC c h ι z` is the evaluation of a *fixed* polynomial matrix `jacMatPoly c h ι`, so by
`RingHom.map_adjugate` the vector `(jacMatC z).adjugate *ᵥ dlColC c h l z` is the evaluation of a
fixed polynomial vector `adjPolyVec c h ι l`; hence `betaC`, `VcoefC`, and finally `Vdir` are
analytic wherever `jacValC ≠ 0`. -/

/-- The polynomial matrix whose evaluation at `z` is `jacMatC c h ι z`. -/
def jacMatPoly (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) :
    Matrix (Fin j) (Fin j) (EAPoly k r) :=
  Matrix.of fun a b => eaD c (ι b) (h a)

/-- The polynomial vector whose evaluation at `z` is `(jacMatC c h ι z).adjugate *ᵥ dlColC c h l z`. -/
def adjPolyVec (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (l : Fin k) :
    Fin j → EAPoly k r :=
  (jacMatPoly c h ι).adjugate *ᵥ fun a => eaD c l (h a)

theorem jacMatC_eq_map (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) :
    jacMatC c h ι z
      = (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) (Work.WilE3.API.eaPsi c z)).mapMatrix
          (jacMatPoly c h ι) := by
  ext a b
  simp only [jacMatC, jacMatPoly, Matrix.of_apply, RingHom.mapMatrix_apply]
  rfl

/-- **Cramer's rule, polynomial form.**  The adjugate-times-column vector of the `ι`-Jacobian is the
evaluation of the fixed polynomial vector `adjPolyVec`. -/
theorem eaEvalC_adjPolyVec (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) :
    (jacMatC c h ι z).adjugate *ᵥ dlColC c h l z
      = fun b => eaEvalC c (adjPolyVec c h ι l b) z := by
  funext b
  have hadj : ∀ a b, eaEvalC c ((jacMatPoly c h ι).adjugate a b) z
      = (jacMatC c h ι z).adjugate a b := by
    intro a b
    have hmadj := RingHom.map_adjugate
      (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) (Work.WilE3.API.eaPsi c z)) (jacMatPoly c h ι)
    rw [← jacMatC_eq_map c h ι z] at hmadj
    have h2 := congrFun (congrFun hmadj a) b
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Work.WilE3.API.eaEvalC_eq] using h2
  have hAp : adjPolyVec c h ι l b
      = ∑ a, (jacMatPoly c h ι).adjugate b a * eaD c l (h a) := by
    rw [adjPolyVec, Matrix.mulVec_apply_eq_sum]
  rw [Matrix.mulVec_apply_eq_sum, hAp]
  rw [Work.WilE3.API.eaEvalC_eq, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← Work.WilE3.API.eaEvalC_eq, hadj b a]
  rfl

/-- Cramer's coefficients are analytic where the `ι`-Jacobian does not vanish. -/
theorem analyticAt_betaC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (b : Fin j) (hz : jacValC c h ι z ≠ 0) :
    AnalyticAt ℂ (fun w => betaC c h ι l w b) z := by
  have h1 : AnalyticAt ℂ (fun w => (jacValC c h ι w)⁻¹) z :=
    (Work.WilE3.API.eaEvalC_fderiv_analytic c (jacDet c h ι) z).1.inv hz
  have h2 : AnalyticAt ℂ
      (fun w => ((jacMatC c h ι w).adjugate *ᵥ dlColC c h l w) b) z := by
    have hfun : (fun w => ((jacMatC c h ι w).adjugate *ᵥ dlColC c h l w) b)
        = fun w => eaEvalC c (adjPolyVec c h ι l b) w := by
      funext w
      exact congrFun (eaEvalC_adjPolyVec c h ι l w) b
    rw [hfun]
    exact (Work.WilE3.API.eaEvalC_fderiv_analytic c (adjPolyVec c h ι l b) z).1
  have hmul : AnalyticAt ℂ (fun w => (jacValC c h ι w)⁻¹ *
      ((jacMatC c h ι w).adjugate *ᵥ dlColC c h l w) b) z := h1.mul h2
  simpa only [betaC, Pi.mul_apply] using hmul

/-- The components of the frame field are analytic where the `ι`-Jacobian does not vanish. -/
theorem analyticAt_VcoefC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (i : Fin k) (hz : jacValC c h ι z ≠ 0) :
    AnalyticAt ℂ (fun w => VcoefC c h ι l w i) z := by
  have hfun : (fun w => VcoefC c h ι l w i)
      = fun w => (if i = l then (1 : ℂ) else 0) -
          ∑ b : Fin j, (if ι b = i then betaC c h ι l w b else 0) := by
    funext w
    simp only [VcoefC]
  rw [hfun]
  have hsum : AnalyticAt ℂ
      (fun w : Fin k → ℂ => ∑ b : Fin j,
        (if ι b = i then betaC c h ι l w b else 0)) z := by
    have hh : AnalyticAt ℂ
        (∑ b : Fin j, fun w : Fin k → ℂ =>
          (if ι b = i then betaC c h ι l w b else 0)) z := by
      refine Finset.analyticAt_sum (α := Fin j) (𝕜 := ℂ) (E := Fin k → ℂ) (F := ℂ)
        (f := fun (b : Fin j) (w : Fin k → ℂ) =>
          (if ι b = i then betaC c h ι l w b else 0)) (c := z) Finset.univ ?_
      intro b _
      by_cases hbi : ι b = i
      · have hb : (fun w : Fin k → ℂ => if ι b = i then betaC c h ι l w b else 0)
            = fun w => betaC c h ι l w b := by
          funext w
          rw [if_pos hbi]
        rw [hb]
        exact analyticAt_betaC c h ι l z b hz
      · have hb : (fun w : Fin k → ℂ => if ι b = i then betaC c h ι l w b else 0)
            = fun _ => (0 : ℂ) := by
          funext w
          rw [if_neg hbi]
        rw [hb]
        exact analyticAt_const
    rwa [show (∑ b : Fin j, fun w : Fin k → ℂ =>
        (if ι b = i then betaC c h ι l w b else 0))
        = fun w : Fin k → ℂ => ∑ b : Fin j,
            (if ι b = i then betaC c h ι l w b else 0)
        from funext fun w => by simp only [Finset.sum_apply]] at hh
  exact analyticAt_const.sub hsum

/-- **`Vdir` preserves analyticity**, at every point where the `ι`-Jacobian does not vanish. -/
theorem analyticAt_Vdir_aux (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (K : (Fin k → ℂ) → ℂ) (z : Fin k → ℂ)
    (hK : AnalyticAt ℂ K z) (hz : jacValC c h ι z ≠ 0) :
    AnalyticAt ℂ (Vdir c h ι l K) z := by
  have hsum : AnalyticAt ℂ (fun w : Fin k → ℂ =>
      ∑ i : Fin k, VcoefC c h ι l w i * fderiv ℂ K w (Pi.single i 1)) z := by
    have hh : AnalyticAt ℂ
        (∑ i : Fin k, fun w : Fin k → ℂ =>
          VcoefC c h ι l w i * fderiv ℂ K w (Pi.single i 1)) z := by
      refine Finset.analyticAt_sum (α := Fin k) (𝕜 := ℂ) (E := Fin k → ℂ) (F := ℂ)
        (f := fun (i : Fin k) (w : Fin k → ℂ) =>
          VcoefC c h ι l w i * fderiv ℂ K w (Pi.single i 1)) (c := z) Finset.univ ?_
      intro i _
      refine (analyticAt_VcoefC c h ι l z i hz).mul ?_
      exact (((ContinuousLinearMap.apply ℂ ℂ) (Pi.single i (1 : ℂ))).analyticAt
        (fderiv ℂ K z)).comp hK.fderiv
    rwa [show (∑ i : Fin k, fun w : Fin k → ℂ =>
        VcoefC c h ι l w i * fderiv ℂ K w (Pi.single i 1))
        = fun w : Fin k → ℂ => ∑ i : Fin k,
            VcoefC c h ι l w i * fderiv ℂ K w (Pi.single i 1)
        from funext fun w => by simp only [Finset.sum_apply]] at hh
  exact hsum

end

end Work.WilE3.Frame
