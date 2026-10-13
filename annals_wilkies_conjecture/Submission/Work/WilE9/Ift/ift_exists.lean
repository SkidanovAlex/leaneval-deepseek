import Mathlib
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Filter Topology

namespace Work.WilE9.Ift
open WilkiesDesign WilkiesDesign.E

/-! ## Auxiliary material for `ift_exists`

Everything here is a direct computation on the graph map
`p ↦ (j ↦ eaEval c (F j) (Fin.append p.1 p.2))` of the system `F`, whose (ambient) derivative
in the fibre directions is the Jacobian `jm c F`. -/

/-- `appendCLM n q` is `Fin.append` at every point of the product. -/
theorem appendCLM_apply_prod {n q : ℕ} (p : (Fin n → ℝ) × (Fin q → ℝ)) :
    appendCLM n q p = Fin.append p.1 p.2 := by
  obtain ⟨v, w⟩ := p
  exact appendCLM_apply n q v w

/-- The function underlying `appendCLM n q` is `(v, w) ↦ Fin.append v w`. -/
theorem coe_appendCLM {n q : ℕ} :
    ⇑(appendCLM n q) = fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2 :=
  funext (fun p => appendCLM_apply_prod p)

/-- The ambient first derivative of `eaEval c P` at the point `w`, as a continuous linear map. -/
def ambDeriv {N r : ℕ} (c : EAChain N r) (P : EAPoly N r) (w : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ s : Fin N, eaEval c (eaD c s P) w • (ContinuousLinearMap.proj s : (Fin N → ℝ) →L[ℝ] ℝ)

/-- Evaluation of `ambDeriv`. -/
theorem ambDeriv_apply {N r : ℕ} (c : EAChain N r) (P : EAPoly N r) (w z : Fin N → ℝ) :
    ambDeriv c P w z = ∑ s : Fin N, eaEval c (eaD c s P) w * z s := by
  simp only [ambDeriv, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The graph map `(x, y) ↦ (j ↦ eaEval c (F j) (x, y))` of the system `F`. -/
def graphEval {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) :
    ((Fin n → ℝ) × (Fin q → ℝ)) → (Fin q → ℝ) :=
  fun p j => eaEval c (F j) (Fin.append p.1 p.2)

/-- Evaluation of the graph map. -/
theorem graphEval_apply {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r)
    (p : (Fin n → ℝ) × (Fin q → ℝ)) (j : Fin q) :
    graphEval c F p j = eaEval c (F j) (Fin.append p.1 p.2) := rfl

/-- The graph map is `C^∞`. -/
theorem graphEval_contDiff {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) : ContDiff ℝ ⊤ (graphEval c F) := by
  change ContDiff ℝ ⊤ (fun p : (Fin n → ℝ) × (Fin q → ℝ) => fun j : Fin q =>
    eaEval c (F j) (Fin.append p.1 p.2))
  rw [contDiff_pi]
  intro j
  have h := (Work.WilE9.EaD.eaEval_contDiff c (F j)).comp ((appendCLM n q).contDiff (n := ⊤))
  rw [coe_appendCLM] at h
  exact h

/-- The derivative of the graph map at `(x₀, y₀)`. -/
theorem hasFDerivAt_graphEval {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (x₀ : Fin n → ℝ) (y₀ : Fin q → ℝ) :
    HasFDerivAt (graphEval c F)
      (ContinuousLinearMap.pi fun j : Fin q =>
        ambDeriv c (F j) (Fin.append x₀ y₀) ∘SL appendCLM n q) (x₀, y₀) := by
  change HasFDerivAt (fun p : (Fin n → ℝ) × (Fin q → ℝ) => fun j : Fin q =>
      eaEval c (F j) (Fin.append p.1 p.2))
    (ContinuousLinearMap.pi fun j : Fin q =>
      ambDeriv c (F j) (Fin.append x₀ y₀) ∘SL appendCLM n q) (x₀, y₀)
  rw [hasFDerivAt_pi]
  intro j
  have happ : HasFDerivAt (fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2)
      (appendCLM n q) (x₀, y₀) := by
    have h : HasFDerivAt (⇑(appendCLM n q)) (appendCLM n q) (x₀, y₀) :=
      (appendCLM n q).hasFDerivAt
    rwa [coe_appendCLM] at h
  have hcomp := (Work.WilE9.EaD.eaD_hasFDerivAt c (F j) (Fin.append x₀ y₀)).comp (x₀, y₀) happ
  simpa only [ambDeriv, Function.comp_def] using hcomp

/-- Evaluation of the derivative of the graph map in a pure fibre direction: its matrix is the
fibre Jacobian `jm c F`. -/
theorem graphEval_snd {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (x₀ : Fin n → ℝ) (y₀ : Fin q → ℝ) (v : Fin q → ℝ) :
    ((ContinuousLinearMap.pi fun j : Fin q =>
        ambDeriv c (F j) (Fin.append x₀ y₀) ∘SL appendCLM n q)
      ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin q → ℝ)) v
      = Matrix.mulVec (Matrix.of fun j l => eaEval c (eaD c (Fin.natAdd n l) (F j))
          (Fin.append x₀ y₀)) v := by
  ext j
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    appendCLM_apply, ambDeriv_apply, Matrix.mulVec_apply_eq_sum]
  rw [Fin.sum_univ_add]
  have hzero : (∑ i : Fin n, eaEval c (eaD c (Fin.castAdd q i) (F j)) (Fin.append x₀ y₀)
      * (Fin.append 0 v) (Fin.castAdd q i)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Fin.append_left]
    simp
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Fin.append_right, Matrix.of_apply]

/-- **The fibre Jacobian stays invertible near a point where it is invertible.**  If `y` is
continuous at `x₀` and the fibre Jacobian of `F` along the graph of `y` is invertible at `x₀`,
it remains invertible on a neighbourhood. -/
theorem eventually_det_ne_zero {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (x₀ : Fin n → ℝ) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (hy : ContinuousAt y x₀)
    (h0 : (Matrix.map (jm c F) (fun P => eaEval c P (Fin.append x₀ (y x₀)))).det ≠ 0) :
    ∀ᶠ x in 𝓝 x₀,
      (Matrix.map (jm c F) (fun P => eaEval c P (Fin.append x (y x)))).det ≠ 0 := by
  have hfin : Continuous fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2 := by
    have h : Continuous (⇑(appendCLM n q)) := (appendCLM n q).continuous
    rwa [coe_appendCLM] at h
  have hP : Continuous fun p : (Fin n → ℝ) × (Fin q → ℝ) =>
      (Matrix.map (jm c F) (fun P => eaEval c P (Fin.append p.1 p.2))).det := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix (fun j l => ?_)
    have h1 : Continuous fun p : (Fin n → ℝ) × (Fin q → ℝ) =>
        eaEval c ((jm c F) j l) (Fin.append p.1 p.2) :=
      (Work.WilE9.EaD.eaEval_contDiff c ((jm c F) j l)).continuous.comp hfin
    simpa only [Matrix.map_apply] using h1
  have hgraph : ContinuousAt (fun x : Fin n → ℝ => (x, y x)) x₀ :=
    continuousAt_id.prodMk hy
  exact (hP.continuousAt.comp' hgraph).eventually_ne h0

/-- **Existence and smoothness half of the implicit function principle for a semi-Pfaffian
system.**  If `F : Fin q → EAPoly (n+q) r` vanishes at `(x₀, y₀)` and the fibre Jacobian
`∂F/∂y` is invertible there, then there is a `C^∞` map `y` on a neighbourhood of `x₀` with
`y x₀ = y₀`, `F (x, y x) = 0` there and the Jacobian still invertible there — i.e. a solution
satisfying `Work.WilE9.IsSoln`.  Mathlib's `ImplicitFunction` / `ImplicitContDiff` API supplies
the hard part, and `Work.WilE9.EaD.eaD_hasFDerivAt` identifies our Jacobian with the one Mathlib
sees.  Together with `Work.WilE9.Ift.ift_identity` (which takes such a `y` as input) this is what
turns the equations of an effectively smooth `SemiPf` piece into the BNZ formula for the
derivatives of the piece function. -/
theorem ift_exists {n q r : ℕ} (c : WilkiesDesign.E.EAChain (n + q) r)
    (F : Fin q → WilkiesDesign.E.EAPoly (n + q) r) (x₀ : Fin n → ℝ) (y₀ : Fin q → ℝ)
    (h0 : ∀ j, WilkiesDesign.E.eaEval c (F j) (Fin.append x₀ y₀) = 0)
    (hd : (Matrix.of fun j l =>
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd n l) (F j))
          (Fin.append x₀ y₀)).det ≠ 0) :
    ∃ y : (Fin n → ℝ) → (Fin q → ℝ),
      y x₀ = y₀ ∧ ContDiffAt ℝ ⊤ y x₀ ∧ Work.WilE9.IsSoln c F y x₀ := by
  classical
  -- the fibre Jacobian at `(x₀, y₀)`, i.e. the matrix appearing in `hd`
  set A : Matrix (Fin q) (Fin q) ℝ :=
    (Matrix.of fun j l => eaEval c (eaD c (Fin.natAdd n l) (F j)) (Fin.append x₀ y₀)) with hA
  have hAdet : A.det ≠ 0 := by
    simpa only [hA] using hd
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hAdet
  -- smoothness and derivative of the graph map
  have hcdf : ContDiffAt ℝ ⊤ (graphEval c F) (x₀, y₀) := (graphEval_contDiff c F).contDiffAt
  have hpn : (⊤ : WithTop ℕ∞) ≠ 0 := (WithTop.coe_lt_top (0 : ℕ∞)).ne'
  have hif₂ : ((fderiv ℝ (graphEval c F) (x₀, y₀))
      ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin q → ℝ)).IsInvertible := by
    have hpt : ∀ v : Fin q → ℝ,
        ((fderiv ℝ (graphEval c F) (x₀, y₀))
          ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin q → ℝ)) v = Matrix.mulVec A v := by
      intro v
      rw [(hasFDerivAt_graphEval c F x₀ y₀).fderiv, hA]
      exact graphEval_snd c F x₀ y₀ v
    refine ⟨(Matrix.toLinearEquiv' A (Matrix.invertibleOfIsUnitDet A hAunit)).toContinuousLinearEquiv,
      ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rw [hpt v]
    change (Matrix.toLin' A) v = Matrix.mulVec A v
    exact Matrix.toLin'_apply A v
  -- the implicit function supplied by Mathlib
  let y : (Fin n → ℝ) → (Fin q → ℝ) := hcdf.implicitFunction hpn hif₂
  have hyx0 : y x₀ = y₀ := hcdf.implicitFunction_apply_self hpn hif₂
  have hysmooth : ContDiffAt ℝ ⊤ y x₀ := hcdf.contDiffAt_implicitFunction hpn hif₂
  refine ⟨y, hyx0, hysmooth, ?_, ?_⟩
  · -- `F (x, y x) = 0` near `x₀`
    filter_upwards [hcdf.eventually_apply_implicitFunction hpn hif₂] with x hx
    intro j
    have h1 := congrFun hx j
    simp only [graphEval_apply] at h1
    rw [h1, h0 j]
  · -- the fibre Jacobian stays invertible near `x₀`
    refine eventually_det_ne_zero c F x₀ y hysmooth.continuousAt ?_
    rw [hyx0]
    have hmat : Matrix.map (jm c F) (fun P => eaEval c P (Fin.append x₀ y₀)) = A := by
      rw [hA]
      rfl
    rw [hmat]
    exact hAdet

end Work.WilE9.Ift
