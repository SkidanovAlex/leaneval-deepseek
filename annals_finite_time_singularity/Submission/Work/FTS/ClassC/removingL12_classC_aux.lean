import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_norm
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.Cert.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Elliptic.Gsing_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.removingL12_classC_aux` — helpers for `removingL12_classC`

The bookkeeping of the `ClassC` / `EllClassOk 7` instance of Elgindi's Theorem `RemovingL12`
(tex 1034), kept in a separate module so that the target file stays inside the build guard's
size limit:

* `hkNorm_congr_classC` — `HkNorm` only sees the open quadrant;
* `smoothOpen_pthIter_classC` — `∂_θ`-iterates preserve open-quadrant smoothness;
* `scCoeff` and its norm bound ingredients — the coefficient of the radial removal;
* `ellWeakPos_descend` — the weak class `TT.EllWeakPos` descends in the level;
* `orthSource_HkNorm_le_classC` — `|orthSource g|_{ℋ^k} ≤ C|g|_{ℋ^k}` on `ClassC`;
* `gsing_certs_classC` — the classical certificates of the singular term on `ClassC`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## Elementary closure facts -/

/-- `HkNorm` only sees the open quadrant. -/
theorem hkNorm_congr_classC (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-- `∂_θ`-iterates of a function `C^∞` on the open quadrant are `C^∞` there. -/
theorem smoothOpen_pthIter_classC {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- The coefficient of the radial removal:
`α² z² ∂_z²Ψ = α² z² ∂_z²Ψ̂ - scCoeff` with `Ψ̂ = Ψ + Gsing α g · sin 2θ`. -/
def scCoeff (α : ℝ) (g : Fn) : Fn :=
  fun z θ => (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar g z)
    + 5 * (5 + α) * (Real.sin (2 * θ) * Work.Elliptic.Gbar α g z)

theorem scCoeff_apply (α : ℝ) (g : Fn) (z θ : ℝ) :
    scCoeff α g z θ
      = (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar g z)
        + 5 * (5 + α) * (Real.sin (2 * θ) * Work.Elliptic.Gbar α g z) := rfl

theorem scCoeff_eq (α : ℝ) (g : Fn) :
    scCoeff α g = fun z θ => (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar g z)
      + 5 * (5 + α) * (Real.sin (2 * θ) * Work.Elliptic.Gbar α g z) := rfl

/-! ## Descent of the weak class in the level -/

/-- **`TT.EllWeakPos` descends in the level**: the four `HkMem` fields descend by
`TT.HkMem_descend_open` (the open-quadrant smoothness of the four functions is available from the
smoothness of `F` and `Ψ`), and the remaining fields are level-free. -/
theorem ellWeakPos_descend {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {k l : ℕ} (hkl : k ≤ l)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ := by
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.zsq_mul (hΨ.pzIter 2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter_classC hΨ 2
  have hZ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := hB.Dz
  exact ⟨h.eq, h.zero, h.pi_half, (fun z hz => h.orthF z hz), (fun z hz => h.orthPsi z hz),
    h.smooth,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hF.forall h.memF,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hA.forall h.memA,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hB.forall h.memB,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hZ.forall h.memZPth2⟩

/-! ## The source comparison on `ClassC` -/

/-- `orthSource g = g - (15/4) F_*(g)·sin 2θ`, so its `ℋ^k`-norm is bounded by `C|g|_{ℋ^k}`
(only `k ≤ 7` is used, for the descent of `HkMem α 7 g`). -/
theorem orthSource_HkNorm_le_classC (k : ℕ) (hk7 : k ≤ 7) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : Fn), 0 < α → α ≤ 1 → ClassC α g →
      Work.Spaces.HkNorm α k (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α k g := by
  obtain ⟨CF, hCFpos, hFle⟩ := Work.FTS.EllipticEst.Cert.Fstar_Hk_le_open k
  refine ⟨Real.sqrt 2 * (1 + (15 / 4) * CF), by positivity, ?_⟩
  intro α g hα hα1 hg
  have hso : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hmem : Work.Spaces.HkMem α k g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open hk7 hso.forall hg.mem
  have hsinso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul hg.fsm (by fun_prop)
  have hsinmem : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k g hα hα1 hso hmem
  have hcsinmem : Work.Spaces.HkMem α k
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4)) hsinmem
  have hcsinso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' (-(15 / 4)) hsinso
  have hcongr : Work.Spaces.HkSq α k (Work.Elliptic.orthSource g)
      = Work.Spaces.HkSq α k (fun z θ => g z θ
          + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by
    refine Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => ?_)
    simp only [Work.Elliptic.orthSource]; ring
  have htri := Work.FTS.EllipticEst.HkNorm_add_le α k (f := g)
    (g := fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
    hso.forall hcsinso.forall hmem hcsinmem
  have hcm : Work.Spaces.HkNorm α k
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
      = (15 / 4) * Work.Spaces.HkNorm α k
          (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k (-(15 / 4)) hsinso.forall,
      show |(-(15 / 4) : ℝ)| = 15 / 4 by norm_num]
  have hFl := hFle α g hα hα1 hso.forall hmem
  have hnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α k
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
    Work.Spaces.HkNorm_nonneg α k _
  have hgnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  calc Work.Spaces.HkNorm α k (Work.Elliptic.orthSource g)
      = Work.Spaces.HkNorm α k (fun z θ => g z θ
          + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hcongr]
    _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k g
          + Work.Spaces.HkNorm α k
              (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))) := htri
    _ = Real.sqrt 2 * (Work.Spaces.HkNorm α k g
          + (15 / 4) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by rw [hcm]
    _ ≤ Real.sqrt 2 * ((1 + (15 / 4) * CF) * Work.Spaces.HkNorm α k g) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        have h1 := mul_le_mul_of_nonneg_left hFl (by norm_num : (0:ℝ) ≤ 15 / 4)
        have h2 : (15 / 4) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))
            ≤ (15 / 4) * (CF * Work.Spaces.HkNorm α k g) := h1
        nlinarith [h2, hgnn, mul_nonneg hCFpos.le hgnn]
    _ = (Real.sqrt 2 * (1 + (15 / 4) * CF)) * Work.Spaces.HkNorm α k g := by ring

/-! ## The classical certificates of the singular term on `ClassC` -/

/-- **The certificates of `Gsing α g` for `ClassC`-data.**  The angular moment `F_*(g)`, the
singular term `Gsing α g` and its lower part `Ḡ α g` are `C^∞` on `(0,∞)`, and `G = Gsing α g`
satisfies the two ODE relations behind the removal identities. -/
theorem gsing_certs_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Fn} (hg : ClassC α g) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α g) (Set.Ioi 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α g) z = -5 * Work.Elliptic.Gbar α g z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z) := by
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hg.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hg.reg hg.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar g) (deriv (Work.Elliptic.Fstar g) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  exact ⟨hFsm,
    (Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α g hα hFsm hFint hL12).1,
    Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hFsm hFint,
    Work.FTS.EllipticEst.Gsing_deriv_rel α g hα hL12 hFc hJ,
    Work.Elliptic.Gsing_ode α g hα hL12 hFc hJ⟩

end Work.FTS.ClassC
