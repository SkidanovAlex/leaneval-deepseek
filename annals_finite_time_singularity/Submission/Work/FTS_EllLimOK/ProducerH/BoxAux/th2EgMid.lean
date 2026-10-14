import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongGlobal.Global
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
-- ===== merged: Submission.Work.FTS.ClassC.A4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Monotonicity of the solution class in the level -/


/-! ## The trace clause of the `U`-slot, from the Dirichlet data -/

/-- `EllResid α g Ψ` vanishes identically at `θ = 0` when `Ψ` does. -/
theorem EllResid_at_zero {α : ℝ} {g Ψ : Fn} (h : ∀ z, Ψ z 0 = 0) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z 0 = 0 := by
  rw [Work.Elliptic.EllResid]
  simp [h z]

/-- `EllResid α g Ψ` vanishes identically at `θ = π/2` when `Ψ` does. -/
theorem EllResid_at_pi_half {α : ℝ} {g Ψ : Fn} (h : ∀ z, Ψ z (π / 2) = 0) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z (π / 2) = 0 := by
  rw [Work.Elliptic.EllResid]
  simp only [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
  simp [h z]

/-- `∂_z` of a function vanishing identically at an angle vanishes there. -/
theorem pz_eq_zero_of_forall_eq_zero {f : Fn} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0) (z : ℝ) :
    Work.Spaces.pz f z θ₀ = 0 := by
  have hfun : (fun z' : ℝ => f z' θ₀) = fun _ => (0 : ℝ) := funext h
  simp only [Work.Spaces.pz, hfun]
  exact deriv_const z (0 : ℝ)

/-- **The `vanishU` clause of `EllPkgGo` holds for every level-`7` solution** (no trace
hypothesis is needed: it comes from the two Dirichlet values of `Ψ`). -/
theorem vanishU_of_classOk {α : ℝ} {g Ψ : Fn} (h : Work.FTS.EllExist.EllClassOk 7 α g Ψ) :
    Work.Spaces.VanishTheta
      (Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ)) := by
  rw [Work.FTS.EllipticEst.Uop_PhiTil_eq]
  have h0 : ∀ z, Work.Elliptic.EllResid α g Ψ z 0 = 0 := fun z => EllResid_at_zero h.1.2.1 z
  have hπ : ∀ z, Work.Elliptic.EllResid α g Ψ z (π / 2) = 0 :=
    fun z => EllResid_at_pi_half h.1.2.2.1 z
  constructor
  · intro z
    have h1 := pz_eq_zero_of_forall_eq_zero h0 z
    simp only [Work.FTS.EllipticEst.Uop, h0 z, h1]
    ring
  · intro z
    have h1 := pz_eq_zero_of_forall_eq_zero hπ z
    simp only [Work.FTS.EllipticEst.Uop, hπ z, h1]
    ring

/-! ## The four slot estimates, at a fixed constant -/









/-! ## The two packages -/





/-! ## Monotonicity of the packages in the constant -/

/-- `EllPkgK` is monotone in the constant. -/
theorem EllPkgK_mono {α : ℝ} {k : ℕ} {Ce Ce' : ℝ} {g Φg : Fn}
    (h : EllPkgK α k Ce g Φg) (hle : Ce ≤ Ce') : EllPkgK α k Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩⟩ := h
  have hgnn : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hmon : ∀ X : ℝ, X ≤ Ce * Work.Spaces.HkNorm α k g →
      X ≤ Ce' * Work.Spaces.HkNorm α k g :=
    fun X hX => le_trans hX (mul_le_mul_of_nonneg_right hle hgnn)
  exact ⟨h1, h2, ⟨hRm, hmon _ hRb⟩, ⟨hUm, hmon _ hUb⟩, ⟨hVm, hmon _ hVb⟩⟩

/-- `EllPkgGo` is monotone in the constant (`0 < α` is needed only to keep the
`α^{-1/2}`-factor nonnegative). -/
theorem EllPkgGo_mono {α Ce Ce' : ℝ} {g Φg : Fn} (hα : 0 < α)
    (h : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hle : Ce ≤ Ce') :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩, hv, ⟨hTm, hTb⟩⟩ := h
  have hgnn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  refine ⟨h1, h2, ⟨hRm, ?_⟩, ⟨hUm, ?_⟩, ⟨hVm, ?_⟩, hv, ⟨hTm, ?_⟩⟩
  · exact le_trans hRb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hUb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hVb (mul_le_mul_of_nonneg_right hle hgnn)
  · refine le_trans hTb ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hαp) hgnn

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem vopPhiTil_jets_le_Xn6 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn}
    (hE : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      ∀ b : ℕ, b ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Spaces.mixed b 0
            (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le α hα hα1
  refine ⟨C0 * (|Ce| + 1), by positivity, ?_⟩
  intro g hg b hb z θ hz hθ
  obtain ⟨hVsm, hVmem⟩ := (hE g hg).2.2.V.1
  have hVnorm : Work.Spaces.HkNorm α 6
      (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) ≤ Ce * Work.Spaces.HkNorm α 6 g :=
    (hE g hg).2.2.V.2
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have h1 : |Work.Spaces.mixed b 0
        (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) z θ|
      ≤ C0 * Work.Spaces.HkNorm α 6
        (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) :=
    hC0 _ hVsm hVmem b 0 (by omega) z θ hz hθ.1 hθ.2
  have h2 : Work.Spaces.HkNorm α 6
        (Work.Construction.Vop (Work.Construction.PhiTil α g (E g)))
      ≤ |Ce| * Work.FTS.StrongGlobal.Xn6 α g := by
    refine le_trans hVnorm ?_
    simpa only [Work.FTS.StrongGlobal.Xn6] using
      mul_le_mul_of_nonneg_right (le_abs_self Ce) hXnn
  refine le_trans (le_trans h1 (mul_le_mul_of_nonneg_left h2 hC0pos.le)) ?_
  have hCe1 : 0 ≤ |Ce| + 1 := by positivity
  nlinarith [hXnn, hC0pos, hCe1, h2, le_abs_self Ce]

/-- `D_z^j` of a function which does not depend on `θ` does not depend on `θ`. -/
theorem dzIter_theta_indep (R : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => R z) z θ
      = Work.Spaces.DzIter j (fun z _ => R z) z 0 := by
  induction j generalizing z with
  | zero => rfl
  | succ k ih =>
      show z * deriv (fun z' => Work.Spaces.DzIter k (fun z _ => R z) z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter k (fun z _ => R z) z' 0) z
      rw [Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall fun z' => ih z')]

/-! ## The rate of the radial iterates of the singular part `Θ` -/

theorem thetaDz_le_min {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g → ∀ j : ℕ, j ≤ 4 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Spaces.DzIter j (Work.Construction.Theta α g) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS_EllLimOK.PkgJets.L12jets_classC hα hα1
  refine ⟨(1 / (4 * α)) * CL * 2, by positivity, ?_⟩
  intro g hg j hj z θ hz hθ
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  -- `D_z^j Θ = ((1/(4α)) sin 2θ) · D_z^j (L₁₂ g)`
  have hfun : Work.Construction.Theta α g
      = fun z θ => ((1 / (4 * α)) * Real.sin (2 * θ)) *
          (fun z _ => Work.Construction.L12 g z) z θ := by
    funext z θ
    simp only [Work.Construction.Theta, Work.Construction.s2]
  have hDz : Work.Spaces.DzIter j (Work.Construction.Theta α g) z θ
      = ((1 / (4 * α)) * Real.sin (2 * θ))
        * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z θ := by
    rw [hfun]
    exact Work.FTS.TransportS.SupDzAux.sda_DzIter_const_mul_th
      (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))
      (fun z _ => Work.Construction.L12 g z) j z θ
  rw [hDz, abs_mul]
  have hc0 : 0 ≤ (1 / (4 * α)) * Real.sin (2 * θ) := by
    refine mul_nonneg (by positivity) ?_
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [abs_of_nonneg hc0]
  rw [dzIter_theta_indep (fun z => Work.Construction.L12 g z) j z θ]
  have hL := hCL g hg j hj z hz
  have hsin := sin_two_le_two_min hθ
  have hm0 : 0 ≤ min θ (π / 2 - θ) := le_of_lt (lt_min hθ.1 (by linarith [hθ.2]))
  have hA : 0 ≤ (1 / (4 * α)) * (2 * min θ (π / 2 - θ)) := mul_nonneg (by positivity) (by linarith)
  have hB : 0 ≤ CL * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hCLpos.le hXnn
  calc (1 / (4 * α)) * Real.sin (2 * θ)
        * |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
      ≤ ((1 / (4 * α)) * (2 * min θ (π / 2 - θ)))
          * (CL * Work.FTS.StrongGlobal.Xn6 α g) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsin (by positivity)) hL (abs_nonneg _) hA
    _ = ((1 / (4 * α)) * CL * 2) * Work.FTS.StrongGlobal.Xn6 α g
          * min θ (π / 2 - θ) := by ring

/-- Linearity of `D_z^j` in a sum with an angular multiplier (open-quadrant form). -/
theorem dzIter_add_const_mul_aux {A F : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (c : ℝ → ℝ) :
    ∀ j : ℕ, ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.DzIter j (fun z θ => A z θ + c θ * F z θ) z θ
        = Work.Spaces.DzIter j A z θ + c θ * Work.Spaces.DzIter j F z θ := by
  intro j
  induction j with
  | zero => intro z hz θ hθ; rfl
  | succ k ih =>
      intro z hz θ hθ
      have hdf : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter k A z' θ) z :=
        (((hA.DzIter k).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hdg : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter k F z' θ) z :=
        (((hF.DzIter k).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hev : (fun z' => Work.Spaces.DzIter k (fun z θ => A z θ + c θ * F z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter k A z' θ + c θ * Work.Spaces.DzIter k F z' θ) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz)
          (fun z' hz' => ih z' hz' θ hθ)
      show z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => A z θ + c θ * F z θ) z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter k A z' θ) z
          + c θ * (z * deriv (fun z' => Work.Spaces.DzIter k F z' θ) z)
      rw [hev.deriv_eq]
      change z * deriv ((fun z' => Work.Spaces.DzIter k A z' θ)
        + fun z' => c θ * Work.Spaces.DzIter k F z' θ) z = _
      rw [deriv_add hdf (hdg.const_mul (c θ)), deriv_const_mul_field]
      ring


end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
