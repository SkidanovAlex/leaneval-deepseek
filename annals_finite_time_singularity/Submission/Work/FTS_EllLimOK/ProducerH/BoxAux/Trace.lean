import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.PkgK6.vopTransferKSharp
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.RegExportIface.Producers
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
-- ===== merged: Submission.Work.FTS.EllSol.existsEllSolC_classC_of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.existsEllSolC_classC_of`

The class-`C` elliptic layer, in the "second order logic" form of the lead's design (A): from

* (`hb`) an *arbitrary* assignment `g ↦ Ψ` of a level-`8` solution to every profile `g` of the
  linear class `Work.FTS.ClassC.ClassC α g` (this is the existence node A2, here taken as a
  hypothesis, in the range `α ≤ 1/4`),
* (`hEst4`, `hEst6`) the uniform elliptic estimates at levels `4` and `6`,

build a **linear** solution operator `E : Fn →ₗ[ℝ] Fn` carrying both the `ℋ⁴`-package
`Work.FTS.VocabO.EllPkgGo` (owner `VocabO`) and the `ℋ⁶`-package `Work.FTS.ClassC.EllPkgK 6`,
i.e. the frozen `Prop` `Work.FTS.ClassC.ExistsEllSolC`.

## The route

* `Work.FTS.EllSol.ellPkgConj_of_classOk hEst4 hEst6` turns `EllClassOk 8` data over the older
  (7-field) class `Work.FTS.EllSol.ClassC` into the two packages at *one* constant `Ce` and one
  range `α ≤ α₀`.  The class `Work.FTS.ClassC.ClassC` implies that older class
  (`classC_to_ellSolClassC`; the extra fields `mem8`, `tr7` are simply dropped), and the two
  `EllPkgK` structures have identical fields (`ClassC.EllPkgK_of_ellSol`).
* The relation `P g Ψ := EllClassOk 8 α g Ψ ∧ EllPkgGo α Ce g Ψ ∧ EllPkgK α 6 Ce g Ψ` is
  `0`-inhabited (the zero profile: `ellClassOk_zero_eight_fts`) and closed under
  `(g, Ψ) ↦ (g + c • g', Ψ + c • Ψ')` over `ClassC α`: the first component is
  `Work.FTS.ClassC.ellClassOk_add_gen 8` (A3) and the two packages are *re-derived* from the
  hypothesis `ellPkgConj_of_classOk` rather than added.
* `Work.FTS.ClassC.exists_linear_selector_classC` (A6, the Hamel step) then produces the linear
  selector `E`.
-/

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The class `Work.FTS.ClassC.ClassC` (nine fields) implies the older class
`Work.FTS.EllSol.ClassC` (seven fields) of the `EllSol`/`VthAuxC` chain: the extra honesty fields
`mem8` and `tr7` are simply dropped. -/
theorem classC_to_ellSolClassC {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) :
    ClassC α g :=
  ⟨h.norm, h.reg, h.mem, h.tr, h.fsm, h.axis, h.l12⟩

/-- The two `EllPkgK` structures (in `Work.FTS.ClassC` and in `Work.FTS.EllSol`) have exactly the
same five fields, so either converts to the other. -/
theorem EllPkgK_of_ellSol {α : ℝ} {k : ℕ} {Ce : ℝ} {g Ψ : Fn}
    (h : EllPkgK α k Ce g Ψ) : Work.FTS.ClassC.EllPkgK α k Ce g Ψ :=
  ⟨h.sol, h.smooth, h.R, h.U, h.V⟩

/-- The zero profile has the zero level-`8` solution (the `0`-inhabitation of the relation used by
the Hamel step).  Verbatim the proof of `Work.FTS.ClassC.ellClassOk_zero_eight`, kept local so
that this module does not depend on the slot-based assembly `Work.FTS.ClassC.Main`. -/
theorem ellClassOk_zero_eight_fts (α : ℝ) :
    Work.FTS.EllExist.EllClassOk 8 α (0 : Fn) (0 : Fn) := by
  refine ⟨Work.FTS.EllipticEst.IsBslSol_zero α, ?_, ?_⟩
  · change ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => (0 : ℝ))
      Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  · have horth : Work.Elliptic.orthSource (0 : Fn) = (0 : Fn) := Work.FTS.EllSol.orthSource_zero
    have hsin : Work.FTS.EllExist.shiftSing α (0 : Fn) (0 : Fn) = (0 : Fn) := by
      funext z θ
      rw [Work.FTS.EllExist.shiftSing_apply, Work.FTS.EllSol.Gsing_zero]
      simp
    rw [horth, hsin]
    exact Work.FTS.EllSol.ellWeakPos_zero α 8


end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EpsEngine.RHSDataFeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.RHSDataFepsNoTraces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` energy bound of the projected scheme's right-hand side, trace-free form** (the
analogue of `HkIntegrand_perz_RHS` without the `htr` hypothesis). -/
theorem HkIntegrand_perz_RHS_noTraces {α Ce T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T) (hCe : 0 ≤ Ce)
    (hreg : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hmem : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hbd6 : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc 0 T,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_perz_le_noTraces
  refine ⟨C, hCpos, ?_⟩
  intro z hz s hs
  refine le_trans (hC α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) hα (hreg s hs) (hmem s hs)
    z hz) ?_
  have h1 : (1 : ℝ) ≤ 1 + Ce := by linarith
  have h2 : (1 : ℝ) + Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)
      ≤ 1 + Ce := by linarith [hbd6 s hs]
  have h3 : (0 : ℝ)
      ≤ 1 + Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) := by
    have := Work.Spaces.HkNorm_nonneg α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)
    rw [Work.FTS.StrongGlobal.Xn6]
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 2)
    (mul_nonneg hCpos.le (by positivity))

/-- **The per-`z` energy bound of the scheme's right-hand side along an `XBall` curve, with no
trace input.** -/
theorem perz_Feps_noTraces {α C₀ Ce Cs R ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F₀ : ℝ → Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hX : ∀ s ∈ Set.Icc (0 : ℝ) T, XBall α ρ ε R C₀ (F₀ s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Feps α ρ ε Φs E (F₀ s)) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  set G : Fam := fun z θ s => F₀ s z θ with hG
  have hslice : ∀ s : ℝ, slice G s = F₀ s := fun s => rfl
  have hRH : ∀ s : ℝ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E G s = Feps α ρ ε Φs E (F₀ s) := by
    intro s
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice, hslice s]
  obtain ⟨C, hCpos, hC⟩ :=
    HkIntegrand_perz_RHS_noTraces (α := α) (Ce := Ce') (T := T) (ε := ε) (ρ := ρ) (Φs := Φs)
      (E := E) (g := G) hα hε hε1 hT hCe'pos.le
      (fun s hs => by rw [hRH s]; exact (hFeps (F₀ s) (hX s hs)).1)
      (fun s hs => by rw [hRH s]; exact (hFeps (F₀ s) (hX s hs)).2.1)
      (fun s hs => by
        rw [Work.FTS.StrongGlobal.Xn6, hRH s]
        exact (hFeps (F₀ s) (hX s hs)).2.2)
  refine ⟨C * (1 + Ce') ^ 2, by positivity, ?_⟩
  intro z hz s hs
  have h := hC z hz s hs
  rw [hRH s] at h
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Feps α ρ ε Φs E (F₀ s)) z θ)
      ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 := h
    _ = C * (1 + Ce') ^ 2 * (1 + (Work.Spaces.w z) ^ 2) := by ring

/-- **`RHSData` for the scheme's right-hand side, with NO trace input.**  For every Picard index
`n`: if the curve `s ↦ slice (iter (Feps …) g₀ n) s` lies in the `XBall` invariant and is
`EpsSq`-Lipschitz in `s`, then the per-curve data `RHSData α 4 T B (Feps …) g₀ n` holds, with a
constant `B` depending only on `α, ε, C₀, Ce, Cs, R`. -/
theorem exists_RHSData_feps_noTraces {α C₀ Ce Cs R Lw ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        XBall α ρ ε R C₀ (slice (iter (Feps α ρ ε Φs E) g₀ n) s)) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.StrongEps.EpsSq α (fun z θ =>
          slice (iter (Feps α ρ ε Φs E) g₀ n) s z θ
            - slice (iter (Feps α ρ ε Φs E) g₀ n) t z θ)
          ≤ Lw * (s - t) ^ 2) →
      RHSData α 4 T B (Feps α ρ ε Φs E) g₀ n := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  refine ⟨Ce', hCe'pos, ?_⟩
  intro n hP hEq
  obtain ⟨Cz, hCzpos, hCz⟩ := perz_Feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (R := R) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E)
    (F₀ := fun s => slice (iter (Feps α ρ ε Φs E) g₀ n) s)
    hρ hα hε hε1 hR hT hEll hstar hml hP
  have hgates := Feps_gates_of_xball_curve (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := T) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E)
    (g := iter (Feps α ρ ε Φs E) g₀ n) hα hρ hε hε1 hEll hstar hml hR hLw hP hEq
  refine ⟨fun s hs => (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).1,
    fun s hs => Work.FTS.OpenPkg.HkMem_mono_open
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).1 4 (by norm_num)
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).2.1,
    fun s hs => le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num)
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).2.1)
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).2.2,
    hgates.1, hgates.2.1, hgates.2.2,
    fun z hz => ⟨Cz * (1 + (Work.Spaces.w z) ^ 2),
      fun s hs => hCz z hz s hs⟩⟩

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.intervalIntegrable_slice_epsRHSP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

theorem intervalIntegrable_slice_epsRHSP {α C₁ Ce Cs R ε δ Lw : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 ≤ δ) (hLw : 0 ≤ Lw)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      IntervalIntegrable (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice g u) z θ) MeasureTheory.volume 0 δ := by
  intro z θ hzθ
  obtain ⟨hz, hθ1, hθ2⟩ := hzθ
  -- the pointwise Lipschitz gate of the scheme's right-hand side on the `X`-ball
  obtain ⟨C, hCpos, hpt⟩ :=
    Work.FTS.EpsEngine.pt_of_XBall (α := α) (C₀ := C₁) (R := R) (Ce := Ce) (Cs := Cs)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
  -- the curve is `EpsSq`-Lipschitz in the fake time, hence the integrand is Lipschitz in `u`
  have hstep : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g t) z θ|
        ≤ (C * Real.sqrt Lw) * |s - t| := by
    intro s hs t ht
    have h1 := hpt (Work.FTS.Galerkin.slice g s) (Work.FTS.Galerkin.slice g t)
      (hX s hs) (hX t ht) z θ hz hθ1 hθ2
    have h2 : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ))
        ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s hs t ht)
    calc |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g t) z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
            Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (C * Real.sqrt Lw) * |s - t| := by ring
  have hLipOn : LipschitzOnWith ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg Lw)⟩
      (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ)
      (Set.Icc 0 δ) :=
    LipschitzOnWith.of_dist_le_mul (fun s hs t ht => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hstep s hs t ht)
  exact ContinuousOn.intervalIntegrable_of_Icc hδ hLipOn.continuousOn

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/BoxAux/Trace` — the two angular traces of `E g`

The pointwise (in `z`) vanishing of `E g` at both angular endpoints, for a stream function
carrying the level-`8` existence class.  This is the `(T)` of `ProducerH/NOTES_pkgBoxH.md` §4,
at the *value* level: the junk values `E g z 0 = E g z (π/2) = 0` prescribed by `IsBslSol`
are the one-sided limits.

The proof reuses the tree's `ClassC.VopAux.vopTracesPointwise_classC` (traces of the radial
iterates `D_z^j Ξ` of the residual `Ξ = PhiTil α g (E g)` at both endpoints, `j ≤ 6`), by
writing `E g = Ξ + Θ` with `Θ = (1/(4α)) sin 2θ · L₁₂ g` an explicit `θ`-continuous function
vanishing at both endpoints.

Everything is `sorry`-free.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The residual `Φ̃ = PhiTil α g (E g)` is the elliptic residual `EllResid α g (E g)`. -/
theorem phiTil_eq (α : ℝ) (g Ψ : Fn) :
    Work.Construction.PhiTil α g Ψ = Work.Elliptic.EllResid α g Ψ :=
  Work.FTS.ClassC.phiTil_eq_EllResid_gen α g Ψ

/-- The shifted decomposition `E g = Φ̃ + Θ`, with `Θ α g z θ = (1/(4α)) sin 2θ · L₁₂ g z`. -/
theorem Eg_eq_phiTil_add (α : ℝ) (g Ψ : Fn) :
    Ψ = fun z θ => Work.Construction.PhiTil α g Ψ z θ + Work.Construction.Theta α g z θ := by
  funext z θ
  simp only [Work.Construction.PhiTil]
  ring

/-- The pointwise decomposition `E g = Φ̃ + Θ`, in the `θ`-slice form used below. -/
theorem slice_eq_phiTil_add (α : ℝ) (g Ψ : Fn) (z : ℝ) :
    (fun θ => Ψ z θ)
      = fun θ => Work.Construction.PhiTil α g Ψ z θ + Work.Construction.Theta α g z θ := by
  funext θ
  have h := congrFun (congrFun (Eg_eq_phiTil_add α g Ψ) z) θ
  simpa only [Pi.add_apply] using h

/-- `Θ α g z ·` tends to `0` at both angular endpoints (the `z`-factor `L₁₂ g z` is fixed). -/
theorem tendsto_Theta (α : ℝ) (g : Fn) (z : ℝ) :
    (Filter.Tendsto (fun θ => Work.Construction.Theta α g z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => Work.Construction.Theta α g z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hfun : Work.Construction.Theta α g z
      = fun θ => (1 / (4 * α)) * Work.Construction.L12 g z * Real.sin (2 * θ) := by
    funext θ
    simp only [Work.Construction.Theta, Work.Construction.s2_eq]
    ring
  rw [hfun]
  constructor
  · have h2 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) 0 :=
        Real.continuous_sin.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h2.const_mul ((1 / (4 * α)) * Work.Construction.L12 g z)
  · have h2 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hc : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.pi / 2) :=
        Real.continuous_sin.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      have h3 := hc.tendsto.mono_left (nhdsWithin_le_nhds :
        nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ nhds (Real.pi / 2))
      rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi] at h3
      simpa using h3
    simpa using h2.const_mul ((1 / (4 * α)) * Work.Construction.L12 g z)

/-- **The `θ = 0⁺` trace of `E g`.** -/
theorem tendsto_Eg_at_zero {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ => (E g) z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hO7 : Work.FTS.EllExist.EllClassOk 7 α g (E g) :=
    Work.FTS.EllSol.ellClassOk_eight_seven (hE g hg).1
  have htr := (Work.FTS.ClassC.VopAux.vopTracesPointwise_classC 0 (by norm_num) α g (E g)
    hα hα4 hg hO7 z hz).1
  have htr' : Filter.Tendsto (fun θ => Work.Construction.PhiTil α g (E g) z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Work.Spaces.DzIter_zero, phiTil_eq] using htr
  rw [slice_eq_phiTil_add α g (E g) z]
  simpa using htr'.add (tendsto_Theta α g z).1

/-- **The `θ = π/2⁻` trace of `E g`.** -/
theorem tendsto_Eg_at_pi_half {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ => (E g) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hO7 : Work.FTS.EllExist.EllClassOk 7 α g (E g) :=
    Work.FTS.EllSol.ellClassOk_eight_seven (hE g hg).1
  have htr := (Work.FTS.ClassC.VopAux.vopTracesPointwise_classC 0 (by norm_num) α g (E g)
    hα hα4 hg hO7 z hz).2
  have htr' : Filter.Tendsto (fun θ => Work.Construction.PhiTil α g (E g) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [Work.Spaces.DzIter_zero, phiTil_eq] using htr
  rw [slice_eq_phiTil_add α g (E g) z]
  simpa using htr'.add (tendsto_Theta α g z).2

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
