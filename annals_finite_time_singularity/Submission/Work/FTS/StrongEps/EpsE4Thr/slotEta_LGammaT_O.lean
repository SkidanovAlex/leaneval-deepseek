import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotEta_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_B_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.psiA_eta_abs_le_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.gPsi_eta_abs_le_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_EDthW_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The `η`-slot of the level-1 coercivity of `𝓛_Γ^T` in the **open** class

The frozen `Work.FTS.CoercivityFix.Coer1T.slotEta_LGammaT` proves

  `(1/5)·EfEta(f) − 10⁵·(EL12z(f) + EDthW(f) + Ef(f)) ≤ ⟨𝓛_Γ^T f, f⟩_{w² sin^{-η}}`

for `f ∈ Work.FTS.Nonlin.CoerAdm α f` (which carries `RegQ α 5`, hence `SmoothQuad`, the
`C^∞`-on-the-strip class) and derives the whole integrability bundle internally.

The route's data only ever supplies the *open*-quadrant class `RegQo`/`CoerAdmO` (the projected
mollified slice is `SmoothOpen` but never `SmoothQuad`, `not_smoothQuad_Pz_Jeps`), so this file
re-runs the same estimate on the open class, taking the integrability bundle `IntPkgO α f` as a
hypothesis.  The three analytic inputs are the open-class twins

* `OClass.psiA_eta_abs_le_O` — `|⟨T1fun α f, f⟩_{w²sin^{-η}}| ≤ 220·√(EL12z f)·√(EfEta f)`;
* `OClass.gPsi_eta_abs_le_O` — `|⟨T4fun α f, f⟩_{w²sin^{-η}}| ≤ 220·|C₀(f)|·√(EfEta f)`;
* `OClass.C0_sq_le_EDthW_O` — `(C₀(f))² ≤ EDthW(f)`,

and the coercivity `OClass.est_B_O` of the clean operator `𝓛̂ = 𝓛 − Transport`,

  `(47/100)·EfEta(f) ≤ ⟨𝓛̂ f, f⟩_{w²sin^{-η}}`,

obtained from the paper's identity `(LW)` (`Coer1SO.wip_L_self_QO`) and the open-class
angular-transport bound `wip_transport_le_O` (`|η − 1| = 1/100`).  The assembly is the frozen
one: `𝓛_Γ^T = 𝓛 − T1fun − Transport + T4fun` (`LGammaT_eq_sum`), one Cauchy–Schwarz/Young pair
with `δ = 1/8` for the two corrections (`220²/(4·(1/8)) = 96800 < 10⁵`), leaving
`0.47 − 0.25 = 0.22 ≥ 1/5`.

Everything here is `sorry`-free.
-/

theorem slotEta_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) (hG : Work.Coercivity.GammaL2Bnd α) :
    (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f + Work.Coercivity.Ef f)
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f := by
  have hα1' : α ≤ 1 := by linarith
  have hf2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f :=
    Work.FTS.StrongEps.EpsE4Thr.regQo_mono (α := α) (f := f) (k := 2) (l := 5)
      (by norm_num) hf.1
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  -- integrability of `f² w² sin^{-η}`
  have hEfEta_int : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hIP.sqDzEta 0 (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
    ring
  -- integrability of `(D_θ f)² w²`
  have hDthW_int : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    ring
  -- ### The three inputs from the `η`-slot estimates
  have hT1 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T1fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T1fun α f) f|
          ≤ 220 * Real.sqrt (Work.Coercivity.EL12z f) * Real.sqrt (Work.Coercivity.EfEta f) :=
    Work.FTS.StrongEps.EpsE4Thr.OClass.psiA_eta_abs_le_O α hα hα1' hso hHH hEfEta_int
  have hT4 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T4fun α f) f|
          ≤ 220 * |Work.Coercivity.C0 f| * Real.sqrt (Work.Coercivity.EfEta f) :=
    Work.FTS.StrongEps.EpsE4Thr.OClass.gPsi_eta_abs_le_O α hα hα1' hso hEfEta_int
  have hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f :=
    Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_EDthW_O hso hDthW_int
  -- ### Nonnegativity of the energies
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEfEta_nn : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Work.Coercivity.EfEta, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hELnn : 0 ≤ Work.Coercivity.EL12z f := by
    rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  have hEDnn : 0 ≤ Work.Coercivity.EDthW f := by
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  -- ### `|C0 f| ≤ √(EDthW f)`
  have hC0abs : |Work.Coercivity.C0 f| ≤ Real.sqrt (Work.Coercivity.EDthW f) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hC0
  have hT4' : |Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.T4fun α f) f|
      ≤ 220 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.EfEta f) := by
    have h1 : 220 * |Work.Coercivity.C0 f| ≤ 220 * Real.sqrt (Work.Coercivity.EDthW f) :=
      mul_le_mul_of_nonneg_left hC0abs (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (Work.Coercivity.EfEta f))
    exact hT4.2.trans h2
  -- ### Young's inequalities
  have hyoung1 : 220 * Real.sqrt (Work.Coercivity.EL12z f) * Real.sqrt (Work.Coercivity.EfEta f)
      ≤ (1 / 8) * Work.Coercivity.EfEta f + 96800 * Work.Coercivity.EL12z f := by
    have h := Work.Coercivity.young_abs 220 (1 / 8) (Real.sqrt (Work.Coercivity.EfEta f))
      (Real.sqrt (Work.Coercivity.EL12z f)) (by norm_num)
    rw [Real.sq_sqrt hEfEta_nn, Real.sq_sqrt hELnn] at h
    have h2 : (220 : ℝ) ^ 2 / (4 * (1 / 8)) = 96800 := by norm_num
    rw [h2] at h
    calc 220 * Real.sqrt (Work.Coercivity.EL12z f) * Real.sqrt (Work.Coercivity.EfEta f)
        = 220 * Real.sqrt (Work.Coercivity.EfEta f) * Real.sqrt (Work.Coercivity.EL12z f) := by
          ring
      _ ≤ (1 / 8) * Work.Coercivity.EfEta f + 96800 * Work.Coercivity.EL12z f := h
  have hyoung2 : 220 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.EfEta f)
      ≤ (1 / 8) * Work.Coercivity.EfEta f + 96800 * Work.Coercivity.EDthW f := by
    have h := Work.Coercivity.young_abs 220 (1 / 8) (Real.sqrt (Work.Coercivity.EfEta f))
      (Real.sqrt (Work.Coercivity.EDthW f)) (by norm_num)
    rw [Real.sq_sqrt hEfEta_nn, Real.sq_sqrt hEDnn] at h
    have h2 : (220 : ℝ) ^ 2 / (4 * (1 / 8)) = 96800 := by norm_num
    rw [h2] at h
    calc 220 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.EfEta f)
        = 220 * Real.sqrt (Work.Coercivity.EfEta f) * Real.sqrt (Work.Coercivity.EDthW f) := by
          ring
      _ ≤ (1 / 8) * Work.Coercivity.EfEta f + 96800 * Work.Coercivity.EDthW f := h
  -- ### The integrability certificates for the four summands
  have hLint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hIP.intL_f_eta.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
  have hTrint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Work.FTS.CoercivityFix.Coer1.intTransport_of hIP.hint_f_eta
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
  have hT1int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.T1fun α f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hT1.1.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  have hT4int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.T4fun α f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hT4.1.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  -- ### The decomposition of `𝓛_Γ^T` and the split of the pairing
  have hsum := Work.Coercivity.LGammaT_eq_sum α f
  have hsplit := Work.Coercivity.wip_sub_add
    (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
    (Work.Coercivity.L f) (Work.Coercivity.T1fun α f) (Work.Coercivity.Transport f)
    (Work.Coercivity.T4fun α f) f hLint hT1int hTrint hT4int
  have hLhatSplit : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.L f) f
        - Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.Transport f) f :=
    Work.FTS.CoercivityFix.Coer1.wip_sub_left
      (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (A := Work.Coercivity.L f) (B := Work.Coercivity.Transport f) (C := f) hLint hTrint
  -- ### The coercivity of `𝓛̂` on the open class
  have hB := Work.FTS.StrongEps.EpsE4Thr.est_B_O α hα (by linarith : α ≤ 1 / 4) hf2 hIP
  have hweight : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.FTS.CoercivityFix.Lhat f) f := rfl
  have hB' : (47 / 100) * Work.Coercivity.EfEta f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.FTS.CoercivityFix.Lhat f) f := by
    rw [Work.FTS.CoercivityFix.Coer1.EfEta_eq_En, ← hweight]
    exact hB
  -- ### The two lower bounds on the corrections
  have hT1b : Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T1fun α f) f
        ≤ 220 * Real.sqrt (Work.Coercivity.EL12z f) * Real.sqrt (Work.Coercivity.EfEta f) := by
    have h := le_abs_self (Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Coercivity.T1fun α f) f)
    linarith [h, hT1.2]
  have hT4b : -(220 * Real.sqrt (Work.Coercivity.EDthW f)
        * Real.sqrt (Work.Coercivity.EfEta f))
        ≤ Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T4fun α f) f := by
    have h := neg_abs_le (Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Coercivity.T4fun α f) f)
    linarith [h, hT4']
  -- ### The numerical assembly
  have key : (1 / 5) * Work.Coercivity.EfEta f
      - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f) ≤
      Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Coercivity.LGammaT α f) f := by
    rw [hsum, hsplit]
    linarith [hB', hT1b, hT4b, hyoung1, hyoung2, hLhatSplit, hEfEta_nn]
  calc (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f + Work.Coercivity.Ef f)
      ≤ (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f) := by
        nlinarith [hEfnn]
    _ ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f := key

end Work.FTS.StrongEps.EpsE4Thr
