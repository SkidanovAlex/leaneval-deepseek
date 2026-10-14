import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.thetaBound
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriFourthLevel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false






/-! ## The radius upgrade of the modulation clause

The target's hypothesis is `hml : MuLamOK α C₀ Φs E`, i.e. the μ/λ-clause at the **single** radius
`C₀ α²`.  Every producer on the level-four route needs it at the radius of the *level* at which the
barrier is run — which is strictly larger than `C₀` whenever the datum must be strictly inside the
level (see `ball_of_barrier_datum_ball`).  This is not an interface item: the chapter `FTS_MuLamOK`
proves the clause at *every* class-`C` ball, for `α` below a threshold depending only on the
radius constant. -/

/-- **The radius upgrade of `MuLamOK`.**

`Work.FTS_MuLamOK.MuLamOK_proved_eventually` gives the μ/λ-clause at the radius `C₀'` for `α` below
a threshold depending on `C₀'`, `Ce`, `Cs`, from the packages `EllPkgGo` (the `EllPkgK` half of
`hEll` is not used) and `StarPkgo2`; monotonicity of the clause in its size constant
(`MuLamOK_mono_C₀`) then downgrades `C₀' = max K 1` to the caller's `K`.  So along the `ε`-scheme
the modulation bounds are available on the class-`C` ball of *any* radius `K α²`. -/
theorem MuLamOK_of_hEll_hstar {Ce Cs K : ℝ} (hK : 0 ≤ K) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∀ {Φs : Fn} {E : Fn → Fn},
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.FTS.StrongEps.MuLamOK α K Φs E := by
  obtain ⟨α₂, hα₂, hmain⟩ := Work.FTS_MuLamOK.MuLamOK_proved_eventually (C₀ := max K 1)
    (Ce := Ce) (Cs := Cs) (lt_max_of_lt_right zero_lt_one)
  exact ⟨α₂, hα₂, fun α hα Φs E hEll hstar =>
    Work.FTS_MuLamOK.MuLamOK_mono_C₀
      (hmain α hα hstar fun f hf => (hEll f hf).1) (le_max_left K 1)⟩

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthShiftHigh =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-- **The final arithmetic of the high-shift row.**  From the two weighted energies
`∫_μ g²ρA² ≤ C₁·S₄·(1+S)` and `∫_μ ρB² ≤ S` and the size `√S₄ ≤ M` of the datum, the
two-variable Cauchy–Schwarz price `√(C₁ S₄ (1+S))·√S` is dominated by
`(√C₁+1)(1+M)²(1+S)`.

(`√((1+S)S) ≤ 1+S`, `M ≤ (1+M)²` and `√C₁ ≤ √C₁+1` are the only inequalities used.) -/
private lemma fkShiftHigh_arith {C S₄ S M : ℝ} (hC : 0 < C) (hS₄ : 0 ≤ S₄) (hS : 0 ≤ S)
    (hM : 0 ≤ M) (h4 : Real.sqrt S₄ ≤ M) :
    Real.sqrt (C * S₄ * (1 + S)) * Real.sqrt S
      ≤ (Real.sqrt C + 1) * (1 + M) * (1 + M) * (1 + S) := by
  have hCs : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have h1S : 0 ≤ 1 + S := by linarith
  have hfac : Real.sqrt (C * S₄ * (1 + S))
      = Real.sqrt C * Real.sqrt S₄ * Real.sqrt (1 + S) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ C * S₄), Real.sqrt_mul hC.le]
  have hkey : Real.sqrt (C * S₄ * (1 + S)) * Real.sqrt S ≤ Real.sqrt C * M * (1 + S) := by
    have h1 : Real.sqrt (1 + S) * Real.sqrt S ≤ 1 + S := by
      have h2 : (1 + S) * S ≤ (1 + S) * (1 + S) := by nlinarith
      calc Real.sqrt (1 + S) * Real.sqrt S = Real.sqrt ((1 + S) * S) :=
            (Real.sqrt_mul h1S S).symm
        _ ≤ Real.sqrt ((1 + S) * (1 + S)) := Real.sqrt_le_sqrt h2
        _ = 1 + S := Real.sqrt_mul_self h1S
    rw [hfac]
    calc Real.sqrt C * Real.sqrt S₄ * Real.sqrt (1 + S) * Real.sqrt S
        = Real.sqrt C * Real.sqrt S₄ * (Real.sqrt (1 + S) * Real.sqrt S) := by ring
      _ ≤ Real.sqrt C * Real.sqrt S₄ * (1 + S) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.sqrt C * M * (1 + S) := by
          have h3 : Real.sqrt S₄ * (1 + S) ≤ M * (1 + S) :=
            mul_le_mul_of_nonneg_right h4 h1S
          calc Real.sqrt C * Real.sqrt S₄ * (1 + S)
              = Real.sqrt C * (Real.sqrt S₄ * (1 + S)) := by ring
            _ ≤ Real.sqrt C * (M * (1 + S)) := mul_le_mul_of_nonneg_left h3 hCs
            _ = Real.sqrt C * M * (1 + S) := by ring
  have hfin : Real.sqrt C * M * (1 + S)
      ≤ (Real.sqrt C + 1) * (1 + M) * (1 + M) * (1 + S) := by
    have hM2 : M ≤ (1 + M) * (1 + M) := by nlinarith
    have hX : 0 ≤ (1 + M) * (1 + M) := by positivity
    have h1 : Real.sqrt C * M * (1 + S)
        ≤ Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S) := by
      have h := mul_le_mul_of_nonneg_right hM2 h1S
      calc Real.sqrt C * M * (1 + S) = Real.sqrt C * (M * (1 + S)) := by ring
        _ ≤ Real.sqrt C * ((1 + M) * (1 + M) * (1 + S)) :=
            mul_le_mul_of_nonneg_left h hCs
        _ = Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S) := by ring
    have h2 : Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S)
        ≤ (Real.sqrt C + 1) * ((1 + M) * (1 + M)) * (1 + S) := by
      have h3 : Real.sqrt C * ((1 + M) * (1 + M))
          ≤ (Real.sqrt C + 1) * ((1 + M) * (1 + M)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
      exact mul_le_mul_of_nonneg_right h3 h1S
    refine le_trans h1 ?_
    calc Real.sqrt C * ((1 + M) * (1 + M)) * (1 + S)
        ≤ (Real.sqrt C + 1) * ((1 + M) * (1 + M)) * (1 + S) := h2
      _ = (Real.sqrt C + 1) * (1 + M) * (1 + M) * (1 + S) := by ring
  exact le_trans hkey hfin

/-- **The assembly of the high-shift row.**  Abstract form: the two-variable
Cauchy–Schwarz `FkAux.fkShiftHigh_absCS` applied to the two weighted energies, followed by
`fkShiftHigh_arith`. -/
private lemma fkShiftHigh_assembly {μ : MeasureTheory.Measure (ℝ × ℝ)} {g : ℝ → ℝ}
    {A B ρ : ℝ → ℝ → ℝ} {C₁ S₄ S M : ℝ}
    (hC₁ : 0 < C₁) (hS₄ : 0 ≤ S₄) (hS : 0 ≤ S) (hM : 0 ≤ M) (hsqrt : Real.sqrt S₄ ≤ M)
    (hρ : ∀ᵐ p ∂μ, 0 ≤ ρ p.1 p.2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ)
    (hFint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2) μ)
    (hFbd : (∫ p, (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂μ) ≤ C₁ * S₄ * (1 + S))
    (hGint : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) μ)
    (hGbd : (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂μ) ≤ S) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ ∧
      |∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ|
        ≤ (Real.sqrt C₁ + 1) * (1 + M) * (1 + M) * (1 + S) := by
  obtain ⟨hint, hbd⟩ := fkShiftHigh_absCS (μ := μ) hρ haesm hFint hGint
  refine ⟨hint, ?_⟩
  refine hbd.trans ?_
  refine (mul_le_mul (Real.sqrt_le_sqrt hFbd) (Real.sqrt_le_sqrt hGbd)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans ?_
  exact fkShiftHigh_arith hC₁ hS₄ hS hM hsqrt

theorem fkRowDthShiftHigh : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      4 ≤ b₁ → b₁ ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fkShiftHigh_shiftF
  refine ⟨Real.sqrt C₁ + 1, by positivity, ?_⟩
  intro α hαmem f M ρ b₁ hDat hb₁4 hb₁6 hρ
  have hα0 : 0 < α := hαmem.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hDat.sm
  have h6 : Work.Spaces.HkMem α 6 f := hDat.h6
  have hS6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hS4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hsqrt4 : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ M := by
    simpa only [Work.Spaces.HkNorm] using hDat.bdd
  -- the `F²`-energy (the shift slot against the angular slot) and the `G²`-energy
  obtain ⟨hFint, hFbd⟩ := hC₁ α hαmem f M b₁ ρ hDat hb₁4 hb₁6 hρ
  obtain ⟨hGint, hGbd⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt (α := α) (f := f)
      (a := 0) (j := 6) (ρ := ρ) hα0 (by norm_num) hρ hsm h6
  -- the leaf weight is nonnegative a.e. on the product measure
  have hρae : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM, 0 ≤ ρ p.1 p.2 := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_PM_Q0] with p hp
    exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_nonneg (α := α) (a := 0) (ρ := ρ)
      hρ p.1 p.2 hp.1 hp.2.1 hp.2.2
  -- a.e. strong measurability of the pairing
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
            * Work.Spaces.mixed 6 0 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkMomentAe α f b₁ hsm h6 hb₁6
    have h2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_leafW (α := α) (a := 0) (ρ := ρ) hρ
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed hsm (6 - b₁) 1
    have h4 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.mixed 6 0 f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed hsm 6 0
    exact (h1.mul (h2.mul (h3.mul h4))).congr
      (Filter.Eventually.of_forall fun p => by simp only [Pi.mul_apply]; ring)
  exact fkShiftHigh_assembly hC₁pos hS4 hS6 hM0 hsqrt4 hρae haesm hFint hFbd hGint hGbd

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12jets_classC` — the radial `z∂_z`-jets of `L₁₂` on the class `C`

`Work.Construction.L12 g z = ∫_z^∞ ∫_θ K(θ) g(s,θ)/s dθ ds` is the radial `L₁₂`-transform of the
fundamental model.  The goal is the *uniform* bound (uniform in `z > 0`, `α`-degradation allowed)

  `|D_z^j (L₁₂ g)(z)| ≤ C·Xn₆(g)`,   `j ≤ 4`,  `Xn₆(g) = |g|_{ℋ⁶}`,

for every `g` in the linear elliptic class `Work.FTS.ClassC.ClassC α`.

## Route

The jets are *angular moments*: with `Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ`,

* `j = 0`: `|L₁₂ g z| ≤ C·|g|_{ℋ⁴} ≤ C·|g|_{ℋ⁶}` by the Cauchy–Schwarz computation of
  `Work.FTS.GalBasis.cc.abs_L12_le_HkNorm` at level `6` (`Pieces.L12_sup_six`);
* `j ≥ 1`: the tower `D_z^{m+1}(L₁₂ g) = -Qang g m` (proved here by induction from
  `Pieces.qang_deriv_classC`, the differentiation of the angular moment under the `θ`-integral)
  converts the jet into `Qang g (j-1)`, and `Pieces.ang_moment_sup` bounds the moment by
  `4√3·Xn₆(g)`: the *window* form of the radial Hardy inequality
  (`FkAux.fkSliceSup_sliceSupGraded`) gives the slice bound
  `∫_θ sin(2θ)^{-η}(D_z^j g z θ)² ≤ 3 HkSq α 6 g` for **every** `z > 0`, which is what removes the
  `z`-dependence and makes the estimate uniform on `(0,∞)`.

The base case `D_z (L₁₂ g) = -Qang g 0` uses the fundamental theorem of calculus for the tail
integral (`Work.FM.hasDerivAt_L12`), whose two hypotheses are the integrability of the
`L₁₂`-density on `(0,∞)` (`MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn`, which
needs only continuity on the open quadrant plus `ℋ⁴`-honesty — exactly what `ClassC` supplies) and
its continuity at the base point (a consequence of the differentiability of `Qang g 0`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

open Work.FTS_EllLimOK.PkgJets.Pieces (ang_moment_sup L12_sup_six qang_deriv_classC)

/-! ## `Qang g 0` is the angular moment `FK g` -/

/-! ## The tower identity `D_z^{m+1}(L₁₂ g) = -Qang g m` -/

/-- **The tower identity** for a `ClassC` datum: for `m ≤ 3` and `z > 0`,

  `D_z^{m+1}(L₁₂ g)(z) = - Qang g m z`,   `Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ`.

The proof is the induction with step `D_z(Qang g m) = Qang g (m+1)`, i.e.
`z·∂_z(Qang g m)(z) = Qang g (m+1)(z)`, which is `Pieces.qang_deriv_classC`. -/
theorem DzdIter_L12_eq_neg_Qang {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) {m : ℕ} (hm : m ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter (m + 1) (fun z => Work.Construction.L12 g z) z
      = - Work.Elliptic.Qang g m z := by
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 4 (by norm_num) hg.mem
  have hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0 := hg.reg.continuousOn
  have hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcont hmem4
  have hbase : ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g 0 z := by
    intro z hz
    have hcontD : ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z := by
      have hQ0 := qang_deriv_classC hα hα1 hg (m := 0) (by norm_num) hz
      have h1 : ContinuousAt (fun x => Work.Elliptic.Qang g 0 x / x) z :=
        hQ0.continuousAt.div continuousAt_id (ne_of_gt hz)
      refine h1.congr ?_
      filter_upwards with x
      exact (Work.Elliptic.L12dens_eq_Qang_div g x).symm
    have hd : deriv (fun z' => Work.Construction.L12 g z') z
        = -(Work.Construction.L12dens g z) :=
      (Work.FM.hasDerivAt_L12 hint hcontD hz).deriv
    change z * deriv (fun z' => Work.Construction.L12 g z') z = - Work.Elliptic.Qang g 0 z
    rw [hd, mul_neg, Work.Construction.mul_L12dens_eq_FK (ne_of_gt hz), Qang_zero_eq_FK]
  have hgen : ∀ m : ℕ, m ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (m + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g m z := by
    intro m
    induction m with
    | zero => intro _ z hz; exact hbase z hz
    | succ n ih =>
        intro hn z hz
        have hQ := qang_deriv_classC hα hα1 hg (m := n) (by omega) hz
        have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)
            =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (by omega) z' hz'
        have hdv : deriv (Work.Elliptic.DzdIter (n + 1)
              (fun z => Work.Construction.L12 g z)) z
            = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (Work.Elliptic.DzdIter (n + 1)
              (fun z => Work.Construction.L12 g z)) z = - Work.Elliptic.Qang g (n + 1) z
        rw [hdv, hQ.deriv, mul_neg, mul_div_assoc',
          mul_div_cancel_left₀ (Work.Elliptic.Qang g (n + 1) z) (ne_of_gt hz)]
  exact hgen m hm z hz

/-! ## The target -/

theorem L12jets_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g := by
  obtain ⟨CL, hCLpos, hCL⟩ := L12_sup_six
  refine ⟨CL + 4 * Real.sqrt 3 + 1, by positivity, ?_⟩
  intro g hg j hj z hz
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hle1 : CL ≤ CL + 4 * Real.sqrt 3 + 1 := by linarith [Real.sqrt_nonneg 3]
  have hle2 : 4 * Real.sqrt 3 ≤ CL + 4 * Real.sqrt 3 + 1 := by linarith [hCLpos.le]
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    simp only [Work.Spaces.DzIter_zero]
    exact le_trans (hCL α g hmem6 z (le_of_lt hz)) (mul_le_mul_of_nonneg_right hle1 hXnn)
  · have hjk : j - 1 ≤ 3 := by omega
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 g z) j z 0]
    have htower := DzdIter_L12_eq_neg_Qang hα hα1 hg (m := j - 1) hjk hz
    rw [Nat.sub_add_cancel hjpos] at htower
    rw [htower, abs_neg]
    exact le_trans (ang_moment_sup hα hα1 hg hjk hz) (mul_le_mul_of_nonneg_right hle2 hXnn)

end Work.FTS_EllLimOK.PkgJets
end
end
