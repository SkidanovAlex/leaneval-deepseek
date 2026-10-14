import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.I1Paper_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Clairaut identity for the mixed slot -/




end
end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Elementary helpers about the `ℋ⁴`-functionals -/

/-- `HkMem` is invariant under negation. -/
theorem mem_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (-f) := by
  obtain ⟨h1, h2⟩ := h
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k (-f) z θ
      = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    exact (h1 z hz).congr (Filter.Eventually.of_forall (fun θ => (hpt z θ).symm))
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (-f) z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      funext fun z => MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => hpt z θ)
    rw [hfun]
    exact h2

/-- `HkSq` is invariant under negation. -/
theorem sq_neg {α : ℝ} (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (-f) = Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  rw [Work.FTS.EllipticEst.HkIntegrand_neg α k f]

/-- `Xn` is invariant under negation. -/
theorem Xn_neg {α : ℝ} (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (-f) = Work.FTS.Nonlin.Xn α f := by
  simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  rw [sq_neg]

/-- **`HkMem α n (D_θ f)`** from `SmoothOpen f` and `HkMem α (n+1) f`. -/
theorem hkMem_Dth_of_smoothOpen {α : ℝ} (hα : 0 < α) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hsm).continuousOn_HkIntegrand α n)
    h.1 h.2
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ)

/-- **Binary additivity of the `ℋ⁴`-membership and the `ℋ⁴`-norm**, with the factor `2`. -/
theorem add2 {α : ℝ} (hα : 0 < α) {u v : ℝ → ℝ → ℝ} {Bu Bv : ℝ}
    (husm : Work.FTS.EllipticEst.SmoothOpen u) (hvsm : Work.FTS.EllipticEst.SmoothOpen v)
    (hu : Work.Spaces.HkMem α 4 u) (hv : Work.Spaces.HkMem α 4 v)
    (bu : Work.FTS.Nonlin.Xn α u ≤ Bu) (bv : Work.FTS.Nonlin.Xn α v ≤ Bv)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    Work.Spaces.HkMem α 4 (fun z θ => u z θ + v z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => u z θ + v z θ) ≤ 2 * (Bu + Bv) := by
  have hmem : Work.Spaces.HkMem α 4 (fun z θ => u z θ + v z θ) :=
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (husm.forall 4) (hvsm.forall 4) hu hv
  refine ⟨hmem, ?_⟩
  have hb := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα husm hvsm hu hv
  have h1 : Work.FTS.Nonlin.Xn α u ≤ Bu := bu
  have h2 : Work.FTS.Nonlin.Xn α v ≤ Bv := bv
  have h3 : Work.Spaces.HkNorm α 4 u = Work.FTS.Nonlin.Xn α u := rfl
  have h4 : Work.Spaces.HkNorm α 4 v = Work.FTS.Nonlin.Xn α v := rfl
  rw [h3, h4] at hb
  linarith

/-- **`SmoothOpen (z ↦ L₁₂ w z)`** for a datum of the linear class `C` (delivered by the
colleague working on `HkMemXnN0`; see
`Submission/Work/FTS/StrongEps/ClassCRHS/smoothOpen_L12_radial_classC.lean`). -/
theorem smoothOpen_L12_radial_aux {α : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
  smoothOpen_L12_radial_classC hα hw

/-! ## The `N₀`-split on the open quadrant -/

/-- **The split of `N₀ α (F_*+w) w` into the seven rows** on the open quadrant (delivered by the
colleague working on `HkMemXnN0`; see
`Submission/Work/FTS/StrongEps/ClassCRHS/N0_split_open.lean`). -/
theorem N0_split_open_aux {α : ℝ} (hα : 0 < α) {w : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α w) w z θ
        = Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ
                    + Work.FTS.Nonlin.N06F α w z θ))))) :=
  N0_split_open hα hw

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Extension of a pointwise integrand bound to the closed quadrant.**  Both integrands
vanish on the two boundary lines `z = 0` and `sin(2θ) = 0`, so a bound valid on the open
quadrant extends to `Iz × Iθ` as soon as the constant is nonnegative. -/
theorem HkIntegrand_le_Izθ_of_Ioo {α : ℝ} (hα : 0 < α) {m l : ℕ} {X Y : Fn} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α m X z θ ≤ C * Work.Spaces.HkIntegrand α l Y z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α m X z θ ≤ C * Work.Spaces.HkIntegrand α l Y z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact mul_nonneg hC (Work.Spaces.HkIntegrand_nonneg α l Y 0 θ)
  · by_cases hsin : Real.sin (2 * θ) = 0
    · rw [Work.FTS.StrongPersist.HkIntegrand_eq_zero_of_sin_zero (α := α) hα (k := m) hsin]
      exact mul_nonneg hC (Work.Spaces.HkIntegrand_nonneg α l Y z θ)
    · have hsinpos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Work.Elliptic.sin_two_nonneg_of_mem hθ) (Ne.symm hsin)
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
      exact h z hzpos θ hθIoo

/-- **The pointwise integrand domination for `Lhat`**, on the closed quadrant. -/
theorem Lhat_HkIntegrand_le (α : ℝ) (hα : 0 < α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨C, hC, h⟩ := Lhat_integrand_le α hα m
  exact ⟨C, hC, fun g hs => HkIntegrand_le_Izθ_of_Ioo (α := α) (m := m) (l := m + 1)
    (X := Work.FTS.CoercivityFix.Lhat g) (Y := g) (C := C) hα hC.le (h g hs)⟩

/-- **`ℋ^m`-membership of `Lhat g`** from the order-`(m+1)` honesty of `g`. -/
theorem Lhat_mem (α : ℝ) (hα : 0 < α) (m : ℕ) {g : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α (m + 1) g) :
    Work.Spaces.HkMem α m (Work.FTS.CoercivityFix.Lhat g) := by
  obtain ⟨C, hC, h⟩ := Lhat_HkIntegrand_le α hα m
  refine Work.FTS.LocData.HkMem_of_majorant α m
    (f := Work.FTS.CoercivityFix.Lhat g)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α (m + 1) g z θ)
    ((q0Sm_Lhat hs m).continuousOn_HkIntegrand α) ?_ ?_ ?_
  · intro z hz
    exact (hm.1 z hz).const_mul C
  · have hI2 : MeasureTheory.IntegrableOn (fun z => C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (m + 1) g z θ)) Work.Spaces.Iz := hm.2.const_mul C
    refine hI2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C
      (fun θ => Work.Spaces.HkIntegrand α (m + 1) g z θ)).symm
  · intro z hz θ hθ
    exact h g hs z hz θ hθ

/-- **The integrated form**: `|Lhat g|²_{ℋ^m} ≤ C·|g|²_{ℋ^{m+1}}`. -/
theorem HkSq_Lhat_le (α : ℝ) (hα : 0 < α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α (m + 1) g →
        Work.Spaces.HkSq α m (Work.FTS.CoercivityFix.Lhat g)
          ≤ C * Work.Spaces.HkSq α (m + 1) g := by
  obtain ⟨C, hC, h⟩ := Lhat_HkIntegrand_le α hα m
  refine ⟨C, hC, fun g hs hm => ?_⟩
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have hout : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m
          (Work.FTS.CoercivityFix.Lhat g) z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have hinner : (∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C _
    rw [← hinner]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m
        (Work.FTS.CoercivityFix.Lhat g) z θ) ((hm.1 z hz).const_mul C) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact h g hs z hz θ hθ
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.CoercivityFix.Lhat g) z θ)
    (hm.2.const_mul C) hout) ?_
  exact le_of_eq (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iz) C
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ))

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The assembly of the row

The whole estimate is carried by the identity

`∫_z∫_θ ρ·(D_z^bD_θ^a u)·(D_z^bD_θ^a f) = ∑_{k≤b} C(b,k)·∫_z (D_z^kL₁₂f)·(∫_θ ρ·(D_z^{b-k}D_θ^{a+1}f)·(D_z^bD_θ^a f))`

for `u = L₁₂(f)·D_θf` (Leibniz for the radial coefficient `L₁₂ f`), the two bounds

* `k = 0`: the signed `θ`-integral is the `θ`-integration by parts of the extra angular
  derivative (`h0le`);
* `k ≥ 1`: the `θ`-slot product is dominated by `HkIntegrand α 6 f`, and the coefficient
  `D_z^kL₁₂ f` is bounded by `C₄|f|_{ℋ⁴}` (`k ≤ 4`) resp. `C₆|f|_{ℋ⁶}` (`k ≥ 5`), the two
  remaining `k ≥ 5` slots being priced by Cauchy–Schwarz (`hcs`). -/
theorem T4bRowSlot_core {Ccs C0 C4 C6 : ℝ} (hCcspos : 0 < Ccs) (hC0pos : 0 < C0)
    (hC4pos : 0 < C4) (hC6pos : 0 < C6)
    (hsup4 : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ C4 * Work.Spaces.HkNorm α 4 g)
    (hsup6 : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ C6 * Work.Spaces.HkNorm α 6 g)
    (hlr : ∀ (X : ℝ → ℝ) (g : ℝ → ℝ → ℝ), ContDiffOn ℝ 6 X (Set.Ioi 0) →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ (b a : ℕ), b ≤ 6 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => X z * g z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k X z * Work.Spaces.mixed (b - k) a g z θ))
    (hcs : ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b k : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.TransportS.IsLeafW α a ρ → 5 ≤ k → k ≤ b → a + b ≤ 6 →
      (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ|)
        ≤ Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
    (h0le : ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ C0 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨(C0 + 384 * (C4 + C6 * Ccs)) + 1, by positivity, ?_⟩
  intro α hα f a b ρ hso hm6 hm7 _hvanish _haxis hl12 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hb6 : b ≤ 6 := by omega
  -- ## the uniform bounds on the `z`-jets of the radial coefficient `L₁₂(f)`
  have hs4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hsup4 α f hα0 hα1 hso hm6 hl12 k hk z hz
  have hs6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun k hk z hz => hsup6 α f hα0 hα1 hso hm6 hm7 hl12 k hk z hz
  -- ## the Leibniz identity on the open quadrant
  have hleib : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.mixed (b - k) (a + 1) f z θ) := by
    intro z θ hz h1
    have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
      have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
        (by norm_num : 2 ≤ 7)).1
      rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
      exact h
    rw [hlr (fun z => Work.Construction.L12 f z) (Work.Spaces.Dth f) hXsm hso.Dth b a
      (by omega) z θ hz h1.1 h1.2]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Work.FTS.StrongPersist.H6Pair6Aux.mixed_Dth_eq]
  -- ## the `θ`-slice identity
  have hPhi_eq : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)) := by
    intro z hz
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ρ z θ * Work.Spaces.mixed b a
            (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.mixed b a f z θ
          = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
              * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                  * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                      * Work.Spaces.mixed b a f z θ)) := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      rw [hleib z θ hz ⟨h1, h2⟩]
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [MeasureTheory.integral_congr_ae hpt]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_const_mul]
    · intro k hk
      exact ((Psi_slice_int (k := k) hα0 hso hleaf hm7 hab hz).const_mul _).const_mul _
  -- ## the `z`-integral identity
  have hInt : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
          * (∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)) := by
    rw [MeasureTheory.integral_congr_ae (ae_Iz_of_pos hPhi_eq)]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [MeasureTheory.integral_const_mul]
    · intro k hk
      have hkb : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hK : 0 ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
          else C6 * Work.Spaces.HkNorm α 6 f) := by
        split_ifs
        · exact mul_nonneg (le_of_lt hC4pos) (Work.Spaces.HkNorm_nonneg α 4 f)
        · exact mul_nonneg (le_of_lt hC6pos) (Work.Spaces.HkNorm_nonneg α 6 f)
      exact (DzdX_Psi_int (k := k) hα0 hso hleaf hm7 hab (by omega) hK
        (fun z hz => by
          split_ifs with h4
          · exact hs4 k h4 z hz
          · exact hs6 k (by omega) z hz)).const_mul _

  -- ## the `k = 0` term (the `θ`-integration by parts of the extra angular derivative)
  have hk0 : |(b.choose 0 : ℝ) * (∫ z in Work.Spaces.Iz,
        Work.Elliptic.DzdIter 0 (fun z => Work.Construction.L12 f z) z
          * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - 0) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ))|
      ≤ C0 * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
    have h := h0le α hα f a b ρ hso hm6 hm7 hl12 hab hleaf
    simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, mul_assoc,
      Work.Elliptic.DzdIter_zero] using h
  -- ## the tail terms
  have hterm : ∀ k ∈ Finset.range b,
      |(b.choose (k + 1) : ℝ) * (∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|
        ≤ 64 * ((C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)) := by
    intro k hk
    have hkb : k + 1 ≤ b := by have := Finset.mem_range.mp hk; omega
    have hk6 : k + 1 ≤ 6 := by omega
    have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hc64 : (b.choose (k + 1) : ℝ) ≤ 64 := by
      have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb6
      have h3 : b.choose (k + 1) ≤ 2 ^ b := Nat.choose_le_two_pow b (k + 1)
      have h4 : b.choose (k + 1) ≤ 64 := by
        have h5 := le_trans h3 h2
        norm_num at h5
        exact h5
      exact_mod_cast h4
    have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f :=
      mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f)
    have hinner_abs : (∫ z in Work.Spaces.Iz,
          ‖Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)‖)
        = ∫ z in Work.Spaces.Iz,
            |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
            * |∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ| := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Real.norm_eq_abs, abs_mul]
    have hPsiint : IntegrableOn (fun z => |∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ|) Work.Spaces.Iz :=
      (Psi_intz (k := k + 1) hα0 hso hleaf hm7 hab).abs
    have hinner : |∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)|
        ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
      by_cases h4 : k + 1 ≤ 4
      · have hstep : (∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|)
            ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (hPsiint.const_mul _) ?_
          filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
          exact mul_le_mul_of_nonneg_right (hs4 (k + 1) h4 z hz) (abs_nonneg _)
        have hPsi_le : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
              * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ|) ≤ Work.Spaces.HkSq α 6 f := by
          rw [Work.Spaces.HkSq]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => abs_nonneg _)) hm6.2 ?_
          filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
          exact Psi_le_int6 (k := k + 1) hα0 hso hleaf hm6 hab hk1 hkb hz
        calc |∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)|
            ≤ ∫ z in Work.Spaces.Iz, ‖Work.Elliptic.DzdIter (k + 1)
                (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)‖ :=
              (by rw [← Real.norm_eq_abs]; exact MeasureTheory.norm_integral_le_integral_norm _)
          _ = ∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ| := hinner_abs
          _ ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := hstep
          _ ≤ (C4 * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkSq α 6 f :=
              mul_le_mul_of_nonneg_left hPsi_le
                (mul_nonneg (le_of_lt hC4pos) (Work.Spaces.HkNorm_nonneg α 4 f))
          _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
              have h1 : C4 ≤ C4 + C6 * Ccs := by
                nlinarith [le_of_lt hC6pos, le_of_lt hCcspos]
              calc C4 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
                  = C4 * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by ring
                _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) :=
                    mul_le_mul_of_nonneg_right h1
                      (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f))
      · have h5 : 5 ≤ k + 1 := by omega
        have hstep : (∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|)
            ≤ (C6 * Work.Spaces.HkNorm α 6 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (hPsiint.const_mul _) ?_
          filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
          exact mul_le_mul_of_nonneg_right (hs6 (k + 1) hk6 z hz) (abs_nonneg _)
        have hPsi_le : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
              * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ|)
            ≤ Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f :=
          hcs α hα f a b (k + 1) ρ hso hm6 hleaf h5 hkb hab
        have hsq6 : Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f
            = Work.Spaces.HkSq α 6 f := by
          simp only [Work.Spaces.HkNorm]
          rw [← sq, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
        calc |∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)|
            ≤ ∫ z in Work.Spaces.Iz, ‖Work.Elliptic.DzdIter (k + 1)
                (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)‖ :=
              (by rw [← Real.norm_eq_abs]; exact MeasureTheory.norm_integral_le_integral_norm _)
          _ = ∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ| := hinner_abs
          _ ≤ (C6 * Work.Spaces.HkNorm α 6 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := hstep
          _ ≤ (C6 * Work.Spaces.HkNorm α 6 f)
              * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) :=
              mul_le_mul_of_nonneg_left hPsi_le
                (mul_nonneg (le_of_lt hC6pos) (Work.Spaces.HkNorm_nonneg α 6 f))
          _ = (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
              rw [show C6 * Work.Spaces.HkNorm α 6 f
                    * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
                  = (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f
                      * (Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)) from by ring,
                hsq6]
          _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
              have h1 : C6 * Ccs ≤ C4 + C6 * Ccs := by linarith [le_of_lt hC4pos]
              calc (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
                  = (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := rfl
                _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) :=
                    mul_le_mul_of_nonneg_right h1
                      (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f))
    calc |(b.choose (k + 1) : ℝ) * (∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|
        = (b.choose (k + 1) : ℝ) * |∫ z in Work.Spaces.Iz,
            Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
              * (∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ)| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 64 * ((C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul hc64 hinner (abs_nonneg _) (by norm_num)
  -- ## the whole pairing
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ (C0 + 384 * (C4 + C6 * Ccs))
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
    rw [hInt]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_range_succ']
    have htail : (∑ k ∈ Finset.range b,
        |(b.choose (k + 1) : ℝ) * (∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|)
        ≤ 6 * (64 * ((C4 + C6 * Ccs)
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f))) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hb6' : (b : ℝ) ≤ 6 := by exact_mod_cast hb6
      have hnn : 0 ≤ 64 * ((C4 + C6 * Ccs)
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)) :=
        mul_nonneg (by norm_num) (mul_nonneg
          (add_nonneg (le_of_lt hC4pos) (mul_nonneg (le_of_lt hC6pos) (le_of_lt hCcspos)))
          (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f)))
      exact mul_le_mul_of_nonneg_right hb6' hnn
    refine le_trans (add_le_add htail hk0) ?_
    · rw [show 6 * (64 * ((C4 + C6 * Ccs)
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)))
            + C0 * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
          = (C0 + 384 * (C4 + C6 * Ccs))
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) from by ring]
  rw [Work.FTS.TransportS.slotPairing]
  refine le_trans hmain ?_
  have hNnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have hpos : 0 < α ^ (3 : ℝ) := Real.rpow_pos_of_pos hα0 3
    rw [Real.rpow_neg hα0.le]
    exact (one_le_inv₀ hpos).mpr (Real.rpow_le_one hα0.le hα1 (by norm_num))
  have key : Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
      ≤ α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : Work.Spaces.HkNorm α 4 f ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 := by
      have h2 : Work.Spaces.HkNorm α 4 f ≤ 1 + Work.Spaces.HkNorm α 4 f := by linarith
      calc Work.Spaces.HkNorm α 4 f ≤ 1 + Work.Spaces.HkNorm α 4 f := h2
        _ = (1 + Work.Spaces.HkNorm α 4 f) ^ 1 := by ring
        _ ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    calc Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
        ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul h1 h4 hSnn (by positivity)
      _ ≤ (α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4)
            * (1 + Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          calc (1 + Work.Spaces.HkNorm α 4 f) ^ 4
              = 1 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 := by ring
            _ ≤ α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 :=
                mul_le_mul_of_nonneg_right hα3 (by positivity)
      _ = α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  calc (C0 + 384 * (C4 + C6 * Ccs))
        * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
      ≤ (C0 + 384 * (C4 + C6 * Ccs)) * (α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ ((C0 + 384 * (C4 + C6 * Ccs)) + 1) * (α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith
    _ = ((C0 + 384 * (C4 + C6 * Ccs)) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The open quadrant `(0,∞) × (0,π/2)` as seen by the product measure -/

/-- The open quadrant is conull for the product of the two restrictions, so both the a.e.
strong measurability and the a.e. domination may be checked there. -/
private lemma quad_ae_eq {α : ℝ} {f : ℝ → ℝ → ℝ} {a j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      0 ≤ ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ∧
        ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      0 ≤ ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2 ∧
        ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  rw [MeasureTheory.Measure.prod_restrict]
  refine (MeasureTheory.ae_restrict_congr_set hprod).mpr ?_
  refine (MeasureTheory.ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)).mpr ?_
  refine Filter.Eventually.of_forall fun p hp => ?_
  obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
  exact h p.1 p.2 hz hθ.1 hθ.2

/-! ## Continuity of the leaf weights on the open quadrant -/

/-- The plain square of the radial weight is continuous on the open quadrant. -/
private lemma continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.pow ?_ 2
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- `sin(2θ)^c` is continuous on the open quadrant for every exponent `c`. -/
private lemma continuousOn_sin_rpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hf : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  refine (hf.continuousOn).rpow_const ?_
  intro p hp
  obtain ⟨-, hθ⟩ := Set.mem_prod.mp hp
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

/-- Every leaf weight is continuous on the open quadrant. -/
private lemma continuousOn_leaf {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · simp only [Work.FTS.TransportS.leafEta]
    exact continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 _)
  · exact continuousOn_w_sq_Q0
  · simp only [Work.FTS.TransportS.leafGam]
    exact continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 _)

/-! ## The main statement -/

theorem fkSlotSqInt {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a j : ℕ} (haj : a + j ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm6 : Work.Spaces.HkMem α 6 f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed j a f p.1 p.2 ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≤ Work.Spaces.HkSq α 6 f := by
  -- the a.e. strong measurability of the target integrand (continuity on the open quadrant)
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    show ContinuousOn ((fun p : ℝ × ℝ => ρ p.1 p.2)
      * (fun p : ℝ × ℝ => Work.Spaces.mixed j a f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    exact (continuousOn_leaf hρ).mul (((hsm.mixed j a).continuousOn).pow 2)
  -- the dominating `HkIntegrand α 6 f` is a.e. strongly measurable ...
  have hAESMHk : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α 6)
  -- ... and integrable for the product measure (the two halves of `HkMem` are exactly the
  -- slice and the outer integrability of `integrable_prod_of_iterated`)
  have hHk : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := Work.Spaces.HkIntegrand α 6 f)
      (fun x y => Work.Spaces.HkIntegrand_nonneg α 6 f x y)
      hAESMHk
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hm6.1 z hz))
      hm6.2).1
  -- the pointwise domination on the open quadrant
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      0 ≤ ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ∧
        ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have h0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ0 hθ1
    have hle : ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_of_le hα hρ le_rfl z θ hz hθ
    have h2 : Work.FTS.TransportS.slotW α a z θ
        * (Work.Spaces.mixed j a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.slotW_slot_le hα hθ haj
    exact ⟨mul_nonneg h0 (sq_nonneg _),
      le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) h2⟩
  have hbound := quad_ae_eq hpoint
  -- the target is integrable, being dominated a.e. by the integrable `HkIntegrand`
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hHk.mono' hAESM (by
      filter_upwards [hbound] with p hp
      rw [Real.norm_of_nonneg hp.1]
      exact hp.2)
  refine ⟨hInt, ?_⟩
  -- the product integral is the iterated integral, for which the bound is already proved
  have hval : (∫ p : ℝ × ℝ, ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 :=
    (MeasureTheory.integral_integral
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ρ z θ * Work.Spaces.mixed j a f z θ ^ 2) hInt).symm
  rw [hval]
  exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 hα hm6 a j ρ haj hρ

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Decomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/Decomp` — the coefficient majorants of the `N`-zero-mode estimate

The four pointwise bounds of the zero-mode estimate: the `ℛ`, `𝒰`, `𝒱`-coefficients of
`Ξ = PhiTil α (F_*+f) (Φs + E f)` (split into the star and the perturbation residuals, and
priced by `StarPkgo`/`EllPkgGo` + the `ℋ⁴`-Agmon bound) and the angular moment `FK (F_*+f)`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The arithmetic glue of the four coefficient bounds.**  A star coefficient bounded by
`Cstar · max Cs 0 · α` (with `Cstar` dominated by the `Kcoef` bracket) plus a perturbation
coefficient bounded by `Cp α^{-1/2} Ce · Xn α f` add up to at most `Kcoef`. -/
theorem add_le_Kcoef {α M Ce Cs Cp Cu Cag Cstar K R : ℝ} {f : Fn}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M)
    (hCp : 0 < Cp) (hCu : 0 < Cu) (hCag : 0 < Cag) (hCe0 : 0 < Ce)
    (hCs0 : 0 ≤ Cstar) (hCsle : Cstar ≤ Cp + Cu + Cag + 1)
    (hM : Work.FTS.Nonlin.Xn α f ≤ M)
    (hK : K ≤ Cstar * max Cs 0 * α)
    (hR : R ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :
    K + R ≤ Kcoef α M Ce Cs Cp Cu Cag := by
  have hr0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hr1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_rpow_neg_half hα0 hα1
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith
  have hM1' : (0 : ℝ) ≤ 1 + M := by linarith
  have hCs1 : max Cs 0 ≤ 1 + |Ce| + |Cs| := by
    refine le_trans (max_le (le_abs_self Cs) (abs_nonneg Cs)) ?_
    have := abs_nonneg Ce
    linarith
  have hCs0' : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hAb0 : (0 : ℝ) ≤ 1 + |Ce| + |Cs| := le_trans hCs0' hCs1
  have hZ0 : 0 < Cp + Cu + Cag + 1 := by linarith
  have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := by linarith
  -- the star part
  have hK1 : K ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
    refine le_trans hK ?_
    have hCM : Cstar * max Cs 0 ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) :=
      mul_le_mul hCsle hCs1 hCs0' hZ0.le
    have hCM0 : 0 ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) :=
      mul_nonneg hZ0.le hAb0
    have hαle : α ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      nlinarith [hr1, hM1, hM0, hα1, hα0]
    refine le_trans (mul_le_mul_of_nonneg_right hCM hα0.le) ?_
    calc (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α
        ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|)
            * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
          mul_le_mul_of_nonneg_left hαle hCM0
      _ = (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
          ring
  -- the perturbation part
  have hR1 : R ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
    refine le_trans hR ?_
    have hCe_le : Ce ≤ 1 + |Ce| + |Cs| := by
      have := abs_nonneg Cs
      linarith [le_abs_self Ce]
    have hP0 : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
      mul_nonneg (mul_nonneg hCp.le hr0) hM1'
    have hstep1 : Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * (1 + M) :=
      mul_le_mul_of_nonneg_left hX1 (mul_nonneg (mul_nonneg hCp.le hr0) hCe0.le)
    have hstep2 : Cp * α ^ (-(1 / 2 : ℝ)) * Ce * (1 + M)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M) := by
      calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * (1 + M)
          = (Cp * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * Ce := by ring
        _ ≤ (Cp * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * (1 + |Ce| + |Cs|) :=
            mul_le_mul_of_nonneg_left hCe_le hP0
        _ = Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M) := by ring
    have hstep3 : Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M)
        ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      have hQ0 : 0 ≤ (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
        mul_nonneg (mul_nonneg hAb0 hr0) hM1'
      calc Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M)
          = ((1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * Cp := by ring
        _ ≤ ((1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * (Cp + Cu + Cag + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hQ0
        _ = (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
            ring
    exact le_trans hstep1 (le_trans hstep2 hstep3)
  have hA0 : 0 ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
    mul_nonneg (mul_nonneg (mul_nonneg hZ0.le hAb0) hr0) hM1'
  have : K + R ≤ 2 * ((Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|)
      * α ^ (-(1 / 2 : ℝ)) * (1 + M)) := by linarith
  refine le_trans this ?_
  rw [Kcoef]
  nlinarith [hA0]

/-- **The four coefficient majorants.**  On the open quadrant the three coefficients
`ℛ(Ξ)`, `𝒰(Ξ)`, `𝒱(Ξ)` of `Ξ = PhiTil α (F_*+f) (Φs + Ef)` and the angular moment
`FK (F_*+f)` are all bounded by `Kcoef`. -/
theorem NZ_coefs {α M Ce Cs : ℝ} {f Ef Φs : Fn} {Cp Cu Cag : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M) (hCe0 : 0 < Ce)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f)
    (hmem7 : Work.Spaces.HkMem α 7 f) (hM : Work.FTS.Nonlin.Xn α f ≤ M)
    (hstar : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce f Ef)
    (hCp : 0 < Cp) (hCu : 0 < Cu) (hCag : 0 < Cag)
    (hresR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
    (hresU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ / Work.Construction.s2 θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
    (hresV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
    (hUstar : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ Cu * max Cs 0 * α)
    (hsupf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag ∧
      |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag ∧
      |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag ∧
      |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ Kcoef α M Ce Cs Cp Cu Cag := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hp0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hCe1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by
    have h1 := abs_nonneg Ce
    have h2 := abs_nonneg Cs
    linarith
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith
  have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := by linarith
  have hmaxCs : max Cs 0 ≤ 1 + |Ce| + |Cs| := by
    refine le_trans (max_le (le_abs_self Cs) (abs_nonneg Cs)) ?_
    have := abs_nonneg Ce; linarith
  have hCe' : Ce ≤ 1 + |Ce| + |Cs| := by
    have := abs_nonneg Cs; linarith [le_abs_self Ce, abs_nonneg Ce]
  -- =============== 1. the `L₁₂`-additivity and the decomposition of `Ξ`
  have hL : ∀ z' : ℝ, 0 < z' → Work.Construction.L12 (Work.Construction.Ftot α f) z'
      = Work.Construction.L12 (Work.Construction.Fstar α) z' + Work.Construction.L12 f z' :=
    fun z' hz' => NZaux.L12AddFstar hα0 hα1 hso hmem4 z' hz'
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α f Ef z θ') := by
    funext θ'
    have h := hL z hz
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.Ftot] at h ⊢
    rw [h]
    ring
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α f Ef z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have h := hL z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.Ftot] at h ⊢
    rw [h]
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α f Ef z θ := congrFun hsliceθ θ
  -- =============== 2. differentiability of the two halves
  have hΞs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα0 hα1 hstar
  have hΞszd : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z :=
    Work.FTS.NonlinRows.Rl1.openSlice_diffZ hΞs hz ⟨hθ, hθ2⟩
  have hΞstd : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_diffT hΞs hz ⟨hθ, hθ2⟩
  have h12cd : ContDiffOn ℝ 6 (fun z' => Work.Construction.L12 f z') (Set.Ioi (0 : ℝ)) :=
    Work.FTS.StrongPersist.contDiffOn6_L12_of hso hmem7
  have h12diff : DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z :=
    (h12cd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hΞpdef : Work.FTS.Nonlin.PhiTg α f Ef
      = fun z' θ' => Ef z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 f z' := rfl
  have hΞpzd : DifferentiableAt ℝ (fun z' => Work.FTS.Nonlin.PhiTg α f Ef z' θ) z := by
    rw [hΞpdef]
    exact (hgo.smooth.hasDerivAt_slice ⟨hθ, hθ2⟩ hz).differentiableAt.sub
      ((differentiableAt_const ((1 / (4 * α)) * Work.Construction.s2 θ)).mul h12diff)
  have hs2d : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hΞptd : DifferentiableAt ℝ (fun θ' => Work.FTS.Nonlin.PhiTg α f Ef z θ') θ := by
    rw [hΞpdef]
    exact (Work.FTS.NonlinRows.Rl1.openSlice_diffT hgo.smooth hz ⟨hθ, hθ2⟩).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2d).mul
        (differentiableAt_const _))
  -- =============== 3. the additivity of the three operators
  have hpzP : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α f Ef) z θ := by
    have hderiv := hslicez.deriv_eq
    have hsum := Work.FTS.Nonlinear.Pieces.pz_add_of_diff hΞszd hΞpzd
    simp only [Work.Spaces.pz] at hsum hderiv ⊢
    exact hderiv.trans hsum
  have hpthP : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α f Ef) z θ := by
    have hderiv := congrArg (fun F : ℝ → ℝ => deriv F θ) hsliceθ
    have hsum := Work.FTS.Nonlinear.Pieces.pth_add_of_diff hΞstd hΞptd
    simp only [Work.Spaces.pth] at hsum hderiv ⊢
    exact hderiv.trans hsum
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ := by
    simp only [Work.Construction.Rop]
    rw [hval, hpzP, hpthP]
    ring
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ := by
    simp only [Work.Construction.Uop]
    rw [hval, hpzP]
    ring
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ := by
    simp only [Work.Construction.Vop]
    rw [hval, hpthP]
    ring
  -- =============== 4. the three coefficient bounds
  have hRle : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    have h1 := Work.FTS.NonlinRows.Rl1.star_Rop_le hα0 hstar z hz θ ⟨hθ, hθ2⟩
    have h2 := hresR z θ hz hθ hθ2
    rw [hRop]
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h2)) ?_
    exact add_le_Kcoef (Cstar := 1) (K := max Cs 0 * α)
      (R := Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
      hα0 hα1 hM0 hCp hCu hCag hCe0 (by norm_num) (by linarith) hM (by simp) (le_refl _)
  have hUle : |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    have h1 := hUstar z θ hz hθI
    have h2 := hresU z θ hz hθ hθ2
    have h3 : |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
      have hs2n : Work.Construction.s2 θ ≠ 0 := by
        have hsp : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [hθ2, Real.pi_pos])
        rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
        exact ne_of_gt hsp
      have hEq : |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ|
          = |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := by
        rw [← abs_mul, div_mul_cancel₀ _ hs2n]
      calc |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ|
          = |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := hEq
        _ ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| * 1 :=
            mul_le_mul_of_nonneg_left
              (show |Work.Construction.s2 θ| ≤ 1 from Real.abs_sin_le_one (2 * θ))
              (abs_nonneg _)
        _ = |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| := mul_one _
        _ ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := h2
    rw [hUop]
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h3)) ?_
    exact add_le_Kcoef (Cstar := Cu) (K := Cu * max Cs 0 * α)
      (R := Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
      hα0 hα1 hM0 hCp hCu hCag hCe0 hCu.le (by linarith) hM (le_refl _) (le_refl _)
  have hVle : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    have h1 := Work.FTS.NonlinRows.Rl1.star_Vop_le hα0 hstar z hz θ ⟨hθ, hθ2⟩
    have h2 := hresV z θ hz hθ hθ2
    rw [hVop]
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h2)) ?_
    exact add_le_Kcoef (Cstar := 1) (K := max Cs 0 * α)
      (R := Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
      hα0 hα1 hM0 hCp hCu hCag hCe0 (by norm_num) (by linarith) hM (by simp) (le_refl _)
  have hFKle : |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
      ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    refine le_trans (FK_le hα0 hα1 hM0 hCag hM hsupf hz) ?_
    have hr0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
    have hM1 : (0 : ℝ) ≤ 1 + M := by linarith
    have hAb0 : (0 : ℝ) ≤ 1 + |Ce| + |Cs| := by positivity
    have hZ0 : 0 < Cp + Cu + Cag + 1 := by linarith
    have hstep : 100 * (1 + Cag) ≤ 1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) := by
      have hA : (100 : ℝ) * (1 + Cag) ≤ 1000 * (Cp + Cu + Cag + 1) := by linarith
      have hB : (1000 : ℝ) * (Cp + Cu + Cag + 1)
          ≤ 1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) :=
        le_mul_of_one_le_right (le_of_lt (by linarith)) (by linarith)
      linarith
    calc 100 * (1 + Cag) * α ^ (-(1 / 2 : ℝ)) * (1 + M)
        = (100 * (1 + Cag)) * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) := by ring
      _ ≤ (1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|))
            * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
          mul_le_mul_of_nonneg_right hstep (mul_nonneg hr0 hM1)
      _ = Kcoef α M Ce Cs Cp Cu Cag := by rw [Kcoef]; ring
  exact ⟨hRle, hUle, hVle, hFKle⟩

end Work.FTS.StrongPersist.H6Rows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the `∃ C` pipeline lemma

Instantiation of `main_bound_core`: the constant `Cf` (signed radial IBP), `C6` (plain sup at
order `≤ 4`), `Cm` (mixed sup at order `≤ 4`) and the two exceptional `L²` constants
`excC11`, `excC02` are pulled from the corresponding `∃ C` lemmas, the pointwise package
`SupPkg` is built from them (`CoefThMem 1 f` supplying the `∂_θf`-bound), and the final
constant is
`(Cf + 1030) · ((C6 + Cm + 1 + √(10·excC11) + √(10·excC02)) + (Cm + C6 + 1) + 1)`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 3200000


end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
