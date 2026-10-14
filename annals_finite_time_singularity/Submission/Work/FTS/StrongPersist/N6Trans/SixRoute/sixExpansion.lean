import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityStep.Step.Coercive
import Submission.Work.FTS.EllSol.Trunc.PassAux2
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.weakSliceContinuousKit
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Comm2_levels =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

theorem Comm2_levels (α : ℝ) (hα : 0 < α)
    {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    Work.FTS.CoercivityFix.Assembly.Comm2 α 2
        (Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α)
      ∧ Work.FTS.CoercivityFix.Assembly.Comm2 α 3
        (Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α)
      ∧ Work.FTS.CoercivityFix.Assembly.Comm2 α 4
        (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) := by
  -- The base level `Comm2 α 1 (H1IP α)`, then three applications of the induction step.
  have h1 : Comm2 α 1 (Work.Coercivity.H1IP α) := Comm2_L1 α hα
  have h2 : Comm2 α 2 (IP2 c₁ c₂ α) := Comm2_succ α hα 1 h1
  have h3 : Comm2 α 3 (IP3 c₁ c₂ c₁' c₂' α) := Comm2_succ α hα 2 h2
  have h4 : Comm2 α 4 (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) := Comm2_succ α hα 3 h3
  exact ⟨h2, h3, h4⟩

end Work.FTS.CoercivityFix.Assembly
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `θ`-derivative of `𝓛_Γ^T` in the interior class

`𝓛_Γ^T f = 𝓛̂ f + Γ(θ)·K(z)` with a `θ`-independent `K`, so on the open quadrant the `θ`-slice
of `𝓛_Γ^T f` is the sum of the `θ`-slice of `𝓛̂ f` and of `Γ(θ)·K`; differentiating and
multiplying by `sin(2θ)` gives `D_θ(𝓛̂ f) + T2 + T4`. -/

/-- The `θ`-independent coefficient `K(z)` of the `Corr`-part: the `Corr` of `f` is
`Γ(θ)·K(z)`. -/
def slotK (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  -(2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) * Work.Coercivity.L12f f z
    + (2 * z ^ 2 / (1 + z) ^ 3) * Work.Coercivity.C0 f / Work.Spaces.c α


/-! ## The core of the slot estimate

The three analytic inputs (the two `D_θΓ`-bounds and the integrability of the clean pairing)
are hypotheses here; `slotGam_LGammaT` below supplies them from the sibling files. -/


/-! ## The `T2`-bound: a short Cauchy–Schwarz route

`T2 α f = -D_θΓ(θ)·A(z)` with `A(z) = (2z/(c(1+z)²))·L₁₂(f)(z)` is a product of a function of
`θ` alone and one of `z` alone, so the `γ`-weighted pairing factors as the product of *two*
`L²`-norms:

  `|⟨T2 α f, D_θ f⟩_γ| ≤ ‖D_θΓ·sin^{-γ/2}‖₂ · ‖A·w‖₂ · ‖D_θf·w·sin^{-γ/2}‖₂`.

The three factors are `γamDth_l2_bound` (`∫ (D_θΓ)²sin^{-γ} ≤ 100α`), the Hardy inequality
`EL12z ≤ 16Ef` (giving `∫ (A w)² = (4/c²)EL12z ≤ 6400 Ef`) and `EDth α f` itself.  This gives
`800·√α·√(Ef)·√(EDth)`, which the Young split `(1/200, 3.2·10⁷α)` turns into the estimate
needed by the slot. -/



end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.HkIntegrand_Dz_le_succ_Q0Sm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Congruence of `D_θ` and of the iterated `D_z` on the open quadrant

Both operators are local; on the open set `Qd` two functions that agree there have equal
`D_θ`- and equal `D_z^j`-profiles, by `Work.Spaces.pth_congr_of_isOpen` respectively
`Work.Spaces.pz_congr_of_isOpen`. -/

/-- `D_θ` is congruent on the open quadrant. -/
theorem Dth_congr_Qd {X Y : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Qd → X z θ = Y z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd → Work.Spaces.Dth X z θ = Work.Spaces.Dth Y z θ := by
  intro z θ hzθ
  have hEq : Set.EqOn (Function.uncurry X) (Function.uncurry Y) Qd :=
    fun p hp => h p.1 p.2 hp
  simp only [Work.Spaces.Dth]
  rw [Work.Spaces.pth_congr_of_isOpen isOpen_Qd hEq hzθ]

/-- The iterated `D_z` is congruent on the open quadrant. -/
theorem DzIter_congr_Qd {X Y : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Qd → X z θ = Y z θ) (j : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.DzIter j X z θ = Work.Spaces.DzIter j Y z θ := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro z θ hzθ
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DzIter j X))
          (Function.uncurry (Work.Spaces.DzIter j Y)) Qd :=
        fun p hp => ih p.1 p.2 hp
      show z * Work.Spaces.pz (Work.Spaces.DzIter j X) z θ
          = z * Work.Spaces.pz (Work.Spaces.DzIter j Y) z θ
      rw [Work.Spaces.pz_congr_of_isOpen isOpen_Qd hEq hzθ]

/-- `D_z^i (D_z X) = D_z^{i+1} X`, definitionally from `D_z^{i+b} = D_z^i ∘ D_z^b`. -/
theorem DzIter_Dz_eq (i : ℕ) (X : Fn) :
    Work.Spaces.DzIter i (Work.Spaces.Dz X) = Work.Spaces.DzIter (i + 1) X := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-! ## The finite-order index shift `D_θ^a (D_z u) = mixed 1 a u`

The honest hypothesis is `u ∈ C^{a+1}` on `Qd`: the identity is `∂_θ`-`∂_z` commutation of total
order `a + 1`.  It is proved by induction on `a`; the step applies Clairaut
(`Work.Spaces.Dz_Dth_comm`) to the `C²` profile `D_θ^a u` (which needs `u ∈ C^{a+2}`, one order
more, exactly as the induction hypothesis for level `a` supplies it). -/

theorem DthIter_Dz_eq_mixed_one {u : Fn} {N : ℕ} (h : Q0Sm N u) {a : ℕ} (ha : a + 1 ≤ N) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.DthIter a (Work.Spaces.Dz u) z θ = Work.Spaces.mixed 1 a u z θ := by
  induction a with
  | zero => intro z θ _; rfl
  | succ a ih =>
      intro z θ hzθ
      have ha' : a + 1 ≤ N := by omega
      -- `D_θ^a u` is `C²` on `Qd`, because `u` is `C^{a+2}` there.
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter a u)) (z, θ) :=
        (contDiffOn_DthIter_nat isOpen_Qd (G := u) a 2
          (h.mono (l := a + 2) (by omega))).contDiffAt (isOpen_Qd.mem_nhds hzθ)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter a u)) z θ
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter a u)) z θ :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter a u) hcd
      show Work.Spaces.Dth (Work.Spaces.DthIter a (Work.Spaces.Dz u)) z θ
          = Work.Spaces.mixed 1 (a + 1) u z θ
      rw [Dth_congr_Qd (X := Work.Spaces.DthIter a (Work.Spaces.Dz u))
            (Y := Work.Spaces.Dz (Work.Spaces.DthIter a u)) (ih ha') z θ hzθ, ← hcomm]
      rfl

/-- **The index shift on the open quadrant**: `D_z^b D_θ^a (D_z u) = D_z^{b+1} D_θ^a u`. -/
theorem mixed_Dz_shift_Q0Sm {u : Fn} {N : ℕ} (h : Q0Sm N u) {a : ℕ} (ha : a + 1 ≤ N) (b : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.mixed b a (Work.Spaces.Dz u) z θ
        = Work.Spaces.mixed (b + 1) a u z θ := by
  intro z θ hzθ
  have hX := DzIter_congr_Qd (X := Work.Spaces.DthIter a (Work.Spaces.Dz u))
    (Y := Work.Spaces.Dz (Work.Spaces.DthIter a u)) (DthIter_Dz_eq_mixed_one h ha) b z θ hzθ
  have hfun : Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a u))
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) :=
    (Work.Spaces.DzIter_add_right b 1 (Work.Spaces.DthIter a u)).symm
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz u)) z θ
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) z θ
  rw [hX, hfun]

/-! ## The pointwise domination of the `ℋ^k`-integrands -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`. -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- **Every summand of `HkIntegrand α m (D_z X)` is a summand of `HkIntegrand α (m+1) X`**, with
the same weight: the pure summands by `D_z^i (D_z X) = D_z^{i+1} X`, the mixed summands by the
index shift `mixed_Dz_shift_Q0Sm`.  Hence the pointwise domination of the integrands.  This is
the finite-order (`Q0Sm`) companion of `QuadPorts.HkIntegrand_Dz_le_succ` (`SmoothQuad`) and of
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ` (`SmoothOpen`). -/
theorem HkIntegrand_Dz_le_succ_Q0Sm (α : ℝ) (m : ℕ) {X : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.Q0Sm (m + 1) X) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) X z θ := by
  intro z θ hzθ
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
      = (∑ i ∈ Finset.range (m + 1),
            (Work.Spaces.DzIter i (Work.Spaces.Dz X) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j ≤ m
              then (Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (m + 1) X z θ
      = (∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (m + 2), ∑ b ∈ Finset.range (m + 2),
            (if 1 ≤ a ∧ a + b ≤ m + 1
              then (Work.Spaces.mixed b a X z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (m + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz X) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le m
      (fun a => (Work.Spaces.DzIter a X z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq i X])
  have h2 : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ * W) ^ 2 else 0))
      = (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed (j + 1) i X z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [ite_eq_left hc, ite_eq_left hc,
        mixed_Dz_shift_Q0Sm h (a := i) (by omega) j z θ hzθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hkey : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed (j + 1) i X z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (m + 2), ∑ b ∈ Finset.range (m + 2),
            (if 1 ≤ a ∧ a + b ≤ m + 1
              then (Work.Spaces.mixed b a X z θ * W) ^ 2 else 0)) :=
    Work.Coercivity.SumShiftZ_le m
      (fun a b => (Work.Spaces.mixed b a X z θ * W) ^ 2) (fun a b => sq_nonneg _)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.mixedSlotOfNiceE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-! ## The integration domain and the four slot integrands -/

/-- The half-strip `ℝ × Iθ` carrying all the slot integrals. -/
abbrev slotI : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ

/-- The open strip `ℝ × (0, π/2)` on which the data is assumed `C²`. -/
abbrev slotStrip : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem measurableSet_slotI : MeasurableSet slotI :=
  MeasurableSet.univ.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)

theorem isOpen_slotStrip : IsOpen slotStrip := isOpen_univ.prod isOpen_Ioo



/-- The heavy `L_b`-slot `(∂_t f - b f)²·σ_η`. -/
def slotV (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2

/-- The heavy `L_b²`-slot `(∂_t²f - 2b ∂_tf + b²f)²·σ_η`. -/
def slotZ (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - 2 * b * Work.Spaces.pz f p.1 p.2
    + b ^ 2 * f p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2

/-- The heavy angular slot `(∂_θ²f)²·σ_η`. -/
def slotQ (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2

/-- The heavy mixed slot `(∂_θL_b f)²·σ_η = (∂_θ∂_tf - b ∂_θf)²·σ_η`. -/
def slotM (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - b * Work.Spaces.pth f p.1 p.2) ^ 2
    * Work.FTS.EllipticEst.sEta p.2

@[simp] theorem slotV_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotV b f p = (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2
      * Work.FTS.EllipticEst.sEta p.2 := rfl

@[simp] theorem slotZ_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotZ b f p = (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - 2 * b * Work.Spaces.pz f p.1 p.2
      + b ^ 2 * f p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := rfl

@[simp] theorem slotQ_apply (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotQ f p = (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2
      * Work.FTS.EllipticEst.sEta p.2 := rfl

@[simp] theorem slotM_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotM b f p = (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - b * Work.Spaces.pth f p.1 p.2) ^ 2
      * Work.FTS.EllipticEst.sEta p.2 := rfl

theorem slotV_nonneg {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotV b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotZ_nonneg {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotZ b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotQ_nonneg {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotQ f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotM_nonneg {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotM b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

variable {b : ℝ} {u : ℝ → ℝ → ℝ}

/-! ## The mixed slot of the truncation is the mixed slot of the datum on the plateau -/

/-- On the plateau `|t| < N` the mixed slot `∂_θL_b` of the truncation `uTr N b u` agrees
pointwise with that of the datum `u`.  (The point is that `L_b (uTr N b u) = χ_N·L_b u` there,
and differentiating in `θ` commutes with the `t`-only cutoff.) -/
theorem uTr_slotM_eq (hu : ContDiffOn ℝ 2 (Function.uncurry u) slotStrip)
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    {N t θ : ℝ} (hN : (2 : ℝ) ≤ N) (ht : |t| < N) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u) (t, θ) = slotM b u (t, θ) := by
  have hNpos : 0 < N := lt_of_le_of_lt (abs_nonneg t) ht
  have hmem : (t, θ) ∈ slotStrip := ⟨trivial, hθ⟩
  have hstrip : IsOpen slotStrip := isOpen_slotStrip
  -- `uTr N b u` is `C²` on the strip
  have hUcd : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.EllSol.ShiftFT.uTr N b u)) slotStrip :=
    (Work.FTS.EllSol.ShiftFT.uTr_niceFlat N b u hN hu h0 hπ).1
  -- the `θ`-slices which occur below are differentiable at `θ`
  have hdPzU : DifferentiableAt ℝ
      (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 1) (by norm_num)
      (Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hstrip 1 hUcd) hmem).2
  have hdU : DifferentiableAt ℝ (fun θ' => Work.FTS.EllSol.ShiftFT.uTr N b u t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 2) (by norm_num)
      hUcd hmem).2
  have hdPzu : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz u t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 1) (by norm_num)
      (Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hstrip 1 hu) hmem).2
  have hdu : DifferentiableAt ℝ (fun θ' => u t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 2) (by norm_num)
      hu hmem).2
  -- write both sides as derivatives
  have hleft : Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) t θ
      - b * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ
      = deriv (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ'
          - b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ') θ := by
    rw [show (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ'
          - b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ')
        = (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ')
          - (fun θ' => b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ') from rfl,
      deriv_sub hdPzU (hdU.const_mul b), deriv_const_mul b hdU]
    rfl
  have hright : Work.Spaces.pth (Work.Spaces.pz u) t θ - b * Work.Spaces.pth u t θ
      = deriv (fun θ' => Work.Spaces.pz u t θ' - b * u t θ') θ := by
    rw [show (fun θ' => Work.Spaces.pz u t θ' - b * u t θ')
        = (fun θ' => Work.Spaces.pz u t θ') - (fun θ' => b * u t θ') from rfl,
      deriv_sub hdPzu (hdu.const_mul b), deriv_const_mul b hdu]
    rfl
  -- the two functions of `θ` agree on the open interval
  have hev : (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ'
        - b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pz u t θ' - b * u t θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    rw [Work.FTS.EllSol.ShiftFT.uTrAone_uTr_sh N b u hu t θ' hθ',
      Work.FTS.EllSol.ShiftFT.uTrAone.deriv_phiTr_eq_zero_of_lt N t hNpos
        (by nlinarith [abs_nonneg t, ht]),
      Work.FTS.EllSol.ShiftFT.phiTr_eq_one hNpos (by linarith),
      Work.FTS.EllSol.Trunc.chi_eq_one hNpos (le_of_lt ht)]
    ring
  rw [slotM_apply, slotM_apply, hleft, hright, hev.deriv_eq]

/-! ## A.e. strong measurability of the truncation's mixed slot -/

/-- The mixed slot of `uTr N b u` is a.e. strongly measurable for `volume.restrict slotI`
(it is continuous on the open strip, which differs from `slotI` by the null set `θ = 0, π/2`). -/
theorem aesm_slotM_uTr (hu : ContDiffOn ℝ 2 (Function.uncurry u) slotStrip)
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    {N : ℝ} (hN : (2 : ℝ) ≤ N) :
    AEStronglyMeasurable (slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u))
      (volume.restrict slotI) := by
  have hstrip : IsOpen slotStrip := isOpen_slotStrip
  have hUcd : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.EllSol.ShiftFT.uTr N b u)) slotStrip :=
    (Work.FTS.EllSol.ShiftFT.uTr_niceFlat N b u hN hu h0 hπ).1
  have h1 : ContDiffOn ℝ 0 (Function.uncurry
      (Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)))) slotStrip :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pth_succ hstrip 0
      (Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hstrip 1 hUcd)
  have h2 : ContDiffOn ℝ 1 (Function.uncurry
      (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u))) slotStrip :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pth_succ hstrip 1 hUcd
  have hcont : ContinuousOn (slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u)) slotStrip := by
    have hc1 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2)
        slotStrip := h1.continuousOn
    have hc2 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2) slotStrip := h2.continuousOn
    have hW : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) slotStrip :=
      Work.FTS.EllSol.Trunc.continuousOn_wE_comp
    have hsub : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
          - b * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2) slotStrip :=
      hc1.sub (hc2.const_mul b)
    show ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
        - b * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2) slotStrip
    exact (hsub.pow 2).mul hW
  exact Work.FTS.EllSol.Trunc.aesm_strip hcont

/-! ## The core: `b ≥ 0` -/

theorem slotFiniteness_nonneg
    (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ (b : ℝ) (w : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat w →
      MeasureTheory.IntegrableOn (slotV b w) slotI →
      MeasureTheory.IntegrableOn (slotZ b w) slotI →
      MeasureTheory.IntegrableOn (slotQ w) slotI →
      (∫⁻ p in slotI, ENNReal.ofReal (slotM b w p))
        ≤ ENNReal.ofReal (C * ((∫ p in slotI, slotV b w p)
            + Real.sqrt ((∫ p in slotI, slotZ b w p) * (∫ p in slotI, slotQ w p)))))
    (b : ℝ) (hb : 0 ≤ b) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) slotStrip)
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (slotV b u) slotI)
    (hZ : MeasureTheory.IntegrableOn (slotZ b u) slotI)
    (hQ : MeasureTheory.IntegrableOn (slotQ u) slotI) :
    (∫⁻ p in slotI, ENNReal.ofReal (slotM b u p)) < ⊤ := by
  -- the three slot bounds for the truncation family
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.ShiftFT.uTr_Aone b u hb hu h0 hπ hV
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Work.FTS.EllSol.ShiftFT.uTr_Atwo b u hb hu h0 hπ hZ hV
  obtain ⟨K₃, hK₃pos, hK₃⟩ := Work.FTS.EllSol.ShiftFT.uTr_Athree b u hb hu h0 hπ hQ
  set A₁ : ℝ := ∫ p in slotI, slotV b u p with hA₁
  set A₂ : ℝ := ∫ p in slotI, slotZ b u p with hA₂
  set A₃ : ℝ := ∫ p in slotI, slotQ u p with hA₃
  have hA₁nn : 0 ≤ A₁ := by
    rw [hA₁]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
      (fun p hp => slotV_nonneg hp)
  have hA₂nn : 0 ≤ A₂ := by
    rw [hA₂]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
      (fun p hp => slotZ_nonneg hp)
  have hA₃nn : 0 ≤ A₃ := by
    rw [hA₃]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
      (fun p hp => slotQ_nonneg hp)
  set B : ℝ := C * (K₁ * A₁ + Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃))) with hB
  -- the uniform truncation bound
  have key : ∀ N : ℝ, 2 ≤ N →
      (∫⁻ p in slotI, ENNReal.ofReal
        (slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u) p)) ≤ ENNReal.ofReal B := by
    intro N hN
    have hNF : Work.FTS.EllSol.FlatFT.NiceFlat (Work.FTS.EllSol.ShiftFT.uTr N b u) :=
      Work.FTS.EllSol.ShiftFT.uTr_niceFlat N b u hN hu h0 hπ
    obtain ⟨hI₁, hle₁⟩ := hK₁ N hN
    obtain ⟨hI₂, hle₂⟩ := hK₂ N hN
    obtain ⟨hI₃, hle₃⟩ := hK₃ N hN
    have hmain := hC b (Work.FTS.EllSol.ShiftFT.uTr N b u) hNF hI₁ hI₂ hI₃
    refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
    set X : ℝ := ∫ p in slotI, slotV b (Work.FTS.EllSol.ShiftFT.uTr N b u) p with hX
    set Y : ℝ := ∫ p in slotI, slotZ b (Work.FTS.EllSol.ShiftFT.uTr N b u) p with hY
    set Z : ℝ := ∫ p in slotI, slotQ (Work.FTS.EllSol.ShiftFT.uTr N b u) p with hZ
    have hXle : X ≤ K₁ * A₁ := by rw [hX, hA₁]; exact hle₁
    have hYle : Y ≤ K₂ * A₂ + K₂ * A₁ := by
      have h1 : Y ≤ K₂ * A₂ + (K₂ / N) * A₁ := by rw [hY, hA₂, hA₁]; exact hle₂
      have h2 : (K₂ / N) * A₁ ≤ K₂ * A₁ := by
        have hN1 : (1 : ℝ) ≤ N := by linarith
        have : K₂ / N ≤ K₂ := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < N)]
          nlinarith [hK₂pos, hN1]
        exact mul_le_mul_of_nonneg_right this hA₁nn
      linarith
    have hZle : Z ≤ K₃ * A₃ := by rw [hZ, hA₃]; exact hle₃
    have hZnn : 0 ≤ Z := by
      rw [hZ]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
        (fun p hp => slotQ_nonneg hp)
    have hK2A : 0 ≤ K₂ * A₂ + K₂ * A₁ := by nlinarith [hK₂pos, hA₁nn, hA₂nn]
    have hs : Real.sqrt (Y * Z) ≤ Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃)) :=
      Real.sqrt_le_sqrt (mul_le_mul hYle hZle hZnn hK2A)
    have hsum : X + Real.sqrt (Y * Z)
        ≤ K₁ * A₁ + Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃)) := add_le_add hXle hs
    calc C * (X + Real.sqrt (Y * Z))
        ≤ C * (K₁ * A₁ + Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃))) :=
          mul_le_mul_of_nonneg_left hsum hCpos.le
      _ = B := by rw [hB]
  -- the truncation scale
  set Nf : ℕ → ℝ := fun n => (n : ℝ) + 2 with hNf
  have hNf2 : ∀ n : ℕ, 2 ≤ Nf n := by
    intro n; rw [hNf]; push_cast; have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  -- a.e. strong measurability of every truncation integrand
  have hAE : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p))
      (volume.restrict slotI) :=
    fun n => (aesm_slotM_uTr hu h0 hπ (hNf2 n)).aemeasurable.ennreal_ofReal
  -- the pointwise liminf
  have hlim : ∀ᵐ p ∂(volume.restrict slotI),
      ENNReal.ofReal (slotM b u p)
        = Filter.liminf (fun n : ℕ =>
            ENNReal.ofReal (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_slotI]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    rcases lt_or_eq_of_le hp.2.1 with hpos | hzero
    · rcases lt_or_eq_of_le hp.2.2 with hlt | hpi
      · obtain ⟨n₀, hn₀⟩ := exists_nat_gt |p.1|
        have hev : (fun n : ℕ => ENNReal.ofReal
              (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p))
            =ᶠ[Filter.atTop] (fun _ => ENNReal.ofReal (slotM b u p)) := by
          filter_upwards [Filter.eventually_atTop.mpr ⟨n₀, fun n hn => hn⟩] with n hn
          have hlt' : |p.1| < Nf n := by
            have h1 : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            rw [hNf]; push_cast; linarith
          rw [uTr_slotM_eq hu h0 hπ (hNf2 n) hlt' ⟨hpos, hlt⟩]
        rw [Filter.liminf_congr hev, Filter.liminf_const]
      · have hz : Work.FTS.EllipticEst.sEta p.2 = 0 := by
          rw [hpi]; exact Work.FTS.EllSol.Trunc.wE_pi_div_two
        have hzu : slotM b u p = 0 := by rw [slotM_apply, hz, mul_zero]
        have hzn : ∀ n : ℕ, slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p = 0 := by
          intro n; rw [slotM_apply, hz, mul_zero]
        rw [hzu]
        simp only [hzn, ENNReal.ofReal_zero]
        rw [Filter.liminf_const]
    · have hz : Work.FTS.EllipticEst.sEta p.2 = 0 := by
        rw [← hzero]; exact Work.FTS.EllSol.Trunc.wE_zero
      have hzu : slotM b u p = 0 := by rw [slotM_apply, hz, mul_zero]
      have hzn : ∀ n : ℕ, slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p = 0 := by
        intro n; rw [slotM_apply, hz, mul_zero]
      rw [hzu]
      simp only [hzn, ENNReal.ofReal_zero]
      rw [Filter.liminf_const]
  -- the Fatou chain
  have hstep : ∀ n : ℕ, (∫⁻ p in slotI, ENNReal.ofReal
      (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) ≤ ENNReal.ofReal B :=
    fun n => key (Nf n) (hNf2 n)
  have hlimle : Filter.liminf (fun n : ℕ => ∫⁻ p in slotI, ENNReal.ofReal
      (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop ≤ ENNReal.ofReal B := by
    refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall (fun n => bot_le)⟩ ?_
    intro x hx
    obtain ⟨n, hn⟩ := hx.exists
    exact le_trans hn (hstep n)
  calc (∫⁻ p in slotI, ENNReal.ofReal (slotM b u p))
      = ∫⁻ p in slotI, Filter.liminf (fun n : ℕ => ENNReal.ofReal
          (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop :=
        MeasureTheory.lintegral_congr_ae hlim
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in slotI, ENNReal.ofReal
          (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le' hAE
    _ ≤ ENNReal.ofReal B := hlimle
    _ < ⊤ := ENNReal.ofReal_lt_top

end

theorem mixedSlotOfNice
    (hNice : ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ) (u : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat u →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
      (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2))
        ≤ ENNReal.ofReal (C * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
            + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)))))
    (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hZ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)) < ⊤ := by
  obtain ⟨C, hCpos, hC⟩ := hNice
  by_cases hb : 0 ≤ b
  · exact slotFiniteness_nonneg C hCpos hC b hb u hu h0 hπ hV hZ hQ
  · push_neg at hb
    -- for `b < 0` reflect the time variable: the reflected datum satisfies the same
    -- hypotheses with the shift `-b ≥ 0`
    have hb' : 0 ≤ -b := by linarith
    obtain ⟨hu', h0', hπ', hV', hZ', hQ'⟩ := reflectData b u hu h0 hπ hV hZ hQ
    have hcore := slotFiniteness_nonneg C hCpos hC (-b) hb' (fun t θ => u (-t) θ)
      hu' h0' hπ' hV' hZ' hQ'
    have hcore' : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - (-b) * Work.Spaces.pth (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2)) < ⊤ := hcore
    rw [← reflectMixed b u hu] at hcore'
    exact hcore'

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllSol.SpecAux.ShiftSlot11Lin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff ENNReal
open Work.Spaces
open Work.FTS.EllSol.FlatFT

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "thEta" => Work.FTS.EllipticEst.thEta


end

end Work.FTS.EllSol.SpecAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.S20LowerAlt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Step5

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **`s20A2` is the `j = 0` summand of `pPure`.** -/
theorem s20src_A2_eq_pSlot (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.s20A2 Ψ = s20src_pSlot 0 Ψ := by
  unfold Work.FTS.EllipticEst.H2W.s20A2 s20src_pSlot s20src_slotZ s20src_slotFun
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
    (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ) z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ)).symm

theorem s20src_lower_own : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
          + Work.FTS.EllipticEst.H2W.s20A0 Ψ
        ≤ C * Work.FTS.EllipticEst.H2W.pPure Ψ := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  refine ⟨1 + 2 * C0, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ### the per-slice Poincaré bound
  have hslice : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) ∧
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    intro z hz
    have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ := hΨso
    have hu : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      fun n => (hΨso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
    obtain ⟨hlim0, hlim1⟩ := Work.H2W.psi_slice_limits hα h z hz
    obtain ⟨-, -, hInt2, -, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
    obtain ⟨hInt0, hInt1, hbnd0, hbnd1⟩ := hC0 (fun θ => Ψ z θ) hu hlim0 hlim1 hInt2
    have hone : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        1 ≤ Work.FTS.EllipticEst.sEta θ := s20src_one_le_sEta_ae
    have hb0 : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
      have hmono : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => (Ψ z θ) ^ 2)
          (g := fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          (Filter.Eventually.of_forall fun θ => sq_nonneg _) hInt0
          (by
            filter_upwards [hone] with θ hθ
            nlinarith [sq_nonneg (Ψ z θ)])
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using
        le_trans hmono hbnd0
    have hb1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        ≤ C0 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
      have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          (g := fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          (Filter.Eventually.of_forall fun θ => sq_nonneg _) hInt1
          (by
            filter_upwards [hone] with θ hθ
            nlinarith [sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)])
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using
        le_trans hmono hbnd1
    exact ⟨hb0, hb1⟩
  -- ### the `z`-integrability of the majorant
  have hBsEta : MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 Ψ) Work.FTS.EllipticEst.sEta z)
      Work.Spaces.Iz :=
    s20src_integrableOn_slotZ_sEta_DzIter hΨso h.memB 0 (by norm_num)
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => C0 * ((Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ))) Work.Spaces.Iz :=
    (hBsEta.const_mul C0).congr (Filter.Eventually.of_forall fun z => by
      have h : s20src_slotZ (Work.Spaces.pthIter 2 Ψ) Work.FTS.EllipticEst.sEta z
          = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        unfold s20src_slotZ s20src_slotFun
        exact MeasureTheory.integral_const_mul _ _
      simp only [h])
  -- ### the two `z`-level comparisons
  have hA0 : Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ C0 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ C0 * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      filter_upwards [s20src_ae_pos_mem_Iz] with z hz
      have h1 := (hslice z hz).1
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      nlinarith [h1, hw]
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _)
          (integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)))
      hmaj hpt
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  have hA1 : Work.FTS.EllipticEst.H2W.s20A1 Ψ
      ≤ C0 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          ≤ C0 * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      filter_upwards [s20src_ae_pos_mem_Iz] with z hz
      have h1 := (hslice z hz).2
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      nlinarith [h1, hw]
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _)
          (integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)))
      hmaj hpt
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  -- ### the identification of the majorant with `pPure`'s `j = 0` summand
  have hpull : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) = s20src_pSlot 0 Ψ := by
    unfold s20src_pSlot s20src_slotZ s20src_slotFun
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
      (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)).symm
  -- ### the summand bound
  have hp0 : s20src_pSlot 0 Ψ
      ≤ Work.FTS.EllipticEst.H2W.pPure Ψ := by
    rw [s20src_pPure_eq_three Ψ]
    linarith [s20src_pSlot_nonneg 0 Ψ, s20src_pSlot_nonneg 1 Ψ, s20src_pSlot_nonneg 2 Ψ]
  have hsum : Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ (1 + 2 * C0) * Work.FTS.EllipticEst.H2W.pPure Ψ := by
    rw [s20src_A2_eq_pSlot Ψ]
    rw [hpull] at hA0 hA1
    nlinarith [hA0, hA1, hp0, hC0pos.le, s20src_pSlot_nonneg 0 Ψ]
  exact hsum

end Work.FTS.EllipticEst.H2W.Step5
end
end
-- ===== merged: Submission.Work.FTS.IPGen.slotPairing_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Membership in the *open* angular interval, almost everywhere -/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval a.e.: `Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e. -/
theorem ip_ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The square-root form of Cauchy–Schwarz on a set -/

/-- **Cauchy–Schwarz in square-root form**: for nonnegative integrable `A`, `B` on `s`,

  `∫_s √A · √B ≤ √(∫_s A) · √(∫_s B)`.

(For nonnegative `A` the square root `√A` is square-integrable exactly when `A` is integrable,
so this is `Work.Spaces.cs_integral` applied to `√A`, `√B`.) -/
theorem cs_sqrt_le {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hAnn x)).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hBnn x)).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg hAnn) _

/-! ## The two-level Cauchy–Schwarz engine for a general nonnegative weight -/

/-- **The `L²`-Cauchy–Schwarz bound for a single slot with a general weight.**

Suppose `ρ ≥ 0` on `Iθ` and that, a.e. in `θ` (equivalently for `θ ∈ (0,π/2)`, the two
endpoints being null), the weight times the square of each slot is dominated by the
`ℋ⁴`-integrand of the corresponding datum:
`ρ z θ · X z θ ² ≤ HkIntegrand α 4 f z θ` and `ρ z θ · Y z θ ² ≤ HkIntegrand α 4 g z θ`.
Then the weighted slot pairing is bounded by the product of the two `ℋ⁴`-norms with constant
`1`:

  `|∫_z ∫_θ ρ · X · Y| ≤ |f|_{ℋ⁴} · |g|_{ℋ⁴}`.

Route: at each `z`, the pointwise domination turns `ρ |X| |Y|` into the product of the two
`L²`-functions `√(HkIntegrand α 4 f z ·)`, `√(HkIntegrand α 4 g z ·)`; the `θ`-Cauchy–Schwarz
(`cs_sqrt_le`) bounds the `θ`-integral of that product by `√(F z) √(G z)`, where `F`, `G` are
the two slice energies; the `z`-Cauchy–Schwarz (`cs_sqrt_le` again, with `F`, `G` integrable by
`HkMem`) then gives `√(HkSq α 4 f) · √(HkSq α 4 g)`. -/
theorem cs_slotInt_abs_le {α : ℝ} {ρ X Y f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g)
    (hρnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hdf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ)
    (hdg : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hG
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hFint : IntegrableOn F Work.Spaces.Iz := by rw [hF]; exact hmf.2
  have hGint : IntegrableOn G Work.Spaces.Iz := by rw [hG]; exact hmg.2
  -- the `z`-majorant `√F · √G` is integrable, `F` and `G` being in `L¹`
  have hprod : IntegrableOn (fun z => Real.sqrt (F z) * Real.sqrt (G z)) Work.Spaces.Iz := by
    have hFm : AEStronglyMeasurable (fun z => Real.sqrt (F z)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
    have hGm : AEStronglyMeasurable (fun z => Real.sqrt (G z)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
    have hFsq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hFint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
    have hGsq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hGint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
    have hFlp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq hFm).mpr hFsq
    have hGlp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq hGm).mpr hGsq
    exact memLp_one_iff_integrable.mp (hFlp.mul hGlp)
  -- the angular estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hprodθ : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) Work.Spaces.Iθ := by
      have hfm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmf.1 z hz).aestronglyMeasurable
      have hgm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmg.1 z hz).aestronglyMeasurable
      have hfsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmf.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)).symm))
      have hgsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmg.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).symm))
      have hflp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hfm).mpr hfsq
      have hglp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hgm).mpr hgsq
      exact memLp_one_iff_integrable.mp (hflp.mul hglp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |ρ z θ * X z θ * Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
      filter_upwards [ip_ae_mem_Ioo_Iθ] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hρ0 : 0 ≤ ρ z θ := hρnn z hz θ hθI
      have hsX : Real.sqrt (ρ z θ * (X z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) :=
        Real.sqrt_le_sqrt (hdf z hz θ hθ)
      have hsY : Real.sqrt (ρ z θ * (Y z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
        Real.sqrt_le_sqrt (hdg z hz θ hθ)
      have hs : Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) = ρ z θ := by
        rw [← sq, Real.sq_sqrt hρ0]
      calc |ρ z θ * X z θ * Y z θ|
          = ρ z θ * |X z θ| * |Y z θ| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
        _ = (Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ)) * |X z θ| * |Y z θ| := by rw [hs]
        _ = Real.sqrt (ρ z θ * (X z θ) ^ 2) * Real.sqrt (ρ z θ * (Y z θ) ^ 2) := by
            rw [Real.sqrt_mul hρ0, Real.sqrt_mul hρ0, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
            ring
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul hsX hsY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) hprodθ hpt
      _ ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
          rw [hF, hG]
          exact cs_sqrt_le (hmf.1 z hz) (hmg.1 z hz)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ ∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hprod
          (ae_restrict_of_forall_mem hIzm hslice)
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        cs_sqrt_le hFint hGint hFnn hGnn
    _ = Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkSq, Work.Spaces.HkSq, hF, hG]

/-! ## Nonnegativity of the leaf weights, and their pointwise slot domination -/

/-- Every leaf weight of `IP4` is nonnegative on `Iz × Iθ`. -/
theorem leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z hz θ hθ
    exact sq_nonneg _
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **The pointwise slot domination of a leaf weight.**  For the slot `(a,b)` of `ℋ⁴`
(`a + b ≤ 4`) and any leaf weight `ρ` attached to `a`, the weight times the square of the slot
of `h` is dominated by the `ℋ⁴`-integrand of `h`, at every point with `z ∈ Iz`,
`θ ∈ (0,π/2)`:

  `ρ z θ · (D_z^bD_θ^a h z θ)² ≤ HkIntegrand α 4 h z θ`.

Each leaf weight is the square of one of the block weights `Whz = w σ^{-η/2}` (`leafEta`), `1`
(`leafOne`, which is dominated by `Whz²`, resp. by `Wm²` at the mixed slots) and `Wm = W σ^{-γ/2}`
(`leafGam`, only at slots with `a ≥ 1`), and the blocks of `HkIntegrand α 4` are exactly the
squares of those weights times the slots (`Work.Spaces.sq_le_HkIntegrand_z` and
`Work.Spaces.sq_le_HkIntegrand_mixed`). -/
theorem leaf_dom {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 4)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (h : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσ : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha, rfl⟩
  · -- `ρ = leafEta = Whz²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ 4 := by omega
      have hkey : Work.FTS.TransportS.leafEta z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, ← Work.FTS.H2.hbi_Whz_sq z θ hσ]
        ring
      rw [hkey]
      exact Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ b hb
    · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h0
      have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
      simp only [Work.FTS.H2.Wm] at hWm
      have hle : Work.FTS.TransportS.leafEta z θ ≤ Work.Spaces.Wt α z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, hWm]
        exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
      calc Work.FTS.TransportS.leafEta z θ * (Work.Spaces.mixed b a h z θ) ^ 2
          ≤ Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ a b h1 (by omega)
  · -- `ρ = leafOne = 1²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ 4 := by omega
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.H2.Whz z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hσ]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          ≤ Work.FTS.H2.Whz z θ ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ b hb
    · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h0
      have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
      simp only [Work.FTS.H2.Wm] at hWm
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.Spaces.Wt α z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, hWm]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.mixed b a h z θ) ^ 2
          ≤ Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ a b h1 (by omega)
  · -- `ρ = leafGam α = Wm²`, only at slots with `a ≥ 1`
    have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
    simp only [Work.FTS.H2.Wm] at hWm
    have hle : Work.FTS.TransportS.leafGam α z θ = Work.Spaces.Wt α z θ ^ 2 := by
      rw [Work.FTS.TransportS.leafGam, ← hWm]
    calc Work.FTS.TransportS.leafGam α z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        = Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 := by rw [hle]
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ a b ha (by omega)

/-! ## The requested per-slot bound -/

theorem slotPairing_abs_le {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 4)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    {f g : Work.FTS.Galerkin.Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmf : Work.Spaces.HkMem α 4 f)
    (hmg : Work.Spaces.HkMem α 4 g) :
    |Work.FTS.TransportS.slotPairing ρ a b f g|
      ≤ Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      ρ z θ * Work.Spaces.mixed b a f z θ * Work.Spaces.mixed b a g z θ|
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
    cs_slotInt_abs_le hmf hmg (leaf_nonneg hρ)
      (fun z hz θ hθ => leaf_dom hα hab hρ f hz hθ)
      (fun z hz θ hθ => leaf_dom hα hab hρ g hz hθ)
  rw [Work.FTS.TransportS.slotPairing]
  simpa only [Work.FTS.Nonlin.Xn] using hmain

end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.Rop_pointwiseU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Rop_pointwiseU`: the pointwise bounds for `ℛ(Φ̃_*)` with a **constant uniform in `α`, `Cs`,
`Φs`**

`Work.FTS.Nonlinear.Pieces.RNP.Rop_pointwise` establishes the four pointwise bounds for
`ℛ(Φ̃_*) = Rop α (PhiTs α Φs)` with a constant `C` that is allowed to depend on `α`, `Cs`, `Φs`.
Its proof, however, only ever uses

* the `𝒲^{4,∞}`-bound `WlInf α 4 ((z+1)/z·ℛ(Φ̃_*)) ≤ Cs·α` of `StarPkg`, and
* the truncated bound `WlInf α 4 (χ_{Iθ}·ℛ(Φ̃_*)) ≤ K·(max Cs 0·α)` of
  `row10aux.Rstar_WlInf`, whose constant `K` is *universal*,

so the same constant `2K+1` works for every admissible `(α, Cs, Φs)`.  This file makes that
explicit: `Rop_uK` is the universal constant extracted from `Rstar_WlInf` (via
`Classical.choose`, so that it is a genuine global constant rather than a bound variable), and
the proof of `Rop_pointwise` goes through verbatim with `C = 2·Rop_uK + 1`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false





end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNPV2.row11 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNPV2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Row 11 of the `N4` table

The piece is `N₁^{**} = 2 ℛ(Φ̃_*) F_*` (`Work.FTS.Nonlin.N1ss`) and the claim is
`|N₁^{**}|_{ℋ⁴} ≤ K α²`.

The design's route (`FTS/N45_DESIGN_LEAD.md` §3.4, row 11) splits `N₁^{**}` as the product of an
*angular* factor and a *radial* factor:

* `F_*(z,θ) = Bv(θ)·z/(1+z)²` with `Bv(θ) = 2αΓ(θ)/c(α)`, so
  `N₁^{**} = (2 Bv(θ)) · (ℛ(Φ̃_*) z/(1+z)²)`;
* the angular factor is controlled by the explicit estimates of `Bv_WlInf` (`|Bv| ≤ 20α`,
  `|D_θ^j Bv| ≤ 20α tBound(j-1)0 · sin(2θ)^{-α/5}/(α+sin 2θ)`);
* the radial factor carries the whole `𝒲^{4,∞}`-content: `((z+1)³/z²)·(ℛ(Φ̃_*)z/(1+z)²) = ℛ̃(Φ̃_*)`
  is exactly the *weighted* coefficient of the star package, whose `𝒲^{4,∞}`-norm is `≤ Cs α`.

The passage from `𝒲^{4,∞}`-control of the radial factor to the pointwise bounds needed by
`wtoHQ_of_pointwise` is `WtoH_Radial_Q`/`WtoH_Mixed_Q`, and the product with the angular factor
is handled by the pointwise Leibniz rules of the interior class `SmoothQuad`
(`sqm_pz_DthIter_mul_le_4`).  Both factors are `SmoothQuad`, so every Leibniz expansion used
below is an identity — none of the (false) *global* product rules for `𝒲^{4,∞}` is needed. -/

/-! ## The two factors -/

/-- The angular factor `2 Bv(θ)` of row 11 — a function of `θ` alone. -/
def angF (α : ℝ) : ℝ → ℝ := fun θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Bv α θ

/-- The angular factor, viewed as a function of `(z,θ)`. -/
def angB (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => angF α θ

/-- The radial factor `ℛ(Φ̃_*) · z/(1+z)²` of row 11. -/
def radA (α : ℝ) (Φs : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2

@[simp] theorem angF_apply (α θ : ℝ) :
    angF α θ = 2 * Work.FTS.Nonlinear.Pieces.RNP.Bv α θ := rfl

@[simp] theorem angB_apply (α z θ : ℝ) : angB α z θ = angF α θ := rfl

@[simp] theorem radA_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    radA α Φs z θ
      = Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2 := rfl

/-- **The factorisation of row 11**: `N₁^{**} = (2 Bv(θ))·(ℛ(Φ̃_*) z/(1+z)²)`. -/
theorem N1ss_eq_angB_mul_radA (α : ℝ) (Φs : Fn) :
    Work.FTS.Nonlin.N1ss α Φs = fun z θ => angB α z θ * radA α Φs z θ := by
  funext z θ
  simp only [Work.FTS.Nonlin.N1ss, angB, angF, radA, Work.Construction.Fstar,
    Work.FM.Fstar, Work.FTS.Nonlinear.Pieces.RNP.Bv]
  ring_nf

/-- The weighted radial factor is the weighted coefficient of the star package. -/
theorem weighted_eq_Rv (α : ℝ) (Φs : Fn) :
    (fun z θ => (z + 1) ^ 3 / z ^ 2 * radA α Φs z θ)
      = Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs := by
  funext z θ
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp [radA, Work.FTS.Nonlinear.Pieces.RNP.Rv]
  · rcases eq_or_ne z (-1) with hz1 | hz1
    · subst hz1; simp [radA, Work.FTS.Nonlinear.Pieces.RNP.Rv]
    · have h1 : (1 + z : ℝ) ≠ 0 := by intro hh; exact hz1 (by linarith)
      simp only [radA, Work.FTS.Nonlinear.Pieces.RNP.Rv, Work.FTS.Nonlin.PhiTs]
      rw [div_mul_div_comm,
        show (z + 1) ^ 3 * (Work.Construction.Rop α
              (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ * z)
            = ((1 + z) * (1 + z) ^ 2) * (Work.Construction.Rop α
              (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ * z) by ring,
        show z ^ 2 * (1 + z) ^ 2 = (z * (1 + z) ^ 2) * z by ring]
      field_simp
      ring

/-- `∂_z^k` of a product with a factor depending on `θ` alone: the factor comes out.  (The
`z`-derivative is blind to the `θ`-dependence of the constant.) -/
theorem pzIter_theta_mul (k : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter k (fun z θ => a θ * f z θ)
      = fun z θ => a θ * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
      funext z θ
      exact Work.FTS.Nonlinear.Pieces.RNP.deriv_const_mul_loc (a θ)
        (fun z' => Work.Spaces.pzIter k f z' θ) z

/-! ## Smoothness of the two factors -/

/-- `Bv(α,·)` is `C^∞` on the open interval `(0,π/2)`. -/
theorem contDiffOn_Bv (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Bv α θ) (Set.Ioo 0 (π / 2)) := by
  rw [Work.FTS.Nonlinear.Pieces.RNP.Bv_eq_const_mul α]
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    Real.contDiff_sin.contDiffOn.mul (Real.contDiff_cos.contDiffOn.pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hGam : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π / 2)) := hbase.rpow_const_of_ne hne
  exact contDiffOn_const.mul hGam

/-- The angular factor is `C^∞` on the open quadrant. -/
theorem smoothQuad_angF (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (fun z θ => angF α θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => angF α θ)) Work.Spaces.quadU
  have hsnd : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.2)
      Work.Spaces.quadU := contDiffOn_snd
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => angF α θ)
      (Set.Ioo 0 (π / 2)) := contDiffOn_const.mul (contDiffOn_Bv α)
  have h := h2.comp hsnd (fun p hp => hp.2)
  refine h.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  rfl



/-! ## The angular weight and the pointwise bounds for the angular factor -/

/-- The angular weight `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}` of the `𝒲^{4,∞}`-norm. -/
def Phi (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- A universal bound for the auxiliary constants `tBound j 0`, `j ≤ 3`. -/
def TBound : ℝ := (∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1)) + 1

theorem TBound_pos : 0 < TBound := by
  have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1) :=
    Finset.sum_nonneg (fun j _ => by linarith [Work.Spaces.tBound_nonneg j 0])
  rw [TBound]
  linarith

theorem tBound_le_TBound (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) :
    Work.Spaces.tBound (j - 1) 0 ≤ TBound := by
  have hmem : j - 1 ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hsingle : Work.Spaces.tBound (j - 1) 0 + 1
      ≤ ∑ i ∈ Finset.range 4, (Work.Spaces.tBound i 0 + 1) :=
    Finset.single_le_sum (f := fun i : ℕ => Work.Spaces.tBound i 0 + 1)
      (fun i _ => by linarith [Work.Spaces.tBound_nonneg i 0]) hmem
  rw [TBound]
  linarith

theorem Phi_nonneg (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Phi α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)

theorem Phi_le_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Phi α θ ≤ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 (by positivity)
  have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
  calc Phi α θ = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := rfl
    _ ≤ 2 * 1 := mul_le_mul h1 hr (Real.rpow_nonneg hs0 _) (by norm_num)
    _ = 2 := by norm_num

/-- The angular factor is bounded by `40α`. -/
theorem angF_abs_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : |angF α θ| ≤ 40 * α := by
  have h := Work.FTS.Nonlinear.Pieces.RNP.Bv_abs_le α hα hα1 hθ
  rw [angF_apply, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- The angular derivatives of the angular factor carry the weight `Φ`. -/
theorem dthU_angF_weight_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    (hj4 : j ≤ 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.dthU^[j] (angF α) θ| ≤ 40 * α * TBound * Phi α θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hd0 : 0 < α + Real.sin (2 * θ) := by linarith
  have hdne : α + Real.sin (2 * θ) ≠ 0 := ne_of_gt hd0
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg (le_of_lt hs0) _) (le_of_lt hd0)
  have hss : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) = 1 := by
    rw [mul_comm, ← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero]
  have hprod : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (le_of_lt hd0) (Real.rpow_nonneg (le_of_lt hs0) _)
  have hid : (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) = 1 := by
    rw [div_mul_eq_mul_div, mul_comm ((Real.sin (2 * θ)) ^ (-(α / 5)))
        ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)),
      mul_assoc, hss, mul_one, div_self hdne]
  have hB := Work.FTS.Nonlinear.Pieces.RNP.Bv_dthIter_weight_le α hα hα1 j hj hθI
  have hB' : |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs0) _),
      abs_of_nonneg (le_of_lt hd0), mul_div_assoc] at hB
    exact hB
  have hkey : |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    calc |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
        = |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
          rw [hid, mul_one]
      _ = (|Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      _ ≤ (20 * α * Work.Spaces.tBound (j - 1) 0)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right hB' hprod
  have hfun : angF α = fun t => 2 * Work.FTS.Nonlinear.Pieces.RNP.Bv α t := rfl
  rw [hfun, Work.Spaces.dthU_iter_const_mul,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hTB := tBound_le_TBound j hj hj4
  have hΦ0 := Phi_nonneg α hα hθI
  have hstep : 20 * α * Work.Spaces.tBound (j - 1) 0
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      ≤ 20 * α * TBound * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    have h1 : 20 * α * Work.Spaces.tBound (j - 1) 0 ≤ 20 * α * TBound :=
      mul_le_mul_of_nonneg_left hTB (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hprod
  simp only [Phi]
  calc 2 * |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
      ≤ 2 * (20 * α * Work.Spaces.tBound (j - 1) 0
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ ≤ 2 * (20 * α * TBound * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 40 * α * TBound * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring

/-- The angular derivatives of the angular factor, without weight. -/
theorem dthU_angF_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    (hj4 : j ≤ 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.dthU^[j] (angF α) θ| ≤ 80 * α * TBound := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hw := dthU_angF_weight_le hα hα1 j hj hj4 hθ
  have hΦ := Phi_le_two α hα hα1 hθI
  calc |Work.Spaces.dthU^[j] (angF α) θ|
      ≤ 40 * α * TBound * Phi α θ := hw
    _ ≤ 40 * α * TBound * 2 := by
        have hT0 : (0 : ℝ) < TBound := TBound_pos
        have : (0 : ℝ) ≤ 40 * α * TBound := by positivity
        exact mul_le_mul_of_nonneg_left hΦ this
    _ = 80 * α * TBound := by ring

/-- The constant `Ca` dominating all the angular bounds of row 11. -/
def Ca : ℝ := 100 * TBound + 100

theorem Ca_pos : 0 < Ca := by
  have := TBound_pos
  rw [Ca]; linarith

theorem Ca_ge_40 : 40 ≤ Ca := by
  have := TBound_pos
  rw [Ca]; linarith

theorem Ca_ge_80 : 80 * TBound ≤ Ca := by
  have := TBound_pos
  rw [Ca]; linarith

theorem Ca_ge_40TB : 40 * TBound ≤ Ca := by
  have := TBound_pos
  rw [Ca]; linarith

/-! ## The collapse of the double Leibniz sum -/

/-- When the first factor of a product depends on `θ` alone, the double Leibniz sum of
`∂_z^l D_θ^i` collapses: only the `c = 0` terms survive. -/
theorem mixed_sum_collapse (l i : ℕ) (a2 : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z (θ' : ℝ) => a2 θ')) z θ|
          * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) F) z θ|)
      = ∑ a ∈ Finset.range (i + 1),
          |Work.Spaces.dthU^[a] a2 θ| * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) F) z θ| := by
  have hDthfun : ∀ a : ℕ, Work.Spaces.DthIter a (fun z (θ' : ℝ) => a2 θ')
      = fun _ (θ' : ℝ) => Work.Spaces.dthU^[a] a2 θ' := by
    intro a
    funext z' θ'
    exact Work.FTS.Nonlinear.Pieces.RNP.DthIter_z_indep a2 a z' θ'
  rw [Finset.sum_eq_single (0 : ℕ)]
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Work.Spaces.pzIter_zero, hDthfun a, Nat.sub_zero]
  · intro c hc hcne
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [hDthfun a, Work.FTS.Nonlinear.Pieces.RNP.pzIter_z_indep_ne_zero
      (Work.Spaces.dthU^[a] a2) c hcne]
    simp
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos l)) h0

/-! ## Row 11 -/


end Work.FTS.Nonlinear.Pieces.RNPV2
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.n3split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.Pieces.Rl1

/-!
# `n3split` — the four-way split of the transport term `N₃`

`N₃ = -2α V(Φ̃) D_z F` with `F = F_* + g` and `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F)`.  Writing
`Φ̃ = Φ̃_* + Φ̃_g` with `Φ̃_* = PhiTil α (Fstar α) Φs` and `Φ̃_g = PhiTil α g Φg`
(which uses the additivity `L₁₂(F_* + g) = L₁₂(F_*) + L₁₂(g)` of `hL`, together with the
linearity of `Theta` in `F`) and `F = F_* + g`, the product splits into the four pieces
`N₃^{gg} + N₃^{gs} + N₃^{sg} + N₃^{ss}` of `Work.FTS.Nonlin.Defs`.

This is the `N₃` component of the split in `Work.FTS.Nonlinear.Pieces.splitsDiff`,
restated with the local (`z > 0`) hypotheses available in the `rl1` row.
-/


end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.sin_rpow_deriv_sq_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sin(2θ)^(2-γ)·(∂_θ D_z^s F · w)² = (D_z^s D_θ F · W)²`

The two facts behind the identity of the linearised angular Hardy estimate: at an interior
point `(z,θ)` of the open quadrant and for a datum `F` smooth there,

* the angular derivative `D_θ F = sin(2θ) ∂_θ F` commutes with `D_z^s = (z ∂_z)^s`, i.e.
  `D_z^s D_θ F = sin(2θ)·∂_θ(D_z^s F)`
  (`mixed_one_eq_sin_mul_pth`, from `DzIter_const_mul_apply` + Clairaut);
* the weight identity `sin(2θ)^(2-γ) = (sin(2θ)·sin(2θ)^(-γ/2))²`
  (`sin_rpow_sq_factor`, pure `Real.rpow` algebra on the positive base `sin(2θ)`).

Together they give `sin(2θ)^(2-γ)·(∂_θD_z^sF · w)² = (D_z^sD_θF · w·sin(2θ)^(-γ/2))²`, which is
the statement below after unfolding `Wt = w·w_θ` and `w_θ = sin(2θ)^(-γ/2)`.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

/-- **The angular derivative of the radial iterates.**  For `F` smooth on the open quadrant and
`(z,θ)` an interior point, `D_z^s D_θ F = sin(2θ)·∂_θ(D_z^s F)`.

The factor `sin(2θ)` of `D_θ` is `z`-independent, so it passes through the iterated curvilinear
radial derivative (`Work.FTS.H2.DzIter_const_mul_apply`); the remaining identity
`D_z^s (∂_θ F) = ∂_θ (D_z^s F)` is Clairaut's theorem in the form valid on the open quadrant
(`Work.Blocks.pth_DzIter_eqOn_Q0`). -/
theorem mixed_one_eq_sin_mul_pth (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (s : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed s 1 F z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter s F) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  -- the `sin(2θ)`-factor of `D_θ` passes through the radial iterates
  have h2 : Work.Spaces.DzIter s (Work.Spaces.Dth F) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter s (Work.Spaces.pth F) z θ := by
    rw [show Work.Spaces.Dth F
          = (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth F z θ) from rfl]
    exact Work.FTS.H2.DzIter_const_mul_apply (fun θ => Real.sin (2 * θ))
      (Work.Spaces.pth F) s z θ
  -- Clairaut: `∂_θ` commutes with `D_z^s` on the open quadrant
  have h3 : Work.Spaces.DzIter s (Work.Spaces.pth F) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter s F) z θ :=
    (Work.Blocks.pth_DzIter_eqOn_Q0 hF s hmem).symm
  rw [show Work.Spaces.mixed s 1 F = Work.Spaces.DzIter s (Work.Spaces.Dth F) from rfl,
    h2, h3]

/-- **The weight identity.**  For `S > 0`, `S^(2-γ) = (S·S^(-γ/2))²`.

Pure `Real.rpow` algebra: first `S^(-γ/2)·S^(-γ/2) = S^(-γ/2 + -γ/2)` (`Real.rpow_add`),
then `S·S = S^2` (`Real.rpow_two`) and `S^2·S^(-γ) = S^(2-γ)` (`Real.rpow_add` again).  All
the `rpow` steps are on the positive base `S`, so no degeneracy of `sin(2θ)` or of the
exponent `2-γ` can occur. -/
theorem sin_rpow_sq_factor (γ S : ℝ) (hS : 0 < S) :
    S ^ (2 - γ) = (S * S ^ (-(γ / 2))) ^ 2 := by
  have hs2 : (S ^ (-(γ / 2))) ^ 2 = S ^ (-(γ / 2) + -(γ / 2)) := by
    rw [sq, ← Real.rpow_add hS]
  rw [mul_pow, hs2, ← Real.rpow_two, ← Real.rpow_add hS]
  congr 1
  ring

theorem sin_rpow_deriv_sq_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (s : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed s 1 F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  -- the identity `D_z^s D_θ F = sin(2θ) ∂_θ(D_z^s F)`, with `∂_θ` spelled `deriv`
  have hmix : Work.Spaces.mixed s 1 F z θ
      = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ := by
    rw [mixed_one_eq_sin_mul_pth F hF s hz hθ]
    rfl
  rw [hmix, Work.Spaces.Wt, Work.Spaces.wTheta]
  -- the base of every `rpow` below is positive
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hinner := sin_rpow_sq_factor (Work.Spaces.gam α) (Real.sin (2 * θ)) hS
  -- `(sin(2θ) ∂_θ(D_z^sF) (w·sin(2θ)^(-γ/2)))² = (sin(2θ)·sin(2θ)^(-γ/2))²·(∂_θ(D_z^sF)·w)²`
  have hsq : (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          * (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2 := by
    rw [show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))
        = (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))
          * (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) by ring,
      mul_pow]
  exact (hsq.trans (by rw [hinner])).symm

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.WlInf_theta_only_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real Topology ContDiff
open MeasureTheory Set Filter


/-- `∂_z^k` of a function of `θ` alone vanishes for `k ≥ 1`. -/
private lemma pzIter_theta_eq_zero (g : ℝ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (fun _ θ => g θ) = fun _ _ => (0 : ℝ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact pzIter_theta_only_succ g k'

/-- `∂_z^k D_θ^j` of a function of `θ` alone vanishes for `k ≥ 1`. -/
private lemma pzIter_DthIter_theta_eq_zero (g : ℝ → ℝ) (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) = fun _ _ => (0 : ℝ) := by
  rw [DthIter_theta_only]
  exact pzIter_theta_eq_zero (Work.Spaces.dthU^[j] g) hk

/-- `|a·s/d| = |a|·s/d` for `s, d ≥ 0`. -/
private lemma abs_mul_div_of_nonneg {a s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) :
    |a * s / d| = |a| * s / d := by
  rw [abs_div, abs_mul, abs_of_nonneg hs, abs_of_nonneg hd]

/-- The angular slot with `k = 0` is bounded by `C`. -/
private lemma angSlot_zero_le (α C : ℝ) (hα : 0 < α) (g : ℝ → ℝ)
    (hw : ∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] g θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ C)
    {j : ℕ} (hj1 : 1 ≤ j) (hj5 : j ≤ 5) :
    Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0
        * Work.Spaces.pzIter 0 (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ C := by
  refine Work.Spaces.supAbs_le (fun z _ θ hθ => ?_)
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hd : 0 ≤ α + Real.sin (2 * θ) := by linarith
  rw [Work.Spaces.pzIter_zero, DthIter_theta_only]
  simp only [pow_zero, one_mul]
  rw [abs_mul_div_of_nonneg (Real.rpow_nonneg hs _) hd]
  exact hw j hj1 hj5 θ hθ

private lemma sum6_ite_eq (C : ℝ) :
    (∑ k ∈ Finset.range 6, (if k = 0 then C else (0 : ℝ))) = C := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hbne
    rw [ite_eq_right hbne]
  · intro h
    exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 6)) h

private lemma sum66_ite_eq (C : ℝ) :
    (∑ j ∈ Finset.range 6, ∑ k ∈ Finset.range 6,
      (if k = 0 ∧ 1 ≤ j ∧ j ≤ 5 then C else (0 : ℝ))) = 5 * C := by
  have hinner : ∀ j : ℕ, (∑ k ∈ Finset.range 6,
      (if k = 0 ∧ 1 ≤ j ∧ j ≤ 5 then C else (0 : ℝ)))
      = (if 1 ≤ j ∧ j ≤ 5 then C else (0 : ℝ)) := by
    intro j
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hbne
      rw [ite_eq_right (fun h => hbne h.1)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 6)) h
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [Finset.sum_range_succ' (fun j => if 1 ≤ j ∧ j ≤ 5 then C else (0 : ℝ)) 5]
  have h0 : (if 1 ≤ (0 : ℕ) ∧ (0 : ℕ) ≤ 5 then C else (0 : ℝ)) = 0 := by norm_num
  rw [h0, add_zero]
  have hone : ∀ j ∈ Finset.range 5,
      (if 1 ≤ j + 1 ∧ j + 1 ≤ 5 then C else (0 : ℝ)) = C := by
    intro j hj
    have hj5 : j < 5 := Finset.mem_range.mp hj
    rw [ite_eq_left (by omega : 1 ≤ j + 1 ∧ j + 1 ≤ 5)]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-- Sharp `𝒲^{5,∞}`-reduction for a function of `θ` alone.

For `F = fun _ θ => g θ` the derivatives `pzIter k F` vanish for `k ≥ 1` and
`DthIter j F = fun _ θ => dthU^[j] g θ` (`pzIter_theta_only_succ`, `DthIter_theta_only` in
`FTS/PhiStar/Psi0Est/Defs`), so in `WlInf α 5 F` only the slots with `k = 0` survive: the
radial slot contributes `supAbs (fun _ θ => g θ) ≤ C`, the five angular slots
`k = 0`, `1 ≤ j ≤ 5` contribute `supAbs (fun _ θ => dthU^[j] g θ · weight) ≤ C` each, and
every slot with `k ≥ 1` is the supremum of the zero function (`supAbs_zero_eq`).  Total
`C + 5C = 6C`. -/
theorem WlInf_theta_only_six (α : ℝ) (C : ℝ) (hα : 0 < α) (hC : 0 < C) (g : ℝ → ℝ)
    (hg : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ C)
    (hw : ∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] g θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ C) :
    Work.Spaces.WlInfMem α 5 (fun _ θ => g θ) ∧
      Work.Spaces.WlInf α 5 (fun _ θ => g θ) ≤ 6 * C := by
  have hC0 : 0 ≤ C := le_of_lt hC
  have hs2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  constructor
  · constructor
    · intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ hθ => ?_)
        simpa using hg θ hθ
      · have hk1 : 1 ≤ k := by omega
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (fun _ θ => g θ) z θ = 0 := by
          rw [pzIter_theta_eq_zero g hk1]
        rw [hz]
        simp only [mul_zero, abs_zero]
        exact hC0
    · intro j _ k _ hj1 hjk
      by_cases hk0 : k = 0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ hθ => ?_)
        have hd : 0 ≤ α + Real.sin (2 * θ) := by linarith [hs2 θ hθ]
        rw [Work.Spaces.pzIter_zero, DthIter_theta_only]
        simp only [pow_zero, one_mul]
        rw [abs_mul_div_of_nonneg (Real.rpow_nonneg (hs2 θ hθ) _) hd]
        exact hw j hj1 (by omega) θ hθ
      · have hk1 : 1 ≤ k := by omega
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ = 0 := by
          rw [pzIter_DthIter_theta_eq_zero g j hk1]
        rw [hz]
        simp only [mul_zero, zero_mul, zero_div, abs_zero]
        exact hC0
  · rw [Work.Spaces.WlInf]
    have hS1 : (∑ k ∈ Finset.range (5 + 1), Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (fun _ θ => g θ) z θ)) ≤ C := by
      refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) (le_of_eq (sum6_ite_eq C))
      by_cases hk0 : k = 0
      · subst hk0
        rw [ite_eq_left rfl]
        refine Work.Spaces.supAbs_le (fun z _ θ hθ => ?_)
        simpa using hg θ hθ
      · have hk1 : 1 ≤ k := by omega
        rw [ite_eq_right hk0]
        refine Work.Spaces.supAbs_le (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (fun _ θ => g θ) z θ = 0 := by
          rw [pzIter_theta_eq_zero g hk1]
        rw [hz]
        simp
    have hS2 : (∑ j ∈ Finset.range (5 + 1), ∑ k ∈ Finset.range (5 + 1),
        if 1 ≤ j ∧ k + j ≤ 5 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 5 * C := by
      refine le_trans (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_)))
        (le_of_eq (sum66_ite_eq C))
      by_cases h : 1 ≤ j ∧ k + j ≤ 5
      · rw [ite_eq_left h]
        have hj1 : 1 ≤ j := h.1
        have hj5 : j ≤ 5 := by omega
        by_cases hk0 : k = 0
        · subst hk0
          rw [ite_eq_left ⟨rfl, hj1, hj5⟩]
          exact angSlot_zero_le α C hα g hw hj1 hj5
        · have hk1 : 1 ≤ k := by omega
          rw [ite_eq_right (fun hh => hk0 hh.1)]
          refine Work.Spaces.supAbs_le (fun z _ θ _ => ?_)
          have hz : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ = 0 := by
            rw [pzIter_DthIter_theta_eq_zero g j hk1]
          rw [hz]
          simp
      · rw [ite_eq_right h]
        split_ifs with hh
        · exact hC0
        · exact le_refl 0
    linarith

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.cVecBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Psi0Est.cVecBound` — the coefficients `cVec j r` are bounded on `ℝ`

The coefficient family `cVec` of `AClassDefs` is generated from `c₀,₀ = 2cos 2θ` by the
operations `f ↦ D_θ f`, `f ↦ 4 sin²θ · f`, `f ↦ f + g` and subtraction, starting from the
explicitly `IsCoef` functions.  Since `IsCoef f` (i.e. `f θ = A(sin θ) + cos θ · B(sin θ)`
with `A, B : ℝ[X]`) is closed under all of these and every `IsCoef` function is bounded on
`ℝ`, each `cVec j r` admits a uniform bound `cB j r`, which is the content of `cVecBound`.

Everything is proved here from scratch; the only inputs are the definition of `IsCoef` and
of `cVec` in `AClassDefs`.
-/

noncomputable section

open scoped Real Topology

open Polynomial

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

namespace CVecBnd

/-! ## Elementary polynomial evaluation bounds -/

/-- For `|x| ≤ 1`, the value `p.eval x` of a real polynomial is bounded by the sum of the
absolute values of its coefficients (in degrees up to `natDegree p`). -/
lemma abs_eval_le (p : ℝ[X]) (x : ℝ) (hx : |x| ≤ 1) :
    |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hxi : |x ^ i| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) hx
  calc |p.coeff i| * |x ^ i| ≤ |p.coeff i| * 1 := mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
    _ = |p.coeff i| := by ring

/-! ## The class `IsCoef` is closed under the generating operations, and bounded -/

lemma isCoef_zero : IsCoef (0 : ℝ → ℝ) := ⟨0, 0, fun _ => by simp⟩

lemma isCoef_add {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f + g) := by
  obtain ⟨A1, B1, h1⟩ := hf
  obtain ⟨A2, B2, h2⟩ := hg
  exact ⟨A1 + A2, B1 + B2, fun θ => by
    rw [Pi.add_apply, h1 θ, h2 θ]; simp only [Polynomial.eval_add]; ring⟩

lemma isCoef_neg {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (-f) := by
  obtain ⟨A, B, h⟩ := hf
  exact ⟨-A, -B, fun θ => by
    rw [Pi.neg_apply, h θ]; simp only [Polynomial.eval_neg]; ring⟩

lemma isCoef_sub {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f - g) := by
  rw [sub_eq_add_neg]; exact isCoef_add hf (isCoef_neg hg)


/-- `IsCoef` is closed under multiplication: `(A₁ + cB₁)(A₂ + cB₂)` with `c = cos θ`,
`s = sin θ` is `(A₁A₂ + (1-X²)B₁B₂)(s) + c·(A₁B₂ + A₂B₁)(s)`. -/
lemma isCoef_mul {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f * g) := by
  obtain ⟨A1, B1, h1⟩ := hf
  obtain ⟨A2, B2, h2⟩ := hg
  refine ⟨A1 * A2 + (1 - X ^ 2) * B1 * B2, A1 * B2 + A2 * B1, ?_⟩
  intro θ
  rw [Pi.mul_apply, h1 θ, h2 θ]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  linear_combination (Polynomial.eval (Real.sin θ) B1 * Polynomial.eval (Real.sin θ) B2) * hc

/-- `IsCoef` is closed under `D_θ = dthU`: writing `f θ = A(s) + c·B(s)` (`s = sin θ`,
`c = cos θ`) one has `deriv f θ = c A'(s) - s B(s) + c² B'(s)`, so
`D_θ f θ = 2 s (1-s²)·A'(s) + c·2s·((1-s²)B'(s) - s B(s))`, an `IsCoef` function with
data `(2X(1-X²)·A', 2X((1-X²)·B' - X·B))`. -/
lemma isCoef_dthU {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (Work.Spaces.dthU f) := by
  obtain ⟨A, B, h⟩ := hf
  rw [show f = fun θ => Polynomial.eval (Real.sin θ) A
      + Real.cos θ * Polynomial.eval (Real.sin θ) B from funext h]
  clear h
  refine ⟨2 * X * (1 - X ^ 2) * derivative A,
    2 * X * ((1 - X ^ 2) * derivative B - X * B), ?_⟩
  intro θ
  rw [Work.Spaces.dthU_apply]
  have h1 : HasDerivAt (fun θ => Polynomial.eval (Real.sin θ) A)
      (Polynomial.eval (Real.sin θ) (derivative A) * Real.cos θ) θ :=
    (Polynomial.hasDerivAt A (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)
  have h2 : HasDerivAt (fun θ => Real.cos θ * Polynomial.eval (Real.sin θ) B)
      ((-Real.sin θ) * Polynomial.eval (Real.sin θ) B
        + Real.cos θ * (Polynomial.eval (Real.sin θ) (derivative B) * Real.cos θ)) θ :=
    (Real.hasDerivAt_cos θ).mul
      ((Polynomial.hasDerivAt B (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ))
  have hd : deriv (fun θ => Polynomial.eval (Real.sin θ) A
        + Real.cos θ * Polynomial.eval (Real.sin θ) B) θ
      = Polynomial.eval (Real.sin θ) (derivative A) * Real.cos θ
        + ((-Real.sin θ) * Polynomial.eval (Real.sin θ) B
          + Real.cos θ * (Polynomial.eval (Real.sin θ) (derivative B) * Real.cos θ)) :=
    (h1.add h2).deriv
  rw [hd, Real.sin_two_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  linear_combination (2 * Real.sin θ * (Polynomial.eval (Real.sin θ) (derivative A)
    + Real.cos θ * Polynomial.eval (Real.sin θ) (derivative B))) * hc

/-- Every `IsCoef` function is bounded on `ℝ`: `|A(sin θ)| ≤ Σ|coeff|` and
`|cos θ · B(sin θ)| ≤ Σ|coeff|`. -/
lemma isCoef_bdd {f : ℝ → ℝ} (hf : IsCoef f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, |f θ| ≤ M := by
  obtain ⟨A, B, h⟩ := hf
  refine ⟨(∑ i ∈ Finset.range (A.natDegree + 1), |A.coeff i|)
    + (∑ i ∈ Finset.range (B.natDegree + 1), |B.coeff i|), by positivity, ?_⟩
  intro θ
  rw [h θ]
  have hA := abs_eval_le A (Real.sin θ) (Real.abs_sin_le_one θ)
  have hB := abs_eval_le B (Real.sin θ) (Real.abs_sin_le_one θ)
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  calc |Polynomial.eval (Real.sin θ) A + Real.cos θ * Polynomial.eval (Real.sin θ) B|
      ≤ |Polynomial.eval (Real.sin θ) A|
          + |Real.cos θ * Polynomial.eval (Real.sin θ) B| := abs_add_le _ _
    _ ≤ (∑ i ∈ Finset.range (A.natDegree + 1), |A.coeff i|)
          + 1 * (∑ i ∈ Finset.range (B.natDegree + 1), |B.coeff i|) := by
        apply add_le_add hA
        rw [abs_mul]
        exact mul_le_mul hc hB (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-! ## The initial data of the recursion -/

lemma isCoef_two_cos_two : IsCoef (fun θ => 2 * Real.cos (2 * θ)) := by
  refine ⟨Polynomial.C 2 - Polynomial.C 4 * X ^ 2, 0, fun θ => ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]
  rw [Real.cos_two_mul']
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma isCoef_four_sin_sq : IsCoef (fun θ => 4 * Real.sin θ ^ 2) := by
  refine ⟨Polynomial.C 4 * X ^ 2, 0, fun θ => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]

/-! ## Unfolding `cVec` along the recursion -/

/-- The `cVec`-recursion in its general form: for `k ≠ j`,
`cVec (j+1) (k+1) = D_θ (cVec j (k+1)) + 4sin²θ · cVec j (k+1) + cVec j k`. -/
lemma cVec_succ_succ_of_ne (j k : ℕ) (h : k ≠ j) :
    cVec (j + 1) (k + 1) = fun θ => Work.Spaces.dthU (cVec j (k + 1)) θ
      + 4 * Real.sin θ ^ 2 * cVec j (k + 1) θ + cVec j (k + 1 - 1) θ := by
  cases j with
  | zero =>
    simp only [cVec]
    rw [if_neg (by omega : ¬ k + 1 = 0 + 1), if_neg (by omega : ¬ k + 1 = 0)]
  | succ j =>
    simp only [cVec]
    rw [if_neg (by omega : ¬ k + 1 = j + 1 + 1), if_neg (by omega : ¬ k + 1 = 0)]

/-- **Every coefficient `cVec j r` is in the class `IsCoef`** (hence bounded).  Induction on
`j` with a full case analysis on `r`, using the closure properties above. -/
lemma isCoef_cVec : ∀ j r, IsCoef (cVec j r) := by
  intro j
  induction j with
  | zero =>
    intro r
    rcases r with _ | k
    · rw [cVec_zero_zero]; exact isCoef_two_cos_two
    · rw [cVec_zero_of_ne (k + 1) (by omega)]; exact isCoef_zero
  | succ j ih =>
    intro r
    rcases r with _ | k
    · rw [cVec_succ_zero]
      exact isCoef_add (isCoef_dthU (ih 0)) (isCoef_mul isCoef_four_sin_sq (ih 0))
    · by_cases hk : k = j
      · rw [hk, cVec_succ_self]
        exact isCoef_sub (ih j) isCoef_four_sin_sq
      · rw [cVec_succ_succ_of_ne j k hk]
        exact isCoef_add (isCoef_add (isCoef_dthU (ih (k + 1)))
          (isCoef_mul isCoef_four_sin_sq (ih (k + 1)))) (ih (k + 1 - 1))

end CVecBnd

theorem cVecBound : ∃ cB : ℕ → ℕ → ℝ, (∀ j r, 0 ≤ cB j r) ∧ ∀ j r (θ : ℝ), |Work.FTS.PhiStar.Psi0Est.cVec j r θ| ≤ cB j r := by
  have h : ∀ j r, ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, |cVec j r θ| ≤ M :=
    fun j r => CVecBnd.isCoef_bdd (CVecBnd.isCoef_cVec j r)
  exact ⟨fun j r => Classical.choose (h j r),
    fun j r => (Classical.choose_spec (h j r)).1,
    fun j r θ => (Classical.choose_spec (h j r)).2 θ⟩

end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.deriv_psiSol_eventuallyEq_M1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The first derivative of the model `ψ = psiSol α` is the explicit function `M1 α` in a
neighbourhood of each endpoint.

`psiSol α θ = sin(2θ)·(Kc α + wZer α θ)` and `wZer' = qfun α` (by the FTC,
`intervalIntegral.integral_hasDerivAt_right`, at every point where `qfun α` is continuous,
in particular at every `θ ∈ (-1/2,0)` and `θ ∈ (π/2, π/2+1/2)`), so the product rule gives
`deriv (psiSol α) θ = 2cos(2θ)(Kc α + wZer α θ) + sin(2θ)·qfun α θ = M1 α θ` for
`θ ≠ 0, π/2` in that interval (this is `dthU_psiSol` divided by `sin 2θ`).  At the endpoints
the same product rule applies since the coefficient of `qfun α θ` is `sin(2θ₀) = 0`, so the
junk value of `qfun` at `0` and at `π/2` is irrelevant.  Hence `deriv (psiSol α)` agrees with
`M1 α` in a full neighbourhood of each endpoint. -/
theorem deriv_psiSol_eventuallyEq_M1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hq0 : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds 0) (nhds 0))
    (hqπ : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds (Real.pi / 2)) (nhds 0)) :
    Filter.EventuallyEq (nhds 0) (deriv (Work.FTS.PhiStar.psiSol α))
      (Work.FTS.PhiStar.Psi0Est.M1 α) ∧
    Filter.EventuallyEq (nhds (Real.pi / 2)) (deriv (Work.FTS.PhiStar.psiSol α))
      (Work.FTS.PhiStar.Psi0Est.M1 α) := by
  -- `qfun` is continuous at the two endpoints, with the values `0` and `0` (which are also
  -- its junk values at `0` and `π/2`), so it is continuous wherever it is defined there.
  have hq0v : qfun α 0 = 0 := by simp [qfun]
  have hqπv : qfun α (Real.pi / 2) = 0 := by simp [qfun, Pfun, Gzero]
  have hc0 : ContinuousAt (qfun α) 0 := by rw [ContinuousAt, hq0v]; exact hq0
  have hcπ : ContinuousAt (qfun α) (Real.pi / 2) := by rw [ContinuousAt, hqπv]; exact hqπ
  -- continuity at any point where `sin` and `cos` do not vanish
  have hfun_cont : ∀ x : ℝ, Real.cos x ≠ 0 → Real.sin x ≠ 0 → ContinuousAt (qfun α) x := by
    intro x hcos hsin
    have hG : ContinuousAt (Gzero α) x := (continuous_Gzero α (le_of_lt hα)).continuousAt
    have hP : ContinuousAt (Pfun α) x := by
      have h : ContinuousAt (fun t : ℝ => Gzero α t / (2 * Real.cos t ^ 3)) x :=
        hG.div (by fun_prop) (by
          have h3 : Real.cos x ^ 3 ≠ 0 := pow_ne_zero 3 hcos
          simpa using mul_ne_zero two_ne_zero h3)
      exact h
    have hq : ContinuousAt (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2) x :=
      hP.div (by fun_prop) (pow_ne_zero 2 hsin)
    exact hq
  -- continuity of `qfun` on `[-1/2, π/2+1/2]` (where `sin`, `cos` vanish only at `0`, `π/2`)
  have hcont_off : ∀ x : ℝ, -(1 / 2) ≤ x → x ≤ Real.pi / 2 + 1 / 2 → x ≠ 0 → x ≠ Real.pi / 2 →
      ContinuousAt (qfun α) x := by
    intro x h1 h2 hx0 hxπ
    have hsin : Real.sin x ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hx (by linarith [h1, Real.pi_gt_three]))
      · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [h2, Real.pi_gt_three]))
    have hcos : Real.cos x ≠ 0 := by
      rcases lt_or_gt_of_ne hxπ with hx | hx
      · exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h1, Real.pi_gt_three], hx⟩)
      · exact ne_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt hx (by linarith [h2, Real.pi_gt_three]))
    exact hfun_cont x hcos hsin
  have hcontOn_closed : ContinuousOn (qfun α) (Set.Icc (-(1 / 2)) (Real.pi / 2 + 1 / 2)) := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact hc0.continuousWithinAt
    by_cases hxπ : x = Real.pi / 2
    · rw [hxπ]; exact hcπ.continuousWithinAt
    · exact (hcont_off x hx.1 hx.2 hx0 hxπ).continuousWithinAt
  have hcontOn_open : ContinuousOn (qfun α) (Set.Ioo (-(1 / 2)) (Real.pi / 2 + 1 / 2)) := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact hc0.continuousWithinAt
    by_cases hxπ : x = Real.pi / 2
    · rw [hxπ]; exact hcπ.continuousWithinAt
    · exact (hcont_off x (le_of_lt hx.1) (le_of_lt hx.2) hx0 hxπ).continuousWithinAt
  -- `wZer' = qfun` on the whole neighbourhood `(-1/2, π/2+1/2)`, endpoints included
  have hkey : ∀ θ : ℝ, -(1 / 2) < θ → θ < Real.pi / 2 + 1 / 2 →
      HasDerivAt (wZer α) (qfun α θ) θ := by
    intro θ h1 h2
    have hsub : Set.uIcc (0:ℝ) θ ⊆ Set.Icc (-(1 / 2)) (Real.pi / 2 + 1 / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith [Real.pi_pos]⟩
    have hint : IntervalIntegrable (qfun α) volume 0 θ :=
      (hcontOn_closed.mono hsub).intervalIntegrable
    have hcont : ContinuousAt (qfun α) θ := by
      by_cases hθ0 : θ = 0
      · rw [hθ0]; exact hc0
      by_cases hθπ : θ = Real.pi / 2
      · rw [hθπ]; exact hcπ
      · exact hcont_off θ (le_of_lt h1) (le_of_lt h2) hθ0 hθπ
    have hmeas : StronglyMeasurableAtFilter (qfun α) (nhds θ) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcontOn_open θ ⟨h1, h2⟩
    exact intervalIntegral.integral_hasDerivAt_right (f := qfun α) (a := 0) (b := θ)
      hint hmeas hcont
  -- hence the product rule gives the announced formula on the whole neighbourhood
  have hderiv : ∀ θ : ℝ, -(1 / 2) < θ → θ < Real.pi / 2 + 1 / 2 →
      deriv (psiSol α) θ = M1 α θ := by
    intro θ h1 h2
    have hw := hkey θ h1 h2
    have hd : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
      have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have h := hlin.sin
      have hval : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
      rw [hval] at h
      exact h
    have hmul := hd.mul (hw.const_add (Kc α))
    have hfun : psiSol α = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => Kc α + wZer α t) :=
      rfl
    rw [hfun, hmul.deriv]
    simp only [M1]
  constructor
  · show ∀ᶠ θ in nhds (0:ℝ), deriv (psiSol α) θ = M1 α θ
    rw [Filter.eventually_iff]
    refine mem_of_superset (isOpen_Ioo.mem_nhds
      (show (0:ℝ) ∈ Set.Ioo (-(1 / 2)) (1 / 2) from ⟨by norm_num, by norm_num⟩)) ?_
    intro θ hθ
    exact hderiv θ hθ.1 (by linarith [hθ.2, Real.pi_pos])
  · show ∀ᶠ θ in nhds (Real.pi / 2), deriv (psiSol α) θ = M1 α θ
    rw [Filter.eventually_iff]
    have hmem : (Real.pi / 2) ∈ Set.Ioo (Real.pi / 2 - 1 / 2) (Real.pi / 2 + 1 / 2) :=
      ⟨by linarith, by linarith⟩
    refine mem_of_superset (isOpen_Ioo.mem_nhds hmem) ?_
    intro θ hθ
    exact hderiv θ (by linarith [hθ.1, Real.pi_pos]) hθ.2

end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.hasDerivAt_M1_endpoints =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real Topology ContDiff
open MeasureTheory Set Filter
open Asymptotics

/-! ## The two elementary derivative lemmas the endpoint argument needs

The proof of `hasDerivAt_M1_endpoints` splits `M1 α` into the sum of

* `A θ = 2cos(2θ)(Kc α + wZer α θ)`, whose derivative at an endpoint is governed by the
  fundamental theorem of calculus applied to `wZer = ∫_0^θ qfun α`; and
* `B θ = sin(2θ)·qfun α θ`, which vanishes at the endpoint and whose difference quotient is
  `O(θ-θ₀)·o(1) = o(θ-θ₀)`.

The second ingredient is the general lemma `hasDerivAt_mul_zero_tendsto` (differentiable
factor vanishing at the point, times a factor tending to `0`). -/

/-- If `f` is differentiable at `x` with `f x = 0` and `g → 0` at `x`, then `f·g` has
derivative `0` at `x`: the factor `f · - f x = f` is `O(· - x)` while `g` is `o(1)`. -/
theorem hasDerivAt_mul_zero_tendsto {f g : ℝ → ℝ} {x c : ℝ}
    (hf : HasDerivAt f c x) (hfx : f x = 0) (hg : Tendsto g (nhds x) (nhds 0)) :
    HasDerivAt (fun y => f y * g y) 0 x := by
  have hO : (fun y => f y - f x) =O[𝓝 x] (fun y => y - x) := hf.isBigO_sub
  have hL : (fun y => g y) =o[𝓝 x] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 hg
  have hprod := hO.mul_isLittleO hL
  rw [hasDerivAt_iff_isLittleO]
  refine hprod.congr ?_ ?_
  · intro y
    simp only [hfx, zero_mul, sub_zero, smul_eq_mul, mul_zero]
  · intro y; ring

/-- `qfun α = Pfun α / sin²` is measurable. -/
lemma measurable_qfun' (α : ℝ) (hα : 0 ≤ α) : Measurable (qfun α) := by
  rw [show qfun α = fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2 from rfl]
  exact (measurable_Pfun α hα).div (by fun_prop)

/-- **The endpoint derivatives of `M1`**: at a point `θ₀` where `sin(2θ₀) = 0`,
`qfun α θ₀ = 0`, the integrand `qfun α` is continuous at `θ₀` (hypothesis `hlim`) and
integrates on `[0,θ₀]`, the model `M1 α` has derivative `0`.

This is the common core of the two conjuncts: `wZer` is differentiated at the endpoint by the
fundamental theorem of calculus, `A` by the product rule (its derivative is a multiple of
`sin(2θ₀) = 0` plus `qfun α θ₀ = 0`), and `B` by `hasDerivAt_mul_zero_tendsto`. -/
private lemma hasDerivAt_M1_at (α : ℝ) (hα : 0 < α) {θ₀ : ℝ}
    (hsin : Real.sin (2 * θ₀) = 0) (hq0v : qfun α θ₀ = 0)
    (hlim : Tendsto (qfun α) (nhds θ₀) (nhds 0))
    (hint : IntervalIntegrable (qfun α) volume 0 θ₀) :
    HasDerivAt (M1 α) 0 θ₀ := by
  have hmeas : Measurable (qfun α) := measurable_qfun' α (le_of_lt hα)
  -- the derivative of `wZer` at the endpoint, from the FTC and continuity of the integrand
  have hw : HasDerivAt (wZer α) 0 θ₀ := by
    have hcont : ContinuousAt (qfun α) θ₀ := by
      show Tendsto (qfun α) (nhds θ₀) (nhds (qfun α θ₀))
      rw [hq0v]; exact hlim
    have hsm : StronglyMeasurableAtFilter (qfun α) (nhds θ₀) volume :=
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter
    have h := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := θ₀)
      (f := qfun α) hint hsm hcont
    have h' : HasDerivAt (wZer α) (qfun α θ₀) θ₀ := by
      rw [← show wZer α = fun u => ∫ x in (0 : ℝ)..u, qfun α x from rfl] at h
      exact h
    rw [hq0v] at h'
    exact h'
  -- the derivative of `A θ = 2cos(2θ)(Kc α + wZer α θ)` is zero at the endpoint
  have hv1 : HasDerivAt (fun θ : ℝ => 2 * Real.cos (2 * θ)) (-4 * Real.sin (2 * θ₀)) θ₀ := by
    have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ₀ := by
      simpa using (hasDerivAt_id θ₀).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ₀) * 2) θ₀ := h1.cos
    have h3 := h2.const_mul (2 : ℝ)
    convert h3 using 1
    ring
  have hv2 : HasDerivAt (fun θ : ℝ => Kc α + wZer α θ) (qfun α θ₀) θ₀ := by
    rw [hq0v]; exact hw.const_add (Kc α)
  have hA : HasDerivAt (fun θ : ℝ => 2 * Real.cos (2 * θ) * (Kc α + wZer α θ)) 0 θ₀ :=
    (hv1.mul hv2).congr_deriv (by rw [hsin, hq0v]; ring)
  -- the derivative of `B θ = sin(2θ)·qfun α θ` is zero at the endpoint
  have hs : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ₀)) θ₀ := by
    have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ₀ := by
      simpa using (hasDerivAt_id θ₀).const_mul (2 : ℝ)
    have h2 := h1.sin
    convert h2 using 1
    ring
  have hB : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * qfun α θ) 0 θ₀ :=
    hasDerivAt_mul_zero_tendsto hs hsin hlim
  have hM : (fun θ : ℝ => 2 * Real.cos (2 * θ) * (Kc α + wZer α θ)
      + Real.sin (2 * θ) * qfun α θ) = M1 α := rfl
  rw [← hM]
  refine (hA.add hB).congr_deriv ?_
  norm_num

/-- The model `M1 α` for `ψ'` is flat at the two endpoints: `HasDerivAt (M1 α) 0 θ` for
`θ = 0` and `θ = π/2`.

Write `M1 α θ = A θ + B θ` with `A θ = 2cos(2θ)(Kc α + wZer α θ)` and
`B θ = sin(2θ)·qfun α θ`.

The product rule together with `HasDerivAt wZer (qfun α θ) θ` (FTC plus continuity at the
endpoint, from the hypothesis) gives
`A' θ = 2(-2sin(2θ)(Kc + wZer θ) + cos(2θ)·qfun α θ)`, which is `0` at `θ = 0`
(`sin 0 = 0` and `qfun α 0 = Pfun α 0/0 = 0`) and at `θ = π/2` (`sin π = 0`, `cos π = -1`,
`qfun α (π/2) = Pfun α (π/2)/1 = Gzero α (π/2)/(2cos³(π/2)) = 0`).

The function `B` vanishes at both endpoints since `sin(2θ₀) = 0`, and
`(B θ - B θ₀)/(θ - θ₀) = (sin(2θ)/(θ-θ₀))·qfun α θ → 2cos(2θ₀)·0 = 0` by the hypothesis
`qfun α → 0` at the endpoint and `deriv (sin ∘ (2·)) θ₀ = 2cos(2θ₀)`, so
`HasDerivAt B 0 θ₀`.  Hence `HasDerivAt (M1 α) (0+0) θ₀`. -/
theorem hasDerivAt_M1_endpoints (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hq0 : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds 0) (nhds 0))
    (hqπ : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds (Real.pi / 2)) (nhds 0)) :
    HasDerivAt (Work.FTS.PhiStar.Psi0Est.M1 α) 0 0 ∧
      HasDerivAt (Work.FTS.PhiStar.Psi0Est.M1 α) 0 (Real.pi / 2) := by
  constructor
  · refine hasDerivAt_M1_at α hα (by simp) (by simp [qfun]) hq0 ?_
    refine ⟨?_, ?_⟩ <;> (rw [Set.Ioc_self]; exact integrableOn_empty)
  · refine hasDerivAt_M1_at α hα ?_ ?_ hqπ ?_
    · rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    · simp [qfun, Pfun, Gzero]
    · have h := integrableOn_Pfun_div α hα hα1
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at h
      exact h.mono_set Set.Ioc_subset_Icc_self

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.qfun_tendsto_endpoints_alt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

private lemma cos_ge_half {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : (1 / 2 : ℝ) ≤ Real.cos θ := by
  have hθle : θ ≤ 1 / 2 := (abs_le.mp hθ).2
  have h1 : Real.cos (Real.pi / 3) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (x := |θ|) (y := Real.pi / 3) (abs_nonneg θ)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three])
  rw [Real.cos_pi_div_three] at h1
  have h4 : Real.cos |θ| = Real.cos θ := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.cos_neg]
  rwa [h4] at h1

private lemma abs_sin_ge {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : |θ| / 2 ≤ |Real.sin θ| := by
  have hθle : θ ≤ 1 / 2 := (abs_le.mp hθ).2
  have hθge : -(1 / 2) ≤ θ := (abs_le.mp hθ).1
  have hπ : (2 / Real.pi) * |θ| ≤ Real.sin |θ| :=
    Real.mul_le_sin (abs_nonneg θ) (by linarith [hθ, Real.pi_gt_three])
  have h2 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
    linarith [Real.pi_lt_four]
  have h3 : |θ| / 2 ≤ Real.sin |θ| := by
    calc |θ| / 2 = (1 / 2) * |θ| := by ring
      _ ≤ (2 / Real.pi) * |θ| := mul_le_mul_of_nonneg_right h2 (abs_nonneg θ)
      _ ≤ Real.sin |θ| := hπ
  have h4 : Real.sin |θ| = |Real.sin θ| := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h
        (by linarith [hθle, Real.pi_gt_three]))]
    · rw [abs_of_neg h, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h
        (by linarith [hθge, Real.pi_gt_three]))]
  rwa [h4] at h3

private lemma sin_ge_half {θ : ℝ} (hθ : |θ - Real.pi / 2| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ Real.sin θ := by
  have h1 : Real.sin θ = Real.cos (θ - Real.pi / 2) := by
    have h := Real.sin_add_pi_div_two (θ - Real.pi / 2)
    rwa [show (θ - Real.pi / 2) + Real.pi / 2 = θ from by ring] at h
  rw [h1]
  rcases le_or_gt 0 (θ - Real.pi / 2) with h | h
  · exact cos_ge_half hθ
  · have h' : |-(θ - Real.pi / 2)| ≤ 1 / 2 := by rw [abs_neg]; exact hθ
    rw [← Real.cos_neg (θ - Real.pi / 2)]
    exact cos_ge_half h'

private lemma abs_cos_ge {θ : ℝ} (hθ : |θ - Real.pi / 2| ≤ 1 / 2) :
    |θ - Real.pi / 2| / 2 ≤ |Real.cos θ| := by
  have h1 : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
    have h := Real.cos_pi_div_two_sub (Real.pi / 2 - θ)
    rwa [sub_sub_cancel] at h
  have h2 : Real.sin (Real.pi / 2 - θ) = -Real.sin (θ - Real.pi / 2) := by
    rw [show Real.pi / 2 - θ = -(θ - Real.pi / 2) from by ring, Real.sin_neg]
  rw [h1, h2, abs_neg]
  exact abs_sin_ge hθ

theorem qfun_tendsto_zero_alt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (qfun α) (nhds 0) (nhds 0) := by
  obtain ⟨C, hCpos, hCbd⟩ := Gzero_rpow_zero α hα hα1
  have hα3 : 0 < α / 3 := by linarith
  have hbound : ∀ θ : ℝ, |θ| ≤ 1 / 2 → |qfun α θ| ≤ (16 * C) * |θ| ^ (α / 3) := by
    intro θ hθ
    rcases eq_or_ne θ 0 with rfl | hne
    · have hz : qfun α 0 = 0 := by simp [qfun, Pfun]
      simp only [hz, abs_zero, Real.zero_rpow (ne_of_gt hα3), mul_zero, le_refl]
    · have hcos : (1 / 2 : ℝ) ≤ Real.cos θ := cos_ge_half hθ
      have hcos3 : (1 / 8 : ℝ) ≤ Real.cos θ ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hcos 3
        norm_num at h
        exact h
      have hsin2 : θ ^ 2 / 4 ≤ Real.sin θ ^ 2 := by
        have h' : (|θ| / 2) ^ 2 ≤ |Real.sin θ| ^ 2 :=
          pow_le_pow_left₀ (by positivity) (abs_sin_ge hθ) 2
        have h1 : (|θ| / 2) ^ 2 = θ ^ 2 / 4 := by rw [div_pow, sq_abs θ]; norm_num
        have h2 : |Real.sin θ| ^ 2 = Real.sin θ ^ 2 := sq_abs _
        rwa [h1, h2] at h'
      have hden : θ ^ 2 / 16 ≤ 2 * Real.cos θ ^ 3 * Real.sin θ ^ 2 := by
        have hA : 2 * Real.cos θ ^ 3 * (θ ^ 2 / 4) ≤ 2 * Real.cos θ ^ 3 * Real.sin θ ^ 2 :=
          mul_le_mul_of_nonneg_left hsin2 (by positivity)
        have hB : 2 * (1 / 8) * (θ ^ 2 / 4) ≤ 2 * Real.cos θ ^ 3 * (θ ^ 2 / 4) := by
          have h := mul_le_mul_of_nonneg_right
            (by linarith : (2 : ℝ) * (1 / 8) ≤ 2 * Real.cos θ ^ 3)
            (by positivity : (0 : ℝ) ≤ θ ^ 2 / 4)
          linarith [h]
        calc θ ^ 2 / 16 = 2 * (1 / 8) * (θ ^ 2 / 4) := by ring
          _ ≤ 2 * Real.cos θ ^ 3 * (θ ^ 2 / 4) := hB
          _ ≤ 2 * Real.cos θ ^ 3 * Real.sin θ ^ 2 := hA
      have hG : |Gzero α θ| ≤ C * |θ| ^ (2 + α / 3) := hCbd θ hθ
      have hq : |qfun α θ| = |Gzero α θ| / (2 * Real.cos θ ^ 3 * Real.sin θ ^ 2) := by
        rw [qfun_apply, abs_div, abs_of_nonneg (sq_nonneg (Real.sin θ)), Pfun, abs_div,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.cos θ ^ 3), div_div]
      rw [hq]
      have hstep1 : |Gzero α θ| / (2 * Real.cos θ ^ 3 * Real.sin θ ^ 2)
          ≤ (C * |θ| ^ (2 + α / 3)) / (θ ^ 2 / 16) :=
        div_le_div₀ (by positivity) hG (by positivity) hden
      refine hstep1.trans ?_
      rw [show (2 + α / 3 : ℝ) = (2 : ℝ) + α / 3 from rfl, Real.rpow_add (abs_pos.mpr hne)]
      have hsq : |θ| ^ (2 : ℝ) = θ ^ 2 := by norm_num [Real.rpow_natCast, sq_abs]
      rw [hsq, div_le_iff₀ (by positivity : (0 : ℝ) < θ ^ 2 / 16)]
      ring_nf
      exact le_refl _
  have hlim : Filter.Tendsto (fun θ : ℝ => (16 * C) * |θ| ^ (α / 3)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun θ : ℝ => |θ| ^ (α / 3)) 0 :=
      continuous_abs.continuousAt.rpow_const (Or.inr (le_of_lt hα3))
    have hval : (fun θ : ℝ => |θ| ^ (α / 3)) 0 = 0 := by
      simp only [abs_zero]
      exact Real.zero_rpow (ne_of_gt hα3)
    have h2 : ContinuousAt (fun θ : ℝ => (16 * C) * |θ| ^ (α / 3)) 0 :=
      hcont.const_mul (16 * C)
    have h3 : (fun θ : ℝ => (16 * C) * |θ| ^ (α / 3)) 0 = 0 := by
      simp only [abs_zero, Real.zero_rpow (ne_of_gt hα3), mul_zero]
    simpa only [ContinuousAt, h3] using h2
  have hmain : Filter.Tendsto (fun θ : ℝ => |qfun α θ|) (nhds 0) (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) ?_ hlim
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with θ hθ
    have hθ' : |θ| ≤ 1 / 2 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hθ
      exact le_of_lt hθ
    exact hbound θ hθ'
  have hgoal : Filter.Tendsto (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) (nhds 0) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, qfun_apply] using hmain
  rw [show qfun α = (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) from rfl]
  exact hgoal

/-- The two-sided power bound for `qfun` near `π/2`. -/
theorem qfun_tendsto_pi_div_two_alt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (qfun α) (nhds (Real.pi / 2)) (nhds 0) := by
  obtain ⟨K, hKpos, hKbd⟩ := Gzero_rpow_pi_div_two α hα hα1
  have h2α3 : 0 < 2 * (α / 3) := by linarith
  have hbound : ∀ θ : ℝ, |θ - Real.pi / 2| ≤ 1 / 2 →
      |qfun α θ| ≤ (16 * K) * |θ - Real.pi / 2| ^ (2 * (α / 3)) := by
    intro θ hθ
    rcases eq_or_ne (θ - Real.pi / 2) 0 with hzero | hne
    · have hθpi : θ = Real.pi / 2 := by linarith [sub_eq_zero.mp hzero]
      subst hθpi
      have hq : qfun α (Real.pi / 2) = 0 := by
        rw [qfun_apply, Pfun, Gzero_pi_div_two, Real.cos_pi_div_two]
        norm_num
      simp only [hq, abs_zero, sub_self, abs_zero, Real.zero_rpow (ne_of_gt h2α3), mul_zero,
        le_refl]
    · have hδpos : 0 < |θ - Real.pi / 2| := abs_pos.mpr hne
      have hcos : |θ - Real.pi / 2| / 2 ≤ |Real.cos θ| := abs_cos_ge hθ
      have hcos3 : (|θ - Real.pi / 2| / 2) ^ 3 ≤ |Real.cos θ| ^ 3 :=
        pow_le_pow_left₀ (by positivity) hcos 3
      have hsin2 : (1 / 4 : ℝ) ≤ Real.sin θ ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (sin_ge_half hθ) 2
        norm_num at h
        exact h
      have hden : |θ - Real.pi / 2| ^ 3 / 16 ≤ 2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2 := by
        have hA : 2 * |Real.cos θ| ^ 3 * (1 / 4) ≤
            2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2 :=
          mul_le_mul_of_nonneg_left hsin2 (by positivity)
        have hB : 2 * (|θ - Real.pi / 2| / 2) ^ 3 * (1 / 4) ≤
            2 * |Real.cos θ| ^ 3 * (1 / 4) := by
          have h := mul_le_mul_of_nonneg_right
            (by linarith : 2 * (|θ - Real.pi / 2| / 2) ^ 3 ≤ 2 * |Real.cos θ| ^ 3)
            (by norm_num : (0 : ℝ) ≤ 1 / 4)
          linarith [h]
        calc |θ - Real.pi / 2| ^ 3 / 16 = 2 * (|θ - Real.pi / 2| / 2) ^ 3 * (1 / 4) := by ring
          _ ≤ 2 * |Real.cos θ| ^ 3 * (1 / 4) := hB
          _ ≤ 2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2 := hA
      have hG : |Gzero α θ| ≤ K * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := hKbd θ hθ
      have hq : |qfun α θ| = |Gzero α θ| / (2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2) := by
        rw [qfun_apply, abs_div, abs_of_nonneg (sq_nonneg (Real.sin θ)), Pfun, abs_div,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow, div_div]
      rw [hq]
      have hstep1 : |Gzero α θ| / (2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2)
          ≤ (K * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3))) / (|θ - Real.pi / 2| ^ 3 / 16) :=
        div_le_div₀ (by positivity) hG (by positivity) hden
      refine hstep1.trans ?_
      rw [show (3 + 2 * (α / 3) : ℝ) = (3 : ℝ) + 2 * (α / 3) from rfl,
        Real.rpow_add (abs_pos.mpr hne)]
      have hc3 : |θ - Real.pi / 2| ^ (3 : ℝ) = |θ - Real.pi / 2| ^ 3 := by
        norm_num [Real.rpow_natCast]
      rw [hc3, div_le_iff₀ (by positivity : (0 : ℝ) < |θ - Real.pi / 2| ^ 3 / 16)]
      ring_nf
      exact le_refl _
  have hlim : Filter.Tendsto
      (fun θ : ℝ => (16 * K) * |θ - Real.pi / 2| ^ (2 * (α / 3))) (nhds (Real.pi / 2))
      (nhds 0) := by
    have hcont : ContinuousAt (fun δ : ℝ => |δ| ^ (2 * (α / 3))) 0 :=
      continuous_abs.continuousAt.rpow_const (Or.inr (le_of_lt h2α3))
    have h2 : ContinuousAt (fun δ : ℝ => (16 * K) * |δ| ^ (2 * (α / 3))) 0 :=
      hcont.const_mul (16 * K)
    have h2' : Filter.Tendsto (fun δ : ℝ => (16 * K) * |δ| ^ (2 * (α / 3))) (nhds 0)
        (nhds 0) := by
      have h3 : (fun δ : ℝ => (16 * K) * |δ| ^ (2 * (α / 3))) 0 = 0 := by
        simp only [abs_zero, Real.zero_rpow (ne_of_gt h2α3), mul_zero]
      simpa only [ContinuousAt, h3] using h2
    have h1 : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2) (nhds (Real.pi / 2)) (nhds 0) := by
      have h : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2) (nhds (Real.pi / 2))
          (nhds (Real.pi / 2 - Real.pi / 2)) :=
        tendsto_id.sub tendsto_const_nhds
      simpa using h
    have h3 := h2'.comp h1
    simpa only [Function.comp_def] using h3
  have hmain : Filter.Tendsto (fun θ : ℝ => |qfun α θ|) (nhds (Real.pi / 2)) (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) ?_ hlim
    filter_upwards [Metric.ball_mem_nhds (Real.pi / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
      with θ hθ
    have hθ' : |θ - Real.pi / 2| ≤ 1 / 2 := by
      rw [Metric.mem_ball, Real.dist_eq] at hθ
      exact le_of_lt hθ
    exact hbound θ hθ'
  have hgoal : Filter.Tendsto (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) (nhds (Real.pi / 2))
      (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, qfun_apply] using hmain
  rw [show qfun α = (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) from rfl]
  exact hgoal


/-- **Both endpoint limits at once**, in the shape of `qfun_tendsto_endpoints`. -/
theorem qfun_tendsto_endpoints_alt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (qfun α) (nhds 0) (nhds 0) ∧
      Filter.Tendsto (qfun α) (nhds (Real.pi / 2)) (nhds 0) :=
  ⟨qfun_tendsto_zero_alt α hα hα1, qfun_tendsto_pi_div_two_alt α hα hα1⟩

end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.pzIter_DthIter_leibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.PhiStar

set_option maxHeartbeats 1000000

/-! ## The Leibniz rule for `∂_z^k D_θ^j f`

Write `L = D_θ = sin(2θ) ∂_θ`.  Since `L f = (sin 2·) · ∂_θ f` and `L` is a derivation, the
`j`-th iterate of `L` applied to `f` satisfies the binomial expansion

`L^j f = ∑_{a<j} C(j-1,a) · (L^a (sin 2·)) · (L^{j-1-a} (∂_θ f))`,

because `L^j f = L^{j-1}(L f) = L^{j-1}((sin 2·)·∂_θ f)`.  The statement below is the `k`-fold
`z`-derivative of this identity; since `L^a (sin 2·)` does not depend on `z`, the `z`-derivatives
pass through the coefficients, and all the mixed `∂_z^c`-terms with `c ≥ 1` on the `sin 2·`-factor
vanish. -/

/-- `θ ↦ sin(2θ)` (viewed as a function of `(z,θ)`) is smooth on the open quadrant. -/
private theorem smoothOpen_Sfun : Work.FTS.EllipticEst.SmoothOpen Work.FTS.H2.Sfun := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin

/-- `D_θ` sends functions which do not depend on `z` to functions which do not depend on `z`. -/
private theorem Dth_zindep {u : ℝ → ℝ → ℝ} (h : ∀ z θ, u z θ = u 0 θ) (z θ : ℝ) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth u 0 θ := by
  show Real.sin (2 * θ) * Work.Spaces.pth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u 0 θ
  congr 1
  show deriv (fun θ' => u z θ') θ = deriv (fun θ' => u 0 θ') θ
  congr 1
  funext θ'
  exact h z θ'

/-- Every `D_θ`-iterate of `sin 2·` is independent of `z`. -/
private theorem DthIter_Sfun_zindep (a : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ
      = Work.Spaces.DthIter a Work.FTS.H2.Sfun 0 θ := by
  induction a generalizing z θ with
  | zero => rfl
  | succ a ih => exact Dth_zindep (fun z' θ' => ih z' θ') z θ

/-- Any positive `z`-derivative of `D_θ^a (sin 2·)` vanishes (the function is a function of
`θ` alone). -/
private theorem pzIter_DthIter_Sfun_eq_zero (a c : ℕ) (hc : 1 ≤ c) (z θ : ℝ) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  have hconst : (fun z' => Work.Spaces.DthIter a Work.FTS.H2.Sfun z' θ)
      = fun _ => Work.Spaces.DthIter a Work.FTS.H2.Sfun 0 θ := by
    funext z'
    exact DthIter_Sfun_zindep a z' θ
  rw [hconst, iteratedDeriv_const]
  rcases c with _ | c
  · omega
  · simp

/-- `D_θ^j f = D_θ^{j-1}((sin 2·)·∂_θ f)`: the definitional identity `D_θ f = (sin 2·)·∂_θ f`,
iterated. -/
private theorem DthIter_eq_DthIter_pred_mul (j : ℕ) (hj : 1 ≤ j) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j f
      = Work.Spaces.DthIter (j - 1)
          (fun z θ => Work.FTS.H2.Sfun z θ * Work.Spaces.pth f z θ) := by
  rw [← Nat.sub_add_cancel hj, ← Work.Spaces.DthIter_add_right (j - 1) 1 f]
  rfl

theorem pzIter_DthIter_leibniz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {j k : ℕ} (hj : 1 ≤ j) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ =
      ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ) := by
  have hpth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f) :=
    Work.FTS.EllipticEst.SmoothOpen.pth hf
  -- Write `D_θ^j f` as the `(j-1)`-st iterate of `D_θ` applied to the product `(sin 2·)·∂_θ f`.
  rw [DthIter_eq_DthIter_pred_mul j hj f,
    -- and use the Leibniz rule for `∂_z^k D_θ^{j-1}` on that product.
    Work.FTS.NonlinRows.sqo_pz_DthIter_mul_eq (k := k) (j := j - 1) (f := Work.FTS.H2.Sfun)
      (g := Work.Spaces.pth f) smoothOpen_Sfun hpth z hz θ hθ,
    Nat.sub_add_cancel hj]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Only the `c = 0` term of the inner sum survives: `D_θ^a (sin 2·)` is constant in `z`.
  have hsingle : (∑ c ∈ Finset.range (k + 1), ((j - 1).choose a : ℝ) * (k.choose c : ℝ) *
        (Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ *
          Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
            z θ))
      = ((j - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ) := by
    refine (Finset.sum_eq_single (s := Finset.range (k + 1))
      (f := fun c => ((j - 1).choose a : ℝ) * (k.choose c : ℝ) *
        (Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ *
          Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
            z θ)) 0 ?_ ?_).trans ?_
    · intro c _ hc0
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
      rw [pzIter_DthIter_Sfun_eq_zero a c hc1 z θ]
      ring
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
    · simp only [Nat.choose_zero_right, Nat.cast_one, Work.Spaces.pzIter_zero, Nat.sub_zero]
      ring
  exact hsingle

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.absPairMulWLeHkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux

set_option autoImplicit false

/-! ## The elementary AM–GM with the `sin(2θ)^(gam α - 1) ≤ 1` slack -/


/-! ## The two adjacent mixed slots inside one `HkIntegrand` -/


/-! ## The target -/


end Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-!
# The level-four leaf slot bound

This is the level-four counterpart of `leaf_slot_le6`.  For every slot `(a,b)` with
`a + b ≤ 4` and every leaf weight `ρ` of `IP4` (`IsLeafW α a ρ`), the single weighted `L²`
slot integral `∫_z ∫_θ ρ · (D_z^b D_θ^a f)²` is bounded by the full `ℋ⁴`-energy `HkSq α 4 f`.

The proof is the same as the one at level six, only with `intSlotLeHkSq4` (the level-four
instance of the "general `θ`-weight" slot estimate, built here from
`Work.Spaces.sq_le_HkIntegrand_z/mixed` and `Work.Spaces.L2Sq_*_le_HkSq`) in place of the
level-six `intSlotLeHkSq`.
-/







end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The leaf weights of `IP6` are dominated by the slot weight of `HkIntegrand α 6`.**

For every slot `(a,b)` of the level-six pairing (`a + b ≤ 6`) and every leaf weight
`IsLeafW α a ρ` (i.e. `ρ = w²σ^{-η}`, `ρ = w²`, or `ρ = w²σ^{-γ}` with `a ≥ 1`), the
single weighted `L²` slot integral `∫_z ∫_θ ρ·(D_z^bD_θ^a f)²` is bounded by `HkSq α 6 f`.

The proof is a case distinction on the leaf weight, reducing each case to the corresponding
half of `intSlotLeHkSq` (which controls `∫∫ w²·θw·(D_z^bD_θ^a f)²` whenever `θw` is
pointwise dominated by `σ^{-η}` in the `D_z`-only slots resp. by `σ^{-γ}` in the slots with
an angular derivative).  The three elementary pointwise comparisons are

* `w²·σ^{-η} = (w z)²·σ^{-η}` (the `η`-leaf, a `D_z`-slot weight at `a = 0`);
* `w²·1 ≤ w²·σ^{-η}` when `a = 0` and `1 ≤ σ^{-γ}` when `a ≥ 1` (the σ-free leaf);
* `w²·σ^{-η} ≤ w²·σ^{-γ}` (`η ≤ γ`, `rpow_eta_le_gam`) and `w²·σ^{-γ}` exactly
  (the `γ`-leaf, which by `IsLeafW` only occurs at slots with `a ≥ 1`). -/
theorem leaf_slot_le6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f := by
  intro a b ρ hab hleaf
  have h6 := intSlotLeHkSq α hmem
  have hsin_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have heta_nn : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · -- the `η`-leaf weight `w²σ^{-η}`
    subst hρ
    by_cases ha : 1 ≤ a
    · -- a slot with an angular derivative: compare `σ^{-η} ≤ σ^{-γ}`
      have h := h6.2 b a ha hab (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
        (fun θ hθ => Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafEta] using h
    · -- a `D_z`-only slot: `w²σ^{-η}` is exactly its slot weight
      have ha0 : a = 0 := by omega
      subst a
      have hb : b ≤ 6 := by omega
      have h := h6.1 b hb (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
        (fun θ hθ => le_rfl)
      simpa only [Work.FTS.TransportS.leafEta, Work.Spaces.mixed_zero_right] using h
  · -- the σ-free leaf weight `w²`
    subst hρ
    by_cases ha : 1 ≤ a
    · -- a slot with an angular derivative: `1 ≤ σ^{-γ}`
      have h := h6.2 b a ha hab (fun _ : ℝ => 1) (fun θ hθ => zero_le_one)
        (fun θ hθ => Work.FTS.TransportS.one_le_rpow_neg hgam_nn ⟨hθ.1, hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafOne, mul_one] using h
    · -- a `D_z`-only slot: `1 ≤ σ^{-η}`
      have ha0 : a = 0 := by omega
      subst a
      have hb : b ≤ 6 := by omega
      have h := h6.1 b hb (fun _ : ℝ => 1) (fun θ hθ => zero_le_one)
        (fun θ hθ => Work.FTS.TransportS.one_le_rpow_neg heta_nn ⟨hθ.1, hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafOne, mul_one, Work.Spaces.mixed_zero_right] using h
  · -- the `γ`-leaf weight `w²σ^{-γ}`, which occurs only at slots with `a ≥ 1`
    subst hρ
    have h := h6.2 b a ha1 hab (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
      (fun θ hθ => le_rfl)
    simpa only [Work.FTS.TransportS.leafGam] using h

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowCoefExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The Fubini bridge for `slotPairing`

`slotPairing ρ a b u v` is defined as the iterated set integral
`∫ z in Iz, ∫ θ in Iθ, ρ z θ * D_z^bD_θ^a u z θ * D_z^bD_θ^a v z θ`.  The right-hand side
of the row expansion uses the integral against the *product* of the two restricted measures
`(volume.restrict Iz).prod (volume.restrict Iθ)`, so the two descriptions must be identified.
This is `MeasureTheory.integral_prod`. -/

/-- `slotPairing` is also the integral against the product measure, for an integrable
integrand. -/
private theorem slotPairing_eq_prod_prv (ρ u v : ℝ → ℝ → ℝ) (a b : ℕ)
    (h : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a u p.1 p.2
        * Work.Spaces.mixed b a v p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.TransportS.slotPairing ρ a b u v
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
          * Work.Spaces.mixed b a v p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.FTS.TransportS.slotPairing]
  exact (MeasureTheory.integral_prod
    (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
      * Work.Spaces.mixed b a v p.1 p.2) h).symm

/-! ## Almost everywhere statements on the closed quadrant -/




/-! ## The pointwise Leibniz expansion of the slot -/


/-! ## The row expansion -/


end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## F. Angular integral, radial integral, and the assembly -/

/-- Integrability and the bound of the angular majorant. -/
theorem radAngInt_bound : ∃ M : ℝ, 0 < M ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    MeasureTheory.IntegrableOn (radAngInt α) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, radAngInt α θ) ≤ M := by
  refine ⟨10500, by norm_num, fun α hα hα1 => ?_⟩
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_of_mem_Iθ hθ
  -- the `η`-term
  have hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000 := by
    obtain ⟨h1, h2⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
    refine ⟨h1, ?_⟩
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by rw [Work.Spaces.eta]; norm_num
    rwa [heq] at h2
  -- the `γ`-term
  have hBmeas : AEStronglyMeasurable
      (fun θ : ℝ => α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  obtain ⟨hSint, hSbd⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1)
    (by linarith) (by linarith)
  have hSbd' : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hSbd
  have hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 200 := by
    have hMint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))) Work.Spaces.Iθ :=
      (hSint.const_mul ((2 : ℝ) ^ (-(2 * α / 3)))).const_mul (α ^ 2)
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
      intro θ hθ
      have h := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
      have h4 : 0 ≤ α ^ 2 := sq_nonneg α
      calc α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = α ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ ≤ α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3))
              * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
            mul_le_mul_of_nonneg_left h h4
    have hInt : MeasureTheory.IntegrableOn
        (fun θ : ℝ => α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hMint.mono' hBmeas (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Real.rpow_nonneg (hsin2 θ hθ) _))]
        exact hpt θ hθ)
    refine ⟨hInt, ?_⟩
    have hmono := MeasureTheory.integral_mono_ae hInt hMint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have hpoweq : (∫ θ in Work.Spaces.Iθ, (2 : ℝ) ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
        = (2 : ℝ) ^ (-(2 * α / 3)) * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
      MeasureTheory.integral_const_mul _ _
    rw [hpoweq]
    have hbind : α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α))) ≤ 200 := by
      have h3 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
          (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -(2 * α / 3) ≤ 0)
        simpa using h
      have h5 : (2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α)) ≤ 3000 / (17 * α) := by
        have h6 : 0 ≤ 3000 / (17 * α) := by positivity
        nlinarith [h3, h6]
      have h7 : α ^ 2 * (3000 / (17 * α)) ≤ 3000 / 17 := by
        have he : α ^ 2 * (3000 / (17 * α)) = 3000 * α / 17 := by field_simp
        rw [he]
        nlinarith [hα1, hα]
      have h8 : 0 ≤ α ^ 2 := sq_nonneg α
      calc α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α)))
          ≤ α ^ 2 * (3000 / (17 * α)) := mul_le_mul_of_nonneg_left h5 h8
        _ ≤ 3000 / 17 := h7
        _ ≤ 200 := by norm_num
    have h4 : (2 : ℝ) ^ (-(2 * α / 3))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
        ≤ (2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hSbd' (Real.rpow_nonneg (by norm_num) _)
    exact (mul_le_mul_of_nonneg_left h4 (sq_nonneg α)).trans hbind
  constructor
  · exact hA.1.add hB.1
  · have heq : (∫ θ in Work.Spaces.Iθ, radAngInt α θ)
        = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∫ θ in Work.Spaces.Iθ, α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
      MeasureTheory.integral_add hA.1 hB.1
    rw [heq]
    linarith [hA.2, hB.2]

/-- Measurability of the `Zop`-iterates of the radial profile. -/
lemma measurable_Zop_iter (j : ℕ) : Measurable (Work.Spaces.Zop^[j] bcoefRad) := by
  induction j with
  | zero =>
      rw [show Work.Spaces.Zop^[0] bcoefRad = bcoefRad from rfl]
      rw [show bcoefRad = fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 from rfl]
      fun_prop
  | succ j ih =>
      have h : Work.Spaces.Zop^[j + 1] bcoefRad
          = fun z : ℝ => z * deriv (Work.Spaces.Zop^[j] bcoefRad) z := by
        funext z
        rw [Function.iterate_succ_apply']
        rfl
      rw [h]
      exact measurable_id.mul (measurable_deriv _)

lemma measurable_w : Measurable Work.Spaces.w := by
  unfold Work.Spaces.w
  fun_prop

lemma measurable_radSnorm : Measurable radSnorm := by
  unfold radSnorm
  refine Finset.measurable_sum _ fun j _ => ?_
  have h3 : Measurable (fun a : ℝ =>
      (Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a) :=
    (measurable_Zop_iter j).mul measurable_w
  have hgoal : (fun a : ℝ => ((Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a) ^ 2)
      = fun a : ℝ => ((Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a)
          * ((Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a) := by
    funext a; rw [pow_two]
  rw [hgoal]
  exact h3.mul h3

/-- The integral of `radSnorm` is bounded, given the pointwise radial bound. -/
theorem radSnorm_int_le {K : ℝ} (hK : 0 ≤ K)
    (hrb : ∀ j ≤ 3, ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z| ≤ K / (1 + z)) :
    MeasureTheory.IntegrableOn radSnorm Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, radSnorm z) ≤ 8 * K ^ 2 := by
  have hpt : ∀ z ∈ Work.Spaces.Iz, radSnorm z ≤ 4 * K ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z hz
    have h1z : (0 : ℝ) < 1 + z := by
      have hz0 : 0 ≤ z := hz
      linarith
    have h1 : ∀ j ∈ Finset.range 4,
        ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ K ^ 2 * (1 / (1 + z) ^ 2) := by
      intro j hj
      have hj3 : j ≤ 3 := by have := Finset.mem_range.mp hj; omega
      have h := hrb j hj3 z hz
      have h2 : ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ (K / (1 + z)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K / (1 + z))]
        exact h
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, one_div]
      ring
    have hsum := Finset.sum_le_sum h1
    rw [radSnorm_apply]
    refine hsum.trans ?_
    have hsum' : (∑ _j ∈ Finset.range 4, K ^ 2 * (1 / (1 + z) ^ 2))
        = 4 * K ^ 2 * (1 / (1 + z) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum']
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => 4 * K ^ 2 * (1 / (1 + z) ^ 2))
      Work.Spaces.Iz := Work.Elliptic.WtoH_IntZ.1.const_mul (4 * K ^ 2)
  have hSint : MeasureTheory.IntegrableOn radSnorm Work.Spaces.Iz := by
    refine hdom.mono' measurable_radSnorm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (radSnorm_nonneg z)]
    exact hpt z hz
  refine ⟨hSint, ?_⟩
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => radSnorm_nonneg z) hdom
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have h2 : (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 2 := Work.Elliptic.WtoH_IntZ.2
  have h3 : (0 : ℝ) ≤ 4 * K ^ 2 := by positivity
  calc 4 * K ^ 2 * (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 4 * K ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 8 * K ^ 2 := by ring

/-- The radial fact (proved in `bcoefRadBound`). -/
theorem rad_aux : ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ), j ≤ 3 → ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z| ≤ K / (1 + z) :=
  bcoefRad_zop_bound

/-- The angular fact (proved as `radAngInt_bound` below). -/
theorem ang_aux : ∃ M : ℝ, 0 < M ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (radAngInt α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, radAngInt α θ) ≤ M := radAngInt_bound

theorem bcoef_gamCoef_le_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => gamCoefAng α θ * bcoefRad z) ∧
    Work.Spaces.HkMem α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) ∧
    Work.Spaces.HkSq α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) ≤ C := by
  obtain ⟨K, hKpos, hrb⟩ := rad_aux
  obtain ⟨M, hMpos, hang⟩ := ang_aux
  have hK : 0 ≤ K := le_of_lt hKpos
  have hC0nn : (0 : ℝ) ≤ radC0 := radC0_nonneg
  refine ⟨128 * K ^ 2 * radC0 * M + 1,
    by have h : (0 : ℝ) ≤ 128 * K ^ 2 * radC0 * M :=
         mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hC0nn)
           (le_of_lt hMpos)
       linarith, fun α hα hα1 => ?_⟩
  obtain ⟨hangint, hangbd⟩ := hang α hα hα1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => gamCoefAng α θ * bcoefRad z) := smoothOpen_prod α
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, radAngInt α θ :=
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => radAngInt_nonneg (sin_two_nonneg_of_mem_Iθ hθ)))
  have hmajint : ∀ z : ℝ, MeasureTheory.Integrable
      (fun θ : ℝ => radSnorm z * (16 * radC0 * radAngInt α θ))
      (volume.restrict Work.Spaces.Iθ) := by
    intro z
    exact (hangint.const_mul (16 * radC0)).const_mul (radSnorm z)
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) z θ)
        ≤ radSnorm z * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ)) := by
    intro z hz
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
          ≤ radSnorm z * (16 * radC0 * radAngInt α θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hkIntegrand_le hα hα1 z hz θ hθ)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 3 _ z θ)
      (hmajint z) hae
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  refine ⟨hsm, ?_, ?_⟩
  · refine Work.FTS.LocData.HkMem_of_majorant α 3
      (M := fun z θ => radSnorm z * (16 * radC0 * radAngInt α θ)) ?_ ?_ ?_ ?_
    · simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn_HkIntegrand α 3
    · intro z hz
      exact hmajint z
    · have hS := (radSnorm_int_le hK hrb).1
      have he : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            radSnorm z * (16 * radC0 * radAngInt α θ))
          = fun z : ℝ => radSnorm z * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ)) := by
        funext z
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [he]
      exact hS.mul_const _
    · intro z hz θ hθ
      exact hkIntegrand_le hα hα1 z hz θ hθ
  · rw [Work.Spaces.HkSq]
    have hSbd := (radSnorm_int_le hK hrb).2
    have houter := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 3 _ z θ)
      ((radSnorm_int_le hK hrb).1.mul_const _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
    rw [MeasureTheory.integral_mul_const] at houter
    refine houter.trans ?_
    have h1 : (∫ z in Work.Spaces.Iz, radSnorm z) * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ))
        ≤ 8 * K ^ 2 * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ)) :=
      mul_le_mul_of_nonneg_right hSbd (mul_nonneg (mul_nonneg (by norm_num) radC0_nonneg) hA0)
    refine h1.trans ?_
    have h2 : 8 * K ^ 2 * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ))
        ≤ 8 * K ^ 2 * (16 * radC0 * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hangbd
        (mul_nonneg (by norm_num) radC0_nonneg)) (by positivity)
    refine h2.trans ?_
    have hEq : 8 * K ^ 2 * (16 * radC0 * M) = 128 * K ^ 2 * radC0 * M := by ring
    linarith [hEq]



/-- **The projector coefficient `Bcoef α = (Γ(θ)/c(α))·2z²/(1+z)³` is smooth on the open
quadrant and lies in `ℋ³`, with `ℋ³`-norm-square bounded uniformly for `α ∈ (0,1]`.** -/
theorem bcoef_gamCoef_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkMem α 3
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkSq α 3
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ≤ C := by
  simpa only [bcoefRad, gamCoefAng] using bcoef_gamCoef_le_aux

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.bcoefRad_zop_bound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The `Zop`-iterates of the radial profile

The level-three closed form is `Work.FTS.StrongPersist.L3Aux.Zop_three_eq` of
`bcoefRadBound.lean`; the next three levels are derived here from the explicit
derivatives `radZop_deriv4/5/6` of the sibling modules of this directory. -/

/-- The fourth `Zop`-iterate of `bcoefRad`, sixth-degree-quartic closed form. -/
lemma Zop_four_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[3] Work.FTS.StrongPersist.L3Aux.bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (-y ^ 3 + 18 * y ^ 2 - 33 * y + 8) / (1 + y) ^ 6) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.StrongPersist.L3Aux.Zop_three_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[3] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7
  show z * deriv (Work.Spaces.Zop^[3] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7
  rw [hev.deriv_eq, (radZop_deriv4 z hzne).deriv]
  field_simp

/-- The fifth `Zop`-iterate of `bcoefRad`. -/
lemma Zop_five_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
          / (1 + z) ^ 8 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16) / (1 + y) ^ 7) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_four_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32) / (1 + z) ^ 8
  show z * deriv (Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32) / (1 + z) ^ 8
  rw [hev.deriv_eq, (radZop_deriv5 z hzne).deriv]
  field_simp

/-- The sixth `Zop`-iterate of `bcoefRad`. -/
lemma Zop_six_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[6] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2
          - 1611 * z + 64) / (1 + z) ^ 9 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (-y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32)
        / (1 + y) ^ 8) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_five_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2
        - 1611 * z + 64) / (1 + z) ^ 9
  show z * deriv (Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
    = 2 * z ^ 2 * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2
        - 1611 * z + 64) / (1 + z) ^ 9
  rw [hev.deriv_eq, (radZop_deriv6 z hzne).deriv]
  field_simp

/-! ## The weighted bound -/

/-- Given the closed form `Zop^[j] bcoefRad z = 2z²P(z)/(1+z)^(3+j)` at a point
`z > 0`, together with `|P z| ≤ C(1+z)^j`, the weighted iterate at `z` is at most
`2C/(1+z)`. -/
lemma weighted_le_of_form (j : ℕ) (C : ℝ) (P : ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hform : Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad z
      = 2 * z ^ 2 * P z / (1 + z) ^ (3 + j))
    (hP : |P z| ≤ C * (1 + z) ^ j) :
    |Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad z * Work.Spaces.w z|
      ≤ 2 * C / (1 + z) := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hform, hw]
  have hAB : 2 * z ^ 2 * P z / (1 + z) ^ (3 + j) * ((1 + z) ^ 2 / z ^ 2)
      = 2 * P z / (1 + z) ^ (j + 1) := by
    field_simp
    ring
  rw [hAB]
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (pow_pos h1z (j + 1))]
  rw [div_le_iff₀ (pow_pos h1z (j + 1))]
  have h2 : 2 * |P z| ≤ 2 * C * (1 + z) ^ j := by
    have := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  calc 2 * |P z| ≤ 2 * C * (1 + z) ^ j := h2
    _ = 2 * C / (1 + z) * (1 + z) ^ (j + 1) := by
        rw [pow_succ]
        field_simp

/-- `|P_4| ≤ 360(1+z)^4` on `z ≥ 0`; `360` is the sum of the absolute values of the
coefficients of `P_4 = z⁴-41z³+171z²-131z+16`. -/
lemma quart_bound {z : ℝ} (hz : 0 ≤ z) :
    |z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16| ≤ 360 * (1 + z) ^ 4 := by
  have h := abs_le_quartic z 1 (-41) 171 (-131) 16 hz
  rw [show (1 : ℝ) * z ^ 4 + (-41) * z ^ 3 + 171 * z ^ 2 + (-131) * z + 16
        = z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16 by ring,
      show |(1 : ℝ)| + |(-41 : ℝ)| + |(171 : ℝ)| + |(-131 : ℝ)| + |(16 : ℝ)| = 360 by norm_num]
    at h
  exact h

/-- `|P_5| ≤ 2520(1+z)^5` on `z ≥ 0`, the sum of the absolute values of the
coefficients of `P_5 = -z⁵+88z⁴-718z³+1208z²-473z+32`. -/
lemma quint_bound {z : ℝ} (hz : 0 ≤ z) :
    |-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32|
      ≤ 2520 * (1 + z) ^ 5 := by
  have h := abs_le_quintic z (-1) 88 (-718) 1208 (-473) 32 hz
  rw [show (-1 : ℝ) * z ^ 5 + 88 * z ^ 4 + (-718) * z ^ 3 + 1208 * z ^ 2 + (-473) * z + 32
        = -z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32 by ring,
      show |(-1 : ℝ)| + |(88 : ℝ)| + |(-718 : ℝ)| + |(1208 : ℝ)| + |(-473 : ℝ)| + |(32 : ℝ)|
        = 2520 by norm_num] at h
  exact h

/-- `|P_6| ≤ 20160(1+z)^6` on `z ≥ 0`, the sum of the absolute values of the
coefficients of `P_6 = z⁶-183z⁵+2682z⁴-8422z³+7197z²-1611z+64`. -/
lemma sext_bound {z : ℝ} (hz : 0 ≤ z) :
    |z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2 - 1611 * z + 64|
      ≤ 20160 * (1 + z) ^ 6 := by
  have h := abs_le_sextic z 1 (-183) 2682 (-8422) 7197 (-1611) 64 hz
  rw [show (1 : ℝ) * z ^ 6 + (-183) * z ^ 5 + 2682 * z ^ 4 + (-8422) * z ^ 3 + 7197 * z ^ 2
        + (-1611) * z + 64
        = z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2 - 1611 * z + 64 by ring,
      show |(1 : ℝ)| + |(-183 : ℝ)| + |(2682 : ℝ)| + |(-8422 : ℝ)| + |(7197 : ℝ)|
        + |(-1611 : ℝ)| + |(64 : ℝ)| = 20160 by norm_num] at h
  exact h

-- The weighted `Zop`-iterates of the radial profile `bcoefRad z = 2z²/(1+z)³` are bounded by
-- `K/(1+z)` uniformly for `j ≤ 6`, `z ≥ 0`.  (The `j ≤ 3` case is `L3Aux.bcoefRad_zop_bound`,
-- proved in the imported `bcoefRadBound.lean` by explicit closed forms; the same route works.)
-- Route: `(Zop^[j] bcoefRad) z = 2z²P_j(z)/(1+z)^(3+j)` with `P_0 = 1`, `P_1 = 2-z`,
-- `P_2 = z²-7z+4`, `P_3 = -z³+18z²-33z+8`, `P_4 = z⁴-41z³+171z²-131z+16`,
-- `P_5 = -z⁵+88z⁴-718z³+1208z²-473z+32`, `P_6 = z⁶-183z⁵+2682z⁴-8422z³+7197z²-1611z+64`
-- (recursion `P_{j+1} = (1+z)(2P_j + zP_j') - (3+j)zP_j`), so that multiplying by
-- `w z = (1+z)²/z²` leaves `2P_j(z)/(1+z)^(j+1)`; a `j`-th degree polynomial bound of `P_j`
-- on `z ≥ 0` gives `K` (explicitly `K = 40320 = 2·∑|coeffs of P_6|` works; the sharp constant
-- is `2^(j+1)`, i.e. `128`).
theorem bcoefRad_zop_bound6 : ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ), j ≤ 6 → ∀ z ∈ Set.Ici (0 : ℝ),
    |(Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
      ≤ K / (1 + z) := by
  obtain ⟨K0, hK0pos, hK0⟩ := Work.FTS.StrongPersist.L3Aux.bcoefRad_zop_bound
  refine ⟨max 40320 K0, lt_max_of_lt_left (by norm_num), ?_⟩
  intro j hj z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  by_cases hj3 : j ≤ 3
  · exact le_trans (hK0 j hj3 z hz)
      (div_le_div_of_nonneg_right (le_max_right 40320 K0) (le_of_lt h1z))
  · -- `3 < j ≤ 6`
    have hj4 : 3 < j := by omega
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rcases eq_or_lt_of_le hz0 with hz' | hzpos
    · rw [← hz', hw0, mul_zero, abs_zero, add_zero, div_one]
      exact le_of_lt (lt_max_of_lt_left (by norm_num : (0 : ℝ) < 40320))
    · have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
      have hj46 : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hj46 with h4 | h5 | h6
      · subst h4
        have h := weighted_le_of_form 4 360
            (fun t : ℝ => t ^ 4 - 41 * t ^ 3 + 171 * t ^ 2 - 131 * t + 16)
            hzpos (Zop_four_eq hzIoi) (quart_bound hz0)
        calc |(Work.Spaces.Zop^[4] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
            ≤ 2 * 360 / (1 + z) := h
          _ = 720 / (1 + z) := by norm_num
          _ ≤ max 40320 K0 / (1 + z) :=
              div_le_div_of_nonneg_right (by norm_num) (le_of_lt h1z)
      · subst h5
        have h := weighted_le_of_form 5 2520
            (fun t : ℝ => -t ^ 5 + 88 * t ^ 4 - 718 * t ^ 3 + 1208 * t ^ 2 - 473 * t + 32)
            hzpos (Zop_five_eq hzIoi) (quint_bound hz0)
        calc |(Work.Spaces.Zop^[5] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
            ≤ 2 * 2520 / (1 + z) := h
          _ = 5040 / (1 + z) := by norm_num
          _ ≤ max 40320 K0 / (1 + z) :=
              div_le_div_of_nonneg_right (by norm_num) (le_of_lt h1z)
      · subst h6
        have h := weighted_le_of_form 6 20160
            (fun t : ℝ => t ^ 6 - 183 * t ^ 5 + 2682 * t ^ 4 - 8422 * t ^ 3 + 7197 * t ^ 2
              - 1611 * t + 64)
            hzpos (Zop_six_eq hzIoi) (sext_bound hz0)
        calc |(Work.Spaces.Zop^[6] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
            ≤ 2 * 20160 / (1 + z) := h
          _ = 40320 / (1 + z) := by norm_num
          _ ≤ max 40320 K0 / (1 + z) :=
              div_le_div_of_nonneg_right (le_max_left 40320 K0) (le_of_lt h1z)

end

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HonestSupMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The honest-class `L^∞`-bound of order `≤ 2` for mixed derivatives.**

For `f` of class `C^∞` on the *open* quadrant with honest `ℋ⁴`-membership (no decay, no
smoothness at the angular boundary, no `𝒲^{l,∞}`-coefficient hypothesis), every mixed
derivative `D_z^bD_θ^a f` with `a + b ≤ 2` is bounded on the open quadrant by
`C/√(γ-1)·|f|_{ℋ⁴}` with a universal `C`.

This is a junction of two proved lemmas:

* `a = 0`, `b ≤ 2`: `Work.FTS.TransportS.sup_dz_le_hk` (pure radial derivatives, honest class);
* `a ≥ 1`: `Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn`, which bounds every mixed
  `D_z^bD_θ^af` with `1 ≤ a`, `a + b ≤ 2` by `√15·|f|_{ℋ⁴}`; since `γ - 1 = α/10 ≤ 1/10`
  one has `1 ≤ 1/√(γ-1)`, so the `1/√(γ-1)` shape covers it. -/
theorem HonestSupMixed : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C1, _, hC1⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨max C0 C1, lt_max_of_lt_left hC0pos, ?_⟩
  intro α f hα hα1 hF hmem b a hab z θ hz hθ hθ2
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1 : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hs1 : Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hγ1
  have hsr : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hγ)]; simpa using hs1
  set s : ℝ := Real.sqrt (Work.Spaces.gam α - 1) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hγ
  set A : ℝ := Work.Spaces.HkNorm α 4 f with hA
  have hA0 : 0 ≤ A := Work.Spaces.HkNorm_nonneg α 4 f
  have hC0nn : 0 ≤ C0 := le_of_lt hC0pos
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    have h := hC0 α f hα hα1 hF hmem b (by omega) z θ hz hθ hθ2
    have h' : |Work.Spaces.mixed b 0 f z θ| ≤ C0 / s * A := by
      simpa only [Work.Spaces.mixed_zero_right, hsdef, hA] using h
    have hle : C0 / s * A ≤ max C0 C1 / s * A := by
      refine mul_le_mul_of_nonneg_right ?_ hA0
      exact div_le_div_of_nonneg_right (le_max_left _ _) hs0.le
    linarith
  · have h := hC1 α f hα hα1 hF hmem b a hapos hab z θ hz hθ hθ2
    have h' : |Work.Spaces.mixed b a f z θ| ≤ C1 * A := by
      simpa only [Work.FTS.Nonlin.Xn, hA] using h
    have hstep : C1 * A ≤ max C0 C1 / s * A := by
      have hmax : C1 ≤ max C0 C1 := le_max_right _ _
      have hmax0 : 0 ≤ max C0 C1 := le_trans hC0nn (le_max_left _ _)
      have h1 : C1 * A ≤ max C0 C1 * A := mul_le_mul_of_nonneg_right hmax hA0
      have h2 : max C0 C1 * A ≤ max C0 C1 * ((1 / s) * A) := by
        refine mul_le_mul_of_nonneg_left ?_ hmax0
        calc A = 1 * A := by ring
          _ ≤ (1 / s) * A := mul_le_mul_of_nonneg_right hsr hA0
      have h3 : max C0 C1 * ((1 / s) * A) = max C0 C1 / s * A := by
        rw [div_eq_mul_inv]; ring
      linarith [h1, h2, h3.le, h3.ge]
    linarith

end Work.FTS.StrongPersist.N6Trans
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter
open Finset

noncomputable section

set_option autoImplicit false

/-- **The "easy" Leibniz majorant of the `D_θ`-transport pairing.**

For each slot `(a,b)` of the flat `ℋ⁴`-pairing (`a` the `θ`-order, `b` the `z`-order,
`a + b ≤ 4`) and each Leibniz split `(a1,b1) ≤ (a,b)` of `mixed b a (f·D_θg)` *except* the
"hard" split `(a1,b1) = (0,0)` (in which all derivatives fall on the `g`-block), the summand is

  `slotW α a · |mixed b1 a1 f| · |mixed (b-b1)(a-a1+1) g| · |mixed b a g|`.

This is the sum of absolute values of all the Leibniz summands of
`∑_{(a,b), a+b ≤ 4} ∫∫ slotW α a · |mixed b a (f·D_θg)| · |mixed b a g|`
up to the five hard summands. -/
def EasyLeib (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
      (if a + b ≤ 4 then
        ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then 0 else
            Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)
      else 0)

/-! ## The matching of the two Leibniz majorants

Both `EasyLeib` and `EasyMajor` are finite sums of *absolute values* of Leibniz summands, so the
comparison is purely combinatorial: the Leibniz summand of the slot `(a,b)` is literally a summand
of `EasyMajor` up to the binomial factor of the Leibniz rule, and `EasyMajor` retains *at least*
every summand that `EasyLeib` keeps.  (This block is a verbatim port of the completed proof in
`Submission/Work/FTS/StrongPersist/N6Trans/LeibMajor/EasyLeib_le_EasyMajor.lean`, whose module
imports this one; the declaration below is the one the consumers of this module use.) -/

/-- The `a`-th slot sum of `EasyLeib` (the inner double sum over the Leibniz splits). -/
private def FL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (a : ℕ) : ℝ :=
  ∑ b ∈ Finset.range 5,
    (if a + b ≤ 4 then
      ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then 0 else
          Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|)
    else 0)

/-- The `D_z`-part of `EasyMajor` (the `xD` summands). -/
private def ZL (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
    (if i = 4 ∧ b = 0 then 0 else |Work.FTS.H2.xD f g i b z θ|)

/-- The `i`-th mixed slot of `EasyMajor` (the `yM` summands). -/
private def MiL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 5,
    (if 1 ≤ i ∧ i + j ≤ 4 then
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |Work.FTS.H2.yM α f g i j a b z θ|)
    else 0)

private lemma EasyLeib_eq_sum_FL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    EasyLeib α f g z θ = ∑ a ∈ Finset.range 5, FL α f g z θ a := rfl

private lemma EasyMajor_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.EasyMajor α f g z θ
      = ZL f g z θ + ∑ i ∈ Finset.range 5, MiL α f g z θ i := rfl

/-- The elementary product inequality behind every summand comparison: a nonnegative weight
`W` times three nonnegative factors is dominated by the same expression with the coefficient
`c ≥ 1` in front and the weight `W` moved to the back. -/
private lemma prod_four_le {W c A B C : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hc : 1 ≤ c) : W * A * B * C ≤ c * A * B * C * W := by
  have hX : 0 ≤ A * B * C := by positivity
  have h1 : W ≤ c * W := by nlinarith
  calc W * A * B * C = W * (A * B * C) := by ring
    _ ≤ (c * W) * (A * B * C) := mul_le_mul_of_nonneg_right h1 hX
    _ = c * A * B * C * W := by ring

/-- The `a = 0` summand (`a1 = 0` fixed): the `D_z`-slot Leibniz summand of `EasyLeib` is
dominated by the `xD` summand of `EasyMajor` with the same split `k`, the factor
`(m.choose k) ≥ 1` accounting for the binomial coefficient of the Leibniz rule. -/
private lemma xD_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {m k : ℕ} (hk : k ≤ m) :
    (if (0:ℕ) = 0 ∧ k = 0 then 0 else
      Work.FTS.TransportS.slotW α 0 z θ * |Work.Spaces.mixed k 0 f z θ|
        * |Work.Spaces.mixed (m - k) (0 - 0 + 1) g z θ| * |Work.Spaces.mixed m 0 g z θ|)
      ≤ (if m = 4 ∧ k = 0 then 0 else |Work.FTS.H2.xD f g m k z θ|) := by
  by_cases hk0 : k = 0
  · rw [if_pos ⟨rfl, hk0⟩]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [if_neg (fun h => hk0 h.2), if_neg (fun h => hk0 h.2)]
    simp only [Work.FTS.TransportS.slotW_zero]
    have hxabs : |Work.FTS.H2.xD f g m k z θ|
        = (m.choose k : ℝ) * |Work.Spaces.DzIter k f z θ|
          * |Work.Spaces.mixed (m - k) 1 g z θ| * |Work.Spaces.DzIter m g z θ|
          * Work.FTS.H2.Whz z θ ^ 2 := by
      unfold Work.FTS.H2.xD
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (m.choose k : ℝ) from Nat.cast_nonneg _),
        abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg (Work.FTS.H2.Whz z θ))]
      ring
    rw [hxabs]
    have hc : (1:ℝ) ≤ (m.choose k : ℝ) := by
      have h := Nat.choose_pos hk
      exact_mod_cast h
    exact prod_four_le (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hc

/-- The `a ≥ 1` summand: the mixed-slot Leibniz summand of `EasyLeib` is dominated by the
`yM` summand of `EasyMajor` with the same split `(a1,b1)`, the binomial product
`(a.choose a1)·(b.choose b1) ≥ 1` accounting for the Leibniz coefficients. -/
private lemma yM_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {a b a1 b1 : ℕ}
    (ha : 1 ≤ a) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) :
    (if a1 = 0 ∧ b1 = 0 then 0 else
      Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
      ≤ (if a1 = 0 ∧ b1 = 0 ∧ a + b = 4 then 0
          else |Work.FTS.H2.yM α f g a b a1 b1 z θ|) := by
  by_cases h00 : a1 = 0 ∧ b1 = 0
  · rw [if_pos h00]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [if_neg h00, if_neg (fun h => h00 ⟨h.1, h.2.1⟩)]
    simp only [Work.FTS.TransportS.slotW_of_pos' α ha]
    have hyabs : |Work.FTS.H2.yM α f g a b a1 b1 z θ|
        = ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
          * Work.FTS.H2.Wm α z θ ^ 2 := by
      unfold Work.FTS.H2.yM
      rw [abs_mul, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ (a.choose a1 : ℝ) from Nat.cast_nonneg _),
        abs_of_nonneg (show (0:ℝ) ≤ (b.choose b1 : ℝ) from Nat.cast_nonneg _),
        abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg (Work.FTS.H2.Wm α z θ))]
      ring
    rw [hyabs]
    have h1 : (1:ℝ) ≤ (a.choose a1 : ℝ) := by
      have h := Nat.choose_pos ha1
      exact_mod_cast h
    have h2 : (1:ℝ) ≤ (b.choose b1 : ℝ) := by
      have h := Nat.choose_pos hb1
      exact_mod_cast h
    have hc : (1:ℝ) ≤ ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) := by nlinarith
    exact prod_four_le (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hc

/-- The `a = 0` slot of `EasyLeib` is dominated by the `D_z`-part `ZL` of `EasyMajor`. -/
private lemma FL_zero_le_ZL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    FL α f g z θ 0 ≤ ZL f g z θ := by
  unfold FL ZL
  refine Finset.sum_le_sum fun b hb => ?_
  have hb4 : b ≤ 4 := by have := Finset.mem_range.mp hb; omega
  rw [if_pos (by omega : 0 + b ≤ 4)]
  rw [show (0:ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
  refine Finset.sum_le_sum fun b1 hb1 => ?_
  have hb1' : b1 ≤ b := by have := Finset.mem_range.mp hb1; omega
  exact xD_term_le (α := α) (f := f) (g := g) (z := z) (θ := θ) (m := b) (k := b1) hb1'

/-- Every mixed slot of `EasyMajor` is nonnegative. -/
private lemma MiL_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) :
    0 ≤ MiL α f g z θ i := by
  unfold MiL
  refine Finset.sum_nonneg fun j hj => ?_
  split_ifs
  · exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => by
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
  · exact le_rfl

/-- Every slot of `EasyLeib` with `a ≥ 1` is dominated by the corresponding mixed slot of
`EasyMajor`. -/
private lemma FL_le_MiL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) (hi : 1 ≤ i) :
    FL α f g z θ i ≤ MiL α f g z θ i := by
  unfold FL MiL
  refine Finset.sum_le_sum fun b hb => ?_
  by_cases hg : i + b ≤ 4
  · rw [if_pos hg, if_pos ⟨hi, hg⟩]
    refine Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 => ?_
    exact yM_term_le (α := α) (f := f) (g := g) (z := z) (θ := θ) (a := i) (b := b)
      (a1 := a1) (b1 := b1) hi (by have := Finset.mem_range.mp ha1; omega)
      (by have := Finset.mem_range.mp hb1; omega)
  · rw [if_neg hg, if_neg (fun h => hg h.2)]

/-- **The matching of the easy Leibniz majorant with `EasyMajor`.**

Pointwise on the open quadrant, the easy Leibniz majorant `EasyLeib` of the `D_θ`-transport
pairing is dominated by the workspace majorant `Work.FTS.H2.EasyMajor` of the flat `ℋ⁴`-pairing
(with the `xD`/`yM` summands of `Submission/Work/FTS/H2/T1EasyBound.lean`): the Leibniz summand
of the slot `(a,b)` (in the `D_z`-slot case `a = 0` with the `z`-order `i := b` and the split
`b1`) is *literally* `|xD f g b b1|` up to the binomial factor, and in the mixed case
`a ≥ 1` it is `|yM α f g a b a1 b1|`; and `EasyMajor` retains every one of them except the
two hard families `(i,b) = (4,0)` resp. `(a,b) = (0,0)`, `i + j = 4`, which are excluded from
`EasyLeib` as well.  `EasyMajor` additionally retains the hard summands of the slots with
`a + b ≤ 3`, which only makes it larger.

Route: rewrite the `θ`-derivative `mixed (b-b1)(a-a1) (D_θg) = mixed (b-b1)(a-a1+1) g`, expand
the two definitions, and compare term by term (`Finset.sum_le_sum`, `Finset.sum_nonneg`,
`if_pos`/`if_neg` with the guards of `EasyMajor`). -/
theorem EasyLeib_le_EasyMajor {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      EasyLeib α f g z θ ≤ Work.FTS.H2.EasyMajor α f g z θ := by
  intro z θ hz hθ hθ2
  rw [EasyMajor_eq, EasyLeib_eq_sum_FL]
  have hA : FL α f g z θ 0 ≤ ZL f g z θ := FL_zero_le_ZL α f g z θ
  have hB : (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1))
      ≤ MiL α f g z θ 0 + ∑ a ∈ Finset.range 4, MiL α f g z θ (a + 1) := by
    have h1 : (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1))
        ≤ ∑ a ∈ Finset.range 4, MiL α f g z θ (a + 1) :=
      Finset.sum_le_sum fun a ha => FL_le_MiL α f g z θ (a + 1) (by omega)
    have h2 : (0:ℝ) ≤ MiL α f g z θ 0 := MiL_nonneg α f g z θ 0
    linarith
  have hsplit1 : (∑ a ∈ Finset.range 5, FL α f g z θ a)
      = (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1)) + FL α f g z θ 0 :=
    Finset.sum_range_succ' (fun a => FL α f g z θ a) 4
  have hsplit2 : (∑ i ∈ Finset.range 5, MiL α f g z θ i)
      = (∑ i ∈ Finset.range 4, MiL α f g z θ (i + 1)) + MiL α f g z θ 0 :=
    Finset.sum_range_succ' (fun i => MiL α f g z θ i) 4
  rw [hsplit1, hsplit2]
  linarith

end

end Work.FTS.StrongPersist.N6Trans
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open MeasureTheory Set Filter
open scoped Real Topology

/-- The open quadrant `(0,∞) × (0,π/2)` has full measure for the product of the two restricted
Lebesgue measures `(volume|Iz).prod (volume|Iθ)`. -/
theorem ae_mem_Q0_prod :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (0 : ℝ) < p.1 ∧ (0 : ℝ) < p.2 ∧ p.2 < π / 2 := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : MeasureTheory.Measure (ℝ × ℝ))] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    fun p hp => hp

set_option quotPrecheck false in
/-- The product of the two restricted Lebesgue measures, as it appears throughout the flat
pairing estimates. -/
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))


end Work.FTS.StrongPersist.N6Trans.SixRoute
end
