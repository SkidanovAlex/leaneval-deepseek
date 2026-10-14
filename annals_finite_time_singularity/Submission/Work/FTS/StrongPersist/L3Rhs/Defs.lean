import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Series.Deleg.psiCmodeAux.Basic
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.angGram_modeSum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter



end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.cmode_abs_le_of_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon.CmpSupp

set_option autoImplicit false

/-- **The mode coefficients of a continuous, compactly supported source are `O(1/√(eNorm m))`.**

`cmode m F t` is the quotient `bInt m F t / eNorm m`, where `bInt` is the scalar product of the
slice `F t ·` with the mode `eFam m` in `L²(Iθ, cos θ dθ)`.  Cauchy–Schwarz bounds the numerator
by `√(∫_{Iθ} (F t θ)² cos θ) · √(eNorm m)`, and the first factor is uniformly bounded on the
compact rectangle `[a,b] × Iθ` because `F` is continuous there.  (The support hypothesis is not
needed: the estimate is uniform on any compact set.)

This is the fifth conjunct of `cmode_facts`; it is what makes the mode series
`Σ_m cmode m F z · e_m(θ)` comparable with the `L²`-normalised modes. -/
theorem cmode_abs_le_of_continuous {a b : ℝ} {F : ℝ → ℝ → ℝ}
    (hFc : Continuous (Function.uncurry F))
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → F z θ = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b,
        |Work.FTS.PhiStar.Series.cmode m F t|
          ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  have hmeas : MeasurableSet Work.Spaces.Iθ := by rw [hIθ]; exact measurableSet_Icc
  have hcomp : IsCompact Work.Spaces.Iθ := by rw [hIθ]; exact isCompact_Icc
  -- the rectangle `[a,b] × Iθ` is compact and `F` is continuous there
  have hrect : IsCompact (Set.Icc a b ×ˢ Work.Spaces.Iθ) := isCompact_Icc.prod hcomp
  obtain ⟨C, hC⟩ := hrect.exists_bound_of_continuousOn hFc.continuousOn
  -- replace `C` by a nonnegative bound (`C` is only determined up to the empty-set case)
  set C' : ℝ := max C 0 with hC'def
  have hC'nn : 0 ≤ C' := le_max_right _ _
  have hC'bd : ∀ x ∈ Set.Icc a b ×ˢ Work.Spaces.Iθ, ‖Function.uncurry F x‖ ≤ C' :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  -- `∫_{Iθ} cos = 1`
  have hcosint : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
    rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hπ, integral_cos, Real.sin_pi_div_two, Real.sin_zero]
    ring
  refine ⟨C' + 1, by linarith, ?_⟩
  intro m t ht
  -- the two factors of the Cauchy–Schwarz inequality, and their continuity
  have hFt : Continuous (fun θ : ℝ => F t θ) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hEcont : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    Work.EllipticEst.ModalSolution.continuous_eFam m
  have hfcont : Continuous (fun θ : ℝ => Real.sqrt (Real.cos θ) * F t θ) :=
    (Real.continuous_sqrt.comp Real.continuous_cos).mul hFt
  have hgcont : Continuous (fun θ : ℝ =>
      Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Real.continuous_sqrt.comp Real.continuous_cos).mul hEcont
  have hfasm : AEStronglyMeasurable (fun θ : ℝ => Real.sqrt (Real.cos θ) * F t θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hfcont.continuousOn.aestronglyMeasurable hmeas
  have hgasm : AEStronglyMeasurable (fun θ : ℝ =>
      Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hgcont.continuousOn.aestronglyMeasurable hmeas
  have hfint : Integrable (fun θ : ℝ => (Real.sqrt (Real.cos θ) * F t θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact hcomp (hfcont.pow 2).continuousOn
  have hgint : Integrable (fun θ : ℝ =>
      (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact hcomp (hgcont.pow 2).continuousOn
  -- Cauchy–Schwarz in `L²(Iθ, cos θ dθ)`
  have hCS := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    hgasm hfasm hgint hfint
  have hCSb : |Work.EllipticEst.ModalSolution.bInt m F t| ≤
      Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Real.sqrt (Real.cos θ) * F t θ) ^ 2) := by
    simpa only [Work.EllipticEst.ModalSolution.bInt] using hCS
  -- the two squared norms
  have hG2 : (∫ θ in Work.Spaces.Iθ,
        (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
      = Work.EllipticEst.ModalSolution.eNorm m := by
    rw [Work.EllipticEst.ModalSolution.eNorm]
    refine MeasureTheory.setIntegral_congr_fun hmeas (fun θ hθ => ?_)
    rw [hIθ] at hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hcos]
    ring
  have hF2 : (∫ θ in Work.Spaces.Iθ, (Real.sqrt (Real.cos θ) * F t θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun hmeas (fun θ hθ => ?_)
    rw [hIθ] at hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hcos]
    ring
  -- the slice energy is bounded by `C'²`
  have hEbound : (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ) ≤ C' ^ 2 := by
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ ≤ C' ^ 2 * Real.cos θ := by
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by rwa [← hIθ]
      have hcos : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
      have h1 : |F t θ| ≤ C' := by
        have h := hC'bd (t, θ) ⟨ht, hθ⟩
        simpa [Function.uncurry, Real.norm_eq_abs] using h
      have h2 : (F t θ) ^ 2 ≤ C' ^ 2 := by
        have h3 := pow_le_pow_left₀ (abs_nonneg (F t θ)) h1 2
        rwa [sq_abs] at h3
      exact mul_le_mul_of_nonneg_right h2 hcos
    have hint1 : IntegrableOn (fun θ : ℝ => (F t θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact hcomp
        ((hFt.pow 2).mul Real.continuous_cos).continuousOn
    have hint2 : IntegrableOn (fun θ : ℝ => C' ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact hcomp
        (continuous_const.mul Real.continuous_cos).continuousOn
    calc (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C' ^ 2 * Real.cos θ :=
          MeasureTheory.setIntegral_mono_on hint1 hint2 hmeas hpt
      _ = C' ^ 2 * ∫ θ in Work.Spaces.Iθ, Real.cos θ := by
          rw [MeasureTheory.integral_const_mul]
      _ = C' ^ 2 := by rw [hcosint, mul_one]
  -- the numerator bound
  have hnum : |Work.EllipticEst.ModalSolution.bInt m F t|
      ≤ C' * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
    calc |Work.EllipticEst.ModalSolution.bInt m F t|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Real.sqrt (Real.cos θ) * F t θ) ^ 2) := hCSb
      _ = Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ) := by
          rw [hG2, hF2, mul_comm]
      _ ≤ Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) * C' :=
          mul_le_mul_of_nonneg_left
            (le_trans (Real.sqrt_le_sqrt hEbound) (by rw [Real.sqrt_sq hC'nn]))
            (Real.sqrt_nonneg _)
      _ = C' * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by ring
  -- division by `eNorm m > 0`
  have hNe : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hsqne : Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hNe)
  calc |Work.FTS.PhiStar.Series.cmode m F t|
      = |Work.EllipticEst.ModalSolution.bInt m F t|
          / Work.EllipticEst.ModalSolution.eNorm m := by
        rw [Work.EllipticEst.ModalSolution.cmode_eq m F t, abs_div, abs_of_pos hNe]
    _ ≤ (C' * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          / Work.EllipticEst.ModalSolution.eNorm m :=
        div_le_div_of_nonneg_right hnum hNe.le
    _ = C' / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
        rw [div_eq_div_iff hNe.ne' hsqne]
        rw [mul_assoc, Real.mul_self_sqrt hNe.le]
    _ ≤ (C' + 1) / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
        div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end Work.FTS.ClassCHon.CmpSupp
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000


end Work.FTS.ClassCHon.Zpz
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.BmodeExpansionSelf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

set_option autoImplicit false

/-! ## Elementary facts -/

/-- The angular eigenfunctions are continuous. -/
lemma continuous_eFam_aux (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ => Real.cos θ
    * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

/-- The vanishing `sin θ cos²θ`-moment kills the kernel coefficient `bmode 0 ψ`. -/
lemma bmode_zero_aux {ψ : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF

/-- `Icc 0 (π/2)` and `Ioo 0 (π/2)` carry the same restricted Lebesgue measure. -/
lemma restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hsub : Work.Spaces.Iθ \ Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ {0} ∪ {Real.pi / 2} := by
      intro x hx
      simp only [Set.mem_sdiff, Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioo, Set.mem_union,
        Set.mem_singleton_iff] at hx ⊢
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (le_antisymm hx.1.2 (le_of_not_gt fun hlt => hx.2 ⟨h, hlt⟩))
    have hfin : ({0} ∪ {Real.pi / 2} : Set ℝ).Finite :=
      (Set.finite_singleton (0 : ℝ)).union (Set.finite_singleton (Real.pi / 2))
    exact measure_mono_null hsub (hfin.measure_zero volume)
  · have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) \ Work.Spaces.Iθ ⊆ (∅ : Set ℝ) := by
      intro x hx
      simp only [Set.mem_sdiff, Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioo] at hx
      exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
    exact measure_mono_null hsub measure_empty

/-! ## The majorant -/

/-- The summable majorant of the `m`-th term `bmode m ψ · eFam m θ`: for `m ≥ 1` the term is
bounded by `Cd Cg (2m+1)^{-3/2}`. -/
def mcMajor (Cd Cg : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 0 else Cd * Cg * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))

lemma mcMajor_nonneg (Cd Cg : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg) (m : ℕ) :
    0 ≤ mcMajor Cd Cg m := by
  rw [mcMajor]
  split
  · norm_num
  · positivity

lemma mcMajor_le (Cd Cg : ℝ) (hCd : 0 ≤ Cd) (hCg : 0 ≤ Cg) (m : ℕ) :
    mcMajor Cd Cg m ≤ Cd * Cg * (((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  rw [mcMajor]
  split
  · exact mul_nonneg (mul_nonneg hCd hCg) (Real.rpow_nonneg (by positivity) _)
  · have hbase : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h1 : ((m : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ (2 * (m : ℝ) + 1) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (le_of_lt hbase) hle (by norm_num)
    have h3 : (2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))
        ≤ ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_neg (le_of_lt hbase), inv_eq_one_div,
        inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hbase _) h1
    exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hCd hCg)

/-- `Σ_m (m+1)^{-3/2}` converges. -/
lemma summable_rpow_neg_three_halves :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
  have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) 1).mpr h0
  simpa only [Nat.cast_add, Nat.cast_one] using h1

lemma summable_mcMajor (Cd Cg : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg) :
    Summable (mcMajor Cd Cg) := by
  refine Summable.of_nonneg_of_le (fun m => mcMajor_nonneg Cd Cg hCd hCg m) (fun m => ?_)
    ((summable_rpow_neg_three_halves).mul_left (Cd * Cg))
  exact mcMajor_le Cd Cg (le_of_lt hCd) (le_of_lt hCg) m

/-! ## The arithmetic of the term bound -/

/-- `(2m+1)² ≤ lam m` for `m ≥ 1`. -/
lemma sq_two_mul_add_one_le_lam {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  rw [Work.FTS.PhiStar.Gegenbauer.lam]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

lemma one_div_mul_sqrt (t : ℝ) (ht : 0 < t) : 1 / (t * Real.sqrt t) = t ^ (-(3 / 2 : ℝ)) := by
  have h1 : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [← h1, Real.rpow_neg (le_of_lt ht), inv_eq_one_div]

/-- The per-mode arithmetic of the majorant: `(2m+1)/(lam m · √(2m+1)) ≤ (2m+1)^{-3/2}`. -/
lemma div_lam_sqrt_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ (2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have htpos : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hsqrtpos : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr htpos
  have hdenpos : 0 < (2 * (m : ℝ) + 1) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
    mul_pos (pow_pos htpos 2) hsqrtpos
  have hsq := sq_two_mul_add_one_le_lam hm
  have hden : (2 * (m : ℝ) + 1) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
      ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hsq (le_of_lt hsqrtpos)
  have hinv : (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
      ≤ ((2 * (m : ℝ) + 1) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hdenpos hden
  have h1 : (2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ (2 * (m : ℝ) + 1) / ((2 * (m : ℝ) + 1) ^ 2
          * Real.sqrt (2 * (m : ℝ) + 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt htpos)
  have h2 : (2 * (m : ℝ) + 1) / ((2 * (m : ℝ) + 1) ^ 2
        * Real.sqrt (2 * (m : ℝ) + 1))
      = (2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have h3 : (2 * (m : ℝ) + 1) / ((2 * (m : ℝ) + 1) ^ 2
          * Real.sqrt (2 * (m : ℝ) + 1))
        = 1 / ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [h3, one_div_mul_sqrt _ htpos]
  exact le_trans h1 (le_of_eq h2)

/-! ## The term bound and its consequences -/

/-- **The per-term bound.** -/
lemma abs_bmode_mul_eFam_le (ψ : ℝ → ℝ) (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ‖Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
      ≤ mcMajor Cd Cg m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [hb0, zero_mul, norm_zero, mcMajor]
    simp
  · have h1 : ‖Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        = |Work.FTS.PhiStar.Series.bmode m ψ|
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
      rw [Real.norm_eq_abs, abs_mul]
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos (by
        rw [Work.FTS.PhiStar.Gegenbauer.lam]
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith) (Real.sqrt_pos.mpr (by positivity))
    have hstep : |Work.FTS.PhiStar.Series.bmode m ψ|
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Cd * Cg * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
      have hb := hdec m hm
      have he := hgr m θ hθ
      have harith : (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
            * (2 * (m : ℝ) + 1)
          ≤ Cd * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
        have h := div_lam_sqrt_le (m := m) hm
        have hdiv : (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) * (2 * (m : ℝ) + 1)
            = Cd * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) := by
          ring
        rw [hdiv]
        exact mul_le_mul_of_nonneg_left h (le_of_lt hCd)
      calc |Work.FTS.PhiStar.Series.bmode m ψ|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * (Cg * (2 * (m : ℝ) + 1)) :=
            mul_le_mul hb he (abs_nonneg _) (le_of_lt (div_pos hCd hden))
        _ = Cg * ((Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))) * (2 * (m : ℝ) + 1)) := by ring
        _ ≤ Cg * (Cd * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left harith (le_of_lt hCg)
        _ = Cd * Cg * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by ring
    rw [h1, mcMajor, if_neg (by omega : ¬ (m = 0))]
    exact hstep

/-- **Pointwise summability** of the mode series on `Iθ`. -/
lemma summable_bmode_eFam_aux (ψ : ℝ → ℝ) (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1)) :
    ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ =>
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  intro θ hθ
  refine Summable.of_norm_bounded (summable_mcMajor Cd Cg hCd hCg) (fun m => ?_)
  exact abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m hθ

/-- **Continuity** of the mode series on `Iθ`. -/
lemma continuousOn_tsum_bmode_eFam_aux (ψ : ℝ → ℝ)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1)) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      Work.Spaces.Iθ :=
  continuousOn_tsum (fun m => ((continuous_eFam_aux m).const_mul _).continuousOn)
    (summable_mcMajor Cd Cg hCd hCg)
    (fun m θ hθ => abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m hθ)

/-- **The `eFam n`-coefficient of the series is `bmode n ψ`.** -/
lemma integral_series_mul_eFam_aux (ψ : ℝ → ℝ) (n : ℕ)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1)) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  have hB : 0 ≤ Cg * (2 * (n : ℝ) + 1) := by positivity
  have hmain : HasSum (fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := by
    refine hasSum_integral_of_dominated_convergence
      (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun m θ => (Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (f := fun θ => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (fun m _ => mcMajor Cd Cg m * (Cg * (2 * (n : ℝ) + 1))) ?_ ?_ ?_ ?_ ?_
    · intro m
      exact ((continuous_const.mul (continuous_eFam_aux m)).mul
        ((continuous_eFam_aux n).mul Real.continuous_cos)).aestronglyMeasurable
    · intro m
      simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m ha
      have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ Cg * (2 * (n : ℝ) + 1) := by
        rw [abs_mul]
        calc |Work.FTS.PhiStar.Gegenbauer.eFam n a| * |Real.cos a|
            ≤ (Cg * (2 * (n : ℝ) + 1)) * 1 :=
              mul_le_mul (hgr n a ha) (Real.abs_cos_le_one a) (abs_nonneg _) hB
          _ = Cg * (2 * (n : ℝ) + 1) := by ring
      exact mul_le_mul h1 h2 (abs_nonneg _) (mcMajor_nonneg Cd Cg hCd hCg m)
    · exact Filter.Eventually.of_forall
        (fun _ => (summable_mcMajor Cd Cg hCd hCg).mul_right _)
    · haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
        constructor
        rw [Work.Spaces.Iθ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))).measure_lt_top
      have hc : Integrable (fun _ : ℝ =>
          ∑' m : ℕ, mcMajor Cd Cg m * (Cg * (2 * (n : ℝ) + 1)))
          (volume.restrict Work.Spaces.Iθ) := integrable_const _
      simpa using hc
    · simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      exact ((summable_bmode_eFam_aux ψ hb0 hCd hCg hdec hgr a ha).hasSum).mul_right _
  have hterm : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = Work.FTS.PhiStar.Series.bmode m ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
    intro m
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, integral_const_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hGzero : ∀ m : ℕ, m ≠ n →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0 := by
    intro m hmn
    rw [Work.FTS.PhiStar.Series.iota_eq_interval]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hGn : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ :=
    integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    _ = ∑' m : ℕ, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := hmain.tsum_eq.symm
    _ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := tsum_congr hterm
    _ = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        tsum_eq_single n (fun m hm => by rw [hGzero m hm, mul_zero])
    _ = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2
            * Real.cos θ) := by rw [hGn]

/-! ## The expansion -/

theorem BmodeExpansionSelf (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hcont : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨M₀, hM₀⟩ := hbdd
  set M : ℝ := |M₀| with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact abs_nonneg _
  have hM : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M := by
    intro θ hθ
    rw [hMdef]
    exact le_trans (hM₀ θ hθ) (le_abs_self M₀)
  have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := bmode_zero_aux hmom
  set F : ℝ → ℝ := fun θ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
    * Work.FTS.PhiStar.Gegenbauer.eFam m θ with hF
  have hFcont : ContinuousOn F Work.Spaces.Iθ :=
    continuousOn_tsum_bmode_eFam_aux ψ hb0 hCd hCg hdec hgr
  have hFcontIoo : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)) :=
    hFcont.mono Set.Ioo_subset_Icc_self
  have hK : 0 ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
    tsum_nonneg (fun m => mcMajor_nonneg Cd Cg hCd hCg m)
  -- the coefficient of the series against `eFam n`
  have hcoef : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, F θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    have h := integral_series_mul_eFam_aux ψ n hb0 hCd hCg hdec hgr
    simpa only [hF] using h
  -- the difference is orthogonal to every eigenfunction
  have horth : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0 := by
    intro n
    have hψint : IntegrableOn (fun θ : ℝ => ψ θ
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) Work.Spaces.Iθ := by
      refine IntegrableOn.of_bound ?_ ?_ (M * (Cg * (2 * (n : ℝ) + 1))) ?_
      · rw [Work.Spaces.Iθ]
        exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))).measure_lt_top
      · rw [restrict_Iθ_eq_restrict_Ioo]
        exact (hcont.aestronglyMeasurable measurableSet_Ioo).mul
          (((continuous_eFam_aux n).continuousOn.mul Real.continuous_cos.continuousOn).aestronglyMeasurable
            measurableSet_Ioo)
      · rw [restrict_Iθ_eq_restrict_Ioo, ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall (fun θ hθ => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |ψ θ| ≤ M := hM θ hθ
        have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ|
            ≤ Cg * (2 * (n : ℝ) + 1) := by
          rw [abs_mul]
          calc |Work.FTS.PhiStar.Gegenbauer.eFam n θ| * |Real.cos θ|
              ≤ (Cg * (2 * (n : ℝ) + 1)) * 1 :=
                mul_le_mul (hgr n θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
                  (Real.abs_cos_le_one θ) (abs_nonneg _) (by positivity)
            _ = Cg * (2 * (n : ℝ) + 1) := by ring
        exact mul_le_mul h1 h2 (abs_nonneg _) hMnn
    have hFint : IntegrableOn (fun θ : ℝ => F θ
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hFcont.mul (((continuous_eFam_aux n).mul Real.continuous_cos).continuousOn))
    have hcongr : (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
          * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, (ψ θ
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
          - F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hcongr, integral_sub hψint hFint]
    have hψcoef : (∫ θ in Work.Spaces.Iθ, ψ θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ
          * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
      rw [← Work.FTS.PhiStar.Series.bmode_mul_norm n ψ]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have hFcoef : (∫ θ in Work.Spaces.Iθ, F θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ
          * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
      rw [← hcoef n]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hψcoef, hFcoef, sub_self]
  -- measurability of the difference on `Iθ`
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => ψ θ - F θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    exact (hcont.aestronglyMeasurable measurableSet_Ioo).sub
      (hFcontIoo.aestronglyMeasurable measurableSet_Ioo)
  -- integrability of `(ψ - F)² cos θ` on `Iθ`
  have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(ψ θ - F θ) ^ 2 * Real.cos θ‖
        ≤ (M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2 := by
    intro θ hθ
    have hFb : |F θ| ≤ ∑' m : ℕ, mcMajor Cd Cg m := by
      have hsumRaw : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
        Summable.of_norm_bounded (summable_mcMajor Cd Cg hCd hCg)
          (fun m => abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      have hsumθ : Summable (fun m : ℕ => ‖Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖) := hsumRaw.norm
      calc |F θ| = ‖F θ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' m : ℕ, ‖Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ :=
            norm_tsum_le_tsum_norm hsumθ
        _ ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
            Summable.tsum_le_tsum (fun m => abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m
              ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) hsumθ (summable_mcMajor Cd Cg hCd hCg)
    have h1 : |ψ θ - F θ| ≤ M + ∑' m : ℕ, mcMajor Cd Cg m := by
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · have h2 : -F θ ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
          le_trans (neg_le_abs (F θ)) hFb
        have h3 : ψ θ ≤ M := le_trans (le_abs_self (ψ θ)) (hM θ hθ)
        linarith
      · have h2 : F θ ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
          le_trans (le_abs_self (F θ)) hFb
        have h3 : -ψ θ ≤ M := le_trans (neg_le_abs (ψ θ)) (hM θ hθ)
        linarith
    calc ‖(ψ θ - F θ) ^ 2 * Real.cos θ‖
        = |ψ θ - F θ| ^ 2 * |Real.cos θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), sq_abs]
      _ ≤ (M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2 * 1 := by
          refine mul_le_mul ?_ (Real.abs_cos_le_one θ) (abs_nonneg _) (by positivity)
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2 := by ring
  have hint : IntegrableOn (fun θ : ℝ => (ψ θ - F θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
    refine IntegrableOn.of_bound ?_ ?_ ((M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2) ?_
    · rw [Work.Spaces.Iθ]
      exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))).measure_lt_top
    · rw [restrict_Iθ_eq_restrict_Ioo]
      exact (((hcont.sub hFcontIoo).aestronglyMeasurable measurableSet_Ioo).pow 2).mul
        (Real.continuous_cos.continuousOn.aestronglyMeasurable measurableSet_Ioo)
    · rw [restrict_Iθ_eq_restrict_Ioo, ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall (fun θ hθ => hbound θ hθ)
  -- completeness
  have hae := Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => ψ θ - F θ)
    hmeas hint horth
  have hae' : (fun θ : ℝ => ψ θ - F θ)
      =ᵐ[volume.restrict (Set.Ioo 0 (Real.pi / 2))] 0 := by
    rw [← restrict_Iθ_eq_restrict_Ioo]
    exact hae
  have heq : EqOn (fun θ : ℝ => ψ θ - F θ) 0 (Set.Ioo 0 (Real.pi / 2)) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo (hcont.sub hFcontIoo) continuousOn_const
  intro θ hθ
  have h0 : ψ θ - F θ = 0 := heq hθ
  have h1 : F θ = ψ θ := by linarith
  simpa only [hF] using h1

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.cmode_sq_le_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- The `m`-th Gegenbauer mode `e_m`, locally abbreviated. -/
private abbrev eF (m : ℕ) : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m

/-- Almost every point of `Iθ = [0, π/2]` is interior: the two endpoints are null. -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
private theorem setIntegral_Iθ_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.lzero1_pair_eFam_c2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Gegenbauer (eFam lam)
open Work.FTS.EllipticEst (Lzero1)

/-! ### Auxiliary lemmas for the `Lzero1` pairing identity -/

/-- `cos θ > 0` on the open angular interval. -/
private lemma cos_pos_of_Ioo' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩

/-- A `C²` function on the closed angular interval is bounded there. -/
private lemma abs_bound_of_continuousOn {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) :
    ∃ B : ℝ, ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |v θ| ≤ B := by
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))) hv.continuousOn
  exact ⟨B, fun θ hθ => by simpa [Real.norm_eq_abs] using hB θ hθ⟩

/-- **`Lzero1 v` is continuous on the open interval** for `v` of class `C²` on the closed one.
On `(0, π/2)` the two `deriv`-occurrences of `Lzero1` may be replaced by the `derivWithin`
versions on `Icc` (which are continuous there by `ContDiffOn.derivWithin`, twice) and the
`deriv (tan θ · v θ)` by the explicit product-rule expression. -/
private lemma continuousOn_Lzero1 {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) :
    ContinuousOn (Lzero1 v) (Set.Ioo 0 (Real.pi / 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hpi2
  have hw1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hU (by norm_num)
  have hw2 : ContDiffOn ℝ 0
      (derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hw1.derivWithin hU (by norm_num)
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  have htan : ContinuousOn Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuousOn_tan_Ioo.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn.pow 2
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ^ 2 ≠ 0 :=
    fun θ hθ => pow_ne_zero 2 (ne_of_gt (cos_pos_of_Ioo' hθ))
  have hmain : ContinuousOn (fun θ : ℝ =>
      -(derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) θ)
      + (v θ / Real.cos θ ^ 2 + Real.tan θ * derivWithin v (Set.Icc 0 (Real.pi / 2)) θ)
      - 6 * v θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((hw2.continuousOn.mono hsub).neg).add
      ((((hv.continuousOn.mono hsub).div hcos2 hne).add
        (htan.mul (hw1.continuousOn.mono hsub))))).sub
      (continuousOn_const.mul (hv.continuousOn.mono hsub))
  refine hmain.congr (fun θ hθ => ?_)
  have hmem : Set.Icc 0 (Real.pi / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
  have hev : derivWithin v (Set.Icc 0 (Real.pi / 2)) =ᶠ[𝓝 θ] deriv v := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hA : deriv (deriv v) θ
      = derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) θ := by
    have h1 : deriv (derivWithin v (Set.Icc 0 (Real.pi / 2))) θ = deriv (deriv v) θ :=
      hev.deriv_eq
    have h2 : deriv (derivWithin v (Set.Icc 0 (Real.pi / 2))) θ
        = derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) θ :=
      (derivWithin_of_mem_nhds hmem).symm
    exact h1.symm.trans h2
  have hB : deriv (fun t : ℝ => Real.tan t * v t) θ
      = v θ / Real.cos θ ^ 2 + Real.tan θ * deriv v θ := by
    have hdv : HasDerivAt v (deriv v θ) θ :=
      ((hv.mono hsub).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
        (by norm_num) |>.hasDerivAt
    have h1 : deriv (fun t : ℝ => Real.tan t * v t) θ
        = 1 / Real.cos θ ^ 2 * v θ + Real.tan θ * deriv v θ :=
      ((Real.hasDerivAt_tan (ne_of_gt (cos_pos_of_Ioo' hθ))).mul hdv).deriv
    rw [h1]
    ring
  have hC : derivWithin v (Set.Icc 0 (Real.pi / 2)) θ = deriv v θ :=
    derivWithin_of_mem_nhds hmem
  simp only [Lzero1]
  rw [show deriv (fun t : ℝ => deriv v t) θ = deriv (deriv v) θ from rfl, hA, hB, ← hC]

/-- **The primitive `P θ = cos θ · (e_n' v - e_n v')` is continuous on the closed interval.**
All factors except `deriv v` are continuous there, and `deriv v` agrees with
`derivWithin v Icc` on the interior; at the endpoints both terms of the bracket vanish
(`e_n 0 = 0`, `v (π/2) = 0`, `cos (π/2) = 0`). -/
private lemma continuousOn_P_primitive (v : ℝ → ℝ) (n : ℕ)
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0) :
    ContinuousOn (fun θ => Real.cos θ * (deriv (eFam n) θ * v θ - eFam n θ * deriv v θ))
      (Set.Icc 0 (Real.pi / 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hpi2
  have hw1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hU (by norm_num)
  have hde : ContinuousOn (deriv (eFam n)) (Set.Icc 0 (Real.pi / 2)) :=
    (ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n)).continuous.continuousOn
  have hec : ContinuousOn (fun θ => eFam n θ) (Set.Icc 0 (Real.pi / 2)) :=
    (Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n).continuous.continuousOn
  have hmain : ContinuousOn (fun θ => Real.cos θ * (deriv (eFam n) θ * v θ
      - eFam n θ * derivWithin v (Set.Icc 0 (Real.pi / 2)) θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn.mul
      ((hde.mul hv.continuousOn).sub (hec.mul hw1.continuousOn))
  refine hmain.congr (fun θ hθ => ?_)
  simp only []
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    simp only [h0, Work.FTS.PhiStar.Series.Deleg.eFam_zero n]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      simp only [Real.cos_pi_div_two]
      ring
    · rw [derivWithin_of_mem_nhds (Icc_mem_nhds h h2)]

/-- **The pointwise Wronskian identity** for `e_n` and `v`: on the open interval the derivative
of the primitive `P` is exactly the pairing integrand `(Lzero1 v - lam n · v) · e_n · cos θ`. -/
private lemma hasDerivAt_P_primitive {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' => Real.cos θ' * (deriv (eFam n) θ' * v θ' - eFam n θ' * deriv v θ'))
      ((Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ) θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Ioo' hθ)
  have hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv.mono Set.Ioo_subset_Icc_self
  have hop : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hsm : ContDiff ℝ 3 (eFam n) := Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n
  have he1 : HasDerivAt (eFam n) (deriv (eFam n) θ) θ :=
    (hsm.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have he2 : HasDerivAt (deriv (eFam n)) (deriv (deriv (eFam n)) θ) θ :=
    ((ContDiff.deriv' (n := 2) hsm).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hv1 : HasDerivAt v (deriv v θ) θ :=
    ((hv2.contDiffAt hop).differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffOn ℝ 1 (deriv v) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hv1' : HasDerivAt (deriv v) (deriv (deriv v) θ) θ :=
    ((hd1.contDiffAt hop).differentiableAt (by norm_num)).hasDerivAt
  have h := Work.FTS.PhiStar.Series.Deleg.hasDerivAt_lzero_wronskian (f := eFam n) (g := v)
    hcos he1 he2 hv1 hv1'
  refine h.congr_deriv ?_
  rw [Work.FTS.PhiStar.Series.Deleg.eFam_Lzero1 n hθ]
  ring

/-- **The `Lzero1` pairing identity for a `C²` slice (self-adjointness in the weight `cos θ dθ`).**

For `v` of class `C²` (within the) closed interval `[0, π/2]` with `v 0 = v (π/2) = 0`, and
`e := eFam n`, `lam n = 2n(2n+5)` (the Dirichlet eigenvalue of `Lzero1`, see `eFam_Lzero`),
one has

  `∫_{Iθ} (Lzero1 v) · e_n · cos θ = lam n · ∫_{Iθ} v · e_n · cos θ`.

The extra hypothesis `hbd` (a bound for `Lzero1 v` on the *open* interval) is used only for
integrability bookkeeping: the global `deriv` occurring in `Lzero1` is junk at the two
endpoints `0, π/2`, and `hbd` says the integrand is bounded on `(0, π/2)`, hence an honest
Bochner integrand.  It is supplied by the companion lemma `lzero1_bdd_on_Ioo`; the identity
itself does not need it mathematically.

*Route (for the prover).*  Write `e := eFam n` and
`P θ := -((e θ * deriv v θ - deriv e θ * v θ) * Real.cos θ)`.
For `θ ∈ Set.Ioo 0 (π/2)` both `v` (by `hv.mono Ioo_subset_Icc_self`) and `eFam n`
(`contDiff_eFam n`) are `C²` on a neighbourhood of `θ`, so the product rule gives
`HasDerivAt P (…) θ`; expanding and using the eigen-equation in the form
`Lzero1 (eFam n) θ = lam n * eFam n θ` (from `eFam_Lzero` + `Lzero1_eq_Lzero`, valid because
`Real.cos θ ≠ 0` on the open interval) the derivative is exactly

  `(Lzero1 v θ - lam n * v θ) * e θ * Real.cos θ`.

(This is the same computation as the private `hasDerivAt_primitive` of
`Submission/Work/EllipticEst/ModalSolution/Lzero1_energy_cos_correct.lean`, and as
`Submission/Work/FTS/PhiStar/Series/lzero1Primitive.lean` — do NOT import the latter: it
currently fails to build in this workspace.  Re-prove the ~20-line pointwise identity locally.)

`P` is continuous on `Icc`: all factors but `deriv v` are continuous there (`hv.continuousOn`,
`contDiff_eFam n`), and `deriv v θ = derivWithin v (Icc 0 (π/2)) θ` for `θ ∈ Ioo`
(`derivWithin_of_mem_nhds`, as `Icc ∈ 𝓝 θ`), while `ContDiffOn ℝ 1 (derivWithin v Icc) Icc`
(`hv.derivWithin (uniqueDiffOn_Icc _)`) is continuous on the compact `Icc`.  The endpoint
values are `P 0 = P (π/2) = 0`: at `θ = 0` the junk factor `deriv v 0` is multiplied by
`eFam n 0 = 0`, at `θ = π/2` by `v (π/2) = 0` and by `cos (π/2) = 0`.  Hence
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` gives `∫_0^{π/2} (…) = 0`, provided the
integrand is `IntervalIntegrable` on `(0, π/2)` — that follows from `hbd`, from boundedness of
`v` and `e` on `Icc`, and from the fact that the integrand equals a continuous function on
`Ioo`, the only point of `uIoc 0 (π/2)` outside `Ioo` being `π/2` where the junk is multiplied
by `eFam n (π/2) = 0` and `cos (π/2) = 0`.  Splitting the interval integral of
`(Lzero1 v - lam n * v) * e * cos` with `MeasureTheory.integral_sub` (both pieces integrable by
the same boundedness argument) and converting the interval integral on `0..π/2` into the set
integral over `Iθ` (`MeasureTheory.integral_Icc_eq_integral_Ioc` +
`intervalIntegral.integral_of_le`, cf. `ModalSolution.intervalIntegral_eq_setIntegral`) gives
the claim. -/
theorem lzero1_pair_eFam_c2 (v : ℝ → ℝ) (n : ℕ)
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0)
    (hbd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.Lzero1 v θ| ≤ M) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam n
        * (∫ θ in Work.Spaces.Iθ,
            v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle : (0 : ℝ) ≤ Real.pi / 2 := hpi2.le
  obtain ⟨M, hM⟩ := hbd
  have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg _)
    (hM (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  obtain ⟨Q, hQnn, hQ⟩ := Work.FTS.PhiStar.Series.Deleg.eFam_abs_bound n
  obtain ⟨B, hB⟩ := abs_bound_of_continuousOn hv
  have hBnn : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨le_refl 0, hle⟩)
  have hLc : ContinuousOn (fun θ => Lzero1 v θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_Lzero1 hv
  have hEc : ContinuousOn (fun θ => eFam n θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n).continuous.continuousOn
  have hVc : ContinuousOn v (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv.continuousOn.mono Set.Ioo_subset_Icc_self
  have hCc : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn
  have hMc : ContinuousOn (fun θ => lam n * v θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_const.mul hVc
  -- interval integrability of the two pieces of the split integrand
  have hint1 : IntervalIntegrable (fun θ => Lzero1 v θ * eFam n θ * Real.cos θ)
      volume 0 (Real.pi / 2) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle
      ((hLc.mul hEc).mul hCc) (M * Q) ?_
    intro θ hθ
    have hb1 : |Lzero1 v θ| ≤ M := hM θ hθ
    have hb2 : |eFam n θ| ≤ Q := hQ θ ⟨hθ.1.le, hθ.2.le⟩
    have hb3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    calc |Lzero1 v θ * eFam n θ * Real.cos θ|
        = |Lzero1 v θ| * |eFam n θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ M * Q * 1 := mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hMnn) hb3
          (abs_nonneg _) (mul_nonneg hMnn hQnn)
      _ = M * Q := by ring
  have hint2 : IntervalIntegrable (fun θ => v θ * eFam n θ * Real.cos θ)
      volume 0 (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact (hv.continuousOn.mul
      ((Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n).continuous.continuousOn)).mul
      Real.continuous_cos.continuousOn
  -- interval integrability of the difference integrand
  have hintg : IntervalIntegrable
      (fun θ => (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ)
      volume 0 (Real.pi / 2) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle
      (((hLc.sub hMc).mul hEc).mul hCc) ((M + |lam n| * B) * Q) ?_
    intro θ hθ
    have hb1 : |Lzero1 v θ - lam n * v θ| ≤ M + |lam n| * B := by
      calc |Lzero1 v θ - lam n * v θ| ≤ |Lzero1 v θ| + |lam n * v θ| := abs_sub _ _
        _ = |Lzero1 v θ| + |lam n| * |v θ| := by rw [abs_mul]
        _ ≤ M + |lam n| * B := add_le_add (hM θ hθ)
            (mul_le_mul_of_nonneg_left (hB θ ⟨hθ.1.le, hθ.2.le⟩) (abs_nonneg _))
    have hb2 : |eFam n θ| ≤ Q := hQ θ ⟨hθ.1.le, hθ.2.le⟩
    have hb3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hA : (0 : ℝ) ≤ M + |lam n| * B :=
      add_nonneg hMnn (mul_nonneg (abs_nonneg _) hBnn)
    calc |(Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ|
        = |Lzero1 v θ - lam n * v θ| * |eFam n θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ (M + |lam n| * B) * Q * 1 := mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hA)
          hb3 (abs_nonneg _) (mul_nonneg hA hQnn)
      _ = (M + |lam n| * B) * Q := by ring
  -- the fundamental theorem of calculus for the primitive `P`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    (continuousOn_P_primitive v n hv h0 h1)
    (fun x hx => hasDerivAt_P_primitive hv n hx) hintg
  have hP0 : Real.cos 0 * (deriv (eFam n) 0 * v 0 - eFam n 0 * deriv v 0) = 0 := by
    rw [h0, Work.FTS.PhiStar.Series.Deleg.eFam_zero n]
    ring
  have hPpi : Real.cos (Real.pi / 2) * (deriv (eFam n) (Real.pi / 2) * v (Real.pi / 2)
      - eFam n (Real.pi / 2) * deriv v (Real.pi / 2)) = 0 := by
    rw [Real.cos_pi_div_two]
    ring
  have hzero : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ) = 0 := by
    rw [hFTC, hPpi, hP0, sub_self]
  -- splitting the integrand
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), Lzero1 v θ * eFam n θ * Real.cos θ)
        - lam n * (∫ θ in (0 : ℝ)..(Real.pi / 2), v θ * eFam n θ * Real.cos θ) := by
    have hsub : IntervalIntegrable
        (fun θ => lam n * (v θ * eFam n θ * Real.cos θ)) volume 0 (Real.pi / 2) :=
      hint2.const_mul _
    rw [show (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ)
        = ∫ θ in (0 : ℝ)..(Real.pi / 2),
            (Lzero1 v θ * eFam n θ * Real.cos θ
              - lam n * (v θ * eFam n θ * Real.cos θ)) from
      intervalIntegral.integral_congr (fun θ _ => by ring)]
    rw [intervalIntegral.integral_sub hint1 hsub, intervalIntegral.integral_const_mul]
  -- converting the interval integral into the set integral over `Iθ`
  have hIθ : ∀ F : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, F θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
    intro F
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  rw [hIθ (fun θ => Lzero1 v θ * eFam n θ * Real.cos θ),
    hIθ (fun θ => v θ * eFam n θ * Real.cos θ)]
  linarith [hzero, hsplit]

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.sliceMass_moment_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory
open scoped Real

/-- **Weighted Cauchy–Schwarz for the `η`-weighted slice pairing.**

With the weights `A θ = (F z θ)^2 * sin(2θ)^{-η}` and
`B θ = (eFam m θ cos θ)^2 * sin(2θ)^{η}` the Cauchy–Schwarz (Bunyakovsky) inequality applied to
`√A` and `√B` gives

`(∫_Iθ F z θ · eFam m θ · cos θ)^2 ≤ (∫_Iθ (F z θ)^2 sin(2θ)^{-η}) · (∫_Iθ (eFam m θ cos θ)^2 sin(2θ)^{η})`,

because `√A · √B = |F z θ| · |eFam m θ cos θ|` on the interior of `Iθ` (the two weights multiply to
`1` there) and the target integral is dominated by the integral of its absolute value.  The
integrability hypothesis on `A` is used, together with the fact that `B` is integrable on the
compact `Iθ` (the `eFam m` are polynomials composed with `sin`, multiplied by `cos`). -/
theorem sliceMass_moment_le {m : ℕ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
              * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  let A : ℝ → ℝ := fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let B : ℝ → ℝ := fun θ : ℝ =>
    (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hA : MeasureTheory.IntegrableOn A Work.Spaces.Iθ := hint
  have hB : MeasureTheory.IntegrableOn B Work.Spaces.Iθ :=
    (Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow m).1
  have hAnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ A x := by
    intro x hx
    change 0 ≤ (F z x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.PhiStar.Honesty.sin_two_nonneg_of_mem_Iθ hx) _)
  have hBnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ B x := by
    intro x hx
    change 0 ≤ (Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x) ^ 2
      * (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.PhiStar.Honesty.sin_two_nonneg_of_mem_Iθ hx) _)
  -- Cauchy–Schwarz for the two square roots
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le hIθ hA hB hAnn hBnn
  -- The square-root product equals `|F z ·| * |eFam m · · cos ·|` up to the two endpoints of `Iθ`.
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Work.Spaces.Iθ →
      Real.sqrt (A x) * Real.sqrt (B x)
        = |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| := by
    rw [MeasureTheory.ae_iff]
    have hnull : volume ({(0 : ℝ), π / 2} : Set ℝ) = 0 :=
      Set.Finite.measure_zero ((Set.finite_singleton (π / 2)).insert (0 : ℝ)) volume
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro x hx
    rw [Set.mem_setOf_eq, not_imp] at hx
    obtain ⟨hxI, hxne⟩ := hx
    have hmem : (0 : ℝ) ≤ x ∧ x ≤ π / 2 := hxI
    have hbd : ¬ (0 < x ∧ x < π / 2) := fun h =>
      hxne (Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo F m z h)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases lt_or_eq_of_le hmem.1 with h0 | h0
    · right
      have hge : π / 2 ≤ x := by
        by_contra hlt
        exact hbd ⟨h0, lt_of_not_ge hlt⟩
      exact le_antisymm hmem.2 hge
    · left; exact h0.symm
  have hEq : (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) * Real.sqrt (B x))
      = ∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| :=
    MeasureTheory.setIntegral_congr_ae hIθ hae
  -- The target integral is dominated by the integral of its absolute value, which in turn is the
  -- integral of `|F| * |eFam·cos|`.
  have h1 : |∫ x in Work.Spaces.Iθ,
        F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|
      ≤ ∫ x in Work.Spaces.Iθ,
          |F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := (volume : Measure ℝ).restrict Work.Spaces.Iθ)
        (f := fun x : ℝ => F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x))
  have h2 : (∫ x in Work.Spaces.Iθ,
        |F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|)
      = ∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| :=
    MeasureTheory.setIntegral_congr_fun hIθ (fun x _ => by
      rw [abs_mul, abs_mul, abs_mul]
      ring)
  have h3 : |∫ x in Work.Spaces.Iθ,
        F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|
      ≤ ∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| := by
    rw [← h2]; exact h1
  calc (∫ x in Work.Spaces.Iθ, F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x) ^ 2
      = |∫ x in Work.Spaces.Iθ,
            F z x * Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x in Work.Spaces.Iθ,
          |F z x| * |Work.FTS.PhiStar.Gegenbauer.eFam m x * Real.cos x|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) * Real.sqrt (B x)) ^ 2 := by rw [hEq]
    _ ≤ (∫ x in Work.Spaces.Iθ, A x) * (∫ x in Work.Spaces.Iθ, B x) := hcs

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.tsum_bmode_eFam_eq_of_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## The `m = 0` coefficient vanishes from the moment condition -/

/-- Under the moment condition `∫_Iθ ψ · sinCos2 = 0` the `0`-th Gegenbauer coefficient of `ψ`
vanishes (`eFam 0 · cos = 3 sinCos2`). -/
lemma bmode_zero_of_moment (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF

/-! ## The pointwise bound behind summability, continuity and integration -/

/-- `|bmode m ψ · eFam m θ| ≤ Cd·Cg·(m+1)^{-3/2}` on `Iθ`, from the growth bound on `eFam` and
the decay bound on `bmode` (and the vanishing of the `m = 0` term). -/
lemma abs_bmode_mul_eFam_le (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    {Cg Cd : ℝ} (hCg : 0 < Cg) (hCd : 0 < Cd)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * ((m : ℝ) + 1))
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [bmode_zero_of_moment ψ hmom, zero_mul, abs_zero]
    exact le_of_lt (mul_pos (mul_pos hCd hCg) (Real.rpow_pos_of_pos (by norm_num) _))
  · rw [abs_mul]
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc |Work.FTS.PhiStar.Series.bmode m ψ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) * (Cg * ((m : ℝ) + 1)) :=
          mul_le_mul (hdec m hm) (hsup m θ hθ) (abs_nonneg _)
            (le_of_lt (mul_pos hCd (Real.rpow_pos_of_pos hmpos _)))
      _ = Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
          have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1)
              = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
            calc ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1)
                = ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
              _ = ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ) + 1) := (Real.rpow_add hmpos _ _).symm
              _ = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by norm_num
          rw [← hp]
          ring

/-! ## The three series lemmas -/

/-- The mode series is summable at every point of `Iθ`. -/
lemma summable_bmode_eFam (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  intro θ hθ
  refine Summable.of_norm_bounded
    ((Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2) (by norm_num)).mul_left
      (Cd * Cg)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bmode_mul_eFam_le ψ hmom hCg hCd hsup hdec m hθ

/-- The sum of the mode series is continuous on `Iθ` (Weierstrass M-test). -/
lemma continuousOn_tsum_bmode_eFam (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hsum : ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  refine continuousOn_tsum
    (fun m => (continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).continuousOn)
    ((Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2) (by norm_num)).mul_left
      (Cd * Cg)) (fun m θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bmode_mul_eFam_le ψ hmom hCg hCd hsup hdec m hθ

/-- The `e_n`-coefficient of the sum of the mode series, computed by dominated convergence. -/
lemma integral_series_mul_eFam (ψ : ℝ → ℝ) (n : ℕ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hsum : ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ *
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  have hB : 0 ≤ Cg * ((n : ℝ) + 1) :=
    le_of_lt (mul_pos hCg (by positivity))
  have hmain : HasSum (fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := by
    refine hasSum_integral_of_dominated_convergence
      (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun m θ => (Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (f := fun θ => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (fun m _ => (Cd * Cg * (Cg * ((n : ℝ) + 1))) * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))
      ?_ ?_ ?_ ?_ ?_
    · intro m
      exact ((continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).mul
        ((Work.FTS.PhiStar.Series.continuous_eFam n).mul Real.continuous_cos)).aestronglyMeasurable
    · intro m
      simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_bmode_mul_eFam_le ψ hmom hCg hCd hsup hdec m ha
      have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ Cg * ((n : ℝ) + 1) := by
        rw [abs_mul]
        calc |Work.FTS.PhiStar.Gegenbauer.eFam n a| * |Real.cos a|
            ≤ (Cg * ((n : ℝ) + 1)) * 1 :=
              mul_le_mul (hsup n a ha) (Real.abs_cos_le_one a) (abs_nonneg _) hB
          _ = Cg * ((n : ℝ) + 1) := by ring
      have h3 : (0 : ℝ) ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
        le_of_lt (mul_pos (mul_pos hCd hCg) (Real.rpow_pos_of_pos (by positivity) _))
      calc |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m a|
            * |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ (Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) * (Cg * ((n : ℝ) + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) h3
        _ = (Cd * Cg * (Cg * ((n : ℝ) + 1))) * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by ring
    · exact Filter.Eventually.of_forall
        (fun _ => (Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2)
          (by norm_num)).mul_left _)
    · exact integrable_const _
    · simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      exact ((hsum a ha).hasSum).mul_right _
  -- identify the two sides
  set G : ℕ → ℝ := fun m => ∫ θ in Work.Spaces.Iθ,
    Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
      * Real.cos θ with hG
  have hterm : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = Work.FTS.PhiStar.Series.bmode m ψ * G m := by
    intro m
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, integral_const_mul, hG]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hGzero : ∀ m : ℕ, m ≠ n → G m = 0 := by
    intro m hmn
    show (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0
    rw [Work.FTS.PhiStar.Series.iota_eq_interval]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hGn : G n = ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ := by
    rw [hG]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    _ = ∑' m : ℕ, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := hmain.tsum_eq.symm
    _ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * G m := tsum_congr hterm
    _ = Work.FTS.PhiStar.Series.bmode n ψ * G n :=
        tsum_eq_single n (fun m hm => by rw [hGzero m hm, mul_zero])
    _ = Work.FTS.PhiStar.Series.bmode n ψ *
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
        rw [hGn]

/-! ## The assembly -/

theorem tsum_bmode_eFam_eq_of_continuous (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hcont : ContinuousOn ψ Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  have hsum := summable_bmode_eFam ψ hmom hsup hdec
  have hcontF := continuousOn_tsum_bmode_eFam ψ hmom hsup hdec hsum
  set F : ℝ → ℝ := fun θ =>
    ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
    with hFdef
  have hFcont : ContinuousOn F Work.Spaces.Iθ := hcontF
  have hcontSub : ContinuousOn (fun θ : ℝ => ψ θ - F θ) Work.Spaces.Iθ :=
    hcont.sub hFcont
  -- the `e_n`-coefficients of `ψ` and of the series
  have hψcoef : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    rw [← Work.FTS.PhiStar.Series.bmode_mul_norm n ψ]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hFcoef : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    rw [← integral_series_mul_eFam ψ n hmom hsup hdec hsum]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  -- orthogonality of the difference against every eigenfunction
  have horth : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ) = 0 := by
    intro n
    have hψint : IntegrableOn
        (fun θ : ℝ => ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hcont.mul ((Work.FTS.PhiStar.Series.continuous_eFam n).continuousOn.mul
          Real.continuous_cos.continuousOn))
    have hFint : IntegrableOn
        (fun θ : ℝ => F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hFcont.mul ((Work.FTS.PhiStar.Series.continuous_eFam n).continuousOn.mul
          Real.continuous_cos.continuousOn))
    have hcongr : (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
          * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
              - F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hcongr, integral_sub hψint hFint, hψcoef n, hFcoef n, sub_self]
  -- measurability and integrability of the difference
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => ψ θ - F θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hcontSub.aestronglyMeasurable measurableSet_Icc
  have hint : IntegrableOn (fun θ : ℝ => (ψ θ - F θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hcontSub.pow 2).mul Real.continuous_cos.continuousOn)
  have hae : (fun θ : ℝ => ψ θ - F θ) =ᵐ[volume.restrict Work.Spaces.Iθ] 0 :=
    Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => ψ θ - F θ) hmeas hint horth
  -- transfer to the open interval and use continuity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hae' : (fun θ : ℝ => ψ θ - F θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq : EqOn (fun θ : ℝ => ψ θ - F θ) 0 (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hae' isOpen_Ioo
      (hcontSub.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
      continuousOn_const
  intro θ hθ hθ2
  have h0 : ψ θ - F θ = 0 := heq ⟨hθ, hθ2⟩
  have : F θ = ψ θ := by linarith
  exact this

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity and the square-root form -/

theorem Sq6_nonneg (α : ℝ) (f : Fn) : 0 ≤ Sq6 α f := Work.Spaces.HkSq_nonneg α 6 f

theorem Xn6_nonneg (α : ℝ) (f : Fn) : 0 ≤ Xn6 α f := Real.sqrt_nonneg _


theorem Xn6_sq (α : ℝ) (f : Fn) : Xn6 α f ^ 2 = Sq6 α f := Real.sq_sqrt (Sq6_nonneg α f)

theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : Fn) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ

/-! ## Monotonicity in the order -/

/-- **Pointwise monotonicity of the `ℋ^k`-integrand in the order** (`k' ≤ k ⟹ ≤`).  This is
`Work.FTS.StrongLWP.HkIntegrand_mono`, the pointwise half of `ℋ^k ⊂ ℋ^{k'}`. -/
theorem HkIntegrand_le_of_le (α : ℝ) {k k' : ℕ} (hkk : k ≤ k') (f : Fn) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α k' f z θ :=
  Work.FTS.StrongLWP.HkIntegrand_mono α f hkk z θ

/-- **`ℋ⁶ ⊂ ℋ⁴` at the level of the norm**: the order-`6` norm dominates the order-`4` one
(the order-`6` membership is what makes the comparison meaningful). -/
theorem Xn_le_Xn6 (α : ℝ) {f : Fn} (hf : H6Mem α f) : Xn α f ≤ Xn6 α f :=
  Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4) (by norm_num) hf

/-- **`ℋ^k`-membership descends in the order**, for data smooth on the open quadrant: the
level-`k` integrand is a sub-sum of the level-`k'` one and `SmoothOpen` supplies the a.e. strong
measurability of the smaller one.  (Thin wrapper around
`Work.FTS.EllipticEst.TT.HkMem_descend_open`; it is what turns S2's order-`6` output into the
order-`4` membership `RegPkgMin.mem4` asks for.) -/
theorem HkMem_of_le_of_smoothOpen (α : ℝ) {k k' : ℕ} (hkk : k ≤ k') {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.Spaces.HkMem α k' f) :
    Work.Spaces.HkMem α k f :=
  Work.FTS.EllipticEst.TT.HkMem_descend_open hkk
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm) hf

/-- The `ℋ⁴`-membership of a slice whose `ℋ⁶`-membership and interior smoothness are known —
the form in which S2's output feeds `RegPkgMin.mem4`. -/
theorem HkMem_four_of_six {α : ℝ} {f : Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hf : H6Mem α f) : Work.Spaces.HkMem α 4 f :=
  HkMem_of_le_of_smoothOpen α (by norm_num) hsm hf


/-! ## The integrand vanishes on the axis -/

/-- At `z = 0` the radial weight `w 0 = (1+0)²/0²` is `0` by the totalised division of `ℝ`, so
**every** summand of the `ℋ^k`-integrand vanishes.  This is the null-set fact which makes the
`z = 0` end of the domain harmless in all a.e. arguments of the chapter. -/
theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : Fn) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have hWt : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, hw]
  unfold Work.Spaces.HkIntegrand
  simp only [hw, hWt, mul_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

/-! ## Projections of the clause packages -/




/-! ## The `XnBddOn` API -/




/-! ## Projections of the regularity packages -/






/-! ## Bridges to the sibling area `FTS/StrongLWP`

The S1/S3 area (`Work.FTS.StrongLWP`) carries its own copies of `IsBslSolPos`, `RegPkgMin`,
`RegPkgH6` and `Xn6`.  The two `IsBslSolPos` differ only in the bracketing of the two Dirichlet
identities; the two `RegPkgMin` have the same fields in the same order.  The bridges below let a
consumer use S2 (`persist_H6`) and S6 (`dbd_of_eq`) together with S1/S3 in either vocabulary. -/






end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs =====
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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The coefficient functions of the `F_*`-pieces -/

/-- The coefficient `D_θ F_*` of the second half of `I^{N₀}_4`. -/
abbrev NA4 (α : ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dth (Work.Construction.Fstar α)

/-- The coefficient `c2m · D_zF_*` of the first half of `I^{N₀}_5`. -/
abbrev NA5 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The coefficient `c2m · L₁₂(F_*)` of `I^{N₀}_6`. -/
abbrev NA6 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z

/-! ## The seven pieces of `N₀` -/

/-- `I^{N₀}_1 + I^{N₀}_2` in the shape of `H6Rows.FstarI12H6`. -/
abbrev NA1 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- `I^{N₀}_3 = (1/α)·(L₁₂(f)·f)`. -/
abbrev NP3 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / α) * (Work.Construction.L12 f z * f z θ)

/-- `I^{N₀}_4` with the `F_*`-half of `∂_θF`, in the shape of `T45aRow`. -/
abbrev NP4a (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * NA4 α z θ)

/-- `I^{N₀}_4` with the `f`-half of `∂_θF`, in the shape of `T4bRowSlot`. -/
abbrev NP4b (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)

/-- `I^{N₀}_5` with the `F_*`-half of `D_zF`, in the shape of `T45aRow`. -/
abbrev NP5a (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) * (Work.Construction.L12 f z * NA5 α z θ)

/-- `I^{N₀}_5` with the `f`-half of `D_zF`, in the shape of `T5bRow`/`row_l12_dz`. -/
abbrev NP5b (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Construction.L12 f z
    * Work.Spaces.Dz f z θ)

/-- `I^{N₀}_6`, in the shape of `row_A_dz`. -/
abbrev NP6 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) * (NA6 α z θ * Work.Spaces.Dz f z θ)

/-! ## The `Q₀`-congruence of the elementary slot pairing -/


/-! ## Scaling a per-slot bound -/


/-! ## The elementary `α`-arithmetic -/

/-- `α ^ (-m) ≤ α ^ (-(10:ℝ))` for `0 < α ≤ 1` and `m ≤ 10`. -/
theorem rpow_neg_le_neg_ten {α m : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hm : m ≤ 10) :
    α ^ (-m) ≤ α ^ (-(10 : ℝ)) := by
  have h : α ^ (-m) = α ^ (10 - m) * α ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hα0]
    ring_nf
  rw [h]
  have hle : α ^ (10 - m) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by linarith)
  calc α ^ (10 - m) * α ^ (-(10 : ℝ)) ≤ 1 * α ^ (-(10 : ℝ)) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hα0.le _)
    _ = α ^ (-(10 : ℝ)) := one_mul _

/-- `1 ≤ α ^ (-(10:ℝ))` for `0 < α ≤ 1`. -/
theorem one_le_rpow_neg_ten {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(10 : ℝ)) := by
  rw [Real.rpow_neg hα0.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast]
  exact (one_le_inv₀ (by positivity : (0 : ℝ) < α ^ 10)).mpr (pow_le_one₀ hα0.le hα1)


/-- `√t ≤ 1 + t` for `t ≥ 0`. -/
theorem sqrt_le_one_add {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ 1 + t := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

/-! ## Smoothness of the pieces -/

theorem smoothOpen_NA1 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA1 α) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (3 / (2 * α))
      * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_const_mul (3 / (2 * α)) (so_snd contDiff_s2))
      (smoothOpen_L12_Fstar α)) (smoothOpen_Fstar α).pth
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) (smoothOpen_L12_Fstar α)) (smoothOpen_Fstar α).Dz
  have h12 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ((3 / (2 * α))
      * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    so_sub h1 h2
  exact h12

theorem smoothOpen_NA4 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA4 α) :=
  (smoothOpen_Fstar α).Dth

theorem smoothOpen_NA5 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA5 α) :=
  so_mul (so_snd contDiff_c2m) (smoothOpen_Fstar α).Dz

theorem smoothOpen_NA6 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA6 α) :=
  so_mul (so_snd contDiff_c2m) (smoothOpen_L12_Fstar α)

theorem smoothOpen_NP3 {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP3 α f) :=
  so_const_mul (1 / α) (so_mul hL hf)

theorem smoothOpen_NP4a {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP4a α f) :=
  so_const_mul (3 / (2 * α)) (so_mul hL (smoothOpen_NA4 α))

theorem smoothOpen_NP4b {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP4b α f) :=
  so_const_mul (3 / (2 * α)) (so_mul hL hf.Dth)

theorem smoothOpen_NP5a {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP5a α f) :=
  so_const_mul (-1) (so_mul hL (smoothOpen_NA5 α))

theorem smoothOpen_NP5b {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP5b α f) :=
  so_const_mul (-1) (so_mul (so_mul (so_snd contDiff_c2m) hL) hf.Dz)

theorem smoothOpen_NP6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP6 α f) :=
  so_const_mul (-1) (so_mul (smoothOpen_NA6 α) hf.Dz)


/-- `α ^ s ≤ α ^ (-(10:ℝ))` for `0 < α ≤ 1` and `s ≥ -10`. -/
theorem rpow_le_neg_ten_of {α s : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hs : -10 ≤ s) :
    α ^ s ≤ α ^ (-(10 : ℝ)) := by
  rw [show s = -(-s) from by ring]
  exact rpow_neg_le_neg_ten hα0 hα1 (by linarith)


/-- `c·α^m·(1+X)^4·(1+S) ≤ (c+1)·α^{-10}·(1+X)^4·(1+S)` for `m ≥ -10`. -/
theorem majorant_rpow {α X S c m : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hm : -10 ≤ m) :
    c * α ^ m * (1 + X) ^ 4 * (1 + S)
      ≤ (c + 1) * (α ^ (-(10 : ℝ)) * (1 + X) ^ 4 * (1 + S)) := by
  have hpow : α ^ m ≤ α ^ (-(10 : ℝ)) := rpow_le_neg_ten_of hα0 hα1 hm
  have hA : 0 ≤ (1 + X) ^ 4 * (1 + S) := mul_nonneg (by positivity) (by linarith)
  have hm10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc c * α ^ m * (1 + X) ^ 4 * (1 + S)
      = c * (α ^ m * ((1 + X) ^ 4 * (1 + S))) := by ring
    _ ≤ c * (α ^ (-(10 : ℝ)) * ((1 + X) ^ 4 * (1 + S))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hA) hc
    _ ≤ (c + 1) * (α ^ (-(10 : ℝ)) * ((1 + X) ^ 4 * (1 + S))) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hm10 hA)
    _ = (c + 1) * (α ^ (-(10 : ℝ)) * (1 + X) ^ 4 * (1 + S)) := by ring

/-- `(1/α)·c·α^{-3}·A ≤ (c+1)·(α^{-10}·A)`. -/
theorem inv_three {α c A : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    (1 / α) * c * α ^ (-(3 : ℝ)) * A ≤ (c + 1) * (α ^ (-(10 : ℝ)) * A) := by
  have hpow : α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ)) = α ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hα0]; norm_num
  have h4 : α ^ (-(4 : ℝ)) ≤ α ^ (-(10 : ℝ)) := rpow_le_neg_ten_of hα0 hα1 (by norm_num)
  have h10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc (1 / α) * c * α ^ (-(3 : ℝ)) * A
      = c * (α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ))) * A := by
        rw [show (1 : ℝ) / α = α ^ (-(1 : ℝ)) from by rw [Real.rpow_neg_one, one_div]]
        ring
    _ = c * α ^ (-(4 : ℝ)) * A := by rw [hpow]
    _ ≤ c * α ^ (-(10 : ℝ)) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hc) hA
    _ ≤ (c + 1) * (α ^ (-(10 : ℝ)) * A) := by
        have hle : c * α ^ (-(10 : ℝ)) ≤ (c + 1) * α ^ (-(10 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) h10
        calc c * α ^ (-(10 : ℝ)) * A = (c * α ^ (-(10 : ℝ))) * A := rfl
          _ ≤ ((c + 1) * α ^ (-(10 : ℝ))) * A := mul_le_mul_of_nonneg_right hle hA
          _ = (c + 1) * (α ^ (-(10 : ℝ)) * A) := by ring

/-- `(1/α)·(c·W)·α^{-3}·A ≤ (c·Cd+1)·(α^{-10}·A)` for `W ≤ Cd·α^e`, `e ≥ 0`. -/
theorem inv_W_three {α c W Cd A e : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hW0 : 0 ≤ W)
    (hW : W ≤ Cd * α ^ e) (hCd : 0 ≤ Cd) (he : 0 ≤ e) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    (1 / α) * (c * W) * α ^ (-(3 : ℝ)) * A ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
  have hpow : α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ)) = α ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hα0]; norm_num
  have hm4 : -10 ≤ e - 4 := by linarith
  have hW4 : W * α ^ (-(4 : ℝ)) ≤ Cd * α ^ (-(10 : ℝ)) := by
    have h1 : W * α ^ (-(4 : ℝ)) ≤ (Cd * α ^ e) * α ^ (-(4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hα0.le _)
    have h2 : (Cd * α ^ e) * α ^ (-(4 : ℝ)) = Cd * α ^ (e - 4) := by
      rw [mul_assoc, ← Real.rpow_add hα0]
      ring_nf
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (rpow_le_neg_ten_of hα0 hα1 hm4) hCd)
  have h10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc (1 / α) * (c * W) * α ^ (-(3 : ℝ)) * A
      = c * (W * (α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ)))) * A := by
        rw [show (1 : ℝ) / α = α ^ (-(1 : ℝ)) from by rw [Real.rpow_neg_one, one_div]]
        ring
    _ = c * (W * α ^ (-(4 : ℝ))) * A := by rw [hpow]
    _ ≤ c * (Cd * α ^ (-(10 : ℝ))) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW4 hc) hA
    _ ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
        have hle : c * (Cd * α ^ (-(10 : ℝ))) ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
          calc c * (Cd * α ^ (-(10 : ℝ))) = (c * Cd) * α ^ (-(10 : ℝ)) := by ring
            _ ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) h10
        calc c * (Cd * α ^ (-(10 : ℝ))) * A
            = (c * (Cd * α ^ (-(10 : ℝ)))) * A := rfl
          _ ≤ ((c * Cd + 1) * α ^ (-(10 : ℝ))) * A := mul_le_mul_of_nonneg_right hle hA
          _ = (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by ring

/-- `c·W·α^{-3}·A ≤ (c·Cd+1)·(α^{-10}·A)` for `W ≤ Cd·α^e`, `e ≥ 0`. -/
theorem W_three {α c W Cd A e : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hW0 : 0 ≤ W)
    (hW : W ≤ Cd * α ^ e) (hCd : 0 ≤ Cd) (he : 0 ≤ e) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    c * W * α ^ (-(3 : ℝ)) * A ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
  have hm3 : -10 ≤ e - 3 := by linarith
  have hW3 : W * α ^ (-(3 : ℝ)) ≤ Cd * α ^ (-(10 : ℝ)) := by
    have h1 : W * α ^ (-(3 : ℝ)) ≤ (Cd * α ^ e) * α ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hα0.le _)
    have h2 : (Cd * α ^ e) * α ^ (-(3 : ℝ)) = Cd * α ^ (e - 3) := by
      rw [mul_assoc, ← Real.rpow_add hα0]
      ring_nf
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (rpow_le_neg_ten_of hα0 hα1 hm3) hCd)
  have h10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc c * W * α ^ (-(3 : ℝ)) * A = c * (W * α ^ (-(3 : ℝ))) * A := by ring
    _ ≤ c * (Cd * α ^ (-(10 : ℝ))) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW3 hc) hA
    _ ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
        have hle : c * (Cd * α ^ (-(10 : ℝ))) ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
          calc c * (Cd * α ^ (-(10 : ℝ))) = (c * Cd) * α ^ (-(10 : ℝ)) := by ring
            _ ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) h10
        calc c * (Cd * α ^ (-(10 : ℝ))) * A
            = (c * (Cd * α ^ (-(10 : ℝ)))) * A := rfl
          _ ≤ ((c * Cd + 1) * α ^ (-(10 : ℝ))) * A := mul_le_mul_of_nonneg_right hle hA
          _ = (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by ring


/-- The standard majorant `α^{-10}·(1+|f|_{ℋ⁴})⁴·(1+|f|²_{ℋ⁶})` of the row. -/
abbrev NFact (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)

/-- The triangle inequality for a seven-fold sum. -/
theorem abs_sum7_le (x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    |x1 + x2 + x3 + x4 + x5 + x6 + x7|
      ≤ |x1| + |x2| + |x3| + |x4| + |x5| + |x6| + |x7| := by
  have h1 := abs_add_le (x1 + x2 + x3 + x4 + x5 + x6) x7
  have h2 := abs_add_le (x1 + x2 + x3 + x4 + x5) x6
  have h3 := abs_add_le (x1 + x2 + x3 + x4) x5
  have h4 := abs_add_le (x1 + x2 + x3) x4
  have h5 := abs_add_le (x1 + x2) x3
  have h6 := abs_add_le x1 x2
  linarith [abs_nonneg x1, abs_nonneg x2, abs_nonneg x3, abs_nonneg x4, abs_nonneg x5,
    abs_nonneg x6, abs_nonneg x7]

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotLeHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The two angular endpoints are null for `volume.restrict Iθ` -/

private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## Nonnegativity of the leaf weights on the closed quadrant -/

private lemma leaf_nonneg_prv {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z _ θ hθ
    rw [Work.FTS.TransportS.leafEta]
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z _ θ _
    rw [Work.FTS.TransportS.leafOne]
    exact sq_nonneg _
  · intro z _ θ hθ
    rw [Work.FTS.TransportS.leafGam]
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## The pointwise domination of a leaf weight by a block weight -/

/-- The two leaf weights of a `D_z`-only slot (`a = 0`) — `leafEta` and `leafOne` — are
dominated by `(Whz)² = w²σ^{-η}`.  (`leafGam` is excluded at `a = 0` by `IsLeafW`, and
rightly so: `w²σ^{-γ} ≤ w²σ^{-η}` is false on the open quadrant since `γ > η`.) -/
private lemma leaf_le_Whz_sq {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a = 0) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
  subst ha
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha1, _⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Whz_sq z θ hs]
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
  · exact absurd ha1 (by omega)

/-- Every leaf weight is dominated by `(Wm)² = w²σ^{-γ}`, the block weight of the mixed
slots.  This is where `γ ≥ η` (`Work.FTS.H2.rpow_eta_le_gam`) is used. -/
private lemma leaf_le_Wm_sq {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
  · rw [Work.FTS.TransportS.leafGam, Work.FTS.H2.hbi_Wm_sq α z θ hs]

/-- **The pointwise slot domination.**  For a leaf weight `ρ` of the slot `a` and any slot
`(a, b)` of order `≤ N`, the weighted slot of any datum `h` is dominated by the
`ℋ^N`-integrand of `h` on the open quadrant. -/
private lemma leaf_dom {α : ℝ} (hα : 0 < α) {N a b : ℕ} (hab : a + b ≤ N)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {h : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α N h z θ := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [Work.Spaces.mixed_zero_right]
    have hb : b ≤ N := by omega
    calc ρ z θ * (Work.Spaces.DzIter b h z θ) ^ 2
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Whz_sq hρ rfl hθ) (sq_nonneg _)
      _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ = (Work.Spaces.DzIter b h z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.H2.Whz_eq]
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α N h z θ b hb
  · have h1 : 1 ≤ a := hpos
    calc ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        ≤ (Work.FTS.H2.Wm α z θ) ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Wm_sq hα hρ hθ) (sq_nonneg _)
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simp only [Work.FTS.H2.Wm]; ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α N h z θ a b h1 hab

/-! ## The single-slot energy bound -/


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.topSlotZLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `topSlotZLe`: the top (`D_z^6`) slot of the `ℋ⁶`-norm

The `ℋ⁶`-integrand of `Work.Spaces.HkIntegrand` contains, for the index `i = 6` of its pure
`D_z`-sum, the summand

  `(D_z^6 f z θ · w z / sin(2θ)^{η/2})² = (w z)² · sin(2θ)^{-η} · (D_z^6 f z θ)²`

(`Work.Spaces.sq_mul_div_rpow`).  Pulling the radial factor `(w z)²` out of the angular
integral shows that the `η`-weighted angular mass of the top radial derivative, against the
radial weight `w²`, is exactly that summand integrated in `θ`; it is therefore dominated
pointwise in `z` by the whole `ℋ⁶`-integrand, and its `z`-integral by `HkSq α 6 f`.  That is
the first conjunct of `topSlotZLe`.  The second conjunct is the same statement without the
angular weight `sin(2θ)^{-η}`; since `sin(2θ) ∈ (0,1]` on the interior of `Iθ` we have
`sin(2θ)^{-η} ≥ 1` there, so the unweighted mass is dominated by the η-weighted one (the two
endpoints of `Iθ` are null), which is the case `q = 0` of the general slot statement below.

Everything is proved for the general slot `∫_θ w(z)² sin(2θ)^{-q} (D_z^j f)²` with
`0 ≤ q ≤ η` and `j ≤ k`, of which the two required instances are `(q,j,k) = (η,6,6)` and
`(0,6,6)`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The a.e. angular domination of a pure `D_z`-slot by the `ℋ^k`-integrand -/


/-! ## Pulling the radial weight out of the angular integral -/



/-! ## The marginal slot estimate -/


/-! ## The requested statement -/


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.gamSliceCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# The `γ`-weighted angular Cauchy–Schwarz inequality `gamSliceCS`

For a datum `f` which is `C^∞` on the open quadrant and honestly in `ℋ⁶`, and for every
`z > 0`, the two angular slices `θ ↦ D_θ f (z,θ)` and `θ ↦ D_z⁵D_θ f (z,θ)` satisfy the
weighted Cauchy–Schwarz inequality

`∫_Iθ sin(2θ)^{-γ}·|D_θf|·|D_z⁵D_θf| ≤ √(∫_Iθ sin(2θ)^{-γ}(D_θf)²)·√(∫_Iθ sin(2θ)^{-γ}(D_z⁵D_θf)²)`

with weight `sin(2θ)^{-γ}`, `γ = gam α`.  This is the slice form of the leaf-`γ` slot estimate of
the level-six rows; it is a *pure* Cauchy–Schwarz statement, the only work being

* the honestness of the two weighted square integrals (extracted from `HkMem α 6 f`: both slots
  `(i,j) = (1,0)` and `(1,5)` occur in `HkIntegrand α 6 f`, and the weight of the slot is
  `w(z)²·sin(2θ)^{-γ}`, so dividing by the (positive) constant `w(z)²` gives integrability of the
  slice weight `sin(2θ)^{-γ}` times the slot square);
* the pointwise identity `√(ρX²)·√(ρY²) = ρ|X||Y|` for `ρ = sin(2θ)^{-γ} ≥ 0`, which identifies
  the Cauchy–Schwarz left-hand side with the target integrand.

Nothing here is lost beyond the Cauchy–Schwarz inequality itself.
-/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_gsc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) > 0` on the open quadrant. -/
private lemma sin_two_pos_gsc {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `(z,θ) ↦ sin(2θ)^{-q}` is continuous on the open quadrant. -/
private lemma continuousOn_sin_rpow_gsc (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_gsc hp)))

/-- The square of the mixed weight factorises: `(w·sin(2θ)^{-γ/2})² = w²·sin(2θ)^{-γ}` on `Iθ`. -/
private lemma Wt_sq_eq_gsc (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- **Cauchy–Schwarz in square-root form on the slice `Iθ`**: for `A`, `B` nonnegative on `Iθ`
and integrable there, `∫_Iθ √A·√B ≤ √(∫_Iθ A)·√(∫_Iθ B)`.  (The nonnegativity is needed only on
`Iθ`, which is all the application has.) -/
private lemma cs_sqrt_le_Iθ_gsc {A B : ℝ → ℝ}
    (hA : IntegrableOn A Work.Spaces.Iθ) (hB : IntegrableOn B Work.Spaces.Iθ)
    (hAnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A θ) (hBnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B θ) :
    (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ))
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ, B θ) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsmA : AEStronglyMeasurable (fun θ => Real.sqrt (A θ))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hsmB : AEStronglyMeasurable (fun θ => Real.sqrt (B θ))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hAe : A =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Real.sqrt (A θ) ^ 2) :=
    (ae_restrict_mem hIθm).mono (fun θ hθ => (Real.sq_sqrt (hAnn θ hθ)).symm)
  have hBe : B =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Real.sqrt (B θ) ^ 2) :=
    (ae_restrict_mem hIθm).mono (fun θ hθ => (Real.sq_sqrt (hBnn θ hθ)).symm)
  have hAq : Integrable (fun θ => Real.sqrt (A θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    (show Integrable A (volume.restrict Work.Spaces.Iθ) from hA).congr hAe
  have hBq : Integrable (fun θ => Real.sqrt (B θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    (show Integrable B (volume.restrict Work.Spaces.Iθ) from hB).congr hBe
  have hAlp : MemLp (fun θ => Real.sqrt (A θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hsmA).mpr hAq
  have hBlp : MemLp (fun θ => Real.sqrt (B θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hsmB).mpr hBq
  have hcs := Work.Spaces.cs_integral hAlp hBlp
  have e1 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, A θ :=
    integral_congr_ae hAe.symm
  have e2 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (B θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, B θ :=
    integral_congr_ae hBe.symm
  rw [e1, e2] at hcs
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ) :=
    integral_nonneg (f := fun θ => Real.sqrt (A θ) * Real.sqrt (B θ))
      (fun θ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hP : 0 ≤ ∫ θ in Work.Spaces.Iθ, A θ := setIntegral_nonneg hIθm hAnn
  have hQ : 0 ≤ ∫ θ in Work.Spaces.Iθ, B θ := setIntegral_nonneg hIθm hBnn
  have hle := (Real.le_sqrt hnn (mul_nonneg hP hQ)).mpr hcs
  rwa [Real.sqrt_mul hP] at hle

theorem gamSliceCS : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
  intro α f hα hα1 hsm hmem z hz
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_gsc hθ
  -- ## Integrability of the two weighted slot squares
  have hslot : ∀ j : ℕ, j ≤ 5 → IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j 1 f z θ) ^ 2) Work.Spaces.Iθ := by
    intro j hj
    -- continuity of the slice integrand on the open quadrant
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j 1 f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_rpow_gsc (Work.Spaces.gam α)).mul
        (((hsm.mixed j 1).forall 0).continuousOn.pow 2)
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j 1 f z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    -- the `w(z)²`-multiple of that integrand is dominated by the `ℋ⁶`-integrand
    have hbig : IntegrableOn (fun θ : ℝ => (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j 1 f z θ) ^ 2)) Work.Spaces.Iθ := by
      refine (hmem.1 z (le_of_lt hz)).mono' (haesm.const_mul ((Work.Spaces.w z) ^ 2)) ?_
      refine ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
      have hs := hsin θ hθ
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j 1 f z θ) ^ 2) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hs _) (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hkey : (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j 1 f z θ) ^ 2) := by
        rw [mul_pow, Wt_sq_eq_gsc α z θ hs]
        ring
      rw [← hkey]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ 1 j le_rfl (by omega)
    -- divide the constant `w(z)² > 0` out
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have hpos : 0 < Work.Spaces.w z := by
        rw [Work.Spaces.w]
        exact div_pos (by positivity) (by positivity)
      exact pow_ne_zero 2 (ne_of_gt hpos)
    refine ((show Integrable _ (volume.restrict Work.Spaces.Iθ) from hbig).const_mul
      (((Work.Spaces.w z) ^ 2)⁻¹)).congr (Eventually.of_forall fun θ => ?_)
    exact inv_mul_cancel_left₀ hw _
  -- ## Cauchy–Schwarz with the pointwise square-root identity
  have hCS := cs_sqrt_le_Iθ_gsc
    (A := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 0 1 f z θ) ^ 2)
    (B := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 5 1 f z θ) ^ 2)
    (hslot 0 (by norm_num)) (hslot 5 (by norm_num))
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (hsin θ hθ) _) (sq_nonneg _))
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (hsin θ hθ) _) (sq_nonneg _))
  refine le_trans (le_of_eq ?_) hCS
  refine setIntegral_congr_fun hIθm (fun θ hθ => ?_)
  have hρnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg (hsin θ hθ) _
  rw [Real.sqrt_mul hρnn, Real.sqrt_mul hρnn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [show (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * |Work.Spaces.mixed 0 1 f z θ|)
        * (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * |Work.Spaces.mixed 5 1 f z θ|)
      = (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) from by ring,
    Real.mul_self_sqrt hρnn]
  ring

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowMulAsm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

set_option quotPrecheck false in
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

/-! ## The pointwise Leibniz majorant -/

/-- **The pointwise majorant of a single slot pairing.**  For `SmoothOpen` functions and a
nonnegative weight, the weighted product `ρ·(D_z^bD_θ^a(f·g))·(D_z^bD_θ^a g)` is dominated by
the Leibniz sum of the products of the absolute values of the individual slots. -/
theorem abs_mixed_mul_le_sum {f g ρ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hρ : 0 ≤ ρ z θ) :
    ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
  have hX := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f g hf hg z θ hz hθ0 hθ1
  have habs : |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|) := by
    rw [hX]
    calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ f z θ
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g z θ)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1),
            |∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (Work.Spaces.mixed b₁ a₁ f z θ
                    * Work.Spaces.mixed (b - b₁) (a - a₁) g z θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ f z θ
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g z θ)| :=
          Finset.sum_le_sum fun a₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (|Work.Spaces.mixed b₁ a₁ f z θ|
                  * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          rw [abs_mul, abs_mul, abs_mul]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose a₁ : ℝ)),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose b₁ : ℝ))]
          try ring_nf
  calc ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      = ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ|
        * |Work.Spaces.mixed b a g z θ| := by rw [abs_mul]; ring
    _ ≤ ρ z θ * (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|))
        * |Work.Spaces.mixed b a g z θ| := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hρ) (abs_nonneg _)
    _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        ring

/-! ## The assembly -/

/-- **The level-six `A · f` coefficient row**, assembled from the Leibniz expansion and the two
per-summand bounds. -/
theorem rowMulAsm
    (hExp : ∀ {f g : ℝ → ℝ → ℝ} (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) IPM →
      (∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) IPM) →
      Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * g z θ) g
        = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2 ∂IPM))
    (hSmall : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
        CoefData α A K0 K4 K6 → DatData α f M →
        a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
          ≤ C * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
    (hLarge : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
        CoefData α A K0 K4 K6 → DatData α f M →
        3 ≤ a₁ + b₁ → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
          ≤ C * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
        CoefData α A K0 K4 K6 → DatData α f M → a + b ≤ 6 →
        Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
          ≤ C * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Ce, hCep, hsmall⟩ := hSmall
  obtain ⟨Cl, hClp, hlarge⟩ := hLarge
  have hC0 : (0 : ℝ) < max Ce Cl := lt_of_lt_of_le hCep (le_max_left _ _)
  refine ⟨64 * max Ce Cl + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := hcoef.sm
  have hA4 : Work.Spaces.HkMem α 4 A := hcoef.h4
  have hA6 : Work.Spaces.HkMem α 6 A := hcoef.h6
  have hAval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0 := hcoef.val
  have hAn4 : Work.FTS.Nonlin.Xn α A ≤ K4 := hcoef.n4
  have hAn6 : Work.Spaces.HkNorm α 6 A ≤ K6 := hcoef.n6
  have hfSm : Work.FTS.EllipticEst.SmoothOpen f := hdat.sm
  have hf6 : Work.Spaces.HkMem α 6 f := hdat.h6
  have hf7 : Work.Spaces.HkMem α 7 f := hdat.h7
  have hfVanish : Work.Spaces.VanishTheta f := hdat.vanish
  have hfAxis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0 := hdat.axis
  have hfBdd : Work.FTS.Nonlin.Xn α f ≤ M := hdat.bdd
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := le_trans (abs_nonneg (A 1 1))
    (hAval 1 1 (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hAn4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hAn6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hfBdd
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN0 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hα3pos : 0 < α ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hα0 _
  set RHS : ℝ := (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) with hRHSdef
  have hRHS0 : 0 ≤ RHS := by
    rw [hRHSdef]
    refine add_nonneg (mul_nonneg (by linarith) (by linarith)) ?_
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  set C0 : ℝ := max Ce Cl with hC0def
  set Kv : ℝ := C0 * α ^ (-(3 : ℝ)) * RHS with hKvdef
  have hKv0 : 0 ≤ Kv := by
    rw [hKvdef]
    exact mul_nonneg (mul_nonneg (le_of_lt hC0) (le_of_lt hα3pos)) hRHS0
  -- the per-summand integrability and bounds
  have hterm : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b → MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM| ≤ Kv := by
    intro a₁ b₁ ha₁ hb₁
    have hle : ∀ Cc : ℝ, Cc ≤ C0 →
        Cc * α ^ (-(3 : ℝ)) * RHS ≤ Kv := by
      intro Cc hCc
      rw [hKvdef, hC0def]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCc (le_of_lt hα3pos)) hRHS0
    by_cases hp : a₁ + b₁ ≤ 2
    · obtain ⟨hint, hbd⟩ :=
        hsmall α hα A f K0 K4 K6 M a b a₁ b₁ ρ hcoef hdat hp ha₁ hb₁ hab hleaf
      exact ⟨hint, le_trans hbd (hle Ce (le_max_left _ _))⟩
    · have hp3 : 3 ≤ a₁ + b₁ := by omega
      obtain ⟨hint, hbd⟩ :=
        hlarge α hα A f K0 K4 K6 M a b a₁ b₁ ρ hcoef hdat hp3 ha₁ hb₁ hab hleaf
      exact ⟨hint, le_trans hbd (hle Cl (le_max_right _ _))⟩
  have hint : ∀ a₁ : ℕ, a₁ ≤ a → ∀ b₁ : ℕ, b₁ ≤ b → MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) IPM :=
    fun a₁ ha₁ b₁ hb₁ => (hterm a₁ b₁ ha₁ hb₁).1
  have hbd : ∀ a₁ : ℕ, a₁ ≤ a → ∀ b₁ : ℕ, b₁ ≤ b →
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM| ≤ Kv :=
    fun a₁ ha₁ b₁ hb₁ => (hterm a₁ b₁ ha₁ hb₁).2
  -- the majorant
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ A p.1 p.2|
              * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
              * |Work.Spaces.mixed b a f p.1 p.2|)) IPM := by
    refine MeasureTheory.integrable_finset_sum _ fun a₁ ha₁ => ?_
    refine MeasureTheory.integrable_finset_sum _ fun b₁ hb₁ => ?_
    have ha₁' : a₁ ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
    have hb₁' : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    refine (((hint a₁ ha₁' b₁ hb₁').abs).const_mul
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))).congr ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * |ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2|
          = ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ A p.1 p.2|
                  * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
                  * |Work.Spaces.mixed b a f p.1 p.2|))
      (fun z θ hz hθ0 hθ1 => by
        simp only [abs_mul,
          abs_of_nonneg (Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z
            ⟨le_of_lt hθ0, le_of_lt hθ1⟩)])] with p hp
    exact hp
  -- integrability of the left-hand integrand
  have hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) IPM := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          rcases hleaf with h | h | ⟨-, h⟩
          · subst h
            simpa [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
          · subst h
            simpa [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
          · subst h
            simpa [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
        have hXcont : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          have hpt : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2),
              Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
                = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
                    ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                      * (Work.Spaces.mixed b₁ a₁ A p.1 p.2
                          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) :=
            fun p hp =>
              Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a A f hAsm hfSm
                p.1 p.2 hp.1 hp.2.1 hp.2.2
          refine ContinuousOn.congr ?_ hpt
          refine continuousOn_finset_sum _ fun a₁ _ => ?_
          refine continuousOn_finset_sum _ fun b₁ _ => ?_
          refine ContinuousOn.const_mul ?_ _
          exact ((Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hAsm b₁ a₁).mul
            (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfSm
              (b - b₁) (a - a₁)))
        exact (hρcont.mul hXcont).mul
          (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfSm b a)
      exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    · have hpt : ∀ᵐ p ∂IPM, ‖ρ p.1 p.2
            * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2‖
          ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ A p.1 p.2|
                    * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
                    * |Work.Spaces.mixed b a f p.1 p.2|) :=
        Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ0 hθ1 => by
          rw [Real.norm_eq_abs]
          have hρnn : 0 ≤ ρ z θ :=
            Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z ⟨le_of_lt hθ0, le_of_lt hθ1⟩
          have hlhs : |ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                * Work.Spaces.mixed b a f z θ|
              = ρ z θ * |Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                * Work.Spaces.mixed b a f z θ| := by
            rw [show ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                  * Work.Spaces.mixed b a f z θ
                = ρ z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                  * Work.Spaces.mixed b a f z θ) from by ring,
              abs_mul, abs_of_nonneg hρnn]
          rw [hlhs]
          exact abs_mixed_mul_le_sum hAsm hfSm a b hz hθ0 hθ1 hρnn
      filter_upwards [hpt] with p hp
      exact hp
  rw [hExp a b ρ hAsm hfSm hXY hint]
  have hbnd : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b →
      |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
        * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)|
        ≤ ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv := by
    intro a₁ b₁ ha₁ hb₁
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hbd a₁ ha₁ b₁ hb₁)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hbinom : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
    rw [← Finset.sum_mul_sum]
    congr 1
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 64 := by norm_num
  have hmain : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)| ≤ 64 * Kv := by
    have h1 : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)| :=
          Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)|)
        ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv := by
      refine Finset.sum_le_sum fun a₁ ha₁ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun b₁ hb₁ => hbnd a₁ b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))
    have h3 : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv)
        = (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) * Kv := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_mul]
    refine (h1.trans h2).trans ?_
    rw [h3, hbinom]
    exact mul_le_mul_of_nonneg_right hpow hKv0
  refine le_trans hmain ?_
  have hα3R0 : 0 ≤ α ^ (-(3 : ℝ)) * RHS := mul_nonneg (le_of_lt hα3pos) hRHS0
  have hstep : (64 : ℝ) * Kv = (64 * C0) * (α ^ (-(3 : ℝ)) * RHS) := by
    rw [hKvdef]; ring
  rw [hstep, hC0def]
  have h2 : (64 * max Ce Cl) * (α ^ (-(3 : ℝ)) * RHS)
      ≤ (64 * max Ce Cl + 1) * (α ^ (-(3 : ℝ)) * RHS) :=
    mul_le_mul_of_nonneg_right (by linarith) hα3R0
  have h3 : (64 * max Ce Cl + 1) * (α ^ (-(3 : ℝ)) * RHS)
      = (64 * max Ce Cl + 1) * α ^ (-(3 : ℝ)) * RHS := by ring
  rw [h3] at h2
  exact h2

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- The open interval `(0,π/2)` is conull in `Iθ = [0,π/2]`: it differs from `Iθ` only at the
two endpoints. -/
private theorem xProdIntLe_ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- **The pure `D_z`-slot comparison.**  For an interior angle (`sin 2θ > 0`) the weighted
square `w(z)²(D_z^iA)²` is dominated by the `ℋ⁶`-integrand, because `sin(2θ)^{-η} ≥ 1` there
and the weighted square `(D_z^iA · w/sin(2θ)^{η/2})²` is one of the summands of `HkIntegrand`. -/
private theorem xProdIntLe_w_sq_dzIter_sq_le (α : ℝ) (A : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter i A z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
  have h1 := Work.Spaces.sq_le_HkIntegrand_z α 6 A z θ i hi
  have hid : (Work.Spaces.DzIter i A z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i A z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.sq_mul_div_rpow (Work.Spaces.DzIter i A z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) Work.Spaces.eta (le_of_lt hsin) (by norm_num [Work.Spaces.eta])
  rw [hid] at h1
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one (2 * θ))
      (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
    simpa using h
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter i A z θ) ^ 2
      = (Work.Spaces.DzIter i A z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter i A z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (by positivity) hone
    _ ≤ Work.Spaces.HkIntegrand α 6 A z θ := h1

/-- **The mixed-slot comparison.**  The weighted square `w(z)² sin(2θ)^{-γ}(D_z^5D_θA)²` is
exactly the square of the `(i,j) = (1,5)` summand of `HkIntegrand` (all angles, the boundary
values being `0` on both sides), hence is dominated by the whole integrand. -/
private theorem xProdIntLe_w_sq_mixed_sq_le (α : ℝ) (A : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
      ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
  have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α 6 A z θ 1 5 (le_refl 1) (by norm_num)
  have hs2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hsin,
      show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) = -(Work.Spaces.gam α) by ring]
  have hid : (Work.Spaces.mixed 5 1 A z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 A z θ) ^ 2) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hs2]
    ring
  rwa [hid] at h1

/-- **The pointwise-in-`z` comparison**: for `z ∈ Iz` the `θ`-integrated combination of the two
angular averages is dominated by the `θ`-integral of the whole `ℋ⁶`-integrand, with the same
coefficients `4/π` and `200/(γ-1)`. -/
private theorem xProdIntLe_key (α : ℝ) (A : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α 6 A) :
    ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2))
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ) := by
  have hgam : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  have h200 : 0 ≤ 200 / (Work.Spaces.gam α - 1) := by rw [hgam]; positivity
  have h4pi : 0 ≤ 4 / Real.pi := by positivity
  have hIoo := xProdIntLe_ae_mem_Ioo_Iθ
  intro z hz
  have hstep1 : (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmem.1 z hz) ?_
    filter_upwards [hIoo] with θ hθ
    exact xProdIntLe_w_sq_dzIter_sq_le α A
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
      5 (by norm_num)
  have hstep2 : (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      exact mul_nonneg (sq_nonneg _) (mul_nonneg
        (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _))
    · filter_upwards [hIoo] with θ hθ
      exact xProdIntLe_w_sq_mixed_sq_le α A
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  calc (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2))
      = (4 / Real.pi) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2))
        + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2)) := by ring
    _ ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
        + (200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ) :=
        add_le_add (mul_le_mul_of_nonneg_left hstep1 h4pi)
          (mul_le_mul_of_nonneg_left hstep2 h200)
    _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ) := by ring

/-- The two angular averages are a.e. strongly measurable functions of `z` on `Iz`: each is the
`θ`-integral of a function continuous on the open quadrant `(0,∞) × (0,π/2)`, and that quadrant
is conull inside `Iz × Iθ`. -/
private theorem xProdIntLe_aesm_averages (α : ℝ) (A : ℝ → ℝ → ℝ)
    (hso : Work.FTS.EllipticEst.SmoothOpen A) :
    AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) ∧
      AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) := by
  have hsin : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  refine ⟨?_, ?_⟩
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 5 A p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := ((hso.DzIter 5).forall 0).continuousOn.pow 2
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 A p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsin p hp)))).mul
        (((hso.mixed 5 1).forall 0).continuousOn.pow 2)
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- The radial weight `w(z)²` is measurable (division by `z²` is measurable on `ℝ`); it is the
only `z`-dependent factor besides the two angular averages. -/
private theorem xProdIntLe_aesm_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
  have hmeas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    rw [show (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 from by funext z; rfl]
    fun_prop
  exact hmeas.aestronglyMeasurable

theorem xProdIntLe : ∀ (α : ℝ) (A : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 6 A →
    MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z, (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 6 A := by
  intro α A hα hα1 hso hmem
  have hgam : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  have h200 : 0 ≤ 200 / (Work.Spaces.gam α - 1) := by rw [hgam]; positivity
  have h4pi : 0 ≤ 4 / Real.pi := by positivity
  have hkey := xProdIntLe_key α A hα hmem
  have hsinNN : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- nonnegativity of the integrand
  have hGnn : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2
      * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 A z θ) ^ 2)) := by
    intro z
    refine mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg h4pi ?_) (mul_nonneg h200 ?_))
    · exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    · exact MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
          mul_nonneg (Real.rpow_nonneg (hsinNN θ hθ) _) (sq_nonneg _))
  -- the dominating integrable function
  have hdom : MeasureTheory.Integrable (fun z : ℝ =>
      (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
  obtain ⟨haesm1, haesm2⟩ := xProdIntLe_aesm_averages α A hso
  have haesmW := xProdIntLe_aesm_w_sq
  constructor
  · refine MeasureTheory.Integrable.mono' hdom (haesmW.mul ?_) ?_
    · exact (haesm1.const_mul (4 / Real.pi)).add
        (haesm2.const_mul (200 / (Work.Spaces.gam α - 1)))
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rw [Real.norm_of_nonneg (hGnn z)]
      exact hkey z hz
  · have hmono := MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall hGnn) hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hkey)
    rw [MeasureTheory.integral_const_mul] at hmono
    rw [Work.Spaces.HkSq]
    exact hmono

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open MeasureTheory

/-- Cauchy–Schwarz for square roots of nonnegative integrable functions. -/
theorem cs_sqrt_int {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β} {A B : β → ℝ}
    (hA : MeasureTheory.Integrable A μ) (hB : MeasureTheory.Integrable B μ)
    (hAnn : 0 ≤ᵐ[μ] A) (hBnn : 0 ≤ᵐ[μ] B) :
    MeasureTheory.Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x)) μ ∧
      (∫ x, Real.sqrt (A x) * Real.sqrt (B x) ∂μ)
        ≤ Real.sqrt (∫ x, A x ∂μ) * Real.sqrt (∫ x, B x ∂μ) := by
  -- `√A` and `√B` are `L²` functions, so their product is `L¹` (Hölder with `p = q = 2`).
  have hsmA : AEStronglyMeasurable (fun x => Real.sqrt (A x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hsmB : AEStronglyMeasurable (fun x => Real.sqrt (B x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hsqA : (fun x => Real.sqrt (A x) ^ 2) =ᵐ[μ] A := by
    filter_upwards [hAnn] with x hx
    exact Real.sq_sqrt hx
  have hsqB : (fun x => Real.sqrt (B x) ^ 2) =ᵐ[μ] B := by
    filter_upwards [hBnn] with x hx
    exact Real.sq_sqrt hx
  -- the same statement for the real power `(·) ^ (2 : ℝ)`, used by the `Lp` machinery
  have hsqAr : (fun x => Real.sqrt (A x) ^ (2 : ℝ)) =ᵐ[μ] A := by
    filter_upwards [hsqA] with x hx
    rwa [Real.rpow_two]
  have hsqBr : (fun x => Real.sqrt (B x) ^ (2 : ℝ)) =ᵐ[μ] B := by
    filter_upwards [hsqB] with x hx
    rwa [Real.rpow_two]
  have hmemA : MemLp (fun x => Real.sqrt (A x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsmA).2 (hA.congr hsqA.symm)
  have hmemB : MemLp (fun x => Real.sqrt (B x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsmB).2 (hB.congr hsqB.symm)
  have hmemA' : MemLp (fun x => Real.sqrt (A x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hmemA
  have hmemB' : MemLp (fun x => Real.sqrt (B x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hmemB
  have hnnA : 0 ≤ᵐ[μ] fun x => Real.sqrt (A x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hnnB : 0 ≤ᵐ[μ] fun x => Real.sqrt (B x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hnnA hnnB hmemA' hmemB'
  have heqA : (∫ x, Real.sqrt (A x) ^ (2 : ℝ) ∂μ) = ∫ x, A x ∂μ := integral_congr_ae hsqAr
  have heqB : (∫ x, Real.sqrt (B x) ^ (2 : ℝ) ∂μ) = ∫ x, B x ∂μ := integral_congr_ae hsqBr
  have hInt : Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x)) μ :=
    (hmemA.integrable_mul hmemB).congr (Filter.Eventually.of_forall fun x => rfl)
  have hstep : (∫ x, Real.sqrt (A x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        * (∫ x, Real.sqrt (B x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      = Real.sqrt (∫ x, A x ∂μ) * Real.sqrt (∫ x, B x ∂μ) := by
    rw [heqA, heqB, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact ⟨hInt, hholder.trans_eq hstep⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA4_WlInf6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `𝒲^{6,∞}`-data of the coefficient `(3/(2α))·D_θF_*`

The `A₄`-coefficient of the `N₀`-row is `A₄ = (3/(2α))·D_θ(F_*)`.  The scaled
profile `D_θ(F_*)` is already known to lie in `𝒲^{6,∞}` with norm `≤ C α²`
(`Work.FTS.StrongPersist.DthFstar_W6`), so the present lemma is the bookkeeping
which (a) records the smoothness on the open quadrant and (b) transports the
`𝒲^{6,∞}`-membership and the norm through the scalar factor `3/(2α)`:

* `SmoothOpen (D_θF_*)` comes from `SmoothQuad_Fstar` (`D_θ` preserves the class,
  open-quadrant version) and multiplication by a constant;
* `WlInfMem α 6` is transported by the elementary scaling lemmas
  `WlInfMem_const_mul'`/`WlInf_const_mul_le` below (the iterated operators commute
  with scalar multiplication — `deriv_const_mul_field` is unconditional);
* the norm `(3/(2α))·(C α²) = (3C/2)·α` is `α`-linear, as required.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.Spaces
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Smoothness on the open quadrant -/


/-- `SmoothOpen` is stable under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  exact contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf n)

/-! ## Scalar multiplication commutes with the iterated operators

`deriv_const_mul` needs differentiability, but `deriv_const_mul_field` is
unconditional (the junk value `0` is compatible with scalar multiplication), which is
what makes these two identities valid for an arbitrary `f`. -/

theorem pzIter_const_mul' (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz]
      exact deriv_const_mul_field c

theorem DthIter_const_mul' (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field c]
      ring

/-! ## Scaling the suprema and the `𝒲^{l,∞}`-data -/

theorem SupFinite_const_mul {g : ℝ → ℝ → ℝ} (c : ℝ) (h : SupFinite g) :
    SupFinite (fun z θ => c * g z θ) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨|c| * M, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM ⟨z, hz, θ, hθ, rfl⟩) (abs_nonneg c)

theorem SupFinite_congr {g h : ℝ → ℝ → ℝ} (hgh : ∀ z θ, g z θ = h z θ) (hg : SupFinite g) :
    SupFinite h := by
  obtain ⟨M, hM⟩ := hg
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  rw [← hgh z θ]
  exact hM ⟨z, hz, θ, hθ, rfl⟩



/-- Membership in `𝒲^{l,∞}` is preserved by scalar multiplication. -/
theorem WlInfMem_const_mul' {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (c : ℝ)
    (hmem : WlInfMem α l f) :
    WlInfMem α l (fun z θ => c * f z θ) := by
  refine ⟨fun k hk => ?_, fun j hj k hk hj1 hjk => ?_⟩
  · refine SupFinite_congr (fun z θ => ?_) (SupFinite_const_mul c (hmem.1 k hk))
    rw [pzIter_const_mul']
    ring
  · refine SupFinite_congr (fun z θ => ?_) (SupFinite_const_mul c (hmem.2 j hj k hk hj1 hjk))
    rw [DthIter_const_mul', pzIter_const_mul']
    ring


/-! ## The requested statement -/


end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.NZarith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/NZarith` — the numeric step of the `N`-zero-mode estimate

The final arithmetic of `NZzero6`: the `ℝ`-inequality

`9·Kcoef α M Ce Cs Cp Cu Cag · (6·(√(π/2)·M + Cf·α))
   ≤ K · (1+|Ce|+|Cs|)⁴ · α^{-9} · (1+M)⁴`

with `K := 54000·(Cp+Cu+Cag+Cf+1)·(√(π/2)+Cf+1) + 1`.  It is isolated here (rather than
inlined in `NZzero6`) because the surrounding declaration is heartbeat-limited: this way the
`ring`/`nlinarith` work happens in a small context.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The numeric step of the zero-mode estimate.** -/
theorem NZ_arith {α M Ce Cs Cp Cu Cag Cf : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M) (hCf : 0 < Cf)
    (hCp : 0 < Cp) (hCu : 0 < Cu) (hCag : 0 < Cag) :
    9 * Kcoef α M Ce Cs Cp Cu Cag * (6 * (Real.sqrt (Real.pi / 2) * M + Cf * α))
      ≤ (54000 * (Cp + Cu + Cag + Cf + 1) * (Real.sqrt (Real.pi / 2) + Cf + 1) + 1)
          * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  set X : ℝ := 1 + |Ce| + |Cs| with hX
  set B : ℝ := 1 + M with hB
  set P : ℝ := α ^ (-(9 : ℝ)) with hP
  set Cc : ℝ := Real.sqrt (Real.pi / 2) + Cf + 1 with hCc
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  -- the unfolding of `Kcoef`
  have hK : Kcoef α M Ce Cs Cp Cu Cag = 1000 * (Cp + Cu + Cag + 1) * X * α ^ (-(1 / 2 : ℝ)) * B := by
    rw [Kcoef, hX, hB]
  -- the elementary facts
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX]
    have h1 := abs_nonneg Ce
    have h2 := abs_nonneg Cs
    linarith
  have hX0 : (0 : ℝ) ≤ X := le_trans zero_le_one hX1
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; linarith
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hP0 : (0 : ℝ) ≤ P := by rw [hP]; exact Real.rpow_nonneg hα0.le _
  have hRP : α ^ (-(1 / 2 : ℝ)) ≤ P := by
    rw [hP]
    exact Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hCc1 : (1 : ℝ) ≤ Cc := by rw [hCc]; linarith [hsqrt0, hCf.le]
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans zero_le_one hCc1
  have hX4 : X ≤ X ^ 4 := by
    have h2 : (1 : ℝ) ≤ X * X := by
      have h := mul_le_mul hX1 hX1 zero_le_one hX0
      linarith
    have h3 : (1 : ℝ) ≤ X * X * X := by
      have h := mul_le_mul h2 hX1 zero_le_one (mul_nonneg hX0 hX0)
      linarith
    have h4 : (1 : ℝ) ≤ X * X * X * X := by
      have h := mul_le_mul h3 hX1 zero_le_one (mul_nonneg (mul_nonneg hX0 hX0) hX0)
      linarith
    have h5 : X * 1 ≤ X * (X * X * X) := mul_le_mul_of_nonneg_left h3 hX0
    have h6 : X ≤ X * X * X * X := by linarith
    calc X ≤ X * X * X * X := h6
      _ = X ^ 4 := by ring
  have hB4 : B * B ≤ B ^ 4 := by
    have h2 : (1 : ℝ) ≤ B * B := by
      have h := mul_le_mul hB1 hB1 zero_le_one hB0
      linarith
    have h3 : B * B ≤ (B * B) * (B * B) := by
      have h := mul_le_mul_of_nonneg_left h2 (mul_nonneg hB0 hB0)
      simpa using h
    calc B * B ≤ (B * B) * (B * B) := h3
      _ = B ^ 4 := by ring
  -- the datum factor
  have hc : Real.sqrt (Real.pi / 2) * M + Cf * α ≤ Cc * B := by
    rw [hCc, hB]
    have h1 : Real.sqrt (Real.pi / 2) * M ≤ Real.sqrt (Real.pi / 2) * (1 + M) :=
      mul_le_mul_of_nonneg_left (by linarith) hsqrt0
    have h2 : Cf * α ≤ Cf := mul_le_of_le_one_right hCf.le hα1
    have h3 : Cf ≤ Cf * (1 + M) := le_mul_of_one_le_right hCf.le (by linarith)
    nlinarith [h1, h2, h3, hsqrt0, hCf.le, hM0]
  -- the key product inequality
  have hkey : X * (α ^ (-(1 / 2 : ℝ)) * (B * (Real.sqrt (Real.pi / 2) * M + Cf * α)))
      ≤ Cc * (X ^ 4 * P * B ^ 4) := by
    have hbc : B * (Real.sqrt (Real.pi / 2) * M + Cf * α) ≤ B * (Cc * B) :=
      mul_le_mul_of_nonneg_left hc hB0
    have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
    have hinner : X * (α ^ (-(1 / 2 : ℝ)) * (B * B)) ≤ X ^ 4 * (P * B ^ 4) := by
      have h1 : X * (α ^ (-(1 / 2 : ℝ)) * (B * B))
          ≤ X ^ 4 * (α ^ (-(1 / 2 : ℝ)) * (B * B)) :=
        mul_le_mul_of_nonneg_right hX4 (mul_nonneg hr0 (mul_nonneg hB0 hB0))
      have h2 : X ^ 4 * (α ^ (-(1 / 2 : ℝ)) * (B * B)) ≤ X ^ 4 * (P * (B * B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRP (mul_nonneg hB0 hB0))
          (pow_nonneg hX0 4)
      have h3 : X ^ 4 * (P * (B * B)) ≤ X ^ 4 * (P * B ^ 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB4 hP0) (pow_nonneg hX0 4)
      exact le_trans h1 (le_trans h2 h3)
    calc X * (α ^ (-(1 / 2 : ℝ)) * (B * (Real.sqrt (Real.pi / 2) * M + Cf * α)))
        ≤ X * (α ^ (-(1 / 2 : ℝ)) * (B * (Cc * B))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbc hr0) hX0
      _ = Cc * (X * (α ^ (-(1 / 2 : ℝ)) * (B * B))) := by ring
      _ ≤ Cc * (X ^ 4 * (P * B ^ 4)) := mul_le_mul_of_nonneg_left hinner hCc0
      _ = Cc * (X ^ 4 * P * B ^ 4) := by ring
  -- the coefficient bookkeeping
  have hA : Cp + Cu + Cag + 1 ≤ Cp + Cu + Cag + Cf + 1 := by linarith
  have hA0 : (0 : ℝ) ≤ 54000 * (Cp + Cu + Cag + 1) := by linarith
  have hQ0 : (0 : ℝ) ≤ X ^ 4 * P * B ^ 4 :=
    mul_nonneg (mul_nonneg (pow_nonneg hX0 4) hP0) (pow_nonneg hB0 4)
  rw [hK]
  calc 9 * (1000 * (Cp + Cu + Cag + 1) * X * α ^ (-(1 / 2 : ℝ)) * B)
        * (6 * (Real.sqrt (Real.pi / 2) * M + Cf * α))
      = 54000 * (Cp + Cu + Cag + 1)
          * (X * (α ^ (-(1 / 2 : ℝ)) * (B * (Real.sqrt (Real.pi / 2) * M + Cf * α)))) := by
        ring
    _ ≤ 54000 * (Cp + Cu + Cag + 1) * (Cc * (X ^ 4 * P * B ^ 4)) :=
        mul_le_mul_of_nonneg_left hkey hA0
    _ ≤ 54000 * (Cp + Cu + Cag + Cf + 1) * (Cc * (X ^ 4 * P * B ^ 4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_nonneg hCc0 hQ0)
    _ ≤ (54000 * (Cp + Cu + Cag + Cf + 1) * Cc + 1) * (X ^ 4 * P * B ^ 4) := by
        have h0 : (0 : ℝ) ≤ 54000 * (Cp + Cu + Cag + Cf + 1) * Cc := by
          have h1 : (0 : ℝ) ≤ Cp + Cu + Cag + Cf + 1 := by linarith
          positivity
        have hstep : 54000 * (Cp + Cu + Cag + Cf + 1) * (Cc * (X ^ 4 * P * B ^ 4))
            = (54000 * (Cp + Cu + Cag + Cf + 1) * Cc) * (X ^ 4 * P * B ^ 4) := by ring
        rw [hstep]
        exact mul_le_mul_of_nonneg_right (by linarith) hQ0
    _ = (54000 * (Cp + Cu + Cag + Cf + 1) * Cc + 1) * X ^ 4 * P * B ^ 4 := by ring

end Work.FTS.StrongPersist.H6Rows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.PtBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/PtBound` — the pointwise bound of the `N`-zero-mode estimate

From the four coefficient majorants (`NZaux/NZ_coefs`), the five terms of `N` are dominated
pointwise on the open quadrant by `9·Kcoef` times the sum of the six slots.
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

/-- **The pointwise bound of the five terms of `N`.**  On the open quadrant `|K θ·N|` is
dominated by `9·Kcoef` times the sum of the six slots. -/
theorem NZ_pt {α M Ce Cs : ℝ} {f Ef Φs : Fn} {Cp Cu Cag : ℝ} {z θ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M) (hCp : 0 < Cp) (hCu : 0 < Cu)
    (hCag : 0 < Cag) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2)
    (hRle : |Work.Construction.Rop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag)
    (hUle : |Work.Construction.Uop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag)
    (hVle : |Work.Construction.Vop (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag)
    (hFKle : |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ Kcoef α M Ce Cs Cp Cu Cag) :
    |Work.Spaces.K θ * Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ) z θ|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag * (∑ j : Fin 6, |slots α f j z θ|) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
  -- =============== 5. the algebra and the pointwise bound
  have hKc0 : 0 ≤ Kcoef α M Ce Cs Cp Cu Cag := (Kcoef_pos hα0 hCp hCu hCag hM0).le
  have hs2ne : Work.Construction.s2 θ ≠ 0 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ, Real.pi_pos])
      (by linarith [hθ2, Real.pi_pos]))
  have hK3 : |Work.Spaces.K θ| ≤ 3 :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have hratio : Work.Spaces.K θ / Work.Construction.s2 θ = (3 / 2) * Real.cos θ := by
    have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
      rw [Work.Spaces.K, Real.sin_two_mul]; ring
    have hs2' : Real.sin (2 * θ) ≠ 0 := hs2ne
    rw [hK, show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact mul_div_cancel_right₀ _ hs2'
  have hc1 : |Work.Spaces.K θ * (2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        - (Real.sin θ) ^ 2 * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
    have hsin : (Real.sin θ) ^ 2 ≤ 1 :=
      pow_le_one₀ (Real.sin_nonneg_of_mem_Icc ⟨hθ.le, by linarith [Real.pi_pos]⟩)
        (Real.sin_le_one θ)
    have h2 : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ|
        ≤ 2 * Kcoef α M Ce Cs Cp Cu Cag := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hRle (by norm_num)
    have h3 : |(Real.sin θ) ^ 2 * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ Kcoef α M Ce Cs Cp Cu Cag := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
      exact le_trans (mul_le_mul_of_nonneg_right hsin (abs_nonneg _)) (by simpa using hFKle)
    have hX : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by
      calc |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
          ≤ |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|
            + |(Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z| := by
            have h := abs_add_le (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ)
              (-((Real.sin θ) ^ 2 * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            simpa only [sub_eq_add_neg, abs_neg] using h
        _ ≤ 2 * Kcoef α M Ce Cs Cp Cu Cag + Kcoef α M Ce Cs Cp Cu Cag := add_le_add h2 h3
        _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
    rw [abs_mul]
    calc |Work.Spaces.K θ| * |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ 3 * (3 * Kcoef α M Ce Cs Cp Cu Cag) :=
          mul_le_mul hK3 hX (abs_nonneg _) (by norm_num)
      _ = 9 * Kcoef α M Ce Cs Cp Cu Cag := by ring
  have hc2 : |Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
          + (1 / 2) * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
    have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hsplit : Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
          + (1 / 2) * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
        = (Work.Spaces.K θ / Work.Construction.s2 θ)
            * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
          + (-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))) := by
      field_simp
      ring
    have hA : |(Work.Spaces.K θ / Work.Construction.s2 θ)
          * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ))| ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by
      rw [hratio, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2),
        abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc (3 / 2) * |Real.cos θ| * (2 * |Work.Construction.Uop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|)
          ≤ (3 / 2) * (2 * Kcoef α M Ce Cs Cp Cu Cag) := by
            refine mul_le_mul (by linarith [hcos])
              (mul_le_mul_of_nonneg_left hUle (by norm_num)) (by positivity) (by norm_num)
        _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
    have hB : |-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))|
        ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc |Work.Spaces.K θ| * ((1 / 2) * |Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|)
          ≤ 3 * ((1 / 2) * Kcoef α M Ce Cs Cp Cu Cag) := by
            refine mul_le_mul hK3 (mul_le_mul_of_nonneg_left hFKle (by norm_num))
              (by positivity) (by norm_num)
        _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
    rw [hsplit]
    calc |(Work.Spaces.K θ / Work.Construction.s2 θ)
            * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
          + (-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))|
        ≤ |(Work.Spaces.K θ / Work.Construction.s2 θ)
            * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))|
          + |-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))| := abs_add_le _ _
      _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag + 3 * Kcoef α M Ce Cs Cp Cu Cag := add_le_add hA hB
      _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
  have hc3 : |Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ)| ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
    have e1 : |-(2 * α)| = 2 * α := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hα0.le]
    have e2 : |Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ)|
        = |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ|) := by
      rw [abs_mul, abs_mul, e1]
    rw [e2]
    calc |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|)
        ≤ 3 * (2 * α * Kcoef α M Ce Cs Cp Cu Cag) := by
          refine mul_le_mul hK3 ?_ (by positivity) (by norm_num)
          have h1 : α * |Work.Construction.Vop (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ α * Kcoef α M Ce Cs Cp Cu Cag :=
            mul_le_mul_of_nonneg_left hVle (le_of_lt hα0)
          calc 2 * α * |Work.Construction.Vop (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|
              = 2 * (α * |Work.Construction.Vop (Work.Construction.PhiTil α
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ|) := by ring
            _ ≤ 2 * (α * Kcoef α M Ce Cs Cp Cu Cag) :=
                mul_le_mul_of_nonneg_left h1 (by norm_num)
            _ = 2 * α * Kcoef α M Ce Cs Cp Cu Cag := by ring
      _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
          have h1 : 3 * (2 * α) ≤ 9 := by linarith
          calc 3 * (2 * α * Kcoef α M Ce Cs Cp Cu Cag)
              = (3 * (2 * α)) * Kcoef α M Ce Cs Cp Cu Cag := by ring
            _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := mul_le_mul_of_nonneg_right h1 hKc0
  -- the slot additivity on `F = F_* + f`
  have hDthF : Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ := by
    have hth := Work.FTS.NonlinRows.Rl1.openSlice_pth_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α))
      hso hz ⟨hθ, hθ2⟩
    simp only [Work.Spaces.Dth]
    rw [hth]
    ring
  have hDzF : Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ := by
    have hpz := Work.FTS.NonlinRows.Rl1.openSlice_pz_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α))
      hso hz ⟨hθ, hθ2⟩
    simp only [Work.Spaces.Dz]
    rw [hpz]
    ring
  have hsum6 : (∑ j : Fin 6, |slots α f j z θ|)
      = |f z θ| + |Work.Spaces.Dth f z θ| + |Work.Spaces.Dz f z θ|
        + |Work.Construction.Fstar α z θ| + |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := by
    simp only [slots, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val]
  have hid : Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ) z θ
      = (2 * Work.Construction.Rop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)
        * (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      + (-(2 * (Work.Construction.Uop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
            + (1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
        * Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      + (-(2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ)
        * Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ := by
    have hs2' : Real.sin (2 * θ) ≠ 0 := hs2ne
    simp only [Work.Construction.N, Work.Spaces.Dth, Work.Construction.s2]
    field_simp [hs2']
    ring_nf
  rw [hid, hDthF, hDzF]
  have hexp : Work.Spaces.K θ * ((2 * Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)
        * (Work.Construction.Fstar α z θ + f z θ)
      + (-(2 * (Work.Construction.Uop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
            / Work.Construction.s2 θ)
            + (1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
      + (-(2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ)
          * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ))
      = (Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Construction.Fstar α z θ + f z θ)
        + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
        + (Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ) := by
    ring
  rw [hexp]
  have hT1 : |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        - (Real.sin θ) ^ 2 * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
        * (Work.Construction.Fstar α z θ + f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag * |Work.Construction.Fstar α z θ + f z θ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
  have hT2 : |(Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
        + (1 / 2) * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
        * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag
        * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)
  have hT3 : |(Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ))
        * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag
        * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc3 (abs_nonneg _)
  have htri : |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Construction.Fstar α z θ + f z θ)
        + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
        + (Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)|
      ≤ |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            * (Work.Construction.Fstar α z θ + f z θ)|
        + |(Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)|
        + |(Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)| := by
    have h1 : |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            * (Work.Construction.Fstar α z θ + f z θ)
          + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
                (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
                + (1 / 2) * Work.Construction.FK
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
              * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)|
          ≤ |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
                (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ
                - (Real.sin θ) ^ 2 * Work.Construction.FK
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
                * (Work.Construction.Fstar α z θ + f z θ)|
            + |(Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
                  (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                    (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
                  + (1 / 2) * Work.Construction.FK
                    (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
                * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)| :=
      abs_add_le _ _
    have h2 := abs_add_le ((Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            * (Work.Construction.Fstar α z θ + f z θ)
          + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
                (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
                + (1 / 2) * Work.Construction.FK
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
              * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ))
        ((Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ))
    linarith [h1, h2]
  have hb1 : |Work.Construction.Fstar α z θ + f z θ|
      ≤ |Work.Construction.Fstar α z θ| + |f z θ| := abs_add_le _ _
  have hb2 : |Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ|
      ≤ |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dth f z θ| :=
    abs_add_le _ _
  have hb3 : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ|
      ≤ |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dz f z θ| :=
    abs_add_le _ _
  have h9 : 0 ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by linarith
  calc |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Construction.Fstar α z θ + f z θ)
        + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
        + (Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag * |Work.Construction.Fstar α z θ + f z θ|
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ|
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ| := by
        linarith [htri, hT1, hT2, hT3]
    _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|Work.Construction.Fstar α z θ| + |f z θ|)
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|Work.Spaces.Dth (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dth f z θ|)
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|Work.Spaces.Dz (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dz f z θ|) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_of_nonneg_left hb1 h9
        · exact mul_le_mul_of_nonneg_left hb2 h9
        · exact mul_le_mul_of_nonneg_left hb3 h9
    _ = 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|f z θ| + |Work.Spaces.Dth f z θ| + |Work.Spaces.Dz f z θ|
            + |Work.Construction.Fstar α z θ|
            + |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
            + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|) := by ring
    _ = 9 * Kcoef α M Ce Cs Cp Cu Cag * (∑ j : Fin 6, |slots α f j z θ|) := by rw [hsum6]

end Work.FTS.StrongPersist.H6Rows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (N0fix N03g N04aF N04bF N05aF N05bF N06F
  N1gg N1gs N1sg N1ss N2gg N2gs N2sg N2ss N3gg N3gs N3sg N3ss
  N4gg N4gs N4sg N4ss N5gg N5gs N5sg N5ss MuAK)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The blocks of `N₀` -/

/-- The `g`-dependent block of `N₀`: rows 2--7 of the paper's table, at the profile `F = F_*+f`. -/
def N0gSum (α : ℝ) (f : Fn) : Fn := fun z θ =>
  N03g α f z θ + N04aF α f z θ + N04bF α f z θ
    + N05aF α f z θ + N05bF α f z θ + N06F α f z θ

/-! ## The blocks of `N` -/

/-- The pure-star block of `N`: `N₁^{ss} + N₂^{ss} + N₃^{ss} + N₄^{ss} + N₅^{ss}`
(the terms in which the elliptic residual and the transported profile are both the star ones).
`N₄^{ss}`, `N₅^{ss}` depend on `α` only. -/
def NSsSum (α : ℝ) (Φs : Fn) : Fn := fun z θ =>
  N1ss α Φs z θ + N2ss α Φs z θ + N3ss α Φs z θ + N4ss α z θ + N5ss α z θ

/-- The block of `N` in which the *star* elliptic residual is transported by the modulation:
`N₁^{sg} + N₂^{sg} + N₃^{sg}`. -/
def NSgSum (α : ℝ) (Φs f : Fn) : Fn := fun z θ =>
  N1sg α Φs f z θ + N2sg α Φs f z θ + N3sg α Φs f z θ

/-- The block of `N` in which the *perturbation* elliptic residual multiplies `F_*`:
`N₁^{gs} + N₂^{gs} + N₃^{gs}`. -/
def NGsSum (α : ℝ) (f Φg : Fn) : Fn := fun z θ =>
  N1gs α f Φg z θ + N2gs α f Φg z θ + N3gs α f Φg z θ

/-- The block of `N` in which the *perturbation* elliptic residual is transported by the
modulation: `N₁^{gg} + N₂^{gg} + N₃^{gg}`. -/
def NGgSum (α : ℝ) (f Φg : Fn) : Fn := fun z θ =>
  N1gg α f Φg z θ + N2gg α f Φg z θ + N3gg α f Φg z θ

/-- The angular-moment block of `N`: the six terms in which the factor `FK F = FK F_* + FK f`
occurs (`N₄^{gg}, N₅^{gg}, N₄^{gs}, N₅^{gs}, N₄^{sg}, N₅^{sg}`). -/
def NFkSum (α : ℝ) (f : Fn) : Fn := fun z θ =>
  N4gg α f z θ + N5gg f z θ + N4gs α f z θ + N5gs α f z θ + N4sg α f z θ + N5sg α f z θ


end Work.FTS.StrongPersist.L3Rhs
end
end
