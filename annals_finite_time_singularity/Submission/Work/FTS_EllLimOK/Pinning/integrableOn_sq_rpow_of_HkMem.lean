import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.ClassC.HkMem_of_plain_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Local helpers

The reduction `HkMem α k f` from the *plain* slots `D_z^j f` and `D_z^j ∂_θ^r f` rests on one
pointwise estimate: on the open quadrant the mixed derivative `D_z^j D_θ^i f` (`i ≥ 1`) is a
`θ`-dependent linear combination of the plain slots `D_z^j ∂_θ^r f`, `1 ≤ r ≤ i`, whose
coefficients satisfy `|a_{i,r}(θ)| ≤ K_r sin(2θ)^r`.  The conormal factor `sin(2θ)^r` with
`r ≥ 1` pays for the difference between the `γ`-weight of the mixed slot and the `η`-weight of
the plain slots: `sin(2θ)^{r-γ/2} ≤ sin(2θ)^{-η/2}` as soon as `r ≥ (γ-η)/2`, which holds
because `r ≥ 1` and `γ ≤ 3/2`.  This gives the required domination. -/

/-- The level-`0` `ℋ^k`-integrand collapses to the square of the `η`-weighted profile. -/
theorem HkIntegrand_zero_eq_classC (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- If the product weight `Wt α z θ` does not vanish at a point of `Iz × Iθ`, then that point
lies in the open quadrant. -/
theorem Wt_ne_zero_quadrant {α z θ : ℝ} (hα : 0 < α) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) (h : Work.Spaces.Wt α z θ ≠ 0) :
    0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  have hz0 : 0 ≤ z := hz
  have hθI : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
  have hw : Work.Spaces.w z ≠ 0 := fun hw0 => h (by rw [Work.Spaces.Wt, hw0, zero_mul])
  have hwt : Work.Spaces.wTheta α θ ≠ 0 := fun h0 => h (by rw [Work.Spaces.Wt, h0, mul_zero])
  have hzpos : 0 < z := by
    rcases lt_or_eq_of_le hz0 with h' | h'
    · exact h'
    · exfalso; apply hw; rw [← h']; simp [Work.Spaces.w]
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    intro hs0
    apply hwt
    rw [Work.Spaces.wTheta, hs0]
    refine Real.zero_rpow ?_
    have hγ : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    intro hc
    linarith
  refine ⟨hzpos, ?_, ?_⟩
  · rcases lt_or_eq_of_le hθI.1 with h' | h'
    · exact h'
    · exact absurd (by rw [← h']; simp) hsin
  · rcases lt_or_eq_of_le hθI.2 with h' | h'
    · exact h'
    · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hsin

/-- `SmoothOpen` is preserved by the iterates of `∂_θ`. -/
theorem SmoothOpen_pthIter_classC {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (r : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter r f) := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- The expansion of `D_θ^i f` in the plain angular basis, at each point of the open
quadrant, for `f` which is `C^∞` there. -/
theorem dthCoef_expansion_Q0 {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i f z θ
        = ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
              * Work.Spaces.pthIter r f z θ := by
  intro z θ hz hθ0 hθ1
  refine Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local i f z θ ?_
  intro n
  exact (hsm.forall n).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))

/-- **The mixed derivative in the plain angular basis.**  On the open quadrant,
`D_z^j D_θ^{m+1} f = Σ_{1 ≤ r ≤ m+1} a_{m+1,r}(θ) · D_z^j ∂_θ^r f`, a linear combination of the
plain slots with `θ`-only coefficients (the `r = 0` term of the expansion of `D_θ^{m+1}`
vanishes). -/
theorem mixed_eq_sum_dthCoef_succ {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (m j : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j (m + 1) f z θ
        = ∑ r ∈ Finset.Icc 1 (m + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
              * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ := by
  intro z θ hz hθ0 hθ1
  have hexp := dthCoef_expansion_Q0 hsm (m + 1)
  have h1 : Work.Spaces.DzIter j (Work.Spaces.DthIter (m + 1) f) z θ
      = Work.Spaces.DzIter j (fun z θ => ∑ r ∈ Finset.range (m + 2),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.pthIter r f z θ) z θ :=
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter (m + 1) f)
      (G := fun z θ => ∑ r ∈ Finset.range (m + 2),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.pthIter r f z θ)
      (fun z' θ' hz' hθ0' hθ1' => hexp z' θ' hz' hθ0' hθ1') j z θ hz hθ0 hθ1
  have h2 : Work.Spaces.DzIter j (fun z θ => ∑ r ∈ Finset.range (m + 2),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
          * Work.Spaces.pthIter r f z θ) z θ
      = ∑ r ∈ Finset.range (m + 2),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ :=
    Work.FTS.H2.STQ.DzIter_sum_theta_coeff_eqOn (Finset.range (m + 2))
      (fun r θ => Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ)
      (fun r => Work.Spaces.pthIter r f) Work.FTS.EllipticEst.isOpen_Q0
      (fun r _ => SmoothOpen_pthIter_classC hsm r) j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
  have h3 : (∑ r ∈ Finset.range (m + 2),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
          * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ)
      = ∑ r ∈ Finset.Icc 1 (m + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ :=
    Work.FTS.EllipticEst.remov.Baux.sum_range_succ_eq_sum_Icc m _ (by
      have h0 : Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) 0 θ = 0 := by
        have h := congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_succ_zero m) θ
        simpa using h
      show Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) 0 θ
          * Work.Spaces.DzIter j (Work.Spaces.pthIter 0 f) z θ = 0
      rw [h0, zero_mul])
  show Work.Spaces.DzIter j (Work.Spaces.DthIter (m + 1) f) z θ = _
  rw [h1, h2, h3]



/-! ## The constant attached to a mixed slot -/




/-! ## The assembly -/


end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkSq_pth_grad`

The level-`0` square of the `ℋ`-norm of the angular derivative of the radial gradient
`U u = z ∂_z u` equals the iterated integral of `(V u)²σ`, where `V u = z ∂_z∂_θu` and
`σ = sigE = sin(2θ)^{-η}`:

  `HkSq α 0 (∂_θ(z∂_zu)) = ∫_z w(z)² ∫_θ (V u z θ)² σ(θ)`.

This is a pure rewriting statement: on the *open* quadrant `(0,∞) × (0,π/2)` the two
functions `∂_θ U u` and `V u` agree by Clairaut (`Work.Spaces.pz_pth_comm`), the two
integration domains `Iz = [0,∞)`, `Iθ = [0,π/2]` differ from `Ioi 0`, `Ioo 0 (π/2)` by
null sets (`{0}` and `{0, π/2}`), and the level-`0` `ℋ`-integrand is the weighted square
`w²·g²·σ` (`Honest.HkIntegrand_zero_eq`, `Honest.sq_profile_eq`).  No integrability
hypothesis is needed: all integrals are totalised, and the manipulations used are valid
for arbitrary (junk-valued) integrals.

The only hypothesis on `u` is joint `C^n`-smoothness on the open quadrant, for every `n`
(in particular `C²`, which is all Clairaut needs).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **Clairaut for the mixed slot.**  On the open quadrant, `∂_θ(z∂_z u) = z∂_z∂_θu`,
i.e. `pth (grad u) = V u`.

`pth (grad u) z θ = z·∂_θ(∂_zu)`, and the order of the two partial derivatives may be
swapped because `u` is `C²` at `(z,θ)`. -/
theorem pth_grad_eq_V (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Iθo,
      Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ = V u z θ := by
  intro z hz θ hθ
  have hqd : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt (hqd.mem_nhds ⟨hz, hθ⟩)
  have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
  have h1 : Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ := by
    show deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ
    simp only [Work.FTS.EllipticEst.H2W.Ae.grad]
    rw [deriv_const_mul_field]
  rw [h1]
  show z * deriv (fun θ' => Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [hcl]
  rfl


/-- **`HkSq α 0 (∂_θ U u)` as the `V u`-energy.** -/
theorem HkSq_zero_pth_grad (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
  have hgrad := pth_grad_eq_V u hu
  calc Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        Work.FTS.EllipticEst.Honest.HkSq_zero_eq α _
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          (fun θ hθ =>
            Work.FTS.EllipticEst.Honest.sq_profile_eq _ z θ
              (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ))
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Iθo,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
    _ = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo,
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigE θ :=
        MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume)).symm
    _ = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
        rw [show (∫ θ in Iθo,
              (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * sigE θ)
            = ∫ θ in Iθo,
              ((V u z θ) ^ 2 * sigE θ) * (Work.Spaces.w z) ^ 2 from by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
          rw [hgrad z hz θ hθ]
          ring]
        rw [MeasureTheory.integral_mul_const]
        ring

theorem HkSq_pth_grad (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                * Work.FTS.EllipticEst.AeI1Fts.sigE θ :=
  HkSq_zero_pth_grad α u hu

end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.UBB_continuousOn_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

/-- The rectangle `[a,b] × [c,d]` of the statement lies in the open quadrant when
`a > 0`, `c > 0` and `d < π/2` (and is empty otherwise). -/
theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩

/-- The iterated angular derivative `∂_θ^i` of a datum smooth on the open quadrant is again
smooth on the open quadrant. -/
theorem smoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Continuity of `∂_θ^i F` on the open quadrant. -/
theorem continuousOn_uncurry_pthIter {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter i F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
  (smoothOpen_pthIter hF i).continuousOn


end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedCollarBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false

/-!
## The `(1)`-D collar bound for the angular cut-off `psiD δ`

We prove `mixedCollarBound`: there is a universal constant `Cw > 0` such that for every
`K > 0`, `δ > 0` with `4δ ≤ π/2`, and every `f` whose slices satisfy the two endpoint *rates*

`f(θ)² ≤ K θ^{1+η} ∫_0^θ σ (f')²`,  `f(θ)² ≤ K (π/2-θ)^{1+η} ∫_θ^{π/2} σ (f')²`

(with `σ = sin(2θ)^{-η}`, `η = 99/100`) one has

`|∫_0^{π/2} σ ψ_δ'' f²| ≤ Cw K (∫_0^δ σ (f')² + ∫_{π/2-δ}^{π/2} σ (f')²)`.

The proof is pointwise: `ψ_δ''` vanishes on `(δ/2, π/2-δ/2)` and is `O(1/δ²)` everywhere, so

`|σ ψ_δ'' f²| ≤ (Cψ/δ²) σ f² · 1_{collar}`,

and on the collars the rates give `σ f² ≤ K A_i C₀ · (distance to the endpoint)`, whose integral
over the collar of width `δ` is `≤ K A_i C₀ δ²`; this cancels the `1/δ²`.

(The pointwise bounds `σ θ θ^{1+η} ≤ (π/4)^η θ` and its reflected twin follow from
`sin(2θ) ≥ 4θ/π`.)
-/

/-- On `(0,π/4]` we have `θ^{1+η} σ(θ) ≤ (π/4)^η θ`. -/
theorem sigTheta_mul_rpow_le_left {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 4) :
    θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * θ := by
  have hη := Work.Spaces.eta_pos
  have hπ := Real.pi_pos
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsin_le : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin_pos
  have hsin : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
    have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith)
    calc (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      _ ≤ Real.sin (2 * θ) := h
  have hratio : θ / Real.sin (2 * θ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hsin_pos]
    calc θ = (Real.pi / 4) * ((4 / Real.pi) * θ) := by field_simp
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin (by positivity)
  have hpow : (θ / Real.sin (2 * θ)) ^ Work.Spaces.eta
      ≤ (Real.pi / 4) ^ Work.Spaces.eta :=
    Real.rpow_le_rpow (by positivity) hratio (le_of_lt hη)
  have hident : θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ
      = θ * (θ / Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [Work.FTS.EllipticEst.AngSecond.sig, Real.rpow_neg hsin_le, Real.rpow_add hθ0,
      Real.rpow_one, Real.div_rpow (le_of_lt hθ0) hsin_le, div_eq_mul_inv]
    ring
  rw [hident]
  calc θ * (θ / Real.sin (2 * θ)) ^ Work.Spaces.eta
      ≤ θ * (Real.pi / 4) ^ Work.Spaces.eta := mul_le_mul_of_nonneg_left hpow (le_of_lt hθ0)
    _ = (Real.pi / 4) ^ Work.Spaces.eta * θ := by ring

/-- The angular weight is invariant under `θ ↦ π/2 - θ`. -/
theorem sigTheta_reflect (θ : ℝ) :
    Work.FTS.EllipticEst.AngSecond.sig (Real.pi / 2 - θ)
      = Work.FTS.EllipticEst.AngSecond.sig θ := by
  rw [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.AngSecond.sig,
    show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- On `[π/4, π/2)` we have `(π/2-θ)^{1+η} σ(θ) ≤ (π/4)^η (π/2-θ)`. -/
theorem sigTheta_mul_rpow_le_right {θ : ℝ} (hθ : Real.pi / 4 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) := by
  have h1 : 0 < Real.pi / 2 - θ := by linarith
  have h2 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have h := sigTheta_mul_rpow_le_left h1 h2
  rwa [sigTheta_reflect] at h


/-- **The mixed collar bound.**  A single constant `Cw` works in `CollarBound`. -/
theorem mixedCollarBound : ∃ Cw : ℝ, 0 < Cw ∧ Work.FTS.EllipticEst.Deleg.CollarBound Cw := by
  obtain ⟨C1, hC1pos, hC1⟩ := psiD_deriv2_bound_alt
  have hmid0 := psiD_deriv2_zero_mid
  have hC0pos : 0 < (Real.pi / 4) ^ Work.Spaces.eta :=
    Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _
  have hCwpos : 0 < C1 * (2 * (Real.pi / 4) ^ Work.Spaces.eta) + 1 := by
    nlinarith [hC1pos, hC0pos]
  refine ⟨C1 * (2 * (Real.pi / 4) ^ Work.Spaces.eta) + 1, hCwpos, ?_⟩
  intro K hK δ hδ hδ2 f hf1 hfint hrateL hrateR
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδπ : δ < Real.pi / 2 := by linarith
  have hδ8 : δ ≤ Real.pi / 8 := by linarith
  have hδ4 : δ ≤ Real.pi / 4 := by linarith
  -- ### order of the two factors of the integrand
  have hd_eq : (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      = fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    funext θ; ring
  have hfint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) volume := by
    rw [hd_eq]; exact hfint
  -- ### the two collars
  have hc1I : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Ioo_right (le_of_lt hδπ)
  have hc2I : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Ioo_left (by linarith)
  have hsig_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ := fun θ hθ =>
    Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hd_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2 :=
    fun θ hθ => mul_nonneg (hsig_nn θ hθ) (sq_nonneg _)
  have hc1intd : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      (Set.Ioo (0 : ℝ) δ) volume := hfint'.mono_set hc1I
  have hc2intd : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) volume := hfint'.mono_set hc2I
  -- ### the two collar energies, and `C0`
  let A1 : ℝ := ∫ t in Set.Ioo (0 : ℝ) δ,
    Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2
  let A2 : ℝ := ∫ t in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
    Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2
  let C0 : ℝ := (Real.pi / 4) ^ Work.Spaces.eta
  have hA1nn : 0 ≤ A1 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => hd_nn θ (hc1I hθ))
  have hA2nn : 0 ≤ A2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => hd_nn θ (hc2I hθ))
  -- ### the pointwise bounds on the two collars
  have hpt1 : ∀ θ ∈ Set.Ioo (0 : ℝ) δ,
      Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2 ≤ K * A1 * (C0 * θ) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hc1I hθ
    have hθ0 : 0 < θ := hθ.1
    have hθ4 : θ ≤ Real.pi / 4 := by linarith [hθ.2, hδ4]
    have hE : (∫ t in Set.Ioo (0 : ℝ) θ,
        Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ A1 := by
      refine MeasureTheory.setIntegral_mono_set hc1intd ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hd_nn t (hc1I ht)
      · exact Eventually.of_forall
          (fun t ht => Set.Ioo_subset_Ioo_right (le_of_lt hθ.2) ht)
    have hrate := hrateL θ hθI
    have hrate' : (f θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo (0 : ℝ) θ,
            Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) := by
      simpa only [← hd_eq] using hrate
    have hYnn : 0 ≤ θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hθ0) _) (hsig_nn θ hθI)
    have h2 : θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ ≤ C0 * θ :=
      sigTheta_mul_rpow_le_left hθ0 hθ4
    calc Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2
        ≤ Work.FTS.EllipticEst.AngSecond.sig θ
            * (K * θ ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo (0 : ℝ) θ,
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hrate' (hsig_nn θ hθI)
      _ = K * (∫ t in Set.Ioo (0 : ℝ) θ,
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
            * (θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
      _ ≤ K * A1 * (C0 * θ) := by
          have h1 : K * (∫ t in Set.Ioo (0 : ℝ) θ,
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ K * A1 :=
            mul_le_mul_of_nonneg_left hE (le_of_lt hK)
          calc K * (∫ t in Set.Ioo (0 : ℝ) θ,
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
                * (θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ)
              ≤ K * A1 * (θ ^ (1 + Work.Spaces.eta)
                  * Work.FTS.EllipticEst.AngSecond.sig θ) :=
                mul_le_mul_of_nonneg_right h1 hYnn
            _ ≤ K * A1 * (C0 * θ) :=
                mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_of_lt hK) hA1nn)
  have hpt2 : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
      Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2
        ≤ K * A2 * (C0 * (Real.pi / 2 - θ)) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hc2I hθ
    have hθ4 : Real.pi / 4 ≤ θ := by linarith [hθ.1, hδ4]
    have hE : (∫ t in Set.Ioo θ (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ A2 := by
      refine MeasureTheory.setIntegral_mono_set hc2intd ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hd_nn t (hc2I ht)
      · exact Eventually.of_forall
          (fun t ht => Set.Ioo_subset_Ioo_left (le_of_lt hθ.1) ht)
    have hrate := hrateR θ hθI
    have hrate' : (f θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2),
            Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) := by
      simpa only [← hd_eq] using hrate
    have hYnn : 0 ≤ (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * Work.FTS.EllipticEst.AngSecond.sig θ :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hθ.2]) _) (hsig_nn θ hθI)
    have h2 : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * Work.FTS.EllipticEst.AngSecond.sig θ ≤ C0 * (Real.pi / 2 - θ) :=
      sigTheta_mul_rpow_le_right hθ4 hθI.2
    calc Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2
        ≤ Work.FTS.EllipticEst.AngSecond.sig θ
            * (K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo θ (Real.pi / 2),
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hrate' (hsig_nn θ hθI)
      _ = K * (∫ t in Set.Ioo θ (Real.pi / 2),
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
            * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
      _ ≤ K * A2 * (C0 * (Real.pi / 2 - θ)) := by
          have h1 : K * (∫ t in Set.Ioo θ (Real.pi / 2),
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ K * A2 :=
            mul_le_mul_of_nonneg_left hE (le_of_lt hK)
          calc K * (∫ t in Set.Ioo θ (Real.pi / 2),
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
                * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                    * Work.FTS.EllipticEst.AngSecond.sig θ)
              ≤ K * A2 * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                  * Work.FTS.EllipticEst.AngSecond.sig θ) :=
                mul_le_mul_of_nonneg_right h1 hYnn
            _ ≤ K * A2 * (C0 * (Real.pi / 2 - θ)) :=
                mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_of_lt hK) hA2nn)
  -- ### the dominating function
  let g1 : ℝ → ℝ := fun θ => (C1 / δ ^ 2) * K * A1 * C0
      * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ
  let g2 : ℝ → ℝ := fun θ => (C1 / δ ^ 2) * K * A2 * C0
      * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator (fun θ : ℝ => Real.pi / 2 - θ) θ
  have hg1eq : ∀ θ : ℝ, g1 θ = (C1 / δ ^ 2) * K * A1 * C0
      * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ := fun θ => rfl
  have hg2eq : ∀ θ : ℝ, g2 θ = (C1 / δ ^ 2) * K * A2 * C0
      * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
          (fun θ : ℝ => Real.pi / 2 - θ) θ := fun θ => rfl
  -- ### integrability of the dominating function
  have hvol1 : volume (Set.Ioo (0 : ℝ) δ) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hvol2 : volume (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hlin1 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ) (Set.Ioo (0 : ℝ) δ) volume := by
    refine MeasureTheory.IntegrableOn.of_bound hvol1 continuous_id.aestronglyMeasurable δ ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_pos ht.1]
    exact le_of_lt ht.2
  have hlin2 : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.pi / 2 - θ)
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) volume := by
    refine MeasureTheory.IntegrableOn.of_bound hvol2
      ((continuous_const.sub continuous_id)).aestronglyMeasurable δ ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
    linarith [ht.1]
  have hint1 : Integrable ((Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => θ) (Set.Ioo (0 : ℝ) δ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hlin1.restrict
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2 h
  have hint2 : Integrable ((Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
      (fun θ : ℝ => Real.pi / 2 - θ))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.pi / 2 - θ)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hlin2.restrict
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2 h
  have hg1int : Integrable g1 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change Integrable (fun θ => (C1 / δ ^ 2) * K * A1 * C0
      * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ) _
    exact hint1.const_mul _
  have hg2int : Integrable g2 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change Integrable (fun θ => (C1 / δ ^ 2) * K * A2 * C0
      * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
          (fun θ : ℝ => Real.pi / 2 - θ) θ) _
    exact hint2.const_mul _
  have hsumint : Integrable (fun θ => g1 θ + g2 θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hg1int.add hg2int
  -- ### the pointwise domination
  have hpt : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ‖(Work.FTS.EllipticEst.AngSecond.sig θ
          * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2)‖
        ≤ g1 θ + g2 θ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθI
    by_cases h1 : θ ∈ Set.Ioo (0 : ℝ) δ
    · have h2not : θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) := by
        intro hc
        linarith [h1.2, hc.1, hδ8]
      rw [hg1eq θ, hg2eq θ, Set.indicator_of_mem h1, Set.indicator_of_notMem h2not,
        mul_zero, add_zero, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (hsig_nn θ hθI), abs_of_nonneg (sq_nonneg (f θ))]
      have hψ : |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| ≤ C1 / δ ^ 2 :=
        hC1 δ hδ θ
      calc Work.FTS.EllipticEst.AngSecond.sig θ
            * |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| * (f θ) ^ 2
          ≤ Work.FTS.EllipticEst.AngSecond.sig θ * (C1 / δ ^ 2) * (f θ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hψ (hsig_nn θ hθI)) (sq_nonneg _)
        _ = (C1 / δ ^ 2) * (Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2) := by ring
        _ ≤ (C1 / δ ^ 2) * (K * A1 * (C0 * θ)) :=
            mul_le_mul_of_nonneg_left (hpt1 θ h1)
              (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
        _ = (C1 / δ ^ 2) * K * A1 * C0 * θ := by ring
    · by_cases h2 : θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)
      · rw [hg1eq θ, hg2eq θ, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
          mul_zero, zero_add, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (hsig_nn θ hθI), abs_of_nonneg (sq_nonneg (f θ))]
        have hψ : |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| ≤ C1 / δ ^ 2 :=
          hC1 δ hδ θ
        calc Work.FTS.EllipticEst.AngSecond.sig θ
              * |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| * (f θ) ^ 2
            ≤ Work.FTS.EllipticEst.AngSecond.sig θ * (C1 / δ ^ 2) * (f θ) ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hψ (hsig_nn θ hθI)) (sq_nonneg _)
          _ = (C1 / δ ^ 2) * (Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2) := by ring
          _ ≤ (C1 / δ ^ 2) * (K * A2 * (C0 * (Real.pi / 2 - θ))) :=
              mul_le_mul_of_nonneg_left (hpt2 θ h2)
                (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
          _ = (C1 / δ ^ 2) * K * A2 * C0 * (Real.pi / 2 - θ) := by ring
      · have hθge : δ ≤ θ := by
          rcases lt_or_ge θ δ with hlt | hge
          · exact absurd ⟨hθI.1, hlt⟩ h1
          · exact hge
        have hθle : θ ≤ Real.pi / 2 - δ := by
          rcases lt_or_ge (Real.pi / 2 - δ) θ with hlt | hge
          · exact absurd ⟨hlt, hθI.2⟩ h2
          · exact hge
        have hmid : deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ = 0 :=
          hmid0 δ hδ θ (by linarith) (by linarith)
        have hGz : Work.FTS.EllipticEst.AngSecond.sig θ
            * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2 = 0 := by
          rw [hmid, mul_zero, zero_mul]
        have hg1z : g1 θ = 0 := by
          rw [hg1eq θ, Set.indicator_of_notMem h1, mul_zero]
        have hg2z : g2 θ = 0 := by
          rw [hg2eq θ, Set.indicator_of_notMem h2, mul_zero]
        rw [hGz, hg1z, hg2z, norm_zero, add_zero]
  -- ### the integral of the dominating function
  have hstep1 : |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ
          * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g1 θ + g2 θ) := by
    have h := MeasureTheory.norm_integral_le_of_norm_le hsumint hpt
    simpa only [Real.norm_eq_abs] using h
  have hstep2 : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g1 θ + g2 θ)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ)
        + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ) :=
    MeasureTheory.integral_add hg1int hg2int
  have hg1val : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ
      = (C1 / δ ^ 2) * K * A1 * C0 * (∫ θ in Set.Ioo (0 : ℝ) δ, θ) := by
    change ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (C1 / δ ^ 2) * K * A1 * C0
        * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ
      = (C1 / δ ^ 2) * K * A1 * C0 * (∫ θ in Set.Ioo (0 : ℝ) δ, θ)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo, Set.inter_comm,
      Set.inter_eq_left.2 hc1I]
  have hg2val : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ
      = (C1 / δ ^ 2) * K * A2 * C0
        * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.pi / 2 - θ)) := by
    change ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (C1 / δ ^ 2) * K * A2 * C0
        * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
            (fun θ : ℝ => Real.pi / 2 - θ) θ
      = (C1 / δ ^ 2) * K * A2 * C0
        * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.pi / 2 - θ))
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo, Set.inter_comm,
      Set.inter_eq_left.2 hc2I]
  have hvolc1 : ∫ θ in Set.Ioo (0 : ℝ) δ, θ = δ ^ 2 / 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (le_of_lt hδ), integral_id]
    ring
  have hvolc2 : ∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.pi / 2 - θ)
      = δ ^ 2 / 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_comp_sub_left (f := fun y : ℝ => y) (d := Real.pi / 2),
      integral_id]
    ring
  have hg1le : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ ≤ C1 * K * A1 * C0 := by
    rw [hg1val, hvolc1]
    have hnn : 0 ≤ (C1 / δ ^ 2) * K * A1 * C0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
        (le_of_lt hK)) hA1nn) (le_of_lt hC0pos)
    calc (C1 / δ ^ 2) * K * A1 * C0 * (δ ^ 2 / 2)
        ≤ (C1 / δ ^ 2) * K * A1 * C0 * δ ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg δ]) hnn
      _ = C1 * K * A1 * C0 := by
          rw [show (C1 / δ ^ 2) * K * A1 * C0 * δ ^ 2
              = ((C1 / δ ^ 2) * δ ^ 2) * K * A1 * C0 by ring,
            div_mul_cancel₀ C1 (pow_ne_zero 2 (ne_of_gt hδ))]
  have hg2le : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ ≤ C1 * K * A2 * C0 := by
    rw [hg2val, hvolc2]
    have hnn : 0 ≤ (C1 / δ ^ 2) * K * A2 * C0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
        (le_of_lt hK)) hA2nn) (le_of_lt hC0pos)
    calc (C1 / δ ^ 2) * K * A2 * C0 * (δ ^ 2 / 2)
        ≤ (C1 / δ ^ 2) * K * A2 * C0 * δ ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg δ]) hnn
      _ = C1 * K * A2 * C0 := by
          rw [show (C1 / δ ^ 2) * K * A2 * C0 * δ ^ 2
              = ((C1 / δ ^ 2) * δ ^ 2) * K * A2 * C0 by ring,
            div_mul_cancel₀ C1 (pow_ne_zero 2 (ne_of_gt hδ))]
  have hfinal : |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ
          * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
      ≤ (C1 * (2 * C0) + 1) * K * (A1 + A2) := by
    calc |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.FTS.EllipticEst.AngSecond.sig θ
            * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g1 θ + g2 θ) := hstep1
      _ = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ)
            + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ) := hstep2
      _ ≤ C1 * K * A1 * C0 + C1 * K * A2 * C0 := add_le_add hg1le hg2le
      _ = C1 * K * C0 * (A1 + A2) := by ring
      _ ≤ (C1 * (2 * C0) + 1) * K * (A1 + A2) := by
          have hx : 0 ≤ C1 * K * C0 * (A1 + A2) :=
            mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1pos) (le_of_lt hK))
              (le_of_lt hC0pos)) (add_nonneg hA1nn hA2nn)
          have hy : 0 ≤ K * (A1 + A2) :=
            mul_nonneg (le_of_lt hK) (add_nonneg hA1nn hA2nn)
          nlinarith [hx, hy]
  exact hfinal

end Work.FTS.EllipticEst.Deleg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.QuadBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The open quadrant -/

/-- The open quadrant `Q = (0,∞) × (0,π/2)`. -/
abbrev quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_quad : IsOpen quad := isOpen_Ioi.prod isOpen_Ioo



/-! ## The smoothness ladder -/

/-- `C^n` on `Q` for every `n` is `C^∞` on `Q`. -/
theorem contDiffOn_smoothOrder_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) quad :=
  contDiffOn_infty.mpr hu

/-- `∂_z^k` preserves `C^∞` on the open quadrant. -/
theorem contDiffOn_pzIter_quad' {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pzIter k g)) quad := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.pz (Work.Spaces.pzIter k g))) quad
      exact Work.FTS.LocData.contDiffOn_pz isOpen_quad ih

/-- `∂_θ^k` preserves `C^∞` on the open quadrant. -/
theorem contDiffOn_pthIter_quad' {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pthIter k g)) quad := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter k g))) quad
      exact Work.FTS.LocData.contDiffOn_pth isOpen_quad ih

theorem contDiffOn_pzIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pzIter k u)) quad :=
  contDiffOn_pzIter_quad' (contDiffOn_smoothOrder_quad hu) k

theorem contDiffOn_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pthIter k u)) quad :=
  contDiffOn_pthIter_quad' (contDiffOn_smoothOrder_quad hu) k

/-- Any `∂_z^k ∂_θ^i u` is `C^∞` on the open quadrant. -/
theorem contDiffOn_pzIter_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter k (Work.Spaces.pthIter i u))) quad :=
  contDiffOn_pzIter_quad' (contDiffOn_pthIter_quad hu i) k

theorem continuousOn_pzIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter k u p.1 p.2) quad :=
  (contDiffOn_pzIter_quad hu k).continuousOn


theorem continuousOn_pzIter_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter k (Work.Spaces.pthIter i u) p.1 p.2)
      quad :=
  (contDiffOn_pzIter_pthIter_quad hu k i).continuousOn

/-- `U z = z ∂_z u` is a continuous function of `(z,θ)` on the open quadrant. -/
theorem continuousOn_Uz_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2) quad :=
  (continuousOn_fst.mul (continuousOn_pzIter_quad hu 1)).congr (fun p _ => rfl)

/-- `V z = z ∂_z∂_θ u` is a continuous function of `(z,θ)` on the open quadrant. -/
theorem continuousOn_Vz_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2) quad :=
  (continuousOn_fst.mul (continuousOn_pzIter_pthIter_quad hu 1 1)).congr (fun p _ => rfl)

/-! ## The `θ`-slices -/

/-- The `θ`-slice of `∂_z^k u` is `C^∞` on `(0,π/2)` for `z > 0`. -/
theorem contDiffOn_slice_pzIter {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.pzIter k u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.LocData.contDiffOn_slice_θ (G := Work.Spaces.pzIter k u) (s := Set.Ioi 0)
    (t := Set.Ioo 0 (Real.pi / 2)) (contDiffOn_pzIter_quad hu k) hz


/-- `U z = z ∂_z u` is `C¹` in `θ` on `(0,π/2)` for `z > 0`. -/
theorem contDiffOn_Uz_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
  ((contDiffOn_slice_pzIter hu 1 hz).const_smul (z : ℝ)).of_le (by norm_num)

/-- Clairaut on the slice: `∂_θ (z ∂_z u) = z ∂_z∂_θ u` on the open quadrant. -/
theorem deriv_Uz_eq_Vz {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ
      = Work.FTS.EllipticEst.AeColl.Vz u z θ := by
  have hp : (z, θ) ∈ quad := ⟨hz, hθ⟩
  have h2 : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt (isOpen_quad.mem_nhds hp)
  have hcomm : Work.Spaces.pz (Work.Spaces.pth u) z θ
      = Work.Spaces.pth (Work.Spaces.pz u) z θ := Work.Spaces.pz_pth_comm h2
  show deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [deriv_const_mul_field]
  show z * Work.Spaces.pth (Work.Spaces.pz u) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [hcomm]

/-! ## A.e. strong measurability of `θ`-integrals on the quadrant -/

/-- The `θ`-integral over a measurable set `S ⊆ [0,π/2]` of a function continuous on the open
quadrant is a.e. strongly measurable as a function of `z` (Fubini). -/
theorem aesm_thetaIntegral_Ioi {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) quad) {S : Set ℝ}
    (hS : MeasurableSet S) (hSI : S ⊆ Work.Spaces.Iθ) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in S, F z θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hG : MeasureTheory.AEStronglyMeasurable
      ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => F p.1 p.2) hcont).indicator
      (MeasurableSet.univ.prod hS)
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hG.integral_prod_right'
  have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
      = fun z => ∫ θ in S, F z θ := by
    funext z
    have hpt : (fun θ => ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
        = (S.indicator (fun θ => F z θ)) := by
      funext θ
      by_cases h : θ ∈ S
      · rw [Set.indicator_of_mem (show (z, θ) ∈ (Set.univ ×ˢ S : Set (ℝ × ℝ)) from
            ⟨Set.mem_univ z, h⟩), Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem (show ¬((z, θ) ∈ (Set.univ ×ˢ S : Set (ℝ × ℝ))) from
            fun hh => h hh.2), Set.indicator_of_notMem h]
    calc (∫ θ in Work.Spaces.Iθ,
            ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
        = ∫ θ in Work.Spaces.Iθ, (S.indicator (fun θ => F z θ)) θ := by rw [hpt]
      _ = ∫ θ in S, F z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
            MeasureTheory.integral_indicator hS
      _ = ∫ θ in S, F z θ := by
            rw [MeasureTheory.Measure.restrict_restrict_of_subset hSI]
  rw [hfun] at h1
  exact h1.mono_measure (le_of_eq (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))))

end Work.FTS.EllipticEst.Deleg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.mixed_Dzpth_expand_V =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false


end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.I1_ibp_identity_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.remov

open Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000


/-! ## The limit `n → ∞` -/




end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.PsiCutBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The affine coefficient `u ↦ u - c` -/

/-! ## The two radial factors of `cutA` -/








/-! ## The affine coefficient `u ↦ u - c` -/








/-! ## The bound for the linear coefficient -/


/-! ## The uniform bound for `cutA` -/


/-! ## The two angular factors of `cutB` -/











/-! ## The derivatives of `ρ_λ` -/





theorem iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  have e : iteratedDeriv 2 f = iteratedDeriv 1 (deriv f) := iteratedDeriv_succ' (n := 1) (f := f)
  rw [e, iteratedDeriv_one]



/-! ## The bound for the `ρ_λ` coefficient -/


/-! ## The uniform bound for `cutB` -/



end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.Upart_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The localisation family `UN N`

`UN N = {p | p.1 ∉ Ioo (plo N) (phiN N) ∨ p.2 ∉ Ioo (qlo N) (qhi N)}` (`Subcut.Defs`) is the
complement of the expanding open plateau, hence an antitone family of measurable sets whose
intersection is null on the domain `Iz × Iθ`.  The two facts proved here are the hypotheses of the
generic dominated-convergence lemma `tendsto_iterated_indicator_of_ae` below. -/











/-! ## The generic dominated-convergence lemma -/



end

end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.NonlinRows.mixed_slot_mul_pth_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The non-linear mixed slot `D_z^jD_θ^i(f · ∂_θ g)`

Pointwise estimate: the weighted mixed derivative
`D_z^jD_θ^i(f · ∂_θg) · Wt α` of a product of a datum `f` whose mixed derivatives are
`O(sin 2θ)` and the angular derivative of a datum `g` whose angular derivatives satisfy the
`sin 2θ`-divisibility estimate is bounded, in the `ℋ^6`-weight, by `K · C_ψ` times the
`ℋ^6`-integrand of `g`.

The proof is the Leibniz expansion `leibniz_open_mixed` followed by termwise bookkeeping:
each factor `D_z^aD_θ^b f` contributes the factor `sin 2θ` which, together with the
`sin 2θ` of the `C_ψ`-hypothesis, matches the `sin(2θ)^{-γ/2}` of the weight `Wt`.
-/








end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.abs_mixed_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The finite-sum bookkeeping of the Leibniz expansion.**  For `a + b ≤ 6`, the total mass
of the binomial coefficients of the two-operator Leibniz rule is at most `2^a·2^b ≤ 2^6 = 64`,
against a constant per-term bound `T ≥ 0`. -/
theorem sum_choose_mul_le (a b : ℕ) (hab : a + b ≤ 6) (T : ℝ) (hT : 0 ≤ T) :
    ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T ≤ 64 * T := by
  have hsum_a : ∑ a₁ ∈ Finset.range (a + 1), ((a.choose a₁ : ℝ)) = (2 : ℝ) ^ a := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hsum_b : ∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ)) = (2 : ℝ) ^ b := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have key : ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T
      = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * T := by
    have step1 : (∑ a₁ ∈ Finset.range (a + 1), (a.choose a₁ : ℝ))
          * (∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ) * T))
        = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            (a.choose a₁ : ℝ) * ((b.choose b₁ : ℝ) * T) :=
      Finset.sum_mul_sum _ _ _ _
    have step2 : (∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ) * T))
        = (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)) * T :=
      (Finset.sum_mul _ _ _).symm
    calc ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T
        = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            (a.choose a₁ : ℝ) * ((b.choose b₁ : ℝ) * T) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          ring
      _ = (∑ a₁ ∈ Finset.range (a + 1), (a.choose a₁ : ℝ))
            * (∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ) * T)) := step1.symm
      _ = (∑ a₁ ∈ Finset.range (a + 1), (a.choose a₁ : ℝ))
            * ((∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)) * T) := by rw [step2]
      _ = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * T := by rw [hsum_a, hsum_b]; ring
  rw [key]
  have h2 : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  exact mul_le_mul_of_nonneg_right h2 hT

theorem abs_mixed_mul_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {A Q : ℝ → ℝ → ℝ} {KA KQ : ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hQ : Work.FTS.EllipticEst.SmoothOpen Q)
    (hAdec : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1))
    (hQdec : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i Q z θ| ≤ KQ * (z / (1 + z) ^ 2) *
          (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1))
    {a b : ℕ} (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ|
        ≤ KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) *
            (if 1 ≤ a then 8192 * (Real.sin (2 * θ)) ^ (α / 5) else 8192) := by
  intro z θ hz hθ0 hθ1
  -- ## Elementary angular and radial facts
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hspos
  have hsle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hznn : 0 ≤ z := le_of_lt hz
  have hd1 : 0 ≤ z / (1 + z) := div_nonneg hznn (by linarith)
  have hd2 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hznn (by positivity)
  have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsnn _
  have hs3 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 3) := Real.rpow_nonneg hsnn _
  -- ## The two decay constants are nonnegative
  have hKA : 0 ≤ KA := by
    by_contra hlt
    push_neg at hlt
    have h1 := hAdec 0 1 (by norm_num) z θ hz hθ0 hθ1
    rw [if_pos (le_refl 1)] at h1
    have h2 : KA * (z / (1 + z))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) < 0 :=
      mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hlt (div_pos hz (by linarith)))
        (mul_pos (by linarith) (Real.rpow_pos_of_pos hspos _))
    linarith [abs_nonneg (Work.Spaces.mixed 0 1 A z θ)]
  have hKQ : 0 ≤ KQ := by
    by_contra hlt
    push_neg at hlt
    have h1 := hQdec 0 0 (by norm_num) z θ hz hθ0 hθ1
    rw [if_neg (by norm_num : ¬ (1 : ℕ) ≤ 0)] at h1
    simp only [mul_one] at h1
    have h2 : KQ * (z / (1 + z) ^ 2) < 0 :=
      mul_neg_of_neg_of_pos hlt (div_pos hz (by positivity))
    linarith [abs_nonneg (Work.Spaces.mixed 0 0 Q z θ)]
  -- ## The two composite constants
  set W : ℝ := KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) with hW
  have hWnn : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (mul_nonneg (mul_nonneg hKA hKQ) hd1) hd2
  set T : ℝ := (if 1 ≤ a then 2 * W * (Real.sin (2 * θ)) ^ (α / 5) else W) with hT
  have hTnn : 0 ≤ T := by
    rw [hT]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
      exact mul_nonneg (mul_nonneg (by norm_num) hWnn) hsp
    · rw [if_neg ha]; exact hWnn
  -- ## The per-term bound
  have hper : ∀ a₁ ≤ a, ∀ b₁ ≤ b,
      |Work.Spaces.mixed b₁ a₁ A z θ| * |Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| ≤ T := by
    intro a₁ ha₁ b₁ hb₁
    have hA₁ := hAdec b₁ a₁ (by omega) z θ hz hθ0 hθ1
    by_cases ha₁' : 1 ≤ a₁
    · -- ### the first block carries an angular derivative
      rw [if_pos ha₁'] at hA₁
      have hAp : 0 ≤ KA * (z / (1 + z))
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
        mul_nonneg (mul_nonneg hKA hd1) (mul_nonneg (by linarith) hsp)
      have hQb : |Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| ≤ KQ * (z / (1 + z) ^ 2) := by
        have hQ₁ := hQdec (b - b₁) (a - a₁) (by omega) z θ hz hθ0 hθ1
        by_cases h2 : 1 ≤ a - a₁
        · rw [if_pos h2] at hQ₁
          refine le_trans hQ₁ ?_
          calc KQ * (z / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (α / 3)
              ≤ KQ * (z / (1 + z) ^ 2) * 1 :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_one hsnn hsle (by positivity))
                  (mul_nonneg hKQ hd2)
            _ = KQ * (z / (1 + z) ^ 2) := by ring
        · rw [if_neg h2] at hQ₁
          simpa using hQ₁
      refine le_trans (mul_le_mul hA₁ hQb (abs_nonneg _) hAp) ?_
      have hW1 : W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          = (KA * (z / (1 + z))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            * (KQ * (z / (1 + z) ^ 2)) := by
        rw [hW]; ring
      rw [← hW1]
      by_cases ha : 1 ≤ a
      · rw [hT]; simp only [if_pos ha]
        have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
        have hstep : W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            ≤ W * (2 * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hsp) hWnn
        calc W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            ≤ W * (2 * (Real.sin (2 * θ)) ^ (α / 5)) := hstep
          _ = 2 * W * (Real.sin (2 * θ)) ^ (α / 5) := by ring
      · exfalso; omega
    · -- ### the first block has no angular derivative: then `a₁ = 0`
      obtain rfl : a₁ = 0 := by omega
      rw [if_neg (by norm_num : ¬ (1 : ℕ) ≤ 0)] at hA₁
      simp only [mul_one] at hA₁
      have hAp : 0 ≤ KA * (z / (1 + z)) := mul_nonneg hKA hd1
      by_cases ha : 1 ≤ a
      · -- the angular derivative has moved entirely to `Q`
        have hQ₁ := hQdec (b - b₁) (a - 0) (by omega) z θ hz hθ0 hθ1
        have h2 : 1 ≤ a - 0 := by omega
        rw [if_pos h2] at hQ₁
        have hQp2 : 0 ≤ KQ * (z / (1 + z) ^ 2) := mul_nonneg hKQ hd2
        have hexp : (Real.sin (2 * θ)) ^ (α / 3) ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Real.rpow_le_rpow_of_exponent_ge hspos hsle (by linarith)
        have hW1 : W * (Real.sin (2 * θ)) ^ (α / 5)
            = (KA * (z / (1 + z)))
              * (KQ * (z / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          rw [hW]; ring
        refine le_trans (mul_le_mul hA₁ hQ₁ (abs_nonneg _) hAp) ?_
        refine le_trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp hQp2) hAp) ?_
        rw [← hW1]
        rw [hT]; simp only [if_pos ha]
        nlinarith [mul_nonneg hWnn hsp]
      · -- no angular derivative anywhere
        have h2 : ¬ (1 ≤ a - 0) := by omega
        have hQ₁ := hQdec (b - b₁) (a - 0) (by omega) z θ hz hθ0 hθ1
        rw [if_neg h2] at hQ₁
        simp only [mul_one] at hQ₁
        refine le_trans (mul_le_mul hA₁ hQ₁ (abs_nonneg _) hAp) ?_
        have hW1 : W = (KA * (z / (1 + z))) * (KQ * (z / (1 + z) ^ 2)) := by
          rw [hW]; ring
        rw [← hW1, hT]; simp only [if_neg ha]
        rfl
  -- ## The Leibniz expansion and the sum bound
  have hleib := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a A Q hA hQ z θ hz hθ0 hθ1
  rw [hleib]
  have hsum : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)|
      ≤ 64 * T := by
    calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact Finset.sum_le_sum fun a₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T := by
          refine Finset.sum_le_sum fun a₁ ha₁ => Finset.sum_le_sum fun b₁ hb₁ => ?_
          have ha₁le : a₁ ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
          have hb₁le : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
          have hX : |Work.Spaces.mixed b₁ a₁ A z θ
              * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| ≤ T := by
            rw [abs_mul]
            exact hper a₁ ha₁le b₁ hb₁le
          have hC : 0 ≤ (a.choose a₁ : ℝ) * (b.choose b₁ : ℝ) := by positivity
          calc |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)|
              = ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * |Work.Spaces.mixed b₁ a₁ A z θ
                    * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| := by
                rw [abs_mul, abs_of_nonneg hC]
            _ ≤ ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T :=
                mul_le_mul_of_nonneg_left hX hC
      _ ≤ 64 * T := sum_choose_mul_le a b hab T hTnn
  refine le_trans hsum ?_
  by_cases ha : 1 ≤ a
  · simp only [hT, if_pos ha]
    have hWs : 0 ≤ W * (Real.sin (2 * θ)) ^ (α / 5) := mul_nonneg hWnn hsp
    calc 64 * (2 * W * (Real.sin (2 * θ)) ^ (α / 5))
        = 128 * (W * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      _ ≤ 8192 * (W * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right (by norm_num) hWs
      _ = W * (8192 * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
  · simp only [hT, if_neg ha]
    calc 64 * W ≤ 8192 * W := mul_le_mul_of_nonneg_right (by norm_num) hWnn
      _ = W * 8192 := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `f² · sin(2θ)^{-η}` on the angular interval, from `ℋ^k`-membership

The `0`-th summand of the `ℋ^k`-weighted integrand of `f` is

`(D_z^0 f · w(z) / sin(2θ)^{η/2})² = f(z,θ)² · w(z)² · sin(2θ)^{-η}`,

and `Work.FTS.EllipticEst.integrableOn_zSummand` (the open-quadrant version of the basic
`ℋ^k` API of `OpenQDefs.lean`) says that this summand is integrable on `Iθ` for every
`z ∈ Iz`.  On the open quadrant the radial weight `w` is a positive *constant* (in `θ`), so
scalar multiplication by `(w(z)²)^{-1}` transfers the integrability to the unweighted
quantity `f(z,θ)² · sin(2θ)^{-η}`.  (At the two endpoints `θ = 0, π/2` both sides of the
pointwise identity vanish separately, so no exceptional set has to be removed.)

This is the `η`-weighted honesty statement consumed by the pinning argument at the corner
`θ = π/2`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Pinning

/-- **The pointwise identity converting the `0`-th weighted summand into the unweighted
`η`-weighted square.**  For `z > 0` and `θ ∈ Iθ`,

`(w z²)^{-1} · (F · w z / sin(2θ)^{η/2})² = F² · sin(2θ)^{-η}`.

Both sides vanish at the endpoints `θ = 0, π/2` (where `sin(2θ) = 0`); on the open interval
the identity is the `rpow` algebra `(sin(2θ)^{η/2})² = sin(2θ)^{η}` together with the
cancellation of the constant factor `w z²`. -/
lemma inv_w_sq_mul_weighted_sq_eq (z θ F : ℝ) (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z ^ 2)⁻¹ * (F * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = F ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    have h2 : 0 ≤ 2 * θ ∧ 2 * θ ≤ Real.pi := by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    exact Real.sin_nonneg_of_mem_Icc ⟨h2.1, h2.2⟩
  have hwn : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with hs | hs
  · -- endpoints: `sin(2θ) = 0`, both sides vanish
    rw [hs]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [h1, h2]
    simp
  · -- interior: `0 < sin(2θ)` and the `rpow` exponent is additive
    have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin0 (Ne.symm hs)
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hsin0]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, Real.rpow_neg hsin0 (Work.Spaces.eta)]
    field_simp

theorem integrableOn_sq_rpow_of_HkMem {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn
        (fun θ => (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
  intro z hz
  -- the `i = 0` weighted `D_z`-summand of the `ℋ^k`-integrand is integrable on `Iθ`
  have hsum : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 0 f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hsm hmem 0 (Nat.zero_le k)
      (Set.mem_Ici.mpr hz.le)
  -- rescale by the (positive, `θ`-independent) constant `(w z²)^{-1}`
  have hc : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z ^ 2)⁻¹ *
      (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    hsum.integrable.const_mul _
  refine hc.congr_fun ?_ ?_
  · intro θ hθ
    rw [Work.Spaces.DzIter_zero]
    exact inv_w_sq_mul_weighted_sq_eq z θ (f z θ) hz hθ
  · rw [Work.Spaces.Iθ]
    exact measurableSet_Icc

end Work.FTS_EllLimOK.Pinning
end
end
