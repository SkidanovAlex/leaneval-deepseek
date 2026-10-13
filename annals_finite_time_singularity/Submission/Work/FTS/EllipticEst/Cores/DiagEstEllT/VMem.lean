/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores/DiagEstEllT/VMem` — honesty of the straightened datum in `EllHypT`

Under the orthogonality condition, the straightened datum `V = Ψ + Gsing α F · sin 2θ` of
Theorem `RemovingL12` is the sum of `Ψ` (`C^∞` on the open quadrant) and the radial-times-angular
layer `Gsing α F · sin 2θ` (`C^{k+1}` in `z`, `C^∞` in `θ`).  Both summands are therefore `C^k` on
the open quadrant, and `HkIntegrand α k` only involves the indices `i ≤ k`, `i + j ≤ k`: so the
finite-order subadditivity `HkIntegrand_add_le_of_contDiffOn` gives the domination that
`HkMem_of_add_dominated` needs, with the hypothesis `SmoothOpen h` replaced by the (weaker, and
here *available*) `ContDiffOn ℝ k (uncurry h) Q0`.

The two structural ingredients are
* `honest_HkMem_gsing_sin` (`Cores/DiagEstEllT/StraightMem.lean`) — honesty of the layer, which
  uses the orthogonality identity `Gsing α F = -(15/4) F_*(Ψ)`;
* `HkIntegrand_add_le_of_contDiffOn` (`Cores/DiagEstEllT/HkIntegrand_add_le_of_contDiffOn.lean`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.StraightMem
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Continuity of the `ℋ^k`-integrand from finite-order smoothness -/

/-- **The uncurried `ℋ^k`-integrand of a `C^k`-on-the-open-quadrant function is continuous
there.**  This is the finite-order version of `SmoothOpen.continuousOn_HkIntegrand`: the four
ingredients are `contDiffOn_DzIter_fin`, `contDiffOn_DthIter_fin` (for the `D_z^j D_θ^i`-block)
and the continuity of the two weights. -/
theorem continuousOn_HkIntegrand_of_contDiffOn {h : ℝ → ℝ → ℝ} {k : ℕ}
    (hh : ContDiffOn ℝ k (Function.uncurry h) Work.FTS.EllipticEst.Q0) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        Work.FTS.EllipticEst.Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
        funext p; rfl
      rw [hfun2]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp =>
          pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
    refine hw.mul ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hZ : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := fun i hi =>
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hh i hi).continuousOn
  have hM : ∀ j i, i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
    intro j i hij
    have hi : i ≤ k := by omega
    have hstep := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hh i hi
    have hfin := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hstep j
      (by omega : j ≤ k - i)
    have hgoal : (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
        = Function.uncurry (Work.Spaces.mixed j i h) := rfl
    rw [hgoal]
    exact hfin.continuousOn
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i h p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i h p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact (((hZ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).mul
      continuousOn_wdivsin_Q0).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((hM j i h.2).mul hWt)).pow 2
    · exact continuousOn_const

/-! ## Finite-order smoothness of the two summands of the straightened datum -/

/-- `Ψ` is `C^k` on the open quadrant (from `SmoothOpen Ψ`). -/
theorem contDiffOn_Psi_of_EllHypT {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ContDiffOn ℝ k (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp (honest_smoothOpen_Psi h) k

/-- The layer `Gsing α F · sin 2θ` is `C^k` on the open quadrant. -/
theorem contDiffOn_gsing_sin_of_EllHypT {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ContDiffOn ℝ k
      (Function.uncurry (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
  have hα1 : α ≤ 1 := by linarith
  have hGsm : ContDiffOn ℝ k (fun z : ℝ => Work.Elliptic.Gsing α F z) (Set.Ioi 0) :=
    (honest_Gsing_cDiff hα hα1 hk h).1 k (by omega)
  have hGprod : ContDiffOn ℝ k (fun p : ℝ × ℝ => Work.Elliptic.Gsing α F p.1)
      Work.FTS.EllipticEst.Q0 :=
    hGsm.comp contDiffOn_fst
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContDiffOn ℝ k (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact (hGprod.mul hsin).congr (fun p _ => rfl)

/-- The straightened datum is `C^k` on the open quadrant. -/
theorem contDiffOn_V_of_EllHypT {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    ContDiffOn ℝ k (Function.uncurry (Vfts α F Ψ)) Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_Psi_of_EllHypT h).add (contDiffOn_gsing_sin_of_EllHypT hα hα4 hk h)

/-! ## Honesty of the straightened datum -/

/-- **`V = Ψ + Gsing α F · sin 2θ` is honestly in `ℋ^k`** in the class `EllHypT`, under the
orthogonality condition. -/
theorem honest_HkMem_V {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypT α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vfts α F Ψ)) :
    Work.Spaces.HkMem α k (Vfts α F Ψ) := by
  have hVc := contDiffOn_V_of_EllHypT hα hα4 hk h
  have hΨc := contDiffOn_Psi_of_EllHypT h
  have hGc := contDiffOn_gsing_sin_of_EllHypT hα hα4 hk h
  refine HkMem_of_add_dominated_cont α k
    (continuousOn_HkIntegrand_of_contDiffOn hVc α)
    h.memPsi (honest_HkMem_gsing_sin hα hα4 h hOrth) ?_
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0]
    filter_upwards with θ
    rw [Work.Spaces.HkIntegrand_zero_z]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k Ψ 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k
      (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) 0 θ
    linarith
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | hpos
    · have hs : Real.sin (2 * θ) = 0 := by rw [← h0]; simp
      rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k (Vfts α F Ψ) z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k Ψ z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
          (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ hs]
      norm_num
    · rcases lt_or_eq_of_le hθ.2 with hlt | hpi
      · exact HkIntegrand_add_le_of_contDiffOn α k hΨc hGc z θ hzpos hpos hlt
      · have hs : Real.sin (2 * θ) = 0 := by
          rw [hpi, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k (Vfts α F Ψ) z θ hs,
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k Ψ z θ hs,
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
            (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ hs]
        norm_num

end Work.FTS.EllipticEst.Cores.DiagEstEllT
