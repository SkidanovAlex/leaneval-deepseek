/-
# `Cd6/Cd6Basic` — the `C^6`-on-`Q0` smoothness calculus of the operators `D_z`, `D_θ`

The `𝒲^{6,∞}`-priced product rule in the `C^6` (rather than `C^∞`) class needs the analogue
of the `SmoothOpen` API of `FTS/EllipticEst/OpenQDefs.lean` for the hypothesis

`CO6 h := ContDiffOn ℝ 6 (Function.uncurry h) Q0`  (`Q0 = (0,∞) × (0,π/2)`).

Everything used here is *finite order*: the operators `D_z = z∂_z` and `D_θ = sin(2θ)∂_θ`
each lose exactly one order of `ContDiffOn` on the open quadrant
(`ApproxCC.contDiffOn_partialZ/partialT`), and the multipliers `z` and `sin(2θ)` are smooth,
so `D_z^i D_θ^j h` is `C^{6-i-j}` on `Q0` as soon as `h` is `C^6` there.  Consequently the
weighted integrand `HkIntegrand α k h` is continuous on `Q0` for every `k ≤ 6`, which is the
input of the `a.e.`-strong-measurability argument of the assembly of the product rule.

All the order bookkeeping is phrased with *variables* (`M`, `N` and equations such as
`i + N = M`) rather than arithmetic inside the `ContDiffOn` order, because the order lives in
`WithTop ℕ∞` and `n - i` written directly there is re-elaborated as the `WithTop` subtraction.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.ApproxCC.contDiffOn_plainMixed
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.GalBasis.ApproxCC (partialZ partialT)

/-! ## The uncurried forms of `D_z` and `D_θ` -/

/-- `D_z X = z ∂_z X`, as an identity of uncurried functions. -/
theorem uncurry_Dz_eq (X : ℝ → ℝ → ℝ) :
    Function.uncurry (Work.Spaces.Dz X)
      = fun p : ℝ × ℝ => p.1 * partialZ (Function.uncurry X) p := rfl

/-- `D_θ X = sin(2θ) ∂_θ X`, as an identity of uncurried functions. -/
theorem uncurry_Dth_eq (X : ℝ → ℝ → ℝ) :
    Function.uncurry (Work.Spaces.Dth X)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * partialT (Function.uncurry X) p := rfl

/-- `(z,θ) ↦ sin(2θ)` is `C^n` on the open quadrant. -/
theorem contDiffOn_sin_two_snd (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
  (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).of_le le_top).contDiffOn).mono
    (Set.subset_univ _)

/-! ## The one-step order loss -/

/-- `D_z` loses one order of `ContDiffOn` on the open quadrant. -/
theorem contDiffOn_uncurry_Dz_step {M n : ℕ} {X : ℝ → ℝ → ℝ} (hn : n + 1 = M)
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz X)) Work.FTS.EllipticEst.Q0 := by
  rw [uncurry_Dz_eq]
  rw [← hn] at h
  exact contDiffOn_fst.mul
    (Work.FTS.GalBasis.ApproxCC.contDiffOn_partialZ Work.FTS.EllipticEst.isOpen_Q0 h)

/-- `D_θ` loses one order of `ContDiffOn` on the open quadrant. -/
theorem contDiffOn_uncurry_Dth_step {M n : ℕ} {X : ℝ → ℝ → ℝ} (hn : n + 1 = M)
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth X)) Work.FTS.EllipticEst.Q0 := by
  rw [uncurry_Dth_eq]
  rw [← hn] at h
  exact (contDiffOn_sin_two_snd n).mul
    (Work.FTS.GalBasis.ApproxCC.contDiffOn_partialT Work.FTS.EllipticEst.isOpen_Q0 h)

/-! ## The iterated operators -/

/-- `D_z^i h` is `C^N` on the open quadrant whenever `h` is `C^{i+N}` there. -/
theorem contDiffOn_uncurry_DzIter_aux {M : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ∀ i N : ℕ, i + N = M →
      ContDiffOn ℝ N (Function.uncurry (Work.Spaces.DzIter i X))
        Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero =>
      intro N hN
      rw [← hN] at h
      simpa using h
  | succ i ih =>
      intro N hN
      have h1 : ContDiffOn ℝ (N + 1) (Function.uncurry (Work.Spaces.DzIter i X))
          Work.FTS.EllipticEst.Q0 := ih (N + 1) (by omega)
      have h2 := contDiffOn_uncurry_Dz_step (M := N + 1) (n := N) (by omega) h1
      simpa only [Work.Spaces.DzIter_succ] using h2

/-- `D_θ^i h` is `C^N` on the open quadrant whenever `h` is `C^{i+N}` there. -/
theorem contDiffOn_uncurry_DthIter_aux {M : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ∀ i N : ℕ, i + N = M →
      ContDiffOn ℝ N (Function.uncurry (Work.Spaces.DthIter i X))
        Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero =>
      intro N hN
      rw [← hN] at h
      simpa using h
  | succ i ih =>
      intro N hN
      have h1 : ContDiffOn ℝ (N + 1) (Function.uncurry (Work.Spaces.DthIter i X))
          Work.FTS.EllipticEst.Q0 := ih (N + 1) (by omega)
      have h2 := contDiffOn_uncurry_Dth_step (M := N + 1) (n := N) (by omega) h1
      simpa only [Work.Spaces.DthIter_succ] using h2

/-- `D_z^j D_θ^i h` is `C^N` on the open quadrant whenever `h` is `C^{i+j+N}` there. -/
theorem contDiffOn_uncurry_mixed_aux {M : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ∀ j i N : ℕ, i + j + N = M →
      ContDiffOn ℝ N (Function.uncurry (Work.Spaces.mixed j i X))
        Work.FTS.EllipticEst.Q0 := by
  intro j i N hN
  set V : ℕ := j + N with hV
  have h1 : ContDiffOn ℝ V (Function.uncurry (Work.Spaces.DthIter i X))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_DthIter_aux h i V (by omega)
  have h2 : ContDiffOn ℝ N
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_DzIter_aux h1 j N (by omega)
  simpa only [Work.Spaces.mixed] using h2

/-- Continuity of `D_z^i h` on the open quadrant for `i ≤ 6`, for `h` of class `C^6`. -/
theorem continuousOn_uncurry_DzIter {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 6 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {i : ℕ} (hi : i ≤ 6) :
    ContinuousOn (Function.uncurry (Work.Spaces.DzIter i X)) Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_uncurry_DzIter_aux (M := 6) h i (6 - i) (by omega)).continuousOn

/-- Continuity of `D_z^j D_θ^i h` on the open quadrant for `i + j ≤ 6`. -/
theorem continuousOn_uncurry_mixed {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 6 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hij : i + j ≤ 6) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed j i X)) Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_uncurry_mixed_aux (M := 6) h j i (6 - i - j) (by omega)).continuousOn

/-- A pointwise product of two `C^6` functions on the open quadrant is `C^6`. -/
theorem contDiffOn_uncurry_mul_cd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ * g z θ))
      Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hf.mul hg

/-! ## Continuity of the weighted integrand on the open quadrant -/

/-- `HkIntegrand α k h` is continuous on the open quadrant, for `k ≤ 6`, as soon as `h` is
`C^6` there.  (The `SmoothOpen` version is `EllipticEst.SmoothOpen.continuousOn_HkIntegrand`.) -/
theorem continuousOn_HkIntegrand_cd6 {α : ℝ} {k : ℕ} (hk : k ≤ 6) {h : ℝ → ℝ → ℝ}
    (hh : ContDiffOn ℝ 6 (Function.uncurry h) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hz : ∀ i : ℕ, i ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i h p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
    fun i hi => continuousOn_uncurry_DzIter hh (Nat.le_trans hi hk)
  have hm : ∀ j i : ℕ, i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
    fun j i hij => continuousOn_uncurry_mixed hh (Nat.le_trans hij hk)
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
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
      rw [hfun2]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    refine hw.mul ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i h p.1 p.2
              * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i h p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact (((hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul
      Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j hj => ?_))
    split_ifs with hc
    · exact (((hm j i hc.2).mul hWt)).pow 2
    · exact continuousOn_const

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
