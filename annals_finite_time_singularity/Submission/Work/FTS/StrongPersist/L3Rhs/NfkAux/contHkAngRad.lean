import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Continuity of the `ℋ^k`-integrand of an angular `×` radial product

`HkIntegrand α k (fun z θ => a θ * r z)` is continuous on the open quadrant as soon as
the angular iterates `D_θ^i a` (`i ≤ k`) are continuous on `(0,π/2)` and the radial
iterates `D_z^b r` (`b ≤ k`) are continuous on `(0,∞)`.

The two unconditional separation identities `dzIter_ang_rad` / `mixed_ang_rad` rewrite the
iterates of the product `(z,θ) ↦ a θ · r z` as products of the iterates of the two
factors; the weights `w z` and `Wt α z θ` are continuous on the open quadrant (where
`z ≠ 0` and `sin(2θ) > 0`), so every summand is continuous.

This is the general-`k` form of the `k = 4` statement proved (privately) in
`Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le`. -/

private lemma continuousOn_mul_apply {f g : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun p => f p * g p) s :=
  (hf.mul hg).congr (fun p _ => (Pi.mul_apply f g p).symm)

private lemma continuousOn_pow_apply {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun p => f p ^ n) s :=
  (hf.pow n).congr (fun p _ => (Pi.pow_apply f n p).symm)

private lemma continuousOn_w_angRad :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private lemma continuousOn_sinpow_angRad (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2)))

private lemma continuousOn_wdivsin_angRad :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  continuousOn_w_angRad.div (continuousOn_sinpow_angRad (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2) _))

private lemma continuousOn_Wt_angRad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine (continuousOn_w_angRad.mul (continuousOn_sinpow_angRad (-(Work.Spaces.gam α / 2)))).congr
    (fun p _ => ?_)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, Pi.mul_apply]

theorem contHkAngRad (k : ℕ) (α : ℝ) (a r : ℝ → ℝ)
    (hcontA : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hcontR : ∀ b : ℕ, b ≤ k → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (fun z θ => a θ * r z)
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hA0 : ContinuousOn (fun θ : ℝ => a θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hcontA 0 (Nat.zero_le k)).congr (fun θ _ => by simp)
  have hA : ContinuousOn (fun p : ℝ × ℝ => a p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hA0.comp continuousOn_snd (fun p hp => hp.2)
  have hDzd : ∀ b : ℕ, b ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b r p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun b hb => (hcontR b hb).comp continuousOn_fst (fun p hp => hp.1)
  have hDth : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun i hi => (hcontA i hi).comp continuousOn_snd (fun p hp => hp.2)
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (a p.2 * Work.Elliptic.DzdIter i r p.1
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ (fun i hi => ?_)
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          a p.2 * Work.Elliptic.DzdIter i r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply hA (hDzd i (by have := Finset.mem_range.mp hi; omega))
      have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          (a p.2 * Work.Elliptic.DzdIter i r p.1)
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply h1 continuousOn_wdivsin_angRad
      exact continuousOn_pow_apply h2 2
    · refine continuousOn_finsetSum _ (fun i hi => continuousOn_finsetSum _ (fun j hj => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0)
            = fun p : ℝ × ℝ =>
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by
          funext p; rw [if_pos h]
        rw [hfun]
        have h1 : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply (hDth i (by have := Finset.mem_range.mp hi; omega))
            (hDzd j (by have := Finset.mem_range.mp hj; omega))
        have h2 : ContinuousOn (fun p : ℝ × ℝ =>
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) * Work.Spaces.Wt α p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply h1 (continuousOn_Wt_angRad α)
        exact continuousOn_pow_apply h2 2
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) = fun _ : ℝ × ℝ => (0 : ℝ) := by
          funext p; rw [if_neg h]
        rw [hfun]
        exact continuousOn_const
  · intro p _hp
    simp only [Work.Spaces.HkIntegrand, Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      Work.FTS.Nonlinear.Pieces.mixed_ang_rad]

end Work.FTS.StrongPersist.L3Rhs.NfkAux
