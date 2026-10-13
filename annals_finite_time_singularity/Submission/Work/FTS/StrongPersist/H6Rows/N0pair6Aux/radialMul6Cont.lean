import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the order-`6` `ℋ`-integrand of a radial multiple

For a radial factor `X` which is only `C^6` on `(0,∞)` (it is *not* smooth on a neighbourhood of
the closed quadrant, so none of the `C^∞`-machinery of `Work.Spaces` applies to the product) and
a datum `f` smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)`, the weighted integrand

`HkIntegrand α 6 (fun z θ => X z * f z θ)`

is continuous on the open quadrant.  Every one of the finitely many derivatives occurring in
`HkIntegrand` is a `z`-only combination of the `z`-only iterates of `D_z = z ∂_z`, so the
Leibniz expansion `H6Pair6Aux.leibniz_radial_mul` (which needs only `X` of class `C^6` on
`(0,∞)`) exhibits it as a finite sum of products of continuous functions.

The two weights `w z / sin(2θ)^{η/2}` and `W α z θ = w z / sin(2θ)^{γ/2}` are continuous on the
open quadrant since `sin(2θ) > 0` there.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open Set Filter

set_option maxHeartbeats 1600000

/-! ## The weights on the open quadrant -/

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The radial weight `w z = (1+z)²/z²` is continuous on the open quadrant. -/
private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- The angular weight `sin(2θ)^c` is continuous on the open quadrant. -/
private lemma continuousOn_sinpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 (Work.FTS.EllipticEst.mem_Q0.mp hp).2)))

/-- The product weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 _)

/-! ## The mixed derivatives of a radial multiple -/

/-- **Continuity of the mixed derivatives of a radial multiple.**  For `X` of class `C^6` on
`(0,∞)`, `f` smooth on the open quadrant and `j ≤ 6`, the function
`(z,θ) ↦ D_z^j D_θ^i (X · f) z θ` is continuous on `Q0` (with no restriction on `i`).

The key point is that the derivative in `z` may be transferred to the radial factor by
`H6Pair6Aux.leibniz_radial_mul`, which is available for a merely `C^6` factor `X`. -/
private lemma continuousOn_mixed_radial_mul {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {j i : ℕ} (hj : j ≤ 6) :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (fun z θ => X z * f z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  -- the Leibniz sum, which is manifestly continuous
  have hS : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
        (Work.Elliptic.DzdIter k X p.1 * Work.Spaces.mixed (j - k) i f p.1 p.2))
      Work.FTS.EllipticEst.Q0 := by
    refine continuousOn_finsetSum _ (fun k hk => ?_)
    have hk6 : k ≤ 6 := by
      have := Finset.mem_range.mp hk
      omega
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)
    · exact (Work.FTS.StrongPersist.L3Rhs.NfkAux.continuousOn_DzdIter_of_radial
        (r := X) (n := 6) (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := k) hk6).comp
        continuousOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    · exact (hf.mixed (j - k) i).continuousOn
  refine hS.congr (fun p hp => ?_)
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj p.1 p.2 hz hθ0 hθ1

/-! ## The requested continuity -/

theorem radialMul6Cont (α : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  -- the `D_z`-slots
  have hDz : ∀ i : ℕ, i ≤ 6 → ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i (fun z θ => X z * f z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun i hi => continuousOn_mixed_radial_mul (X := X) (f := f) hX hf (j := i) (i := 0) hi
  -- the mixed slots
  have hMx : ∀ j i : ℕ, i + j ≤ 6 → ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i (fun z θ => X z * f z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun j i hij => continuousOn_mixed_radial_mul (X := X) (f := f) hX hf (j := j) (i := i)
      (by omega)
  -- the weighted `D_z`-slot
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1
      / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_w_Q0.div (continuousOn_sinpow_Q0 _) (fun p hp =>
      ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Q0 (Work.FTS.EllipticEst.mem_Q0.mp hp).2) _))
  have hHk : (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (6 + 1),
              (Work.Spaces.DzIter i (fun z θ => X z * f z θ) p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
                if 1 ≤ i ∧ i + j ≤ 6
                then (Work.Spaces.mixed j i (fun z θ => X z * f z θ) p.1 p.2
                  * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (6 + 1)) (fun i hi => ?_)
    exact ((hDz i (by have := Finset.mem_range.mp hi; omega)).mul hwdiv).pow 2
  · refine continuousOn_finsetSum (Finset.range (6 + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (6 + 1)) (fun j _ => ?_))
    split_ifs with hic
    · exact (((hMx j i hic.2).mul (continuousOn_Wt_Q0 α))).pow 2
    · exact continuousOn_const

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
