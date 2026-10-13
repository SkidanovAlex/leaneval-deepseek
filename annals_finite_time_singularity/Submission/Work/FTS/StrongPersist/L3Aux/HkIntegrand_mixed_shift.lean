/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ^k`-integrand of a mixed derivative is dominated by a shifted integrand

This is the open-quadrant version of
`Work.FTS.StrongLWP.Sobolev.HkIntegrand_mixed_le`: the datum is only `C^∞` on the *open*
quadrant `Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`), and the point `(z,θ)`
ranges over the *closed* domain `Iz × Iθ`.

Both the commutation identity `D_z^qD_θ^p (D_z^bD_θ^a g) = D_z^{q+b}D_θ^{p+a} g` and the
comparison `w/sin(2θ)^{η/2} ≤ Wt = w·sin(2θ)^{-γ/2}` of the two weights are interior
statements, so the open-quadrant smoothness `SmoothOpen` suffices; on the angular boundary
`sin(2θ) = 0` and on the radial boundary `z = 0` both integrands vanish.

The proof is a term-by-term matching of the finitely many summands: the summands of
`HkIntegrand α k (D_z^bD_θ^a g)` are (after the commutativity above) the summands of
`HkIntegrand α (k+a+b) g` of the same order, the pure `D_z`-summands being compared through
the `sin(2θ)^{-η/2} ≤ sin(2θ)^{-γ/2}` inequality when the angular order `a` is positive.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Sobolev.HkIntegrand_mixed_le
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.H_le_Wt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Locality and commutation on an open set

`D_z` and `D_θ` are local operators, and they commute at every point at which the datum is
`C²` (Clairaut).  The lemmas below spell this out for an arbitrary *open* set `V` on which
the datum is `C^∞` in the genuine smooth order `Work.Stability.smoothOrder` — which is
exactly the shape of the hypothesis `Work.FTS.EllipticEst.SmoothOpen` at `V = Q0`. -/

/-- Two functions agreeing on an open set have the same `D_z`-iterates there. -/
private lemma DzIter_congr_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b F))
      (Function.uncurry (Work.Spaces.DzIter b G)) V := by
  induction b with
  | zero => exact h
  | succ n ih =>
      intro y hy
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2
      rw [hpz]

/-- On an open set on which `g` is `C^∞`, `D_z` commutes with every iterate of `D_θ`. -/
private theorem DzDthIterCommOn_open {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (hV.mem_nhds hy)).of_le (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- On an open set on which `g` is `C^∞`, `D_z^b` commutes with `D_θ^a`. -/
private theorem DzIterDthIterCommOn_open {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        DzDthIterCommOn_open hV (Work.FTS.LocData.contDiffOn_DzIter hV hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-- `D_z^qD_θ^p (D_z^bD_θ^a g) = D_z^{q+b}D_θ^{p+a} g` at every point of an open set on
which `g` is `C^∞`. -/
private theorem mixed_mixed_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (q p b a : ℕ)
    {z θ : ℝ} (hy : (z, θ) ∈ V) :
    Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (q + b) (p + a) g z θ := by
  have hX : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DthIter a g)) V :=
    Work.FTS.LocData.contDiffOn_DthIter hV hg a
  have hcommEq : Set.EqOn
      (Function.uncurry
        (Work.Spaces.DthIter p (Work.Spaces.DzIter b (Work.Spaces.DthIter a g))))
      (Function.uncurry
        (Work.Spaces.DzIter b (Work.Spaces.DthIter p (Work.Spaces.DthIter a g))))
      V := (DzIterDthIterCommOn_open hV hX b p).symm
  have h1 : Work.Spaces.DzIter q
        (Work.Spaces.DthIter p (Work.Spaces.DzIter b (Work.Spaces.DthIter a g))) z θ
      = Work.Spaces.DzIter q
        (Work.Spaces.DzIter b (Work.Spaces.DthIter p (Work.Spaces.DthIter a g))) z θ :=
    (DzIter_congr_of_isOpen hV hcommEq q) hy
  simp only [Work.Spaces.mixed]
  rw [h1, ← Work.Spaces.DzIter_add_right q b (Work.Spaces.DthIter p (Work.Spaces.DthIter a g)),
    Work.Spaces.DthIter_add_right p a g]

/-- The same identity on the open quadrant, in the shape used by the pointwise estimate. -/
private theorem mixed_mixed_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (q p b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (q + b) (p + a) g z θ :=
  mixed_mixed_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hg q p b a
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)

/-! ## Vanishing of the integrand on the boundary of the domain -/

/-- At `sin(2θ) = 0` the `ℋ^k`-integrand vanishes for every `f`: the `1/sin(2θ)^{η/2}` of
the first sum and the `Wt = w·sin(2θ)^{-γ/2}` of the second are both `0`. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have hgam : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hWt : Work.Spaces.Wt α z θ = 0 := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, hs,
      Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (div_pos hgam (by norm_num)))), mul_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [hWt, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- At `z = 0` the `ℋ^k`-integrand vanishes for every `f`, because the radial weight
`w = (1+z)²/z²` is `0` there (Lean's totalised division). -/
private lemma HkIntegrand_apply_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hw0, zero_div, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [Work.Spaces.Wt, hw0, zero_mul, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-! ## The pointwise domination -/

/-- **Every summand of `HkIntegrand α k (D_z^bD_θ^a g)` is a summand of
`HkIntegrand α (a+b+k) g`.**  The pure `D_z`-summands of the left-hand side are the
`D_z`-shifted pure summands of the right-hand side when `a = 0`, and the mixed summands
`(D_z^{p+b}D_θ^a g · Wt)²` when `a ≥ 1`; in both cases the weight
`w/sin(2θ)^{η/2} ≤ Wt` has to be paid only when a `D_θ` falls on the datum.  The mixed
summands of the left-hand side are shifted by the commutativity of the two operators. -/
private theorem hkIntegrand_mixed_shift_aux (α : ℝ) (hα : 0 < α) (k a b : ℕ)
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ
        ≤ Work.Spaces.HkIntegrand α (a + b + k) g z θ := by
  intro z hzI θ hθ
  have hz0le : (0 : ℝ) ≤ z := hzI
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α hα k (Work.Spaces.mixed b a g) hsin,
      HkIntegrand_eq_zero_of_sin α hα (a + b + k) g hsin]
  · -- the radial boundary `z = 0`: the left-hand integrand vanishes
    rcases eq_or_lt_of_le hz0le with hzo | hz
    · have h0 : Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ = 0 := by
        rw [← hzo]
        exact HkIntegrand_apply_zero α k (Work.Spaces.mixed b a g) θ
      rw [h0]
      exact Work.Spaces.HkIntegrand_nonneg α (a + b + k) g z θ
    · -- the interior of the domain
      have hθ0 : 0 < θ := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact absurd (by rw [← h]; simp) hsin
        · exact h
      have hθ1 : θ < π / 2 := by
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exact absurd (by rw [h]; rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) hsin
      set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
      set W : ℝ := Work.Spaces.Wt α z θ with hW
      have hHW : H ^ 2 ≤ W ^ 2 := by
        rw [hH, hW]; exact Work.Spaces.H_le_Wt α hα z θ hzI hθ
      -- The `(D_θ`-order, `D_z`-order)`-indexed building block of the two integrands.
      set T : ℕ × ℕ → ℝ := fun x =>
        if x.1 = 0 then (Work.Spaces.DzIter x.2 g z θ * H) ^ 2
        else (Work.Spaces.mixed x.2 x.1 g z θ * W) ^ 2 with hT
      have hTnn : ∀ x, 0 ≤ T x := by
        rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
      -- The index sets of the two sums of the right-hand side.
      set R1 : Finset (ℕ × ℕ) := (Finset.range (a + b + k + 1)).image (fun q => ((0 : ℕ), q))
        with hR1def
      set R2 : Finset (ℕ × ℕ) :=
        ((Finset.range (a + b + k + 1)) ×ˢ (Finset.range (a + b + k + 1))).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ a + b + k) with hR2def
      -- The index sets of the two sums of the left-hand side, shifted into the right-hand side.
      set S1 : Finset (ℕ × ℕ) := (Finset.range (k + 1)).image (fun p => (a, p + b)) with hS1def
      set S2 : Finset (ℕ × ℕ) :=
        (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)).image
            (fun x : ℕ × ℕ => (x.1 + a, x.2 + b)) with hS2def
      have hR1 : (∑ x ∈ R1, T x)
          = ∑ q ∈ Finset.range (a + b + k + 1), (Work.Spaces.DzIter q g z θ * H) ^ 2 := by
        rw [hR1def]
        have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q))
            (↑(Finset.range (a + b + k + 1)) : Set ℕ) := by
          intro x _ y _ h; simpa using h
        rw [Finset.sum_image (f := T) hinj]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        simp only [hT]; simp
      have hR2 : (∑ x ∈ R2, T x)
          = ∑ p ∈ Finset.range (a + b + k + 1), ∑ q ∈ Finset.range (a + b + k + 1),
              (if 1 ≤ p ∧ p + q ≤ a + b + k
                then (Work.Spaces.mixed q p g z θ * W) ^ 2 else 0) := by
        rw [hR2def, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        simp only [hT]
        by_cases hc : 1 ≤ p ∧ p + q ≤ a + b + k
        · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
        · rw [if_neg hc, if_neg hc]
      have hLHSunfold : Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ
          = (∑ p ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter p (Work.Spaces.mixed b a g) z θ * H) ^ 2)
            + ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
                (if 1 ≤ p ∧ p + q ≤ k
                  then (Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ * W) ^ 2
                  else 0) := by
        simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
      have hRHSunfold : Work.Spaces.HkIntegrand α (a + b + k) g z θ
          = (∑ q ∈ Finset.range (a + b + k + 1), (Work.Spaces.DzIter q g z θ * H) ^ 2)
            + ∑ p ∈ Finset.range (a + b + k + 1), ∑ q ∈ Finset.range (a + b + k + 1),
                (if 1 ≤ p ∧ p + q ≤ a + b + k
                  then (Work.Spaces.mixed q p g z θ * W) ^ 2 else 0) := by
        simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
      -- The first sum of the left-hand side sits on `S1`.
      have hS1 : (∑ p ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter p (Work.Spaces.mixed b a g) z θ * H) ^ 2)
          ≤ ∑ x ∈ S1, T x := by
        rw [hS1def]
        have hinj : Set.InjOn (fun p : ℕ => (a, p + b)) (↑(Finset.range (k + 1)) : Set ℕ) := by
          intro x _ y _ h; simpa using h
        rw [Finset.sum_image (f := T) hinj]
        refine Finset.sum_le_sum (fun p _ => ?_)
        simp only [hT]
        by_cases ha : a = 0
        · subst ha
          rw [if_pos rfl, Work.Spaces.mixed_zero_right,
            ← Work.Spaces.DzIter_add_right p b g]
        · rw [if_neg (by omega : ¬ a = 0)]
          have hDz : Work.Spaces.DzIter p (Work.Spaces.mixed b a g)
              = Work.Spaces.mixed (p + b) a g := by
            simp only [Work.Spaces.mixed]; rw [Work.Spaces.DzIter_add_right]
          rw [hDz]
          nlinarith [hHW, sq_nonneg (Work.Spaces.mixed (p + b) a g z θ)]
      -- The second sum of the left-hand side equals the sum on `S2`.
      have hS2 : (∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
            (if 1 ≤ p ∧ p + q ≤ k
              then (Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ * W) ^ 2 else 0))
          = ∑ x ∈ S2, T x := by
        rw [hS2def]
        have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + a, x.2 + b))
            (↑(((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
              (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)) : Set (ℕ × ℕ)) := by
          intro x _ y _ h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
        rw [Finset.sum_image (f := T) hinj, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        dsimp only
        by_cases hc : 1 ≤ p ∧ p + q ≤ k
        · rw [if_pos hc, if_pos hc]
          simp only [hT]
          rw [if_neg (by omega : ¬ p + a = 0)]
          rw [mixed_mixed_Q0 hg q p b a hz hθ0 hθ1]
        · rw [if_neg hc, if_neg hc]
      have hdisjS : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [hS1def, Finset.mem_image] at hx1
        obtain ⟨p, _, rfl⟩ := hx1
        rw [hS2def, Finset.mem_image] at hx2
        obtain ⟨y, hy, hxy⟩ := hx2
        rw [Finset.mem_filter] at hy
        simp only [Prod.mk.injEq] at hxy
        have hy1 : 1 ≤ y.1 := hy.2.1
        omega
      have hdisjR : Disjoint R1 R2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [hR1def, Finset.mem_image] at hx1
        obtain ⟨q, _, rfl⟩ := hx1
        rw [hR2def, Finset.mem_filter] at hx2
        have h := hx2.2.1
        simp only at h
        omega
      have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
        intro x hx
        rw [Finset.mem_union] at hx ⊢
        rcases hx with hx | hx
        · rw [hS1def, Finset.mem_image] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          rw [Finset.mem_range] at hp
          by_cases ha : a = 0
          · left
            rw [hR1def, Finset.mem_image]
            exact ⟨p + b, by rw [Finset.mem_range]; omega, by simp [ha]⟩
          · right
            rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
              Finset.mem_range]
            dsimp only
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
        · rw [hS2def, Finset.mem_image] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
          right
          rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          dsimp only
          exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      rw [hLHSunfold, hRHSunfold, ← hR1, ← hR2]
      calc _ ≤ (∑ x ∈ S1, T x) + (∑ x ∈ S2, T x) := add_le_add hS1 (le_of_eq hS2)
        _ = ∑ x ∈ S1 ∪ S2, T x := (Finset.sum_union hdisjS).symm
        _ ≤ ∑ x ∈ R1 ∪ R2, T x :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
        _ = (∑ x ∈ R1, T x) + (∑ x ∈ R2, T x) := Finset.sum_union hdisjR

/-- **The shifted `ℋ^k`-integrand of a mixed derivative** (the requested statement): for a
datum which is `C^∞` on the open quadrant and every `z ∈ [0,∞)`, `θ ∈ [0,π/2]`,

  `HkIntegrand α k (D_z^bD_θ^a g) z θ ≤ HkIntegrand α (k+a+b) g z θ`. -/
theorem HkIntegrand_mixed_shift (α : ℝ) (hα : 0 < α) (k a b : ℕ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ
        ≤ Work.Spaces.HkIntegrand α (k + a + b) g z θ := by
  intro z hz θ hθ
  have h := hkIntegrand_mixed_shift_aux α hα k a b hg z hz θ hθ
  rwa [show a + b + k = k + a + b from by omega] at h

end Work.FTS.StrongPersist.L3Aux
