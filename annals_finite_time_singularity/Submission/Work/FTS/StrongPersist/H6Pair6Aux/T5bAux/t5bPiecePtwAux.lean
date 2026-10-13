/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T5bAux/t5bPiecePtwAux` — the pointwise bound of a Leibniz summand `t5bPiece`

This module collects the analytic inputs of `T5bAux.t5bPiecePtwIntegrable`: the pointwise
bound of the summands

`t5bPiece f ρ a b k i = ρ(z,θ) · (D_z^kL₁₂ f)(z) · (D_θ^ic₂ₘ)(θ) · D_z^{b-k+1}D_θ^{a-i}f · D_z^bD_θ^af`

of the row `T5bRow` by the weighted `ℋ⁷`/`ℋ⁶` integrands of `f` on the open quadrant, together
with the elementary lemmas it rests on:

* finite-order smoothness of the radial iterates `(z∂_z)^k` (`contDiffOn_Zop_iterate`) and
  continuity of the `D_z`-iterates of `L₁₂(f)` on `(0,∞)`;
* continuity of the three leaf weights on the open quadrant;
* the AM–GM slot steps (`abs_mul_abs_mul_le_zslot`, `abs_mul_abs_mul_le_gam`,
  `sin_mul_abs_mul_abs_mul_le_gam`) turning the product of the two weighted slots into the sum
  of the two integrands;
* the weight identity `sq_mul_Wt_mul_sin` converting the `γ`-slot into the `(γ-1)`-weight.

Everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Finite-order smoothness of the radial iterates `(z∂_z)^k` -/

/-- If `r` is `C^K` on `(0,∞)` then its `k`-th `D_z`-iterate (`D_z = z∂_z`) is `C^{K-k}`
there, for `k ≤ K`: each application of `D_z` costs one derivative. -/
theorem contDiffOn_Zop_iterate {r : ℝ → ℝ} {K : ℕ}
    (h : ContDiffOn ℝ K r (Set.Ioi 0)) :
    ∀ k : ℕ, k ≤ K →
      ContDiffOn ℝ ((K - k : ℕ) : WithTop ℕ∞) ((Work.Spaces.Zop^[k]) r) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
      intro hk
      have hk' : k ≤ K := le_trans (Nat.le_succ k) hk
      have ih' := ih hk'
      rw [Function.iterate_succ_apply']
      show ContDiffOn ℝ ((K - (k + 1) : ℕ) : WithTop ℕ∞)
        (fun z => z * deriv ((Work.Spaces.Zop^[k]) r) z) (Set.Ioi 0)
      have hder : ContDiffOn ℝ ((K - (k + 1) : ℕ) : WithTop ℕ∞)
          (deriv ((Work.Spaces.Zop^[k]) r)) (Set.Ioi 0) :=
        ih'.deriv_of_isOpen isOpen_Ioi (by
          exact_mod_cast (show K - (k + 1) + 1 ≤ K - k by omega))
      exact contDiffOn_id.mul hder

/-- `L₁₂(f)` is `C⁷` on `(0,∞)` in the class of the row. -/
theorem contDiffOn_L12_seven {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 7 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
  (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα hα1 hso hm7 (by norm_num)).congr
    (fun z _ => (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm)

/-- The `D_z`-iterates of `L₁₂(f)` are continuous on `(0,∞)`. -/
theorem continuousOn_DzdIter_L12 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm7 : Work.Spaces.HkMem α 7 f)
    {k : ℕ} (hk : k ≤ 6) :
    ContinuousOn (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      (Set.Ioi 0) := by
  have hZ := contDiffOn_Zop_iterate (K := 7) (h := contDiffOn_L12_seven hα hα1 hso hm7) k
    (by omega)
  have hcont := hZ.continuousOn
  rwa [Work.FTS.StrongPersist.H6Pair6Aux.Zop_iter_eq_DzdIter] at hcont

/-! ## The leaf weights are continuous on the open quadrant -/

/-- The uncurried leaf weight of the slot `a` is continuous on the open quadrant. -/
theorem continuousOn_leaf_Q0 {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with rfl | rfl | ⟨_, rfl⟩
  · have h := (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta))
    exact h.congr (fun p _ => by simp only [Pi.mul_apply, Work.FTS.TransportS.leafEta])
  · simpa only [Work.FTS.TransportS.leafOne,
      Work.FTS.StrongPersist.H6Pair6Aux.leafOne_eq] using
      Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0
  · have h := (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α)))
    exact h.congr (fun p _ => by simp only [Pi.mul_apply, Work.FTS.TransportS.leafGam])

/-! ## The AM–GM slot steps -/

/-- If the squares of `A`, `B` are dominated by `P` resp. `Q`, then `|A||B| ≤ P + Q`. -/
theorem abs_mul_le_add_of_sq_le {P Q A B : ℝ} (hA : A ^ 2 ≤ P) (hB : B ^ 2 ≤ Q) :
    |A| * |B| ≤ P + Q := by
  have h1 : |A| * |B| ≤ (1 / 2) * A ^ 2 + (1 / 2) * B ^ 2 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.abs_mul_le_half A B
    rwa [abs_mul] at h
  have hP : 0 ≤ P := le_trans (sq_nonneg A) hA
  have hQ : 0 ≤ Q := le_trans (sq_nonneg B) hB
  linarith

/-- **The `η`-slot AM–GM step.**  If `|ρ|` is dominated by the square of the `D_z`-slot weight
`w/sin(2θ)^{η/2}` and the corresponding weighted squares of `X`, `Y` are slots of the levels
`7` resp. `6`, then `|ρ||X||Y|` is bounded by the sum of the two integrands. -/
theorem abs_mul_abs_mul_le_zslot {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {X Y z θ : ℝ}
    (hsn : 0 ≤ Real.sin (2 * θ))
    (hρ : |ρ z θ| ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
    (hX : (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f z θ)
    (hY : (Y * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    |ρ z θ| * |X| * |Y| ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
  have hW : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    div_nonneg (by rw [Work.Spaces.w]; positivity) (Real.rpow_nonneg hsn _)
  calc |ρ z θ| * |X| * |Y|
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 * |X| * |Y| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (abs_nonneg _)) (abs_nonneg _)
    _ = |X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
          * |Y * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hW]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
        abs_mul_le_add_of_sq_le hX hY

/-- **The `γ`-slot AM–GM step.**  The same as `abs_mul_abs_mul_le_zslot` with the mixed slot
weight `Wt α = w·sin(2θ)^{-γ/2}` on both `X` and `Y`. -/
theorem abs_mul_abs_mul_le_gam {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {X Y z θ : ℝ}
    (hsn : 0 ≤ Real.sin (2 * θ))
    (hρ : |ρ z θ| ≤ (Work.Spaces.Wt α z θ) ^ 2)
    (hX : (X * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ)
    (hY : (Y * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    |ρ z θ| * |X| * |Y| ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
  have hW : 0 ≤ Work.Spaces.Wt α z θ := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_nonneg (by rw [Work.Spaces.w]; positivity) (Real.rpow_nonneg hsn _)
  calc |ρ z θ| * |X| * |Y| ≤ (Work.Spaces.Wt α z θ) ^ 2 * |X| * |Y| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (abs_nonneg _)) (abs_nonneg _)
    _ = |X * Work.Spaces.Wt α z θ| * |Y * Work.Spaces.Wt α z θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hW]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
        abs_mul_le_add_of_sq_le hX hY

/-- **The `γ`-slot AM–GM step with a `sin(2θ)` factor.**  This is the form needed when the
angular coefficient contributes a factor `sin(2θ)`: the extra `sin(2θ)` (at most `1`) is spent
on `X`, whose weighted square is therefore allowed to carry it. -/
theorem sin_mul_abs_mul_abs_mul_le_gam {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {X Y z θ : ℝ}
    (hsn : 0 ≤ Real.sin (2 * θ))
    (hρ : |ρ z θ| ≤ (Work.Spaces.Wt α z θ) ^ 2)
    (hX : (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ)
    (hY : (Y * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    Real.sin (2 * θ) * |ρ z θ| * |X| * |Y|
      ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
  have hW : 0 ≤ Work.Spaces.Wt α z θ := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_nonneg (by rw [Work.Spaces.w]; positivity) (Real.rpow_nonneg hsn _)
  calc Real.sin (2 * θ) * |ρ z θ| * |X| * |Y|
      = Real.sin (2 * θ) * (|ρ z θ| * |X| * |Y|) := by ring
    _ ≤ Real.sin (2 * θ) * ((Work.Spaces.Wt α z θ) ^ 2 * |X| * |Y|) := by
        refine mul_le_mul_of_nonneg_left ?_ hsn
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (abs_nonneg _))
          (abs_nonneg _)
    _ = |X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)| * |Y * Work.Spaces.Wt α z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW, abs_of_nonneg hsn]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
        abs_mul_le_add_of_sq_le hX hY

/-- `(X·Wt α·sin 2θ)² ≤ w²·sin(2θ)^{-(γ-1)}·X²`: the `sin(2θ)`-factor (at most `1`) turns the
`γ`-slot weight `sin(2θ)^{-γ}` into a weight that is *dominated* by the `(γ-1)`-weight of
`domGm1`. -/
theorem sq_mul_Wt_mul_sin_le (α z θ X : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) (hs1 : Real.sin (2 * θ) ≤ 1) :
    (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) * X ^ 2 := by
  have hrw2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    rw [show (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ ((2 : ℝ)) by
      simpa using (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm, ← Real.rpow_add hs]
    congr 1
    ring
  have hpow : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
    linarith
  calc (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
      = X ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
    _ = X ^ 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * (Real.sin (2 * θ)) ^ 2 := by rw [Work.Spaces.bt_Wt_sq α z θ hα hθ]
    _ = X ^ 2 * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2) := by ring
    _ = X ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
        rw [hrw2]
    _ ≤ X ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) * X ^ 2 := by
        ring

/-! ## The pointwise bound on the open quadrant -/

/-- **The pointwise bound of a Leibniz summand** on the open quadrant.  Each of the five
factors of `t5bPiece` is bounded separately, and the two `f`-slots are paired by AM–GM. -/
theorem t5bPiece_abs_le_quad {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {M Cc : ℝ} {k i : ℕ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hab : a + b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hMnn : 0 ≤ M) (hCc : 0 ≤ Cc)
    (hA : ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ M)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hCcg : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter j (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    (hk : k ≤ b) (hi : i ≤ a) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |t5bPiece f ρ a b k i (z, θ)| ≤
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
  intro z θ hz hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongPersist.H6Pair6Aux.sin_two_pos hθIoo
  have hsn : 0 ≤ Real.sin (2 * θ) := le_of_lt hs
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hA' : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ M := hA z hz
  have hρnn : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθI
  have hcoef : (1 : ℝ) ≤ (b.choose k : ℝ) * (a.choose i : ℝ) := by
    have h1 : (1 : ℝ) ≤ (b.choose k : ℝ) := by
      have h := Nat.choose_pos hk
      exact_mod_cast (by omega : 1 ≤ b.choose k)
    have h2 : (1 : ℝ) ≤ (a.choose i : ℝ) := by
      have h := Nat.choose_pos hi
      exact_mod_cast (by omega : 1 ≤ a.choose i)
    nlinarith
  set X : ℝ := Work.Spaces.mixed (b - k + 1) (a - i) f z θ with hXdef
  set Y : ℝ := Work.Spaces.mixed b a f z θ with hYdef
  have hcore : |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
      * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
      * |X| * |Y|
      ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · -- ## Case `a = 0` (hence `i = 0`): the pure `D_z`-slots
      have hi0 : i = 0 := by omega
      have hB : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| ≤ Cc := by
        rw [hi0]
        simpa using hCcbd θ hθI
      have hρle : |ρ z θ| ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        rw [abs_of_nonneg hρnn]
        have h := Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_any (z := z) hα hleaf hθIoo
        rw [ha0] at h
        rw [wdivSq z θ hsn, ← Work.FTS.TransportS.slotW_zero_eq α hθIoo]
        exact h
      have hX2 : (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
        rw [hXdef, ha0, hi0, Nat.sub_zero, Work.Spaces.mixed_zero_right]
        exact Work.Spaces.sq_le_HkIntegrand_z α 7 f z θ (b - k + 1) (by omega)
      have hY2 : (Y * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        rw [hYdef, ha0, Work.Spaces.mixed_zero_right]
        exact Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ b (by omega)
      have hXY := abs_mul_abs_mul_le_zslot (α := α) (f := f) hsn hρle hX2 hY2
      calc |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| * |X| * |Y|
          = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|)
              * (|ρ z θ| * |X| * |Y|) := by ring
        _ ≤ (M * Cc) * (|ρ z θ| * |X| * |Y|) :=
            mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hMnn) le_rfl
              (by positivity) (mul_nonneg hMnn hCc)
        _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_left hXY (mul_nonneg hMnn hCc)
    · -- ## Case `a ≥ 1`: the mixed `γ`-slots
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have hρle : |ρ z θ| ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
        rw [abs_of_nonneg hρnn]
        have h1 : (Work.Spaces.Wt α z θ) ^ 2 = Work.FTS.TransportS.slotW α a z θ :=
          (Work.Spaces.bt_Wt_sq α z θ hα hθI).trans
            (Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθIoo).symm
        exact (Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_any (z := z) hα hleaf hθIoo).trans
          (le_of_eq h1.symm)
      have hY2 : (Y * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        rw [hYdef]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b ha1 (by omega)
      by_cases hi0 : i = 0
      · -- ## Case `a ≥ 1`, `i = 0`
        have hB : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| ≤ Cc := by
          rw [hi0]
          simpa using hCcbd θ hθI
        have hX2 : (X * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
          rw [hXdef, hi0, Nat.sub_zero]
          exact Work.Spaces.sq_le_HkIntegrand_mixed α 7 f z θ a (b - k + 1) ha1 (by omega)
        have hXY := abs_mul_abs_mul_le_gam (α := α) (f := f) hsn hρle hX2 hY2
        calc |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| * |X| * |Y|
            = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|)
                * (|ρ z θ| * |X| * |Y|) := by ring
          _ ≤ (M * Cc) * (|ρ z θ| * |X| * |Y|) :=
              mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hMnn) le_rfl
                (by positivity) (mul_nonneg hMnn hCc)
          _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
              mul_le_mul_of_nonneg_left hXY (mul_nonneg hMnn hCc)
      · -- ## Case `a ≥ 1`, `i ≥ 1`: the coefficient contributes a `sin(2θ)`
        have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        have hB : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
            ≤ Cc * Real.sin (2 * θ) := hCcg i hi1 (by omega) z θ hθI
        have hX2 : (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
            ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
          by_cases hai : a - i = 0
          · have hx : X = Work.Spaces.DzIter (b - k + 1) f z θ := by
              rw [hXdef, hai, Work.Spaces.mixed_zero_right]
            rw [hx]
            refine (sq_mul_Wt_mul_sin_le α z θ (Work.Spaces.DzIter (b - k + 1) f z θ) hα hθI hs
              hs1).trans ?_
            exact Work.FTS.StrongPersist.H6Pair6Aux.domGm1 (α := α) hα hα1 (f := f) (a' := 0)
              (b' := b - k + 1) (n := 7) hθIoo (by omega)
          · have hai1 : 1 ≤ a - i := Nat.one_le_iff_ne_zero.mpr hai
            have hX' : (X * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
              rw [hXdef]
              exact Work.Spaces.sq_le_HkIntegrand_mixed α 7 f z θ (a - i) (b - k + 1) hai1
                (by omega)
            calc (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
                = (X * Work.Spaces.Wt α z θ) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
              _ ≤ (X * Work.Spaces.Wt α z θ) ^ 2 * 1 :=
                  mul_le_mul_of_nonneg_left (by nlinarith [hsn, hs1]) (sq_nonneg _)
              _ = (X * Work.Spaces.Wt α z θ) ^ 2 := by ring
              _ ≤ Work.Spaces.HkIntegrand α 7 f z θ := hX'
        have hXY := sin_mul_abs_mul_abs_mul_le_gam (α := α) (f := f) hsn hρle hX2 hY2
        calc |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| * |X| * |Y|
            = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|)
                * (|ρ z θ| * |X| * |Y|) := by ring
          _ ≤ (M * (Cc * Real.sin (2 * θ))) * (|ρ z θ| * |X| * |Y|) :=
              mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hMnn) le_rfl
                (by positivity) (mul_nonneg hMnn (mul_nonneg hCc hsn))
          _ = M * Cc * (Real.sin (2 * θ) * |ρ z θ| * |X| * |Y|) := by ring
          _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
              mul_le_mul_of_nonneg_left hXY (mul_nonneg hMnn hCc)
  have habs : |t5bPiece f ρ a b k i (z, θ)|
      = |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        * |X| * |Y| := by
    simp only [t5bPiece, abs_mul, ← hXdef, ← hYdef]
  calc |t5bPiece f ρ a b k i (z, θ)|
      = |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        * |X| * |Y| := habs
    _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := hcore
    _ = 1 * (M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)) := by
        ring
    _ ≤ ((b.choose k : ℝ) * (a.choose i : ℝ))
          * (M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (mul_nonneg hMnn hCc)
            (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 7 f z θ)
              (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)))
    _ = ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
