/-
# `E1Parts/RadABnd` — continuity and the majorant bound for `Efun`

* `continuousOn_Big`, `continuousOn_Efun`: the explicit expression of `RadAPieces.Efun` is
  continuous on `(0,∞)`, since every block `D_z^b (ampA α)`, `D_z^j (ampB α)`, `D_z^c (L₁₂ f)`
  and the weight `w` are (`RadAZop.continuousOn_Zop_iter_of_contDiffOn` and `QangDiff`);
* `Efun_le_Maj`: the pointwise domination by the majorant `Maj`, from the boundedness of the
  `D_z`-iterates of `ampA` and Cauchy–Schwarz on the Leibniz sum.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `Big` is continuous on `(0,∞)`. -/
theorem continuousOn_Big (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) :
    ContinuousOn (Big α f j) (Set.Ioi (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  have hLcont : ContinuousOn (fun z : ℝ => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn α hα hα1 f hsm hmem).continuousOn
  have hAsm : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_ampA α hα hα1
  have hBsm : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_ampB α
  have hAcont : ∀ b : ℕ, b ≤ 3 → ContinuousOn (fun z : ℝ =>
      Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
      (Set.Ioi (0 : ℝ)) := by
    intro b hb
    have hZ : ContinuousOn (Work.Spaces.Zop^[b]
        (Work.FTS.CoercivityFix.Transfer.ampA α)) (Set.Ioi (0 : ℝ)) :=
      continuousOn_Zop_iter_of_contDiffOn (n := 3 - b)
        (hu := hAsm.of_le (by exact_mod_cast (by omega : b + (3 - b) ≤ 3)))
    simpa only [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter] using hZ
  have hBcont : ContinuousOn (fun z : ℝ =>
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z)
      (Set.Ioi (0 : ℝ)) := by
    have hZ : ContinuousOn (Work.Spaces.Zop^[j]
        (Work.FTS.CoercivityFix.Transfer.ampB α)) (Set.Ioi (0 : ℝ)) :=
      continuousOn_Zop_iter_of_contDiffOn (n := 0)
        (hu := hBsm.of_le (by exact_mod_cast (by omega : j + 0 ≤ 3)))
    simpa only [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter] using hZ
  have hcondcont : ∀ b : ℕ, ContinuousOn (fun z : ℝ =>
      if j - b = 0 then Work.Coercivity.L12f f z
      else - Work.Elliptic.Qang f (j - b - 1) z) (Set.Ioi (0 : ℝ)) := by
    intro b
    by_cases h : j - b = 0
    · rw [show (fun z : ℝ => if j - b = 0 then Work.Coercivity.L12f f z
          else - Work.Elliptic.Qang f (j - b - 1) z) = fun z : ℝ => Work.Coercivity.L12f f z
          from by funext z; rw [if_pos h]]
      exact hLcont
    · rw [show (fun z : ℝ => if j - b = 0 then Work.Coercivity.L12f f z
          else - Work.Elliptic.Qang f (j - b - 1) z)
          = fun z : ℝ => - Work.Elliptic.Qang f (j - b - 1) z
          from by funext z; rw [if_neg h]]
      exact ((Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).2 (j - b - 1) (by omega)).neg
  have hfun : Big α f j = fun z : ℝ =>
      -(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
    funext z; rw [Big_eq]
  rw [hfun]
  refine ContinuousOn.add ?_ (continuousOn_const.mul hBcont)
  refine ContinuousOn.neg ?_
  refine continuousOn_finsetSum _ fun b hb => ?_
  have hb3 : b ≤ 3 := by
    have := Finset.mem_range.mp hb
    omega
  exact (continuousOn_const.mul (hAcont b hb3)).mul (hcondcont b)

/-- `Efun` is continuous on `(0,∞)`. -/
theorem continuousOn_Efun (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) :
    ContinuousOn (Efun α f j) (Set.Ioi (0 : ℝ)) := by
  have hbig := continuousOn_Big α hα hα1 f hf hj
  have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
    have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hfun : Efun α f j = fun z : ℝ =>
      Big α f j z * Big α f j z * (Work.Spaces.w z * Work.Spaces.w z) := by
    funext z; rw [Efun_eq_Big]
  rw [hfun]
  exact (hbig.mul hbig).mul (hwcont.mul hwcont)

/-- `Efun` is nonnegative. -/
theorem Efun_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    0 ≤ Efun α f j z := by
  rw [Efun_eq_Big]
  have hw : 0 ≤ Work.Spaces.w z := by
    have hfun : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
    rw [hfun]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 : (0 : ℝ) ≤ Big α f j z * Big α f j z := mul_self_nonneg _
  have h2 : (0 : ℝ) ≤ Work.Spaces.w z * Work.Spaces.w z := mul_nonneg hw hw
  exact mul_nonneg h1 h2

/-- **The pointwise domination of `Efun` by `Maj`.** -/
theorem Efun_le_Maj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ z ∈ Set.Ioi (0 : ℝ), Efun α f j z ≤ Maj α f j K z := by
  intro z hz
  have hw_nn : 0 ≤ Work.Spaces.w z * Work.Spaces.w z := by
    have h : 0 ≤ Work.Spaces.w z := by
      have hfun : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      rw [hfun]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg h h
  have hchoose : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  -- the sum of the `L₁₂ f`-iterates
  have hsum_bound : |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z)|
      ≤ K * 2 ^ j * ∑ c ∈ Finset.range (j + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
    have hS_nn : 0 ≤ ∑ c ∈ Finset.range (j + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| :=
      Finset.sum_nonneg fun c _ => abs_nonneg _
    have hterm : ∀ b ∈ Finset.range (j + 1),
        |(j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
          * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z)|
        ≤ K * ((j.choose b : ℝ) * ∑ c ∈ Finset.range (j + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) := by
      intro b hb
      have hC : 0 ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
      have hb4 : b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hAb : |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd b hb4 z hz
      have hXb : |Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z|
          ≤ ∑ c ∈ Finset.range (j + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| :=
        Finset.single_le_sum (f := fun c => |Work.Elliptic.DzdIter c
            (Work.Coercivity.L12f f) z|) (fun c _ => abs_nonneg _) (Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hb
          omega))
      calc |(j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
            * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z)|
          = (j.choose b : ℝ) * |Work.Elliptic.DzdIter b
              (Work.FTS.CoercivityFix.Transfer.ampA α) z|
            * |Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC]
        _ ≤ (j.choose b : ℝ) * K * ∑ c ∈ Finset.range (j + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hAb hC) hXb (abs_nonneg _) ?_
            exact mul_nonneg hC hKnn
        _ = K * ((j.choose b : ℝ) * ∑ c ∈ Finset.range (j + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) := by ring
    have h3 : ∑ b ∈ Finset.range (j + 1), K * ((j.choose b : ℝ)
          * ∑ c ∈ Finset.range (j + 1), |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
        = K * 2 ^ j * ∑ c ∈ Finset.range (j + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, hchoose]
      ring
    have h2 := Finset.sum_le_sum hterm
    have h1 := Finset.abs_sum_le_sum_abs (s := Finset.range (j + 1))
      (f := fun b => (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z))
    linarith [h1, h2, h3.le, h3.ge]
  have hbracket : |Big α f j z| ≤ K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
      + |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
        * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z| := by
    have hconv : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
          * (if j - b = 0 then Work.Coercivity.L12f f z
              else - Work.Elliptic.Qang f (j - b - 1) z))
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
          * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have hbj : j - b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      rw [dzdIter_L_as_if α hα hα1 hf hbj z hz]
    have h1 : |Big α f j z| ≤ |-(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
          * (if j - b = 0 then Work.Coercivity.L12f f z
              else - Work.Elliptic.Qang f (j - b - 1) z))|
        + |(Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z)| := by
      rw [Big_eq]
      exact abs_add_le _ _
    rw [abs_neg, abs_mul] at h1
    rw [hconv] at h1
    linarith [h1, hsum_bound]
  have hS_nn : 0 ≤ ∑ c ∈ Finset.range (j + 1),
      |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| :=
    Finset.sum_nonneg fun c _ => abs_nonneg _
  have hsq : (Big α f j z) ^ 2 ≤ 2 * ((K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
      + (|Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
        * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z|) ^ 2) := by
    calc (Big α f j z) ^ 2 = |Big α f j z| ^ 2 := by rw [sq_abs]
      _ ≤ ((K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|))
          + (|Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
            * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z|)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hbracket 2
      _ ≤ 2 * ((K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
          + (|Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
            * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z|) ^ 2) := by
          nlinarith [sq_nonneg (K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
            - |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
              * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z|)]
  have hcs : (∑ c ∈ Finset.range (j + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
      (f := fun c => |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
    rw [Finset.card_range] at h
    simpa only [nsmul_eq_mul, sq_abs, Nat.cast_add, Nat.cast_one] using h
  have hAmaj : (K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
      ≤ (K * 2 ^ j) ^ 2 * ((j : ℝ) + 1) * ∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by
    have hK2 : 0 ≤ K * 2 ^ j := by positivity
    calc (K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
        = (K * 2 ^ j) ^ 2 * (∑ c ∈ Finset.range (j + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) ^ 2 := by ring
      _ ≤ (K * 2 ^ j) ^ 2 * (((j : ℝ) + 1) * ∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (K * 2 ^ j) ^ 2 * ((j : ℝ) + 1) * ∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by ring
  have hBmaj : (|Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
        * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z|) ^ 2
      = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 := by
    rw [mul_pow, sq_abs, sq_abs]
  rw [Efun_eq_Big, Maj_eq]
  rw [show (Work.Spaces.w z) ^ 2 = Work.Spaces.w z * Work.Spaces.w z from by ring]
  have hsumdist : (∑ c ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
      * (Work.Spaces.w z * Work.Spaces.w z)
      = ∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z * Work.Spaces.w z) := by
    rw [Finset.sum_mul]
  rw [← hsumdist]
  have hY_nn : 0 ≤ ∑ c ∈ Finset.range (j + 1),
      (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 :=
    Finset.sum_nonneg fun c _ => sq_nonneg _
  have hsq' : (Big α f j z) ^ 2 * (Work.Spaces.w z * Work.Spaces.w z)
      ≤ 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1) * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
            * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2)
        * (Work.Spaces.w z * Work.Spaces.w z) := by
    have hmain : (Big α f j z) ^ 2 ≤ 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)
        * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2) := by
      linarith [hsq, hAmaj, hBmaj.le, hBmaj.ge]
    exact mul_le_mul_of_nonneg_right hmain hw_nn
  have hexp : Big α f j z * Big α f j z * (Work.Spaces.w z * Work.Spaces.w z)
      = (Big α f j z) ^ 2 * (Work.Spaces.w z * Work.Spaces.w z) := by ring
  rw [hexp]
  have hexp2 : 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
        * ((∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
          * (Work.Spaces.w z * Work.Spaces.w z))
      + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
        * ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z * Work.Spaces.w z))
      = 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1) * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
            * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2)
        * (Work.Spaces.w z * Work.Spaces.w z) := by ring
  rw [hexp2]
  exact hsq'

end Work.FTS.CoercivityFix.Transfer.E1Parts
