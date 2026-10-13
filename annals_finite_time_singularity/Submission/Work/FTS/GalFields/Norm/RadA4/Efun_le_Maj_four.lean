/-
# `GalFields/Norm/RadA4/Efun_le_Maj_four` — the order-`4` pointwise majorant

`E1Parts.Efun_le_Maj` is the pointwise domination `Efun α f j z ≤ Maj α f j K z` for `j ≤ 3`.
The statement here is the same at `j ≤ 4`; the proof of the order-`3` version never uses its
bound on `j` (the `j`-dependence enters only through `j - b ≤ 4`, which holds as soon as
`j ≤ 4`), so the argument transfers verbatim: expand `Big` into a Leibniz sum plus the
`ampB`-term, apply `(a+b)² ≤ 2a² + 2b²`, bound every `D_z^b (ampA α)` by `K` and every
conditional block by `D_z^c (L₁₂ f)` (`dzdIter_L_as_if`), then Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) and `j.choose b ≤ 2^j`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Choose.Sum
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The pointwise domination of `Efun` by `Maj`, at order up to `4`.** -/
theorem Efun_le_Maj_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 4) {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.FTS.CoercivityFix.Transfer.E1Parts.Efun α f j z
        ≤ Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z := by
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
  have hbracket : |Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z|
      ≤ K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
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
      rw [Work.FTS.CoercivityFix.Transfer.E1Parts.dzdIter_L_as_if α hα hα1 hf hbj z hz]
    have h1 : |Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z|
        ≤ |-(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
          * (if j - b = 0 then Work.Coercivity.L12f f z
              else - Work.Elliptic.Qang f (j - b - 1) z))|
        + |(Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z)| := by
      rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Big_eq]
      exact abs_add_le _ _
    rw [abs_neg, abs_mul] at h1
    rw [hconv] at h1
    linarith [h1, hsum_bound]
  have hS_nn : 0 ≤ ∑ c ∈ Finset.range (j + 1),
      |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| :=
    Finset.sum_nonneg fun c _ => abs_nonneg _
  have hsq : (Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z) ^ 2
      ≤ 2 * ((K * 2 ^ j * (∑ c ∈ Finset.range (j + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
      + (|Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α|
        * |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z|) ^ 2) := by
    calc (Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z) ^ 2
        = |Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z| ^ 2 := by rw [sq_abs]
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
  rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Efun_eq_Big,
    Work.FTS.CoercivityFix.Transfer.E1Parts.Maj_eq]
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
  have hsq' : (Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z) ^ 2
        * (Work.Spaces.w z * Work.Spaces.w z)
      ≤ 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1) * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
            * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2)
        * (Work.Spaces.w z * Work.Spaces.w z) := by
    have hmain : (Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z) ^ 2
        ≤ 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)
        * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2) := by
      linarith [hsq, hAmaj, hBmaj.le, hBmaj.ge]
    exact mul_le_mul_of_nonneg_right hmain hw_nn
  have hexp : Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z
        * Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z
        * (Work.Spaces.w z * Work.Spaces.w z)
      = (Work.FTS.CoercivityFix.Transfer.E1Parts.Big α f j z) ^ 2
        * (Work.Spaces.w z * Work.Spaces.w z) := by ring
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

end Work.FTS.GalFields.Norm.RadA4
