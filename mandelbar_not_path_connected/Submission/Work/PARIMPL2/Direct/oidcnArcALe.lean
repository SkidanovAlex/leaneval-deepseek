import Mathlib
import Submission.Work.PARIMPL2.Direct.oidcnHelpers
import Submission.Work.PARIMPL2.Direct.oidArcNeg
import Submission.Work.PARIMPL2.Direct.oidArcPos
import Submission.Work.PARIMPL2.Direct.orbitCrossBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## The "A" (negative arc) cross term for the `cr ≤ 0` case

We bound the second summand produced by `oidcnSplit`: on the negative arc `j < j0`
(where `λ x j > π/2`) we have `ocA ≤ 0` and each factor `1 + oidCf i ∈ [0,1]`.
Hence the tail product `∏_{i > j0} (1 + oidCf i)` lies in `[0,1]` and can be dropped,
and the remaining factor `1 - ∏_{i∈(j,j0]} (1 + oidCf i)` is dominated by
`exp(∑ oidCg) - 1`, to which `oidArcNeg` applies. -/

theorem oidcnArcALe (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcr : cr ≤ 0) (hcpR : |cr| ≤ 3 * R / 32 + 81 / 64)
    (n j0 : ℕ) (x y : ℕ → ℝ) (hj0 : j0 < n)
    (hneg : ∀ j < j0, Real.pi / 2 < lam * x j)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hCab1 : ∀ j < n, |Work.PARIMPL2.Direct.oidCf lam cr x y j| ≤ 1)
    (hSn : |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    (∑ j ∈ Finset.range j0, |Work.PARIMPL2.Direct.ocA lam x y j|
        * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i))
        * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i)))
      ≤ 8 * (Real.exp (12 * |cr| / R) - 1) := by
  have hRpos : (0 : ℝ) < R := by linarith
  -- Each factor `1 + oidCf i` lies in `[0,1]` for `i < n`.
  have hFmem : ∀ i, i < n → 0 ≤ 1 + oidCf lam cr x y i ∧ 1 + oidCf lam cr x y i ≤ 1 := by
    intro i hin
    have hnp : oidCf lam cr x y i ≤ 0 := oidCf_nonpos lam cr hlam hcr x y i
    have h2 : -oidCf lam cr x y i ≤ 1 := by
      have h := hCab1 i hin
      rwa [abs_of_nonpos hnp] at h
    constructor <;> linarith
  -- The tail product is in `[0,1]`.
  have hPnn : 0 ≤ ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i) :=
    Finset.prod_nonneg (fun i hi => (hFmem i (Finset.mem_Ico.mp hi).2).1)
  have hPle1 : (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i)) ≤ 1 :=
    oidcn_prod_le_one (Finset.Ico (j0 + 1) n) (fun i => 1 + oidCf lam cr x y i)
      (fun i hi => (hFmem i (Finset.mem_Ico.mp hi).2).1)
      (fun i hi => (hFmem i (Finset.mem_Ico.mp hi).2).2)
  -- `|cr| ≤ 3R/16`, as required by `oidArcNeg`.
  have hcpR16 : |cr| ≤ 3 * R / 16 := by linarith [hcpR, hR]
  -- Termwise domination by the exponential form.
  have hterm : ∀ j ∈ Finset.range j0,
      |ocA lam x y j| * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
        * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + oidCf lam cr x y i))
      ≤ |ocA lam x y j| *
          (Real.exp (∑ i ∈ Finset.Ico (j + 1) (j0 + 1), oidCg lam |cr| x y i) - 1) := by
    intro j hj
    have hjlt : j < j0 := Finset.mem_range.mp hj
    have hQi : ∀ i ∈ Finset.Ico (j + 1) (j0 + 1), i < n := fun i hi => by
      have h := (Finset.mem_Ico.mp hi).2; omega
    have hQle1 : (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + oidCf lam cr x y i)) ≤ 1 :=
      oidcn_prod_le_one (Finset.Ico (j + 1) (j0 + 1)) (fun i => 1 + oidCf lam cr x y i)
        (fun i hi => (hFmem i (hQi i hi)).1) (fun i hi => (hFmem i (hQi i hi)).2)
    have hQnn : 0 ≤ 1 - (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + oidCf lam cr x y i)) :=
      sub_nonneg.mpr hQle1
    have hE := oidcn_one_sub_prod_le_exp lam cr hlam hcr x y (Finset.Ico (j + 1) (j0 + 1))
      (fun i hi => hCab1 i (hQi i hi))
    rw [mul_assoc]
    calc |ocA lam x y j| * ((∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
            * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + oidCf lam cr x y i)))
        ≤ |ocA lam x y j| * (1 * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1),
            (1 + oidCf lam cr x y i))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPle1 hQnn) (abs_nonneg _)
      _ = |ocA lam x y j| *
            (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + oidCf lam cr x y i)) := by
          rw [one_mul]
      _ ≤ |ocA lam x y j| *
            (Real.exp (∑ i ∈ Finset.Ico (j + 1) (j0 + 1), oidCg lam |cr| x y i) - 1) :=
          mul_le_mul_of_nonneg_left hE (abs_nonneg _)
  have hArcNeg := oidArcNeg lam R |cr| hlam hR hlamR (abs_nonneg cr) hcpR16 n j0 x y
    (le_of_lt hj0) hneg hx1 hx2 hdec hDpos hSn
  calc (∑ j ∈ Finset.range j0, |ocA lam x y j|
          * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
          * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + oidCf lam cr x y i)))
      ≤ ∑ j ∈ Finset.range j0, |ocA lam x y j| *
          (Real.exp (∑ i ∈ Finset.Ico (j + 1) (j0 + 1), oidCg lam |cr| x y i) - 1) :=
        Finset.sum_le_sum hterm
    _ ≤ 8 * (Real.exp (12 * |cr| / R) - 1) := hArcNeg

end Work.PARIMPL2.Direct
