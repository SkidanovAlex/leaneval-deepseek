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

/-! ## The positive-arc ("B") part of the negative-arc crossing bound

For `cr ≤ 0` the crossing coefficients satisfy `-1 ≤ C'_i ≤ 0`, so every factor
`1 + C'_i` lies in `[0,1]` and the partial products decrease as more factors are
included.  Writing `P_j = ∏_{i∈[j+1,n)}(1+C'_i)` and `Q = ∏_{i∈[j0+1,n)}(1+C'_i)`,
for `j0 ≤ j` we have `Q = P_j · ∏_{i∈[j0+1,j+1)}(1+C'_i)`, whence

`P_j - Q = P_j (1 - ∏_{i∈[j0+1,j+1)}(1+C'_i)) ≤ 1 - ∏_{i∈[j0+1,j+1)}(1+C'_i)
          ≤ exp (∑_{i∈[j0+1,j+1)} Cg_i) - 1`,

and the exponential form of the positive-arc estimate `oidArcPos` bounds the
resulting weighted sum by `6 (exp (12 |cr| / R) - 1)`. -/

theorem oidcnArcBLe (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcr : cr ≤ 0)
    (n j0 : ℕ) (x y : ℕ → ℝ) (hj0 : j0 < n)
    (hpos : ∀ j, j0 ≤ j → j < n → lam * x j ≤ Real.pi / 2)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hCab1 : ∀ j < n, |Work.PARIMPL2.Direct.oidCf lam cr x y j| ≤ 1)
    (hSn : |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    (∑ j ∈ Finset.Ico j0 n, Work.PARIMPL2.Direct.ocA lam x y j
        * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i)))
      ≤ 6 * (Real.exp (12 * |cr| / R) - 1) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by have := hx1 j hj; linarith
  have htpos : ∀ j ≤ n, 0 < lam * x j := fun j hj => mul_pos hlam (hxpos j hj)
  -- ## the factors `1 + C'_i` lie in `[0,1]`
  have hCnp : ∀ i, oidCf lam cr x y i ≤ 0 := oidCf_nonpos lam cr hlam hcr x y
  have hC0 : ∀ i, i < n → 0 ≤ 1 + oidCf lam cr x y i := by
    intro i hi
    have h1 := (abs_le.mp (hCab1 i hi)).1
    have h2 := hCnp i
    linarith
  have hC1 : ∀ i, i < n → 1 + oidCf lam cr x y i ≤ 1 := by
    intro i hi
    have h2 := hCnp i
    linarith
  -- ## `ocA` is nonnegative on the positive arc
  have hAnn : ∀ j, j0 ≤ j → j < n → 0 ≤ ocA lam x y j := by
    intro j hj1 hj2
    have hjn : j ≤ n := le_of_lt hj2
    have h0 : 0 < lam * x j := htpos j hjn
    have hπ : lam * x j ≤ Real.pi / 2 := hpos j hj1 hj2
    have hs : 0 < Real.sin (lam * x j) :=
      Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos, hπ])
    have hc : 0 ≤ Real.cos (lam * x j) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [h0, Real.pi_pos], hπ⟩
    rw [ocA]
    exact div_nonneg (mul_nonneg (mul_nonneg hlam.le hs.le) hc) (hDpos j hjn).le
  -- ## the pointwise comparison with the exponential form
  have hpt : ∀ j ∈ Finset.Ico j0 n,
      ocA lam x y j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
      ≤ ocA lam x y j
          * (Real.exp (∑ i ∈ Finset.Ico (j0 + 1) (j + 1), oidCg lam |cr| x y i) - 1) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    have hA := hAnn j hj1 hj2
    set P : ℝ := ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i) with hP
    set Q : ℝ := ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i) with hQ
    set S : ℝ := ∏ i ∈ Finset.Ico (j0 + 1) (j + 1), (1 + oidCf lam cr x y i) with hS
    set X : ℝ := ∑ i ∈ Finset.Ico (j0 + 1) (j + 1), oidCg lam |cr| x y i with hX
    have hQS : Q = S * P := by
      rw [hQ, hS, hP]
      exact (Finset.prod_Ico_consecutive (fun i => (1 + oidCf lam cr x y i))
        (by omega) (by omega)).symm
    have hP1 : P ≤ 1 := by
      rw [hP]
      exact oidcn_prod_le_one (Finset.Ico (j + 1) n)
        (fun i => 1 + oidCf lam cr x y i)
        (fun i hi => hC0 i (Finset.mem_Ico.mp hi).2)
        (fun i hi => hC1 i (Finset.mem_Ico.mp hi).2)
    have hsub : 1 - S ≤ Real.exp X - 1 := by
      rw [hS, hX]
      exact oidcn_one_sub_prod_le_exp lam cr hlam hcr x y (Finset.Ico (j0 + 1) (j + 1))
        (fun i hi => hCab1 i (by have := (Finset.mem_Ico.mp hi).2; omega))
    have hS1 : S ≤ 1 := by
      rw [hS]
      exact oidcn_prod_le_one (Finset.Ico (j0 + 1) (j + 1))
        (fun i => 1 + oidCf lam cr x y i)
        (fun i hi => hC0 i (by have := (Finset.mem_Ico.mp hi).2; omega))
        (fun i hi => hC1 i (by have := (Finset.mem_Ico.mp hi).2; omega))
    have hkey : P - Q ≤ Real.exp X - 1 := by
      rw [hQS]
      have h1 : P * (1 - S) ≤ 1 * (1 - S) := mul_le_mul_of_nonneg_right hP1 (by linarith)
      linarith [h1, hsub]
    have hPQ : (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
        - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i) = P - Q := by
      rw [hP, hQ]
    rw [hPQ, hX] at hkey ⊢
    exact mul_le_mul_of_nonneg_left hkey hA
  -- ## assembly: pointwise comparison plus the positive-arc estimate
  calc (∑ j ∈ Finset.Ico j0 n, ocA lam x y j
        * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i)))
      ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j
          * (Real.exp (∑ i ∈ Finset.Ico (j0 + 1) (j + 1), oidCg lam |cr| x y i) - 1) :=
        Finset.sum_le_sum hpt
    _ ≤ 6 * (Real.exp (12 * |cr| / R) - 1) :=
        oidArcPos lam R |cr| hlam hR hlamR (abs_nonneg cr) n j0 x y (le_of_lt hj0)
          hpos hx1 hx2 hdec hDpos hSn

end Work.PARIMPL2.Direct
