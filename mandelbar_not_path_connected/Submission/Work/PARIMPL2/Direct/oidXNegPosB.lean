import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidSharpSn
import Submission.Work.PARIMPL2.Direct.oidNegCf_le_sin
import Submission.Work.PARIMPL2.Direct.oidXLeBetaAux
import Submission.Work.PARIMPL2.Direct.oidcnHelpers
import Submission.Work.PARIMPL2.Direct.oidSplitJ0
import Submission.Work.PARIMPL2.Direct.oidArcATel
import Submission.Work.PARIMPL2.Direct.oidArcBTel
import Submission.Work.PARIMPL2.Direct.oidArithB

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## The weighted cross-sum bound for `cr ≤ 0` and `0 ≤ Σ ocA`

We prove `Σ_{j<n} ocA_j · ∏_{i∈(j,n)} (1 + oidCf_i) ≤ 8(1+log R)` under the strip
hypotheses, `cr ≤ 0`, `oidCf_i ∈ [-1,0]`, and `0 ≤ Σ ocA_j ≤ 30`.

Since `cr ≤ 0`, every coefficient `C_i := oidCf_i` is `≤ 0`, so all factors
`1 + C_i ∈ [0,1]` and every backward product lies in `[0,1]`.  Let `j0` be the crossing
index of `λx` through `π/2` (`oidcn_exists_cross`): then `ocA_j ≤ 0` for `j < j0` (arc A)
and `ocA_j ≥ 0` for `j0 ≤ j < n` (arc B).

With `S := Σ_{j<n} ocA_j`, the algebraic splitting identity `oidSplitJ0` gives
```
X := Σ_{j<n} ocA_j ∏_{i∈(j,n)} (1+C_i)
   = Qb·(S + P) + E1,
Qb := ∏_{i∈[j0,n)} (1+C_i),
P  := Σ_{j<j0} (-ocA_j)·(1 - ∏_{i∈(j,j0)} (1+C_i))     ≥ 0,
E1 := Σ_{j∈[j0,n)} ocA_j·(∏_{i∈(j,n)} (1+C_i) - Qb)     ≥ 0.
```
Because `0 ≤ Qb ≤ 1`, `P ≥ 0` and `S ≥ 0`, we get `X ≤ S + P + E1`.

* On arc A (`j < j0`), `1 - ∏_{i∈(j,j0)}(1+C_i) ≤ Σ_{i∈(j,j0)} |C_i| ≤ |cr|·Σ_{i∈(j,j0)} λ²/sin²`,
  and the `lambda`-telescoping bound `oidArcATel` gives
  `Σ_{i∈(j,j0)} λ²/sin²(λx_i) ≤ 3λ·(-cot(λx_j))`.  Hence
  `(-ocA_j)·(...) ≤ 3|cr|·λ²cos²(λx_j)/D_j ≤ 3|cr|·λ²/D_j`, so `P ≤ 3|cr|·Σ_{j<j0} λ²/D_j`.
* On arc B (`j ≥ j0`), `∏_{i∈(j,n)}(1+C_i) - Qb ≤ 1 - ∏_{i∈[j0,j+1)}(1+C_i) ≤ Σ_{i∈[j0,j+1)}|C_i|`, and
  `oidArcBTel` bounds the telescoped `λ²/sin²` sum by `3λ cot(λx_j) + λ²/sin²(λx_j)`.  Using
  `λ cot(λx_j) ≤ 1/x_j ≤ 4/R` one gets the termwise bound
  `ocA_j·(...) ≤ |cr|(3 + 4/R)·λ²/D_j`, hence `E1 ≤ |cr|(3+4/R)·Σ_{j≥j0} λ²/D_j`.

Adding and using `hGoc` (`Σ_{j<n} λ²/D_j ≤ 24/R`) and `|cr| ≤ 3R/32 + 81/64`,
`X ≤ 30 + |cr|(3+4/R)(24/R) ≤ 8(1+log R)` (`oidArithB`). -/

/-- Arithmetic core of the arc-A term: for `0 < D`, `s ≠ 0`, `c² ≤ 1`,
`(-(λ s c/D))·(3λ(-(c/s))) ≤ 3λ²/D`. -/
private theorem keyA (lam D s c : ℝ) (hD : 0 < D) (_hs : s ≠ 0) (hc : c ^ 2 ≤ 1) :
    (-(lam * s * c / D)) * (3 * lam * (-(c / s))) ≤ 3 * (lam ^ 2 / D) := by
  have hkey : (-(lam * s * c / D)) * (3 * lam * (-(c / s))) = 3 * (lam ^ 2 * c ^ 2 / D) := by
    field_simp
  rw [hkey]
  have h3 : lam ^ 2 * c ^ 2 ≤ lam ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc (sq_nonneg lam); simpa using this
  have h2 : lam ^ 2 * c ^ 2 / D ≤ lam ^ 2 / D := div_le_div_of_nonneg_right h3 hD.le
  linarith

/-- Arithmetic core of the arc-B term: for `0 < R`, `0 < D`, `s ≠ 0`, `c² ≤ 1` and
`λ(c/s) ≤ 4/R`, `(λ s c/D)·(3λ(c/s) + λ²/s²) ≤ (3+4/R)·λ²/D`. -/
private theorem keyB (lam R D s c : ℝ) (hR : 0 < R) (hD : 0 < D) (_hs : s ≠ 0)
    (hc : c ^ 2 ≤ 1) (hcot : lam * (c / s) ≤ 4 / R) :
    (lam * s * c / D) * (3 * lam * (c / s) + lam ^ 2 / s ^ 2) ≤ (3 + 4 / R) * (lam ^ 2 / D) := by
  have hkey : (lam * s * c / D) * (3 * lam * (c / s) + lam ^ 2 / s ^ 2)
      = 3 * (lam ^ 2 * c ^ 2 / D) + (lam ^ 2 / D) * (lam * (c / s)) := by
    field_simp
  rw [hkey]
  have h3 : lam ^ 2 * c ^ 2 ≤ lam ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc (sq_nonneg lam); simpa using this
  have h4 : lam ^ 2 * c ^ 2 / D ≤ lam ^ 2 / D := div_le_div_of_nonneg_right h3 hD.le
  have h5 : (lam ^ 2 / D) * (lam * (c / s)) ≤ (lam ^ 2 / D) * (4 / R) :=
    mul_le_mul_of_nonneg_left hcot (div_nonneg (sq_nonneg lam) hD.le)
  have h6 : (3 + 4 / R) * (lam ^ 2 / D) = 3 * (lam ^ 2 / D) + (lam ^ 2 / D) * (4 / R) := by
    ring
  linarith [h4, h5, h6]

theorem oidXNegPosB (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcr0 : cr ≤ 0) (hcpR : |cr| ≤ 3 * R / 32 + 81 / 64)
    (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hGoc : ∑ j ∈ Finset.range n,
        lam ^ 2 / (Real.sin (lam * x j) ^ 2 + Real.sinh (lam * y j) ^ 2) ≤ 24 / R)
    (hCnp : ∀ j < n, Work.PARIMPL2.Direct.oidCf lam cr x y j ≤ 0)
    (hCabs : ∀ j < n, |Work.PARIMPL2.Direct.oidCf lam cr x y j| ≤ 1)
    (hSnn : 0 ≤ ∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j)
    (hS30 : ∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j ≤ 30) :
    ∑ j ∈ Finset.range n,
        Work.PARIMPL2.Direct.ocA lam x y j *
          ∏ i ∈ Finset.Ico (j + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i)
      ≤ 8 * (1 + Real.log R) := by
  classical
  have hRpos : (0:ℝ) < R := by linarith
  have habs : |cr| = -cr := abs_of_nonpos hcr0
  have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by linarith [hx1 j hj]
  have htxpos : ∀ j ≤ n, 0 < lam * x j := fun j hj => mul_pos hlam (hxpos j hj)
  have htxltpi : ∀ j ≤ n, lam * x j < Real.pi := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
    rw [he] at h
    have h2 : 0 < lam * R / 4 := by positivity
    linarith
  have hsinpos : ∀ j ≤ n, 0 < Real.sin (lam * x j) := fun j hj =>
    Real.sin_pos_of_pos_of_lt_pi (htxpos j hj) (htxltpi j hj)
  have hfac := oidXLeBeta_one_add_mem lam cr hlam hcr0 n x y hCabs hCnp
  obtain ⟨j0, hj0n, hneg, hposarc⟩ := oidcn_exists_cross lam hlam n x hdec
  have hAneg : ∀ j < j0, ocA lam x y j ≤ 0 := fun j hj =>
    oidXLeBeta_ocA_nonpos lam R hlam hR hlamR n x y hx2 hDpos j0 hj0n hneg j hj
  have hApos : ∀ j, j0 ≤ j → j < n → 0 ≤ ocA lam x y j := by
    intro j hj1 hj2
    have hjn : j ≤ n := le_of_lt hj2
    have hc : 0 ≤ Real.cos (lam * x j) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [htxpos j hjn, Real.pi_pos], hposarc j hj1 hj2⟩
    rw [ocA]
    exact div_nonneg (mul_nonneg (mul_nonneg hlam.le (hsinpos j hjn).le) hc) (hDpos j hjn).le
  have hGocD : ∑ j ∈ Finset.range n, lam ^ 2 / ocDen lam x y j ≤ 24 / R := by
    simpa [ocDen] using hGoc
  have hmain : (∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i))
        * ((∑ j ∈ Finset.range n, ocA lam x y j)
          + (∑ j ∈ Finset.range j0,
              (-ocA lam x y j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))))
      + (∑ j ∈ Finset.Ico j0 n, ocA lam x y j
          * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
            - ∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i)))
      ≤ 30 + |cr| * (3 + 4 / R) * (24 / R) := by
    have hQb_le1 : (∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i)) ≤ 1 :=
      oidcn_prod_le_one _ _ (fun i hi => (hfac i (Finset.mem_Ico.mp hi).2).1)
        (fun i hi => (hfac i (Finset.mem_Ico.mp hi).2).2)
    have hPnn : 0 ≤ ∑ j ∈ Finset.range j0,
        (-ocA lam x y j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i)) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      refine mul_nonneg (by linarith [hAneg j hjlt]) ?_
      exact sub_nonneg.mpr (oidcn_prod_le_one _ _
        (fun i hi => (hfac i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj0n)).1)
        (fun i hi => (hfac i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj0n)).2))
    have hPb : (∑ j ∈ Finset.range j0,
          (-ocA lam x y j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i)))
        ≤ 3 * |cr| * (∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      have hjn : j < n := lt_of_lt_of_le hjlt hj0n
      have hAj : 0 ≤ -ocA lam x y j := by linarith [hAneg j hjlt]
      have hprod_eq : (∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))
          = ∏ i ∈ Finset.Ico (j + 1) j0, (1 - |oidCf lam cr x y i|) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i < n := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj0n
        rw [abs_of_nonpos (hCnp i hi')]; ring
      have hunion : 1 - (∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))
          ≤ ∑ i ∈ Finset.Ico (j + 1) j0, |oidCf lam cr x y i| := by
        rw [hprod_eq]
        exact oidcn_one_sub_prod_le_sum _ _ (fun i _ => abs_nonneg _)
          (fun i hi => hCabs i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj0n))
      have hsum : ∑ i ∈ Finset.Ico (j + 1) j0, |oidCf lam cr x y i|
          ≤ |cr| * (∑ i ∈ Finset.Ico (j + 1) j0,
              lam ^ 2 / (Real.sin (lam * x i)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < n := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj0n
        have h := oidNegCf_le_sin lam cr hlam hcr0 n x y i hi'
          (hsinpos i (le_of_lt hi')) (hDpos i (le_of_lt hi'))
        rw [abs_of_nonpos (hCnp i hi'), habs]
        refine le_trans h (le_of_eq ?_)
        ring
      have htel : ∑ i ∈ Finset.Ico (j + 1) j0, lam ^ 2 / (Real.sin (lam * x i)) ^ 2
          ≤ 3 * lam * (-Real.cot (lam * x j)) :=
        oidArcATel lam hlam n j0 x hj0n hdec hneg (fun k hk => htxltpi k (by omega)) j hjlt
      have hstep : 1 - (∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))
          ≤ 3 * |cr| * lam * (-Real.cot (lam * x j)) := by
        calc 1 - (∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))
            ≤ ∑ i ∈ Finset.Ico (j + 1) j0, |oidCf lam cr x y i| := hunion
          _ ≤ |cr| * (∑ i ∈ Finset.Ico (j + 1) j0,
                lam ^ 2 / (Real.sin (lam * x i)) ^ 2) := hsum
          _ ≤ |cr| * (3 * lam * (-Real.cot (lam * x j))) :=
                mul_le_mul_of_nonneg_left htel (abs_nonneg cr)
          _ = 3 * |cr| * lam * (-Real.cot (lam * x j)) := by ring
      have hkey : (-ocA lam x y j) * (3 * |cr| * lam * (-Real.cot (lam * x j)))
          ≤ 3 * |cr| * (lam ^ 2 / ocDen lam x y j) := by
        have hD : 0 < ocDen lam x y j := hDpos j (le_of_lt hjn)
        have hs : Real.sin (lam * x j) ≠ 0 := ne_of_gt (hsinpos j (le_of_lt hjn))
        have hc : Real.cos (lam * x j) ^ 2 ≤ 1 := Real.cos_sq_le_one _
        have h1 := keyA lam (ocDen lam x y j) (Real.sin (lam * x j)) (Real.cos (lam * x j)) hD hs hc
        have heq : (-ocA lam x y j) * (3 * |cr| * lam * (-Real.cot (lam * x j)))
            = |cr| * ((-(lam * Real.sin (lam * x j) * Real.cos (lam * x j) / ocDen lam x y j))
                * (3 * lam * (-(Real.cos (lam * x j) / Real.sin (lam * x j))))) := by
          rw [ocA, Real.cot_eq_cos_div_sin]; ring
        rw [heq]
        calc |cr| * ((-(lam * Real.sin (lam * x j) * Real.cos (lam * x j) / ocDen lam x y j))
                * (3 * lam * (-(Real.cos (lam * x j) / Real.sin (lam * x j)))))
            ≤ |cr| * (3 * (lam ^ 2 / ocDen lam x y j)) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg cr)
          _ = 3 * |cr| * (lam ^ 2 / ocDen lam x y j) := by ring
      exact le_trans (mul_le_mul_of_nonneg_left hstep hAj) hkey
    have hE1b : (∑ j ∈ Finset.Ico j0 n, ocA lam x y j
          * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
            - ∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i)))
        ≤ |cr| * (3 + 4 / R) * (∑ j ∈ Finset.Ico j0 n, lam ^ 2 / ocDen lam x y j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hjn : j ≤ n := le_of_lt hj2
      have hAj : 0 ≤ ocA lam x y j := hApos j hj1 hj2
      have hconsec := Finset.prod_Ico_consecutive (fun i => 1 + oidCf lam cr x y i)
        (m := j0) (n := j + 1) (k := n) (by omega) (by omega)
      have hS1 : (∏ i ∈ Finset.Ico j0 (j + 1), (1 + oidCf lam cr x y i)) ≤ 1 :=
        oidcn_prod_le_one _ _
          (fun i hi => (hfac i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj2)).1)
          (fun i hi => (hfac i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj2)).2)
      have hS1nn : 0 ≤ (∏ i ∈ Finset.Ico j0 (j + 1), (1 + oidCf lam cr x y i)) :=
        Finset.prod_nonneg (fun i hi => (hfac i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj2)).1)
      have hWnn : 0 ≤ (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i)) :=
        Finset.prod_nonneg (fun i hi => (hfac i (Finset.mem_Ico.mp hi).2).1)
      have hWle1 : (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i)) ≤ 1 :=
        oidcn_prod_le_one _ _ (fun i hi => (hfac i (Finset.mem_Ico.mp hi).2).1)
          (fun i hi => (hfac i (Finset.mem_Ico.mp hi).2).2)
      have hprod_eq : (∏ i ∈ Finset.Ico j0 (j + 1), (1 + oidCf lam cr x y i))
          = ∏ i ∈ Finset.Ico j0 (j + 1), (1 - |oidCf lam cr x y i|) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i < n := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj2
        rw [abs_of_nonpos (hCnp i hi')]; ring
      have hunion : 1 - (∏ i ∈ Finset.Ico j0 (j + 1), (1 + oidCf lam cr x y i))
          ≤ ∑ i ∈ Finset.Ico j0 (j + 1), |oidCf lam cr x y i| := by
        rw [hprod_eq]
        exact oidcn_one_sub_prod_le_sum _ _ (fun i _ => abs_nonneg _)
          (fun i hi => hCabs i (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj2))
      have hsum : ∑ i ∈ Finset.Ico j0 (j + 1), |oidCf lam cr x y i|
          ≤ |cr| * (∑ i ∈ Finset.Ico j0 (j + 1),
              lam ^ 2 / (Real.sin (lam * x i)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < n := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hj2
        have h := oidNegCf_le_sin lam cr hlam hcr0 n x y i hi'
          (hsinpos i (le_of_lt hi')) (hDpos i (le_of_lt hi'))
        rw [abs_of_nonpos (hCnp i hi'), habs]
        refine le_trans h (le_of_eq ?_)
        ring
      have harc : ∀ k, j0 ≤ k → k ≤ j → 0 < lam * x k ∧ lam * x k ≤ Real.pi / 2 :=
        fun k hk1 hk2 => ⟨htxpos k (by omega), hposarc k hk1 (by omega)⟩
      have htel : ∑ i ∈ Finset.Ico j0 (j + 1), lam ^ 2 / (Real.sin (lam * x i)) ^ 2
          ≤ 3 * lam * Real.cot (lam * x j) + lam ^ 2 / (Real.sin (lam * x j)) ^ 2 :=
        oidArcBTel lam hlam j0 j x hj1 (fun k hk => hdec k (by omega)) harc
      have hsub : (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
            - ∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i)
          ≤ 1 - (∏ i ∈ Finset.Ico j0 (j + 1), (1 + oidCf lam cr x y i)) := by
        rw [← hconsec]
        nlinarith [hS1, hS1nn, hWnn, hWle1]
      have hstep : (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
            - ∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i)
          ≤ |cr| * (3 * lam * Real.cot (lam * x j) + lam ^ 2 / (Real.sin (lam * x j)) ^ 2) := by
        calc (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
              - ∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i)
            ≤ 1 - (∏ i ∈ Finset.Ico j0 (j + 1), (1 + oidCf lam cr x y i)) := hsub
          _ ≤ ∑ i ∈ Finset.Ico j0 (j + 1), |oidCf lam cr x y i| := hunion
          _ ≤ |cr| * (∑ i ∈ Finset.Ico j0 (j + 1),
                lam ^ 2 / (Real.sin (lam * x i)) ^ 2) := hsum
          _ ≤ |cr| * (3 * lam * Real.cot (lam * x j)
                + lam ^ 2 / (Real.sin (lam * x j)) ^ 2) :=
              mul_le_mul_of_nonneg_left htel (abs_nonneg cr)
      have hkey : ocA lam x y j
            * (3 * lam * Real.cot (lam * x j) + lam ^ 2 / (Real.sin (lam * x j)) ^ 2)
          ≤ (3 + 4 / R) * (lam ^ 2 / ocDen lam x y j) := by
        have hD : 0 < ocDen lam x y j := hDpos j hjn
        have hs : Real.sin (lam * x j) ≠ 0 := ne_of_gt (hsinpos j hjn)
        have hc : Real.cos (lam * x j) ^ 2 ≤ 1 := Real.cos_sq_le_one _
        have hcot1 : Real.cot (lam * x j) ≤ 1 / (lam * x j) :=
          oidSharp_cot_le_inv _ (htxpos j hjn) (htxltpi j hjn)
        have hcot2 : lam * Real.cot (lam * x j) ≤ 1 / x j := by
          have h := mul_le_mul_of_nonneg_left hcot1 hlam.le
          rwa [show lam * (1 / (lam * x j)) = 1 / x j by field_simp] at h
        have hcot3 : lam * Real.cot (lam * x j) ≤ 4 / R := by
          have h1 : 1 / x j ≤ 4 / R := by
            rw [div_le_div_iff₀ (hxpos j hjn) hRpos]
            have := hx1 j hjn; linarith
          linarith
        have hcot3' : lam * (Real.cos (lam * x j) / Real.sin (lam * x j)) ≤ 4 / R := by
          rwa [Real.cot_eq_cos_div_sin] at hcot3
        have h2 := keyB lam R (ocDen lam x y j) (Real.sin (lam * x j)) (Real.cos (lam * x j))
          hRpos hD hs hc hcot3'
        rw [ocA, Real.cot_eq_cos_div_sin]
        exact h2
      have e1 : ocA lam x y j
            * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i))
              - ∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i))
          ≤ ocA lam x y j
            * (|cr| * (3 * lam * Real.cot (lam * x j)
              + lam ^ 2 / (Real.sin (lam * x j)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep hAj
      have e2 : ocA lam x y j
            * (|cr| * (3 * lam * Real.cot (lam * x j)
              + lam ^ 2 / (Real.sin (lam * x j)) ^ 2))
          ≤ |cr| * (3 + 4 / R) * (lam ^ 2 / ocDen lam x y j) := by
        calc ocA lam x y j * (|cr| * (3 * lam * Real.cot (lam * x j)
                + lam ^ 2 / (Real.sin (lam * x j)) ^ 2))
            = |cr| * (ocA lam x y j * (3 * lam * Real.cot (lam * x j)
                + lam ^ 2 / (Real.sin (lam * x j)) ^ 2)) := by ring
          _ ≤ |cr| * ((3 + 4 / R) * (lam ^ 2 / ocDen lam x y j)) :=
              mul_le_mul_of_nonneg_left hkey (abs_nonneg cr)
          _ = |cr| * (3 + 4 / R) * (lam ^ 2 / ocDen lam x y j) := by ring
      exact le_trans e1 e2
    have hGAnn : 0 ≤ ∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j :=
      Finset.sum_nonneg (fun j hj =>
        div_nonneg (sq_nonneg lam) (hDpos j (le_trans (le_of_lt (Finset.mem_range.mp hj)) hj0n)).le)
    have hGBnn : 0 ≤ ∑ j ∈ Finset.Ico j0 n, lam ^ 2 / ocDen lam x y j :=
      Finset.sum_nonneg (fun j hj =>
        div_nonneg (sq_nonneg lam) (hDpos j (le_of_lt (Finset.mem_Ico.mp hj).2)).le)
    have hGAB : (∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j)
        + (∑ j ∈ Finset.Ico j0 n, lam ^ 2 / ocDen lam x y j) ≤ 24 / R := by
      rw [Finset.sum_range_add_sum_Ico (fun j => lam ^ 2 / ocDen lam x y j) hj0n]
      exact hGocD
    have h3R : (3:ℝ) ≤ 3 + 4 / R := by
      have : 0 < 4 / R := by positivity
      linarith
    have hsum3 : 3 * |cr| * (∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j)
        + |cr| * (3 + 4 / R) * (∑ j ∈ Finset.Ico j0 n, lam ^ 2 / ocDen lam x y j)
        ≤ |cr| * (3 + 4 / R) * (24 / R) := by
      have h1 : 3 * |cr| ≤ (3 + 4 / R) * |cr| := by
        have := mul_le_mul_of_nonneg_right h3R (abs_nonneg cr); linarith
      have hA1 : 3 * |cr| * (∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j)
          ≤ (3 + 4 / R) * |cr| * (∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j) :=
        mul_le_mul_of_nonneg_right h1 hGAnn
      have h2 : 0 ≤ |cr| * (3 + 4 / R) := mul_nonneg (abs_nonneg cr) (by linarith)
      have hA3 : |cr| * (3 + 4 / R)
            * ((∑ j ∈ Finset.range j0, lam ^ 2 / ocDen lam x y j)
              + (∑ j ∈ Finset.Ico j0 n, lam ^ 2 / ocDen lam x y j))
          ≤ |cr| * (3 + 4 / R) * (24 / R) := mul_le_mul_of_nonneg_left hGAB h2
      nlinarith [hA1, hA3, hGAnn, hGBnn, h3R, abs_nonneg cr]
    have hSP : (∏ i ∈ Finset.Ico j0 n, (1 + oidCf lam cr x y i))
          * ((∑ j ∈ Finset.range n, ocA lam x y j)
            + (∑ j ∈ Finset.range j0,
                (-ocA lam x y j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))))
        ≤ (∑ j ∈ Finset.range n, ocA lam x y j)
            + (∑ j ∈ Finset.range j0,
                (-ocA lam x y j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + oidCf lam cr x y i))) := by
      rw [mul_add]
      exact add_le_add (mul_le_of_le_one_left hSnn hQb_le1) (mul_le_of_le_one_left hPnn hQb_le1)
    linarith [hSP, hPb, hE1b, hsum3, hS30]
  rw [oidSplitJ0 (ocA lam x y) (oidCf lam cr x y) n j0 hj0n]
  exact le_trans hmain (oidArithB R cr hR hcpR)

end Work.PARIMPL2.Direct
