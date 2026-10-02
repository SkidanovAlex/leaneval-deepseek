import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidXNegPosB
import Submission.Work.PARIMPL2.Direct.oidCrossSplit
import Submission.Work.PARIMPL2.Direct.oidCrossNegNonpos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## The absolute-value form of the `cr ≤ 0`, `0 ≤ Σ ocA` bound

`oidXNegPosB` gives the one-sided bound `X ≤ 8(1+log R)` for the weighted cross-sum
`X := Σ_{j<n} ocA_j · ∏_{i∈(j,n)} (1 + oidCf_i)`, in the branch `cr ≤ 0`, `0 ≤ Σ ocA_j ≤ 30`.
Here we upgrade it to `|X| ≤ 8(1+log R)`, i.e. we add the lower bound `0 ≤ X`.

Since `cr ≤ 0` and `|oidCf_i| ≤ 1`, every factor `1 + oidCf_i` lies in `[0,1]`, so every
backward product `Q_j := ∏_{i∈(j,n)} (1 + oidCf_i)` lies in `[0,1]`.  Let `j0` be the crossing
index of `λx` through `π/2` (`oidcn_exists_cross`): `ocA_j ≤ 0` for `j < j0` and `ocA_j ≥ 0`
for `j0 ≤ j < n`.  Writing `Qb := Q_{j0} = ∏_{i∈(j0,n)} (1 + oidCf_i) ∈ [0,1]`, each product
`Q_j` is compared with `Qb` by monotonicity of products of factors in `[0,1]`:

* `j < j0`: `Q_j = (∏_{i∈(j,j0]} ·) · Qb ≤ Qb`, and `ocA_j ≤ 0`, hence `ocA_j·Q_j ≥ ocA_j·Qb`;
* `j0 ≤ j`: `Qb = (∏_{i∈(j0,j]} ·) · Q_j ≤ Q_j`, and `ocA_j ≥ 0`, hence `ocA_j·Q_j ≥ ocA_j·Qb`.

Summing, `X ≥ Qb · Σ_{j<n} ocA_j ≥ 0` because `Σ_{j<n} ocA_j ≥ 0`. -/

/-- Monotonicity of finite products of nonnegative real factors bounded by `1`: a larger index
set gives a smaller product.  (The Mathlib lemma `Finset.prod_le_prod_of_subset_of_le_one` needs
`[MulLeftMono ℝ]`, which does not exist.) -/
private theorem ocIco_prod_le_prod_le_one (s t : Finset ℕ) (f : ℕ → ℝ)
    (hsub : s ⊆ t) (hnn : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  have hkey := Finset.prod_sdiff hsub (f := f)
  have hle : ∏ i ∈ t \ s, f i ≤ 1 :=
    oidcn_prod_le_one _ _ (fun i hi => hnn i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1)
  have hnn' : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hnn i (hsub hi))
  calc ∏ i ∈ t, f i = (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := hkey.symm
    _ ≤ 1 * ∏ i ∈ s, f i := mul_le_mul_of_nonneg_right hle hnn'
    _ = ∏ i ∈ s, f i := one_mul _

theorem oidXNegPosAbs (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcr : cr ≤ 0) (hcrR2 : |cr| ≤ 3 * R / 32 + 81 / 64) (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hGoc : ∑ j ∈ Finset.range n, lam ^ 2 / Work.PARIMPL2.Direct.ocDen lam x y j ≤ 24 / R)
    (hCn : ∀ i < n, Work.PARIMPL2.Direct.oidCf lam cr x y i ≤ 0)
    (hCabs : ∀ i < n, |Work.PARIMPL2.Direct.oidCf lam cr x y i| ≤ 1)
    (hSnn : 0 ≤ ∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j)
    (hS30 : ∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j ≤ 30) :
    |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i)|
      ≤ 8 * (1 + Real.log R) := by
  have hGocB : ∑ j ∈ Finset.range n,
      lam ^ 2 / (Real.sin (lam * x j) ^ 2 + Real.sinh (lam * y j) ^ 2) ≤ 24 / R := by
    simpa [ocDen] using hGoc
  have hXnn : 0 ≤ ∑ j ∈ Finset.range n,
      ocA lam x y j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i) := by
    obtain ⟨j0, hj0n, hneg, hposarc⟩ := oidcn_exists_cross lam hlam n x hdec
    have hT : ∀ j < n, 0 ≤ 1 + oidCf lam cr x y j ∧ 1 + oidCf lam cr x y j ≤ 1 := by
      intro j hj
      have h1 := (abs_le.mp (hCabs j hj)).1
      have h2 := hCn j hj
      exact ⟨by linarith, by linarith⟩
    have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by linarith [hx1 j hj]
    have htxpos : ∀ j ≤ n, 0 < lam * x j := fun j hj => mul_pos hlam (hxpos j hj)
    have hAle : ∀ j < j0, ocA lam x y j ≤ 0 := fun j hj =>
      oidXLeBeta_ocA_nonpos lam R hlam hR hlamR n x y hx2 hDpos j0 hj0n hneg j hj
    have hAge : ∀ j, j0 ≤ j → j < n → 0 ≤ ocA lam x y j := by
      intro j hj1 hj2
      have hjn : j ≤ n := le_of_lt hj2
      have hc : 0 ≤ Real.cos (lam * x j) :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [htxpos j hjn, Real.pi_pos], hposarc j hj1 hj2⟩
      have hs : 0 ≤ Real.sin (lam * x j) :=
        Real.sin_nonneg_of_mem_Icc
          ⟨(htxpos j hjn).le, by linarith [hposarc j hj1 hj2, Real.pi_pos]⟩
      rw [ocA]
      exact div_nonneg (mul_nonneg (mul_nonneg hlam.le hs) hc) (hDpos j hjn).le
    have hQbnn : 0 ≤ ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i) :=
      Finset.prod_nonneg (fun i hi => (hT i (Finset.mem_Ico.mp hi).2).1)
    have hterm : ∀ j < n, ocA lam x y j * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
        ≤ ocA lam x y j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i) := by
      intro j hjn
      have hside : ∀ i ∈ Finset.Ico (j + 1) n,
          0 ≤ 1 + oidCf lam cr x y i ∧ 1 + oidCf lam cr x y i ≤ 1 :=
        fun i hi => hT i (Finset.mem_Ico.mp hi).2
      have hside2 : ∀ i ∈ Finset.Ico (j0 + 1) n,
          0 ≤ 1 + oidCf lam cr x y i ∧ 1 + oidCf lam cr x y i ≤ 1 :=
        fun i hi => hT i (Finset.mem_Ico.mp hi).2
      rcases lt_or_ge j j0 with hj | hj
      · refine mul_le_mul_of_nonpos_left ?_ (hAle j hj)
        refine ocIco_prod_le_prod_le_one (Finset.Ico (j0 + 1) n) (Finset.Ico (j + 1) n) _
          ?_ (fun i hi => (hside i hi).1) (fun i hi => (hside i hi).2)
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact Finset.mem_Ico.mpr ⟨by omega, h2⟩
      · refine mul_le_mul_of_nonneg_left ?_ (hAge j hj hjn)
        refine ocIco_prod_le_prod_le_one (Finset.Ico (j + 1) n) (Finset.Ico (j0 + 1) n) _
          ?_ (fun i hi => (hside2 i hi).1) (fun i hi => (hside2 i hi).2)
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact Finset.mem_Ico.mpr ⟨by omega, h2⟩
    have hsum : ∑ j ∈ Finset.range n,
          ocA lam x y j * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
        ≤ ∑ j ∈ Finset.range n,
          ocA lam x y j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr x y i) :=
      Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
    have hmul : (∑ j ∈ Finset.range n,
          ocA lam x y j * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i)))
        = (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i))
          * (∑ j ∈ Finset.range n, ocA lam x y j) := by
      rw [← Finset.sum_mul, mul_comm]
    rw [hmul] at hsum
    linarith [hsum, mul_nonneg hQbnn hSnn]
  rw [abs_of_nonneg hXnn]
  exact oidXNegPosB lam R cr hlam hR hlamR hcr hcrR2 n x y hx1 hx2 hdec hDpos hGocB
    hCn hCabs hSnn hS30

end Work.PARIMPL2.Direct
