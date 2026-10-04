import Mathlib
import Submission.Work.Diff.STE.DeTurckJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Degree bookkeeping for the entrywise bounds on the DeTurck operator `pPhi`

`Work.Diff.STE.DeTurck.pPhi` is built from the jet data `(A, L, B)`, `(Abar, Lbar, Bbar)` and the
inverse Gram matrices `jInv A`, `jInv Abar` by sums and products.  Every entry of the jet data is
bounded (by `M` in the foreground, `MB` in the background, `MA` for the Gram matrix `A`), and every
entry of `jInv` is bounded by `cl⁻¹`.

This file provides the bookkeeping used to propagate such bounds through arbitrary sums and
products: a `size` predicate `Lv dM dA dB dc K x` asserting

`|x| ≤ K * (1+M)^dM * (1+MA)^dA * (1+MB)^dB * (cl⁻¹)^dc`

together with the closure lemmas

* `Lv.mul` (products add the four degrees and multiply the constants),
* `Lv.add`, `Lv.sub`, `Lv.neg`, `Lv.smul`, `Lv.sum` (sums keep the degrees, constants add),
* `Lv.mono` (the degrees are monotone),
* `Lv.const`, `Lv.zero`.

The product is written in a *right-nested* way, so that `mul_nonneg hK (Lv.X_nonneg hh ..)`
is literally the product appearing in `Lv`, and `mul_le_mul` applies without reassociation.

Typical use (all factors nonnegative, hypotheses `hh : Hyp M MA MB cl`, `hK : 0 ≤ K`):

```lean
have h1 : Lv 1 0 0 0 K M MA MB cl (L (bB a) p q) := hL a p q
have h2 : Lv 1 0 0 0 K M MA MB cl (L (bB b) p q) := hL b p q
have h3 : Lv 1 0 0 0 (K + K) M MA MB cl (L (bB a) p q + L (bB b) p q) := Lv.add h1 h2 hh hK hK
exact Lv.smul (2⁻¹) h3
```
-/

open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.STE.Lead

open Work.Diff.EXT Work.Diff.STE.DeTurck

noncomputable section

/-- The size hypotheses: `M`, `MA`, `MB ≥ 1` and `0 < cl ≤ 1`. -/
structure Hyp (M MA MB cl : ℝ) : Prop where
  hM : 1 ≤ M
  hA : 1 ≤ MA
  hB : 1 ≤ MB
  hcl : 0 < cl
  hcl1 : cl ≤ 1

/-- `Lv dM dA dB dc K x` records the bound
`|x| ≤ K * (1+M)^dM * (1+MA)^dA * (1+MB)^dB * (cl⁻¹)^dc`. -/
def Lv (dM dA dB dc : ℕ) (K M MA MB cl x : ℝ) : Prop :=
  |x| ≤ K * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc)))

section Kit

variable {M MA MB cl : ℝ}

lemma Hyp.one_add_M_pos (hh : Hyp M MA MB cl) : 0 < 1 + M := by linarith [hh.hM]
lemma Hyp.one_add_A_pos (hh : Hyp M MA MB cl) : 0 < 1 + MA := by linarith [hh.hA]
lemma Hyp.one_add_B_pos (hh : Hyp M MA MB cl) : 0 < 1 + MB := by linarith [hh.hB]
lemma Hyp.inv_cl_pos (hh : Hyp M MA MB cl) : 0 < cl⁻¹ := inv_pos.mpr hh.hcl
lemma Hyp.one_le_inv_cl (hh : Hyp M MA MB cl) : 1 ≤ cl⁻¹ := by
  rw [one_le_inv₀ hh.hcl]; exact hh.hcl1
lemma Hyp.pow_M_nonneg (hh : Hyp M MA MB cl) (d : ℕ) : 0 ≤ (1 + M) ^ d :=
  pow_nonneg hh.one_add_M_pos.le d
lemma Hyp.pow_A_nonneg (hh : Hyp M MA MB cl) (d : ℕ) : 0 ≤ (1 + MA) ^ d :=
  pow_nonneg hh.one_add_A_pos.le d
lemma Hyp.pow_B_nonneg (hh : Hyp M MA MB cl) (d : ℕ) : 0 ≤ (1 + MB) ^ d :=
  pow_nonneg hh.one_add_B_pos.le d
lemma Hyp.pow_inv_nonneg (hh : Hyp M MA MB cl) (d : ℕ) : 0 ≤ (cl⁻¹) ^ d :=
  pow_nonneg hh.inv_cl_pos.le d

/-- The product appearing in `Lv` is nonnegative. -/
lemma Lv.X_nonneg (hh : Hyp M MA MB cl) (dM dA dB dc : ℕ) :
    0 ≤ (1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc)) :=
  mul_nonneg (hh.pow_M_nonneg dM)
    (mul_nonneg (hh.pow_A_nonneg dA) (mul_nonneg (hh.pow_B_nonneg dB) (hh.pow_inv_nonneg dc)))

/-- A constant is bounded at degree `0`. -/
lemma Lv.const (c M MA MB cl : ℝ) : Lv 0 0 0 0 |c| M MA MB cl c := by
  simp only [Lv, pow_zero, mul_one, le_refl]

/-- Monotonicity of the degrees. -/
lemma Lv.mono {dM1 dA1 dB1 dc1 dM2 dA2 dB2 dc2 : ℕ} {K x : ℝ}
    (h : Lv dM1 dA1 dB1 dc1 K M MA MB cl x) (hh : Hyp M MA MB cl) (hK : 0 ≤ K)
    (hM : dM1 ≤ dM2) (hA : dA1 ≤ dA2) (hB : dB1 ≤ dB2) (hc : dc1 ≤ dc2) :
    Lv dM2 dA2 dB2 dc2 K M MA MB cl x := by
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith [hh.hM]
  have hA1 : (1 : ℝ) ≤ 1 + MA := by linarith [hh.hA]
  have hB1 : (1 : ℝ) ≤ 1 + MB := by linarith [hh.hB]
  have hc1 : (1 : ℝ) ≤ cl⁻¹ := hh.one_le_inv_cl
  have hpM : (1 + M) ^ dM1 ≤ (1 + M) ^ dM2 := pow_le_pow_right₀ hM1 hM
  have hpA : (1 + MA) ^ dA1 ≤ (1 + MA) ^ dA2 := pow_le_pow_right₀ hA1 hA
  have hpB : (1 + MB) ^ dB1 ≤ (1 + MB) ^ dB2 := pow_le_pow_right₀ hB1 hB
  have hpc : (cl⁻¹) ^ dc1 ≤ (cl⁻¹) ^ dc2 := pow_le_pow_right₀ hc1 hc
  have e1 : (1 + MB) ^ dB1 * (cl⁻¹) ^ dc1 ≤ (1 + MB) ^ dB2 * (cl⁻¹) ^ dc2 :=
    mul_le_mul hpB hpc (hh.pow_inv_nonneg dc1) (hh.pow_B_nonneg dB2)
  have e2 : (1 + MA) ^ dA1 * ((1 + MB) ^ dB1 * (cl⁻¹) ^ dc1)
      ≤ (1 + MA) ^ dA2 * ((1 + MB) ^ dB2 * (cl⁻¹) ^ dc2) :=
    mul_le_mul hpA e1 (mul_nonneg (hh.pow_B_nonneg dB1) (hh.pow_inv_nonneg dc1))
      (hh.pow_A_nonneg dA2)
  have e3 : (1 + M) ^ dM1 * ((1 + MA) ^ dA1 * ((1 + MB) ^ dB1 * (cl⁻¹) ^ dc1))
      ≤ (1 + M) ^ dM2 * ((1 + MA) ^ dA2 * ((1 + MB) ^ dB2 * (cl⁻¹) ^ dc2)) :=
    mul_le_mul hpM e2 (mul_nonneg (hh.pow_A_nonneg dA1)
      (mul_nonneg (hh.pow_B_nonneg dB1) (hh.pow_inv_nonneg dc1))) (hh.pow_M_nonneg dM2)
  simp only [Lv] at h ⊢
  exact le_trans h (mul_le_mul_of_nonneg_left e3 hK)

/-- Products add the four degrees. -/
lemma Lv.mul {dM1 dA1 dB1 dc1 dM2 dA2 dB2 dc2 : ℕ} {K1 K2 x y : ℝ}
    (h1 : Lv dM1 dA1 dB1 dc1 K1 M MA MB cl x)
    (h2 : Lv dM2 dA2 dB2 dc2 K2 M MA MB cl y)
    (hh : Hyp M MA MB cl) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Lv (dM1 + dM2) (dA1 + dA2) (dB1 + dB2) (dc1 + dc2) (K1 * K2) M MA MB cl (x * y) := by
  simp only [Lv] at h1 h2 ⊢
  have hX1 : 0 ≤ (1 + M) ^ dM1 * ((1 + MA) ^ dA1 * ((1 + MB) ^ dB1 * (cl⁻¹) ^ dc1)) :=
    Lv.X_nonneg hh dM1 dA1 dB1 dc1
  rw [abs_mul]
  calc |x| * |y|
      ≤ (K1 * ((1 + M) ^ dM1 * ((1 + MA) ^ dA1 * ((1 + MB) ^ dB1 * (cl⁻¹) ^ dc1)))) *
        (K2 * ((1 + M) ^ dM2 * ((1 + MA) ^ dA2 * ((1 + MB) ^ dB2 * (cl⁻¹) ^ dc2)))) :=
        mul_le_mul h1 h2 (abs_nonneg y) (mul_nonneg hK1 hX1)
    _ = K1 * K2 * ((1 + M) ^ (dM1 + dM2) *
          ((1 + MA) ^ (dA1 + dA2) * ((1 + MB) ^ (dB1 + dB2) * (cl⁻¹) ^ (dc1 + dc2)))) := by
        simp only [pow_add]; ring

/-- Sums keep the degree, constants add. -/
lemma Lv.add {dM dA dB dc : ℕ} {K1 K2 x y : ℝ}
    (h1 : Lv dM dA dB dc K1 M MA MB cl x) (h2 : Lv dM dA dB dc K2 M MA MB cl y)
    (hh : Hyp M MA MB cl) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Lv dM dA dB dc (K1 + K2) M MA MB cl (x + y) := by
  simp only [Lv] at h1 h2 ⊢
  calc |x + y| ≤ |x| + |y| := abs_add_le x y
    _ ≤ K1 * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc)))
        + K2 * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) :=
        add_le_add h1 h2
    _ = (K1 + K2) * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) := by
        ring

/-- Differences keep the degree, constants add. -/
lemma Lv.sub {dM dA dB dc : ℕ} {K1 K2 x y : ℝ}
    (h1 : Lv dM dA dB dc K1 M MA MB cl x) (h2 : Lv dM dA dB dc K2 M MA MB cl y)
    (hh : Hyp M MA MB cl) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Lv dM dA dB dc (K1 + K2) M MA MB cl (x - y) := by
  simp only [Lv] at h1 h2 ⊢
  calc |x - y| = |x + (-y)| := by rw [sub_eq_add_neg]
    _ ≤ |x| + |-y| := abs_add_le x (-y)
    _ = |x| + |y| := by rw [abs_neg]
    _ ≤ K1 * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc)))
        + K2 * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) :=
        add_le_add h1 h2
    _ = (K1 + K2) * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) := by
        ring

/-- With *different* input degrees: take the componentwise maximum. -/
lemma Lv.addmax {dM1 dA1 dB1 dc1 dM2 dA2 dB2 dc2 : ℕ} {K1 K2 x y : ℝ}
    (h1 : Lv dM1 dA1 dB1 dc1 K1 M MA MB cl x) (h2 : Lv dM2 dA2 dB2 dc2 K2 M MA MB cl y)
    (hh : Hyp M MA MB cl) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Lv (max dM1 dM2) (max dA1 dA2) (max dB1 dB2) (max dc1 dc2) (K1 + K2) M MA MB cl
      (x + y) :=
  Lv.add (Lv.mono h1 hh hK1 (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _))
    (Lv.mono h2 hh hK2 (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
      (le_max_right _ _)) hh hK1 hK2

/-- With *different* input degrees: take the componentwise maximum. -/
lemma Lv.submax {dM1 dA1 dB1 dc1 dM2 dA2 dB2 dc2 : ℕ} {K1 K2 x y : ℝ}
    (h1 : Lv dM1 dA1 dB1 dc1 K1 M MA MB cl x) (h2 : Lv dM2 dA2 dB2 dc2 K2 M MA MB cl y)
    (hh : Hyp M MA MB cl) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Lv (max dM1 dM2) (max dA1 dA2) (max dB1 dB2) (max dc1 dc2) (K1 + K2) M MA MB cl
      (x - y) :=
  Lv.sub (Lv.mono h1 hh hK1 (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _))
    (Lv.mono h2 hh hK2 (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
      (le_max_right _ _)) hh hK1 hK2

/-- Negation keeps the degree. -/
lemma Lv.neg {dM dA dB dc : ℕ} {K x : ℝ} (h : Lv dM dA dB dc K M MA MB cl x) :
    Lv dM dA dB dc K M MA MB cl (-x) := by
  simp only [Lv] at h ⊢
  rwa [abs_neg]

/-- Multiplication by a scalar: the constant is multiplied by `|c|`. -/
lemma Lv.smul (c : ℝ) {dM dA dB dc : ℕ} {K x : ℝ}
    (h : Lv dM dA dB dc K M MA MB cl x) :
    Lv dM dA dB dc (|c| * K) M MA MB cl (c * x) := by
  simp only [Lv] at h ⊢
  rw [abs_mul]
  calc |c| * |x| ≤ |c| * (K * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc)))) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg c)
    _ = |c| * K * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) := by
        ring

/-- A finite sum keeps the degree; the constant is multiplied by the cardinality. -/
lemma Lv.sum {ι : Type*} [Fintype ι] {dM dA dB dc : ℕ} {K : ℝ} {f : ι → ℝ}
    (hf : ∀ i, Lv dM dA dB dc K M MA MB cl (f i)) (hh : Hyp M MA MB cl) (hK : 0 ≤ K) :
    Lv dM dA dB dc ((Fintype.card ι : ℝ) * K) M MA MB cl (∑ i, f i) := by
  simp only [Lv] at hf ⊢
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, K * ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) :=
        Finset.sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι : ℝ) * K *
          ((1 + M) ^ dM * ((1 + MA) ^ dA * ((1 + MB) ^ dB * (cl⁻¹) ^ dc))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

end Kit

end

end Work.Diff.STE.Lead
