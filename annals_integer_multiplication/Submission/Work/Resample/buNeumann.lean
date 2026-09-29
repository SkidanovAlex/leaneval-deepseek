import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.buNeumannArith
import Submission.Work.Resample.buNeumannNum

set_option maxHeartbeats 1600000

namespace Work.Resample

open HvdH

/-! ## Tools for the Neumann truncation

We bound the truncation error of the alternating Neumann series
`(1+E)⁻¹ = 1 - E + E² - …` at `n = egN p α s t`, given that `E` contracts by
`c = 2^{-α²(t/s-1)}`. -/

/-- `(-A)^j = (-1)^j • A^j` for complex matrices. -/
lemma buNegPow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j : ℕ) :
    (-A) ^ j = (-1 : ℂ) ^ j • A ^ j := by
  have h : (-A : Matrix (Fin d) (Fin d) ℂ) = (-1 : ℂ) • A := by
    rw [neg_smul, one_smul]
  rw [h, smul_pow]

/-- Iterating a contraction. -/
lemma buPowNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ v : Fin d → ℂ, ‖A.mulVec v‖ ≤ c * ‖v‖) (j : ℕ) (v : Fin d → ℂ) :
    ‖(A ^ j).mulVec v‖ ≤ c ^ j * ‖v‖ := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    rw [show (A : Matrix (Fin d) (Fin d) ℂ) ^ (j + 1) = A ^ j * A from pow_succ A j,
        ← Matrix.mulVec_mulVec, show c ^ (j + 1) = c ^ j * c from pow_succ c j]
    calc ‖(A ^ j).mulVec (A.mulVec v)‖ ≤ c ^ j * ‖A.mulVec v‖ := ih (A.mulVec v)
      _ ≤ c ^ j * (c * ‖v‖) := mul_le_mul_of_nonneg_left (hA v) (pow_nonneg hc j)
      _ = (c ^ j * c) * ‖v‖ := by ring

/-- The geometric tail `∑_{i≥0} c^{i+n} B = c^n B/(1-c)`. -/
lemma buGeomTsum (c B : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n : ℕ) :
    ∑' i : ℕ, c ^ (i + n) * B = c ^ n * B / (1 - c) := by
  have hfun : (fun i : ℕ => c ^ (i + n) * B) = fun i : ℕ => c ^ n * (c ^ i * B) := by
    funext i; rw [pow_add]; ring
  rw [hfun, tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hc0 hc1]
  ring

/-- `‖(-1)^k • v‖ = ‖v‖`. -/
lemma buNormNegOne {d : ℕ} (k : ℕ) (v : Fin d → ℂ) : ‖(-1 : ℂ) ^ k • v‖ = ‖v‖ := by
  rw [norm_smul, norm_pow, show ‖(-1 : ℂ)‖ = 1 by simp, one_pow, one_mul]

/-- Truncation bound for the alternating Neumann series: if `‖A^j u‖ ≤ c^j ‖u‖` for every `j`
and `∑_j (-1)^j A^j u = w`, then the partial sum up to `n` is close to `w` (tail bound) and is
itself bounded by the geometric series. -/
private lemma buTail {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (u w : Fin d → ℂ) (n : ℕ)
    (hpow : ∀ j : ℕ, ‖(A ^ j).mulVec u‖ ≤ c ^ j * ‖u‖)
    (hHas : HasSum (fun j : ℕ => (-1 : ℂ) ^ j • ((A ^ j).mulVec u)) w) :
    ‖(∑ j ∈ Finset.range n, (-1 : ℂ) ^ j • ((A ^ j).mulVec u)) - w‖
        ≤ c ^ n * ‖u‖ / (1 - c) ∧
    ‖(∑ j ∈ Finset.range n, (-1 : ℂ) ^ j • ((A ^ j).mulVec u))‖ ≤ ‖u‖ * (1 - c)⁻¹ := by
  have hsumm : Summable fun j : ℕ => (-1 : ℂ) ^ j • ((A ^ j).mulVec u) := hHas.summable
  have hnormsumm : Summable fun j : ℕ => ‖(-1 : ℂ) ^ j • ((A ^ j).mulVec u)‖ := hsumm.norm
  have hinj : Function.Injective fun i : ℕ => i + n := fun a b h => Nat.add_right_cancel h
  have hshiftnorm :
      Summable fun i : ℕ => ‖(-1 : ℂ) ^ (i + n) • ((A ^ (i + n)).mulVec u)‖ :=
    hnormsumm.comp_injective hinj
  have hgeq : Summable fun i : ℕ => c ^ (i + n) * ‖u‖ :=
    ((summable_geometric_of_lt_one hc0 hc1).comp_injective hinj).mul_right ‖u‖
  have hstep : ∀ i : ℕ, ‖(-1 : ℂ) ^ (i + n) • ((A ^ (i + n)).mulVec u)‖ ≤ c ^ (i + n) * ‖u‖ := by
    intro i
    rw [buNormNegOne (i + n) ((A ^ (i + n)).mulVec u)]
    exact hpow (i + n)
  have htailbound :
      ‖∑' i : ℕ, (-1 : ℂ) ^ (i + n) • ((A ^ (i + n)).mulVec u)‖ ≤ c ^ n * ‖u‖ / (1 - c) := by
    refine le_trans (norm_tsum_le_tsum_norm hshiftnorm) ?_
    refine le_trans (Summable.tsum_le_tsum hstep hshiftnorm hgeq) ?_
    exact le_of_eq (buGeomTsum c ‖u‖ hc0 hc1 n)
  have hsplit : (∑ i ∈ Finset.range n, (-1 : ℂ) ^ i • ((A ^ i).mulVec u))
      + (∑' i : ℕ, (-1 : ℂ) ^ (i + n) • ((A ^ (i + n)).mulVec u))
      = ∑' i : ℕ, (-1 : ℂ) ^ i • ((A ^ i).mulVec u) :=
    Summable.sum_add_tsum_nat_add n hsumm
  have hw : (∑' i : ℕ, (-1 : ℂ) ^ i • ((A ^ i).mulVec u)) = w := hHas.tsum_eq
  have hdiff : (∑ i ∈ Finset.range n, (-1 : ℂ) ^ i • ((A ^ i).mulVec u)) - w
      = -(∑' i : ℕ, (-1 : ℂ) ^ (i + n) • ((A ^ (i + n)).mulVec u)) := by
    rw [← hw, ← hsplit]; abel
  have hsum2 : ∑ i ∈ Finset.range n, ‖(-1 : ℂ) ^ i • ((A ^ i).mulVec u)‖
      ≤ ∑ i ∈ Finset.range n, c ^ i * ‖u‖ := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [buNormNegOne i ((A ^ i).mulVec u)]
    exact hpow i
  have hsum3 : ∑ i ∈ Finset.range n, c ^ i * ‖u‖ = (∑ i ∈ Finset.range n, c ^ i) * ‖u‖ :=
    (Finset.sum_mul _ _ _).symm
  have hgeo : ∑ i ∈ Finset.range n, c ^ i ≤ (1 - c)⁻¹ := by
    have hpos : 0 < 1 - c := by linarith
    have hgm : (∑ i ∈ Finset.range n, c ^ i) * (1 - c) = 1 - c ^ n := geom_sum_mul_neg c n
    have hcn : c ^ n ≤ 1 := pow_le_one₀ hc0 (le_of_lt hc1)
    have h1 : (1 - c) * (∑ i ∈ Finset.range n, c ^ i) ≤ 1 := by
      calc (1 - c) * (∑ i ∈ Finset.range n, c ^ i) = 1 - c ^ n := by rw [mul_comm, hgm]
        _ ≤ 1 := sub_le_self 1 (pow_nonneg hc0 n)
    have h2 := (le_inv_mul_iff₀ hpos).mpr h1
    simpa using h2
  constructor
  · rw [hdiff, norm_neg]; exact htailbound
  · calc ‖∑ i ∈ Finset.range n, (-1 : ℂ) ^ i • ((A ^ i).mulVec u)‖
        ≤ ∑ i ∈ Finset.range n, ‖(-1 : ℂ) ^ i • ((A ^ i).mulVec u)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, c ^ i * ‖u‖ := hsum2
      _ = (∑ i ∈ Finset.range n, c ^ i) * ‖u‖ := hsum3
      _ ≤ (1 - c)⁻¹ * ‖u‖ := mul_le_mul_of_nonneg_right hgeo (norm_nonneg u)
      _ = ‖u‖ * (1 - c)⁻¹ := by ring

/-- Truncation of the Neumann series `N⁻¹ = I - E + E² - …` at `n = egN p α s t`:
the truncated alternating sum is within `2^{-p}` of `(1/2) • Jmat • z`, and has norm `≤ 1`.
(`egN p α s t = ⌈p s/(α²(t-s))⌉`; `ResMath1DProp` supplies `Jmat z = ∑_j (-E)^j z` (`HasSum`) and
`‖E u‖ ≤ 2^{-α²(t/s-1)}‖u‖`; `θ = t/s - 1 ≥ p/α⁴ > 0` gives `α²θ ≥ 1`, so the tail
`‖∑_{j≥n} (-1)^j E^j (z/2)‖ ≤ (1/2)·2^{-α²θn}/(1 - 2^{-α²θ}) ≤ 2^{-p}` because `α²θ·n ≥ p`.) -/
theorem buNeumann (RM : HvdH.ResMath1DProp) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
    (hcop : Nat.Coprime s t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
    (z : Fin s → ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(∑ j ∈ Finset.range (Work.Resample.egN p α s t), (-1 : ℂ) ^ j •
        ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • z))
      - (1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec z)‖ ≤ 1 / (2 : ℝ) ^ p ∧
    ‖(∑ j ∈ Finset.range (Work.Resample.egN p α s t), (-1 : ℂ) ^ j •
        ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • z))‖ ≤ 1 := by
  obtain ⟨ha1, han⟩ := buNeumannArith p α s t hs hst hα hαp hθ
  obtain ⟨-, -, -, hEn, hHasE, -, -, -⟩ := RM s t α p hs hst hcop hα hαp hθ
  let a : ℝ := (α : ℝ) ^ 2 * ((t : ℝ) / s - 1)
  let c : ℝ := (2 : ℝ) ^ (-a)
  let u : Fin s → ℂ := (1 / 2 : ℂ) • z
  let w : Fin s → ℂ := (HvdH.Jmat s t α).mulVec u
  have ha1' : 1 ≤ a := ha1
  have han' : (p : ℝ) ≤ a * (egN p α s t : ℕ) := han
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1'
  have hc0 : 0 ≤ c := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-a))
  have hc1 : c < 1 := (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mpr
    (Or.inl ⟨by norm_num, by linarith⟩)
  have hEn' : ∀ v : Fin s → ℂ, ‖(HvdH.Emat s t α).mulVec v‖ ≤ c * ‖v‖ := fun v => hEn v
  have hpow : ∀ j : ℕ, ‖((HvdH.Emat s t α) ^ j).mulVec u‖ ≤ c ^ j * ‖u‖ :=
    fun j => buPowNorm (HvdH.Emat s t α) c hc0 hEn' j u
  have hHas : HasSum (fun j : ℕ => (-1 : ℂ) ^ j • (((HvdH.Emat s t α) ^ j).mulVec u)) w := by
    have h0 : HasSum (fun j : ℕ => (-1 : ℂ) ^ j • (((HvdH.Emat s t α) ^ j).mulVec u))
        ((HvdH.Jmat s t α).mulVec u) :=
      (hHasE u).congr_fun (fun j => by rw [buNegPow (HvdH.Emat s t α) j, Matrix.smul_mulVec])
    exact h0
  have hwu : (1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec z) = w := by
    show (1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec z)
      = (HvdH.Jmat s t α).mulVec ((1 / 2 : ℂ) • z)
    rw [Matrix.mulVec_smul]
  obtain ⟨hbt1, hbt2⟩ :=
    buTail (HvdH.Emat s t α) c hc0 hc1 u w (egN p α s t) hpow hHas
  have hu : ‖u‖ ≤ 1 / 2 := by
    show ‖(1 / 2 : ℂ) • z‖ ≤ 1 / 2
    rw [norm_smul]
    have h1 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [h1]
    linarith [norm_nonneg z, hz]
  have hnum := buNeumannNum p (egN p α s t) a ha1' han'
  have hnum1 : (1 / 2) * (c ^ (egN p α s t) / (1 - c)) ≤ 1 / (2 : ℝ) ^ p := hnum.1
  have hnum2 : (1 / 2) * (1 - c)⁻¹ ≤ 1 := hnum.2
  have hpos : 0 < 1 - c := by linarith
  constructor
  · rw [hwu]
    show ‖(∑ j ∈ Finset.range (egN p α s t),
        (-1 : ℂ) ^ j • (((HvdH.Emat s t α) ^ j).mulVec u)) - w‖ ≤ 1 / (2 : ℝ) ^ p
    refine le_trans hbt1 ?_
    have hnonneg : 0 ≤ c ^ (egN p α s t) / (1 - c) :=
      div_nonneg (pow_nonneg hc0 _) hpos.le
    calc c ^ (egN p α s t) * ‖u‖ / (1 - c) = (c ^ (egN p α s t) / (1 - c)) * ‖u‖ := by ring
      _ ≤ (c ^ (egN p α s t) / (1 - c)) * (1 / 2) := mul_le_mul_of_nonneg_left hu hnonneg
      _ = (1 / 2) * (c ^ (egN p α s t) / (1 - c)) := by ring
      _ ≤ 1 / (2 : ℝ) ^ p := hnum1
  · show ‖(∑ j ∈ Finset.range (egN p α s t),
        (-1 : ℂ) ^ j • (((HvdH.Emat s t α) ^ j).mulVec u))‖ ≤ 1
    refine le_trans hbt2 ?_
    calc ‖u‖ * (1 - c)⁻¹ ≤ (1 / 2) * (1 - c)⁻¹ :=
          mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr hpos.le)
      _ ≤ 1 := hnum2

end Work.Resample
