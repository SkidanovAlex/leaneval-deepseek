import Mathlib
import Submission.Work.Horn.fatouQ_defs

namespace Work.Horn.FatouQ

open Work.Horn.Flower

/-- The defect `Efun` of the approximate Fatou coordinate in the chart `w = c/z^q` is `O(‖z‖^(q+1))`
on the petal, and on the petal `‖z‖^q = ‖c‖/‖w‖`, so it is `O(w.re ^ (-(1 + 1/q)))` as `w.re → ∞`. -/
theorem Efun_bound {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q) {C : ℝ}
    (hC : 0 ≤ C)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w)
    (hidd : ∀ w : ℂ, M < w.re →
      Work.Horn.FatouQ.zBranch q a j (Work.Horn.FatouQ.gfun f q a j w) =
        f (Work.Horn.FatouQ.zBranch q a j w))
    (hdef : ∀ z ∈ Work.Horn.Flower.petal q a M j,
      ‖Work.Horn.FatouQ.Acorr f q a (f z) - Work.Horn.FatouQ.Acorr f q a z - 1‖ ≤
        C * ‖z‖ ^ (q + 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, M < w.re →
      ‖Work.Horn.FatouQ.Efun f q a j w‖ ≤ B / w.re ^ (1 + 1 / (q : ℝ)) := by
  have hq : 1 ≤ q := hd.hS.hq
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hqR : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hMpos : 0 < M := hd.hM
  have hcc : cc q a ≠ 0 := hd.hgeo.cc_ne_zero
  have hA : 0 < ‖cc q a‖ := norm_pos_iff.mpr hcc
  have hrnonneg : 0 ≤ 1 + 1 / (q : ℝ) := by positivity
  have hrmul : (q : ℝ) * (1 + 1 / (q : ℝ)) = (q : ℝ) + 1 := by
    rw [mul_add, mul_one, mul_one_div, div_self hqR]
  refine ⟨C * ‖cc q a‖ ^ (1 + 1 / (q : ℝ)), by positivity, ?_⟩
  intro w hw
  have hwpos : 0 < w.re := lt_trans hMpos hw
  have hwne : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  set z : ℂ := zBranch q a j w with hz
  have hzpet : z ∈ petal q a M j := hpetal w hw
  have hz0 : z ≠ 0 := fun h => hd.hgeo.not_mem_petal_zero j (h ▸ hzpet)
  have hchartz : chartQ q a z = w := hchart w hw
  have hzqne : z ^ q ≠ 0 := pow_ne_zero q hz0
  have hcq : cc q a = w * z ^ q := (div_eq_iff hzqne).mp hchartz
  have hzq : z ^ q = cc q a / w := by
    rw [eq_div_iff hwne, hcq, mul_comm]
  -- on the petal the chart is a bijection `w = c/z^q`, hence `‖z‖^q = ‖c‖/‖w‖`
  have hnorm : ‖z‖ ^ q = ‖cc q a‖ / ‖w‖ := by
    have h := congrArg norm hzq
    rwa [norm_pow, norm_div] at h
  have hsplit : ‖z‖ ^ (q + 1 : ℕ) = (‖z‖ ^ (q : ℝ)) ^ (1 + 1 / (q : ℝ)) := by
    rw [← Real.rpow_natCast]
    push_cast
    rw [← hrmul, Real.rpow_mul (norm_nonneg z)]
  have hzle : ‖z‖ ^ (q : ℝ) ≤ ‖cc q a‖ / w.re := by
    rw [Real.rpow_natCast, hnorm]
    exact div_le_div_of_nonneg_left hA.le hwpos (Complex.re_le_norm w)
  have key : ‖z‖ ^ (q + 1) ≤
      ‖cc q a‖ ^ (1 + 1 / (q : ℝ)) / w.re ^ (1 + 1 / (q : ℝ)) := by
    rw [hsplit]
    calc (‖z‖ ^ (q : ℝ)) ^ (1 + 1 / (q : ℝ))
        ≤ (‖cc q a‖ / w.re) ^ (1 + 1 / (q : ℝ)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg z) _) hzle hrnonneg
      _ = ‖cc q a‖ ^ (1 + 1 / (q : ℝ)) / w.re ^ (1 + 1 / (q : ℝ)) :=
          Real.div_rpow hA.le hwpos.le _
  -- rewrite `Efun` as the defect of `Acorr` along the orbit
  have hEfun : Efun f q a j w = Acorr f q a (f z) - Acorr f q a z - 1 := by
    simp only [Efun, Xfun]
    rw [hidd w hw]
  calc ‖Efun f q a j w‖
      = ‖Acorr f q a (f z) - Acorr f q a z - 1‖ := by rw [hEfun]
    _ ≤ C * ‖z‖ ^ (q + 1) := hdef z hzpet
    _ ≤ C * (‖cc q a‖ ^ (1 + 1 / (q : ℝ)) / w.re ^ (1 + 1 / (q : ℝ))) :=
        mul_le_mul_of_nonneg_left key hC
    _ = C * ‖cc q a‖ ^ (1 + 1 / (q : ℝ)) / w.re ^ (1 + 1 / (q : ℝ)) := by
        rw [mul_div_assoc]

end Work.Horn.FatouQ
