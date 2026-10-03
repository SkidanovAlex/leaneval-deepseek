import Mathlib
import Submission.Work.Horn.FatouQ.Xfun_basic

namespace Work.Horn.FatouQ

open Work.Horn.Flower

/-!
# The elementary part `∑_{i=1}^{q-1} (g_i/(i-q)) (1/z)^{q-i}` of the approximate Fatou coordinate

On the petal the chart identity `w = c / z^q` (equivalently `z^q = c / w`) gives
`‖1/z‖^q = ‖w‖ / ‖c‖`, so each power `(1/z)^{q-i}` is bounded by a constant times
`‖w‖ ^ ((q-i)/q)`.  Since `1 ≤ i ≤ q - 1` we have `(q - i)/q ≤ 1 - 1/q < 1`, and the elementary
estimate `r ^ s ≤ r ^ θ + 1` (`rpow_le_rpow_add_one`) turns this into the Hölder-type bound
`≤ C ‖w‖ ^ θ + C` with `θ = 1 - 1/q`.  The finite sum is then bounded by summing the constants.
-/

noncomputable section

theorem Xfun_sum_bound {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w) :
    ∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖∑ i ∈ Finset.Icc 1 (q - 1),
          Work.Horn.FatouQ.gcoef f q a i / ((i : ℂ) - (q : ℂ)) *
            (Work.Horn.FatouQ.zBranch q a j w)⁻¹ ^ (q - i)‖ ≤ C0 * ‖w‖ ^ θ + C1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr j.pos
  -- per-term estimate, with the local exponent `e = (q - i)/q`
  have key : ∀ i ∈ Finset.Icc 1 (q - 1), ∀ w : ℂ, M < w.re →
      ‖gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖ ≤
        (‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ *
          ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) * (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) := by
    intro i hi w hw
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiq : i ≤ q - 1 := (Finset.mem_Icc.mp hi).2
    have hiq' : i ≤ q := by omega
    have hch := hchart w hw
    have hc : cc q a ≠ 0 := cc_ne_zero_of_chart j hd.hM hw hch
    have htq : ‖(zBranch q a j w)⁻¹‖ ^ q = ‖w‖ / ‖cc q a‖ := norm_inv_zBranch_pow j hd.hM hw hch
    set e : ℝ := (((q - i : ℕ) : ℝ)) / (q : ℝ) with he
    have he0 : 0 ≤ e := by rw [he]; exact div_nonneg (Nat.cast_nonneg _) hqR.le
    have heθ : e ≤ 1 - 1 / (q : ℝ) := by
      rw [he]
      have hcast : ((q - i : ℕ) : ℝ) = (q : ℝ) - (i : ℝ) := Nat.cast_sub hiq'
      rw [hcast, div_le_iff₀ hqR]
      have h2 : (1 - 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) - 1 := by
        rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ (ne_of_gt hqR)]
      rw [h2]
      have hi1' : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      linarith
    have hθ1 : 1 - 1 / (q : ℝ) ≤ 1 := by
      have h : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith
    have hpow : ‖(zBranch q a j w)⁻¹‖ ^ (q - i) ≤
        (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) * ‖cc q a‖ ^ (-e) := by
      rw [rpow_nat_pow_eq (norm_nonneg _) j.pos hiq', htq, he]
      rw [Real.div_rpow (norm_nonneg w) (norm_nonneg (cc q a))]
      have hle : ‖w‖ ^ e ≤ ‖w‖ ^ (1 - 1 / (q : ℝ)) + 1 :=
        rpow_le_rpow_add_one he0 heθ hθ1 (norm_nonneg w)
      have hcpos : 0 < ‖cc q a‖ := norm_pos_iff.mpr hc
      have hne : 0 ≤ ‖cc q a‖ ^ (-e) := Real.rpow_nonneg hcpos.le _
      have hb : 0 ≤ ‖w‖ ^ (1 - 1 / (q : ℝ)) + 1 := by positivity
      rw [div_eq_mul_inv, ← Real.rpow_neg hcpos.le]
      exact mul_le_mul hle le_rfl hne hb
    have hnorm : ‖gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖
        = ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖(zBranch q a j w)⁻¹‖ ^ (q - i) := by
      rw [norm_mul, norm_pow]
    rw [hnorm]
    calc ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖(zBranch q a j w)⁻¹‖ ^ (q - i)
        ≤ ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ *
            ((‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) * ‖cc q a‖ ^ (-e)) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-e)) *
            (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) := by ring
  -- the sum of the constants
  refine ⟨∑ i ∈ Finset.Icc 1 (q - 1),
      ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ))),
    ∑ i ∈ Finset.Icc 1 (q - 1),
      ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ))),
    1 - 1 / (q : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  · have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast j.pos
    have h2 : 1 / (q : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hqR, one_mul]; exact h1
    linarith
  · have h : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
    linarith
  · intro w hw
    have h1 : ‖∑ i ∈ Finset.Icc 1 (q - 1),
        gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖ ≤
        ∑ i ∈ Finset.Icc 1 (q - 1),
          ‖gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖ :=
      norm_sum_le _ _
    have h2 := Finset.sum_le_sum (fun i hi => key i hi w hw)
    have h3 : (∑ i ∈ Finset.Icc 1 (q - 1),
        (‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) *
          (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1)) =
        (∑ i ∈ Finset.Icc 1 (q - 1),
          ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) *
          (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) := (Finset.sum_mul _ _ _).symm
    calc ‖∑ i ∈ Finset.Icc 1 (q - 1),
        gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖
        ≤ ∑ i ∈ Finset.Icc 1 (q - 1),
          ‖gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖ := h1
      _ ≤ ∑ i ∈ Finset.Icc 1 (q - 1),
          (‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) *
            (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) := h2
      _ = (∑ i ∈ Finset.Icc 1 (q - 1),
          ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) *
            (‖w‖ ^ (1 - 1 / (q : ℝ)) + 1) := h3
      _ = (∑ i ∈ Finset.Icc 1 (q - 1),
          ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) *
            ‖w‖ ^ (1 - 1 / (q : ℝ)) +
          (∑ i ∈ Finset.Icc 1 (q - 1),
            ‖gcoef f q a i / ((i : ℂ) - (q : ℂ))‖ * ‖cc q a‖ ^ (-(((q - i : ℕ) : ℝ) / (q : ℝ)))) := by ring

end

end Work.Horn.FatouQ
