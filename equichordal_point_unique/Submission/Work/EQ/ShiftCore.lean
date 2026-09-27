import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.CycleDefs

/-! # `ShiftCore`: the shift `σ` on chain data, self-contained

A local copy of the shift facts proved in `Submission/Work/EQ/H0_structure.lean`
(the region `hShiftInv` … `hShiftInv_mem_H0`), placed in the sub-namespace
`Work.EQ.ShiftCore` so that it can be imported without pulling in the rest of
`H0_structure` (whose later sections are not needed here and whose proofs are
still under construction).

`hShift` itself is defined in `DefsCore`.  The declarations below are
statement-for-statement the ones in `H0_structure`, with the same names, taken
inside the namespace `ShiftCore`.
-/

namespace Work.EQ

open Filter _root_.Topology

namespace ShiftCore

noncomputable def hShiftInv (a : ℝ) (p : ChainData) : ChainData :=
  (fun n => p.1 (n - 1), p.2.1 / (eqLam a : ℂ), (eqLam a : ℂ) * p.2.2)

lemma eqLam_pos_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma eqLam_ne_zero_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a ≠ 0 :=
  ne_of_gt (eqLam_pos_of ha0 ha1)

lemma eqLam_lt_one_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma continuous_hShift (a : ℝ) : Continuous (hShift a) := by
  unfold hShift
  refine Continuous.prodMk (continuous_pi fun n => ?_) (Continuous.prodMk ?_ ?_)
  · exact (continuous_apply (n + 1)).comp continuous_fst
  · exact continuous_const.mul (continuous_fst.comp continuous_snd)
  · exact (continuous_snd.comp continuous_snd).div_const _

lemma continuous_hShiftInv (a : ℝ) : Continuous (hShiftInv a) := by
  unfold hShiftInv
  refine Continuous.prodMk (continuous_pi fun n => ?_) (Continuous.prodMk ?_ ?_)
  · exact (continuous_apply (n - 1)).comp continuous_fst
  · exact (continuous_fst.comp continuous_snd).div_const _
  · exact continuous_const.mul (continuous_snd.comp continuous_snd)

lemma hShift_hShiftInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : hShift a ∘ hShiftInv a = id := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  funext q
  ext n <;> simp only [hShift, hShiftInv, Function.comp_apply, id_eq] <;> ring_nf
  · rw [mul_comm ((eqLam a : ℂ)) q.2.1]; exact mul_inv_cancel_right₀ hlam q.2.1
  · rw [mul_comm ((eqLam a : ℂ)) q.2.2]; exact mul_inv_cancel_right₀ hlam q.2.2

lemma hShiftInv_hShift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : hShiftInv a ∘ hShift a = id := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  funext q
  ext n <;> simp only [hShift, hShiftInv, Function.comp_apply, id_eq] <;> ring_nf
  · rw [mul_comm ((eqLam a : ℂ)) q.2.1]; exact mul_inv_cancel_right₀ hlam q.2.1
  · rw [mul_comm ((eqLam a : ℂ)) q.2.2]; exact mul_inv_cancel_right₀ hlam q.2.2

lemma hShift_inv_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    hShiftInv a (hShift a q) = q := congrFun (hShiftInv_hShift ha0 ha1) q

lemma hShift_inv_eq' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    hShift a (hShiftInv a q) = q := congrFun (hShift_hShiftInv ha0 ha1) q

lemma isChain_hShift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) : IsChain a h (hShift a p) := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  obtain ⟨hreg, hpsi1, hpsi2, hfwd, hbwd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact hreg (n + 1)
  · exact mul_ne_zero hlam hpsi1
  · exact div_ne_zero hpsi2 hlam
  · have h1 : ∀ᶠ n : ℕ in atTop,
        p.1 ((n : ℤ) + 1) = germC a h ((eqLam a : ℂ) ^ (n + 1) * p.2.1) :=
      (tendsto_add_atTop_nat 1).eventually hfwd
    filter_upwards [h1] with n hn
    simp only [hShift]
    rw [hn, pow_succ]
    ring_nf
  · have h2 : ∀ᶠ n : ℕ in atTop,
        p.1 (-(((n - 1 : ℕ)) : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n - 1) * p.2.2) :=
      (tendsto_sub_atTop_nat 1).eventually hbwd
    filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    simp only [hShift]
    have hcast : -((n : ℤ)) + 1 = -(((n - 1 : ℕ)) : ℤ) := by omega
    rw [hcast, hn]
    congr 1
    have hpow : (eqLam a : ℂ) ^ n = (eqLam a : ℂ) ^ (n - 1) * (eqLam a : ℂ) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    rw [hpow, mul_assoc, mul_div_cancel₀ p.2.2 hlam]

lemma isChain_hShiftInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) : IsChain a h (hShiftInv a p) := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  obtain ⟨hreg, hpsi1, hpsi2, hfwd, hbwd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [hShiftInv]
    rw [show (n : ℤ) + 1 - 1 = n by ring]
    simpa [sub_add_cancel] using hreg (n - 1)
  · exact div_ne_zero hpsi1 hlam
  · exact mul_ne_zero hlam hpsi2
  · have h1 : ∀ᶠ n : ℕ in atTop,
        p.1 (((n - 1 : ℕ)) : ℤ) = germC a h ((eqLam a : ℂ) ^ (n - 1) * p.2.1) :=
      (tendsto_sub_atTop_nat 1).eventually hfwd
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    simp only [hShiftInv]
    have hcast : ((n : ℤ)) - 1 = (((n - 1 : ℕ)) : ℤ) := by omega
    rw [hcast, hn]
    congr 1
    have hpow : (eqLam a : ℂ) ^ n = (eqLam a : ℂ) ^ (n - 1) * (eqLam a : ℂ) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    rw [hpow, mul_assoc, mul_div_cancel₀ p.2.1 hlam]
  · have h2 : ∀ᶠ n : ℕ in atTop,
        p.1 (-(((n + 1 : ℕ)) : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n + 1) * p.2.2) :=
      (tendsto_add_atTop_nat 1).eventually hbwd
    filter_upwards [h2] with n hn
    simp only [hShiftInv]
    rw [show -((n : ℤ)) - 1 = -(((n + 1 : ℕ)) : ℤ) by push_cast; ring, hn, pow_succ]
    congr 1
    ring

lemma hShift_mem_H0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : p ∈ H0 a h) : hShift a p ∈ H0 a h := by
  obtain ⟨e, he, f, hfcont, hf0, hf⟩ := hp
  have hlam : 0 < eqLam a := eqLam_pos_of ha0 ha1
  have hlam' : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  have key : ∀ u : ℂ, u ∈ Metric.ball (hShift a p).2.1 (eqLam a * e) →
      u / (eqLam a : ℂ) ∈ Metric.ball p.2.1 e := by
    intro u hu
    simp only [Metric.mem_ball, dist_eq_norm] at hu ⊢
    have hu' : ‖u - (eqLam a : ℂ) * p.2.1‖ < eqLam a * e := by simpa only [hShift] using hu
    have h1 : u / (eqLam a : ℂ) - p.2.1 =
        (u - (eqLam a : ℂ) * p.2.1) / (eqLam a : ℂ) := by
      rw [sub_div, mul_div_cancel_left₀ p.2.1 hlam']
    have h2 : ‖u / (eqLam a : ℂ) - p.2.1‖ = ‖u - (eqLam a : ℂ) * p.2.1‖ / eqLam a := by
      rw [h1, norm_div, Complex.norm_of_nonneg (le_of_lt hlam)]
    have h3 : ‖u - (eqLam a : ℂ) * p.2.1‖ / eqLam a < e := by
      rw [div_lt_iff₀ hlam]
      exact lt_of_lt_of_eq hu' (mul_comm (eqLam a) e)
    linarith [h2, h3]
  refine ⟨eqLam a * e, mul_pos hlam he, (fun u => hShift a (f (u / (eqLam a : ℂ)))), ?_, ?_, ?_⟩
  · exact (continuous_hShift a).comp_continuousOn (hfcont.comp (continuousOn_id.div_const _) key)
  · have hbase : (eqLam a : ℂ) * p.2.1 / (eqLam a : ℂ) = p.2.1 :=
      mul_div_cancel_left₀ p.2.1 hlam'
    simp only [hShift, hbase, hf0]
  · intro u hu
    obtain ⟨hc, hpsi⟩ := hf _ (key u hu)
    refine ⟨isChain_hShift ha0 ha1 hc, ?_⟩
    simp only [hShift]
    rw [hpsi]
    exact mul_div_cancel₀ u hlam'

lemma hShiftInv_mem_H0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : p ∈ H0 a h) : hShiftInv a p ∈ H0 a h := by
  obtain ⟨e, he, f, hfcont, hf0, hf⟩ := hp
  have hlam : 0 < eqLam a := eqLam_pos_of ha0 ha1
  have hlam' : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  have key : ∀ u : ℂ, u ∈ Metric.ball (p.2.1 / (eqLam a : ℂ)) (e / eqLam a) →
      (eqLam a : ℂ) * u ∈ Metric.ball p.2.1 e := by
    intro u hu
    simp only [Metric.mem_ball, dist_eq_norm] at hu ⊢
    have h1 : (eqLam a : ℂ) * u - p.2.1 =
        (eqLam a : ℂ) * (u - p.2.1 / (eqLam a : ℂ)) := by
      rw [mul_sub, mul_div_cancel₀ p.2.1 hlam']
    have h2 : ‖(eqLam a : ℂ) * u - p.2.1‖ = eqLam a * ‖u - p.2.1 / (eqLam a : ℂ)‖ := by
      rw [h1, norm_mul, Complex.norm_of_nonneg (le_of_lt hlam)]
    have h3 : eqLam a * ‖u - p.2.1 / (eqLam a : ℂ)‖ < eqLam a * (e / eqLam a) :=
      mul_lt_mul_of_pos_left hu hlam
    have h4 : eqLam a * (e / eqLam a) = e := mul_div_cancel₀ e (eqLam_ne_zero_of ha0 ha1)
    linarith [h2, h3, h4]
  refine ⟨e / eqLam a, div_pos he hlam, (fun u => hShiftInv a (f ((eqLam a : ℂ) * u))), ?_, ?_, ?_⟩
  · exact (continuous_hShiftInv a).comp_continuousOn
      (hfcont.comp (continuousOn_const.mul continuousOn_id) key)
  · have hbase : (eqLam a : ℂ) * (p.2.1 / (eqLam a : ℂ)) = p.2.1 :=
      mul_div_cancel₀ p.2.1 hlam'
    simp only [hShiftInv, hbase, hf0]
  · intro u hu
    obtain ⟨hc, hpsi⟩ := hf _ (key u hu)
    refine ⟨isChain_hShiftInv ha0 ha1 hc, ?_⟩
    simp only [hShiftInv]
    rw [hpsi]
    exact mul_div_cancel_left₀ u hlam'

end ShiftCore

end Work.EQ
