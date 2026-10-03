import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.pert2v2.steps
import Submission.Work.Pert.pert2v2.fatou_proper_im
import Submission.Work.Pert.RBlock6.walk_dev_le
import Submission.Work.Pert.pert2v2.GatePreimageReBound.walk_trace
import Submission.Work.Pert.pert2v2.GatePreimageReBound.walk_sum_bound

namespace Work.Pert.pert2v2.GatePreimageReBound

-- Forward walk in the lower gate: from a point `z` of `Qm Ξ α` with `z.re ≤ -1` and `z.im` large,
-- walk the `F`-orbit forward while the real part increases by ≈ 1 per step, until the real part
-- lands in `[0,1]`.  `F` is a near-translation by 1 on the gate (defect ≤ 1/32, exponentially small
-- above height `Ydec`), so the accumulated displacement error of the walk is summable; the walk
-- preserves `Φ` up to the exact level shift `+ N`.
theorem walk_fwd_re {Ξ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {M κ Ydec : ℝ}
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (habel : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φ (F w) = Φ w + 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, Ydec < w.im →
      ‖F w - (w + 1)‖ ≤ M * Real.exp (-(κ * w.im)))
    (hM : 0 < M) (hκ : 0 < κ) :
    ∃ K : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → z.re ≤ -1 → K ≤ z.im →
      ∃ z' : ℂ, z' ∈ Work.Pert.Qm Ξ α ∧ ∃ N : ℕ, Φ z' = Φ z + (N : ℂ) ∧
        z'.re ∈ Set.Icc (-2 : ℝ) 2 ∧ z.im - 1 ≤ z'.im ∧
        ‖(Φ z' - z') - (Φ z - z)‖ ≤ 1 := by
  -- the geometric datum of the gate: `-Re z < Im z + C` for `z` in the gate at positive height
  set C : ℝ := -Ξ + (1 / α).re + |(1 / α).im| with hCdef
  set C' : ℝ := C + 2 with hC'def
  obtain ⟨T, hT⟩ := walk_sum_bound M κ C' Ydec hM hκ
  set K : ℝ := max T
    (max ((31 / 30) * (max (Ξ + 17 / 16) (11 / 8) + C / 31) + 1) (|C| + 1)) with hKdef
  refine ⟨K, ?_⟩
  intro z hzQ hzre hzim
  have hTK : T ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK0 : max ((31 / 30) * (max (Ξ + 17 / 16) (11 / 8) + C / 31) + 1) (|C| + 1) ≤ K := by
    rw [hKdef]; exact le_max_right _ _
  have hlim : (31 / 30) * (max (Ξ + 17 / 16) (11 / 8) + C / 31) + 1 ≤ K :=
    le_trans (le_max_left _ _) hK0
  have hCab : |C| + 1 ≤ K := le_trans (le_max_right _ _) hK0
  have hTm : T ≤ z.im := le_trans hTK hzim
  have hlimm : (31 / 30) * (max (Ξ + 17 / 16) (11 / 8) + C / 31) + 1 ≤ z.im :=
    le_trans hlim hzim
  have hCabsm : |C| + 1 ≤ z.im := le_trans hCab hzim
  have hzim0 : 0 ≤ z.im := by linarith [abs_nonneg C]
  -- `hA`: the hypothesis of the trace lemma
  have hA : max (Ξ + 17 / 16) (11 / 8) ≤ (30 / 31 : ℝ) * z.im - C / 31 := by
    have h2 := mul_le_mul_of_nonneg_left hlimm (show (0 : ℝ) ≤ 30 / 31 by norm_num)
    have h3 : max (Ξ + 17 / 16) (11 / 8) + C / 31 + 30 / 31 ≤ (30 / 31 : ℝ) * z.im := by
      nlinarith [h2]
    linarith
  -- `hC`: `-Re z < Im z + C`, from the gate membership
  have hCpt : -z.re < z.im + C := by
    have hmem := (Work.Pert.mem_Qm_iff_g (Ξ := Ξ) (α := α) z).mp hzQ
    have hA' : 0 < z.re - Ξ + (1 / α).re + |z.im + (1 / α).im| := by
      simpa only [Work.Pert.margA_g] using hmem.1
    have h1 : |z.im + (1 / α).im| ≤ z.im + |(1 / α).im| := by
      calc |z.im + (1 / α).im| ≤ |z.im| + |(1 / α).im| := abs_add_le _ _
        _ = z.im + |(1 / α).im| := by rw [abs_of_nonneg hzim0]
    rw [hCdef]
    linarith
  -- ### the stopping index
  set x : ℝ := (32 / 31) * (z.im + C) with hxdef
  set J : ℕ := Nat.floor x + 1 with hJdef
  have hxC : 0 < z.im + C := by linarith [neg_abs_le C]
  have hx0 : 0 ≤ x := by
    rw [hxdef]; exact mul_nonneg (by norm_num) (le_of_lt hxC)
  have hJx : x < (J : ℝ) := by
    have h := Nat.lt_floor_add_one x
    rw [hJdef]; push_cast; linarith
  have hJle : (J : ℝ) ≤ x + 1 := by
    have h := Nat.floor_le hx0
    rw [hJdef]; push_cast; linarith
  have hJstep : z.im + C < (31 / 32 : ℝ) * (J : ℝ) := by
    have h3 : (31 / 32 : ℝ) * x < (31 / 32 : ℝ) * (J : ℝ) :=
      mul_lt_mul_of_pos_left hJx (by norm_num)
    rw [hxdef] at h3
    nlinarith [h3]
  -- there is an index at which the real part becomes nonnegative
  have hex : ∃ j : ℕ, 0 ≤ (F^[j] z).re := by
    by_contra hcon
    have hneg : ∀ j : ℕ, (F^[j] z).re < 0 := fun j => not_le.mp (fun h => hcon ⟨j, h⟩)
    have htr := walk_trace hNT hzQ hCpt hA J (fun i _ => hneg i)
    have h1 : z.re + (31 / 32 : ℝ) * (J : ℝ) ≤ (F^[J] z).re := htr.2.1
    have h4 : 0 < z.re + (z.im + C) := by linarith
    linarith [hneg J]
  set n : ℕ := Nat.find hex with hn
  have hn_spec : 0 ≤ (F^[n] z).re := by rw [hn]; exact Nat.find_spec hex
  have hn_min : ∀ i : ℕ, i < n → (F^[i] z).re < 0 := by
    intro i hi
    exact not_le.mp (Nat.find_min hex (hn ▸ hi))
  -- the first such index is at most `J`
  have hn_le_J : n ≤ J := by
    by_cases hcase : ∃ i : ℕ, i < J ∧ 0 ≤ (F^[i] z).re
    · obtain ⟨i, hiJ, hi⟩ := hcase
      have h1 : Nat.find hex ≤ i := Nat.find_le hi
      exact le_trans (hn.symm ▸ h1) (le_of_lt hiJ)
    · have hneg : ∀ i : ℕ, i < J → (F^[i] z).re < 0 :=
        fun i hiJ => not_le.mp (fun h => hcase ⟨i, hiJ, h⟩)
      have htr := walk_trace hNT hzQ hCpt hA J hneg
      have h1 : z.re + (31 / 32 : ℝ) * (J : ℝ) ≤ (F^[J] z).re := htr.2.1
      have h4 : 0 < z.re + (z.im + C) := by linarith
      have hpos : 0 < (F^[J] z).re := by linarith
      exact hn.symm ▸ Nat.find_le (le_of_lt hpos)
  have hn_bound : (n : ℝ) ≤ (32 / 31) * (z.im + C') := by
    have h1 : (n : ℝ) ≤ (J : ℝ) := by exact_mod_cast hn_le_J
    have h3 : x + 1 ≤ (32 / 31) * (z.im + C') := by
      rw [hxdef, hC'def]
      nlinarith
    linarith
  -- ### the summable defect bound
  obtain ⟨hYdec, hsum⟩ := hT z.im hTm n hn_bound
  have htrace : ∀ j : ℕ, j ≤ n → (F^[j] z) ∈ Work.Pert.Qm Ξ α :=
    (walk_trace hNT hzQ hCpt hA n hn_min).1
  have htrace_im : ∀ j : ℕ, j < n → z.im - (j : ℝ) / 32 ≤ (F^[j] z).im := fun j hj =>
    (walk_trace hNT hzQ hCpt hA j (fun i hi => hn_min i (lt_trans hi hj))).2.2
  have hdef_le : ∀ j : ℕ, j < n →
      ‖F (F^[j] z) - (F^[j] z + 1)‖ ≤ M * Real.exp (-(κ * ((F^[j] z).im))) := by
    intro j hj
    refine hdec _ (htrace j (le_of_lt hj)) ?_
    linarith [hYdec j hj, htrace_im j hj]
  have hdev := Work.Pert.RBlock6.walk_dev_le (F := F)
    (G := fun w : ℂ => M * Real.exp (-(κ * w.im))) (ς := z) (N := n) hdef_le
  have hsum_le : (∑ j ∈ Finset.range n, M * Real.exp (-(κ * ((F^[j] z).im)))) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum ?_) hsum
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    have hexp : Real.exp (-(κ * ((F^[j] z).im)))
        ≤ Real.exp (-(κ * (z.im - (j : ℝ) / 32))) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : κ * (z.im - (j : ℝ) / 32) ≤ κ * ((F^[j] z).im) :=
        mul_le_mul_of_nonneg_left (htrace_im j hj') (le_of_lt hκ)
      linarith
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt hM)
  have hnorm : ‖F^[n] z - (z + (n : ℂ))‖ ≤ 1 := le_trans hdev hsum_le
  -- ### conclusion
  have hab : Φ (F^[n] z) = Φ z + (n : ℂ) := Work.Pert.abel_iter htrace habel
  have hre_up : (F^[n] z).re ≤ 2 := by
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exfalso
        rw [h0] at hn_spec
        simp at hn_spec
        linarith
      · exact hpos
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    have hklt : k < n := by omega
    have hk_mem : (F^[k] z) ∈ Work.Pert.Qm Ξ α := htrace k (by omega)
    have hstepk : ‖F (F^[k] z) - (F^[k] z + 1)‖ ≤ (1 / 32 : ℝ) := (hNT.2 _ hk_mem).1
    have hrek : (F^[k] z).re < 0 := hn_min k hklt
    have heq : (F^[n] z).re = (F (F^[k] z)).re := by
      rw [hk, Function.iterate_succ_apply']
    rw [heq]
    have h := Complex.abs_re_le_norm (F (F^[k] z) - (F^[k] z + 1))
    have hre : (F (F^[k] z) - (F^[k] z + 1)).re
        = (F (F^[k] z)).re - (F^[k] z).re - 1 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
    rw [hre] at h
    linarith [(abs_le.mp h).2, hstepk]
  have him_low : z.im - 1 ≤ (F^[n] z).im := by
    have h := Complex.abs_im_le_norm (F^[n] z - (z + (n : ℂ)))
    have him : (F^[n] z - (z + (n : ℂ))).im = (F^[n] z).im - z.im := by simp
    rw [him] at h
    have h2 : |(F^[n] z).im - z.im| ≤ 1 := le_trans h hnorm
    linarith [(abs_le.mp h2).1]
  have hphi : ‖(Φ (F^[n] z) - F^[n] z) - (Φ z - z)‖ ≤ 1 := by
    rw [hab]
    have he : (Φ z + (n : ℂ) - F^[n] z) - (Φ z - z) = -(F^[n] z - (z + (n : ℂ))) := by ring
    rw [he, norm_neg]
    exact hnorm
  exact ⟨F^[n] z, htrace n le_rfl, n, hab, ⟨by linarith, hre_up⟩, him_low, hphi⟩

end Work.Pert.pert2v2.GatePreimageReBound
