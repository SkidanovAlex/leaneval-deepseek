import Mathlib
import Submission.Work.SG.RepCoh_prep

namespace Work.SG

/-! ## Private helpers for `Work.SG.RepCoh_piv` -/

/-- The `wcComb` fold keeps the length at most `M` (it is `M` until an out-of-range
row index collapses it to `[]`). -/
private theorem wcComb_length_le (M : ℕ) (R : List (List ℤ)) (wc : List (List (ℕ × ℤ)))
    (c : ℕ) (hRrow : ∀ row ∈ R, row.length = M) :
    (RC.wcComb M R wc c).length ≤ M := by
  change (List.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 []))
    (RC.vzero M) (wc.getD c [])).length ≤ M
  suffices h : ∀ (s : List (ℕ × ℤ)) (acc : List ℤ), acc.length ≤ M →
      (s.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 [])) acc).length
        ≤ M by
    exact h _ _ (by simp [RC.vzero])
  intro s
  induction s with
  | nil => intro acc hacc; simpa using hacc
  | cons p t ih =>
    intro acc hacc
    rw [List.foldl_cons]
    apply ih
    rw [List.length_zipWith]
    have hrow : (R.getD p.1 []).length ≤ M := by
      rcases lt_or_ge p.1 R.length with hp | hp
      · rw [List.getD_eq_getElem _ _ hp]; exact le_of_eq (hRrow _ (List.getElem_mem hp))
      · rw [List.getD_eq_default _ _ hp]; simp
    exact le_trans (Nat.min_le_left _ _) hacc

/-- `Data.ldot (wcComb M R wc c) v` is divisible by `n` whenever every row of `R`
annihilates `v` modulo `n`. -/
private theorem wcComb_ldot_dvd {n : ℤ} {M : ℕ} {R : List (List ℤ)}
    {wc : List (List (ℕ × ℤ))} {c : ℕ} {v : List ℤ}
    (hRrow : ∀ row ∈ R, row.length = M)
    (hvS : ∀ row ∈ R, Data.ldot row v % n = 0) :
    n ∣ Data.ldot (RC.wcComb M R wc c) v := by
  by_cases hidx : ∀ p ∈ wc.getD c [], p.1 < R.length
  · rw [wcComb_ldot M R wc c v hRrow hidx]
    apply List.dvd_sum
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hp1 : p.1 < R.length := hidx p hp
    have hmem : R.getD p.1 [] ∈ R := by
      rw [List.getD_eq_getElem _ _ hp1]; exact List.getElem_mem hp1
    exact dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr (hvS _ hmem)) p.2
  · push_neg at hidx
    obtain ⟨p, hp, hp1⟩ := hidx
    rw [wcComb_eq_nil M R wc c ⟨p, hp, hp1⟩]
    simp [Data.ldot]

/-- Removing the `c`-th term from the `ldot`-sum of `w` against `v` changes it by a
multiple of `n`, provided `v` vanishes below `c` and `w` is `0` mod `n` above `c`. -/
private theorem sum_range_sub_self_dvd {n : ℤ} {w v : List ℤ} {c M : ℕ}
    (hwl : w.length ≤ M)
    (hv0 : ∀ q, q < c → v.getD q 0 = 0)
    (hwq : ∀ q, c < q → q < M → w.getD q 0 % n = 0) :
    n ∣ ((List.range w.length).map (fun q => w.getD q 0 * v.getD q 0)).sum
        - w.getD c 0 * v.getD c 0 := by
  by_cases hcw : c < w.length
  · set k : ℕ := w.length - (c + 1) with hkdef
    have hwlen : w.length = (c + 1) + k := by omega
    have hsplit : List.range w.length
        = List.range c ++ ([c] ++ (List.range k).map (fun i => (c + 1) + i)) := by
      rw [hwlen, List.range_add, List.range_succ, List.append_assoc]
    have hS : ((List.range w.length).map (fun q => w.getD q 0 * v.getD q 0)).sum
        = w.getD c 0 * v.getD c 0
          + (((List.range k).map (fun i => (c + 1) + i)).map
              (fun q => w.getD q 0 * v.getD q 0)).sum := by
      rw [hsplit, List.map_append, List.map_append, List.sum_append, List.sum_append]
      have h1 : (List.map (fun q => w.getD q 0 * v.getD q 0) (List.range c)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        rw [List.mem_range] at hq
        rw [hv0 q hq, mul_zero]
      have h2 : (List.map (fun q => w.getD q 0 * v.getD q 0) [c]).sum
          = w.getD c 0 * v.getD c 0 := by simp
      rw [h1, h2]; ring
    have hT : n ∣ (((List.range k).map (fun i => (c + 1) + i)).map
        (fun q => w.getD q 0 * v.getD q 0)).sum := by
      rw [List.map_map]
      apply List.dvd_sum
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [List.mem_range] at hi
      simp only [Function.comp_apply]
      have hq1 : c < (c + 1) + i := by omega
      have hq2 : (c + 1) + i < M := by
        have : (c + 1) + i < w.length := by omega
        omega
      exact dvd_mul_of_dvd_left
        (Int.dvd_iff_emod_eq_zero.mpr (hwq ((c + 1) + i) hq1 hq2)) (v.getD ((c + 1) + i) 0)
    have hfin : ((List.range w.length).map (fun q => w.getD q 0 * v.getD q 0)).sum
          - w.getD c 0 * v.getD c 0
        = (((List.range k).map (fun i => (c + 1) + i)).map
            (fun q => w.getD q 0 * v.getD q 0)).sum := by
      rw [hS]; ring
    rw [hfin]; exact hT
  · have hwle : w.length ≤ c := not_lt.mp hcw
    have hSc : ((List.range w.length).map (fun q => w.getD q 0 * v.getD q 0)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [List.mem_range] at hq
      have hqc : q < c := lt_of_lt_of_le hq hwle
      rw [hv0 q hqc, mul_zero]
    have hwc0 : w.getD c 0 = 0 := List.getD_eq_default w (0 : ℤ) hwle
    rw [hSc, hwc0]; simp

/-- Pure arithmetic core: if `n ∣ b·a` and `b ≡ m (mod n)` with `n = piv·m`, `piv > 0`,
then `piv ∣ a`. -/
private theorem piv_dvd_of_dvd_mul {n piv m b a : ℤ} (hn : 0 < n) (_hpiv : 0 < piv)
    (hm : n = piv * m) (h1 : n ∣ b * a) (h2 : n ∣ b - m) : piv ∣ a := by
  have hmne : m ≠ 0 := by
    intro h; rw [h, mul_zero] at hm; omega
  have hsub : n ∣ b * a - m * a := by
    have h := dvd_mul_of_dvd_left h2 a
    rwa [sub_mul] at h
  have h3 : n ∣ m * a := by
    have h := dvd_sub h1 hsub
    rwa [show b * a - (b * a - m * a) = m * a from by ring] at h
  have h4 : piv * m ∣ m * a := by rw [← hm]; exact h3
  have h5 : m * piv ∣ m * a := by
    have hcm : piv * m = m * piv := mul_comm _ _
    rwa [hcm] at h4
  exact (Int.mul_dvd_mul_iff_left hmne).mp h5

/-- Pivot extraction for the elimination argument: if `v` is annihilated modulo `n` by every row of `R`, and `v` vanishes below the column `c`, then the pivot entry `(H.getD c []).getD c 1` divides `v.getD c 0`.

The module `Submission.Work.SG.RepCoh_prep` provides the flat-vector toolkit used below: `ldot_eq_sum_getD`, `ldot_congr`, `ldot_vadd/vsub/vz`, `ldot_vadd_right/vsub_right/vz_right`, `vz_getD`, `vsub_getD`, `getD_eq_getD_of_lt`, plus `wcComb_ldot`, `wcComb_length`, `wcComb_eq_nil` describing `Work.SG.RC.wcComb M R wc c` as the integer combination `∑ p.2 • R[p.1]` over `p ∈ wc.getD c []` (when every index `p.1 < R.length`), and its collapse to `[]` when some index is out of range. -/
theorem RepCoh_piv {n : ℤ} (hn : 0 < n) {M : ℕ} {R H : List (List ℤ)}
    {wc : List (List (ℕ × ℤ))}
    (hH : H.length = M) (hHrow : ∀ c, c < M → (H.getD c []).length = M)
    (hech : ∀ c, c < M → Work.SG.RC.EchAt c (H.getD c []))
    (hdvd : ∀ c, c < M → n % (H.getD c []).getD c 1 = 0)
    (hann : ∀ c, c < M → ∀ row ∈ R, Data.ldot row (H.getD c []) % n = 0)
    (hRrow : ∀ row ∈ R, row.length = M)
    (hwclen : wc.length = M)
    (hwc : ∀ c, c < M → ∀ q, c < q → q < M → (Work.SG.RC.wcComb M R wc c).getD q 0 % n = 0)
    (hwcp : ∀ c, c < M → ((Work.SG.RC.wcComb M R wc c).getD c 0 - n / (H.getD c []).getD c 1) % n = 0)
    (c : ℕ) (hc : c < M) {v : List ℤ}
    (hv0 : ∀ q, q < c → v.getD q 0 = 0)
    (hvS : ∀ row ∈ R, Data.ldot row v % n = 0) :
    ∃ k : ℤ, v.getD c 0 = (H.getD c []).getD c 1 * k := by
  set piv : ℤ := (H.getD c []).getD c 1 with hpivdef
  set m : ℤ := n / piv with hmdef
  have hpiv_pos : 0 < piv := by
    rw [hpivdef]
    have h0 : 0 < (H.getD c []).getD c 0 := (hech c hc).2
    rwa [getD_eq_getD_of_lt (H.getD c []) (by rw [hHrow c hc]; exact hc) (0 : ℤ) (1 : ℤ)] at h0
  have hdvdpiv : piv ∣ n := by
    rw [hpivdef]
    exact Int.dvd_iff_emod_eq_zero.mpr (hdvd c hc)
  have hmul : n = piv * m := by
    rw [hmdef, mul_comm]
    exact (Int.ediv_mul_cancel hdvdpiv).symm
  set w : List ℤ := Work.SG.RC.wcComb M R wc c with hwdef
  have hwc' : ∀ q, c < q → q < M → w.getD q 0 % n = 0 := by
    intro q hcq hqM; rw [hwdef]; exact hwc c hc q hcq hqM
  have hwcp' : (w.getD c 0 - m) % n = 0 := by
    rw [hwdef, hmdef, hpivdef]; exact hwcp c hc
  have hwl_le : w.length ≤ M := by
    rw [hwdef]; exact wcComb_length_le M R wc c hRrow
  have hdvd_ldot : n ∣ Data.ldot w v := by
    rw [hwdef]; exact wcComb_ldot_dvd hRrow hvS
  have hdvd_rest : n ∣ Data.ldot w v - w.getD c 0 * v.getD c 0 := by
    rw [ldot_eq_sum_getD w v]
    exact sum_range_sub_self_dvd hwl_le hv0 hwc'
  have hdvd_prod : n ∣ w.getD c 0 * v.getD c 0 := by
    have hneg : n ∣ w.getD c 0 * v.getD c 0 - Data.ldot w v := by
      rw [show w.getD c 0 * v.getD c 0 - Data.ldot w v
            = -(Data.ldot w v - w.getD c 0 * v.getD c 0) from by ring]
      exact dvd_neg.mpr hdvd_rest
    have hsum := dvd_add hneg hdvd_ldot
    rwa [show w.getD c 0 * v.getD c 0 - Data.ldot w v + Data.ldot w v
            = w.getD c 0 * v.getD c 0 from by ring] at hsum
  have hcong : n ∣ w.getD c 0 - m := Int.dvd_iff_emod_eq_zero.mpr hwcp'
  have hpivdvd : piv ∣ v.getD c 0 :=
    piv_dvd_of_dvd_mul hn hpiv_pos hmul hdvd_prod hcong
  obtain ⟨k, hk⟩ := hpivdvd
  exact ⟨k, hk⟩

end Work.SG
