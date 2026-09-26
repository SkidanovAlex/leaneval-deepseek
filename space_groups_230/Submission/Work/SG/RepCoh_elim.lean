import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RepCoh_prep
import Submission.Work.SG.RepCoh_piv

namespace Work.SG

open Work.SG.RC

/-- Core of the elimination argument, for `y` already of length `M`:
a vector annihilated modulo `n` by every row of `R` lies in the `ℤ`-span modulo `n` of the
upper-echelon rows `H`, using the `wc` column-combination certificates. -/
theorem RepCoh_elim_core {n : ℤ} (hn : 0 < n) {M : ℕ} {R H : List (List ℤ)}
    {wc : List (List (ℕ × ℤ))}
    (hH : H.length = M) (hHrow : ∀ c, c < M → (H.getD c []).length = M)
    (hech : ∀ c, c < M → Work.SG.RC.EchAt c (H.getD c []))
    (hdvd : ∀ c, c < M → n % (H.getD c []).getD c 1 = 0)
    (hann : ∀ c, c < M → ∀ row ∈ R, Data.ldot row (H.getD c []) % n = 0)
    (hRrow : ∀ row ∈ R, row.length = M)
    (hwclen : wc.length = M)
    (hwc : ∀ c, c < M → ∀ q, c < q → q < M → (Work.SG.RC.wcComb M R wc c).getD q 0 % n = 0)
    (hwcp : ∀ c, c < M → ((Work.SG.RC.wcComb M R wc c).getD c 0 - n / (H.getD c []).getD c 1) % n = 0)
    {y : List ℤ} (hylen : y.length = M) (hy : ∀ row ∈ R, Data.ldot row y % n = 0) :
    ∃ t : List ℤ, ∀ q, q < M → (y.getD q 0 - Work.SG.RC.linC H t q) % n = 0 := by
  have key : ∀ c ≤ M, ∃ ts r : List ℤ, ts.length = c ∧ r.length = M ∧
      (∀ q, q < c → r.getD q 0 = 0) ∧ (∀ row ∈ R, Data.ldot row r % n = 0) ∧
      (∀ q, q < M → r.getD q 0 = y.getD q 0 -
        ((List.range c).map (fun c' => ts.getD c' 0 * (H.getD c' []).getD q 0)).sum) := by
    intro c
    induction c with
    | zero =>
      intro _
      exact ⟨[], y, rfl, hylen, (by intro q hq; omega), hy, (by intro q hq; simp)⟩
    | succ c ih =>
      intro hc
      have hcm : c < M := by omega
      obtain ⟨ts, r, hts, hr, hrz, hrS, hreq⟩ := ih (by omega)
      have hdpos : 0 < (H.getD c []).getD c 1 := by
        have h0 : 0 < (H.getD c []).getD c 0 := (hech c hcm).2
        rwa [getD_eq_getD_of_lt (H.getD c []) (by rw [hHrow c hcm]; exact hcm) (0 : ℤ) (1 : ℤ)] at h0
      have hdne : (H.getD c []).getD c 1 ≠ 0 := ne_of_gt hdpos
      obtain ⟨k', hk'⟩ := RepCoh_piv hn hH hHrow hech hdvd hann hRrow hwclen hwc hwcp c hcm
        (v := r) hrz hrS
      set k : ℤ := r.getD c 0 / (H.getD c []).getD c 1 with hkdef
      have hk : r.getD c 0 = (H.getD c []).getD c 1 * k := by
        rw [hkdef, hk']
        rw [mul_comm ((H.getD c []).getD c 1) k', Int.mul_ediv_cancel k' hdne]
        ring
      refine ⟨ts ++ [k], vsub r (vz k (H.getD c [])), ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hts]; simp
      · rw [vsub_length, vz_length, hr, hHrow c hcm, min_self]
      · intro q hq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
        · rw [vsub_getD _ _ (by rw [hr]; omega) (by rw [vz_length, hHrow c hcm]; omega),
            vz_getD, hrz q hq, (hech c hcm).1 q hq]
          ring
        · rw [hq]
          rw [vsub_getD _ _ (by rw [hr]; omega) (by rw [vz_length, hHrow c hcm]; omega),
            vz_getD, getD_eq_getD_of_lt (H.getD c []) (by rw [hHrow c hcm]; exact hcm) (0 : ℤ) (1 : ℤ),
            hk]
          ring
      · intro row hrR
        have hSr : n ∣ Data.ldot row r := Int.dvd_iff_emod_eq_zero.mpr (hrS row hrR)
        have hSH : n ∣ Data.ldot row (H.getD c []) :=
          Int.dvd_iff_emod_eq_zero.mpr (hann c hcm row hrR)
        have hlin : Data.ldot row (vsub r (vz k (H.getD c [])))
            = Data.ldot row r - k * Data.ldot row (H.getD c []) := by
          rw [ldot_vsub_right _ _ _ (by rw [vz_length, hr, hHrow c hcm]), ldot_vz_right]
        rw [hlin]
        exact Int.dvd_iff_emod_eq_zero.mp (dvd_sub hSr (dvd_mul_of_dvd_right hSH k))
      · intro q hq
        rw [vsub_getD _ _ (by rw [hr]; exact hq) (by rw [vz_length, hHrow c hcm]; exact hq),
          vz_getD]
        rw [sum_range_succ_map]
        have hsum : ((List.range c).map
              (fun c' => (ts ++ [k]).getD c' 0 * (H.getD c' []).getD q 0)).sum
            = ((List.range c).map
              (fun c' => ts.getD c' 0 * (H.getD c' []).getD q 0)).sum := by
          apply sum_range_congr
          intro c' hc'
          rw [append_singleton_getD ts k (by rw [hts]; exact hc')]
        have hkc : (ts ++ [k]).getD c 0 = k := by
          rw [← hts]
          exact append_singleton_getD_self ts k
        rw [hsum, hkc, hreq q hq]
        ring
  obtain ⟨ts, r, hts, hr, hrz, hrS, hreq⟩ := key M le_rfl
  refine ⟨ts, fun q hq => ?_⟩
  have h0 : r.getD q 0 = 0 := hrz q hq
  have hlin : Work.SG.RC.linC H ts q
      = ((List.range M).map (fun c' => ts.getD c' 0 * (H.getD c' []).getD q 0)).sum := by
    unfold Work.SG.RC.linC
    rw [hH]
  rw [hlin, ← hreq q hq, h0]
  simp

theorem RepCoh_elim {n : ℤ} (hn : 0 < n) {M : ℕ} {R H : List (List ℤ)}
    {wc : List (List (ℕ × ℤ))}
    (hH : H.length = M) (hHrow : ∀ c, c < M → (H.getD c []).length = M)
    (hech : ∀ c, c < M → Work.SG.RC.EchAt c (H.getD c []))
    (hdvd : ∀ c, c < M → n % (H.getD c []).getD c 1 = 0)
    (hann : ∀ c, c < M → ∀ row ∈ R, Data.ldot row (H.getD c []) % n = 0)
    (hRrow : ∀ row ∈ R, row.length = M)
    (hwclen : wc.length = M)
    (hwc : ∀ c, c < M → ∀ q, c < q → q < M → (Work.SG.RC.wcComb M R wc c).getD q 0 % n = 0)
    (hwcp : ∀ c, c < M → ((Work.SG.RC.wcComb M R wc c).getD c 0 - n / (H.getD c []).getD c 1) % n = 0)
    {y : List ℤ} (hy : ∀ row ∈ R, Data.ldot row y % n = 0) :
    ∃ t : List ℤ, ∀ q, q < M → (y.getD q 0 - Work.SG.RC.linC H t q) % n = 0 := by
  set yp : List ℤ := (List.range M).map (fun q => y.getD q 0) with hyp
  have hlen : yp.length = M := by rw [hyp, List.length_map, List.length_range]
  have hget : ∀ q, q < M → yp.getD q 0 = y.getD q 0 := by
    intro q hq
    rw [hyp]
    exact map_range_getD _ hq
  have hpann : ∀ row ∈ R, Data.ldot row yp % n = 0 := by
    intro row hr
    have hcong : Data.ldot row yp = Data.ldot row y := by
      apply ldot_congr
      intro q hq
      exact hget q (by rw [hRrow row hr] at hq; exact hq)
    rw [hcong]
    exact hy row hr
  obtain ⟨t, ht⟩ :=
    RepCoh_elim_core hn hH hHrow hech hdvd hann hRrow hwclen hwc hwcp hlen hpann
  exact ⟨t, fun q hq => by rw [← hget q hq]; exact ht q hq⟩

end Work.SG
