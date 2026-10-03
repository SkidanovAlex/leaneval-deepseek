import Mathlib
import Submission.Work.Peluse.UControl.bandCore
import Submission.Work.Peluse.Prop36SW.uNormPowCollapsePlain
import Submission.Work.Peluse.Prop36SW.uNormPowFibre
import Submission.Work.Peluse.Prop36SW.uNormPowCollapsePlainUpper

/-!
# The ambient / window / level transfer for the uniformity-norm power

`Work.Peluse.Prop36SW.uNormPowTransferTwo`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse

/-! ## Elementary facts -/

lemma uNormPow_nonneg (t : ℕ) (Q S : Finset ℤ) (f : ℤ → ℂ) : 0 ≤ uNormPow t Q S f := by
  rw [uNormPow, boxNormPow]
  exact norm_nonneg _

/-- The uniformity-norm power of the zero function vanishes. -/
lemma uNormPow_zeroFun (t : ℕ) (Q S : Finset ℤ) :
    uNormPow t Q S (0 : ℤ → ℂ) = 0 := by
  rw [uNormPow, boxNormPow, boxSumPow, prodCubeSum]
  simp

/-- The power-mean inequality for a finite sum of nonnegative reals, with the cardinality of the
support of the family as the effective number of terms. -/
private lemma sum_pow_le_card_pow_mul_sum_pow {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ s, a i) ^ k
      ≤ ((s.filter (fun i => a i ≠ 0)).card : ℝ) ^ (k - 1) * ∑ i ∈ s, (a i) ^ k := by
  classical
  set s' : Finset ι := s.filter (fun i => a i ≠ 0) with hs'
  have hsub : s' ⊆ s := Finset.filter_subset _ _
  have h0 : ∀ i ∈ s, i ∉ s' → a i = 0 := by
    intro i hi hni
    by_contra hne
    exact hni (by rw [hs']; exact Finset.mem_filter.mpr ⟨hi, hne⟩)
  have hsum : (∑ i ∈ s, a i) = ∑ i ∈ s', a i :=
    (Finset.sum_subset hsub (fun i hi hni => h0 i hi hni)).symm
  have hkne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hsumk : (∑ i ∈ s, (a i) ^ k) = ∑ i ∈ s', (a i) ^ k :=
    (Finset.sum_subset hsub (fun i hi hni => by
      rw [h0 i hi hni, zero_pow hkne])).symm
  rw [hsum, hsumk]
  by_cases hne : s'.Nonempty
  · have habs : ∀ i ∈ s', |a i| = a i := fun i hi => abs_of_nonneg (ha i (hsub hi))
    have hkpos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h := Real.rpow_sum_le_const_mul_sum_rpow s' a hkpos
    have h1 : (∑ i ∈ s', |a i|) = ∑ i ∈ s', a i := Finset.sum_congr rfl habs
    have h2 : (∑ i ∈ s', |a i| ^ (k : ℝ)) = ∑ i ∈ s', (a i) ^ k :=
      Finset.sum_congr rfl (fun i hi => by rw [habs i hi, Real.rpow_natCast])
    have h3 : ((s'.card : ℝ)) ^ ((k : ℝ) - 1) = ((s'.card : ℝ)) ^ (k - 1) := by
      rw [show (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hk]; ring,
        Real.rpow_natCast]
    rw [h1, h2, h3, Real.rpow_natCast] at h
    exact h
  · have hempty : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp [zero_pow hkne]

/-- `s ≤ t' * 2 ^ (s - t')` for `2 ≤ t' ≤ s`. -/
lemma le_mul_two_pow_sub (t' s : ℕ) (ht' : 2 ≤ t') (hts : t' ≤ s) :
    s ≤ t' * 2 ^ (s - t') := by
  obtain ⟨m, rfl⟩ : ∃ m, s = t' + m := ⟨s - t', by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hle : m ≤ 2 * (2 ^ m - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h2 : m + 1 ≤ 2 ^ (m + 1) - 1 := by
        rw [Nat.pow_succ]; omega
      have h3 : 2 ^ (m + 1) - 1 ≤ 2 * (2 ^ (m + 1) - 1) := by omega
      exact le_trans h2 h3
  have h2 : 2 * (2 ^ m - 1) ≤ t' * (2 ^ m - 1) := Nat.mul_le_mul_right _ ht'
  have h3 : t' * (2 ^ m - 1) = t' * 2 ^ m - t' := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have h4 : m ≤ t' * 2 ^ m - t' := by
    rw [← h3]; exact le_trans hle h2
  have h5 : t' + (t' * 2 ^ m - t') = t' * 2 ^ m :=
    Nat.add_sub_cancel' (by
      calc t' = t' * 1 := (Nat.mul_one t').symm
        _ ≤ t' * 2 ^ m := Nat.mul_le_mul_left _ Nat.one_le_two_pow)
  calc t' + m ≤ t' + (t' * 2 ^ m - t') := by omega
    _ = t' * 2 ^ m := h5


/-! ## The plain level raise -/

/-- **The plain (un-dilated) level raise.**  For `2 ≤ t' ≤ s` there is `c > 0` such that for every
direction length `L ≥ 1`, every ambient `M ≥ 1` and every `1`-bounded `f` supported in `symIcc M`,

`c * (‖f‖^{2^{t'}}_{U^{t'}_{[L]}([-M,M])})^{2^{s-t'}} ≤ ‖f‖^{2^s}_{U^s_{[L]}([-M,M])}`,

with **no** hypothesis relating `L` to `M`. -/
theorem plainLevelRaise (t' s : ℕ) (ht' : 2 ≤ t') (hts : t' ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ L → 1 ≤ M → SupportIn f M →
      (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ (2 ^ (s - t'))
        ≤ uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f := by
  obtain ⟨c₀, hc₀, hlev⟩ := Work.Peluse.UControl.uNormPow_level_raise t' s (by omega) hts
  obtain ⟨C₂, hC₂, hcol₂⟩ := uNormPowCollapsePlain (le_trans ht' hts)
  obtain ⟨C_U, hC_U, hcolU⟩ := uNormPowCollapsePlainUpper ht'
  set k : ℕ := 2 ^ (s - t') with hk
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  have hk3 : (0:ℝ) < (1/3 : ℝ) ^ (k - 1) := by positivity
  have caseSmall : ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ L → L ≤ 2 * M + 1 → SupportIn f M →
      (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c₀ * (1 / 3) ^ (k - 1) * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k
        ≤ uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f := by
    intro L M f hL hLM hsup hb
    have hdir : ∀ a ∈ arithIcc (1 : ℤ) L, |a| ≤ ((2 * M + 1 : ℕ) : ℤ) := by
      intro a ha
      rw [arithIcc] at ha
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
      have hnL : n ≤ L := (Finset.mem_Icc.mp hn).2
      rw [one_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (n:ℤ))]
      exact_mod_cast le_trans hnL hLM
    have h1 : c₀ * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc (2 * M + 1)) f) ^ k
        ≤ uNormPow s (arithIcc (1 : ℤ) L) (symIcc (2 * M + 1)) f := by
      simpa [hk] using hlev (arithIcc (1 : ℤ) L) (2 * M + 1) f
        (Work.Peluse.UControl.arithIcc_nonempty (by norm_num) hL) (by omega) hdir (hsup.mono (by omega)) hb
    set ρ : ℝ := ((symIcc M).card : ℝ) / ((symIcc (2 * M + 1)).card : ℝ) with hρdef
    have hcardM : ((symIcc M).card : ℝ) = ((2 * M + 1 : ℕ) : ℝ) := by
      rw [Work.Peluse.UControl.card_symIcc]
    have hcard2M : ((symIcc (2 * M + 1)).card : ℝ) = ((2 * (2 * M + 1) + 1 : ℕ) : ℝ) := by
      rw [Work.Peluse.UControl.card_symIcc]
    have h2Mpos : (0:ℝ) < ((2 * (2 * M + 1) + 1 : ℕ) : ℝ) := by positivity
    have hρpos : 0 < ρ := by
      rw [hρdef, hcardM, hcard2M]
      exact div_pos (by positivity) h2Mpos
    have hρge : (1 / 3 : ℝ) ≤ ρ := by
      rw [hρdef, hcardM, hcard2M, le_div_iff₀ h2Mpos]
      push_cast
      nlinarith [Nat.zero_le M]
    have hc1 : ((symIcc M).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (Work.Peluse.UControl.symIcc_nonempty M))
    have hc2 : ((symIcc (2 * M + 1)).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (Work.Peluse.UControl.symIcc_nonempty (2 * M + 1)))
    have hwr_t : uNormPow t' (arithIcc (1 : ℤ) L) (symIcc (2 * M + 1)) f
        = ρ * uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f := by
      have h := Work.Peluse.UControl.uNormPow_window_ratio t' (arithIcc (1 : ℤ) L) (symIcc M) (symIcc (2 * M + 1)) f
        (Work.Peluse.UControl.symIcc_nonempty _)
      rw [h, hρdef]
      field_simp
    have hwr_s : uNormPow s (arithIcc (1 : ℤ) L) (symIcc (2 * M + 1)) f
        = ρ * uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f := by
      have h := Work.Peluse.UControl.uNormPow_window_ratio s (arithIcc (1 : ℤ) L) (symIcc M) (symIcc (2 * M + 1)) f
        (Work.Peluse.UControl.symIcc_nonempty _)
      rw [h, hρdef]
      field_simp
    have h2 : c₀ * (ρ * uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k
        ≤ ρ * uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f := by
      rw [← hwr_t, ← hwr_s]; exact h1
    have h3 : c₀ * ρ ^ (k - 1) * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k
        ≤ uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f := by
      refine le_of_mul_le_mul_left ?_ hρpos
      have he : ρ * (c₀ * ρ ^ (k - 1)
          * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k)
          = c₀ * (ρ * uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k := by
        rw [mul_pow,
          show ρ ^ k = ρ * ρ ^ (k - 1) by rw [← pow_succ', Nat.sub_add_cancel hk1]]
        ring
      rw [he]; exact h2
    have h4 : (1 / 3 : ℝ) ^ (k - 1) ≤ ρ ^ (k - 1) := pow_le_pow_left₀ (by norm_num) hρge _
    have h5 : 0 ≤ (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k :=
      pow_nonneg (uNormPow_nonneg _ _ _ _) _
    calc c₀ * (1 / 3) ^ (k - 1) * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k
        = c₀ * ((1 / 3) ^ (k - 1) * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k) := by ring
      _ ≤ c₀ * (ρ ^ (k - 1) * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 h5) hc₀.le
      _ = c₀ * ρ ^ (k - 1) * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k := by ring
      _ ≤ _ := h3
  have caseBig : ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ L → 1 ≤ M → 2 * M + 1 ≤ L → SupportIn f M →
      (∀ x : ℤ, ‖f x‖ ≤ 1) →
      (c₀ * (1 / 3) ^ (k - 1) * (C₂ / C_U ^ k))
          * (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ k
        ≤ uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f := by
    intro L M f hL hM hLM hsup hb
    set α : ℝ := (((2 * M + 1 : ℕ)) : ℝ) / (L : ℝ) with hαdef
    have hLpos : (0:ℝ) < (L:ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : (0:ℕ) < 2 * M + 1) hLM)
    have hαpos : 0 < α := by rw [hαdef]; positivity
    have hαle : α ≤ 1 := by rw [hαdef, div_le_one hLpos]; exact_mod_cast hLM
    set c : ℝ := c₀ * (1 / 3) ^ (k - 1) with hcdef
    have hcpos : 0 < c := mul_pos hc₀ hk3
    set ULt : ℝ := uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f with hULt
    set ULs : ℝ := uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) f with hULs
    set U21t : ℝ := uNormPow t' (arithIcc (1 : ℤ) (2 * M + 1)) (symIcc M) f with hU21t
    set U21s : ℝ := uNormPow s (arithIcc (1 : ℤ) (2 * M + 1)) (symIcc M) f with hU21s
    have hULtnn : 0 ≤ ULt := uNormPow_nonneg _ _ _ _
    have hULsnn : 0 ≤ ULs := uNormPow_nonneg _ _ _ _
    have hU21tnn : 0 ≤ U21t := uNormPow_nonneg _ _ _ _
    have hU21snn : 0 ≤ U21s := uNormPow_nonneg _ _ _ _
    have hup : ULt ≤ C_U * α ^ t' * U21t := by
      have h := hcolU L M f hM hLM hsup hb
      rw [hαdef]; simpa [hULt, hU21t] using h
    have hBs : C₂ * α ^ s * U21s ≤ ULs := by
      have h := hcol₂ L M f hM hLM hsup hb
      rw [hαdef]; simpa [hULs, hU21s] using h
    have hC : c * U21t ^ k ≤ U21s := by
      have h := caseSmall (2 * M + 1) M f (by omega) le_rfl hsup hb
      simpa [hU21t, hU21s, hcdef] using h
    have hαk : α ^ (t' * k) ≤ α ^ s :=
      pow_le_pow_of_le_one hαpos.le hαle (le_mul_two_pow_sub t' s ht' hts)
    have hpow : ULt ^ k ≤ (C_U * α ^ t') ^ k * U21t ^ k := by
      have h := pow_le_pow_left₀ hULtnn hup k
      rwa [mul_pow] at h
    have hCUpos : 0 < C_U ^ k := pow_pos hC_U k
    have step1 : (c * (C₂ / C_U ^ k)) * ULt ^ k
        ≤ (c * (C₂ / C_U ^ k)) * ((C_U * α ^ t') ^ k * U21t ^ k) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have step2 : (c * (C₂ / C_U ^ k)) * ((C_U * α ^ t') ^ k * U21t ^ k)
        = c * C₂ * α ^ (t' * k) * U21t ^ k := by
      field_simp
      ring
    have step3 : c * C₂ * α ^ (t' * k) * U21t ^ k ≤ c * C₂ * α ^ s * U21t ^ k := by
      have hfac : 0 ≤ c * C₂ * U21t ^ k := by positivity
      calc c * C₂ * α ^ (t' * k) * U21t ^ k
          = (c * C₂ * U21t ^ k) * α ^ (t' * k) := by ring
        _ ≤ (c * C₂ * U21t ^ k) * α ^ s := mul_le_mul_of_nonneg_left hαk hfac
        _ = c * C₂ * α ^ s * U21t ^ k := by ring
    have step4 : c * C₂ * α ^ s * U21t ^ k ≤ C₂ * α ^ s * U21s := by
      have hfac : 0 ≤ C₂ * α ^ s := by positivity
      calc c * C₂ * α ^ s * U21t ^ k = (C₂ * α ^ s) * (c * U21t ^ k) := by ring
        _ ≤ (C₂ * α ^ s) * U21s := mul_le_mul_of_nonneg_left hC hfac
        _ = C₂ * α ^ s * U21s := by ring
    calc (c * (C₂ / C_U ^ k)) * ULt ^ k
        ≤ (c * (C₂ / C_U ^ k)) * ((C_U * α ^ t') ^ k * U21t ^ k) := step1
      _ = c * C₂ * α ^ (t' * k) * U21t ^ k := step2
      _ ≤ c * C₂ * α ^ s * U21t ^ k := step3
      _ ≤ C₂ * α ^ s * U21s := step4
      _ ≤ ULs := hBs
  refine ⟨min (c₀ * (1 / 3) ^ (k - 1)) (c₀ * (1 / 3) ^ (k - 1) * (C₂ / C_U ^ k)),
    lt_min (mul_pos hc₀ hk3) (mul_pos (mul_pos hc₀ hk3) (div_pos hC₂ (pow_pos hC_U k))), ?_⟩
  intro L M f hL hM hsup hb
  have hnn : 0 ≤ (uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) f) ^ (2 ^ (s - t')) :=
    pow_nonneg (uNormPow_nonneg _ _ _ _) _
  by_cases hLM : L ≤ 2 * M + 1
  · refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnn) ?_
    simpa [hk] using caseSmall L M f hL hLM hsup hb
  · refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnn) ?_
    simpa [hk] using caseBig L M f hL hM (le_of_lt (not_le.mp hLM)) hsup hb


/-! ## Support and counting of the fibres -/

lemma mem_symIcc_of_ne_zero {f : ℤ → ℂ} {N : ℕ} (hsup : SupportIn f N) {x : ℤ}
    (hx : f x ≠ 0) : x ∈ symIcc N := by
  rw [Work.Peluse.PET.mem_symIcc_iff_abs]
  by_contra hcon
  push_neg at hcon
  have h2 : N < x.natAbs := by
    have h3 : (N : ℤ) < x.natAbs := by
      rw [Int.natCast_natAbs]; exact hcon
    exact_mod_cast h3
  exact hx (hsup x h2)

/-- The fibre `z ↦ f (κ z + r)` of a function supported in `[-N,N]` is supported in
`[-⌊N/|κ|⌋-1, ⌊N/|κ|⌋+1]`. -/
lemma fibreSupportIn {κ : ℤ} {N M : ℕ} {f : ℤ → ℂ} (hsup : SupportIn f N)
    (hM : N / κ.natAbs + 1 ≤ M) (r : ℕ) (hr : r < κ.natAbs) :
    SupportIn (fun z : ℤ => f (κ * z + (r : ℤ))) M := by
  intro z hz
  apply hsup
  have hκpos : 0 < κ.natAbs := lt_of_le_of_lt (Nat.zero_le r) hr
  have hNM : N + 1 ≤ κ.natAbs * M := by
    have h1 : κ.natAbs * (N / κ.natAbs + 1) ≤ κ.natAbs * M := Nat.mul_le_mul_left _ hM
    have h2 : N = κ.natAbs * (N / κ.natAbs) + N % κ.natAbs := (Nat.div_add_mod N κ.natAbs).symm
    have h3 : N % κ.natAbs ≤ κ.natAbs - 1 := by
      have := Nat.mod_lt N hκpos; omega
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  have hzM : M + 1 ≤ z.natAbs := by omega
  have hstep : κ.natAbs * z.natAbs ≤ (κ * z + (r : ℤ)).natAbs + r := by
    have h1 : (κ * z).natAbs ≤ (κ * z + (r : ℤ)).natAbs + (-(r : ℤ)).natAbs := by
      have h := Int.natAbs_add_le (κ * z + (r : ℤ)) (-(r : ℤ))
      simpa using h
    rw [Int.natAbs_neg, Int.natAbs_natCast] at h1
    rwa [Int.natAbs_mul] at h1
  have hbig : N + 1 + κ.natAbs ≤ κ.natAbs * z.natAbs := by
    have h2 : κ.natAbs * (M + 1) ≤ κ.natAbs * z.natAbs := Nat.mul_le_mul_left _ hzM
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  have hrle : r ≤ κ.natAbs - 1 := by omega
  omega

/-- The number of `r < |κ|` for which the fibre `z ↦ f (κ z + r)` is non-zero is at most `2N+1`
when `f` is supported in `[-N,N]`. -/
lemma fibreCount_le {κ : ℤ} {N : ℕ} {f : ℤ → ℂ} (hsup : SupportIn f N) (hκ : κ ≠ 0)
    {s : Finset ℕ} (hs : s ⊆ Finset.range κ.natAbs)
    (hex : ∀ r ∈ s, ∃ z : ℤ, f (κ * z + (r : ℤ)) ≠ 0) :
    s.card ≤ 2 * N + 1 := by
  classical
  let Z : ℕ → ℤ := fun r => if h : r ∈ s then Classical.choose (hex r h) else 0
  have hZ : ∀ r ∈ s, f (κ * Z r + (r : ℤ)) ≠ 0 := by
    intro r hr
    simp only [Z, dif_pos hr]
    exact Classical.choose_spec (hex r hr)
  have hZmem : ∀ r ∈ s, κ * Z r + (r : ℤ) ∈ symIcc N := fun r hr =>
    mem_symIcc_of_ne_zero hsup (hZ r hr)
  have hinj : Set.InjOn (fun r : ℕ => κ * Z r + (r : ℤ)) ↑s := by
    intro a ha b hb hab
    have ha' : a < κ.natAbs := Finset.mem_range.mp (hs ha)
    have hb' : b < κ.natAbs := Finset.mem_range.mp (hs hb)
    have hkey : κ * (Z a - Z b) = (b : ℤ) - (a : ℤ) := by
      have h : κ * Z a + (a : ℤ) = κ * Z b + (b : ℤ) := hab
      linarith
    have hnat : κ.natAbs * (Z a - Z b).natAbs = ((b : ℤ) - (a : ℤ)).natAbs := by
      rw [← Int.natAbs_mul, hkey]
    have hlt : ((b : ℤ) - (a : ℤ)).natAbs < κ.natAbs := by
      have h1 : ((b : ℤ) - (a : ℤ)).natAbs ≤ max a b := by
        by_cases h : a ≤ b
        · have he : (b : ℤ) - (a : ℤ) = ((b - a : ℕ) : ℤ) := by rw [Nat.cast_sub h]
          rw [he, Int.natAbs_natCast]
          exact le_trans (Nat.sub_le _ _) (Nat.le_max_right _ _)
        · have h' : b < a := not_le.mp h
          have he : (b : ℤ) - (a : ℤ) = -(((a - b : ℕ)) : ℤ) := by
            rw [Nat.cast_sub (le_of_lt h')]; ring
          rw [he, Int.natAbs_neg, Int.natAbs_natCast]
          exact le_trans (Nat.sub_le _ _) (Nat.le_max_left _ _)
      exact lt_of_le_of_lt h1 (max_lt ha' hb')
    by_contra hne
    have hpos : 1 ≤ (Z a - Z b).natAbs := by
      rcases Nat.eq_zero_or_pos (Z a - Z b).natAbs with h | h
      · exfalso
        have hz : Z a - Z b = 0 := Int.natAbs_eq_zero.mp h
        have hzk : κ * (Z a - Z b) = 0 := by rw [hz]; ring
        have hzero : (b : ℤ) - (a : ℤ) = 0 := by rw [← hkey]; exact hzk
        exact hne (by omega)
      · exact h
    have hle : κ.natAbs ≤ κ.natAbs * (Z a - Z b).natAbs := by
      calc κ.natAbs = κ.natAbs * 1 := (Nat.mul_one _).symm
        _ ≤ κ.natAbs * (Z a - Z b).natAbs := Nat.mul_le_mul_left _ hpos
    have hcontra : κ.natAbs ≤ ((b : ℤ) - (a : ℤ)).natAbs := by rw [← hnat]; exact hle
    exact absurd hcontra (not_le.mpr hlt)
  have hcard := Finset.card_le_card_of_injOn (fun r => κ * Z r + (r : ℤ)) hZmem hinj
  rw [Work.Peluse.UControl.card_symIcc] at hcard
  exact hcard


/-! ## The level raise at fixed data ##-/

/-- **The level raise at fixed data.**  For `2 ≤ t' ≤ s` there is `c > 0` such that for every
`κ ≠ 0`, every `L ≥ 1`, every `N` and every `1`-bounded `f` supported in `symIcc N`,

`c * (‖f‖^{2^{t'}}_{U^{t'}_{κ[L]}([-N,N])})^{2^{s-t'}} ≤ ‖f‖^{2^s}_{U^s_{κ[L]}([-N,N])}`,

with **no** hypothesis relating `|κ| L` to `N`. -/
theorem uNormPow_level_raise_fixed (t' s : ℕ) (ht' : 2 ≤ t') (hts : t' ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (κ : ℤ), κ ≠ 0 → ∀ (L N : ℕ) (f : ℤ → ℂ),
      1 ≤ L → SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c * (uNormPow t' (arithIcc κ L) (symIcc N) f) ^ (2 ^ (s - t'))
        ≤ uNormPow s (arithIcc κ L) (symIcc N) f := by
  obtain ⟨c₁, hc₁, hplain⟩ := plainLevelRaise t' s ht' hts
  set k : ℕ := 2 ^ (s - t') with hk
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  have ht'1 : 1 ≤ t' := le_trans (by norm_num) ht'
  have hs1 : 1 ≤ s := le_trans (by omega : 1 ≤ t') hts
  refine ⟨c₁ * (1 / 5) ^ (k - 1), mul_pos hc₁ (by positivity), ?_⟩
  intro κ hκ L N f hL hsup hb
  classical
  set M : ℕ := max 1 (N / κ.natAbs + 1) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : N / κ.natAbs + 1 ≤ M := le_max_right _ _
  set g : ℕ → ℤ → ℂ := fun r z => f (κ * z + (r : ℤ)) with hg
  have hgsup : ∀ r, r < κ.natAbs → SupportIn (g r) M :=
    fun r hr => fibreSupportIn hsup hM2 r hr
  have hgb : ∀ (r : ℕ) (z : ℤ), ‖g r z‖ ≤ 1 := fun r z => hb _
  have hfib_t := uNormPowFibre t' ht'1 κ hκ L N M f hsup
  have hfib_s := uNormPowFibre s hs1 κ hκ L N M f hsup
  set SW : ℝ := ((symIcc M).card : ℝ) with hSW
  set SN : ℝ := ((symIcc N).card : ℝ) with hSN
  have hSWpos : 0 < SW := by
    rw [hSW]; exact_mod_cast Finset.card_pos.mpr (Work.Peluse.UControl.symIcc_nonempty M)
  have hSNpos : 0 < SN := by
    rw [hSN]; exact_mod_cast Finset.card_pos.mpr (Work.Peluse.UControl.symIcc_nonempty N)
  set Λ : ℕ → ℝ := fun r => SW * uNormPow t' (arithIcc (1 : ℤ) L) (symIcc M) (g r) with hΛ
  set Γ : ℕ → ℝ := fun r => SW * uNormPow s (arithIcc (1 : ℤ) L) (symIcc M) (g r) with hΓ
  have hΛnn : ∀ r, 0 ≤ Λ r := fun r => mul_nonneg hSWpos.le (uNormPow_nonneg _ _ _ _)
  have hΓnn : ∀ r, 0 ≤ Γ r := fun r => mul_nonneg hSWpos.le (uNormPow_nonneg _ _ _ _)
  have hsum_t : SN * uNormPow t' (arithIcc κ L) (symIcc N) f
      = ∑ r ∈ Finset.range κ.natAbs, Λ r := by
    rw [hfib_t, hΛ, hSN, hSW, ← Finset.mul_sum, ← mul_assoc,
      mul_inv_cancel₀ (by
        exact_mod_cast (Finset.card_ne_zero.mpr (Work.Peluse.UControl.symIcc_nonempty N))), one_mul]
  have hsum_s : SN * uNormPow s (arithIcc κ L) (symIcc N) f
      = ∑ r ∈ Finset.range κ.natAbs, Γ r := by
    rw [hfib_s, hΓ, hSN, hSW, ← Finset.mul_sum, ← mul_assoc,
      mul_inv_cancel₀ (by
        exact_mod_cast (Finset.card_ne_zero.mpr (Work.Peluse.UControl.symIcc_nonempty N))), one_mul]
  have hper : ∀ r ∈ Finset.range κ.natAbs, c₁ * (Λ r) ^ k ≤ SW ^ (k - 1) * Γ r := by
    intro r hr
    have hrlt : r < κ.natAbs := Finset.mem_range.mp hr
    have h := hplain L M (g r) hL hM1 (hgsup r hrlt) (hgb r)
    have hSWk : (0:ℝ) < SW ^ k := pow_pos hSWpos k
    have h2 : c₁ * (SW * uNormPow t' (arithIcc (1:ℤ) L) (symIcc M) (g r)) ^ k
        ≤ SW ^ k * uNormPow s (arithIcc (1:ℤ) L) (symIcc M) (g r) := by
      rw [mul_pow]
      calc c₁ * (SW ^ k * uNormPow t' (arithIcc (1:ℤ) L) (symIcc M) (g r) ^ k)
          = SW ^ k * (c₁ * uNormPow t' (arithIcc (1:ℤ) L) (symIcc M) (g r) ^ k) := by ring
        _ ≤ SW ^ k * uNormPow s (arithIcc (1:ℤ) L) (symIcc M) (g r) :=
            mul_le_mul_of_nonneg_left h hSWk.le
    have h4 : SW ^ k * uNormPow s (arithIcc (1:ℤ) L) (symIcc M) (g r)
        = SW ^ (k - 1) * Γ r := by
      rw [hΓ,
        show SW ^ k = SW ^ (k - 1) * SW by rw [← pow_succ, Nat.sub_add_cancel hk1]]
      ring
    rw [hΛ]
    exact h2.trans_eq h4
  set m : ℕ := ((Finset.range κ.natAbs).filter (fun r => Λ r ≠ 0)).card with hm
  have hjensen : (∑ r ∈ Finset.range κ.natAbs, Λ r) ^ k
      ≤ ((m : ℝ)) ^ (k - 1) * ∑ r ∈ Finset.range κ.natAbs, (Λ r) ^ k := by
    have h := sum_pow_le_card_pow_mul_sum_pow (Finset.range κ.natAbs) Λ (fun r _ => hΛnn r) hk1
    simpa [hm] using h
  have hsum_per : c₁ * ∑ r ∈ Finset.range κ.natAbs, (Λ r) ^ k
      ≤ SW ^ (k - 1) * ∑ r ∈ Finset.range κ.natAbs, Γ r := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun r hr => hper r hr)
  have hmκ : m ≤ κ.natAbs := by
    rw [hm]
    simpa using Finset.card_filter_le (Finset.range κ.natAbs) (fun r : ℕ => Λ r ≠ 0)
  have hmN : m ≤ 2 * N + 1 := by
    have hsub : (Finset.range κ.natAbs).filter (fun r => Λ r ≠ 0) ⊆
        (Finset.range κ.natAbs).filter (fun r => ∃ z : ℤ, g r z ≠ 0) := by
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨hr.1, ?_⟩
      by_contra hcon
      push_neg at hcon
      have hzero : g r = 0 := funext hcon
      exact hr.2 (by simp only [hΛ]; rw [hzero, uNormPow_zeroFun, mul_zero])
    rw [hm]
    refine le_trans (Finset.card_le_card hsub)
      (fibreCount_le (s := (Finset.range κ.natAbs).filter (fun r => ∃ z : ℤ, g r z ≠ 0))
        hsup hκ (Finset.filter_subset _ _) ?_)
    exact fun r hr => (Finset.mem_filter.mp hr).2
  have hmSW : ((m : ℕ) : ℝ) * SW ≤ 5 * SN := by
    have hSWval : SW = ((2 * M + 1 : ℕ) : ℝ) := by
      rw [hSW, Work.Peluse.UControl.card_symIcc]
    have hSNval : SN = ((2 * N + 1 : ℕ) : ℝ) := by
      rw [hSN, Work.Peluse.UControl.card_symIcc]
    rw [hSWval, hSNval]
    by_cases hcase : κ.natAbs ≤ 2 * N + 1
    · have hMle : (2 * M + 1 : ℕ) ≤ 2 * (N / κ.natAbs + 1) + 1 := by
        have h0 : M ≤ N / κ.natAbs + 1 := by
          rw [hMdef]
          exact max_le (Nat.le_add_left 1 (N / κ.natAbs)) le_rfl
        omega
      have h1 : m * (2 * M + 1) ≤ κ.natAbs * (2 * (N / κ.natAbs + 1) + 1) :=
        Nat.mul_le_mul hmκ hMle
      have h2 : κ.natAbs * (2 * (N / κ.natAbs + 1) + 1) ≤ 5 * (2 * N + 1) := by
        have h3 : κ.natAbs * (N / κ.natAbs) ≤ N := Nat.mul_div_le N κ.natAbs
        nlinarith [hcase, Nat.zero_le κ.natAbs, Nat.zero_le N]
      exact_mod_cast le_trans h1 h2
    · have hdiv : N / κ.natAbs = 0 := Nat.div_eq_of_lt (by omega)
      have hMone : M = 1 := by
        rw [hMdef, hdiv]; norm_num
      have h2 : m * (2 * M + 1) ≤ m * 3 := by rw [hMone]
      have h3 : m * 3 ≤ (2 * N + 1) * 3 := Nat.mul_le_mul_right _ hmN
      have h4 : (2 * N + 1) * 3 ≤ 5 * (2 * N + 1) := by omega
      exact_mod_cast le_trans (le_trans h2 h3) h4
  have key1 : c₁ * (SN * uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k
      ≤ ((m : ℝ) * SW) ^ (k - 1) * (SN * uNormPow s (arithIcc κ L) (symIcc N) f) := by
    rw [hsum_t, hsum_s]
    calc c₁ * (∑ r ∈ Finset.range κ.natAbs, Λ r) ^ k
        ≤ c₁ * (((m : ℝ)) ^ (k - 1) * ∑ r ∈ Finset.range κ.natAbs, (Λ r) ^ k) :=
          mul_le_mul_of_nonneg_left hjensen hc₁.le
      _ = ((m : ℝ)) ^ (k - 1) * (c₁ * ∑ r ∈ Finset.range κ.natAbs, (Λ r) ^ k) := by ring
      _ ≤ ((m : ℝ)) ^ (k - 1) * (SW ^ (k - 1) * ∑ r ∈ Finset.range κ.natAbs, Γ r) :=
          mul_le_mul_of_nonneg_left hsum_per (pow_nonneg (Nat.cast_nonneg m) _)
      _ = ((m : ℝ) * SW) ^ (k - 1) * ∑ r ∈ Finset.range κ.natAbs, Γ r := by
          rw [mul_pow]; ring
  have key3 : c₁ * (SN * uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k
      ≤ (5 * SN) ^ (k - 1) * (SN * uNormPow s (arithIcc κ L) (symIcc N) f) := by
    refine le_trans key1 ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hmSW (k - 1))
      (mul_nonneg hSNpos.le (uNormPow_nonneg _ _ _ _))
  have key5 : c₁ * (uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k
      ≤ 5 ^ (k - 1) * uNormPow s (arithIcc κ L) (symIcc N) f := by
    refine le_of_mul_le_mul_left ?_ (pow_pos hSNpos k)
    calc SN ^ k * (c₁ * (uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k)
        = c₁ * (SN * uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k := by rw [mul_pow]; ring
      _ ≤ (5 * SN) ^ (k - 1) * (SN * uNormPow s (arithIcc κ L) (symIcc N) f) := key3
      _ = SN ^ k * (5 ^ (k - 1) * uNormPow s (arithIcc κ L) (symIcc N) f) := by
          rw [mul_pow,
            show SN ^ k = SN ^ (k - 1) * SN by rw [← pow_succ, Nat.sub_add_cancel hk1]]
          ring
  calc c₁ * (1 / 5) ^ (k - 1) * (uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k
      = (1 / 5) ^ (k - 1) * (c₁ * (uNormPow t' (arithIcc κ L) (symIcc N) f) ^ k) := by ring
    _ ≤ (1 / 5) ^ (k - 1) * (5 ^ (k - 1) * uNormPow s (arithIcc κ L) (symIcc N) f) :=
        mul_le_mul_of_nonneg_left key5 (by positivity)
    _ = uNormPow s (arithIcc κ L) (symIcc N) f := by
        rw [← mul_assoc, ← mul_pow]
        norm_num


/-! ## The target -/

theorem uNormPowTransferTwo (s t' : ℕ) (ht' : 2 ≤ t') (hts : t' ≤ s) :
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧
      ∀ (κ : ℤ), κ ≠ 0 → ∀ (L L' N N' : ℕ) (f : ℤ → ℂ),
        L ≤ N → 1 ≤ L → L ≤ L' → N ≤ N' → Work.Peluse.SupportIn f N →
        (∀ x : ℤ, ‖f x‖ ≤ 1) →
        C * (Work.Peluse.uNormPow t' (Work.Peluse.arithIcc κ L') (Work.Peluse.symIcc N') f) ^ E
          ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ L) (Work.Peluse.symIcc N) f := by
  obtain ⟨C₁, hC₁, hshr⟩ := Work.Peluse.UControl.uNormPow_shrink_ambient (s := t') ht'
  obtain ⟨c, hc, hfix⟩ := uNormPow_level_raise_fixed t' s ht' hts
  set k : ℕ := 2 ^ (s - t') with hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have h0 : (0 : ℕ) < k := by rw [hk]; exact lt_of_lt_of_le Nat.zero_lt_one Nat.one_le_two_pow
    exact_mod_cast h0
  refine ⟨c * C₁ ^ k, (k : ℝ), mul_pos hc (pow_pos hC₁ k), hkpos, ?_⟩
  intro κ hκ L L' N N' f hLN hL hLL hNN hsup hb
  have h1 := hshr κ L L' N N' f hκ hL hLL hNN hsup hb
  have h2 := hfix κ hκ L N f hL hsup hb
  have h3 : (C₁ * Work.Peluse.uNormPow t'
        (Work.Peluse.arithIcc κ L') (Work.Peluse.symIcc N') f) ^ k
      ≤ (Work.Peluse.uNormPow t'
        (Work.Peluse.arithIcc κ L) (Work.Peluse.symIcc N) f) ^ k :=
    pow_le_pow_left₀ (mul_nonneg hC₁.le (uNormPow_nonneg _ _ _ _)) h1 k
  rw [Real.rpow_natCast]
  calc c * C₁ ^ k * (Work.Peluse.uNormPow t'
          (Work.Peluse.arithIcc κ L') (Work.Peluse.symIcc N') f) ^ k
      = c * (C₁ * Work.Peluse.uNormPow t'
          (Work.Peluse.arithIcc κ L') (Work.Peluse.symIcc N') f) ^ k := by
        rw [mul_pow]; ring
    _ ≤ c * (Work.Peluse.uNormPow t'
          (Work.Peluse.arithIcc κ L) (Work.Peluse.symIcc N) f) ^ k :=
        mul_le_mul_of_nonneg_left h3 hc.le
    _ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ L) (Work.Peluse.symIcc N) f := h2

end

end Work.Peluse.Prop36SW
