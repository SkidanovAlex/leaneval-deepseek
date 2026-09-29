import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.param.pow_six_mul_add_one
import Submission.Work.Main.param.two_pow_le_pow

namespace Work.Main.param

/-- Every chunk size `tᵢ` of a valid parameter list exceeds `2d`: the parameter hypothesis
says the interval `((1 - 1/(2d))·tᵢ, (1 - 1/(4d))·tᵢ]` contains the odd number `sᵢ ≥ 1`. -/
private lemma paramOK_getD_gt {n : ℕ} {ts ss : List ℕ} (hOK : HvdH.ParamOK n ts ss) {i : ℕ}
    (hi : i < HvdH.D) : 2 * HvdH.D < ts.getD i 0 := by
  obtain ⟨hDts, hDss, -, -, -, hssineq, -, hodd⟩ := hOK
  obtain ⟨hin1, hin2⟩ := hssineq i hi
  have hsslen : i < ss.length := by rw [hDss]; exact hi
  set t := ts.getD i 0 with htdef
  set s := ss.getD i 0 with hsdef
  have hsmem : s ∈ ss := by
    rw [hsdef, List.getD_eq_getElem ss 0 hsslen]
    exact List.getElem_mem hsslen
  have hspos : 1 ≤ s := by have := (hodd s hsmem).pos; omega
  have hDcast : (0 : ℝ) < (HvdH.D : ℝ) := by norm_num [HvdH.D]
  have hcoef : (0 : ℝ) < 1 / (4 * (HvdH.D : ℝ)) := by
    apply one_div_pos.mpr; linarith
  have h2D : (0 : ℝ) < 2 * (HvdH.D : ℝ) := by linarith
  have htpos : 0 < t := by
    by_contra h
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos h
    rw [ht0] at hin2
    simp only [Nat.cast_zero, mul_zero] at hin2
    have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hspos
    linarith
  have hst_lt : (s : ℝ) < (t : ℝ) := by
    have hlt : (1 - 1 / (4 * (HvdH.D : ℝ))) * (t : ℝ) < (t : ℝ) := by
      have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
      nlinarith [mul_pos hcoef htR]
    exact lt_of_le_of_lt hin2 hlt
  have hst : s < t := by exact_mod_cast hst_lt
  have hk1 : 1 ≤ t - s := by omega
  have hk2 : ((t - s : ℕ) : ℝ) * (2 * (HvdH.D : ℝ)) < (t : ℝ) := by
    have hsub : ((t - s : ℕ) : ℝ) = (t : ℝ) - (s : ℝ) := Nat.cast_sub (le_of_lt hst)
    have hsimp : (1 - 2 / (4 * (HvdH.D : ℝ))) = 1 - 1 / (2 * (HvdH.D : ℝ)) := by ring
    rw [hsimp] at hin1
    have htmp : (t : ℝ) - (s : ℝ) < (t : ℝ) / (2 * (HvdH.D : ℝ)) := by
      have heq : (1 - 1 / (2 * (HvdH.D : ℝ))) * (t : ℝ) =
          (t : ℝ) - (t : ℝ) / (2 * (HvdH.D : ℝ)) := by ring
      linarith [hin1, heq]
    rw [hsub]
    have hh := (lt_div_iff₀ h2D).mp htmp
    linarith
  have hle1 : (1 : ℝ) ≤ ((t - s : ℕ) : ℝ) := by exact_mod_cast hk1
  have hfin : (2 * (HvdH.D : ℝ)) < (t : ℝ) := by nlinarith
  have hfin2 : 2 * HvdH.D < t := by exact_mod_cast hfin
  rw [htdef] at hfin2
  exact hfin2

theorem tsSum_pow_le {n K : ℕ} {ts ss : List ℕ} (hOK : HvdH.ParamOK n ts ss)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) (hb : 256 * K ^ 2 ≤ HvdH.bpar n) :
    ts.sum * (HvdH.ppar n + 1) ^ K ≤ n * n.size := by
  have hgt : ∀ i < HvdH.D, 2 * HvdH.D < ts.getD i 0 := fun i hi => paramOK_getD_gt hOK hi
  obtain ⟨hDts, hDss, hpair, hprod, hent, hssineq, hcop, hodd⟩ := hOK
  set b := HvdH.bpar n with hbdef
  set T := HvdH.Tpar n with hTdef
  set R := HvdH.rpar n with hRdef
  set m := (HvdH.kTpar n + HvdH.D - 1) / HvdH.D with hmdef
  have hDnum : HvdH.D = 1729 := rfl
  have hDpos : 0 < HvdH.D := by norm_num [HvdH.D]
  have hD1 : 1 ≤ HvdH.D := hDpos
  have hRm : R = 2 ^ m := by rw [hRdef, HvdH.rpar, hmdef]
  -- R exceeds 2d
  have h0len : 0 < ts.length := by rw [hDts]; exact hDpos
  have ht_gt : 2 * HvdH.D < ts.getD 0 0 := hgt 0 hDpos
  have hmem0 : ts.getD 0 0 ∈ ts := by
    rw [List.getD_eq_getElem ts 0 h0len]
    exact List.getElem_mem h0len
  have hRgt : 2 * HvdH.D < R := by
    rcases hent (ts.getD 0 0) hmem0 with h | h
    · omega
    · omega
  -- R^d ≤ 2^d T
  have hRD : R ^ HvdH.D ≤ 2 ^ HvdH.D * T := by
    have hm : m * HvdH.D ≤ HvdH.kTpar n + HvdH.D - 1 := by
      rw [hmdef]; exact Nat.div_mul_le_self _ _
    rw [hRm, ← pow_mul]
    calc 2 ^ (m * HvdH.D) ≤ 2 ^ (HvdH.kTpar n + HvdH.D - 1) :=
          (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hm
      _ ≤ 2 ^ (HvdH.kTpar n + HvdH.D) :=
          (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)
      _ = 2 ^ HvdH.kTpar n * 2 ^ HvdH.D := pow_add _ _ _
      _ = T * 2 ^ HvdH.D := by rw [hTdef, HvdH.Tpar]
      _ = 2 ^ HvdH.D * T := by ring
  -- T ≥ 2^(11d)
  have hm12 : 12 ≤ m := by
    rcases Nat.lt_or_ge m 12 with h | h
    · exfalso
      have hle : R ≤ 2 ^ 11 := by
        rw [hRm]
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)
      have h211 : 2 ^ 11 < 2 * HvdH.D := by norm_num [HvdH.D]
      omega
    · exact h
  have hTbig : 2 ^ (11 * HvdH.D) ≤ T := by
    have h1 : 2 ^ (12 * HvdH.D) ≤ R ^ HvdH.D := by
      rw [hRm, ← pow_mul]
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr (by nlinarith)
    have h2 : 2 ^ (12 * HvdH.D) = 2 ^ (11 * HvdH.D) * 2 ^ HvdH.D := by
      have he : 12 * HvdH.D = 11 * HvdH.D + HvdH.D := by ring
      rw [he, pow_add]
    have h3 : 2 ^ HvdH.D * 2 ^ (11 * HvdH.D) ≤ 2 ^ HvdH.D * T := by
      have h4 : 2 ^ HvdH.D * 2 ^ (11 * HvdH.D) = 2 ^ (12 * HvdH.D) := by
        rw [Nat.mul_comm (2 ^ HvdH.D), h2]
      rw [h4]
      exact le_trans h1 hRD
    exact Nat.le_of_mul_le_mul_left h3 (by positivity)
  -- b ≥ 1
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · exfalso
      have hbc : HvdH.bpar n = 0 := by rw [← hbdef]; exact hb0
      have hnle : n ≤ 1 := by
        have h := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) n
        have hbc' : Nat.clog 2 n = 0 := hbc
        rw [hbc'] at h
        simpa using h
      have hnpos : 1 ≤ n := by
        by_contra h
        have hn0 : n = 0 := by omega
        rw [hn0] at hTb
        simp only [Nat.mul_zero] at hTb
        omega
      have hn1 : n = 1 := by omega
      have hT1 : T = 1 := by
        rw [hTdef, HvdH.Tpar, HvdH.kTpar, HvdH.bpar, hn1]
        simp [Nat.clog_one_right]
      have h2le : 2 ≤ 2 ^ (11 * HvdH.D) := by
        have h1 : (1 : ℕ) ≤ 11 * HvdH.D := by norm_num [HvdH.D]
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (11 * HvdH.D) := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr h1
      omega
    · exact hb1
  -- T ≤ 8n
  have hT8 : T ≤ 8 * n := by
    have h1 : T ≤ T * b := Nat.le_mul_of_pos_right T hbpos
    omega
  -- b is large
  have hb256 : 256 ≤ b := by
    have hnle : n ≤ 2 ^ b := by
      have h := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) n
      have hb_eq : b = Nat.clog 2 n := by rw [hbdef, HvdH.bpar]
      rw [← hb_eq] at h
      exact h
    have hle : 2 ^ (11 * HvdH.D) ≤ 2 ^ (b + 3) := by
      calc 2 ^ (11 * HvdH.D) ≤ T := hTbig
        _ ≤ 8 * n := hT8
        _ ≤ 8 * 2 ^ b := by nlinarith
        _ = 2 ^ 3 * 2 ^ b := by norm_num
        _ = 2 ^ (b + 3) := by rw [pow_add]; ring
    have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    rw [hDnum] at h
    omega
  have hK256 : 256 * K ^ 2 ≤ b := hb
  -- n ≥ 2^(b-1)
  have hn2 : 1 < n := by
    by_contra h
    have hnle1 : n ≤ 1 := by omega
    have hbc : HvdH.bpar n = 0 := by
      rw [HvdH.bpar]
      have h1 : n ≤ 2 ^ 0 := by simpa using hnle1
      have h2 := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr h1
      omega
    omega
  have hnpred : 2 ^ (b - 1) < n := by
    have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num : 1 < 2) hn2
    simp only [Nat.pred_eq_sub_one] at h
    have hb_eq : b = Nat.clog 2 n := by rw [hbdef, HvdH.bpar]
    rw [hb_eq]
    exact h
  -- b ≤ n.size
  have hbsize : b ≤ n.size := by
    rw [hbdef, HvdH.bpar]
    exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr (le_of_lt (Nat.lt_size_self n))
  -- ts.sum ≤ d·R
  have hsumR : ts.sum ≤ HvdH.D * R := by
    have hbnd : ∀ t ∈ ts, t ≤ R := by
      intro t ht
      rcases hent t ht with h | h
      · omega
      · omega
    have h1 : ts.sum ≤ (ts.map (fun _ => R)).sum := by
      simpa using (List.sum_le_sum (l := ts) (f := id) (g := fun _ => R) hbnd)
    have h2 : (ts.map (fun _ => R)).sum = HvdH.D * R := by
      have : (ts.map (fun _ => R)).sum = ts.length * R := by
        simp
      rw [hDts] at this
      exact this
    omega
  -- the two delegated arithmetic bounds
  have hX : (6 * b + 1) ^ (K * HvdH.D) ≤ 2 ^ (HvdH.D * b / 8) := by
    have h := pow_six_mul_add_one (b := b) (K := K) hb256 hK256
    simpa [hDnum] using h
  have hY : 2 ^ (12 * HvdH.D + 3 + HvdH.D * b / 8) ≤ n ^ (HvdH.D - 1) := by
    have h := two_pow_le_pow (b := b) (n := n) (by omega) hnpred
    simpa [hDnum] using h
  -- final power comparison
  have hDD : HvdH.D ^ HvdH.D * 2 ^ HvdH.D * 8 ≤ 2 ^ (12 * HvdH.D + 3) := by
    have h1 : HvdH.D ≤ 2 ^ 11 := by norm_num [HvdH.D]
    have h2 : HvdH.D ^ HvdH.D ≤ 2 ^ (11 * HvdH.D) := by
      have := Nat.pow_le_pow_left h1 HvdH.D
      rwa [← pow_mul] at this
    have h3 : HvdH.D ^ HvdH.D * 2 ^ HvdH.D * 8 ≤ 2 ^ (11 * HvdH.D) * 2 ^ HvdH.D * 2 ^ 3 :=
      Nat.mul_le_mul (Nat.mul_le_mul h2 le_rfl) (by norm_num)
    calc HvdH.D ^ HvdH.D * 2 ^ HvdH.D * 8 ≤ 2 ^ (11 * HvdH.D) * 2 ^ HvdH.D * 2 ^ 3 := h3
      _ = 2 ^ (11 * HvdH.D + HvdH.D + 3) := by
          rw [← pow_add, ← pow_add]
      _ = 2 ^ (12 * HvdH.D + 3) := by
          have he : 11 * HvdH.D + HvdH.D + 3 = 12 * HvdH.D + 3 := by ring
          rw [he]
  have hP : (ts.sum * (6 * b + 1) ^ K) ^ HvdH.D ≤ (n * b) ^ HvdH.D := by
    calc (ts.sum * (6 * b + 1) ^ K) ^ HvdH.D
        = ts.sum ^ HvdH.D * ((6 * b + 1) ^ K) ^ HvdH.D := mul_pow _ _ _
      _ = ts.sum ^ HvdH.D * (6 * b + 1) ^ (K * HvdH.D) := by rw [pow_mul]
      _ ≤ (HvdH.D * R) ^ HvdH.D * 2 ^ (HvdH.D * b / 8) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hsumR _) hX
      _ = HvdH.D ^ HvdH.D * R ^ HvdH.D * 2 ^ (HvdH.D * b / 8) := by rw [mul_pow]
      _ ≤ HvdH.D ^ HvdH.D * (2 ^ HvdH.D * T) * 2 ^ (HvdH.D * b / 8) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hRD)
      _ ≤ HvdH.D ^ HvdH.D * (2 ^ HvdH.D * (8 * n)) * 2 ^ (HvdH.D * b / 8) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT8))
      _ ≤ 2 ^ (12 * HvdH.D + 3) * n * 2 ^ (HvdH.D * b / 8) := by
          have : HvdH.D ^ HvdH.D * (2 ^ HvdH.D * (8 * n)) =
              (HvdH.D ^ HvdH.D * 2 ^ HvdH.D * 8) * n := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hDD)
      _ = n * (2 ^ (12 * HvdH.D + 3) * 2 ^ (HvdH.D * b / 8)) := by ring
      _ = n * 2 ^ (12 * HvdH.D + 3 + HvdH.D * b / 8) := by rw [← pow_add]
      _ ≤ n * n ^ (HvdH.D - 1) := Nat.mul_le_mul_left _ hY
      _ = n ^ HvdH.D := by
          rw [← pow_succ', Nat.sub_add_cancel hD1]
      _ ≤ n ^ HvdH.D * b ^ HvdH.D :=
          Nat.le_mul_of_pos_right _ (pow_pos hbpos _)
      _ = (n * b) ^ HvdH.D := by rw [mul_pow]
  have key : ts.sum * (6 * b + 1) ^ K ≤ n * b :=
    (Nat.pow_le_pow_iff_left (by omega : HvdH.D ≠ 0)).mp hP
  have hppar : HvdH.ppar n + 1 = 6 * b + 1 := by rw [HvdH.ppar, ← hbdef]
  calc ts.sum * (HvdH.ppar n + 1) ^ K = ts.sum * (6 * b + 1) ^ K := by rw [hppar]
    _ ≤ n * b := key
    _ ≤ n * n.size := Nat.mul_le_mul_left n hbsize

end Work.Main.param
