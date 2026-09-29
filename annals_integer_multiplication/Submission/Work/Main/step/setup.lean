import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Params.steps
import Submission.Work.Params.vszlemmas
import Submission.Work.ConvR.listProdB

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 4000

namespace Work.Main.step

open HvdH

/-! ## Elementary size arithmetic -/

theorem vsz_int_nat (m : ℕ) : vsz (Val.int (m : ℤ)) = m.size + 2 := by
  rw [Work.Main.vsz_int, HvdH.isz, Int.natAbs_natCast]

theorem size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, Nat.pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_sub_le (a b : ℕ) : (a - b).size ≤ a.size := Nat.size_le_size (Nat.sub_le a b)

theorem size_add_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ max a.size b.size :=
    lt_of_lt_of_le (Nat.lt_size_self a) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb : b < 2 ^ max a.size b.size :=
    lt_of_lt_of_le (Nat.lt_size_self b) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  calc a + b < 2 ^ max a.size b.size + 2 ^ max a.size b.size := Nat.add_lt_add ha hb
    _ = 2 ^ (max a.size b.size + 1) := by rw [pow_succ]; ring

theorem pow_sq_le (s : ℕ) : (s + 1) ^ 2 ≤ 3 * 2 ^ s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases lt_or_ge s 3 with hs | hs
    · interval_cases s <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      have hk : 2 ≤ k := by omega
      have h1 : (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
      calc (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := h1
        _ ≤ 2 * (3 * 2 ^ k) := Nat.mul_le_mul_left 2 (ih k (by omega))
        _ = 3 * 2 ^ (k + 1) := by ring

theorem size_sq_le (n : ℕ) : (n.size + 1) ^ 2 ≤ 6 * (n + 1) := by
  have h1 : 2 ^ (n.size - 1) ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have h2 : 0 < n.size := Nat.size_pos.mpr h
      have h3 : n.size - 1 < n.size := Nat.sub_lt h2 (by norm_num)
      exact le_trans (Nat.lt_size.mp h3) (by omega)
  have h2 : 2 ^ n.size ≤ 2 * (n + 1) := by
    rcases Nat.eq_zero_or_pos n.size with h | h
    · rw [h]; omega
    · have he : n.size = (n.size - 1) + 1 := (Nat.succ_pred_eq_of_pos h).symm
      have h4 : 2 ^ n.size = 2 ^ (n.size - 1) * 2 := by
        nth_rewrite 1 [he]
        rw [pow_succ]
      rw [h4]
      calc 2 ^ (n.size - 1) * 2 = 2 * 2 ^ (n.size - 1) := by ring
        _ ≤ 2 * (n + 1) := Nat.mul_le_mul_left 2 h1
  calc (n.size + 1) ^ 2 ≤ 3 * 2 ^ n.size := pow_sq_le n.size
    _ ≤ 3 * (2 * (n + 1)) := Nat.mul_le_mul_left 3 h2
    _ = 6 * (n + 1) := by ring

/-! ## Cost arithmetic for the per-step budget `KB*KB*B` -/

theorem cost_pick {K0 k s Cg KB B : ℕ} (hK : K0 ≤ KB) (hk : k + 1 ≤ 13)
    (hs : s + 1 ≤ 13 * (Cg * B)) (hCB : 169 * Cg ≤ KB) :
    K0 * (k + 1) * (s + 1) ≤ KB * KB * B := by
  have h1 : K0 * (k + 1) ≤ KB * 13 := Nat.mul_le_mul hK hk
  calc K0 * (k + 1) * (s + 1) ≤ (KB * 13) * (13 * (Cg * B)) := Nat.mul_le_mul h1 hs
    _ = (169 * Cg) * KB * B := by ring
    _ ≤ (KB * KB) * B := by
        have h3 : (169 * Cg) * KB ≤ KB * KB := Nat.mul_le_mul_right KB hCB
        exact Nat.mul_le_mul_right B h3
    _ = KB * KB * B := by ring

theorem cost_basic {K0 s Cg KB B : ℕ} (hK : K0 ≤ KB) (hs : s ≤ 4 * (Cg * B))
    (hCB : 4 * Cg ≤ KB) : K0 * s ≤ KB * KB * B := by
  calc K0 * s ≤ KB * (4 * (Cg * B)) := Nat.mul_le_mul hK hs
    _ = (4 * Cg) * KB * B := by ring
    _ ≤ (KB * KB) * B := by
        have h3 : (4 * Cg) * KB ≤ KB * KB := Nat.mul_le_mul_right KB hCB
        exact Nat.mul_le_mul_right B h3
    _ = KB * KB * B := by ring

theorem cost_sm {K0 s C KB B : ℕ} (hK : K0 ≤ KB) (hs : s ≤ C * B) (hC : C ≤ KB) :
    K0 * s ≤ KB * KB * B := by
  calc K0 * s ≤ KB * (C * B) := Nat.mul_le_mul hK hs
    _ = C * KB * B := by ring
    _ ≤ KB * KB * B := by
        have h3 : C * KB ≤ KB * KB := Nat.mul_le_mul_right KB hC
        exact Nat.mul_le_mul_right B h3

theorem cost_lp {K0 V K2 KB B S : ℕ} (hK : K0 ≤ KB) (hV : V + 1 ≤ 115201 * S)
    (hS : S ^ 2 ≤ K2 * B) (h2 : 115201 ^ 2 * K2 ≤ KB) :
    K0 * (V + 1) ^ 2 ≤ KB * KB * B := by
  have h1 : (V + 1) ^ 2 ≤ (115201 * S) ^ 2 := Nat.pow_le_pow_left hV 2
  have h1' : (115201 * S) ^ 2 = 115201 ^ 2 * S ^ 2 := by ring
  calc K0 * (V + 1) ^ 2 ≤ KB * (115201 * S) ^ 2 := Nat.mul_le_mul hK h1
    _ = KB * (115201 ^ 2 * S ^ 2) := by rw [h1']
    _ ≤ KB * (115201 ^ 2 * (K2 * B)) := Nat.mul_le_mul_left KB (Nat.mul_le_mul_left _ hS)
    _ = (115201 ^ 2 * K2) * KB * B := by ring
    _ ≤ (KB * KB) * B := Nat.mul_le_mul_right B (Nat.mul_le_mul_right KB h2)
    _ = KB * KB * B := by ring

theorem cost_nc {K0 a b C KB B : ℕ} (hK : K0 ≤ KB) (h : a * b ≤ C * B) (hC : C ≤ KB) :
    K0 * a * b ≤ KB * KB * B := by
  have h1 : K0 * a * b ≤ KB * (a * b) := by
    calc K0 * a * b = (K0 * a) * b := by ring
      _ ≤ (KB * a) * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_right a hK)
      _ = KB * (a * b) := by ring
  calc K0 * a * b ≤ KB * (a * b) := h1
    _ ≤ KB * (C * B) := Nat.mul_le_mul_left KB h
    _ = C * KB * B := by ring
    _ ≤ KB * KB * B := by
        have h3 : C * KB ≤ KB * KB := Nat.mul_le_mul_right KB hC
        exact Nat.mul_le_mul_right B h3

/-! ## `nchunks` -/

theorem nchunks_le_succ (n b : ℕ) : nchunks n b ≤ n + 1 := by
  rw [nchunks]
  rcases Nat.eq_zero_or_pos b with h | h
  · rw [h, Nat.div_zero]; omega
  · refine Nat.div_le_of_le_mul ?_
    have hsub : n + b - 1 ≤ n + b := Nat.sub_le _ _
    nlinarith [hsub, h]

theorem size_succ_le (n : ℕ) : (n + 1).size ≤ n.size + 1 := by
  rw [Nat.size_le]
  have h1 : n < 2 ^ n.size := Nat.lt_size_self n
  have h3 : 1 ≤ 2 ^ n.size := Nat.one_le_two_pow
  calc n + 1 ≤ 2 ^ n.size := h1
    _ < 2 ^ (n.size + 1) := by rw [pow_succ]; omega

theorem nchunks_size_le (n b : ℕ) : (nchunks n b).size ≤ n.size + 1 := by
  have h := nchunks_le_succ n b
  exact le_trans (Nat.size_le_size h) (size_succ_le n)

/-! ## Sizes of the parameters `bpar ... rpar` -/

theorem clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))

theorem bpar_size_le (n : ℕ) : (bpar n).size ≤ n.size :=
  Nat.size_le_size (by rw [bpar]; exact clog_two_le_self n)

theorem bpar_size (n : ℕ) : (bpar n).size ≤ n.size + 1 := by have := bpar_size_le n; omega

theorem ppar_size (n : ℕ) : (ppar n).size ≤ n.size + 4 := by
  unfold ppar
  have h := size_mul_le 6 (bpar n)
  have h6 : (6 : ℕ).size ≤ 3 := Nat.size_le.mpr (by norm_num)
  have hb := bpar_size n
  omega

theorem apar_size (n : ℕ) : (apar n).size ≤ n.size + 30 := by
  have hle : apar n ≤ 12 * D ^ 2 * bpar n + 1 := by
    unfold apar
    have h1 : Nat.sqrt (Nat.sqrt (12 * D ^ 2 * bpar n - 1)) ≤ 12 * D ^ 2 * bpar n - 1 :=
      le_trans (Nat.sqrt_le_self _) (Nat.sqrt_le_self (12 * D ^ 2 * bpar n - 1))
    omega
  have h2 : (12 * D ^ 2 * bpar n).size ≤ 26 + (bpar n).size := by
    have h := size_mul_le (12 * D ^ 2) (bpar n)
    have h26 : (12 * D ^ 2).size ≤ 26 := Nat.size_le.mpr (by norm_num [D])
    omega
  have h3 : (12 * D ^ 2 * bpar n + 1).size ≤
      max (12 * D ^ 2 * bpar n).size (1 : ℕ).size + 1 := size_add_le _ _
  have h1 : (1 : ℕ).size ≤ 1 := Nat.size_le.mpr (by norm_num)
  have hb := bpar_size n
  calc (apar n).size ≤ (12 * D ^ 2 * bpar n + 1).size := Nat.size_le_size hle
    _ ≤ max (12 * D ^ 2 * bpar n).size (1 : ℕ).size + 1 := h3
    _ ≤ n.size + 30 := by omega

theorem kTpar_le (n : ℕ) : kTpar n ≤ n.size + 3 := by
  refine Nat.clog_le_of_le_pow ?_
  have hb : (4 * n + bpar n - 1) / bpar n ≤ 4 * n + 1 := by
    rcases Nat.eq_zero_or_pos (bpar n) with h | h
    · rw [h, Nat.div_zero]; omega
    · refine Nat.div_le_of_le_mul ?_
      have hsub : 4 * n + bpar n - 1 ≤ 4 * n + bpar n := Nat.sub_le _ _
      nlinarith [hsub, h]
  have h4 : 4 * n + 1 ≤ 2 ^ (n.size + 3) := by
    have h1 : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : 4 * 2 ^ n.size = 2 ^ (n.size + 2) := by rw [pow_add]; ring
    have h5 : 4 * n + 1 ≤ 4 * 2 ^ n.size := by nlinarith
    have h7 : 2 ^ (n.size + 2) ≤ 2 ^ (n.size + 3) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans h5 (le_trans (le_of_eq h2) h7)
  exact le_trans hb h4

theorem kr_div_le (n : ℕ) : (kTpar n + D - 1) / D ≤ kTpar n := by
  have hD : 1 ≤ D := by norm_num [D]
  have hD2 : 2 ≤ D := by norm_num [D]
  have h : kTpar n + D - 1 < (kTpar n + 1) * D := by
    rcases Nat.eq_zero_or_pos (kTpar n) with hk | hk
    · rw [hk]; simp only [Nat.zero_add]; omega
    · have h1 : kTpar n + D - 1 ≤ kTpar n + D := Nat.sub_le _ _
      nlinarith [h1, hk, hD2]
  have h2 : (kTpar n + D - 1) / D < kTpar n + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < D)]
    exact h
  omega

theorem Tpar_size (n : ℕ) : (Tpar n).size ≤ n.size + 4 := by
  have h : (Tpar n).size = kTpar n + 1 := by unfold Tpar; rw [Nat.size_pow]
  rw [h]
  have := kTpar_le n
  omega

theorem rpar_le_pow (n : ℕ) : rpar n ≤ 2 ^ (n.size + 3) := by
  unfold rpar
  exact Nat.pow_le_pow_right (by norm_num) (le_trans (kr_div_le n) (kTpar_le n))

theorem rpar_size (n : ℕ) : (rpar n).size ≤ n.size + 4 := by
  have h1 : (2 ^ (n.size + 3)).size ≤ n.size + 4 := by simp [Nat.size_pow]
  exact le_trans (Nat.size_le_size (rpar_le_pow n)) h1

/-! ## Consequences of `ParamOK` -/

theorem mem_getD {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  have h1 : l.getD i 0 = l[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  rw [h1]
  exact List.getElem_mem h

theorem prod_le_of_getD {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 ≤ l₂.getD i 0) : l₁.prod ≤ l₂.prod := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons x t ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y u =>
      have hlen' : t.length = u.length := by simpa using hlen
      have hxy : x ≤ y := by have := h 0 (by simp); simpa using this
      have htu : ∀ i, i < t.length → t.getD i 0 ≤ u.getD i 0 := by
        intro i hi
        have := h (i + 1) (by simpa using hi)
        simpa using this
      simp only [List.prod_cons]
      exact Nat.mul_le_mul hxy (ih hlen' htu)

theorem ts_ss_elem_le (n : ℕ) (ts ss : List ℕ) (h : HvdH.ParamOK n ts ss) :
    (∀ t ∈ ts, t ≤ 2 ^ (n.size + 3)) ∧ (∀ s ∈ ss, s ≤ 2 ^ (n.size + 3)) := by
  obtain ⟨htslen, hsslen, -, -, htpar, hwin, -, -⟩ := h
  have hts : ∀ t ∈ ts, t ≤ 2 ^ (n.size + 3) := by
    intro t ht
    rcases htpar t ht with h1 | h1
    · rw [h1]; exact rpar_le_pow n
    · have h2 : t ≤ rpar n := by omega
      exact le_trans h2 (rpar_le_pow n)
  refine ⟨hts, ?_⟩
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
  have hiD : i < D := by rw [← hsslen]; exact hi
  have hti : ts.getD i 0 ≤ 2 ^ (n.size + 3) :=
    hts (ts.getD i 0) (mem_getD (by rw [htslen]; exact hiD))
  have hle : (ss.getD i 0 : ℝ) ≤ (ts.getD i 0 : ℝ) := by
    have hw := (hwin i hiD).2
    refine le_trans hw ?_
    have h0 : (0 : ℝ) ≤ (ts.getD i 0 : ℝ) := by positivity
    have hc : (0 : ℝ) < 1 / (4 * (D : ℝ)) := by
      have hD : (0 : ℝ) < (D : ℝ) := by have hD' : D = 1729 := rfl; rw [hD']; norm_num
      positivity
    nlinarith
  have h2 : ss.getD i 0 ≤ ts.getD i 0 := by exact_mod_cast hle
  have h3 : ss[i] ≤ ts.getD i 0 := by
    have h4 : ss.getD i 0 = ss[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rw [h4] at h2
    exact h2
  exact le_trans h3 hti

theorem ss_prod_le_ts_prod (n : ℕ) (ts ss : List ℕ) (h : HvdH.ParamOK n ts ss) :
    ss.prod ≤ ts.prod := by
  obtain ⟨htslen, hsslen, -, -, -, hwin, -, -⟩ := h
  refine prod_le_of_getD (by rw [hsslen, htslen]) (fun i hi => ?_)
  have hiD : i < D := by rw [← hsslen]; exact hi
  have hle : (ss.getD i 0 : ℝ) ≤ (ts.getD i 0 : ℝ) := by
    have hw := (hwin i hiD).2
    refine le_trans hw ?_
    have h0 : (0 : ℝ) ≤ (ts.getD i 0 : ℝ) := by positivity
    have hc : (0 : ℝ) < 1 / (4 * (D : ℝ)) := by
      have hD : (0 : ℝ) < (D : ℝ) := by have hD' : D = 1729 := rfl; rw [hD']; norm_num
      positivity
    nlinarith
  exact_mod_cast hle

theorem ss_prod_size (n : ℕ) (ts ss : List ℕ) (h : HvdH.ParamOK n ts ss) :
    (ss.prod).size ≤ 1729 * (n.size + 4) := by
  have hsslen : ss.length = D := h.2.1
  have hb := (ts_ss_elem_le n ts ss h).2
  have h1 : ss.prod ≤ (2 ^ (n.size + 3)) ^ ss.length := List.prod_le_pow_length ss _ hb
  rw [hsslen] at h1
  have h3 : (2 ^ (n.size + 3)) ^ D = 2 ^ (D * (n.size + 3)) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [h3] at h1
  have h4 : (ss.prod).size ≤ D * (n.size + 3) + 1 := by
    have h5 : ((2 : ℕ) ^ (D * (n.size + 3))).size = D * (n.size + 3) + 1 := Nat.size_pow
    rw [← h5]
    exact Nat.size_le_size h1
  rw [show D = 1729 from rfl] at h4
  omega

theorem vsz_intList_le {l : List ℕ} {B : ℕ} (h : ∀ m ∈ l, m.size + 2 ≤ B) :
    vsz (intList l) ≤ (l.length + 1) * (B + 1) := by
  induction l with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons m t ih =>
    have hm : m.size + 2 ≤ B := h m (by simp)
    have ht : ∀ m' ∈ t, m'.size + 2 ≤ B := fun m' hm' => h m' (by simp [hm'])
    have hih := ih ht
    have hcons : vsz (intList (m :: t)) = (m.size + 2) + vsz (intList t) + 1 := by
      have e1 : intList (m :: t) = Val.cons (Val.int (m : ℤ)) (intList t) := rfl
      rw [e1, Work.Params.vsz_cons, vsz_int_nat]
    rw [hcons, List.length_cons]
    nlinarith

theorem vsz_intList_params (n : ℕ) (ts ss : List ℕ) (h : HvdH.ParamOK n ts ss) :
    vsz (intList ts) ≤ 115200 * (n.size + 1) ∧ vsz (intList ss) ≤ 115200 * (n.size + 1) := by
  have htslen : ts.length = D := h.1
  have hsslen : ss.length = D := h.2.1
  obtain ⟨hts, hss⟩ := ts_ss_elem_le n ts ss h
  have key : ∀ (l : List ℕ), l.length = D → (∀ m ∈ l, m ≤ 2 ^ (n.size + 3)) →
      vsz (intList l) ≤ 115200 * (n.size + 1) := by
    intro l hl hb
    have hsz : ∀ m ∈ l, m.size + 2 ≤ n.size + 6 := by
      intro m hm
      have h1 : m ≤ 2 ^ (n.size + 3) := hb m hm
      have h2 : m.size ≤ n.size + 4 := by
        refine Nat.size_le.mpr ?_
        calc m ≤ 2 ^ (n.size + 3) := h1
          _ < 2 ^ (n.size + 4) := by
              have h4 : 2 ^ (n.size + 4) = 2 ^ (n.size + 3) * 2 := by rw [pow_succ]
              rw [h4]
              have h5 : 1 ≤ 2 ^ (n.size + 3) := Nat.one_le_two_pow
              omega
      omega
    have h1 := vsz_intList_le hsz
    rw [hl] at h1
    calc vsz (intList l) ≤ (D + 1) * (n.size + 6 + 1) := h1
      _ ≤ 115200 * (n.size + 1) := by rw [show D = 1729 from rfl]; omega
  exact ⟨key ts htslen hts, key ss hsslen hss⟩

theorem paramOK_two_le (n : ℕ) (ts ss : List ℕ) (h : HvdH.ParamOK n ts ss) : 2 ≤ n := by
  by_contra hc
  push_neg at hc
  obtain ⟨htslen, hsslen, -, -, htpar, hwin, -, hodd⟩ := h
  have hb : bpar n = 0 := by
    rw [bpar]
    have h2 : Nat.clog 2 n ≤ 0 := by
      rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
      omega
    omega
  have hr : rpar n = 1 := by
    have h1 : kTpar n = 0 := by rw [kTpar, hb, Nat.div_zero, Nat.clog_zero_right]
    rw [rpar, h1, Nat.zero_add]
    rw [show D = 1729 from rfl]
    norm_num
  have ht1 : ∀ t ∈ ts, t = 1 := by
    intro t ht
    rcases htpar t ht with h1 | h1
    · rw [h1, hr]
    · rw [hr] at h1; omega
  have hDpos : 0 < D := by rw [show D = 1729 from rfl]; norm_num
  have hlen : 0 < ts.length := by rw [htslen]; exact hDpos
  have hts0 : ts.getD 0 0 = 1 := ht1 (ts.getD 0 0) (mem_getD hlen)
  have hlen2 : 0 < ss.length := by rw [hsslen]; exact hDpos
  have hwin0 := (hwin 0 hDpos).2
  have hlt : (ss.getD 0 0 : ℝ) < 1 := by
    rw [hts0] at hwin0
    push_cast at hwin0
    have hc : (0 : ℝ) < 1 / (4 * (D : ℝ)) := by
      have hD : (0 : ℝ) < (D : ℝ) := by have hD' : D = 1729 := rfl; rw [hD']; norm_num
      positivity
    nlinarith
  have hs0 : ss.getD 0 0 = 0 := Nat.cast_lt_one.mp hlt
  have hodd0 : Odd (ss.getD 0 0) := hodd (ss.getD 0 0) (mem_getD hlen2)
  rw [hs0] at hodd0
  obtain ⟨k, hk⟩ := hodd0
  omega

/-! ## The auxiliary words -/

/-- `[int x, int y] -> [int (max (size x) (size y)), int x, int y]`. -/
theorem sizeMaxWord (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (x y : ℕ) (R : List Val),
      WordR main prog
        (fun vs => vs = [Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
        (fun _ out => out = [Val.int ((max x.size y.size : ℕ) : ℤ),
          Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
        (fun _ => K * (x.size + y.size + 8)) := by
  obtain ⟨pDup, Kdup, hdup⟩ := hKer.dup
  obtain ⟨pPick, Kpick, hpick⟩ := hKer.pick
  obtain ⟨pSize, Ksize, hsize⟩ := hInt.size
  obtain ⟨pMax, Kmax, hmax⟩ := hInt.max
  let Ks : ℕ := 100 * (Kdup + Kpick + Ksize + Kmax + 1)
  have hKs : Ks = 100 * (Kdup + Kpick + Ksize + Kmax + 1) := rfl
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq pDup pSize) (pPick 2)) pSize) pMax, 10 * Ks, ?_⟩
  intro main x y R
  have hnx : vsz (Val.int (x : ℤ)) ≤ x.size + y.size + 8 := by rw [vsz_int_nat]; omega
  have hny : vsz (Val.int (y : ℤ)) ≤ x.size + y.size + 8 := by rw [vsz_int_nat]; omega
  have hnsx : vsz (Val.int (((x.size : ℕ)) : ℤ)) ≤ x.size + y.size + 8 := by
    rw [vsz_int_nat]
    have := size_le_self x.size
    omega
  have hnsy : vsz (Val.int (((y.size : ℕ)) : ℤ)) ≤ x.size + y.size + 8 := by
    rw [vsz_int_nat]
    have := size_le_self y.size
    omega
  have hix : isz (x : ℤ) ≤ x.size + y.size + 8 := by
    rw [HvdH.isz, Int.natAbs_natCast]
    have := size_le_self x.size
    omega
  have hiy : isz (y : ℤ) ≤ x.size + y.size + 8 := by
    rw [HvdH.isz, Int.natAbs_natCast]
    have := size_le_self y.size
    omega
  have hi1 : isz (1 : ℤ) ≤ x.size + y.size + 8 := by
    have h3 : isz (1 : ℤ) = 3 := by rw [HvdH.isz]; norm_num
    rw [h3]; omega
  have hisx : isz (((x.size : ℕ)) : ℤ) ≤ x.size + y.size + 8 := by
    rw [HvdH.isz, Int.natAbs_natCast]
    have := size_le_self x.size
    omega
  have hisy : isz (((y.size : ℕ)) : ℤ) ≤ x.size + y.size + 8 := by
    rw [HvdH.isz, Int.natAbs_natCast]
    have := size_le_self y.size
    omega
  have step1 : WordR main pDup
      (fun vs => vs = [Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (x : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => Ks * (x.size + y.size + 8)) := by
    refine Work.Params.dupStep (main := main) hKer (hdup main) (Val.int (x : ℤ))
      ([Val.int (y : ℤ)] ++ R) (Ks * (x.size + y.size + 8)) ?_
    have h1 : vsz (Val.int (x : ℤ)) + 1 ≤ 2 * (x.size + y.size + 8) := by omega
    calc Kdup * (vsz (Val.int (x : ℤ)) + 1) ≤ Kdup * (2 * (x.size + y.size + 8)) :=
          Nat.mul_le_mul_left _ h1
      _ = 2 * Kdup * (x.size + y.size + 8) := by ring
      _ ≤ Ks * (x.size + y.size + 8) := by
          have h2 : 2 * Kdup ≤ Ks := by rw [hKs]; nlinarith
          exact Nat.mul_le_mul_right _ h2
  have step2 : WordR main pSize
      (fun vs => vs = [Val.int (x : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => Ks * (x.size + y.size + 8)) := by
    have hc : Ksize * isz (x : ℤ) ≤ Ks * (x.size + y.size + 8) := by
      calc Ksize * isz (x : ℤ) ≤ Ksize * (x.size + y.size + 8) := Nat.mul_le_mul_left _ hix
        _ ≤ Ks * (x.size + y.size + 8) := Nat.mul_le_mul_right _ (by rw [hKs]; nlinarith)
    refine Work.Params.step_rw (main := main) hKer
      (Work.Params.unStep (main := main) hKer (hsize main) (x : ℤ)
        ([Val.int (x : ℤ), Val.int (y : ℤ)] ++ R) trivial (Ks * (x.size + y.size + 8)) hc) ?_
    simp [Int.natAbs_natCast]
  have step3 : WordR main (pPick 2)
      (fun vs => vs = [Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (y : ℤ), Val.int (((x.size : ℕ)) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => Ks * (x.size + y.size + 8)) := by
    refine Work.Params.pickStep (main := main) hKer (hpick main) 2
      ([Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (by simp) (Ks * (x.size + y.size + 8)) ?_
    have hs : (((([Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R).take 3).map vsz).sum + 1)
        ≤ 13 * (x.size + y.size + 8) := by
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
      omega
    calc Kpick * (2 + 1) *
          (((([Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R).take 3).map vsz).sum + 1)
        ≤ Kpick * 3 * (13 * (x.size + y.size + 8)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) hs
      _ = 39 * Kpick * (x.size + y.size + 8) := by ring
      _ ≤ Ks * (x.size + y.size + 8) := by
          have h2 : 39 * Kpick ≤ Ks := by rw [hKs]; nlinarith
          exact Nat.mul_le_mul_right _ h2
  have step4 : WordR main pSize
      (fun vs => vs = [Val.int (y : ℤ), Val.int (((x.size : ℕ)) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((y.size : ℕ)) : ℤ), Val.int (((x.size : ℕ)) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => Ks * (x.size + y.size + 8)) := by
    have hc : Ksize * isz (y : ℤ) ≤ Ks * (x.size + y.size + 8) := by
      calc Ksize * isz (y : ℤ) ≤ Ksize * (x.size + y.size + 8) := Nat.mul_le_mul_left _ hiy
        _ ≤ Ks * (x.size + y.size + 8) := Nat.mul_le_mul_right _ (by rw [hKs]; nlinarith)
    refine Work.Params.step_rw (main := main) hKer
      (Work.Params.unStep (main := main) hKer (hsize main) (y : ℤ)
        ([Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R) trivial
        (Ks * (x.size + y.size + 8)) hc) ?_
    simp [Int.natAbs_natCast]
  have step5 : WordR main pMax
      (fun vs => vs = [Val.int (((y.size : ℕ)) : ℤ), Val.int (((x.size : ℕ)) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int ((max x.size y.size : ℕ) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => Ks * (x.size + y.size + 8)) := by
    have hc : Kmax * (isz (((y.size : ℕ)) : ℤ) + isz (((x.size : ℕ)) : ℤ)) ≤
        Ks * (x.size + y.size + 8) := by
      have h2 : isz (((y.size : ℕ)) : ℤ) + isz (((x.size : ℕ)) : ℤ) ≤ 2 * (x.size + y.size + 8) := by
        omega
      calc Kmax * (isz (((y.size : ℕ)) : ℤ) + isz (((x.size : ℕ)) : ℤ))
          ≤ Kmax * (2 * (x.size + y.size + 8)) := Nat.mul_le_mul_left _ h2
        _ = 2 * Kmax * (x.size + y.size + 8) := by ring
        _ ≤ Ks * (x.size + y.size + 8) := by
            have h3 : 2 * Kmax ≤ Ks := by rw [hKs]; nlinarith
            exact Nat.mul_le_mul_right _ h3
    refine Work.Params.binStepP (main := main) hKer (hmax main) (((y.size : ℕ)) : ℤ)
      (((x.size : ℕ)) : ℤ) ([Val.int (x : ℤ), Val.int (y : ℤ)] ++ R) trivial
      (((max x.size y.size : ℕ)) : ℤ) ?_ (Ks * (x.size + y.size + 8)) hc
    have hc' : ((max x.size y.size : ℕ) : ℤ) = max ((x.size : ℕ) : ℤ) ((y.size : ℕ) : ℤ) :=
      Nat.cast_max _ _
    rw [hc']
    exact max_comm _ _
  have c2 : WordR main (Cmd.seq pDup pSize)
      (fun vs => vs = [Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((x.size : ℕ)) : ℤ), Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => 2 * (Ks * (x.size + y.size + 8))) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer step1 step2) ?_
    omega
  have c3 : WordR main (Cmd.seq (Cmd.seq pDup pSize) (pPick 2))
      (fun vs => vs = [Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (y : ℤ), Val.int (((x.size : ℕ)) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => 3 * (Ks * (x.size + y.size + 8))) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer c2 step3) ?_
    omega
  have c4 : WordR main (Cmd.seq (Cmd.seq (Cmd.seq pDup pSize) (pPick 2)) pSize)
      (fun vs => vs = [Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((y.size : ℕ)) : ℤ), Val.int (((x.size : ℕ)) : ℤ),
        Val.int (x : ℤ), Val.int (y : ℤ)] ++ R)
      (fun _ => 4 * (Ks * (x.size + y.size + 8))) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer c3 step4) ?_
    omega
  refine Work.Params.conseqC (main := main) hKer
    (Work.Params.seqC (main := main) hKer c4 step5) ?_
  have h1 : 4 * (Ks * (x.size + y.size + 8)) + Ks * (x.size + y.size + 8) = 5 * (Ks * (x.size + y.size + 8)) := by ring
  rw [h1]
  calc 5 * (Ks * (x.size + y.size + 8)) = (5 * Ks) * (x.size + y.size + 8) := by ring
    _ ≤ (10 * Ks) * (x.size + y.size + 8) := Nat.mul_le_mul_right _ (by omega)
    _ = 10 * Ks * (x.size + y.size + 8) := by ring

/-- `[int n, int b] -> [int (nchunks n b), int b]` for `1 ≤ b` and `b.size ≤ n.size`. -/
theorem nchunksWordAux (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (n b : ℕ) (R : List Val),
      1 ≤ b → b.size ≤ n.size →
      WordR main prog
        (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
        (fun _ out => out = [Val.int ((nchunks n b : ℕ) : ℤ), Val.int (b : ℤ)] ++ R)
        (fun _ => K * (n.size + b.size + 8) * (n.size + b.size + 8)) := by
  obtain ⟨pDup, Kdup, hdup⟩ := hKer.dup
  obtain ⟨pDrop, Kdrop, hdrop⟩ := hKer.drop
  obtain ⟨pSwap, Kswap, hswap⟩ := hKer.swap
  obtain ⟨pPick, Kpick, hpick⟩ := hKer.pick
  obtain ⟨pRoll, Kroll, hroll⟩ := hKer.roll
  obtain ⟨pPush, Kpush, hpush⟩ := hKer.pushVal
  obtain ⟨pAdd, Kadd, hadd⟩ := hInt.add
  obtain ⟨pSub, Ksub, hsub⟩ := hInt.sub
  obtain ⟨pFdiv, Kfdiv, hfdiv⟩ := hInt.fdiv
  let S : ℕ := 1000 * (Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + Kadd + Ksub + Kfdiv + 1)
  have hS : S = 1000 * (Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + Kadd + Ksub + Kfdiv + 1) := rfl
  let Q1 : Cmd := pDup
  let Q2 : Cmd := Cmd.seq Q1 (pPush (.int (1 : ℤ)))
  let Q3 : Cmd := Cmd.seq Q2 pSwap
  let Q4 : Cmd := Cmd.seq Q3 pSub
  let Q5 : Cmd := Cmd.seq Q4 (pPick 2)
  let Q6 : Cmd := Cmd.seq Q5 pDup
  let Q7 : Cmd := Cmd.seq Q6 (pRoll 2)
  let Q8 : Cmd := Cmd.seq Q7 pAdd
  let Q9 : Cmd := Cmd.seq Q8 pFdiv
  let Q10 : Cmd := Cmd.seq Q9 (pRoll 1)
  let Q11 : Cmd := Cmd.seq Q10 pDrop
  refine ⟨Q11, 20 * S, ?_⟩
  intro main n b R hb hbsz
  let U : ℕ := n.size + b.size + 8
  have hU : U = n.size + b.size + 8 := rfl
  have hU1 : 1 ≤ U := by omega
  have hnv : vsz (Val.int (n : ℤ)) ≤ U := by rw [vsz_int_nat, hU]; omega
  have hbv : vsz (Val.int (b : ℤ)) ≤ U := by rw [vsz_int_nat, hU]; omega
  have h1v : vsz (Val.int (1 : ℤ)) ≤ U := by
    have h3 : vsz (Val.int (1 : ℤ)) = 3 := by
      rw [Work.Main.vsz_int, HvdH.isz]
      norm_num
    rw [h3, hU]; omega
  have hnat1 : (((n : ℤ) - 1).natAbs) ≤ n + 1 := by
    have h2 := Int.natAbs_sub_le (n : ℤ) 1
    rw [Int.natAbs_natCast] at h2
    have h3 : ((1 : ℤ)).natAbs = 1 := by norm_num
    omega
  have hnat2 : ((((n : ℤ) - 1) + (b : ℤ)).natAbs) ≤ n + b + 1 := by
    have h2 := Int.natAbs_add_le ((n : ℤ) - 1) (b : ℤ)
    rw [Int.natAbs_natCast] at h2
    omega
  have hsubv : vsz (Val.int ((n : ℤ) - 1)) ≤ U := by
    rw [Work.Main.vsz_int, HvdH.isz]
    have h1 := Nat.size_le_size hnat1
    have h3 : (n + 1).size ≤ n.size + 1 := size_succ_le n
    omega
  have hn1 : isz ((n : ℤ) - 1) ≤ U := by
    rw [HvdH.isz]
    have h1 := Nat.size_le_size hnat1
    have h3 : (n + 1).size ≤ n.size + 1 := size_succ_le n
    omega
  have hiszn : isz (n : ℤ) ≤ U := by rw [HvdH.isz, Int.natAbs_natCast, hU]; omega
  have hiszb : isz (b : ℤ) ≤ U := by rw [HvdH.isz, Int.natAbs_natCast, hU]; omega
  have hisz1 : isz (1 : ℤ) ≤ U := by
    have h3 : isz (1 : ℤ) = 3 := by rw [HvdH.isz]; norm_num
    rw [h3, hU]; omega
  have hdiv : isz (((n : ℤ) - 1) + (b : ℤ)) * isz (b : ℤ) ≤ U * U := by
    have h1 : isz (((n : ℤ) - 1) + (b : ℤ)) ≤ U := by
      rw [HvdH.isz]
      have h2 := Nat.size_le_size hnat2
      have h3 : (n + b + 1).size ≤ max n.size b.size + 2 := by
        have h4 : (n + b + 1) = (n + b) + 1 := by omega
        rw [h4]
        have h5 : (n + b).size ≤ max n.size b.size + 1 := size_add_le n b
        have h6 := size_succ_le (n + b)
        omega
      omega
    exact Nat.mul_le_mul h1 hiszb
  have hqv : vsz (Val.int ((nchunks n b : ℕ) : ℤ)) ≤ U := by
    rw [vsz_int_nat]
    have h1 := nchunks_size_le n b
    rw [hU]
    omega
  have step1 : WordR main pDup
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (n : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.dupStep (main := main) hKer (hdup main) (Val.int (n : ℤ))
      ([Val.int (b : ℤ)] ++ R) (S * U * U) ?_
    have h1 : vsz (Val.int (n : ℤ)) + 1 ≤ 2 * U := by omega
    calc Kdup * (vsz (Val.int (n : ℤ)) + 1) ≤ Kdup * (2 * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * Kdup * U := by ring
      _ ≤ 2 * Kdup * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 2 * Kdup * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 2 * Kdup ≤ S := by rw [hS]; nlinarith
          calc 2 * Kdup * U * U = (2 * Kdup) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step2 : WordR main (pPush (.int (1 : ℤ)))
      (fun vs => vs = [Val.int (n : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (1 : ℤ), Val.int (n : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.pushValStep (main := main) hKer (hpush main) (.int (1 : ℤ))
      ([Val.int (n : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) (S * U * U) ?_
    have h1 : vsz (Val.int (1 : ℤ)) + 1 ≤ 2 * U := by omega
    calc Kpush * (vsz (Val.int (1 : ℤ)) + 1) ≤ Kpush * (2 * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * Kpush * U := by ring
      _ ≤ 2 * Kpush * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 2 * Kpush * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 2 * Kpush ≤ S := by rw [hS]; nlinarith
          calc 2 * Kpush * U * U = (2 * Kpush) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step3 : WordR main pSwap
      (fun vs => vs = [Val.int (1 : ℤ), Val.int (n : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (n : ℤ), Val.int (1 : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.swapStep (main := main) hKer (hswap main) (Val.int (1 : ℤ))
      (Val.int (n : ℤ)) ([Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) (S * U * U) ?_
    have h1 : vsz (Val.int (1 : ℤ)) + vsz (Val.int (n : ℤ)) + 1 ≤ 3 * U := by omega
    calc Kswap * (vsz (Val.int (1 : ℤ)) + vsz (Val.int (n : ℤ)) + 1) ≤ Kswap * (3 * U) :=
          Nat.mul_le_mul_left _ h1
      _ = 3 * Kswap * U := by ring
      _ ≤ 3 * Kswap * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 3 * Kswap * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 3 * Kswap ≤ S := by rw [hS]; nlinarith
          calc 3 * Kswap * U * U = (3 * Kswap) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step4 : WordR main pSub
      (fun vs => vs = [Val.int (n : ℤ), Val.int (1 : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.binStep (main := main) hKer (hsub main) (n : ℤ) (1 : ℤ)
      ([Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) trivial (S * U * U) ?_
    have h1 : isz (n : ℤ) + isz (1 : ℤ) ≤ 2 * U := by omega
    calc Ksub * (isz (n : ℤ) + isz (1 : ℤ)) ≤ Ksub * (2 * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * Ksub * U := by ring
      _ ≤ 2 * Ksub * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 2 * Ksub * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 2 * Ksub ≤ S := by rw [hS]; nlinarith
          calc 2 * Ksub * U * U = (2 * Ksub) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step5 : WordR main (pPick 2)
      (fun vs => vs = [Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (b : ℤ), Val.int ((n : ℤ) - 1), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.pickStep (main := main) hKer (hpick main) 2
      ([Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) (by simp) (S * U * U) ?_
    have hs : (((([Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R).take 3).map vsz).sum + 1)
        ≤ 13 * U := by
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
      omega
    calc Kpick * (2 + 1) *
          (((([Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R).take 3).map vsz).sum + 1)
        ≤ Kpick * 3 * (13 * U) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) hs
      _ = 39 * Kpick * U := by ring
      _ ≤ 39 * Kpick * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 39 * Kpick * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 39 * Kpick ≤ S := by rw [hS]; nlinarith
          calc 39 * Kpick * U * U = (39 * Kpick) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step6 : WordR main pDup
      (fun vs => vs = [Val.int (b : ℤ), Val.int ((n : ℤ) - 1), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (b : ℤ), Val.int (b : ℤ), Val.int ((n : ℤ) - 1),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.dupStep (main := main) hKer (hdup main) (Val.int (b : ℤ))
      ([Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) (S * U * U) ?_
    have h1 : vsz (Val.int (b : ℤ)) + 1 ≤ 2 * U := by omega
    calc Kdup * (vsz (Val.int (b : ℤ)) + 1) ≤ Kdup * (2 * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * Kdup * U := by ring
      _ ≤ 2 * Kdup * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 2 * Kdup * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 2 * Kdup ≤ S := by rw [hS]; nlinarith
          calc 2 * Kdup * U * U = (2 * Kdup) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step7 : WordR main (pRoll 2)
      (fun vs => vs = [Val.int (b : ℤ), Val.int (b : ℤ), Val.int ((n : ℤ) - 1),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int ((n : ℤ) - 1), Val.int (b : ℤ), Val.int (b : ℤ),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.rollStep (main := main) hKer (hroll main) 2
      ([Val.int (b : ℤ), Val.int (b : ℤ), Val.int ((n : ℤ) - 1), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R) (by simp) (S * U * U) ?_
    have hs : (((([Val.int (b : ℤ), Val.int (b : ℤ), Val.int ((n : ℤ) - 1), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R).take 3).map vsz).sum + 1) ≤ 13 * U := by
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
      omega
    calc Kroll * (2 + 1) *
          (((([Val.int (b : ℤ), Val.int (b : ℤ), Val.int ((n : ℤ) - 1), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R).take 3).map vsz).sum + 1)
        ≤ Kroll * 3 * (13 * U) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) hs
      _ = 39 * Kroll * U := by ring
      _ ≤ 39 * Kroll * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 39 * Kroll * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 39 * Kroll ≤ S := by rw [hS]; nlinarith
          calc 39 * Kroll * U * U = (39 * Kroll) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step8 : WordR main pAdd
      (fun vs => vs = [Val.int ((n : ℤ) - 1), Val.int (b : ℤ), Val.int (b : ℤ),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((n : ℤ) - 1) + (b : ℤ)), Val.int (b : ℤ),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.binStep (main := main) hKer (hadd main) ((n : ℤ) - 1) (b : ℤ)
      ([Val.int (b : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) trivial (S * U * U) ?_
    have h1 : isz ((n : ℤ) - 1) + isz (b : ℤ) ≤ 2 * U := by omega
    calc Kadd * (isz ((n : ℤ) - 1) + isz (b : ℤ)) ≤ Kadd * (2 * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * Kadd * U := by ring
      _ ≤ 2 * Kadd * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 2 * Kadd * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 2 * Kadd ≤ S := by rw [hS]; nlinarith
          calc 2 * Kadd * U * U = (2 * Kadd) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have hcast : ((n : ℤ) - 1) + (b : ℤ) = (((n + b - 1 : ℕ)) : ℤ) := by
    have h1 : 1 ≤ n + b := by omega
    rw [Int.natCast_sub h1, Nat.cast_add, Nat.cast_one]
    ring
  have hq : Int.fdiv (((n : ℤ) - 1) + (b : ℤ)) (b : ℤ) = (((nchunks n b : ℕ)) : ℤ) := by
    rw [hcast, ← Int.ofNat_fdiv]
    rfl
  have step9 : WordR main pFdiv
      (fun vs => vs = [Val.int (((n : ℤ) - 1) + (b : ℤ)), Val.int (b : ℤ),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.step_rw (main := main) hKer
      (Work.Params.binStepP (main := main) hKer (hfdiv main) (((n : ℤ) - 1) + (b : ℤ)) (b : ℤ)
        ([Val.int (n : ℤ), Val.int (b : ℤ)] ++ R) (by exact_mod_cast hb) (((nchunks n b : ℕ)) : ℤ)
        hq (S * U * U) ?_) ?_
    · have hbase : Kfdiv * isz (((n : ℤ) - 1) + (b : ℤ)) * isz (b : ℤ) ≤ Kfdiv * (U * U) := by
        have e : Kfdiv * isz (((n : ℤ) - 1) + (b : ℤ)) * isz (b : ℤ)
            = Kfdiv * (isz (((n : ℤ) - 1) + (b : ℤ)) * isz (b : ℤ)) := by ring
        rw [e]
        exact Nat.mul_le_mul_left _ hdiv
      have h2 : Kfdiv ≤ S := by rw [hS]; nlinarith
      calc Kfdiv * isz (((n : ℤ) - 1) + (b : ℤ)) * isz (b : ℤ) ≤ Kfdiv * (U * U) := hbase
        _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
        _ = S * U * U := by ring
    · rfl
  have step10 : WordR main (pRoll 1)
      (fun vs => vs = [Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (n : ℤ), Val.int (((nchunks n b : ℕ)) : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.rollStep (main := main) hKer (hroll main) 1
      ([Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (by simp) (S * U * U) ?_
    have hs : (((([Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R).take 2).map vsz).sum + 1)
        ≤ 13 * U := by
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
      omega
    calc Kroll * (1 + 1) *
          (((([Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R).take 2).map vsz).sum + 1)
        ≤ Kroll * 2 * (13 * U) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) hs
      _ = 26 * Kroll * U := by ring
      _ ≤ 26 * Kroll * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 26 * Kroll * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 26 * Kroll ≤ S := by rw [hS]; nlinarith
          calc 26 * Kroll * U * U = (26 * Kroll) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have step11 : WordR main pDrop
      (fun vs => vs = [Val.int (n : ℤ), Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => S * U * U) := by
    refine Work.Params.dropStep (main := main) hKer (hdrop main) (Val.int (n : ℤ))
      ([Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (b : ℤ)] ++ R) (S * U * U) ?_
    have h1 : vsz (Val.int (n : ℤ)) + 1 ≤ 2 * U := by omega
    calc Kdrop * (vsz (Val.int (n : ℤ)) + 1) ≤ Kdrop * (2 * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * Kdrop * U := by ring
      _ ≤ 2 * Kdrop * (U * U) := by
          have h2 : U ≤ U * U := by nlinarith [hU1]
          exact Nat.mul_le_mul_left _ h2
      _ = 2 * Kdrop * U * U := by ring
      _ ≤ S * U * U := by
          have h2 : 2 * Kdrop ≤ S := by rw [hS]; nlinarith
          calc 2 * Kdrop * U * U = (2 * Kdrop) * (U * U) := by ring
            _ ≤ S * (U * U) := Nat.mul_le_mul_right _ h2
            _ = S * U * U := by ring
  have acc2 : WordR main Q2
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (1 : ℤ), Val.int (n : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => 2 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer step1 step2) ?_
    omega
  have acc3 : WordR main Q3
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (n : ℤ), Val.int (1 : ℤ), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => 3 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc2 step3) ?_
    omega
  have acc4 : WordR main Q4
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int ((n : ℤ) - 1), Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => 4 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc3 step4) ?_
    omega
  have acc5 : WordR main Q5
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (b : ℤ), Val.int ((n : ℤ) - 1), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ => 5 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc4 step5) ?_
    omega
  have acc6 : WordR main Q6
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (b : ℤ), Val.int (b : ℤ), Val.int ((n : ℤ) - 1),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => 6 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc5 step6) ?_
    omega
  have acc7 : WordR main Q7
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int ((n : ℤ) - 1), Val.int (b : ℤ), Val.int (b : ℤ),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => 7 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc6 step7) ?_
    omega
  have acc8 : WordR main Q8
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((n : ℤ) - 1) + (b : ℤ)), Val.int (b : ℤ),
        Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ => 8 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc7 step8) ?_
    omega
  have acc9 : WordR main Q9
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (((nchunks n b : ℕ)) : ℤ), Val.int (n : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ => 9 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc8 step9) ?_
    omega
  have acc10 : WordR main Q10
      (fun vs => vs = [Val.int (n : ℤ), Val.int (b : ℤ)] ++ R)
      (fun _ out => out = [Val.int (n : ℤ), Val.int (((nchunks n b : ℕ)) : ℤ),
        Val.int (b : ℤ)] ++ R)
      (fun _ => 10 * (S * U * U)) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer acc9 step10) ?_
    omega
  refine Work.Params.conseqC (main := main) hKer
    (Work.Params.seqC (main := main) hKer acc10 step11) ?_
  have h2 : 20 * S * (n.size + b.size + 8) * (n.size + b.size + 8) = 20 * S * (U * U) := by
    rw [hU]; ring
  have h1 : 10 * (S * U * U) + S * U * U = 11 * S * (U * U) := by ring
  rw [h2, h1]
  exact Nat.mul_le_mul_right _ (by omega)

theorem setup (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hLay : HvdH.LayoutLib)
    (progPar : HvdH.Cmd) (KPar nPar : ℕ)
    (hPar : ∀ (main : HvdH.Cmd) (n : ℕ), nPar ≤ n →
      HvdH.WordR main progPar (fun vs => ∃ rest, vs = HvdH.Val.int n :: rest)
        (fun vs out => ∃ rest ts ss, vs = HvdH.Val.int n :: rest ∧ HvdH.ParamOK n ts ss ∧
          out = HvdH.Val.int (HvdH.bpar n) :: HvdH.Val.int (HvdH.ppar n) :: HvdH.Val.int (HvdH.apar n) ::
            HvdH.Val.int (HvdH.Tpar n) :: HvdH.Val.int (HvdH.rpar n) :: HvdH.intList ts :: HvdH.intList ss :: rest)
        (fun _ => KPar * (n.size + 1) ^ KPar)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (R : List HvdH.Val) (x y : ℕ),
      nPar ≤ max x.size y.size →
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int x, HvdH.Val.int y] ++ R)
        (fun vs out => vs = [HvdH.Val.int x, HvdH.Val.int y] ++ R ∧
          ∃ (sp : SP), out = env sp R ∧ sp.x = x ∧ sp.y = y ∧
            sp.b = HvdH.bpar (max x.size y.size) ∧ sp.p = HvdH.ppar (max x.size y.size) ∧
            sp.α = HvdH.apar (max x.size y.size) ∧ sp.S = sp.ss.prod ∧
            sp.ts.prod = HvdH.Tpar (max x.size y.size) ∧
            sp.ss.length = HvdH.D ∧ sp.ts.length = HvdH.D ∧
            HvdH.ParamOK (max x.size y.size) sp.ts sp.ss ∧
            sp.N' = nchunks (max x.size y.size) (HvdH.bpar (max x.size y.size)))
        (fun _ => KPar * ((max x.size y.size).size + 1) ^ KPar * K + K * (x.size + y.size + 1)) := by
  obtain ⟨pDup, Kdup, hdup⟩ := hKer.dup
  obtain ⟨pDrop, Kdrop, hdrop⟩ := hKer.drop
  obtain ⟨pRoll, Kroll, hroll⟩ := hKer.roll
  obtain ⟨pPick, Kpick, hpick⟩ := hKer.pick
  obtain ⟨pLP, KLP, hLP⟩ := Work.ConvR.listProdB hKer hInt hLay
  obtain ⟨pSM, KSM, hSM⟩ := sizeMaxWord hKer hInt
  obtain ⟨pNC, KNC, hNC⟩ := nchunksWordAux hKer hInt
  let S : ℕ := Kdup + Kdrop + Kroll + Kpick + KLP + KNC + KSM + 100
  have hSdef : S = Kdup + Kdrop + Kroll + Kpick + KLP + KNC + KSM + 100 := rfl
  let Cg : ℕ := 115300
  have hCgdef : Cg = 115300 := rfl
  let KB : ℕ := (S + 1) * (Cg + 1) * 2 ^ 20
  have hKBdef : KB = (S + 1) * (Cg + 1) * 2 ^ 20 := rfl
  let T1 : Cmd := pRoll 6
  let T2 : Cmd := Cmd.seq T1 pDup
  let T3 : Cmd := Cmd.seq T2 pLP
  let T4 : Cmd := Cmd.seq T3 (pPick 2)
  let T5 : Cmd := Cmd.seq T4 (pPick 9)
  let T6 : Cmd := Cmd.seq T5 pNC
  let T7 : Cmd := Cmd.seq T6 (pRoll 4)
  let T8 : Cmd := Cmd.seq T7 pDrop
  let T9 : Cmd := Cmd.seq T8 (pRoll 6)
  let T10 : Cmd := Cmd.seq T9 pDrop
  let T11 : Cmd := Cmd.seq T10 (pRoll 6)
  let T12 : Cmd := Cmd.seq T11 pDrop
  let T13 : Cmd := Cmd.seq T12 (pRoll 7)
  let T14 : Cmd := Cmd.seq T13 pDrop
  let T15 : Cmd := Cmd.seq T14 (pRoll 3)
  let T16 : Cmd := Cmd.seq T15 (pRoll 6)
  let T17 : Cmd := Cmd.seq T16 (pRoll 6)
  let T18 : Cmd := Cmd.seq T17 (pRoll 6)
  let T19 : Cmd := Cmd.seq T18 (pRoll 5)
  let T20 : Cmd := Cmd.seq T19 (pRoll 5)
  let T21 : Cmd := Cmd.seq T20 (pRoll 6)
  let P1 : Cmd := pSM
  let P2 : Cmd := Cmd.seq P1 pDup
  let P3 : Cmd := Cmd.seq P2 progPar
  let PROG : Cmd := Cmd.seq P3 T21
  refine ⟨PROG, 32 * (KB * KB) + 1, ?_⟩
  intro main R x y hle
  let n : ℕ := max x.size y.size
  have hn : n = max x.size y.size := rfl
  let B : ℕ := n + 1
  have hBdef : B = n + 1 := rfl
  let CB : ℕ := KB * KB * B
  have hCBdef : CB = KB * KB * B := rfl
  let vb : Val := Val.int ((HvdH.bpar n : ℕ) : ℤ)
  let vp : Val := Val.int ((HvdH.ppar n : ℕ) : ℤ)
  let va : Val := Val.int ((HvdH.apar n : ℕ) : ℤ)
  let vT : Val := Val.int ((HvdH.Tpar n : ℕ) : ℤ)
  let vr : Val := Val.int ((HvdH.rpar n : ℕ) : ℤ)
  let vn : Val := Val.int ((n : ℕ) : ℤ)
  let vx : Val := Val.int ((x : ℕ) : ℤ)
  let vy : Val := Val.int ((y : ℕ) : ℤ)
  let vQ : Val := Val.int ((nchunks n (HvdH.bpar n) : ℕ) : ℤ)
  have hxn : x.size ≤ n := by rw [hn]; exact le_max_left _ _
  have hyn : y.size ≤ n := by rw [hn]; exact le_max_right _ _
  have hCg2 : 2 ≤ Cg := by rw [hCgdef]; norm_num
  have hCg115200 : 115200 ≤ Cg := by rw [hCgdef]; norm_num
  have hKB169 : 169 * Cg ≤ KB := by rw [hKBdef]; nlinarith
  have hKB4 : 4 * Cg ≤ KB := by rw [hKBdef]; nlinarith
  have hKB6 : 6 ≤ KB := by rw [hKBdef]; nlinarith
  have hKB2 : 2 ≤ KB := by rw [hKBdef]; nlinarith
  have hKB16 : 16 ≤ KB := by rw [hKBdef]; nlinarith
  have hKB384 : 384 ≤ KB := by rw [hKBdef]; nlinarith
  have hKB1 : 1 ≤ KB := by omega
  have hKLPKB : KLP ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKNCKB : KNC ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKSMKB : KSM ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKdupKB : Kdup ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKdropKB : Kdrop ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKrollKB : Kroll ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKpickKB : Kpick ≤ KB := by rw [hKBdef, hSdef]; nlinarith
  have hKLP2 : 115201 ^ 2 * 6 ≤ KB := by rw [hKBdef]; nlinarith
  have hB1 : 1 ≤ B := by rw [hBdef]; omega
  have hCgB : 1 ≤ Cg * B := by nlinarith [hCg2, hB1]
  have hnsz : n.size ≤ n := size_le_self n
  have hvx : vsz vx ≤ Cg * B := by
      show vsz (Val.int ((x : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      nlinarith [hxn, hCg2]
  have hvy : vsz vy ≤ Cg * B := by
      show vsz (Val.int ((y : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      nlinarith [hyn, hCg2]
  have hvn : vsz vn ≤ Cg * B := by
      show vsz (Val.int ((n : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      nlinarith [hnsz, hCg2]
  have hvb : vsz vb ≤ Cg * B := by
      show vsz (Val.int ((HvdH.bpar n : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := bpar_size n
      nlinarith [hnsz, hCg2]
  have hvp : vsz vp ≤ Cg * B := by
      show vsz (Val.int ((HvdH.ppar n : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := ppar_size n
      nlinarith [hnsz, hCg2]
  have hva : vsz va ≤ Cg * B := by
      show vsz (Val.int ((HvdH.apar n : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := apar_size n
      nlinarith [hnsz, hCg2]
  have hvT : vsz vT ≤ Cg * B := by
      show vsz (Val.int ((HvdH.Tpar n : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := Tpar_size n
      nlinarith [hnsz, hCg2]
  have hvr : vsz vr ≤ Cg * B := by
      show vsz (Val.int ((HvdH.rpar n : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := rpar_size n
      nlinarith [hnsz, hCg2]
  have hvQ : vsz vQ ≤ Cg * B := by
      show vsz (Val.int ((nchunks n (HvdH.bpar n) : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := nchunks_size_le n (HvdH.bpar n)
      nlinarith [hnsz, hCg2]
  have htail : ∀ (ts ss : List ℕ), HvdH.ParamOK n ts ss →
      WordR main T21 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R))
        (fun _ out => out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R))
        (fun _ => 21 * CB) := by
    intro ts ss hok
    have hvt : vsz (HvdH.intList ts) ≤ Cg * B := by
      have h1 := (vsz_intList_params n ts ss hok).1
      have h2 : 115200 * (n.size + 1) ≤ Cg * B := by
        rw [hBdef]
        nlinarith [hnsz, hCg115200]
      exact le_trans h1 h2
    have hvss : vsz (HvdH.intList ss) ≤ Cg * B := by
      have h1 := (vsz_intList_params n ts ss hok).2
      have h2 : 115200 * (n.size + 1) ≤ Cg * B := by
        rw [hBdef]
        nlinarith [hnsz, hCg115200]
      exact le_trans h1 h2
    have hvS : vsz (Val.int ((ss.prod : ℕ) : ℤ)) ≤ Cg * B := by
      show vsz (Val.int ((ss.prod : ℕ) : ℤ)) ≤ Cg * B
      rw [vsz_int_nat, hBdef]
      have h1 := ss_prod_size n ts ss hok
      nlinarith [hnsz, hCg2]
    have s1 : WordR main (pRoll 6) (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s2 : WordR main pDup (fun vs => vs = ([(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ss),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      refine Work.Params.dupStep (main := main) hKer (hdup main) (HvdH.intList ss) ([vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) CB ?_
      have h1 : vsz (HvdH.intList ss) + 1 ≤ 4 * (Cg * B) := by have := hvss; omega
      exact cost_basic hKdupKB h1 hKB4
    have s3 : WordR main pLP (fun vs => vs = ([(HvdH.intList ss),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      refine hKer.conseq main pLP (fun vs => vs = HvdH.intList ss :: ([(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R))
          (fun vs => vs = ([(HvdH.intList ss),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = Val.int ((ss.prod : ℕ) : ℤ) :: ([(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R))
          (fun _ out => out = ([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun vs => KLP * (vsz (vs.headD Val.nil) + 1) ^ 2)
          (fun _ => CB) (hLP main ss ([(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun vs h => h) (fun vs out _ hq => by rw [hq]; rfl) ?_
      intro vs hv
      rw [hv]
      simp only [List.cons_append, List.nil_append, List.headD_cons]
      have h1 : vsz (HvdH.intList ss) + 1 ≤ 115201 * (n.size + 1) := by
        have h2 := (vsz_intList_params n ts ss hok).2
        have h3 : 1 ≤ n.size + 1 := by omega
        omega
      have h2 : (n.size + 1) ^ 2 ≤ 6 * B := by rw [hBdef]; exact size_sq_le n
      exact cost_lp (K0 := KLP) (V := vsz (HvdH.intList ss)) (K2 := 6) (S := n.size + 1)
        (KB := KB) (B := B) hKLPKB h1 h2 hKLP2
    have s4 : WordR main (pPick 2) (fun vs => vs = ([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (2 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.pickStep (main := main) hKer (hpick main) 2 ([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) (by simp) CB
        (cost_pick (K0 := Kpick) (k := 2) (s := (((([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (2 + 1)).map vsz).sum)
          (Cg := Cg) (KB := KB) (B := B) hKpickKB (by norm_num) hs hKB169)
    have s5 : WordR main (pPick 9) (fun vs => vs = ([vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vn,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (9 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.pickStep (main := main) hKer (hpick main) 9 ([vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) (by simp) CB
        (cost_pick (K0 := Kpick) (k := 9) (s := (((([vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (9 + 1)).map vsz).sum)
          (Cg := Cg) (KB := KB) (B := B) hKpickKB (by norm_num) hs hKB169)
    have s6 : WordR main pNC (fun vs => vs = ([vn,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (hNC main n (HvdH.bpar n) ([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) ?_ ?_) ?_
      · have h2 := (paramOK_two_le n ts ss hok)
        have h3 : 0 < HvdH.bpar n := Nat.clog_pos (by norm_num) (by omega)
        omega
      · exact bpar_size_le n
      · have h1 : (n.size + (HvdH.bpar n).size + 8) * (n.size + (HvdH.bpar n).size + 8) ≤ 384 * B := by
          have hb := bpar_size_le n
          have h3 : (n.size + 1) ^ 2 ≤ 6 * B := by rw [hBdef]; exact size_sq_le n
          nlinarith
        exact cost_nc (K0 := KNC) (a := n.size + (HvdH.bpar n).size + 8)
          (b := n.size + (HvdH.bpar n).size + 8) (C := 384) (KB := KB) (B := B)
          hKNCKB h1 hKB384
    have s7 : WordR main (pRoll 4) (fun vs => vs = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vb,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (4 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 4 ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 4) (s := (((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (4 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s8 : WordR main pDrop (fun vs => vs = ([vb,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      refine Work.Params.dropStep (main := main) hKer (hdrop main) vb ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) CB ?_
      have h1 : vsz vb + 1 ≤ 4 * (Cg * B) := by have := hvb; omega
      exact cost_basic hKdropKB h1 hKB4
    have s9 : WordR main (pRoll 6) (fun vs => vs = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vT,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s10 : WordR main pDrop (fun vs => vs = ([vT,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      refine Work.Params.dropStep (main := main) hKer (hdrop main) vT ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R) CB ?_
      have h1 : vsz vT + 1 ≤ 4 * (Cg * B) := by have := hvT; omega
      exact cost_basic hKdropKB h1 hKB4
    have s11 : WordR main (pRoll 6) (fun vs => vs = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vr,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s12 : WordR main pDrop (fun vs => vs = ([vr,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => CB) := by
      refine Work.Params.dropStep (main := main) hKer (hdrop main) vr ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R) CB ?_
      have h1 : vsz vr + 1 ≤ 4 * (Cg * B) := by have := hvr; omega
      exact cost_basic hKdropKB h1 hKB4
    have s13 : WordR main (pRoll 7) (fun vs => vs = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ out => out = ([vn,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)).take (7 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 7 ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 7) (s := (((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)).take (7 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s14 : WordR main pDrop (fun vs => vs = ([vn,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ => CB) := by
      refine Work.Params.dropStep (main := main) hKer (hdrop main) vn ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R) CB ?_
      have h1 : vsz vn + 1 ≤ 4 * (Cg * B) := by have := hvn; omega
      exact cost_basic hKdropKB h1 hKB4
    have s15 : WordR main (pRoll 3) (fun vs => vs = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)).take (3 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 3 ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 3) (s := (((([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)).take (3 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s16 : WordR main (pRoll 6) (fun vs => vs = ([(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,(HvdH.intList ts),vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,(HvdH.intList ts),vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,(HvdH.intList ts),vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s17 : WordR main (pRoll 6) (fun vs => vs = ([(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,vx,vy] ++ R)) (fun _ out => out = ([va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s18 : WordR main (pRoll 6) (fun vs => vs = ([va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,vx,vy] ++ R)) (fun _ out => out = ([vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s19 : WordR main (pRoll 5) (fun vs => vs = ([vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ out => out = ([vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)).take (5 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 5 ([vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 5) (s := (((([vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)).take (5 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s20 : WordR main (pRoll 5) (fun vs => vs = ([vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)).take (5 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 5 ([vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 5) (s := (((([vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)).take (5 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have s21 : WordR main (pRoll 6) (fun vs => vs = ([vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ out => out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R)) (fun _ => CB) := by
      have hs : ((((([vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)).take (6 + 1)).map vsz).sum + 1) ≤ 13 * (Cg * B) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.cons_append, List.nil_append]
        omega
      exact Work.Params.step_rw (main := main) hKer
        (Work.Params.rollStep (main := main) hKer (hroll main) 6 ([vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R) (by simp) CB
          (cost_pick (K0 := Kroll) (k := 6) (s := (((([vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)).take (6 + 1)).map vsz).sum)
            (Cg := Cg) (KB := KB) (B := B) hKrollKB (by norm_num) hs hKB169)) (by simp)
    have c1 : WordR main T1 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 1 * CB) := by
      exact Work.Params.conseqC (main := main) hKer s1 (Nat.le_of_eq (by ring))
    have c2 : WordR main T2 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ss),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 2 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c1 s2) ?_
      exact Nat.le_of_eq (by ring)
    have c3 : WordR main T3 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 3 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c2 s3) ?_
      exact Nat.le_of_eq (by ring)
    have c4 : WordR main T4 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 4 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c3 s4) ?_
      exact Nat.le_of_eq (by ring)
    have c5 : WordR main T5 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vn,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 5 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c4 s5) ?_
      exact Nat.le_of_eq (by ring)
    have c6 : WordR main T6 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vb,vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 6 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c5 s6) ?_
      exact Nat.le_of_eq (by ring)
    have c7 : WordR main T7 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vb,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 7 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c6 s7) ?_
      exact Nat.le_of_eq (by ring)
    have c8 : WordR main T8 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vT,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 8 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c7 s8) ?_
      exact Nat.le_of_eq (by ring)
    have c9 : WordR main T9 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vT,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 9 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c8 s9) ?_
      exact Nat.le_of_eq (by ring)
    have c10 : WordR main T10 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,vr,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 10 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c9 s10) ?_
      exact Nat.le_of_eq (by ring)
    have c11 : WordR main T11 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vr,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 11 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c10 s11) ?_
      exact Nat.le_of_eq (by ring)
    have c12 : WordR main T12 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vn,vx,vy] ++ R)) (fun _ => 12 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c11 s12) ?_
      exact Nat.le_of_eq (by ring)
    have c13 : WordR main T13 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vn,vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ => 13 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c12 s13) ?_
      exact Nat.le_of_eq (by ring)
    have c14 : WordR main T14 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),(HvdH.intList ss),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ => 14 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c13 s14) ?_
      exact Nat.le_of_eq (by ring)
    have c15 : WordR main T15 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,(HvdH.intList ts),vx,vy] ++ R)) (fun _ => 15 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c14 s15) ?_
      exact Nat.le_of_eq (by ring)
    have c16 : WordR main T16 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,va,vx,vy] ++ R)) (fun _ => 16 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c15 s16) ?_
      exact Nat.le_of_eq (by ring)
    have c17 : WordR main T17 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vp,vx,vy] ++ R)) (fun _ => 17 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c16 s17) ?_
      exact Nat.le_of_eq (by ring)
    have c18 : WordR main T18 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,vb,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ => 18 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c17 s18) ?_
      exact Nat.le_of_eq (by ring)
    have c19 : WordR main T19 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vQ,(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ => 19 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c18 s19) ?_
      exact Nat.le_of_eq (by ring)
    have c20 : WordR main T20 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),(Val.int ((ss.prod : ℕ) : ℤ)),vx,vy] ++ R)) (fun _ => 20 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c19 s20) ?_
      exact Nat.le_of_eq (by ring)
    have c21 : WordR main T21 (fun vs => vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R)) (fun _ out => out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R)) (fun _ => 21 * CB) := by
      refine Work.Params.conseqC (main := main) hKer
        (Work.Params.seqC (main := main) hKer c20 s21) ?_
      exact Nat.le_of_eq (by ring)
    exact c21
  have htailE : WordR main T21
      (fun vs => ∃ ts ss, HvdH.ParamOK n ts ss ∧ vs = ([vb,vp,va,vT,vr,(HvdH.intList ts),(HvdH.intList ss),vn,vx,vy] ++ R))
      (fun _ out => ∃ ts ss, HvdH.ParamOK n ts ss ∧ out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R))
      (fun _ => 21 * CB) := by
    intro vs hpre s' Rs hs
    obtain ⟨ts, ss, hok, hvs⟩ := hpre
    obtain ⟨out, s'', m, hpost, hev, hle, hstk, hoth⟩ := htail ts ss hok vs hvs s' Rs hs
    exact ⟨out, s'', m, ⟨ts, ss, hok, hpost⟩, hev, hle, hstk, hoth⟩
  have stepSM : WordR main P1 (fun vs => vs = [vx, vy] ++ R) (fun _ out => out = [vn, vx, vy] ++ R) (fun _ => CB) := by
    refine Work.Params.conseqC (main := main) hKer (hSM main x y R) ?_
    have h1 : x.size + y.size + 8 ≤ 16 * B := by rw [hBdef, hn]; omega
    exact cost_sm hKSMKB h1 hKB16
  have stepDup : WordR main pDup (fun vs => vs = [vn, vx, vy] ++ R) (fun _ out => out = [vn, vn, vx, vy] ++ R) (fun _ => CB) := by
    refine Work.Params.dupStep (main := main) hKer (hdup main) vn ([vx, vy] ++ R) CB ?_
    have h1 : vsz vn + 1 ≤ 4 * (Cg * B) := by have := hvn; omega
    exact cost_basic hKdupKB h1 hKB4
  have stepPar : WordR main progPar (fun vs => vs = [vn, vn, vx, vy] ++ R)
      (fun _ out => ∃ ts ss, HvdH.ParamOK n ts ss ∧
        out = [vb, vp, va, vT, vr, HvdH.intList ts, HvdH.intList ss, vn, vx, vy] ++ R)
      (fun _ => KPar * (n.size + 1) ^ KPar) := by
    refine hKer.conseq main progPar _ (fun vs => vs = [vn, vn, vx, vy] ++ R) _ _ _ _
      (hPar main n (by rw [hn]; exact hle)) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨[vn, vx, vy] ++ R, hvs⟩
    · intro vs out hvs hpost
      obtain ⟨rest, ts, ss, hvs', hok, hout⟩ := hpost
      have hrest : rest = [vn, vx, vy] ++ R := by
        rw [hvs] at hvs'
        have h2 := (List.cons.injEq _ _ _ _).mp hvs'.symm
        exact h2.2
      refine ⟨ts, ss, hok, ?_⟩
      rw [hout, hrest]
      rfl
    · intro vs _; exact le_rfl
  have hSMdup : WordR main P2 (fun vs => vs = [vx, vy] ++ R)
      (fun _ out => out = [vn, vn, vx, vy] ++ R) (fun _ => 2 * CB) := by
    refine Work.Params.conseqC (main := main) hKer
      (Work.Params.seqC (main := main) hKer stepSM stepDup) ?_
    exact Nat.le_of_eq (by ring)
  have hSMdupPar : WordR main P3 (fun vs => vs = [vx, vy] ++ R)
      (fun _ out => ∃ ts ss, HvdH.ParamOK n ts ss ∧
        out = [vb, vp, va, vT, vr, HvdH.intList ts, HvdH.intList ss, vn, vx, vy] ++ R)
      (fun _ => KPar * (n.size + 1) ^ KPar + 2 * CB) := by
    have h0 := hKer.seq main P2 progPar _ _ _ _ _ _ _ hSMdup stepPar
      (fun vs mid _ hmid => ⟨hmid, le_rfl⟩)
    refine hKer.conseq main (Cmd.seq P2 progPar) _ _ _ _ _ _ h0 ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out _ hpost
      obtain ⟨mid, -, ts, ss, hok, hout⟩ := hpost
      exact ⟨ts, ss, hok, hout⟩
    · intro vs _; exact Nat.le_of_eq (by ring)
  have hAll0 := hKer.seq main P3 T21 _ _ _ _ _ _ (fun _ => 21 * CB) hSMdupPar htailE
    (fun vs mid _ hmid => ⟨hmid, le_rfl⟩)
  have hAll : WordR main PROG (fun vs => vs = [vx, vy] ++ R)
      (fun _ out => ∃ ts ss, HvdH.ParamOK n ts ss ∧ out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R))
      (fun _ => (KPar * (n.size + 1) ^ KPar + 2 * CB) + 21 * CB) := by
    refine hKer.conseq main PROG _ _ _ _ _ _ hAll0 ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out _ hq
      obtain ⟨mid, hm, ts, ss, hok, hout⟩ := hq
      exact ⟨ts, ss, hok, hout⟩
    · intro vs _; exact le_rfl
  have hFin : WordR main PROG (fun vs => vs = [vx, vy] ++ R)
      (fun _ out => ∃ ts ss, HvdH.ParamOK n ts ss ∧ out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R))
      (fun _ => KPar * (n.size + 1) ^ KPar + 23 * CB) := by
    refine hKer.conseq main PROG _ _ _ _ _ _ hAll ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out _ hq; exact hq
    · intro vs _; exact Nat.le_of_eq (by ring)
  refine hKer.conseq main PROG (fun vs => vs = [vx, vy] ++ R) (fun vs => vs = [vx, vy] ++ R)
    (fun _ out => ∃ ts ss, HvdH.ParamOK n ts ss ∧ out = ([(Val.int ((ss.prod : ℕ) : ℤ)),vQ,vb,vp,va,(HvdH.intList ts),(HvdH.intList ss),vx,vy] ++ R))
    (fun vs out => vs = [HvdH.Val.int x, HvdH.Val.int y] ++ R ∧
      ∃ (sp : SP), out = env sp R ∧ sp.x = x ∧ sp.y = y ∧
        sp.b = HvdH.bpar (max x.size y.size) ∧ sp.p = HvdH.ppar (max x.size y.size) ∧
        sp.α = HvdH.apar (max x.size y.size) ∧ sp.S = sp.ss.prod ∧
        sp.ts.prod = HvdH.Tpar (max x.size y.size) ∧
        sp.ss.length = HvdH.D ∧ sp.ts.length = HvdH.D ∧
        HvdH.ParamOK (max x.size y.size) sp.ts sp.ss ∧
        sp.N' = nchunks (max x.size y.size) (HvdH.bpar (max x.size y.size)))
    (fun _ => KPar * (n.size + 1) ^ KPar + 23 * CB)
    (fun _ => KPar * ((max x.size y.size).size + 1) ^ KPar * (32 * (KB * KB) + 1) +
      (32 * (KB * KB) + 1) * (x.size + y.size + 1)) hFin ?_ ?_ ?_
  · intro vs h; exact h
  · intro vs out hvs hpost
    obtain ⟨ts, ss, hok, hout⟩ := hpost
    let sp : SP := { S := ss.prod, N' := nchunks n (HvdH.bpar n), b := HvdH.bpar n, p := HvdH.ppar n, α := HvdH.apar n, x := x, y := y, ts := ts, ss := ss }
    refine ⟨hvs, ⟨sp, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hok.2.2.2.1, hok.2.1, hok.1, hok, rfl⟩⟩
    · rw [hout]; rfl
  · intro vs _
    show KPar * (n.size + 1) ^ KPar + 23 * CB ≤
      KPar * (n.size + 1) ^ KPar * (32 * (KB * KB) + 1) + (32 * (KB * KB) + 1) * (x.size + y.size + 1)
    have hc1 : 23 * CB ≤ 32 * (KB * KB) * (x.size + y.size + 1) := by
      have h2 : 23 * (KB * KB) ≤ 32 * (KB * KB) := by omega
      have h3 : B ≤ x.size + y.size + 1 := by rw [hBdef, hn]; omega
      calc 23 * CB = (23 * (KB * KB)) * B := by rw [hCBdef]; ring
        _ ≤ (32 * (KB * KB)) * B := Nat.mul_le_mul_right B h2
        _ ≤ (32 * (KB * KB)) * (x.size + y.size + 1) := Nat.mul_le_mul_left _ h3
    have hc2 : KPar * (n.size + 1) ^ KPar ≤ KPar * (n.size + 1) ^ KPar * (32 * (KB * KB) + 1) := by
      calc KPar * (n.size + 1) ^ KPar = KPar * (n.size + 1) ^ KPar * 1 := by ring
        _ ≤ KPar * (n.size + 1) ^ KPar * (32 * (KB * KB) + 1) := by
            exact Nat.mul_le_mul_left _ (Nat.le_add_left 1 (32 * (KB * KB)))
    refine le_trans (Nat.add_le_add hc2 hc1) ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right (32 * (KB * KB)) 1)) _

end Work.Main.step
