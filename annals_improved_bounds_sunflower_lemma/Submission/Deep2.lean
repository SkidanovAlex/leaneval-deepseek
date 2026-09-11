import Mathlib
import Submission.Deep
import Submission.FixedU
import Submission.Levels1
import Submission.PairSum
import Submission.LevelFinal

/-!
# Assembly of `rao_petal` from `fixed_U_step`
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- h := ⌈kap·n/r⌉ -/
noncomputable def hstep (n : ℕ) (r : ℝ) : ℕ := Nat.ceil ((kap * (n : ℝ)) / r)

/-- size of the first level (positive). -/
lemma hstep_pos {n : ℕ} {r : ℝ} (hrn : r ≤ (n : ℝ)) (hr1 : 1 ≤ r) (n0 : 0 < n) :
    0 < hstep n r := by
  unfold hstep
  apply Nat.ceil_pos.mpr
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast n0
  have hkap0 : 0 < kap := by unfold kap; positivity
  positivity

/-- `hstep ≥ kap·n/r` -/
lemma hstep_lower {n : ℕ} {r : ℝ} (hrn : r ≤ (n : ℝ)) (hr1 : 1 ≤ r) :
    ((kap * (n : ℝ)) / r ≤ (hstep n r : ℝ)) := by
  unfold hstep
  exact_mod_cast Nat.le_ceil ((kap * (n : ℝ)) / r)

/-- `hstep ≤ 2·kap·n/r` for `r ≥ kap` -/
lemma hstep_upper {n : ℕ} {r : ℝ} (hrn : r ≤ (n : ℝ)) (hr1 : 1 ≤ r) (hkap1 : kap ≤ r)
    (n0 : 0 < n) :
    ((hstep n r : ℝ) ≤ 2 * (kap * (n : ℝ)) / r) := by
  unfold hstep
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hx1 : (1 : ℝ) ≤ (kap * (n : ℝ)) / r := by
    have hnrg : (1 : ℝ) ≤ (n : ℝ) / r := by
      rw [le_div_iff₀ hr0]
      nlinarith
    have hkap1' : (1 : ℝ) ≤ kap := by unfold kap; norm_num
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast n0
    have hmul : (1 : ℝ) ≤ kap * ((n : ℝ) / r) := by
      have h20 : 0 ≤ (n : ℝ) / r := le_of_lt (by rw [div_pos_iff_of_pos_right hr0]; positivity)
      nlinarith
    calc
      (1 : ℝ) ≤ kap * ((n : ℝ) / r) := hmul
      _ = (kap * (n : ℝ)) / r := by
        rw [div_eq_mul_inv]
        ring
  have hceil_le : ((Nat.ceil ((kap * (n : ℝ)) / r) : ℝ) ≤ 2 * ((kap * (n : ℝ)) / r)) := by
    have hx0 : (0 : ℝ) ≤ (kap * (n : ℝ)) / r := by nlinarith
    have hcl : ((Nat.ceil ((kap * (n : ℝ)) / r) : ℝ) < (kap * (n : ℝ)) / r + 1) := by
      exact_mod_cast (Nat.ceil_lt_add_one hx0)
    have h2 : (kap * (n : ℝ)) / r + 1 ≤ 2 * ((kap * (n : ℝ)) / r) := by
      nlinarith [hx1]
    exact le_trans (le_of_lt hcl) h2
  have hconv : 2 * ((kap * (n : ℝ)) / r) = 2 * (kap * (n : ℝ)) / r := by ring
  simpa [hconv] using hceil_le

lemma hcap_nat {n i h : ℕ} (hcap : ((i + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (n : ℝ) / 8) :
    (8 * ((i + 1) * h) ≤ n) := by
  have hcap8 : (8 : ℝ) * (((i + 1 : ℕ) : ℝ) * (h : ℝ)) ≤ (n : ℝ) := by nlinarith
  have hreal : ((8 * ((i + 1) * h) : ℕ) : ℝ) ≤ (n : ℝ) := by
    norm_num at hcap8 ⊢
    exact hcap8
  exact_mod_cast hreal
lemma hcap_ih_h {n i h : ℕ} (hcap : ((i + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (n : ℝ) / 8) :
    i * h + h ≤ n := by
  have hB := hcap_nat (n := n) (i := i) (h := h) hcap
  -- i·h + h = (i+1)·h ≤ 8((i+1)h) ≤ n
  have hle : i * h + h ≤ 8 * ((i + 1) * h) := by
    have : i * h + h = (i + 1) * h := by ring
    rw [this]
    simpa using (Nat.mul_le_mul_right ((i + 1) * h) (by omega : (1 : ℕ) ≤ 8))
  omega
lemma hcap_ih_2h {n i h : ℕ} (hcap : ((i + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (n : ℝ) / 8) :
    i * h + 2 * h ≤ n := by
  have hB := hcap_nat (n := n) (i := i) (h := h) hcap
  have hle : i * h + 2 * h ≤ 8 * ((i + 1) * h) := by
    have : i * h + 2 * h = (i + 2) * h := by ring
    rw [this]
    simpa [Nat.mul_assoc] using (Nat.mul_le_mul_right h (by omega : (i + 2 : ℕ) ≤ 8 * (i + 1)))
  omega
lemma hcap_8ih {n i h : ℕ} (hcap : ((i + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (n : ℝ) / 8) :
    8 * (i * h) ≤ n := by
  have hB := hcap_nat (n := n) (i := i) (h := h) hcap
  have : 8 * (i * h) ≤ 8 * ((i + 1) * h) := by
    exact Nat.mul_le_mul_left 8 (by
      have : i * h ≤ (i + 1) * h := by
        simpa using (Nat.mul_le_mul_right h (by omega : i ≤ i + 1))
      exact this)
  omega
lemma hcap_ih_le_n {n i h : ℕ} (hcap : ((i + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (n : ℝ) / 8) :
    i * h ≤ n := by
  have h1 : (i + 1) * h ≤ n := by
    have hsum : i * h + h = (i + 1) * h := by ring
    rw [← hsum]
    exact hcap_ih_h (n := n) (i := i) (h := h) hcap
  have : i * h ≤ (i + 1) * h := by
    simpa using (Nat.mul_le_mul_right h (by omega : i ≤ i + 1))
  omega


/-- |S| ≥ r^k and r ≥ 1, k ≥ 1 imply S.Nonempty. -/
lemma S_ne_of_Sr {S : Finset (Finset α)} {k : ℕ} {r : ℝ} (hk : 1 ≤ k) (hr1 : 1 ≤ r)
    (hSr : (S.card : ℝ) ≥ r ^ k) : S.Nonempty := by
  have h1 : (1 : ℝ) ≤ r ^ k := by
    exact one_le_pow₀ hr1
  have hpos : 0 < S.card := by
    have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by nlinarith
    exact_mod_cast (by nlinarith : (0 : ℝ) < (S.card : ℝ))
  exact Finset.card_pos.mp hpos


lemma level_step {X : Finset α} {S : Finset (Finset α)} {k : ℕ} {r : ℝ}
    (hk : 2 ≤ k) (hn6 : 6 * k ≤ X.card)
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hSr : (S.card : ℝ) ≥ r ^ k) (hr1 : 1 ≤ r) (hrn : r ≤ (X.card : ℝ))
    (i : ℕ) (hcap : ((i + 1 : ℕ) : ℝ) * (hstep X.card r : ℝ) ≤ (X.card : ℝ) / 8) :
    Echi S X ((i + 1) * hstep X.card r) ≤ c0 * Echi S X (i * hstep X.card r) := by
  let h : ℕ := hstep X.card r
  have hXpos : 0 < X.card := by omega
  have hhpos : 0 < h := by simpa [h] using hstep_pos (n := X.card) (r := r) hrn hr1 hXpos
  have hcap' : ((i + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (X.card : ℝ) / 8 := by simpa [h] using hcap
  have hSn : S.Nonempty := S_ne_of_Sr (k := k) (r := r) (by omega) hr1 hSr
  have hstepU : ∀ U ∈ cardSubsets X (i * h), Eext S X U h ≤ c0 * Efix S U := by
    intro U hU
    have hUs := Finset.mem_powersetCard.mp hU
    refine fixed_U_step (X:=X) (S:=S) (k:=k) (r:=r) hk hn6 hS huni hspread hSr hr1 hrn
      (U:=U) (v:=h) hUs.1 ?h8u ?hv ?hkap ?huv2 ?huv ?hrbig
    · have : 8 * (i * h) ≤ X.card := hcap_8ih (n := X.card) (i := i) (h := h) hcap'
      rw [hUs.2]
      exact this
    · exact hhpos
    · have hl := hstep_lower (n := X.card) (r := r) hrn hr1
      simpa [h] using hl
    · have hi2h' : i * h + 2 * h ≤ X.card := hcap_ih_2h (n := X.card) (i := i) (h := h) hcap'
      rw [hUs.2]
      exact hi2h'
    · have hih : i * h + h ≤ X.card := hcap_ih_h (n := X.card) (i := i) (h := h) hcap'
      rw [hUs.2]
      exact hih
    · have hkap' : (kap * (X.card : ℝ)) / r ≤ (h : ℝ) := by
        have hl := hstep_lower (n := X.card) (r := r) hrn hr1
        simpa [h] using hl
      have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
      have hn0 : 0 < (X.card : ℝ) := by exact_mod_cast hXpos
      have hrmul : kap * (X.card : ℝ) ≤ (h : ℝ) * r := by
        rw [div_le_iff₀ hr0] at hkap'
        nlinarith
      have hrh : kap ≤ ((h : ℝ) * r) / (X.card : ℝ) := by
        rw [le_div_iff₀ hn0]
        nlinarith
      have h6 : (2 : ℝ) ^ 6 ≤ kap := by unfold kap; norm_num
      exact le_trans h6 (by simpa [div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using hrh)
  have hres : Echi S X (i * h + h) ≤ c0 * Echi S X (i * h) := by
    apply Echi_step_of_fixed (S:=S) (X:=X) (u := i * h) (v := h) (c0 := c0)
    · exact hcap_ih_le_n (n := X.card) (i := i) (h := h) hcap'
    · have hi2h' : i * h + 2 * h ≤ X.card := hcap_ih_2h (n := X.card) (i := i) (h := h) hcap'
      have hle : h ≤ X.card - i * h := by omega
      exact hle
    · exact hSn
    · exact hstepU
  rw [show i * h + h = (i + 1) * h by ring] at hres
  change Echi S X ((i + 1) * h) ≤ c0 * Echi S X (i * h)
  exact hres


/-! ## The level claim -/
lemma level_claim {X : Finset α} {S : Finset (Finset α)} {k : ℕ} {r : ℝ}
    (hk : 2 ≤ k) (hn6 : 6 * k ≤ X.card)
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hSr : (S.card : ℝ) ≥ r ^ k) (hr1 : 1 ≤ r) (hrn : r ≤ (X.card : ℝ))
    (m : ℕ) (hmcap : (m : ℝ) * (hstep X.card r : ℝ) ≤ (X.card : ℝ) / 8) :
    Echi S X (m * hstep X.card r) ≤ k * c0 ^ m := by
  let h : ℕ := hstep X.card r
  revert hmcap
  induction m with
  | zero =>
      intro hmcap
      have h0 := Echi_zero_le (S := S) (X := X) (k := k) hS huni
      simpa using h0
  | succ m ih =>
      intro hmcap
      have hcap' : ((m + 1 : ℕ) : ℝ) * (h : ℝ) ≤ (X.card : ℝ) / 8 := by simpa [h] using hmcap
      have hstep1 := level_step (X := X) (S := S) (k := k) (r := r) hk hn6 hS huni hspread hSr hr1 hrn
        (i := m) (by simpa [h] using hcap')
      have hle1 : Echi S X ((m + 1) * h) ≤ c0 * Echi S X (m * h) := by simpa [h] using hstep1
      have hle2 : c0 * Echi S X (m * h) ≤ c0 * (k * c0 ^ m) := by
        have hh0 : 0 ≤ (h : ℝ) := by positivity
        have hmle : (m : ℝ) * (h : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (h : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_succ m)) hh0
        have hprem : (m : ℝ) * (hstep X.card r : ℝ) ≤ (X.card : ℝ) / 8 := by
          simpa [h] using (le_trans hmle hcap')
        have hih := ih hprem
        have hih' : Echi S X (m * h) ≤ k * c0 ^ m := by simpa [h] using hih
        have hc0 : 0 ≤ c0 := by unfold c0; norm_num
        exact mul_le_mul_of_nonneg_left hih' hc0
      calc
        Echi S X ((m + 1) * h) ≤ c0 * Echi S X (m * h) := hle1
        _ ≤ c0 * (k * c0 ^ m) := hle2
        _ = k * c0 ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- X.card ≥ 12 when k ≥ 2 and 6k ≤ X.card -/
lemma Xcard_ge_12 {X : Finset α} {k : ℕ} (hk : 2 ≤ k) (hn6 : 6 * k ≤ X.card) :
    (12 : ℝ) ≤ (X.card : ℝ) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h6n2 : (6 : ℝ) * (k : ℝ) ≤ (X.card : ℝ) := by
    have h6n : ((6 * k : ℕ) : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hn6
    simpa [Nat.cast_mul] using h6n
  nlinarith

/-- ceil(γ·n) ≤ n/8 when 0<γ≤1/32 and 12 ≤ n (real) -/
lemma ceil_gamma_le {γ : ℝ} {n : ℕ} (hγ0 : 0 < γ) (hγs : γ ≤ 1 / 32)
    (hn : (12 : ℝ) ≤ (n : ℝ)) :
    (Nat.ceil (γ * (n : ℝ)) : ℝ) ≤ (n : ℝ) / 8 := by
  have hγn0 : 0 ≤ γ * (n : ℝ) := mul_nonneg (le_of_lt hγ0) (by positivity)
  have hc1 : (Nat.ceil (γ * (n : ℝ)) : ℝ) < γ * (n : ℝ) + 1 := by
    exact_mod_cast (Nat.ceil_lt_add_one hγn0)
  have hg : γ * (n : ℝ) ≤ (n : ℝ) / 32 := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (mul_le_mul_of_nonneg_right hγs hn0)
  calc
    (Nat.ceil (γ * (n : ℝ)) : ℝ) ≤ γ * (n : ℝ) + 1 := le_of_lt hc1
    _ ≤ (n : ℝ) / 32 + 1 := by nlinarith only [hg]
    _ ≤ (n : ℝ) / 8 := by nlinarith only [hn]

/-- ceil(γn) ≤ n (nat) -/
lemma ceil_gamma_le_n {γ : ℝ} {n : ℕ} (hγ0 : 0 < γ) (hγs : γ ≤ 1 / 32)
    (hn : (12 : ℝ) ≤ (n : ℝ)) : Nat.ceil (γ * (n : ℝ)) ≤ n := by
  have h := ceil_gamma_le (γ := γ) (n := n) hγ0 hγs hn
  -- ≤ n/8 ≤ n
  have hle : (n : ℝ) / 8 ≤ (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by nlinarith
    nlinarith only [hn1]
  exact_mod_cast (le_trans h hle)

/-- c0-related constants -/
lemma c0_bounds : (0 : ℝ) < c0 ∧ c0 ≤ 1 := by
  unfold c0; norm_num

lemma c0_log_pos : (0 : ℝ) < Real.log (1 / c0) := by
  unfold c0
  apply Real.log_pos
  norm_num


/-! ## rao_petal -/
theorem rao_petal {X : Finset α} {S : Finset (Finset α)} {k : ℕ} {r γ ε : ℝ} {m : ℕ}
    (hk : 2 ≤ k)
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hSr : (S.card : ℝ) ≥ r ^ k)
    (hr1 : 1 ≤ r) (hrn : r ≤ (X.card : ℝ))
    (hn6 : 6 * k ≤ X.card)
    (hrkap : kap ≤ r)
    (hγ0 : 0 < γ) (hγs : γ ≤ 1 / 32)
    (hmγ : (m : ℝ) ≥ γ * (X.card : ℝ)) (hmn : m ≤ X.card)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hrbig : Bpetal / γ * Real.log (2 * (k : ℝ) / ε) ≤ r) :
    Echi S X m ≤ ε := by
  let n : ℕ := X.card
  have hnpos : 0 < n := by
    have : 6 * k ≤ n := by simpa [n] using hn6
    omega
  let h : ℕ := hstep n r
  let m0 : ℕ := Nat.ceil (γ * (n : ℝ))
  let j : ℕ := m0 / h
  have hn12 : (12 : ℝ) ≤ (n : ℝ) := by
    simpa [n] using (Xcard_ge_12 (X := X) (k := k) hk hn6)
  -- m0 ≤ m
  have hm0_le_m : m0 ≤ m := by
    unfold m0
    rw [Nat.ceil_le]
    exact hmγ
  have hm0n : (m0 : ℝ) ≤ (n : ℝ) / 8 := by
    simpa [m0, n] using (ceil_gamma_le (γ := γ) (n := X.card) hγ0 hγs (by simpa [n] using hn12))
  have hm0_le_n : m0 ≤ n := by
    simpa [m0, n] using (ceil_gamma_le_n (γ := γ) (n := X.card) hγ0 hγs (by simpa [n] using hn12))
  have hj_le_m0 : j * h ≤ m0 := by
    unfold j
    exact Nat.div_mul_le_self m0 h
  have hjh_n : (j : ℝ) * (h : ℝ) ≤ (n : ℝ) / 8 := by
    have hcast : ((j * h : ℕ) : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast hj_le_m0
    calc
      (j : ℝ) * (h : ℝ) = ((j * h : ℕ) : ℝ) := by simp [Nat.cast_mul]
      _ ≤ (m0 : ℝ) := hcast
      _ ≤ (n : ℝ) / 8 := hm0n
  have hlc := level_claim (X := X) (S := S) (k := k) (r := r) hk hn6 hS huni hspread hSr hr1 hrn
    (m := j) (by simpa [h, n] using hjh_n)
  have hlc' : Echi S X (j * h) ≤ k * c0 ^ j := by simpa [h, n] using hlc
  have hanti1 : Echi S X m ≤ Echi S X m0 := Echi_antitone (S := S) (X := X) (w := m) (u := m0)
    hm0_le_m hmn
  have hanti2 : Echi S X m0 ≤ Echi S X (j * h) := Echi_antitone (S := S) (X := X) (w := m0) (u := j * h)
    hj_le_m0 (by exact_mod_cast hm0_le_n)
  have hfinal : k * c0 ^ j ≤ ε := by
    -- j = m0/h
    have hj_def : j = m0 / h := by rfl
    -- 0 < h
    have hh : 0 < h := by
      simpa [h] using (hstep_pos (n := n) (r := r) (by simpa [n] using hrn) hr1 hnpos)
    -- γ·n ≤ m0
    have hm0ge : γ * (n : ℝ) ≤ (m0 : ℝ) := by
      unfold m0
      exact_mod_cast (Nat.le_ceil (γ * (n : ℝ)))
    -- h ≤ 2·kap·n/r
    have hh_ub : (h : ℝ) ≤ 2 * (kap * (n : ℝ)) / r := by
      have hup := hstep_upper (n := n) (r := r) (by simpa [n] using hrn) hr1 hrkap hnpos
      simpa [h] using hup
    exact final_level_bound (n := n) (h := h) (m0 := m0) (j := j) (k := k)
      (r := r) (γ := γ) (ε := ε) hj_def hh hm0ge hh_ub hγ0 hε0 hε1 hk hrbig hnpos hr1
  exact le_trans (le_trans hanti1 (le_trans hanti2 hlc')) hfinal

