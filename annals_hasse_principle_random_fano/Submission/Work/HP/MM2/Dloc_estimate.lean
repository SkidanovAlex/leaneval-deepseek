import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.Sstar2_loc_pair
import Submission.Work.HP.DlocReindex
import Submission.Work.HP.FF_bound
import Submission.Work.HP.EE_lower_all
import Submission.Work.HP.Lat.detL_ge_one

/-!
# L3e: the estimate for `D^loc`

Assembly of `Dloc_estimate` (Browning--Le Boudec--Sawin, node N09, Lemma D local) from

* the per-pair asymptotic `Sstar2_loc_pair` (L2b),
* the reindexing identity `DlocReindex`,
* `FF_bound` and `EE_lower_all`,

exactly as in `DESIGN_REVIEW.md` §1.2 ("`D^loc`" and "Final assembly").

The sum over pairs of the per-pair main terms is `mainTerm`, and the errors add up to
`2ι A^{N-2} (F_{d,n}(B) + E_{d,n}(B)/log A)`; Lemma F and the lower half of Lemma E turn this
into `mainTerm / sqrt(log A)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Local abbreviations -/

/-- `(α W)^2 / 4` with `α = log B`, `W = bigW (wOf B)`. -/
private def dlocW (B : ℝ) : ℝ := (Real.log B * (bigW (wOf B) : ℝ)) ^ 2 / 4

/-- `2 ι_{d,n} A^{N-2}`, the coefficient of the main term. -/
private def dlocM (d n : ℕ) (A : ℝ) : ℝ := 2 * iotaDN d n * A ^ (NN d n - 2)

/-- `‖ν(x)‖ ‖ν(y)‖`. -/
private def dlocN (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  eNorm (veronese d n p.1) * eNorm (veronese d n p.2)

/-- `𝓢*_2(Γ^{loc}_{x,y}(W); 𝒯^{loc}_{x,y}(A,α))`. -/
private def dlocS (d n : ℕ) (A B : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B))) (TlocSet d n p.1 p.2 A (Real.log B))

/-! ## Elementary auxiliary facts -/

private lemma iotaDN_nonneg' (d n : ℕ) : 0 ≤ iotaDN d n := by
  rw [iotaDN]
  refine div_nonneg ENNReal.toReal_nonneg ?_
  refine mul_nonneg (by norm_num) ?_
  exact tsum_nonneg (fun k => by positivity)

private lemma bigW_pos' (w : ℝ) : 0 < bigW w := by
  rw [bigW]
  exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _

private lemma isPrim_ne_zero_dl' {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : IsPrim v) :
    v ≠ 0 := by
  intro h
  rw [IsPrim] at hv
  have h0 : (Finset.univ.gcd (0 : ι → ℤ)) = 0 := by
    rw [Finset.gcd_eq_zero_iff]; intro i _; rfl
  rw [← h] at h0
  rw [h0] at hv
  exact one_ne_zero hv.symm

private lemma sq_pos_of_ne_zero' {a : ℝ} (h : a ≠ 0) : 0 < a ^ 2 := by
  rcases lt_or_gt_of_ne h.symm with hlt | hgt
  · nlinarith
  · nlinarith

private lemma eNorm_pos_of_ne_zero' {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    0 < eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  rw [eNorm]
  apply Real.sqrt_pos.mpr
  have h1 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((v j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : 0 < ((v i : ℝ)) ^ 2 := sq_pos_of_ne_zero' (by exact_mod_cast hi)
  linarith

private lemma pow_eq_zero_nat {a : ℤ} {k : ℕ} (hk : 0 < k) (h : a ^ k = 0) : a = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  simpa using h

/-- The monomial `X_i^d`. -/
private def monDiD (d n : ℕ) (i : Fin (n + 1)) : Mon d n :=
  ⟨fun k => ⟨if k = i then d else 0, by split <;> omega⟩,
   by rw [Finset.sum_ite_eq' Finset.univ i (fun _ => d)]; simp⟩

private lemma veronese_monDiD (d n : ℕ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    veronese d n x (monDiD d n i) = x i ^ d := by
  simp only [veronese, monDiD]
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma veronese_ne_zero_of_ne_zero {d n : ℕ} (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ}
    (hx : x ≠ 0) : veronese d n x ≠ 0 := by
  intro h
  apply hx
  funext i
  have h1 : veronese d n x (monDiD d n i) = x i ^ d := veronese_monDiD d n x i
  have h2 : x i ^ d = 0 := by rw [← h1, h]; rfl
  exact pow_eq_zero_nat (k := d) (by omega) h2

private lemma eNorm_veronese_pos (d n : ℕ) (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ}
    (hx : IsPrim x) : 0 < eNorm (veronese d n x) :=
  eNorm_pos_of_ne_zero' (veronese_ne_zero_of_ne_zero hd (isPrim_ne_zero_dl' hx))

private lemma dlocN_nonneg (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    0 ≤ dlocN d n p :=
  mul_nonneg (eNorm_nonneg _) (eNorm_nonneg _)

/-- For `p ∈ Ω` the norm product `‖ν(x)‖‖ν(y)‖` does not vanish. -/
private lemma dlocN_ne_zero (d n : ℕ) (hd : 1 ≤ d) {B : ℝ}
    {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)} (hp : p ∈ Omega d n B) :
    dlocN d n p ≠ 0 := by
  have h1 : 0 < eNorm (veronese d n p.1) := eNorm_veronese_pos d n hd hp.1.1
  have h2 : 0 < eNorm (veronese d n p.2) := eNorm_veronese_pos d n hd hp.2.1.1
  exact ne_of_gt (mul_pos h1 h2)

private lemma detL_Gam_ne_zero (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    detL (Gam d n p.1 p.2) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le one_pos (Lat.detL_ge_one (Gam d n p.1 p.2)))

/-- **The per-pair identity.** The weight `(αW)²/4` times `locMain` divided by
`‖ν(x)‖‖ν(y)‖` is the clean main term `2ι A^{N-2}/det Γ`. -/
private lemma dlocW_locMain_identity (d n : ℕ) [DecidableEq (Mon d n)] (A B : ℝ)
    (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))
    (hα : 0 < Real.log B) (hW : 0 < (bigW (wOf B) : ℝ))
    (hN : dlocN d n p ≠ 0) (hD : detL (Gam d n p.1 p.2) ≠ 0) :
    dlocW B * (locMain d n A B p / dlocN d n p)
      = dlocM d n A / detL (Gam d n p.1 p.2) := by
  have hαW : Real.log B * (bigW (wOf B) : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hW)
  have hN1 : eNorm (veronese d n p.1) ≠ 0 := fun h => hN (by rw [dlocN, h, zero_mul])
  have hN2 : eNorm (veronese d n p.2) ≠ 0 := fun h => hN (by rw [dlocN, h, mul_zero])
  rw [dlocW, dlocM, dlocN, locMain]
  field_simp
  ring

/-! ## The estimate -/

/-- (L3e) `D^loc` (no degenerate part: `λ_N(GamLoc(Q)) ≤ Q ≤ W` for every pair). -/
private theorem dloc_estimate_of (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d)
    (hpair : ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ p ∈ Omega d n B,
        |Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B))) (TlocSet d n p.1 p.2 A (Real.log B))
            - locMain d n A B p|
          ≤ C * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A))
    (hFFbound : ∃ K B₀ : ℝ, 0 < K ∧ ∀ B : ℝ, B₀ ≤ B →
      FF d n B ≤ K * B ^ 2 / Real.log B ^ ((1 : ℝ) / 2))
    (hEElower : ∃ c B₀ : ℝ, 0 < c ∧ ∀ B : ℝ, B₀ ≤ B → c * B ^ 2 ≤ EE d n B) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      |Dloc d n A B - mainTerm d n A B|
        ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
  obtain ⟨C, Bp, hCpos, hpair⟩ := hpair
  obtain ⟨KF, BF, hKFpos, hKF⟩ := hFFbound
  obtain ⟨c, BE, hcpos, hc⟩ := hEElower
  have hCnn : 0 ≤ C := hCpos.le
  refine ⟨C * (KF * Real.sqrt 2 / c + 1),
      max (max Bp BF) (max BE (Real.exp 2 + 1)), ?_⟩
  intro A B hB hBA hAB
  have hBp : Bp ≤ B :=
    le_trans (le_trans (le_max_left Bp BF) (le_max_left (max Bp BF) _)) hB
  have hBF : BF ≤ B :=
    le_trans (le_trans (le_max_right Bp BF) (le_max_left (max Bp BF) _)) hB
  have hBE : BE ≤ B :=
    le_trans (le_trans (le_max_left BE (Real.exp 2 + 1)) (le_max_right (max Bp BF) _)) hB
  have hexp2 : Real.exp 2 + 1 ≤ B :=
    le_trans (le_trans (le_max_right BE (Real.exp 2 + 1)) (le_max_right (max Bp BF) _)) hB
  have hBexp : Real.exp 2 ≤ B := by linarith [Real.exp_pos 2]
  have hB1 : 1 < B := by
    have h := Real.add_one_le_exp 2
    linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB1
  have hAexp : Real.exp (5 / 3) ≤ A := by
    have h1 : (Real.exp 2) ^ ((5 : ℝ) / 6) ≤ B ^ ((5 : ℝ) / 6) :=
      Real.rpow_le_rpow (Real.exp_pos 2).le hBexp (by norm_num)
    have h2 : (Real.exp 2) ^ ((5 : ℝ) / 6) = Real.exp (5 / 3) := by
      rw [← Real.exp_mul]; norm_num
    linarith
  have hlogA : 1 ≤ Real.log A := by
    have h3 := Real.log_le_log (Real.exp_pos (5 / 3)) hAexp
    rw [Real.log_exp] at h3
    linarith
  have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos (5 / 3)) hAexp
  have hlogA0 : 0 < Real.log A := lt_of_lt_of_le one_pos hlogA
  have hWpos : 0 < (bigW (wOf B) : ℝ) := by
    exact_mod_cast bigW_pos' (wOf B)
  classical
  set F : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    (Omega_finite d n B).toFinset with hFdef
  have hFmem : ∀ p, p ∈ F ↔ p ∈ Omega d n B := fun p => by
    rw [hFdef, Set.Finite.mem_toFinset]
  have hEE : EE d n B = ∑ p ∈ F, 1 / detL (Gam d n p.1 p.2) := by
    rw [EE, finsum_mem_eq_finite_toFinset_sum _ (Omega_finite d n B), ← hFdef]
  have hFF : FF d n B = ∑ p ∈ F, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2) := by
    rw [FF, finsum_mem_eq_finite_toFinset_sum _ (Omega_finite d n B), ← hFdef]
  have hDloc : Dloc d n A B = ∑ p ∈ F, dlocW B * (dlocS d n A B p / dlocN d n p) := by
    rw [DlocReindex d n A B hB1]
    rw [finsum_mem_eq_finite_toFinset_sum _ (Omega_finite d n B), ← hFdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [dlocW, dlocS, dlocN]
  have hmain1 : mainTerm d n A B = ∑ p ∈ F, dlocM d n A / detL (Gam d n p.1 p.2) := by
    rw [mainTerm, hEE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [dlocM]
    ring
  have hid : ∀ p ∈ F, dlocW B * (locMain d n A B p / dlocN d n p)
      = dlocM d n A / detL (Gam d n p.1 p.2) :=
    fun p hp => dlocW_locMain_identity d n A B p hlogB hWpos
      (dlocN_ne_zero d n (by omega) ((hFmem p).mp hp)) (detL_Gam_ne_zero d n p)
  have hmain2 : mainTerm d n A B
      = ∑ p ∈ F, dlocW B * (locMain d n A B p / dlocN d n p) := by
    rw [hmain1]
    exact (Finset.sum_congr rfl hid).symm
  have hsub : Dloc d n A B - mainTerm d n A B
      = ∑ p ∈ F, dlocW B * (dlocS d n A B p - locMain d n A B p) / dlocN d n p := by
    rw [hDloc, hmain2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hNnn : ∀ p, 0 ≤ dlocN d n p := dlocN_nonneg d n
  have hw0 : 0 ≤ dlocW B := by rw [dlocW]; positivity
  -- Step 1: term-by-term, using the per-pair asymptotic
  have herr1 : |∑ p ∈ F, dlocW B * (dlocS d n A B p - locMain d n A B p) / dlocN d n p|
      ≤ ∑ p ∈ F, dlocW B
          * (C * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A))
          / dlocN d n p := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p hp => ?_)
    have hpOm : p ∈ Omega d n B := (hFmem p).mp hp
    have hpb := hpair A B hBp hBA hAB p hpOm
    have hkey : |dlocW B * (dlocS d n A B p - locMain d n A B p) / dlocN d n p|
        = (dlocW B / dlocN d n p) * |dlocS d n A B p - locMain d n A B p| := by
      rw [abs_div, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (hNnn p)]
      ring
    rw [hkey]
    refine le_trans (mul_le_mul_of_nonneg_left hpb (div_nonneg hw0 (hNnn p))) ?_
    rw [div_mul_eq_mul_div]
  -- Step 2: sum the per-pair main terms
  have herr2 : ∑ p ∈ F, dlocW B
        * (C * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A)) / dlocN d n p
      = C * dlocM d n A * FF d n B + (C * dlocM d n A / Real.log A) * EE d n B := by
    rw [hFF, hEE, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h := hid p hp
    rw [show dlocW B * (C * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A))
          / dlocN d n p
        = C * (errXY d n B p.1 p.2 + 1 / Real.log A)
            * (dlocW B * (locMain d n A B p / dlocN d n p)) from by ring_nf, h]
    ring
  have herr : |Dloc d n A B - mainTerm d n A B|
      ≤ C * dlocM d n A * (FF d n B + EE d n B / Real.log A) := by
    rw [hsub]
    refine le_trans herr1 ?_
    rw [herr2]
    exact le_of_eq (by ring_nf)
  -- Step 3: `F_{d,n}(B) ≪ E_{d,n}(B)/sqrt(log A)`, `E ≫ B²`
  have hFF1 : FF d n B ≤ KF * B ^ 2 / Real.log B ^ ((1 : ℝ) / 2) := hKF B hBF
  have hEE1 : c * B ^ 2 ≤ EE d n B := hc B hBE
  have hEE0 : 0 ≤ EE d n B := le_trans (mul_nonneg hcpos.le (sq_nonneg B)) hEE1
  have hlogAnn : 0 ≤ Real.log A := hlogA0.le
  have hlogAB : Real.log A / 2 ≤ Real.log B := by
    have h1 : Real.log A ≤ Real.log (B ^ 2) := Real.log_le_log hA0 hAB
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hsqrtcmp : Real.log A ^ ((1 : ℝ) / 2) / Real.sqrt 2 ≤ Real.log B ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_div hlogAnn]
    exact Real.sqrt_le_sqrt hlogAB
  have hsqrtApos : 0 < Real.log A ^ ((1 : ℝ) / 2) / Real.sqrt 2 := by
    refine div_pos ?_ (Real.sqrt_pos.mpr (by norm_num))
    rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_pos.mpr hlogA0
  have hFF2 : FF d n B ≤ KF * Real.sqrt 2 * B ^ 2 / Real.log A ^ ((1 : ℝ) / 2) := by
    calc FF d n B ≤ KF * B ^ 2 / Real.log B ^ ((1 : ℝ) / 2) := hFF1
      _ ≤ KF * B ^ 2 / (Real.log A ^ ((1 : ℝ) / 2) / Real.sqrt 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hKFpos.le (sq_nonneg B)) hsqrtApos hsqrtcmp
      _ = KF * Real.sqrt 2 * B ^ 2 / Real.log A ^ ((1 : ℝ) / 2) := by
          rw [div_div_eq_mul_div]; ring_nf
  have hFF3 : FF d n B ≤ (KF * Real.sqrt 2 / c) * EE d n B / Real.log A ^ ((1 : ℝ) / 2) := by
    calc FF d n B ≤ KF * Real.sqrt 2 * B ^ 2 / Real.log A ^ ((1 : ℝ) / 2) := hFF2
      _ ≤ KF * Real.sqrt 2 * (EE d n B / c) / Real.log A ^ ((1 : ℝ) / 2) := by
          refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hlogAnn _)
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKFpos.le (Real.sqrt_nonneg 2))
          rw [le_div_iff₀ hcpos]
          linarith
      _ = (KF * Real.sqrt 2 / c) * EE d n B / Real.log A ^ ((1 : ℝ) / 2) := by ring
  have hEl : EE d n B / Real.log A ≤ EE d n B / Real.log A ^ ((1 : ℝ) / 2) := by
    have hs : Real.sqrt (Real.log A) ≤ Real.log A := by
      have hsq : (Real.sqrt (Real.log A)) ^ 2 = Real.log A := Real.sq_sqrt hlogAnn
      have hs1 : 1 ≤ Real.sqrt (Real.log A) := by
        nlinarith [Real.sqrt_nonneg (Real.log A), hlogA, hsq]
      nlinarith [Real.sqrt_nonneg (Real.log A), hs1, hsq,
        mul_nonneg (sub_nonneg.mpr hs1) (Real.sqrt_nonneg (Real.log A))]
    rw [← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_left hEE0 (Real.sqrt_pos.mpr hlogA0) hs
  have hFFb : FF d n B + EE d n B / Real.log A
      ≤ (KF * Real.sqrt 2 / c + 1) * EE d n B / Real.log A ^ ((1 : ℝ) / 2) := by
    calc FF d n B + EE d n B / Real.log A
        ≤ (KF * Real.sqrt 2 / c) * EE d n B / Real.log A ^ ((1 : ℝ) / 2)
            + EE d n B / Real.log A ^ ((1 : ℝ) / 2) := add_le_add hFF3 hEl
      _ = (KF * Real.sqrt 2 / c + 1) * EE d n B / Real.log A ^ ((1 : ℝ) / 2) := by ring
  have hM0 : 0 ≤ dlocM d n A := by
    rw [dlocM]
    exact mul_nonneg (mul_nonneg (by norm_num) (iotaDN_nonneg' d n)) (pow_nonneg hA0.le _)
  calc |Dloc d n A B - mainTerm d n A B|
      ≤ C * dlocM d n A * (FF d n B + EE d n B / Real.log A) := herr
    _ ≤ C * dlocM d n A * ((KF * Real.sqrt 2 / c + 1) * EE d n B
          / Real.log A ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hFFb (mul_nonneg hCnn hM0)
    _ = C * (KF * Real.sqrt 2 / c + 1) * mainTerm d n A B
          / Real.log A ^ ((1 : ℝ) / 2) := by
        rw [mainTerm, dlocM]; ring

/-! ## The node -/

/-- (L3e) `D^loc` (no degenerate part: `λ_N(GamLoc(Q)) ≤ Q ≤ W` for every pair). -/
theorem Dloc_estimate (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      |Dloc d n A B - mainTerm d n A B|
        ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) :=
  dloc_estimate_of d n hd (Sstar2_loc_pair d n hd hdn h22) (FF_bound d n hd hdn h22)
    (EE_lower_all d n hd hdn h22)

end Work.HP.MM2
