import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.Sig2.finset_sum_rpow_neg_le
import Submission.Work.HP.Sig2.log_pow_le_rpow
import Submission.Work.HP.Sig2.le_mul_log_of_div_log_le
import Submission.Work.HP.Sig2.d3_lt_of_caseI
import Submission.Work.HP.MDEstimates.muXY_le
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.MDEstimates.detGam_lower
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.NN_ge_add_two
import Submission.Work.HP.Sig2.per_pair_sum_bound
import Submission.Work.HP.Sig2.omega_d3_count

/-!
# Case I of the large-`μ` part of the second moment

The complement of `Sigma2_caseF` inside the `μ(x,y) > A` range: the branch where the maximum
in `muXY` is the first argument, i.e. `¬ (𝔡₂³ ≤ 𝔡₃ ‖x‖‖y‖)`.  We prove
`Σ^{(2,I)}_{d,n}(A,B) ≤ K A^{N_{d,n}-2-1/3} B²`.

This is the paper's quantity `𝓘_{d,n}(A,B)` (Browning--Le Boudec--Sawin, Annals 2023, proof of
Lemma D).  The pair count over `𝔡₃` (`omega_d3_count`), the per-pair Lemma-R0 bound
(`per_pair_sum_bound`, converted in Case I by `mu_div_det_le`), the dyadic layer cake
(`finset_sum_rpow_le` via `caseI_piece_bound`), and the absorption of the logarithm (`caseI_arith_term`)
are combined into four `𝔡₃`-regimes.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section


namespace Work.HP.Sig2
open Work.HP

private def mkMonI (d n : ℕ) (g : Fin (n + 1) → ℕ) (hg : ∀ i, g i ≤ d)
    (hsum : ∑ i, g i = d) : Mon d n :=
  ⟨fun i => ⟨g i, Nat.lt_succ_of_le (hg i)⟩, by simpa using hsum⟩

private lemma mkMonI_val (d n : ℕ) (g : Fin (n + 1) → ℕ) (hg : ∀ i, g i ≤ d)
    (hsum : ∑ i, g i = d) (j : Fin (n + 1)) :
    (((mkMonI d n g hg hsum).1 j : Fin (d + 1)) : ℕ) = g j := rfl

private def pureFun (d n : ℕ) (j : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun i => if i = j then d else 0

private def mixFun (d n : ℕ) (z o q : Fin (n + 1)) (c : ℕ) : Fin (n + 1) → ℕ :=
  fun i => (if i = z then d - 1 - c else 0) + (if i = o then c else 0) + (if i = q then 1 else 0)

private def pureMon (d n : ℕ) (j : Fin (n + 1)) : Mon d n :=
  mkMonI d n (pureFun d n j) (fun i => by simp only [pureFun]; split <;> omega) (by
    rw [show (∑ i, pureFun d n j i) = d from by
      simp only [pureFun]
      rw [Fintype.sum_ite_eq']])

private lemma pureMon_val (d n : ℕ) (j i : Fin (n + 1)) :
    (((pureMon d n j).1 i : Fin (d + 1)) : ℕ) = pureFun d n j i := rfl

private lemma pureFun_self (d n : ℕ) (j : Fin (n + 1)) : pureFun d n j j = d := by
  simp [pureFun]

private lemma pureFun_of_ne (d n : ℕ) (j i : Fin (n + 1)) (h : i ≠ j) :
    pureFun d n j i = 0 := by
  simp [pureFun, h]

private def mixMon (d n : ℕ) (z o q : Fin (n + 1)) (c : ℕ) (hc : c ≤ d - 1) (hd : 5 ≤ d) :
    Mon d n :=
  mkMonI d n (mixFun d n z o q c) (fun i => by
    simp only [mixFun]
    split_ifs <;> omega) (by
    rw [show (∑ i, mixFun d n z o q c i) = d from by
      simp only [mixFun]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq',
        Fintype.sum_ite_eq']
      omega])

private lemma mixMon_val (d n : ℕ) (z o q : Fin (n + 1)) (c : ℕ) (hc : c ≤ d - 1) (hd : 5 ≤ d)
    (i : Fin (n + 1)) :
    (((mixMon d n z o q c hc hd).1 i : Fin (d + 1)) : ℕ) = mixFun d n z o q c i := rfl

private lemma mixFun_q (d n : ℕ) (z o q : Fin (n + 1)) (c : ℕ) (hzq : z ≠ q) (hoq : o ≠ q) :
    mixFun d n z o q c q = 1 := by
  simp only [mixFun]
  rw [if_neg (Ne.symm hzq), if_neg (Ne.symm hoq)]
  simp

private lemma mixFun_o (d n : ℕ) (z o q : Fin (n + 1)) (c : ℕ) (hzo : z ≠ o) (hoq : o ≠ q) :
    mixFun d n z o q c o = c := by
  simp only [mixFun]
  rw [if_neg (Ne.symm hzo), if_neg hoq]
  simp

/-- `N_{d,n} ≥ n + 6` for `5 ≤ d ≤ n`. -/
theorem NN_ge_add_six (d n : ℕ) (hd : 5 ≤ d) (hdn : d ≤ n) : n + 6 ≤ NN d n := by
  have hn2 : 2 ≤ n := by omega
  let z : Fin (n + 1) := ⟨0, by omega⟩
  let o : Fin (n + 1) := ⟨1, by omega⟩
  let q : Fin (n + 1) := ⟨2, by omega⟩
  have hzo : z ≠ o := by intro h; have := congrArg Fin.val h; simp [z, o] at this
  have hzq : z ≠ q := by intro h; have := congrArg Fin.val h; simp [z, q] at this
  have hoq : o ≠ q := by intro h; have := congrArg Fin.val h; simp [o, q] at this
  let phi : Fin (n + 1) ⊕ Fin 5 → Mon d n := fun s => match s with
    | Sum.inl j => pureMon d n j
    | Sum.inr c => mixMon d n z o q (c : ℕ) (by have := c.isLt; omega) hd
  have hphi_inl : ∀ j, phi (Sum.inl j) = pureMon d n j := fun j => rfl
  have hphi_inr : ∀ c : Fin 5, phi (Sum.inr c)
      = mixMon d n z o q (c : ℕ) (by have := c.isLt; omega) hd := fun c => rfl
  have hinj : Function.Injective phi := by
    intro a b hab
    rcases a with j | c <;> rcases b with j' | c'
    · rw [hphi_inl j, hphi_inl j'] at hab
      rw [Sum.inl.injEq]
      by_contra hj
      have hv := congrArg (fun m : Mon d n => ((m.1 j : Fin (d + 1)) : ℕ)) hab
      rw [pureMon_val, pureMon_val, pureFun_self] at hv
      rw [pureFun_of_ne d n j' j hj] at hv
      omega
    · rw [hphi_inl j, hphi_inr c'] at hab
      exfalso
      have hv := congrArg (fun m : Mon d n => ((m.1 q : Fin (d + 1)) : ℕ)) hab
      rw [pureMon_val, mixMon_val, mixFun_q d n z o q (c' : ℕ) hzq hoq] at hv
      by_cases hqj : q = j
      · rw [show pureFun d n j q = d from by rw [hqj]; exact pureFun_self d n j] at hv
        omega
      · rw [pureFun_of_ne d n j q hqj] at hv
        omega
    · rw [hphi_inr c, hphi_inl j'] at hab
      exfalso
      have hv := congrArg (fun m : Mon d n => ((m.1 q : Fin (d + 1)) : ℕ)) hab
      rw [pureMon_val, mixMon_val, mixFun_q d n z o q (c : ℕ) hzq hoq] at hv
      by_cases hqj : q = j'
      · rw [show pureFun d n j' q = d from by rw [hqj]; exact pureFun_self d n j'] at hv
        omega
      · rw [pureFun_of_ne d n j' q hqj] at hv
        omega
    · rw [hphi_inr c, hphi_inr c'] at hab
      rw [Sum.inr.injEq]
      have hv := congrArg (fun m : Mon d n => ((m.1 o : Fin (d + 1)) : ℕ)) hab
      rw [mixMon_val, mixMon_val, mixFun_o d n z o q (c : ℕ) hzo hoq,
        mixFun_o d n z o q (c' : ℕ) hzo hoq] at hv
      exact Fin.ext hv
  have hcard : Fintype.card (Fin (n + 1) ⊕ Fin 5) = n + 6 := by
    simp [Fintype.card_sum]
  rw [← hcard]
  exact Fintype.card_le_of_injective _ hinj



/-! ## Arithmetic helpers -/

lemma caseI_arith_raw (A B CB C : ℝ) (p : ℝ) (q m : ℕ)
    (hA1 : 1 ≤ A) (hB0 : 0 ≤ B) (hCB : 0 ≤ CB) (hC : 0 ≤ C)
    (hBle : B ≤ CB * A * (Real.log A + 1)) (hq : 2 ≤ q) :
    C * A ^ p * B ^ q * (Real.log A + 1) ^ m
      ≤ C * CB ^ (q - 2) * A ^ (p + ((q - 2 : ℕ) : ℝ)) * B ^ 2
        * (Real.log A + 1) ^ (m + (q - 2)) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hL0 : 0 ≤ Real.log A + 1 := by
    have := Real.log_nonneg hA1
    linarith
  have hBq : B ^ q = B ^ 2 * B ^ (q - 2) := by
    conv_lhs => rw [show q = 2 + (q - 2) from (Nat.add_sub_of_le hq).symm]
    rw [pow_add]
  have hkey : B ^ (q - 2) ≤ CB ^ (q - 2) * A ^ (q - 2) * (Real.log A + 1) ^ (q - 2) := by
    have h := pow_le_pow_left₀ hB0 hBle (q - 2)
    rwa [mul_pow, mul_pow] at h
  have hCAnn : 0 ≤ C * A ^ p * B ^ 2 * (Real.log A + 1) ^ m :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hA0.le p))
      (pow_nonneg hB0 2)) (pow_nonneg hL0 m)
  have h3 : (C * A ^ p * B ^ 2 * (Real.log A + 1) ^ m) *
        (CB ^ (q - 2) * A ^ (q - 2) * (Real.log A + 1) ^ (q - 2))
      = C * CB ^ (q - 2) * A ^ (p + ((q - 2 : ℕ) : ℝ)) * B ^ 2
        * (Real.log A + 1) ^ (m + (q - 2)) := by
    rw [show (C * A ^ p * B ^ 2 * (Real.log A + 1) ^ m) *
          (CB ^ (q - 2) * A ^ (q - 2) * (Real.log A + 1) ^ (q - 2))
        = C * CB ^ (q - 2) * (A ^ p * A ^ (q - 2)) * B ^ 2
          * ((Real.log A + 1) ^ m * (Real.log A + 1) ^ (q - 2)) from by ac_rfl]
    rw [← Real.rpow_natCast A (q - 2), ← Real.rpow_add hA0, ← pow_add]
  calc C * A ^ p * B ^ q * (Real.log A + 1) ^ m
      = (C * A ^ p * B ^ 2 * (Real.log A + 1) ^ m) * B ^ (q - 2) := by
        rw [hBq]; ac_rfl
    _ ≤ (C * A ^ p * B ^ 2 * (Real.log A + 1) ^ m) *
          (CB ^ (q - 2) * A ^ (q - 2) * (Real.log A + 1) ^ (q - 2)) :=
        mul_le_mul_of_nonneg_left hkey hCAnn
    _ = C * CB ^ (q - 2) * A ^ (p + ((q - 2 : ℕ) : ℝ)) * B ^ 2
          * (Real.log A + 1) ^ (m + (q - 2)) := h3

lemma caseI_pow_le_pow_aux (a : ℝ) (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  conv_rhs => rw [← Nat.add_sub_of_le h]
  rw [pow_add]
  exact le_mul_of_one_le_right (pow_nonneg (le_trans zero_le_one ha) m) (one_le_pow₀ ha)

lemma caseI_arith_term (A B CB C : ℝ) (E p : ℝ) (q M m : ℕ) (ε : ℝ)
    (hA1 : 1 ≤ A) (hB0 : 0 ≤ B) (hCB : 0 ≤ CB) (hC : 0 ≤ C) (hε : 0 < ε)
    (hBle : B ≤ CB * A * (Real.log A + 1)) (hq : 2 ≤ q)
    (hL : (Real.log A + 1) ^ M ≤ A ^ ε) (hm : m + (q - 2) ≤ M)
    (hp : p + ((q - 2 : ℕ) : ℝ) ≤ E - ε) :
    C * A ^ p * B ^ q * (Real.log A + 1) ^ m ≤ C * CB ^ (q - 2) * A ^ E * B ^ 2 := by
  have hraw := caseI_arith_raw A B CB C p q m hA1 hB0 hCB hC hBle hq
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hL1 : 1 ≤ Real.log A + 1 := by
    have := Real.log_nonneg hA1
    linarith
  have hL0 : 0 ≤ Real.log A + 1 := le_trans zero_le_one hL1
  have hexp : A ^ (p + ((q - 2 : ℕ) : ℝ)) ≤ A ^ (E - ε) :=
    Real.rpow_le_rpow_of_exponent_le hA1 hp
  have hlog' : (Real.log A + 1) ^ (m + (q - 2)) ≤ A ^ ε :=
    le_trans (caseI_pow_le_pow_aux (Real.log A + 1) hL1 hm) hL
  have hCB0 : 0 ≤ CB ^ (q - 2) := pow_nonneg hCB _
  calc C * A ^ p * B ^ q * (Real.log A + 1) ^ m
      ≤ C * CB ^ (q - 2) * A ^ (p + ((q - 2 : ℕ) : ℝ)) * B ^ 2
          * (Real.log A + 1) ^ (m + (q - 2)) := hraw
    _ ≤ C * CB ^ (q - 2) * A ^ (E - ε) * B ^ 2 * (Real.log A + 1) ^ (m + (q - 2)) := by
        have h1 : (C * CB ^ (q - 2)) * A ^ (p + ((q - 2 : ℕ) : ℝ))
            ≤ (C * CB ^ (q - 2)) * A ^ (E - ε) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hC hCB0)
        have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hB0 2)
        exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hL0 _)
    _ ≤ C * CB ^ (q - 2) * A ^ (E - ε) * B ^ 2 * A ^ ε :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = C * CB ^ (q - 2) * A ^ E * B ^ 2 := by
        rw [show C * CB ^ (q - 2) * A ^ (E - ε) * B ^ 2 * A ^ ε
              = C * CB ^ (q - 2) * (A ^ (E - ε) * A ^ ε) * B ^ 2 from by ring,
          show A ^ (E - ε) * A ^ ε = A ^ E from by
            rw [← Real.rpow_add hA0]; congr 1; ring]

theorem caseI_piece_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (Kpp : ℝ) (hKpp : 0 < Kpp)
    (hpp : ∀ (A B : ℝ) (R : ℕ) (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      d ≤ R → R ≤ NN d n - 3 → 1 ≤ A →
      (∀ p ∈ T, p ∈ Omega d n B) →
      (∀ p ∈ T, A < muXY n p.1 p.2) →
      (∀ p ∈ T, ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))) →
      (∑ p ∈ T, pairS0 d n A p) ≤ Kpp * (A ^ (NN d n - 2 - R) *
            (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * (R - d)) *
              (∑ p ∈ T, (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ))) +
            A ^ (NN d n - 3 - R) * T.card))
    (Kc : ℝ) (hKc : 0 < Kc) (B : ℝ)
    (hcnt : ∀ (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      (∀ p ∈ T, p ∈ Omega d n B) → ∀ Δ : ℝ, 1 ≤ Δ →
      (((T.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card : ℝ))
        ≤ Kc * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ 6 * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2)
    (A Θ₁ Θ₂ CL : ℝ) (R : ℕ)
    (hB0 : 0 ≤ B) (hA1 : 1 ≤ A) (hΘ₁ : 1 ≤ Θ₁) (hΘ₁₂ : Θ₁ ≤ Θ₂) (hCL : 0 < CL)
    (hlog : Real.log (2 * Θ₂) + 1 ≤ CL * (Real.log A + 1))
    (hdR : d ≤ R) (hRn1 : n - 1 ≤ R) (hRN : R ≤ NN d n - 3)
    (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)))
    (hTΩ : ∀ p ∈ T, p ∈ Omega d n B)
    (hTμ : ∀ p ∈ T, A < muXY n p.1 p.2)
    (hTcase : ∀ p ∈ T, ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)))
    (hTlo : ∀ p ∈ T, Θ₁ ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))
    (hThi : ∀ p ∈ T, dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Θ₂) :
    (∑ p ∈ T, pairS0 d n A p) ≤
      Kpp * (16 * Kc * 2 ^ (NN d n) * CL ^ 3 + Kc * CL ^ 2 + 1) *
        (A ^ (NN d n - 2 - R) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * (R - d) + 6) *
            ((Θ₁ ^ (R - (n - 1)))⁻¹) * (Real.log A + 1) ^ 3
          + A ^ (NN d n - 3 - R) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ 6 * Θ₂ ^ (n - 1) *
              (Real.log A + 1) ^ 2) := by
  classical
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
  have hΛ1 : 1 ≤ Θ₂ := le_trans hΘ₁ hΘ₁₂
  have hWnn : (0:ℝ) ≤ W := Real.rpow_nonneg hB0 _
  have hW6nn : (0:ℝ) ≤ Kc * W ^ 6 := mul_nonneg hKc.le (pow_nonneg hWnn 6)
  have hlog2nn : (0:ℝ) ≤ Real.log (2 * Θ₂) := Real.log_nonneg (by linarith)
  have hlogAnn : (0:ℝ) ≤ Real.log A + 1 := by
    have := Real.log_nonneg hA1
    linarith
  have hAnn : (0:ℝ) ≤ A ^ (NN d n - 2 - R) := pow_nonneg (by linarith) _
  have hAnn3 : (0:ℝ) ≤ A ^ (NN d n - 3 - R) := pow_nonneg (by linarith) _
  have hW2nn : (0:ℝ) ≤ W ^ (2 * (R - d)) := pow_nonneg hWnn _
  have h2Nnn : (0:ℝ) ≤ 2 ^ (NN d n) := pow_nonneg (by norm_num) _
  have hCL2 : (0:ℝ) ≤ CL ^ 2 := pow_nonneg hCL.le 2
  have hCL3 : (0:ℝ) ≤ CL ^ 3 := pow_nonneg hCL.le 3
  have hΘ₁0 : (0:ℝ) ≤ Θ₁ := by linarith
  have hΘ₂0 : (0:ℝ) ≤ Θ₂ := by linarith
  have hInv1 : (0:ℝ) ≤ (Θ₁ ^ (R - (n - 1)))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg hΘ₁0 (R - (n - 1)))
  have hΘ₂nn : (0:ℝ) ≤ Θ₂ ^ (n - 1) := pow_nonneg hΘ₂0 (n - 1)
  -- (1) the per-pair sum bound
  have h1 := hpp A B R T hdR hRN hA1 hTΩ hTμ hTcase
  -- (2) the dyadic layer cake
  have h2 := finset_sum_rpow_neg_le T
    (fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) Θ₁ Θ₂ (Kc * W ^ 6) (n - 1) R
    hRn1 hΘ₁ hΛ1 hTlo hThi hW6nn (fun Δ hΔ => hcnt T hTΩ Δ hΔ)
  -- (3) the count of `T` itself
  have h3 : (T.card : ℝ) ≤ Kc * W ^ 6 * Θ₂ ^ (n - 1) * (Real.log (2 * Θ₂)) ^ 2 := by
    have hfilter : T.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Θ₂) = T :=
      Finset.filter_true_of_mem (fun p hp => hThi p hp)
    have h := hcnt T hTΩ Θ₂ hΛ1
    rwa [hfilter] at h
  -- (4) log conversions
  have hlog3 : (Real.log (2 * Θ₂) + 1) ^ 3 ≤ CL ^ 3 * (Real.log A + 1) ^ 3 := by
    have h := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ Real.log (2 * Θ₂) + 1) hlog 3
    rwa [mul_pow] at h
  have hlog2 : (Real.log (2 * Θ₂)) ^ 2 ≤ CL ^ 2 * (Real.log A + 1) ^ 2 := by
    have hle : Real.log (2 * Θ₂) ≤ CL * (Real.log A + 1) := by linarith
    have h := pow_le_pow_left₀ hlog2nn hle 2
    rwa [mul_pow] at h
  -- (5) the two terms
  have h3nR : (2:ℝ) ^ R ≤ 2 ^ (NN d n) := by
    have hle : ((R : ℕ) : ℝ) ≤ ((NN d n : ℕ) : ℝ) := by
      exact_mod_cast (le_trans hRN (Nat.sub_le (NN d n) 3))
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hle
    simpa only [Real.rpow_natCast] using h
  have hL1 : (∑ p ∈ T, (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
      ≤ 16 * Kc * 2 ^ (NN d n) * CL ^ 3 * W ^ 6 * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
          (Real.log A + 1) ^ 3 := by
    refine le_trans h2 ?_
    have hb : (0:ℝ) ≤ 16 * (Kc * W ^ 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) :=
      mul_nonneg (mul_nonneg (by norm_num) hW6nn) hInv1
    have h1 : 2 ^ R * (Real.log (2 * Θ₂) + 1) ^ 3
        ≤ 2 ^ (NN d n) * (CL ^ 3 * (Real.log A + 1) ^ 3) :=
      mul_le_mul h3nR hlog3 (pow_nonneg (by linarith : (0:ℝ) ≤ Real.log (2 * Θ₂) + 1) 3) h2Nnn
    calc 16 * (Kc * W ^ 6) * 2 ^ R * ((Θ₁ ^ (R - (n - 1)))⁻¹) * (Real.log (2 * Θ₂) + 1) ^ 3
        = (16 * (Kc * W ^ 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹)) *
            (2 ^ R * (Real.log (2 * Θ₂) + 1) ^ 3) := by ring
      _ ≤ (16 * (Kc * W ^ 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹)) *
            (2 ^ (NN d n) * (CL ^ 3 * (Real.log A + 1) ^ 3)) :=
          mul_le_mul_of_nonneg_left h1 hb
      _ = 16 * Kc * 2 ^ (NN d n) * CL ^ 3 * W ^ 6 * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
            (Real.log A + 1) ^ 3 := by ring
  have hT1 : A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
      (∑ p ∈ T, (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
      ≤ (16 * Kc * 2 ^ (NN d n) * CL ^ 3) *
          (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
            (Real.log A + 1) ^ 3) := by
    have hA0 : (0:ℝ) ≤ A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) := mul_nonneg hAnn hW2nn
    refine le_trans (mul_le_mul_of_nonneg_left hL1 hA0) (le_of_eq ?_)
    ring
  have hL2 : Kc * W ^ 6 * Θ₂ ^ (n - 1) * (Real.log (2 * Θ₂)) ^ 2
      ≤ Kc * W ^ 6 * (CL ^ 2 * (Real.log A + 1) ^ 2) * Θ₂ ^ (n - 1) := by
    have hb : (0:ℝ) ≤ Kc * W ^ 6 * Θ₂ ^ (n - 1) := mul_nonneg (mul_nonneg hKc.le (pow_nonneg hWnn 6)) hΘ₂nn
    have h1 : (Real.log (2 * Θ₂)) ^ 2 ≤ CL ^ 2 * (Real.log A + 1) ^ 2 := hlog2
    calc Kc * W ^ 6 * Θ₂ ^ (n - 1) * (Real.log (2 * Θ₂)) ^ 2
        = (Kc * W ^ 6 * Θ₂ ^ (n - 1)) * (Real.log (2 * Θ₂)) ^ 2 := by ring
      _ ≤ (Kc * W ^ 6 * Θ₂ ^ (n - 1)) * (CL ^ 2 * (Real.log A + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hb
      _ = Kc * W ^ 6 * (CL ^ 2 * (Real.log A + 1) ^ 2) * Θ₂ ^ (n - 1) := by ring
  have hT2 : A ^ (NN d n - 3 - R) * (T.card : ℝ)
      ≤ (Kc * CL ^ 2) * (A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) *
            (Real.log A + 1) ^ 2) := by
    have hA3 : (0:ℝ) ≤ A ^ (NN d n - 3 - R) := hAnn3
    refine le_trans (mul_le_mul_of_nonneg_left h3 hA3) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hL2 hA3) (le_of_eq ?_)
    ring
  have hsum : (∑ p ∈ T, pairS0 d n A p)
      ≤ Kpp * ((16 * Kc * 2 ^ (NN d n) * CL ^ 3) *
            (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
              (Real.log A + 1) ^ 3)
          + (Kc * CL ^ 2) * (A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) *
              (Real.log A + 1) ^ 2)) := by
    have h := hpp A B R T hdR hRN hA1 hTΩ hTμ hTcase
    have hsm : A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
          (∑ p ∈ T, (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
        + A ^ (NN d n - 3 - R) * (T.card : ℝ)
        ≤ (16 * Kc * 2 ^ (NN d n) * CL ^ 3) *
            (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
              (Real.log A + 1) ^ 3)
          + (Kc * CL ^ 2) * (A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) *
              (Real.log A + 1) ^ 2) := add_le_add hT1 hT2
    exact le_trans h (mul_le_mul_of_nonneg_left hsm hKpp.le)
  have hgoal : Kpp * ((16 * Kc * 2 ^ (NN d n) * CL ^ 3) *
            (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
              (Real.log A + 1) ^ 3)
          + (Kc * CL ^ 2) * (A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) *
              (Real.log A + 1) ^ 2))
      ≤ Kpp * (16 * Kc * 2 ^ (NN d n) * CL ^ 3 + Kc * CL ^ 2 + 1) *
        (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) *
            ((Θ₁ ^ (R - (n - 1)))⁻¹) * (Real.log A + 1) ^ 3
          + A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) * (Real.log A + 1) ^ 2) := by
    have hU : (0:ℝ) ≤ A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) *
        ((Θ₁ ^ (R - (n - 1)))⁻¹) * (Real.log A + 1) ^ 3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hAnn (pow_nonneg hWnn _)) hInv1)
        (pow_nonneg hlogAnn 3)
    have hV : (0:ℝ) ≤ A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) *
        (Real.log A + 1) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hAnn3 (pow_nonneg hWnn 6)) hΘ₂nn)
        (pow_nonneg hlogAnn 2)
    have hC : (0:ℝ) ≤ 16 * Kc * 2 ^ (NN d n) * CL ^ 3 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKc.le) h2Nnn) hCL3
    have hC2 : (0:ℝ) ≤ Kc * CL ^ 2 := mul_nonneg hKc.le hCL2
    have h3 : (16 * Kc * 2 ^ (NN d n) * CL ^ 3) *
          (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
            (Real.log A + 1) ^ 3)
        + (Kc * CL ^ 2) * (A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) *
            (Real.log A + 1) ^ 2)
        ≤ (16 * Kc * 2 ^ (NN d n) * CL ^ 3 + Kc * CL ^ 2 + 1) *
          (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d) + 6) * ((Θ₁ ^ (R - (n - 1)))⁻¹) *
              (Real.log A + 1) ^ 3
            + A ^ (NN d n - 3 - R) * W ^ 6 * Θ₂ ^ (n - 1) * (Real.log A + 1) ^ 2) := by
      nlinarith [hU, hV, hC, hC2]
    refine le_trans (mul_le_mul_of_nonneg_left h3 hKpp.le) (le_of_eq ?_)
    ring
  exact le_trans hsum hgoal


private lemma inv_pow_eq_rpow (A : ℝ) (hA : 0 < A) (k : ℕ) : (A ^ k)⁻¹ = A ^ (-(k : ℝ)) := by
  rw [← Real.rpow_natCast A k, ← Real.rpow_neg hA.le]

private lemma hlog_rpow_le (A : ℝ) (hA1 : 1 ≤ A) (c : ℝ) (hc : c ≤ 1) (CL : ℝ)
    (hcl : Real.log 2 + 2 ≤ CL) : Real.log (2 * A ^ c) + 1 ≤ CL * (Real.log A + 1) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hlogAnn : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hlogA1 : 1 ≤ Real.log A + 1 := by linarith
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hApos c).ne', Real.log_rpow hApos]
  have h1 : c * Real.log A ≤ Real.log A := by nlinarith [hlogAnn, hc]
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : Real.log 2 + c * Real.log A + 1 ≤ (Real.log 2 + 2) * (Real.log A + 1) := by
    nlinarith [h1, hlogAnn, hlog2nn]
  exact le_trans h2 (by nlinarith [hlogA1, hcl])

private lemma hlog_dmax (n : ℕ) (hn1 : 1 ≤ n) (A B CB : ℝ) (s : ℝ)
    (hA1 : 1 ≤ A) (hBpos : 0 < B) (hCB1 : 1 ≤ CB) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hBle : B ≤ CB * A * (Real.log A + 1)) :
    Real.log (2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A)) + 1
      ≤ (Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + 4) * (Real.log A + 1) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hCBpos : 0 < CB := lt_of_lt_of_le zero_lt_one hCB1
  have hLpos : 0 < Real.log A + 1 := by
    have := Real.log_nonneg hA1
    linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hloglog : Real.log (Real.log A + 1) ≤ Real.log A := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hBs : B ^ s ≤ CB * A * (Real.log A + 1) := by
    have hCAL1 : 1 ≤ CB * A * (Real.log A + 1) := by
      have h1 : 1 ≤ CB * A := by nlinarith [hCB1, hA1]
      have h2 : (1:ℝ) ≤ Real.log A + 1 := by linarith
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (CB * A) * (Real.log A + 1) := mul_le_mul h1 h2 zero_le_one (by linarith)
    calc B ^ s ≤ (CB * A * (Real.log A + 1)) ^ s := Real.rpow_le_rpow hBpos.le hBle hs
      _ ≤ (CB * A * (Real.log A + 1)) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hCAL1 hs1
      _ = CB * A * (Real.log A + 1) := Real.rpow_one _
  have hPpos : 0 < 2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A) := by positivity
  have hPle : 2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A)
      ≤ 6 * (n : ℝ) ^ 2 * CB ^ 2 * A * (Real.log A + 1) ^ 2 := by
    have hsq : (B ^ s) ^ 2 ≤ (CB * A * (Real.log A + 1)) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hBpos.le s) hBs 2
    have h6 : 0 ≤ 6 * (n : ℝ) ^ 2 / A := by positivity
    calc 2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A)
        = (6 * (n : ℝ) ^ 2 / A) * (B ^ s) ^ 2 := by ring
      _ ≤ (6 * (n : ℝ) ^ 2 / A) * (CB * A * (Real.log A + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq h6
      _ = 6 * (n : ℝ) ^ 2 * CB ^ 2 * A * (Real.log A + 1) ^ 2 := by
          field_simp
  have hlogP1 : Real.log (2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A))
      ≤ Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2 * A * (Real.log A + 1) ^ 2) :=
    Real.log_le_log hPpos hPle
  have hlogP2 : Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2 * A * (Real.log A + 1) ^ 2)
      = Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + Real.log A + 2 * Real.log (Real.log A + 1) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  have hlogP : Real.log (2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A))
      ≤ Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + 3 * Real.log A := by
    refine le_trans hlogP1 ?_
    rw [hlogP2]
    linarith
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hsq1 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hn1'
  have hsq2 : (1:ℝ) ≤ CB^2 := one_le_pow₀ hCB1
  have h6n : (1:ℝ) ≤ 6 * (n:ℝ)^2 * CB^2 := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (6 * (n:ℝ)^2) * CB^2 :=
          mul_le_mul (by nlinarith [hsq1]) hsq2 zero_le_one (by nlinarith [hsq1])
  have hXnn : 0 ≤ Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) := Real.log_nonneg h6n
  have hfin : Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + 3 * Real.log A + 1
      ≤ (Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + 4) * (Real.log A + 1) := by
    nlinarith [hlogA, hXnn]
  have hstep : Real.log (2 * (3 * (n : ℝ) ^ 2 * (B ^ s) ^ 2 / A)) + 1
      ≤ Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + 3 * Real.log A + 1 := by linarith [hlogP]
  exact le_trans hstep hfin

set_option maxHeartbeats 16000000 in
theorem caseI_main (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn3 : 3 ≤ n)
    (h22 : (d, n) ≠ (2, 2)) (h33 : (d, n) ≠ (3, 3)) (h44 : (d, n) ≠ (4, 4))
    (Kpp : ℝ) (hKpppos : 0 < Kpp)
    (hpp : ∀ (A B : ℝ) (R : ℕ) (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      d ≤ R → R ≤ NN d n - 3 → 1 ≤ A →
      (∀ p ∈ T, p ∈ Omega d n B) → (∀ p ∈ T, A < muXY n p.1 p.2) →
      (∀ p ∈ T, ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))) →
      (∑ p ∈ T, pairS0 d n A p) ≤ Kpp * (A ^ (NN d n - 2 - R) *
            (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * (R - d)) *
              (∑ p ∈ T, (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ))) +
            A ^ (NN d n - 3 - R) * T.card))
    (Kc : ℝ) (hKcpos : 0 < Kc)
    (hcnt0 : ∀ (B Δ : ℝ), 1 ≤ B → 1 ≤ Δ →
      (({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ}.ncard : ℝ))
        ≤ Kc * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ 6 * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          ¬ (muXY n p.1 p.2 ≤ A) ∧
          ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
            ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))},
        pairS0 d n A p)
        ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  classical
  obtain ⟨A₀l, hA₀l1, hA₀l⟩ := log_pow_le_rpow (2 * n + 4) (1 / 6) (by norm_num)
  obtain ⟨CB₀, hCB₀pos, hCB₀le⟩ := le_mul_log_of_div_log_le 16 (by norm_num)
  set CB : ℝ := max CB₀ 1 with hCBdef
  have hCB1 : (1 : ℝ) ≤ CB := le_max_right _ _
  have hCBpos : 0 < CB := lt_of_lt_of_le zero_lt_one hCB1
  have hCBle : ∀ A B : ℝ, 16 ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      B ≤ CB * A * (Real.log A + 1) := by
    intro A B h16 hAB hAB2
    have h1 := hCB₀le A B h16 hAB hAB2
    have h2 : CB₀ ≤ CB := le_max_left _ _
    have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
    have hA1 : (1 : ℝ) ≤ A := by
      have h0 : (1 : ℝ) ≤ B / Real.log B := by
        rw [le_div_iff₀ hlogBpos]
        have := Real.log_le_self (by linarith : (0:ℝ) ≤ B)
        linarith
      linarith
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
    have hLnn : (0 : ℝ) ≤ Real.log A + 1 := by linarith
    have h4 : CB₀ * A * (Real.log A + 1) ≤ CB * A * (Real.log A + 1) := by
      apply mul_le_mul_of_nonneg_right _ hLnn
      exact mul_le_mul_of_nonneg_right h2 (by linarith)
    linarith [h1, h4]
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn1 : 1 ≤ n := by omega
  set CL : ℝ := Real.log (6 * (n : ℝ) ^ 2 * CB ^ 2) + 4 with hCLdef
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsq1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1'
  have hsq2 : (1 : ℝ) ≤ CB ^ 2 := one_le_pow₀ hCB1
  have h6n : (1 : ℝ) ≤ 6 * (n : ℝ) ^ 2 * CB ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (6 * (n : ℝ) ^ 2) * CB ^ 2 :=
          mul_le_mul (by nlinarith [hsq1]) hsq2 zero_le_one (by nlinarith [hsq1])
  have hCLpos : 0 < CL := by rw [hCLdef]; linarith [Real.log_nonneg h6n]
  have h6n2 : (2 : ℝ) ≤ 6 * (n : ℝ) ^ 2 * CB ^ 2 := by
    have hA : (6 : ℝ) * 1 ≤ 6 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq1 (by norm_num : (0 : ℝ) ≤ 6)
    have hB : 6 * (n : ℝ) ^ 2 * 1 ≤ 6 * (n : ℝ) ^ 2 * CB ^ 2 :=
      mul_le_mul_of_nonneg_left hsq2 (by positivity)
    linarith
  have hlog2CL : Real.log 2 + 2 ≤ CL := by
    rw [hCLdef]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h6n2
    linarith
  set Kbase : ℝ := Kpp * (16 * Kc * 2 ^ (NN d n) * CL ^ 3 + Kc * CL ^ 2 + 1) with hKbasedef
  have hKbasepos : 0 < Kbase := by
    rw [hKbasedef]
    have : (0 : ℝ) < 16 * Kc * 2 ^ (NN d n) * CL ^ 3 + Kc * CL ^ 2 + 1 := by positivity
    positivity
  set Kterm : ℝ := Kbase * ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) with hKtermdef
  have hKtermpos : 0 < Kterm := by
    rw [hKtermdef]
    have : (0 : ℝ) < (3 * (n : ℝ) ^ 2) ^ (n - 1) + 1 := by positivity
    have : (0 : ℝ) < 1 + 10 * CB ^ (2 * n + 2) := by positivity
    positivity
  set KK : ℝ := 10 * Kterm with hKKdef
  have hKKpos : 0 < KK := by rw [hKKdef]; linarith
  refine ⟨KK, max 16 (max (4 * A₀l ^ 2 + 4) ((18 * (n : ℝ) ^ 2) ^ 6 + 4)), hKKpos, ?_⟩
  intro A B hB hAB hAB2
  have hB16 : 16 ≤ B := le_trans (le_max_left _ _) hB
  have hBmax2 : 4 * A₀l ^ 2 + 4 ≤ B :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hBmax3 : (18 * (n : ℝ) ^ 2) ^ 6 + 4 ≤ B :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hBpos : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      have h := Real.log_le_self (le_of_lt hBpos)
      linarith
    linarith
  have hApos : 0 < A := by linarith
  have hlogAnn : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hL1 : 1 ≤ Real.log A + 1 := by
    have := Real.log_nonneg hA1
    linarith
  have hA₀le : A₀l ≤ A := by
    have hlogle : Real.log B ≤ 2 * B ^ ((1 : ℝ) / 2) := by
      have h := Real.log_le_rpow_div (le_of_lt hBpos) (by norm_num : (0 : ℝ) < 1 / 2)
      have h2 : B ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 2 * B ^ ((1 : ℝ) / 2) := by ring
      linarith [h, h2]
    have hA₀l2 : A₀l ^ 2 ≤ B / 4 := by linarith
    have hA₀lnn : 0 ≤ A₀l := by linarith [hA₀l1]
    have h2A : 2 * A₀l ≤ B ^ ((1 : ℝ) / 2) := by
      have hsq : (2 * A₀l) ^ 2 ≤ B := by nlinarith [hA₀l2, hA₀lnn]
      have h := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ 2 * A₀l by linarith)] at h
      rwa [Real.sqrt_eq_rpow] at h
    have hbl : A₀l ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      calc A₀l * Real.log B ≤ A₀l * (2 * B ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hlogle hA₀lnn
      _ = (2 * A₀l) * B ^ ((1 : ℝ) / 2) := by ring
      _ ≤ B ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h2A (Real.rpow_nonneg hBpos.le _)
      _ = B ^ (1 : ℝ) := by rw [← Real.rpow_add hBpos]; norm_num
      _ = B := Real.rpow_one B
    exact le_trans hbl hAB
  have hAlog : (Real.log A + 1) ^ (2 * n + 4) ≤ A ^ ((1 : ℝ) / 6) := hA₀l A hA₀le
  have hBleCB : B ≤ CB * A * (Real.log A + 1) := hCBle A B hB16 hAB hAB2
  have h18 : 18 * (n : ℝ) ^ 2 ≤ B ^ ((1 : ℝ) / 6) := by
    have h0 : (0 : ℝ) ≤ 18 * (n : ℝ) ^ 2 := by positivity
    have hbase : (18 * (n : ℝ) ^ 2) ^ 6 ≤ B := by linarith
    have hb : ((18 * (n : ℝ) ^ 2) ^ 6) ^ ((1 : ℝ) / 6) = 18 * (n : ℝ) ^ 2 := by
      have h1 : ((18 * (n : ℝ) ^ 2) ^ 6) ^ ((1 : ℝ) / 6)
          = ((18 * (n : ℝ) ^ 2) ^ ((6 : ℕ) : ℝ)) ^ ((1 : ℝ) / 6) := by
        rw [Real.rpow_natCast]
      rw [h1, ← Real.rpow_mul h0]
      rw [show ((6 : ℕ) : ℝ) * ((1 : ℝ) / 6) = 1 by norm_num, Real.rpow_one]
    have hc : ((18 * (n : ℝ) ^ 2) ^ 6) ^ ((1 : ℝ) / 6) ≤ B ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow (pow_nonneg h0 6) hbase (by norm_num)
    rwa [hb] at hc
  -- the summation set and its Finset
  set S : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A) ∧
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))} with hSdef
  have hSfin : S.Finite :=
    ((MDBasic.finite_sets d n A B (fun _ => True)).2.2).subset (fun p hp => hp.1)
  set T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := hSfin.toFinset with hTdef
  have hTmem : ∀ p, p ∈ T ↔ p ∈ S := fun p => Set.Finite.mem_toFinset hSfin
  have hsum_eq : (∑ᶠ p ∈ S, pairS0 d n A p) = ∑ p ∈ T, pairS0 d n A p := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, hTdef]
  change (∑ᶠ p ∈ S, pairS0 d n A p) ≤ KK * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2
  rw [hsum_eq]
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
  have hW0 : 0 ≤ W := Real.rpow_nonneg hBpos.le _
  -- Finset counting bound from the hypothesis
  have hcntT : ∀ (T' : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      (∀ p ∈ T', p ∈ Omega d n B) → ∀ Δ : ℝ, 1 ≤ Δ →
      ((T'.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card : ℝ)
        ≤ Kc * W ^ 6 * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2 := by
    intro T' hT' Δ hΔ
    set F : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
      T'.filter (fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ) with hF
    set S' : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
      {p | p ∈ Omega d n B ∧ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ} with hS'def
    have hS'fin : S'.Finite :=
      ((MDBasic.finite_sets d n B B (fun _ => True)).2.2).subset (fun p hp => hp.1)
    have hsub : (↑F : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))) ⊆ S' := by
      intro p hp
      rw [Finset.mem_coe, hF, Finset.mem_filter] at hp
      exact ⟨hT' p hp.1, hp.2⟩
    have h1 : (F : Set _).ncard ≤ S'.ncard := Set.ncard_le_ncard hsub hS'fin
    have h2 : F.card ≤ S'.ncard := by rw [← Set.ncard_coe_finset F]; exact h1
    have h2' : (F.card : ℝ) ≤ (S'.ncard : ℝ) := by exact_mod_cast h2
    refine le_trans h2' ?_
    rw [hS'def]
    simpa [hWdef] using hcnt0 B Δ hB1 hΔ
  -- structural facts about `T`
  have hTΩ : ∀ p ∈ T, p ∈ Omega d n B := fun p hp => ((hTmem p).mp hp).1
  have hTμ : ∀ p ∈ T, A < muXY n p.1 p.2 := fun p hp => lt_of_not_ge ((hTmem p).mp hp).2.1
  have hTcase : ∀ p ∈ T, ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
      dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
      ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)) :=
    fun p hp => ((hTmem p).mp hp).2.2
  have hTd3ge1 : ∀ p ∈ T, 1 ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := by
    intro p hp
    exact (MDEstimates.dmin_facts n hn2).2.2.1 p.1 p.2 (li_of_mem_Omega d n B p (hTΩ p hp))
  have hTd3lt : ∀ p ∈ T, dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) < 3 * (n : ℝ) ^ 2 * W ^ 2 / A := by
    intro p hp
    have hΩ := hTΩ p hp
    have hLI := li_of_mem_Omega d n B p hΩ
    have hdf := MDEstimates.dmin_facts n hn2
    have hle := d3_lt_of_caseI n p.1 p.2 A
      (lt_of_lt_of_le zero_lt_one (hdf.1 p.1 p.2 hLI))
      (lt_of_lt_of_le zero_lt_one (hdf.2.2.1 p.1 p.2 hLI))
      (hdf.2.1 p.1 p.2 hLI) hApos (hTμ p hp) (hTcase p hp)
    have hXY : eNorm p.1 * eNorm p.2 ≤ W ^ 2 := by
      have h1 : eNorm p.1 ≤ W := hΩ.1.2
      have h2 : eNorm p.2 ≤ W := hΩ.2.1.2
      nlinarith [eNorm_nonneg p.1, eNorm_nonneg p.2, hW0, h1, h2]
    calc dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
        < 3 * (n : ℝ) ^ 2 * (eNorm p.1 * eNorm p.2) / A := hle
      _ ≤ 3 * (n : ℝ) ^ 2 * W ^ 2 / A := by
          apply div_le_div_of_nonneg_right _ hApos.le
          exact mul_le_mul_of_nonneg_left hXY (by positivity)
  -- the arithmetic engine
  have arithT : ∀ (C p : ℝ) (q m : ℕ), 0 ≤ C → 2 ≤ q → m + (q - 2) ≤ 2 * n + 4 →
      p + ((q - 2 : ℕ) : ℝ) ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 →
      C * A ^ p * B ^ q * (Real.log A + 1) ^ m
        ≤ C * CB ^ (q - 2) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
    fun C p q m hC hq hm hp =>
      caseI_arith_term A B CB C ((NN d n : ℝ) - 7 / 3) p q (2 * n + 4) m (1 / 6)
        hA1 hBpos.le hCBpos.le hC (by norm_num) hBleCB hq hAlog hm hp
  have hEeq : (NN d n : ℝ) - 2 - (1 : ℝ) / 3 = (NN d n : ℝ) - 7 / 3 := by ring
  have hcast2 : ∀ R : ℕ, R ≤ NN d n - 3 →
      ((NN d n - 2 - R : ℕ) : ℝ) = (NN d n : ℝ) - 2 - R := by
    intro R hR
    have h1 : R ≤ NN d n - 2 := by omega
    have h2 : 2 ≤ NN d n := by have := six_le_NN d n hd hdn; omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    norm_num
  have hcast3 : ∀ R : ℕ, R ≤ NN d n - 3 →
      ((NN d n - 3 - R : ℕ) : ℝ) = (NN d n : ℝ) - 3 - R := by
    intro R hR
    have h2 : 3 ≤ NN d n := by have := six_le_NN d n hd hdn; omega
    rw [Nat.cast_sub hR, Nat.cast_sub h2]
    norm_num
  have hthpow : ∀ (c : ℝ) (k : ℕ), (A ^ c) ^ k = A ^ (c * k) := by
    intro c k
    rw [← Real.rpow_natCast (A ^ c) k, Real.rpow_mul hApos.le]
  have hthinv : ∀ (c : ℝ) (k : ℕ), ((A ^ c) ^ k)⁻¹ = A ^ (-(c * k)) := by
    intro c k
    rw [hthpow c k, ← Real.rpow_neg hApos.le (c * k)]
  have hshift : ∀ (P : ℕ) (r : ℝ) (q m : ℕ) (C : ℝ), 0 ≤ C → 2 ≤ q → m + (q - 2) ≤ 2 * n + 4 →
      ((P : ℕ) : ℝ) + r + ((q - 2 : ℕ) : ℝ) ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 →
      C * (A ^ P * A ^ r) * B ^ q * (Real.log A + 1) ^ m
        ≤ C * CB ^ (q - 2) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
    intro P r q m C hC hq hm hp
    rw [← Real.rpow_natCast A P, ← Real.rpow_add hApos]
    exact arithT C (((P : ℕ) : ℝ) + r) q m hC hq hm hp
  -- coefficient absorption
  have h31 : (1 : ℝ) ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) + 1 := by
    have : (0 : ℝ) ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) := by positivity
    linarith
  have h31pos : (0 : ℝ) < (3 * (n : ℝ) ^ 2) ^ (n - 1) + 1 := by linarith
  have h10 : ∀ q : ℕ, 2 ≤ q → q - 2 ≤ 2 * n + 2 → CB ^ (q - 2) ≤ 1 + 10 * CB ^ (2 * n + 2) := by
    intro q hq hq2
    have hCBq : CB ^ (q - 2) ≤ CB ^ (2 * n + 2) := caseI_pow_le_pow_aux CB hCB1 hq2
    have hnn : (0 : ℝ) ≤ CB ^ (2 * n + 2) := pow_nonneg hCBpos.le _
    linarith
  have habs1 : ∀ q : ℕ, 2 ≤ q → q - 2 ≤ 2 * n + 2 →
      (1 : ℝ) * CB ^ (q - 2) ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by
    intro q hq hq2
    refine le_trans (by simpa using h10 q hq hq2) ?_
    exact le_mul_of_one_le_left (by positivity) h31
  have habs2 : ∀ q : ℕ, 2 ≤ q → q - 2 ≤ 2 * n + 2 →
      (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (q - 2)
        ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by
    intro q hq hq2
    have h1 : (0 : ℝ) ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) := by positivity
    have h2 := h10 q hq hq2
    have h3 : (0 : ℝ) ≤ 1 + 10 * CB ^ (2 * n + 2) := by positivity
    calc (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (q - 2)
        ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) * (1 + 10 * CB ^ (2 * n + 2)) :=
          mul_le_mul_of_nonneg_left h2 h1
      _ ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) h3
  have hKq : ∀ q : ℕ, 2 ≤ q → q - 2 ≤ 2 * n + 2 → Kbase * CB ^ (q - 2) ≤ Kterm := by
    intro q hq hq2
    have h10' : CB ^ (q - 2) ≤ 1 + 10 * CB ^ (2 * n + 2) := h10 q hq hq2
    calc Kbase * CB ^ (q - 2) ≤ Kbase * (1 + 10 * CB ^ (2 * n + 2)) :=
          mul_le_mul_of_nonneg_left h10' hKbasepos.le
      _ ≤ Kbase * ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by
          calc Kbase * (1 + 10 * CB ^ (2 * n + 2))
              ≤ Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))) :=
                mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) h31) hKbasepos.le
            _ = Kbase * ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by
                ac_rfl
      _ = Kterm := by rw [hKtermdef]
  have hKq2 : Kbase * (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2) ≤ Kterm := by
    have h1 : (0 : ℝ) ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) := by positivity
    have h2 : (0 : ℝ) ≤ CB ^ (2 * n + 2) := by positivity
    have h4 : (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)
        ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by
      calc (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)
          ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) * (1 + 10 * CB ^ (2 * n + 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) h1
        _ ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    calc Kbase * (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)
        = Kbase * ((3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)) := by ring
      _ ≤ Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))) :=
          mul_le_mul_of_nonneg_left h4 hKbasepos.le
      _ = Kbase * ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by ring
      _ = Kterm := by rw [hKtermdef]
  have kmul : ∀ (t : ℝ) (q : ℕ), 2 ≤ q → q - 2 ≤ 2 * n + 2 →
      t ≤ CB ^ (q - 2) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 →
      Kbase * t ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
    intro t q hq hq2 ht
    have hnn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by positivity
    calc Kbase * t ≤ Kbase * (CB ^ (q - 2) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKbasepos.le
          calc t ≤ CB ^ (q - 2) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := ht
            _ = CB ^ (q - 2) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
      _ = (Kbase * CB ^ (q - 2)) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
      _ ≤ Kterm * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
          mul_le_mul_of_nonneg_right (hKq q hq hq2) hnn
      _ = Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := (mul_assoc Kterm _ _).symm
  have key : ∀ (C : ℝ) (P : ℕ) (r : ℝ) (q m : ℕ), 0 ≤ C → 2 ≤ q → q - 2 ≤ 2 * n + 2 →
      m + (q - 2) ≤ 2 * n + 4 →
      ((P : ℕ) : ℝ) + r + ((q - 2 : ℕ) : ℝ) ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 →
      C * CB ^ (q - 2) ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) →
      Kbase * (C * (A ^ P * A ^ r) * B ^ q * (Real.log A + 1) ^ m)
        ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
    intro C P r q m hC hq hq2 hm hp hCabs
    have h1 : C * (A ^ P * A ^ r) * B ^ q * (Real.log A + 1) ^ m
        ≤ C * CB ^ (q - 2) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have h := arithT C (((P : ℕ) : ℝ) + r) q m hC hq hm hp
      rw [← Real.rpow_natCast A P, ← Real.rpow_add hApos]
      exact h
    calc Kbase * (C * (A ^ P * A ^ r) * B ^ q * (Real.log A + 1) ^ m)
        ≤ Kbase * (C * CB ^ (q - 2) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hKbasepos.le
      _ = (Kbase * (C * CB ^ (q - 2))) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
      _ ≤ (Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))))
            * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCabs hKbasepos.le) (by positivity)
      _ = (Kterm) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by rw [hKtermdef]; ac_rfl
      _ = Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := (mul_assoc Kterm _ _).symm

  rcases (by omega : n = d ∨ n = d + 1 ∨ d + 2 ≤ n) with hnd | hnd | hnd
  · -- ==================== n = d ====================
    have hd5 : 5 ≤ d := by
      rcases Nat.lt_or_ge d 5 with hlt | hge
      · have hd234 : d = 2 ∨ d = 3 ∨ d = 4 := by omega
        rcases hd234 with h | h | h
        · exact absurd (by rw [hnd, h]) h22
        · exact absurd (by rw [hnd, h]) h33
        · exact absurd (by rw [hnd, h]) h44
      · exact hge
    have hn5R : (5 : ℝ) ≤ (n : ℝ) := by
      have : 5 ≤ n := by omega
      exact_mod_cast this
    have hWdB : W = B := by
      rw [hWdef]
      have h1 : 1 / ((n : ℝ) + 1 - d) = 1 := by rw [hnd]; ring_nf
      rw [h1, Real.rpow_one]
    have hWB : B ^ (1 / ((n : ℝ) + 1 - d)) = B := by
      have h1 : 1 / ((n : ℝ) + 1 - d) = 1 := by rw [hnd]; ring_nf
      rw [h1, Real.rpow_one]
    have hN6 : n + 6 ≤ NN d n := NN_ge_add_six d n (by omega) hdn
    have hRN1 : n ≤ NN d n - 3 := by omega
    have hRN2 : n + 1 ≤ NN d n - 3 := by omega
    have hRN3 : n + 2 ≤ NN d n - 3 := by omega
    have hRN4 : n + 3 ≤ NN d n - 3 := by omega
    set th1 : ℝ := A ^ ((1 : ℝ) / 4) with hth1def
    set th2 : ℝ := A ^ ((1 : ℝ) / 2) with hth2def
    set th3 : ℝ := A ^ ((3 : ℝ) / 4) with hth3def
    have hth1ge : (1 : ℝ) ≤ th1 := Real.one_le_rpow hA1 (by norm_num)
    have hth12 : th1 ≤ th2 := by
      rw [hth1def, hth2def]; exact Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
    have hth23 : th2 ≤ th3 := by
      rw [hth2def, hth3def]; exact Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
    have hth13 : th1 ≤ th3 := le_trans hth12 hth23
    set Dmax : ℝ := 3 * (n : ℝ) ^ 2 * W ^ 2 / A with hDmaxdef
    have hlog1 : Real.log (2 * (1 : ℝ)) + 1 ≤ CL * (Real.log A + 1) := by
      rw [mul_one]
      have h2 : Real.log 2 + 1 ≤ (Real.log 2 + 2) * (Real.log A + 1) := by
        nlinarith [hL1, hlogAnn, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
      have h3 : (Real.log 2 + 2) * (Real.log A + 1) ≤ CL * (Real.log A + 1) :=
        mul_le_mul_of_nonneg_right hlog2CL (by linarith)
      exact le_trans h2 h3
    have hlogq : ∀ c : ℝ, c ≤ 1 → Real.log (2 * A ^ c) + 1 ≤ CL * (Real.log A + 1) :=
      fun c hc => hlog_rpow_le A hA1 c hc CL hlog2CL
    set P1 : ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) → Prop :=
      fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ th1 with hP1def
    set T1 : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := T.filter P1 with hT1def
    set U1 : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := T.filter (fun p => ¬ P1 p) with hU1def
    set P2 : ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) → Prop :=
      fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ th2 with hP2def
    set T2 : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := U1.filter P2 with hT2def
    set U2 : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := U1.filter (fun p => ¬ P2 p) with hU2def
    set P3 : ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) → Prop :=
      fun p => dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ th3 with hP3def
    set T3 : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := U2.filter P3 with hT3def
    set T4 : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := U2.filter (fun p => ¬ P3 p) with hT4def
    have hsplit1 : (∑ p ∈ T, pairS0 d n A p)
        = (∑ p ∈ T1, pairS0 d n A p) + (∑ p ∈ U1, pairS0 d n A p) := by
      rw [hT1def, hU1def]
      exact (Finset.sum_filter_add_sum_filter_not T P1 (fun p => pairS0 d n A p)).symm
    have hsplit2 : (∑ p ∈ U1, pairS0 d n A p)
        = (∑ p ∈ T2, pairS0 d n A p) + (∑ p ∈ U2, pairS0 d n A p) := by
      rw [hT2def, hU2def]
      exact (Finset.sum_filter_add_sum_filter_not U1 P2 (fun p => pairS0 d n A p)).symm
    have hsplit3 : (∑ p ∈ U2, pairS0 d n A p)
        = (∑ p ∈ T3, pairS0 d n A p) + (∑ p ∈ T4, pairS0 d n A p) := by
      rw [hT3def, hT4def]
      exact (Finset.sum_filter_add_sum_filter_not U2 P3 (fun p => pairS0 d n A p)).symm
    have sT1 : ∀ p ∈ T1, p ∈ T := by intro p hp; rw [hT1def] at hp; exact (Finset.mem_filter.mp hp).1
    have sU1 : ∀ p ∈ U1, p ∈ T := by intro p hp; rw [hU1def] at hp; exact (Finset.mem_filter.mp hp).1
    have sT2 : ∀ p ∈ T2, p ∈ T := by intro p hp; rw [hT2def] at hp; exact sU1 p (Finset.mem_filter.mp hp).1
    have sU2 : ∀ p ∈ U2, p ∈ T := by intro p hp; rw [hU2def] at hp; exact sU1 p (Finset.mem_filter.mp hp).1
    have sT3 : ∀ p ∈ T3, p ∈ T := by intro p hp; rw [hT3def] at hp; exact sU2 p (Finset.mem_filter.mp hp).1
    have sT4 : ∀ p ∈ T4, p ∈ T := by intro p hp; rw [hT4def] at hp; exact sU2 p (Finset.mem_filter.mp hp).1
    have mT1 : ∀ p ∈ T1, P1 p := by intro p hp; rw [hT1def] at hp; exact (Finset.mem_filter.mp hp).2
    have mU1 : ∀ p ∈ U1, ¬ P1 p := by intro p hp; rw [hU1def] at hp; exact (Finset.mem_filter.mp hp).2
    have mT2 : ∀ p ∈ T2, P2 p := by intro p hp; rw [hT2def] at hp; exact (Finset.mem_filter.mp hp).2
    have mU2 : ∀ p ∈ U2, ¬ P2 p := by intro p hp; rw [hU2def] at hp; exact (Finset.mem_filter.mp hp).2
    have mT3 : ∀ p ∈ T3, P3 p := by intro p hp; rw [hT3def] at hp; exact (Finset.mem_filter.mp hp).2
    have mT4 : ∀ p ∈ T4, ¬ P3 p := by intro p hp; rw [hT4def] at hp; exact (Finset.mem_filter.mp hp).2
    have mem1 : ∀ p, p ∈ T2 → p ∈ U1 := by intro p hp; rw [hT2def] at hp; exact (Finset.mem_filter.mp hp).1
    have mem2 : ∀ p, p ∈ T3 → p ∈ U2 := by intro p hp; rw [hT3def] at hp; exact (Finset.mem_filter.mp hp).1
    have ml1 : ∀ p ∈ U1, th1 ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := by
      intro p hp
      have h := mU1 p hp
      rw [hP1def] at h
      rw [hth1def]
      exact le_of_lt (lt_of_not_ge h)
    have ml2 : ∀ p ∈ U2, th2 ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := by
      intro p hp
      have h := mU2 p hp
      rw [hP2def] at h
      rw [hth2def]
      exact le_of_lt (lt_of_not_ge h)
    have ml3 : ∀ p ∈ T4, th3 ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := by
      intro p hp
      have h := mT4 p hp
      rw [hP3def] at h
      rw [hth3def]
      exact le_of_lt (lt_of_not_ge h)
    have hpair1 : (∑ p ∈ T1, pairS0 d n A p) ≤
        Kbase * (A ^ (NN d n - 2 - n) * B ^ 6 * (Real.log A + 1) ^ 3
          + A ^ (NN d n - 3 - n) * B ^ 6 * th1 ^ (n - 1) * (Real.log A + 1) ^ 2) := by
      have hraw := caseI_piece_bound d n hd hdn Kpp hKpppos hpp Kc hKcpos B hcntT A 1 th1 CL n
        (le_of_lt hBpos) hA1 (le_refl 1) hth1ge hCLpos
        (by rw [hth1def]; exact hlogq (1 / 4) (by norm_num)) (by omega) (by omega) hRN1
        T1 (fun p hp => hTΩ p (sT1 p hp)) (fun p hp => hTμ p (sT1 p hp))
        (fun p hp => hTcase p (sT1 p hp)) (fun p hp => hTd3ge1 p (sT1 p hp))
        (fun p hp => mT1 p hp)
      refine le_trans hraw ?_
      rw [hWB, show 2 * (n - d) + 6 = 6 from by omega, show n - (n - 1) = 1 from by omega, hKbasedef]
      norm_num
    have hpair2 : (∑ p ∈ T2, pairS0 d n A p) ≤
        Kbase * (A ^ (NN d n - 2 - (n + 1)) * B ^ 8 * (th1 ^ 2)⁻¹ * (Real.log A + 1) ^ 3
          + A ^ (NN d n - 3 - (n + 1)) * B ^ 6 * th2 ^ (n - 1)
            * (Real.log A + 1) ^ 2) := by
      have hraw := caseI_piece_bound d n hd hdn Kpp hKpppos hpp Kc hKcpos B hcntT A th1
        th2 CL (n + 1) (le_of_lt hBpos) hA1 hth1ge hth12 hCLpos
        (by rw [hth2def]; exact hlogq (1 / 2) (by norm_num)) (by omega) (by omega) hRN2
        T2 (fun p hp => hTΩ p (sT2 p hp)) (fun p hp => hTμ p (sT2 p hp))
        (fun p hp => hTcase p (sT2 p hp))
        (fun p hp => ml1 p (mem1 p hp))
        (fun p hp => mT2 p hp)
      refine le_trans hraw ?_
      rw [hWB, show 2 * ((n + 1) - d) + 6 = 8 from by omega, show (n + 1) - (n - 1) = 2 from by omega, hKbasedef]
    have hpair3 : (∑ p ∈ T3, pairS0 d n A p) ≤
        Kbase * (A ^ (NN d n - 2 - (n + 2)) * B ^ 10 * (th2 ^ 3)⁻¹ * (Real.log A + 1) ^ 3
          + A ^ (NN d n - 3 - (n + 2)) * B ^ 6 * th3 ^ (n - 1)
            * (Real.log A + 1) ^ 2) := by
      have hraw := caseI_piece_bound d n hd hdn Kpp hKpppos hpp Kc hKcpos B hcntT A th2
        th3 CL (n + 2) (le_of_lt hBpos) hA1 (le_trans hth1ge hth12) hth23 hCLpos
        (by rw [hth3def]; exact hlogq (3 / 4) (by norm_num)) (by omega) (by omega) hRN3
        T3 (fun p hp => hTΩ p (sT3 p hp)) (fun p hp => hTμ p (sT3 p hp))
        (fun p hp => hTcase p (sT3 p hp))
        (fun p hp => ml2 p (mem2 p hp))
        (fun p hp => mT3 p hp)
      refine le_trans hraw ?_
      rw [hWB, show 2 * ((n + 2) - d) + 6 = 10 from by omega, show (n + 2) - (n - 1) = 3 from by omega, hKbasedef]
    have hpair4 : (∑ p ∈ T4, pairS0 d n A p) ≤
        Kbase * (A ^ (NN d n - 2 - (n + 3)) * B ^ 12 * (th3 ^ 4)⁻¹ * (Real.log A + 1) ^ 3
          + A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2) := by
      by_cases hcase4 : th3 ≤ Dmax
      · have hraw := caseI_piece_bound d n hd hdn Kpp hKpppos hpp Kc hKcpos B hcntT A th3 Dmax CL (n + 3)
          (le_of_lt hBpos) hA1 (le_trans hth1ge hth13) hcase4 hCLpos
          (by rw [hDmaxdef]; rw [hWdef]
              exact hlog_dmax n (by omega) A B CB (1 / ((n : ℝ) + 1 - d))
                hA1 hBpos hCB1 (by rw [hnd]; norm_num) (by rw [hnd]; norm_num) hBleCB)
          (by omega) (by omega) hRN4
          T4 (fun p hp => hTΩ p (sT4 p hp)) (fun p hp => hTμ p (sT4 p hp))
          (fun p hp => hTcase p (sT4 p hp)) (fun p hp => ml3 p hp)
          (fun p hp => le_of_lt (hTd3lt p (sT4 p hp)))
        refine le_trans hraw ?_
        rw [hWB, show 2 * ((n + 3) - d) + 6 = 12 from by omega, show (n + 3) - (n - 1) = 4 from by omega, hKbasedef]
      · have hT4e : T4 = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro p hp
          have h1 := ml3 p hp
          have h2 := hTd3lt p (sT4 p hp)
          rw [hDmaxdef] at h2
          linarith [h1, h2, hcase4]
        rw [hT4e]
        simp only [Finset.sum_empty]
        positivity
    -- term bounds
    have hT11 : A ^ (NN d n - 2 - n) * B ^ 6 * (Real.log A + 1) ^ 3
        ≤ CB ^ 4 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hp : ((NN d n : ℝ) - 2 - n) + ((6 - 2 : ℕ) : ℝ) ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        norm_num
        linarith [hn5R]
      have h := arithT 1 ((NN d n : ℝ) - 2 - n) 6 3 (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [← Real.rpow_natCast A (NN d n - 2 - n), hcast2 n hRN1]
      exact h
    have hT12 : A ^ (NN d n - 3 - n) * B ^ 6 * th1 ^ (n - 1) * (Real.log A + 1) ^ 2
        ≤ CB ^ 4 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hc : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      have hp : ((NN d n : ℝ) - 3 - n) + ((1 / 4 * ((n - 1 : ℕ) : ℝ))) + ((6 - 2 : ℕ) : ℝ)
          ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        rw [hc]; norm_num; linarith [hn5R]
      have h := arithT (1:ℝ) (((NN d n : ℝ) - 3 - n) + ((1 / 4 * ((n - 1 : ℕ) : ℝ)))) 6 2
        (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [show A ^ (NN d n - 3 - n) * B ^ 6 * th1 ^ (n - 1) * (Real.log A + 1) ^ 2
          = (A ^ (NN d n - 3 - n) * A ^ ((1 / 4 * ((n - 1 : ℕ) : ℝ)))) * B ^ 6
              * (Real.log A + 1) ^ 2 from by
        rw [hth1def, hthpow (1 / 4) (n - 1)]; ring]
      rw [← Real.rpow_natCast A (NN d n - 3 - n), hcast3 n hRN1, ← Real.rpow_add hApos]
      exact h
    have hT21 : A ^ (NN d n - 2 - (n + 1)) * B ^ 8 * (th1 ^ 2)⁻¹ * (Real.log A + 1) ^ 3
        ≤ CB ^ 6 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hp : ((NN d n : ℝ) - 2 - (((n + 1 : ℕ)) : ℝ)) + (-(1 / 4 * 2 : ℝ)) + ((8 - 2 : ℕ) : ℝ)
          ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        norm_num; linarith [hn5R]
      have h := arithT (1:ℝ) (((NN d n : ℝ) - 2 - (((n + 1 : ℕ)) : ℝ)) + (-(1 / 4 * 2 : ℝ))) 8 3
        (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [show A ^ (NN d n - 2 - (n + 1)) * B ^ 8 * (th1 ^ 2)⁻¹ * (Real.log A + 1) ^ 3
          = (A ^ (NN d n - 2 - (n + 1)) * A ^ (-(1 / 4 * 2 : ℝ))) * B ^ 8
              * (Real.log A + 1) ^ 3 from by
        rw [hth1def, hthinv (1 / 4) 2]; ring]
      rw [← Real.rpow_natCast A (NN d n - 2 - (n + 1)), hcast2 (n + 1) hRN2, ← Real.rpow_add hApos]
      exact h
    have hT22 : A ^ (NN d n - 3 - (n + 1)) * B ^ 6 * th2 ^ (n - 1) * (Real.log A + 1) ^ 2
        ≤ CB ^ 4 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hc : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      have hp : ((NN d n : ℝ) - 3 - (((n + 1 : ℕ)) : ℝ)) + ((1 / 2 * ((n - 1 : ℕ) : ℝ))) + ((6 - 2 : ℕ) : ℝ)
          ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        rw [hc]; norm_num; linarith [hn5R]
      have h := arithT (1:ℝ) (((NN d n : ℝ) - 3 - (((n + 1 : ℕ)) : ℝ)) + ((1 / 2 * ((n - 1 : ℕ) : ℝ)))) 6 2
        (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [show A ^ (NN d n - 3 - (n + 1)) * B ^ 6 * th2 ^ (n - 1) * (Real.log A + 1) ^ 2
          = (A ^ (NN d n - 3 - (n + 1)) * A ^ ((1 / 2 * ((n - 1 : ℕ) : ℝ)))) * B ^ 6
              * (Real.log A + 1) ^ 2 from by
        rw [hth2def, hthpow (1 / 2) (n - 1)]; ring]
      rw [← Real.rpow_natCast A (NN d n - 3 - (n + 1)), hcast3 (n + 1) hRN2, ← Real.rpow_add hApos]
      exact h
    have hT31 : A ^ (NN d n - 2 - (n + 2)) * B ^ 10 * (th2 ^ 3)⁻¹ * (Real.log A + 1) ^ 3
        ≤ CB ^ 8 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hp : ((NN d n : ℝ) - 2 - (((n + 2 : ℕ)) : ℝ)) + (-(1 / 2 * 3 : ℝ)) + ((10 - 2 : ℕ) : ℝ)
          ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        norm_num; linarith [hn5R]
      have h := arithT (1:ℝ) (((NN d n : ℝ) - 2 - (((n + 2 : ℕ)) : ℝ)) + (-(1 / 2 * 3 : ℝ))) 10 3
        (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [show A ^ (NN d n - 2 - (n + 2)) * B ^ 10 * (th2 ^ 3)⁻¹ * (Real.log A + 1) ^ 3
          = (A ^ (NN d n - 2 - (n + 2)) * A ^ (-(1 / 2 * 3 : ℝ))) * B ^ 10
              * (Real.log A + 1) ^ 3 from by
        rw [hth2def, hthinv (1 / 2) 3]; ring]
      rw [← Real.rpow_natCast A (NN d n - 2 - (n + 2)), hcast2 (n + 2) hRN3, ← Real.rpow_add hApos]
      exact h
    have hT32 : A ^ (NN d n - 3 - (n + 2)) * B ^ 6 * th3 ^ (n - 1) * (Real.log A + 1) ^ 2
        ≤ CB ^ 4 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hc : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      have hp : ((NN d n : ℝ) - 3 - (((n + 2 : ℕ)) : ℝ)) + ((3 / 4 * ((n - 1 : ℕ) : ℝ))) + ((6 - 2 : ℕ) : ℝ)
          ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        rw [hc]; norm_num; linarith [hn5R]
      have h := arithT (1:ℝ) (((NN d n : ℝ) - 3 - (((n + 2 : ℕ)) : ℝ)) + ((3 / 4 * ((n - 1 : ℕ) : ℝ)))) 6 2
        (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [show A ^ (NN d n - 3 - (n + 2)) * B ^ 6 * th3 ^ (n - 1) * (Real.log A + 1) ^ 2
          = (A ^ (NN d n - 3 - (n + 2)) * A ^ ((3 / 4 * ((n - 1 : ℕ) : ℝ)))) * B ^ 6
              * (Real.log A + 1) ^ 2 from by
        rw [hth3def, hthpow (3 / 4) (n - 1)]; ring]
      rw [← Real.rpow_natCast A (NN d n - 3 - (n + 2)), hcast3 (n + 2) hRN3, ← Real.rpow_add hApos]
      exact h
    have hT41 : A ^ (NN d n - 2 - (n + 3)) * B ^ 12 * (th3 ^ 4)⁻¹ * (Real.log A + 1) ^ 3
        ≤ CB ^ 10 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have hp : ((NN d n : ℝ) - 2 - (((n + 3 : ℕ)) : ℝ)) + (-(3 / 4 * 4 : ℝ)) + ((12 - 2 : ℕ) : ℝ)
          ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        norm_num; linarith [hn5R]
      have h := arithT (1:ℝ) (((NN d n : ℝ) - 2 - (((n + 3 : ℕ)) : ℝ)) + (-(3 / 4 * 4 : ℝ))) 12 3
        (by norm_num) (by norm_num) (by omega) hp
      simp only [one_mul] at h
      rw [show A ^ (NN d n - 2 - (n + 3)) * B ^ 12 * (th3 ^ 4)⁻¹ * (Real.log A + 1) ^ 3
          = (A ^ (NN d n - 2 - (n + 3)) * A ^ (-(3 / 4 * 4 : ℝ))) * B ^ 12
              * (Real.log A + 1) ^ 3 from by
        rw [hth3def, hthinv (3 / 4) 4]; ring]
      rw [← Real.rpow_natCast A (NN d n - 2 - (n + 3)), hcast2 (n + 3) hRN4, ← Real.rpow_add hApos]
      exact h
    have hT42 : A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
        ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2) * A ^ ((NN d n : ℝ) - 7 / 3)
            * B ^ 2 := by
      have hcs : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      have hp : ((NN d n : ℝ) - 3 - (((n + 3 : ℕ)) : ℝ)) + (-(((n - 1 : ℕ)) : ℝ))
          + ((2 * n + 4 - 2 : ℕ) : ℝ) ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
        have h2 : ((2 * n + 4 - 2 : ℕ) : ℝ) = 2 * (n : ℝ) + 2 := by
          have hh : 2 * n + 4 - 2 = 2 * n + 2 := by omega
          rw [hh]; push_cast; ring
        have h3 : (((n + 3 : ℕ)) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
        rw [hcs, h2, h3]; linarith [hn5R]
      have hBp : B ^ 6 * (W ^ 2) ^ (n - 1) = B ^ (2 * n + 4) := by
        rw [hWdB, ← pow_mul, ← pow_add]
        congr 1
        omega
      have hDp0 : B ^ 6 * Dmax ^ (n - 1)
          = (3 * (n : ℝ) ^ 2) ^ (n - 1) * B ^ (2 * n + 4) * (A ^ (n - 1))⁻¹ := by
        have h3 : B ^ 6 * Dmax ^ (n - 1)
            = B ^ 6 * ((3 * (n : ℝ) ^ 2) ^ (n - 1) * (W ^ 2) ^ (n - 1) * (A ^ (n - 1))⁻¹) := by
          rw [hDmaxdef, div_eq_mul_inv, mul_pow, mul_pow, inv_pow]
        rw [h3, show B ^ 6 * ((3 * (n : ℝ) ^ 2) ^ (n - 1) * (W ^ 2) ^ (n - 1) * (A ^ (n - 1))⁻¹)
            = (3 * (n : ℝ) ^ 2) ^ (n - 1) * (B ^ 6 * (W ^ 2) ^ (n - 1)) * (A ^ (n - 1))⁻¹
            from by ring, hBp]
      have h := arithT ((3 * (n : ℝ) ^ 2) ^ (n - 1))
        (((NN d n : ℝ) - 3 - (((n + 3 : ℕ)) : ℝ)) + (-(((n - 1 : ℕ)) : ℝ))) (2 * n + 4) 2
        (by positivity) (by omega) (by omega) hp
      rw [show A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
          = (3 * (n : ℝ) ^ 2) ^ (n - 1)
              * (A ^ (NN d n - 3 - (n + 3)) * A ^ (-(((n - 1 : ℕ)) : ℝ)))
              * B ^ (2 * n + 4) * (Real.log A + 1) ^ 2 from by
        rw [show A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1)
              = A ^ (NN d n - 3 - (n + 3)) * (B ^ 6 * Dmax ^ (n - 1)) from by ring,
          hDp0, inv_pow_eq_rpow A hApos]
        ring]
      rw [← Real.rpow_natCast A (NN d n - 3 - (n + 3)), hcast3 (n + 3) hRN4, ← Real.rpow_add hApos]
      exact h
    have hp1 : (∑ p ∈ T1, pairS0 d n A p) ≤ 2 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have h1 : Kbase * (A ^ (NN d n - 2 - n) * B ^ 6 * (Real.log A + 1) ^ 3)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 6 (by norm_num) (by omega) hT11
      have h2 : Kbase * (A ^ (NN d n - 3 - n) * B ^ 6 * th1 ^ (n - 1) * (Real.log A + 1) ^ 2)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 6 (by norm_num) (by omega) hT12
      refine le_trans hpair1 ?_
      rw [show Kbase * (A ^ (NN d n - 2 - n) * B ^ 6 * (Real.log A + 1) ^ 3
            + A ^ (NN d n - 3 - n) * B ^ 6 * th1 ^ (n - 1) * (Real.log A + 1) ^ 2)
          = Kbase * (A ^ (NN d n - 2 - n) * B ^ 6 * (Real.log A + 1) ^ 3)
            + Kbase * (A ^ (NN d n - 3 - n) * B ^ 6 * th1 ^ (n - 1) * (Real.log A + 1) ^ 2)
          from by ring]
      linarith [h1, h2]
    have hp2 : (∑ p ∈ T2, pairS0 d n A p) ≤ 2 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have h1 : Kbase * (A ^ (NN d n - 2 - (n + 1)) * B ^ 8 * (th1 ^ 2)⁻¹ * (Real.log A + 1) ^ 3)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 8 (by norm_num) (by omega) hT21
      have h2 : Kbase * (A ^ (NN d n - 3 - (n + 1)) * B ^ 6 * th2 ^ (n - 1) * (Real.log A + 1) ^ 2)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 6 (by norm_num) (by omega) hT22
      refine le_trans hpair2 ?_
      rw [show Kbase * (A ^ (NN d n - 2 - (n + 1)) * B ^ 8 * (th1 ^ 2)⁻¹ * (Real.log A + 1) ^ 3
            + A ^ (NN d n - 3 - (n + 1)) * B ^ 6 * th2 ^ (n - 1) * (Real.log A + 1) ^ 2)
          = Kbase * (A ^ (NN d n - 2 - (n + 1)) * B ^ 8 * (th1 ^ 2)⁻¹ * (Real.log A + 1) ^ 3)
            + Kbase * (A ^ (NN d n - 3 - (n + 1)) * B ^ 6 * th2 ^ (n - 1) * (Real.log A + 1) ^ 2)
          from by ring]
      linarith [h1, h2]
    have hp3 : (∑ p ∈ T3, pairS0 d n A p) ≤ 2 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have h1 : Kbase * (A ^ (NN d n - 2 - (n + 2)) * B ^ 10 * (th2 ^ 3)⁻¹ * (Real.log A + 1) ^ 3)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 10 (by norm_num) (by omega) hT31
      have h2 : Kbase * (A ^ (NN d n - 3 - (n + 2)) * B ^ 6 * th3 ^ (n - 1) * (Real.log A + 1) ^ 2)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 6 (by norm_num) (by omega) hT32
      refine le_trans hpair3 ?_
      rw [show Kbase * (A ^ (NN d n - 2 - (n + 2)) * B ^ 10 * (th2 ^ 3)⁻¹ * (Real.log A + 1) ^ 3
            + A ^ (NN d n - 3 - (n + 2)) * B ^ 6 * th3 ^ (n - 1) * (Real.log A + 1) ^ 2)
          = Kbase * (A ^ (NN d n - 2 - (n + 2)) * B ^ 10 * (th2 ^ 3)⁻¹ * (Real.log A + 1) ^ 3)
            + Kbase * (A ^ (NN d n - 3 - (n + 2)) * B ^ 6 * th3 ^ (n - 1) * (Real.log A + 1) ^ 2)
          from by ring]
      linarith [h1, h2]
    have hp4 : (∑ p ∈ T4, pairS0 d n A p) ≤ 2 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      have h1 : Kbase * (A ^ (NN d n - 2 - (n + 3)) * B ^ 12 * (th3 ^ 4)⁻¹ * (Real.log A + 1) ^ 3)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
        kmul _ 12 (by norm_num) (by omega) hT41
      have h2 : Kbase * (A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2)
          ≤ Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
        have hnn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by positivity
        calc Kbase * (A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2)
            ≤ Kbase * ((3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)
                * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ hKbasepos.le
              calc A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
                  ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)
                      * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := hT42
                _ = (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2)
                      * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
          _ = (Kbase * (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ (2 * n + 2))
                * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
          _ ≤ Kterm * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
              mul_le_mul_of_nonneg_right hKq2 hnn
          _ = Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := (mul_assoc _ _ _).symm
      refine le_trans hpair4 ?_
      rw [show Kbase * (A ^ (NN d n - 2 - (n + 3)) * B ^ 12 * (th3 ^ 4)⁻¹ * (Real.log A + 1) ^ 3
            + A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2)
          = Kbase * (A ^ (NN d n - 2 - (n + 3)) * B ^ 12 * (th3 ^ 4)⁻¹ * (Real.log A + 1) ^ 3)
            + Kbase * (A ^ (NN d n - 3 - (n + 3)) * B ^ 6 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2)
          from by ring]
      linarith [h1, h2]
    have htot : (∑ p ∈ T, pairS0 d n A p) ≤ 8 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
      rw [hsplit1, hsplit2, hsplit3]
      linarith [hp1, hp2, hp3, hp4]
    refine le_trans htot ?_
    rw [hEeq]
    have hnn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by positivity
    rw [hKKdef]
    calc 8 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2
        = 8 * Kterm * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ac_rfl
      _ ≤ 10 * Kterm * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by
          nlinarith [mul_nonneg hKtermpos.le hnn]
      _ = 10 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by ac_rfl

  · -- ==================== n = d + 1 ====================
    have hq1 : (n : ℝ) = (d : ℝ) + 1 := by rw [hnd]; push_cast; ring
    have hs2 : 1 / ((n : ℝ) + 1 - d) = 1 / 2 := by rw [hq1]; ring_nf
    have hn15 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hW2 : W ^ 2 = B := by
      calc W ^ 2 = (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 : ℝ) := by
            rw [hWdef]; exact (Real.rpow_natCast _ 2).symm
        _ = B ^ ((1 / ((n : ℝ) + 1 - d)) * 2) := by rw [← Real.rpow_mul hBpos.le]
        _ = B ^ (1 : ℝ) := by rw [show 1 / ((n : ℝ) + 1 - d) * 2 = 1 by rw [hs2]; norm_num]
        _ = B := Real.rpow_one B
    have hW6 : W ^ 6 = B ^ 3 := by
      calc W ^ 6 = (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (6 : ℝ) := by
            rw [hWdef]; exact (Real.rpow_natCast _ 6).symm
        _ = B ^ ((1 / ((n : ℝ) + 1 - d)) * 6) := by rw [← Real.rpow_mul hBpos.le]
        _ = B ^ (3 : ℝ) := by rw [show 1 / ((n : ℝ) + 1 - d) * 6 = 3 by rw [hs2]; norm_num]
        _ = B ^ 3 := Real.rpow_natCast B 3
    set Dmax : ℝ := 3 * (n : ℝ) ^ 2 * W ^ 2 / A with hDmaxdef
    have hs0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1 - d) := by rw [hs2]; norm_num
    have hs1 : 1 / ((n : ℝ) + 1 - d) ≤ 1 := by rw [hs2]; norm_num
    have hRN1 : n - 1 ≤ NN d n - 3 := by
      have := NN_ge_add_two d n hd hdn; omega
    by_cases hcase1 : 1 ≤ Dmax
    · have hraw := caseI_piece_bound d n hd hdn Kpp hKpppos hpp Kc hKcpos B hcntT A 1 Dmax CL (n - 1)
        (le_of_lt hBpos) hA1 (le_refl 1) hcase1 hCLpos
        (by rw [hDmaxdef]; rw [hWdef]
            exact hlog_dmax n (by omega) A B CB (1 / ((n : ℝ) + 1 - d))
              hA1 hBpos hCB1 hs0 hs1 hBleCB)
        (by omega) (by omega) hRN1 T hTΩ hTμ hTcase hTd3ge1
        (fun p hp => le_of_lt (hTd3lt p hp))
      have ht1 : A ^ (NN d n - 2 - (n - 1)) * B ^ 3 * (Real.log A + 1) ^ 3
          ≤ CB ^ 1 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
        have hcs1 : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        have hp : ((NN d n : ℝ) - 2 - (((n - 1 : ℕ)) : ℝ)) + ((3 - 2 : ℕ) : ℝ)
            ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
          rw [hcs1]; norm_num
          linarith [hn15]
        have h := arithT 1 ((NN d n : ℝ) - 2 - (((n - 1 : ℕ)) : ℝ)) 3 3
          (by norm_num) (by norm_num) (by omega) hp
        simp only [one_mul] at h
        rw [← Real.rpow_natCast A (NN d n - 2 - (n - 1)), hcast2 (n - 1) hRN1]
        exact h
      have ht2 : A ^ (NN d n - 3 - (n - 1)) * B ^ 3 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
          ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ n * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
        have hcs : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        have hDp0 : B ^ 3 * Dmax ^ (n - 1)
            = (3 * (n : ℝ) ^ 2) ^ (n - 1) * B ^ (n + 2) * (A ^ (n - 1))⁻¹ := by
          have h3 : B ^ 3 * Dmax ^ (n - 1)
              = B ^ 3 * ((3 * (n : ℝ) ^ 2) ^ (n - 1) * (W ^ 2) ^ (n - 1) * (A ^ (n - 1))⁻¹) := by
            rw [hDmaxdef, div_eq_mul_inv, mul_pow, mul_pow, inv_pow]
          have hBW : B ^ 3 * (W ^ 2) ^ (n - 1) = B ^ (n + 2) := by
            rw [hW2, ← pow_add]
            congr 1
            omega
          rw [h3, show B ^ 3 * ((3 * (n : ℝ) ^ 2) ^ (n - 1) * (W ^ 2) ^ (n - 1) * (A ^ (n - 1))⁻¹)
              = (3 * (n : ℝ) ^ 2) ^ (n - 1) * (B ^ 3 * (W ^ 2) ^ (n - 1)) * (A ^ (n - 1))⁻¹
              from by ring, hBW]
        have hp : ((NN d n : ℝ) - 3 - (((n - 1 : ℕ)) : ℝ)) + (-(((n - 1 : ℕ)) : ℝ))
            + ((n + 2 - 2 : ℕ) : ℝ) ≤ ((NN d n : ℝ) - 7 / 3) - 1 / 6 := by
          have h1 : (((n + 2 - 2 : ℕ)) : ℝ) = (n : ℝ) := by
            have hh : n + 2 - 2 = n := by omega
            rw [hh]
          rw [hcs, h1]; linarith [hn15]
        have h := arithT ((3 * (n : ℝ) ^ 2) ^ (n - 1))
          (((NN d n : ℝ) - 3 - (((n - 1 : ℕ)) : ℝ)) + (-(((n - 1 : ℕ)) : ℝ))) (n + 2) 2
          (by positivity) (by omega) (by omega) hp
        rw [show A ^ (NN d n - 3 - (n - 1)) * B ^ 3 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
            = (3 * (n : ℝ) ^ 2) ^ (n - 1)
                * (A ^ (NN d n - 3 - (n - 1)) * A ^ (-(((n - 1 : ℕ)) : ℝ)))
                * B ^ (n + 2) * (Real.log A + 1) ^ 2 from by
          rw [show A ^ (NN d n - 3 - (n - 1)) * B ^ 3 * Dmax ^ (n - 1)
                = A ^ (NN d n - 3 - (n - 1)) * (B ^ 3 * Dmax ^ (n - 1)) from by ring,
            hDp0, inv_pow_eq_rpow A hApos]
          ring]
        rw [← Real.rpow_natCast A (NN d n - 3 - (n - 1)), hcast3 (n - 1) hRN1]
        rw [← Real.rpow_add hApos]
        exact h
      have hsq : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by positivity
      have hXX : (0 : ℝ) ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) := by positivity
      have ho : A ^ (NN d n - 2 - (n - 1)) * B ^ 3 * (Real.log A + 1) ^ 3
            + A ^ (NN d n - 3 - (n - 1)) * B ^ 3 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
          ≤ (CB + (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ n) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by
        calc A ^ (NN d n - 2 - (n - 1)) * B ^ 3 * (Real.log A + 1) ^ 3
              + A ^ (NN d n - 3 - (n - 1)) * B ^ 3 * Dmax ^ (n - 1) * (Real.log A + 1) ^ 2
            ≤ CB * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2
              + ((3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ n) * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
              refine add_le_add ?_ ?_
              · calc A ^ (NN d n - 2 - (n - 1)) * B ^ 3 * (Real.log A + 1) ^ 3
                    ≤ CB ^ 1 * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := ht1
                  _ = CB * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by norm_num
              · exact ht2
          _ = (CB + (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ n)
                * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
      refine le_trans hraw ?_
      rw [show 2 * ((n - 1) - d) + 6 = 6 by omega, show (n - 1) - (n - 1) = 0 by omega]
      rw [hW6]
      simp only [pow_zero, inv_one, mul_one, one_mul, hKbasedef]
      -- goal: Kpp * (...) * (neat terms) ≤ KK * A^E * B^2
      refine le_trans (mul_le_mul_of_nonneg_left ho hKbasepos.le) ?_
      have hcoef : CB + (3 * (n : ℝ) ^ 2) ^ (n - 1) * CB ^ n
          ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by
        have hY : (0 : ℝ) ≤ CB ^ (2 * n + 2) := by positivity
        have h1' : CB ≤ 1 + 10 * CB ^ (2 * n + 2) := by
          have hY1 : CB ≤ CB ^ (2 * n + 2) := by
            simpa using caseI_pow_le_pow_aux CB hCB1 (show 1 ≤ 2 * n + 2 by omega)
          linarith
        have h2' : CB ^ n ≤ 1 + 10 * CB ^ (2 * n + 2) := by
          have hY1 : CB ^ n ≤ CB ^ (2 * n + 2) := caseI_pow_le_pow_aux CB hCB1 (show n ≤ 2 * n + 2 by omega)
          linarith
        nlinarith [hXX, h1', h2', hCBpos.le,
          mul_nonneg hXX (mul_nonneg hCBpos.le (by positivity : (0:ℝ) ≤ CB ^ (n-1)))]
      have hCnn : (0 : ℝ) ≤ ((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)) := by positivity
      refine le_trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoef hsq) hKbasepos.le) ?_
      rw [hKKdef, hKtermdef, hEeq]
      have hCnn2 : (0 : ℝ) ≤ Kbase
          * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))) :=
        mul_nonneg hKbasepos.le hCnn
      calc Kpp * (16 * Kc * 2 ^ NN d n * CL ^ 3 + Kc * CL ^ 2 + 1)
            * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))
              * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2))
          = Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))
              * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)) := by rw [hKbasedef]
        _ ≤ 10 * Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)))
              * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by
            calc Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))
                  * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2))
                = (Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2))))
                    * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
              _ ≤ (10 * (Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)))))
                    * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
                  mul_le_mul_of_nonneg_right (by linarith [hCnn2]) hsq
              _ = 10 * Kbase * (((3 * (n : ℝ) ^ 2) ^ (n - 1) + 1) * (1 + 10 * CB ^ (2 * n + 2)))
                    * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by ring
        _ = 10 * Kterm * A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 := by rw [hKtermdef]; ring
    · have hTempty : T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have h1 := hTd3ge1 p hp
        have h2 := hTd3lt p hp
        rw [hDmaxdef] at h2
        linarith [h1, h2, hcase1]
      rw [hTempty]
      simp only [Finset.sum_empty]
      positivity
  · -- ==================== d + 2 ≤ n ====================
    have hTempty : T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hΩ := hTΩ p hp
      have hLI := li_of_mem_Omega d n B p hΩ
      have hμle := MDEstimates.muXY_le d n p.1 p.2 hΩ.1.1 hΩ.2.1.1 hLI
      have he1 : eNorm p.1 ≤ W := hΩ.1.2
      have he2 : eNorm p.2 ≤ W := hΩ.2.1.2
      have hd3 : (3 : ℝ) ≤ (n : ℝ) + 1 - d := by
        have h1 : (d : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast (by omega : d + 2 ≤ n)
        linarith
      have hd3pos : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
      have hs3 : 1 / ((n : ℝ) + 1 - d) * 2 ≤ (2 : ℝ) / 3 := by
        rw [show 1 / ((n : ℝ) + 1 - d) * 2 = 2 / ((n : ℝ) + 1 - d) by ring]
        rw [div_le_iff₀ hd3pos, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
        nlinarith [hd3]
      have hW23 : W ^ 2 ≤ B ^ ((2 : ℝ) / 3) := by
        calc W ^ 2 = (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 : ℝ) := by
              rw [hWdef]; exact (Real.rpow_natCast _ 2).symm
          _ = B ^ ((1 / ((n : ℝ) + 1 - d)) * 2) := by rw [← Real.rpow_mul hBpos.le]
          _ ≤ B ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le hB1 hs3
      have hAub : A < 3 * (n : ℝ) ^ 2 * B ^ ((2 : ℝ) / 3) := by
        calc A < muXY n p.1 p.2 := hTμ p hp
          _ ≤ 3 * (n : ℝ) ^ 2 * (eNorm p.1 * eNorm p.2) := hμle
          _ ≤ 3 * (n : ℝ) ^ 2 * W ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [eNorm_nonneg p.1, eNorm_nonneg p.2, hW0, he1, he2]
          _ ≤ 3 * (n : ℝ) ^ 2 * B ^ ((2 : ℝ) / 3) :=
              mul_le_mul_of_nonneg_left hW23 (by positivity)
      have hlogBle : B / Real.log B < 3 * (n : ℝ) ^ 2 * B ^ ((2 : ℝ) / 3) :=
        lt_of_le_of_lt hAB hAub
      have hlog6 : Real.log B ≤ 6 * B ^ ((1 : ℝ) / 6) := by
        have h := Real.log_le_rpow_div (le_of_lt hBpos) (by norm_num : (0 : ℝ) < 1 / 6)
        rw [div_eq_mul_inv, one_div] at h
        linarith [h]
      have hcube : 3 * (n : ℝ) ^ 2 * Real.log B ≤ B ^ ((1 : ℝ) / 3) := by
        calc 3 * (n : ℝ) ^ 2 * Real.log B ≤ 3 * (n : ℝ) ^ 2 * (6 * B ^ ((1 : ℝ) / 6)) :=
              mul_le_mul_of_nonneg_left hlog6 (by positivity)
          _ = 18 * (n : ℝ) ^ 2 * B ^ ((1 : ℝ) / 6) := by ring
          _ ≤ B ^ ((1 : ℝ) / 6) * B ^ ((1 : ℝ) / 6) :=
              mul_le_mul_of_nonneg_right h18 (Real.rpow_nonneg hBpos.le _)
          _ = B ^ ((1 : ℝ) / 3) := by rw [← Real.rpow_add hBpos]; norm_num
      have hB13 : B ^ ((1 : ℝ) / 3) < 3 * (n : ℝ) ^ 2 * Real.log B := by
        have h := (div_lt_iff₀ hlogBpos).mp hlogBle
        have hB23 : (0 : ℝ) < B ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hBpos _
        have h2 : B / B ^ ((2 : ℝ) / 3) < 3 * (n : ℝ) ^ 2 * Real.log B :=
          (div_lt_iff₀ hB23).mpr (by rw [mul_comm]; linarith [h])
        rw [show B / B ^ ((2 : ℝ) / 3) = B ^ ((1 : ℝ) / 3) from by
          rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hBpos _)), ← Real.rpow_add hBpos,
            show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num, Real.rpow_one]] at h2
        exact h2
      linarith [hcube, hB13]
    rw [hTempty]
    simp only [Finset.sum_empty]
    positivity

/-- **Case I.** `Σ^{(2,I)}_{d,n}(A,B) ≤ K A^{N_{d,n}-2-1/3} B²`. -/
theorem Sigma2_caseI (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) (h44 : (d, n) ≠ (4, 4)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          ¬ (muXY n p.1 p.2 ≤ A) ∧
          ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
            ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))},
        pairS0 d n A p)
        ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn : n = 2 := by omega
      have hd2 : d = 2 := by omega
      exact absurd (by simp [hn, hd2]) h22
    · exact h
  obtain ⟨C₀, hC₀pos, hC₀⟩ := MDEstimates.detGam_lower d n hd hn2
  have hCdet : ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      C₀⁻¹ * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)
        ≤ detL (Gam d n x y) := by
    intro x y hx hy hLI
    have h := hC₀ x y hx hy hLI
    have h2 : C₀⁻¹ * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1)
        * eNorm y ^ (d - 1)) ≤ C₀⁻¹ * (C₀ * detL (Gam d n x y)) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hC₀pos.le)
    have h3 : C₀⁻¹ * (C₀ * detL (Gam d n x y)) = detL (Gam d n x y) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC₀pos), one_mul]
    linarith [h2, h3.le, h3.ge]
  obtain ⟨Kpp, hKpppos, hpp⟩ := per_pair_sum_bound d n hd hdn C₀⁻¹ (inv_pos.mpr hC₀pos) hCdet
  obtain ⟨Kc, hKcpos, hcnt0⟩ := omega_d3_count d n hn3 hdn
  exact caseI_main d n hd hdn hn3 h22 h33 h44 Kpp hKpppos hpp Kc hKcpos hcnt0

end Work.HP.Sig2
