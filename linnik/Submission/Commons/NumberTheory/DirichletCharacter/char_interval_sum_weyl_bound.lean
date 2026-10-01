import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.char_head_sum_weyl_bound
import Submission.Commons.Analysis.ExponentialSums.log_phase_shifted_head_sum_weyl

open Complex
open scoped Real BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

set_option maxHeartbeats 4000000

/-! ### Arithmetic helpers -/

lemma brk_mono {Y Y' : ℕ} (h : Y ≤ Y') {t : ℝ} (ht : 1 ≤ t) : brk Y t ≤ brk Y' t := by
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog : Real.log (2*(Y:ℝ)) ≤ Real.log (2*(Y':ℝ)) := by
    rcases Nat.eq_zero_or_pos Y with hY0 | hYpos
    · subst hY0
      rcases Nat.eq_zero_or_pos Y' with hY'0 | hY'pos
      · subst hY'0; simp
      · simp only [Nat.cast_zero, mul_zero, Real.log_zero]
        apply Real.log_nonneg
        have : (1:ℝ) ≤ (Y':ℝ) := by exact_mod_cast hY'pos
        linarith
    · have hpos : (0:ℝ) < 2*(Y:ℝ) := by
        have : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hYpos
        linarith
      apply Real.log_le_log hpos
      have : (Y:ℝ) ≤ (Y':ℝ) := by exact_mod_cast h
      linarith
  have hsqrt : Real.sqrt (Y:ℝ) ≤ Real.sqrt (Y':ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h)
  unfold brk
  have h1 : t ^ (1/6:ℝ) * (1 + Real.log (2*(Y:ℝ)))
      ≤ t ^ (1/6:ℝ) * (1 + Real.log (2*(Y':ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg ht0.le _)
  have h2 : t ^ (-(1/6):ℝ) * Real.sqrt (Y:ℝ) ≤ t ^ (-(1/6):ℝ) * Real.sqrt (Y':ℝ) :=
    mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg ht0.le _)
  linarith

lemma le_add_mul_iff_div_le {N a q m : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    N + 1 ≤ a + q * m ↔ (N + q - a) / q ≤ m := by
  constructor
  · intro h
    by_cases haN : a ≤ N + 1
    · have hx : N + 1 - a ≤ q * m := by omega
      have hkey : N + q - a = (N + 1 - a) + q - 1 := by omega
      rw [hkey, Nat.div_le_iff_le_mul hq]
      have hmq : N + 1 - a ≤ m * q := by rw [Nat.mul_comm]; exact hx
      omega
    · have hlt : N + q - a < q := by omega
      rw [Nat.div_eq_of_lt hlt]; exact Nat.zero_le _
  · intro h
    have hmono : a + q * ((N + q - a) / q) ≤ a + q * m :=
      Nat.add_le_add_left (Nat.mul_le_mul_left q h) a
    have hbound : N + 1 ≤ a + q * ((N + q - a) / q) := by
      have hd := Nat.div_add_mod (N + q - a) q
      have hmod : (N + q - a) % q ≤ q - 1 := by
        have := Nat.mod_lt (N + q - a) hq; omega
      omega
    omega

lemma add_mul_le_iff_le_div {N M a q m : ℕ} (hq : 0 < q) (ha : a ≤ N + M) :
    a + q * m ≤ N + M ↔ m ≤ (N + M - a) / q := by
  constructor
  · intro h
    have h1 : q * m ≤ N + M - a := by omega
    rw [Nat.le_div_iff_mul_le hq]
    rw [Nat.mul_comm]
    exact h1
  · intro h
    have h1 : m * q ≤ N + M - a := (Nat.le_div_iff_mul_le hq).mp h
    have h2 : q * m ≤ N + M - a := by rw [Nat.mul_comm]; exact h1
    omega

lemma add_mul_sub_one (a q m : ℕ) (ha : 1 ≤ a) : a + q*m - 1 = a - 1 + q*m := by
  omega

lemma div_interval_len_le {q Y N M a : ℕ} (hq : 1 ≤ q) (hY : 1 ≤ Y) (hMY : M ≤ q * Y)
    (hlo : N + 1 ≤ a + q * ((N + q - a) / q))
    (hhi : a + q * ((N + M - a) / q) ≤ N + M) :
    (N + M - a) / q - (N + q - a) / q + 1 ≤ Y := by
  by_cases hle : (N + q - a) / q ≤ (N + M - a) / q
  · have h3 : q * ((N + M - a) / q - (N + q - a) / q) ≤ M - 1 := by
      rw [Nat.mul_sub_left_distrib]
      have h2 : q * ((N + M - a) / q) - q * ((N + q - a) / q)
          = (a + q * ((N + M - a) / q)) - (a + q * ((N + q - a) / q)) :=
        (Nat.add_sub_add_left a (q * ((N + M - a) / q)) (q * ((N + q - a) / q))).symm
      rw [h2]; omega
    have h5 : (N + M - a) / q - (N + q - a) / q < Y := by
      by_contra hcon
      have hcon' : Y ≤ (N + M - a) / q - (N + q - a) / q := by omega
      have h6 : q * Y ≤ q * ((N + M - a) / q - (N + q - a) / q) :=
        Nat.mul_le_mul_left q hcon'
      have hqY1 : 1 ≤ q * Y := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      have hM1 : M - 1 < q * Y := by omega
      omega
    omega
  · have hz : (N + M - a) / q - (N + q - a) / q = 0 :=
      Nat.sub_eq_zero_of_le (le_of_not_ge hle)
    omega

lemma sum_Icc_shift {M : Type*} [AddCommMonoid M] (L H : ℕ) (hL : 1 ≤ L) (hLH : L ≤ H)
    (g : ℕ → M) :
    ∑ m ∈ Finset.Icc L H, g m = ∑ j ∈ Finset.Icc 1 (H - L + 1), g (L - 1 + j) := by
  refine Finset.sum_bij (fun m _ => m - L + 1) ?_ ?_ ?_ ?_
  · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  · intro m1 hm1 m2 hm2 h
    rw [Finset.mem_Icc] at hm1 hm2; omega
  · intro j hj; rw [Finset.mem_Icc] at hj
    refine ⟨L - 1 + j, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · omega
  · intro m hm; rw [Finset.mem_Icc] at hm; congr 1; omega

lemma interval_residue_decomp (q N M : ℕ) (hq : 1 ≤ q) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc (N + 1) (N + M), f n
      = ∑ a ∈ Finset.Icc 1 (min q (N + M)),
          ∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q), f (a + q * m) := by
  have hq0 : 0 < q := hq
  rw [Finset.sum_sigma' (Finset.Icc 1 (min q (N + M)))
        (fun a => Finset.Icc ((N + q - a) / q) ((N + M - a) / q))
        (fun a m => f (a + q * m))]
  have key : ∀ n : ℕ, 1 ≤ n → ((n - 1) % q + 1) + q * ((n - 1) / q) = n := by
    intro n hn
    have h1 : (n - 1) % q + q * ((n - 1) / q) = n - 1 := by
      have h := Nat.div_add_mod (n - 1) q; omega
    omega
  refine Finset.sum_bij (fun n _ => (⟨(n - 1) % q + 1, (n - 1) / q⟩ : Sigma (fun _ : ℕ => ℕ)))
    ?_ ?_ ?_ ?_
  · rintro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : 1 ≤ n := by omega
    have hmodle : (n - 1) % q ≤ n - 1 := Nat.mod_le _ _
    have haq : (n - 1) % q + 1 ≤ q := by have := Nat.mod_lt (n - 1) hq0; omega
    have haNM : (n - 1) % q + 1 ≤ N + M := by
      have h2 : (n - 1) % q + 1 ≤ (n - 1) + 1 := by omega
      rw [Nat.sub_add_cancel hn1'] at h2
      exact le_trans h2 hn2
    have h1a : 1 ≤ (n - 1) % q + 1 := by omega
    have h2a : (n - 1) % q + 1 ≤ min q (N + M) := le_min haq haNM
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨h1a, h2a⟩, ?_⟩
    rw [Finset.mem_Icc]
    have hdec := key n hn1'
    exact ⟨(le_add_mul_iff_div_le hq0 haq).mp (by rw [hdec]; exact hn1),
           (add_mul_le_iff_le_div hq0 haNM).mp (by rw [hdec]; exact hn2)⟩
  · rintro n1 hn1 n2 hn2 h
    have hn1' : 1 ≤ n1 := by have := (Finset.mem_Icc.mp hn1).1; omega
    have hn2' : 1 ≤ n2 := by have := (Finset.mem_Icc.mp hn2).1; omega
    have e1 : (n1 - 1) % q + 1 = (n2 - 1) % q + 1 := by
      have := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.1) h; simpa using this
    have e2 : (n1 - 1) / q = (n2 - 1) / q := by
      have := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) h; simpa using this
    have k1 := key n1 hn1'
    have k2 := key n2 hn2'
    rw [e1, e2] at k1
    omega
  · rintro ⟨a, m⟩ hb
    obtain ⟨ha, hm⟩ := Finset.mem_sigma.mp hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    have haq : a ≤ q := le_trans ha2 (min_le_left q (N + M))
    have haNM : a ≤ N + M := le_trans ha2 (min_le_right q (N + M))
    have hlt : a - 1 < q := by omega
    refine ⟨a + q * m, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨(le_add_mul_iff_div_le hq0 haq).mpr hmlo,
             (add_mul_le_iff_le_div hq0 haNM).mpr hmhi⟩
    · have hcomp1 : (a + q * m - 1) % q + 1 = a := by
        rw [add_mul_sub_one a q m ha1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        exact Nat.sub_add_cancel ha1
      have hcomp2 : (a + q * m - 1) / q = m := by
        rw [add_mul_sub_one a q m ha1, Nat.add_mul_div_left _ _ hq0, Nat.div_eq_of_lt hlt,
            Nat.zero_add]
      exact Sigma.ext hcomp1 (heq_of_eq hcomp2)
  · rintro n hn
    have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    show f n = f ((n - 1) % q + 1 + q * ((n - 1) / q))
    rw [key n hn1]

/-! ### Main theorem -/

theorem char_interval_sum_weyl_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (N M Y : ℕ)
        (hM : M ≤ q * Y) (hY : 1 ≤ Y) (T : ℝ) (hT : 1 ≤ T)
        (hYt : (Y : ℝ) ^ 2 ≤ T),
        ‖∑ n ∈ Finset.Icc (N + 1) (N + M),
            χ (n : ZMod q) *
              Complex.exp ((((2 * Real.pi * (-(T / (2 * Real.pi)) * Real.log (n : ℝ))) : ℝ) : ℂ) *
                Complex.I) / Real.sqrt (n : ℝ)‖
          ≤ C * Real.sqrt (q : ℝ) *
              (T ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
                T ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by
  obtain ⟨Cs, hCspos, hshift⟩ :=
    Commons.Analysis.ExponentialSums.log_phase_shifted_head_sum_weyl
  refine ⟨Cs + 2, by positivity, ?_⟩
  intro q hq χ N M Y hM hY T hT hYt
  have hq0n : 0 < q := by omega
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0n
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hbrk1 : (1:ℝ) ≤ brk Y T := by
    unfold brk
    have hlog : 0 ≤ Real.log (2*(Y:ℝ)) := Real.log_nonneg (by
      have : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
      linarith)
    have h1 : (1:ℝ) ≤ T ^ (1/6:ℝ) * (1 + Real.log (2*(Y:ℝ))) := by
      have := Real.one_le_rpow hT (by norm_num : (0:ℝ) ≤ 1/6)
      nlinarith [this, hlog, Real.rpow_nonneg hT0.le (1/6:ℝ)]
    have h2 : 0 ≤ T ^ (-(1/6):ℝ) * Real.sqrt (Y:ℝ) :=
      mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.sqrt_nonneg _)
    linarith
  -- block bound
  have block_le : ∀ (c : ℝ) (_hc : 0 < c) (L H Y' : ℕ), 1 ≤ L → H - L + 1 ≤ Y' → 1 ≤ Y' →
      (Y':ℝ)^2 ≤ T →
      ‖∑ m ∈ Finset.Icc L H, wsum T ((m:ℝ) + c)‖ ≤ Cs * brk Y' T := by
    intro c hc L H Y' hL hlen hY' hY't
    by_cases hLH : L ≤ H
    · rw [sum_Icc_shift L H hL hLH (fun m => wsum T ((m:ℝ) + c))]
      have hc' : 0 < ((L:ℝ) - 1) + c := by
        have : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
        linarith
      have hstep : (∑ j ∈ Finset.Icc 1 (H - L + 1), wsum T (((L - 1 + j : ℕ):ℝ) + c))
          = ∑ j ∈ Finset.Icc 1 (H - L + 1),
              cexp (↑(-(T * Real.log (((L:ℝ) - 1 + c) + (j:ℝ)))) * I)
                / ↑√(((L:ℝ) - 1 + c) + (j:ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hcast : (((L - 1 + j : ℕ):ℝ) + c) = (j:ℝ) + ((L:ℝ) - 1 + c) := by
          have hL1 : ((L - 1 : ℕ):ℝ) = (L:ℝ) - 1 := by
            rw [Nat.cast_sub hL]; norm_num
          push_cast [hL1]
          ring
        rw [hcast]
        exact wsum_shift T ((L:ℝ) - 1 + c) j
      rw [hstep]
      have hlenY : (((H - L + 1 : ℕ)) : ℝ)^2 ≤ T := by
        have h1 : (((H - L + 1 : ℕ)) : ℝ) ≤ (Y':ℝ) := by exact_mod_cast hlen
        have h2 : (0:ℝ) ≤ (((H - L + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
        nlinarith [hY't]
      have hsh := hshift (((L:ℝ) - 1) + c) hc' (H - L + 1) (by omega) T hT hlenY
      refine le_trans hsh ?_
      apply mul_le_mul_of_nonneg_left _ hCspos.le
      exact brk_mono hlen hT
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
      exact mul_nonneg hCspos.le (brk_nonneg hY' hT)
  -- inner bound
  have inner_bound : ∀ a ∈ Finset.Icc 1 (min q (N + M)),
      ‖∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
          χ ((a + q * m : ℕ) : ZMod q) * wsum T ((a + q * m : ℕ) : ℝ)‖
        ≤ (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt ((q : ℝ) / (a : ℝ)) + Cs * brk Y T) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    have haq : a ≤ q := le_trans ha2 (min_le_left q (N + M))
    have haNM : a ≤ N + M := le_trans ha2 (min_le_right q (N + M))
    have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hper : ∀ m : ℕ, χ ((a + q * m : ℕ) : ZMod q) = χ (a : ZMod q) := by
      intro m
      have : ((a + q * m : ℕ) : ZMod q) = (a : ZMod q) := by
        push_cast
        rw [ZMod.natCast_self, zero_mul, add_zero]
      rw [this]
    have hgt : ∀ m : ℕ, ((a + q * m : ℕ) : ℝ) = (q:ℝ) * ((m:ℝ) + (a:ℝ)/(q:ℝ)) := by
      intro m
      have : ((a + q * m : ℕ) : ℝ) = (a:ℝ) + (q:ℝ) * (m:ℝ) := by push_cast; ring
      rw [this]; field_simp; ring
    have hfac : (∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
            χ ((a + q * m : ℕ) : ZMod q) * wsum T ((a + q * m : ℕ) : ℝ))
        = χ (a : ZMod q) * wsum T (q:ℝ) *
            ∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
              wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [hper m, hgt m, wsum_mul T (q:ℝ) ((m:ℝ) + (a:ℝ)/(q:ℝ)) hq0 (by positivity)]
      ring
    rw [hfac, norm_mul, norm_mul, norm_wsum hq0]
    have hS : ‖∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
          wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖ ≤ Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y T := by
      by_cases hle : (N + q - a) / q ≤ (N + M - a) / q
      · have hlo : N + 1 ≤ a + q * ((N + q - a) / q) :=
          (le_add_mul_iff_div_le hq0n haq).mpr le_rfl
        have hhi : a + q * ((N + M - a) / q) ≤ N + M :=
          (add_mul_le_iff_le_div hq0n haNM).mpr le_rfl
        have hlen : (N + M - a) / q - (N + q - a) / q + 1 ≤ Y :=
          div_interval_len_le hq hY hM hlo hhi
        by_cases h0 : (N + q - a) / q = 0
        · have hsplit : (Finset.Icc ((N + q - a) / q) ((N + M - a) / q))
              = insert 0 (Finset.Icc 1 ((N + M - a) / q)) := by
            rw [h0]; exact Icc_zero_eq_insert _
          rw [hsplit, Finset.sum_insert (by simp : (0:ℕ) ∉ Finset.Icc 1 ((N + M - a) / q))]
          have hnorm0 : ‖wsum T ((0:ℕ) + (a:ℝ)/(q:ℝ))‖ = Real.sqrt ((q:ℝ)/(a:ℝ)) := by
            have : (0:ℕ) + (a:ℝ)/(q:ℝ) = (a:ℝ)/(q:ℝ) := by push_cast; ring
            rw [this, norm_wsum (div_pos hapos hq0), ← Real.sqrt_inv, inv_div]
          have htail : ‖∑ m ∈ Finset.Icc 1 ((N + M - a) / q),
                wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖ ≤ Cs * brk Y T := by
            have hlen' : (N + M - a) / q - 1 + 1 ≤ Y := by omega
            exact block_le ((a:ℝ)/(q:ℝ)) (div_pos hapos hq0) 1 ((N + M - a) / q) Y
              le_rfl hlen' hY hYt
          calc ‖wsum T ((0:ℕ) + (a:ℝ)/(q:ℝ))
                + ∑ m ∈ Finset.Icc 1 ((N + M - a) / q), wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖
              ≤ ‖wsum T ((0:ℕ) + (a:ℝ)/(q:ℝ))‖
                + ‖∑ m ∈ Finset.Icc 1 ((N + M - a) / q), wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖ :=
                norm_add_le _ _
            _ ≤ Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y T := by
                rw [hnorm0]; exact add_le_add le_rfl htail
        · have hge1 : 1 ≤ (N + q - a) / q := Nat.one_le_iff_ne_zero.mpr h0
          have hblk := block_le ((a:ℝ)/(q:ℝ)) (div_pos hapos hq0) ((N + q - a) / q)
            ((N + M - a) / q) Y hge1 hlen hY hYt
          exact le_trans hblk (le_add_of_nonneg_left (Real.sqrt_nonneg _))
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCspos.le (brk_nonneg hY hT))
    have hmain : ‖χ (a : ZMod q)‖ * (Real.sqrt (q:ℝ))⁻¹
          * ‖∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
              wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖
        ≤ (Real.sqrt (q:ℝ))⁻¹ * (Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y T) := by
      have h1 : ‖χ (a : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      have h2 : (0:ℝ) ≤ (Real.sqrt (q:ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hposS : (0:ℝ) ≤ ‖∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
              wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖ := norm_nonneg _
      have hposR : (0:ℝ) ≤ 1 * (Real.sqrt (q:ℝ))⁻¹ := by positivity
      calc ‖χ (a : ZMod q)‖ * (Real.sqrt (q:ℝ))⁻¹
            * ‖∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
                wsum T ((m:ℝ) + (a:ℝ)/(q:ℝ))‖
          ≤ 1 * (Real.sqrt (q:ℝ))⁻¹ * (Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y T) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right h1 h2
            · exact hS
            · exact hposS
            · exact hposR
        _ = (Real.sqrt (q:ℝ))⁻¹ * (Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y T) := by ring
    exact hmain
  -- assemble
  have hrewrite : (∑ n ∈ Finset.Icc (N + 1) (N + M),
            χ (n : ZMod q) *
              Complex.exp ((((2 * Real.pi * (-(T / (2 * Real.pi)) * Real.log (n : ℝ))) : ℝ) : ℂ) *
                Complex.I) / Real.sqrt (n : ℝ))
        = ∑ n ∈ Finset.Icc (N + 1) (N + M), χ n * wsum T (n:ℝ) :=
    Finset.sum_congr rfl (fun n _ => target_summand χ T n)
  rw [hrewrite, interval_residue_decomp q N M hq (fun n => χ n * wsum T (n:ℝ))]
  calc ‖∑ a ∈ Finset.Icc 1 (min q (N + M)),
          ∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
            χ ((a + q * m : ℕ) : ZMod q) * wsum T ((a + q * m : ℕ) : ℝ)‖
      ≤ ∑ a ∈ Finset.Icc 1 (min q (N + M)),
          ‖∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q),
            χ ((a + q * m : ℕ) : ZMod q) * wsum T ((a + q * m : ℕ) : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 (min q (N + M)),
          (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt ((q : ℝ) / (a : ℝ)) + Cs * brk Y T) :=
        Finset.sum_le_sum inner_bound
    _ = (Real.sqrt (q : ℝ))⁻¹ *
          ∑ a ∈ Finset.Icc 1 (min q (N + M)),
            (Real.sqrt ((q : ℝ) / (a : ℝ)) + Cs * brk Y T) := by rw [Finset.mul_sum]
    _ ≤ (Real.sqrt (q : ℝ))⁻¹ * (2*(q:ℝ) + (q:ℝ) * (Cs * brk Y T)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
        rw [Finset.sum_add_distrib]
        have h1 : (∑ a ∈ Finset.Icc 1 (min q (N + M)), Real.sqrt ((q:ℝ)/(a:ℝ))) ≤ 2*(q:ℝ) :=
          sqrt_sum_div_le q (min q (N + M)) (min_le_left q (N + M))
        have h2 : (∑ a ∈ Finset.Icc 1 (min q (N + M)), Cs * brk Y T)
            = (((min q (N + M) : ℕ)) : ℝ) * (Cs * brk Y T) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          congr 1
        have h3 : (((min q (N + M) : ℕ)) : ℝ) * (Cs * brk Y T) ≤ (q:ℝ) * (Cs * brk Y T) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hCspos.le (brk_nonneg hY hT))
          exact_mod_cast min_le_left q (N + M)
        rw [h2]
        linarith
    _ = 2*Real.sqrt (q:ℝ) + Cs*Real.sqrt (q:ℝ)*brk Y T := by
        rw [show (Real.sqrt (q:ℝ))⁻¹ * (2*(q:ℝ) + (q:ℝ) * (Cs * brk Y T))
              = 2*((Real.sqrt (q:ℝ))⁻¹ * (q:ℝ))
                + ((Real.sqrt (q:ℝ))⁻¹ * (q:ℝ)) * (Cs * brk Y T) by ring]
        rw [inv_sqrt_mul_self hq0]; ring
    _ ≤ (Cs + 2) * Real.sqrt (q : ℝ) *
          (T ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
            T ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by
        unfold brk
        have hs0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
        have hb : (1:ℝ) ≤ T ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
              T ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ) := hbrk1
        have hkey : (0:ℝ) ≤ Real.sqrt (q:ℝ) * (T ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
              T ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ) - 1) :=
          mul_nonneg hs0 (by linarith)
        nlinarith [hkey, hs0, hb, hCspos.le]

end

end Commons.NumberTheory.DirichletCharacter
