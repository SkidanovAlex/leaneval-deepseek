import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.LgUpSpec
import Submission.Work.CNum.LogUpMSpec
import Submission.Work.CNum.LogUpMSpecPos
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.SerInvStep
import Submission.Work.CNum.SerInvTermC
import Submission.Work.CNum.SerTailBound
import Submission.Work.CNum.SerAnalyticSharpTail
import Submission.Work.ANum.h_log_bound
import Submission.Work.CNum.SerCoreIneqR

/-!
# `Work.CNum.SerUpSpecR` — soundness of the certificate `serUp`

`Work.CNum.serUp x y e` is the fixed-point (mantissa, scale `SC = 2^30`) upper bound for
`Real.log ‖h w‖`, where `h = Submission.CDTPlan.hauptH` is the hauptmodul and `w` lies in the
closed ball of centre `c = (x + iy)/SC` and radius `ρ = e/SC`.

The certificate evaluates the logarithmic series

  `log ‖h w‖ ≤ log 256 + log R + 24 Σ_{J=1}^{44} log (‖1 + c^J‖ + a_J) + 24 R^45/(1-R)`,
  `R = ‖c‖ + ρ`,

where the perturbation coefficients `a_J = (45-J) σ^{J-1} ρ` are *countdown*-shaped: the term
with exponent `J` carries the coefficient `45 - J`.  The analysis therefore splits into

* `SerAnalyticSharpTail`: a sharp analytic bound with the exact telescoping perturbation
  `R^J - c^J` for the first 44 exponents and the sharpened geometric tail;
* `SerCoreIneq`: the global numerical comparison of the two sums, which trades the surplus of
  the *small* coefficients against the deficit of the large ones and against the log-versus-
  linear slack of the tail;
* `SerAuxB_specR` below: the induction over the certificate's recursion, using `SerInvStep`
  (the invariant is preserved) and `SerInvTermC` (each term is bounded).

The case `e = 0` is handled separately, with the cruder tail bound of `Work.ANum.h_log_bound`
(no tail slack is needed there, since the two perturbation coefficients in play are both `0`).
-/

namespace Work.CNum

open Work.ANum
open scoped BigOperators

/-! ## `|x|,|y| < 2^30` when `‖(x+iy)/SC‖ < 1` -/

lemma natAbs_lt_of_norm_ltR {x y : ℤ} (h : ‖spt x y‖ < 1) :
    Int.natAbs x < 2 ^ 30 ∧ Int.natAbs y < 2 ^ 30 := by
  have h1 : Real.sqrt ((x * x + y * y).toNat : ℝ) / (SC : ℝ) < 1 := by
    have h2 := h
    rw [spt, norm_pt] at h2
    exact h2
  have h2 : Real.sqrt ((x * x + y * y).toNat : ℝ) < (SC : ℝ) := by
    rw [div_lt_one SC_posR] at h1
    exact h1
  have h3 : ((x * x + y * y).toNat : ℝ) < (SC : ℝ) ^ 2 := by
    calc ((x * x + y * y).toNat : ℝ)
        = (Real.sqrt ((x * x + y * y).toNat : ℝ)) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
      _ < (SC : ℝ) ^ 2 := pow_lt_pow_left₀ h2 (Real.sqrt_nonneg _) (by norm_num)
  have h4 : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 < (SC : ℝ) ^ 2 := by
    rw [← cast_sq_add]
    exact h3
  have hx2 : (x : ℝ) ^ 2 < (SC : ℝ) ^ 2 :=
    lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg _)) h4
  have hy2 : (y : ℝ) ^ 2 < (SC : ℝ) ^ 2 :=
    lt_of_le_of_lt (le_add_of_nonneg_left (sq_nonneg _)) h4
  have hxa : |(x : ℝ)| < (SC : ℝ) := by
    rw [sq_lt_sq] at hx2
    rwa [abs_of_pos SC_posR] at hx2
  have hya : |(y : ℝ)| < (SC : ℝ) := by
    rw [sq_lt_sq] at hy2
    rwa [abs_of_pos SC_posR] at hy2
  have hSC30 : SC = (2 : ℤ) ^ 30 := by norm_num [Work.ANum.SC]
  have hxl : -(SC : ℤ) < x := by
    have := (abs_lt.mp hxa).1
    exact_mod_cast this
  have hxu : x < SC := by
    have := (abs_lt.mp hxa).2
    exact_mod_cast this
  have hyl : -(SC : ℤ) < y := by
    have := (abs_lt.mp hya).1
    exact_mod_cast this
  have hyu : y < SC := by
    have := (abs_lt.mp hya).2
    exact_mod_cast this
  rw [hSC30] at hxl hxu hyl hyu
  constructor <;> omega

/-! ## Base case -/

lemma SerInvZeroR {x y e : ℤ} (he : 0 ≤ e) (hr1 : srad x y e < 1) :
    SerInv x y e (nrmUp x y + e) 0 x y 0 SC := by
  have he0 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  have hc1 : ‖spt x y‖ < 1 := by
    have h := hr1
    rw [srad] at h
    linarith
  obtain ⟨hxa, hya⟩ := natAbs_lt_of_norm_ltR hc1
  refine ⟨le_refl 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m2r_zero]; norm_num
  · rw [srad, pow_zero, m2r_SC]
  · rw [m2r_SC]; norm_num
  · have : spt x y ^ (0 + 1) - spt x y = 0 := by ring
    rw [this, norm_zero, m2r_zero]
  · have h1 : Int.natAbs (SC + x) ≤ Int.natAbs SC + Int.natAbs x := Int.natAbs_add_le SC x
    have h3 : Int.natAbs SC = (2 : ℕ) ^ 30 := by
      rw [show SC = (2:ℤ)^30 by norm_num [Work.ANum.SC]]
      exact Int.natAbs_natCast _
    omega
  · omega

/-! ## The induction over the countdown -/

lemma SerAuxB_specR {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : m2r σ < 1)
    (hRσ : srad x y e ≤ m2r σ)
    (hterm : ∀ {k : ℕ}, k < SERM → ∀ {px py pe sg : ℤ}, SerInv x y e σ k px py pe sg →
      sTc x y e k ≤ m2r (logUpM (shi x y σ e (SERM - 1 - k) px py pe sg))) :
    ∀ m, m ≤ SERM → ∀ (px py pe sg acc : ℤ), SerInv x y e σ (SERM - m) px py pe sg →
      m2r acc + 24 * (∑ J ∈ Finset.Icc 1 m, sTc x y e (SERM - J))
        ≤ m2r (serAuxB x y σ e m px py pe sg acc) := by
  intro m
  induction m with
  | zero =>
      intro hm px py pe sg acc h
      simp [serAuxB]
  | succ m ih =>
      intro hm px py pe sg acc h
      have hm' : m ≤ SERM := by omega
      have hk : SERM - (m + 1) < SERM := by omega
      have hthis := hterm hk h
      have hidx : SERM - 1 - (SERM - (m + 1)) = m := by omega
      have hthis' : sTc x y e (SERM - (m + 1)) ≤ m2r (logUpM (shi x y σ e m px py pe sg)) := by
        rw [hidx] at hthis
        exact hthis
      have hst := SerInvStep he hσlt hRσ h
      have hidx2 : SERM - (m + 1) + 1 = SERM - m := by omega
      have hst' : SerInv x y e σ (SERM - m) (snx x y px py) (sny x y px py) (snpe σ pe) (snsg σ sg) := by
        rw [hidx2] at hst
        exact hst
      have hIH := ih hm' (snx x y px py) (sny x y px py) (snpe σ pe) (snsg σ sg)
        (acc + 24 * logUpM (shi x y σ e m px py pe sg)) hst'
      rw [m2r_add, m2r_mul_int'] at hIH
      push_cast at hIH
      have hunf : serAuxB x y σ e (m + 1) px py pe sg acc
          = serAuxB x y σ e m (snx x y px py) (sny x y px py) (snpe σ pe) (snsg σ sg)
              (acc + 24 * logUpM (shi x y σ e m px py pe sg)) := by
        simp only [serAuxB, snx, sny, snpe, snsg, shi]
      rw [hunf]
      have hsum : (∑ J ∈ Finset.Icc 1 (m + 1), sTc x y e (SERM - J))
          = sTc x y e (SERM - (m + 1)) + ∑ J ∈ Finset.Icc 1 m, sTc x y e (SERM - J) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), add_comm]
      rw [hsum]
      linarith


/-! ## The per-term interval step used to apply the core inequality -/

/-- For `u ∈ [1-c^J, 1+c^J]`, `log (u+δ) - log (u+a)` is at most the larger of its two endpoint
values (the map `u ↦ (u+δ)/(u+a)` is monotone). -/
lemma log_term_le_max_endpointsR {u δ a c : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hu1 : 1 - c ≤ u) (hu2 : u ≤ 1 + c) (hc1 : c < 1) :
    Real.log (u + δ) - Real.log (u + a)
      ≤ max (Real.log (1 - c + δ) - Real.log (1 - c + a))
            (Real.log (1 + c + δ) - Real.log (1 + c + a)) := by
  have hupos : 0 < u + δ := by linarith [hu1, hc1, hδ]
  have hupos' : 0 < u + a := by linarith [hu1, hc1, ha]
  have h1 : 0 < 1 - c + δ := by linarith
  have h1' : 0 < 1 - c + a := by linarith
  have h2 : 0 < 1 + c + δ := by linarith
  have h2' : 0 < 1 + c + a := by linarith
  rcases le_total a δ with h | h
  · have hratio : (u + δ) / (u + a) ≤ (1 - c + δ) / (1 - c + a) := by
      rw [div_le_div_iff₀ hupos' h1']
      nlinarith [hu1, h]
    have hlog := Real.log_le_log (div_pos hupos hupos') hratio
    rw [Real.log_div (ne_of_gt hupos) (ne_of_gt hupos'),
      Real.log_div (ne_of_gt h1) (ne_of_gt h1')] at hlog
    exact le_trans hlog (le_max_left _ _)
  · have hratio : (u + δ) / (u + a) ≤ (1 + c + δ) / (1 + c + a) := by
      rw [div_le_div_iff₀ hupos' h2']
      nlinarith [hu2, h]
    have hlog := Real.log_le_log (div_pos hupos hupos') hratio
    rw [Real.log_div (ne_of_gt hupos) (ne_of_gt hupos'),
      Real.log_div (ne_of_gt h2) (ne_of_gt h2')] at hlog
    exact le_trans hlog (le_max_right _ _)


/-! ## auxiliary facts -/

lemma nrmUp_le_pow36R {x y : ℤ} (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34) :
    nrmUp x y ≤ 2 ^ 36 := by
  obtain ⟨hlt, h5⟩ := natAbs_sq_add hx hy
  have h6 : (x * x + y * y).toNat ≤ 2 ^ 69 := by
    rw [h5]
    have hx2 := Nat.pow_le_pow_left hx 2
    have hy2 := Nat.pow_le_pow_left hy 2
    calc x.natAbs ^ 2 + y.natAbs ^ 2 ≤ (2 ^ 34) ^ 2 + (2 ^ 34) ^ 2 := Nat.add_le_add hx2 hy2
      _ = 2 ^ 69 := by norm_num
  have h1 : ((isqrt (x * x + y * y).toNat : ℤ) : ℝ) ≤ 2 ^ 35 := by
    have h3 := sqDn_le_sqrt_toNat hlt
    have h4 : Real.sqrt (((x * x + y * y).toNat : ℕ) : ℝ) ≤ (2 ^ 35 : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      have h7 : (((x * x + y * y).toNat : ℕ) : ℝ) ≤ 2 ^ 69 := by exact_mod_cast h6
      calc (((x * x + y * y).toNat : ℕ) : ℝ) ≤ 2 ^ 69 := h7
        _ ≤ (2 ^ 35 : ℝ) ^ 2 := by norm_num
    linarith
  have h2 : (isqrt (x * x + y * y).toNat : ℤ) ≤ 2 ^ 35 := by exact_mod_cast h1
  simp only [nrmUp, sqUp]
  omega

/-- the per-term comparison with `a_J` -/
lemma sTc_eqR {x y e : ℤ} {J : ℕ} (hJ : 1 ≤ J) :
    sTc x y e (J - 1)
      = Real.log (‖(1 : ℂ) + spt x y ^ J‖
          + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e) := by
  simp only [sTc, scoef]
  have h1 : J - 1 + 1 = J := by omega
  have h2 : SERM - (J - 1) = SERM + 1 - J := by omega
  rw [h1, h2]

/-- reindexing the certificate's sum -/
lemma sum_sTc_reflectR {x y e : ℤ} :
    (∑ J ∈ Finset.Icc 1 SERM, sTc x y e (SERM - J))
      = ∑ J ∈ Finset.Icc 1 SERM, sTc x y e (J - 1) := by
  refine Finset.sum_bij (fun J _ => SERM + 1 - J) ?_ ?_ ?_ ?_
  · intro J hJ
    simp only [Finset.mem_Icc] at hJ ⊢
    omega
  · intro J1 hJ1 J2 hJ2 heq
    simp only [Finset.mem_Icc] at hJ1 hJ2
    omega
  · intro K hK
    simp only [Finset.mem_Icc] at hK
    exact ⟨SERM + 1 - K, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro J hJ
    congr 1
    omega

/-- the per-term interval bound for the core inequality -/
lemma hterm_coreR {x y e : ℤ} (he : 0 ≤ e) (hc1 : ‖spt x y‖ < 1) {J : ℕ} (hJ : 1 ≤ J) :
    Real.log (‖(1 : ℂ) + spt x y ^ J‖ + (srad x y e ^ J - ‖spt x y‖ ^ J))
        - Real.log (‖(1 : ℂ) + spt x y ^ J‖
            + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e)
      ≤ max (Real.log (1 - ‖spt x y‖ ^ J + (srad x y e ^ J - ‖spt x y‖ ^ J))
            - Real.log (1 - ‖spt x y‖ ^ J
                + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e))
            (Real.log (1 + ‖spt x y‖ ^ J + (srad x y e ^ J - ‖spt x y‖ ^ J))
            - Real.log (1 + ‖spt x y‖ ^ J
                + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e)) := by
  have hsrad0 : 0 ≤ srad x y e := by
    rw [srad]; exact add_nonneg (norm_nonneg _) (m2r_nonneg_NrmSpec he)
  have hc0 : 0 ≤ ‖spt x y‖ := norm_nonneg _
  have hup1 : 1 - ‖spt x y‖ ^ J ≤ ‖(1 : ℂ) + spt x y ^ J‖ := by
    have h := norm_add_le ((1 : ℂ) + spt x y ^ J) (-(spt x y ^ J))
    rw [show (1 : ℂ) + spt x y ^ J + -(spt x y ^ J) = 1 by ring, norm_one, norm_neg,
      norm_pow] at h
    linarith
  have hup2 : ‖(1 : ℂ) + spt x y ^ J‖ ≤ 1 + ‖spt x y‖ ^ J := by
    have h := norm_add_le (1 : ℂ) (spt x y ^ J)
    rw [norm_one, norm_pow] at h
    exact h
  have hcJ : ‖spt x y‖ ^ J < 1 := pow_lt_one₀ hc0 hc1 (by omega)
  exact log_term_le_max_endpointsR
    (by
      have : ‖spt x y‖ ^ J ≤ srad x y e ^ J := by
        apply pow_le_pow_left₀ hc0
        rw [srad]; exact le_add_of_nonneg_right (m2r_nonneg_NrmSpec he)
      linarith)
    (by
      have h1 : (0 : ℝ) ≤ ((SERM + 1 - J : ℕ) : ℝ) := Nat.cast_nonneg _
      have h3 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
      exact mul_nonneg (mul_nonneg h1 (pow_nonneg hsrad0 _)) h3)
    hup1 hup2 hcJ


/-! ## The two analytic inputs -/


/-- Reindexing a `range`-sum of `f (n+1)` as an `Icc 1 SERM`-sum. -/
lemma sum_range_succ_IccR (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range SERM, f (n + 1)) = ∑ J ∈ Finset.Icc 1 SERM, f J := by
  refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n1 _ n2 _ h
    omega
  · intro J hJ
    simp only [Finset.mem_Icc] at hJ
    exact ⟨J - 1, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro n _
    rfl

/-- `SerUpSpecR` for `e = 0`: the two perturbation coefficients in play both vanish, so the
cruder tail bound of `Work.ANum.h_log_bound` suffices. -/
theorem SerUpSpecZeroR {x y : ℤ} {w : ℂ} (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34)
    (hσ1 : m2r (nrmUp x y + (0 : ℤ)) < 1) (hσ0 : m2r (0 : ℤ) < m2r (nrmDn x y))
    (hw : ‖w - spt x y‖ ≤ m2r (0 : ℤ)) :
    Real.log ‖Submission.CDTPlan.hauptH w‖ ≤ m2r (serUp x y (0 : ℤ)) := by
  have hw0 : w = spt x y := by
    have h : w - spt x y = 0 := by simpa [m2r_zero] using hw
    exact sub_eq_zero.mp h
  subst hw0
  have hσ1' : m2r (nrmUp x y) < 1 := by simpa using hσ1
  have hσ0' : 0 < m2r (nrmDn x y) := by simpa only [m2r_zero] using hσ0
  have hNorm : ‖spt x y‖ ≤ m2r (nrmUp x y) := by simpa only [spt] using NrmUpSpec hx hy
  have hNormDn : m2r (nrmDn x y) ≤ ‖spt x y‖ := by simpa only [spt] using NrmDnSpec hx hy
  have hcpos : 0 < ‖spt x y‖ := lt_of_lt_of_le hσ0' hNormDn
  have hc1 : ‖spt x y‖ < 1 := lt_of_le_of_lt hNorm hσ1'
  have hsrad : srad x y (0 : ℤ) = ‖spt x y‖ := by rw [srad, m2r_zero, add_zero]
  have hRσ : srad x y (0 : ℤ) ≤ m2r (nrmUp x y + (0 : ℤ)) := by
    rw [srad, m2r_add, m2r_zero, add_zero, add_zero]; exact hNorm
  -- the analytic bound
  have hlog := h_log_bound (spt x y) (0 : ℝ) le_rfl hcpos hcpos (by linarith [hc1]) SERM (spt x y)
    (by simp)
  have hlog' : Real.log ‖Submission.CDTPlan.hauptH (spt x y)‖ ≤ Real.log 256
      + Real.log ‖spt x y‖
      + 24 * (∑ n ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + spt x y ^ (n + 1)‖)
      + 24 * (‖spt x y‖ ^ (SERM + 1) / (1 - ‖spt x y‖)) := by
    simpa using hlog
  have hsum1 : (∑ n ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + spt x y ^ (n + 1)‖)
      = ∑ J ∈ Finset.Icc 1 SERM, Real.log ‖(1 : ℂ) + spt x y ^ J‖ :=
    sum_range_succ_IccR (fun J => Real.log ‖(1 : ℂ) + spt x y ^ J‖)
  -- the certificate
  have hcert := SerAuxB_specR (le_refl (0 : ℤ)) hσ1' hRσ
      (SerInvTermC (le_refl (0 : ℤ)) hσ1' hRσ) SERM (le_refl SERM) x y 0 SC 0
      (by simpa using SerInvZeroR (le_refl (0 : ℤ)) (by rw [hsrad]; exact hc1))
  rw [m2r_zero, zero_add] at hcert
  have hS : (∑ J ∈ Finset.Icc 1 SERM, sTc x y (0 : ℤ) (SERM - J))
      = ∑ J ∈ Finset.Icc 1 SERM, Real.log ‖(1 : ℂ) + spt x y ^ J‖ := by
    rw [sum_sTc_reflectR]
    refine Finset.sum_congr rfl (fun J hJ => ?_)
    rw [Finset.mem_Icc] at hJ
    rw [sTc_eqR (by omega)]
    simp [m2r_zero]
  rw [hS] at hcert
  -- the tail bound and the two logarithm bounds
  have htail := SerTailBound (le_refl (0 : ℤ)) hσ1' hRσ
  rw [hsrad] at htail
  have hσge1 : 1 ≤ nrmUp x y := by
    have : 1 ≤ nrmUp x y := by
      simp only [nrmUp, sqUp]
      omega
    omega
  have hσ60 : nrmUp x y ≤ 2 ^ 60 := by
    have h1 : nrmUp x y ≤ 2 ^ 36 := nrmUp_le_pow36R hx hy
    norm_num
    omega
  have hlogup : Real.log ‖spt x y‖ ≤ m2r (logUpM (nrmUp x y + (0 : ℤ))) := by
    have h := LogUpMSpec_pos hσge1 (by simpa using hσ60) (by simpa using hNorm) hcpos
    simpa using h
  have hlg : Real.log 256 ≤ m2r (lgUp (256 * SC)) := by
    have h := lgUp_spec (n := 256 * SC) (by nlinarith [SC_pos]) (by norm_num [Work.ANum.SC])
    have h2 : m2r (256 * SC) = (256 : ℝ) := by rw [m2r_mul_SC']; norm_num
    rwa [h2] at h
  have hserUp : m2r (serUp x y (0 : ℤ)) = m2r (lgUp (256 * SC))
      + m2r (logUpM (nrmUp x y + (0 : ℤ)))
      + m2r (serAuxB x y (nrmUp x y + (0 : ℤ)) (0 : ℤ) SERM x y 0 SC 0)
      + 24 * m2r (divUz (SC * powM true (nrmUp x y + (0 : ℤ)) (SERM + 1)) (SC - (nrmUp x y + (0 : ℤ)))
          + divUz (SC * mulU (0 : ℤ) ((SERM + 1) * powM true (nrmUp x y + (0 : ℤ)) SERM))
              ((SC - (nrmUp x y + (0 : ℤ))) * (SC - (nrmUp x y + (0 : ℤ)))) + 4) := by
    rw [serUp]
    simp only [m2r_add, m2r_mul_int']
    norm_num
  simp only [add_zero] at htail hlogup hserUp hcert
  linarith [hlog', hsum1, hcert, htail, hlogup, hlg, hserUp]

theorem SerUpSpecAuxR {x y e : ℤ} {w : ℂ} (he : 0 ≤ e) (hepos : 0 < e)
    (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34)
    (hσ1 : m2r (nrmUp x y + e) < 1) (hσ0 : m2r e < m2r (nrmDn x y))
    (hσ8 : m2r (nrmUp x y + e) ≤ 4 / 5) (hρs : m2r e ≤ 1 / 1000)
    (hw : ‖w - spt x y‖ ≤ m2r e) :
    Real.log ‖Submission.CDTPlan.hauptH w‖ ≤ m2r (serUp x y e) := by
  have he0 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  have hρ : 0 < m2r e := by
    rw [m2r]
    exact div_pos (by exact_mod_cast hepos) SC_posR
  have hNorm : ‖spt x y‖ ≤ m2r (nrmUp x y) := by simpa only [spt] using NrmUpSpec hx hy
  have hNormDn : m2r (nrmDn x y) ≤ ‖spt x y‖ := by simpa only [spt] using NrmDnSpec hx hy
  have hρlt : m2r e < ‖spt x y‖ := lt_of_lt_of_le hσ0 hNormDn
  have hcpos : 0 < ‖spt x y‖ := lt_of_le_of_lt he0 hρlt
  have hRσ : srad x y e ≤ m2r (nrmUp x y + e) := by
    rw [srad, m2r_add]; exact add_le_add hNorm le_rfl
  have hR1 : srad x y e < 1 := lt_of_le_of_lt hRσ hσ1
  have hsrad0 : 0 ≤ srad x y e := by rw [srad]; exact add_nonneg (norm_nonneg _) he0
  have hc1 : ‖spt x y‖ < 1 :=
    lt_of_le_of_lt (by rw [srad]; exact le_add_of_nonneg_right he0) hR1
  have hwR : ‖w‖ ≤ srad x y e := by
    have h : ‖w‖ ≤ ‖w - spt x y‖ + ‖spt x y‖ := by
      have := norm_add_le (w - spt x y) (spt x y)
      rwa [sub_add_cancel] at this
    rw [srad]; linarith
  -- (1) the analytic bound
  have hana := SerAnalyticSharpTail hcpos hρ hρlt rfl hwR hw (by rw [srad]) hR1
  -- (2) the certificate's term bound
  have hcert := SerAuxB_specR he hσ1 hRσ (SerInvTermC he hσ1 hRσ) SERM (le_refl SERM) x y 0 SC 0
    (by simpa using SerInvZeroR he hR1)
  rw [m2r_zero, zero_add] at hcert
  -- (3) reindex the certificate's sum and identify the terms
  have hS : (∑ J ∈ Finset.Icc 1 SERM, sTc x y e (SERM - J))
      = ∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + spt x y ^ J‖
          + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e) := by
    rw [sum_sTc_reflectR]
    exact Finset.sum_congr rfl (fun J hJ => by
      rw [Finset.mem_Icc] at hJ
      exact sTc_eqR (by omega))
  rw [hS] at hcert
  -- (4) the core inequality
  have hcoreapp : (∑ J ∈ Finset.Icc 1 SERM,
        Real.log (‖(1 : ℂ) + spt x y ^ J‖ + (srad x y e ^ J - ‖spt x y‖ ^ J)))
      ≤ (∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + spt x y ^ J‖
            + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e))
        + (srad x y e ^ (2 * (SERM + 1)) / (2 * (1 - srad x y e ^ 2))
            - srad x y e ^ (3 * (SERM + 1)) / (3 * (1 - srad x y e ^ 3))) := by
    have hbound : (∑ J ∈ Finset.Icc 1 SERM,
        (Real.log (‖(1 : ℂ) + spt x y ^ J‖ + (srad x y e ^ J - ‖spt x y‖ ^ J))
          - Real.log (‖(1 : ℂ) + spt x y ^ J‖
              + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e)))
        ≤ ∑ J ∈ Finset.Icc 1 SERM, max
            (Real.log (1 - ‖spt x y‖ ^ J + (srad x y e ^ J - ‖spt x y‖ ^ J))
              - Real.log (1 - ‖spt x y‖ ^ J
                  + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e))
            (Real.log (1 + ‖spt x y‖ ^ J + (srad x y e ^ J - ‖spt x y‖ ^ J))
              - Real.log (1 + ‖spt x y‖ ^ J
                  + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e)) := by
      refine Finset.sum_le_sum (fun J hJ => ?_)
      rw [Finset.mem_Icc] at hJ
      exact hterm_coreR he hc1 (by omega)
    have hR8 : ‖spt x y‖ + m2r e ≤ 4 / 5 := le_trans hRσ hσ8
    have hmax : (∑ J ∈ Finset.Icc 1 SERM, max
        (Real.log (1 - ‖spt x y‖ ^ J + (srad x y e ^ J - ‖spt x y‖ ^ J))
          - Real.log (1 - ‖spt x y‖ ^ J
              + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e))
        (Real.log (1 + ‖spt x y‖ ^ J + (srad x y e ^ J - ‖spt x y‖ ^ J))
          - Real.log (1 + ‖spt x y‖ ^ J
              + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e)))
        ≤ (srad x y e ^ (2 * (SERM + 1)) / (2 * (1 - srad x y e ^ 2))
            - srad x y e ^ (3 * (SERM + 1)) / (3 * (1 - srad x y e ^ 3))) := by
      have h := SerCoreIneqR (c := ‖spt x y‖) (ρ := m2r e) hcpos hρ hρlt hR1 hR8 hρs
      simpa only [SERM, srad] using h
    have hsumsub := Finset.sum_sub_distrib (s := Finset.Icc 1 SERM)
      (f := fun J => Real.log (‖(1 : ℂ) + spt x y ^ J‖ + (srad x y e ^ J - ‖spt x y‖ ^ J)))
      (g := fun J => Real.log (‖(1 : ℂ) + spt x y ^ J‖
              + ((SERM + 1 - J : ℕ) : ℝ) * srad x y e ^ (J - 1) * m2r e))
    linarith [hmax]
  -- (5) the tail, the two log bounds
  have htail := SerTailBound he hσ1 hRσ
  have hσge1 : 1 ≤ nrmUp x y + e := by
    have : 1 ≤ nrmUp x y := by
      simp only [nrmUp, sqUp]
      omega
    omega
  have hσ60 : nrmUp x y + e ≤ 2 ^ 60 := by
    have h1 : nrmUp x y ≤ 2 ^ 36 := nrmUp_le_pow36R hx hy
    have h2 : e < SC := by
      have h3 : (e : ℝ) < (SC : ℝ) := by
        have h4 : m2r e < 1 := lt_of_lt_of_le hρlt hc1.le
        rw [m2r, div_lt_one SC_posR] at h4
        exact h4
      exact_mod_cast h3
    have h4 : SC = (2 : ℤ) ^ 30 := by norm_num [Work.ANum.SC]
    omega
  have hlogup : Real.log (srad x y e) ≤ m2r (logUpM (nrmUp x y + e)) :=
    LogUpMSpec_pos hσge1 hσ60 hRσ (lt_of_lt_of_le hcpos (by rw [srad]; exact le_add_of_nonneg_right he0))
  have hlg : Real.log 256 ≤ m2r (lgUp (256 * SC)) := by
    have h := lgUp_spec (n := 256 * SC) (by nlinarith [SC_pos]) (by norm_num [Work.ANum.SC])
    have h2 : m2r (256 * SC) = (256 : ℝ) := by rw [m2r_mul_SC']; norm_num
    rwa [h2] at h
  have hserUp : m2r (serUp x y e) = m2r (lgUp (256 * SC)) + m2r (logUpM (nrmUp x y + e))
      + m2r (serAuxB x y (nrmUp x y + e) e SERM x y 0 SC 0)
      + 24 * m2r (divUz (SC * powM true (nrmUp x y + e) (SERM + 1)) (SC - (nrmUp x y + e))
          + divUz (SC * mulU e ((SERM + 1) * powM true (nrmUp x y + e) SERM))
              ((SC - (nrmUp x y + e)) * (SC - (nrmUp x y + e))) + 4) := by
    rw [serUp]
    simp only [m2r_add, m2r_mul_int']
    norm_num
  linarith [hana, hcert, hcoreapp, htail, hlogup, hlg, hserUp]


/-- **The assignment.** `serUp` is a sound upper bound for `log ‖h w‖` on the closed ball of
centre `c = (x+iy)/SC` and radius `ρ = e/SC`. -/
theorem SerUpSpecR {x y e : ℤ} {w : ℂ} (he : 0 ≤ e) (hx : Int.natAbs x ≤ 2 ^ 34)
    (hy : Int.natAbs y ≤ 2 ^ 34)
    (hσ1 : Work.ANum.m2r (Work.CNum.nrmUp x y + e) < 1)
    (hσ0 : Work.ANum.m2r e < Work.ANum.m2r (Work.CNum.nrmDn x y))
    (hσ8 : Work.ANum.m2r (Work.CNum.nrmUp x y + e) ≤ 4 / 5)
    (hρs : Work.ANum.m2r e ≤ 1 / 1000)
    (hw : ‖w - ((x : ℝ) + (y : ℝ) * Complex.I) / (Work.ANum.SC : ℝ)‖ ≤ Work.ANum.m2r e) :
    Real.log ‖Submission.CDTPlan.hauptH w‖ ≤ Work.ANum.m2r (Work.CNum.serUp x y e) := by
  by_cases he0 : e = 0
  · subst he0
    exact SerUpSpecZeroR hx hy (by simpa using hσ1) (by simpa using hσ0)
      (by simpa only [spt] using hw)
  · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
    exact SerUpSpecAuxR he hepos hx hy hσ1 hσ0 hσ8 hρs (by simpa only [spt] using hw)


end Work.CNum
