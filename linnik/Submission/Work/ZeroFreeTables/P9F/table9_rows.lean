/-
# ZeroFreeTables.P9F.table9_rows

The twenty row lemmas of the Table 9 assembly: combining the numerical certificate
(`rowcert_*`), the exponential enclosures (`expb_*`) and the monotonicity of
`x ↦ La θ λ x − La θ λ (x − c)` with the Lemma 9.2 inequality (`hcore`) gives a
contradiction at each tabulated point.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9F.Defs
import Submission.Work.ZeroFreeTables.P9F.La_defs
import Submission.Work.ZeroFreeTables.P9F.table9_certs
import Submission.Work.ZeroFreeTables.P9F.table9_expb
import Submission.Work.ZeroFreeTables.P9F.tf71F_real_eq
import Submission.Work.ZeroFreeTables.testFn7_1
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables.P9F

open Work.ZeroFreeTables

/-- `La θ λ 0 = F(0)` in the explicit form of HB Lemma 7.1. -/
theorem La_zero (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    La θ lam 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
  have h1 := TestFn_F_eq_integral (tf71T θ lam hθ0 hθ1 hlam) 0
  have h2 : (tf71T θ lam hθ0 hθ1 hlam).F 0 = La θ lam 0 := by
    rw [h1]
    unfold La
    apply intervalIntegral.integral_congr
    intro t _
    simp [tf71T]
  rw [← h2]
  exact tf71Fc_zero_re θ lam hθ0 hθ1 hlam

theorem rowcontra_034_1283 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (17/50 : ℝ)) (hlajc : laj ≤ (1283/1000 : ℝ))
    (hcore : 0 ≤ ((81/100 : ℝ) ^ 2 + 1/2) * (La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - laj))
        - 2 * (81/100 : ℝ) * La θ (21/500 : ℝ) 0
        + tf71f θ (21/500 : ℝ) 0 * (4496782761/5000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (21/500 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_034_1283 h1 h2 htan
  have hcert := rowcert_034_1283 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (21/500 : ℝ) (17/50 : ℝ) = tf71Fr θ (21/500 : ℝ) ((-17/50 : ℝ)) := by
    have h := tf71F_real_eq θ (21/500 : ℝ) ((-17/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (21/500 : ℝ) (17/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (21/500 : ℝ)), Real.exp (-(((-17/50 : ℝ)) * t)) * tf71f θ (21/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-17/50 : ℝ)) * t) = (17/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (21/500 : ℝ) ((17/50 : ℝ) - (1283/1000 : ℝ)) = tf71Fr θ (21/500 : ℝ) ((943/1000 : ℝ)) := by
    have h := tf71F_real_eq θ (21/500 : ℝ) ((943/1000 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (21/500 : ℝ) ((17/50 : ℝ) - (1283/1000 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (21/500 : ℝ)), Real.exp (-(((943/1000 : ℝ)) * t)) * tf71f θ (21/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((943/1000 : ℝ)) * t) = ((17/50 : ℝ) - (1283/1000 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (21/500 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (21/500 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (21/500 : ℝ) 0 = (21/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (21/500 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - laj) ≤ La θ (21/500 : ℝ) (17/50 : ℝ) - La θ (21/500 : ℝ) ((17/50 : ℝ) - (1283/1000 : ℝ)) := by
    have hstep : La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - laj) ≤ La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - (1283/1000 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (1283/1000 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - (1283/1000 : ℝ)) ≤ La θ (21/500 : ℝ) (17/50 : ℝ) - La θ (21/500 : ℝ) ((17/50 : ℝ) - (1283/1000 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (1283/1000 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((81/100 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (21/500 : ℝ) ((-17/50 : ℝ)) - tf71Fr θ (21/500 : ℝ) ((943/1000 : ℝ)))
      - 2 * (81/100 : ℝ) * La θ (21/500 : ℝ) 0 + tf71f θ (21/500 : ℝ) 0 * (4496782761/5000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_036_123 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (9/25 : ℝ)) (hlajc : laj ≤ (123/100 : ℝ))
    (hcore : 0 ≤ ((407/500 : ℝ) ^ 2 + 1/2) * (La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - laj))
        - 2 * (407/500 : ℝ) * La θ (21/500 : ℝ) 0
        + tf71f θ (21/500 : ℝ) 0 * (338664717947/375000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (21/500 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_036_123 h1 h2 htan
  have hcert := rowcert_036_123 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (21/500 : ℝ) (9/25 : ℝ) = tf71Fr θ (21/500 : ℝ) ((-9/25 : ℝ)) := by
    have h := tf71F_real_eq θ (21/500 : ℝ) ((-9/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (21/500 : ℝ) (9/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (21/500 : ℝ)), Real.exp (-(((-9/25 : ℝ)) * t)) * tf71f θ (21/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-9/25 : ℝ)) * t) = (9/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (21/500 : ℝ) ((9/25 : ℝ) - (123/100 : ℝ)) = tf71Fr θ (21/500 : ℝ) ((87/100 : ℝ)) := by
    have h := tf71F_real_eq θ (21/500 : ℝ) ((87/100 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (21/500 : ℝ) ((9/25 : ℝ) - (123/100 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (21/500 : ℝ)), Real.exp (-(((87/100 : ℝ)) * t)) * tf71f θ (21/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((87/100 : ℝ)) * t) = ((9/25 : ℝ) - (123/100 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (21/500 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (21/500 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (21/500 : ℝ) 0 = (21/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (21/500 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - laj) ≤ La θ (21/500 : ℝ) (9/25 : ℝ) - La θ (21/500 : ℝ) ((9/25 : ℝ) - (123/100 : ℝ)) := by
    have hstep : La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - laj) ≤ La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - (123/100 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (123/100 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (21/500 : ℝ) la1 - La θ (21/500 : ℝ) (la1 - (123/100 : ℝ)) ≤ La θ (21/500 : ℝ) (9/25 : ℝ) - La θ (21/500 : ℝ) ((9/25 : ℝ) - (123/100 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (123/100 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((407/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (21/500 : ℝ) ((-9/25 : ℝ)) - tf71Fr θ (21/500 : ℝ) ((87/100 : ℝ)))
      - 2 * (407/500 : ℝ) * La θ (21/500 : ℝ) 0 + tf71f θ (21/500 : ℝ) 0 * (338664717947/375000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_038_1181 {θ la1 laj : ℝ}
    (h1 : (15291537476963/10000000000000 : ℝ) ≤ θ) (h2 : θ ≤ (152915374769631/100000000000000 : ℝ)) (htan : Real.tan θ = (24/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (19/50 : ℝ)) (hlajc : laj ≤ (1181/1000 : ℝ))
    (hcore : 0 ≤ ((817/1000 : ℝ) ^ 2 + 1/2) * (La θ (9/200 : ℝ) la1 - La θ (9/200 : ℝ) (la1 - laj))
        - 2 * (817/1000 : ℝ) * La θ (9/200 : ℝ) 0
        + tf71f θ (9/200 : ℝ) 0 * (1358882154467/1500000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (9/200 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_038_1181 h1 h2 htan
  have hcert := rowcert_038_1181 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (9/200 : ℝ) (19/50 : ℝ) = tf71Fr θ (9/200 : ℝ) ((-19/50 : ℝ)) := by
    have h := tf71F_real_eq θ (9/200 : ℝ) ((-19/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (9/200 : ℝ) (19/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (9/200 : ℝ)), Real.exp (-(((-19/50 : ℝ)) * t)) * tf71f θ (9/200 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-19/50 : ℝ)) * t) = (19/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (9/200 : ℝ) ((19/50 : ℝ) - (1181/1000 : ℝ)) = tf71Fr θ (9/200 : ℝ) ((801/1000 : ℝ)) := by
    have h := tf71F_real_eq θ (9/200 : ℝ) ((801/1000 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (9/200 : ℝ) ((19/50 : ℝ) - (1181/1000 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (9/200 : ℝ)), Real.exp (-(((801/1000 : ℝ)) * t)) * tf71f θ (9/200 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((801/1000 : ℝ)) * t) = ((19/50 : ℝ) - (1181/1000 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (9/200 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (9/200 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (9/200 : ℝ) 0 = (9/200 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (9/200 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (9/200 : ℝ) la1 - La θ (9/200 : ℝ) (la1 - laj) ≤ La θ (9/200 : ℝ) (19/50 : ℝ) - La θ (9/200 : ℝ) ((19/50 : ℝ) - (1181/1000 : ℝ)) := by
    have hstep : La θ (9/200 : ℝ) la1 - La θ (9/200 : ℝ) (la1 - laj) ≤ La θ (9/200 : ℝ) la1 - La θ (9/200 : ℝ) (la1 - (1181/1000 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (1181/1000 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (9/200 : ℝ) la1 - La θ (9/200 : ℝ) (la1 - (1181/1000 : ℝ)) ≤ La θ (9/200 : ℝ) (19/50 : ℝ) - La θ (9/200 : ℝ) ((19/50 : ℝ) - (1181/1000 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (1181/1000 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((817/1000 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (9/200 : ℝ) ((-19/50 : ℝ)) - tf71Fr θ (9/200 : ℝ) ((801/1000 : ℝ)))
      - 2 * (817/1000 : ℝ) * La θ (9/200 : ℝ) 0 + tf71f θ (9/200 : ℝ) 0 * (1358882154467/1500000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_04_1135 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (2/5 : ℝ)) (hlajc : laj ≤ (227/200 : ℝ))
    (hcore : 0 ≤ ((41/50 : ℝ) ^ 2 + 1/2) * (La θ (11/250 : ℝ) la1 - La θ (11/250 : ℝ) (la1 - laj))
        - 2 * (41/50 : ℝ) * La θ (11/250 : ℝ) 0
        + tf71f θ (11/250 : ℝ) 0 * (3407774843/3750000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (11/250 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_04_1135 h1 h2 htan
  have hcert := rowcert_04_1135 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (11/250 : ℝ) (2/5 : ℝ) = tf71Fr θ (11/250 : ℝ) ((-2/5 : ℝ)) := by
    have h := tf71F_real_eq θ (11/250 : ℝ) ((-2/5 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (11/250 : ℝ) (2/5 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (11/250 : ℝ)), Real.exp (-(((-2/5 : ℝ)) * t)) * tf71f θ (11/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-2/5 : ℝ)) * t) = (2/5 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (11/250 : ℝ) ((2/5 : ℝ) - (227/200 : ℝ)) = tf71Fr θ (11/250 : ℝ) ((147/200 : ℝ)) := by
    have h := tf71F_real_eq θ (11/250 : ℝ) ((147/200 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (11/250 : ℝ) ((2/5 : ℝ) - (227/200 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (11/250 : ℝ)), Real.exp (-(((147/200 : ℝ)) * t)) * tf71f θ (11/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((147/200 : ℝ)) * t) = ((2/5 : ℝ) - (227/200 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (11/250 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (11/250 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (11/250 : ℝ) 0 = (11/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (11/250 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (11/250 : ℝ) la1 - La θ (11/250 : ℝ) (la1 - laj) ≤ La θ (11/250 : ℝ) (2/5 : ℝ) - La θ (11/250 : ℝ) ((2/5 : ℝ) - (227/200 : ℝ)) := by
    have hstep : La θ (11/250 : ℝ) la1 - La θ (11/250 : ℝ) (la1 - laj) ≤ La θ (11/250 : ℝ) la1 - La θ (11/250 : ℝ) (la1 - (227/200 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (227/200 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (11/250 : ℝ) la1 - La θ (11/250 : ℝ) (la1 - (227/200 : ℝ)) ≤ La θ (11/250 : ℝ) (2/5 : ℝ) - La θ (11/250 : ℝ) ((2/5 : ℝ) - (227/200 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (227/200 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((41/50 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (11/250 : ℝ) ((-2/5 : ℝ)) - tf71Fr θ (11/250 : ℝ) ((147/200 : ℝ)))
      - 2 * (41/50 : ℝ) * La θ (11/250 : ℝ) 0 + tf71f θ (11/250 : ℝ) 0 * (3407774843/3750000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_042_1094 {θ la1 laj : ℝ}
    (h1 : (15291537476963/10000000000000 : ℝ) ≤ θ) (h2 : θ ≤ (152915374769631/100000000000000 : ℝ)) (htan : Real.tan θ = (24/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (21/50 : ℝ)) (hlajc : laj ≤ (547/500 : ℝ))
    (hcore : 0 ≤ ((411/500 : ℝ) ^ 2 + 1/2) * (La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj))
        - 2 * (411/500 : ℝ) * La θ (23/500 : ℝ) 0
        + tf71f θ (23/500 : ℝ) 0 * (113827579921/125000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (23/500 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_042_1094 h1 h2 htan
  have hcert := rowcert_042_1094 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (23/500 : ℝ) (21/50 : ℝ) = tf71Fr θ (23/500 : ℝ) ((-21/50 : ℝ)) := by
    have h := tf71F_real_eq θ (23/500 : ℝ) ((-21/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (23/500 : ℝ) (21/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (23/500 : ℝ)), Real.exp (-(((-21/50 : ℝ)) * t)) * tf71f θ (23/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-21/50 : ℝ)) * t) = (21/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (23/500 : ℝ) ((21/50 : ℝ) - (547/500 : ℝ)) = tf71Fr θ (23/500 : ℝ) ((337/500 : ℝ)) := by
    have h := tf71F_real_eq θ (23/500 : ℝ) ((337/500 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (23/500 : ℝ) ((21/50 : ℝ) - (547/500 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (23/500 : ℝ)), Real.exp (-(((337/500 : ℝ)) * t)) * tf71f θ (23/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((337/500 : ℝ)) * t) = ((21/50 : ℝ) - (547/500 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (23/500 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (23/500 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (23/500 : ℝ) 0 = (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (23/500 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj) ≤ La θ (23/500 : ℝ) (21/50 : ℝ) - La θ (23/500 : ℝ) ((21/50 : ℝ) - (547/500 : ℝ)) := by
    have hstep : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj) ≤ La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - (547/500 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (547/500 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - (547/500 : ℝ)) ≤ La θ (23/500 : ℝ) (21/50 : ℝ) - La θ (23/500 : ℝ) ((21/50 : ℝ) - (547/500 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (547/500 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((411/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (23/500 : ℝ) ((-21/50 : ℝ)) - tf71Fr θ (23/500 : ℝ) ((337/500 : ℝ)))
      - 2 * (411/500 : ℝ) * La θ (23/500 : ℝ) 0 + tf71f θ (23/500 : ℝ) 0 * (113827579921/125000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_044_1055 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (11/25 : ℝ)) (hlajc : laj ≤ (211/200 : ℝ))
    (hcore : 0 ≤ ((33/40 : ℝ) ^ 2 + 1/2) * (La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj))
        - 2 * (33/40 : ℝ) * La θ (23/500 : ℝ) 0
        + tf71f θ (23/500 : ℝ) 0 * (730755329/800000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (23/500 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_044_1055 h1 h2 htan
  have hcert := rowcert_044_1055 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (23/500 : ℝ) (11/25 : ℝ) = tf71Fr θ (23/500 : ℝ) ((-11/25 : ℝ)) := by
    have h := tf71F_real_eq θ (23/500 : ℝ) ((-11/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (23/500 : ℝ) (11/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (23/500 : ℝ)), Real.exp (-(((-11/25 : ℝ)) * t)) * tf71f θ (23/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-11/25 : ℝ)) * t) = (11/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (23/500 : ℝ) ((11/25 : ℝ) - (211/200 : ℝ)) = tf71Fr θ (23/500 : ℝ) ((123/200 : ℝ)) := by
    have h := tf71F_real_eq θ (23/500 : ℝ) ((123/200 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (23/500 : ℝ) ((11/25 : ℝ) - (211/200 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (23/500 : ℝ)), Real.exp (-(((123/200 : ℝ)) * t)) * tf71f θ (23/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((123/200 : ℝ)) * t) = ((11/25 : ℝ) - (211/200 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (23/500 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (23/500 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (23/500 : ℝ) 0 = (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (23/500 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj) ≤ La θ (23/500 : ℝ) (11/25 : ℝ) - La θ (23/500 : ℝ) ((11/25 : ℝ) - (211/200 : ℝ)) := by
    have hstep : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj) ≤ La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - (211/200 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (211/200 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - (211/200 : ℝ)) ≤ La θ (23/500 : ℝ) (11/25 : ℝ) - La θ (23/500 : ℝ) ((11/25 : ℝ) - (211/200 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (211/200 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((33/40 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (23/500 : ℝ) ((-11/25 : ℝ)) - tf71Fr θ (23/500 : ℝ) ((123/200 : ℝ)))
      - 2 * (33/40 : ℝ) * La θ (23/500 : ℝ) 0 + tf71f θ (23/500 : ℝ) 0 * (730755329/800000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_046_1018 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (23/50 : ℝ)) (hlajc : laj ≤ (509/500 : ℝ))
    (hcore : 0 ≤ ((207/250 : ℝ) ^ 2 + 1/2) * (La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj))
        - 2 * (207/250 : ℝ) * La θ (23/500 : ℝ) 0
        + tf71f θ (23/500 : ℝ) 0 * (28633458849/31250000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (23/500 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_046_1018 h1 h2 htan
  have hcert := rowcert_046_1018 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (23/500 : ℝ) (23/50 : ℝ) = tf71Fr θ (23/500 : ℝ) ((-23/50 : ℝ)) := by
    have h := tf71F_real_eq θ (23/500 : ℝ) ((-23/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (23/500 : ℝ) (23/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (23/500 : ℝ)), Real.exp (-(((-23/50 : ℝ)) * t)) * tf71f θ (23/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-23/50 : ℝ)) * t) = (23/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (23/500 : ℝ) ((23/50 : ℝ) - (509/500 : ℝ)) = tf71Fr θ (23/500 : ℝ) ((279/500 : ℝ)) := by
    have h := tf71F_real_eq θ (23/500 : ℝ) ((279/500 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (23/500 : ℝ) ((23/50 : ℝ) - (509/500 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (23/500 : ℝ)), Real.exp (-(((279/500 : ℝ)) * t)) * tf71f θ (23/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((279/500 : ℝ)) * t) = ((23/50 : ℝ) - (509/500 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (23/500 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (23/500 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (23/500 : ℝ) 0 = (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (23/500 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj) ≤ La θ (23/500 : ℝ) (23/50 : ℝ) - La θ (23/500 : ℝ) ((23/50 : ℝ) - (509/500 : ℝ)) := by
    have hstep : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - laj) ≤ La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - (509/500 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (509/500 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (23/500 : ℝ) la1 - La θ (23/500 : ℝ) (la1 - (509/500 : ℝ)) ≤ La θ (23/500 : ℝ) (23/50 : ℝ) - La θ (23/500 : ℝ) ((23/50 : ℝ) - (509/500 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (509/500 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((207/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (23/500 : ℝ) ((-23/50 : ℝ)) - tf71Fr θ (23/500 : ℝ) ((279/500 : ℝ)))
      - 2 * (207/250 : ℝ) * La θ (23/500 : ℝ) 0 + tf71f θ (23/500 : ℝ) 0 * (28633458849/31250000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_048_0984 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (12/25 : ℝ)) (hlajc : laj ≤ (123/125 : ℝ))
    (hcore : 0 ≤ ((104/125 : ℝ) ^ 2 + 1/2) * (La θ (47/1000 : ℝ) la1 - La θ (47/1000 : ℝ) (la1 - laj))
        - 2 * (104/125 : ℝ) * La θ (47/1000 : ℝ) 0
        + tf71f θ (47/1000 : ℝ) 0 * (21563532323/23437500000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (47/1000 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_048_0984 h1 h2 htan
  have hcert := rowcert_048_0984 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (47/1000 : ℝ) (12/25 : ℝ) = tf71Fr θ (47/1000 : ℝ) ((-12/25 : ℝ)) := by
    have h := tf71F_real_eq θ (47/1000 : ℝ) ((-12/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (47/1000 : ℝ) (12/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (47/1000 : ℝ)), Real.exp (-(((-12/25 : ℝ)) * t)) * tf71f θ (47/1000 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-12/25 : ℝ)) * t) = (12/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (47/1000 : ℝ) ((12/25 : ℝ) - (123/125 : ℝ)) = tf71Fr θ (47/1000 : ℝ) ((63/125 : ℝ)) := by
    have h := tf71F_real_eq θ (47/1000 : ℝ) ((63/125 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (47/1000 : ℝ) ((12/25 : ℝ) - (123/125 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (47/1000 : ℝ)), Real.exp (-(((63/125 : ℝ)) * t)) * tf71f θ (47/1000 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((63/125 : ℝ)) * t) = ((12/25 : ℝ) - (123/125 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (47/1000 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (47/1000 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (47/1000 : ℝ) 0 = (47/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (47/1000 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (47/1000 : ℝ) la1 - La θ (47/1000 : ℝ) (la1 - laj) ≤ La θ (47/1000 : ℝ) (12/25 : ℝ) - La θ (47/1000 : ℝ) ((12/25 : ℝ) - (123/125 : ℝ)) := by
    have hstep : La θ (47/1000 : ℝ) la1 - La θ (47/1000 : ℝ) (la1 - laj) ≤ La θ (47/1000 : ℝ) la1 - La θ (47/1000 : ℝ) (la1 - (123/125 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (123/125 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (47/1000 : ℝ) la1 - La θ (47/1000 : ℝ) (la1 - (123/125 : ℝ)) ≤ La θ (47/1000 : ℝ) (12/25 : ℝ) - La θ (47/1000 : ℝ) ((12/25 : ℝ) - (123/125 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (123/125 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((104/125 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (47/1000 : ℝ) ((-12/25 : ℝ)) - tf71Fr θ (47/1000 : ℝ) ((63/125 : ℝ)))
      - 2 * (104/125 : ℝ) * La θ (47/1000 : ℝ) 0 + tf71f θ (47/1000 : ℝ) 0 * (21563532323/23437500000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_05_0952 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (1/2 : ℝ)) (hlajc : laj ≤ (119/125 : ℝ))
    (hcore : 0 ≤ ((417/500 : ℝ) ^ 2 + 1/2) * (La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj))
        - 2 * (417/500 : ℝ) * La θ (6/125 : ℝ) 0
        + tf71f θ (6/125 : ℝ) 0 * (115241590889/125000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (6/125 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_05_0952 h1 h2 htan
  have hcert := rowcert_05_0952 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (6/125 : ℝ) (1/2 : ℝ) = tf71Fr θ (6/125 : ℝ) ((-1/2 : ℝ)) := by
    have h := tf71F_real_eq θ (6/125 : ℝ) ((-1/2 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (6/125 : ℝ) (1/2 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (6/125 : ℝ)), Real.exp (-(((-1/2 : ℝ)) * t)) * tf71f θ (6/125 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-1/2 : ℝ)) * t) = (1/2 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (6/125 : ℝ) ((1/2 : ℝ) - (119/125 : ℝ)) = tf71Fr θ (6/125 : ℝ) ((113/250 : ℝ)) := by
    have h := tf71F_real_eq θ (6/125 : ℝ) ((113/250 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (6/125 : ℝ) ((1/2 : ℝ) - (119/125 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (6/125 : ℝ)), Real.exp (-(((113/250 : ℝ)) * t)) * tf71f θ (6/125 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((113/250 : ℝ)) * t) = ((1/2 : ℝ) - (119/125 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (6/125 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (6/125 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (6/125 : ℝ) 0 = (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (6/125 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj) ≤ La θ (6/125 : ℝ) (1/2 : ℝ) - La θ (6/125 : ℝ) ((1/2 : ℝ) - (119/125 : ℝ)) := by
    have hstep : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj) ≤ La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - (119/125 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (119/125 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - (119/125 : ℝ)) ≤ La θ (6/125 : ℝ) (1/2 : ℝ) - La θ (6/125 : ℝ) ((1/2 : ℝ) - (119/125 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (119/125 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((417/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (6/125 : ℝ) ((-1/2 : ℝ)) - tf71Fr θ (6/125 : ℝ) ((113/250 : ℝ)))
      - 2 * (417/500 : ℝ) * La θ (6/125 : ℝ) 0 + tf71f θ (6/125 : ℝ) 0 * (115241590889/125000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_052_0922 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (13/25 : ℝ)) (hlajc : laj ≤ (461/500 : ℝ))
    (hcore : 0 ≤ ((209/250 : ℝ) ^ 2 + 1/2) * (La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj))
        - 2 * (209/250 : ℝ) * La θ (6/125 : ℝ) 0
        + tf71f θ (6/125 : ℝ) 0 * (28869460681/31250000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (6/125 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_052_0922 h1 h2 htan
  have hcert := rowcert_052_0922 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (6/125 : ℝ) (13/25 : ℝ) = tf71Fr θ (6/125 : ℝ) ((-13/25 : ℝ)) := by
    have h := tf71F_real_eq θ (6/125 : ℝ) ((-13/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (6/125 : ℝ) (13/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (6/125 : ℝ)), Real.exp (-(((-13/25 : ℝ)) * t)) * tf71f θ (6/125 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-13/25 : ℝ)) * t) = (13/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (6/125 : ℝ) ((13/25 : ℝ) - (461/500 : ℝ)) = tf71Fr θ (6/125 : ℝ) ((201/500 : ℝ)) := by
    have h := tf71F_real_eq θ (6/125 : ℝ) ((201/500 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (6/125 : ℝ) ((13/25 : ℝ) - (461/500 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (6/125 : ℝ)), Real.exp (-(((201/500 : ℝ)) * t)) * tf71f θ (6/125 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((201/500 : ℝ)) * t) = ((13/25 : ℝ) - (461/500 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (6/125 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (6/125 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (6/125 : ℝ) 0 = (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (6/125 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj) ≤ La θ (6/125 : ℝ) (13/25 : ℝ) - La θ (6/125 : ℝ) ((13/25 : ℝ) - (461/500 : ℝ)) := by
    have hstep : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj) ≤ La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - (461/500 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (461/500 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - (461/500 : ℝ)) ≤ La θ (6/125 : ℝ) (13/25 : ℝ) - La θ (6/125 : ℝ) ((13/25 : ℝ) - (461/500 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (461/500 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((209/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (6/125 : ℝ) ((-13/25 : ℝ)) - tf71Fr θ (6/125 : ℝ) ((201/500 : ℝ)))
      - 2 * (209/250 : ℝ) * La θ (6/125 : ℝ) 0 + tf71f θ (6/125 : ℝ) 0 * (28869460681/31250000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_054_0893 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (27/50 : ℝ)) (hlajc : laj ≤ (893/1000 : ℝ))
    (hcore : 0 ≤ ((419/500 : ℝ) ^ 2 + 1/2) * (La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj))
        - 2 * (419/500 : ℝ) * La θ (6/125 : ℝ) 0
        + tf71f θ (6/125 : ℝ) 0 * (347142783683/375000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (6/125 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_054_0893 h1 h2 htan
  have hcert := rowcert_054_0893 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (6/125 : ℝ) (27/50 : ℝ) = tf71Fr θ (6/125 : ℝ) ((-27/50 : ℝ)) := by
    have h := tf71F_real_eq θ (6/125 : ℝ) ((-27/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (6/125 : ℝ) (27/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (6/125 : ℝ)), Real.exp (-(((-27/50 : ℝ)) * t)) * tf71f θ (6/125 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-27/50 : ℝ)) * t) = (27/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (6/125 : ℝ) ((27/50 : ℝ) - (893/1000 : ℝ)) = tf71Fr θ (6/125 : ℝ) ((353/1000 : ℝ)) := by
    have h := tf71F_real_eq θ (6/125 : ℝ) ((353/1000 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (6/125 : ℝ) ((27/50 : ℝ) - (893/1000 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (6/125 : ℝ)), Real.exp (-(((353/1000 : ℝ)) * t)) * tf71f θ (6/125 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((353/1000 : ℝ)) * t) = ((27/50 : ℝ) - (893/1000 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (6/125 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (6/125 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (6/125 : ℝ) 0 = (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (6/125 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj) ≤ La θ (6/125 : ℝ) (27/50 : ℝ) - La θ (6/125 : ℝ) ((27/50 : ℝ) - (893/1000 : ℝ)) := by
    have hstep : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - laj) ≤ La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - (893/1000 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (893/1000 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (6/125 : ℝ) la1 - La θ (6/125 : ℝ) (la1 - (893/1000 : ℝ)) ≤ La θ (6/125 : ℝ) (27/50 : ℝ) - La θ (6/125 : ℝ) ((27/50 : ℝ) - (893/1000 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (893/1000 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((419/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (6/125 : ℝ) ((-27/50 : ℝ)) - tf71Fr θ (6/125 : ℝ) ((353/1000 : ℝ)))
      - 2 * (419/500 : ℝ) * La θ (6/125 : ℝ) 0 + tf71f θ (6/125 : ℝ) 0 * (347142783683/375000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_056_0866 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (14/25 : ℝ)) (hlajc : laj ≤ (433/500 : ℝ))
    (hcore : 0 ≤ ((21/25 : ℝ) ^ 2 + 1/2) * (La θ (49/1000 : ℝ) la1 - La θ (49/1000 : ℝ) (la1 - laj))
        - 2 * (21/25 : ℝ) * La θ (49/1000 : ℝ) 0
        + tf71f θ (49/1000 : ℝ) 0 * (72469279/78125000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (49/1000 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_056_0866 h1 h2 htan
  have hcert := rowcert_056_0866 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (49/1000 : ℝ) (14/25 : ℝ) = tf71Fr θ (49/1000 : ℝ) ((-14/25 : ℝ)) := by
    have h := tf71F_real_eq θ (49/1000 : ℝ) ((-14/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (49/1000 : ℝ) (14/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (49/1000 : ℝ)), Real.exp (-(((-14/25 : ℝ)) * t)) * tf71f θ (49/1000 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-14/25 : ℝ)) * t) = (14/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (49/1000 : ℝ) ((14/25 : ℝ) - (433/500 : ℝ)) = tf71Fr θ (49/1000 : ℝ) ((153/500 : ℝ)) := by
    have h := tf71F_real_eq θ (49/1000 : ℝ) ((153/500 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (49/1000 : ℝ) ((14/25 : ℝ) - (433/500 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (49/1000 : ℝ)), Real.exp (-(((153/500 : ℝ)) * t)) * tf71f θ (49/1000 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((153/500 : ℝ)) * t) = ((14/25 : ℝ) - (433/500 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (49/1000 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (49/1000 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (49/1000 : ℝ) 0 = (49/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (49/1000 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (49/1000 : ℝ) la1 - La θ (49/1000 : ℝ) (la1 - laj) ≤ La θ (49/1000 : ℝ) (14/25 : ℝ) - La θ (49/1000 : ℝ) ((14/25 : ℝ) - (433/500 : ℝ)) := by
    have hstep : La θ (49/1000 : ℝ) la1 - La θ (49/1000 : ℝ) (la1 - laj) ≤ La θ (49/1000 : ℝ) la1 - La θ (49/1000 : ℝ) (la1 - (433/500 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (433/500 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (49/1000 : ℝ) la1 - La θ (49/1000 : ℝ) (la1 - (433/500 : ℝ)) ≤ La θ (49/1000 : ℝ) (14/25 : ℝ) - La θ (49/1000 : ℝ) ((14/25 : ℝ) - (433/500 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (433/500 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((21/25 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (49/1000 : ℝ) ((-14/25 : ℝ)) - tf71Fr θ (49/1000 : ℝ) ((153/500 : ℝ)))
      - 2 * (21/25 : ℝ) * La θ (49/1000 : ℝ) 0 + tf71f θ (49/1000 : ℝ) 0 * (72469279/78125000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_058_084 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (29/50 : ℝ)) (hlajc : laj ≤ (21/25 : ℝ))
    (hcore : 0 ≤ ((421/500 : ℝ) ^ 2 + 1/2) * (La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - laj))
        - 2 * (421/500 : ℝ) * La θ (1/20 : ℝ) 0
        + tf71f θ (1/20 : ℝ) 0 * (116187598241/125000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (1/20 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_058_084 h1 h2 htan
  have hcert := rowcert_058_084 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (1/20 : ℝ) (29/50 : ℝ) = tf71Fr θ (1/20 : ℝ) ((-29/50 : ℝ)) := by
    have h := tf71F_real_eq θ (1/20 : ℝ) ((-29/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (1/20 : ℝ) (29/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (1/20 : ℝ)), Real.exp (-(((-29/50 : ℝ)) * t)) * tf71f θ (1/20 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-29/50 : ℝ)) * t) = (29/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (1/20 : ℝ) ((29/50 : ℝ) - (21/25 : ℝ)) = tf71Fr θ (1/20 : ℝ) ((13/50 : ℝ)) := by
    have h := tf71F_real_eq θ (1/20 : ℝ) ((13/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (1/20 : ℝ) ((29/50 : ℝ) - (21/25 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (1/20 : ℝ)), Real.exp (-(((13/50 : ℝ)) * t)) * tf71f θ (1/20 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((13/50 : ℝ)) * t) = ((29/50 : ℝ) - (21/25 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (1/20 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (1/20 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (1/20 : ℝ) 0 = (1/20 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (1/20 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - laj) ≤ La θ (1/20 : ℝ) (29/50 : ℝ) - La θ (1/20 : ℝ) ((29/50 : ℝ) - (21/25 : ℝ)) := by
    have hstep : La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - laj) ≤ La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - (21/25 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (21/25 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - (21/25 : ℝ)) ≤ La θ (1/20 : ℝ) (29/50 : ℝ) - La θ (1/20 : ℝ) ((29/50 : ℝ) - (21/25 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (21/25 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((421/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (1/20 : ℝ) ((-29/50 : ℝ)) - tf71Fr θ (1/20 : ℝ) ((13/50 : ℝ)))
      - 2 * (421/500 : ℝ) * La θ (1/20 : ℝ) 0 + tf71f θ (1/20 : ℝ) 0 * (116187598241/125000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_06_0816 {θ la1 laj : ℝ}
    (h1 : (150422816301907/100000000000000 : ℝ) ≤ θ) (h2 : θ ≤ (37605704075477/25000000000000 : ℝ)) (htan : Real.tan θ = (15/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (3/5 : ℝ)) (hlajc : laj ≤ (102/125 : ℝ))
    (hcore : 0 ≤ ((211/250 : ℝ) ^ 2 + 1/2) * (La θ (41/500 : ℝ) la1 - La θ (41/500 : ℝ) (la1 - laj))
        - 2 * (211/250 : ℝ) * La θ (41/500 : ℝ) 0
        + tf71f θ (41/500 : ℝ) 0 * (87318387563/93750000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (41/500 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_06_0816 h1 h2 htan
  have hcert := rowcert_06_0816 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (41/500 : ℝ) (3/5 : ℝ) = tf71Fr θ (41/500 : ℝ) ((-3/5 : ℝ)) := by
    have h := tf71F_real_eq θ (41/500 : ℝ) ((-3/5 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (41/500 : ℝ) (3/5 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (41/500 : ℝ)), Real.exp (-(((-3/5 : ℝ)) * t)) * tf71f θ (41/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-3/5 : ℝ)) * t) = (3/5 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (41/500 : ℝ) ((3/5 : ℝ) - (102/125 : ℝ)) = tf71Fr θ (41/500 : ℝ) ((27/125 : ℝ)) := by
    have h := tf71F_real_eq θ (41/500 : ℝ) ((27/125 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (41/500 : ℝ) ((3/5 : ℝ) - (102/125 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (41/500 : ℝ)), Real.exp (-(((27/125 : ℝ)) * t)) * tf71f θ (41/500 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((27/125 : ℝ)) * t) = ((3/5 : ℝ) - (102/125 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (41/500 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (41/500 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (41/500 : ℝ) 0 = (41/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (41/500 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (41/500 : ℝ) la1 - La θ (41/500 : ℝ) (la1 - laj) ≤ La θ (41/500 : ℝ) (3/5 : ℝ) - La θ (41/500 : ℝ) ((3/5 : ℝ) - (102/125 : ℝ)) := by
    have hstep : La θ (41/500 : ℝ) la1 - La θ (41/500 : ℝ) (la1 - laj) ≤ La θ (41/500 : ℝ) la1 - La θ (41/500 : ℝ) (la1 - (102/125 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (102/125 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (41/500 : ℝ) la1 - La θ (41/500 : ℝ) (la1 - (102/125 : ℝ)) ≤ La θ (41/500 : ℝ) (3/5 : ℝ) - La θ (41/500 : ℝ) ((3/5 : ℝ) - (102/125 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (102/125 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((211/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (41/500 : ℝ) ((-3/5 : ℝ)) - tf71Fr θ (41/500 : ℝ) ((27/125 : ℝ)))
      - 2 * (211/250 : ℝ) * La θ (41/500 : ℝ) 0 + tf71f θ (41/500 : ℝ) 0 * (87318387563/93750000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_062_0792 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (31/50 : ℝ)) (hlajc : laj ≤ (99/125 : ℝ))
    (hcore : 0 ≤ ((847/1000 : ℝ) ^ 2 + 1/2) * (La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - laj))
        - 2 * (847/1000 : ℝ) * La θ (1/20 : ℝ) 0
        + tf71f θ (1/20 : ℝ) 0 * (1401362484227/1500000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (1/20 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_062_0792 h1 h2 htan
  have hcert := rowcert_062_0792 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (1/20 : ℝ) (31/50 : ℝ) = tf71Fr θ (1/20 : ℝ) ((-31/50 : ℝ)) := by
    have h := tf71F_real_eq θ (1/20 : ℝ) ((-31/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (1/20 : ℝ) (31/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (1/20 : ℝ)), Real.exp (-(((-31/50 : ℝ)) * t)) * tf71f θ (1/20 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-31/50 : ℝ)) * t) = (31/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (1/20 : ℝ) ((31/50 : ℝ) - (99/125 : ℝ)) = tf71Fr θ (1/20 : ℝ) ((43/250 : ℝ)) := by
    have h := tf71F_real_eq θ (1/20 : ℝ) ((43/250 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (1/20 : ℝ) ((31/50 : ℝ) - (99/125 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (1/20 : ℝ)), Real.exp (-(((43/250 : ℝ)) * t)) * tf71f θ (1/20 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((43/250 : ℝ)) * t) = ((31/50 : ℝ) - (99/125 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (1/20 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (1/20 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (1/20 : ℝ) 0 = (1/20 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (1/20 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - laj) ≤ La θ (1/20 : ℝ) (31/50 : ℝ) - La θ (1/20 : ℝ) ((31/50 : ℝ) - (99/125 : ℝ)) := by
    have hstep : La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - laj) ≤ La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - (99/125 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (99/125 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (1/20 : ℝ) la1 - La θ (1/20 : ℝ) (la1 - (99/125 : ℝ)) ≤ La θ (1/20 : ℝ) (31/50 : ℝ) - La θ (1/20 : ℝ) ((31/50 : ℝ) - (99/125 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (99/125 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((847/1000 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (1/20 : ℝ) ((-31/50 : ℝ)) - tf71Fr θ (1/20 : ℝ) ((43/250 : ℝ)))
      - 2 * (847/1000 : ℝ) * La θ (1/20 : ℝ) 0 + tf71f θ (1/20 : ℝ) 0 * (1401362484227/1500000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_064_077 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (16/25 : ℝ)) (hlajc : laj ≤ (77/100 : ℝ))
    (hcore : 0 ≤ ((849/1000 : ℝ) ^ 2 + 1/2) * (La θ (51/1000 : ℝ) la1 - La θ (51/1000 : ℝ) (la1 - laj))
        - 2 * (849/1000 : ℝ) * La θ (51/1000 : ℝ) 0
        + tf71f θ (51/1000 : ℝ) 0 * (468070168801/500000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (51/1000 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_064_077 h1 h2 htan
  have hcert := rowcert_064_077 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (51/1000 : ℝ) (16/25 : ℝ) = tf71Fr θ (51/1000 : ℝ) ((-16/25 : ℝ)) := by
    have h := tf71F_real_eq θ (51/1000 : ℝ) ((-16/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (51/1000 : ℝ) (16/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (51/1000 : ℝ)), Real.exp (-(((-16/25 : ℝ)) * t)) * tf71f θ (51/1000 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-16/25 : ℝ)) * t) = (16/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (51/1000 : ℝ) ((16/25 : ℝ) - (77/100 : ℝ)) = tf71Fr θ (51/1000 : ℝ) ((13/100 : ℝ)) := by
    have h := tf71F_real_eq θ (51/1000 : ℝ) ((13/100 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (51/1000 : ℝ) ((16/25 : ℝ) - (77/100 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (51/1000 : ℝ)), Real.exp (-(((13/100 : ℝ)) * t)) * tf71f θ (51/1000 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((13/100 : ℝ)) * t) = ((16/25 : ℝ) - (77/100 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (51/1000 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (51/1000 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (51/1000 : ℝ) 0 = (51/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (51/1000 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (51/1000 : ℝ) la1 - La θ (51/1000 : ℝ) (la1 - laj) ≤ La θ (51/1000 : ℝ) (16/25 : ℝ) - La θ (51/1000 : ℝ) ((16/25 : ℝ) - (77/100 : ℝ)) := by
    have hstep : La θ (51/1000 : ℝ) la1 - La θ (51/1000 : ℝ) (la1 - laj) ≤ La θ (51/1000 : ℝ) la1 - La θ (51/1000 : ℝ) (la1 - (77/100 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (77/100 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (51/1000 : ℝ) la1 - La θ (51/1000 : ℝ) (la1 - (77/100 : ℝ)) ≤ La θ (51/1000 : ℝ) (16/25 : ℝ) - La θ (51/1000 : ℝ) ((16/25 : ℝ) - (77/100 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (77/100 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((849/1000 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (51/1000 : ℝ) ((-16/25 : ℝ)) - tf71Fr θ (51/1000 : ℝ) ((13/100 : ℝ)))
      - 2 * (849/1000 : ℝ) * La θ (51/1000 : ℝ) 0 + tf71f θ (51/1000 : ℝ) 0 * (468070168801/500000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_066_0748 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (33/50 : ℝ)) (hlajc : laj ≤ (187/250 : ℝ))
    (hcore : 0 ≤ ((213/250 : ℝ) ^ 2 + 1/2) * (La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj))
        - 2 * (213/250 : ℝ) * La θ (13/250 : ℝ) 0
        + tf71f θ (13/250 : ℝ) 0 * (29343464369/31250000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_066_0748 h1 h2 htan
  have hcert := rowcert_066_0748 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (13/250 : ℝ) (33/50 : ℝ) = tf71Fr θ (13/250 : ℝ) ((-33/50 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((-33/50 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) (33/50 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((-33/50 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-33/50 : ℝ)) * t) = (33/50 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (13/250 : ℝ) ((33/50 : ℝ) - (187/250 : ℝ)) = tf71Fr θ (13/250 : ℝ) ((11/125 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((11/125 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) ((33/50 : ℝ) - (187/250 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((11/125 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((11/125 : ℝ)) * t) = ((33/50 : ℝ) - (187/250 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (13/250 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (13/250 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (13/250 : ℝ) 0 = (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (13/250 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) (33/50 : ℝ) - La θ (13/250 : ℝ) ((33/50 : ℝ) - (187/250 : ℝ)) := by
    have hstep : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (187/250 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (187/250 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (187/250 : ℝ)) ≤ La θ (13/250 : ℝ) (33/50 : ℝ) - La θ (13/250 : ℝ) ((33/50 : ℝ) - (187/250 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (187/250 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((213/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) ((-33/50 : ℝ)) - tf71Fr θ (13/250 : ℝ) ((11/125 : ℝ)))
      - 2 * (213/250 : ℝ) * La θ (13/250 : ℝ) 0 + tf71f θ (13/250 : ℝ) 0 * (29343464369/31250000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_068_0728 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (17/25 : ℝ)) (hlajc : laj ≤ (91/125 : ℝ))
    (hcore : 0 ≤ ((427/500 : ℝ) ^ 2 + 1/2) * (La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj))
        - 2 * (427/500 : ℝ) * La θ (13/250 : ℝ) 0
        + tf71f θ (13/250 : ℝ) 0 * (117611609329/125000000000 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_068_0728 h1 h2 htan
  have hcert := rowcert_068_0728 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (13/250 : ℝ) (17/25 : ℝ) = tf71Fr θ (13/250 : ℝ) ((-17/25 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((-17/25 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) (17/25 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((-17/25 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-17/25 : ℝ)) * t) = (17/25 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (13/250 : ℝ) ((17/25 : ℝ) - (91/125 : ℝ)) = tf71Fr θ (13/250 : ℝ) ((6/125 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((6/125 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) ((17/25 : ℝ) - (91/125 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((6/125 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((6/125 : ℝ)) * t) = ((17/25 : ℝ) - (91/125 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (13/250 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (13/250 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (13/250 : ℝ) 0 = (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (13/250 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) (17/25 : ℝ) - La θ (13/250 : ℝ) ((17/25 : ℝ) - (91/125 : ℝ)) := by
    have hstep : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (91/125 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (91/125 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (91/125 : ℝ)) ≤ La θ (13/250 : ℝ) (17/25 : ℝ) - La θ (13/250 : ℝ) ((17/25 : ℝ) - (91/125 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (91/125 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((427/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) ((-17/25 : ℝ)) - tf71Fr θ (13/250 : ℝ) ((6/125 : ℝ)))
      - 2 * (427/500 : ℝ) * La θ (13/250 : ℝ) 0 + tf71f θ (13/250 : ℝ) 0 * (117611609329/125000000000 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_07_0708 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (7/10 : ℝ)) (hlajc : laj ≤ (177/250 : ℝ))
    (hcore : 0 ≤ ((107/125 : ℝ) ^ 2 + 1/2) * (La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj))
        - 2 * (107/125 : ℝ) * La θ (13/250 : ℝ) 0
        + tf71f θ (13/250 : ℝ) 0 * (2762098309/2929687500 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi, hE2lo, hE2hi⟩ := expb_07_0708 h1 h2 htan
  have hcert := rowcert_07_0708 h1 h2 htan hE1lo hE1hi hE2lo hE2hi
  have hLa_a : La θ (13/250 : ℝ) (7/10 : ℝ) = tf71Fr θ (13/250 : ℝ) ((-7/10 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((-7/10 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) (7/10 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((-7/10 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-7/10 : ℝ)) * t) = (7/10 : ℝ) * t by ring])
    rw [h', h]
  have hLa_ac : La θ (13/250 : ℝ) ((7/10 : ℝ) - (177/250 : ℝ)) = tf71Fr θ (13/250 : ℝ) ((1/125 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((1/125 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) ((7/10 : ℝ) - (177/250 : ℝ)) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((1/125 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((1/125 : ℝ)) * t) = ((7/10 : ℝ) - (177/250 : ℝ)) * t by ring])
    rw [h', h]
  have hLa0 : La θ (13/250 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (13/250 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (13/250 : ℝ) 0 = (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (13/250 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) (7/10 : ℝ) - La θ (13/250 : ℝ) ((7/10 : ℝ) - (177/250 : ℝ)) := by
    have hstep : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (177/250 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (177/250 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (177/250 : ℝ)) ≤ La θ (13/250 : ℝ) (7/10 : ℝ) - La θ (13/250 : ℝ) ((7/10 : ℝ) - (177/250 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (177/250 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      exact this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((107/125 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) ((-7/10 : ℝ)) - tf71Fr θ (13/250 : ℝ) ((1/125 : ℝ)))
      - 2 * (107/125 : ℝ) * La θ (13/250 : ℝ) 0 + tf71f θ (13/250 : ℝ) 0 * (2762098309/2929687500 : ℝ) := by
    rw [hLa_a, hLa_ac] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

theorem rowcontra_0704_0704 {θ la1 laj : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ) (h2 : θ ≤ (153081763967161/100000000000000 : ℝ)) (htan : Real.tan θ = (25/1 : ℝ))
    (hla10 : 0 ≤ la1) (hla1a : la1 ≤ (88/125 : ℝ)) (hlajc : laj ≤ (88/125 : ℝ))
    (hcore : 0 ≤ ((107/125 : ℝ) ^ 2 + 1/2) * (La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj))
        - 2 * (107/125 : ℝ) * La θ (13/250 : ℝ) 0
        + tf71f θ (13/250 : ℝ) 0 * (2762098309/2929687500 : ℝ)) : False := by
  have hθ0 : 0 < θ := by linarith
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hlam : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨hE1lo, hE1hi⟩ := expb_0704_0704 h1 h2 htan
  have hcert := rowcert_0704_0704 h1 h2 htan hE1lo hE1hi
  -- hcert : (k²+½)·(tf71Fr (-a) − F(0)) − 2k F(0) + f0(slack) < 0
  have hLa_a : La θ (13/250 : ℝ) (88/125 : ℝ) = tf71Fr θ (13/250 : ℝ) ((-88/125 : ℝ)) := by
    have h := tf71F_real_eq θ (13/250 : ℝ) ((-88/125 : ℝ)) hθ0 hθπ hlam (by norm_num)
    have h' : La θ (13/250 : ℝ) (88/125 : ℝ) = ∫ t in (0:ℝ)..(2 * tf71γ θ (13/250 : ℝ)), Real.exp (-(((-88/125 : ℝ)) * t)) * tf71f θ (13/250 : ℝ) t := by
      unfold La
      exact intervalIntegral.integral_congr (fun t _ => by rw [show -(((-88/125 : ℝ)) * t) = (88/125 : ℝ) * t by ring])
    rw [h', h]
  have hLa0 : La θ (13/250 : ℝ) 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [La_zero θ (13/250 : ℝ) hθ0 hθπ hlam] <;> ring_nf
  have hf0 : tf71f θ (13/250 : ℝ) 0 = (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) := by
    rw [tf71f_at_zero (θ := θ) (lam := (13/250 : ℝ)) hθ0 hθπ hlam] <;> ring_nf
  have hmono : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) (88/125 : ℝ) - La θ (13/250 : ℝ) 0 := by
    have hstep : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - laj) ≤ La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (88/125 : ℝ)) := by
      have := La_mono hθ0 hθπ hlam (show la1 - (88/125 : ℝ) ≤ la1 - laj by linarith)
      linarith
    have hstep2 : La θ (13/250 : ℝ) la1 - La θ (13/250 : ℝ) (la1 - (88/125 : ℝ)) ≤ La θ (13/250 : ℝ) (88/125 : ℝ) - La θ (13/250 : ℝ) ((88/125 : ℝ) - (88/125 : ℝ)) := by
      have := La_sub_mono (show (0:ℝ) ≤ (88/125 : ℝ) by norm_num) hθ0 hθπ hlam hla1a
      simpa only [show (88/125 : ℝ) - (88/125 : ℝ) = 0 by norm_num] using this
    linarith [hstep, hstep2]
  have hA : 0 ≤ ((107/125 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) ((-88/125 : ℝ)) - 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      - 2 * (107/125 : ℝ) * La θ (13/250 : ℝ) 0 + tf71f θ (13/250 : ℝ) 0 * (2762098309/2929687500 : ℝ) := by
    rw [hLa_a, hLa0] at hmono
    linarith [hcore, hmono, hf0]
  rw [hLa0, hf0] at hA
  linarith [hA, hcert]

end Work.ZeroFreeTables.P9F
