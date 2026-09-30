import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.tk_bad_defs
import Submission.Work.BMF.SD.tk_general
import Submission.Work.BMF.SD.markov_inv
import Submission.Work.BMF.SD.multiples_card_le
import Submission.Work.BMF.SD.corr_dil_split
import Submission.Work.BMF.SD.tkw_error_le
import Submission.Work.BMF.SD.tkw_bad_per_y

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF

theorem tk_bad_weight (k : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ K : ℝ, 0 < K ∧ K ≤ 3200 / c₀ ^ 2 + 64 / c₀ + 8 ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n),
      ∀ (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X →
      ∀ (F : PhaseFamily k f c₀ X H),
        (∑ p ∈ primesIn P Q, (1 / (p : ℝ)) *
          (((F.fam.filter (fun y => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
            ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))).card : ℝ)))
          ≤ K * (F.fam.card : ℝ) := by
  refine ⟨3200 / c₀ ^ 2 + 64 / c₀ + 8, ?_, le_rfl, ?_⟩
  · positivity
  · intro f hf hmul X H P Q hP2 hPQ hQ3 hHX F
    have hQ2 : (2 : ℝ) ≤ Q := le_trans hP2 hPQ
    have hQpos : 0 < Q := by linarith
    have hH8 : (8 : ℝ) ≤ H := by
      have h8 : (8 : ℝ) ≤ Q ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hQ2 3
        norm_num at h
        exact h
      linarith
    have hHpos : 0 < H := by linarith
    have hH1 : (1 : ℝ) ≤ H := by linarith
    have hXpos : 0 < X := by linarith
    -- Turan--Kubilius second-moment bound for the discrepancy with the phase inserted
    have hTK : ∀ y ∈ F.fam, ∑ p ∈ primesIn P Q, (p : ℝ) * ‖tkw_disc f (F.pol y) p y H‖ ^ 2
        ≤ 200 * H ^ 2 := by
      intro y hy
      have hy0 : 0 ≤ y := by
        have h1 : X / 10 ≤ y := (F.isFam.1 y hy).1
        linarith
      have hg : ∀ n : ℕ, ‖f n * eC (-(Polynomial.eval (n : ℝ) (F.pol y)))‖ ≤ 1 := by
        intro n
        rw [norm_mul, norm_eC', mul_one]
        exact hf n
      have h := tk_general P Q y H (fun n => f n * eC (-(Polynomial.eval (n : ℝ) (F.pol y))))
        hP2 hPQ hQ3 hH1 hy0 hg
      simpa only [tkw_disc] using h
    -- Small discrepancy implies a large correlation of the dilated phase
    have hgood : ∀ y ∈ F.fam, ∀ p ∈ primesIn P Q, ¬ tkw_bad c₀ H f (F.pol y) y p →
        (c₀ / 2) * (H / (p : ℝ)) ≤
          ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖ := by
      intro y hy p hp hnb
      have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hppos : (0 : ℝ) < (p : ℝ) := by
        have : 0 < p := hpP.pos
        exact_mod_cast this
      have hpQ : (p : ℝ) ≤ Q := by
        have h1 : p ≤ ⌊Q⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        calc (p : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ Q := Nat.floor_le hQpos.le
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        have h : 2 ≤ p := hpP.two_le
        exact_mod_cast h
      have hbig : 64 / c₀ ≤ (p : ℝ) := by
        have h := hnb
        simp only [tkw_bad] at h
        push_neg at h
        exact h.1
      have hdisc' : (p : ℝ) ^ 2 * ‖tkw_disc f (F.pol y) p y H‖ ^ 2 ≤ (c₀ / 4) ^ 2 * H ^ 2 := by
        have h := hnb
        simp only [tkw_bad] at h
        push_neg at h
        exact h.2
      have hdisc : ‖tkw_disc f (F.pol y) p y H‖ ≤ (c₀ / 4) * (H / (p : ℝ)) := by
        have h1 : ((p : ℝ) * ‖tkw_disc f (F.pol y) p y H‖) ^ 2 ≤ ((c₀ / 4) * H) ^ 2 := by
          have h2 : ((p : ℝ) * ‖tkw_disc f (F.pol y) p y H‖) ^ 2
              = (p : ℝ) ^ 2 * ‖tkw_disc f (F.pol y) p y H‖ ^ 2 := by ring
          rw [h2]
          calc (p : ℝ) ^ 2 * ‖tkw_disc f (F.pol y) p y H‖ ^ 2 ≤ (c₀ / 4) ^ 2 * H ^ 2 := hdisc'
            _ = ((c₀ / 4) * H) ^ 2 := by ring
        have h3 : (p : ℝ) * ‖tkw_disc f (F.pol y) p y H‖ ≤ (c₀ / 4) * H := by
          have h4 := Real.sqrt_le_sqrt h1
          rw [Real.sqrt_sq (mul_nonneg hppos.le (norm_nonneg _)),
            Real.sqrt_sq (mul_nonneg (by positivity) hHpos.le)] at h4
          exact h4
        have h3' : ‖tkw_disc f (F.pol y) p y H‖ * (p : ℝ) ≤ (c₀ / 4) * H := by
          rw [mul_comm]; exact h3
        rw [← mul_div_assoc]
        exact (le_div_iff₀ hppos).mpr h3'
      have hcorr : c₀ * H ≤ ‖corr f (F.pol y) y H‖ := F.corr_ge y hy
      have hm3 : (3 * c₀ / 4) * (H / (p : ℝ)) ≤
          ‖∑ m ∈ natIcc (y / p) ((y + H) / p),
            f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y)))‖ := by
        have hsplit : (∑ m ∈ natIcc (y / p) ((y + H) / p),
              f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y))))
            = tkw_disc f (F.pol y) p y H + (1 / (p : ℂ)) * corr f (F.pol y) y H := by
          simp only [tkw_disc, corr]
          ring
        have h1 : ‖(1 / (p : ℂ)) * corr f (F.pol y) y H‖
            = (1 / (p : ℝ)) * ‖corr f (F.pol y) y H‖ := by
          rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        rw [hsplit]
        have h2 : ‖(1 / (p : ℂ)) * corr f (F.pol y) y H‖ - ‖tkw_disc f (F.pol y) p y H‖
            ≤ ‖tkw_disc f (F.pol y) p y H + (1 / (p : ℂ)) * corr f (F.pol y) y H‖ := by
          have h5 := abs_norm_sub_norm_le ((1 / (p : ℂ)) * corr f (F.pol y) y H)
            (-(tkw_disc f (F.pol y) p y H))
          have h6 : ‖-(tkw_disc f (F.pol y) p y H)‖ = ‖tkw_disc f (F.pol y) p y H‖ := norm_neg _
          have h7 : (1 / (p : ℂ)) * corr f (F.pol y) y H - (-(tkw_disc f (F.pol y) p y H))
              = tkw_disc f (F.pol y) p y H + (1 / (p : ℂ)) * corr f (F.pol y) y H := by ring
          rw [h7, h6] at h5
          exact le_trans (le_abs_self _) h5
        have h6 : (1 / (p : ℝ)) * (c₀ * H) ≤ (1 / (p : ℝ)) * ‖corr f (F.pol y) y H‖ :=
          mul_le_mul_of_nonneg_left hcorr (by positivity)
        have h7 : (1 / (p : ℝ)) * (c₀ * H) = c₀ * H / (p : ℝ) := by ring
        have h8 : c₀ * H / (p : ℝ) - (c₀ / 4) * (H / (p : ℝ)) = (3 * c₀ / 4) * (H / (p : ℝ)) :=
          by ring
        linarith [h1, h2, h6, h7, h8, hdisc]
      have hmult := corr_dil_split f hf hmul (F.pol y) p hpP y H
      have hcardmult : (((natIcc (y / p) ((y + H) / p)).filter (fun m => p ∣ m)).card : ℝ)
          ≤ H / (p : ℝ) ^ 2 + 2 := by
        have hab : y / p ≤ (y + H) / p := by
          rw [add_div]
          exact le_add_of_nonneg_right (div_nonneg hHpos.le hppos.le)
        have h := multiples_card_le p (y / p) ((y + H) / p) hpP.pos hab
        have h2 : ((y + H) / p - y / p) / (p : ℝ) = H / (p : ℝ) ^ 2 := by
          field_simp; ring
        linarith [h, h2]
      have herr : ‖(∑ m ∈ natIcc (y / p) ((y + H) / p),
            f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y))))
          - f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p)‖
          ≤ (c₀ / 4) * (H / (p : ℝ)) := by
        have h1 : 2 * (H / (p : ℝ) ^ 2 + 2) ≤ (c₀ / 4) * (H / (p : ℝ)) :=
          tkw_error_le c₀ H Q p hc₀ hp2 hbig hpQ hQ3
        linarith [hmult, hcardmult, h1]
      have hmain : (c₀ / 2) * (H / (p : ℝ))
          ≤ ‖f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p)‖ := by
        have h5 := norm_add_le (f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p))
          ((∑ m ∈ natIcc (y / p) ((y + H) / p),
            f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y))))
          - f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p))
        have h6 : f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p)
            + ((∑ m ∈ natIcc (y / p) ((y + H) / p),
              f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y))))
            - f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p))
            = (∑ m ∈ natIcc (y / p) ((y + H) / p),
              f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y)))) := by ring
        rw [h6] at h5
        have h7 : (0 : ℝ) ≤ ‖(∑ m ∈ natIcc (y / p) ((y + H) / p),
            f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) (F.pol y))))
          - f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p)‖ := norm_nonneg _
        linarith [h5, hm3, herr, h7]
      have hnorm_le : ‖f p * corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p)‖
          ≤ ‖corr f (dil (p : ℝ) (F.pol y)) (y / p) (H / p)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hf p)
      linarith
    -- Assembly: pointwise `bad ⊆ bad`, then swap the order of summation
    have hstep2 : ∑ y ∈ F.fam, ∑ p ∈ (primesIn P Q).filter
          (fun p => tkw_bad c₀ H f (F.pol y) y p), (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ primesIn P Q, (1 / (p : ℝ)) *
            ((F.fam.filter (fun y => tkw_bad c₀ H f (F.pol y) y p)).card : ℝ) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter (s := F.fam)
        (p := fun y => tkw_bad c₀ H f (F.pol y) y p) (f := fun _ => (1 : ℝ) / (p : ℝ))]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have hpoint : ∀ p ∈ primesIn P Q,
        ((F.fam.filter (fun y => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
          ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))).card : ℝ)
        ≤ ((F.fam.filter (fun y => tkw_bad c₀ H f (F.pol y) y p)).card : ℝ) := by
      intro p hp
      have hsub : F.fam.filter (fun y => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
          ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))
          ⊆ F.fam.filter (fun y => tkw_bad c₀ H f (F.pol y) y p) := by
        intro y hy
        rw [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by
          by_contra hnb
          exact hy.2 (hgood y hy.1 p hp hnb)⟩
      exact_mod_cast Finset.card_le_card hsub
    calc ∑ p ∈ primesIn P Q, (1 / (p : ℝ)) *
          (((F.fam.filter (fun y => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
            ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))).card : ℝ))
        ≤ ∑ p ∈ primesIn P Q, (1 / (p : ℝ)) *
            ((F.fam.filter (fun y => tkw_bad c₀ H f (F.pol y) y p)).card : ℝ) :=
          Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hpoint p hp) (by positivity))
      _ = ∑ y ∈ F.fam, ∑ p ∈ (primesIn P Q).filter
            (fun p => tkw_bad c₀ H f (F.pol y) y p), (1 : ℝ) / (p : ℝ) := hstep2.symm
      _ ≤ ∑ _y ∈ F.fam, (3200 / c₀ ^ 2 + 64 / c₀ + 8) :=
          Finset.sum_le_sum (fun y hy => tkw_bad_per_y c₀ H hc₀ hHpos f (F.pol y)
            (primesIn P Q) y (hTK y hy))
      _ = (3200 / c₀ ^ 2 + 64 / c₀ + 8) * (F.fam.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Work.BMF.SD
