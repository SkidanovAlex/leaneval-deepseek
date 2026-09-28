import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.tau_basic
import Submission.Work.HP.evaldefs
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.IntForm
import Submission.Work.HP.LsetAux.abs_rNorm_sub_le
import Submission.Work.HP.HP2.mon_lip
import Submission.Work.HP.HP2.veronese_lip_sharp
import Submission.Work.HP.HP2.sum_abs_le_sqrt_card_mul

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.HP2

private theorem formEvalR_sub_le_rNorm (d n : ℕ) (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ) :
    |formEvalR d n a x - formEvalR d n a y| ≤
      rNorm a * rNorm (veronese d n x - veronese d n y) := by
  have h : formEvalR d n a x - formEvalR d n a y = dotR a (veronese d n x - veronese d n y) := by
    rw [formEvalR_eq_dotR, formEvalR_eq_dotR, dotR_sub_right]
  rw [h]
  exact abs_dotR_le a _

private theorem abs_formEvalR_le_rNorm (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) :
    |formEvalR d n a x| ≤ rNorm a * rNorm (veronese d n x) := by
  rw [formEvalR_eq_dotR]
  exact abs_dotR_le a _

private theorem veronese_rNorm_lip_sharp (d n : ℕ) {R : ℝ} (hR : 1 ≤ R)
    {x y : Fin (n + 1) → ℝ} (hx : rNorm x ≤ R) (hy : rNorm y ≤ R) :
    rNorm (veronese d n x - veronese d n y) ≤
      Real.sqrt (NN d n) * ((d : ℝ) * R ^ (d - 1) * (∑ i, |x i - y i|)) := by
  have hM : 0 ≤ (d : ℝ) * R ^ (d - 1) * (∑ i, |x i - y i|) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (le_trans zero_le_one hR) _))
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hcoord : ∀ μ : Mon d n,
      |(veronese d n x - veronese d n y) μ| ≤ (d : ℝ) * R ^ (d - 1) * (∑ i, |x i - y i|) :=
    fun μ => by simpa using veronese_lip_sharp d n μ hR hx hy
  exact Work.HP.rNorm_le_sqrt_card_mul (veronese d n x - veronese d n y) hM hcoord

private theorem veronese_sq_lip (d n : ℕ) {R : ℝ} (hR : 1 ≤ R)
    {x y : Fin (n + 1) → ℝ} (hx : rNorm x ≤ R) (hy : rNorm y ≤ R) :
    |(rNorm (veronese d n x)) ^ 2 - (rNorm (veronese d n y)) ^ 2| ≤
      2 * (NN d n : ℝ) * (d : ℝ) * R ^ (2 * d - 1) * (∑ i, |x i - y i|) := by
  set Sx := rNorm (veronese d n x) with hSxd
  set Sy := rNorm (veronese d n y) with hSyd
  set T := ∑ i, |x i - y i| with hTd
  set s := Real.sqrt (NN d n) with hsd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hSr : rNorm (veronese d n x - veronese d n y) ≤ s * ((d : ℝ) * R ^ (d - 1) * T) := by
    have h := veronese_rNorm_lip_sharp d n hR hx hy
    simpa [hsd, hTd] using h
  have hdiff : |Sx - Sy| ≤ s * ((d : ℝ) * R ^ (d - 1) * T) := by
    have h := Work.HP.LsetAux.abs_rNorm_sub_le (veronese d n x) (veronese d n y)
    rw [hSxd, hSyd]
    exact h.trans hSr
  have hbound : |Sx + Sy| ≤ 2 * s * R ^ d := by
    have h1 : Sx ≤ s * R ^ d := by
      rw [hSxd, hsd]
      exact Work.HP.rNorm_veronese_le hR0 hx
    have h2 : Sy ≤ s * R ^ d := by
      rw [hSyd, hsd]
      exact Work.HP.rNorm_veronese_le hR0 hy
    calc |Sx + Sy| ≤ |Sx| + |Sy| := abs_add_le _ _
      _ = Sx + Sy := by rw [abs_of_nonneg (by rw [hSxd]; exact rNorm_nonneg _),
            abs_of_nonneg (by rw [hSyd]; exact rNorm_nonneg _)]
      _ ≤ s * R ^ d + s * R ^ d := add_le_add h1 h2
      _ = 2 * s * R ^ d := by ring
  have hfac : Sx ^ 2 - Sy ^ 2 = (Sx - Sy) * (Sx + Sy) := by ring
  rw [hfac, abs_mul]
  have hprod : 0 ≤ s * ((d : ℝ) * R ^ (d - 1) * T) :=
    mul_nonneg hs0 (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hR0 _)) hT0)
  calc |Sx - Sy| * |Sx + Sy| ≤ (s * ((d : ℝ) * R ^ (d - 1) * T)) * (2 * s * R ^ d) :=
        mul_le_mul hdiff hbound (abs_nonneg _) hprod
    _ = 2 * (NN d n : ℝ) * (d : ℝ) * R ^ (2 * d - 1) * T := by
        have hsq : s * s = (NN d n : ℝ) := by
          rw [hsd, ← sq]; exact Real.sq_sqrt (by positivity)
        have hpow : R ^ (d - 1) * R ^ d = R ^ (2 * d - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [← hsq, ← hpow]; ring

private theorem formEvalR_sq_lip (d n : ℕ) (a : Mon d n → ℝ) {R : ℝ} (hR : 1 ≤ R)
    {x y : Fin (n + 1) → ℝ} (hx : rNorm x ≤ R) (hy : rNorm y ≤ R) :
    |(formEvalR d n a x) ^ 2 - (formEvalR d n a y) ^ 2| ≤
      2 * (NN d n : ℝ) * (d : ℝ) * (rNorm a) ^ 2 * R ^ (2 * d - 1) * (∑ i, |x i - y i|) := by
  set Qx := formEvalR d n a x with hQxd
  set Qy := formEvalR d n a y with hQyd
  set A := rNorm a with hAd
  set T := ∑ i, |x i - y i| with hTd
  set s := Real.sqrt (NN d n) with hsd
  have hA0 : 0 ≤ A := by rw [hAd]; exact rNorm_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hSr : rNorm (veronese d n x - veronese d n y) ≤ s * ((d : ℝ) * R ^ (d - 1) * T) := by
    have h := veronese_rNorm_lip_sharp d n hR hx hy
    simpa [hsd, hTd] using h
  have hSx : rNorm (veronese d n x) ≤ s * R ^ d := by
    rw [hsd]; exact Work.HP.rNorm_veronese_le hR0 hx
  have hSy : rNorm (veronese d n y) ≤ s * R ^ d := by
    rw [hsd]; exact Work.HP.rNorm_veronese_le hR0 hy
  have hlip : |Qx - Qy| ≤ A * (s * ((d : ℝ) * R ^ (d - 1) * T)) := by
    have h1 : |Qx - Qy| ≤ A * rNorm (veronese d n x - veronese d n y) := by
      rw [hQxd, hQyd, hAd]
      exact formEvalR_sub_le_rNorm d n a x y
    exact h1.trans (mul_le_mul_of_nonneg_left hSr hA0)
  have hQxb : |Qx| ≤ A * (s * R ^ d) := by
    have h1 : |Qx| ≤ A * rNorm (veronese d n x) := by
      rw [hQxd, hAd]
      exact abs_formEvalR_le_rNorm d n a x
    exact h1.trans (mul_le_mul_of_nonneg_left hSx hA0)
  have hQyb : |Qy| ≤ A * (s * R ^ d) := by
    have h1 : |Qy| ≤ A * rNorm (veronese d n y) := by
      rw [hQyd, hAd]
      exact abs_formEvalR_le_rNorm d n a y
    exact h1.trans (mul_le_mul_of_nonneg_left hSy hA0)
  have hsum : |Qx + Qy| ≤ 2 * (A * (s * R ^ d)) := by
    calc |Qx + Qy| ≤ |Qx| + |Qy| := abs_add_le _ _
      _ ≤ A * (s * R ^ d) + A * (s * R ^ d) := add_le_add hQxb hQyb
      _ = 2 * (A * (s * R ^ d)) := by ring
  have hfac : Qx ^ 2 - Qy ^ 2 = (Qx - Qy) * (Qx + Qy) := by ring
  rw [hfac, abs_mul]
  have hprod : 0 ≤ A * (s * ((d : ℝ) * R ^ (d - 1) * T)) :=
    mul_nonneg hA0 (mul_nonneg hs0 (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hR0 _)) hT0))
  calc |Qx - Qy| * |Qx + Qy|
        ≤ (A * (s * ((d : ℝ) * R ^ (d - 1) * T))) * (2 * (A * (s * R ^ d))) :=
        mul_le_mul hlip hsum (abs_nonneg _) hprod
    _ = 2 * (NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T := by
        have hsq : s * s = (NN d n : ℝ) := by
          rw [hsd, ← sq]; exact Real.sq_sqrt (by positivity)
        have hpow : R ^ (d - 1) * R ^ d = R ^ (2 * d - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [← hsq, ← hpow]; ring

theorem Psi_lip_sharp (d n : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Work.HP.Mon d n → ℤ) (α R : ℝ) (x y : Fin (n + 1) → ℝ),
      1 ≤ α → 1 ≤ R → Work.HP.rNorm x ≤ R → Work.HP.rNorm y ≤ R →
      |Work.HP.Psi d n a α x - Work.HP.Psi d n a α y|
        ≤ C * α ^ 2 * (Work.HP.eNorm a) ^ 2 * R ^ (2 * d - 1) * Work.HP.rNorm (x - y) := by
  refine ⟨10 * (NN d n : ℝ) * (d : ℝ) * ((n : ℝ) + 1) + 1, by positivity, ?_⟩
  intro a α R x y hα hR hx hy
  simp only [Psi]
  set Qx := formEvalR d n (toR a) x with hQxd
  set Qy := formEvalR d n (toR a) y with hQyd
  set Sx := rNorm (veronese d n x) with hSxd
  set Sy := rNorm (veronese d n y) with hSyd
  set A := eNorm a with hAd
  set T := ∑ i, |x i - y i| with hTd
  set δ := rNorm (x - y) with hδd
  have hA0 : 0 ≤ A := by rw [hAd]; exact Real.sqrt_nonneg _
  have hα0 : 0 ≤ α := le_trans zero_le_one hα
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hT0 : 0 ≤ T := by rw [hTd]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hδ0 : 0 ≤ δ := by rw [hδd]; exact rNorm_nonneg _
  have hk1 : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hTδ : T ≤ Real.sqrt ((n : ℝ) + 1) * δ := by
    have h := sum_abs_le_sqrt_card_mul (x - y)
    simpa [hTd, hδd, Pi.sub_apply] using h
  have hsq : |Qx ^ 2 - Qy ^ 2| ≤ 2 * (NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T := by
    have h := formEvalR_sq_lip d n (toR a) hR hx hy
    rw [Work.HP.rNorm_toR] at h
    simpa [hQxd, hQyd, hAd, hTd] using h
  have hvsq : |Sx ^ 2 - Sy ^ 2| ≤ 2 * (NN d n : ℝ) * (d : ℝ) * R ^ (2 * d - 1) * T := by
    have h := veronese_sq_lip d n hR hx hy
    simpa [hSxd, hSyd, hTd] using h
  have h4nn : (0:ℝ) ≤ 4 * α ^ 2 := by positivity
  have hA2nn : (0:ℝ) ≤ A ^ 2 := by positivity
  have hmain : |4 * α ^ 2 * Qx ^ 2 - A ^ 2 * Sx ^ 2 - (4 * α ^ 2 * Qy ^ 2 - A ^ 2 * Sy ^ 2)|
      ≤ 4 * α ^ 2 * (2 * (NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T)
        + A ^ 2 * (2 * (NN d n : ℝ) * (d : ℝ) * R ^ (2 * d - 1) * T) := by
    have hsplit : 4 * α ^ 2 * Qx ^ 2 - A ^ 2 * Sx ^ 2 - (4 * α ^ 2 * Qy ^ 2 - A ^ 2 * Sy ^ 2)
        = 4 * α ^ 2 * (Qx ^ 2 - Qy ^ 2) - A ^ 2 * (Sx ^ 2 - Sy ^ 2) := by ring
    rw [hsplit]
    have htri : |4 * α ^ 2 * (Qx ^ 2 - Qy ^ 2) - A ^ 2 * (Sx ^ 2 - Sy ^ 2)|
        ≤ |4 * α ^ 2 * (Qx ^ 2 - Qy ^ 2)| + |A ^ 2 * (Sx ^ 2 - Sy ^ 2)| := by
      have h := abs_sub_le (4 * α ^ 2 * (Qx ^ 2 - Qy ^ 2)) 0 (A ^ 2 * (Sx ^ 2 - Sy ^ 2))
      rw [sub_zero, zero_sub, abs_neg] at h
      exact h
    calc |4 * α ^ 2 * (Qx ^ 2 - Qy ^ 2) - A ^ 2 * (Sx ^ 2 - Sy ^ 2)|
        ≤ |4 * α ^ 2 * (Qx ^ 2 - Qy ^ 2)| + |A ^ 2 * (Sx ^ 2 - Sy ^ 2)| := htri
      _ = 4 * α ^ 2 * |Qx ^ 2 - Qy ^ 2| + A ^ 2 * |Sx ^ 2 - Sy ^ 2| := by
          rw [abs_mul, abs_of_nonneg h4nn, abs_mul, abs_of_nonneg hA2nn]
      _ ≤ 4 * α ^ 2 * (2 * (NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T)
            + A ^ 2 * (2 * (NN d n : ℝ) * (d : ℝ) * R ^ (2 * d - 1) * T) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hsq (by positivity)
          · exact mul_le_mul_of_nonneg_left hvsq (by positivity)
  have hM0 : 0 ≤ (NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T := by positivity
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_self_iff]; exact Or.inr hk1
  calc |4 * α ^ 2 * Qx ^ 2 - A ^ 2 * Sx ^ 2 - (4 * α ^ 2 * Qy ^ 2 - A ^ 2 * Sy ^ 2)|
      ≤ 4 * α ^ 2 * (2 * (NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T)
        + A ^ 2 * (2 * (NN d n : ℝ) * (d : ℝ) * R ^ (2 * d - 1) * T) := hmain
    _ = (8 * α ^ 2 + 2) * ((NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T) := by ring
    _ ≤ 10 * α ^ 2 * ((NN d n : ℝ) * (d : ℝ) * A ^ 2 * R ^ (2 * d - 1) * T) := by
        apply mul_le_mul_of_nonneg_right _ hM0
        nlinarith [sq_nonneg (α - 1), hα]
    _ = 10 * (NN d n : ℝ) * (d : ℝ) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1) * T := by ring
    _ ≤ 10 * (NN d n : ℝ) * (d : ℝ) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1)
          * (Real.sqrt ((n : ℝ) + 1) * δ) := by
        apply mul_le_mul_of_nonneg_left hTδ
        positivity
    _ ≤ (10 * (NN d n : ℝ) * (d : ℝ) * ((n : ℝ) + 1) + 1) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1) * δ := by
        have hs : Real.sqrt ((n : ℝ) + 1) * δ ≤ ((n : ℝ) + 1) * δ :=
          mul_le_mul_of_nonneg_right hsqrt hδ0
        have hcoef : 0 ≤ 10 * (NN d n : ℝ) * (d : ℝ) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1) := by positivity
        calc 10 * (NN d n : ℝ) * (d : ℝ) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1)
              * (Real.sqrt ((n : ℝ) + 1) * δ)
            ≤ 10 * (NN d n : ℝ) * (d : ℝ) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1)
              * (((n : ℝ) + 1) * δ) := mul_le_mul_of_nonneg_left hs hcoef
          _ = 10 * (NN d n : ℝ) * (d : ℝ) * ((n : ℝ) + 1) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1) * δ := by ring
          _ ≤ (10 * (NN d n : ℝ) * (d : ℝ) * ((n : ℝ) + 1) + 1) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1) * δ := by
              have hxp : (10 * (NN d n : ℝ) * (d : ℝ) * ((n : ℝ) + 1) + 1) * α ^ 2 * A ^ 2
                    * R ^ (2 * d - 1) * δ
                  = 10 * (NN d n : ℝ) * (d : ℝ) * ((n : ℝ) + 1) * α ^ 2 * A ^ 2 * R ^ (2 * d - 1) * δ
                    + α ^ 2 * A ^ 2 * R ^ (2 * d - 1) * δ := by ring
              rw [hxp]
              exact le_add_of_nonneg_right (by positivity)

end Work.HP.HP2
