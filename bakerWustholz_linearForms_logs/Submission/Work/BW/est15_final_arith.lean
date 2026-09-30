import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.num_est15_slacks
import Submission.Work.BW.num_est15_arch2
import Submission.Work.BW.est15_arith_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `m⁻¹(d - m) ≤ d - 1` for `1 ≤ m` and `1 ≤ d`. -/
private lemma est15_hQle' (d m : ℝ) (hm1 : 1 ≤ m) (hd1 : 1 ≤ d) :
    (1 / m) * (d - m) ≤ d - 1 := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have h2 : d * 1 ≤ d * m := mul_le_mul_of_nonneg_left hm1 hd0
  have h3 : (1 / m) * (d - m) = (d - m) / m := by ring
  rw [h3, div_le_iff₀ hm0]
  linarith [h2]

/-- The pure real-arithmetic assembly of BW (15) at level `J`: from the Archimedean core bound
`(1/m)(d-m)·Ci ≤ (d-1)hT* + (d-1)(0.193·S·D/d) + 0.007·(|s|/2^J)·D` together with the three slack
bounds `LNN ≤ 0.001·S·D/d`, `MonS ≤ (|s|/2^J)·D`, `E ≤ kum_J` and `1 ≤ m`, `1 ≤ d`, `Hp ≥ 0`, gets
the final shape of the estimate: the `Ci`-budget `0.193 + 0.001 = 0.194 ≤ 0.204` of `(1-1/d)SD`
and the `|s|`-budget `0.007 + 1 = 1.007`. -/
private lemma est15_final_assembly {d m h S D Tst Hp LNN Ci MonS E K z : ℝ}
    (hd1 : 1 ≤ d) (hm1 : 1 ≤ m) (hh : 0 ≤ h) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hz : 0 ≤ z) (hHp : 0 ≤ Hp) (hLNN0 : 0 ≤ LNN) (hE0 : 0 ≤ E)
    (hLNN : LNN ≤ 0.001 * S * D / d) (hMonS : MonS ≤ z * D) (hE : E ≤ K)
    (hcore : (1 / m) * (d - m) * Ci ≤ (d - 1) * (h * Tst) + (d - 1) * (0.018 * S * D / d)
        + (d - 1) * (0.075 * S * D / d) + (d - 1) * (0.1 * S * D / d) + 0.007 * z * D) :
    (1 / m) * Hp + (1 / m) * (d - m) * (LNN + Ci) + (1 / m) * (MonS + E)
      ≤ Hp + (1 - 1 / d) * (d * h * Tst + 0.204 * S * D) + 1.007 * z * D + K := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd1
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
  have h1m0 : (0 : ℝ) ≤ 1 / m := by positivity
  have h1m1 : 1 / m ≤ 1 := by
    rw [one_div]; exact inv_le_one_of_one_le₀ hm1
  have hd10 : (0 : ℝ) ≤ d - 1 := by linarith
  have hSD0 : (0 : ℝ) ≤ S * D := mul_nonneg hS hD
  have hcoef0 : (0 : ℝ) ≤ 1 - 1 / d := by
    rw [sub_nonneg, one_div]
    exact inv_le_one_of_one_le₀ hd1
  -- ## the `Hp` term
  have hstep1 : (1 / m) * Hp ≤ Hp := by
    have h := mul_le_mul_of_nonneg_right h1m1 hHp
    linarith [h]
  -- ## the `LNN` term
  have hQ : (1 / m) * (d - m) ≤ d - 1 := est15_hQle' d m hm1 hd1
  have hLNN1 : (1 / m) * (d - m) * LNN ≤ (d - 1) * LNN :=
    mul_le_mul_of_nonneg_right hQ hLNN0
  have hLNN2 : (d - 1) * LNN ≤ (d - 1) * (0.001 * S * D / d) :=
    mul_le_mul_of_nonneg_left hLNN hd10
  have hLNN3 : (d - 1) * (0.001 * S * D / d) = (1 - 1 / d) * (0.001 * S * D) := by
    field_simp <;> ring
  -- ## the coefficient budget `0.193 + 0.001 ≤ 0.204`
  have hb1 : (d - 1) * (0.018 * S * D / d) = (1 - 1 / d) * (0.018 * S * D) := by
    field_simp <;> ring
  have hb2 : (d - 1) * (0.075 * S * D / d) = (1 - 1 / d) * (0.075 * S * D) := by
    field_simp <;> ring
  have hb3 : (d - 1) * (0.1 * S * D / d) = (1 - 1 / d) * (0.1 * S * D) := by
    field_simp <;> ring
  have hbud : (d - 1) * (0.018 * S * D / d) + (d - 1) * (0.075 * S * D / d)
        + (d - 1) * (0.1 * S * D / d) + (1 - 1 / d) * (0.001 * S * D)
      ≤ (1 - 1 / d) * (0.204 * S * D) := by
    rw [hb1, hb2, hb3]
    have he : (1 - 1 / d) * (0.018 * S * D) + (1 - 1 / d) * (0.075 * S * D)
        + (1 - 1 / d) * (0.1 * S * D) + (1 - 1 / d) * (0.001 * S * D)
        = (1 - 1 / d) * (0.194 * S * D) := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hcoef0
    nlinarith [hSD0]
  -- ## the `MonS` term
  have hMon1 : (1 / m) * MonS ≤ z * D := by
    rcases le_total MonS 0 with hle | hge
    · have h : (1 / m) * MonS ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1m0 hle
      have h2 : (0 : ℝ) ≤ z * D := mul_nonneg hz hD
      linarith
    · have h := mul_le_mul_of_nonneg_right h1m1 hge
      linarith [h, hMonS]
  -- ## the Kummer term
  have hE1 : (1 / m) * E ≤ K := by
    have h := mul_le_mul_of_nonneg_right h1m1 hE0
    linarith [h, hE]
  -- ## assembly
  have hsplit : (1 / m) * (d - m) * (LNN + Ci) = (1 / m) * (d - m) * LNN + (1 / m) * (d - m) * Ci :=
    by ring
  have hsplit2 : (1 / m) * (MonS + E) = (1 / m) * MonS + (1 / m) * E := by ring
  have hT : (1 - 1 / d) * (d * h * Tst) = (d - 1) * (h * Tst) := by
    field_simp <;> ring
  have hdist : (1 - 1 / d) * (d * h * Tst + 0.204 * S * D)
      = (1 - 1 / d) * (d * h * Tst) + (1 - 1 / d) * (0.204 * S * D) := by ring
  rw [hsplit, hsplit2, hdist, hT]
  linarith [hstep1, hLNN1, hLNN2, hLNN3, hbud, hMon1, hE1, hcore]

theorem est15_final_arith {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (Tst m LNN MonS : ℝ) (hTst : Tst ≤ acT K σ) (htT : estTp t + (t0 : ℝ) ≤ Tst)
    (hm1 : 1 ≤ m) (hmd : m ≤ (dK K : ℝ))
    (hLNN : LNN ≤ 0.001 * acS K r b v * acD K σ / (dK K : ℝ)) (hLNN0 : 0 ≤ LNN)
    (hMonS : MonS ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ) (hp : 0 ≤ Height.logHeight p) :
    (1 / m) * Height.logHeight p
      + (1 / m) * ((dK K : ℝ) - m) * (LNN + estCi K b v σ J t0 t s)
      + (1 / m) * (MonS + estKum K b v σ J)
      ≤ Height.logHeight p
        + (1 - 1 / (dK K : ℝ)) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst
            + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J := by
  classical
  -- ## non-degeneracy
  have hr : 2 ≤ r := H.hr
  have hd1 : 1 ≤ dK K := Module.finrank_pos
  have hdR : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
  have hh0 : (0 : ℝ) ≤ (acH K b v : ℝ) := by positivity
  have hS0 : (0 : ℝ) ≤ acS K r b v := by simp only [acS]; positivity
  have hDpos : (0 : ℝ) < acD K σ := pD_pos hr hd1 σ (fun j => sigma_ge H j)
  have hD0 : (0 : ℝ) ≤ acD K σ := le_of_lt hDpos
  have hz0 : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) / 2 ^ J := by positivity
  have hTp0 : (0 : ℝ) ≤ estTp t := by simp only [estTp]; positivity
  have ht0nn : (0 : ℝ) ≤ (t0 : ℝ) := Nat.cast_nonneg _
  have hTst0 : (0 : ℝ) ≤ Tst := by linarith [htT, hTp0, ht0nn]
  have htp : estTp t ≤ Tst := by linarith [htT, ht0nn]
  have ht0 : (t0 : ℝ) ≤ Tst := by linarith [htT, hTp0]
  -- ## the Archimedean core, with `estTp t + t₀` replaced by `Tst`
  have hcore0 := est15_arith_core H J t0 t s Tst m hTst hTst0 ht0 htp hm1 hmd
  have hd1R : (0 : ℝ) ≤ (dK K : ℝ) - 1 := by linarith
  have hcore : (1 / m) * ((dK K : ℝ) - m) * estCi K b v σ J t0 t s
      ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * Tst)
        + ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ))
        + ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ))
        + ((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ))
        + 0.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ := by
    have hmono : ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * (estTp t + (t0 : ℝ)))
        ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * Tst) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htT hh0) hd1R
    linarith [hcore0, hmono]
  -- ## the Kummer term
  have hkum : estKum K b v σ J ≤ kumJ K b v σ J := by
    simpa only [estKum] using (num_est15_slacks H J).2.2.2
  have hE0 : (0 : ℝ) ≤ estKum K b v σ J := by simp only [estKum]; positivity
  exact est15_final_assembly hdR hm1 hh0 hS0 hD0 hz0 hp hLNN0 hE0 hLNN hMonS hkum hcore

end Work.BW
