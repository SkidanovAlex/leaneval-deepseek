import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_own_c
import Submission.Work.Deep.Nibble.log_one_sub_bound

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

/-! ## Elementary estimates -/

/-- `1 + t + t²/4 ≤ exp t` for `t ≥ 0`, from `exp (t/2) ≥ 1 + t/2`. -/
lemma r2S_exp_quad {t : ℝ} (ht : 0 ≤ t) : 1 + t + t ^ 2 / 4 ≤ Real.exp t := by
  have h1 : 1 + t / 2 ≤ Real.exp (t / 2) := by
    have h := Real.add_one_le_exp (t / 2)
    linarith only [h]
  have h0 : (0 : ℝ) ≤ 1 + t / 2 := by linarith only [ht]
  have h2 : (1 + t / 2) ^ 2 ≤ (Real.exp (t / 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have he : (Real.exp (t / 2)) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : (1 + t / 2) ^ 2 = 1 + t + t ^ 2 / 4 := by ring
  linarith only [h2, he, hsq]

/-- `log (1 - p) ≥ -(p + 2 p²)` for `0 ≤ p ≤ 1/2`. -/
lemma r2S_log_bound {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    -(p + 2 * p ^ 2) ≤ Real.log (1 - p) := by
  have h1p : 0 < 1 - p := by linarith only [hp2]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 - p)⁻¹ from inv_pos.mpr h1p)
  rw [Real.log_inv] at h
  have h2 : (1 - p)⁻¹ - 1 = p / (1 - p) := by
    rw [inv_eq_one_div]
    field_simp
    ring
  rw [h2] at h
  have h3 : p / (1 - p) ≤ p + 2 * p ^ 2 := by
    rw [div_le_iff₀ h1p]
    nlinarith only [hp2, sq_nonneg p]
  linarith only [h, h3]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The per-vertex estimate -/

/-- **Per-vertex estimate for the collision multiplicity.**

If `p = θ/D`, `|d - D| ≤ ε D` with `4ε ≤ δ ≤ θ/100`, `0 < θ ≤ 1/100` and `8θ² ≤ δ D`, then the
contribution `d p (1 - (1-p)^{d-1})` of a vertex of degree `d` to the mean collision multiplicity
is at most `(1 + δ/2) (θ - θ e^{-θ})`. -/
lemma r2S_per_vertex {θ δ ε p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100) (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100)
    (hεδ : 4 * ε ≤ δ) {D d : ℕ} (hD : 8 ≤ D) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp2 : p ≤ 1 / 2) (hpD : p * (D : ℝ) = θ) (hbig : 8 * θ ^ 2 ≤ δ * (D : ℝ))
    (hdeg : |(d : ℝ) - (D : ℝ)| ≤ ε * (D : ℝ)) :
    (d : ℝ) * p - (d : ℝ) * p * (1 - p) ^ (d - 1)
      ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) := by
  have hθnn : 0 ≤ θ := le_of_lt hθ0
  have hεθ4 : ε ≤ θ / 4 := by linarith only [hεδ, hδ1, hε0]
  have hq0 : 0 ≤ 1 - p := by linarith only [hp1]
  have hq1 : 1 - p ≤ 1 := by linarith only [hp0]
  have hqpos : 0 < 1 - p := by linarith only [hp2]
  have hlog : -(p + 2 * p ^ 2) ≤ Real.log (1 - p) := r2S_log_bound hp0 hp2
  have hE : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hθ0])
  have hAnn : 0 ≤ θ - θ * Real.exp (-θ) := by nlinarith only [hθnn, hE]
  have hAnn' : 0 ≤ 1 - Real.exp (-θ) := by linarith only [hE]
  -- exponential form of the `(d-1)`-fold comparison of `(1-p)^{d-1}` with a lower bound
  have hpow_of : ∀ {Λ : ℝ}, ((d - 1 : ℕ) : ℝ) * (p + 2 * p ^ 2) ≤ Λ →
      Real.exp (-Λ) ≤ (1 - p) ^ (d - 1) := by
    intro Λ hΛ
    have heq : Real.exp (((d - 1 : ℕ) : ℝ) * Real.log (1 - p)) = (1 - p) ^ (d - 1) := by
      rw [Real.exp_nat_mul, Real.exp_log hqpos]
    rw [← heq]
    apply Real.exp_le_exp.mpr
    have h1 : ((d - 1 : ℕ) : ℝ) * (-(p + 2 * p ^ 2)) ≤ ((d - 1 : ℕ) : ℝ) * Real.log (1 - p) :=
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    have h2 : ((d - 1 : ℕ) : ℝ) * (-(p + 2 * p ^ 2))
        = -(((d - 1 : ℕ) : ℝ) * (p + 2 * p ^ 2)) := by ring
    linarith only [h1, h2, hΛ]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `d = 0`
    subst hd0
    have h : 0 ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) :=
      mul_nonneg (by linarith only [hδ0]) hAnn
    simpa using h
  · have hd1R : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hdpos, Nat.cast_one]
    have hdl1 : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.sub_le d 1
    by_cases hle : d ≤ D
    · -- case `d ≤ D`
      have hdle : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hle
      have hDp : (D : ℝ) * p = θ := by rw [mul_comm (D : ℝ) p, hpD]
      have hdp : (d : ℝ) * p ≤ θ := by
        have h1 : (d : ℝ) * p ≤ (D : ℝ) * p := mul_le_mul_of_nonneg_right hdle hp0
        linarith only [h1, hDp]
      have hΛ : ((d - 1 : ℕ) : ℝ) * (p + 2 * p ^ 2) ≤ θ := by
        have hA : ((d - 1 : ℕ) : ℝ) * p ≤ θ - p := by
          rw [hd1R]; nlinarith only [hdp]
        have hB : 2 * (((d - 1 : ℕ) : ℝ) * p ^ 2) ≤ p := by
          have h4 : ((d - 1 : ℕ) : ℝ) * p ^ 2 ≤ (D : ℝ) * p ^ 2 :=
            mul_le_mul_of_nonneg_right (le_trans hdl1 hdle) (sq_nonneg p)
          have h5 : (D : ℝ) * p ^ 2 = θ * p := by
            calc (D : ℝ) * p ^ 2 = ((D : ℝ) * p) * p := by ring
              _ = θ * p := by rw [hDp]
          have h6 : 2 * (θ * p) ≤ p := by nlinarith only [hθ1, hp0]
          nlinarith only [h4, h5, h6]
        nlinarith only [hA, hB]
      have hpow : Real.exp (-θ) ≤ (1 - p) ^ (d - 1) := hpow_of hΛ
      have hden : 1 - (1 - p) ^ (d - 1) ≤ 1 - Real.exp (-θ) := by linarith only [hpow]
      have hnnc : 0 ≤ 1 - (1 - p) ^ (d - 1) := by
        have h := pow_le_one₀ hq0 hq1 (n := d - 1)
        linarith only [h]
      calc (d : ℝ) * p - (d : ℝ) * p * (1 - p) ^ (d - 1)
          = (d : ℝ) * p * (1 - (1 - p) ^ (d - 1)) := by ring
        _ ≤ θ * (1 - Real.exp (-θ)) := mul_le_mul hdp hden hnnc hθnn
        _ ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) := by
            have h1 : θ * (1 - Real.exp (-θ)) = (1 : ℝ) * (θ - θ * Real.exp (-θ)) := by ring
            rw [h1]
            exact mul_le_mul_of_nonneg_right
              (by linarith only [hδ0] : (1 : ℝ) ≤ 1 + δ / 2) hAnn
    · -- case `D < d`
      have hdDup : (d : ℝ) ≤ (1 + ε) * (D : ℝ) := by
        have h := (abs_le.mp hdeg).2
        nlinarith only [h]
      have hx : (1 + ε) * θ ≤ θ + θ ^ 2 / 4 := by
        have h : ε * θ ≤ θ ^ 2 / 4 := by nlinarith only [hεθ4, hθnn]
        nlinarith only [h]
      have h2x : 2 * ((1 + ε) * θ) ≤ 1 := by
        have hsq : θ ^ 2 ≤ θ / 100 := by nlinarith only [hθnn, hθ1]
        nlinarith only [hx, hsq, hθ1]
      have hxn : 0 ≤ (1 + ε) * θ := by nlinarith only [hε0, hθnn]
      have hdpx : (d : ℝ) * p ≤ (1 + ε) * θ := by
        have h1 : (d : ℝ) * p ≤ (1 + ε) * (D : ℝ) * p := mul_le_mul_of_nonneg_right hdDup hp0
        have h2 : (1 + ε) * (D : ℝ) * p = (1 + ε) * θ := by
          calc (1 + ε) * (D : ℝ) * p = (1 + ε) * ((D : ℝ) * p) := by ring
            _ = (1 + ε) * θ := by rw [mul_comm (D : ℝ) p, hpD]
        linarith only [h1, h2]
      have hΛ : ((d - 1 : ℕ) : ℝ) * (p + 2 * p ^ 2) ≤ (1 + ε) * θ := by
        have hA : ((d - 1 : ℕ) : ℝ) * p ≤ (1 + ε) * θ - p := by
          rw [hd1R]; nlinarith only [hdpx]
        have hB : 2 * (((d - 1 : ℕ) : ℝ) * p ^ 2) ≤ p := by
          have h4 : ((d - 1 : ℕ) : ℝ) * p ^ 2 ≤ (1 + ε) * (D : ℝ) * p ^ 2 :=
            mul_le_mul_of_nonneg_right (le_trans hdl1 hdDup) (sq_nonneg p)
          have h5 : (1 + ε) * (D : ℝ) * p ^ 2 = ((1 + ε) * θ) * p := by
            calc (1 + ε) * (D : ℝ) * p ^ 2 = (1 + ε) * ((D : ℝ) * p) * p := by ring
              _ = (1 + ε) * θ * p := by rw [mul_comm (D : ℝ) p, hpD]
              _ = ((1 + ε) * θ) * p := by ring
          have h6 : 2 * (((1 + ε) * θ) * p) ≤ p := by nlinarith only [h2x, hp0]
          nlinarith only [h4, h5, h6]
        nlinarith only [hA, hB]
      have hpow : Real.exp (-((1 + ε) * θ)) ≤ (1 - p) ^ (d - 1) := hpow_of hΛ
      have hden : 1 - (1 - p) ^ (d - 1) ≤ 1 - Real.exp (-((1 + ε) * θ)) := by
        linarith only [hpow]
      have hnnc : 0 ≤ 1 - (1 - p) ^ (d - 1) := by
        have h := pow_le_one₀ hq0 hq1 (n := d - 1)
        linarith only [h]
      have hstep1 : (d : ℝ) * p - (d : ℝ) * p * (1 - p) ^ (d - 1)
          ≤ ((1 + ε) * θ) * (1 - Real.exp (-((1 + ε) * θ))) := by
        have he : (d : ℝ) * p - (d : ℝ) * p * (1 - p) ^ (d - 1)
            = (d : ℝ) * p * (1 - (1 - p) ^ (d - 1)) := by ring
        rw [he]
        exact mul_le_mul hdpx hden hnnc hxn
      have hdec : ((1 + ε) * θ) * (1 - Real.exp (-((1 + ε) * θ)))
          ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) := by
        have hA : 0 ≤ 1 - Real.exp (-θ) := hAnn'
        have hB : 0 ≤ 1 - Real.exp (-(ε * θ)) := by
          have h : Real.exp (-(ε * θ)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith only [hε0, hθnn])
          linarith only [h]
        have hexpadd : Real.exp (-((1 + ε) * θ)) = Real.exp (-θ) * Real.exp (-(ε * θ)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h1es : 1 - Real.exp (-(ε * θ)) ≤ ε * θ := by
          have h := Real.add_one_le_exp (-(ε * θ))
          linarith only [h]
        have hKI : ((1 + ε) * θ) * Real.exp (-θ) ≤ 1 - Real.exp (-θ) := by
          have hq : 1 + θ + θ ^ 2 / 4 ≤ Real.exp θ := r2S_exp_quad hθnn
          have hxle : (1 + ε) * θ ≤ Real.exp θ - 1 := by linarith only [hq, hx]
          have h2 := mul_le_mul_of_nonneg_right hxle (Real.exp_nonneg (-θ))
          have h3 : (Real.exp θ - 1) * Real.exp (-θ) = 1 - Real.exp (-θ) := by
            rw [sub_mul, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
          linarith only [h2, h3]
        have hident : ((1 + ε) * θ) * (1 - Real.exp (-((1 + ε) * θ)))
            = θ * (1 - Real.exp (-θ)) + (ε * θ) * (1 - Real.exp (-θ))
              + (((1 + ε) * θ) * Real.exp (-θ)) * (1 - Real.exp (-(ε * θ))) := by
          rw [hexpadd]; ring
        have h3 : (((1 + ε) * θ) * Real.exp (-θ)) * (1 - Real.exp (-(ε * θ)))
            ≤ (1 - Real.exp (-θ)) * (ε * θ) := by
          calc (((1 + ε) * θ) * Real.exp (-θ)) * (1 - Real.exp (-(ε * θ)))
              ≤ (1 - Real.exp (-θ)) * (1 - Real.exp (-(ε * θ))) :=
                mul_le_mul_of_nonneg_right hKI hB
            _ ≤ (1 - Real.exp (-θ)) * (ε * θ) := mul_le_mul_of_nonneg_left h1es hA
        have h2e : 2 * ε ≤ δ / 2 := by linarith only [hεδ]
        have hfin_eq : θ * (1 - Real.exp (-θ)) + (ε * θ) * (1 - Real.exp (-θ))
              + (1 - Real.exp (-θ)) * (ε * θ)
            = (1 + 2 * ε) * (θ * (1 - Real.exp (-θ))) := by ring
        have hfin_mono : (1 + 2 * ε) * (θ * (1 - Real.exp (-θ)))
            ≤ (1 + δ / 2) * (θ * (1 - Real.exp (-θ))) :=
          mul_le_mul_of_nonneg_right (by linarith only [h2e] : 1 + 2 * ε ≤ 1 + δ / 2)
            (mul_nonneg hθnn hA)
        have hfin_rhs : (1 + δ / 2) * (θ * (1 - Real.exp (-θ)))
            = (1 + δ / 2) * (θ - θ * Real.exp (-θ)) := by ring
        linarith only [hident, h3, hfin_eq, hfin_mono, hfin_rhs]
      linarith only [hstep1, hdec]

/-! ## The main estimate -/

theorem r2_S_mean {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V))
    {θ δ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ)
    {D : ℕ} (hD : 8 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hθD : θ / (D : ℝ) ≤ 1 / 2) (hbig : 8 * θ ^ 2 ≤ δ * (D : ℝ))
    (hdeg : ∀ v : V, |((Work.Deep.Nibble.hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) :
    (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ((Work.Deep.Nibble.collMult 𝓖 ω : ℕ) : ℝ))
      ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) * (Fintype.card V : ℝ) := by
  classical
  have hDne : (D : ℝ) ≠ 0 := by
    have h : 0 < D := by omega
    exact_mod_cast ne_of_gt h
  have hpd : (θ / (D : ℝ)) * (D : ℝ) = θ := div_mul_cancel₀ θ hDne
  have hmean := (r2_exp_adv 𝓖 (p := θ / (D : ℝ)) hp0 hp1).1
  rw [hmean]
  have hsum : ∑ v : V, ((hd 𝓖 v : ℝ) * (θ / (D : ℝ)) - (hd 𝓖 v : ℝ) * (θ / (D : ℝ))
        * (1 - θ / (D : ℝ)) ^ (hd 𝓖 v - 1))
      ≤ ∑ _v : V, (1 + δ / 2) * (θ - θ * Real.exp (-θ)) :=
    Finset.sum_le_sum fun v _ =>
      r2S_per_vertex hθ0 hθ1 hδ0 hδ1 hε0 hε1 hεδ hD hp0 hp1 hθD hpd hbig (hdeg v)
  refine le_trans hsum (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Work.Deep.Nibble
