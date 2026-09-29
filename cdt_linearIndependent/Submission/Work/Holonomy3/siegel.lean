import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.disc_shift_lipschitz
import Submission.Work.Holonomy3.lattice_lowdisc_card
import Submission.Work.Holonomy3.card_bad_real
import Submission.Work.Holonomy3.matEntry_bound
import Submission.Work.Holonomy3.auxSeries_injective
import Submission.Work.Holonomy3.coeff_auxSeries_mkQ
import Submission.Work.Holonomy3.final_arith

set_option maxHeartbeats 8000000

attribute [local instance] Matrix.seminormedAddCommGroup

namespace Work.Holonomy3
open Submission.CDTPlan Submission.CDT.Discrepancy
open scoped BigOperators

variable {m r d : ℕ} {D : ℕ} {ε δ : ℝ}

/-- `(x+1)^d - x^d ≤ d (x+1)^{d-1}` for `x ≥ 0`. -/
lemma pow_add_one_sub_pow_le (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    (x + 1) ^ d - x ^ d ≤ (d : ℝ) * (x + 1) ^ (d - 1) := by
  induction d with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      norm_num
    · have hx1 : (0:ℝ) ≤ x + 1 := by linarith
      have hpow : (x + 1) ^ (n + 1) - x ^ (n + 1) =
          (x + 1) * ((x + 1) ^ n - x ^ n) + x ^ n := by
        rw [pow_succ, pow_succ]; ring
      have hxn : x ^ n ≤ (x + 1) ^ n := pow_le_pow_left₀ hx (by linarith) n
      have hstep : (x + 1) * ((x + 1) ^ n - x ^ n) ≤ (x + 1) * ((n : ℝ) * (x + 1) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left ih hx1
      have hsplit : (x + 1) * ((n : ℝ) * (x + 1) ^ (n - 1)) = (n : ℝ) * (x + 1) ^ n := by
        rw [mul_comm (x + 1), mul_assoc, ← pow_succ]
        congr 2
        exact Nat.sub_add_cancel hn
      have h2 : (n : ℝ) * (x + 1) ^ n + x ^ n ≤ ((n : ℝ) + 1) * (x + 1) ^ n := by
        nlinarith [hxn]
      calc (x + 1) ^ (n + 1) - x ^ (n + 1)
          = (x + 1) * ((x + 1) ^ n - x ^ n) + x ^ n := hpow
        _ ≤ (x + 1) * ((n : ℝ) * (x + 1) ^ (n - 1)) + x ^ n := by linarith
        _ = (n : ℝ) * (x + 1) ^ n + x ^ n := by rw [hsplit]
        _ ≤ ((n : ℝ) + 1) * (x + 1) ^ n := h2
        _ = ((n + 1 : ℕ) : ℝ) * (x + 1) ^ ((n + 1) - 1) := by
            push_cast [Nat.add_sub_cancel]
            ring

/-- `A^d c ≤ ε` eventually, for `0 ≤ A < 1`. -/
lemma exists_pow_mul_le {A ε c : ℝ} (hA : 0 ≤ A) (hA1 : A < 1) (hε : 0 < ε) (hc : 0 < c) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → A ^ d * c ≤ ε := by
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hA hA1
  have h1 : ∀ᶠ d : ℕ in Filter.atTop, A ^ d < ε / c :=
    (tendsto_order.1 h0).2 _ (div_pos hε hc)
  obtain ⟨d₀, hd₀⟩ := Filter.eventually_atTop.1 h1
  exact ⟨d₀, fun d hd => by
    have h := hd₀ d hd
    rw [lt_div_iff₀ hc] at h
    linarith⟩

/-- `B / D ≤ ε` eventually, for `B ≥ 0`. -/
lemma exists_div_le {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → B / D ≤ ε := by
  refine ⟨Nat.ceil (B / ε) + 1, fun D hD => ?_⟩
  have hceil : B / ε ≤ (Nat.ceil (B / ε) : ℝ) := Nat.le_ceil _
  have hDge : (Nat.ceil (B / ε) : ℝ) ≤ D := by
    have h1 : Nat.ceil (B / ε) ≤ D := Nat.le_of_succ_le hD
    exact_mod_cast h1
  have hD1 : 1 ≤ D := by omega
  have hDpos : (0:ℝ) < D := by exact_mod_cast hD1
  rw [div_le_iff₀ hDpos]
  calc B = (B / ε) * ε := (div_mul_cancel₀ B hε.ne').symm
    _ ≤ (Nat.ceil (B / ε) : ℝ) * ε := mul_le_mul_of_nonneg_right hceil hε.le
    _ = ε * (Nat.ceil (B / ε) : ℝ) := by ring
    _ ≤ ε * (D : ℝ) := mul_le_mul_of_nonneg_left hDge hε.le

/-- `B log(D+1) ≤ ε D^2` eventually, for `B ≥ 0`. -/
lemma exists_mul_log_le {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → B * Real.log (D + 1) ≤ ε * D ^ 2 := by
  obtain ⟨D₀, hD₀⟩ := exists_div_le hB hε
  refine ⟨max D₀ 1, fun D hD => ?_⟩
  have hD1 : 1 ≤ D := le_trans (le_max_right _ _) hD
  have hDpos : (0:ℝ) < D := by exact_mod_cast hD1
  have hlog : Real.log (D + 1) ≤ (D : ℝ) := by
    have h1 : Real.log ((D:ℝ) + 1) ≤ ((D:ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hBD : B ≤ ε * D := by
    have h2 := hD₀ D (le_trans (le_max_left _ _) hD)
    rw [div_le_iff₀ hDpos] at h2
    linarith
  calc B * Real.log (D + 1) ≤ B * D := mul_le_mul_of_nonneg_left hlog hB
    _ ≤ (ε * D) * D := mul_le_mul_of_nonneg_right hBD hDpos.le
    _ = ε * D ^ 2 := by ring


-- ═══════════════════ TEMPORARY STUBS for the pending child modules ═══════════════════

lemma exp_pow_mul_exp (X Y : ℝ) (d : ℕ) (hX : 0 < X) :
    X^d * Real.exp Y = Real.exp ((d:ℝ) * Real.log X + Y) := by
  have h1 : X^d = Real.exp ((d:ℝ) * Real.log X) := by
    conv_lhs => rw [← Real.exp_log hX]
    rw [← Real.exp_nat_mul]
  rw [h1, ← Real.exp_add]

/-- The box part of the row count: `(⌊(m-δ)D⌋+1)^d ≤ A₀^d (m-δ/2)^d D^d`. -/
lemma floor_box_pow_le {m D d : ℕ} {δ A₀ : ℝ} (hA₀ : 0 ≤ A₀) (hmδ : 0 ≤ (m:ℝ) - δ)
    (hDbox : (m-δ)*D + 1 ≤ A₀ * ((m:ℝ) - δ/2) * D) :
    ((Nat.floor ((m-δ)*D) + 1 : ℕ) : ℝ)^d ≤ A₀^d * (((m:ℝ)-δ/2)^d * (D:ℝ)^d) := by
  have h1 : ((Nat.floor ((m-δ)*D) + 1 : ℕ) : ℝ) ≤ A₀ * ((m:ℝ) - δ/2) * D := by
    have h2 : ((Nat.floor ((m-δ)*D) : ℕ) : ℝ) ≤ (m-δ)*D :=
      Nat.floor_le (mul_nonneg hmδ (Nat.cast_nonneg D))
    push_cast
    linarith
  calc ((Nat.floor ((m-δ)*D) + 1 : ℕ) : ℝ)^d ≤ (A₀ * ((m:ℝ) - δ/2) * D)^d :=
        pow_le_pow_left₀ (by linarith) h1 d
    _ = A₀^d * (((m:ℝ)-δ/2)^d * (D:ℝ)^d) := by rw [mul_pow, mul_pow]; ring

/-- The high-discrepancy part of the row count. -/
lemma floor_bad_pow_le {m D d : ℕ} {δ ρ A₀ ε : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρd : ρ ≤ (Real.exp (-(ε/2)^4/200))^d)
    (hμle : ((m:ℝ)+δ)/((m:ℝ)-δ/2) * Real.exp (-(ε/2)^4/200) ≤ A₀) (hA₀ : 0 ≤ A₀)
    (hmδ : 0 < (m:ℝ) - δ/2) :
    ((Nat.floor ((m+δ)*D) : ℕ) : ℝ)^d * ρ ≤ A₀^d * (((m:ℝ)-δ/2)^d * (D:ℝ)^d) := by
  have hnum : (0:ℝ) ≤ (m:ℝ) + δ := by linarith
  have hden : (0:ℝ) ≤ (m:ℝ) - δ/2 := hmδ.le
  have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
  have h1 : ((Nat.floor ((m+δ)*D) : ℕ) : ℝ) ≤ (m+δ)*D :=
    Nat.floor_le (mul_nonneg hnum hDnn)
  have h2 : ((Nat.floor ((m+δ)*D) : ℕ) : ℝ)^d ≤ ((m+δ)*D)^d :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h1 d
  have h3 : ((m:ℝ)+δ)^d * ρ ≤ A₀^d * ((m:ℝ)-δ/2)^d := by
    have hce : 0 ≤ Real.exp (-(ε/2)^4/200) := Real.exp_nonneg _
    have h5 : (((m:ℝ)+δ)/((m:ℝ)-δ/2))^d * (Real.exp (-(ε/2)^4/200))^d ≤ A₀^d := by
      have h6 := pow_le_pow_left₀ (mul_nonneg (div_nonneg hnum hden) hce) hμle d
      rwa [mul_pow] at h6
    have h7 : (Real.exp (-(ε/2)^4/200))^d * ((m:ℝ)+δ)^d ≤ A₀^d * ((m:ℝ)-δ/2)^d := by
      have h8 : ((m:ℝ)+δ)^d / ((m:ℝ)-δ/2)^d = (((m:ℝ)+δ)/((m:ℝ)-δ/2))^d := by rw [div_pow]
      have h9 : ((m:ℝ)+δ)^d / ((m:ℝ)-δ/2)^d * (Real.exp (-(ε/2)^4/200))^d ≤ A₀^d := by
        rw [h8]; exact h5
      have h10 := mul_le_mul_of_nonneg_right h9 (by positivity : (0:ℝ) ≤ ((m:ℝ)-δ/2)^d)
      have hB0 : ((m:ℝ)-δ/2)^d ≠ 0 := by
        have : (0:ℝ) < (m:ℝ)-δ/2 := hmδ
        positivity
      have h11 : (Real.exp (-(ε/2)^4/200))^d * ((m:ℝ)+δ)^d =
          (((m:ℝ)+δ)^d / ((m:ℝ)-δ/2)^d * (Real.exp (-(ε/2)^4/200))^d) * ((m:ℝ)-δ/2)^d := by
        rw [mul_assoc, mul_comm ((Real.exp (-(ε/2)^4/200))^d) (((m:ℝ)-δ/2)^d),
          ← mul_assoc, div_mul_cancel₀ _ hB0, mul_comm]
      rw [h11]
      exact h10
    calc ((m:ℝ)+δ)^d * ρ ≤ ((m:ℝ)+δ)^d * (Real.exp (-(ε/2)^4/200))^d :=
          mul_le_mul_of_nonneg_left hρd (by positivity)
      _ = (Real.exp (-(ε/2)^4/200))^d * ((m:ℝ)+δ)^d := by ring
      _ ≤ A₀^d * ((m:ℝ)-δ/2)^d := h7
  calc ((Nat.floor ((m+δ)*D) : ℕ) : ℝ)^d * ρ ≤ ((m+δ)*D)^d * ρ :=
        mul_le_mul_of_nonneg_right h2 hρ0
    _ = (((m:ℝ)+δ)^d * ρ) * (D:ℝ)^d := by rw [mul_pow]; ring
    _ ≤ (A₀^d * ((m:ℝ)-δ/2)^d) * (D:ℝ)^d :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = A₀^d * (((m:ℝ)-δ/2)^d * (D:ℝ)^d) := by ring

/-- The boundary part of the row count, in the un-divided form. -/
lemma floor_sub_pow_le {m D d : ℕ} {δ : ℝ} (hm : 0 < m) (hmδ : 0 ≤ (m:ℝ) + δ) (hδm : δ ≤ m)
    (hD : 0 < (D:ℝ)) (hR1 : 1 ≤ (m+δ)*D) :
    ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d ≤
      (d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1) := by
  have hDnn : (0:ℝ) ≤ (D:ℝ) := hD.le
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h1 : ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d ≤
      (d:ℝ) * ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^(d-1) :=
    pow_add_one_sub_pow_le _ (Nat.cast_nonneg _) d
  have h2 : ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ) ≤ 2 * ((m+δ)*D) := by
    have h3 : ((Nat.floor ((m+δ)*D) : ℕ) : ℝ) ≤ (m+δ)*D :=
      Nat.floor_le (mul_nonneg hmδ (Nat.cast_nonneg D))
    push_cast
    linarith
  have h4 : ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^(d-1) ≤
      2^(d-1) * ((m:ℝ)+δ)^(d-1) * (D:ℝ)^(d-1) := by
    calc ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^(d-1) ≤ (2 * ((m+δ)*D))^(d-1) :=
          pow_le_pow_left₀ (by positivity) h2 _
      _ = 2^(d-1) * ((m:ℝ)+δ)^(d-1) * (D:ℝ)^(d-1) := by rw [mul_pow, mul_pow]; ring
  have h8 : ((m:ℝ)+δ)^(d-1) ≤ ((m:ℝ)+δ+1)^(d-1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h13 : 2^(d-1) * ((m:ℝ)+δ)^(d-1) * (D:ℝ)^(d-1) ≤
      2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1) := by
    have h14 : 2^(d-1) * ((m:ℝ)+δ)^(d-1) ≤ 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) :=
      mul_le_mul_of_nonneg_left h8 (by positivity)
    exact mul_le_mul_of_nonneg_right h14 (by positivity)
  calc ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d
      ≤ (d:ℝ) * ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^(d-1) := h1
    _ ≤ (d:ℝ) * (2^(d-1) * ((m:ℝ)+δ)^(d-1) * (D:ℝ)^(d-1)) :=
        mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg d)
    _ ≤ (d:ℝ) * (2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1)) :=
        mul_le_mul_of_nonneg_left h13 (Nat.cast_nonneg d)
    _ = (d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1) := by ring

/-- Turning the un-divided boundary bound into the form with `Bdd / D`. -/
lemma bdd_mul_eq {m D d : ℕ} {δ : ℝ} (hd : 0 < d) (hmδ : 0 < (m:ℝ) - δ/2) (hD : 0 < (D:ℝ)) :
    ((d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) / ((m:ℝ)-δ/2)^d / D) *
      (((m:ℝ)-δ/2)^d * (D:ℝ)^d) =
      (d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1) := by
  have hB : ((m:ℝ)-δ/2)^d ≠ 0 := by
    have : (0:ℝ) < (m:ℝ)-δ/2 := hmδ
    positivity
  have hDn : (D:ℝ) ≠ 0 := hD.ne'
  have hDd : (D:ℝ)^d = (D:ℝ)^(d-1) * D := by
    conv_lhs => rw [show d = (d-1)+1 by omega]
    rw [pow_succ]
  rw [div_div, hDd,
    show ((m:ℝ)-δ/2)^d * ((D:ℝ)^(d-1) * D) = (((m:ℝ)-δ/2)^d * D) * (D:ℝ)^(d-1) by ring,
    ← mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hB hDn)]

theorem siegel {m r : ℕ} (hm : 0 < m) (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ)
    (f : Fin m → PowerSeries ℚ) (hden : ∀ i, Submission.CDTPlan.HasDenomType (e i) (b i) (f i))
    (hpi : Submission.CDTPlan.PolyIndependent f) (hdc : Submission.CDTPlan.DClosed f)
    (A : ℝ) (hA : 1 ≤ A)
    (hgr : ∀ i n, ‖((PowerSeries.coeff n (f i) : ℚ) : ℝ)‖ ≤ A ^ n) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → m ∣ d → ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∃ Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ,
        Work.Holonomy3.AuxTemplate D ε (Real.exp (ε * d * D)) Q ∧
        Submission.CDTPlan.auxSeries f Q ≠ 0 ∧
        (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m - δ) * D) →
          MvPowerSeries.coeff n (Submission.CDTPlan.auxSeries f Q) = 0) ∧
        (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m + δ) * D) →
          ε ≤ Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) →
          MvPowerSeries.coeff n (Submission.CDTPlan.auxSeries f Q) = 0) := by
  intro ε hε0 hε1
  -- ═══ the clearing data and the height constant
  set C : DenData b e f hden := denData hden with hCdef
  obtain ⟨Ch, hChnn, hCh⟩ := matEntry_bound b e f hden C hA hgr
  -- ═══ the parameter δ
  set δ : ℝ := min (ε / 2) ((m : ℝ) * ε ^ 4 / 20000) with hδdef
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hε4 : 0 < ε ^ 4 := by positivity
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by positivity)
  have hδlt : δ < ε := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδle : δ ≤ (m : ℝ) * ε ^ 4 / 20000 := by rw [hδdef]; exact min_le_right _ _
  have hδm : δ ≤ (m : ℝ) / 2 := by
    have h4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1.le
    have h2 : (m : ℝ) * ε ^ 4 / 20000 ≤ (m : ℝ) / 2 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 20000)]; nlinarith
    linarith
  have hδm2' : δ ≤ (m:ℝ) := by linarith
  have hδsmall : 3 * δ / (m : ℝ) < (ε / 2) ^ 4 / 200 := by
    have h1 : 3 * δ / (m : ℝ) ≤ 3 * (ε ^ 4 / 20000) := by
      rw [div_le_iff₀ hmR]; nlinarith [hδle]
    have h2 : 3 * (ε ^ 4 / 20000) < (ε / 2) ^ 4 / 200 := by
      have h3 : (ε / 2) ^ 4 / 200 = ε ^ 4 / 3200 := by ring
      rw [h3]; nlinarith [hε4]
    linarith
  -- ═══ the exponential bases
  have hmδ2pos : 0 < (m : ℝ) - δ / 2 := by linarith
  have hmδpos : 0 < (m : ℝ) - δ := by linarith
  set α : ℝ := (m - δ) / (m - δ / 2) with hαdef
  have hα1 : α < 1 := by rw [hαdef, div_lt_one hmδ2pos]; linarith
  have hαpos : 0 < α := by rw [hαdef]; positivity
  set μ : ℝ := ((m + δ) / (m - δ / 2)) * Real.exp (-(ε / 2) ^ 4 / 200) with hμdef
  have hμnn : 0 ≤ μ := by rw [hμdef]; positivity
  have hμ1 : μ < 1 := by
    have hrat : 0 < (m + δ) / (m - δ / 2) := by positivity
    have hlog : Real.log ((m + δ) / (m - δ / 2)) < (ε / 2) ^ 4 / 200 := by
      have h1 : Real.log ((m + δ) / (m - δ / 2)) = Real.log (1 + (3 * δ / 2) / (m - δ / 2)) := by
        have h1b : (m + δ) = (m - δ / 2) + 3 * δ / 2 := by ring
        congr 1
        rw [h1b, add_div, div_self (by linarith : (m - δ / 2) ≠ 0)]
      rw [h1]
      have h2 : Real.log (1 + (3 * δ / 2) / (m - δ / 2)) ≤ (3 * δ / 2) / (m - δ / 2) := by
        have h3 : Real.log (1 + (3 * δ / 2) / (m - δ / 2)) ≤
            (1 + (3 * δ / 2) / (m - δ / 2)) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        linarith
      have h4 : (3 * δ / 2) / (m - δ / 2) ≤ 3 * δ / m := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < m - δ / 2), div_mul_eq_mul_div, le_div_iff₀ hmR]
        nlinarith
      linarith
    have hμpos : 0 < μ := by rw [hμdef]; positivity
    have h5 : Real.log μ < 0 := by
      rw [hμdef, Real.log_mul hrat.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    exact (Real.log_neg_iff hμpos).mp h5
  set A₀ : ℝ := max ((α + 1) / 2) μ with hA0def
  have hA0nn : 0 ≤ A₀ := by
    have h1 : (0:ℝ) ≤ (α + 1) / 2 := by linarith [hαpos]
    rw [hA0def]
    exact le_trans h1 (le_max_left _ _)
  have hA0lt : A₀ < 1 := by
    rw [hA0def]; exact max_lt (by linarith) hμ1
  have hA0α : (α + 1) / 2 ≤ A₀ := le_max_left _ _
  have hA0μ : μ ≤ A₀ := le_max_right _ _
  -- ═══ the threshold for `ρ`
  have hρthresh : ∃ d₂ : ℕ, ∀ d : ℕ, d₂ ≤ d →
      100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100) ≤ 1 / 2 ∧
      100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100) ≤
        Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 200) := by
    refine ⟨Nat.ceil (200 * Real.log 200 / (ε / 2) ^ 4) + 1, fun d hd => ?_⟩
    have hc4 : (0:ℝ) < (ε/2)^4 := by positivity
    have hdge : 200 * Real.log 200 / (ε/2)^4 ≤ (d:ℝ) := by
      have h1 : 200 * Real.log 200 / (ε/2)^4 ≤
          (Nat.ceil (200 * Real.log 200 / (ε/2)^4) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (200 * Real.log 200 / (ε/2)^4) : ℝ) ≤ d := by
        exact_mod_cast (Nat.le_of_succ_le hd)
      linarith
    rw [div_le_iff₀ hc4] at hdge
    have hlog200 : Real.log 200 ≤ (d:ℝ) * (ε/2)^4 / 200 := by linarith
    have hlog100 : Real.log 100 ≤ (d:ℝ) * (ε/2)^4 / 200 :=
      le_trans (Real.log_le_log (by norm_num) (by norm_num)) hlog200
    constructor
    · have h1 : Real.exp (-(d:ℝ) * (ε/2)^4 / 100) ≤ Real.exp (-(Real.log 200)) := by
        apply Real.exp_le_exp.mpr
        have h0 : (0:ℝ) ≤ (d:ℝ) * (ε/2)^4 := by positivity
        nlinarith [hlog200, h0]
      have h2 : Real.exp (-(Real.log 200)) = (200:ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
      rw [h2] at h1
      calc 100 * Real.exp (-(d:ℝ) * (ε/2)^4 / 100) ≤ 100 * (200:ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 1/2 := by norm_num
    · have h3 : (100:ℝ) ≤ Real.exp ((d:ℝ) * (ε/2)^4 / 200) := by
        calc (100:ℝ) = Real.exp (Real.log 100) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp ((d:ℝ) * (ε/2)^4 / 200) := Real.exp_le_exp.mpr hlog100
      calc 100 * Real.exp (-(d:ℝ) * (ε/2)^4 / 100)
          ≤ Real.exp ((d:ℝ) * (ε/2)^4 / 200) * Real.exp (-(d:ℝ) * (ε/2)^4 / 100) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
        _ = Real.exp (-(d:ℝ) * (ε/2)^4 / 200) := by
            rw [← Real.exp_add]; congr 1; ring
  -- ═══ the constants of the `d`-threshold
  set Kd : ℝ := 16*(m:ℝ) + 8*Ch*((m:ℝ)+δ+2) + 4 with hKddef
  have hKdpos : 0 < Kd := by
    rw [hKddef]
    have : (0:ℝ) ≤ Ch * ((m:ℝ) + δ + 1) := mul_nonneg hChnn (by linarith)
    linarith
  obtain ⟨d₂, hd₂⟩ := hρthresh
  obtain ⟨d₃, hd₃⟩ := exists_pow_mul_le hA0nn hA0lt (by linarith : (0:ℝ) < ε/4) hKdpos
  obtain ⟨d₁, hd₁⟩ := balanced_indices m hm (δ/2) (by linarith) (by linarith)
  refine ⟨δ, hδpos, hδlt, ?_⟩
  refine ⟨d₁ + d₂ + (d₃ + (Nat.ceil (8/ε) + 1)), ?_⟩
  intro d hd0 hmd
  have hd1 : d₁ ≤ d := by omega
  have hd2 : d₂ ≤ d := by omega
  have hd3 : d₃ ≤ d := by omega
  have hd8' : Nat.ceil (8/ε) + 1 ≤ d := by omega
  have hdpos : 1 ≤ d := by omega
  have hdR : (0:ℝ) < d := by exact_mod_cast hdpos
  have hd8 : (8:ℝ) ≤ ε * d := by
    have h5 : (8:ℝ)/ε ≤ (d:ℝ) :=
      le_trans (Nat.le_ceil (8/ε)) (by exact_mod_cast Nat.le_of_succ_le hd8')
    rw [div_le_iff₀ hε0] at h5
    linarith
  have hρ1 : 100 * Real.exp (-(d:ℝ) * (ε/2)^4 / 100) ≤ 1/2 := (hd₂ d hd2).1
  have hρ2 : 100 * Real.exp (-(d:ℝ) * (ε/2)^4 / 100) ≤
      Real.exp (-(d:ℝ) * (ε/2)^4 / 200) := (hd₂ d hd2).2
  have hKd : A₀^d * Kd ≤ ε/4 := hd₃ d hd3
  set ρ : ℝ := 100 * Real.exp (-(d:ℝ) * (ε/2)^4 / 100) with hρdef
  have hρnn : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρ1' : ρ ≤ 1/2 := hρ1
  have hρ2' : ρ ≤ Real.exp (-(d:ℝ) * (ε/2)^4 / 200) := hρ2
  -- ═══ the boundary constant
  set Bdd : ℝ := (d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) / ((m:ℝ)-δ/2)^d with hBdddef
  have hBddnn : 0 ≤ Bdd := by
    rw [hBdddef]
    have h1 : (0:ℝ) < (m:ℝ) - δ/2 := by linarith
    have h2 : (0:ℝ) < (m:ℝ) + δ + 1 := by linarith
    have h3 : (0:ℝ) < 2^(d-1) := by positivity
    have h4 : (0:ℝ) ≤ (d:ℝ) := by positivity
    positivity
  -- ═══ the thresholds for `D`
  refine ⟨(Nat.ceil (1/((m:ℝ)+δ)) + 1) + (Nat.ceil (8/ε) + 1) + (Nat.ceil (8/(ε*((m:ℝ)+δ))) + 1)
      + (Nat.ceil (4/δ) + 1) + (Nat.ceil (16*Bdd) + 1) + (Nat.ceil (32*Bdd*(m:ℝ)/ε) + 1)
      + (Nat.ceil (16*Bdd*Ch*((m:ℝ)+δ+2)/ε) + 1) + (Nat.ceil (8*Bdd) + 1), ?_⟩
  intro D hD
  have hTA : Nat.ceil (1/((m:ℝ)+δ)) + 1 ≤ D := by omega
  have hTB : Nat.ceil (8/ε) + 1 ≤ D := by omega
  have hTC : Nat.ceil (8/(ε*((m:ℝ)+δ))) + 1 ≤ D := by omega
  have hTD : Nat.ceil (4/δ) + 1 ≤ D := by omega
  have hTE : Nat.ceil (16*Bdd) + 1 ≤ D := by omega
  have hTF : Nat.ceil (32*Bdd*(m:ℝ)/ε) + 1 ≤ D := by omega
  have hTG : Nat.ceil (16*Bdd*Ch*((m:ℝ)+δ+2)/ε) + 1 ≤ D := by omega
  have hTH : Nat.ceil (8*Bdd) + 1 ≤ D := by omega
  have hmδnn : (0:ℝ) < (m:ℝ) + δ := by linarith
  have hDpos : (0:ℝ) < D := by
    have : 1 ≤ D := by omega
    exact_mod_cast this
  have hD1 : 1 ≤ D := by omega
  -- (1) (m+δ)D ≥ 1
  have hR1 : (1:ℝ) ≤ (m+δ)*D := by
    have h3 : 1/((m:ℝ)+δ) ≤ (D:ℝ) :=
      le_trans (Nat.le_ceil (1/((m:ℝ)+δ)))
        (by exact_mod_cast (Nat.le_of_succ_le hTA))
    rw [div_le_iff₀ hmδnn] at h3
    linarith
  -- (2) 1/D ≤ ε/8 and (4) 1/((m+δ)D) ≤ ε/8
  have hDinv : ((D:ℝ))⁻¹ ≤ ε/8 := by
    rw [inv_eq_one_div, div_le_iff₀ hDpos]
    have h5 : (8:ℝ)/ε ≤ (D:ℝ) :=
      le_trans (Nat.le_ceil (8/ε)) (by exact_mod_cast Nat.le_of_succ_le hTB)
    rw [div_le_iff₀ hε0] at h5
    linarith
  have hDinv2 : ((m+δ)*D)⁻¹ ≤ ε/8 := by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity : (0:ℝ) < (m+δ)*D)]
    have h5 : (8:ℝ)/(ε*((m:ℝ)+δ)) ≤ (D:ℝ) :=
      le_trans (Nat.le_ceil (8/(ε*((m:ℝ)+δ))))
        (by exact_mod_cast (Nat.le_of_succ_le hTC))
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ε*((m:ℝ)+δ))] at h5
    nlinarith [hmδnn]
  -- (3) box inequality
  have hDbox : (m-δ)*D + 1 ≤ A₀*((m:ℝ)-δ/2)*D := by
    have hA0' : ((m:ℝ) - 3*δ/4) ≤ A₀*((m:ℝ)-δ/2) := by
      have h2 : (m:ℝ) - δ/2 ≠ 0 := by linarith
      have hαm : α * ((m:ℝ)-δ/2) = (m:ℝ)-δ := by rw [hαdef, div_mul_cancel₀ ((m:ℝ) - δ) h2]
      have hhalf : ((α+1)/2) * ((m:ℝ)-δ/2) = (m:ℝ) - 3*δ/4 := by
        have hstep : ((α+1)/2) * ((m:ℝ)-δ/2) = (α*((m:ℝ)-δ/2) + ((m:ℝ)-δ/2))/2 := by ring
        rw [hstep, hαm]
        ring
      calc (m:ℝ) - 3*δ/4 = ((α+1)/2) * ((m:ℝ)-δ/2) := hhalf.symm
        _ ≤ A₀ * ((m:ℝ)-δ/2) := mul_le_mul_of_nonneg_right hA0α (by linarith)
    have h4 : (4:ℝ)/δ ≤ (D:ℝ) :=
      le_trans (Nat.le_ceil (4/δ)) (by exact_mod_cast (Nat.le_of_succ_le hTD))
    rw [div_le_iff₀ hδpos] at h4
    have h6 : A₀*((m:ℝ)-δ/2) ≥ (m:ℝ) - 3*δ/4 := hA0'
    have h8 : (m:ℝ) - δ ≤ (m:ℝ) - 3*δ/4 := by linarith
    have h9 : (m:ℝ) - δ + 1/D ≤ A₀*((m:ℝ)-δ/2) := by
      have h10 : 1/D ≤ δ/4 := by
        rw [div_le_iff₀ hDpos]; nlinarith [h4]
      linarith
    have h11 : ((m:ℝ) - δ + 1/D)*D ≤ A₀*((m:ℝ)-δ/2)*D :=
      mul_le_mul_of_nonneg_right h9 hDpos.le
    have h12 : ((m:ℝ) - δ + 1/D)*D = (m-δ)*D + 1 := by
      have h13 : (1:ℝ)/D*D = 1 := div_mul_cancel₀ 1 hDpos.ne'
      calc ((m:ℝ) - δ + 1/D)*D = ((m:ℝ) - δ)*D + (1/D)*D := by ring
        _ = (m-δ)*D + 1 := by rw [h13]
    rw [h12] at h11
    linarith
  -- (5) 4*Bdd/D ≤ 1/4
  have hDB1 : 4*Bdd/D ≤ 1/4 := by
    have h5 : (16:ℝ)*Bdd ≤ (D:ℝ) := by
      have h6 : (16:ℝ)*Bdd ≤ (Nat.ceil (16*Bdd) : ℝ) := Nat.le_ceil _
      have h7 : (Nat.ceil (16*Bdd) : ℝ) ≤ D := by
        exact_mod_cast (Nat.le_of_succ_le hTE)
      linarith
    rw [div_le_iff₀ hDpos]
    linarith
  -- (6) 32*Bdd*m ≤ ε*D
  have hDB2 : 32*Bdd*(m:ℝ) ≤ ε*D := by
    have h5 : 32*Bdd*(m:ℝ)/ε ≤ (D:ℝ) :=
      le_trans (Nat.le_ceil (32*Bdd*(m:ℝ)/ε))
        (by exact_mod_cast (Nat.le_of_succ_le hTF))
    rw [div_le_iff₀ hε0] at h5
    linarith
  -- (7) 16*Bdd*Ch*(m+δ+1) ≤ ε*D
  have hDB3 : 16*Bdd*Ch*((m:ℝ)+δ+2) ≤ ε*D := by
    have h5 : 16*Bdd*Ch*((m:ℝ)+δ+2)/ε ≤ (D:ℝ) :=
      le_trans (Nat.le_ceil (16*Bdd*Ch*((m:ℝ)+δ+2)/ε))
        (by exact_mod_cast (Nat.le_of_succ_le hTG))
    rw [div_le_iff₀ hε0] at h5
    linarith
  -- (8) 2*Bdd/D ≤ 1/4
  have hDB4 : 2*Bdd/D ≤ 1/4 := by
    have h5 : (8:ℝ)*Bdd ≤ (D:ℝ) := by
      have h6 : (8:ℝ)*Bdd ≤ (Nat.ceil (8*Bdd) : ℝ) := Nat.le_ceil _
      have h7 : (Nat.ceil (8*Bdd) : ℝ) ≤ D := by
        exact_mod_cast (Nat.le_of_succ_le hTH)
      linarith
    rw [div_le_iff₀ hDpos]
    linarith
  -- (9) counting hypotheses
  have hbig1 : 4 * (((D:ℝ))⁻¹ + ((d:ℝ))⁻¹) ≤ ε := by
    have h1 : 1/D ≤ ε/8 := by
      rw [div_le_iff₀ hDpos]
      have h5 : (8:ℝ)/ε ≤ (D:ℝ) :=
        le_trans (Nat.le_ceil (8/ε)) (by exact_mod_cast Nat.le_of_succ_le hTB)
      rw [div_le_iff₀ hε0] at h5
      nlinarith [h5]
    have h2 : 1/d ≤ ε/8 := by
      rw [div_le_iff₀ hdR]; nlinarith [hd8]
    rw [inv_eq_one_div, inv_eq_one_div]
    linarith
  have hbig2 : 4 * (((m+δ)*D)⁻¹ + ((d:ℝ))⁻¹) ≤ ε := by
    have h1 : 1/((m+δ)*D) ≤ ε/8 := by
      rw [inv_eq_one_div] at hDinv2
      exact hDinv2
    have h2 : 1/d ≤ ε/8 := by
      rw [div_le_iff₀ hdR]; nlinarith [hd8]
    rw [inv_eq_one_div, inv_eq_one_div]
    linarith
  -- ═══ the row and column counts
  have hVc : ((m:ℝ) - δ/2)^d ≤ ((balSet d m).card : ℝ) := by
    rw [balSet_eq]; exact hd₁ d hd1 hmd
  have hLc : (D:ℝ)^d * (1 - ρ) ≤ ((lowSet d D ε).card : ℝ) := by
    have h := lattice_lowdisc_card (d := d) (D := D) hdpos hD1 hε0 hbig1
    rw [hρdef]
    exact h
  have hBc : ((badSet d D ε δ m).card : ℝ) ≤
      (Nat.floor ((m+δ)*D) : ℝ)^d * ρ +
        (((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d) := by
    have h := card_bad_real (d := d) hdpos (R := (m+δ)*D) hR1 hε0 hbig2
    rw [hρdef]
    simpa only [badSet] using h  -- ═══ the column count
  set V : ℝ := ((m:ℝ) - δ/2)^d * (D:ℝ)^d with hVdef
  have hVnn : 0 ≤ V := by rw [hVdef]; positivity
  have hNc : V * (1 - ρ) ≤ (Fintype.card (ColIdx d D ε m) : ℝ) := by
    rw [card_colIdx, Nat.cast_mul]
    have h : ((m:ℝ)-δ/2)^d * ((D:ℝ)^d * (1-ρ)) ≤
        ((balSet d m).card : ℝ) * ((lowSet d D ε).card : ℝ) :=
      mul_le_mul hVc hLc (by
        have h1 : (0:ℝ) ≤ (D:ℝ)^d * (1-ρ) := by nlinarith [hρ1', pow_nonneg hDpos.le d]
        exact h1) (by positivity)
    have h2 : ((m:ℝ)-δ/2)^d * ((D:ℝ)^d * (1-ρ)) = V * (1-ρ) := by rw [hVdef]; ring
    rw [← h2]
    exact h
  have hVle : V ≤ 2 * (Fintype.card (ColIdx d D ε m) : ℝ) := by
    have h2 : V * (1/2) ≤ V * (1 - ρ) := by
      apply mul_le_mul_of_nonneg_left _ hVnn; linarith
    have h4 : V * (1/2) ≤ (Fintype.card (ColIdx d D ε m) : ℝ) := le_trans h2 hNc
    have h5 : V * (1/2) = V/2 := by ring
    linarith [h4, h5]
  -- ═══ the row count
  have hboxb : ((Nat.floor ((m-δ)*D) + 1 : ℕ) : ℝ)^d ≤ A₀^d * V := by
    rw [hVdef]
    exact floor_box_pow_le hA0nn (by linarith) hDbox
  have hbadb : (Nat.floor ((m+δ)*D) : ℝ)^d * ρ ≤ A₀^d * V := by
    rw [hVdef]
    have hρd : ρ ≤ (Real.exp (-(ε/2)^4/200))^d := by
      rw [← Real.exp_nat_mul]
      convert hρ2' using 2
      ring
    have hμle : ((m:ℝ)+δ)/((m:ℝ)-δ/2) * Real.exp (-(ε/2)^4/200) ≤ A₀ := by
      simpa only [hμdef] using hA0μ
    exact floor_bad_pow_le hρnn hδpos.le hρd hμle hA0nn (by linarith)
  have hbdyb : ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d ≤
      (Bdd/D) * V := by
    have h1 : ((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d ≤
        (d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1) :=
      floor_sub_pow_le hm (by linarith) (by linarith) hDpos hR1
    have h2 : ((d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) / ((m:ℝ)-δ/2)^d / D) *
        (((m:ℝ)-δ/2)^d * (D:ℝ)^d) =
        (d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) * (D:ℝ)^(d-1) :=
      bdd_mul_eq hdpos (by linarith) hDpos
    have h3 : (Bdd/D) * V =
        ((d:ℝ) * 2^(d-1) * ((m:ℝ)+δ+1)^(d-1) / ((m:ℝ)-δ/2)^d / D) *
          (((m:ℝ)-δ/2)^d * (D:ℝ)^d) := by
      rw [hBdddef, hVdef]
    rw [h3, h2]
    exact h1
  have hMc : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤ (2*A₀^d + Bdd/D) * V := by
    rw [card_rowIdx]
    have hrow := card_rowSet_le (d := d) (D := D) (ε := ε) (δ := δ) (m := m)
      (by linarith : δ ≤ m)
    have h1 : ((rowSet d D ε δ m).card : ℝ) ≤
        ((Nat.floor ((m-δ)*D) + 1 : ℕ) : ℝ)^d + ((badSet d D ε δ m).card : ℝ) := by
      push_cast
      exact_mod_cast hrow
    have h2 : ((badSet d D ε δ m).card : ℝ) ≤
        (Nat.floor ((m+δ)*D) : ℝ)^d * ρ +
          (((Nat.floor ((m+δ)*D) : ℕ) + 1 : ℝ)^d - (Nat.floor ((m+δ)*D) : ℝ)^d) := hBc
    linarith [h1, h2, hboxb, hbadb, hbdyb]
  -- ═══ the ratio bound and the Siegel lemma
  have hκN : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
      (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := by
    have h1 : (2*A₀^d + Bdd/D) * V ≤ (2*A₀^d + Bdd/D) * (2 * (Fintype.card (ColIdx d D ε m) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hVle
      have : (0:ℝ) ≤ A₀^d := pow_nonneg hA0nn _
      positivity
    calc (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤ (2*A₀^d + Bdd/D) * V := hMc
      _ ≤ (2*A₀^d + Bdd/D) * (2 * (Fintype.card (ColIdx d D ε m) : ℝ)) := h1
      _ = (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := by ring
  have hAd : A₀^d * 16 ≤ ε/4 := by
    have h1 : (16:ℝ) ≤ Kd := by
      rw [hKddef]
      have h3 : (0:ℝ) ≤ Ch * ((m:ℝ) + δ + 1) := mul_nonneg hChnn (by linarith)
      linarith
    have h2 : A₀^d * 16 ≤ A₀^d * Kd := mul_le_mul_of_nonneg_left h1 (pow_nonneg hA0nn _)
    linarith [hKd, h2]
  have hA0d_le : A₀^d ≤ 1/64 := by
    have h1 : (0:ℝ) < ε := hε0
    nlinarith [hAd, hA0nn, pow_nonneg hA0nn d]
  have hDB4' : 2*(Bdd/D) ≤ 1/4 := by
    have h := hDB4
    rw [show 2*Bdd/D = 2*(Bdd/D) by ring] at h
    exact h
  have hκhalf : 4*A₀^d + 2*(Bdd/D) ≤ 1/2 := by linarith [hA0d_le, hDB4']
  have hNpos : 0 < Fintype.card (ColIdx d D ε m) := by
    have h := hNc
    have h1 : (0:ℝ) < V := by
      rw [hVdef]
      exact mul_pos (pow_pos (by linarith : (0:ℝ) < (m:ℝ) - δ/2) d) (pow_pos hDpos d)
    have h2 : (0:ℝ) < V * (1-ρ) := by
      have h3 : (0:ℝ) < 1 - ρ := by linarith
      exact mul_pos h1 h3
    have : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) := lt_of_lt_of_le h2 h
    exact_mod_cast this
  have hMD : Fintype.card (RowIdx d D ε δ m) < Fintype.card (ColIdx d D ε m) := by
    have h := hκN
    have h1 : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) := by exact_mod_cast hNpos
    have h2 : (Fintype.card (RowIdx d D ε δ m) : ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) := by
      have h3 : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
          (1/2) * (Fintype.card (ColIdx d D ε m) : ℝ) :=
        calc _ ≤ (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := h
          _ ≤ (1/2) * (Fintype.card (ColIdx d D ε m) : ℝ) :=
              mul_le_mul_of_nonneg_right hκhalf h1.le
      linarith
    exact_mod_cast h2
  have hMpos : 0 < Fintype.card (RowIdx d D ε δ m) := by
    refine Fintype.card_pos_iff.mpr ?_
    refine ⟨⟨fun _ => 0, ?_⟩⟩
    rw [mem_rowSet]
    constructor
    · intro j
      have : (0:ℝ) ≤ (m+δ)*D := by positivity
      have := Nat.le_ceil ((m+δ)*D)
      omega
    · left
      intro j
      have : (0:ℝ) ≤ (m-δ)*D := by
        have : (0:ℝ) ≤ (m:ℝ) - δ := by linarith
        positivity
      simpa using this
  set Amat : Matrix (RowIdx d D ε δ m) (ColIdx d D ε m) ℤ := fun r c => matEntry C r.1 c.1 with hAmat
  obtain ⟨y, hy0, hyker, hynorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le Amat hMD hMpos  -- ═══ the height bound for the matrix
  have hAm : ‖Amat‖ ≤ Real.exp (Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) := by
    rw [Matrix.norm_le_iff (Real.exp_nonneg _)]
    intro r c
    have hrow : r.1 ∈ rowSet d D ε δ m := r.2
    rw [mem_rowSet] at hrow
    obtain ⟨hbase, _⟩ := hrow
    have h := hCh d (Nat.ceil ((m+δ)*D)) r.1 (fun s => hbase s) c.1
    rw [hAmat]
    simpa only [Int.norm_eq_abs] using h
  -- ═══ the size of the basis
  have hNle : (Fintype.card (ColIdx d D ε m) : ℝ) ≤ ((m:ℝ) * ((D:ℝ)+1))^d := by
    rw [card_colIdx, Nat.cast_mul]
    have h1 : ((balSet d m).card : ℝ) ≤ (m:ℝ)^d := by
      have h := Finset.card_le_univ (balSet d m)
      simp only [Fintype.card_fun, Fintype.card_fin] at h
      exact_mod_cast h
    have h2 : ((lowSet d D ε).card : ℝ) ≤ ((D:ℝ)+1)^d := by
      have h2'' : ((Fintype.piFinset (fun _ : Fin d => Finset.range (D+1))).filter
          (fun k : Fin d → ℕ => disc (fun j => (k j : ℝ)/(D:ℝ)) < ε)).card ≤ (D+1)^d := by
        refine le_trans (Finset.card_filter_le _ _) ?_
        rw [Fintype.card_piFinset]
        simp
      simp only [lowSet]
      exact_mod_cast h2''
    calc ((balSet d m).card : ℝ) * ((lowSet d D ε).card : ℝ) ≤ (m:ℝ)^d * ((D:ℝ)+1)^d :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((m:ℝ) * ((D:ℝ)+1))^d := by rw [mul_pow]
  -- ═══ the base is bounded by an exponential
  have hbase : (Fintype.card (ColIdx d D ε m) : ℝ) * max 1 ‖Amat‖ ≤
      Real.exp ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
        Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) := by
    have hmax : max 1 ‖Amat‖ ≤
        Real.exp (Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) := by
      rw [max_le_iff]
      refine ⟨?_, hAm⟩
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    calc (Fintype.card (ColIdx d D ε m) : ℝ) * max 1 ‖Amat‖
        ≤ ((m:ℝ) * ((D:ℝ)+1))^d *
            Real.exp (Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) :=
          mul_le_mul hNle hmax (by positivity) (by positivity)
      _ = Real.exp ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
            Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) :=
          exp_pow_mul_exp ((m:ℝ) * ((D:ℝ)+1))
            (Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) d (by positivity)
  -- ═══ the exponent bound
  have hexp_le : (Fintype.card (RowIdx d D ε δ m) : ℝ) /
      ((Fintype.card (ColIdx d D ε m) : ℝ) - Fintype.card (RowIdx d D ε δ m)) ≤
      2 * (4*A₀^d + 2*(Bdd/D)) := by
    have h1 : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) := by exact_mod_cast hNpos
    have h3 : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
        (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := hκN
    have h4 : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
        (1/2) * (Fintype.card (ColIdx d D ε m) : ℝ) :=
      calc _ ≤ (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := h3
        _ ≤ (1/2) * (Fintype.card (ColIdx d D ε m) : ℝ) :=
            mul_le_mul_of_nonneg_right hκhalf h1.le
    have hκnn : (0:ℝ) ≤ 4*A₀^d + 2*(Bdd/D) := by
      have h5 : (0:ℝ) ≤ A₀^d := pow_nonneg hA0nn d
      have h6 : (0:ℝ) ≤ Bdd/D := div_nonneg hBddnn hDpos.le
      linarith
    have hNM : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) -
        Fintype.card (RowIdx d D ε δ m) := by
      refine sub_pos.mpr ?_
      linarith [h1, h4]
    rw [div_le_iff₀ hNM]
    have h7 : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
        (4*A₀^d + 2*(Bdd/D)) * (2 * ((Fintype.card (ColIdx d D ε m) : ℝ) -
          Fintype.card (RowIdx d D ε δ m))) := by
      have h8 : (Fintype.card (ColIdx d D ε m) : ℝ) ≤
          2 * ((Fintype.card (ColIdx d D ε m) : ℝ) - Fintype.card (RowIdx d D ε δ m)) := by
        linarith [h4]
      calc (Fintype.card (RowIdx d D ε δ m) : ℝ)
          ≤ (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := h3
        _ ≤ (4*A₀^d + 2*(Bdd/D)) *
              (2 * ((Fintype.card (ColIdx d D ε m) : ℝ) -
                Fintype.card (RowIdx d D ε δ m))) :=
            mul_le_mul_of_nonneg_left h8 hκnn
    have h9 : (4*A₀^d + 2*(Bdd/D)) * (2 * ((Fintype.card (ColIdx d D ε m) : ℝ) -
        Fintype.card (RowIdx d D ε δ m))) =
        2 * (4*A₀^d + 2*(Bdd/D)) * ((Fintype.card (ColIdx d D ε m) : ℝ) -
          Fintype.card (RowIdx d D ε δ m)) := by ring
    rw [h9] at h7
    exact h7
  -- ═══ the final norm bound
  have harith : 2 * (4*A₀^d + 2*(Bdd/D)) *
      ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
        Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) ≤ ε * d * D := by
    refine final_arith hdpos hm hε0 hChnn hA0nn hBddnn hδpos.le hδm2' hD1 ?_ ?_ ?_ ?_
    · have hKd' := hKd
      have h16 : (16:ℝ) * (m:ℝ) ≤ Kd := by
        rw [hKddef]
        have h3 : (0:ℝ) ≤ Ch * ((m:ℝ) + δ + 2) := mul_nonneg hChnn (by linarith)
        linarith
      calc (16:ℝ) * (m:ℝ) * A₀^d = A₀^d * (16*(m:ℝ)) := by ring
        _ ≤ A₀^d * Kd := mul_le_mul_of_nonneg_left h16 (pow_nonneg hA0nn d)
        _ ≤ ε/4 := hKd'
    · have hKd' := hKd
      have h18 : 8*Ch*((m:ℝ)+δ+2) ≤ Kd := by
        rw [hKddef]
        have h3 : (0:ℝ) ≤ 16*(m:ℝ) := by positivity
        linarith
      calc 8*Ch*((m:ℝ)+δ+2) * A₀^d = A₀^d * (8*Ch*((m:ℝ)+δ+2)) := by ring
        _ ≤ A₀^d * Kd := mul_le_mul_of_nonneg_left h18 (pow_nonneg hA0nn d)
        _ ≤ ε/4 := hKd'
    · exact hDB2
    · exact hDB3
  have hNM' : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) -
      Fintype.card (RowIdx d D ε δ m) := by
    have h1 : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) := by exact_mod_cast hNpos
    have h3 : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
        (4*A₀^d + 2*(Bdd/D)) * (Fintype.card (ColIdx d D ε m) : ℝ) := hκN
    have h4 : (Fintype.card (RowIdx d D ε δ m) : ℝ) ≤
        (1/2) * (Fintype.card (ColIdx d D ε m) : ℝ) :=
      le_trans h3 (mul_le_mul_of_nonneg_right hκhalf h1.le)
    linarith
  have hbase0 : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) * max 1 ‖Amat‖ := by
    have h1 : (0:ℝ) < (Fintype.card (ColIdx d D ε m) : ℝ) := by exact_mod_cast hNpos
    exact mul_pos h1 (by positivity)
  have hEx : (0:ℝ) ≤ (d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
      Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ)) := by
    have hmD1 : (1:ℝ) ≤ (m:ℝ) * ((D:ℝ)+1) := by
      have h2 : (1:ℝ) ≤ (D:ℝ) + 1 := by linarith
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (m:ℝ) * ((D:ℝ)+1) := mul_le_mul hm1R h2 (by norm_num) (by positivity)
    have h1 : (0:ℝ) ≤ (d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) :=
      mul_nonneg (by positivity) (Real.log_nonneg hmD1)
    have h2 : (0:ℝ) ≤ Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ)) :=
      mul_nonneg hChnn (by positivity)
    exact add_nonneg h1 h2
  have hyb : ‖y‖ ≤ Real.exp (ε * d * D) := by
    have hE1 : ((Fintype.card (ColIdx d D ε m) : ℝ) * max 1 ‖Amat‖) ^
        ((Fintype.card (RowIdx d D ε δ m) : ℝ) /
          ((Fintype.card (ColIdx d D ε m) : ℝ) - Fintype.card (RowIdx d D ε δ m))) ≤
        (Real.exp ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
          Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ)))) ^
          ((Fintype.card (RowIdx d D ε δ m) : ℝ) /
            ((Fintype.card (ColIdx d D ε m) : ℝ) - Fintype.card (RowIdx d D ε δ m))) :=
      Real.rpow_le_rpow hbase0.le hbase (div_nonneg (Nat.cast_nonneg _) hNM'.le)
    have hE2 : (Real.exp ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
          Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ)))) ^
          ((Fintype.card (RowIdx d D ε δ m) : ℝ) /
            ((Fintype.card (ColIdx d D ε m) : ℝ) - Fintype.card (RowIdx d D ε δ m))) ≤
        (Real.exp ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
          Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ)))) ^ (2 * (4*A₀^d + 2*(Bdd/D))) :=
      Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hEx) hexp_le
    have hE3 : (Real.exp ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
          Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ)))) ^ (2 * (4*A₀^d + 2*(Bdd/D))) =
        Real.exp (((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
          Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) * (2 * (4*A₀^d + 2*(Bdd/D)))) := by
      rw [Real.exp_mul]
    have hE4 : ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
        Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) * (2 * (4*A₀^d + 2*(Bdd/D))) ≤
        ε * d * D := by
      have := harith
      nlinarith [this]
    exact le_trans hynorm (le_trans hE1 (le_trans hE2 (le_trans (le_of_eq hE3)
      (Real.exp_le_exp.mpr hE4))))
  have hycoord : ∀ p : ColIdx d D ε m, |((y p : ℤ) : ℝ)| ≤ Real.exp (ε * d * D) := by
    intro p
    have h1 := norm_le_pi_norm y p
    have h2 : ‖y p‖ ≤ Real.exp (ε * d * D) := le_trans h1 hyb
    rwa [Int.norm_eq_abs] at h2
  -- ═══ the equations solved by `y`
  have hrowQ : ∀ r : RowIdx d D ε δ m,
      ∑ c : ColIdx d D ε m, (y c : ℚ) * sysCoeffFun f r.1 c.1 = 0 := by
    intro r
    have hker : (∑ c : ColIdx d D ε m, Amat r c * y c) = 0 := by
      have h1 := congr_fun hyker r
      simpa [hAmat, Matrix.mulVec, dotProduct] using h1
    have h2 : (∑ c : ColIdx d D ε m, ((Amat r c : ℤ) : ℚ) * (y c : ℚ)) = 0 := by
      have h3 := congrArg (fun z : ℤ => (z : ℚ)) hker
      push_cast at h3 ⊢
      simpa using h3
    have h4 : (∑ c : ColIdx d D ε m,
        (((rowFac C r.1 : ℕ) : ℚ) * sysCoeffFun f r.1 c.1) * (y c : ℚ)) = 0 := by
      refine Eq.trans ?_ h2
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hAmat, matEntry_spec C r.1 c.1]
      rfl
    have h5 : (((rowFac C r.1 : ℕ) : ℚ) *
        (∑ c : ColIdx d D ε m, sysCoeffFun f r.1 c.1 * (y c : ℚ))) = 0 := by
      rw [Finset.mul_sum]
      refine Eq.trans ?_ h4
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    have h6 : (((rowFac C r.1 : ℕ) : ℚ)) ≠ 0 := by
      have h7 : (0:ℚ) < ∏ s : Fin d, ((C.Nc * clearFac C (r.1 s) : ℕ) : ℚ) := by
        refine Finset.prod_pos (fun s _ => ?_)
        have h8 : 0 < C.Nc * clearFac C (r.1 s) := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one C.hNc) (by
          rw [clearFac]
          exact Nat.mul_pos (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one C.hKmax) (pow_pos (Nat.lcmUpto_pos _) _))
            (Finset.prod_pos (fun j _ => Nat.lcmUpto_pos _)))
        exact_mod_cast h8
      rw [rowFac, Nat.cast_prod]
      exact ne_of_gt h7
    have h9 : (∑ c : ColIdx d D ε m, sysCoeffFun f r.1 c.1 * (y c : ℚ)) = 0 :=
      (mul_eq_zero.mp h5).resolve_left h6
    rw [← h9]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  -- ═══ the template
  refine ⟨mkQ y, ?_, ?_, ?_, ?_⟩
  · -- the auxiliary template
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      exact balanced_mkQ y hi
    · intro i k hk
      have hk' := supported_mkQ y i k hk
      rw [mem_lowSet] at hk'
      exact hk'
    · intro i k
      by_cases hi : i ∈ balSet d m
      · by_cases hk : Finsupp.equivFunOnFinite k ∈ lowSet d D ε
        · exact ⟨y ⟨(i, Finsupp.equivFunOnFinite k), hi, hk⟩,
            by rw [coeff_mkQ y hi]; simp [hk]⟩
        · exact ⟨0, by rw [coeff_mkQ y hi]; simp [hk]⟩
      · exact ⟨0, coeff_mkQ_zero y hi k⟩
    · intro i k
      by_cases hi : i ∈ balSet d m
      · by_cases hk : Finsupp.equivFunOnFinite k ∈ lowSet d D ε
        · rw [coeff_mkQ y hi]
          simp only [dif_pos hk]
          exact hycoord ⟨(i, Finsupp.equivFunOnFinite k), hi, hk⟩
        · rw [coeff_mkQ y hi, dif_neg hk]
          simp only [Rat.cast_zero, abs_zero]
          exact Real.exp_nonneg _
      · rw [coeff_mkQ_zero y hi k]
        simp only [Rat.cast_zero, abs_zero]
        exact Real.exp_nonneg _
  · -- the auxiliary series is nonzero
    intro hzero
    apply hy0
    have h1 : mkQ y = 0 := auxSeries_injective f hpi (mkQ y) hzero
    funext p
    have h2 := congr_fun h1 p.1.1
    have h3 : (mkQ y p.1.1).coeff (Finsupp.equivFunOnFinite.symm p.1.2) = 0 := by
      rw [h2]; simp
    have h5 : Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm p.1.2) = p.1.2 :=
      Finsupp.equivFunOnFinite.apply_symm_apply p.1.2
    rw [coeff_mkQ y p.2.1, h5, dif_pos p.2.2] at h3
    have h4 : (y p : ℚ) = 0 := h3
    exact_mod_cast h4
  · -- vanishing on the small box
    intro n hn
    have hmem : (fun j => n j) ∈ rowSet d D ε δ m := by
      rw [mem_rowSet]
      refine ⟨fun j => ?_, Or.inl hn⟩
      have h := hn j
      have h3 : ((m:ℝ) - δ) * (D:ℝ) ≤ ((m:ℝ) + δ) * (D:ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hδpos]) hDpos.le
      have h2 : (n j : ℝ) ≤ (Nat.ceil ((m+δ)*D) : ℝ) :=
        le_trans h (le_trans h3 (Nat.le_ceil _))
      exact_mod_cast h2
    have h := hrowQ ⟨fun j => n j, hmem⟩
    rw [coeff_auxSeries_mkQ f D ε y n]
    simpa only [sysCoeff] using h
  · -- vanishing off the low-discrepancy set
    intro n hn hdisc
    have hmem : (fun j => n j) ∈ rowSet d D ε δ m := by
      rw [mem_rowSet]
      refine ⟨fun j => ?_, Or.inr ⟨hn, ?_⟩⟩
      · have h := hn j
        have h2 : (n j : ℝ) ≤ (Nat.ceil ((m+δ)*D) : ℝ) := le_trans h (Nat.le_ceil _)
        exact_mod_cast h2
      · simpa using hdisc
    have h := hrowQ ⟨fun j => n j, hmem⟩
    rw [coeff_auxSeries_mkQ f D ε y n]
    simpa only [sysCoeff] using h

end Work.Holonomy3
