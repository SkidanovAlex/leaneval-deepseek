import Mathlib
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.iwP_element_le
import Submission.Work.KMTAreas.iwQ0_le

namespace Work.KMTAreas.A7

open scoped BigOperators
open Work.Analysis.IonescuWainger

/-
# A `ρ`-uniform cardinality bound for the Ionescu--Wainger arithmetic frequency set

Krause--Mirek--Tao, Appendix A: the IW frequency set `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` is a finite
set of frequencies "of height at most `2^l`" which is sensitive to `ρ` (larger `ρ` = smaller set).
The existing result `Work.Analysis.IonescuWainger.iw_height_card_le` gives a `ρ`-dependent bound
`#(ℚ/ℤ)_{≤l} ≤ C(ρ) · 2^{2^{ρl}}` with `C(ρ) = 2^{2·iwC0 ρ} → ∞` as `ρ → 0⁺`. The present
statement is the *uniform* form needed by `Work.KMTAreas.A7.KmtKernelL1Uniform`: for each fixed
`l` there is a finite bound valid for all `ρ ∈ (0,1]`.

The proof mirrors the private lemmas of
`Submission/Work/Analysis/IonescuWainger/iw_height_card_le.lean`, but makes every constant
explicit and uniform in `ρ`:

* the cardinality is at most `Σ_{q ∈ P_{≤l}} q` (union bound over the `q`-torsion subgroups);
* if `l ≤ iwC0 ρ` then `iwP ρ l = Finset.Icc 1 (2^l)`, so `#(ℚ/ℤ)_{≤l} ≤ (2^l)² = 2^{2l}`;
* if `iwC0 ρ < l` then `iwC0 ρ ≥ ⌈10/ρ⌉₊` forces `1/ρ < l/10`, hence `D_ρ < l/5 + 1 ≤ l/4`; so
  every `q ∈ P_{≤l}` is `q = Q · w` with `log₂ Q ≤ 2 l 2^l` and `log₂ w ≤ l²2^l/2`, giving
  `q ≤ 2^{l·(2l+l²)} ≤ 2^{4^l}`, whence `#(ℚ/ℤ)_{≤l} ≤ (2^{4^l})²`.

So `B l := (2^{2^{4l}})² + 1` works.
-/

/-! ## Elementary arithmetic -/

private lemma iwC0_ge_100 (ρ : ℝ) : 100 ≤ iwC0 ρ := by
  rw [iwC0]; omega

private lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- `2^{(n:ℝ)} = (2^n : ℕ)` as reals, with the cast on the right made explicit. -/
private lemma two_rpow_nat_cast (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ)) = (((2 : ℕ) ^ n : ℕ) : ℝ) := by
  rw [Nat.cast_pow]
  exact Real.rpow_natCast (2 : ℝ) n

/-- `(2^{2^{4l}} : ℕ)` viewed as a real is `2^{2^{4l}}`. -/
private lemma two_pow_two_pow_four_cast (l : ℕ) :
    (((2 : ℕ) ^ (2 ^ (4 * l)) : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (4 * l)) := by
  rw [Nat.cast_pow]
  norm_num

private lemma two_mul_le_two_pow_self (l : ℕ) : 2 * l ≤ 2 ^ (2 * l) :=
  le_of_lt (Nat.lt_two_pow_self (n := 2 * l))

private lemma sq_le_two_pow_two_mul (l : ℕ) : l ^ 2 ≤ 2 ^ (2 * l) := by
  have h : l ^ 2 < (2 ^ l) ^ 2 :=
    Nat.pow_lt_pow_left (Nat.lt_two_pow_self (n := l)) (by norm_num : (2 : ℕ) ≠ 0)
  have h2 : (2 ^ l) ^ 2 = 2 ^ (2 * l) := by rw [← pow_mul, Nat.mul_comm]
  exact le_of_lt (h2 ▸ h)

private lemma two_mul_le_two_rpow (l : ℕ) : 2 * (l : ℝ) ≤ (2 : ℝ) ^ (2 * (l : ℝ)) := by
  have h := two_mul_le_two_pow_self l
  have h2 : (((2 ^ (2 * l) : ℕ)) : ℝ) = (2 : ℝ) ^ (2 * (l : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  rw [← h2]
  exact_mod_cast h

private lemma sq_le_two_rpow_two_mul (l : ℕ) : (l : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (l : ℝ)) := by
  have h := sq_le_two_pow_two_mul l
  have h2 : (((2 ^ (2 * l) : ℕ)) : ℝ) = (2 : ℝ) ^ (2 * (l : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  rw [← h2]
  exact_mod_cast h

private lemma two_mul_two_rpow (a : ℝ) : 2 * (2 : ℝ) ^ a = (2 : ℝ) ^ (1 + a) := by
  calc 2 * (2 : ℝ) ^ a = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ a := by rw [Real.rpow_one]
    _ = (2 : ℝ) ^ (1 + a) := by rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]

private lemma mul_exp_le (l : ℕ) (hl : 1 ≤ l) :
    (2 : ℝ) ^ (l : ℝ) * (2 * (l : ℝ) + (l : ℝ) ^ 2) ≤ (2 : ℝ) ^ (4 * (l : ℝ)) := by
  have f1 : 2 * (l : ℝ) ≤ (2 : ℝ) ^ (2 * (l : ℝ)) := two_mul_le_two_rpow l
  have f2 : (l : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (l : ℝ)) := sq_le_two_rpow_two_mul l
  have hY : 2 * (l : ℝ) + (l : ℝ) ^ 2 ≤ 2 * (2 : ℝ) ^ (2 * (l : ℝ)) := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ (l : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (2 : ℝ) ^ (l : ℝ) * (2 * (l : ℝ) + (l : ℝ) ^ 2)
      ≤ (2 : ℝ) ^ (l : ℝ) * (2 * (2 : ℝ) ^ (2 * (l : ℝ))) :=
    mul_le_mul_of_nonneg_left hY hT.le
  have h2 : (2 : ℝ) ^ (l : ℝ) * (2 * (2 : ℝ) ^ (2 * (l : ℝ))) = (2 : ℝ) ^ (3 * (l : ℝ) + 1) := by
    calc (2 : ℝ) ^ (l : ℝ) * (2 * (2 : ℝ) ^ (2 * (l : ℝ)))
        = 2 * ((2 : ℝ) ^ (l : ℝ) * (2 : ℝ) ^ (2 * (l : ℝ))) := by ring
      _ = 2 * (2 : ℝ) ^ ((l : ℝ) + 2 * (l : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      _ = (2 : ℝ) ^ (1 + ((l : ℝ) + 2 * (l : ℝ))) := two_mul_two_rpow _
      _ = (2 : ℝ) ^ (3 * (l : ℝ) + 1) := by congr 1; ring
  have h3 : (2 : ℝ) ^ (3 * (l : ℝ) + 1) ≤ (2 : ℝ) ^ (4 * (l : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hl' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  rw [h2] at h1
  linarith

/-! ## Bounds on `D_ρ = iwD ρ` in the regime `l > iwC0 ρ` -/

private lemma one_div_rho_lt_of_iwC0_lt {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (h : iwC0 ρ < l) :
    1 / ρ < (l : ℝ) / 10 := by
  have hceil : ⌈10 / ρ⌉₊ ≤ iwC0 ρ := by rw [iwC0]; omega
  have h1 : (10 : ℝ) / ρ ≤ ((⌈10 / ρ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈10 / ρ⌉₊ : ℕ) : ℝ) ≤ (iwC0 ρ : ℝ) := by exact_mod_cast hceil
  have h3 : (iwC0 ρ : ℝ) < (l : ℝ) := by exact_mod_cast h
  have h4 : (10 : ℝ) / ρ < (l : ℝ) := by linarith
  rw [div_lt_div_iff₀ hρ (by norm_num : (0 : ℝ) < 10)]
  rw [div_lt_iff₀ hρ] at h4
  linarith

private lemma iwD_le_of_iwC0_lt {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (h : iwC0 ρ < l) :
    (iwD ρ : ℝ) ≤ (l : ℝ) / 5 + 1 := by
  have h5 := one_div_rho_lt_of_iwC0_lt hρ h
  have hD : ((⌊2 / ρ⌋₊ : ℕ) : ℝ) ≤ 2 / ρ := Nat.floor_le (by positivity)
  have h2ρ : (2 : ℝ) / ρ < (l : ℝ) / 5 := by
    have ha : (2 : ℝ) / ρ = 2 * (1 / ρ) := by ring
    have hb : (l : ℝ) / 5 = 2 * ((l : ℝ) / 10) := by ring
    rw [ha, hb]; linarith
  rw [iwD, Nat.cast_add, Nat.cast_one]
  linarith

/-! ## Element bound for `W_{≤l}` -/

private lemma iwW_le_pow (ρ : ℝ) (l : ℕ) {w : ℕ} (hw : w ∈ iwW ρ l) :
    w ≤ (2 ^ l) ^ (iwD ρ * 2 ^ l) := by
  rw [mem_iwW] at hw
  obtain ⟨hdvd, -⟩ := hw
  have hsub : iwPrimeRange ρ l ⊆ Finset.Icc 1 (2 ^ l) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hp2.one_lt.le, (Finset.mem_Icc.mp hp1).2⟩
  have hcard : (iwPrimeRange ρ l).card ≤ 2 ^ l := by
    calc (iwPrimeRange ρ l).card ≤ (Finset.Icc 1 (2 ^ l)).card := Finset.card_le_card hsub
      _ = 2 ^ l := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hprod_le : iwProd ρ l ≤ (2 ^ l) ^ (iwD ρ * 2 ^ l) := by
    rw [iwProd]
    calc ∏ p ∈ iwPrimeRange ρ l, p ^ iwD ρ
        ≤ ∏ _p ∈ iwPrimeRange ρ l, (2 ^ l) ^ iwD ρ := by
          refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) fun p hp => ?_
          exact Nat.pow_le_pow_left (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 _
      _ = ((2 ^ l) ^ iwD ρ) ^ (iwPrimeRange ρ l).card := Finset.prod_const _
      _ ≤ ((2 ^ l) ^ iwD ρ) ^ (2 ^ l) := Nat.pow_le_pow_right (by positivity) hcard
      _ = (2 ^ l) ^ (iwD ρ * 2 ^ l) := by rw [pow_mul]
  exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (iwProd_ne_zero ρ l)) hdvd) hprod_le

/-- Uniform (in `ρ`) element bound for `W_{≤l}` in the regime `l > iwC0 ρ`. -/
private lemma iwW_bound {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (h : iwC0 ρ < l) {w : ℕ}
    (hw : w ∈ iwW ρ l) :
    (w : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2) := by
  have hl20 : (20 : ℝ) ≤ (l : ℝ) := by
    have : 20 ≤ l := by have := iwC0_ge_100 ρ; omega
    exact_mod_cast this
  have hD := iwD_le_of_iwC0_lt hρ h
  have hD4 : (iwD ρ : ℝ) ≤ (l : ℝ) / 4 := by linarith
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  have hwle := iwW_le_pow ρ l hw
  have hcast : (w : ℝ) ≤ (((2 ^ l : ℕ)) : ℝ) ^ (iwD ρ * 2 ^ l) := by exact_mod_cast hwle
  have hbase : (((2 ^ l : ℕ)) : ℝ) = (2 : ℝ) ^ (l : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    norm_num
  rw [hbase] at hcast
  have hstep : (w : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ) * (((iwD ρ * 2 ^ l : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast] at hcast
    calc (w : ℝ) ≤ ((2 : ℝ) ^ (l : ℝ)) ^ (((iwD ρ * 2 ^ l : ℕ)) : ℝ) := hcast
      _ = (2 : ℝ) ^ ((l : ℝ) * (((iwD ρ * 2 ^ l : ℕ)) : ℝ)) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
  have hdex : (((iwD ρ * 2 ^ l : ℕ)) : ℝ) = (iwD ρ : ℝ) * (2 : ℝ) ^ (l : ℝ) := by
    push_cast
    rw [← Real.rpow_natCast]
  calc (w : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ) * (((iwD ρ * 2 ^ l : ℕ)) : ℝ)) := hstep
    _ = (2 : ℝ) ^ ((l : ℝ) * ((iwD ρ : ℝ) * (2 : ℝ) ^ (l : ℝ))) := by rw [hdex]
    _ ≤ (2 : ℝ) ^ ((l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        have hT := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (l : ℝ)
        have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
        have hs1 : (l : ℝ) * ((iwD ρ : ℝ) * (2 : ℝ) ^ (l : ℝ))
            ≤ (l : ℝ) * (((l : ℝ) / 4) * (2 : ℝ) ^ (l : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD4 hT.le) hl0.le
        have hs2 : (l : ℝ) * (((l : ℝ) / 4) * (2 : ℝ) ^ (l : ℝ))
            ≤ (l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2 := by
          have hnn : (0 : ℝ) ≤ (l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) := by positivity
          nlinarith [hT, hl0]
        linarith

/-- Uniform (in `ρ`) bound for `Q_0^{(l)}` in the regime `l > iwC0 ρ`. -/
private lemma iwQ0_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (h : iwC0 ρ < l) :
    (((iwQ0 ρ l : ℕ)) : ℝ) ≤ (2 : ℝ) ^ (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ)) := by
  have hl20 : (20 : ℝ) ≤ (l : ℝ) := by
    have : 20 ≤ l := by have := iwC0_ge_100 ρ; omega
    exact_mod_cast this
  have hD := iwD_le_of_iwC0_lt hρ h
  have hD4 : (iwD ρ : ℝ) ≤ (l : ℝ) / 4 := by linarith
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  have hlog := Work.KMTAreas.log_iwQ0_le ρ hρ l
  have hT : (0 : ℝ) < (2 : ℝ) ^ (l : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have h2ρ : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (l : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [hρ1, (Nat.cast_nonneg l : (0:ℝ) ≤ (l:ℝ))])
  have hlogT : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog1 : Real.log (((iwQ0 ρ l : ℕ)) : ℝ) ≤ (l : ℝ) * (2 : ℝ) ^ (l : ℝ) := by
    have hs1 : 4 * (iwD ρ : ℝ) ≤ (l : ℝ) := by linarith
    have hs2 : 4 * (iwD ρ : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (l : ℝ) * (2 : ℝ) ^ (l : ℝ) := by
      calc 4 * (iwD ρ : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ))
          ≤ (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
            mul_le_mul_of_nonneg_right hs1 hlogT.le
        _ ≤ (l : ℝ) * (2 : ℝ) ^ (l : ℝ) := mul_le_mul_of_nonneg_left h2ρ hl0.le
    linarith
  have hx : (0 : ℝ) < (((iwQ0 ρ l : ℕ)) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l))
  have hlog2' : Real.log (((iwQ0 ρ l : ℕ)) : ℝ) ≤
      2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) * Real.log 2 := by
    have hlT : (0 : ℝ) ≤ (l : ℝ) * (2 : ℝ) ^ (l : ℝ) := le_of_lt (mul_pos hl0 hT)
    have hkey : (l : ℝ) * (2 : ℝ) ^ (l : ℝ)
        ≤ 2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) * Real.log 2 := by
      have h : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [half_le_log_two]
      calc (l : ℝ) * (2 : ℝ) ^ (l : ℝ) = 1 * ((l : ℝ) * (2 : ℝ) ^ (l : ℝ)) :=
            (one_mul _).symm
        _ ≤ (2 * Real.log 2) * ((l : ℝ) * (2 : ℝ) ^ (l : ℝ)) :=
            mul_le_mul_of_nonneg_right h hlT
        _ = 2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) * Real.log 2 := by ring
    linarith
  calc (((iwQ0 ρ l : ℕ)) : ℝ) = Real.exp (Real.log (((iwQ0 ρ l : ℕ)) : ℝ)) := (Real.exp_log hx).symm
    _ ≤ Real.exp (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hlog2'
    _ = (2 : ℝ) ^ (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)
              (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ))]
        congr 1
        ring

/-! ## Cardinality in terms of the sum over `P_{≤l}` -/

private theorem iwArithFreqs_card_le_sum (ρ : ℝ) (l : ℕ) :
    (iwArithFreqs ρ l).card ≤ ∑ q ∈ iwP ρ l, q := by
  unfold iwArithFreqs
  calc ((iwP ρ l).biUnion
          (fun q => (Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle)))).card
      ≤ ∑ q ∈ iwP ρ l,
          ((Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ q ∈ iwP ρ l, q := by
        refine Finset.sum_le_sum fun q _ => ?_
        calc ((Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle))).card
            ≤ (Finset.range q).card := Finset.card_image_le
          _ = q := Finset.card_range q

/-- Uniform (in `ρ`) element bound for `P_{≤l}`. -/
private lemma iwP_element_uniform {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ}
    (h : iwC0 ρ < l) {q : ℕ} (hq : q ∈ iwP ρ l) : q ≤ 2 ^ (2 ^ (4 * l)) := by
  rw [mem_iwP] at hq
  rcases hq with ⟨hle, -, -⟩ | ⟨-, hqc⟩
  · exact absurd hle (not_le_of_gt h)
  · rw [mem_iwPconcrete] at hqc
    obtain ⟨Q, hQ, w, hw, rfl⟩ := hqc
    have hQle : Q ≤ iwQ0 ρ l :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l)) (Nat.mem_divisors.mp hQ).1
    have hQb : (Q : ℝ) ≤ (2 : ℝ) ^ (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ)) :=
      le_trans (by exact_mod_cast hQle) (iwQ0_bound hρ hρ1 h)
    have hwb : (w : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2) :=
      iwW_bound hρ h hw
    have hQnn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
    have hwnn : (0 : ℝ) ≤ (w : ℝ) := by positivity
    have hl1 : 1 ≤ l := by have := iwC0_ge_100 ρ; omega
    have hmul : (Q : ℝ) * (w : ℝ)
        ≤ (2 : ℝ) ^ (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ))
          * (2 : ℝ) ^ ((l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2) :=
      mul_le_mul hQb hwb hwnn (by positivity)
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)] at hmul
    have hT : (0 : ℝ) < (2 : ℝ) ^ (l : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hexp : 2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) + (l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2
        ≤ (2 : ℝ) ^ (4 * (l : ℝ)) := by
      have h := mul_exp_le l hl1
      have h2 : 2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) + (l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2
          ≤ (2 : ℝ) ^ (l : ℝ) * (2 * (l : ℝ) + (l : ℝ) ^ 2) := by
        have hfac : (2 : ℝ) ^ (l : ℝ) * (2 * (l : ℝ) + (l : ℝ) ^ 2)
            = 2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ) + (l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) := by ring
        rw [hfac]
        linarith [mul_nonneg (sq_nonneg (l : ℝ)) hT.le]
      linarith
    have hE : (2 : ℝ) ^ (4 * (l : ℝ)) = (((2 ^ (4 * l) : ℕ)) : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast]
      congr 1
      push_cast; ring
    have hgoal : (2 : ℝ) ^ ((2 : ℝ) ^ (4 * (l : ℝ)))
        = (((2 : ℕ) ^ (2 ^ (4 * l)) : ℕ) : ℝ) := by
      rw [hE]
      exact two_rpow_nat_cast (2 ^ (4 * l))
    have hmain : (Q : ℝ) * (w : ℝ) ≤ (((2 : ℕ) ^ (2 ^ (4 * l)) : ℕ) : ℝ) := by
      calc (Q : ℝ) * (w : ℝ)
          ≤ (2 : ℝ) ^ (2 * (l : ℝ) * (2 : ℝ) ^ (l : ℝ)
              + (l : ℝ) ^ 2 * (2 : ℝ) ^ (l : ℝ) / 2) := hmul
        _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (4 * (l : ℝ))) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (((2 : ℕ) ^ (2 ^ (4 * l)) : ℕ) : ℝ) := hgoal
    have hfin : (((Q * w : ℕ)) : ℝ) ≤ (((2 : ℕ) ^ (2 ^ (4 * l)) : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact hmain
    exact_mod_cast hfin

/-- The case `l ≤ iwC0 ρ`: `2^{2l} ≤ B l`. -/
private lemma two_pow_mul_two_pow_le_B (l : ℕ) :
    (((2 ^ l) * (2 ^ l) : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (2 ^ (4 * l))) ^ 2 + 1 := by
  have h1 : (((2 ^ l) * (2 ^ l) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (l : ℝ)) := by
    push_cast
    rw [← pow_add, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  rw [h1]
  have hl : (l : ℝ) ≤ (((2 ^ (4 * l) : ℕ)) : ℝ) := by
    have h : l ≤ 2 ^ (4 * l) :=
      le_trans (le_of_lt (Nat.lt_two_pow_self (n := l)))
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast h
  have h2 : (2 : ℝ) ^ (2 * (l : ℝ)) ≤ (2 : ℝ) ^ (2 * (((2 ^ (4 * l) : ℕ)) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have h3 : (2 : ℝ) ^ (2 * (((2 ^ (4 * l) : ℕ)) : ℝ)) = ((2 : ℝ) ^ (2 ^ (4 * l))) ^ 2 := by
    rw [← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  linarith [h2, h3]

/-! ## The uniform cardinality bound -/

/-- **A `ρ`-uniform cardinality bound for the Ionescu--Wainger frequency set.**  For every `l`
there is a constant `B l > 0` with `#(ℚ/ℤ)_{≤l} ≤ B l` for all `ρ ∈ (0,1]`. -/
theorem IwArithFreqsCardUniform :
    ∃ B : ℕ → ℝ, (∀ l, 0 < B l) ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ l : ℕ,
      ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) ≤ B l := by
  refine ⟨fun l => ((2 : ℝ) ^ (2 ^ (4 * l))) ^ 2 + 1, fun l => by positivity, ?_⟩
  intro ρ hρ hρ1 l
  set ML : ℕ := 2 ^ (2 ^ (4 * l)) with hML
  have hMLcast : ((ML : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (4 * l)) := by
    rw [hML]
    exact two_pow_two_pow_four_cast l
  by_cases h : l ≤ iwC0 ρ
  · have hP : iwP ρ l = Finset.Icc 1 (2 ^ l) := by rw [iwP, if_pos h]
    have hcard : (iwArithFreqs ρ l).card ≤ (2 ^ l) * (2 ^ l) := by
      calc (iwArithFreqs ρ l).card ≤ ∑ q ∈ iwP ρ l, q := iwArithFreqs_card_le_sum ρ l
        _ = ∑ q ∈ Finset.Icc 1 (2 ^ l), q := by rw [hP]
        _ ≤ ∑ _q ∈ Finset.Icc 1 (2 ^ l), (2 ^ l : ℕ) :=
              Finset.sum_le_sum fun q hq => (Finset.mem_Icc.mp hq).2
        _ = (Finset.Icc 1 (2 ^ l)).card * (2 ^ l) := by rw [Finset.sum_const, smul_eq_mul]
        _ = (2 ^ l) * (2 ^ l) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    calc ((iwArithFreqs ρ l).card : ℝ) ≤ (((2 ^ l) * (2 ^ l) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ ((2 : ℝ) ^ (2 ^ (4 * l))) ^ 2 + 1 := two_pow_mul_two_pow_le_B l
  · push_neg at h
    have hsub : iwP ρ l ⊆ Finset.Icc 1 ML := by
      intro q hq
      exact Finset.mem_Icc.mpr ⟨pos_of_mem_iwP hq, by
        rw [hML]
        exact iwP_element_uniform hρ hρ1 h hq⟩
    have hcardP : (iwP ρ l).card ≤ ML := by
      calc (iwP ρ l).card ≤ (Finset.Icc 1 ML).card := Finset.card_le_card hsub
        _ = ML := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    have hcard : (iwArithFreqs ρ l).card ≤ ML * ML := by
      calc (iwArithFreqs ρ l).card ≤ ∑ q ∈ iwP ρ l, q := iwArithFreqs_card_le_sum ρ l
        _ ≤ ∑ _q ∈ iwP ρ l, ML := Finset.sum_le_sum fun q hq => (Finset.mem_Icc.mp (hsub hq)).2
        _ = (iwP ρ l).card * ML := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ML * ML := Nat.mul_le_mul_right ML hcardP
    calc ((iwArithFreqs ρ l).card : ℝ) ≤ ((ML * ML : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((ML : ℕ) : ℝ) ^ 2 := by push_cast; ring
      _ = ((2 : ℝ) ^ (2 ^ (4 * l))) ^ 2 := by rw [hMLcast]
      _ ≤ ((2 : ℝ) ^ (2 ^ (4 * l))) ^ 2 + 1 := by linarith

end Work.KMTAreas.A7
