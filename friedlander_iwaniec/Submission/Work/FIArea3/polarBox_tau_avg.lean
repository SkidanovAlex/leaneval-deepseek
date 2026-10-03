/-
# `Submission.Work.FIArea3.polarBox_tau_avg`

The average of the divisor function `τ(|z|²)` over the polar box (5.14):
for every admissible set-up and every sector angle `φ`, in the regime
`N^{3/8} ≤ θ√N`,

  `Σ_{z ∈ polar box} τ(|z|²) ≤ C·(θ²N + θ√N + 1)·(1 + log N)²`.

The proof is elementary and uses only the lattice count for the *single* divisibility
`d ∣ |z|²` (`JointCount.card_filter_le_le_arith`, applied with `e = 1`) together with the
classical divisor–summatory estimates `Σ_{d≤D} τ(d)/d ≤ (1+log D)²`,
`Σ_{d≤D} τ(d)/√d ≪ √D log D`, `Σ_{d≤D} τ(d) ≪ D log D`.

The divisor function is split at `u²` (`u = θ√N`): a divisor `d` of `n = |z|²` is either
`≤ u²`, or its cofactor `n/d < (1+θ)/θ² =: E`.  Summing the count bound over the two ranges
and using the summatory estimates gives the result.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith

set_option maxHeartbeats 4000000

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary real / divisor-summatory estimates -/

/-- `1/√(x+1) ≤ 2(√(x+1) − √x)` for `x ≥ 0`; the telescoping input of `Σ 1/√d ≤ 2√D`. -/
lemma inv_sqrt_succ_le (x : ℝ) (hx : 0 ≤ x) :
    1/Real.sqrt (x+1) ≤ 2*(Real.sqrt (x+1) - Real.sqrt x) := by
  have h1 : 0 < Real.sqrt (x+1) := Real.sqrt_pos.mpr (by linarith)
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsum_pos : 0 < Real.sqrt (x+1) + Real.sqrt x := by linarith
  have hdiff : Real.sqrt (x+1) - Real.sqrt x = 1/(Real.sqrt (x+1)+Real.sqrt x) := by
    rw [eq_div_iff (ne_of_gt hsum_pos)]
    have : (Real.sqrt (x+1) - Real.sqrt x)*(Real.sqrt (x+1)+Real.sqrt x)
        = (Real.sqrt (x+1))^2 - (Real.sqrt x)^2 := by ring
    rw [this, Real.sq_sqrt (by linarith), Real.sq_sqrt hx]; ring
  have hs : Real.sqrt (x+1) + Real.sqrt x ≤ 2*Real.sqrt (x+1) := by
    have := Real.sqrt_le_sqrt (show x ≤ x+1 by linarith); linarith
  have h2 : (0:ℝ) < 2*Real.sqrt (x+1) := by positivity
  have hge : 1/(2*Real.sqrt (x+1)) ≤ Real.sqrt (x+1) - Real.sqrt x := by
    rw [hdiff, one_div_le_one_div h2 hsum_pos]
    exact hs
  calc 1/Real.sqrt (x+1) = 2*(1/(2*Real.sqrt (x+1))) := by field_simp
    _ ≤ 2*(Real.sqrt (x+1) - Real.sqrt x) := by linarith [hge]

/-- **The hyperbolic reindexing.**  `Σ_{d≤D} Σ_{e|d} F e (d/e) = Σ_{e≤D} Σ_{f≤D/e} F e f`. -/
lemma hyperbola (D : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, F e (d / e))
      = ∑ e ∈ Finset.Icc 1 D, ∑ f ∈ Finset.Icc 1 (D / e), F e f := by
  rw [Finset.sum_sigma' (Finset.Icc 1 D) (fun d => d.divisors) (fun d e => F e (d / e))]
  rw [Finset.sum_sigma' (Finset.Icc 1 D) (fun e => Finset.Icc 1 (D / e)) (fun e f => F e f)]
  apply Finset.sum_bij' (fun x _ => (⟨x.2, x.1 / x.2⟩ : Sigma (fun _ : ℕ => ℕ)))
    (fun y _ => (⟨y.1 * y.2, y.1⟩ : Sigma (fun _ : ℕ => ℕ)))
  · rintro ⟨d,e⟩ hx
    rw [Finset.mem_sigma] at hx ⊢
    obtain ⟨hd, he⟩ := hx
    rw [Nat.mem_divisors] at he
    obtain ⟨hed, hdne⟩ := he
    have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hed (Nat.pos_of_ne_zero hdne)
    have hde : e * (d / e) = d := Nat.mul_div_cancel' hed
    have hpos : 1 ≤ d / e := by
      rcases Nat.eq_zero_or_pos (d / e) with h | h
      · rw [h, mul_zero] at hde; exact absurd hde.symm hdne
      · exact h
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨he1, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hdne) hed)
        (Finset.mem_Icc.mp hd).2⟩
    · rw [Finset.mem_Icc]; exact ⟨hpos, Nat.div_le_div_right (Finset.mem_Icc.mp hd).2⟩
  · rintro ⟨e,f⟩ hy
    rw [Finset.mem_sigma] at hy ⊢
    obtain ⟨he, hf⟩ := hy
    rw [Finset.mem_Icc] at he hf
    have he0 : e ≠ 0 := Nat.one_le_iff_ne_zero.mp he.1
    have hf0 : f ≠ 0 := Nat.one_le_iff_ne_zero.mp hf.1
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he0 hf0),
        le_trans (Nat.mul_le_mul_left e hf.2) (Nat.mul_div_le D e)⟩
    · rw [Nat.mem_divisors]
      exact ⟨Dvd.intro f rfl, Nat.mul_ne_zero he0 hf0⟩
  · rintro ⟨d,e⟩ hx
    rw [Finset.mem_sigma] at hx
    rw [Nat.mem_divisors] at hx
    have hde : e * (d / e) = d := Nat.mul_div_cancel' hx.2.1
    show (⟨e * (d / e), e⟩ : Sigma (fun _ : ℕ => ℕ)) = ⟨d, e⟩
    rw [hde]
  · rintro ⟨e,f⟩ hy
    rw [Finset.mem_sigma] at hy
    rw [Finset.mem_Icc] at hy
    have hepos : 0 < e := hy.1.1
    have : e * f / e = f := Nat.mul_div_cancel_left f hepos
    show (⟨e, e * f / e⟩ : Sigma (fun _ : ℕ => ℕ)) = ⟨e, f⟩
    rw [this]
  · rintro ⟨d,e⟩ hx
    rfl

/-- `Σ_{d ≤ D} 1/d ≤ 1 + log D` (the harmonic sum). -/
lemma sum_inv_Icc_le (D : ℕ) : (∑ d ∈ Finset.Icc 1 D, (1:ℝ)/(d:ℝ)) ≤ 1 + Real.log (D:ℝ) := by
  have hcast : (∑ d ∈ Finset.Icc 1 D, (1:ℝ)/(d:ℝ)) = (harmonic D : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Rat.cast_inv, Rat.cast_natCast]
    simp [one_div]
  rw [hcast]
  exact harmonic_le_one_add_log D

/-- `Σ_{d ≤ D} 1/√d ≤ 2√D` (telescoping against `√(d+1) − √d`). -/
lemma sum_inv_sqrt_Icc_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (1:ℝ)/Real.sqrt (d:ℝ)) ≤ 2*Real.sqrt (D:ℝ) := by
  have hstep1 : (∑ d ∈ Finset.Icc 1 D, (1:ℝ)/Real.sqrt (d:ℝ))
      = ∑ k ∈ Finset.range D, (1:ℝ)/Real.sqrt (((1:ℕ)+k : ℕ):ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (a:=1) (b:=D)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  rw [hstep1]
  have hterm : ∀ k ∈ Finset.range D, (1:ℝ)/Real.sqrt (((1:ℕ)+k : ℕ):ℝ)
      ≤ 2*(Real.sqrt (((1:ℕ)+k : ℕ):ℝ) - Real.sqrt ((k:ℝ))) := by
    intro k hk
    have hk' : (((1:ℕ)+k : ℕ):ℝ) = (k:ℝ)+1 := by push_cast; ring
    rw [hk']
    exact inv_sqrt_succ_le k (Nat.cast_nonneg k)
  have hsame : (∑ k ∈ Finset.range D, 2*(Real.sqrt (((1:ℕ)+k : ℕ):ℝ) - Real.sqrt ((k:ℝ))))
      = ∑ k ∈ Finset.range D, 2*(Real.sqrt (((k+1:ℕ)):ℝ) - Real.sqrt ((k:ℝ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have : (((1:ℕ)+k : ℕ):ℝ) = ((k+1:ℕ):ℝ) := by push_cast; ring
    rw [this]
  calc ∑ k ∈ Finset.range D, (1:ℝ)/Real.sqrt (((1:ℕ)+k : ℕ):ℝ)
      ≤ ∑ k ∈ Finset.range D, 2*(Real.sqrt (((1:ℕ)+k : ℕ):ℝ) - Real.sqrt ((k:ℝ))) :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.range D, 2*(Real.sqrt (((k+1:ℕ)):ℝ) - Real.sqrt ((k:ℝ))) := hsame
    _ = 2*∑ k ∈ Finset.range D, (Real.sqrt (((k+1:ℕ)):ℝ) - Real.sqrt ((k:ℝ))) := by
        rw [Finset.mul_sum]
    _ = 2*Real.sqrt (D:ℝ) := by
        rw [Finset.sum_range_sub (fun i : ℕ => Real.sqrt ((i:ℝ))) D, Nat.cast_zero,
          Real.sqrt_zero, sub_zero]

/-- `Σ_{d ≤ D} τ(d)/d ≤ (1 + log D)²`. -/
lemma sum_divisors_div_Icc_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) / (d : ℝ))) ≤ (1 + Real.log (D:ℝ))^2 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; norm_num
  have hstep : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) / (d : ℝ)))
      = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, 1/((e:ℝ)*((d/e:ℕ):ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    have hdvd : e ∣ d := (Nat.mem_divisors.mp he).1
    have hcancel : e * (d/e) = d := Nat.mul_div_cancel' hdvd
    have hc : ((e:ℝ)*((d/e:ℕ):ℝ)) = (d:ℝ) := by rw [← Nat.cast_mul, hcancel]
    rw [hc]; norm_num
  rw [hstep, hyperbola D (fun e f => 1/((e:ℝ)*(f:ℝ)))]
  have hloggoal : 0 ≤ 1 + Real.log (D:ℝ) := by
    have : (0:ℝ) ≤ Real.log (D:ℝ) := Real.log_nonneg (by exact_mod_cast hD)
    linarith
  have hinner : ∀ e ∈ Finset.Icc 1 D, (∑ f ∈ Finset.Icc 1 (D/e), 1/((e:ℝ)*(f:ℝ)))
      ≤ (1/(e:ℝ)) * (1 + Real.log (D:ℝ)) := by
    intro e he
    rw [Finset.mem_Icc] at he
    have hepos : (0:ℝ) < (e:ℝ) := by exact_mod_cast he.1
    have hfac : (∑ f ∈ Finset.Icc 1 (D/e), 1/((e:ℝ)*(f:ℝ)))
        = (1/(e:ℝ)) * ∑ f ∈ Finset.Icc 1 (D/e), (1:ℝ)/(f:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      field_simp
    rw [hfac]
    have hharm := sum_inv_Icc_le (D/e)
    have hlog : Real.log ((D/e:ℕ):ℝ) ≤ Real.log (D:ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (Nat.div_pos he.2 (by omega))
      · exact_mod_cast (Nat.div_le_self D e)
    have hstep2 : (1:ℝ) + Real.log ((D/e:ℕ):ℝ) ≤ 1 + Real.log (D:ℝ) := by linarith
    calc (1/(e:ℝ)) * ∑ f ∈ Finset.Icc 1 (D/e), (1:ℝ)/(f:ℝ)
        ≤ (1/(e:ℝ)) * (1 + Real.log ((D/e:ℕ):ℝ)) := by
          apply mul_le_mul_of_nonneg_left hharm (by positivity)
      _ ≤ (1/(e:ℝ)) * (1 + Real.log (D:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hstep2 (by positivity)
  calc (∑ e ∈ Finset.Icc 1 D, ∑ f ∈ Finset.Icc 1 (D/e), 1/((e:ℝ)*(f:ℝ)))
      ≤ ∑ e ∈ Finset.Icc 1 D, (1/(e:ℝ)) * (1 + Real.log (D:ℝ)) := Finset.sum_le_sum hinner
    _ = (1 + Real.log (D:ℝ)) * ∑ e ∈ Finset.Icc 1 D, (1/(e:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
    _ ≤ (1 + Real.log (D:ℝ)) * (1 + Real.log (D:ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_Icc_le D) hloggoal
    _ = (1 + Real.log (D:ℝ))^2 := by ring

/-- `Σ_{d ≤ D} τ(d)/√d ≤ 4√D (1 + log D)`. -/
lemma sum_divisors_div_sqrt_Icc_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) / Real.sqrt (d:ℝ)))
      ≤ 4 * Real.sqrt (D:ℝ) * (1 + Real.log (D:ℝ)) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  have hstep : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) / Real.sqrt (d:ℝ)))
      = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors,
          (1/Real.sqrt (e:ℝ))*(1/Real.sqrt ((d/e:ℕ):ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    have hdvd : e ∣ d := (Nat.mem_divisors.mp he).1
    have hcancel : e * (d/e) = d := Nat.mul_div_cancel' hdvd
    have hs : Real.sqrt ((e:ℝ)) * Real.sqrt ((↑(d/e):ℕ):ℝ) = Real.sqrt (d:ℝ) := by
      rw [← Real.sqrt_mul (show (0:ℝ) ≤ (e:ℝ) by positivity), ← Nat.cast_mul, hcancel]
    rw [Nat.cast_one, one_div, one_div, one_div, ← mul_inv, hs]
  rw [hstep, hyperbola D (fun e f => (1/Real.sqrt (e:ℝ))*(1/Real.sqrt (f:ℝ)))]
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hinner : ∀ e ∈ Finset.Icc 1 D,
      (∑ f ∈ Finset.Icc 1 (D/e), (1/Real.sqrt (e:ℝ))*(1/Real.sqrt (f:ℝ)))
      ≤ 2*Real.sqrt (D:ℝ)/(e:ℝ) := by
    intro e he
    rw [Finset.mem_Icc] at he
    have hepos : (0:ℝ) < (e:ℝ) := by exact_mod_cast he.1
    have hfac : (∑ f ∈ Finset.Icc 1 (D/e), (1/Real.sqrt (e:ℝ))*(1/Real.sqrt (f:ℝ)))
        = (1/Real.sqrt (e:ℝ)) * ∑ f ∈ Finset.Icc 1 (D/e), (1/Real.sqrt (f:ℝ)) := by
      rw [Finset.mul_sum]
    rw [hfac]
    have hharm := sum_inv_sqrt_Icc_le (D/e)
    have hcastle : ((D/e:ℕ):ℝ) ≤ (D:ℝ)/(e:ℝ) := Nat.cast_div_le
    have hsqrtle : Real.sqrt ((↑(D/e):ℕ):ℝ) ≤ Real.sqrt (D:ℝ)/Real.sqrt (e:ℝ) := by
      calc Real.sqrt ((↑(D/e):ℕ):ℝ) ≤ Real.sqrt ((D:ℝ)/(e:ℝ)) := Real.sqrt_le_sqrt hcastle
        _ = Real.sqrt (D:ℝ)/Real.sqrt (e:ℝ) := Real.sqrt_div (le_of_lt hDpos) (e:ℝ)
    have hsq : Real.sqrt (e:ℝ) ^ 2 = (e:ℝ) := Real.sq_sqrt (le_of_lt hepos)
    calc (1/Real.sqrt (e:ℝ)) * ∑ f ∈ Finset.Icc 1 (D/e), (1/Real.sqrt (f:ℝ))
        ≤ (1/Real.sqrt (e:ℝ)) * (2 * Real.sqrt ((↑(D/e):ℕ):ℝ)) := by
          apply mul_le_mul_of_nonneg_left hharm (by positivity)
      _ ≤ (1/Real.sqrt (e:ℝ)) * (2 * (Real.sqrt (D:ℝ)/Real.sqrt (e:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hsqrtle]
      _ = 2*Real.sqrt (D:ℝ)/(e:ℝ) := by
          field_simp
          rw [hsq]
  calc (∑ e ∈ Finset.Icc 1 D, ∑ f ∈ Finset.Icc 1 (D/e), (1/Real.sqrt (e:ℝ))*(1/Real.sqrt (f:ℝ)))
      ≤ ∑ e ∈ Finset.Icc 1 D, 2*Real.sqrt (D:ℝ)/(e:ℝ) := Finset.sum_le_sum hinner
    _ = 2*Real.sqrt (D:ℝ) * ∑ e ∈ Finset.Icc 1 D, (1:ℝ)/(e:ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring_nf
    _ ≤ 2*Real.sqrt (D:ℝ) * (1 + Real.log (D:ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_Icc_le D)
        positivity
    _ ≤ 4 * Real.sqrt (D:ℝ) * (1 + Real.log (D:ℝ)) := by
        have h1 : (0:ℝ) ≤ Real.sqrt (D:ℝ) := Real.sqrt_nonneg _
        have h2 : (0:ℝ) ≤ 1 + Real.log (D:ℝ) := by
          have := Real.log_nonneg (show (1:ℝ) ≤ D by exact_mod_cast hD); linarith
        nlinarith

/-- `Σ_{d ≤ D} τ(d) ≤ D (1 + log D)`. -/
lemma sum_divisors_Icc_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)))
      ≤ (D:ℝ) * (1 + Real.log (D:ℝ)) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  have hstep : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)))
      = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, (1:ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]; simp
  rw [hstep, hyperbola D (fun e f => (1:ℝ))]
  have hconst : ∀ e ∈ Finset.Icc 1 D, (∑ f ∈ Finset.Icc 1 (D/e), (1:ℝ)) = ((D/e:ℕ):ℝ) := by
    intro e he
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    push_cast
    ring
  have h1 : (∑ e ∈ Finset.Icc 1 D, (∑ f ∈ Finset.Icc 1 (D/e), (1:ℝ)))
      = ∑ e ∈ Finset.Icc 1 D, ((D/e:ℕ):ℝ) := Finset.sum_congr rfl hconst
  rw [h1]
  have h2 : (∑ e ∈ Finset.Icc 1 D, ((D/e:ℕ):ℝ)) ≤ ∑ e ∈ Finset.Icc 1 D, (D:ℝ)/(e:ℝ) := by
    apply Finset.sum_le_sum
    intro e he
    exact Nat.cast_div_le
  have h3 : (∑ e ∈ Finset.Icc 1 D, (D:ℝ)/(e:ℝ)) = (D:ℝ) * ∑ e ∈ Finset.Icc 1 D, (1:ℝ)/(e:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  have h4 : (D:ℝ) * ∑ e ∈ Finset.Icc 1 D, (1:ℝ)/(e:ℝ) ≤ (D:ℝ) * (1 + Real.log (D:ℝ)) := by
    apply mul_le_mul_of_nonneg_left (sum_inv_Icc_le D)
    positivity
  linarith [h2, h3.le, h3.ge, h4]

/-! ## 2. The divisor split and the single-divisibility lattice count -/

/-- The indicator count `Σ_{d ≤ D} [d ∣ n]` is the number of divisors of `n` that are `≤ D`. -/
lemma sum_Icc_ite_dvd_eq (n D : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ Finset.Icc 1 D, (if d ∣ n then (1:ℝ) else 0))
      = ((n.divisors.filter (fun d => d ≤ D)).card : ℝ) := by
  have heq : n.divisors.filter (fun d => d ≤ D)
      = (Finset.Icc 1 D).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hle⟩
      rw [Nat.mem_divisors] at hd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hn), hle⟩, hd.1⟩
    · rintro ⟨⟨h1,h2⟩, hdvd⟩
      exact ⟨Nat.mem_divisors.mpr ⟨hdvd, hn⟩, h2⟩
  rw [heq, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ n <;> simp [h]

/-- **The divisor split.**  If every divisor `d > D` of `n` has cofactor `n/d ≤ E`, then
`τ(n)` is at most the number of `≤ D` divisors plus the number of `≤ E` divisors. -/
lemma card_divisors_le_two_Icc_indicator (n D E : ℕ)
    (hcof : ∀ d ∈ n.divisors, D < d → n / d ≤ E) :
    (n.divisors.card : ℝ) ≤
      (∑ d ∈ Finset.Icc 1 D, (if d ∣ n then (1:ℝ) else 0)) +
      (∑ m ∈ Finset.Icc 1 E, (if m ∣ n then (1:ℝ) else 0)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have : (0:ℝ) ≤ (∑ d ∈ Finset.Icc 1 D, (if d ∣ 0 then (1:ℝ) else 0)) +
        (∑ m ∈ Finset.Icc 1 E, (if m ∣ 0 then (1:ℝ) else 0)) := by positivity
    simpa using this
  have hn : n ≠ 0 := hnpos.ne'
  rw [sum_Icc_ite_dvd_eq n D hn, sum_Icc_ite_dvd_eq n E hn]
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.divisors) (p := fun d => d ≤ D)
  have hnot : n.divisors.filter (fun d => ¬ d ≤ D) = n.divisors.filter (fun d => D < d) := by
    apply Finset.filter_congr
    intro d _
    omega
  have hinj : (n.divisors.filter (fun d => D < d)).card
      ≤ (n.divisors.filter (fun m => m ≤ E)).card := by
    apply Finset.card_le_card_of_injOn (fun d => n / d)
    · intro d hd
      rw [Finset.mem_coe, Finset.mem_filter] at hd
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨hdmem, hDd⟩ := hd
      exact ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hdmem).1, hn⟩,
        hcof d hdmem hDd⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have h1 : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have h2 : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have e1 : d₁ * (n / d₁) = n := Nat.mul_div_cancel' h1
      have e2 : d₂ * (n / d₂) = n := Nat.mul_div_cancel' h2
      have heq' : n / d₁ = n / d₂ := heq
      have hcpos : 0 < n / d₁ := by
        rcases Nat.eq_zero_or_pos (n / d₁) with h | h
        · rw [h, mul_zero] at e1; exact absurd e1.symm hn
        · exact h
      have hmm : d₁ * (n / d₁) = d₂ * (n / d₁) := by rw [e1, heq']; exact e2.symm
      exact Nat.mul_right_cancel hcpos hmm
  rw [hnot] at hsplit
  have hcast : (n.divisors.card : ℝ) ≤
      ((n.divisors.filter (fun d => d ≤ D)).card : ℝ)
      + ((n.divisors.filter (fun m => m ≤ E)).card : ℝ) := by
    have heq2 : (n.divisors.filter (fun d => d ≤ D)).card + (n.divisors.filter (fun d => D < d)).card
        = n.divisors.card := hsplit
    have h2 : (n.divisors.filter (fun d => D < d)).card
        ≤ (n.divisors.filter (fun m => m ≤ E)).card := hinj
    have hcast2 : (n.divisors.card : ℝ) = ((n.divisors.filter (fun d => d ≤ D)).card : ℝ)
        + ((n.divisors.filter (fun d => D < d)).card : ℝ) := by
      rw [← heq2]; push_cast; ring
    rw [hcast2]
    have h2' : ((n.divisors.filter (fun d => D < d)).card : ℝ)
        ≤ ((n.divisors.filter (fun m => m ≤ E)).card : ℝ) := by exact_mod_cast h2
    linarith
  exact hcast

/-- The lattice count for `d ∣ |z₂|²`, read off from the joint count with `e = 1`. -/
lemma card_polarBox_filter_dvd_gnorm (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    (((polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((d.divisors.card : ℝ) / (d : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((d.divisors.card : ℝ) / Real.sqrt (d : ℝ))
        + (d.divisors.card : ℝ) := by
  have h := Work.FIArea3.JointCount.card_filter_le_le_arith Pa φ 0 d 1 hd (le_refl 1)
  have heq : (polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIPlan.gnorm z)
      = Work.FIArea3.JointCount.pairBoxFinset Pa φ 0 d 1 := by
    rw [Work.FIArea3.JointCount.pairBoxFinset]
    apply Finset.filter_congr
    intro z _
    simp
  rw [heq]
  exact h

/-! ## 3. Facts about `Params` -/

/-- `1 ≤ log x` for `x ≥ 3`. -/
lemma one_le_log_x_param (Pa : Work.FITop.Params) : 1 ≤ Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  exact le_trans h3 (Real.log_le_log (by norm_num) hx3)

/-- `θ = (log x)^{-A'} ≤ 1`. -/
lemma theta_le_one_param (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  refine Real.rpow_le_one_of_one_le_of_nonpos (one_le_log_x_param Pa) ?_
  have : 0 ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
  linarith

/-! ## 4. The main lemma -/

lemma polarBox_tau_avg :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ C * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
            * (1 + Real.log Pa.N) ^ (2 : ℕ) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro Pa φ hhyp
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  set L : ℝ := 1 + Real.log Pa.N with hL
  set D : ℕ := ⌈u ^ 2⌉₊ with hD
  set E : ℕ := ⌈(1 + Pa.θ) / Pa.θ ^ 2⌉₊ with hE
  -- § basic facts
  have hNpos : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one_param Pa
  have hsqrtN_pos : 0 < Real.sqrt Pa.N := Real.sqrt_pos.mpr hNpos
  have hL1 : 1 ≤ L := by rw [hL]; have := Real.log_nonneg hN1; linarith
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hhyp' : Pa.N ^ ((3:ℝ)/8) ≤ Pa.θ * Real.sqrt Pa.N := by rw [← hu]; exact hhyp
  have hu_ge1 : 1 ≤ u := by
    rw [hu]
    have h1 : (1:ℝ) ≤ Pa.N ^ ((3:ℝ)/8) := Real.one_le_rpow hN1 (by norm_num)
    linarith [hhyp]
  have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu_ge1
  have hu_le : u ≤ Real.sqrt Pa.N := by
    rw [hu]
    calc Pa.θ * Real.sqrt Pa.N ≤ 1 * Real.sqrt Pa.N :=
          mul_le_mul_of_nonneg_right hθ1 hsqrtN_pos.le
      _ = Real.sqrt Pa.N := one_mul _
  have hu2 : u ^ 2 = Pa.θ ^ 2 * Pa.N := by
    rw [hu, mul_pow, Real.sq_sqrt hNpos.le]
  have hu2pos : 0 < u ^ 2 := by positivity
  -- § θ lower bound  θ ≥ N^{-1/8}
  have hNrpow : Pa.N ^ (-(1:ℝ)/8) * Real.sqrt Pa.N = Pa.N ^ ((3:ℝ)/8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]; congr 1; norm_num
  have hθlb : Pa.N ^ (-(1:ℝ)/8) ≤ Pa.θ := by
    have h2 : Pa.N ^ (-(1:ℝ)/8) * Real.sqrt Pa.N ≤ Pa.θ * Real.sqrt Pa.N := by
      rw [hNrpow]; exact hhyp'
    exact le_of_mul_le_mul_right h2 hsqrtN_pos
  have hθ2lb : Pa.N ^ (-(1:ℝ)/4) ≤ Pa.θ ^ 2 := by
    have hsq : (Pa.N ^ (-(1:ℝ)/8))^2 = Pa.N ^ (-(1:ℝ)/4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
    rw [← hsq]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hθlb 2
  -- § u² ≥ N^{3/4}
  have hu2_lb : Pa.N ^ ((3:ℝ)/4) ≤ u ^ 2 := by
    have hmul : Pa.N ^ (-(1:ℝ)/4) * Pa.N ≤ Pa.θ ^ 2 * Pa.N :=
      mul_le_mul_of_nonneg_right hθ2lb hNpos.le
    have heq : Pa.N ^ ((3:ℝ)/4) = Pa.N ^ (-(1:ℝ)/4) * Pa.N := by
      rw [show ((3:ℝ)/4) = -(1:ℝ)/4 + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
    rw [hu2, heq]; exact hmul
  have hsqrt_le_u2 : Real.sqrt Pa.N ≤ u ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    have h2 : Pa.N ^ ((1:ℝ)/2) ≤ Pa.N ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    linarith [h2, hu2_lb]
  -- § √N ≤ u²·L
  have hsqrtN_le_u2L : Real.sqrt Pa.N ≤ u ^ 2 * L := by
    nlinarith [hsqrt_le_u2, hu_ge1, hL1, sq_nonneg u]
  -- § 1 ≤ θ²·u²
  have hone_le_θ2u2 : 1 ≤ Pa.θ ^ 2 * u ^ 2 := by
    have hmul : (Pa.N ^ (-(1:ℝ)/4))^2 * Pa.N ≤ (Pa.θ ^ 2)^2 * Pa.N :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hθ2lb 2) hNpos.le
    have hsq : (Pa.N ^ (-(1:ℝ)/4))^2 = Pa.N ^ (-(1:ℝ)/2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
    have heq : Pa.N ^ ((1:ℝ)/2) = (Pa.N ^ (-(1:ℝ)/4))^2 * Pa.N := by
      rw [show ((1:ℝ)/2) = -(1:ℝ)/2 + 1 by ring, Real.rpow_add hNpos, Real.rpow_one, ← hsq]
    have hNhalf : (1:ℝ) ≤ Pa.N ^ ((1:ℝ)/2) := Real.one_le_rpow hN1 (by norm_num)
    have hgoal : (1:ℝ) ≤ (Pa.θ ^ 2)^2 * Pa.N := by rw [heq] at hNhalf; linarith [hmul, hNhalf]
    rw [hu2]
    nlinarith [hgoal]
  -- § bounds on D and E
  have hDceil : u ^ 2 ≤ (D:ℝ) := by rw [hD]; exact Nat.le_ceil _
  have hDlt : (D:ℝ) < u ^ 2 + 1 := by rw [hD]; exact Nat.ceil_lt_add_one (by positivity)
  have hDle : (D:ℝ) ≤ 2 * u ^ 2 := by nlinarith [hDlt, hu_ge1, sq_nonneg u]
  have hD1 : 1 ≤ D := by
    have : (1:ℝ) ≤ (D:ℝ) := by linarith [hDceil, hu_ge1]
    exact_mod_cast this
  have hlogD : Real.log (D:ℝ) ≤ L := by
    have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD1
    have h1 : Real.log (D:ℝ) ≤ Real.log (2 * u ^ 2) := Real.log_le_log hDpos hDle
    have h2 : Real.log (2 * u ^ 2) = Real.log 2 + 2 * Real.log u := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
    have h3 : Real.log u ≤ Real.log (Real.sqrt Pa.N) := Real.log_le_log hu_pos hu_le
    have h4 : Real.log (Real.sqrt Pa.N) = Real.log Pa.N / 2 := by
      rw [Real.log_sqrt hNpos.le]
    have h5 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [hL]; linarith [h1, h2.le, h2.ge, h3, h4, h5]
  have hlogD2 : 1 + Real.log (D:ℝ) ≤ 2 * L := by linarith [hlogD, hL1]
  have hlogD0 : 0 ≤ Real.log (D:ℝ) := Real.log_nonneg (by exact_mod_cast hD1)
  have hsqrtD : Real.sqrt (D:ℝ) ≤ 2 * u := by
    have h1 : Real.sqrt (D:ℝ) ≤ Real.sqrt (2 * u ^ 2) := Real.sqrt_le_sqrt hDle
    have h2 : Real.sqrt (2 * u ^ 2) = Real.sqrt 2 * u := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (u^2), Real.sqrt_sq hu_pos.le]
    have h3 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]; constructor <;> norm_num
    nlinarith [h1, h2.le, h2.ge, h3, hu_pos]
  have hEceil : (1 + Pa.θ) / Pa.θ ^ 2 ≤ (E:ℝ) := by rw [hE]; exact Nat.le_ceil _
  have hEle : (E:ℝ) ≤ 4 / Pa.θ ^ 2 := by
    have h1 : (1:ℝ) ≤ (1 + Pa.θ)/Pa.θ^2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hθ1, hθ0]
    have h2 : (E:ℝ) < (1 + Pa.θ)/Pa.θ^2 + 1 := by rw [hE]; exact Nat.ceil_lt_add_one (by positivity)
    have h3 : (1 + Pa.θ)/Pa.θ^2 + 1 ≤ 2 * ((1 + Pa.θ)/Pa.θ^2) := by linarith
    have h4 : 2 * ((1 + Pa.θ)/Pa.θ^2) ≤ 4 / Pa.θ^2 := by
      field_simp
      linarith [hθ1]
    linarith [h2.le, h3, h4]
  have hE1 : 1 ≤ E := by
    have : (1:ℝ) ≤ (E:ℝ) := le_trans (by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hθ1, hθ0]) hEceil
    exact_mod_cast this
  have hlogE : Real.log (E:ℝ) ≤ 3 * L := by
    have hEpos : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE1
    have h1 : Real.log (E:ℝ) ≤ Real.log (4 / Pa.θ ^ 2) := Real.log_le_log hEpos hEle
    have h2 : Real.log (4 / Pa.θ ^ 2) = Real.log 4 + 2 * Real.log (1/Pa.θ) := by
      rw [show (4:ℝ)/Pa.θ^2 = 4 * (1/Pa.θ)^2 by field_simp,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have h3 : Real.log (1/Pa.θ) ≤ (1/8) * Real.log Pa.N := by
      have h4 : Real.log (Pa.N ^ (-(1:ℝ)/8)) ≤ Real.log Pa.θ :=
        Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hθlb
      rw [Real.log_rpow hNpos] at h4
      have h5 : Real.log (1/Pa.θ) = - Real.log Pa.θ := by
        rw [one_div, Real.log_inv]
      rw [h5]; linarith
    have h6 : Real.log 4 ≤ 2 := by
      have hl2 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      push_cast
      linarith
    rw [hL]; linarith [h1, h2.le, h2.ge, h3, h6, hL1]
  have hlogE2 : 1 + Real.log (E:ℝ) ≤ 4 * L := by linarith [hlogE, hL1]
  have hlogE0 : 0 ≤ Real.log (E:ℝ) := Real.log_nonneg (by exact_mod_cast hE1)
  have hsqrtE : Real.sqrt (E:ℝ) ≤ 2 / Pa.θ := by
    have h1 : Real.sqrt (E:ℝ) ≤ Real.sqrt (4 / Pa.θ ^ 2) := Real.sqrt_le_sqrt hEle
    have h2 : Real.sqrt (4 / Pa.θ ^ 2) = 2 / Pa.θ := by
      rw [Real.sqrt_div (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num),
        Real.sqrt_sq hθ0.le]
    linarith [h1, h2.le, h2.ge]
  have hu_div_θ : u / Pa.θ = Real.sqrt Pa.N := by
    rw [hu]; field_simp
  -- § the coefficient bound `hcof`
  have hcof : ∀ z ∈ polarBoxFinset Pa φ, ∀ d ∈ (Work.FIPlan.gnorm z).divisors,
      D < d → Work.FIPlan.gnorm z / d ≤ E := by
    intro z hz d hdmem hDd
    obtain ⟨-, hzin⟩ := mem_polarBoxFinset.mp hz
    have hnle : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hzin.2.2.1
    have hnpos : (0:ℝ) < Work.FIPlan.gnorm z := by have := hzin.2.1; linarith [hN1]
    have hdvd : d ∣ Work.FIPlan.gnorm z := (Nat.mem_divisors.mp hdmem).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hdmem
    have hdD : u ^ 2 < (d:ℝ) := by
      have h2 : (D:ℝ) < (d:ℝ) := by exact_mod_cast hDd
      linarith [hDceil]
    have hcast : ((Work.FIPlan.gnorm z / d : ℕ):ℝ) = (Work.FIPlan.gnorm z : ℝ)/(d:ℝ) :=
      Nat.cast_div hdvd (by positivity)
    have h1 : (Work.FIPlan.gnorm z : ℝ)/(d:ℝ) < (Work.FIPlan.gnorm z : ℝ)/u^2 :=
      div_lt_div_of_pos_left hnpos hu2pos hdD
    have h2 : (Work.FIPlan.gnorm z : ℝ)/u^2 ≤ (1 + Pa.θ)/Pa.θ^2 := by
      rw [hu2]
      field_simp
      nlinarith [hnle, sq_nonneg Pa.θ, hθ0]
    have hlt : ((Work.FIPlan.gnorm z / d : ℕ):ℝ) < (E:ℝ) := by
      rw [hcast]; linarith [h1, h2, hEceil]
    exact le_of_lt (by exact_mod_cast hlt)
  -- § the sum chain
  set B : Finset GaussianInt := polarBoxFinset Pa φ with hBdef
  have hpoint : ∀ z ∈ B, ((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤
      (∑ d ∈ Finset.Icc 1 D, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0)) +
      (∑ m ∈ Finset.Icc 1 E, (if m ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0)) :=
    fun z hz => card_divisors_le_two_Icc_indicator (Work.FIPlan.gnorm z) D E (hcof z hz)
  have hcard1 : ∀ d : ℕ,
      (∑ z ∈ B, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))
        = ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
    intro d
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : d ∣ Work.FIPlan.gnorm z <;> simp [h]
  have hS : (∑ z ∈ B, ((Work.FIPlan.gnorm z).divisors.card : ℝ))
      ≤ (∑ d ∈ Finset.Icc 1 D, ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ))
        + (∑ m ∈ Finset.Icc 1 E, ((B.filter (fun z => m ∣ Work.FIPlan.gnorm z)).card : ℝ)) := by
    calc (∑ z ∈ B, ((Work.FIPlan.gnorm z).divisors.card : ℝ))
        ≤ ∑ z ∈ B, ((∑ d ∈ Finset.Icc 1 D, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))
            + (∑ m ∈ Finset.Icc 1 E, (if m ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))) :=
          Finset.sum_le_sum hpoint
      _ = (∑ z ∈ B, ∑ d ∈ Finset.Icc 1 D, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))
            + (∑ z ∈ B, ∑ m ∈ Finset.Icc 1 E, (if m ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0)) :=
          Finset.sum_add_distrib
      _ = (∑ d ∈ Finset.Icc 1 D, ∑ z ∈ B, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))
            + (∑ m ∈ Finset.Icc 1 E, ∑ z ∈ B, (if m ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0)) := by
          have hp : (∑ z ∈ B, ∑ d ∈ Finset.Icc 1 D, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))
              = (∑ d ∈ Finset.Icc 1 D, ∑ z ∈ B, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0)) :=
            Finset.sum_comm
          have hq : (∑ z ∈ B, ∑ m ∈ Finset.Icc 1 E, (if m ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0))
              = (∑ m ∈ Finset.Icc 1 E, ∑ z ∈ B, (if m ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0)) :=
            Finset.sum_comm
          rw [hp, hq]
      _ = (∑ d ∈ Finset.Icc 1 D, ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ))
            + (∑ m ∈ Finset.Icc 1 E, ((B.filter (fun z => m ∣ Work.FIPlan.gnorm z)).card : ℝ)) := by
          rw [Finset.sum_congr rfl (fun d _ => hcard1 d),
            Finset.sum_congr rfl (fun m _ => hcard1 m)]
  -- § the count bound per range
  have hcountL : ∀ d ∈ Finset.Icc 1 D,
      ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ Real.pi * u^2 * ((d.divisors.card : ℝ)/(d:ℝ))
        + 80*u*((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)) + (d.divisors.card : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have h := card_polarBox_filter_dvd_gnorm Pa φ d hd1
    rw [← hBdef, ← hu] at h
    exact h
  have hcountE : ∀ d ∈ Finset.Icc 1 E,
      ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ Real.pi * u^2 * ((d.divisors.card : ℝ)/(d:ℝ))
        + 80*u*((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)) + (d.divisors.card : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have h := card_polarBox_filter_dvd_gnorm Pa φ d hd1
    rw [← hBdef, ← hu] at h
    exact h
  have hT1 : (∑ d ∈ Finset.Icc 1 D, ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ))
      ≤ Real.pi * u^2 * (1 + Real.log (D:ℝ))^2
        + 80*u*(4*Real.sqrt (D:ℝ)*(1 + Real.log (D:ℝ)))
        + (D:ℝ)*(1 + Real.log (D:ℝ)) := by
    calc (∑ d ∈ Finset.Icc 1 D, ((B.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, (Real.pi * u^2 * ((d.divisors.card : ℝ)/(d:ℝ))
            + 80*u*((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)) + (d.divisors.card : ℝ)) :=
          Finset.sum_le_sum hcountL
      _ = Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)/(d:ℝ)))
            + 80*u*(∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)))
            + (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ Real.pi * u^2 * (1 + Real.log (D:ℝ))^2
            + 80*u*(4*Real.sqrt (D:ℝ)*(1 + Real.log (D:ℝ)))
            + (D:ℝ)*(1 + Real.log (D:ℝ)) := by
          have hb1 : Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)/(d:ℝ)))
              ≤ Real.pi * u^2 * (1 + Real.log (D:ℝ))^2 :=
            mul_le_mul_of_nonneg_left (sum_divisors_div_Icc_le D) (by positivity)
          have hb2 : 80*u*(∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)))
              ≤ 80*u*(4*Real.sqrt (D:ℝ)*(1 + Real.log (D:ℝ))) :=
            mul_le_mul_of_nonneg_left (sum_divisors_div_sqrt_Icc_le D) (by positivity)
          have hb3 := sum_divisors_Icc_le D
          linarith [hb1, hb2, hb3]
  have hT2 : (∑ m ∈ Finset.Icc 1 E, ((B.filter (fun z => m ∣ Work.FIPlan.gnorm z)).card : ℝ))
      ≤ Real.pi * u^2 * (1 + Real.log (E:ℝ))^2
        + 80*u*(4*Real.sqrt (E:ℝ)*(1 + Real.log (E:ℝ)))
        + (E:ℝ)*(1 + Real.log (E:ℝ)) := by
    calc (∑ m ∈ Finset.Icc 1 E, ((B.filter (fun z => m ∣ Work.FIPlan.gnorm z)).card : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 E, (Real.pi * u^2 * ((m.divisors.card : ℝ)/(m:ℝ))
            + 80*u*((m.divisors.card : ℝ)/Real.sqrt (m:ℝ)) + (m.divisors.card : ℝ)) :=
          Finset.sum_le_sum hcountE
      _ = Real.pi * u^2 * (∑ m ∈ Finset.Icc 1 E, ((m.divisors.card : ℝ)/(m:ℝ)))
            + 80*u*(∑ m ∈ Finset.Icc 1 E, ((m.divisors.card : ℝ)/Real.sqrt (m:ℝ)))
            + (∑ m ∈ Finset.Icc 1 E, ((m.divisors.card : ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ Real.pi * u^2 * (1 + Real.log (E:ℝ))^2
            + 80*u*(4*Real.sqrt (E:ℝ)*(1 + Real.log (E:ℝ)))
            + (E:ℝ)*(1 + Real.log (E:ℝ)) := by
          have hb1 : Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 E, ((d.divisors.card : ℝ)/(d:ℝ)))
              ≤ Real.pi * u^2 * (1 + Real.log (E:ℝ))^2 :=
            mul_le_mul_of_nonneg_left (sum_divisors_div_Icc_le E) (by positivity)
          have hb2 : 80*u*(∑ d ∈ Finset.Icc 1 E, ((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)))
              ≤ 80*u*(4*Real.sqrt (E:ℝ)*(1 + Real.log (E:ℝ))) :=
            mul_le_mul_of_nonneg_left (sum_divisors_div_sqrt_Icc_le E) (by positivity)
          have hb3 := sum_divisors_Icc_le E
          linarith [hb1, hb2, hb3]
  -- § final arithmetic
  have hbound1 : Real.pi * u^2 * (1 + Real.log (D:ℝ))^2
        + 80*u*(4*Real.sqrt (D:ℝ)*(1 + Real.log (D:ℝ)))
        + (D:ℝ)*(1 + Real.log (D:ℝ)) ≤ 2000 * u^2 * L^2 := by
    have h1 : Real.pi * u^2 * (1 + Real.log (D:ℝ))^2 ≤ Real.pi * u^2 * (2*L)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hlogD2, hlogD0, hL1]
    have h2 : 80*u*(4*Real.sqrt (D:ℝ)*(1 + Real.log (D:ℝ))) ≤ 80*u*(4*(2*u)*(2*L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hsqrtD, hlogD2, hlogD0, hL1, Real.sqrt_nonneg (D:ℝ), hu_pos]
    have h3 : (D:ℝ)*(1 + Real.log (D:ℝ)) ≤ (2*u^2)*(2*L) := by
      apply mul_le_mul hDle hlogD2 (by linarith [hlogD0]) (by positivity)
    have h4 : Real.pi * u^2 * (2*L)^2 ≤ Real.pi * u^2 * (4*L^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have h5 : 80*u*(4*(2*u)*(2*L)) ≤ 1280 * u^2 * L^2 := by
      nlinarith [hu_ge1, hL1, sq_nonneg u, sq_nonneg L]
    have h6 : (2*u^2)*(2*L) ≤ 4 * u^2 * L^2 := by nlinarith [hu_ge1, hL1, sq_nonneg u]
    have hπ := Real.pi_lt_four.le
    nlinarith [h1, h2, h3, h4, h5, h6, hu_ge1, hL1, sq_nonneg u, sq_nonneg L]
  have hbound2 : Real.pi * u^2 * (1 + Real.log (E:ℝ))^2
        + 80*u*(4*Real.sqrt (E:ℝ)*(1 + Real.log (E:ℝ)))
        + (E:ℝ)*(1 + Real.log (E:ℝ)) ≤ 3000 * u^2 * L^2 := by
    have h1 : Real.pi * u^2 * (1 + Real.log (E:ℝ))^2 ≤ Real.pi * u^2 * (4*L)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hlogE2, hlogE0, hL1]
    have h2 : 80*u*(4*Real.sqrt (E:ℝ)*(1 + Real.log (E:ℝ))) ≤ 80*u*(4*(2/Pa.θ)*(4*L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hsqrtE, hlogE2, hlogE0, hL1, Real.sqrt_nonneg (E:ℝ), hθ0]
    have h2b : 80*u*(4*(2/Pa.θ)*(4*L)) = 2560 * ((u/Pa.θ) * L) := by field_simp; ring
    have h2c : (u/Pa.θ) * L = Real.sqrt Pa.N * L := by rw [hu_div_θ]
    have h3 : (E:ℝ)*(1 + Real.log (E:ℝ)) ≤ (4/Pa.θ^2)*(4*L) := by
      apply mul_le_mul hEle hlogE2 (by linarith [hlogE0]) (by positivity)
    have h4 : Real.pi * u^2 * (4*L)^2 ≤ Real.pi * u^2 * (16*L^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have h5 : 80*u*(4*(2/Pa.θ)*(4*L)) ≤ 2560 * u^2 * L^2 := by
      rw [h2b, h2c]
      have h := hsqrtN_le_u2L
      have hh : Real.sqrt Pa.N * L ≤ (u^2*L)*L := mul_le_mul_of_nonneg_right h hL0
      nlinarith [hh, sq_nonneg u, hL1]
    have h6 : (4/Pa.θ^2)*(4*L) ≤ 16 * u^2 * L^2 := by
      have h : 1/Pa.θ^2 ≤ u^2 * L := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hone_le_θ2u2, hL1, sq_nonneg u]
      have hh : (1/Pa.θ^2) * L ≤ (u^2*L) * L := mul_le_mul_of_nonneg_right h hL0
      calc (4/Pa.θ^2)*(4*L) = 16 * ((1/Pa.θ^2)*L) := by ring
        _ ≤ 16 * ((u^2*L)*L) := by linarith [hh]
        _ = 16 * u^2 * L^2 := by ring
    have hπ := Real.pi_lt_four.le
    have hA1 : Real.pi * u^2 * (1 + Real.log (E:ℝ))^2 ≤ 16 * Real.pi * (u^2 * L^2) := by
      nlinarith [h1, h4]
    have hA2 : 80*u*(4*Real.sqrt (E:ℝ)*(1 + Real.log (E:ℝ))) ≤ 2560 * (u^2 * L^2) := by
      nlinarith [h2, h5]
    have hA3 : (E:ℝ)*(1 + Real.log (E:ℝ)) ≤ 16 * (u^2 * L^2) := by
      nlinarith [h3, h6]
    have huL2 : (0:ℝ) ≤ u^2*L^2 := by positivity
    nlinarith [hA1, hA2, hA3, hπ, huL2]
  -- § assemble
  have hfinal : (∑ z ∈ B, ((Work.FIPlan.gnorm z).divisors.card : ℝ))
      ≤ 100000 * (u^2 + u + 1) * L^2 := by
    have h1 : (∑ z ∈ B, ((Work.FIPlan.gnorm z).divisors.card : ℝ)) ≤ 5000 * u^2 * L^2 := by
      linarith [hS, hT1, hT2, hbound1, hbound2]
    nlinarith [h1, hu_ge1, hL0, sq_nonneg u, sq_nonneg L]
  rw [hBdef] at hfinal
  have hconv : (Pa.θ ^ 2 * Pa.N + u + 1) = u^2 + u + 1 := by rw [← hu2]
  rw [hBdef, hconv]
  exact hfinal

end
end Work.FIArea3
