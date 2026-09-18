import Submission.DS.Context
open scoped Nat ENNReal NNReal
open DuffinSchaefferConjecture

/-!
# Summability consequences of the convergence hypothesis

Throughout, `ψ : ℕ+ → ℝ≥0` and we assume `Conv ψ`, i.e. `∑' q, ψ_star ψ q < ∞`.
We define the NNReal versions of the sup-radius `rho` and of `ψ_star` and derive
finiteness and term-vanishing statements.
-/

namespace Submission.DS

/-- Real-valued (NNReal) version of the sup-radius: `ENNReal.toNNReal (rad ψ q)`. -/
noncomputable def rho (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0 := ENNReal.toNNReal (rad ψ q)

/-- NNReal version of `ψ_star ψ q = φ(q) * rho ψ q`. -/
noncomputable def psiStarNN (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0 := (φ q : ℝ≥0) * rho ψ q

section Conv

variable {ψ : ℕ+ → ℝ≥0}

/-- `Conv ψ` : the series `∑' q, ψ_star ψ q` converges (has finite sum). -/
def Conv (ψ : ℕ+ → ℝ≥0) : Prop := (∑' q : ℕ+, ψ_star ψ q) < ∞

lemma psiStar_lt_top (hψ : Conv ψ) (q : ℕ+) : ψ_star ψ q < ∞ := by
  exact lt_of_le_of_lt (ENNReal.le_tsum q) hψ

lemma rad_lt_top (hψ : Conv ψ) (q : ℕ+) : rad ψ q < ∞ := by
  exact lt_of_le_of_lt (rad_le_psiStar ψ q) (psiStar_lt_top hψ q)

lemma rho_spec (hψ : Conv ψ) (q : ℕ+) : (rho ψ q : ℝ≥0∞) = rad ψ q := by
  simpa [rho] using ENNReal.coe_toNNReal (ne_of_lt (rad_lt_top hψ q))

/-- `ψ(q)/q ≤ rho q`. -/
lemma self_le_rho (hψ : Conv ψ) (q : ℕ+) : (ψ q / q : ℝ≥0) ≤ rho ψ q := by
  exact ENNReal.coe_le_coe.mp (by
    rw [rho_spec hψ q]
    exact rad_ge_self ψ q)

/-- If `q' ∣ q` then `ψ(q)/q` is one of the numbers whose sup defines `rad q'`. -/
lemma rad_ge_of_dvd (q' q : ℕ+) (hdiv : q' ∣ q) :
    ((ψ q / q : ℝ≥0) : ℝ≥0∞) ≤ rad ψ q' := by
  have hq0 : (q : ℝ≥0) ≠ 0 := by
    intro h
    apply (PNat.ne_zero q)
    exact_mod_cast congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  rw [coe_div_ne_zero (ψ q) (q : ℝ≥0) hq0]
  unfold rad
  exact le_sSup ⟨q, hdiv, rfl⟩

/-- If `q' ∣ q` then `ψ(q)/q ≤ rho q'`. -/
lemma self_le_rho_of_dvd (hψ : Conv ψ) (q' q : ℕ+) (hdiv : q' ∣ q) :
    (ψ q / q : ℝ≥0) ≤ rho ψ q' := by
  exact ENNReal.coe_le_coe.mp (by
    rw [rho_spec hψ q']
    exact rad_ge_of_dvd q' q hdiv)

lemma psiStar_eq_coe (hψ : Conv ψ) (q : ℕ+) :
    ψ_star ψ q = (psiStarNN ψ q : ℝ≥0∞) := by
  calc
    ψ_star ψ q = (φ q : ℝ≥0∞) * rad ψ q := psiStar_eq_phi_mul_rad ψ q
    _ = (φ q : ℝ≥0∞) * (rho ψ q : ℝ≥0∞) := by rw [rho_spec hψ q]
    _ = (psiStarNN ψ q : ℝ≥0∞) := by
      unfold psiStarNN
      rw [ENNReal.coe_mul]
      norm_num

lemma psiStar_coe_tsum (hψ : Conv ψ) :
    (∑' q : ℕ+, ψ_star ψ q) = (∑' q : ℕ+, (psiStarNN ψ q : ℝ≥0∞)) := by
  exact tsum_congr (fun q => psiStar_eq_coe hψ q)

lemma summable_psiStarNN (hψ : Conv ψ) : Summable (psiStarNN ψ) := by
  have hne : (∑' q : ℕ+, (psiStarNN ψ q : ℝ≥0∞)) ≠ ∞ := by
    rw [← psiStar_coe_tsum hψ]
    exact ne_of_lt hψ
  exact ENNReal.tsum_coe_ne_top_iff_summable.mp hne

lemma rho_le_psiStarNN (hψ : Conv ψ) (q : ℕ+) : rho ψ q ≤ psiStarNN ψ q := by
  have hphi1 : (1 : ℝ≥0) ≤ (φ q : ℝ≥0) := by
    have h : 1 ≤ φ (q : ℕ) := by
      have h0 : 0 < φ (q : ℕ) := (Nat.totient_pos).mpr (by exact_mod_cast q.2 : 0 < (q : ℕ))
      omega
    exact_mod_cast h
  unfold psiStarNN
  calc
    rho ψ q = (1 : ℝ≥0) * rho ψ q := by simp
    _ ≤ (φ q : ℝ≥0) * rho ψ q := by gcongr

/-- NNReal term vanishing: only finitely many `q` have `psiStarNN ψ q ≥ e`. -/
lemma finite_above_psiStarNN (hψ : Conv ψ) :
    ∀ e : ℝ≥0, 0 < e → {q : ℕ+ | e ≤ psiStarNN ψ q}.Finite := by
  intro e he
  have hne : (∑' q : ℕ+, (psiStarNN ψ q : ℝ≥0∞)) ≠ ∞ := by
    rw [← psiStar_coe_tsum hψ]
    exact ne_of_lt hψ
  have he0 : (e : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt he)
  have hfin : {q : ℕ+ | (e : ℝ≥0∞) ≤ (psiStarNN ψ q : ℝ≥0∞)}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hne he0
  exact hfin.subset (by intro q hq; exact ENNReal.coe_le_coe.mpr hq)

/-- Term vanishing for the real values `ψ(q)/q`. -/
lemma finite_above_self (hψ : Conv ψ) :
    ∀ ε : ℝ, 0 < ε → {q : ℕ+ | ε ≤ ((ψ q / q : ℝ≥0) : ℝ)}.Finite := by
  intro ε hε
  let e : ℝ≥0 := ⟨ε, le_of_lt hε⟩
  have he0 : 0 < e := by
    exact NNReal.coe_lt_coe.mp (by change (0 : ℝ) < (⟨ε, le_of_lt hε⟩ : ℝ≥0); exact hε)
  have hfin : {q : ℕ+ | e ≤ psiStarNN ψ q}.Finite := finite_above_psiStarNN hψ e he0
  refine hfin.subset ?_
  intro q hq
  have hqle : (ψ q / q : ℝ≥0) ≤ psiStarNN ψ q :=
    le_trans (self_le_rho hψ q) (rho_le_psiStarNN hψ q)
  have hqR : ε ≤ (psiStarNN ψ q : ℝ) :=
    le_trans hq (NNReal.coe_le_coe.mpr hqle)
  exact NNReal.coe_le_coe.mp (by
    change ε ≤ (psiStarNN ψ q : ℝ)
    exact hqR)

end Conv

end Submission.DS
