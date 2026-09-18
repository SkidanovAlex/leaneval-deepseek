import Submission.DS.TruncDiv
import Submission.DS.Measure
import Submission.DS.Structure

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

/-!
# Case 2 of Theorem 2(b), assuming Theorem 1 (paper §2)

Assume `ψ ≤ 1/2` and `∑ ψ* = ∞`.  Following Catlin / the paper's §2 we set
`m(q) = sup {ψ(n)/n : q ∣ n}` and `ξ(q) = q·m(q)`, i.e. `ξ(q)/q = m(q)`.  Then
`∑ φ(q)·m(q) = ∑ ψ*(q) = ∞`, so Theorem 1 applied to `ξ` yields full measure for the
coprime-reduced limsup `𝒜 ξ`; the inclusion `𝒜 ξ ∖ ℚ ⊆ 𝒦 ψ` transfers full measure
to `𝒦 ψ`.
-/

namespace Submission.DS

variable {ψ : ℕ+ → ℝ≥0}

section xi

/-- The finite NNReal sup-radius: `(rad ψ q).toNNReal`. -/
noncomputable def mRho (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0 := (rad ψ q).toNNReal

/-- Catlin's `ξ(q) = q · m(q)`, so that `ξ(q)/q = m(q) = sup {ψ(n)/n : q ∣ n}`. -/
noncomputable def xi (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0 := (q : ℝ≥0) * mRho ψ q

/-- ENNReal: `a / n ≤ a` for `n ≥ 1`. -/
lemma en_div_le_self (a : NNReal) (n : ℕ+) :
    (a : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (a : ℝ≥0∞) := by
  apply ENNReal.div_le_of_le_mul
  calc
    (a : ℝ≥0∞) = (a : ℝ≥0∞) * 1 := by simp
    _ ≤ (a : ℝ≥0∞) * (n : ℝ≥0∞) := by
      exact mul_le_mul' le_rfl (by exact_mod_cast (show 1 ≤ (n : ℕ) from n.2))

/-- If `ψ ≤ 1/2` then `rad ψ q` is finite. -/
lemma rad_lt_top_of_le_half (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    rad ψ q < ∞ := by
  have hval : ∀ n : ℕ+, q ∣ n → (ψ n : ℝ≥0∞) / (n : ℝ≥0∞) ≤ ((1 / 2 : NNReal) : ℝ≥0∞) := by
    intro n hdvd
    have h1 : (ψ n : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (ψ n : ℝ≥0∞) := en_div_le_self (ψ n) n
    have h2 : (ψ n : ℝ≥0∞) ≤ ((1 / 2 : NNReal) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (hle n)
    exact le_trans h1 h2
  have hle' : rad ψ q ≤ ((1 / 2 : NNReal) : ℝ≥0∞) := by
    unfold rad
    apply sSup_le
    intro y hy
    rcases hy with ⟨n, hdvd, hrfl⟩
    rw [hrfl]
    exact hval n hdvd
  exact lt_of_le_of_lt hle' ENNReal.coe_lt_top

/-- `rad ψ q` equals the coercion of `mRho ψ q`. -/
lemma rad_eq_coe_mRho (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    rad ψ q = (mRho ψ q : ℝ≥0∞) := by
  exact (ENNReal.coe_toNNReal (ne_of_lt (rad_lt_top_of_le_half hle q))).symm

/-- `ξ(q)/q = mRho(q)` in NNReal. -/
lemma xi_div_self (q : ℕ+) : (xi ψ q / q : NNReal) = mRho ψ q := by
  unfold xi
  have hq0 : (q : NNReal) ≠ 0 := by exact_mod_cast (PNat.ne_zero q)
  field_simp [hq0]

/-- `(ξ(q)·φ(q))/q = φ(q)·mRho(q)` in NNReal. -/
lemma xi_mul_phi_div (q : ℕ+) :
    (xi ψ q * (φ q : NNReal)) / q = (φ q : NNReal) * mRho ψ q := by
  unfold xi
  have hq0 : (q : NNReal) ≠ 0 := by exact_mod_cast (PNat.ne_zero q)
  field_simp [hq0]

/-- `ψ*(q)` equals the coercion of `φ(q)·mRho(q)`. -/
lemma psiStar_eq_phi_mRho (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    ψ_star ψ q = (φ q : ℝ≥0∞) * (mRho ψ q : ℝ≥0∞) := by
  rw [psiStar_eq_phi_mul_rad, rad_eq_coe_mRho hle q]

/-- The φ-coefficient: `(φ(q):NNReal:∞) = (φ q : ∞)`. -/
lemma phi_coe_natCast (q : ℕ+) : ((φ q : NNReal) : ℝ≥0∞) = (φ q : ℝ≥0∞) := by
  simp [ENNReal.coe_natCast]

/-- Values `ψ(n)/n` for multiples `q ∣ n` are at most `(1/2)/q`. -/
lemma rad_le_half_div (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    rad ψ q ≤ ((1 / 2 : NNReal) : ℝ≥0∞) / (q : ℝ≥0∞) := by
  have hval : ∀ n : ℕ+, q ∣ n → (ψ n : ℝ≥0∞) / (n : ℝ≥0∞) ≤
      ((1 / 2 : NNReal) : ℝ≥0∞) / (q : ℝ≥0∞) := by
    intro n hdvd
    have hnq : (q : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      exact_mod_cast (Nat.le_of_dvd n.2 ((PNat.dvd_iff).mp hdvd))
    have hle12 : (ψ n : ℝ≥0∞) ≤ ((1 / 2 : NNReal) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (hle n)
    exact ENNReal.div_le_div hle12 hnq
  unfold rad
  apply sSup_le
  intro y hy
  rcases hy with ⟨n, hdvd, hrfl⟩
  rw [hrfl]
  exact hval n hdvd

/-- `mRho(q) ≤ (1/2)/q`. -/
lemma mRho_le_half_div (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    mRho ψ q ≤ (1 / 2 : NNReal) / q := by
  have hle' := rad_le_half_div hle q
  have hb_fin : ((1 / 2 : NNReal) : ℝ≥0∞) / (q : ℝ≥0∞) ≠ ⊤ := by
    exact ne_of_lt (ENNReal.div_lt_top (by exact ENNReal.coe_ne_top)
      (by exact_mod_cast (PNat.ne_zero q) : (q : ℝ≥0∞) ≠ 0))
  have hm : mRho ψ q ≤ (((1 / 2 : NNReal) : ℝ≥0∞) / (q : ℝ≥0∞)).toNNReal := by
    exact (ENNReal.toNNReal_le_toNNReal (ne_of_lt (rad_lt_top_of_le_half hle q)) hb_fin).mpr hle'
  have hB : ((1 / 2 : NNReal) : ℝ≥0∞) / (q : ℝ≥0∞) =
      (((1 / 2 : NNReal) / q : NNReal) : ℝ≥0∞) := by
    rw [show (q : ℝ≥0∞) = ((q : NNReal) : ℝ≥0∞) by simp [ENNReal.coe_natCast]]
    exact (ENNReal.coe_div (p := (1 / 2 : NNReal)) (r := (q : NNReal))
      (by exact_mod_cast (PNat.ne_zero q) : (q : NNReal) ≠ 0)).symm
  have hB' : ((((1 / 2 : NNReal) / q : NNReal) : ℝ≥0∞).toNNReal) = (1 / 2 : NNReal) / q := by
    exact ENNReal.toNNReal_coe ((1 / 2 : NNReal) / q)
  have hm' : mRho ψ q ≤ (1 / 2 : NNReal) / q := by
    rw [hB] at hm
    rwa [hB'] at hm
  exact hm'

/-- `ξ(q) ≤ 1/2` under `ψ ≤ 1/2`. -/
lemma xi_le_half (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) : xi ψ q ≤ 1 / 2 := by
  have hq0 : (q : NNReal) ≠ 0 := by exact_mod_cast (PNat.ne_zero q)
  have h1 : xi ψ q ≤ (q : NNReal) * ((1 / 2 : NNReal) / q) := by
    unfold xi
    exact mul_le_mul_of_nonneg_left (mRho_le_half_div hle q) (by positivity : (0 : NNReal) ≤ (q : NNReal))
  have h2 : (q : NNReal) * ((1 / 2 : NNReal) / q) = 1 / 2 := by
    field_simp [hq0]
  rwa [h2] at h1

/-- Divergence of `∑ ψ*` gives non-summability of `∑ φ(q)·mRho(q)`. -/
lemma not_summable_phi_m (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0))
    (hψ : (∑' q : ℕ+, ψ_star ψ q) = ∞) :
    ¬ Summable (fun q : ℕ+ => (φ q : NNReal) * mRho ψ q) := by
  intro hsum
  have hne : (∑' q : ℕ+, (((φ q : NNReal) * mRho ψ q) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hsum
  have hTop' : (∑' q : ℕ+, (φ q : ℝ≥0∞) * (mRho ψ q : ℝ≥0∞)) = ⊤ := by
    calc
      (∑' q : ℕ+, (φ q : ℝ≥0∞) * (mRho ψ q : ℝ≥0∞)) = (∑' q : ℕ+, ψ_star ψ q) := by
        exact tsum_congr (fun q => (psiStar_eq_phi_mRho hle q).symm)
      _ = ⊤ := hψ
  have hterm : ∀ q : ℕ+, (((φ q : NNReal) * mRho ψ q) : ℝ≥0∞) =
      (φ q : ℝ≥0∞) * (mRho ψ q : ℝ≥0∞) := by
    intro q
    simp [ENNReal.coe_natCast]
  have hTop : (∑' q : ℕ+, (((φ q : NNReal) * mRho ψ q) : ℝ≥0∞)) = ⊤ := by
    calc
      (∑' q : ℕ+, (((φ q : NNReal) * mRho ψ q) : ℝ≥0∞)) =
          (∑' q : ℕ+, (φ q : ℝ≥0∞) * (mRho ψ q : ℝ≥0∞)) := by
        exact tsum_congr hterm
      _ = ⊤ := hTop'
  exact hne hTop

/-- Non-summability transfers from `φ·mRho` to `(ξ·φ)/q`. -/
lemma not_summable_xi (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0))
    (hψ : (∑' q : ℕ+, ψ_star ψ q) = ∞) :
    ¬ Summable (fun q : ℕ+ => (xi ψ q * (φ q : NNReal)) / q) := by
  have hnm := not_summable_phi_m (ψ := ψ) hle hψ
  intro hxi
  apply hnm
  convert hxi using 1
  funext q
  exact (xi_mul_phi_div q).symm

end xi

end Submission.DS
