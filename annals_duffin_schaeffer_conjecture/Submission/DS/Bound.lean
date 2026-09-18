import Submission.DS.Inclusion
import Submission.DS.Totient
import Submission.DS.Summability

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

namespace Submission.DS

lemma Cq_eq_biUnion_interval (ρ : ℕ+ → ℝ≥0) (q : ℕ+) :
    Cq ρ q = ⋃ a ∈ (Finset.Icc 0 (q : ℕ)).filter (fun a => Nat.Coprime a (q : ℕ)),
      {x : ℝ | |x - (a : ℝ) / (q : ℝ)| ≤ (ρ q : ℝ)} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨a, hle, hcop, hb⟩
    exact mem_iUnion₂.mpr ⟨a,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le a, hle⟩, hcop⟩, hb⟩
  · intro hx
    rcases mem_iUnion₂.mp hx with ⟨a, ha, hb⟩
    have ha' : a ≤ (q : ℕ) ∧ Nat.Coprime a (q : ℕ) := by simpa using ha
    exact ⟨a, ha'.1, ha'.2, hb⟩

lemma ofReal_two_mul (r : ℝ≥0) : ENNReal.ofReal (2 * (r : ℝ)) = (2 : ℝ≥0∞) * (r : ℝ≥0∞) := by
  have hnn : (2 : ℝ) * (r : ℝ) = (((2 : ℝ≥0) * r : ℝ≥0) : ℝ) := by
    norm_num [NNReal.coe_mul]
  rw [hnn, ENNReal.ofReal_coe_nnreal]
  rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num]
  rw [← ENNReal.coe_mul]

lemma phi_ge_one_R (q : ℕ+) : (1 : ℝ≥0) ≤ (φ q : ℝ≥0) := by
  have hφ0 : 1 ≤ φ (q : ℕ) := by
    have h := totient_pos_pnat q
    omega
  exact_mod_cast hφ0

lemma nn_ineq (q : ℕ+) (ρ : ℝ≥0) : ((φ q : ℝ≥0) + 1) * (2 * ρ) ≤ (4 : ℝ≥0) * ((φ q : ℝ≥0) * ρ) := by
  have hφ := phi_ge_one_R q
  nlinarith

lemma measure_Cq_inter_Icc_le (ψ : ℕ+ → ℝ≥0) (hψ : Conv ψ) (q : ℕ+) :
    volume (Cq (rho ψ) q ∩ Set.Icc 0 1) ≤ (4 : ℝ≥0∞) * ψ_star ψ q := by
  let I : Finset ℕ := (Finset.Icc 0 (q : ℕ)).filter (fun a => Nat.Coprime a (q : ℕ))
  have hcard : I.card ≤ φ q + 1 := by
    simpa [I, Nat.coprime_comm] using (card_coprime_Icc_zero_le q)
  have hident : Cq (rho ψ) q ∩ Set.Icc 0 1 =
      (⋃ a ∈ I, ({x : ℝ | |x - (a : ℝ) / (q : ℝ)| ≤ ((rho ψ q) : ℝ)} : Set ℝ)) ∩ Set.Icc 0 1 := by
    rw [Cq_eq_biUnion_interval (rho ψ) q]
  have hvol := volume_biUnion_interval_le I (fun a : ℕ => (a : ℝ) / (q : ℝ)) (rho ψ q)
  have hb1 : volume (Cq (rho ψ) q ∩ Set.Icc 0 1) ≤
      (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * ((rho ψ q) : ℝ)) := by
    rw [hident]
    exact hvol
  have hb2 : (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * ((rho ψ q) : ℝ)) ≤
      (((φ q + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (2 * ((rho ψ q) : ℝ)) := by
    exact mul_le_mul' (by exact_mod_cast hcard) le_rfl
  have hb3 : (((φ q + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (2 * ((rho ψ q) : ℝ)) ≤
      (4 : ℝ≥0∞) * ((φ q : ℝ≥0) * rho ψ q : ℝ≥0∞) := by
    rw [ofReal_two_mul]
    rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num,
      show (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) by norm_num,
      show (((φ q + 1 : ℕ) : ℝ≥0∞)) = ((((φ q + 1 : ℕ) : ℝ≥0) : ℝ≥0∞)) by norm_num]
    simp only [← ENNReal.coe_mul]
    rw [ENNReal.coe_le_coe]
    convert nn_ineq q (rho ψ q) using 1 <;> norm_num
  calc
    volume (Cq (rho ψ) q ∩ Set.Icc 0 1) ≤
        (((φ q + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (2 * ((rho ψ q) : ℝ)) := hb1.trans hb2
    _ ≤ (4 : ℝ≥0∞) * ((φ q : ℝ≥0) * rho ψ q : ℝ≥0∞) := hb3
    _ ≤ (4 : ℝ≥0∞) * ψ_star ψ q := by
      rw [psiStar_eq_coe hψ q]
      rfl

end Submission.DS
