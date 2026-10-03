import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.fibre_associated_of_norm_coprime
import Submission.Commons.NumberTheory.GaussianInt.factor_exists_of_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.ncard_units
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

/-- **Every Gaussian integer of norm `m * n`, with `m`, `n` coprime, has exactly four
ordered factorisations `u = p * q` with `‖p‖ = m` and `‖q‖ = n`.**

Indeed, once one such factorisation `u = w * z` exists (see
`factor_exists_of_norm_mul`), any other solution `(p, q)` satisfies `p = w * ε`,
`q = ε⁻¹ * z` for a unit `ε` (`fibre_associated_of_norm_coprime`), and the four units
of `ℤ[i]` produce four distinct solutions. -/
theorem ncard_factor_set_eq_four {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (u : GaussianInt) (hu : u.norm.natAbs = m * n) :
    ({p : GaussianInt × GaussianInt | p.1.norm.natAbs = m ∧ p.2.norm.natAbs = n ∧
        p.1 * p.2 = u}).ncard = 4 := by
  classical
  obtain ⟨w, z, hwz, hw, hz⟩ := factor_exists_of_norm_mul hm hn hcop u hu
  have hwzu : w * z = u := hwz.symm
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; omega
  let S : Set (GaussianInt × GaussianInt) :=
    {p | p.1.norm.natAbs = m ∧ p.2.norm.natAbs = n ∧ p.1 * p.2 = u}
  let T : Set GaussianInt := {y | IsUnit y}
  have hST : S.ncard = T.ncard := by
    refine Set.ncard_congr
      (fun p _ => (if h : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = p.1 then
        ↑(Classical.choose h) else (0 : GaussianInt) : GaussianInt)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      have hwit : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = p.1 :=
        (fibre_associated_of_norm_coprime hcop hp1 hw hp2 hz (by rw [hp3, hwzu])).symm
      change IsUnit (if h : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = p.1 then
        ↑(Classical.choose h) else (0 : GaussianInt))
      rw [dif_pos hwit]
      exact (Classical.choose hwit).isUnit
    · intro p q hp hq heq
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      have hhp : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = p.1 :=
        (fibre_associated_of_norm_coprime hcop hp1 hw hp2 hz (by rw [hp3, hwzu])).symm
      have hhq : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = q.1 :=
        (fibre_associated_of_norm_coprime hcop hq1 hw hq2 hz (by rw [hq3, hwzu])).symm
      have heq' : (↑(Classical.choose hhp) : GaussianInt) = ↑(Classical.choose hhq) := by
        have e1 : (if h : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = p.1 then
            ↑(Classical.choose h) else (0 : GaussianInt)) = ↑(Classical.choose hhp) := dif_pos hhp
        have e2 : (if h : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = q.1 then
            ↑(Classical.choose h) else (0 : GaussianInt)) = ↑(Classical.choose hhq) := dif_pos hhq
        rw [e1, e2] at heq
        exact heq
      have huv : Classical.choose hhp = Classical.choose hhq := Units.ext heq'
      have hp1' : w * (↑(Classical.choose hhp) : GaussianInt) = p.1 := Classical.choose_spec hhp
      have hq1' : w * (↑(Classical.choose hhq) : GaussianInt) = q.1 := Classical.choose_spec hhq
      have hp2' : p.2 = (↑((Classical.choose hhp)⁻¹) : GaussianInt) * z := by
        have h2 : (↑(Classical.choose hhp) : GaussianInt) * p.2 = z := by
          apply mul_left_cancel₀ hw0
          rw [← mul_assoc, hp1', hp3, hwzu]
        have h3 : (↑((Classical.choose hhp)⁻¹) : GaussianInt) *
            ((↑(Classical.choose hhp) : GaussianInt) * p.2) =
            (↑((Classical.choose hhp)⁻¹) : GaussianInt) * z := by rw [h2]
        rw [← mul_assoc, Units.inv_mul, one_mul] at h3
        exact h3
      have hq2' : q.2 = (↑((Classical.choose hhq)⁻¹) : GaussianInt) * z := by
        have h2 : (↑(Classical.choose hhq) : GaussianInt) * q.2 = z := by
          apply mul_left_cancel₀ hw0
          rw [← mul_assoc, hq1', hq3, hwzu]
        have h3 : (↑((Classical.choose hhq)⁻¹) : GaussianInt) *
            ((↑(Classical.choose hhq) : GaussianInt) * q.2) =
            (↑((Classical.choose hhq)⁻¹) : GaussianInt) * z := by rw [h2]
        rw [← mul_assoc, Units.inv_mul, one_mul] at h3
        exact h3
      have h1eq : p.1 = q.1 := by rw [← hp1', ← hq1', huv]
      have h2eq : p.2 = q.2 := by rw [hp2', hq2', huv]
      exact Prod.ext h1eq h2eq
    · intro b hb
      have hbu : IsUnit b := hb
      refine ⟨(w * (↑hbu.unit : GaussianInt), (↑(hbu.unit⁻¹) : GaussianInt) * z), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [Zsqrtd.norm_mul, Int.natAbs_mul, hw, isUnit_norm_natAbs hbu.unit.isUnit, mul_one]
        · rw [Zsqrtd.norm_mul, Int.natAbs_mul, isUnit_norm_natAbs hbu.unit⁻¹.isUnit, one_mul, hz]
        · rw [hwz]
          rw [← mul_assoc, mul_assoc w (↑hbu.unit : GaussianInt) (↑(hbu.unit⁻¹) : GaussianInt),
            Units.mul_inv, mul_one]
      · have hwit : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = w * (↑hbu.unit : GaussianInt) :=
          ⟨hbu.unit, rfl⟩
        have hchoose : Classical.choose hwit = hbu.unit := by
          refine Units.ext ?_
          exact mul_left_cancel₀ hw0 (Classical.choose_spec hwit)
        change (if h : ∃ v : GaussianIntˣ, w * (↑v : GaussianInt) = w * (↑hbu.unit : GaussianInt) then
            ↑(Classical.choose h) else (0 : GaussianInt)) = b
        rw [dif_pos hwit, hchoose, hbu.unit_spec]
  change S.ncard = 4
  rw [hST]
  change ({y : GaussianInt | IsUnit y}).ncard = 4
  exact ncard_units

end Commons.NumberTheory.GaussianInt
