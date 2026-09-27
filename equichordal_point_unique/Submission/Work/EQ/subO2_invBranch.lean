import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.H0_tail_bounded

/-! # The `O₂`-radicand of a backward branch, and the degenerate pairs

Two algebra facts used by the puncture-counting route:

* `Work.EQ.bsq_subO2_invBranch`: the `O₂`-radicand of the `s`-th backward branch of `Q` is
  `(±1 - brho (subO1 a Q))^2`; in particular it *vanishes* exactly when the `O₁`-radicand of `Q`
  is `1` and the branch is the principal one.  This is the algebraic reason why an `O₂`-contact of
  a backward chain is the same phenomenon as an `O₁`-radicand equal to `1`.
* `Work.EQ.eqRelC_bsq_subO2_eq_zero` and `Work.EQ.eqRelC_bsq_subO1_eq_zero`: the only *degenerate*
  points of the relation (F1 of `PAPER_PROOFS.md`) are `O₂` in the first slot and `O₁` in the
  second. -/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- The principal square root of a complex number is never `-1`. -/
theorem brho_ne_neg_one (Z : ℂ × ℂ) : brho Z ≠ -1 := by
  intro h
  have h2 : bsq Z = 1 := by
    have hsq := brho_sq Z
    rw [h] at hsq
    simpa using hsq.symm
  have hb : brho Z = 1 := by
    rw [brho, h2]
    exact Complex.one_cpow _
  rw [hb] at h
  norm_num at h

/-- The `O₂`-translate of the `s`-th backward branch is a multiple of `Q - O₁`. -/
theorem subO2_invBranch_smul (a : ℝ) (s : Bool) (Q : ℂ × ℂ) :
    subO2 a (invBranch a s Q)
      = ((if s then (1 : ℂ) else -1) * (brho (subO1 a Q))⁻¹ - 1) • subO1 a Q := by
  ext <;>
    simp only [invBranch, subO1, subO2, brho, bsq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      div_eq_mul_inv] <;> rcases s <;> simp <;> ring

/-- The `O₂`-radicand of the `s`-th backward branch, in factored form. -/
theorem bsq_subO2_invBranch_mul (a : ℝ) (s : Bool) (Q : ℂ × ℂ) :
    bsq (subO2 a (invBranch a s Q)) =
      ((if s then (1 : ℂ) else -1) * (brho (subO1 a Q))⁻¹ - 1) ^ 2 * bsq (subO1 a Q) := by
  rw [subO2_invBranch_smul, bsq_smul]

/-- **The `O₂`-radicand of a backward branch.**  Off the isotropic lines through `O₁`,
`bsq (subO2 a (invBranch a s Q)) = (±1 - brho (subO1 a Q))^2`. -/
theorem bsq_subO2_invBranch {a : ℝ} {Q : ℂ × ℂ} (s : Bool) (h : bsq (subO1 a Q) ≠ 0) :
    bsq (subO2 a (invBranch a s Q)) = ((if s then (1 : ℂ) else -1) - brho (subO1 a Q)) ^ 2 := by
  rw [bsq_subO2_invBranch_mul]
  have hρ : brho (subO1 a Q) ≠ 0 := brho_ne_zero h
  rw [← brho_sq (subO1 a Q)]
  field_simp

/-- Off the isotropic lines through `O₁`, the `O₂`-radicand of the *false* branch never
vanishes (it equals `(brho + 1)^2`). -/
theorem bsq_subO2_invBranch_false_ne_zero {a : ℝ} {Q : ℂ × ℂ} (h : bsq (subO1 a Q) ≠ 0) :
    bsq (subO2 a (invBranch a false Q)) ≠ 0 := by
  rw [bsq_subO2_invBranch false h]
  simp only [Bool.false_eq_true, ite_false]
  intro h0
  have h1 : -1 - brho (subO1 a Q) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  have hb : brho (subO1 a Q) = -1 := by
    rw [sub_eq_zero] at h1
    exact h1.symm
  exact brho_ne_neg_one (subO1 a Q) hb

/-- **The `O₂`-radicand of the `true` branch vanishes exactly when the `O₁`-radicand is `1`.** -/
theorem bsq_subO2_invBranch_true_eq_zero_iff {a : ℝ} {Q : ℂ × ℂ} (h : bsq (subO1 a Q) ≠ 0) :
    bsq (subO2 a (invBranch a true Q)) = 0 ↔ bsq (subO1 a Q) = 1 := by
  rw [bsq_subO2_invBranch true h]
  simp only [ite_true]
  rw [show ((1 : ℂ) - brho (subO1 a Q)) ^ 2 = 0 ↔ (1 : ℂ) - brho (subO1 a Q) = 0 from
    pow_eq_zero_iff (n := 2) (by norm_num)]
  constructor
  · intro h1
    rw [sub_eq_zero] at h1
    rw [← brho_sq (subO1 a Q), ← h1]
    norm_num
  · intro h1
    rw [sub_eq_zero]
    rcases sq_eq_one_iff.mp (show brho (subO1 a Q) ^ 2 = 1 by rw [brho_sq, h1]) with h2 | h2
    · exact h2.symm
    · exact absurd h2 (brho_ne_neg_one (subO1 a Q))

/-- **The degenerate points of the relation (first slot).**  If `EqRelC a P Q` and the
`O₂`-radicand of `P` vanishes, then `P = O₂`. -/
theorem eqRelC_bsq_subO2_eq_zero {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q)
    (h2 : bsq (subO2 a P) = 0) : P = (((a / 2 : ℝ) : ℂ), (0 : ℂ)) := by
  obtain ⟨h1, h2'⟩ := (eqRelC_iff_reverse P Q).mp h
  by_contra hP
  have hS : P + Q ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp [bsq] at h1
  have hpar : par (P + Q) (subO2 a P) := by
    rw [← sub_subO2 (a := a) (P := P) (Q := Q)] at h2'
    exact par_sub_iff.mp h2'
  obtain ⟨σ, hσ⟩ := exists_smul_of_par hpar hS
  have hbs : bsq (subO2 a P) = σ ^ 2 := by rw [hσ, bsq_smul, h1, mul_one]
  have hσ0 : σ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [← hbs]; exact h2)
  have hz : subO2 a P = 0 := by rw [hσ, hσ0, zero_smul]
  refine hP (Prod.ext ?_ ?_)
  · have := congrArg (fun Z : ℂ × ℂ => Z.1) hz
    simp only [subO2, Prod.fst_zero] at this
    rw [sub_eq_zero] at this
    exact this
  · have := congrArg (fun Z : ℂ × ℂ => Z.2) hz
    simpa [subO2] using this

/-- **The degenerate points of the relation (second slot).**  If `EqRelC a P Q` and the
`O₁`-radicand of `Q` vanishes, then `Q = O₁`. -/
theorem eqRelC_bsq_subO1_eq_zero {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q)
    (h2 : bsq (subO1 a Q) = 0) : Q = (((-(a / 2) : ℝ) : ℂ), (0 : ℂ)) := by
  obtain ⟨h1, h2'⟩ := (eqRelC_iff_reverse P Q).mp h
  by_contra hQ
  have hS : P + Q ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp [bsq] at h1
  obtain ⟨σ, hσ⟩ := exists_smul_of_par h2' hS
  have hbs : bsq (subO1 a Q) = σ ^ 2 := by rw [hσ, bsq_smul, h1, mul_one]
  have hσ0 : σ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [← hbs]; exact h2)
  have hz : subO1 a Q = 0 := by rw [hσ, hσ0, zero_smul]
  refine hQ (Prod.ext ?_ ?_)
  · have := congrArg (fun Z : ℂ × ℂ => Z.1) hz
    simp only [subO1, Prod.fst_zero] at this
    rw [add_eq_zero_iff_eq_neg] at this
    rw [this]
    push_cast
    ring
  · have := congrArg (fun Z : ℂ × ℂ => Z.2) hz
    simpa [subO1] using this

end

end Work.EQ
