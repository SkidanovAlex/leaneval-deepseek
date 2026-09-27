import Mathlib
import Submission.Work.EQ.DefsCore

/-! ## Algebra of the complexified equichordal relation

The relation `EqRelC a P Q` (DefsCore) says in coordinates that `X = P + Q` is a unit vector of
the bilinear form `z₁² + z₂²` which is parallel to `P - O₂` (`O₂ = a/2`).  In this file we set up
the algebra: the bilinear form `bsq`, parallelism `par`, the forward branch `fwdC`, the backward
branches `invBranch`, and the equivalences between them.  We record the correspondence with the
real map `eqU` of Defs.lean as well. -/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- The translation `P ↦ P - O₂` on `ℂ²` (only the first coordinate moves). -/
noncomputable def subO2 (a : ℝ) (P : ℂ × ℂ) : ℂ × ℂ := (P.1 - ((a / 2 : ℝ) : ℂ), P.2)

/-- The translation `P ↦ P - O₁` on `ℂ²` (only the first coordinate moves). -/
noncomputable def subO1 (a : ℝ) (P : ℂ × ℂ) : ℂ × ℂ := (P.1 + ((a / 2 : ℝ) : ℂ), P.2)

/-- The bilinear square form `z₁² + z₂²` on `ℂ²`. -/
noncomputable def bsq (P : ℂ × ℂ) : ℂ := P.1 ^ 2 + P.2 ^ 2

/-- The principal square root of the bilinear square. -/
noncomputable def brho (P : ℂ × ℂ) : ℂ := (bsq P) ^ (1 / 2 : ℂ)

theorem brho_sq (P : ℂ × ℂ) : brho P ^ 2 = bsq P := by
  rw [brho, show (1 / 2 : ℂ) = (((2 : ℕ) : ℂ))⁻¹ by norm_num]
  exact Complex.cpow_nat_inv_pow (bsq P) (by norm_num)

theorem brho_ne_zero {P : ℂ × ℂ} (h : bsq P ≠ 0) : brho P ≠ 0 := by
  intro h0
  exact h (by rw [← brho_sq P, h0]; ring)

/-- The cross-product (parallelism) form on `ℂ²`: `par X Y` says `det(X,Y) = 0`. -/
def par (X Y : ℂ × ℂ) : Prop := X.1 * Y.2 = X.2 * Y.1

theorem par_refl (X : ℂ × ℂ) : par X X := by rw [par]; ring

theorem par_zero_left (Y : ℂ × ℂ) : par 0 Y := by rw [par]; simp

theorem par_zero_right (X : ℂ × ℂ) : par X 0 := by rw [par]; simp

theorem par_comm {X Y : ℂ × ℂ} : par X Y ↔ par Y X := by
  rw [par, par]
  constructor <;> intro h <;> linear_combination -h

theorem par_smul_left (σ : ℂ) {X Y : ℂ × ℂ} : par (σ • X) Y ↔ σ = 0 ∨ par X Y := by
  rw [par, par]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · intro h
    rcases eq_or_ne σ 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (by linear_combination h))
  · rintro (rfl | h)
    · simp
    · linear_combination σ * h

theorem par_smul_right (σ : ℂ) {X Y : ℂ × ℂ} : par X (σ • Y) ↔ σ = 0 ∨ par X Y :=
  ((par_comm (X := X) (Y := σ • Y)).trans (par_smul_left (X := Y) (Y := X) σ)).trans
    (or_congr_right (par_comm (X := X) (Y := Y)).symm)

theorem par_smul_smul (σ τ : ℂ) (Z : ℂ × ℂ) : par (σ • (τ • Z)) Z := by
  rw [← smul_assoc, par_smul_left]
  exact Or.inr (par_refl Z)

/-- If `X ≠ 0` and `Y` is parallel to `X`, then `Y` is a multiple of `X`. -/
theorem exists_smul_of_par {X Y : ℂ × ℂ} (hXY : par X Y) (hX : X ≠ 0) :
    ∃ σ : ℂ, Y = σ • X := by
  rw [par] at hXY
  rcases eq_or_ne X.1 0 with h1 | h1
  · have h2 : X.2 ≠ 0 := fun h2 => hX (by ext <;> simp [h1, h2])
    have hy1 : Y.1 = 0 := by
      rw [h1, zero_mul] at hXY
      exact (mul_eq_zero.mp hXY.symm).resolve_left h2
    refine ⟨Y.2 / X.2, ?_⟩
    ext
    · rw [Prod.smul_fst, smul_eq_mul, hy1, h1, mul_zero]
    · rw [Prod.smul_snd, smul_eq_mul]; field_simp
  · refine ⟨Y.1 / X.1, ?_⟩
    ext
    · rw [Prod.smul_fst, smul_eq_mul]; field_simp
    · rw [Prod.smul_snd, smul_eq_mul]; field_simp; linear_combination hXY

/-- Parallelism is unchanged by replacing `Y` by `X - Y`. -/
theorem par_sub_iff {X Y : ℂ × ℂ} : par X (X - Y) ↔ par X Y := by
  rw [par, par]
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> linear_combination -h

theorem sub_subO1 {a : ℝ} {P Q : ℂ × ℂ} : (P + Q) - subO1 a Q = subO2 a P := by
  ext <;> simp [subO2, subO1] <;> ring

theorem sub_subO2 {a : ℝ} {P Q : ℂ × ℂ} : (P + Q) - subO2 a P = subO1 a Q := by
  ext <;> simp [subO2, subO1] <;> ring

/-- **The relation, in the reverse form.**  Writing `X = P + Q`, the equichordal relation says
that `X` is a unit vector of the bilinear form which is parallel to `Q - O₁`. -/
theorem eqRelC_iff_reverse {a : ℝ} (P Q : ℂ × ℂ) :
    EqRelC a P Q ↔ (bsq (P + Q) = 1 ∧ par (P + Q) (subO1 a Q)) := by
  rw [EqRelC, par, subO1, bsq]
  simp only [Prod.fst_add, Prod.snd_add]
  constructor <;> rintro ⟨e1, e2⟩ <;>
    exact ⟨by linear_combination e1, by linear_combination -e2⟩

/-- The (principal) forward branch of the relation:
`Q = -P + (P - O₂)/ρ`, `ρ² = (P - O₂)·(P - O₂)`. -/
noncomputable def fwdC (a : ℝ) (P : ℂ × ℂ) : ℂ × ℂ :=
  (-P.1 + (P.1 - ((a / 2 : ℝ) : ℂ)) / brho (subO2 a P),
   -P.2 + P.2 / brho (subO2 a P))

theorem fwdC_add (a : ℝ) (P : ℂ × ℂ) : P + fwdC a P = (brho (subO2 a P))⁻¹ • subO2 a P := by
  ext <;>
    simp only [fwdC, subO2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, div_eq_mul_inv] <;> ring

theorem subO1_fwdC (a : ℝ) (P : ℂ × ℂ) :
    subO1 a (fwdC a P) = ((brho (subO2 a P))⁻¹ - 1) • subO2 a P := by
  have h : fwdC a P = (brho (subO2 a P))⁻¹ • subO2 a P - P := by
    rw [← fwdC_add, add_sub_cancel_left]
  rw [h]
  ext <;>
    simp only [subO1, subO2, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] <;> ring

theorem bsq_smul (σ : ℂ) (Z : ℂ × ℂ) : bsq (σ • Z) = σ ^ 2 * bsq Z := by
  rw [bsq, bsq]; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **Forward solvability.**  `fwdC a P` satisfies the relation, when `P ≠ O₂`. -/
theorem eqRelC_fwdC {a : ℝ} {P : ℂ × ℂ} (h : bsq (subO2 a P) ≠ 0) : EqRelC a P (fwdC a P) := by
  rw [eqRelC_iff_reverse, fwdC_add]
  refine ⟨?_, ?_⟩
  · rw [bsq_smul, ← brho_sq (subO2 a P), ← mul_pow, inv_mul_cancel₀ (brho_ne_zero h), one_pow]
  · rw [subO1_fwdC]
    exact (par_smul_left _).mpr (Or.inr ((par_smul_right _).mpr (Or.inr (par_refl _))))

/-- The point of `ℂ²` with real coordinates `(z.re, z.im)`. -/
noncomputable def Rpt (z : ℂ) : ℂ × ℂ := ((z.re : ℂ), (z.im : ℂ))

@[simp] theorem Rpt_fst (z : ℂ) : (Rpt z).1 = z.re := rfl

@[simp] theorem Rpt_snd (z : ℂ) : (Rpt z).2 = z.im := rfl

theorem Rpt_ofReal_re (z : ℂ) : Rpt z = ((z.re : ℂ), (z.im : ℂ)) := rfl

/-- Reassembling the complex number. -/
theorem Rpt_toCplx (z : ℂ) : (Rpt z).1 + (Rpt z).2 * Complex.I = z := by
  simp [Rpt, Complex.re_add_im]

theorem toCplx_inj {z w : ℂ} (h : (Rpt z).1 + (Rpt z).2 * Complex.I = (Rpt w).1 + (Rpt w).2 * Complex.I) :
    z = w := by
  rw [Rpt_toCplx z, Rpt_toCplx w] at h
  exact h

theorem invBranch_add (a : ℝ) (s : Bool) (Q : ℂ × ℂ) :
    invBranch a s Q + Q = (if s then (1 : ℂ) else -1) • ((brho (subO1 a Q))⁻¹ • subO1 a Q) := by
  ext <;>
    simp only [invBranch, subO1, brho, bsq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, div_eq_mul_inv] <;> rcases s <;> simp <;> ring

/-- **Backward solvability.**  `invBranch a s Q` satisfies the relation as the first argument. -/
theorem eqRelC_invBranch {a : ℝ} {Q : ℂ × ℂ} (s : Bool) (h : bsq (subO1 a Q) ≠ 0) :
    EqRelC a (invBranch a s Q) Q := by
  have hρ := brho_ne_zero h
  have hbs : bsq ((if s then (1 : ℂ) else -1) • ((brho (subO1 a Q))⁻¹ • subO1 a Q))
      = (if s then (1 : ℂ) else -1) ^ 2 := by
    calc bsq ((if s then (1 : ℂ) else -1) • ((brho (subO1 a Q))⁻¹ • subO1 a Q))
        = (if s then (1 : ℂ) else -1) ^ 2 * bsq ((brho (subO1 a Q))⁻¹ • subO1 a Q) :=
          bsq_smul _ _
      _ = (if s then (1 : ℂ) else -1) ^ 2 * ((brho (subO1 a Q))⁻¹ ^ 2 * bsq (subO1 a Q)) := by
          rw [bsq_smul]
      _ = (if s then (1 : ℂ) else -1) ^ 2 *
            ((brho (subO1 a Q))⁻¹ ^ 2 * brho (subO1 a Q) ^ 2) := by rw [brho_sq]
      _ = (if s then (1 : ℂ) else -1) ^ 2 := by
          rw [← mul_pow, inv_mul_cancel₀ hρ, one_pow, mul_one]
  rw [eqRelC_iff_reverse, invBranch_add]
  refine ⟨?_, ?_⟩
  · rw [hbs]
    rcases s <;> norm_num
  · rcases s <;> exact par_smul_smul _ _ _

/-- **The two backward branches.**  If `Q - O₁` has nonvanishing bilinear square, any preimage
`P` of `Q` under the relation is `invBranch a true Q` or `invBranch a false Q`. -/
theorem eqRelC_solutions {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hQ : bsq (subO1 a Q) ≠ 0) :
    P = invBranch a true Q ∨ P = invBranch a false Q := by
  obtain ⟨h1, h2⟩ := (eqRelC_iff_reverse P Q).mp h
  have hZ : subO1 a Q ≠ 0 := by
    intro h0
    exact hQ (by rw [h0]; simp [bsq])
  obtain ⟨σ, hσ⟩ := exists_smul_of_par ((par_comm).mp h2) hZ
  have hsq : σ ^ 2 * bsq (subO1 a Q) = 1 := by
    have hh : bsq (σ • subO1 a Q) = 1 := by rw [← hσ]; exact h1
    rwa [bsq_smul] at hh
  have hρ : brho (subO1 a Q) ≠ 0 := brho_ne_zero hQ
  have hσ2 : σ = (brho (subO1 a Q))⁻¹ ∨ σ = -(brho (subO1 a Q))⁻¹ := by
    have key : (σ * brho (subO1 a Q)) ^ 2 = 1 := by
      rw [mul_pow, brho_sq (subO1 a Q)]
      exact hsq
    rw [pow_two] at key
    rcases mul_self_eq_one_iff.mp key with hk | hk
    · left; exact eq_inv_of_mul_eq_one_left hk
    · right
      have hk' : σ * (-brho (subO1 a Q)) = 1 := by rw [mul_neg, hk, neg_neg]
      simpa using eq_inv_of_mul_eq_one_left hk'
  rcases hσ2 with hσ2 | hσ2
  · left
    have hP : P + Q = (brho (subO1 a Q))⁻¹ • subO1 a Q := by rw [hσ, hσ2]
    have hb : invBranch a true Q + Q = (brho (subO1 a Q))⁻¹ • subO1 a Q := by
      simpa using invBranch_add a true Q
    exact add_right_cancel (hP.trans hb.symm)
  · right
    have hP : P + Q = -((brho (subO1 a Q))⁻¹ • subO1 a Q) := by rw [hσ, hσ2, neg_smul]
    have hb : invBranch a false Q + Q = -((brho (subO1 a Q))⁻¹ • subO1 a Q) := by
      simpa using invBranch_add a false Q
    exact add_right_cancel (hP.trans hb.symm)

end

end Work.EQ
