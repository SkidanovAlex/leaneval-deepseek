import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.aDiag_conj_uij
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.mem_sup_Uij_same_target_prod

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLContract.Lemmas

noncomputable section

/-! ## Reduction to the two transvections `u₁₀`, `u₂₀`

Write `u1 s = u₁₀(s)` and `u2 t = u₂₀(t)`.  The point `τ_p = u₁₀(p₁)u₂₀(p₂)Γ` is then the
coset of `u1 p.1 * u2 p.2`.  The three claims of `tau_algebra` are

* the cocycle identity `u1 a u2 b = u1 (a-c) u2 (b-d) (u1 c u2 d)`;
* the conjugacy `a₀^n u₁₀(x)u₂₀(y) a₀^{-n} = u₁₀(e^{3n}x)u₂₀(e^{3n}y)`;
* the kernel identity `τ_p = τ_{p'} ↔ p - p' ∈ ℤ²`. -/

private abbrev u1 (s : ℝ) : SL3 := uij (show (1 : Fin 3) ≠ 0 by decide) s
private abbrev u2 (s : ℝ) : SL3 := uij (show (2 : Fin 3) ≠ 0 by decide) s

private lemma u1_add (a b : ℝ) : u1 (a + b) = u1 a * u1 b := uij_add' _ a b
private lemma u2_add (a b : ℝ) : u2 (a + b) = u2 a * u2 b := uij_add' _ a b
private lemma u1_inv (s : ℝ) : (u1 s)⁻¹ = u1 (-s) := uij_inv' _ s
private lemma u2_inv (s : ℝ) : (u2 s)⁻¹ = u2 (-s) := uij_inv' _ s

private lemma u1u2_comm (s t : ℝ) : u1 s * u2 t = u2 t * u1 s :=
  uij_mul_comm_same_target _ _ s t

private lemma u1u2_prod (a b c d : ℝ) :
    u1 (a + c) * u2 (b + d) = (u1 a * u2 b) * (u1 c * u2 d) := uij_mul_prod _ _ a b c d

private lemma toMat_coe (A : SL3) :
    (((A : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) = toMat A := rfl

/-- Entries of the product of two same-target transvections. -/
private lemma u1u2_entry_10 (a b : ℝ) :
    (((u1 a * u2 b : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 0 = a := by
  rw [toMat_coe, toMat_uij_mul_same_target]
  simp [Matrix.add_apply]

private lemma u1u2_entry_20 (a b : ℝ) :
    (((u1 a * u2 b : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 0 = b := by
  rw [toMat_coe, toMat_uij_mul_same_target]
  simp [Matrix.add_apply]

/-- `u₁₀(c)⁻¹ u₁₀(a) u₂₀(d)⁻¹ u₂₀(b) = u₁₀(a-c) u₂₀(b-d)`: the inverse-product formula for the
two-parameter subgroup `{u₁₀(s) u₂₀(t)}`. -/
private lemma u1u2_inv_mul (a b c d : ℝ) :
    (u1 c * u2 d)⁻¹ * (u1 a * u2 b) = u1 (a - c) * u2 (b - d) := by
  rw [mul_inv_rev, u1_inv, u2_inv]
  rw [← u1u2_comm (-c) (-d)]
  rw [← u1u2_prod (-c) (-d) a b]
  congr 1 <;> ring

/-- `u₁₀(k) ∈ Γ₃` for integral `k`. -/
private lemma u1_int_mem (k : ℤ) : u1 ((k : ℤ) : ℝ) ∈ Γ3 := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) k, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe]
  simp only [Matrix.map_apply]
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  simp only [u1, uij, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `u₂₀(k) ∈ Γ₃` for integral `k`. -/
private lemma u2_int_mem (k : ℤ) : u2 ((k : ℤ) : ℝ) ∈ Γ3 := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) k, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe]
  simp only [Matrix.map_apply]
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  simp only [u2, uij, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **Claim 1 (cocycle).** `τ_{p'} = u₁₀(p'₁-p₁) u₂₀(p'₂-p₂) · τ_p`. -/
private lemma tau_smul_rel (p p' : ℝ × ℝ) :
    tau p' = mkX (u1 (p'.1 - p.1) * u2 (p'.2 - p.2) * (u1 p.1 * u2 p.2)) := by
  change mkX (u1 p'.1 * u2 p'.2)
    = mkX (u1 (p'.1 - p.1) * u2 (p'.2 - p.2) * (u1 p.1 * u2 p.2))
  congr 1
  rw [← u1u2_prod (p'.1 - p.1) (p'.2 - p.2) p.1 p.2]
  congr 1 <;> ring

/-- **Claim 2 (conjugacy).** The `a₀`-conjugate of a `u₁₀`- or `u₂₀`-transvection. -/
private lemma a0_conj (n : ℕ) (s : ℝ) {i : Fin 3} (h : i ≠ 0) (hi : i = 1 ∨ i = 2) :
    (a0 ^ n) * uij h s * (a0 ^ n)⁻¹ = uij h (Real.exp (3 * (n : ℝ)) * s) := by
  rw [show a0 = aDiag ![(-2 : ℝ), 1, 1] from rfl, horoUij_aDiag_pow]
  rw [horoUij_aDiag_conj]
  have hsum : (fun k : Fin 3 => (n : ℝ) * ![(-2 : ℝ), 1, 1] k) i
      - (fun k : Fin 3 => (n : ℝ) * ![(-2 : ℝ), 1, 1] k) 0 = 3 * (n : ℝ) := by
    rcases hi with rfl | rfl <;>
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        ring
  rw [hsum]

end

theorem tau_algebra :
    (∀ p p' : ℝ × ℝ, Work.EKLContract.tau p' =
      Work.EKLContract.mkX (Work.EKLContract.uij (show (1 : Fin 3) ≠ 0 by decide) (p'.1 - p.1) *
        Work.EKLContract.uij (show (2 : Fin 3) ≠ 0 by decide) (p'.2 - p.2) *
        (Work.EKLContract.uij (show (1 : Fin 3) ≠ 0 by decide) p.1 *
         Work.EKLContract.uij (show (2 : Fin 3) ≠ 0 by decide) p.2))) ∧
    (∀ (n : ℕ) (x y : ℝ), (Work.EKLContract.a0 ^ n) *
        (Work.EKLContract.uij (show (1 : Fin 3) ≠ 0 by decide) x *
         Work.EKLContract.uij (show (2 : Fin 3) ≠ 0 by decide) y) * (Work.EKLContract.a0 ^ n)⁻¹ =
      Work.EKLContract.uij (show (1 : Fin 3) ≠ 0 by decide) (Real.exp (3 * (n : ℝ)) * x) *
       Work.EKLContract.uij (show (2 : Fin 3) ≠ 0 by decide) (Real.exp (3 * (n : ℝ)) * y)) ∧
    (∀ p p' : ℝ × ℝ, Work.EKLContract.tau p = Work.EKLContract.tau p' ↔
      (∃ k l : ℤ, p.1 - p'.1 = (k : ℝ) ∧ p.2 - p'.2 = (l : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p p'
    exact tau_smul_rel p p'
  · intro n x y
    rw [show (a0 ^ n) * (u1 x * u2 y) * (a0 ^ n)⁻¹ =
        ((a0 ^ n) * u1 x * (a0 ^ n)⁻¹) * ((a0 ^ n) * u2 y * (a0 ^ n)⁻¹) from by group]
    rw [a0_conj n x (show (1 : Fin 3) ≠ 0 by decide) (Or.inl rfl),
        a0_conj n y (show (2 : Fin 3) ≠ 0 by decide) (Or.inr rfl)]
  · intro p p'
    constructor
    · intro h
      have hmem : (u1 p'.1 * u2 p'.2)⁻¹ * (u1 p.1 * u2 p.2) ∈ Γ3 := by
        have h' : QuotientGroup.mk (u1 p'.1 * u2 p'.2) = QuotientGroup.mk (u1 p.1 * u2 p.2) :=
          h.symm
        exact QuotientGroup.eq.mp h'
      rw [u1u2_inv_mul p.1 p.2 p'.1 p'.2] at hmem
      obtain ⟨k, hk⟩ := Γ3_integral_entries _ hmem 1 0
      obtain ⟨l, hl⟩ := Γ3_integral_entries _ hmem 2 0
      refine ⟨k, l, ?_, ?_⟩
      · rw [← hk, u1u2_entry_10]
      · rw [← hl, u1u2_entry_20]
    · rintro ⟨k, l, hk, hl⟩
      apply QuotientGroup.eq.mpr
      rw [u1u2_inv_mul p'.1 p'.2 p.1 p.2]
      have e1 : p'.1 - p.1 = ((-k : ℤ) : ℝ) := by
        rw [Int.cast_neg, ← hk]; ring
      have e2 : p'.2 - p.2 = ((-l : ℤ) : ℝ) := by
        rw [Int.cast_neg, ← hl]; ring
      rw [e1, e2]
      exact mul_mem (u1_int_mem (-k)) (u2_int_mem (-l))

end Work.EKLComp
