/-
# The kernel `K^{(d)}` is bounded on a neighbourhood of the tangency points `(A • i, i)`

For the two "arc" elements `A = T S T` and `A = S T`, the point `A • i` is a tangency point of
the CKMRV domain `𝒟`, and the pole divisor of `(τ,z) ↦ K^{(d)}(τ,z)` passes through `(A • i, i)`
along the two branches `z = A⁻¹ • τ` and `z = S A⁻¹ • τ`.  Along both branches the residue
vanishes (the two orbit elements `A` and `A S` satisfy `φ = 0`), so the pole is removable and
the kernel is bounded near the point.

The proof follows the pattern of `Work.Asymptotics.KaxisMid.AtIAux.key_bound_I`: the cleared
kernel vanishes at least once along each of the two branches, so the two-zero maximum modulus
bound (`Work.Asymptotics.KaxisMid.AtIAux.two_zero_apply`) bounds it by `C ‖τ - A z‖ ‖τ - A S z‖`,
while `j τ - j z` dominates the same product (after the substitution `τ = A τ'` this is
`Work.Asymptotics.KaxisMid.AtIAux.j_lower_I`); dividing by the growth prefactor gives the bound.
-/
import Mathlib
import Submission.Work.Asymptotics.Graze.Points
import Submission.Work.Asymptotics.Graze.KfunClear_vanish_of_phiPair_uncond
import Submission.Work.Asymptotics.KaxisMid.exists_local_bound_coincidence

set_option maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups Topology
open Work.Kernels
open Work.Asymptotics.KaxisMid

namespace Work.Asymptotics.Graze

/-- The cleared kernel vanishes at the orbit of a grazing element. -/
lemma graze_vanish (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (γ : SL(2, ℤ)) (hγ : GrazeElem γ) : ∀ z : ℍ, KfunClear ℓ d (γ • z) z = 0 :=
  KfunClear_vanish_of_phiPair_uncond ℓ d hd γ (phiPair_graze γ hγ)

/-- `(T S T) S = -(T S)⁻¹` at the level of the action. -/
lemma TST_mul_S_smul (z : ℍ) :
    (((ModularGroup.T * ModularGroup.S * ModularGroup.T) * ModularGroup.S) • z : ℍ)
      = ((ModularGroup.T * ModularGroup.S)⁻¹) • z := by
  have he : ((ModularGroup.T * ModularGroup.S * ModularGroup.T) * ModularGroup.S : SL(2,ℤ))
      = -((ModularGroup.T * ModularGroup.S)⁻¹) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (((ModularGroup.T * ModularGroup.S * ModularGroup.T) * ModularGroup.S : SL(2,ℤ))
        : Matrix (Fin 2) (Fin 2) ℤ) i j
      = ((-((ModularGroup.T * ModularGroup.S)⁻¹) : SL(2,ℤ))
        : Matrix (Fin 2) (Fin 2) ℤ) i j
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [he, ModularGroup.SL_neg_smul]

/-- `(S T) S = -(T S T)⁻¹` at the level of the action. -/
lemma ST_mul_S_smul (z : ℍ) :
    (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) • z : ℍ)
      = ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) • z := by
  have he : ((ModularGroup.S * ModularGroup.T) * ModularGroup.S : SL(2,ℤ))
      = -((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (((ModularGroup.S * ModularGroup.T) * ModularGroup.S : SL(2,ℤ))
        : Matrix (Fin 2) (Fin 2) ℤ) i j
      = ((-((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) : SL(2,ℤ))
        : Matrix (Fin 2) (Fin 2) ℤ) i j
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [he, ModularGroup.SL_neg_smul]

/-- The cleared kernel vanishes on the orbit of `A S` for the arc elements `A`. -/
lemma arc_mul_S_vanish (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (A : SL(2, ℤ)) (hA : IsArc A) : ∀ z : ℍ, KfunClear ℓ d ((A * ModularGroup.S) • z) z = 0 := by
  rcases hA with rfl | rfl
  · intro z
    rw [TST_mul_S_smul z]
    exact graze_vanish ℓ d hd ((ModularGroup.T * ModularGroup.S)⁻¹)
      (Or.inr (Or.inl rfl)) z
  · intro z
    rw [ST_mul_S_smul z]
    exact graze_vanish ℓ d hd ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹)
      (Or.inr (Or.inr (Or.inr rfl))) z

/-- `A ⁻¹ • (A • i) = i`. -/
lemma IsArc_inv_smul_I (A : SL(2, ℤ)) : A⁻¹ • ((A • UpperHalfPlane.I : ℍ)) = UpperHalfPlane.I := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- `IsArc` implies `GrazeElem`. -/
lemma GrazeElem_of_IsArc (A : SL(2, ℤ)) (hA : IsArc A) : GrazeElem A :=
  hA.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr (Or.inl h)))

/-- The `S`-difference: `S • u - S • v = (u - v)/(u v)`. -/
lemma norm_S_sub_S_eq (u v : ℍ) :
    ‖((ModularGroup.S • u : ℍ) : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖
      = ‖(u:ℂ) - (v:ℂ)‖ / (‖(u:ℂ)‖ * ‖(v:ℂ)‖) :=
  KbcAux2.norm_S_sub_S u v

/-- `S * S = -1`. -/
lemma S_mul_S_sl : (ModularGroup.S * ModularGroup.S : SL(2, ℤ)) = -1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  show ((ModularGroup.S * ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
    = ((-1 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- `(-1 : SL(2,ℤ)) • z = z`. -/
lemma neg_one_smul_sl (z : ℍ) : (-1 : SL(2, ℤ)) • z = z := by
  have h : (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) := by norm_num
  rw [h, ModularGroup.SL_neg_smul, one_smul]

/-- **Quadratic vanishing of the cleared kernel near the tangency point.** -/
theorem two_zero_KfunClear_arc (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (A : SL(2, ℤ)) (hA : IsArc A) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ τ z : ℍ,
      ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ → ‖(z:ℂ) - Complex.I‖ < ρ →
      ‖KfunClear ℓ d τ z‖ ≤ C * ‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
        * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖ := by
  obtain ⟨M, hMpos, hMb⟩ := KbcAux2.exists_bound_KfunClear_of_balls ℓ d hd
    (A • UpperHalfPlane.I) UpperHalfPlane.I (R₁ := 1/4) (R₂ := 3/4)
    (by rw [IsArc_im_I A hA]; norm_num) (by rw [UpperHalfPlane.I_im]; norm_num)
  have hArc := GrazeElem_of_IsArc A hA
  refine ⟨1/128, 1024 * M, by norm_num, by positivity, fun τ z hτ hz => ?_⟩
  have hτ4 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/4 := by linarith
  have hτ16 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16 := by linarith
  have hz4 : ‖(z:ℂ) - Complex.I‖ < 3/4 := by linarith
  have hz16 : ‖(z:ℂ) - Complex.I‖ < 1/16 := by linarith
  set D : ℝ := ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ with hD
  by_cases hzi : z = UpperHalfPlane.I
  · subst hzi
    by_cases hτI : τ = A • UpperHalfPlane.I
    · -- `τ = A • i` and `z = i`: the value is `0`
      subst hτI
      have h0 : KfunClear ℓ d (A • UpperHalfPlane.I) UpperHalfPlane.I = 0 :=
        graze_vanish ℓ d hd A hArc _
      rw [h0]
      simp [AtIAux.S_smul_I]
    · -- `τ ≠ A • i`: two-zero bound in the second variable
      have hid : A⁻¹ • ((A • UpperHalfPlane.I : ℍ)) = UpperHalfPlane.I := by
        rw [← mul_smul, inv_mul_cancel, one_smul]
      have hw1 : ‖(((A⁻¹) • τ : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16 := by
        have h := IsArc_inv_smul_sub_le A hA (u := τ) (v := A • UpperHalfPlane.I)
          hτ16 (by rw [sub_self, norm_zero]; norm_num)
        rw [hid] at h
        linarith
      have hw1' : ‖(((A⁻¹) • τ : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < (1:ℝ)/2/2 := by
        rw [show (1:ℝ)/2/2 = 1/4 by norm_num]
        linarith
      have hnum1 : (1:ℝ)/2 ≤ ‖(((A⁻¹) • τ : ℍ) : ℂ)‖ := half_le_norm_of_near_I hw1
      have hw2 : ‖((ModularGroup.S • ((A⁻¹) • τ) : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < (1:ℝ)/2/2 := by
        have h := norm_S_sub_S_eq ((A⁻¹) • τ) UpperHalfPlane.I
        rw [AtIAux.S_smul_I] at h
        have hI : ‖((UpperHalfPlane.I : ℍ) : ℂ)‖ = 1 := by
          rw [UpperHalfPlane.coe_I, Complex.norm_I]
        rw [h, hI, mul_one]
        rw [show (1:ℝ)/2/2 = 1/4 by norm_num]
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      have hne : (A⁻¹) • τ ≠ ModularGroup.S • ((A⁻¹) • τ) := by
        intro h
        have h2 : (A⁻¹) • τ = UpperHalfPlane.I := AtIAux.eq_I_of_S_smul_eq h.symm
        have h3 : τ = A • UpperHalfPlane.I := by
          have h4 := congrArg (fun w : ℍ => A • w) h2
          rwa [← mul_smul, mul_inv_cancel, one_smul] at h4
        exact hτI h3
      have hz1 : KfunClear ℓ d τ (((A⁻¹) • τ : ℍ)) = 0 := by
        have h := graze_vanish ℓ d hd A hArc (((A⁻¹) • τ : ℍ))
        rwa [← mul_smul, mul_inv_cancel, one_smul] at h
      have hz2 : KfunClear ℓ d τ ((ModularGroup.S • ((A⁻¹) • τ) : ℍ)) = 0 := by
        have h := arc_mul_S_vanish ℓ d hd A hA ((ModularGroup.S • ((A⁻¹) • τ) : ℍ))
        rw [mul_smul] at h
        have hSS : ModularGroup.S • (ModularGroup.S • ((A⁻¹) • τ)) = (A⁻¹) • τ := by
          rw [← mul_smul, S_mul_S_sl, neg_one_smul_sl]
        rw [hSS, ← mul_smul, mul_inv_cancel, one_smul] at h
        exact h
      have hb := AtIAux.two_zero_apply (f := fun w : ℍ => KfunClear ℓ d τ w)
        (KbcAux2.mdifferentiable_KfunClear_snd ℓ d hd τ) (c := UpperHalfPlane.I) (r := 1/2) (M := M)
        (by norm_num) (by rw [UpperHalfPlane.I_im]; norm_num) hMpos.le
        (fun w hw => hMb τ w (by linarith)
          (le_trans hw (by norm_num : (1:ℝ)/2 ≤ 3/4)))
        hw1' hw2 hne hz1 hz2
      have hkey := hb UpperHalfPlane.I (by rw [sub_self, norm_zero]; norm_num)
      have e1 : ‖((UpperHalfPlane.I : ℍ) : ℂ) - (((A⁻¹) • τ : ℍ) : ℂ)‖ ≤ 4 * D := by
        have h := IsArc_inv_smul_sub_le A hA (u := τ) (v := A • UpperHalfPlane.I)
          hτ16 (by rw [sub_self, norm_zero]; norm_num)
        rw [hid, ← hD] at h
        rw [norm_sub_rev]
        exact h
      have e1' : ‖(((A⁻¹) • τ : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ ≤ 4 * D := by
        rw [norm_sub_rev]; exact e1
      have e2 : ‖((UpperHalfPlane.I : ℍ) : ℂ) - ((ModularGroup.S • ((A⁻¹) • τ) : ℍ) : ℂ)‖ ≤ 16 * D := by
        have h := norm_S_sub_S_eq UpperHalfPlane.I ((A⁻¹) • τ)
        rw [AtIAux.S_smul_I] at h
        have hI : ‖((UpperHalfPlane.I : ℍ) : ℂ)‖ = 1 := by
          rw [UpperHalfPlane.coe_I, Complex.norm_I]
        rw [h, hI, one_mul]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hnum1, e1, e1', norm_nonneg (((A⁻¹) • τ : ℍ) : ℂ),
          norm_nonneg ((τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ))]
      have h4 : ‖KfunClear ℓ d τ UpperHalfPlane.I‖ ≤ 16 * M * (4 * D) * (16 * D) := by
        have heq : (4 * M / ((1:ℝ)/2)^2 : ℝ) = 16 * M := by
          field_simp
          ring
        rw [heq] at hkey
        refine le_trans hkey ?_
        refine mul_le_mul ?_ e2 (norm_nonneg _) ?_
        · exact mul_le_mul_of_nonneg_left e1 (by positivity)
        · positivity
      have hfinal : 16 * M * (4 * D) * (16 * D)
          ≤ 1024 * M * ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖
            * ‖(τ:ℂ) - ((A • (ModularGroup.S • UpperHalfPlane.I) : ℍ) : ℂ)‖ := by
        rw [AtIAux.S_smul_I]
        rw [hD]
        ring_nf
        exact le_refl _
      linarith [h4, hfinal]
  · -- `z ≠ i`: two-zero bound in the first variable
    have hzS : z ≠ ModularGroup.S • z := fun h => hzi (AtIAux.eq_I_of_S_smul_eq h.symm)
    have hci : ((Complex.I : ℂ)) = ((UpperHalfPlane.I : ℍ) : ℂ) := UpperHalfPlane.coe_I.symm
    have hA1 : ‖((A • z : ℍ) : ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < (1:ℝ)/4/2 := by
      have h := IsArc_smul_sub A hA z UpperHalfPlane.I
      have h2 : ‖((A • z : ℍ) : ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖
          = ‖(z:ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖
            / (‖(z:ℂ) + 1‖ * ‖((UpperHalfPlane.I : ℍ) : ℂ) + 1‖) := by
        rw [h, norm_div, norm_mul]
      rw [UpperHalfPlane.coe_I] at h2
      rw [h2]
      rw [show (1:ℝ)/4/2 = 1/8 by norm_num]
      have h3 : (1:ℝ)/2 ≤ ‖(z:ℂ) + 1‖ := half_le_norm_add_one_of_near_I hz16
      have h4 : (1:ℝ) ≤ ‖(Complex.I) + 1‖ := by
        rw [add_comm, norm_one_add_I]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have h5 : (1:ℝ)/2 ≤ ‖((ModularGroup.S • z : ℍ) : ℂ) + 1‖ := half_le_norm_one_add_S_of_near_I hz16
    have hI2 : (1:ℝ) ≤ ‖(Complex.I) + 1‖ := by
      rw [add_comm, norm_one_add_I]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hS : ‖((ModularGroup.S • z : ℍ) : ℂ) - Complex.I‖ ≤ 2 * ‖(z:ℂ) - Complex.I‖ := by
      have h1 := norm_S_sub_S_eq z UpperHalfPlane.I
      rw [AtIAux.S_smul_I, UpperHalfPlane.coe_I, Complex.norm_I, mul_one] at h1
      have hnum : (1:ℝ)/2 ≤ ‖(z:ℂ)‖ := half_le_norm_of_near_I hz16
      rw [h1]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg ((z:ℂ) - Complex.I)]
    have hA2 : ‖((A • (ModularGroup.S • z) : ℍ) : ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < (1:ℝ)/4/2 := by
      have h := IsArc_smul_sub A hA (ModularGroup.S • z) UpperHalfPlane.I
      have h2 : ‖((A • (ModularGroup.S • z) : ℍ) : ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖
          = ‖((ModularGroup.S • z : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖
            / (‖((ModularGroup.S • z : ℍ) : ℂ) + 1‖
              * ‖((UpperHalfPlane.I : ℍ) : ℂ) + 1‖) := by
        rw [h, norm_div, norm_mul]
      rw [UpperHalfPlane.coe_I] at h2
      rw [h2]
      rw [show (1:ℝ)/4/2 = 1/8 by norm_num]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hS, h5, hI2, hz16.le, norm_nonneg ((z:ℂ) - Complex.I)]
    have hne : A • z ≠ A • (ModularGroup.S • z) := fun h =>
      hzi (AtIAux.eq_I_of_S_smul_eq (smul_left_cancel A h.symm))
    have hz1 : KfunClear ℓ d (A • z) z = 0 := graze_vanish ℓ d hd A hArc z
    have hz2 : KfunClear ℓ d (A • (ModularGroup.S • z)) z = 0 := by
      have h := arc_mul_S_vanish ℓ d hd A hA z
      rwa [mul_smul] at h
    have hb := AtIAux.two_zero_apply (f := fun w : ℍ => KfunClear ℓ d w z)
      (KbcAux2.mdifferentiable_KfunClear_fst ℓ d hd z) (c := A • UpperHalfPlane.I) (r := 1/4)
      (M := M) (by norm_num) (by rw [IsArc_im_I A hA]; norm_num) hMpos.le
      (fun w hw => hMb w z hw (by rw [UpperHalfPlane.coe_I]; linarith [hz4]))
      hA1 hA2 hne hz1 hz2
    have hkey := hb τ (by linarith)
    refine le_trans hkey ?_
    have he : (4 * M / (1/4)^2 : ℝ) = 64 * M := by
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) (norm_nonneg _)

/-- `1 ≤ ‖w + 1‖` for `w` on the disc of radius `1/16` around `i`. -/
lemma one_le_norm_add_one_of_near_I {w : ℍ} (hw : ‖(w:ℂ) - Complex.I‖ < 1/16) :
    (1:ℝ) ≤ ‖(w:ℂ) + 1‖ := by
  have h : ‖(1:ℂ) + Complex.I‖ ≤ ‖(w:ℂ) + 1‖ + ‖(w:ℂ) - Complex.I‖ := by
    have := norm_sub_le ((w:ℂ) + 1) ((w:ℂ) - Complex.I)
    rw [show (w:ℂ) + 1 - ((w:ℂ) - Complex.I) = 1 + Complex.I by ring] at this
    exact this
  rw [norm_one_add_I] at h
  have h2 : (1:ℝ) ≤ Real.sqrt 2 - 1/16 := one_le_sqrt_two_sub_sixteenth
  linarith

/-- `‖w‖ ≤ 2` for `w` on the disc of radius `1/16` around `i`. -/
lemma norm_le_two_of_near_I {w : ℍ} (hw : ‖(w:ℂ) - Complex.I‖ < 1/16) :
    ‖(w:ℂ)‖ ≤ 2 := by
  have h : ‖(w:ℂ)‖ ≤ ‖(Complex.I:ℂ)‖ + ‖(w:ℂ) - Complex.I‖ := by
    have := norm_add_le Complex.I ((w:ℂ) - Complex.I)
    rw [show (Complex.I:ℂ) + ((w:ℂ) - Complex.I) = (w:ℂ) by ring] at this
    exact this
  rw [Complex.norm_I] at h
  linarith

/-- **`j τ - j z` dominates the product of the two branch distances near `(A • i, i)`.** -/
theorem j_lower_arc (A : SL(2, ℤ)) (hA : IsArc A) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ τ z : ℍ,
      ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ → ‖(z:ℂ) - Complex.I‖ < ρ →
      c * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖)
        ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
  obtain ⟨ρI, cI, hρI, hcI, hb⟩ := AtIAux.j_lower_I
  have hmin1 : min (ρI/128) (1/128) ≤ ρI/128 := min_le_left _ _
  have hmin2 : min (ρI/128) (1/128) ≤ 1/128 := min_le_right _ _
  refine ⟨min (ρI/128) (1/128), cI/16, lt_min (by linarith [hρI]) (by norm_num), by positivity,
    fun τ z hτ hz => ?_⟩
  have hρle1 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16 :=
    lt_of_lt_of_le hτ (le_trans hmin2 (by norm_num))
  have hz16 : ‖(z:ℂ) - Complex.I‖ < 1/16 :=
    lt_of_lt_of_le hz (le_trans hmin2 (by norm_num))
  have hρ128 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρI/128 :=
    lt_of_lt_of_le hτ hmin1
  have hz128 : ‖(z:ℂ) - Complex.I‖ < ρI/128 :=
    lt_of_lt_of_le hz hmin1
  have hid : A⁻¹ • ((A • UpperHalfPlane.I : ℍ)) = UpperHalfPlane.I := by
    rw [← mul_smul, inv_mul_cancel, one_smul]
  have hτ'le : ‖((((A⁻¹) • τ : ℍ) : ℂ)) - ((UpperHalfPlane.I : ℍ) : ℂ)‖
      ≤ 4 * ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ := by
    have h := IsArc_inv_smul_sub_le A hA (u := τ) (v := A • UpperHalfPlane.I)
      (lt_of_lt_of_le hρle1 (by norm_num)) (by rw [sub_self, norm_zero]; norm_num)
    rw [hid] at h
    exact h
  have hτ'16 : ‖((((A⁻¹) • τ : ℍ) : ℂ)) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16 := by
    refine lt_of_le_of_lt hτ'le ?_
    have h2 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/128 :=
      lt_of_lt_of_le hτ hmin2
    linarith
  have hτ'I : ‖((((A⁻¹) • τ : ℍ) : ℂ)) - Complex.I‖ < ρI := by
    have h := hτ'le
    rw [show ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I from UpperHalfPlane.coe_I] at h
    refine lt_of_le_of_lt h ?_
    linarith [hρ128]
  have hnumz : (1:ℝ)/2 ≤ ‖(z:ℂ)‖ := half_le_norm_of_near_I hz16
  have hSzI : ‖((ModularGroup.S • z : ℍ) : ℂ) - Complex.I‖ < ρI := by
    have h := norm_S_sub_S_eq z UpperHalfPlane.I
    rw [AtIAux.S_smul_I, UpperHalfPlane.coe_I, Complex.norm_I, mul_one] at h
    rw [h, div_lt_iff₀ (by linarith [hnumz])]
    nlinarith [hz128, hnumz]
  have hmain := hb (((A⁻¹) • τ : ℍ)) (ModularGroup.S • z) hτ'I hSzI
  rw [KernelFacts.jInvariantFun_S_smul] at hmain
  rw [jInvariantFun_smul_of_slash A⁻¹ τ] at hmain
  have hτ'A : ((A • ((A⁻¹) • τ) : ℍ) : ℂ) = (τ:ℂ) := by
    rw [← mul_smul, mul_inv_cancel, one_smul]
  set N : ℝ := ‖((((A⁻¹) • τ : ℍ)) : ℂ) - (z:ℂ)‖ with hN
  set M : ℝ := ‖((((A⁻¹) • τ : ℍ)) : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ with hM
  set D1 : ℝ := ‖(((A⁻¹) • τ : ℍ) : ℂ) + 1‖ * ‖(z:ℂ) + 1‖ with hD1def
  set D2 : ℝ := ‖(((A⁻¹) • τ : ℍ) : ℂ) + 1‖ * ‖((ModularGroup.S • z : ℍ) : ℂ) + 1‖ with hD2def
  set B : ℝ := ‖(z:ℂ)‖ * ‖((((A⁻¹) • τ : ℍ)) : ℂ)‖ with hBdef
  have hD1 : (1:ℝ) ≤ D1 := by
    rw [hD1def]
    have h1 : (1:ℝ) ≤ ‖(((A⁻¹) • τ : ℍ) : ℂ) + 1‖ := one_le_norm_add_one_of_near_I hτ'16
    have h2 : (1:ℝ) ≤ ‖(z:ℂ) + 1‖ := one_le_norm_add_one_of_near_I hz16
    nlinarith
  have hD2 : (1:ℝ)/4 ≤ D2 := by
    rw [hD2def]
    have h1 : (1:ℝ)/2 ≤ ‖(((A⁻¹) • τ : ℍ) : ℂ) + 1‖ := half_le_norm_add_one_of_near_I hτ'16
    have h2 : (1:ℝ)/2 ≤ ‖((ModularGroup.S • z : ℍ) : ℂ) + 1‖ :=
      half_le_norm_one_add_S_of_near_I hz16
    nlinarith
  have hB : B ≤ 4 * D1 := by
    rw [hBdef, hD1def]
    have h1 : ‖((((A⁻¹) • τ : ℍ)) : ℂ)‖ ≤ 2 := norm_le_two_of_near_I hτ'16
    have h2 : ‖(z:ℂ)‖ ≤ 2 := norm_le_two_of_near_I hz16
    nlinarith
  have hNnn : (0:ℝ) ≤ N := by rw [hN]; exact norm_nonneg _
  have hMnn : (0:ℝ) ≤ M := by rw [hM]; exact norm_nonneg _
  have hBpos : (0:ℝ) < B := by
    rw [hBdef]
    have h1 : (1:ℝ)/2 ≤ ‖((((A⁻¹) • τ : ℍ)) : ℂ)‖ := half_le_norm_of_near_I hτ'16
    nlinarith [h1, hnumz]
  have ha : ‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ = N / D1 := by
    have h := IsArc_smul_sub A hA ((A⁻¹) • τ) z
    rw [hτ'A] at h
    rw [h, norm_div, norm_mul]
  have hb' : ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖ = M / D2 := by
    have h := IsArc_smul_sub A hA ((A⁻¹) • τ) (ModularGroup.S • z)
    rw [hτ'A] at h
    rw [h, norm_div, norm_mul]
  have hSA : ‖((ModularGroup.S • z : ℍ) : ℂ) - ((ModularGroup.S • ((A⁻¹) • τ) : ℍ) : ℂ)‖
      = N / B := by
    rw [norm_S_sub_S_eq z ((A⁻¹) • τ), hN, hBdef, norm_sub_rev]
  have hSB : ‖((ModularGroup.S • z : ℍ) : ℂ) - (((A⁻¹) • τ : ℍ) : ℂ)‖ = M := by
    rw [norm_sub_rev, hM]
  have e1 : (1:ℝ)/4 * (N / D1) ≤ N / B := by
    rw [show (1:ℝ)/4 * (N / D1) = N / (4 * D1) by ring]
    exact div_le_div_of_nonneg_left hNnn hBpos hB
  have e2 : (1:ℝ)/4 * (M / D2) ≤ M := by
    rw [show (1:ℝ)/4 * (M / D2) = M / (4 * D2) by ring]
    have h := div_le_div_of_nonneg_left hMnn (by norm_num : (0:ℝ) < 1)
      (by linarith [hD2] : (1:ℝ) ≤ 4 * D2)
    rwa [div_one] at h
  rw [hSA, hSB] at hmain
  rw [ha, hb']
  calc (cI/16) * ((N / D1) * (M / D2))
      = cI * ((1:ℝ)/4 * (N / D1)) * ((1:ℝ)/4 * (M / D2)) := by ring
    _ ≤ cI * (N / B) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left e1 hcI.le) e2 (by positivity) (by positivity)
    _ ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
        have h : cI * (N / B) * M = cI * M * (N / B) := by ring
        rw [h]; exact hmain

/-- **The kernel is bounded on a Euclidean neighbourhood of the tangency point `(A • i, i)`.** -/
theorem key_bound_arc (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (A : SL(2, ℤ)) (hA : IsArc A) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ τ z : ℍ,
      ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ → ‖(z:ℂ) - Complex.I‖ < ρ →
      ‖Kfun ℓ d τ z‖ ≤ C := by
  obtain ⟨ρ1, C1, hρ1, hC1, hb1⟩ := two_zero_KfunClear_arc ℓ d hd A hA
  obtain ⟨ρ2, c2, hρ2, hc2, hb2⟩ := j_lower_arc A hA
  obtain ⟨ρ3, δ, hρ3, hδ, hb3⟩ := AtIAux.exists_DeltaFun_lower (A • UpperHalfPlane.I)
  obtain ⟨ρ4, δz, hρ4, hδz, hb4⟩ := AtIAux.exists_DeltaFun_lower UpperHalfPlane.I
  obtain ⟨C0, hC0pos, hC0⟩ := KaxisMid.exists_bound_Kfun_of_coincidence ℓ d hd
    (isCompact_closedBall (A • UpperHalfPlane.I) 1) (isCompact_closedBall UpperHalfPlane.I 1)
  set ρ : ℝ := min (min ρ1 ρ2) (min (min ρ3 ρ4) (1/4)) with hρdef
  have hρpos : 0 < ρ :=
    lt_min (lt_min hρ1 hρ2) (lt_min (lt_min hρ3 hρ4) (by norm_num))
  have hρρ1 : ρ ≤ ρ1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ2 : ρ ≤ ρ2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρ3 : ρ ≤ ρ3 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρρ4 : ρ ≤ ρ4 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ14 : ρ ≤ 1/4 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, max C0 (C1 / (δ * δz ^ (if d = 8 then 1 else 2) * c2)), hρpos,
    le_trans hC0pos.le (le_max_left _ _), fun τ z hτ hz => ?_⟩
  by_cases hcoin : jInvariantFun τ = jInvariantFun z
  · have h1 : dist τ (A • UpperHalfPlane.I) ≤ 1 :=
      AtIAux.dist_le_one_of_norm_lt (c := A • UpperHalfPlane.I)
        (by rw [IsArc_im_I A hA]; linarith) hτ
    have h2 : dist z UpperHalfPlane.I ≤ 1 :=
      AtIAux.dist_le_one_of_norm_lt (c := UpperHalfPlane.I)
        (by rw [UpperHalfPlane.I_im]; linarith) hz
    exact le_trans (hC0 τ z h1 h2 hcoin) (le_max_left _ _)
  · have hτ1 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ1 := lt_of_lt_of_le hτ hρρ1
    have hz1 : ‖(z:ℂ) - Complex.I‖ < ρ1 := lt_of_lt_of_le hz hρρ1
    have hτ2 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ2 := lt_of_lt_of_le hτ hρρ2
    have hz2 : ‖(z:ℂ) - Complex.I‖ < ρ2 := lt_of_lt_of_le hz hρρ2
    have hτ3 : ‖(τ:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ3 := lt_of_lt_of_le hτ hρρ3
    have hz4 : ‖(z:ℂ) - Complex.I‖ < ρ4 := lt_of_lt_of_le hz hρρ4
    have hΔτ : δ ≤ ‖DeltaFun τ‖ := hb3 τ hτ3
    have hΔz : δz ≤ ‖DeltaFun z‖ := hb4 z hz4
    have h2z := hb1 τ z hτ1 hz1
    have hJlow := hb2 τ z hτ2 hz2
    have hτz : (0 : ℝ) < ‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h
      exact hcoin (by
        rw [show τ = A • z from UpperHalfPlane.ext (sub_eq_zero.mp h),
          jInvariantFun_smul_of_slash])
    have hzSz : (0 : ℝ) < ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h
      refine hcoin ?_
      rw [show τ = A • (ModularGroup.S • z) from UpperHalfPlane.ext (sub_eq_zero.mp h)]
      rw [jInvariantFun_smul_of_slash, KernelFacts.jInvariantFun_S_smul]
    have hne : (0:ℝ) < ‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖ :=
      mul_pos hτz hzSz
    have hKc : ‖KfunClear ℓ d τ z‖ ≤ C1 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
        * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖) := by
      simpa only [mul_assoc] using h2z
    have hJlow' : c2 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
        * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖) ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
      simpa only [mul_assoc] using hJlow
    have hden : δ * δz ^ (if d = 8 then 1 else 2) * (c2 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
        * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖)) ≤ ‖growthPrefactor d τ z‖ := by
      rw [KaxisMid.norm_growthPrefactor]
      have hBe : δz ^ (if d = 8 then 1 else 2) ≤ ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) :=
        pow_le_pow_left₀ hδz.le hΔz _
      have h3 : δ * δz ^ (if d = 8 then 1 else 2)
          ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) :=
        mul_le_mul hΔτ hBe (pow_nonneg hδz.le _) (norm_nonneg _)
      calc δ * δz ^ (if d = 8 then 1 else 2) * (c2 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
            * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖))
          = c2 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
              * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖)
              * (δ * δz ^ (if d = 8 then 1 else 2)) := by ring
        _ ≤ ‖jInvariantFun τ - jInvariantFun z‖ * (‖DeltaFun τ‖
              * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2)) :=
            mul_le_mul hJlow' h3 (by positivity) (norm_nonneg _)
        _ = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2)
              * ‖jInvariantFun τ - jInvariantFun z‖ := by ring
    have hgp_pos : 0 < ‖growthPrefactor d τ z‖ :=
      lt_of_lt_of_le (by positivity) hden
    have hgpne : growthPrefactor d τ z ≠ 0 := by
      simp only [growthPrefactor]
      exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
        (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _))) (sub_ne_zero.mpr hcoin)
    have hKfun_eq : ‖Kfun ℓ d τ z‖
        = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := by
      have h1 := ClearLink.KPlusClear_eq_smul d hd τ z hcoin
      have h2 := ClearLink.KMinusClear_eq_smul ℓ d hd τ z hcoin
      have heq : Kfun ℓ d τ z = KfunClear ℓ d τ z / growthPrefactor d τ z := by
        rw [Kfun, KfunClear, h1, h2]
        field_simp
      rw [heq, norm_div]
    rw [hKfun_eq]
    refine le_trans ?_ (le_max_right _ _)
    rw [div_le_iff₀ hgp_pos]
    refine le_trans (b := C1 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
      * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖)) ?_ ?_
    · simpa only [mul_assoc] using hKc
    · have hDpos : (0:ℝ) < δ * δz ^ (if d = 8 then 1 else 2) * c2 := by positivity
      rw [show C1 / (δ * δz ^ (if d = 8 then 1 else 2) * c2) * ‖growthPrefactor d τ z‖
          = C1 * ‖growthPrefactor d τ z‖ / (δ * δz ^ (if d = 8 then 1 else 2) * c2) by ring]
      rw [le_div_iff₀ hDpos]
      have hden' : ‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖
          * (δ * δz ^ (if d = 8 then 1 else 2) * c2) ≤ ‖growthPrefactor d τ z‖ := by
        calc ‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖
              * (δ * δz ^ (if d = 8 then 1 else 2) * c2)
            = δ * δz ^ (if d = 8 then 1 else 2) * (c2 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
                * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖)) := by ring
          _ ≤ ‖growthPrefactor d τ z‖ := hden
      calc C1 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖
            * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖)
            * (δ * δz ^ (if d = 8 then 1 else 2) * c2)
          = C1 * (‖(τ:ℂ) - ((A • z : ℍ) : ℂ)‖ * ‖(τ:ℂ) - ((A • (ModularGroup.S • z) : ℍ) : ℂ)‖
              * (δ * δz ^ (if d = 8 then 1 else 2) * c2)) := by ring
        _ ≤ C1 * ‖growthPrefactor d τ z‖ := mul_le_mul_of_nonneg_left hden' hC1.le

end Work.Asymptotics.Graze
