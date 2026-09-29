import Mathlib
import Submission.Work.TMContract.Defs

/-!
# RotBasics: vocabulary for the proof of `P_RotBasics` (component C5)

This module fixes the small vocabulary in which the proof of `P_RotBasics` is phrased:

* `vc t = (cos πt, sin πt)`, the point of the unit circle at angle `πt` (the "half-turn"
  parametrization used by `pruferStep`), seen as a complex number;
* `comp a = !![a,-1;1,0]`, the companion matrix (the real transfer matrix `tmR λ E x` is
  `comp (E - 2λ cos 2πx)`);
* `smul A w`, the action of a real `2×2` matrix on `ℂ ≅ ℝ²`;
* `IsPosLift A G`, the statement that `G` presents the *positive* lift of the projective
  action of `A`: `vc (G t) = unit (A (vc t))`.

Units are half-turns: `vc (t + 1) = - vc t`, so `vc (t + 2) = vc t` and `t`, `t + 1` give the
same *direction*.
-/

namespace Work.TMComp.RotBasics

open Work.TMContract

noncomputable section

/-- The point of the unit circle at angle `π t`, as a complex number. -/
def vc (t : ℝ) : ℂ := ⟨Real.cos (Real.pi * t), Real.sin (Real.pi * t)⟩

/-- The companion matrix `[[a,-1],[1,0]]`. -/
def comp (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, -1; 1, 0]

/-- The action of a real `2×2` matrix on `ℂ ≅ ℝ²`. -/
def smul (A : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) : ℂ :=
  ⟨A 0 0 * w.re + A 0 1 * w.im, A 1 0 * w.re + A 1 1 * w.im⟩

/-- The real transfer cocycle `A_n(x) = S_E(x+(n-1)α) ⋯ S_E(x)` (the `ℂ`-valued
`iterC` restricted to real energies). -/
def iterR (α lam E : ℝ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | n + 1, x => tmR lam E (x + (n : ℝ) * α) * iterR α lam E n x

/-- `G` presents the positive lift of the projective action of `A`:
`vc (G t) = unit (A (vc t))` for all `t`. -/
def IsPosLift (A : Matrix (Fin 2) (Fin 2) ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ t, smul A (vc t) = (‖smul A (vc t)‖ : ℝ) • vc (G t)

theorem vc_norm (t : ℝ) : ‖vc t‖ = 1 := by
  have h : ‖vc t‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [vc]
    nlinarith [Real.cos_sq_add_sin_sq (Real.pi * t)]
  nlinarith [norm_nonneg (vc t)]

theorem vc_ne_zero (t : ℝ) : vc t ≠ 0 := by
  intro h
  have := vc_norm t
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem vc_add (s t : ℝ) : vc (s + t) = vc s * vc t := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.mul_re]
    rw [show Real.pi * (s + t) = Real.pi * s + Real.pi * t by ring, Real.cos_add]
  · simp only [vc, Complex.mul_im]
    rw [show Real.pi * (s + t) = Real.pi * s + Real.pi * t by ring, Real.sin_add]
    ring

theorem vc_neg (t : ℝ) : vc (-t) = (starRingEnd ℂ) (vc t) := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.conj_re]
    rw [show Real.pi * -t = -(Real.pi * t) by ring, Real.cos_neg]
  · simp only [vc, Complex.conj_im]
    rw [show Real.pi * -t = -(Real.pi * t) by ring, Real.sin_neg]

theorem vc_two : vc (2 : ℝ) = 1 := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.one_re]
    rw [show Real.pi * 2 = 2 * Real.pi by ring, Real.cos_two_pi]
  · simp only [vc, Complex.one_im]
    rw [show Real.pi * 2 = 2 * Real.pi by ring, Real.sin_two_pi]

theorem vc_add_two (t : ℝ) : vc (t + 2) = vc t := by
  rw [vc_add, vc_two, mul_one]

theorem vc_sub_two (t : ℝ) : vc (t - 2) = vc t := by
  have h := vc_add_two (t - 2)
  rw [show t - 2 + 2 = t by ring] at h
  exact h.symm

theorem vc_add_nat (t : ℝ) (n : ℕ) : vc (t + (n : ℝ) * 2) = vc t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h1]
    have h2 : t + ((n : ℝ) + 1) * 2 = (t + (n : ℝ) * 2) + 2 := by ring
    rw [h2, vc_add_two, ih]

theorem vc_sub_nat (t : ℝ) (n : ℕ) : vc (t - (n : ℝ) * 2) = vc t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h1]
    have h2 : t - ((n : ℝ) + 1) * 2 = (t - (n : ℝ) * 2) - 2 := by ring
    rw [h2, vc_sub_two, ih]

/-- `vc` has period `2` in the argument, for integer multiples. -/
theorem vc_int (t : ℝ) (m : ℤ) : vc (t + m * 2) = vc t := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg m
  · rw [hn]; push_cast; exact vc_add_nat t n
  · rw [hn]
    push_cast
    have h2 : t + -(n : ℝ) * 2 = t - (n : ℝ) * 2 := by ring
    rw [h2, vc_sub_nat]

theorem vc_eq_one {w : ℝ} (h : vc w = 1) : ∃ m : ℤ, w = 2 * m := by
  have h1 : Real.cos (Real.pi * w) = 1 := by
    have := congrArg Complex.re h; simpa [vc] using this
  obtain ⟨n, hn⟩ := Real.cos_eq_one_iff (Real.pi * w) |>.mp h1
  refine ⟨n, ?_⟩
  have h2 : w = 2 * n := by
    have h3 : Real.pi * w = (n : ℝ) * (2 * Real.pi) := hn.symm
    field_simp at h3 ⊢
    linarith
  rw [h2]

/-- Two real numbers with the same `vc` differ by an even integer. -/
theorem vc_eq_iff {s t : ℝ} (h : vc s = vc t) : ∃ m : ℤ, s = t + m * 2 := by
  have h2 : vc (s - t) * vc t = vc s := by
    rw [← vc_add, show s - t + t = s by ring]
  have h3 : vc (s - t) * vc t = 1 * vc t := by rw [h2, h, one_mul]
  have h1 : vc (s - t) = 1 := mul_right_cancel₀ (vc_ne_zero t) h3
  obtain ⟨m, hm⟩ := vc_eq_one h1
  exact ⟨m, by linarith⟩

/-! ## Action of matrices on `ℂ ≅ ℝ²` -/

theorem smul_one (w : ℂ) : smul 1 w = w := by
  refine Complex.ext ?_ ?_ <;>
    simp [smul, Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]

theorem smul_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) :
    smul (A * B) w = smul A (smul B w) := by
  refine Complex.ext ?_ ?_
  · simp only [smul, Matrix.mul_apply, Complex.mul_re, Complex.mul_im, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp only [smul, Matrix.mul_apply, Complex.mul_re, Complex.mul_im, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem smul_smul_real (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (w : ℂ) :
    smul A (c • w) = c • smul A w := by
  refine Complex.ext ?_ ?_ <;>
    simp [smul, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring

theorem norm_smul_real (c : ℝ) (w : ℂ) : ‖c • w‖ = |c| * ‖w‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-- Shifting a positive lift by an even integer does not change it. -/
theorem IsPosLift.add_int (A : Matrix (Fin 2) (Fin 2) ℝ) (G : ℝ → ℝ) (m : ℤ)
    (h : IsPosLift A G) : IsPosLift A (fun t => G t + m * 2) := by
  intro t
  rw [vc_int (G t) m]
  exact h t

/-- Composition of positive lifts. -/
theorem IsPosLift.comp (A B : Matrix (Fin 2) (Fin 2) ℝ) (G H : ℝ → ℝ)
    (hG : IsPosLift A G) (hH : IsPosLift B H) : IsPosLift (A * B) (G ∘ H) := by
  intro t
  have hHt : smul B (vc t) = (‖smul B (vc t)‖ : ℝ) • vc (H t) := hH t
  have hGt : smul A (vc (H t)) = (‖smul A (vc (H t))‖ : ℝ) • vc (G (H t)) := hG (H t)
  have h1 : smul (A * B) (vc t) = (‖smul B (vc t)‖ : ℝ) • smul A (vc (H t)) := by
    conv_lhs => rw [smul_mul, hHt, smul_smul_real]
  have h2 : smul (A * B) (vc t)
      = ((‖smul B (vc t)‖ : ℝ) * ‖smul A (vc (H t))‖) • vc (G (H t)) := by
    conv_lhs => rw [h1, hGt, smul_smul]
  have h3 : ‖smul (A * B) (vc t)‖ = (‖smul B (vc t)‖ : ℝ) * ‖smul A (vc (H t))‖ := by
    rw [h1, norm_smul_real, abs_of_nonneg (norm_nonneg _)]
  calc smul (A * B) (vc t)
      = ((‖smul B (vc t)‖ : ℝ) * ‖smul A (vc (H t))‖) • vc (G (H t)) := h2
    _ = ‖smul (A * B) (vc t)‖ • vc ((G ∘ H) t) := by rw [h3]; rfl

theorem rot_entries (c : ℝ) :
    rot c 0 0 = Real.cos (2 * Real.pi * c) ∧ rot c 0 1 = -Real.sin (2 * Real.pi * c) ∧
      rot c 1 0 = Real.sin (2 * Real.pi * c) ∧ rot c 1 1 = Real.cos (2 * Real.pi * c) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [rot]

/-- Rotations are positive lifts of translations by twice the angle. -/
theorem IsPosLift.rot_lift (c : ℝ) : IsPosLift (rot c) (fun t => t + 2 * c) := by
  intro t
  obtain ⟨h00, h01, h10, h11⟩ := rot_entries c
  have hvc : smul (rot c) (vc t) = vc (t + 2 * c) := by
    refine Complex.ext ?_ ?_
    · simp only [smul, vc, Complex.mul_re, h00, h01, h10, h11]
      rw [show Real.pi * (t + 2 * c) = Real.pi * t + (2 * Real.pi * c) by ring, Real.cos_add]
      ring
    · simp only [smul, vc, Complex.mul_im, h00, h01, h10, h11]
      rw [show Real.pi * (t + 2 * c) = Real.pi * t + (2 * Real.pi * c) by ring, Real.sin_add]
      ring
  rw [hvc, vc_norm]
  simp

/-- A translation of a positive lift by a constant is a positive lift of the rotation by
half that constant, composed with the matrix. -/
theorem IsPosLift.shift (A : Matrix (Fin 2) (Fin 2) ℝ) (G : ℝ → ℝ) (c : ℝ)
    (h : IsPosLift A G) : IsPosLift (rot (c / 2) * A) (fun t => G t + c) := by
  have h1 : IsPosLift (rot (c / 2) * A) ((fun t => t + 2 * (c / 2)) ∘ G) :=
    IsPosLift.comp (rot (c / 2)) A (fun t => t + 2 * (c / 2)) G (IsPosLift.rot_lift (c / 2)) h
  convert h1 using 2 with t
  simp only [Function.comp_apply]
  ring

end

end Work.TMComp.RotBasics
