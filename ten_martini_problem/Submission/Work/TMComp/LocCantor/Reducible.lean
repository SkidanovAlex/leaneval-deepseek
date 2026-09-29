import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.LocCantor.Bloch
import Submission.Work.TMComp.LocCantor.arg_lift

/-!
# C17 (`P_LocCantor`) — from a Bloch wave to a reducibility certificate

(AJ §5, items (5.3)–(5.12).)
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology Set

namespace Work.TMComp
open Work.TMContract
open Work.TMComp.LocCantor

variable {α θ lam E : ℝ} {u : ℤ → ℂ}

theorem sgnMat_det (σ : ℝ) : (sgnMat σ).det = σ := by
  simp [sgnMat, Matrix.det_fin_two]

theorem sgnMat_mul_self {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : sgnMat σ * sgnMat σ = 1 := by
  rcases hσ with rfl | rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sgnMat, Matrix.mul_fin_two]

/-- `diag(1,σ) R_θ diag(1,σ) = R_{σθ}` for `σ = ±1`. -/
theorem sgnMat_conj_rot {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (θ : ℝ) :
    sgnMat σ * rot θ * sgnMat σ = rot (σ * θ) := by
  rcases hσ with rfl | rfl
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [sgnMat, rot, Matrix.mul_fin_two]
  · have h1 : Real.cos (2 * Real.pi * (-1 * θ)) = Real.cos (2 * Real.pi * θ) := by
      rw [show 2 * Real.pi * (-1 * θ) = -(2 * Real.pi * θ) by ring, Real.cos_neg]
    have h2 : Real.sin (2 * Real.pi * (-1 * θ)) = -Real.sin (2 * Real.pi * θ) := by
      rw [show 2 * Real.pi * (-1 * θ) = -(2 * Real.pi * θ) by ring, Real.sin_neg]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sgnMat, rot, Matrix.mul_fin_two, h1, h2]

theorem rot_add (a b : ℝ) : rot a * rot b = rot (a + b) := by
  have h1 : 2 * Real.pi * (a + b) = 2 * Real.pi * a + 2 * Real.pi * b := by ring
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [rot, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      Fin.isValue, h1, Real.cos_add, Real.sin_add]
    <;> ring

theorem rot_neg_mul (a : ℝ) : rot (-a) * rot a = 1 := by
  rw [rot_add, neg_add_cancel]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [rot, Matrix.one_fin_two]

theorem rot_intCast (k : ℤ) : rot ((k : ℝ)) = 1 := by
  have hc : Real.cos (2 * Real.pi * (k : ℝ)) = 1 := by
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring, Real.cos_int_mul_two_pi]
  have hs : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    simpa using Real.sin_add_int_mul_two_pi (0 : ℝ) k
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.one_fin_two, hc, hs]

/-- Rotation of a vector in polar form. -/
theorem rot_mulVec_polar (a b r : ℝ) :
    Matrix.mulVec (rot a) ![r * Real.cos (2 * Real.pi * b), r * Real.sin (2 * Real.pi * b)]
      = ![r * Real.cos (2 * Real.pi * (a + b)), r * Real.sin (2 * Real.pi * (a + b))] := by
  rw [Matrix.mulVec_fin_two]
  have h1 : 2 * Real.pi * (a + b) = 2 * Real.pi * a + 2 * Real.pi * b := by ring
  simp only [rot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Fin.isValue, h1,
    Real.cos_add, Real.sin_add]
  ring_nf

/-- Scalar identity behind `det [W, W̄] = -2i det [Re W, Im W]`. -/
theorem conj_mul_sub (z w : ℂ) :
    z * conj w - conj z * w = Complex.I * (((-2 * (z.re * w.im - z.im * w.re) : ℝ)) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    ring
  · simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    ring

/-- `det [W, W̄] = -2i det [Re W, Im W]`. -/
theorem det_blochMat_eq_det_blochReal (x : ℝ) :
    (blochMat α θ u x).det = -2 * Complex.I * (((blochReal α θ u x).det : ℝ) : ℂ) := by
  have hW : (blochMat α θ u x).det
      = blochVec α θ u x 0 * conj (blochVec α θ u x 1)
        - conj (blochVec α θ u x 0) * blochVec α θ u x 1 := by
    simp [blochMat, Matrix.det_fin_two_of, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val', Fin.isValue]
  have hA : ((blochReal α θ u x).det : ℝ)
      = (blochVec α θ u x 0).re * (blochVec α θ u x 1).im
        - (blochVec α θ u x 0).im * (blochVec α θ u x 1).re := by
    simp [blochReal, Matrix.det_fin_two_of, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val', Fin.isValue]
  rw [hW, hA, conj_mul_sub]
  push_cast
  ring


theorem rot_neg_intCast (k : ℤ) : rot (-(k : ℝ)) = 1 := by
  have h := rot_neg_mul ((k : ℝ))
  rw [rot_intCast k, mul_one] at h
  exact h

theorem rot_det (c : ℝ) : (rot c).det = 1 := by
  show (!![Real.cos (2 * Real.pi * c), -Real.sin (2 * Real.pi * c);
      Real.sin (2 * Real.pi * c), Real.cos (2 * Real.pi * c)] : Matrix (Fin 2) (Fin 2) ℝ).det = 1
  rw [Matrix.det_fin_two_of, ← Real.cos_sq_add_sin_sq (2 * Real.pi * c)]
  ring

theorem tmR_det (lam E x : ℝ) : (tmR lam E x).det = 1 := by
  show (!![E - 2 * lam * Real.cos (2 * Real.pi * x), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).det = 1
  rw [Matrix.det_fin_two_of]
  ring

/-- The main reduction of AJ §5, abstract form: given a determinant-one, one-periodic,
real-analytic conjugacy `B` of the dual cocycle to the constant rotation `R_{-σθ}`, correcting
the homotopy class of `B` with an analytic argument function (child `arg_lift`) puts `E/λ` in
`RedSet` and gives the rotation-number identity. -/
theorem reducible_of_conjugacy
    (hconv : ∀ (α lam E : ℝ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ) (k : ℤ),
      HasDegree B k → (∀ x, B (x + 1) = B x) → (∀ x, (B x).det = 1) → Continuous φ →
      (∀ x, φ (x + 1) = φ x) → (∀ x, B (x + α) * tmR lam E x = rot (φ x) * B x) →
      ∃ j : ℤ, rotLift α lam E = 2 * (∫ x in (0:ℝ)..1, φ x) - 2 * (k : ℝ) * α + 2 * (j : ℝ))
    {α θ lam E : ℝ} (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hBan : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ)
    (hBper : ∀ x, B (x + 1) = B x)
    (hBdet : ∀ x, (B x).det = 1)
    (hBrel : ∀ x, B (x + α) * tmR lam⁻¹ (E * lam⁻¹) x = rot (-(σ * θ)) * B x) :
    ∃ (k j : ℤ), (E * lam⁻¹) ∈ RedSet α lam⁻¹ ∧
      ids α lam⁻¹ (E * lam⁻¹) = 1 + 2 * (σ * θ) + 2 * (k : ℝ) * α - 2 * (j : ℝ) := by
  -- the first column of `B` never vanishes, because `det B = 1`
  have hne : ∀ x, (B x 0 0, B x 1 0) ≠ 0 := by
    intro x hx
    have h1 : B x 0 0 = 0 := by simpa using congrArg Prod.fst hx
    have h2 : B x 1 0 = 0 := by simpa using congrArg Prod.snd hx
    have h0 : (B x).det = 0 := by
      rw [Matrix.det_fin_two, h1, h2]
      ring
    have := hBdet x
    rw [h0] at this
    norm_num at this
  -- the analytic argument function of the first column
  obtain ⟨k, η, hηan, hηper, hang⟩ := arg_lift (f := fun x => (B x 0 0, B x 1 0))
    (hBan 0 0) (hBan 1 0) (fun x => by rw [hBper x]) hne
  -- correct the homotopy class: multiply by `R_{-kx}`, whose degree is `-k`
  set η' : ℝ → ℝ := fun x => η x - (k : ℝ) * x with hη'def
  have hid : AnalyticOnNhd ℝ (fun x : ℝ => x) Set.univ := analyticOnNhd_id
  have hη'an : AnalyticOnNhd ℝ η' Set.univ := by
    have h := hηan.sub (hid.const_smul (c := (k : ℝ)))
    have h2 : (η - (k : ℝ) • fun x : ℝ => x) = η' := by
      funext x
      simp [hη'def, Pi.sub_apply, Pi.smul_apply]
    rwa [h2] at h
  have hη'cont : Continuous η' := continuousOn_univ.mp hη'an.continuousOn
  have hη'per : ∀ x, η' (x + 1) = η' x := by
    intro x
    simp only [hη'def]
    rw [hηper x]
    ring
  set Bp : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x => rot (-((k : ℝ) * x)) * B x with hBpdef
  have hBpdet : ∀ x, (Bp x).det = 1 := by
    intro x
    rw [hBpdef, Matrix.det_mul, rot_det, one_mul, hBdet x]
  have hBpper : ∀ x, Bp (x + 1) = Bp x := by
    intro x
    rw [hBpdef]
    show rot (-((k : ℝ) * (x + 1))) * B (x + 1) = rot (-((k : ℝ) * x)) * B x
    rw [hBper x,
      show -((k : ℝ) * (x + 1)) = -((k : ℝ) * x) + -(k : ℝ) by ring, ← rot_add,
      rot_neg_intCast, mul_one]
  have hcos2 : AnalyticOnNhd ℝ (fun x => Real.cos (2 * Real.pi * (-((k : ℝ) * x)))) Set.univ :=
    (Real.analyticOnNhd_cos (s := Set.univ)).comp
      (((hid.const_smul (c := (k : ℝ))).neg).const_smul (c := 2 * Real.pi))
      (by intro x _; exact Set.mem_univ _)
  have hsin2 : AnalyticOnNhd ℝ (fun x => Real.sin (2 * Real.pi * (-((k : ℝ) * x)))) Set.univ :=
    (Real.analyticOnNhd_sin (s := Set.univ)).comp
      (((hid.const_smul (c := (k : ℝ))).neg).const_smul (c := 2 * Real.pi))
      (by intro x _; exact Set.mem_univ _)
  have hf00 : ∀ x, Bp x 0 0 = Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 0
      - Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 0 := by
    intro x
    rw [hBpdef]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rot, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
      Matrix.head_cons, Matrix.head_fin_const]
    try ring
  have hf01 : ∀ x, Bp x 0 1 = Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 1
      - Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 1 := by
    intro x
    rw [hBpdef]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rot, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
      Matrix.head_cons, Matrix.head_fin_const]
    try ring
  have hf10 : ∀ x, Bp x 1 0 = Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 0
      + Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 0 := by
    intro x
    rw [hBpdef]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rot, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
      Matrix.head_cons, Matrix.head_fin_const]
    try ring
  have hf11 : ∀ x, Bp x 1 1 = Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 1
      + Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 1 := by
    intro x
    rw [hBpdef]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rot, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
      Matrix.head_cons, Matrix.head_fin_const]
    try ring
  have hBpan : ∀ i j, AnalyticOnNhd ℝ (fun x => Bp x i j) Set.univ := by
    intro i j
    fin_cases i <;> fin_cases j
    · show AnalyticOnNhd ℝ (fun x => Bp x 0 0) Set.univ
      rw [show (fun x => Bp x 0 0) = (fun x => Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 0
        - Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 0) from funext hf00]
      exact (hcos2.mul (hBan 0 0)).sub (hsin2.mul (hBan 1 0))
    · show AnalyticOnNhd ℝ (fun x => Bp x 0 1) Set.univ
      rw [show (fun x => Bp x 0 1) = (fun x => Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 1
        - Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 1) from funext hf01]
      exact (hcos2.mul (hBan 0 1)).sub (hsin2.mul (hBan 1 1))
    · show AnalyticOnNhd ℝ (fun x => Bp x 1 0) Set.univ
      rw [show (fun x => Bp x 1 0) = (fun x => Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 0
        + Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 0) from funext hf10]
      exact (hsin2.mul (hBan 0 0)).add (hcos2.mul (hBan 1 0))
    · show AnalyticOnNhd ℝ (fun x => Bp x 1 1) Set.univ
      rw [show (fun x => Bp x 1 1) = (fun x => Real.sin (2 * Real.pi * (-((k : ℝ) * x))) * B x 0 1
        + Real.cos (2 * Real.pi * (-((k : ℝ) * x))) * B x 1 1) from funext hf11]
      exact (hsin2.mul (hBan 0 1)).add (hcos2.mul (hBan 1 1))
  have hBpcont : Continuous Bp :=
    continuous_matrix fun i j => continuousOn_univ.mp (hBpan i j).continuousOn
  have hBpdeg : HasDegree Bp 0 := by
    refine ⟨hBpcont, η', hη'cont, ?_, ?_⟩
    · intro x; rw [hη'per x]; ring
    · intro x
      obtain ⟨r, hr, h1, h2⟩ := hang x
      have h1' : B x 0 0 = r * Real.cos (2 * Real.pi * η x) := h1
      have h2' : B x 1 0 = r * Real.sin (2 * Real.pi * η x) := h2
      refine ⟨r, hr, ?_, ?_⟩
      · rw [hf00 x, h1', h2']
        rw [show (2 : ℝ) * Real.pi * η' x = 2 * Real.pi * (-((k : ℝ) * x)) + 2 * Real.pi * η x by
          rw [hη'def]; ring]
        rw [Real.cos_add]
        ring
      · rw [hf10 x, h1', h2']
        rw [show (2 : ℝ) * Real.pi * η' x = 2 * Real.pi * (-((k : ℝ) * x)) + 2 * Real.pi * η x by
          rw [hη'def]; ring]
        rw [Real.sin_add]
        ring
  have hBprel : ∀ x, Bp (x + α) * tmR lam⁻¹ (E * lam⁻¹) x
      = rot (-((k : ℝ) * α) - (σ * θ)) * Bp x := by
    intro x
    have h1 : Bp (x + α) = rot (-((k : ℝ) * (x + α))) * B (x + α) := by
      simp only [hBpdef]
    have h2 : Bp x = rot (-((k : ℝ) * x)) * B x := by
      simp only [hBpdef]
    have hL : rot (-((k : ℝ) * (x + α))) * (rot (-(σ * θ)) * B x)
        = rot (-((k : ℝ) * α) - ((k : ℝ) * x) - (σ * θ)) * B x := by
      rw [← mul_assoc, rot_add]
      congr 1
      congr 1
      ring_nf
    have hR : rot (-((k : ℝ) * α) - (σ * θ)) * (rot (-((k : ℝ) * x)) * B x)
        = rot (-((k : ℝ) * α) - ((k : ℝ) * x) - (σ * θ)) * B x := by
      rw [← mul_assoc, rot_add]
      congr 1
      congr 1
      ring_nf
    rw [h1, h2, mul_assoc, hBrel x]
    exact hL.trans hR.symm

  refine ⟨k, ?_⟩
  · obtain ⟨j, hj⟩ := hconv α lam⁻¹ (E * lam⁻¹) Bp (fun _ => -((k : ℝ) * α) - (σ * θ)) 0 hBpdeg
      hBpper hBpdet continuous_const (fun _ => rfl) hBprel
    refine ⟨j, ⟨Bp, -((k : ℝ) * α) - (σ * θ), hBpan, hBpper, hBpdet, hBpdeg, hBprel⟩, ?_⟩
    rw [ids, hj]
    simp only [intervalIntegral.integral_const, sub_zero, zero_mul, mul_zero]
    ring

end Work.TMComp
