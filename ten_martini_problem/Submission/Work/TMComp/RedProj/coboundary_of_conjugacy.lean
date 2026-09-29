import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RedProj.so2_tools
import Submission.Work.TMComp.RedProj.cob_so2_angle
import Submission.Work.TMComp.RedProj.cob_polar
import Submission.Work.TMComp.RedProj.continuous_int_eq_const

namespace Work.TMComp.RedProj

open Work.TMContract
open MeasureTheory

/-!
## Elementary matrix/rotation helpers

`cobRot_mul` is the multiplicativity of AJ's rotations `rot`,
`cob_so2_form` says that a real `2×2` matrix `K` with `K * Kᵀ = 1` and `det K = 1` has the
`SO(2)` shape `!![a, -b; b, a]`, and `cob_rot_of_exp` identifies `rot` with the pair
`(cos, sin)` read off from `Complex.exp (2 π i a)`.  These are the purely algebraic part of the
"angle lift" reduction.
-/

/-- `rot` is a homomorphism: `rot a * rot b = rot (a + b)`. -/
theorem cobRot_mul (a b : ℝ) : rot a * rot b = rot (a + b) := by
  have hc : 2 * Real.pi * (a + b) = 2 * Real.pi * a + 2 * Real.pi * b := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, hc, Real.cos_add, Real.sin_add] <;> ring

/-- A `2 × 2` real matrix `K` with `K * Kᵀ = 1` and `det K = 1` is `!![a, -b; b, a]` with
`a = K 0 0` and `b = K 1 0`. -/
theorem cob_so2_form (K : Matrix (Fin 2) (Fin 2) ℝ) (horth : K * Matrix.transpose K = 1)
    (hdet : K.det = 1) :
    K = !![K 0 0, -K 1 0; K 1 0, K 0 0] := by
  have h00 : K 0 0 * K 0 0 + K 0 1 * K 0 1 = 1 := by
    have h := congrFun (congrFun horth 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply] using h
  have h01 : K 0 0 * K 1 0 + K 0 1 * K 1 1 = 0 := by
    have h := congrFun (congrFun horth 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply] using h
  have hd : K 0 0 * K 1 1 - K 0 1 * K 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  have hb : K 0 1 = -K 1 0 := by
    have key : K 1 0 * (K 0 0 * K 0 0 + K 0 1 * K 0 1)
        = (K 0 0 * K 1 0 + K 0 1 * K 1 1) * K 0 0
          - (K 0 0 * K 1 1 - K 0 1 * K 1 0) * K 0 1 := by ring
    rw [h00, mul_one, h01, hd] at key
    linarith
  have hd' : K 1 1 = K 0 0 := by
    have key : K 1 1 * (K 0 0 * K 0 0 + K 0 1 * K 0 1)
        = (K 0 0 * K 1 0 + K 0 1 * K 1 1) * K 0 1
          + (K 0 0 * K 1 1 - K 0 1 * K 1 0) * K 0 0 := by ring
    rw [h00, mul_one, h01, hd] at key
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, hd']

/-- The product of `!![a, -b; b, a]` with its transpose. -/
theorem cob_so2_sq (a b : ℝ) :
    (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.transpose (!![a, -b; b, a])
      = !![a ^ 2 + b ^ 2, 0; 0, a ^ 2 + b ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

/-- If `exp (2 π i a) = s + i t` then `rot a = !![s, -t; t, s]`. -/
theorem cob_rot_of_exp {a s t : ℝ}
    (h : Complex.exp (2 * Real.pi * a * Complex.I) = (s : ℂ) + (t : ℂ) * Complex.I) :
    rot a = !![s, -t; t, s] := by
  have h2 : ((Real.cos (2 * Real.pi * a) : ℂ) + (Real.sin (2 * Real.pi * a) : ℂ) * Complex.I)
      = (s : ℂ) + (t : ℂ) * Complex.I := by
    rw [← Complex.exp_ofReal_mul_I (2 * Real.pi * a)]
    rw [show (((2 * Real.pi * a : ℝ)) : ℂ) * Complex.I = 2 * Real.pi * a * Complex.I by
      push_cast; ring]
    exact h
  have hcos : Real.cos (2 * Real.pi * a) = s := by
    have hre := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero] at hre
    linarith
  have hsin : Real.sin (2 * Real.pi * a) = t := by
    have him := congrArg Complex.im h2
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_add] at him
    linarith
  rw [rot, hcos, hsin]

/-- If `rot a = rot b` then `a - b` is an integer. -/
theorem cob_rot_eq_sub_int {a b : ℝ} (h : rot a = rot b) : ∃ m : ℤ, a - b = (m : ℝ) := by
  have h1 : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b) := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    simpa [rot] using this
  have h2 : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b) := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
    simpa [rot] using this
  have h3 : Real.cos (2 * Real.pi * a - 2 * Real.pi * b) = 1 := by
    rw [Real.cos_sub, h1, h2]
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * b)]
  have h4 : Real.cos (2 * Real.pi * (a - b)) = 1 := by
    rwa [show 2 * Real.pi * (a - b) = 2 * Real.pi * a - 2 * Real.pi * b by ring]
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp h4
  refine ⟨m, ?_⟩
  nlinarith [hm, Real.pi_pos]

/-! ## A shift lemma for the mean

If `κ (x + 1) = κ x + w` with `w : ℤ`, then the mean of `x ↦ κ (x + α)` over a period exceeds
that of `κ` by `w α`. -/

theorem cob_integral_shift (κ : ℝ → ℝ) (hκ : Continuous κ) (w : ℤ)
    (hw : ∀ x, κ (x + 1) = κ x + (w : ℝ)) (α : ℝ) :
    (∫ x in (0 : ℝ)..1, κ (x + α)) = (∫ x in (0 : ℝ)..1, κ x) + (w : ℝ) * α := by
  have hint : ∀ a b : ℝ, IntervalIntegrable κ volume a b := fun a b => hκ.intervalIntegrable a b
  have hg1 : ∀ a : ℝ,
      (∫ x in (0 : ℝ)..1, κ (x + (a + 1))) = (∫ x in (0 : ℝ)..1, κ (x + a)) + (w : ℝ) := by
    intro a
    have hcongr : (∫ x in (0 : ℝ)..1, κ (x + (a + 1)))
        = ∫ x in (0 : ℝ)..1, (κ (x + a) + (w : ℝ)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [show x + (a + 1) = (x + a) + 1 by ring, hw]
    rw [hcongr, intervalIntegral.integral_add (f := fun x => κ (x + a))
      (g := fun _ => (w : ℝ))
      ((hκ.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1)
      intervalIntegrable_const, intervalIntegral.integral_const]
    ring
  have hgnat : ∀ (a : ℝ) (k : ℕ),
      (∫ x in (0 : ℝ)..1, κ (x + (a + (k : ℝ))))
        = (∫ x in (0 : ℝ)..1, κ (x + a)) + (k : ℝ) * (w : ℝ) := by
    intro a k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [show a + ((m + 1 : ℕ) : ℝ) = (a + (m : ℝ)) + 1 by push_cast; ring, hg1, ih]
      push_cast; ring
  have hgt : ∀ t : ℝ, (∫ x in (0 : ℝ)..1, κ (x + t))
      = (∫ x in (0 : ℝ)..1, κ x) + t * (w : ℝ) := by
    intro t
    have h1 : (∫ x in (0 : ℝ)..1, κ (x + t)) = ∫ x in t..(t + 1), κ x := by
      rw [intervalIntegral.integral_comp_add_right]
      rw [show (0 : ℝ) + t = t by ring, show (1 : ℝ) + t = t + 1 by ring]
    rw [h1]
    have h2 : (∫ x in t..(t + 1), κ x)
        = (∫ x in t..(1 : ℝ), κ x) + (∫ x in (1 : ℝ)..(t + 1), κ x) :=
      (intervalIntegral.integral_add_adjacent_intervals (hint t 1) (hint 1 (t + 1))).symm
    rw [h2]
    have h3 : (∫ x in (1 : ℝ)..(t + 1), κ x) = (∫ x in (0 : ℝ)..t, κ (x + 1)) := by
      rw [intervalIntegral.integral_comp_add_right (f := κ) (a := (0:ℝ)) (b := t) 1]
      rw [show (0 : ℝ) + 1 = 1 by ring, show t + 1 = (t + 1) by ring]
    rw [h3]
    have h4 : (∫ x in (0 : ℝ)..t, κ (x + 1)) = (∫ x in (0 : ℝ)..t, κ x) + t * (w : ℝ) := by
      have hc : (∫ x in (0 : ℝ)..t, κ (x + 1)) = ∫ x in (0 : ℝ)..t, (κ x + (w : ℝ)) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [hw x]
      rw [hc, intervalIntegral.integral_add (hint _ _) intervalIntegrable_const,
        intervalIntegral.integral_const]
      ring
    rw [h4]
    have h5 : (∫ x in t..(1 : ℝ), κ x) + (∫ x in (0 : ℝ)..t, κ x) = (∫ x in (0 : ℝ)..1, κ x) := by
      rw [add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t 1)
    linarith [h5]
  have ht0 : (0 : ℝ) ≤ α - (⌊α⌋ : ℝ) := by linarith [Int.floor_le α]
  have ht1 : α - (⌊α⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one α]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg ⌊α⌋
  · have hα : α = (α - (⌊α⌋ : ℝ)) + (k : ℝ) := by rw [hk]; push_cast; ring
    rw [hα, hgnat (α - (⌊α⌋ : ℝ)) k, hgt (α - (⌊α⌋ : ℝ))]
    have : (⌊α⌋ : ℝ) = (k : ℝ) := by rw [hk]; push_cast; ring
    rw [this]; ring
  · have hk' : (⌊α⌋ : ℝ) = -(k : ℝ) := by rw [hk]; push_cast; ring
    have hα : α + (k : ℝ) = α - (⌊α⌋ : ℝ) := by rw [hk']; ring
    have h := hgnat α k
    rw [hα, hgt (α - (⌊α⌋ : ℝ))] at h
    have hα' : α = (α - (⌊α⌋ : ℝ)) - (k : ℝ) := by rw [hk']; ring
    have key : (w : ℝ) * α = ((α - (⌊α⌋ : ℝ)) - (k : ℝ)) * (w : ℝ) := by
      conv_lhs => rw [hα']
      ring
    rw [key]
    linarith [h]


/-! ## The reduction: a transported `SO(2)` cocycle gives an analytic coboundary -/

/-- Given a real analytic `κ` with `rot (κ x) = K x` for an `SO(2)`-valued cocycle `K`
satisfying `K (x + α) = rot c * K x * rot (-φ x)`, the function `φ` is an analytic coboundary
for the rotation `x ↦ x + α`: there is a `1`-periodic analytic `ψ` with
`φ x - ∫₀¹ φ = ψ (x + α) - ψ x`. -/
theorem coboundary_of_so2_data (α c : ℝ) (φ : ℝ → ℝ) (hφc : Continuous φ)
    (K : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hKconj : ∀ x, K (x + α) = rot c * K x * rot (-(φ x)))
    (κ : ℝ → ℝ) (hκan : AnalyticOnNhd ℝ κ Set.univ)
    (hκper : ∀ x, ∃ m : ℤ, κ (x + 1) = κ x + (m : ℝ))
    (hrot : ∀ x, rot (κ x) = K x) :
    ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
      ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x := by
  have hκc : Continuous κ :=
    continuous_iff_continuousAt.mpr fun x => (hκan x trivial).continuousAt
  obtain ⟨w, hw⟩ := continuous_int_eq_const (fun x => κ (x + 1) - κ x)
      ((hκc.comp (continuous_id.add continuous_const)).sub hκc)
      (fun x => by obtain ⟨m, hm⟩ := hκper x; exact ⟨m, by linarith⟩)
  have hwx : ∀ x, κ (x + 1) = κ x + (w : ℝ) := fun x => by have := hw x; linarith
  have hj : ∀ x, ∃ m : ℤ, κ (x + α) - (c + κ x - φ x) = (m : ℝ) := by
    intro x
    have h1 : rot (κ (x + α)) = rot (c + κ x - φ x) := by
      rw [hrot, hKconj x, ← hrot x, cobRot_mul, cobRot_mul] <;> (congr 1 <;> ring)
    exact cob_rot_eq_sub_int h1
  have hjc : Continuous (fun x => κ (x + α) - (c + κ x - φ x)) :=
    (hκc.comp (continuous_id.add continuous_const)).sub ((continuous_const.add hκc).sub hφc)
  obtain ⟨j0, hj0⟩ := continuous_int_eq_const _ hjc hj
  have hφ : ∀ x, φ x = c + (j0 : ℝ) + κ x - κ (x + α) := fun x => by
    have := hj0 x; linarith
  have hintφ : (∫ x in (0 : ℝ)..1, φ x) = c + (j0 : ℝ) - (w : ℝ) * α := by
    have hcongr : (∫ x in (0 : ℝ)..1, φ x)
        = ∫ x in (0 : ℝ)..1, (c + (j0 : ℝ) + κ x - κ (x + α)) :=
      intervalIntegral.integral_congr fun x _ => hφ x
    have hsplit : (∫ x in (0 : ℝ)..1, (c + (j0 : ℝ) + κ x - κ (x + α)))
        = (c + (j0 : ℝ)) + (∫ x in (0 : ℝ)..1, κ x)
          - (∫ x in (0 : ℝ)..1, κ (x + α)) := by
      rw [intervalIntegral.integral_sub (f := fun x : ℝ => c + (j0 : ℝ) + κ x)
        (g := fun x : ℝ => κ (x + α))
        ((continuous_const.add hκc).intervalIntegrable 0 1)
        ((hκc.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1),
        intervalIntegral.integral_add (f := fun _ : ℝ => c + (j0 : ℝ)) (g := κ)
          (continuous_const.intervalIntegrable 0 1) (hκc.intervalIntegrable 0 1),
        intervalIntegral.integral_const]
      ring
    rw [hcongr, hsplit, cob_integral_shift κ hκc w hwx α]
    ring
  refine ⟨fun x => (w : ℝ) * x - κ x, ?_, ?_, ?_⟩
  · intro x
    show (w : ℝ) * (x + 1) - κ (x + 1) = (w : ℝ) * x - κ x
    rw [hwx x]
    ring
  · intro x _
    exact ((analyticAt_const (x := x) (v := (w : ℝ))).mul analyticAt_id).sub (hκan x trivial)
  · intro x
    rw [hintφ, hφ x]
    ring

/-! ## The main lemma (AJ Lemma 4.1, `(1) ⇒ (2)`) -/

/-- Proof route (AJ Lemma 4.1, (1) ⇒ (2)).  Write `H x = O x * (O x)ᵀ` (symmetric positive
definite, det 1) and `H x = (H x)^{1/2}` diagonalisation-free: for `2×2` symmetric positive
`H` with det 1, `H^{1/2} = (H + 1)/√(tr H + 2)` and `H^{-1} = (tr H) • 1 - H`.  Let
`K x := (H x)^{-1/2} * O x ∈ SO(2)`; choose a continuous `κ : ℝ → ℝ` with `rot (κ x) = K x`,
and set `w := κ (x+1) - κ x ∈ ℤ` (independent of `x`).  The relation gives
`rot (κ (x+α) + φ x - κ x) = (H (x+α))^{-1/2} * rot c * (H x)^{1/2} =: rot (ρ x)`, so
`j x := κ (x+α) + φ x - κ x - ρ x ∈ ℤ` is continuous, hence a constant `j₀`.  Transposing
`H (x+α) = rot c * H x * rot (-c)` (which follows from the relation) and comparing with the
conjugated form gives `H x * rot (c - ρ x) = rot (ρ x - c) * H x`; comparing the `(1,2)` and
`(2,1)` entries yields `sin (2π (ρ x - c)) * tr (H x) = 0`, so `ρ x - c ∈ (1/2)ℤ` is constant.
Averaging `j` over `[0,1]` (using `∫ (κ (x+α) - κ x) dx = w * α`) gives
`j₀ + (c + m/2) - ∫ φ = w * α`.  Hence `φ x - ∫φ = w * α + κ x - κ (x+α)`, and
`ψ x := w * x - κ x` is 1-periodic and satisfies the displayed equation.  `ψ` is analytic
because `H`, `K`, `κ` are (for the angle lift: `κ'` is the analytic function obtained from
`(d/dx K x) * (K x)^{-1} ∈ so(2)`, or locally invert `rot` which is a local analytic
diffeomorphism, and glue by uniqueness of analytic continuation). -/
theorem coboundary_of_conjugacy (α : ℝ) (hα : Irrational α)
    (φ : ℝ → ℝ) (hφc : Continuous φ) (hφp : ∀ x, φ (x + 1) = φ x)
    (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (hO : ∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ)
    (hper : ∀ x, O (x + 1) = O x) (hdet : ∀ x, (O x).det = 1)
    (hconj : ∀ x, O (x + α) * Work.TMContract.rot (φ x) = Work.TMContract.rot c * O x) :
    ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
      ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x := by
  obtain ⟨K, hKan, hKper, hKorth, hKdet, hKconj⟩ :=
    cob_polar_factor α c φ O hO hper hdet hconj
  let u : ℝ → ℝ := fun x => K x 0 0
  let v : ℝ → ℝ := fun x => K x 1 0
  have hu : AnalyticOnNhd ℝ u Set.univ := hKan 0 0
  have hv : AnalyticOnNhd ℝ v Set.univ := hKan 1 0
  have huv : ∀ x, u x ^ 2 + v x ^ 2 = 1 := by
    intro x
    have h := hKorth x
    rw [cob_so2_form (K x) (hKorth x) (hKdet x), cob_so2_sq] at h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    simpa [u, v, Matrix.one_apply] using h00
  obtain ⟨κ, hκan, hκexp⟩ := cob_so2_angle_lift u v hu hv huv
  have hrot : ∀ x, rot (κ x) = K x := by
    intro x
    rw [cob_rot_of_exp (hκexp x), cob_so2_form (K x) (hKorth x) (hKdet x)]
  have hκper : ∀ x, ∃ m : ℤ, κ (x + 1) = κ x + (m : ℝ) := by
    intro x
    have h : rot (κ (x + 1)) = rot (κ x) := by rw [hrot, hKper x, ← hrot]
    obtain ⟨m, hm⟩ := cob_rot_eq_sub_int h
    exact ⟨m, by linarith⟩
  exact coboundary_of_so2_data α c φ hφc K hKconj κ hκan hκper hrot

end Work.TMComp.RedProj
