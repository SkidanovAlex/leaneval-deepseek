import Submission.Work.TMComp.RotBasics.RotLift
import Submission.Work.TMComp.RotBasics.UpperLiftProps
import Submission.Work.TMComp.RotBasics.lift_diff_const
import Submission.Work.TMC13.Basic

/-!
# The general lift calculus: part 4 of `P_RotBasics`

Given a continuous, `1`-periodic, `SL(2,ℝ)`-valued `B` of degree `k`, a continuous `1`-periodic
`φ`, and a conjugacy `B (x + α) S_E(x) = rot (φ x) B x`, we show

`rotLift α lam E = 2 ∫₀¹ φ - 2 k α + 2 j`  for some `j : ℤ`.

The proof follows the lift calculus of the paper: the explicit lift `conjLift B η y` of `B y`
(where `η` is the first-column angle of `B`) conjugates the Prüfer step to a translation up to
an even integer constant `2 j`, and averaging the resulting identity over the phase produces
the limit.  Since `conjLift` drifts by `2 η`, and `∫ x, η (x + n α) = k n α + O(1)`, the
degree `k` produces the term `- 2 k α`.
-/

namespace Work.TMComp.RotBasics

open Work.TMContract
open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

/-! ## Algebraic facts about the first column of a matrix -/

/-- `colNorm M > 0` whenever the first column of `M` is nonzero. -/
theorem colNorm_pos {M : Matrix (Fin 2) (Fin 2) ℝ} (h : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0) :
    0 < colNorm M := by
  rw [colNorm]
  refine Real.sqrt_pos.mpr ?_
  rcases h with h | h
  · exact lt_of_lt_of_le (sq_pos_of_ne_zero h) (le_add_of_nonneg_right (sq_nonneg _))
  · exact lt_of_lt_of_le (sq_pos_of_ne_zero h) (le_add_of_nonneg_left (sq_nonneg _))

/-- The norm of the first column of a matrix whose first column is `r (cos, sin)`. -/
theorem colNorm_eq_of_col {M : Matrix (Fin 2) (Fin 2) ℝ} {η r : ℝ} (hr : 0 < r)
    (h00 : M 0 0 = r * Real.cos (2 * Real.pi * η))
    (h10 : M 1 0 = r * Real.sin (2 * Real.pi * η)) : colNorm M = r := by
  rw [colNorm, h00, h10]
  rw [show (r * Real.cos (2 * Real.pi * η)) ^ 2 + (r * Real.sin (2 * Real.pi * η)) ^ 2 = r ^ 2 by
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * η)]]
  exact Real.sqrt_sq (le_of_lt hr)

/-- The `(0,1)`-coefficient `colQ` in the upper-triangular normal form. -/
theorem colQ_eq_of_col {M : Matrix (Fin 2) (Fin 2) ℝ} {η r : ℝ} (hr : 0 < r)
    (hnorm : colNorm M = r)
    (h00 : M 0 0 = r * Real.cos (2 * Real.pi * η))
    (h10 : M 1 0 = r * Real.sin (2 * Real.pi * η)) :
    colQ M = Real.cos (2 * Real.pi * η) * M 0 1 + Real.sin (2 * Real.pi * η) * M 1 1 := by
  rw [colQ, h00, h10, hnorm, div_eq_iff (ne_of_gt hr)]
  ring

/-- **Upper triangular normal form.**  A determinant-one matrix whose first column is
`(r cos 2πη, r sin 2πη)`, `r > 0`, equals `rot η` times the upper triangular matrix with
diagonal `(colNorm M, (colNorm M)⁻¹)` and `(0,1)`-entry `colQ M`. -/
theorem matrix_eq_rot_upper {M : Matrix (Fin 2) (Fin 2) ℝ} {η : ℝ} (hdet : M.det = 1)
    (hcol : ∃ r : ℝ, 0 < r ∧ M 0 0 = r * Real.cos (2 * Real.pi * η) ∧
      M 1 0 = r * Real.sin (2 * Real.pi * η)) :
    M = rot η * !![colNorm M, colQ M; 0, 1 / colNorm M] := by
  obtain ⟨r, hr, h00, h10⟩ := hcol
  have hnorm : colNorm M = r := colNorm_eq_of_col hr h00 h10
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := hdet; rwa [Matrix.det_fin_two] at h
  have hσ : colQ M = Real.cos (2 * Real.pi * η) * M 0 1
      + Real.sin (2 * Real.pi * η) * M 1 1 := colQ_eq_of_col hr hnorm h00 h10
  have hX : Real.cos (2 * Real.pi * η) * M 1 1 - Real.sin (2 * Real.pi * η) * M 0 1
      = (r)⁻¹ := by
    have h : r * (Real.cos (2 * Real.pi * η) * M 1 1
        - Real.sin (2 * Real.pi * η) * M 0 1) = 1 := by
      have h' := hdet'; rw [h00, h10] at h'; nlinarith [h']
    calc Real.cos (2 * Real.pi * η) * M 1 1 - Real.sin (2 * Real.pi * η) * M 0 1
        = r⁻¹ * (r * (Real.cos (2 * Real.pi * η) * M 1 1
            - Real.sin (2 * Real.pi * η) * M 0 1)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]
      _ = r⁻¹ := by rw [h, mul_one]
  have hP : Real.cos (2 * Real.pi * η) ^ 2 + Real.sin (2 * Real.pi * η) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  rw [hσ, hnorm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two, h00, h10]
  · ring
  · rw [hX.symm]
    rw [show Real.cos (2 * Real.pi * η) * (Real.cos (2 * Real.pi * η) * M 0 1
          + Real.sin (2 * Real.pi * η) * M 1 1)
          + -(Real.sin (2 * Real.pi * η) * (Real.cos (2 * Real.pi * η) * M 1 1
            - Real.sin (2 * Real.pi * η) * M 0 1))
          = (Real.cos (2 * Real.pi * η) ^ 2 + Real.sin (2 * Real.pi * η) ^ 2) * M 0 1 by ring]
    rw [hP, one_mul]
  · ring
  · rw [hX.symm]
    rw [show Real.sin (2 * Real.pi * η) * (Real.cos (2 * Real.pi * η) * M 0 1
          + Real.sin (2 * Real.pi * η) * M 1 1)
          + Real.cos (2 * Real.pi * η) * (Real.cos (2 * Real.pi * η) * M 1 1
            - Real.sin (2 * Real.pi * η) * M 0 1)
          = (Real.cos (2 * Real.pi * η) ^ 2 + Real.sin (2 * Real.pi * η) ^ 2) * M 1 1 by ring]
    rw [hP, one_mul]

/-! ## The explicit lift of a continuous `SL(2,ℝ)`-family -/

/-- Continuity of `upperLift` on the region `r > 0` (where it is defined by the principal
argument formula). -/
theorem upperLift_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => upperLift p.1 p.2.1 p.2.2) {p | 0 < p.1} :=
  fun p hp => (upperLift_continuousAt (r₀ := p.1) (q₀ := p.2.1) (t₀ := p.2.2) hp).continuousWithinAt

/-- `conjLift B η y` is a positive lift of `B y`. -/
theorem conjLift_isPosLift (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (η : ℝ → ℝ)
    (hdet : ∀ x, (B x).det = 1)
    (hcol : ∀ x, ∃ r : ℝ, 0 < r ∧ B x 0 0 = r * Real.cos (2 * Real.pi * η x) ∧
      B x 1 0 = r * Real.sin (2 * Real.pi * η x)) (y : ℝ) :
    IsPosLift (B y) (conjLift B η y) := by
  obtain ⟨r, hr, h00, h10⟩ := hcol y
  have hnorm : colNorm (B y) = r := colNorm_eq_of_col hr h00 h10
  have hrpos : 0 < colNorm (B y) := by rw [hnorm]; exact hr
  have hmat : B y = rot (η y) * !![colNorm (B y), colQ (B y); 0, 1 / colNorm (B y)] :=
    matrix_eq_rot_upper (hdet y) ⟨r, hr, h00, h10⟩
  rw [hmat]
  have hcomp := IsPosLift.comp (rot (η y)) !![colNorm (B y), colQ (B y); 0, 1 / colNorm (B y)]
    (fun t => t + 2 * η y) (upperLift (colNorm (B y)) (colQ (B y)))
    (IsPosLift.rot_lift (η y)) (upperLift_isPosLift hrpos)
  convert hcomp using 1
  ext t
  simp only [Function.comp_apply, conjLift]
  ring

/-- Joint continuity of `(y, t) ↦ conjLift B η y t`. -/
theorem conjLift_continuous (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (η : ℝ → ℝ)
    (hB : Continuous B) (hη : Continuous η) (hpos : ∀ y, 0 < colNorm (B y)) :
    Continuous (fun p : ℝ × ℝ => conjLift B η p.1 p.2) := by
  have hentry : ∀ i j : Fin 2, Continuous (fun y : ℝ => B y i j) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hB)
  have hcolNorm : Continuous (fun y : ℝ => colNorm (B y)) := by
    unfold colNorm
    exact Real.continuous_sqrt.comp (((hentry 0 0).pow 2).add ((hentry 1 0).pow 2))
  have hcolQ : Continuous (fun y : ℝ => colQ (B y)) := by
    unfold colQ
    exact Continuous.div (((hentry 0 0).mul (hentry 0 1)).add ((hentry 1 0).mul (hentry 1 1)))
      hcolNorm (fun y => ne_of_gt (hpos y))
  have hmap : Continuous (fun p : ℝ × ℝ =>
      ((colNorm (B p.1), colQ (B p.1), p.2) : ℝ × ℝ × ℝ)) :=
    (hcolNorm.comp continuous_fst).prodMk ((hcolQ.comp continuous_fst).prodMk continuous_snd)
  have hmem : ∀ p : ℝ × ℝ, (colNorm (B p.1), colQ (B p.1), p.2) ∈ {q : ℝ × ℝ × ℝ | 0 < q.1} :=
    fun p => hpos p.1
  have hcomp := upperLift_continuousOn.comp_continuous hmap hmem
  have h2 : Continuous (fun _ : ℝ × ℝ => (2 : ℝ)) := continuous_const
  change Continuous (fun p : ℝ × ℝ =>
    2 * η p.1 + upperLift (colNorm (B p.1)) (colQ (B p.1)) p.2)
  exact (h2.mul (hη.comp continuous_fst)).add hcomp



/-! ## The drift of the first-column angle -/

/-- `∫₀¹ η (x + c) dx` differs from `k c` by a bounded amount when `η (x+1) = η x + k`. -/
theorem eta_integral_shift (η : ℝ → ℝ) (k : ℤ) (hcont : Continuous η)
    (hshift : ∀ x, η (x + 1) = η x + (k : ℝ)) :
    ∃ C : ℝ, ∀ c : ℝ, |(∫ x in (0 : ℝ)..1, η (x + c)) - (k : ℝ) * c| ≤ C := by
  have hFcont : Continuous (fun c : ℝ => ∫ x in (0 : ℝ)..1, η (x + c)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
    exact hcont.comp (continuous_snd.add continuous_fst)
  have hFper : ∀ c : ℝ, (∫ x in (0 : ℝ)..1, η (x + (c + 1)))
      = (∫ x in (0 : ℝ)..1, η (x + c)) + (k : ℝ) := by
    intro c
    have hshift' : ∀ x : ℝ, η (x + (c + 1)) = η (x + c) + (k : ℝ) := by
      intro x; rw [show x + (c + 1) = (x + c) + 1 by ring, hshift]
    have hI : IntervalIntegrable (fun x : ℝ => η (x + c)) volume (0 : ℝ) 1 :=
      ((hcont.comp (continuous_id.add continuous_const))).intervalIntegrable 0 1
    calc (∫ x in (0 : ℝ)..1, η (x + (c + 1)))
        = ∫ x in (0 : ℝ)..1, (η (x + c) + (k : ℝ)) := by
          congr 1 with x; exact hshift' x
      _ = (∫ x in (0 : ℝ)..1, η (x + c)) + (k : ℝ) := by
          rw [intervalIntegral.integral_add hI intervalIntegrable_const,
            intervalIntegral.integral_const]
          simp
  have hper : Function.Periodic (fun c : ℝ => (∫ x in (0 : ℝ)..1, η (x + c)) - (k : ℝ) * c) 1 := by
    intro c
    change (∫ x in (0 : ℝ)..1, η (x + (c + 1))) - (k : ℝ) * (c + 1)
      = (∫ x in (0 : ℝ)..1, η (x + c)) - (k : ℝ) * c
    rw [hFper c]
    ring
  have hcontg : Continuous (fun c : ℝ => (∫ x in (0 : ℝ)..1, η (x + c)) - (k : ℝ) * c) :=
    hFcont.sub ((continuous_const : Continuous (fun _ : ℝ => (k : ℝ))).mul continuous_id)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun c : ℝ => (∫ x in (0 : ℝ)..1, η (x + c)) - (k : ℝ) * c) hcontg.continuousOn
  refine ⟨C, fun c => ?_⟩
  have hz : (∫ x in (0 : ℝ)..1, η (x + c)) - (k : ℝ) * c
      = (∫ x in (0 : ℝ)..1, η (x + (c - (⌊c⌋ : ℝ)))) - (k : ℝ) * (c - (⌊c⌋ : ℝ)) := by
    have h := (hper.zsmul (⌊c⌋ : ℤ)) (c - (⌊c⌋ : ℝ))
    simpa using h
  have hr : c - (⌊c⌋ : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by have := Int.floor_le c; linarith,
     by have := Int.lt_floor_add_one c; linarith⟩
  have hbound := hC _ hr
  rw [Real.norm_eq_abs] at hbound
  rwa [hz]

/-! ## The model estimate -/

/-- **Model estimate.**  Suppose a continuous `h` models the Prüfer iteration as
`h (y+α) (F_y t) = h y t + 2 c y + 2 j`, and `h` differs from `2 η + id` by at most `M`.
Then the phase-averaged Prüfer angle converges to `2 ∫₀¹ c - 2 k α + 2 j`. -/
theorem tendsto_avg_of_model (α lam E : ℝ) (c η : ℝ → ℝ) (k : ℤ) (h : ℝ → ℝ → ℝ) (j : ℤ)
    (M : ℝ)
    (hccont : Continuous c) (hcper : ∀ y : ℝ, c (y + 1) = c y)
    (hηcont : Continuous η) (hηshift : ∀ y : ℝ, η (y + 1) = η y + (k : ℝ))
    (hcont : Continuous (Function.uncurry h))
    (hmod : ∀ y t : ℝ,
      h (y + α) (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t)
        = h y t + 2 * c y + 2 * (j : ℝ))
    (hη : ∀ y t : ℝ, |h y t - t - 2 * η y| ≤ M) :
    Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))
      atTop (nhds (2 * (∫ x in (0 : ℝ)..1, c x) - 2 * (k : ℝ) * α + 2 * (j : ℝ))) := by
  obtain ⟨Cη, hCη⟩ := eta_integral_shift η k hηcont hηshift
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hη 0 0)
  set P : ℝ := ∫ x in (0 : ℝ)..1, c x with hP
  set Q : ℝ := ∫ x in (0 : ℝ)..1, h x 0 with hQ
  set L : ℝ := 2 * P - 2 * (k : ℝ) * α + 2 * (j : ℝ) with hL
  have hmain : ∀ n : ℕ, ∀ x : ℝ, h (x + (n : ℝ) * α) (pruferIter α lam E n x 0)
      = h x 0 + 2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) + 2 * (n : ℝ) * (j : ℝ) := by
    intro n
    induction n with
    | zero => intro x; simp [pruferIter_zero]
    | succ m ih =>
      intro x
      have hstep : pruferIter α lam E (m + 1) x 0
          = pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (x + (m : ℝ) * α)))
              (pruferIter α lam E m x 0) := rfl
      have hcoord : (x + (m : ℝ) * α) + α = x + ((m + 1 : ℕ) : ℝ) * α := by push_cast; ring
      have hmod' := hmod (x + (m : ℝ) * α) (pruferIter α lam E m x 0)
      calc h (x + ((m + 1 : ℕ) : ℝ) * α) (pruferIter α lam E (m + 1) x 0)
          = h ((x + (m : ℝ) * α) + α) (pruferStep
              (E - 2 * lam * Real.cos (2 * Real.pi * (x + (m : ℝ) * α)))
              (pruferIter α lam E m x 0)) := by rw [hstep, hcoord]
        _ = h (x + (m : ℝ) * α) (pruferIter α lam E m x 0) + 2 * c (x + (m : ℝ) * α)
              + 2 * (j : ℝ) := hmod'
        _ = h x 0 + 2 * (∑ i ∈ Finset.range (m + 1), c (x + (i : ℝ) * α))
              + 2 * ((m + 1 : ℕ) : ℝ) * (j : ℝ) := by
              rw [ih x, Finset.sum_range_succ]; push_cast; ring
  have hbd : ∀ n : ℕ, ∀ x : ℝ, |pruferIter α lam E n x 0 + 2 * η (x + (n : ℝ) * α)
      - (h x 0 + 2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) + 2 * (n : ℝ) * (j : ℝ))| ≤ M := by
    intro n x
    rw [← hmain n x]
    have hh := hη (x + (n : ℝ) * α) (pruferIter α lam E n x 0)
    rw [show pruferIter α lam E n x 0 + 2 * η (x + (n : ℝ) * α)
          - h (x + (n : ℝ) * α) (pruferIter α lam E n x 0)
        = -(h (x + (n : ℝ) * α) (pruferIter α lam E n x 0) - pruferIter α lam E n x 0
            - 2 * η (x + (n : ℝ) * α)) by ring, abs_neg]
    exact hh
  have hterm : ∀ i : ℕ, (∫ x in (0 : ℝ)..1, c (x + (i : ℝ) * α)) = P := by
    intro i
    rw [intervalIntegral.integral_comp_add_right]
    rw [show (0 : ℝ) + (i : ℝ) * α = (i : ℝ) * α by ring,
      show (1 : ℝ) + (i : ℝ) * α = (i : ℝ) * α + 1 by ring, hP]
    simpa using Function.Periodic.intervalIntegral_add_eq hcper ((i : ℝ) * α) 0
  have hsum : ∀ n : ℕ, (∫ x in (0 : ℝ)..1, (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)))
      = (n : ℝ) * P := by
    intro n
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    · intro i _
      exact ((hccont.comp (continuous_id.add continuous_const))).intervalIntegrable _ _
  have hu : ∀ n : ℕ, Continuous (fun x : ℝ => pruferIter α lam E n x 0) := fun n =>
    (pruferIter_continuous_xt α lam E n).comp (continuous_id.prodMk continuous_const)
  have hv : ∀ n : ℕ, Continuous (fun x : ℝ => 2 * η (x + (n : ℝ) * α)) := fun n =>
    (continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul
      (hηcont.comp (continuous_id.add continuous_const))
  have hσ : ∀ n : ℕ, Continuous (fun x : ℝ =>
      ∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) := fun n =>
    continuous_finsetSum _ (fun i _ => hccont.comp (continuous_id.add continuous_const))
  have hw : ∀ n : ℕ, Continuous (fun x : ℝ =>
      h x 0 + 2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) + 2 * (n : ℝ) * (j : ℝ)) :=
    fun n => ((hcont.comp (continuous_id.prodMk continuous_const)).add
      ((continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul (hσ n))).add continuous_const
  have hQint : IntervalIntegrable (fun x : ℝ => h x 0) volume (0 : ℝ) 1 :=
    (hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hZ : ∀ n : ℕ, |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0)
      + 2 * (∫ x in (0 : ℝ)..1, η (x + (n : ℝ) * α)) - Q - 2 * (n : ℝ) * P
      - 2 * (n : ℝ) * (j : ℝ)| ≤ M := by
    intro n
    have hIu : IntervalIntegrable (fun x : ℝ => pruferIter α lam E n x 0) volume (0 : ℝ) 1 :=
      (hu n).intervalIntegrable _ _
    have hIv : IntervalIntegrable (fun x : ℝ => 2 * η (x + (n : ℝ) * α)) volume (0 : ℝ) 1 :=
      (hv n).intervalIntegrable _ _
    have hIw : IntervalIntegrable (fun x : ℝ =>
        h x 0 + 2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) + 2 * (n : ℝ) * (j : ℝ))
        volume (0 : ℝ) 1 := (hw n).intervalIntegrable _ _
    have hI2σ : IntervalIntegrable (fun x : ℝ =>
        2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α))) volume (0 : ℝ) 1 :=
      ((continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul (hσ n)).intervalIntegrable _ _
    have hint : (∫ x in (0 : ℝ)..1, (pruferIter α lam E n x 0 + 2 * η (x + (n : ℝ) * α)
        - (h x 0 + 2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) + 2 * (n : ℝ) * (j : ℝ))))
        = (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0)
          + 2 * (∫ x in (0 : ℝ)..1, η (x + (n : ℝ) * α)) - Q - 2 * (n : ℝ) * P
          - 2 * (n : ℝ) * (j : ℝ) := by
      rw [intervalIntegral.integral_sub (hIu.add hIv) hIw,
        intervalIntegral.integral_add hIu hIv,
        intervalIntegral.integral_add (hQint.add hI2σ) intervalIntegrable_const,
        intervalIntegral.integral_add hQint hI2σ,
        intervalIntegral.integral_const_mul (2 : ℝ) (fun x : ℝ => η (x + (n : ℝ) * α)),
        intervalIntegral.integral_const_mul (2 : ℝ)
          (fun x : ℝ => ∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)),
        hsum n, intervalIntegral.integral_const, ← hQ]
      ring
    have hbn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := M)
      (f := fun x : ℝ => pruferIter α lam E n x 0 + 2 * η (x + (n : ℝ) * α)
        - (h x 0 + 2 * (∑ i ∈ Finset.range n, c (x + (i : ℝ) * α)) + 2 * (n : ℝ) * (j : ℝ)))
      (fun x _ => by rw [Real.norm_eq_abs]; exact hbd n x)
    rw [hint, Real.norm_eq_abs] at hbn
    simpa using hbn
  have hkey : ∀ n : ℕ, 1 ≤ n →
      |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - L|
        ≤ (M + 2 * Cη + |Q|) / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set X : ℝ := ((∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0)
        + 2 * (∫ x in (0 : ℝ)..1, η (x + (n : ℝ) * α)) - Q - 2 * (n : ℝ) * P
        - 2 * (n : ℝ) * (j : ℝ)) / (n : ℝ) with hX
    set Y : ℝ := 2 * ((∫ x in (0 : ℝ)..1, η (x + (n : ℝ) * α))
        - (k : ℝ) * ((n : ℝ) * α)) / (n : ℝ) with hYdef
    have hident : (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - L
        = X - Y + Q / (n : ℝ) := by
      rw [hX, hYdef, hL, hP, hQ]
      field_simp
      ring
    have h1 : |X| ≤ M / (n : ℝ) := by
      rw [hX, abs_div, abs_of_pos hnpos]
      exact div_le_div_of_nonneg_right (hZ n) (le_of_lt hnpos)
    have h2 : |Y| ≤ 2 * Cη / (n : ℝ) := by
      rw [hYdef, abs_div, abs_of_pos hnpos, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_div_iff_of_pos_right hnpos]
      linarith [hCη ((n : ℝ) * α)]
    have h3 : |Q / (n : ℝ)| ≤ |Q| / (n : ℝ) := by rw [abs_div, abs_of_pos hnpos]
    have hab : |X - Y + Q / (n : ℝ)| ≤ |X - Y| + |Q / (n : ℝ)| := abs_add_le _ _
    have hab2 : |X - Y| ≤ |X| + |Y| := by simpa using abs_sub_le X 0 Y
    calc |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - L|
        = |X - Y + Q / (n : ℝ)| := by rw [hident]
      _ ≤ M / (n : ℝ) + 2 * Cη / (n : ℝ) + |Q| / (n : ℝ) := by
          linarith [hab, hab2, h1, h2, h3]
      _ = (M + 2 * Cη + |Q|) / (n : ℝ) := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun n : ℕ => (M + 2 * Cη + |Q|) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards with n
    rw [Real.norm_eq_abs]; exact abs_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hkey n hn

/-! ## Part 4: the conjugacy formula -/

set_option maxHeartbeats 2000000 in
/-- **Part 4 of `P_RotBasics`.**  If `B` is a continuous `1`-periodic `SL(2,ℝ)`-valued
conjugacy of degree `k` taking the transfer cocycle to the rotation by `φ`, then
`rotLift α lam E = 2 ∫₀¹ φ - 2 k α + 2 j` for an integer `j`. -/
theorem rotLift_conjugacy (α lam E : ℝ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ) (k : ℤ)
    (hdeg : HasDegree B k) (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hφcont : Continuous φ) (hφper : ∀ x, φ (x + 1) = φ x)
    (hconj : ∀ x, B (x + α) * tmR lam E x = rot (φ x) * B x) :
    ∃ j : ℤ, rotLift α lam E = 2 * (∫ x in (0 : ℝ)..1, φ x) - 2 * (k : ℝ) * α
      + 2 * (j : ℝ) := by
  obtain ⟨hBcont, η, hηcont, hηshift, hηcol⟩ := hdeg
  have hpos : ∀ y : ℝ, 0 < colNorm (B y) := by
    intro y
    obtain ⟨r, hr, h00, h10⟩ := hηcol y
    rw [colNorm_eq_of_col hr h00 h10]
    exact hr
  have hlift : ∀ y : ℝ, IsPosLift (B y) (conjLift B η y) :=
    conjLift_isPosLift B η hdet hηcol
  have hGcont : Continuous (fun p : ℝ × ℝ => conjLift B η p.1 p.2) :=
    conjLift_continuous B η hBcont hηcont hpos
  have hstep : ∀ y : ℝ, ∃ m : ℤ, ∀ t : ℝ,
      conjLift B η (y + α) (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t)
        = conjLift B η y t + 2 * φ y + 2 * (m : ℝ) := by
    intro y
    have hF : Continuous (fun t : ℝ =>
        pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t) :=
      pruferStep_continuous.comp (continuous_const.prodMk continuous_id)
    have hiter : IsPosLift (tmR lam E y) (fun t : ℝ =>
        pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t) := by
      rw [tmR_eq_comp]
      exact pruferStep_isPosLift _
    have h1 : IsPosLift (B (y + α) * tmR lam E y)
        (fun t : ℝ => conjLift B η (y + α)
          (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t)) :=
      IsPosLift.comp (B (y + α)) (tmR lam E y) (conjLift B η (y + α))
        (fun t : ℝ => pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t)
        (hlift (y + α)) hiter
    have h2 : IsPosLift (B (y + α) * tmR lam E y) (fun t : ℝ => conjLift B η y t + 2 * φ y) := by
      rw [hconj y]
      exact IsPosLift.comp (rot (φ y)) (B y) (fun t : ℝ => t + 2 * φ y) (conjLift B η y)
        (IsPosLift.rot_lift (φ y)) (hlift y)
    have hAdet : (B (y + α) * tmR lam E y).det ≠ 0 := by
      rw [Matrix.det_mul, hdet (y + α)]
      have htm : (tmR lam E y).det = 1 := by simp [tmR, Matrix.det_fin_two]
      rw [htm]; norm_num
    have hc1 : Continuous (fun t : ℝ => conjLift B η (y + α)
        (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t)) :=
      hGcont.comp (continuous_const.prodMk hF)
    have hc2 : Continuous (fun t : ℝ => conjLift B η y t + 2 * φ y) :=
      (hGcont.comp (continuous_const.prodMk continuous_id)).add continuous_const
    exact lift_diff_const _ _ _ hAdet h2 h1 hc2 hc1
  choose m hm using hstep
  have hcontm : Continuous (fun y : ℝ => (m y : ℝ)) := by
    have heq : (fun y : ℝ => (m y : ℝ)) = fun y : ℝ =>
        (conjLift B η (y + α) (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) 0)
          - conjLift B η y 0 - 2 * φ y) / 2 := by
      funext y
      have h := hm y 0
      rw [h]; ring
    rw [heq]
    have hF : Continuous (fun y : ℝ =>
        pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) 0) := by
      have harg : Continuous (fun y : ℝ => E - 2 * lam * Real.cos (2 * Real.pi * y)) := by
        fun_prop
      exact pruferStep_continuous.comp (harg.prodMk continuous_const)
    have hA : Continuous (fun y : ℝ => conjLift B η (y + α)
        (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) 0)) :=
      hGcont.comp ((continuous_id.add continuous_const).prodMk hF)
    have hB : Continuous (fun y : ℝ => conjLift B η y 0) :=
      hGcont.comp (continuous_id.prodMk continuous_const)
    exact (((hA.sub hB).sub ((continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul
      hφcont))).div_const 2
  obtain ⟨mi, hmi⟩ := Work.TMC13.exists_int_eq_const hcontm (fun y => ⟨m y, rfl⟩)
  have hmconst : ∀ y : ℝ, m y = mi := fun y => Int.cast_injective (hmi y)
  have hmod : ∀ y t : ℝ, conjLift B η (y + α)
      (pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y)) t)
      = conjLift B η y t + 2 * φ y + 2 * (mi : ℝ) := by
    intro y t
    have h := hm y t
    rw [hmconst y] at h
    exact h
  have hj := tendsto_avg_of_model α lam E φ η k (fun y t : ℝ => conjLift B η y t) mi 2
    hφcont hφper hηcont hηshift hGcont hmod (fun y t => by
      have h1 := upperLift_bound (colNorm (B y)) (colQ (B y)) t
      have h2 : conjLift B η y t - t - 2 * η y
          = upperLift (colNorm (B y)) (colQ (B y)) t - t := by
        simp only [conjLift]; ring
      rw [h2]; exact h1)
  exact ⟨mi, tendsto_nhds_unique (rotLift_tendsto α lam E) hj⟩
end

end Work.TMComp.RotBasics
