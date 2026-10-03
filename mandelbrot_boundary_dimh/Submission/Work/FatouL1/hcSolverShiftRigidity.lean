import Mathlib
import Submission.Work.FatouL1.hcSolverBound
import Submission.Work.FatouL1.hcSolverDifference
import Submission.Work.FatouL1.periodic_bounded_const

/-!
# FATOU-L1: shift rigidity of the Cauchy–Heine solver

If `T` is holomorphic on the strip `(a,b) × ℝ` with `b - a > 2`, is bounded there, and satisfies
the linear difference equation `T (z+1) - T z = h z` with a *bounded* (hence `L¹`-mass bounded) `h`,
then `T` is the solver itself up to an additive constant:

  `T z = c - hcSolver h z`   on `(a + 1/2, b - 1) × ℝ`.

Indeed `S := T + hcSolver h` is holomorphic on the strip `(a+1/2, b)` (of width `> 1`), is bounded
there (`‖hcSolver h‖ ≤ m/2` by `hcSolverBound`), and is `1`-periodic because the shift of
`hcSolver h` cancels `h` (`hcSolverDifference`).  A bounded holomorphic `1`-periodic function on a
strip of width `> 1` is constant (`periodic_bounded_const`).
-/

namespace Work.FatouL1

noncomputable section

open MeasureTheory

/-- The `L¹` mass of `h` on the vertical line through `Re z - 1/2`, as a `lintegral` over
`y ↦ ‖h (z - 1/2 + y I)‖`, is bounded by `m` — obtained from the mass bound on the line
`x = Re z - 1/2` by translating the parameter. -/
private lemma line_mass_shift {a b m : ℝ} {h : ℂ → ℂ}
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {z : ℂ} (hz : z.re - 1 / 2 ∈ Set.Ioo a b) :
    ∫⁻ y : ℝ, ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖ ≤ ENNReal.ofReal m := by
  have harg : ∀ y : ℝ, z - 1 / 2 + (y : ℂ) * Complex.I =
      (((z.re - 1 / 2 : ℝ)) : ℂ) + ((y + z.im : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [Complex.ofReal_add]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hfun : (fun y : ℝ => ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖) =
      fun y : ℝ => ENNReal.ofReal
        ‖h (((z.re - 1 / 2 : ℝ) : ℂ) + ((y + z.im : ℝ) : ℂ) * Complex.I)‖ := by
    funext y; rw [harg y]
  rw [hfun, MeasureTheory.lintegral_add_right_eq_self
    (fun y : ℝ => ENNReal.ofReal ‖h (((z.re - 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖) z.im]
  exact hmass (z.re - 1 / 2) hz

theorem hcSolverShiftRigidity {a b m B : ℝ} (hab : a < b) (hab' : 2 < b - a) {T h : ℂ → ℂ}
    (hT : DifferentiableOn ℂ T {z : ℂ | a < z.re ∧ z.re < b})
    (hh : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    (heq : ∀ z : ℂ, a < z.re → z.re < b → T (z + 1) - T z = h z)
    (hbdd : ∀ z : ℂ, a < z.re → z.re < b → ‖T z‖ ≤ B) :
    ∃ c : ℂ, ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b - 1 → T z = c - Work.FatouL1.hcSolver h z := by
  obtain ⟨hhc_hol, hhc_mass⟩ := hcSolverBound (a := a) (b := b) (m := m) hab hh hint hmass
  have hdiff := hcSolverDifference (a := a) (b := b) (m := m) hab hh hint hmass
  -- the function whose rigidity we prove
  let S : ℂ → ℂ := fun z => T z + Work.FatouL1.hcSolver h z
  have hSval : ∀ w : ℂ, S w = T w + Work.FatouL1.hcSolver h w := fun _ => rfl
  -- openness of the three strips
  have hAopen : IsOpen {z : ℂ | a < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hBopen : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hDopen : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  -- holomorphy of `S` on the strip `(a + 1/2, b)`
  have hS_hol : DifferentiableOn ℂ S {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} := by
    intro z hz
    have hzA : z ∈ {w : ℂ | a < w.re ∧ w.re < b} := ⟨by linarith [hz.1], hz.2⟩
    have hzB : z ∈ {w : ℂ | a + 1 / 2 < w.re ∧ w.re < b + 1 / 2} := ⟨hz.1, by linarith [hz.2]⟩
    have h1 : DifferentiableAt ℂ T z := hT.differentiableAt (hAopen.mem_nhds hzA)
    have h2 : DifferentiableAt ℂ (Work.FatouL1.hcSolver h) z :=
      hhc_hol.differentiableAt (hBopen.mem_nhds hzB)
    exact (h1.add h2).differentiableWithinAt
  -- boundedness of `S` on the strip `(a + 1/2, b)`
  have hS_bdd : ∃ M : ℝ, ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b → ‖S z‖ ≤ M := by
    refine ⟨B + (1 / 2) * (ENNReal.ofReal m).toReal, fun z hz1 hz2 => ?_⟩
    have hzσ : z.re - 1 / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have hline := line_mass_shift hmass hzσ
    have hm : ‖Work.FatouL1.hcSolver h z‖ ≤ (1 / 2) * (ENNReal.ofReal m).toReal := by
      have hbase := hhc_mass z hz1 (by linarith)
      refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hline
    have hTz : ‖T z‖ ≤ B := hbdd z (by linarith) hz2
    calc ‖S z‖ = ‖T z + Work.FatouL1.hcSolver h z‖ := by rw [hSval z]
      _ ≤ ‖T z‖ + ‖Work.FatouL1.hcSolver h z‖ := norm_add_le _ _
      _ ≤ B + (1 / 2) * (ENNReal.ofReal m).toReal := add_le_add hTz hm
  -- `S` is `1`-periodic inside the strip `(a + 1/2, b)`
  have hper : ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b → a + 1 / 2 < (z + 1).re → (z + 1).re < b →
      S (z + 1) = S z := by
    intro z h1 _ h3 h4
    have hre : (z + 1).re = z.re + 1 := by simp
    have hz2 : z.re < b - 1 / 2 := by rw [hre] at h4; linarith
    have he' : T (z + 1) = T z + h z := by
      have h := heq z (by linarith) (by rw [hre] at h4; linarith)
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      exact add_comm _ _
    have hd' : Work.FatouL1.hcSolver h (z + 1) = Work.FatouL1.hcSolver h z - h z := by
      have h := hdiff z h1 hz2
      rw [sub_eq_iff_eq_add'] at h
      rw [h]
      ring
    rw [hSval (z + 1), hSval z, he', hd']
    ring
  -- a bounded holomorphic `1`-periodic function on a strip of width `> 1` is constant
  obtain ⟨c, hc⟩ := periodic_bounded_const (a := a + 1 / 2) (b := b) (T := S)
    (by linarith) hS_hol hper hS_bdd
  refine ⟨c, fun z hz1 hz2 => ?_⟩
  have hzS := hc z (by linarith) (by linarith)
  have hz : T z + Work.FatouL1.hcSolver h z = c := by rw [← hSval z]; exact hzS
  rw [eq_sub_iff_add_eq]
  exact hz

end

end Work.FatouL1
