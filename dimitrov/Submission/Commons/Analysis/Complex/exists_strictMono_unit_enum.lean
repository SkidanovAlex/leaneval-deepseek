import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Commons.Analysis.Complex

/-! Enumerating the points of a finite subset of the unit circle in increasing order of
argument.  The argument is produced from `Complex.arg` by reduction into `[0, 2π)`
(preserving `exp (· * I)`). -/

/-- Reduce a real angle into `[0, 2π)` without changing `exp (t * I)`. -/
noncomputable def angReduce (t : ℝ) : ℝ :=
  t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

theorem angReduce_mem (t : ℝ) : 0 ≤ angReduce t ∧ angReduce t < 2 * Real.pi := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hle : (⌊t / (2 * Real.pi)⌋ : ℝ) ≤ t / (2 * Real.pi) := Int.floor_le _
  have hlt : t / (2 * Real.pi) < (⌊t / (2 * Real.pi)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · have h1 : (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ t := by
      calc (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
          ≤ (t / (2 * Real.pi)) * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hpi)
        _ = t := by field_simp
    unfold angReduce
    linarith
  · have h1 : t < ((⌊t / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
      calc t = (t / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
        _ < ((⌊t / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) :=
            mul_lt_mul_of_pos_right hlt hpi
    unfold angReduce
    nlinarith [h1]

theorem exp_angReduce (t : ℝ) :
    Complex.exp ((angReduce t : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I) := by
  have hreal : angReduce t = t + ((-(⌊t / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi) := by
    unfold angReduce
    push_cast
    ring
  rw [hreal]
  have hcast : (((t + ((-(⌊t / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I
      = (t : ℂ) * Complex.I +
        ((-(⌊t / (2 * Real.pi)⌋) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hcast, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A choice of angle in `[0, 2π)` for every complex number: this is a genuine argument of
`z` whenever `‖z‖ = 1`, i.e. `exp (ang z * I) = z`. -/
noncomputable def ang (z : ℂ) : ℝ := angReduce (Complex.arg z)

theorem ang_mem (z : ℂ) : 0 ≤ ang z ∧ ang z < 2 * Real.pi := angReduce_mem (Complex.arg z)

theorem ang_exp {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp ((ang z : ℂ) * Complex.I) = z := by
  have harg : Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    simpa [hz] using this
  calc Complex.exp ((ang z : ℂ) * Complex.I)
      = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
        unfold ang; rw [exp_angReduce]
    _ = z := harg

theorem exists_strictMono_unit_enum (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1)
    (hne : u.Nonempty) :
    ∃ θ : Fin u.card → ℝ, StrictMono θ ∧ (∀ k, 0 ≤ θ k ∧ θ k < 2 * Real.pi) ∧
      (∀ k, Complex.exp ((θ k : ℂ) * Complex.I) ∈ u) ∧
      (∀ w ∈ u, ∃ k, Complex.exp ((θ k : ℂ) * Complex.I) = w) := by
  classical
  have _hne := hne
  have hang : ∀ w ∈ u, Complex.exp ((ang w : ℂ) * Complex.I) = w :=
    fun w hw => ang_exp (hu w hw)
  have hinj : Set.InjOn ang (↑u : Set ℂ) := by
    intro x hx y hy hxy
    rw [← hang x hx, ← hang y hy, hxy]
  have hcard : (u.image ang).card = u.card := Finset.card_image_of_injOn hinj
  refine ⟨(u.image ang).orderEmbOfFin hcard, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact (u.image ang).orderEmbOfFin hcard |>.lt_iff_lt.mpr hab
  · intro k
    obtain ⟨w, hwu, hw⟩ := Finset.mem_image.mp ((u.image ang).orderEmbOfFin_mem hcard k)
    rw [← hw]
    exact ang_mem w
  · intro k
    obtain ⟨w, hwu, hw⟩ := Finset.mem_image.mp ((u.image ang).orderEmbOfFin_mem hcard k)
    have : Complex.exp (((u.image ang).orderEmbOfFin hcard k : ℝ) * Complex.I) = w := by
      rw [← hw, hang w hwu]
    rw [this]
    exact hwu
  · intro w hwu
    have hmem : ang w ∈ u.image ang := Finset.mem_image.mpr ⟨w, hwu, rfl⟩
    have hrange : ang w ∈ Set.range ((u.image ang).orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact hmem
    obtain ⟨k, hk⟩ := Set.mem_range.mp hrange
    refine ⟨k, ?_⟩
    rw [hk, hang w hwu]

end Commons.Analysis.Complex