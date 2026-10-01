/-
# ZeroFreeTables/XY/KsumWindowKeepFinsetV

The `KsumWindowKeepFinset` retention lemma with a **weakened order hypothesis**: the bound
`ord(u) ≤ 10` is required only for the retained zeros that lie *outside* the Lemma-5.2 window
`‖1 + i·Im s - u‖ ≤ δ`.

Why: in the proof of `KsumWindowKeepFinset` the order bound is used only for the "far" part of the
retained `Finset` (the finite sum is split by `sum_le_filter_add_card_mul`, and the zeros inside the
window are kept *exactly*, only those outside it are absorbed into the slack via `FarZeroSmall`).
The application (`XY.NebenfallOrd2V`) retains a zero `u` of unknown multiplicity that lies *inside*
the window (its distance from the window centre is `λ_u/L ≤ δ` for `q` large), so the uniform order
bound `ord(u) ≤ 10` of `KsumWindowKeepFinset` cannot be discharged; the variant below can.

The proof is literally that of `KsumWindowKeepFinset`, with the single use of `hord` restricted to
the `¬ win u` branch of `hfar` (where the extra hypothesis is available).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.KsumWindowKeepFinset

namespace Work.ZeroFreeTables.XY

theorem KsumWindowKeepFinsetV (x₀ B c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {s : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ 10 * Real.log (q : ℝ) →
        1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
        Commons.NumberTheory.Linnik.L52Hyp χ c (ε/2) δ →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → s.re < u.re → False) →
        ∀ (A : Finset ℂ), A.card ≤ 10 →
        (∀ u ∈ A, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0) →
        (∀ u ∈ A, u.re ≤ s.re) →
        (∀ u ∈ A, |(((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)).re)| ≤ 1) →
        (∀ u ∈ A, ¬ (‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) →
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u) ≤ 10) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q : ℝ)))
          ≤ -(Real.log (q : ℝ)) * (∑ u ∈ A,
                (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * ((Real.log q : ℝ) : ℂ)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
            + f 0 * (c + ε) * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₁, h₁⟩ := KsumWindowKeep x₀ B c hx₀ hB hcont hsupp hf2 hBnd hf0 hF
      (show (0:ℝ) < ε/2 by linarith) hδ0 hδ1
  obtain ⟨q₂, h₂⟩ := FarZeroSmall x₀ B hx₀ hB hcont hsupp hf2 hBnd hf0
      (show (0:ℝ) < ε/100 by linarith) hδ0
  refine ⟨max (max q₁ q₂) 2, ?_⟩
  intro q _inst hq χ _instc hχ s hsre hsim hs1 hH hno A hcard hdiv hle hre hord
  classical
  have hq₁ : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq₂ : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : 0 ≤ Real.log (q:ℝ) := le_of_lt hLpos
  have hf0nn : 0 ≤ f 0 := le_of_lt hf0
  have hεnn : 0 ≤ ε := le_of_lt hε
  -- the primitive character is non-principal
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  -- non-negativity of the divisor on the ball
  have hDnn : ∀ u : ℂ, (0:ℝ) ≤ (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) := by
    intro u
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
    exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u)
  -- the window predicate
  set win : ℂ → Prop := fun u => ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ with hwindef
  -- Lemma 5.2 for the retained set of *window* zeros in `A`
  have hdivW : ∀ u ∈ A.filter win, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 := by
    intro u hu
    exact hdiv u (Finset.mem_filter.mp hu).1
  have hwinW : ∀ u ∈ A.filter win, ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    simpa only [hwindef] using h
  have hzeroW : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
    intro u hdu hw
    exact not_lt.mp (hno u hdu hw)
  have hmain := h₁ hq₁ χ hχ (s := s) hsre hsim hs1 hH (A.filter win) hdivW hwinW hzeroW
  -- the per-zero factor of the retained sum, as a local abbreviation
  set g : ℂ → ℝ := fun u =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
      (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * ((Real.log q : ℝ) : ℂ)) * (t : ℂ))) *
        ((f t : ℝ) : ℂ)).re with hgdef
  -- the far zeros contribute only a constant, absorbed by the extra slack `ε/2`
  have hfar : ∀ u ∈ A, ¬ win u → g u ≤ f 0 * ε / 400 := by
    intro u hu hnu
    have hnu' : ¬ (‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) := by
      simpa only [hwindef] using hnu
    have hδlt : δ < ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ := not_le.mp hnu'
    have hb := h₂ hq₂ hsre (hre u hu) hδlt
    have hordR : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) ≤ 10 := by
      exact_mod_cast hord u hu hnu'
    have h1 : g u ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) * (f 0 * (ε/100) / 40) :=
      mul_le_mul_of_nonneg_left hb (hDnn u)
    have h2 : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) * (f 0 * (ε/100) / 40)
        ≤ 10 * (f 0 * (ε/100) / 40) :=
      mul_le_mul_of_nonneg_right hordR (by positivity)
    have h3 : (10:ℝ) * (f 0 * (ε/100) / 40) = f 0 * ε / 400 := by ring
    linarith [h1, h2, h3]
  have hbase := sum_le_filter_add_card_mul A win g (c := f 0 * ε / 400) (by positivity) hfar
  have hbase' : A.sum g ≤ (A.filter win).sum g + (A.card : ℝ) * (f 0 * ε / 400) := hbase
  have hcardle : (A.card : ℝ) * (f 0 * ε / 400) ≤ f 0 * ε / 40 := by
    have h10 : (A.card : ℝ) ≤ 10 := by exact_mod_cast hcard
    have hc0 : (0:ℝ) ≤ f 0 * ε / 400 := by positivity
    calc (A.card : ℝ) * (f 0 * ε / 400) ≤ 10 * (f 0 * ε / 400) :=
          mul_le_mul_of_nonneg_right h10 hc0
      _ = f 0 * ε / 40 := by ring
  have hsplit : A.sum g ≤ (A.filter win).sum g + f 0 * ε / 40 := by linarith [hbase', hcardle]
  -- finish: absorb the far contribution into the slack
  have hstep : -(Real.log (q:ℝ)) * ((A.filter win).sum g) + f 0 * (c + ε/2) * Real.log (q:ℝ)
      ≤ -(Real.log (q:ℝ)) * (A.sum g) + f 0 * (c + ε) * Real.log (q:ℝ) := by
    have h1 : -(Real.log (q:ℝ)) * ((A.filter win).sum g)
        ≤ -(Real.log (q:ℝ)) * (A.sum g) + Real.log (q:ℝ) * (f 0 * ε / 40) := by
      have hh : Real.log (q:ℝ) * (A.sum g)
          ≤ Real.log (q:ℝ) * ((A.filter win).sum g) + Real.log (q:ℝ) * (f 0 * ε / 40) := by
        calc Real.log (q:ℝ) * (A.sum g) ≤ Real.log (q:ℝ) * ((A.filter win).sum g + f 0 * ε / 40) :=
              mul_le_mul_of_nonneg_left hsplit hLnn
          _ = Real.log (q:ℝ) * ((A.filter win).sum g) + Real.log (q:ℝ) * (f 0 * ε / 40) := by ring
      linarith [hh]
    have h3 : f 0 * (c + ε/2) * Real.log (q:ℝ) + Real.log (q:ℝ) * (f 0 * ε / 40)
        ≤ f 0 * (c + ε) * Real.log (q:ℝ) := by
      have hnn : 0 ≤ f 0 * ε * Real.log (q:ℝ) := mul_nonneg (mul_nonneg hf0nn hεnn) hLnn
      nlinarith [hnn]
    linarith [h1, h3]
  have hKsum : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q : ℝ)))
      = Work.ZeroFreeTables.Ksum q f (Real.log (q : ℝ)) s χ := by
    simp only [Work.ZeroFreeTables.Ksum]
  linarith [hKsum, hmain, hstep]

end Work.ZeroFreeTables.XY
