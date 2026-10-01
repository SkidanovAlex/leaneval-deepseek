/-
# `KsumWindowKeep` — HB Lemma 5.2 with a retained set of window zeros

`XY.KsumTwoWorking` bounds the `K`-sum by `-L·(two retained kernels) + f(0)(c+ε)L`, where the
two retained zeros must lie *strictly to the right* of the evaluation point.  The order-2
`Nebenfall` inequality (`XY/LamPrimeNebenfall`) instead retains zeros that lie in the Lemma-5.2
window `‖1 + i·Im s - u‖ ≤ δ` (Xylouris's `A₂`, i.e. possibly *on* the line `Re = Re s`), and
retains up to three of them at once.

This file provides that form: for any `Finset A` of zeros in the window for which every window
zero satisfies `Re u ≤ Re s` (so that all kernels are non-negative by Condition 2),

`K(s,χ) ≤ -L·Σ_{u∈A} ord(u)·Re F((s-u)L) + f(0)(c+ε)L`.

It is the direct combination of `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim`
(the `ε/2` form, giving `K ≤ -L·W + f(0)(c+ε/2)L` with `W` the full window sum) with the
multi-zero window retention `XY.windowSum_finset_ge` (`Σ_A ≤ W`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.XY.WindowSumFinset

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.XY

/-- **HB Lemma 5.2 with a retained `Finset` of window zeros.** -/
theorem KsumWindowKeep (x₀ B c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
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
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ →
        ∀ (A : Finset ℂ),
          (∀ u ∈ A, (MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0) →
          (∀ u ∈ A, ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) →
          (∀ u : ℂ, (MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
              ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) →
        Work.ZeroFreeTables.Ksum q f (Real.log (q : ℝ)) s χ
          ≤ -(Real.log (q : ℝ)) *
              (∑ u ∈ A, (((MeromorphicOn.divisor
                  (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
                ((∫ t in (0:ℝ)..x₀,
                    Complex.exp (-(((s - u) * ((Real.log q : ℝ) : ℂ)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re))
            + f 0 * (c + ε) * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₁, h₁⟩ := (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim
      x₀ B c hx₀ hB) hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max q₁ 2, ?_⟩
  intro q _inst hq χ _instc hχ s hsre hsim hs1 hH A hdiv hwin hzero
  have hq₁ : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hLnn : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1)
  have hLpos : (0:ℝ) < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  -- HB Lemma 5.2 at `ε/2`
  have hmain : Work.ZeroFreeTables.Ksum q f (Real.log (q : ℝ)) s χ
      ≤ -(Real.log (q : ℝ)) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
            ((∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re) else 0))
        + f 0 * (c + ε) * Real.log (q : ℝ) :=
    h₁ hq₁ χ hχ (fun s' hsre' hsim' hs1' => hH s' hsre' hsim' hs1') s hsre hsim hs1
  -- the retained sum is dominated by the window sum
  have hwin' := windowSum_finset_ge (q := χ.conductor) (χ := χ.primitiveCharacter) hχ'
    (f := f) (x₀ := x₀) (L := Real.log (q:ℝ)) (s := s) (δ := δ) hLnn hF A hdiv hwin hzero
  have hstep : -(Real.log (q : ℝ)) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re) else 0))
      ≤ -(Real.log (q : ℝ)) * (∑ u ∈ A, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
          ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re)) := by
    have h := mul_le_mul_of_nonneg_left hwin' (by linarith : (0:ℝ) ≤ Real.log (q:ℝ))
    linarith
  linarith [hmain, hstep]

end Work.ZeroFreeTables.XY
