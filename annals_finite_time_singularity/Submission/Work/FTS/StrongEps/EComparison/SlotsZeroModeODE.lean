/-
# `SlotsZeroModeODE` - the zero-mode weak ODE of a homogeneous `bslOp`-solution

Proof of the target statement below (see `SlotsZeroModeMain`/`SlotsZeroModeKey3` for the
development).  The three conjuncts are

* `LocallyIntegrableOn (modeCoeff Φ m) (Ioi 0)` and `IntegrableOn ((modeCoeff Φ m)² z^{-4})`
  (`SlotsZeroModeL2`), and
* the weak Euler (indicial) equation with the self-adjoint weight `z^((5-α)/α)`:
  for every test function `ρ` compactly supported in `(0,∞)`,
  `∫_z z^((5-α)/α)(lam m·ρ z - α²z²ρ'' - α(5+α)zρ')·(modeCoeff Φ m z) = 0`,
  which is `key_iter` (the vanishing of the pairing of `Φ` with `bslOp α (ρ ⊗ e_m)`) after the
  pointwise identification `bslOp α (ρ ⊗ e_m) = (lam m·ρ - radOp α ρ)·e_m` off `θ = π/2`.

NOTE on the statement text: the statement as written uses a bare `π`, which is only the
identifier `Real.pi` under `open scoped Real` below (the lakefile sets `autoImplicit = false`,
so without that `open` the bare `π` is an unknown identifier and the file does not even
elaborate).  The statement text itself is unchanged.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem SlotsZeroModeODE {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (h0 : ∀ z, Φ z 0 = 0)
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    ∀ m : ℕ,
      MeasureTheory.LocallyIntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
      (∀ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) → HasCompactSupport ρ →
        tsupport ρ ⊆ Set.Ioi 0 →
        (∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
          - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
          * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ)) = 0) ∧
      MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * z ^ (-4 : ℝ))
        (Set.Ioi 0) := by
  intro m
  have hL2 : L2Facts α Φ := SlotsZeroModeL2 (α := α) (Φ := Φ) hsm hHk
  have hcut : CutFacts m := SlotsZeroCutoff m
  obtain ⟨C, hCpos, hCpt⟩ := hL2.2.2.2.1
  refine ⟨(hL2.1 m).1, ?_, (hL2.1 m).2⟩
  intro ρ hρ hρc hρs
  obtain ⟨a, b, ha, hab, hsub⟩ := exists_Icc_of_tsupport_subset hρc hρs
  have hk := key_iter (α := α) (Φ := Φ) (ρ := ρ) (m := m) (C := C) (a := a) (b := b)
    hsm hsol hρ hρc hρs hcut hL2.2.1 hCpt hCpos.le
    (hL2.2.2.2.2.2.2 a b ha hab) (hL2.2.2.2.2.1 a b ha hab) ha hsub
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
          * (z ^ ((5 - α) / α) * Real.cos θ))
        = z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
            - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
          * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ) := by
    intro z
    have hpt : (∫ θ in Work.Spaces.Iθ, Φ z θ
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, (z ^ ((5 - α) / α)
            * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
              - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
            * (Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
      rw [← restrict_Ioo_eq_Iθ]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      rw [bslOp_sepMode (α := α) (ρ := ρ) (m := m) hcos, radOp]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
  have hcongr : (∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
        * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Real.cos θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
          * (z ^ ((5 - α) / α) * Real.cos θ) := by
    refine MeasureTheory.setIntegral_congr_ae (μ := volume) (s := Set.Ioi 0)
      (f := fun z => z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
        * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ))
      (g := fun z => ∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
          * (z ^ ((5 - α) / α) * Real.cos θ))
      measurableSet_Ioi (Eventually.of_forall fun z _ => (hinner z).symm)
  rw [hcongr, hk]

end Work.FTS.StrongEps.EComparison
