import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.PureP.basic
import Submission.Work.PureP.germ_B2
import Submission.Work.PureP.germ_B3
import Submission.Work.PureP.germ_B4
import Submission.Work.PureP.germ_B5
import Submission.Work.CPull.germs

/-! Guidance from the project lead (the requester):

# Area PureP — pure functions pull back along any lifted map (`PurePullbacks`)
Generalise `Work.CPull.pullbackMero_B2/B3/B4` (proved for φ_C) and the in-progress B₅ (J via its
first-order ODE 2x(x−1)J' − xJ = 2(1−x)L), B₆, B₇ (primitives, `germ_intY`/`germ_tq`) from
`Submission/Work/CPull/` to an arbitrary φ with `LiftData φ Φ`. The x-side expressions
(L = log(1−x)): B₂∘y = 2y − x(x−2)L/(x−1), B₃∘y = −L²/2, B₄∘y = (x−w)(2Li₂ + L²/2), B₅∘y = xJ/(x−1);
Φ ≠ 1 on the disc follows from LiftData (Φ(z)=1 ⇒ Φ(−z) = 1 + Φ(−z)); descend to w = z² by evenness
(`germ_of_even`). Coordinate with CPull's agent H55 (message-free: just import its proved modules).
Contracts: `Submission/CDTPlan/InterfacesA2.lean` (Theorem A template), `InterfacesA.lean` (ψ_A, φ_A,
ANumerics, Zagier integrality), `InterfacesC.lean` (intY, tq, dY), `Interfaces.lean`.
The Theorem-C side has already solved the analogous pieces — REUSE, do not rebuild:
`Submission/Work/CPhi/` (lift of φ_C), `Submission/Work/CPull/` (germs.lean: `germ_of_even`,
`pullbackMero_of_germ`, `germ_intY`, `germ_tq`, pullbackMero_B2/B3/B4, deriv_phiC_zeros_finite),
`Submission/Work/CLift/` (continuation of P along Φ with OdeContinuation),
`Submission/Work/CDcl/` (symmetrised-powers route to the d/dy-closure), `Submission/Work/CDen/`.
Axiom-clean A-side facts: `Submission.Work.Purge.a_side_clean` bundles HA_ode, HB_ode, HC_ode,
GA_odeLHS_eq_zero, Cintegral/Aintegral identities, overconvergesB/C (use it instead of the
native_decide-tainted originals); `Work.ZagBI` re-proved HA_ode cleanly too. Never depend on
`native_decide` (check #print axioms).
-/

namespace Work.PureP

open Complex Metric Filter
open scoped Topology
open Submission.CDTPlan

/-- The pullback germ of `B₁ = 1` along any map `φ` (the trivial case). -/
theorem germ_B1 (φ Φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0)
    (hL : LiftData φ Φ) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n B1 : ℚ) : ℂ) * φ w ^ n) (N w) := by
  refine ⟨fun _ => 1, differentiableOn_const 1, ?_⟩
  refine Filter.Eventually.of_forall fun w => ?_
  refine (hasSum_ite_eq 0 (1 : ℂ)).congr_fun fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [B1]
  · simp [B1, PowerSeries.coeff_one, hn]

/-- `B₆ = ∫ B₃/y`: the germ of `B₆` along `φ` obtained from the germ of `B₃` by `tq` and `intY`. -/
theorem germ_B6 (φ Φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0)
    (hL : LiftData φ Φ) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n B6 : ℚ) : ℂ) * φ w ^ n) (N w) := by
  obtain ⟨N₃, hN₃, hg₃⟩ := germ_B3 φ Φ hφ hφ0 hL
  obtain ⟨N₁, hN₁, hg₁⟩ :=
    Work.CPull.germ_tq (f := B3) 1 hφ hφ0 (phi_ne_zero hL) hN₃ hg₃
  obtain ⟨N, hN, hg⟩ := Work.CPull.germ_intY (f := tq 1 B3) hφ hN₁ hg₁
  exact ⟨N, hN, by rwa [← Work.CPull.B6_eq_intY] at hg⟩

/-- `B₇ = ∫ B₄/y`: the germ of `B₇` along `φ` obtained from the germ of `B₄` by `tq` and `intY`. -/
theorem germ_B7 (φ Φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0)
    (hL : LiftData φ Φ) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n B7 : ℚ) : ℂ) * φ w ^ n) (N w) := by
  obtain ⟨N₄, hN₄, hg₄⟩ := germ_B4 φ Φ hφ hφ0 hL
  obtain ⟨N₁, hN₁, hg₁⟩ :=
    Work.CPull.germ_tq (f := B4) 1 hφ hφ0 (phi_ne_zero hL) hN₄ hg₄
  obtain ⟨N, hN, hg⟩ := Work.CPull.germ_intY (f := tq 1 B4) hφ hN₁ hg₁
  exact ⟨N, hN, by rwa [← Work.CPull.B7_eq_intY] at hg⟩

theorem pure_pullbacks : PurePullbacks := by
  intro φ Φ hφ hφ0 hL i
  fin_cases i
  · exact Work.CPull.pullbackMero_of_germ (germ_B1 φ Φ hφ hφ0 hL)
  · exact Work.CPull.pullbackMero_of_germ (germ_B2 φ Φ hφ hφ0 hL)
  · exact Work.CPull.pullbackMero_of_germ (germ_B3 φ Φ hφ hφ0 hL)
  · exact Work.CPull.pullbackMero_of_germ (germ_B4 φ Φ hφ hφ0 hL)
  · exact Work.CPull.pullbackMero_of_germ (germ_B5 φ Φ hφ hφ0 hL)
  · exact Work.CPull.pullbackMero_of_germ (germ_B6 φ Φ hφ hφ0 hL)
  · exact Work.CPull.pullbackMero_of_germ (germ_B7 φ Φ hφ hφ0 hL)

end Work.PureP
