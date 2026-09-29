import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.CPull.germs
import Submission.Work.APull.germ_lift_even
import Submission.Work.APull.psiA_injective_ball
import Submission.Work.APull.deriv_psiA_ne_zero
import Submission.Work.APull.pullbackMero_deriv
import Submission.Work.APull.deriv_phiA_zeros_finite

/-! Guidance from the project lead (the requester):

# Area APull — pullbacks of the 14 functions along φ_A (`APullbacks`)
Mirror `Work.CPull.c_pullbacks` (H55, Theorem C). Φ from `hΦ` applied to ψ_A (hypotheses from
PsiAFacts and ANumerics' first conjunct ‖ψ_A'(0)‖ ≠ 0). Pure rows: `hPP`. G-rows: G(φ(z²)) =
F(z) + F(−z) (F from hL; `sympSym_subst`), even ⇒ holomorphic in w = z²; derivatives meromorphic with
denominator from the finitely many zeros of φ_A' in the disc (as `deriv_phiC_zeros_finite`: |ψ_A| < 1 on
the closed disc so zeros of h'∘ψ_A lie in a compact subset; ψ_A univalent or argue via isolated zeros);
integrals via `germ_intY`, `germ_tq`. Reuse CPull's generic `germs.lean` lemmas verbatim.
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

namespace Work.APull

open Submission.CDTPlan
open Filter
open scoped Topology

/-
## Proof outline

`APullbacks` asks for the meromorphic pullbacks of the 14 functions `fourteen a b c` along
`phiA = hauptH . psiA` under the absurd relation `ARel a b c`.

* `PhiLiftGen` applied to `psiA` (analytic facts `PsiAFacts`, `deriv psiA 0 = 0` excluded by
  `ANumerics`) produces a lift `Phi` of `z |-> phiA (z^2)` through the symmetrisation coordinate
  (`LiftData phiA Phi`), i.e. `Phi z + Phi (-z) = Phi z * Phi (-z) = phiA (z^2)`.
* Pure rows (`B1..B7`) come from `PurePullbacks` at `(phiA, Phi)`.
* The `G = Sym+HZ` row comes from `HLiftContA` (a holomorphic `F` with germ `Sum (HZ)_k Phi^k = F`)
  through `germ_lift_even`: the even germ `z |-> F z + F (-z)` descends through `w = z^2`
  (`germ_of_even`) and yields the pullback germ of `GZ`.
* The derivative rows come from `deriv_phiA_zeros_finite` (the critical set of `phiA` in the disc is
  finite: `norm (psiA z) < 1` on the closed disc, `psiA` is injective on the disc and
  `deriv psiA != 0` there) combined with `pullbackMero_deriv`.
* The integral rows come from `germ_tq` + `germ_intY`.
-/

theorem a_pullbacks (hL : HLiftContA) (hΦ : PhiLiftGen) (hPP : PurePullbacks) (hM : HauptFacts)
    (hP : PsiAFacts) (hN : ANumerics) : APullbacks := by
  intro a b c hrel i
  -- ψ_A is admissible for PhiLiftGen
  have hψdiff : DifferentiableOn ℂ psiA (Metric.ball 0 1) := hP.2.1
  have hψ0 : psiA 0 = 0 := hP.2.2.1
  have hψbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖psiA z‖ < 1 := hP.2.2.2.1
  have hψinj0 : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, psiA z = 0 → z = 0 := hP.2.2.2.2
  have hψ'0 : deriv psiA 0 ≠ 0 := by
    intro h0
    have h := hN.1
    rw [h0, norm_zero] at h
    norm_num at h
  have hψnorm : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖psiA z‖ < 1 :=
    fun z hz => hψbound z (Metric.ball_subset_closedBall hz)
  have hψinj : ∀ z ∈ Metric.ball (0 : ℂ) 1, psiA z = 0 → z = 0 :=
    fun z hz => hψinj0 z (Metric.ball_subset_closedBall hz)
  obtain ⟨Φ, hΦL⟩ := hΦ psiA hψdiff hψ0 hψ'0 hψnorm hψinj
  have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball 0 1) := hΦL.1
  have hΦrel : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Φ z + Φ (-z) = phiA (z ^ 2) ∧ Φ z * Φ (-z) = phiA (z ^ 2) := hΦL.2.1
  have hΦzero : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z = 0 → z = 0 := hΦL.2.2
  -- φ_A facts
  have hφ0 : phiA 0 = 0 := by
    show hauptH (psiA 0) = 0
    rw [hψ0]
    simp [Submission.CDTPlan.hauptH]
  have hΦ00 : Φ 0 = 0 := by
    have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [Metric.mem_ball]
    have h1 := (hΦrel 0 hmem).2
    rw [show ((0 : ℂ) ^ 2) = 0 from by norm_num, hφ0, neg_zero] at h1
    exact mul_self_eq_zero.mp h1
  have hφdiff : DifferentiableOn ℂ phiA (Metric.ball 0 1) := by
    show DifferentiableOn ℂ (fun z => hauptH (psiA z)) (Metric.ball 0 1)
    exact hM.1.comp hψdiff (fun z hz => by
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      exact hψnorm z (by rwa [Metric.mem_ball, dist_zero_right]))
  have hφ'0 : deriv phiA 0 ≠ 0 := by
    have hdz : DifferentiableAt ℂ psiA 0 :=
      hψdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball]))
    have hmem : psiA 0 ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, hψ0]; norm_num
    have hdh : DifferentiableAt ℂ hauptH (psiA 0) :=
      hM.1.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    have hchain : deriv phiA 0 = deriv hauptH (psiA 0) * deriv psiA 0 := by
      show deriv (fun x => hauptH (psiA x)) 0 = deriv hauptH (psiA 0) * deriv psiA 0
      have h := deriv_comp (x := (0 : ℂ)) hdh hdz
      simpa [Function.comp_def] using h
    rw [hchain, hψ0, hM.2.1]
    exact mul_ne_zero (by norm_num) hψ'0
  have hφzero : ∀ z ∈ Metric.ball (0 : ℂ) 1, phiA z = 0 → z = 0 := by
    intro z hz hz0
    have hmem : psiA z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hψnorm z hz
    have hψz0 : psiA z = 0 := hM.2.2.1 (psiA z) hmem (by simpa only [Submission.CDTPlan.phiA] using hz0)
    exact hψinj z hz hψz0
  -- the G row
  obtain ⟨F, hFdiff, hFsum⟩ := hL a b c hrel Φ hΦL
  obtain ⟨NG, hNG, hgG⟩ :=
    germ_lift_even (HZ a b c) phiA Φ F hφ0 hΦ00 hΦdiff hΦrel hΦzero hFdiff hFsum
  have hgGZ : ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun k : ℕ =>
      ((PowerSeries.coeff k (GZ a b c) : ℚ) : ℂ) * phiA w ^ k) (NG w) := hgG
  have hG : PullbackMero (GZ a b c) phiA := Work.CPull.pullbackMero_of_germ ⟨NG, hNG, hgGZ⟩
  -- the critical set and the derivative rows
  obtain ⟨S, hS⟩ := deriv_phiA_zeros_finite hM hP psiA_injective_ball deriv_psiA_ne_zero
  have hG1 : PullbackMero (dY (GZ a b c)) phiA :=
    pullbackMero_deriv S hφdiff hφ0 hφ'0 hS hG
  have hG2 : PullbackMero (dY (dY (GZ a b c))) phiA :=
    pullbackMero_deriv S hφdiff hφ0 hφ'0 hS hG1
  have hG3 : PullbackMero (dY (dY (dY (GZ a b c)))) phiA :=
    pullbackMero_deriv S hφdiff hφ0 hφ'0 hS hG2
  -- the integral rows
  obtain ⟨Ni, hNi, hgi⟩ := Work.CPull.germ_intY (f := GZ a b c) hφdiff hNG hgGZ
  have hiG : PullbackMero (intY (GZ a b c)) phiA := Work.CPull.pullbackMero_of_germ ⟨Ni, hNi, hgi⟩
  obtain ⟨Nt1, hNt1, hgt1⟩ := Work.CPull.germ_tq (f := GZ a b c) 1 hφdiff hφ0 hφzero hNG hgGZ
  obtain ⟨Ni1, hNi1, hgi1⟩ := Work.CPull.germ_intY (f := tq 1 (GZ a b c)) hφdiff hNt1 hgt1
  have hiG1 : PullbackMero (intY (tq 1 (GZ a b c))) phiA :=
    Work.CPull.pullbackMero_of_germ ⟨Ni1, hNi1, hgi1⟩
  obtain ⟨Nt2, hNt2, hgt2⟩ := Work.CPull.germ_tq (f := GZ a b c) 2 hφdiff hφ0 hφzero hNG hgGZ
  obtain ⟨Ni2, hNi2, hgi2⟩ := Work.CPull.germ_intY (f := tq 2 (GZ a b c)) hφdiff hNt2 hgt2
  have hiG2 : PullbackMero (intY (tq 2 (GZ a b c))) phiA :=
    Work.CPull.pullbackMero_of_germ ⟨Ni2, hNi2, hgi2⟩
  -- the pure rows
  have hpure : ∀ j : Fin 7, PullbackMero (pureB j) phiA :=
    hPP phiA Φ hφdiff hφ0 hΦL
  -- dispatch
  fin_cases i
  · exact hpure (0 : Fin 7)
  · exact hpure (1 : Fin 7)
  · exact hpure (2 : Fin 7)
  · exact hpure (3 : Fin 7)
  · exact hpure (4 : Fin 7)
  · exact hG
  · exact hG1
  · exact hG2
  · exact hG3
  · exact hpure (5 : Fin 7)
  · exact hpure (6 : Fin 7)
  · exact hiG
  · exact hiG1
  · exact hiG2

end Work.APull
