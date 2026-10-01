/-
# The extremal-function package of Heath-Brown §7/§8 (`κ`-bound for `λ₂`)

The "optimal" test function of Heath-Brown (1992), §7 (Lemma 7.1 with the parameter `k = 2`,
i.e. `sin²θ = 2(1 - θ cot θ)`) satisfies *Condition 1* and *Condition 2* of §6 and, in addition,
the identity of Lemma 7.5 with `k = 2`:

`F(-λ) - 2F(0) = -λ⁻¹ f(0)cos²θ`.

The last ingredient of the Deuring–Heilbronn argument ("Lemma 8.2") is that the five-term
inequality of Lemma 8.5 then forces `λ₂ ≥ cos²θ/A`.

This file assembles the package from:

* `extCosFbasic.lean` — the elementary facts about `Commons.NumberTheory.Linnik.extCosF`
  (closed form, positivity at `0`, non-negativity, continuity, `C²`-regularity, the identity of
  Lemma 7.5 and the resulting `κ`-bound);
* `thetaTwo.lean` — existence of the extremal `θ > 3/4`;
* `laplaceAnalytic.lean` / `laplaceDecay.lean` — the Phragmén–Lindelöf inputs for the Laplace
  transform of `extCosF`;
* `extCosF_boundaryRe.lean` — its non-negativity on the imaginary axis;
* `Commons.Analysis.Complex.re_ge_norm_of_boundary` — the Phragmén–Lindelöf step itself.
-/
import Mathlib
import Submission.Work.LinnikAreas.DhRepel.extCosFbasic
import Submission.Work.LinnikAreas.DhRepel.thetaTwo
import Submission.Work.LinnikAreas.DhRepel.laplaceAnalytic
import Submission.Work.LinnikAreas.DhRepel.laplaceDecay
import Submission.Work.LinnikAreas.DhRepel.extCosF_boundaryRe
import Submission.Commons.Analysis.Complex.re_ge_norm_of_boundary

open Real MeasureTheory intervalIntegral Set Filter
open scoped Real Topology

namespace Work.LinnikAreas.DhRepel

noncomputable section

set_option autoImplicit false

theorem extremalPackage : ∃ (θ κ : ℝ), 0 < θ ∧ θ < Real.pi / 2 ∧
    Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ)) ∧ 0 < κ ∧
    (∀ lam : ℝ, 0 < lam → 0 < Commons.NumberTheory.Linnik.extCosF θ lam 0) ∧
    (∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t → 0 ≤ Commons.NumberTheory.Linnik.extCosF θ lam t) ∧
    (∀ lam : ℝ, 0 < lam → ContinuousOn (Commons.NumberTheory.Linnik.extCosF θ lam) (Set.Ici 0)) ∧
    (∀ lam : ℝ, 0 < lam → ∀ t : ℝ,
      2 * (θ / (lam * Real.tan θ)) ≤ t → Commons.NumberTheory.Linnik.extCosF θ lam t = 0) ∧
    (∀ lam : ℝ, 0 < lam → ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
            Complex.exp (-(z * (t : ℂ))) *
              ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ)).re) ∧
    (∀ lam : ℝ, 0 < lam →
      (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
          Real.exp (lam * t) * Commons.NumberTheory.Linnik.extCosF θ lam t)
        - 2 * (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
            Commons.NumberTheory.Linnik.extCosF θ lam t)
      = -(1 / lam) * Commons.NumberTheory.Linnik.extCosF θ lam 0 * Real.cos θ ^ 2) ∧
    (∀ {lam1 lam2 A : ℝ}, 0 < lam2 → 0 ≤ lam1 → lam1 ≤ lam2 → 0 < A →
      (0 ≤ (∫ t in (0:ℝ)..(2 * (θ / (lam2 * Real.tan θ))),
              Real.exp (lam2 * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
          - (∫ t in (0:ℝ)..(2 * (θ / (lam2 * Real.tan θ))),
              Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
          - (∫ t in (0:ℝ)..(2 * (θ / (lam2 * Real.tan θ))),
              Commons.NumberTheory.Linnik.extCosF θ lam2 t)
          + Commons.NumberTheory.Linnik.extCosF θ lam2 0 * A) → κ ≤ lam2 * A) := by
  obtain ⟨θ, hθ34, hθ1, heq⟩ := thetaTwo
  have hθ0 : 0 < θ := by linarith
  have hcosp : 0 < Real.cos θ := cosTheta_pos hθ0 hθ1
  refine ⟨θ, Real.cos θ ^ 2, hθ0, hθ1, heq, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lam hlam
    exact extCosF_zero_pos hθ0 hθ1 hlam hθ34 heq
  · intro lam hlam t ht
    exact extCosF_nonneg_of_nonneg hθ0 hθ1 hlam ht
  · intro lam hlam
    exact continuousOn_extCosF hθ0 hθ1 hlam
  · intro lam hlam t ht
    exact extCosF_eq_zero_of_ge hθ0 hθ1 hlam ht
  · -- Condition 2 of Heath-Brown §6: `Re F(z) ≥ 0` for `Re z ≥ 0`, by Phragmén–Lindelöf
    intro lam hlam z hz
    have hγ : 0 < gammaF θ lam := gammaF_pos hθ0 hθ1 hlam
    have hx₀ : 0 < 2 * gammaF θ lam := by linarith
    have hcont : ContinuousOn
        (fun t : ℝ => ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ))
        (Set.Icc 0 (2 * gammaF θ lam)) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_extCosF hθ0 hθ1 hlam).mono (fun x hx => hx.1))
    have hvan : ∀ t : ℝ, 2 * gammaF θ lam ≤ t →
        ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ) = 0 := by
      intro t ht
      rw [extCosF_eq_zero_of_ge hθ0 hθ1 hlam ht]
      simp
    have hana := laplaceAnalytic (x₀ := 2 * gammaF θ lam) hx₀ hcont
    have hdecc := laplaceDecay (x₀ := 2 * gammaF θ lam) hx₀ hcont
      (contDiffOn_extCosF hθ0 hθ1 hlam) (exists_iteratedDeriv_two_bound_extCosF hθ0 hθ1 hlam) hvan
    have hbd : ∀ y : ℝ, 0 ≤ ((fun w : ℂ => ∫ t in (0:ℝ)..(2 * gammaF θ lam),
        Complex.exp (-(w * (t : ℂ))) * ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ))
          (Complex.I * (y : ℂ))).re
        - ‖(fun _ : ℂ => (0 : ℂ)) (Complex.I * (y : ℂ))‖ := fun y => by
      have h := extCosF_boundaryRe hθ0 hθ1 hlam y
      rw [show 2 * (θ / (lam * Real.tan θ)) = 2 * gammaF θ lam by rw [gammaF]] at h
      simpa using h
    have hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, 0 ≤ w.re → R ≤ ‖w‖ →
        ‖(fun w : ℂ => ∫ t in (0:ℝ)..(2 * gammaF θ lam),
          Complex.exp (-(w * (t : ℂ))) * ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ)) w‖ < ε
        ∧ ‖(fun _ : ℂ => (0 : ℂ)) w‖ < ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := hdecc ε hε
      exact ⟨R, fun w hw hRw => ⟨hR w hw hRw, by simpa using hε⟩⟩
    have hPL := Commons.Analysis.Complex.re_ge_norm_of_boundary
      (F1 := fun w : ℂ => ∫ t in (0:ℝ)..(2 * gammaF θ lam),
        Complex.exp (-(w * (t : ℂ))) * ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ))
      (F2 := fun _ : ℂ => (0 : ℂ)) hana.1 (differentiableOn_const (0 : ℂ)) hana.2
      continuousOn_const hbd hdec
    rw [show 2 * (θ / (lam * Real.tan θ)) = 2 * gammaF θ lam by rw [gammaF]]
    simpa using hPL z hz
  · intro lam hlam
    exact extCosF_laplace_identity hθ0 hθ1 hlam heq
  · intro lam1 lam2 A hlam2 hlam1 h12 hA hineq
    exact cos_sq_le_of_five_term hθ0 hθ1 heq hlam2 hlam1 h12
      (extCosF_zero_pos hθ0 hθ1 hlam2 hθ34 heq) hineq

end

end Work.LinnikAreas.DhRepel
