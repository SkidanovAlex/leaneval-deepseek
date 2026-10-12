import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Rayleigh quotient of a bosonic box state in Dirichlet form

`symQuot N L v Ψ` is the corpus' Rayleigh quotient
`⟪Ψ, 𝓗 N v Ψ⟫ / ‖Ψ‖²` of a symmetric (bosonic) trial state `Ψ`.  This file
rewrites it in the "Dirichlet" form actually used in the sharp small-box
analysis: the kinetic term becomes the box integral of `|∇Ψ|²` (summed over the
`3N` coordinate directions) and the interaction term the box integral of
`Vpot N v · Ψ²`, while the denominator is the box integral of `Ψ²`.

The three ingredients are

* `Submission.BoseGases.energy_decomposition` — the expectation of the
  Hamiltonian splits as kinetic + interaction energy;
* `Submission.BoseGases.kinNeu_emb_eq` — the kinetic energy in operator form
  `∫ Ψ·(−ΔΨ)` equals the gradient form `∫ Σ (∂_{ik}Ψ)²`;
* `(√(∫ Ψ·Ψ))² = ∫ Ψ²`, since `∫ Ψ² ≥ 0`.

The integrability hypothesis needed by `energy_decomposition` is supplied by
`hV : IntOnBox N L (Vpot N v)`: the interaction integrand is `Ψ² · Vpot`, and
`Ψ²` is bounded (it is continuous with compact support).
-/

namespace Work.BoseSym.Assemble

open MeasureTheory Filter

theorem symQuot_eq_dirichlet {N : ℕ} {L : ℝ} (hL : 0 < L) {v : Work.BoseSym.E3 → ℝ}
    (hv : 0 ≤ v) (hV : Work.BoseSym.IntOnBox N L (Work.BoseSym.Vpot N v))
    (Ψ : Submission.BoseGases.SymBox N L) :
    Submission.BoseGases.symQuot N L v Ψ =
      ((Work.BoseSym.intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
          (fderiv ℝ (Ψ : Work.BoseSym.Conf N → ℝ) x (Work.BoseSym.eDir N i k)) ^ 2))
        + (Work.BoseSym.intBox N L (fun x =>
            Work.BoseSym.Vpot N v x * ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2)))
        / (Work.BoseSym.intBox N L (fun x => ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2)) := by
  -- The interaction integrand `Ψ² · Vpot` is integrable on the box, because `Ψ²` is
  -- bounded (continuous with compact support) and `Vpot` is integrable by hypothesis.
  have hint : IntegrableOn (Submission.BoseGases.intIntegrand N L v Ψ.toCInfty0Box)
      (BoseGases.box N L) volume := by
    rw [show Submission.BoseGases.intIntegrand N L v Ψ.toCInfty0Box
        = fun x => ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2 * Work.BoseSym.Vpot N v x from by
      funext x; rfl]
    obtain ⟨C, hC⟩ := (Submission.BoseGases.hasCompactSupport_Ψ hL Ψ.toCInfty0Box).exists_bound_of_continuous
      (Submission.BoseGases.psi_contDiff Ψ.toCInfty0Box).continuous
    refine Integrable.bdd_mul (c := C ^ 2) hV ?_ ?_
    · exact ((Submission.BoseGases.psi_contDiff Ψ.toCInfty0Box).continuous.pow 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2
            = ‖(Ψ : Work.BoseSym.Conf N → ℝ) x‖ ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
        _ ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  -- The numerator: kinetic + interaction, the two box integrals.
  have hnum : (∫ x in BoseGases.box N L,
        (Ψ : Work.BoseSym.Conf N → ℝ) x * BoseGases.𝓗 N v (Ψ : Work.BoseSym.Conf N → ℝ) x)
      = (Work.BoseSym.intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
          (fderiv ℝ (Ψ : Work.BoseSym.Conf N → ℝ) x (Work.BoseSym.eDir N i k)) ^ 2))
        + (Work.BoseSym.intBox N L (fun x =>
            Work.BoseSym.Vpot N v x * ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2)) := by
    have hdecomp := Submission.BoseGases.energy_decomposition N L v Ψ.toCInfty0Box hL hint
    rw [hdecomp]
    congr 1
    · -- kinetic energy in operator form = gradient form
      rw [← Submission.BoseGases.kinNeu_emb_eq hL Ψ.toCInfty0Box]; rfl
    · -- interaction energy = `∫ Vpot · Ψ²`
      rw [← Submission.BoseGases.boxInt_intIntegrand]
      rw [show Submission.BoseGases.intIntegrand N L v Ψ.toCInfty0Box
          = fun x => ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2 * Work.BoseSym.Vpot N v x from by
        funext x; rfl]
      rw [show (∫ x in BoseGases.box N L,
            ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2 * Work.BoseSym.Vpot N v x)
          = ∫ x in BoseGases.box N L,
              Work.BoseSym.Vpot N v x * ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2 from by
            apply integral_congr_ae; filter_upwards with x; ring]
      rfl
  -- The denominator: `(√(∫ Ψ·Ψ))² = ∫ Ψ²`.
  have hden : (Real.sqrt (∫ x in BoseGases.box N L,
        (Ψ : Work.BoseSym.Conf N → ℝ) x * (Ψ : Work.BoseSym.Conf N → ℝ) x)) ^ 2
      = Work.BoseSym.intBox N L (fun x => ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2) := by
    rw [show (∫ x in BoseGases.box N L,
          (Ψ : Work.BoseSym.Conf N → ℝ) x * (Ψ : Work.BoseSym.Conf N → ℝ) x)
        = ∫ x in BoseGases.box N L, ((Ψ : Work.BoseSym.Conf N → ℝ) x) ^ 2 from by
      apply integral_congr_ae; filter_upwards with x; ring]
    rw [Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]
    rfl
  unfold Submission.BoseGases.symQuot
  rw [hnum, hden]

end Work.BoseSym.Assemble
