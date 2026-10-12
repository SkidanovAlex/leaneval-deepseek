import ChallengeDeps
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
import Submission.Work.BoseFixR.mass_le_W1omega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

/-- **Finiteness of the three Coulomb double `∫⁻`-integrals of `W₁ = wScaled ℓ (g₀)` and
`g₀`.**  These are the three `≠ ⊤` hypotheses of `Work.BoseRowsFS.cross_chat_coulomb` at
the FS instance: the Newtonian self-energies of `W₁` and of `g₀`, and the cross energy of
`W₁` against `g₀`, are finite.

Route (existing lemmas only):
* conjunct 3 (cross): `Work.BoseFixR.lintegral_W1_g0_eq` gives
  `= ofReal (8π) * ofReal (∫ x, W₁ x · ω x) < ⊤` with `ω = Classical.choose h`;
* conjunct 2 (`g₀⊗g₀`): `Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton` with
  `g = g₀`, `ω = Classical.choose h` (uses `scattering_newton_representation`,
  `g0w0_integrable`, `Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae`) gives
  `= ofReal (8π·∫g₀ω) < ⊤`;
* conjunct 1 (`W₁⊗W₁`): `Work.BoseFixR.lintegral_W1W1_le_two_W1g0` gives
  `≤ 2·(W₁⊗g₀)` which is finite by conjunct 3. -/
theorem W1_g0_finite {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ y / ‖x - y‖)) ≠ ⊤
    ∧ (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y / ‖x - y‖)) ≠ ⊤
    ∧ (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ x * Submission.BoseGases.g0 v h y / ‖x - y‖)) ≠ ⊤ := by
  have hv : (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ≤ v := hv_nonneg
  -- conjunct 3: the cross energy `W₁⊗g₀` in closed form
  have key3 := Work.BoseFixR.lintegral_W1_g0_eq v h hR hv hvrad hv_supp hRℓ hℓ
  -- conjunct 2: the `g₀⊗g₀` energy is `ofReal (8π ∫ g₀ω)`
  have key2raw := Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton
    (g := Submission.BoseGases.g0 v h) (ω := Classical.choose h) (R := R)
    (Submission.BoseGases.g0_integrable hR hv_supp h)
    (Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h)
    (fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h)
    hR.le
    (Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h)
    (Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    (by
      have h0 := Submission.BoseGases.scattering_newton_representation (v := v)
        (w := Classical.choose h) (R := R) hR hvrad hv_supp
        (Classical.choose_spec h).1 (Classical.choose_spec h).2
      simpa [Submission.BoseGases.g0] using h0)
  -- conjunct 1: the `W₁⊗W₁` energy is at most twice the cross energy
  have key1 := Work.BoseFixR.lintegral_W1W1_le_two_W1g0 v h hR hv hvrad hv_supp hRℓ hℓ
  -- finiteness of the cross energy
  have hkey3 : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x *
        Submission.BoseGases.g0 v h y / ‖x - y‖)) ≠ ⊤ := by
    rw [key3, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * Real.pi)]
    exact ENNReal.ofReal_ne_top
  refine ⟨?_, ?_, ?_⟩
  · simp only [Work.BoseFixR.W1fun]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hkey3) key1
  · rw [key2raw]
    exact ENNReal.ofReal_ne_top
  · simp only [Work.BoseFixR.W1fun]
    exact hkey3

end Work.BoseRowsFS
