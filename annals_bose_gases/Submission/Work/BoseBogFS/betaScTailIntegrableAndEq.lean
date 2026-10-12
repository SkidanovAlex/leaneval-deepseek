import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.betaScTailIntegrableAndEq`

The *tail* of the honest pairing coefficient `betaSc` (in the *scaled* momentum variable
`t = k/√(ρ a v)`) is integrable and computes the same integral as `Ŵ₁` in the *unscaled*
momentum variable `p = √(ρ a v)·t`:

`∫_{‖t‖>T} betaSc(t)²/‖t‖³ dt = (a v)⁻² ∫_{‖p‖>√(ρ a v)·T} (chat W₁ p)²/‖p‖³ dp`.

## Route

* `Work.BoseBogFS.betaSc_eq`: `betaSc v h ρ μ t = (a v)⁻¹ · Ŵ₁(√(ρ a v)·t)`, where
  `Ŵ₁ = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))`;
* the **shell change of variables** `t ↦ S·t` with `S = √(ρ a v) > 0` (`smul_shell_integral`):
  `t ↦ S·t` maps `{T < ‖t‖}` onto `{S·T < ‖p‖}`, and the density `p ↦ g(p)²/‖p‖³` is scale
  invariant — the Jacobian `S³` cancels against the `S³` in `‖t‖⁻³ = S³·‖S•t‖⁻³`, so no factor
  of `S` survives (the integrand `‖p‖⁻³` is *marginal* in dimension three);
* **integrability**: `Work.BoseFixR.IntegrableChatW1sq` gives `p ↦ (Ŵ₁ p)²/(2‖p‖²) ∈ L¹`;
  composing with `t ↦ S•t` keeps it integrable (`MeasureTheory.Integrable.comp_smul`), and on
  `{T < ‖t‖}` the tail density `g(S•t)²/‖t‖³ = (2S²/‖t‖)·(g(S•t)²/(2‖S•t‖²))` is dominated by
  `(2S²/T)` times it (`‖t‖ > T`), which is what `Integrable.mono'` needs.
-/

namespace Work.BoseBogFS

section Aux

open MeasureTheory
open scoped Pointwise

/-- **The shell change of variables.**  For `S > 0`, the dilation `t ↦ S • t` maps the exterior
of the ball of radius `T` onto the exterior of the ball of radius `S·T`, and the density
`p ↦ g(p)²/‖p‖³` is invariant under the substitution: the Jacobian `S³` cancels the `S³` in the
identity `‖t‖⁻³ = S³·‖S•t‖⁻³`. -/
private lemma smul_shell_integral {g : EuclideanSpace ℝ (Fin 3) → ℝ} {S T : ℝ} (hS : 0 < S) :
    (∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (g (S • t)) ^ 2 / ‖t‖ ^ 3)
      = ∫ p in {p : EuclideanSpace ℝ (Fin 3) | S * T < ‖p‖}, (g p) ^ 2 / ‖p‖ ^ 3 := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hset : S • {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}
      = {p : EuclideanSpace ℝ (Fin 3) | S * T < ‖p‖} := by
    ext p
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hS.ne']
    show T < ‖S⁻¹ • p‖ ↔ S * T < ‖p‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS)]
    exact lt_inv_mul_iff₀ hS
  have hnorm : ∀ t : EuclideanSpace ℝ (Fin 3), ‖S • t‖ ^ 3 = S ^ 3 * ‖t‖ ^ 3 := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hS, mul_pow]
  have hpt : ∀ t : EuclideanSpace ℝ (Fin 3),
      (g (S • t)) ^ 2 / ‖t‖ ^ 3 = S ^ 3 * ((g (S • t)) ^ 2 / ‖S • t‖ ^ 3) := by
    intro t
    rw [hnorm t, ← mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero 3 hS.ne')]
  have hsmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖} :=
    measurableSet_lt measurable_const measurable_norm
  rw [← hset]
  calc ∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (g (S • t)) ^ 2 / ‖t‖ ^ 3
      = ∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖},
          S ^ 3 * ((g (S • t)) ^ 2 / ‖S • t‖ ^ 3) :=
        setIntegral_congr_fun hsmeas (fun t _ => hpt t)
    _ = S ^ 3 * ∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖},
          (g (S • t)) ^ 2 / ‖S • t‖ ^ 3 := MeasureTheory.integral_const_mul _ _
    _ = S ^ 3 * ((S ^ 3)⁻¹ * ∫ p in S • {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖},
          (g p) ^ 2 / ‖p‖ ^ 3) := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume)
          (f := fun p : EuclideanSpace ℝ (Fin 3) => (g p) ^ 2 / ‖p‖ ^ 3)
          (s := {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}) hS, hfin]
        simp only [smul_eq_mul]
    _ = ∫ p in S • {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (g p) ^ 2 / ‖p‖ ^ 3 := by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hS.ne'), one_mul]

end Aux

theorem betaScTailIntegrableAndEq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ T : ℝ}
    (hR : 0 < R) (hℓ : 0 < Work.BoseFixR.ell v μ)
    (hv : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ) (hT : 0 < T)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    MeasureTheory.IntegrableOn (fun t : EuclideanSpace ℝ (Fin 3) => (Work.BoseBogFS.betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}
      ∧ (∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (Work.BoseBogFS.betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        = ((_root_.BoseGases.a v) ^ 2)⁻¹
          * ∫ p in {p : EuclideanSpace ℝ (Fin 3) | Real.sqrt (ρ * _root_.BoseGases.a v) * T < ‖p‖},
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) p) ^ 2
                / ‖p‖ ^ 3 := by
  set g : EuclideanSpace ℝ (Fin 3) → ℝ :=
      Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) with hg
  set S : ℝ := Real.sqrt (ρ * _root_.BoseGases.a v) with hS
  have hSpos : 0 < S := by rw [hS]; exact Real.sqrt_pos.mpr (mul_pos hρ hav)
  -- the honest `β` is `(a v)⁻¹` times `Ŵ₁` at the scaled momentum
  have hpt : ∀ t : EuclideanSpace ℝ (Fin 3),
      betaSc v h ρ μ t = (_root_.BoseGases.a v)⁻¹ * g (S • t) := by
    intro t
    rw [hS, hg]
    exact betaSc_eq v hρ.ne' hav.ne' t
  have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hgcont : Continuous g := by
    rw [hg]; exact Work.BoseFixR.continuous_chat _ hWint
  have hGint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => g p ^ 2 / (2 * ‖p‖ ^ 2)) := by
    rw [hg]
    exact Work.BoseFixR.IntegrableChatW1sq h hv hvrad hR hℓ hv_supp hRℓ
  have hGcomp : MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin 3) => g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2)) :=
    hGint.comp_smul hSpos.ne'
  have hbsc_cont : Continuous (fun t : EuclideanSpace ℝ (Fin 3) => betaSc v h ρ μ t) := by
    rw [show (fun t : EuclideanSpace ℝ (Fin 3) => betaSc v h ρ μ t)
        = fun t => (_root_.BoseGases.a v)⁻¹ * g (S • t) from funext hpt]
    exact continuous_const.mul (hgcont.comp (continuous_const_smul _))
  have hsmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖} :=
    measurableSet_lt measurable_const measurable_norm
  -- the tail integrand is continuous on the shell
  have hcont : ContinuousOn
      (fun t : EuclideanSpace ℝ (Fin 3) => (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
      {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖} := by
    refine (hbsc_cont.continuousOn.pow 2).div (continuous_norm.continuousOn.pow 3) ?_
    intro x hx
    exact pow_ne_zero 3 (lt_trans hT hx).ne'
  have hmaj : MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        ((_root_.BoseGases.a v)⁻¹) ^ 2 * (2 * S ^ 2 / T)
          * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2))) :=
    hGcomp.const_mul _
  have hIntLHS : MeasureTheory.IntegrableOn
      (fun t : EuclideanSpace ℝ (Fin 3) => (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
      {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖} := by
    refine MeasureTheory.Integrable.mono' hmaj.integrableOn
      (hcont.aestronglyMeasurable hsmeas) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hsmeas] with t ht
    have hnormne : ‖t‖ ≠ 0 := (lt_trans hT ht).ne'
    have hSne : S ≠ 0 := hSpos.ne'
    have hnorm : ‖S • t‖ ^ 2 = S ^ 2 * ‖t‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hSpos, mul_pow]
    have hkey1 : g (S • t) ^ 2 / ‖t‖ ^ 3
        = (2 * S ^ 2 / ‖t‖) * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2)) := by
      rw [hnorm]; field_simp
    have hkey2 : (2 * S ^ 2 / ‖t‖) ≤ (2 * S ^ 2 / T) :=
      div_le_div_of_nonneg_left (by positivity) hT ht.le
    have hkey3 : (2 * S ^ 2 / ‖t‖) * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2))
        ≤ (2 * S ^ 2 / T) * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right hkey2 (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hpt t]
    calc ((_root_.BoseGases.a v)⁻¹ * g (S • t)) ^ 2 / ‖t‖ ^ 3
        = ((_root_.BoseGases.a v)⁻¹) ^ 2 * (g (S • t) ^ 2 / ‖t‖ ^ 3) := by ring
      _ = ((_root_.BoseGases.a v)⁻¹) ^ 2
            * ((2 * S ^ 2 / ‖t‖) * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2))) := by rw [hkey1]
      _ ≤ ((_root_.BoseGases.a v)⁻¹) ^ 2
            * ((2 * S ^ 2 / T) * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2))) :=
            mul_le_mul_of_nonneg_left hkey3 (by positivity)
      _ = ((_root_.BoseGases.a v)⁻¹) ^ 2 * (2 * S ^ 2 / T)
            * (g (S • t) ^ 2 / (2 * ‖S • t‖ ^ 2)) := by ring
  refine ⟨hIntLHS, ?_⟩
  -- the value of the integral: factor out `(a v)⁻¹`, then the shell substitution
  have h1 : (∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
      = ((_root_.BoseGases.a v)⁻¹) ^ 2
        * ∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (g (S • t)) ^ 2 / ‖t‖ ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun hsmeas (fun t _ => ?_)
    rw [hpt t]; ring
  calc (∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
      = ((_root_.BoseGases.a v)⁻¹) ^ 2
        * ∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, (g (S • t)) ^ 2 / ‖t‖ ^ 3 := h1
    _ = ((_root_.BoseGases.a v)⁻¹) ^ 2
        * ∫ p in {p : EuclideanSpace ℝ (Fin 3) | S * T < ‖p‖}, (g p) ^ 2 / ‖p‖ ^ 3 := by
        rw [smul_shell_integral (g := g) (S := S) (T := T) hSpos]
    _ = ((_root_.BoseGases.a v) ^ 2)⁻¹
        * ∫ p in {p : EuclideanSpace ℝ (Fin 3) | Real.sqrt (ρ * _root_.BoseGases.a v) * T < ‖p‖},
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) p) ^ 2
              / ‖p‖ ^ 3 := by
        rw [hS, hg, inv_pow]

end Work.BoseBogFS
