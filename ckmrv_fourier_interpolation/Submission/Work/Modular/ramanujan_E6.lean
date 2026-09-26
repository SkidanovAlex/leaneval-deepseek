import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Modular.qExpansion_normalizedDerivOfComplex
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.slash_defect
import Submission.Work.Modular.isBoundedAtImInfty_normalizedDerivOfComplex

/-!
# Ramanujan's identity `D E₆ = (E₂ E₆ - E₄²)/2`

This file proves the weight-six Ramanujan identity for the normalized derivative
`D = (2πi)⁻¹ d/dτ` of the normalized Eisenstein series `E₆`.

The argument is the standard one.  The function

`H := ∂₆ E₆ + E₄²/2 = D E₆ - E₂ E₆/2 + E₄²/2`

is slash-invariant of weight `8` (`Derivative.serreDerivative_slash_invariant` for the first
summand, `ModularForm.mul_slash_SL2` for the second), holomorphic, and bounded at `i∞`
(boundedness of `D E₆` is Cauchy's estimate, `isBoundedAtImInfty_normalizedDerivOfComplex`).
Hence it is a level-one modular form of weight `8`.  Its `q`-expansion has vanishing
constant term: `(qExpansion 1 (D E₆)).coeff 0 = 0` because `D` multiplies the `n`-th
`q`-coefficient by `n` (`qExpansion_normalizedDerivOfComplex`), while
`(qExpansion 1 (E₂E₆)).coeff 0 = (qExpansion 1 (E₄²)).coeff 0 = 1`.  Since `0 = ⌊8/12⌋`, Sturm's
bound (`ModularForm.sturm_bound_levelOne`) forces `H = 0`.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm Filter
open scoped Manifold MatrixGroups ModularForm Topology

/-! ## Analyticity of the cusp function of the normalized derivative -/

/-- The `cuspFunction` of the normalized derivative `D f` is analytic at `q = 0`: near the cusp
it is given by `q ↦ q · C'(q)` where `C` is the cusp function of `f`, and that function is
analytic at `0`. -/
private theorem analyticAt_cuspFunction_normalizedDeriv {f : ℍ → ℂ}
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    AnalyticAt ℂ (cuspFunction 1 (Derivative.normalizedDerivOfComplex f)) 0 := by
  have hC : AnalyticAt ℂ (cuspFunction 1 f) 0 :=
    analyticAt_cuspFunction_zero one_pos hper hhol hbdd
  have hanalytic : AnalyticAt ℂ (fun q : ℂ => q * deriv (cuspFunction 1 f) q) 0 :=
    analyticAt_id.mul hC.deriv
  -- On the punctured unit disc the cusp function of `D f` is `q ↦ q C'(q)`.
  have hnonzero : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 →
      cuspFunction 1 (Derivative.normalizedDerivOfComplex f) q =
        q * deriv (cuspFunction 1 f) q := by
    intro q hqne hq
    have hw : 0 < (Function.Periodic.invQParam 1 q).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hqne
    have h1 : cuspFunction 1 (Derivative.normalizedDerivOfComplex f) q =
        Derivative.normalizedDerivOfComplex f
          (ofComplex (Function.Periodic.invQParam 1 q)) :=
      Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hqne
    have h2 : Derivative.normalizedDerivOfComplex f
          (ofComplex (Function.Periodic.invQParam 1 q)) =
        Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q) *
          deriv (cuspFunction 1 f)
            (Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q)) := by
      simpa [ofComplex_apply_of_im_pos hw] using
        normalizedDeriv_eq_qParam_mul_deriv_cuspFunction hper hhol
          ⟨Function.Periodic.invQParam 1 q, hw⟩
    rw [h1, h2, Function.Periodic.qParam_right_inv one_ne_zero hqne]
  -- Value at `q = 0`: both sides vanish, the left one by continuity at `0`.
  have h0eq : cuspFunction 1 (Derivative.normalizedDerivOfComplex f) 0 = 0 := by
    change Function.Periodic.cuspFunction 1
      ((Derivative.normalizedDerivOfComplex f) ∘ ofComplex) 0 = 0
    have hGcont : ContinuousAt
        (fun q : ℂ => q * deriv (cuspFunction 1 f) q) 0 := hanalytic.continuousAt
    have hlim : Tendsto (fun q : ℂ => q * deriv (cuspFunction 1 f) q)
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      have h := hGcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℂ)) (s := {0}ᶜ))
      simpa using h
    have hloc : Function.Periodic.cuspFunction 1
          ((Derivative.normalizedDerivOfComplex f) ∘ ofComplex) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun q : ℂ => q * deriv (cuspFunction 1 f) q) := by
      change ∀ᶠ q in 𝓝[≠] (0 : ℂ), Function.Periodic.cuspFunction 1
          ((Derivative.normalizedDerivOfComplex f) ∘ ofComplex) q =
            (fun q : ℂ => q * deriv (cuspFunction 1 f) q) q
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq hqne
      exact hnonzero q hqne (by simpa using hq)
    have htend : Tendsto (Function.Periodic.cuspFunction 1
        ((Derivative.normalizedDerivOfComplex f) ∘ ofComplex))
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := Filter.Tendsto.congr' hloc.symm hlim
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne, htend.limUnder_eq]
  have hcusp : cuspFunction 1 (Derivative.normalizedDerivOfComplex f) =ᶠ[𝓝 (0 : ℂ)]
      (fun q : ℂ => q * deriv (cuspFunction 1 f) q) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    rcases eq_or_ne q 0 with rfl | hqne
    · simpa using h0eq
    · exact hnonzero q hqne (by simpa using hq)
  exact hanalytic.congr hcusp.symm


/-! ## The auxiliary weight-`8` modular form `∂₆ E₆ + E₄²/2` -/

/-- The auxiliary function `H = ∂₆ E₆ + E₄²/2 = D E₆ - E₂E₆/2 + E₄²/2`, whose vanishing is
Ramanujan's identity. -/
private noncomputable def H8 : ℍ → ℂ :=
  Derivative.serreDerivative (6 : ℂ) E6 + (2 : ℂ)⁻¹ • (E4 * E4)

/-- Unfolding of `H8`. -/
private lemma H8_def : H8
    = Derivative.serreDerivative (6 : ℂ) E6 + (2 : ℂ)⁻¹ • (E4 * E4) := rfl

/-- `H8` in the form appearing in Ramanujan's identity. -/
private lemma H8_eq (z : ℍ) :
    H8 z = Derivative.normalizedDerivOfComplex E6 z - (E2 z * E6 z - E4 z ^ 2) / 2 := by
  simp only [H8, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivative.serreDerivative_apply,
    Pi.mul_apply]
  ring_nf

/-- The Serre derivative `∂₆ E₆` in the form used for `q`-expansions. -/
private lemma serreDerivative_six_E6_eq :
    Derivative.serreDerivative (6 : ℂ) E6
      = Derivative.normalizedDerivOfComplex E6 - ((6 : ℂ) * (12 : ℂ)⁻¹) • (E2 * E6) := by
  funext z
  simp only [Derivative.serreDerivative_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.mul_apply]
  ring_nf

/-- `H8` is slash-invariant of weight `8`. -/
private lemma H8_slash (γ : SL(2, ℤ)) : H8 ∣[(8 : ℤ)] γ = H8 := by
  have hE4sq : (E4 * E4) ∣[(8 : ℤ)] γ = E4 * E4 := by
    have h : (E4 * E4) ∣[((4 : ℤ) + 4)] γ = E4 * E4 := by
      rw [ModularForm.mul_slash_SL2 4 4 γ E4 E4,
        modularForm_slash_eq_self ModularForm.E₄ γ]
    rwa [show (4 : ℤ) + 4 = 8 by norm_num] at h
  have hsmul : ((2 : ℂ)⁻¹ • (E4 * E4)) ∣[(8 : ℤ)] γ = (2 : ℂ)⁻¹ • (E4 * E4) := by
    rw [SL_smul_slash, hE4sq]
  have hSD : Derivative.serreDerivative (6 : ℂ) E6 ∣[(8 : ℤ)] γ
      = Derivative.serreDerivative (6 : ℂ) E6 := by
    have h := Derivative.serreDerivative_slash_invariant (k := 6) (F := E6)
      (ModularFormClass.holo ModularForm.E₆) (modularForm_slash_eq_self ModularForm.E₆ γ)
    simpa using h
  rw [H8_def, SlashAction.add_slash, hSD, hsmul]

theorem ramanujan_E6 :
    Derivative.normalizedDerivOfComplex E6 = fun z : ℍ => (E2 z * E6 z - E4 z ^ 2) / 2 := by
  -- Basic facts about `E₂`, `E₄`, `E₆`
  have hE6per : Function.Periodic (E6 ∘ ofComplex) 1 := by
    simpa using SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL
  have hE6md : MDiff E6 := ModularFormClass.holo ModularForm.E₆
  have hE6bd : IsBoundedAtImInfty E6 := ModularFormClass.bdd_at_infty ModularForm.E₆
  have hE4per : Function.Periodic (E4 ∘ ofComplex) 1 := by
    simpa using SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL
  have hE4md : MDiff E4 := ModularFormClass.holo ModularForm.E₄
  have hE4bd : IsBoundedAtImInfty E4 := ModularFormClass.bdd_at_infty ModularForm.E₄
  have hE2md : MDiff E2 := E2_mdifferentiable
  have hE2bd : IsBoundedAtImInfty E2 := EisensteinSeries.isBoundedAtImInfty_E2
  have hE2per : Function.Periodic (E2 ∘ ofComplex) 1 := E2_periodic_one
  -- Boundedness of `D E₆` (Cauchy's estimate).
  have hDbd : IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex E6) :=
    isBoundedAtImInfty_normalizedDerivOfComplex
      ((UpperHalfPlane.mdifferentiable_iff).mp hE6md) hE6bd
  -- Analyticity of the relevant cusp functions at `q = 0`.
  have hDana : AnalyticAt ℂ (cuspFunction 1 (Derivative.normalizedDerivOfComplex E6)) 0 :=
    analyticAt_cuspFunction_normalizedDeriv hE6per hE6md hE6bd
  have hE2ana : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
    analyticAt_cuspFunction_zero one_pos hE2per hE2md hE2bd
  have hE6ana : AnalyticAt ℂ (cuspFunction 1 E6) 0 :=
    analyticAt_cuspFunction_zero one_pos hE6per hE6md hE6bd
  have hE4ana : AnalyticAt ℂ (cuspFunction 1 E4) 0 :=
    analyticAt_cuspFunction_zero one_pos hE4per hE4md hE4bd
  have h26per : Function.Periodic ((E2 * E6) ∘ ofComplex) 1 := hE2per.mul hE6per
  have h26ana : AnalyticAt ℂ (cuspFunction 1 (E2 * E6)) 0 :=
    analyticAt_cuspFunction_zero one_pos h26per (hE2md.mul hE6md) (hE2bd.mul hE6bd)
  have h44per : Function.Periodic ((E4 * E4) ∘ ofComplex) 1 := hE4per.mul hE4per
  have h44ana : AnalyticAt ℂ (cuspFunction 1 (E4 * E4)) 0 :=
    analyticAt_cuspFunction_zero one_pos h44per (hE4md.mul hE4md) (hE4bd.mul hE4bd)
  have hsmulana : AnalyticAt ℂ (cuspFunction 1 (((6 : ℂ) * (12 : ℂ)⁻¹) • (E2 * E6))) 0 := by
    rw [cuspFunction_smul h26ana.continuousAt]
    exact h26ana.const_smul
  have h44smulana : AnalyticAt ℂ (cuspFunction 1 ((2 : ℂ)⁻¹ • (E4 * E4))) 0 := by
    rw [cuspFunction_smul h44ana.continuousAt]
    exact h44ana.const_smul
  have hSDana : AnalyticAt ℂ (cuspFunction 1 (Derivative.serreDerivative (6 : ℂ) E6)) 0 := by
    rw [serreDerivative_six_E6_eq, cuspFunction_sub hDana.continuousAt hsmulana.continuousAt]
    exact hDana.sub hsmulana
  -- The constant terms of the relevant `q`-expansions.
  have hDcoeff : (qExpansion 1 (Derivative.normalizedDerivOfComplex E6)).coeff 0 = 0 := by
    rw [qExpansion_normalizedDerivOfComplex hE6per hE6md hE6bd 0]
    simp
  have h26coeff : (qExpansion 1 (E2 * E6)).coeff 0 = 1 := by
    rw [qExpansion_mul hE2ana hE6ana, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [E2_qExpansion_coeff, E6_qExpansion_coeff]
  have h44coeff : (qExpansion 1 (E4 * E4)).coeff 0 = 1 := by
    rw [qExpansion_mul hE4ana hE4ana, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [E4_qExpansion_coeff]
  -- The constant term of the `q`-expansion of `∂₆ E₆ = D E₆ - E₂E₆/2`.
  have hSDcoeff : (qExpansion 1 (Derivative.serreDerivative (6 : ℂ) E6)).coeff 0
      = -(2 : ℂ)⁻¹ := by
    rw [serreDerivative_six_E6_eq, qExpansion_sub hDana hsmulana,
      qExpansion_smul h26ana ((6 : ℂ) * (12 : ℂ)⁻¹)]
    rw [map_sub, map_smul, hDcoeff, h26coeff]
    norm_num
  -- `H8` is holomorphic and bounded at `i∞`, hence a modular form of weight `8`.
  have hSDbd : IsBoundedAtImInfty (Derivative.serreDerivative (6 : ℂ) E6) := by
    rw [serreDerivative_six_E6_eq, sub_eq_add_neg]
    exact hDbd.add (((hE2bd.mul hE6bd).smul ((6 : ℂ) * (12 : ℂ)⁻¹)).neg)
  have hH8md : MDiff H8 := by
    rw [H8_def]
    exact (Derivative.serreDerivative_mdifferentiable 6 hE6md).add
      (MDifferentiable.const_smul (2 : ℂ)⁻¹ (hE4md.mul hE4md))
  have hH8bd : IsBoundedAtImInfty H8 := by
    rw [H8_def]
    exact hSDbd.add ((hE4bd.mul hE4bd).smul (2 : ℂ)⁻¹)
  obtain ⟨HMod, hHMod⟩ :=
    modularForm_of_slash_invariant (k := 8) (f := H8) H8_slash hH8md hH8bd
  -- Its `q`-expansion has vanishing constant term.
  have hmod0 : (qExpansion 1 (⇑HMod)).coeff 0 = 0 := by
    rw [hHMod, H8_def, qExpansion_add hSDana h44smulana, qExpansion_smul h44ana (2 : ℂ)⁻¹]
    rw [map_add, map_smul, hSDcoeff, h44coeff]
    norm_num
  -- Sturm's bound: a weight-`8` modular form whose `q`-expansion has order `> 8/12 = 0`
  -- vanishes.
  have horder : (((8 : ℤ).toNat / 12 : ℕ) : ℕ∞) < (qExpansion 1 (⇑HMod)).order := by
    have h1 : (1 : ℕ∞) ≤ (qExpansion 1 (⇑HMod)).order :=
      PowerSeries.le_order _ 1 fun i hi => by
        have hi0 : i = 0 := by
          by_contra h
          have hle : (1 : ℕ∞) ≤ (i : ℕ∞) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
          exact absurd hle (not_le.mpr hi)
        simpa [hi0] using hmod0
    have h2 : (0 : ℕ∞) < (qExpansion 1 (⇑HMod)).order := lt_of_lt_of_le zero_lt_one h1
    have h3 : (((8 : ℤ).toNat / 12 : ℕ) : ℕ∞) = 0 := by norm_num
    rw [h3]
    exact h2
  have hHMod0 : HMod = 0 := ModularForm.sturm_bound_levelOne horder
  have hH8zero : ∀ z : ℍ, H8 z = 0 := by
    intro z
    have hcoe : (⇑HMod : ℍ → ℂ) = 0 := by rw [hHMod0, FunLike.coe_zero]
    have hz : HMod z = H8 z := congrFun hHMod z
    rw [congrFun hcoe z] at hz
    exact hz.symm
  -- Hence Ramanujan's identity.
  funext z
  have hz : H8 z = 0 := hH8zero z
  rw [H8_eq z] at hz
  exact sub_eq_zero.mp hz

end Work.Modular
