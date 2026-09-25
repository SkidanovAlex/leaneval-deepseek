import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.KPWW.thm19_of_thm19At2r

open MeasureTheory
open scoped ENNReal BigOperators lp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ## The duality/interpolation reduction of KMSZ §3.1 for the Ionescu–Wainger supersets `Σ_N`

`iwEndpoint2r` and `iwRangeBound` differ only in the exponent of the conclusion: the former is the
single exponent `p = 2r`, the latter the range `p ∈ [(2r)', 2r]`, with *the same* hypotheses (the
same symbol `ψ`, the same narrowness, the same `ℝ`-multiplier norms `IWMult r ψ A` and
`IWMult r (star ∘ ψ) A`, the same constant `A`).  So the reduction is the abstract operator one:

* the adjoint of the arc multiplier `opArcLM ψ hψ E` for the hermitian pairing
  `Σ_n u n · star (v n)` is `opArcLM (star ∘ ψ) h (star∘ψ) E` (`opArcLM_pairing`), so the endpoint
  bound applied to the *conjugate* symbol gives the `ℓ^{(2r)'}` bound for the primal operator with
  the same constant `C·A`;
* the endpoint bound itself is the `ℓ^{2r}` bound;
* Riesz–Thorin (`ellp_interpolation`) between the two exponents gives every
  `p ∈ [(2r)', 2r]` with constant `(C·A)^{1-θ}(C·A)^θ = C·A` (`M^{1-θ} M^{θ} = M`).
-/

/-- **The KMSZ §3.1 reduction for the Ionescu–Wainger superset `Σ_N`**: the endpoint case `p = 2r` (`Work.BourgainPlan.Maximal.iwEndpoint2r`) implies the full range `p ∈ [(2r)', 2r]` (`Work.BourgainPlan.Maximal.iwRangeBound`), by duality (`KPWW.opArcLM_pairing`, `KPWW.eLpNorm_dual_of_pairing`) and Riesz–Thorin (`Maximal.ellp_interpolation`). -/
theorem iwRangeBound_of_endpoint (h : Work.BourgainPlan.Maximal.iwEndpoint2r) :
    Work.BourgainPlan.Maximal.iwRangeBound := by
  intro ρ hρ r hr
  obtain ⟨C, hCpos, N₁, hbdd⟩ := h ρ hρ r hr
  refine ⟨C, hCpos, N₁, ?_⟩
  intro N hN ε hεpos hεle ψ hψ hsupp A hA hAψ hAψst p hp_lo hp_hi f hf
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set q : ℝ := 2 * (r : ℝ) with hqdef
  have hq2 : 2 ≤ q := by rw [hqdef]; linarith
  have hqpos : 0 < q := by linarith
  have h1q : 1 < q := by linarith
  set M : ℝ := C * A with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg hCpos.le hA
  -- the conjugate symbol `star ∘ ψ` and the two `IWMult` hypotheses for it
  set ψstar : AddCircle (1 : ℝ) → ℂ := star ψ with hψstardef
  have hψstarapply : ∀ ξ : AddCircle (1 : ℝ), ψstar ξ = star (ψ ξ) := by
    intro ξ; rw [hψstardef]; exact Pi.star_apply ψ ξ
  have hψstarmem : MemLp ψstar ⊤ (AddCircle.haarAddCircle (T := 1)) := by
    rw [hψstardef]; exact hψ.star
  have hsuppstar : ∀ ξ : AddCircle (1 : ℝ), ε < ‖ξ‖ → ψstar ξ = 0 := by
    intro ξ hξ; rw [hψstarapply ξ, hsupp ξ hξ, star_zero]
  have hAψstar : IWMult r ψstar A := hAψst
  have hAψst' : IWMult r (fun ξ => star (ψstar ξ)) A := by
    have hfun : (fun ξ : AddCircle (1 : ℝ) => star (ψstar ξ)) = ψ := by
      funext ξ; simp [hψstarapply]
    rw [hfun]; exact hAψ
  -- the endpoint bound at the exponent `q = 2r`, for `ψ` and for `ψstar`
  have hintψ : ∀ (u : ℤ → ℂ) (hu : Memℓp u 2),
      ∫⁻ n : ℤ, ‖opArc ψ hψ (iwSigma ρ N) u hu n‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ n : ℤ, ‖u n‖ₑ ^ q ∂Measure.count := by
    intro u hu
    have hb := hbdd N hN ε hεpos hεle ψ hψ hsupp A hA hAψ hAψst u hu
    rw [← hMdef] at hb
    exact hb
  have hintψstar : ∀ (u : ℤ → ℂ) (hu : Memℓp u 2),
      ∫⁻ n : ℤ, ‖opArc ψstar hψstarmem (iwSigma ρ N) u hu n‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ n : ℤ, ‖u n‖ₑ ^ q ∂Measure.count := by
    intro u hu
    have hb := hbdd N hN ε hεpos hεle ψstar hψstarmem hsuppstar A hA hAψstar hAψst' u hu
    rw [← hMdef] at hb
    exact hb
  have hend_q := Work.BourgainPlan.KPWW.eLpNorm_opArcLM_le_of_lintegral hqpos hMnn ψ hψ
    (iwSigma ρ N) hintψ
  have hend_q_star := Work.BourgainPlan.KPWW.eLpNorm_opArcLM_le_of_lintegral hqpos hMnn ψstar
    hψstarmem (iwSigma ρ N) hintψstar
  -- duality: the `ℓ^{(2r)'}` bound for the primal operator
  have hpq_conj : Real.HolderConjugate q (q / (q - 1)) := by
    have hh := Real.HolderConjugate.conjExponent h1q
    simpa [Real.conjExponent] using hh
  have hpair : ∀ u v : ℤ →₀ ℂ,
      ∑' n : ℤ, (v : ℤ → ℂ) n * star (opArcLM ψ hψ (iwSigma ρ N) u n)
        = ∑' n : ℤ, (opArcLM ψstar hψstarmem (iwSigma ρ N) v n) * star ((u : ℤ → ℂ) n) :=
    fun u v => Work.BourgainPlan.KPWW.opArcLM_pairing (φ := ψ) (ψ := ψstar) hψ hψstarmem
      hψstarapply (iwSigma ρ N) u v
  have hq'_end : ∀ g : ℤ →₀ ℂ,
      eLpNorm (opArcLM ψ hψ (iwSigma ρ N) g) (ENNReal.ofReal (q / (q - 1))) Measure.count
        ≤ ENNReal.ofReal M * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (q / (q - 1)))
            Measure.count :=
    Work.BourgainPlan.KPWW.eLpNorm_dual_of_pairing (p := q / (q - 1)) (q := q) hpq_conj.symm hMnn
      (opArcLM ψ hψ (iwSigma ρ N)) (opArcLM ψstar hψstarmem (iwSigma ρ N)) hpair hend_q_star
  have hp_lo' : q / (q - 1) ≤ p := by rw [hqdef]; exact hp_lo
  have hp_hi' : p ≤ q := by rw [hqdef]; exact hp_hi
  have hq1pos : 0 < q - 1 := by linarith
  have hq'pos : 0 < q / (q - 1) := by positivity
  have hq'le : q / (q - 1) ≤ q := by
    rw [div_le_iff₀ hq1pos]
    have hh : 0 ≤ q * (q - 2) := mul_nonneg (le_of_lt hqpos) (by linarith)
    linarith
  have hone_lt : 1 < q / (q - 1) := by rw [lt_div_iff₀ hq1pos]; linarith
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one (hone_lt.le.trans hp_lo')
  have hp1 : 1 < p := lt_of_lt_of_le hone_lt hp_lo'
  rcases lt_or_eq_of_le hMnn with hMpos | hMzero
  · -- non-degenerate case: duality + Riesz–Thorin
    set θ : ℝ := (1 / (q / (q - 1)) - 1 / p) / (1 / (q / (q - 1)) - 1 / q) with hθdef
    have hden_nn : 0 ≤ 1 / (q / (q - 1)) - 1 / q := by
      have hh := one_div_le_one_div_of_le hq'pos hq'le
      linarith
    have hnum_nn : 0 ≤ 1 / (q / (q - 1)) - 1 / p := by
      have hh := one_div_le_one_div_of_le hq'pos hp_lo'
      linarith
    have hnum_le : 1 / (q / (q - 1)) - 1 / p ≤ 1 / (q / (q - 1)) - 1 / q := by
      have hh := one_div_le_one_div_of_le hp0 hp_hi'
      linarith
    have hθ0 : 0 ≤ θ := by rw [hθdef]; exact div_nonneg hnum_nn hden_nn
    have hθ1 : θ ≤ 1 := by
      rw [hθdef]
      rcases eq_or_lt_of_le hden_nn with h0 | hpos
      · rw [← h0]; simp
      · exact (div_le_one hpos).mpr hnum_le
    have hθp : 1 / p = (1 - θ) / (q / (q - 1)) + θ / q := by
      have key : θ * (1 / (q / (q - 1)) - 1 / q) = 1 / (q / (q - 1)) - 1 / p := by
        rw [hθdef]
        rcases eq_or_lt_of_le hden_nn with h0 | hpos
        · have hA0 : 1 / (q / (q - 1)) - 1 / p = 0 := by
            have h' := hnum_le
            rw [← h0] at h'
            linarith
          rw [← h0, hA0]
          simp
        · exact div_mul_cancel₀ _ (ne_of_gt hpos)
      have hval : (1 - θ) / (q / (q - 1)) + θ / q
          = 1 / (q / (q - 1)) - θ * (1 / (q / (q - 1)) - 1 / q) := by ring
      rw [hval, key]
      ring
    have hMpow : M ^ (1 - θ) * M ^ θ = M := by
      rw [← Real.rpow_add hMpos]
      rw [show 1 - θ + θ = 1 by ring, Real.rpow_one]
    have hinterp := ellp_interpolation (q₀ := q / (q - 1)) (q₁ := q) (p := p) (θ := θ)
      (A := M) (B := M) (le_of_lt hone_lt) hq'le hp1 hθ0 hθ1 hθp hMpos hMpos
      (opArcLM ψ hψ (iwSigma ρ N)) hq'_end hend_q
    have hfin : ∀ g : ℤ →₀ ℂ,
        eLpNorm (opArcLM ψ hψ (iwSigma ρ N) g) (ENNReal.ofReal p) Measure.count
          ≤ ENNReal.ofReal M * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      intro g
      have hh := hinterp g
      rwa [hMpow] at hh
    have hext := Work.BourgainPlan.KPWW.eLpNorm_opArc_le_of_finsupp hp0 hMnn ψ hψ
      (iwSigma ρ N) hfin f hf
    have hlin : (eLpNorm (opArc ψ hψ (iwSigma ρ N) f hf) (ENNReal.ofReal p)
          Measure.count) ^ p
        = ∫⁻ n : ℤ, ‖opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ ^ p ∂Measure.count := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
          ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp0.le,
        ← ENNReal.rpow_mul,
        show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
    have hlin' : (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p
        = ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
          ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp0.le,
        ← ENNReal.rpow_mul,
        show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
    have hmain : ∫⁻ n : ℤ, ‖opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ ^ p ∂Measure.count
        ≤ ENNReal.ofReal (M ^ p) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
      calc ∫⁻ n : ℤ, ‖opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ ^ p ∂Measure.count
          = (eLpNorm (opArc ψ hψ (iwSigma ρ N) f hf) (ENNReal.ofReal p)
              Measure.count) ^ p := hlin.symm
        _ ≤ (ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
            ENNReal.rpow_le_rpow hext hp0.le
        _ = (ENNReal.ofReal M) ^ p
              * (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
            ENNReal.mul_rpow_of_nonneg _ _ hp0.le
        _ = ENNReal.ofReal (M ^ p) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
            rw [ENNReal.ofReal_rpow_of_nonneg hMnn hp0.le, hlin']
    rw [hMdef] at hmain
    exact hmain
  · -- degenerate case `M = 0`: the endpoint bound forces the multiplier output to vanish
    have hb := hbdd N hN ε hεpos hεle ψ hψ hsupp A hA hAψ hAψst f hf
    rw [← hMdef, ← hMzero] at hb
    have hzq : ∫⁻ n : ℤ, ‖opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ ^ q ∂Measure.count = 0 := by
      have h0 : ENNReal.ofReal ((0 : ℝ) ^ q) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ q ∂Measure.count = 0 := by
        rw [Real.zero_rpow (ne_of_gt hqpos)]; simp
      rw [h0] at hb
      exact le_antisymm hb zero_le
    rw [Work.BourgainPlan.KPWW.lintegral_enorm_rpow_eq_zero_of_eq_zero hqpos hp0 hzq]
    exact zero_le

end

end Work.BourgainPlan.Maximal
