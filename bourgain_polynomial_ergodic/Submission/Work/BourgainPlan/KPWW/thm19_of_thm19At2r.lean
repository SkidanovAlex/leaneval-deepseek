import Mathlib
import Submission.Work.BourgainPlan.KPWW.Thm19
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_ftLp
import Submission.Work.BourgainPlan.KPWW.opArcLM_pairing
import Submission.Work.BourgainPlan.KPWW.eLpNorm_le_of_pairing_bound
import Submission.Work.BourgainPlan.KPWW.eLpNorm_opArc_le_of_finsupp

open MeasureTheory
open scoped ENNReal BigOperators lp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.KPWW

open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal

noncomputable section

/-! ## Elementary helpers -/

/-- `opArc` only depends on the sequence, not on the proof that it lies in `ℓ²`. -/
theorem opArc_congr_memℓp (φ : AddCircle (1 : ℝ) → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset (AddCircle (1 : ℝ))) {f : ℤ → ℂ} (hf hf' : Memℓp f 2) :
    opArc φ hφ E f hf = opArc φ hφ E f hf' := by
  funext n
  simp only [opArc, opMul, opMulLp, ftLp_congr_memℓp rfl hf hf']

/-- The adjunction `⟪Φ • F, G⟫ = ⟪F, star Φ • G⟫` for an `L^∞`-symbol `Φ` acting on `L²`. -/
theorem inner_lpSMul_star' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Φ : Lp ℂ ⊤ μ) (F G : Lp ℂ 2 μ) :
    inner ℂ (Φ • F : Lp ℂ 2 μ) G = inner ℂ F (star Φ • G : Lp ℂ 2 μ) := by
  rw [inner_lpSMul_star (star Φ) F G, star_star]

/-- The symbol of the conjugate bump is the conjugate of the symbol: if `ψ = star ∘ φ` pointwise,
then `star (arcSymbolLp φ hφ E) = arcSymbolLp ψ hψ E`. -/
theorem star_arcSymbolLp {φ ψ : AddCircle (1 : ℝ) → ℂ}
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hψ : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hψφ : ∀ ξ, ψ ξ = star (φ ξ)) (E : Finset (AddCircle (1 : ℝ))) :
    star (arcSymbolLp φ hφ E) = arcSymbolLp ψ hψ E := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (arcSymbolLp φ hφ E), arcSymbolLp_coeFn φ hφ E,
    arcSymbolLp_coeFn ψ hψ E] with ξ h1 h2 h3
  rw [h1]
  simp only [Pi.star_apply, h2, h3]
  simp only [arcSymbol_apply]
  rw [star_sum]
  exact Finset.sum_congr rfl (fun β _ => (hψφ (ξ - β)).symm)

/-- If `∫⁻ ‖u‖^q = 0` with `q > 0`, then `∫⁻ ‖u‖^p = 0` for every `p > 0`.  (On the counting
measure the two `∫⁻`-conditions are the two ways of saying that `u` vanishes.) -/
theorem lintegral_enorm_rpow_eq_zero_of_eq_zero {q p : ℝ} (hq : 0 < q) (hp : 0 < p)
    {u : ℤ → ℂ} (h : ∫⁻ n : ℤ, ‖u n‖ₑ ^ q ∂Measure.count = 0) :
    ∫⁻ n : ℤ, ‖u n‖ₑ ^ p ∂Measure.count = 0 := by
  have h3 : (fun n : ℤ => ‖u n‖ₑ ^ q) =ᵐ[Measure.count] 0 :=
    (lintegral_eq_zero_iff (Measurable.of_discrete (f := fun n : ℤ => ‖u n‖ₑ ^ q))).mp h
  have hae : (fun n : ℤ => ‖u n‖ₑ) =ᵐ[Measure.count] 0 := by
    filter_upwards [h3] with n hn
    simpa using (ENNReal.rpow_eq_zero_iff_of_pos hq).mp hn
  rw [lintegral_congr_ae (g := fun _ : ℤ => (0 : ℝ≥0∞)) ?_]
  · simp
  · filter_upwards [hae] with n hn
    have hn' : ‖u n‖ₑ = 0 := by simpa using hn
    have hfin : ‖u n‖ₑ ^ p = (0 : ℝ≥0∞) := by rw [hn', ENNReal.zero_rpow_of_pos hp]
    simpa using hfin

/-- **Endpoint extraction.**  A `∫⁻`-bound at the exponent `q` for `opArc φ hφ E`, valid for all
`ℓ²`-sequences, gives the `eLpNorm`-bound at the exponent `q` for the linear map `opArcLM φ hφ E`
on finitely supported sequences. -/
theorem eLpNorm_opArcLM_le_of_lintegral {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (φ : AddCircle (1 : ℝ) → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (E : Finset (AddCircle (1 : ℝ)))
    (hint : ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
      ∫⁻ n : ℤ, ‖opArc φ hφ E f hf n‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ q ∂Measure.count) :
    ∀ g : ℤ →₀ ℂ, eLpNorm (opArcLM φ hφ E g) (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal M * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal q) Measure.count := by
  intro g
  have hLM : opArcLM φ hφ E g = opArc φ hφ E (g : ℤ → ℂ) (memℓp_finsupp g) := by
    funext n; rw [opArcLM_apply]
  rw [hLM]
  have h := hint (g : ℤ → ℂ) (memℓp_finsupp g)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hq.le]
  calc (∫⁻ n : ℤ, ‖opArc φ hφ E (g : ℤ → ℂ) (memℓp_finsupp g) n‖ₑ ^ q ∂Measure.count) ^ (1 / q)
      ≤ (ENNReal.ofReal (M ^ q) * ∫⁻ n : ℤ, ‖(g : ℤ → ℂ) n‖ₑ ^ q ∂Measure.count) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = (ENNReal.ofReal (M ^ q)) ^ (1 / q)
          * (∫⁻ n : ℤ, ‖(g : ℤ → ℂ) n‖ₑ ^ q ∂Measure.count) ^ (1 / q) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal M * (∫⁻ n : ℤ, ‖(g : ℤ → ℂ) n‖ₑ ^ q ∂Measure.count) ^ (1 / q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hM q) (by positivity),
          ← Real.rpow_mul hM q (1 / q), mul_one_div_cancel (ne_of_gt hq), Real.rpow_one]

/-! ## The duality step for finitely supported sequences -/

/-- **Operator duality on finitely supported sequences.**  If `Tstar` is the transpose of `T` for
the hermitian pairing `⟨u, v⟩ = Σ_n u n * star (v n)` (equation `hpair`) and `Tstar` satisfies the
`ℓ^q`-bound with constant `M`, then `T` satisfies the `ℓ^p`-bound with the same constant, for `p`
Hölder conjugate to `q`. -/
theorem eLpNorm_dual_of_pairing {p q : ℝ} (hpq : Real.HolderConjugate p q) {M : ℝ} (hM : 0 ≤ M)
    (T Tstar : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (hpair : ∀ f g : ℤ →₀ ℂ, ∑' n : ℤ, (g : ℤ → ℂ) n * star (T f n)
        = ∑' n : ℤ, (Tstar g) n * star ((f : ℤ → ℂ) n))
    (hTstar : ∀ g : ℤ →₀ ℂ, eLpNorm (Tstar g) (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal M * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal q) Measure.count) :
    ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal M * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  intro f
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set Sf : ℝ := (∑ n ∈ f.support, ‖(f : ℤ → ℂ) n‖ ^ p) ^ (1 / p) with hSfdef
  have hSfnn : 0 ≤ Sf := by
    rw [hSfdef]
    exact Real.rpow_nonneg (Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)) _
  have hf_eLp : eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count = ENNReal.ofReal Sf := by
    rw [hSfdef]
    exact eLpNorm_count_eq_ofReal_sum (f := (f : ℤ → ℂ)) (W := f.support)
      (fun n hn => Finsupp.notMem_support_iff.mp hn) hp0
  refine le_trans (eLpNorm_le_of_pairing_bound hpq (h := T f) (c := M * Sf)
    (mul_nonneg hM hSfnn) ?_) ?_
  · intro g
    have hsumL : ∑ n ∈ g.support, (g : ℤ → ℂ) n * star (T f n)
        = ∑' n : ℤ, (g : ℤ → ℂ) n * star (T f n) :=
      (tsum_eq_sum (s := g.support) (fun n hn => by
        rw [Finsupp.notMem_support_iff.mp hn, zero_mul])).symm
    have hsumR : ∑ n ∈ f.support, (Tstar g) n * star ((f : ℤ → ℂ) n)
        = ∑' n : ℤ, (Tstar g) n * star ((f : ℤ → ℂ) n) :=
      (tsum_eq_sum (s := f.support) (fun n hn => by
        rw [Finsupp.notMem_support_iff.mp hn, star_zero, mul_zero])).symm
    rw [hsumL, hpair f g, ← hsumR]
    have hH1 : ‖∑ n ∈ f.support, (Tstar g) n * star ((f : ℤ → ℂ) n)‖
        ≤ ∑ n ∈ f.support, ‖(f : ℤ → ℂ) n‖ * ‖(Tstar g) n‖ := by
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun n _ => by rw [norm_mul, norm_star, mul_comm])
    have hH2 : ∑ n ∈ f.support, ‖(f : ℤ → ℂ) n‖ * ‖(Tstar g) n‖
        ≤ Sf * (∑ n ∈ f.support, ‖(Tstar g) n‖ ^ q) ^ (1 / q) := by
      rw [hSfdef]
      exact Real.inner_le_Lp_mul_Lq_of_nonneg (s := f.support) (f := fun n => ‖(f : ℤ → ℂ) n‖)
        (g := fun n => ‖(Tstar g) n‖) hpq (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
    have hH3 : (∑ n ∈ f.support, ‖(Tstar g) n‖ ^ q) ^ (1 / q)
        ≤ M * (∑ n ∈ g.support, ‖(g : ℤ → ℂ) n‖ ^ q) ^ (1 / q) := by
      have h2 : ENNReal.ofReal ((∑ n ∈ f.support, ‖(Tstar g) n‖ ^ q) ^ (1 / q))
          ≤ ENNReal.ofReal (M * (∑ n ∈ g.support, ‖(g : ℤ → ℂ) n‖ ^ q) ^ (1 / q)) := by
        refine le_trans (ofReal_sum_le_eLpNorm_count (Tstar g) hq0 f.support) ?_
        refine le_trans (hTstar g) ?_
        rw [eLpNorm_count_eq_ofReal_sum (f := (g : ℤ → ℂ)) (W := g.support)
              (fun n hn => Finsupp.notMem_support_iff.mp hn) hq0,
            ← ENNReal.ofReal_mul hM]
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM
        (Real.rpow_nonneg (Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) q)) _))).mp h2
    calc ‖∑ n ∈ f.support, (Tstar g) n * star ((f : ℤ → ℂ) n)‖
        ≤ ∑ n ∈ f.support, ‖(f : ℤ → ℂ) n‖ * ‖(Tstar g) n‖ := hH1
      _ ≤ Sf * (∑ n ∈ f.support, ‖(Tstar g) n‖ ^ q) ^ (1 / q) := hH2
      _ ≤ Sf * (M * (∑ n ∈ g.support, ‖(g : ℤ → ℂ) n‖ ^ q) ^ (1 / q)) :=
          mul_le_mul_of_nonneg_left hH3 hSfnn
      _ = (M * Sf) * (∑ n ∈ g.support, ‖(g : ℤ → ℂ) n‖ ^ q) ^ (1 / q) := by ring
  · rw [hf_eLp, ← ENNReal.ofReal_mul hM]

/-! ## The main theorem -/

/-- The KMSZ §3.1 reduction "by duality and interpolation it suffices to prove `p = 2r`", in the
form needed by the `KPWW` chapter: the endpoint case `Thm19At2r` (the Ionescu–Wainger bound at the
single exponent `2r`, for every `r ≥ 1`) implies the full range `p ∈ [(2r)', 2r]` of `Thm19`.

Route.  The operator `opArc φ hφ E` is the ℓ²-multiplier with symbol `Σ_{β ∈ E} φ(· - β)`, whose
adjoint (for the hermitian pairing `Σ_n u n * star (v n)` on `ℤ`, via Plancherel) is
`opArc (star ∘ φ) hψ E` (`star = conj` on `ℂ`): the symbol of the adjoint is the conjugate of the
symbol.  Consequently the bound of `Thm19At2r` applied to the *conjugate* bump `star ∘ φ` gives the
`ℓ^{(2r)'}` bound for `opArc φ hφ E` with the same constant, and the bound of `Thm19At2r` itself
gives the `ℓ^{2r}` bound.  Riesz–Thorin on `ℤ` with the counting measure
(`Submission.Work.BourgainPlan.Maximal.ellp_interpolation`, for linear maps on finitely supported
sequences) then gives the `ℓ^p` bound for every `p` between `(2r)'` and `2r`, with the constant
`K^{1-θ} K^{θ} = K` because both endpoint constants coincide; the passage from finitely supported
sequences to all `f` with `Memℓp f 2` is by truncation when `f ∈ ℓ^p`, and is trivial (the
right-hand side infinite) when `f ∉ ℓ^p`.  The one degenerate case is `A = 0`, where the hypothesis
forces the multiplier to vanish; it is handled by the non-degeneracy of the Fourier transform (a
non-zero `φ` on a ball of positive radius gives a non-zero periodisation). -/
theorem thm19_of_thm19At2r (h : Work.BourgainPlan.KPWW.Thm19At2r) :
    Work.BourgainPlan.KPWW.Thm19 := by
  intro r hr
  obtain ⟨C, hCpos, hbdd⟩ := h r hr
  refine ⟨C, hCpos, ?_⟩
  intro p hp_lo hp_hi N hN ε hεpos hεle φ hφ hsupp A hA hAc hAc' f hf
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set q : ℝ := 2 * (r : ℝ) with hqdef
  have hq2 : 2 ≤ q := by rw [hqdef]; linarith
  have hqpos : 0 < q := by linarith
  have h1q : 1 < q := by linarith
  set M : ℝ := C * (N : ℝ) ^ (C / Real.log (Real.log (N : ℝ))) * A with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hA
  set ψ : AddCircle (1 : ℝ) → ℂ := star φ with hψdef
  have hψapply : ∀ ξ : AddCircle (1 : ℝ), ψ ξ = star (φ ξ) := by
    intro ξ; rw [hψdef]; exact Pi.star_apply φ ξ
  have hψmem : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)) := by
    rw [hψdef]; exact hφ.star
  have hsuppψ : ∀ ξ : AddCircle (1 : ℝ), ε < ‖ξ‖ → ψ ξ = 0 := by
    intro ξ hξ; rw [hψapply ξ, hsupp ξ hξ, star_zero]
  have hAcψ : ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (ψ (ξ : AddCircle (1 : ℝ)) : ℂ) * FourierTransform.fourier g ξ) x‖ₑ ^ q
          ∂volume
        ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q ∂volume := by
    intro g hg
    have hfg : (fun ξ : ℝ => (ψ (ξ : AddCircle (1 : ℝ)) : ℂ) * FourierTransform.fourier g ξ)
        = (fun ξ : ℝ => (star (φ (ξ : AddCircle (1 : ℝ))) : ℂ)
            * FourierTransform.fourier g ξ) := by
      funext ξ; rw [hψapply (ξ : AddCircle (1 : ℝ))]
    rw [hfg]
    exact hAc' g hg
  have hAcψ' : ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (star (ψ (ξ : AddCircle (1 : ℝ))) : ℂ)
            * FourierTransform.fourier g ξ) x‖ₑ ^ q ∂volume
        ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q ∂volume := by
    intro g hg
    have hfg : (fun ξ : ℝ => (star (ψ (ξ : AddCircle (1 : ℝ))) : ℂ)
          * FourierTransform.fourier g ξ)
        = (fun ξ : ℝ => (φ (ξ : AddCircle (1 : ℝ)) : ℂ) * FourierTransform.fourier g ξ) := by
      funext ξ; rw [hψapply (ξ : AddCircle (1 : ℝ))]; simp
    rw [hfg]
    exact hAc g hg
  have hintφ : ∀ (u : ℤ → ℂ) (hu : Memℓp u 2),
      ∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset N) u hu n‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ n : ℤ, ‖u n‖ₑ ^ q ∂Measure.count := by
    intro u hu
    have hb := hbdd N hN ε hεpos hεle φ hφ hsupp A hA hAc hAc' u hu
    rw [← hMdef] at hb
    exact hb
  have hintψ : ∀ (u : ℤ → ℂ) (hu : Memℓp u 2),
      ∫⁻ n : ℤ, ‖opArc ψ hψmem (canonicalFinset N) u hu n‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ n : ℤ, ‖u n‖ₑ ^ q ∂Measure.count := by
    intro u hu
    have hb := hbdd N hN ε hεpos hεle ψ hψmem hsuppψ A hA hAcψ hAcψ' u hu
    rw [← hMdef] at hb
    exact hb
  have hend_q := eLpNorm_opArcLM_le_of_lintegral hqpos hMnn φ hφ (canonicalFinset N) hintφ
  have hend_q_psi := eLpNorm_opArcLM_le_of_lintegral hqpos hMnn ψ hψmem (canonicalFinset N) hintψ
  have hpq_conj : Real.HolderConjugate q (q / (q - 1)) := by
    have hh := Real.HolderConjugate.conjExponent h1q
    simpa [Real.conjExponent] using hh
  have hpair : ∀ u v : ℤ →₀ ℂ,
      ∑' n : ℤ, (v : ℤ → ℂ) n * star (opArcLM φ hφ (canonicalFinset N) u n)
        = ∑' n : ℤ, (opArcLM ψ hψmem (canonicalFinset N) v n) * star ((u : ℤ → ℂ) n) :=
    fun u v => opArcLM_pairing (φ := φ) (ψ := ψ) hφ hψmem hψapply (canonicalFinset N) u v
  have hq'_end : ∀ g : ℤ →₀ ℂ,
      eLpNorm (opArcLM φ hφ (canonicalFinset N) g) (ENNReal.ofReal (q / (q - 1)))
          Measure.count
        ≤ ENNReal.ofReal M * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (q / (q - 1)))
            Measure.count :=
    eLpNorm_dual_of_pairing (p := q / (q - 1)) (q := q) hpq_conj.symm hMnn
      (opArcLM φ hφ (canonicalFinset N)) (opArcLM ψ hψmem (canonicalFinset N)) hpair hend_q_psi
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
  · -- the non-degenerate case `M > 0`: duality + Riesz–Thorin
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
      (opArcLM φ hφ (canonicalFinset N)) hq'_end hend_q
    have hfin : ∀ g : ℤ →₀ ℂ,
        eLpNorm (opArcLM φ hφ (canonicalFinset N) g) (ENNReal.ofReal p) Measure.count
          ≤ ENNReal.ofReal M * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      intro g
      have hh := hinterp g
      rwa [hMpow] at hh
    have hext := eLpNorm_opArc_le_of_finsupp hp0 hMnn φ hφ (canonicalFinset N) hfin f hf
    have hlin : (eLpNorm (opArc φ hφ (canonicalFinset N) f hf) (ENNReal.ofReal p)
          Measure.count) ^ p
        = ∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset N) f hf n‖ₑ ^ p ∂Measure.count := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
          ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul,
        show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
    have hlin' : (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p
        = ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
          ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul,
        show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
    have hmain : ∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset N) f hf n‖ₑ ^ p ∂Measure.count
        ≤ ENNReal.ofReal (M ^ p) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
      calc ∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset N) f hf n‖ₑ ^ p ∂Measure.count
          = (eLpNorm (opArc φ hφ (canonicalFinset N) f hf) (ENNReal.ofReal p)
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
  · -- the degenerate case `A = 0`: the hypothesis forces the multiplier to vanish
    have hb := hbdd N hN ε hεpos hεle φ hφ hsupp A hA hAc hAc' f hf
    rw [← hMdef, ← hMzero] at hb
    have hzq : ∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset N) f hf n‖ₑ ^ q ∂Measure.count = 0 := by
      have h0 : ENNReal.ofReal ((0 : ℝ) ^ q) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ q ∂Measure.count = 0 := by
        rw [Real.zero_rpow (ne_of_gt hqpos)]; simp
      rw [h0] at hb
      exact le_antisymm hb zero_le
    rw [lintegral_enorm_rpow_eq_zero_of_eq_zero hqpos hp0 hzq]
    exact zero_le

end

end Work.BourgainPlan.KPWW
