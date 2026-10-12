import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.chiScale_kinFT_tail
import Submission.Work.BoseBoxFock.FRK.conv_restricted_le
import Submission.Work.BoseBoxFock.FRK.kinFT_conv_mul
import Submission.Work.BoseBoxFock.FRK.kinFT_mul_conv
import Submission.Work.BoseBoxFock.FRK.smearK_integrable
import Submission.Work.BoseBoxFock.FRK.smearK_kinFT
import Submission.Work.BoseBoxFock.FRK.smeared_mem
import Submission.Work.BoseBoxFock.FRK.winChi_facts
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseFixB3.HighMassAux.parseval_L1L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# `Work.BoseBoxFock.FRK.windowHigh_le` — the windowed high-momentum split (S1)

This is the S1 leaf of the FRK design (`LEAD_DESIGN_formrowkin_v2.md` §1): the high-momentum part
of the windowed mean-free state `winState ℓ ψ = χ_Λ(ψ − ⨍ψ)` is dominated by the high-momentum
form `momForm` plus a small multiple of the bare mean-free mass `gapBare`.

## The proof in outline

Write `u := 1_{Λ}(Qψ)` (the mean-free state localised in the box), `χ := χ_Λ`, `g := χ·u`, so that
`winState ℓ ψ = χ·u`.  Fix the frequency cut `φ := freqCut κ₀` with `κ₀ = (d²ℓ)⁻¹ ≤ κ` (so `φ ≡ 1`
on the ball of radius `κ₀`, and `φ` is supported in the ball of radius `5κ₀/4 ≤ 5κ/4`, at distance
`≥ κ/4` from the high set `{3κ/2 ≤ ‖p‖}`), and let `K` be its inverse Fourier transform
(`smearK κ₀`).

* **Product ⟹ convolution** (`kinFT_mul_conv`): `kinFT g = (2π)⁻³ (Chin * û)`, where
  `Chin = kinFT χ`, `û = kinFT u`.
* **Splitting** `û = φ·û + (1−φ)·û`: the second summand is `kinFT w` for the *genuine* function
  `w := u − K * u` (`kinFT_conv_mul`, `smearK_kinFT`), so no Fourier inversion of `u` is needed.
* **High part**: `‖Chin * kinFT w‖ = (2π)^{9/2}‖χ·w‖ ≤ (2π)^{9/2}·sup|χ|·‖w‖`, using Plancherel
  on the position-space product; and `‖w‖² = (2π)⁻³∫‖(1−φ)û‖² ≤ momForm`.
* **Low part**: `conv_restricted_le` gives `‖1_T(Chin * (φ·û))‖ ≤ ε‖φ·û‖` with
  `ε = ∫_{‖s‖≥κ/4}‖Chin s‖ds ≤ C d⁶` (`chiScale_kinFT_tail`, using `ℓκ ≥ d⁻²`).
* The constants: `(5/4)·sup|χ|² ≤ (5/4)(48/π) ≤ 23` (`chi_sq_bounds`).
-/
noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- (S1) windowed high-momentum split. -/
theorem windowHigh_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 →
    (d ^ 2 * ℓ)⁻¹ ≤ κ → ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        (if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0)
          * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2
      ≤ 23 * Work.BoseKinLoc.momForm ℓ d 0 ψ
        + K * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  -- TODO(child `chiScale_kinFT_tail`): the tail bound on the cutoff
  have htail : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ R : ℝ}, 0 < ℓ → 0 ≤ R →
      ∫ q in {q : E3 | R ≤ ‖q‖}, ‖Submission.BoseGases.kinFT
          (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) q‖
        ≤ C * (1 + ℓ * R) ^ (-3 : ℤ) := chiScale_kinFT_tail
  -- TODO(child `conv_restricted_le`, now proved in `FRK/conv_restricted_le.lean`)
  have hCR : ∀ {k μ' : E3 → ℂ} {R gp : ℝ}, 0 ≤ gp → Integrable k →
      Integrable (fun p : E3 => ‖μ' p‖ ^ 2) → (∀ p : E3, μ' p ≠ 0 → ‖p‖ ≤ R) →
      (∫ p : E3, (if R + gp ≤ ‖p‖ then (1 : ℝ) else 0) *
          ‖∫ s : E3, k s * μ' (p - s)‖ ^ 2)
        ≤ (∫ s : E3, (if gp ≤ ‖s‖ then (1 : ℝ) else 0) * ‖k s‖) ^ 2 *
            (∫ p : E3, ‖μ' p‖ ^ 2) :=
    fun hgp hk hμ hsupp => conv_restricted_le hgp hk hμ hsupp
  obtain ⟨Cε, hCε0, hCε⟩ := htail
  refine ⟨5 * (((2 * Real.pi) ^ 3 : ℝ)⁻¹) ^ 2 * (64 * Cε) ^ 2, by positivity, ?_⟩
  intro ℓ d κ hℓ hd hd1 hκ ψ hψ
  set k0 : ℝ := (d ^ 2 * ℓ)⁻¹ with hk0def
  have hk0pos : 0 < k0 := by rw [hk0def]; positivity
  have hk0le : k0 ≤ κ := by rw [hk0def]; exact hκ
  -- ## the state, the cutoff and the smoothing kernel
  set χc : E3 → ℂ := winChi ℓ with hχcdef
  set u : E3 → ℂ := winU ℓ ψ with hudef
  set φ : E3 → ℝ := freqCut k0 with hφdef
  set Kc : E3 → ℂ := fun x : E3 => ((smearK k0 x : ℝ) : ℂ) with hKcdef
  set wax : E3 → ℂ := fun z : E3 => ∫ y : E3, Kc y * u (z - y) with hwaxdef
  set w : E3 → ℂ := fun z : E3 => u z - wax z with hwdef
  -- ## elementary facts
  have hg : Work.BoseBoxFock.winState ℓ ψ = fun z => χc z * u z := by
    rw [hχcdef, hudef]; exact winState_eq_winChi_mul_winU hℓ ψ
  -- TODO(child `winChi_facts`)
  have hχfacts : Continuous (winChi ℓ) ∧ HasCompactSupport (winChi ℓ)
      ∧ Integrable (Submission.BoseGases.kinFT (winChi ℓ))
      ∧ (∀ z : E3, winChi ℓ z = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) *
          ∫ s : E3, Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ)) *
            Submission.BoseGases.kinFT (winChi ℓ) s) := winChi_facts hℓ
  obtain ⟨hχcont, hχcs, hχint, hinvχ⟩ := hχfacts
  have hχdiff : ContDiff ℝ (⊤ : ℕ∞) χc := by
    rw [hχcdef]; exact contDiff_winChi (ne_of_gt hℓ)
  -- TODO(children `smearK_integrable`, `smearK_kinFT`)
  have hsmearK_int : Integrable (fun x : E3 => ((smearK k0 x : ℝ) : ℂ)) :=
    smearK_integrable hk0pos
  have hsmearK_kinFT :
      Submission.BoseGases.kinFT (fun x : E3 => ((smearK k0 x : ℝ) : ℂ))
        = fun p : E3 => ((freqCut k0 p : ℝ) : ℂ) := smearK_kinFT hk0pos
  have hKc_int : Integrable Kc := by rw [hKcdef]; exact hsmearK_int
  have hKc_eq : ∀ p : E3, Submission.BoseGases.kinFT Kc p = (φ p : ℂ) := by
    intro p; rw [hKcdef, hφdef]
    exact congrFun hsmearK_kinFT p
  have hKc_bd : ∀ y : E3, ‖Kc y‖ ≤ ((2 * Real.pi) ^ 3 : ℝ)⁻¹ * (∫ p : E3, freqCut k0 p) := by
    intro y
    have hcs : HasCompactSupport (fun p : E3 => freqCut k0 p * Real.cos (inner ℝ p y)) :=
      (freqCut_hasCompactSupport (ne_of_gt hk0pos)).mul_right
    have hcont : Continuous (fun p : E3 => freqCut k0 p * Real.cos (inner ℝ p y)) :=
      (freqCut_contDiff (ne_of_gt hk0pos)).continuous.mul
        (Real.continuous_cos.comp (by fun_prop))
    have hint : Integrable (fun p : E3 => freqCut k0 p * Real.cos (inner ℝ p y)) :=
      hcont.integrable_of_hasCompactSupport hcs
    have hint2 : Integrable (fun p : E3 => freqCut k0 p) :=
      (freqCut_contDiff (ne_of_gt hk0pos)).continuous.integrable_of_hasCompactSupport
        (freqCut_hasCompactSupport (ne_of_gt hk0pos))
    have hle : ∫ p : E3, ‖freqCut k0 p * Real.cos (inner ℝ p y)‖ ≤ ∫ p : E3, freqCut k0 p := by
      refine integral_mono hint.norm hint2 (fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (freqCut_nonneg k0 p)]
      exact mul_le_of_le_one_right (freqCut_nonneg k0 p) (Real.abs_cos_le_one _)
    have hval : ‖Kc y‖ = |((2 * Real.pi) ^ 3 : ℝ)⁻¹ *
        ∫ p : E3, freqCut k0 p * Real.cos (inner ℝ p y)| := by
      rw [hKcdef]
      simp only [smearK]
      rw [norm_ofReal_complex]
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * Real.pi) ^ 3 : ℝ)⁻¹)]
    calc ((2 * Real.pi) ^ 3 : ℝ)⁻¹ *
            |∫ p : E3, freqCut k0 p * Real.cos (inner ℝ p y)|
        ≤ ((2 * Real.pi) ^ 3 : ℝ)⁻¹ * ∫ p : E3, ‖freqCut k0 p * Real.cos (inner ℝ p y)‖ :=
          mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
      _ ≤ ((2 * Real.pi) ^ 3 : ℝ)⁻¹ * ∫ p : E3, freqCut k0 p :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((2 * Real.pi) ^ 3 : ℝ)⁻¹ * (∫ p : E3, freqCut k0 p) := rfl
  have hu_int : Integrable u := by rw [hudef]; exact integrable_winU hℓ hψ
  have hu_sq : Integrable (fun z : E3 => ‖u z‖ ^ 2) := by
    rw [hudef]; exact integrable_winU_sq hℓ hψ
  have hKc_eq_wax : wax = fun z : E3 => ∫ y : E3, Kc y * u (z - y) := rfl
  -- TODO(child `smeared_mem`)
  have hsmeared : Integrable (fun z : E3 => ∫ y : E3, Kc y * u (z - y))
      ∧ Integrable (fun z : E3 => ‖∫ y : E3, Kc y * u (z - y)‖ ^ 2) :=
    smeared_mem hKc_int hKc_bd hu_int hu_sq
  obtain ⟨hwax_int, hwax_sq⟩ := hsmeared
  have hw_int : Integrable w := by
    rw [hwdef]; exact hu_int.sub hwax_int
  have hw_sq : Integrable (fun z : E3 => ‖w z‖ ^ 2) := by
    rw [hwdef]
    have hb : Integrable (fun z : E3 => 2 * ‖u z‖ ^ 2 + 2 * ‖wax z‖ ^ 2) :=
      (hu_sq.const_mul 2).add (hwax_sq.const_mul 2)
    have hm : AEMeasurable (fun z : E3 => ‖u z - wax z‖ ^ 2) volume :=
      ((hu_int.aemeasurable.sub hwax_int.aemeasurable).norm.pow_const 2)
    refine Integrable.mono' hb hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    change ‖(‖u z - wax z‖ ^ 2 : ℝ)‖ ≤ 2 * ‖u z‖ ^ 2 + 2 * ‖wax z‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h2 : ‖u z - wax z‖ ≤ ‖u z‖ + ‖wax z‖ := norm_sub_le _ _
    have h3 : ‖u z - wax z‖ ^ 2 ≤ (‖u z‖ + ‖wax z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : (‖u z‖ + ‖wax z‖) ^ 2 ≤ 2 * ‖u z‖ ^ 2 + 2 * ‖wax z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖u z‖ - ‖wax z‖)]
    linarith
  -- TODO(children `kinFT_conv_mul`, `kinFT_mul_conv`)
  have hConvmul : ∀ {K uu : E3 → ℂ}, Integrable K → Integrable uu → ∀ p : E3,
      Submission.BoseGases.kinFT (fun z : E3 => ∫ y : E3, K y * uu (z - y)) p
        = Submission.BoseGases.kinFT K p * Submission.BoseGases.kinFT uu p := by
    intro K uu hK hu p; exact kinFT_conv_mul hK hu p
  have hMulconv : ∀ {χ ww : E3 → ℂ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      Integrable (Submission.BoseGases.kinFT χ) →
      (∀ z : E3, χ z = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) *
        ∫ s : E3, Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ)) *
          Submission.BoseGases.kinFT χ s) →
      Integrable ww → ∀ p : E3,
      Submission.BoseGases.kinFT (fun z : E3 => χ z * ww z) p
        = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * ∫ s : E3,
            Submission.BoseGases.kinFT χ s * Submission.BoseGases.kinFT ww (p - s) := by
    intro χ ww h1 h2 h3 h4 hw p; exact kinFT_mul_conv h1 h2 h3 h4 hw p
  -- ## the frequency cutoff decomposition of `kinFT u`
  have hkin_conv : ∀ p : E3, Submission.BoseGases.kinFT wax p
      = (φ p : ℂ) * Submission.BoseGases.kinFT u p := by
    intro p
    rw [← hKc_eq p]
    exact hConvmul hKc_int hu_int p
  set μ : E3 → ℂ := fun q : E3 => (φ q : ℂ) * Submission.BoseGases.kinFT u q with hμdef
  have hkin_u : ∀ p : E3, Submission.BoseGases.kinFT u p
      = μ p + Submission.BoseGases.kinFT w p := by
    intro p
    have h1 : Submission.BoseGases.kinFT u p
        = Submission.BoseGases.kinFT wax p + Submission.BoseGases.kinFT w p := by
      have hw : u = wax - (-1 : ℂ) • w := by
        funext z
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef]
        ring
      calc Submission.BoseGases.kinFT u p
          = Submission.BoseGases.kinFT (wax - (-1 : ℂ) • w) p := by rw [← hw]
        _ = Submission.BoseGases.kinFT wax p + Submission.BoseGases.kinFT w p := by
              rw [Work.OneBodyKin.kinFT_sub_smul hwax_int hw_int (-1) p]
              ring
    rw [h1, hkin_conv p, hμdef]
  have hμ_sq : Integrable (fun q : E3 => ‖μ q‖ ^ 2) := by
    have hmem : MemLp (Submission.BoseGases.kinFT u) 2 volume :=
      Work.BoseKinLoc.Momentum.memLp_kinFT hu_int
        ((memLp_two_iff_integrable_sq_norm hu_int.aestronglyMeasurable).mpr hu_sq)
    have hbase : Integrable (fun q : E3 => ‖Submission.BoseGases.kinFT u q‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    have hm : AEMeasurable (fun q : E3 =>
        ‖((φ q : ℝ) : ℂ) * Submission.BoseGases.kinFT u q‖ ^ 2) volume :=
      ((Complex.continuous_ofReal.measurable.comp
          (freqCut_contDiff (ne_of_gt hk0pos)).continuous.measurable).aemeasurable.mul
        hmem.aemeasurable).norm.pow_const 2
    refine Integrable.mono' hbase hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    change ‖(‖((φ q : ℝ) : ℂ) * Submission.BoseGases.kinFT u q‖ ^ 2 : ℝ)‖ ≤
      ‖Submission.BoseGases.kinFT u q‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have h1 : ‖((φ q : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_ofReal_complex, abs_of_nonneg (by rw [hφdef]; exact freqCut_nonneg k0 q)]
      rw [hφdef]; exact freqCut_le_one k0 q
    have h2 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT u q‖ ^ 2 := sq_nonneg _
    have h1b : ‖((φ q : ℝ) : ℂ)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg ((φ q : ℝ) : ℂ), h1]
    nlinarith [h1b, h2]
  set CA : E3 → ℂ := fun p : E3 =>
    ∫ s : E3, Submission.BoseGases.kinFT χc s * μ (p - s) with hCAdef
  set CB : E3 → ℂ := fun p : E3 =>
    ∫ s : E3, Submission.BoseGases.kinFT χc s * Submission.BoseGases.kinFT w (p - s) with hCBdef
  have hKCu : ∀ p : E3, Submission.BoseGases.kinFT (fun z => χc z * u z) p
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ * (CA p + CB p) := by
    intro p
    have hw : (fun z : E3 => χc z * u z)
        = (fun z : E3 => χc z * wax z) - (-1 : ℂ) • (fun z : E3 => χc z * w z) := by
      funext z
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef]
      ring
    rw [hw, Work.OneBodyKin.kinFT_sub_smul (integrable_winChi_mul hwax_int)
      (integrable_winChi_mul hw_int) (-1) p]
    rw [hMulconv hχdiff hχcs hχint hinvχ hwax_int p,
      hMulconv hχdiff hχcs hχint hinvχ hw_int p]
    have hCAp : (∫ s : E3, Submission.BoseGases.kinFT χc s *
          Submission.BoseGases.kinFT wax (p - s)) = CA p := by
      rw [hCAdef]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show Submission.BoseGases.kinFT χc s * Submission.BoseGases.kinFT wax (p - s)
        = Submission.BoseGases.kinFT χc s * μ (p - s)
      rw [hkin_conv (p - s), hμdef]
    rw [hCAp]
    simp only [hCBdef]
    push_cast
    ring

  -- ## the high-momentum set
  set T : Set E3 := {p : E3 | 3 * κ / 2 ≤ ‖p‖} with hTdef
  have hTmeas : MeasurableSet T := (isClosed_le continuous_const continuous_norm).measurableSet
  set c3 : ℝ := ((2 * Real.pi) ^ 3 : ℝ)⁻¹ with hc3def
  have hc3pos : 0 < c3 := by rw [hc3def]; positivity
  -- ## the target's integral as a set integral over `T`
  have hLHS : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
        (if 3 * κ / 2 ≤ ‖p‖ then (1 : ℝ) else 0)
          * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2
      = c3 * ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2 := by
    rw [hg, hc3def]
    congr 1
    rw [← integral_indicator hTmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ T
    · have h1 : 3 * κ / 2 ≤ ‖p‖ := hp
      rw [Set.indicator_of_mem hp]; simp [h1]
    · have h1 : ¬ (3 * κ / 2 ≤ ‖p‖) := hp
      rw [Set.indicator_of_notMem hp]; simp [h1]
  rw [hLHS]
  -- ## the constant `c3 = ((2π)³)⁻¹`, in the two spellings
  have hc3inv : (c3 : ℂ) = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ := by
    rw [hc3def, Complex.ofReal_inv]
  have hc3mul : c3 * ((2 * Real.pi) ^ 3) = 1 := by
    rw [hc3def, inv_mul_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0)]
  -- ## the two pieces of `kinFT (χ_Λ · u)`
  have hCA_int : ∀ p : E3, CA p = ∫ s : E3, Submission.BoseGases.kinFT χc s *
      Submission.BoseGases.kinFT wax (p - s) := by
    intro p
    rw [hCAdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Submission.BoseGases.kinFT χc s * μ (p - s)
      = Submission.BoseGases.kinFT χc s * Submission.BoseGases.kinFT wax (p - s)
    rw [hkin_conv (p - s)]
  have hCA_kinFT : ∀ p : E3, Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p
      = (c3 : ℂ) * CA p := by
    intro p
    have h2 := hMulconv hχdiff hχcs hχint hinvχ hwax_int p
    rw [← hCA_int p, ← hc3inv] at h2
    exact h2
  have hCB_kinFT : ∀ p : E3, Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p
      = (c3 : ℂ) * CB p := by
    intro p
    have h2 := hMulconv hχdiff hχcs hχint hinvχ hw_int p
    rw [← hc3inv] at h2
    rw [hCBdef]
    exact h2
  have hsplit_id : ∀ p : E3, Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p
      = Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p
        + Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p := by
    intro p
    rw [hCA_kinFT p, hCB_kinFT p, ← mul_add, hc3inv]
    exact hKCu p
  -- ## integrability of the two squared transforms
  have hχwax_int : Integrable (fun z : E3 => χc z * wax z) := integrable_winChi_mul hwax_int
  have hχw_int : Integrable (fun z : E3 => χc z * w z) := integrable_winChi_mul hw_int
  have hχwax_mem : MemLp (fun z : E3 => χc z * wax z) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hχwax_int.aestronglyMeasurable).mpr
      (integrable_normSq_winChi_mul hwax_sq)
  have hχw_mem : MemLp (fun z : E3 => χc z * w z) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hχw_int.aestronglyMeasurable).mpr
      (integrable_normSq_winChi_mul hw_sq)
  have hmem1 : MemLp (Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z)) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hχwax_int hχwax_mem
  have hmem2 : MemLp (Submission.BoseGases.kinFT (fun z : E3 => χc z * w z)) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hχw_int hχw_mem
  have hE1 : Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem1.aestronglyMeasurable).mp hmem1
  have hE2 : Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem2.aestronglyMeasurable).mp hmem2
  -- ## the asymmetric `(a+b)²` splitting
  have hInt_split : ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2
      ≤ 5 * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p‖ ^ 2)
        + (5 / 4) * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2) := by
    have h1 : ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2
        = ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p
            + Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only []
      rw [hsplit_id p]
    rw [h1]
    exact integral_norm_add_sq_le hTmeas hE1 hE2
  -- ## the far/low bound (the `wax` piece)
  have hff : 5 * κ / 4 + κ / 4 = 3 * κ / 2 := by ring
  have hsupp : ∀ p : E3, μ p ≠ 0 → ‖p‖ ≤ 5 * κ / 4 := by
    intro p hp
    have hp' : φ p ≠ 0 := by
      intro h0
      exact hp (by change (φ p : ℂ) * Submission.BoseGases.kinFT u p = 0
                   rw [h0, Complex.ofReal_zero, zero_mul])
    have h := freqCut_ne_zero_le hk0pos (by rwa [hφdef] at hp')
    linarith [hk0le]
  have hκpos : 0 < κ := lt_of_lt_of_le hk0pos hk0le
  have hCA_bound : ∫ p in T, ‖CA p‖ ^ 2
      ≤ (∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2) := by
    have h1 := hCR (k := Submission.BoseGases.kinFT χc) (μ' := μ) (R := 5 * κ / 4) (gp := κ / 4)
      (by positivity) hχint hμ_sq hsupp
    have h2 : ∫ p in T, ‖CA p‖ ^ 2 = ∫ p : E3,
        (if 5 * κ / 4 + κ / 4 ≤ ‖p‖ then (1 : ℝ) else 0) *
          ‖∫ s : E3, Submission.BoseGases.kinFT χc s * μ (p - s)‖ ^ 2 := by
      rw [← integral_indicator hTmeas, hff]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only []
      by_cases hp : 3 * κ / 2 ≤ ‖p‖
      · rw [Set.indicator_of_mem (show p ∈ T from hp), if_pos hp, one_mul]
      · rw [Set.indicator_of_notMem (show p ∉ T from hp), if_neg hp, zero_mul]
    rw [h2]
    exact h1
  have hE1_le : ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p‖ ^ 2
      ≤ (c3) ^ 2 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)) := by
    have h1 : ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p‖ ^ 2
        = (c3) ^ 2 * ∫ p in T, ‖CA p‖ ^ 2 := by
      rw [show (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p‖ ^ 2)
          = ∫ p in T, ‖(c3 : ℂ) * CA p‖ ^ 2 from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only []
        rw [hCA_kinFT p]]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only []
      rw [norm_mul_ofReal_sq (le_of_lt hc3pos)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hCA_bound (sq_nonneg _)
  -- ## the far/high bound (the `w` piece)
  have hE2_le : ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2
      ≤ ((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2 := by
    have h1 : ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2
        ≤ ∫ p : E3, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2 := by
      rw [← integral_indicator hTmeas]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_) hE2
        (Filter.Eventually.of_forall fun p => ?_)
      · change (0 : ℝ) ≤ T.indicator
          (fun p : E3 => ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2) p
        by_cases hp : p ∈ T
        · rw [Set.indicator_of_mem hp]
          exact sq_nonneg _
        · rw [Set.indicator_of_notMem hp]
      · change T.indicator
          (fun p : E3 => ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2) p
          ≤ ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2
        by_cases hp : p ∈ T
        · rw [Set.indicator_of_mem hp]
        · rw [Set.indicator_of_notMem hp]
          exact sq_nonneg _
    refine le_trans h1 ?_
    exact le_of_eq (Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hχw_int hχw_mem)
  -- ## the tail bound on the cutoff
  have hε : (∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
        ‖Submission.BoseGases.kinFT χc s‖) ≤ 64 * Cε * d ^ 6 := by
    have hT4 : MeasurableSet {s : E3 | κ / 4 ≤ ‖s‖} :=
      (isClosed_le continuous_const continuous_norm).measurableSet
    have h1 : (∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
          ‖Submission.BoseGases.kinFT χc s‖)
        = ∫ s in {s : E3 | κ / 4 ≤ ‖s‖}, ‖Submission.BoseGases.kinFT χc s‖ := by
      rw [← integral_indicator hT4]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      change (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) * ‖Submission.BoseGases.kinFT χc s‖
        = {q : E3 | κ / 4 ≤ ‖q‖}.indicator
            (fun q : E3 => ‖Submission.BoseGases.kinFT χc q‖) s
      by_cases hs : κ / 4 ≤ ‖s‖
      · rw [Set.indicator_of_mem (show s ∈ {q : E3 | κ / 4 ≤ ‖q‖} from hs), if_pos hs, one_mul]
      · rw [Set.indicator_of_notMem (show s ∉ {q : E3 | κ / 4 ≤ ‖q‖} from hs), if_neg hs, zero_mul]
    have h2 : (∫ s in {s : E3 | κ / 4 ≤ ‖s‖}, ‖Submission.BoseGases.kinFT χc s‖)
        = ∫ s in {s : E3 | κ / 4 ≤ ‖s‖}, ‖Submission.BoseGases.kinFT
            (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) s‖ := by
      have hχw : (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) = winChi ℓ := rfl
      rw [hχcdef, ← hχw]
    have h3 := hCε hℓ (show (0:ℝ) ≤ κ / 4 by linarith [hκpos])
    rw [h1, h2]
    refine le_trans h3 ?_
    have hz : (1 + ℓ * (κ / 4)) ^ (-3 : ℤ) = ((1 + ℓ * (κ / 4)) ^ 3)⁻¹ := by
      rw [zpow_neg, zpow_ofNat]
    rw [hz]
    have hcore : ((1 + ℓ * (κ / 4)) ^ 3)⁻¹ ≤ 64 * d ^ 6 := by
      have hb1 : (1 : ℝ) / (4 * d ^ 2) ≤ ℓ * (κ / 4) := by
        have h := mul_le_mul_of_nonneg_left hκ hℓ.le
        have h2' : ℓ * (d ^ 2 * ℓ)⁻¹ = (d ^ 2)⁻¹ := by field_simp
        rw [h2'] at h
        have h4 : (1 : ℝ) / (4 * d ^ 2) = (d ^ 2)⁻¹ / 4 := by field_simp
        rw [h4]
        linarith
      have hp1 : (0:ℝ) < (1 : ℝ) / (4 * d ^ 2) := by positivity
      have hp2 : (0:ℝ) < ℓ * (κ / 4) := by positivity
      have e1 : ((ℓ * (κ / 4)) ^ 3)⁻¹ ≤ (((1:ℝ) / (4 * d ^ 2)) ^ 3)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (le_of_lt hp1) hb1 3
      have e2 : ((1 + ℓ * (κ / 4)) ^ 3)⁻¹ ≤ ((ℓ * (κ / 4)) ^ 3)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (le_of_lt hp2) (by linarith) 3
      have e3 : (((1:ℝ) / (4 * d ^ 2)) ^ 3)⁻¹ = 64 * d ^ 6 := by
        rw [one_div, inv_pow, inv_inv]
        ring
      linarith [e1, e2, e3.le, e3.ge]
    nlinarith [hcore, hCε0]
  -- ## the two remaining bounds
  have hmem_u : MemLp (Submission.BoseGases.kinFT u) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hu_int
      ((memLp_two_iff_integrable_sq_norm hu_int.aestronglyMeasurable).mpr hu_sq)
  have hbase_u : Integrable (fun q : E3 => ‖Submission.BoseGases.kinFT u q‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem_u.aestronglyMeasurable).mp hmem_u
  have hμ_le : (∫ q : E3, ‖μ q‖ ^ 2) ≤ ((2 * Real.pi) ^ 3) * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
    have h1 : (∫ q : E3, ‖μ q‖ ^ 2) ≤ ∫ q : E3, ‖Submission.BoseGases.kinFT u q‖ ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => sq_nonneg _) hbase_u
        (Filter.Eventually.of_forall fun q => ?_)
      rw [hμdef]
      change ‖((φ q : ℝ) : ℂ) * Submission.BoseGases.kinFT u q‖ ^ 2
        ≤ ‖Submission.BoseGases.kinFT u q‖ ^ 2
      rw [norm_mul, norm_ofReal_complex, mul_pow]
      have h1' : ‖((φ q : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_ofReal_complex, abs_of_nonneg (by rw [hφdef]; exact freqCut_nonneg k0 q)]
        rw [hφdef]; exact freqCut_le_one k0 q
      have h1a : |φ q| ≤ 1 := by
        rw [norm_ofReal_complex] at h1'
        exact h1'
      have h1'' : |φ q| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (φ q), h1a]
      exact le_trans (mul_le_mul_of_nonneg_right h1''
        (sq_nonneg (‖Submission.BoseGases.kinFT u q‖))) (le_of_eq (one_mul _))
    have h2 : ∫ q : E3, ‖Submission.BoseGases.kinFT u q‖ ^ 2
        = ((2 * Real.pi) ^ 3) * ∫ q : E3, ‖u q‖ ^ 2 :=
      Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hu_int
        ((memLp_two_iff_integrable_sq_norm hu_int.aestronglyMeasurable).mpr hu_sq)
    have h3 : ∫ q : E3, ‖u q‖ ^ 2 = Work.BoseKinLoc.gapBare ℓ 0 ψ := by
      rw [hudef]
      exact (gapBare_eq_integral_winU hℓ ψ).symm
    rw [h3] at h2
    exact le_trans h1 h2.le
  have hχw_le : (∫ z : E3, ‖χc z * w z‖ ^ 2)
      ≤ (48 / Real.pi) * Work.BoseKinLoc.momForm ℓ d 0 ψ := by
    have h1 : (∫ z : E3, ‖χc z * w z‖ ^ 2) ≤ (48 / Real.pi) * ∫ z : E3, ‖w z‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
        (hw_sq.const_mul _) (Filter.Eventually.of_forall fun z => ?_)
      change ‖χc z * w z‖ ^ 2 ≤ (48 / Real.pi) * ‖w z‖ ^ 2
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (winChi_sq_le ℓ z) (sq_nonneg _)
    have h2 : ∫ z : E3, ‖w z‖ ^ 2
        = (((2 * Real.pi) ^ 3 : ℝ)⁻¹) * ∫ p : E3, ‖Submission.BoseGases.kinFT w p‖ ^ 2 := by
      rw [Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hw_int
        ((memLp_two_iff_integrable_sq_norm hw_int.aestronglyMeasurable).mpr hw_sq)]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0), one_mul]
    have h3 : ∫ p : E3, ‖Submission.BoseGases.kinFT w p‖ ^ 2
        = ∫ p : E3, ‖(1 - (φ p : ℂ)) * Submission.BoseGases.kinFT u p‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      change ‖Submission.BoseGases.kinFT w p‖ ^ 2
        = ‖(1 - (φ p : ℂ)) * Submission.BoseGases.kinFT u p‖ ^ 2
      have hsol : Submission.BoseGases.kinFT w p
          = (1 - (φ p : ℂ)) * Submission.BoseGases.kinFT u p := by
        have h' := hkin_u p
        rw [hμdef] at h'
        simp only [] at h'
        linear_combination -h'
      rw [hsol]
    have h4 : ∫ p : E3, ‖(1 - (φ p : ℂ)) * Submission.BoseGases.kinFT u p‖ ^ 2
        ≤ ∫ p : E3, (if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT u p‖ ^ 2 := by
      have hset : MeasurableSet {p : E3 | (d ^ 2 * ℓ)⁻¹ < ‖p‖} :=
        (isOpen_lt continuous_const continuous_norm).measurableSet
      have hind : Integrable (fun p : E3 => (if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0) *
          ‖Submission.BoseGases.kinFT u p‖ ^ 2) := by
        refine (hbase_u.indicator hset).congr (Filter.Eventually.of_forall fun p => ?_)
        simp only [Set.indicator_apply]
        by_cases hp : (d ^ 2 * ℓ)⁻¹ < ‖p‖ <;> simp [hp]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _) hind
        (Filter.Eventually.of_forall fun p => ?_)
      change ‖(1 - (φ p : ℂ)) * Submission.BoseGases.kinFT u p‖ ^ 2
        ≤ (if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0) * ‖Submission.BoseGases.kinFT u p‖ ^ 2
      by_cases hp : (d ^ 2 * ℓ)⁻¹ < ‖p‖
      · rw [if_pos hp, norm_mul, mul_pow]
        have h5 : ‖(1 : ℂ) - (φ p : ℂ)‖ ^ 2 ≤ 1 :=
          norm_one_sub_ofReal_sq_le (by rw [hφdef]; exact freqCut_nonneg k0 p)
            (by rw [hφdef]; exact freqCut_le_one k0 p)
        have h6 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT u p‖ ^ 2 := sq_nonneg _
        nlinarith [h5, h6]
      · rw [if_neg hp]
        have h5 : (φ p : ℂ) = 1 := by
          rw [hφdef]
          have h6 : ‖p‖ ≤ k0 := by rw [hk0def]; exact not_lt.mp hp
          rw [freqCut_eq_one hk0pos h6, Complex.ofReal_one]
        rw [h5, sub_self, zero_mul, norm_zero, zero_pow (by norm_num), zero_mul]
    have h5 : (∫ p : E3, (if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0) *
          ‖Submission.BoseGases.kinFT u p‖ ^ 2)
        = ((2 * Real.pi) ^ 3) * Work.BoseKinLoc.momForm ℓ d 0 ψ := by
      rw [momForm_eq_winU, ← hudef, ← mul_assoc,
        mul_inv_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0), one_mul]
    calc (∫ z : E3, ‖χc z * w z‖ ^ 2)
        ≤ (48 / Real.pi) * ∫ z : E3, ‖w z‖ ^ 2 := h1
      _ = (48 / Real.pi) * ((((2 * Real.pi) ^ 3 : ℝ)⁻¹) *
            ∫ p : E3, ‖Submission.BoseGases.kinFT w p‖ ^ 2) := by rw [h2]
      _ = (48 / Real.pi) * ((((2 * Real.pi) ^ 3 : ℝ)⁻¹) *
            ∫ p : E3, ‖(1 - (φ p : ℂ)) * Submission.BoseGases.kinFT u p‖ ^ 2) := by rw [h3]
      _ ≤ (48 / Real.pi) * ((((2 * Real.pi) ^ 3 : ℝ)⁻¹) *
            ∫ p : E3, (if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0) *
              ‖Submission.BoseGases.kinFT u p‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (48 / Real.pi) * ((((2 * Real.pi) ^ 3 : ℝ)⁻¹) *
            (((2 * Real.pi) ^ 3) * Work.BoseKinLoc.momForm ℓ d 0 ψ)) := by rw [h5]
      _ = (48 / Real.pi) * Work.BoseKinLoc.momForm ℓ d 0 ψ := by
          field_simp
          try ring
  -- ## the numerical endgame
  have hpos1 : (0:ℝ) ≤ ∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
      ‖Submission.BoseGases.kinFT χc s‖ := by
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : κ / 4 ≤ ‖s‖ <;> simp [hs, norm_nonneg]
  have hpos2 : (0:ℝ) ≤ ∫ q : E3, ‖μ q‖ ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun q => sq_nonneg _)
  have hmm0 : (0:ℝ) ≤ Work.BoseKinLoc.momForm ℓ d 0 ψ :=
    Work.BoseKinLoc.momForm_nonneg (ℓ := ℓ) (d := d) (u := 0) (ψ := ψ)
  have hgb0 : (0:ℝ) ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ :=
    Work.BoseKinLoc.gapBare_nonneg ℓ 0 ψ
  have hε2 : (∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
      ‖Submission.BoseGases.kinFT χc s‖) ^ 2 ≤ (64 * Cε) ^ 2 * d ^ 6 := by
    have h := pow_le_pow_left₀ hpos1 hε 2
    have hd6 : d ^ 12 ≤ d ^ 6 := by
      rw [show d ^ 12 = d ^ 6 * d ^ 6 from by ring]
      nlinarith [pow_pos hd 6, pow_le_one₀ hd.le hd1 (n := 6)]
    nlinarith [h, hCε0]
  have hpi : (48 / Real.pi) * (5 / 4) ≤ 23 := by
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  -- the master chain
  have hkey : c3 * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2)
      ≤ 5 * ((c3) ^ 3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
        + (5 / 4) * (c3 * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2)) := by
    have hstep : c3 * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2)
        ≤ c3 * (5 * ((c3) ^ 2 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
              ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
          + (5 / 4) * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hc3pos)
      calc ∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2
          ≤ 5 * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * wax z) p‖ ^ 2)
            + (5 / 4) * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * w z) p‖ ^ 2) :=
            hInt_split
        _ ≤ 5 * ((c3) ^ 2 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
              ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
            + (5 / 4) * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2) := by
            have e1 := hE1_le
            have e2 := hE2_le
            linarith
    calc c3 * (∫ p in T, ‖Submission.BoseGases.kinFT (fun z : E3 => χc z * u z) p‖ ^ 2)
        ≤ c3 * (5 * ((c3) ^ 2 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
              ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
          + (5 / 4) * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2)) := hstep
      _ = 5 * ((c3) ^ 3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
              ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
          + (5 / 4) * (c3 * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2)) := by ring
  -- the two halves of the master chain
  have hA1 : 5 * ((c3) ^ 3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
        ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
      ≤ 5 * ((((2 * Real.pi) ^ 3 : ℝ)⁻¹) ^ 2 * ((64 * Cε) ^ 2 * d ^ 6 *
          Work.BoseKinLoc.gapBare ℓ 0 ψ)) := by
    have hinner : c3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
          ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2))
        ≤ (64 * Cε) ^ 2 * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
      have h1 : (∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)
          ≤ ((64 * Cε) ^ 2 * d ^ 6) * (((2 * Real.pi) ^ 3) * Work.BoseKinLoc.gapBare ℓ 0 ψ) :=
        mul_le_mul hε2 hμ_le hpos2 (by positivity)
      calc c3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2))
          ≤ c3 * (((64 * Cε) ^ 2 * d ^ 6) * (((2 * Real.pi) ^ 3) * Work.BoseKinLoc.gapBare ℓ 0 ψ)) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hc3pos)
        _ = (64 * Cε) ^ 2 * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
            rw [show c3 * (((64 * Cε) ^ 2 * d ^ 6) * (((2 * Real.pi) ^ 3) * Work.BoseKinLoc.gapBare ℓ 0 ψ))
                = ((64 * Cε) ^ 2 * d ^ 6) * (c3 * ((2 * Real.pi) ^ 3)) * Work.BoseKinLoc.gapBare ℓ 0 ψ
                from by ring,
              hc3mul, mul_one]
    have hX : c3 ^ 3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
          ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2))
        = (c3) ^ 2 * (c3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
          ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2))) := by ring
    rw [hX]
    have hc3sq : (c3) ^ 2 = (((2 * Real.pi) ^ 3 : ℝ)⁻¹) ^ 2 := by rw [hc3def]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 5)
    calc (c3) ^ 2 * (c3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2)))
        = (((2 * Real.pi) ^ 3 : ℝ)⁻¹) ^ 2 * (c3 * ((∫ s : E3, (if κ / 4 ≤ ‖s‖ then (1 : ℝ) else 0) *
            ‖Submission.BoseGases.kinFT χc s‖) ^ 2 * (∫ q : E3, ‖μ q‖ ^ 2))) := by rw [hc3sq]
      _ ≤ (((2 * Real.pi) ^ 3 : ℝ)⁻¹) ^ 2 * ((64 * Cε) ^ 2 * d ^ 6 *
            Work.BoseKinLoc.gapBare ℓ 0 ψ) := mul_le_mul_of_nonneg_left hinner (by positivity)
  have hA2 : (5 / 4) * (c3 * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2))
      ≤ 23 * Work.BoseKinLoc.momForm ℓ d 0 ψ := by
    have h1 : c3 * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2)
        = ∫ z : E3, ‖χc z * w z‖ ^ 2 := by
      rw [show c3 * (((2 * Real.pi) ^ 3) * ∫ z : E3, ‖χc z * w z‖ ^ 2)
          = (c3 * ((2 * Real.pi) ^ 3)) * ∫ z : E3, ‖χc z * w z‖ ^ 2 from by ring,
        hc3mul, one_mul]
    rw [h1]
    calc (5 / 4) * ∫ z : E3, ‖χc z * w z‖ ^ 2
        ≤ (5 / 4) * ((48 / Real.pi) * Work.BoseKinLoc.momForm ℓ d 0 ψ) :=
          mul_le_mul_of_nonneg_left hχw_le (by norm_num)
      _ = ((5 / 4) * (48 / Real.pi)) * Work.BoseKinLoc.momForm ℓ d 0 ψ := by ring
      _ ≤ 23 * Work.BoseKinLoc.momForm ℓ d 0 ψ := by
          refine mul_le_mul_of_nonneg_right ?_ hmm0
          rw [show (5 / 4 : ℝ) * (48 / Real.pi) = 60 / Real.pi from by ring]
          rw [div_le_iff₀ Real.pi_pos]
          nlinarith [Real.pi_gt_three]
  linarith [hkey, hA1, hA2]

end Work.BoseBoxFock.FRK
