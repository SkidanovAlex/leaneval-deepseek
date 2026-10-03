import Mathlib
import Submission.Work.KMTAreas.MSW_pairing
import Submission.Port.Aesm

/-!
# `MSW_single_torsion` — the single-torsion (Magyar–Stein–Wainger) sampling principle

The Ionescu–Wainger projection at the single torsion set `(1/Q)ℤ/ℤ`, with a Schwartz symbol `φ`
supported in the short arc `ℝ_{≤k} = [-2^k,2^k]` where `2^k · 2Q ≤ 1`, is bounded on `ℓ^p(ℤ)` by
a constant times the `L^p(ℝ)` operator norm of the continuous multiplier `T_φ`.

The proof is the Shannon-sampling/de Leeuw transfer: for finitely supported `f, g` on `ℤ` the
pairing of the projection with `g` is the `L²(ℝ)` pairing `⟪T_φ (I f), I g⟫`, where `I` is the
Shannon interpolation operator with symbol the fixed cutoff `χ ≡ 1` on the support of `φ`
(`MSW_interp_bound`); each of the `Q` torsion terms is bounded by `msw_term_bound`, and the result
follows by `ℓ^p` duality (`MSW_dual_pairing`, `MSW_dual_pairing_one`).

## Main result

* `Work.KMTAreas.MSW_single_torsion`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier

/-- **`MSW_single_torsion`** — the Magyar–Stein–Wainger sampling principle for the single torsion
subgroup `(1/Q)ℤ/ℤ`. -/
theorem MSW_single_torsion {Q : ℕ} (hQ : 1 ≤ Q) {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤) :
    ∃ C : NNReal, 0 < C ∧ ∀ {k : ℤ}, (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1 →
      ∀ {φ : SchwartzMap ℝ ℂ}, (∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) →
      ∀ {M : NNReal}, Work.Analysis.IWMultiplier.IsLqMultiplierBound p (φ : ℝ → ℂ) M →
        Work.Analysis.IWMultiplier.IWLqBoundScalar (Work.KMTAreas.iwDenomFreqs {Q})
          (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) p (C * M) := by
  obtain ⟨CK, hCKpos, hCK⟩ := MSW_interp_bound mswK
  refine ⟨(Q : NNReal) * CK * CK + 1, by positivity, ?_⟩
  intro k hk φ hφ M hM f hf
  set C : NNReal := (Q : NNReal) * CK * CK + 1 with hC
  have hCM : ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ)) ≤ (C : ℝ) * (M : ℝ) := by
    have hCval : (C : ℝ) = (Q : ℝ) * (CK : ℝ) * (CK : ℝ) + 1 := by
      rw [hC]; push_cast; ring
    rw [hCval]; nlinarith [M.coe_nonneg]
  have hCM' : (Q : NNReal) * M * CK * CK ≤ C * M := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hCM
  have hCMcast : ENNReal.ofReal (((C * M : NNReal) : ℝ)) = ENNReal.ofReal ((C : ℝ) * (M : ℝ)) := by
    congr 1
  set X : ℤ → ℂ := fun n => Work.Analysis.IWMultiplier.iwConv (iwDenomFreqs {Q})
    (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) f n with hX
  have hfin : eLpNorm f p Measure.count < ⊤ := msw_eLpNorm_lt_top hp1 hp2 hf
  have hconv : ENNReal.ofReal ((C * M * (eLpNorm f p Measure.count).toNNReal : NNReal) : ℝ)
      = ENNReal.ofReal (((C * M : NNReal) : ℝ)) * eLpNorm f p Measure.count := by
    rw [show (((C * M * (eLpNorm f p Measure.count).toNNReal : NNReal) : ℝ))
        = ((C * M : NNReal) : ℝ) * ((eLpNorm f p Measure.count).toNNReal : ℝ) from by
          first | rfl | (push_cast; ring),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((C * M : NNReal) : ℝ)),
      msw_ofReal_toNNReal hfin]
  have hXae : AEMeasurable X Measure.count := (measurable_of_countable X).aemeasurable
  rcases eq_or_lt_of_le hp1 with hp_eq | hp_gt
  · -- `p = 1`: duality against bounded test functions
    subst hp_eq
    refine le_trans (MSW_dual_pairing_one
      (A := C * M * (eLpNorm f 1 Measure.count).toNNReal) ?_) ?_
    · intro g hg hg1
      have hpb := msw_pairing_bound_aux (Q := Q) hQ hk hφ (ENNReal.HolderTriple.instInfty 1)
        le_rfl le_top hM hCK (msw_support_zero hf) (msw_support_zero hg)
      have hgle : eLpNorm g (⊤ : ENNReal) Measure.count ≤ 1 := by
        have h := eLpNorm_le_of_ae_bound (hf := by pw_aesm) (μ := Measure.count) (p := (⊤ : ENNReal)) (C := 1)
          (f := g) (Filter.Eventually.of_forall fun n => by simpa using hg1 n)
        simpa using h
      rw [hconv]
      calc enorm (tsum (fun n : ℤ => X n * starRingEnd ℂ (g n)))
          ≤ ENNReal.ofReal ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ))
              * eLpNorm f 1 Measure.count * eLpNorm g (⊤ : ENNReal) Measure.count := hpb
        _ ≤ ENNReal.ofReal (((C * M : NNReal) : ℝ)) * eLpNorm f 1 Measure.count
              * eLpNorm g (⊤ : ENNReal) Measure.count := by
            have : ENNReal.ofReal ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ))
                ≤ ENNReal.ofReal (((C * M : NNReal) : ℝ)) := by
              rw [hCMcast]; exact ENNReal.ofReal_le_ofReal hCM
            gcongr
        _ ≤ ENNReal.ofReal (((C * M : NNReal) : ℝ)) * eLpNorm f 1 Measure.count * 1 := by gcongr
        _ = ENNReal.ofReal (((C * M : NNReal) : ℝ)) * eLpNorm f 1 Measure.count := by rw [mul_one]
    · rw [← hconv]
  · -- `1 < p`: `ℓ^p` duality
    have hq1 : 1 < p.toReal := by
      have h := (ENNReal.toReal_lt_toReal (by norm_num : (1 : ENNReal) ≠ ⊤) (ne_of_lt hp2)).mpr hp_gt
      simpa using h
    have hr1 : (1 : ENNReal) ≤ ENNReal.ofReal (p.toReal / (p.toReal - 1)) := by
      refine ENNReal.one_le_ofReal.mpr ?_
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hpr : p.HolderConjugate (ENNReal.ofReal (p.toReal / (p.toReal - 1))) := by
      have hpq : Real.HolderConjugate p.toReal (p.toReal / (p.toReal - 1)) :=
        (Real.holderConjugate_iff_eq_conjExponent hq1).mpr rfl
      have h2 := Real.HolderConjugate.ennrealOfReal hpq
      rwa [ENNReal.ofReal_toReal (ne_of_lt hp2)] at h2
    have hdp := MSW_dual_pairing (q := p.toReal)
      (A := C * M * (eLpNorm f p Measure.count).toNNReal) hq1 hXae ?_
    · rw [show ENNReal.ofReal p.toReal = p from ENNReal.ofReal_toReal (ne_of_lt hp2)] at hdp
      exact le_trans hdp (le_of_eq hconv)
    · intro g hg
      calc enorm (tsum (fun n : ℤ => X n * starRingEnd ℂ (g n)))
          ≤ ENNReal.ofReal ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ))
              * eLpNorm f p Measure.count
              * eLpNorm g (ENNReal.ofReal (p.toReal / (p.toReal - 1))) Measure.count :=
            msw_pairing_bound_aux (Q := Q) hQ hk hφ hpr hp1 hr1 hM hCK
              (msw_support_zero hf) (msw_support_zero hg)
        _ ≤ ENNReal.ofReal (((C * M : NNReal) : ℝ)) * eLpNorm f p Measure.count
              * eLpNorm g (ENNReal.ofReal (p.toReal / (p.toReal - 1))) Measure.count := by
            gcongr
            first | exact hCM' | exact hCM
        _ = ENNReal.ofReal ((C * M * (eLpNorm f p Measure.count).toNNReal : NNReal) : ℝ)
              * eLpNorm g (ENNReal.ofReal (p.toReal / (p.toReal - 1))) Measure.count := by
            rw [hconv]

end Work.KMTAreas
