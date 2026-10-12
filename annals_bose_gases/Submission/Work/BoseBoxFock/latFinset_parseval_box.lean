import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latBox_ae_eq_latCell
import Submission.Work.BoseBoxFock.latChar_orthogonal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latFinset_parseval_box`

Finite lattice Parseval on the closed cube `[0,ℓ]³`:

    ∫ z in [0,ℓ]³, ‖∑_{n ∈ s} ρ n · e^{i⟪kmomInt ℓ n, z⟫}‖²  =  ℓ³ · ∑_{n ∈ s} ‖ρ n‖² .

The lattice characters `χ_n(z) = e^{i⟪kmomInt ℓ n, z⟫}` are pairwise orthogonal on the
fundamental cell `[0,ℓ)³` (`Work.BoseBoxFock.latChar_orthogonal`, the one-dimensional
computation `∫_{[0,ℓ)} e^{i c t} = ℓ·δ_{c,0}` tensorised over the three coordinates), and both
the closed cube and the half-open cell have volume `ℓ³`, so they agree almost everywhere
(`Work.BoseBoxFock.latBox_ae_eq_latCell`).

The proof expands `‖F‖² = (F · conj F).re` for `F = ∑_{n∈s} ρ n χ_n`, interchanges the finite
sum with the integral (`integral_finsetSum` on the restricted measure
`volume.restrict (latCell ℓ)`, all summands being continuous and bounded, hence integrable on
the finite-measure cell), and evaluates each matrix element by orthogonality:

    ∫_{cell} χ_m · conj(χ_n) = ∫_{cell} χ_{m-n} = ℓ³ · [m = n] .

The remaining double sum collapses to `ℓ³ · ∑_{n∈s} ρ n · conj (ρ n)`, whose real part is
`ℓ³ · ∑_{n∈s} ‖ρ n‖²`.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The lattice character `z ↦ e^{i⟪kmomInt ℓ n, z⟫}` on `E3 = ℝ³`. -/
private def latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))

private lemma kmomInt_sub (ℓ : ℝ) (m n : Fin 3 → ℤ) :
    kmomInt ℓ (m - n) = kmomInt ℓ m - kmomInt ℓ n := by
  have h := LatFourier.kmomInt_add ℓ (m - n) n
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- `χ_m · conj χ_n = χ_{m-n}`. -/
private lemma latChr_mul_conj (ℓ : ℝ) (m n : Fin 3 → ℤ) (z : E3) :
    latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z) = latChr ℓ (m - n) z := by
  simp only [latChr]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]
  congr 1
  rw [kmomInt_sub ℓ m n]
  simp only [inner_sub_left]
  push_cast
  ring

/-- The characters have modulus one. -/
private lemma norm_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChr ℓ n z‖ = 1 := by
  rw [latChr, Complex.norm_exp]
  have h : (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  rw [h, Real.exp_zero]

private lemma continuous_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) : Continuous (latChr ℓ n) := by
  change Continuous (fun z : E3 => Complex.exp (Complex.I *
    ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
  fun_prop

/-- `‖z‖² = (z · conj z).re`. -/
private lemma sq_norm_eq_re (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.sq_norm, Complex.mul_conj, Complex.ofReal_re]

theorem latFinset_parseval_box {ℓ : ℝ} (hℓ : 0 < ℓ) (s : Finset (Fin 3 → ℤ))
    (ρ : (Fin 3 → ℤ) → ℂ) :
    (∫ z in Work.BoseBoxFock.LatFourier.latBox ℓ,
      ‖∑ n ∈ s, ρ n * Complex.exp (Complex.I *
        ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ))‖ ^ 2)
      = ℓ ^ 3 * ∑ n ∈ s, ‖ρ n‖ ^ 2 := by
  classical
  change (∫ z in LatFourier.latBox ℓ, ‖∑ n ∈ s, ρ n * latChr ℓ n z‖ ^ 2)
      = ℓ ^ 3 * ∑ n ∈ s, ‖ρ n‖ ^ 2
  -- the cell has finite measure, so bounded continuous functions are integrable on it
  have hC : volume (LatFourier.latCell ℓ) ≠ ⊤ := by
    rw [LatFourier.volume_latCell hℓ.le]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (LatFourier.latCell ℓ)) :=
    isFiniteMeasure_restrict.mpr hC
  -- the closed cube and the half-open cell agree a.e.
  rw [setIntegral_congr_set (latBox_ae_eq_latCell hℓ.le)]
  set F : E3 → ℂ := fun z => ∑ n ∈ s, ρ n * latChr ℓ n z with hF
  have hbdd : ∀ z : E3, ‖F z‖ ≤ ∑ n ∈ s, ‖ρ n‖ := by
    intro z
    rw [hF]
    calc ‖∑ n ∈ s, ρ n * latChr ℓ n z‖ ≤ ∑ n ∈ s, ‖ρ n * latChr ℓ n z‖ := norm_sum_le _ _
      _ = ∑ n ∈ s, ‖ρ n‖ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul, norm_latChr, mul_one]
  have hcontF : Continuous F := by
    rw [hF]
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_latChr ℓ n)
  have hGint : Integrable (fun z : E3 => F z * (starRingEnd ℂ) (F z))
      (volume.restrict (LatFourier.latCell ℓ)) := by
    refine Integrable.of_bound ?_ ((∑ n ∈ s, ‖ρ n‖) ^ 2) ?_
    · exact (hcontF.mul (Complex.continuous_conj.comp hcontF)).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [norm_mul, RCLike.norm_conj]
      have h2 : ‖F z‖ * ‖F z‖ = ‖F z‖ ^ 2 := by ring
      rw [h2]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbdd z) 2
  -- pointwise expansion of `F · conj F`
  have hpt : ∀ z : E3, F z * (starRingEnd ℂ) (F z)
      = ∑ m ∈ s, ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
          * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z)) := by
    intro z
    rw [hF]
    rw [map_sum]
    simp only [map_mul]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  -- the matrix elements of the characters
  have hkey : ∀ m n : Fin 3 → ℤ,
      (∫ z in LatFourier.latCell ℓ, latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z))
        = if m - n = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
    intro m n
    have h1 : (fun z : E3 => latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z))
        = (fun z : E3 => Complex.exp (Complex.I *
            ((inner ℝ (kmomInt ℓ (m - n)) z : ℝ) : ℂ))) :=
      funext fun z => by simpa only [latChr] using latChr_mul_conj ℓ m n z
    rw [h1]
    exact latChar_orthogonal hℓ (m - n)
  have hint : ∀ m n : Fin 3 → ℤ,
      Integrable (fun z : E3 => (ρ m * (starRingEnd ℂ) (ρ n))
        * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z)))
        (volume.restrict (LatFourier.latCell ℓ)) := by
    intro m n
    refine Integrable.of_bound ?_ (‖ρ m‖ * ‖ρ n‖) ?_
    · have hcont : Continuous (fun z : E3 => (ρ m * (starRingEnd ℂ) (ρ n))
          * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z))) :=
        continuous_const.mul ((continuous_latChr ℓ m).mul
          (Complex.continuous_conj.comp (continuous_latChr ℓ n)))
      exact hcont.aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      simp only [norm_mul, RCLike.norm_conj, norm_latChr, mul_one, le_refl]
  have hint2 : ∀ m : Fin 3 → ℤ,
      Integrable (fun z : E3 => ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
        * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z)))
        (volume.restrict (LatFourier.latCell ℓ)) := by
    intro m
    refine Integrable.of_bound ?_ (‖ρ m‖ * ∑ n ∈ s, ‖ρ n‖) ?_
    · have hcont : Continuous (fun z : E3 => ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
          * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z))) :=
        continuous_finsetSum _ fun n _ => continuous_const.mul
          ((continuous_latChr ℓ m).mul (Complex.continuous_conj.comp (continuous_latChr ℓ n)))
      exact hcont.aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      calc ‖∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
            * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z))‖
          ≤ ∑ n ∈ s, ‖(ρ m * (starRingEnd ℂ) (ρ n))
            * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z))‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ s, ‖ρ m‖ * ‖ρ n‖ := by
            refine Finset.sum_le_sum fun n _ => ?_
            simp only [norm_mul, RCLike.norm_conj, norm_latChr, mul_one, le_refl]
        _ = ‖ρ m‖ * ∑ n ∈ s, ‖ρ n‖ := by rw [Finset.mul_sum]
  -- interchange the finite sums with the integral and evaluate the matrix elements
  have hlin : (∫ z in LatFourier.latCell ℓ, F z * (starRingEnd ℂ) (F z))
      = ∑ m ∈ s, ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
          * (if m - n = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0) := by
    calc (∫ z in LatFourier.latCell ℓ, F z * (starRingEnd ℂ) (F z))
        = ∫ z in LatFourier.latCell ℓ, ∑ m ∈ s, ∑ n ∈ s,
            (ρ m * (starRingEnd ℂ) (ρ n))
              * (latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z)) :=
          setIntegral_congr_fun (LatFourier.measurableSet_latCell ℓ) fun z _ => hpt z
      _ = ∑ m ∈ s, ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
            * (∫ z in LatFourier.latCell ℓ,
                latChr ℓ m z * (starRingEnd ℂ) (latChr ℓ n z)) := by
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun m _ => ?_
            rw [integral_finsetSum]
            · refine Finset.sum_congr rfl fun n _ => ?_
              rw [integral_const_mul]
            · intro n _
              exact hint m n
          · intro m _
            exact hint2 m
      _ = ∑ m ∈ s, ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
            * (if m - n = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0) := by
          simp only [hkey]
  -- collapse the orthogonal double sum
  have hcollapse : (∑ m ∈ s, ∑ n ∈ s, (ρ m * (starRingEnd ℂ) (ρ n))
        * (if m - n = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ n ∈ s, ρ n * (starRingEnd ℂ) (ρ n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    refine Eq.trans (Finset.sum_eq_single m ?_ ?_) ?_
    · intro n hn hne
      have h : m - n ≠ 0 := fun hh => hne (sub_eq_zero.mp hh).symm
      rw [if_neg h, mul_zero]
    · intro hnot
      exact absurd hm hnot
    · rw [sub_self, if_pos rfl]
      ring
  have hW : ∑ n ∈ s, ρ n * (starRingEnd ℂ) (ρ n) = ((∑ n ∈ s, ‖ρ n‖ ^ 2 : ℝ) : ℂ) := by
    change ∑ n ∈ s, ρ n * (starRingEnd ℂ) (ρ n) = Complex.ofRealHom (∑ n ∈ s, ‖ρ n‖ ^ 2)
    rw [map_sum Complex.ofRealHom]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  have hre : (((ℓ ^ 3 : ℝ) : ℂ) * ∑ n ∈ s, ρ n * (starRingEnd ℂ) (ρ n)).re
      = ℓ ^ 3 * ∑ n ∈ s, ‖ρ n‖ ^ 2 := by
    rw [hW, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hstep1 : (∫ z in LatFourier.latCell ℓ, ‖F z‖ ^ 2)
      = ∫ z in LatFourier.latCell ℓ, (F z * (starRingEnd ℂ) (F z)).re :=
    setIntegral_congr_fun (LatFourier.measurableSet_latCell ℓ) fun z _ => sq_norm_eq_re (F z)
  have hstep2 : (∫ z in LatFourier.latCell ℓ, (F z * (starRingEnd ℂ) (F z)).re)
      = (∫ z in LatFourier.latCell ℓ, F z * (starRingEnd ℂ) (F z)).re := by
    simpa using integral_re hGint
  rw [hstep1, hstep2, hlin, hcollapse, hre]

end Work.BoseBoxFock
