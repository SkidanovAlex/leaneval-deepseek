import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.DefsC
import Submission.Work.BoseBoxFock.frameSampling_latBox
import Submission.Work.BoseBoxFock.latBox_ae_eq_latCell
import Submission.Work.BoseBoxFock.latChar_orthogonal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The objects of the expansion

With `b n = (ℓ³)⁻¹ kinFT Φ (κ_n)` and the characters `e^{±i⟪κ_n,z⟫}` on the lattice
`ℓℤ³`, the absolutely convergent Fourier series `S = Σ'_n b n · e^{i⟪κ_n,·⟫}` is a continuous
function whose lattice Fourier coefficients are `ℓ³ · b n`; the whole lemma is the comparison of
`S` with the periodisation `latPerC ℓ Φ`. -/

/-- The lattice Fourier coefficient `b n = (ℓ³)⁻¹ kinFT Φ (κ_n)` of the expansion. -/
private noncomputable def latB (ℓ : ℝ) (Φ : E3 → ℂ) (n : Fin 3 → ℤ) : ℂ :=
  (ℓ^3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)

/-- The character `e^{i⟪κ_n,z⟫}`. -/
private noncomputable def latChrP (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))

/-- The conjugate character `e^{-i⟪κ_n,z⟫}`. -/
private noncomputable def latChrN (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ℂ :=
  Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))

/-- The absolutely convergent Fourier series `S z = Σ'_n b n e^{i⟪κ_n,z⟫}` of the periodisation. -/
private noncomputable def latSer (ℓ : ℝ) (Φ : E3 → ℂ) (z : E3) : ℂ :=
  ∑' n, latB ℓ Φ n * latChrP ℓ n z

/-! ## Elementary properties of the characters -/

private lemma latChrP_norm (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChrP ℓ n z‖ = 1 := by
  rw [latChrP, mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I]

private lemma latChrN_norm (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChrN ℓ n z‖ = 1 := by
  rw [latChrN, show -(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))
      = ((-(inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma latChrP_cont (ℓ : ℝ) (n : Fin 3 → ℤ) : Continuous (latChrP ℓ n) := by
  change Continuous (fun z : E3 =>
    Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
  fun_prop

private lemma latChrN_cont (ℓ : ℝ) (n : Fin 3 → ℤ) : Continuous (latChrN ℓ n) := by
  change Continuous (fun z : E3 =>
    Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))))
  fun_prop

private lemma kmomInt_sub (ℓ : ℝ) (m n : Fin 3 → ℤ) :
    Work.BoseBoxFock.kmomInt ℓ (m - n)
      = Work.BoseBoxFock.kmomInt ℓ m - Work.BoseBoxFock.kmomInt ℓ n := by
  have h := Work.BoseBoxFock.LatFourier.kmomInt_add ℓ (m - n) n
  rw [sub_add_cancel] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

/-- The character product: `χ_n · χ̄_m = χ_{n-m}`. -/
private lemma latChrP_mul_latChrN (ℓ : ℝ) (n m : Fin 3 → ℤ) (z : E3) :
    latChrP ℓ n z * latChrN ℓ m z = latChrP ℓ (n - m) z := by
  simp only [latChrP, latChrN]
  rw [← Complex.exp_add]
  congr 1
  show Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ)
      + -(Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℝ) : ℂ))
    = Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ (n - m)) z : ℝ) : ℂ)
  rw [kmomInt_sub, inner_sub_left]
  push_cast
  ring

/-! ## Summability and continuity of the series -/

private lemma latB_summable {ℓ : ℝ} {Φ : E3 → ℂ}
    (hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖)) :
    Summable (fun n => ‖latB ℓ Φ n‖) := by
  have h1 : Summable (fun n : Fin 3 → ℤ => ‖(ℓ^3)⁻¹‖ *
      ‖Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖) := hsumm.mul_left _
  refine h1.congr fun n => ?_
  simp [latB]

private lemma latSum_summable {ℓ : ℝ} {Φ : E3 → ℂ}
    (hsum : Summable (fun n => ‖latB ℓ Φ n‖)) (z : E3) :
    Summable (fun n => latB ℓ Φ n * latChrP ℓ n z) := by
  refine Summable.of_norm ?_
  refine hsum.congr fun n => ?_
  rw [norm_mul, latChrP_norm, mul_one]

private lemma latSer_cont {ℓ : ℝ} {Φ : E3 → ℂ} (hsum : Summable (fun n => ‖latB ℓ Φ n‖)) :
    Continuous (latSer ℓ Φ) := by
  have h := continuous_tsum (u := fun n => ‖latB ℓ Φ n‖)
    (f := fun (n : Fin 3 → ℤ) (z : E3) => latB ℓ Φ n * latChrP ℓ n z)
    (fun n => continuous_const.mul (latChrP_cont ℓ n)) hsum
    (fun n z => by rw [norm_mul, latChrP_norm, mul_one])
  exact h

/-- The series `S` is periodic under the lattice translations. -/
private lemma latSer_add_latVec {ℓ : ℝ} {Φ : E3 → ℂ} (hℓne : ℓ ≠ 0)
    (v : Fin 3 → ℤ) (z : E3) :
    latSer ℓ Φ (z + ℓ • Work.BoseBoxFock.latVec v) = latSer ℓ Φ z := by
  simp only [latSer]
  refine tsum_congr fun n => ?_
  rw [show latChrP ℓ n (z + ℓ • Work.BoseBoxFock.latVec v) = latChrP ℓ n z from
    Work.BoseBoxFock.LatFourier.exp_I_inner_add_latVec hℓne n v z]

/-- The algebra `ℓ³ · b n = kinFT Φ (κ_n)`. -/
private lemma latB_mul_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (Φ : E3 → ℂ) (m : Fin 3 → ℤ) :
    (ℓ^3 : ℂ) * latB ℓ Φ m
      = Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ m) := by
  have hne : (ℓ^3 : ℂ) ≠ 0 := by
    have h0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ)
    simpa using pow_ne_zero 3 h0
  rw [latB]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-! ## The lattice Fourier coefficients of the series -/

/-- Every lattice Fourier coefficient of `S` is `ℓ³ b n`.  This is the termwise integration of the
absolutely convergent series against the conjugate character, using the orthogonality
`Work.BoseBoxFock.latChar_orthogonal` of the characters on the fundamental cell. -/
private lemma latSer_coeff {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : E3 → ℂ}
    (hsum : Summable (fun n => ‖latB ℓ Φ n‖)) (m : Fin 3 → ℤ) :
    (∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, latSer ℓ Φ z * latChrN ℓ m z)
      = (ℓ^3 : ℂ) * latB ℓ Φ m := by
  haveI : IsFiniteMeasure (volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Work.BoseBoxFock.LatFourier.volume_latCell hℓ.le]; exact ENNReal.ofReal_ne_top)
  have hint : ∀ n : Fin 3 → ℤ, Integrable (fun z => (latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z)
      (volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)) := by
    intro n
    refine Integrable.of_bound ?_ ‖latB ℓ Φ n‖ ?_
    · exact ((continuous_const.mul (latChrP_cont ℓ n)).mul (latChrN_cont ℓ m)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul, norm_mul, latChrP_norm, latChrN_norm, mul_one, mul_one]
  have hnorm_int : ∀ n, (∫ z, ‖(latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z‖
      ∂(volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ))) = ‖latB ℓ Φ n‖ * ℓ^3 := by
    intro n
    have hpt : ∀ z, ‖(latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z‖ = ‖latB ℓ Φ n‖ := by
      intro z; rw [norm_mul, norm_mul, latChrP_norm, latChrN_norm, mul_one, mul_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const,
      MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply_univ,
      Work.BoseBoxFock.LatFourier.volume_latCell hℓ.le,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]
  have hsum_int : Summable (fun n => ∫ z, ‖(latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z‖
      ∂(volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ))) := by
    refine (hsum.mul_right (ℓ^3)).congr fun n => ?_
    rw [hnorm_int n]
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum_int
  have hcongr : (∫ z, ∑' n, (latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z
        ∂(volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)))
      = ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, latSer ℓ Φ z * latChrN ℓ m z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [latSer]
    rw [tsum_mul_right]
  rw [hcongr] at hHS
  have hval : ∀ n, (∫ z, (latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z
      ∂(volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)))
      = latB ℓ Φ n * (if n - m = 0 then ((ℓ^3 : ℝ) : ℂ) else 0) := by
    intro n
    have hpt : ∀ z, (latB ℓ Φ n * latChrP ℓ n z) * latChrN ℓ m z
        = latB ℓ Φ n * latChrP ℓ (n - m) z := by
      intro z; rw [mul_assoc, latChrP_mul_latChrN]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
    congr 1
    exact Work.BoseBoxFock.latChar_orthogonal hℓ (n - m)
  have hsingle : HasSum (fun n => latB ℓ Φ n * (if n - m = 0 then ((ℓ^3 : ℝ) : ℂ) else 0))
      (latB ℓ Φ m * ((ℓ^3 : ℝ) : ℂ)) := by
    have hh := hasSum_single
      (f := fun n => latB ℓ Φ n * (if n - m = 0 then ((ℓ^3 : ℝ) : ℂ) else 0)) m
      (fun n hn => by rw [if_neg (fun h => hn (sub_eq_zero.mp h)), mul_zero])
    simpa using hh
  have hfin := (hHS.congr_fun (fun n => (hval n).symm)).unique hsingle
  rw [hfin]
  push_cast
  ring

/-! ## The periodisation is continuous and locally a finite sum -/

private lemma isCompact_latBox {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsCompact (Work.BoseBoxFock.LatFourier.latBox ℓ) :=
  Metric.isCompact_of_isClosed_isBounded (Work.BoseBoxFock.LatFourier.isClosed_latBox ℓ)
    ((Metric.isBounded_closedBall (x := (0 : E3)) (r := Real.sqrt 3 * ℓ)).subset
      (fun x hx => by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact Work.BoseBoxFock.LatFourier.latBox_subset_closedBall hℓ.le hx))

/-- On the ball of radius `B`, the periodisation is the finite sum over the lattice points of
`latVec`-norm at most `(ρ+B)/ℓ`. -/
private lemma latPerC_eq_sum_latBall {ℓ ρ B : ℝ} (hℓ : 0 < ℓ) {Φ : E3 → ℂ}
    (hΦs : ∀ x, ρ < ‖x‖ → Φ x = 0) {z : E3} (hz : ‖z‖ ≤ B) :
    latPerC ℓ Φ z = ∑ m ∈ Work.BoseBoxFock.LatFourier.latBall ((ρ + B) / ℓ),
      Φ (z + ℓ • Work.BoseBoxFock.latVec m) := by
  rw [latPerC]
  refine tsum_eq_sum (s := Work.BoseBoxFock.LatFourier.latBall ((ρ + B) / ℓ)) (fun m hm => ?_)
  have hnot : (ρ + B) / ℓ < ‖Work.BoseBoxFock.latVec m‖ := by
    rw [← not_le]
    intro hc
    exact hm ((Work.BoseBoxFock.LatFourier.mem_latBall).mpr hc)
  have h4 : ρ + B < ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
    rw [div_lt_iff₀ hℓ] at hnot
    linarith [hnot]
  have hgt : ρ < ‖z + ℓ • Work.BoseBoxFock.latVec m‖ := by
    have h2 : ‖ℓ • Work.BoseBoxFock.latVec m‖
        ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := by
      calc ‖ℓ • Work.BoseBoxFock.latVec m‖
            = ‖(z + ℓ • Work.BoseBoxFock.latVec m) - z‖ := by congr 1; abel
        _ ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := norm_sub_le _ _
    have h5 : ‖ℓ • Work.BoseBoxFock.latVec m‖ = ℓ * ‖Work.BoseBoxFock.latVec m‖ :=
      Work.BoseBoxFock.LatFourier.latVec_norm_smul ℓ hℓ.le m
    linarith
  simp [hΦs _ hgt]

private lemma continuous_latPerC {ℓ ρ : ℝ} (hℓ : 0 < ℓ) {Φ : E3 → ℂ}
    (hΦc : Continuous Φ) (hΦs : ∀ x, ρ < ‖x‖ → Φ x = 0) :
    Continuous (latPerC ℓ Φ) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  have hg : Continuous (fun z : E3 =>
      ∑ m ∈ Work.BoseBoxFock.LatFourier.latBall ((ρ + (‖z₀‖ + 1)) / ℓ),
        Φ (z + ℓ • Work.BoseBoxFock.latVec m)) :=
    continuous_finsetSum _ fun m _ => hΦc.comp (continuous_id.add continuous_const)
  refine hg.continuousAt.congr ?_
  have hev : ∀ᶠ z in nhds z₀, ‖z‖ ≤ ‖z₀‖ + 1 := by
    have hop : IsOpen {z : E3 | ‖z‖ < ‖z₀‖ + 1} := isOpen_lt continuous_norm continuous_const
    have hz₀ : z₀ ∈ {z : E3 | ‖z‖ < ‖z₀‖ + 1} := by
      show ‖z₀‖ < ‖z₀‖ + 1
      linarith
    filter_upwards [hop.mem_nhds hz₀] with z hz
    exact hz.le
  filter_upwards [hev] with z hz
  exact (latPerC_eq_sum_latBall hℓ hΦs hz).symm

/-! ## The `L²` step: the difference is a.e. zero on the fundamental box -/

private lemma integrableOn_latCell_of_continuousOn_latBox {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hf : ContinuousOn f (Work.BoseBoxFock.LatFourier.latBox ℓ)) :
    Integrable f (volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)) := by
  rw [← MeasureTheory.Measure.restrict_congr_set
    (Work.BoseBoxFock.latBox_ae_eq_latCell hℓ.le)]
  exact hf.integrableOn_compact (isCompact_latBox hℓ)

/-- The closed box is the closure of its interior. -/
private lemma latBox_subset_closure_interior {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseBoxFock.LatFourier.latBox ℓ
      ⊆ closure (interior (Work.BoseBoxFock.LatFourier.latBox ℓ)) := by
  have hconv : Convex ℝ (Work.BoseBoxFock.LatFourier.latBox ℓ) := by
    intro x hx y hy a b ha hb hab
    simp only [Work.BoseBoxFock.LatFourier.mem_latBox, Set.mem_Icc] at hx hy ⊢
    intro i
    have h1 := hx i
    have h2 := hy i
    have hxy : (a • x + b • y) i = a * x i + b * y i := by
      simp [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hxy]
    exact ⟨by nlinarith [h1.1, h2.1], by nlinarith [h1.2, h2.2]⟩
  have hne : (interior (Work.BoseBoxFock.LatFourier.latBox ℓ)).Nonempty := by
    have hsub : {x : E3 | ∀ i, x i ∈ Set.Ioo (0:ℝ) ℓ}
        ⊆ Work.BoseBoxFock.LatFourier.latBox ℓ := by
      intro x hx
      rw [Work.BoseBoxFock.LatFourier.mem_latBox]
      intro i
      exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩
    have hopen : IsOpen {x : E3 | ∀ i, x i ∈ Set.Ioo (0:ℝ) ℓ} := by
      rw [show {x : E3 | ∀ i, x i ∈ Set.Ioo (0:ℝ) ℓ}
          = ⋂ i : Fin 3, {x : E3 | x i ∈ Set.Ioo (0:ℝ) ℓ} from by
        ext x; simp]
      exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (by fun_prop)
    refine ⟨WithLp.toLp 2 (fun _ : Fin 3 => ℓ/2), interior_maximal hsub hopen ?_⟩
    intro i
    show ℓ/2 ∈ Set.Ioo (0:ℝ) ℓ
    exact ⟨by linarith, by linarith⟩
  rw [Convex.closure_interior_eq_closure_of_nonempty_interior hconv hne,
    (Work.BoseBoxFock.LatFourier.isClosed_latBox ℓ).closure_eq]

/-- Absolutely/uniformly convergent Fourier expansion of the periodisation of a smooth compactly
supported `Φ` (the two inputs `hsumm`, `hcoeff` are supplied in this chapter by
`Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL` and `Work.BoseBoxFock.L1Tails.latPerC_fourierCoeff`,
so this statement isolates the expansion step).
Route: with `b n := (ℓ^3)⁻¹ kinFT Φ (κ_n)`, `hsumm` makes `S z := Σ'_n b n * e^{i⟪κ_n,z⟫}`
well defined, continuous (`continuous_tsum`, dominated by `‖b n‖`), and `S` has the required
`HasSum`; integrate termwise (`MeasureTheory.integral_tsum` and
`Work.BoseBoxFock.latChar_orthogonal`) to see that every lattice Fourier coefficient of `S` is
`ℓ^3 * b n`, equal to that of `latPerC ℓ Φ` by `hcoeff`.  Then
`Work.BoseBoxFock.frameSampling_latBox` applied to `latBox ℓ ∋ z ↦ S z - latPerC ℓ Φ z`
(`latBox` and `latCell` agree a.e.: `Work.BoseBoxFock.latBox_ae_eq_latCell`) makes that difference
zero a.e.; being continuous and `ℓℤ³`-periodic it vanishes everywhere
(`Work.BoseBoxFock.L1Tails.latPerC_add_latVec` for the periodic part). -/
theorem latPerC_hasSum_fourier {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖))
    (hcoeff : ∀ n : Fin 3 → ℤ,
      (∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
          Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
            * Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))))
        = Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n))
    (z : EuclideanSpace ℝ (Fin 3)) :
    HasSum (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
        Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)
        * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
      (Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z) := by
  classical
  -- a radius containing the support of `Φ`
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ∀ x : E3, ρ < ‖x‖ → Φ x = 0 := by
    obtain ⟨ρ, hρ⟩ := hc.isBounded.subset_closedBall (0 : E3)
    refine ⟨ρ, fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    have h1 := hρ hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
    linarith
  have hb : Summable (fun n => ‖latB ℓ Φ n‖) := latB_summable hsumm
  have hScont : Continuous (latSer ℓ Φ) := latSer_cont hb
  have hPcont : Continuous (latPerC ℓ Φ) := continuous_latPerC hℓ hΦ.continuous hρ
  let T : E3 → ℂ := fun w => latSer ℓ Φ w - latPerC ℓ Φ w
  have hTcont : Continuous T := hScont.sub hPcont
  -- all lattice Fourier coefficients of `T` vanish
  have hTcoeff : ∀ m : Fin 3 → ℤ,
      (∫ w in Work.BoseBoxFock.LatFourier.latCell ℓ, T w * latChrN ℓ m w) = 0 := by
    intro m
    have hSint : Integrable (fun w => latSer ℓ Φ w * latChrN ℓ m w)
        (volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)) :=
      integrableOn_latCell_of_continuousOn_latBox hℓ
        ((hScont.mul (latChrN_cont ℓ m)).continuousOn)
    have hPint : Integrable (fun w => latPerC ℓ Φ w * latChrN ℓ m w)
        (volume.restrict (Work.BoseBoxFock.LatFourier.latCell ℓ)) :=
      integrableOn_latCell_of_continuousOn_latBox hℓ
        ((hPcont.mul (latChrN_cont ℓ m)).continuousOn)
    have hPc : (∫ w in Work.BoseBoxFock.LatFourier.latCell ℓ, latPerC ℓ Φ w * latChrN ℓ m w)
        = Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ m) := hcoeff m
    have hstep : (∫ w in Work.BoseBoxFock.LatFourier.latCell ℓ, T w * latChrN ℓ m w)
        = ∫ w in Work.BoseBoxFock.LatFourier.latCell ℓ,
            (latSer ℓ Φ w * latChrN ℓ m w - latPerC ℓ Φ w * latChrN ℓ m w) :=
      MeasureTheory.setIntegral_congr_fun
        (Work.BoseBoxFock.LatFourier.measurableSet_latCell ℓ)
        (fun w _ => by simp only [T]; ring)
    rw [hstep, MeasureTheory.integral_sub hSint hPint, latSer_coeff hℓ hb m, hPc,
      latB_mul_eq hℓ Φ m, sub_self]
  -- the indicator of the box
  let g : E3 → ℂ := (Work.BoseBoxFock.LatFourier.latBox ℓ).indicator T
  have hgaesm : AEStronglyMeasurable g volume :=
    (hTcont.aestronglyMeasurable).indicator
      (Work.BoseBoxFock.LatFourier.measurableSet_latBox ℓ)
  have hgbdd : ∃ C : ℝ, ∀ x : E3, ‖g x‖ ≤ C := by
    obtain ⟨C, hC⟩ :=
      (isCompact_latBox hℓ).exists_bound_of_continuousOn hTcont.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ Work.BoseBoxFock.LatFourier.latBox ℓ
    · have h1 : ‖g x‖ = ‖T x‖ := by simp [g, Set.indicator_of_mem hx]
      rw [h1]; exact le_trans (hC x hx) (le_max_left _ _)
    · have h1 : ‖g x‖ = 0 := by simp [g, Set.indicator_of_notMem hx]
      rw [h1]; exact le_max_right _ _
  have hgsupp : ∀ x, x ∉ Work.BoseBoxFock.LatFourier.latBox ℓ → g x = 0 :=
    fun x hx => by simp [g, Set.indicator_of_notMem hx]
  have hgmem : MemLp g 2 volume :=
    Work.BoseBoxFock.LatFourier.memLp_of_bdd_of_latBox hℓ hgaesm hgbdd hgsupp
  have htsupp : tsupport g ⊆ Work.BoseBoxFock.LatFourier.latBox ℓ := by
    refine closure_minimal (fun x hx => ?_) (Work.BoseBoxFock.LatFourier.isClosed_latBox ℓ)
    by_contra hx'
    exact hx (hgsupp x hx')
  have hfs := Work.BoseBoxFock.frameSampling_latBox hℓ hgmem htsupp
  -- all sampling coefficients of `g` vanish
  have hgcoeff : ∀ n : Fin 3 → ℤ,
      Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n) = 0 := by
    intro n
    rw [Submission.BoseGases.kinFT]
    have hfun : (fun y : E3 => Complex.exp
          (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) y : ℝ) : ℂ))) * g y)
        = (Work.BoseBoxFock.LatFourier.latBox ℓ).indicator (fun y : E3 => latChrN ℓ n y * T y) := by
      funext y
      by_cases hy : y ∈ Work.BoseBoxFock.LatFourier.latBox ℓ
      · rw [Set.indicator_of_mem hy]
        simp only [g, Set.indicator_of_mem hy, latChrN]
      · rw [Set.indicator_of_notMem hy]
        simp only [g, Set.indicator_of_notMem hy, mul_zero]
    rw [hfun, MeasureTheory.integral_indicator
      (Work.BoseBoxFock.LatFourier.measurableSet_latBox ℓ),
      MeasureTheory.setIntegral_congr_set (Work.BoseBoxFock.latBox_ae_eq_latCell hℓ.le),
      MeasureTheory.setIntegral_congr_fun (Work.BoseBoxFock.LatFourier.measurableSet_latCell ℓ)
        (fun y _ => mul_comm (latChrN ℓ n y) (T y))]
    exact hTcoeff n
  -- hence `∫ ‖g‖² = 0`
  have hsumzero : (ℓ^3 * ∫ x : E3, ‖g x‖^2) = 0 := by
    have h3 : HasSum (fun _ : Fin 3 → ℤ => (0 : ℝ)) (ℓ^3 * ∫ x : E3, ‖g x‖^2) :=
      hfs.congr_fun (fun n => by rw [hgcoeff n]; simp)
    exact h3.unique hasSum_zero
  have hintzero : (∫ x : E3, ‖g x‖^2) = 0 := by
    rcases mul_eq_zero.mp hsumzero with h | h
    · exact absurd h (by positivity)
    · exact h
  have hgint : (∫ x : E3, ‖g x‖^2)
      = ∫ x in Work.BoseBoxFock.LatFourier.latBox ℓ, ‖T x‖^2 := by
    have hpt : ∀ x : E3, ‖g x‖^2
        = (Work.BoseBoxFock.LatFourier.latBox ℓ).indicator (fun x => ‖T x‖^2) x := by
      intro x
      by_cases hx : x ∈ Work.BoseBoxFock.LatFourier.latBox ℓ
      · simp [g, Set.indicator_of_mem hx]
      · simp [g, Set.indicator_of_notMem hx]
    simp_rw [hpt]
    exact MeasureTheory.integral_indicator (Work.BoseBoxFock.LatFourier.measurableSet_latBox ℓ)
  have hTintzero : (∫ x in Work.BoseBoxFock.LatFourier.latBox ℓ, ‖T x‖^2) = 0 := by
    rw [← hgint, hintzero]
  -- `T = 0` a.e. on the box
  have hTae : T =ᵐ[volume.restrict (Work.BoseBoxFock.LatFourier.latBox ℓ)] 0 := by
    have hnn : 0 ≤ᵐ[volume.restrict (Work.BoseBoxFock.LatFourier.latBox ℓ)]
        (fun x : E3 => ‖T x‖^2) :=
      Filter.Eventually.of_forall fun x => by positivity
    have hint : IntegrableOn (fun x : E3 => ‖T x‖^2)
        (Work.BoseBoxFock.LatFourier.latBox ℓ) volume :=
      ((hTcont.norm.pow 2).continuousOn).integrableOn_compact (isCompact_latBox hℓ)
    have hnorm : (fun x : E3 => ‖T x‖^2)
        =ᵐ[volume.restrict (Work.BoseBoxFock.LatFourier.latBox ℓ)] 0 :=
      (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).mp hTintzero
    filter_upwards [hnorm] with x hx
    have h2 : ‖T x‖ = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hx
    exact norm_eq_zero.mp h2
  -- and, being continuous, everywhere on the box
  have hTeq : ∀ w ∈ Work.BoseBoxFock.LatFourier.latBox ℓ, T w = 0 := by
    intro w hw
    simpa using (MeasureTheory.Measure.eqOn_of_ae_eq hTae hTcont.continuousOn
      continuousOn_const (latBox_subset_closure_interior hℓ)) hw
  -- translate the given `z` into the box and use periodicity
  set v : Fin 3 → ℤ := fun i => ⌊z i / ℓ⌋ with hv
  have hwmem : z - ℓ • Work.BoseBoxFock.latVec v ∈ Work.BoseBoxFock.LatFourier.latBox ℓ := by
    rw [Work.BoseBoxFock.LatFourier.mem_latBox]
    intro i
    have hsub : (z - ℓ • Work.BoseBoxFock.latVec v) i = z i - ℓ * (v i : ℝ) := by
      simp [WithLp.ofLp_sub, WithLp.ofLp_smul, Work.BoseBoxFock.latVec, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
    have hvi : (v i : ℝ) = (⌊z i / ℓ⌋ : ℝ) := by rw [hv]
    have hkey : z i - ℓ * (v i : ℝ) = ℓ * (z i / ℓ - (⌊z i / ℓ⌋ : ℝ)) := by
      rw [hvi, mul_sub, mul_div_cancel₀ (z i) (ne_of_gt hℓ)]
    rw [hsub, hkey, Set.mem_Icc]
    have ht0 : 0 ≤ z i / ℓ - (⌊z i / ℓ⌋ : ℝ) := by
      have := Int.floor_le (z i / ℓ); linarith
    have ht1 : z i / ℓ - (⌊z i / ℓ⌋ : ℝ) ≤ 1 := by
      have := Int.lt_floor_add_one (z i / ℓ); linarith
    exact ⟨mul_nonneg hℓ.le ht0, by nlinarith [hℓ, ht1]⟩
  have hzeq : T z = 0 := by
    have hper : T (z - ℓ • Work.BoseBoxFock.latVec v + ℓ • Work.BoseBoxFock.latVec v)
        = T (z - ℓ • Work.BoseBoxFock.latVec v) := by
      simp only [T]
      rw [latSer_add_latVec (ne_of_gt hℓ) v (z - ℓ • Work.BoseBoxFock.latVec v),
        latPerC_add_latVec ℓ Φ v (z - ℓ • Work.BoseBoxFock.latVec v)]
    have hsimp : z - ℓ • Work.BoseBoxFock.latVec v + ℓ • Work.BoseBoxFock.latVec v = z := by abel
    rw [hsimp] at hper
    rw [hper]
    exact hTeq _ hwmem
  have hseq : latSer ℓ Φ z = latPerC ℓ Φ z := by
    have := hzeq
    simp only [T] at this
    exact sub_eq_zero.mp this
  rw [← hseq]
  simpa only [latSer, latB, latChrP] using (latSum_summable hb z).hasSum

end Work.BoseBoxFock.L1Tails
