import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.PCFU.hatChih_sum_le
import Submission.Work.BoseBoxFock.kinFT_lattice_tail_sq_lt
import Submission.Work.BoseFixR.LatGreen.W1funDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary lemmas

The pairing of a lattice frame `z ↦ Σ_{k : Lab N} W k · e^{i⟪κ_k,z⟫}` with box-supported `L²`
functions is bounded by `(sup_k ‖W k‖)·ℓ³·‖f‖₂‖g‖₂`: expanding the frame into its finite
trigonometric sum and pairing coefficient by coefficient reduces it to Cauchy–Schwarz over `Lab N`
plus the lattice (`L²` frame/Poisson) identity `hasSum_kinFT_lattice_L2`, which bounds the lattice
sum of the squared Fourier samples by `ℓ³∫‖·‖²`.

The constant `sup_k ‖W k‖` is bounded by `∫|W1fun|` (uniform in `fu, N`, by
`W1hat_abs_le`/`abs_chat_le_integral_abs`).
-/

/-- `MemLp` plus support in the box `boxL ℓ` (a set of finite measure) gives integrability. -/
lemma KfrU_aux_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3))
    (hfs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL ℓ) : Integrable f := by
  have hvol : volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL (B := Work.BoseK15.corpusBox) hℓ]
    exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hvol⟩
  have h1 : MemLp f 1 (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    (hf.restrict _).mono_exponent (by norm_num)
  have hind : Integrable ((Work.BoseK15.corpusBox.boxL ℓ).indicator f) :=
    (integrable_indicator_iff (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)).mpr
      (memLp_one_iff_integrable.mp h1)
  refine hind.congr (Filter.Eventually.of_forall (fun x => ?_))
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    have hx' : x ∉ tsupport f := fun hc => hx (hfs hc)
    have hx'' : x ∉ Function.support f := fun hc => hx' (subset_closure hc)
    rw [Function.mem_support, not_not] at hx''
    exact hx''.symm

/-- **Lattice Bessel**: the finite lattice sum over `Lab N ⊆ ℤ³` of the squared Fourier samples
of a box-supported `L²` function is at most `ℓ³∫‖f‖²` (the full-lattice Poisson/aliasing identity
`hasSum_kinFT_lattice_L2`, restricted to the finite set). -/
lemma KfrU_aux_sum_kinFT_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {f : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3))
    (hfs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ∑ k : Lab N, ‖Submission.BoseGases.kinFT f (kmomLab ℓ N k)‖ ^ 2
      ≤ ℓ ^ 3 * ∫ x : E3, ‖f x‖ ^ 2 := by
  have hHS := hasSum_kinFT_lattice_L2 (μ := ℓ) hℓ hf hfs
  have hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT f (kmomInt ℓ n)‖ ^ 2) := hHS.summable
  calc ∑ k : Lab N, ‖Submission.BoseGases.kinFT f (kmomLab ℓ N k)‖ ^ 2
      = ∑ n ∈ Finset.univ.image (labVec N),
          ‖Submission.BoseGases.kinFT f (kmomInt ℓ n)‖ ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ hab => labVec_injective N hab)]
        rfl
    _ ≤ ∑' n : Fin 3 → ℤ, ‖Submission.BoseGases.kinFT f (kmomInt ℓ n)‖ ^ 2 :=
        hsumm.sum_le_tsum _ (fun i _ => sq_nonneg _)
    _ = ℓ ^ 3 * ∫ x : E3, ‖f x‖ ^ 2 := hHS.tsum_eq

/-- The `+i` version of the lattice Bessel bound: the same estimate for the Fourier samples with
the conjugated plane wave `e^{+i⟪κ_k,y⟫}` (the reflection `κ_k ↦ -κ_k` permutes `Lab N`). -/
lemma KfrU_aux_sum_exp_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {g : E3 → ℂ}
    (hg : MemLp g 2 (volume : Measure E3))
    (hgs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ∑ k : Lab N,
        ‖∫ y : E3,
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y‖ ^ 2
      ≤ ℓ ^ 3 * ∫ y : E3, ‖g y‖ ^ 2 := by
  have hpt : ∀ k : Lab N,
      (∫ y : E3, Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y)
        = Submission.BoseGases.kinFT g (kmomLab ℓ N (-k)) := by
    intro k
    have hkey : ∀ y : E3, Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y
        = Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N (-k)) y : ℂ))) * g y := by
      intro y
      congr 1
      congr 1
      rw [kmomLab_neg, inner_neg_left]
      push_cast
      ring
    rw [Submission.BoseGases.kinFT]
    exact integral_congr_ae (Filter.Eventually.of_forall hkey)
  simp only [hpt]
  calc ∑ k : Lab N, ‖Submission.BoseGases.kinFT g (kmomLab ℓ N (-k))‖ ^ 2
      = ∑ k : Lab N, ‖Submission.BoseGases.kinFT g (kmomLab ℓ N k)‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (Lab N))
          (fun k : Lab N => ‖Submission.BoseGases.kinFT g (kmomLab ℓ N k)‖ ^ 2)
    _ ≤ ℓ ^ 3 * ∫ y : E3, ‖g y‖ ^ 2 := KfrU_aux_sum_kinFT_sq_le hℓ N hg hgs

/-- **The pairing bound for a general lattice frame.**  For `f, g ∈ L²` supported in the box
`boxL ℓ` and weights `W` with `‖W k‖ ≤ C`,

`‖∫_w∫_y f w · (Σ_{k : Lab N} W k · e^{i⟪κ_k,y−w⟫}) · g y‖ ≤ C ℓ³ ‖f‖₂ ‖g‖₂`.

Proof: expand the frame; the double integral is the finite sum
`Σ_k (W k · B_k) · A_k` with `A_k = kinFT f (κ_k)`, `B_k = ∫_y e^{i⟪κ_k,y⟫}g y`; then
Cauchy–Schwarz over `Lab N` and the two Bessel bounds `KfrU_aux_sum_kinFT_sq_le`,
`KfrU_aux_sum_exp_sq_le`. -/
lemma KfrU_aux_pairing_sum_le {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {W : Lab N → ℂ} {C : ℝ}
    (hC0 : 0 ≤ C) (hW : ∀ k : Lab N, ‖W k‖ ≤ C) {f g : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3)) (hg : MemLp g 2 (volume : Measure E3))
    (hfs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hgs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ‖∫ w : E3, ∫ y : E3,
        f w * (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y‖
      ≤ C * ℓ ^ 3 * Real.sqrt (∫ w : E3, ‖f w‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
  have hfint : Integrable f := KfrU_aux_integrable hℓ hf hfs
  have hgint : Integrable g := KfrU_aux_integrable hℓ hg hgs
  -- the bounded factor `e^{i⟪κ_k,·⟫}`
  have hbdd : ∀ k : Lab N, ∀ᵐ y : E3 ∂(volume : Measure E3),
      ‖Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))‖ ≤ 1 := by
    intro k
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [show Complex.I * ((inner ℝ (kmomLab ℓ N k) y : ℝ) : ℂ)
          = ((inner ℝ (kmomLab ℓ N k) y : ℝ) : ℂ) * Complex.I from by ring,
      Complex.norm_exp_ofReal_mul_I]
  -- the coefficients
  set B : Lab N → ℂ := fun k => ∫ y : E3,
    Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y with hB
  set A : Lab N → ℂ := fun k => Submission.BoseGases.kinFT f (kmomLab ℓ N k) with hA
  -- the inner expansion, for every `w`
  have hstep1 : ∀ w : E3,
      (∫ y : E3, f w * (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y)
        = f w * (∑ k : Lab N,
            (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))) * B k) := by
    intro w
    rw [show (∫ y : E3, f w * (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y)
        = ∫ y : E3, f w * ((∑ k : Lab N, W k *
            Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y) from
          integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring)),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun y : E3 => (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y)
        = (fun y : E3 => ∑ k : Lab N,
            (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))) *
              (Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y)) from
          funext (fun y => by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [show Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))
                = Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) *
                  Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ))) from by
              rw [← Complex.exp_add]
              congr 1
              rw [inner_sub_right]
              push_cast
              ring]
            ring)]
    rw [MeasureTheory.integral_finsetSum (Finset.univ : Finset (Lab N))
      (f := fun (k : Lab N) (y : E3) =>
        (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))) *
          (Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y))
      (fun k _ => ((hgint.mul_bdd (by fun_prop) (hbdd k)).const_mul
        (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ))))).congr
          (Filter.Eventually.of_forall (fun y => by ring)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MeasureTheory.integral_const_mul, hB]
  -- the outer expansion
  have hstep2 : (∫ w : E3, f w * (∑ k : Lab N,
        (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))) * B k))
      = ∑ k : Lab N, (W k * B k) * A k := by
    have hE2 : ∀ (k : Lab N) (w : E3),
        ‖Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))‖ ≤ 1 := by
      intro k w
      rw [show -(Complex.I * ((inner ℝ (kmomLab ℓ N k) w : ℝ) : ℂ))
            = ((-(inner ℝ (kmomLab ℓ N k) w) : ℝ) : ℂ) * Complex.I from by
          push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [show (fun w : E3 => f w * (∑ k : Lab N,
          (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))) * B k))
        = (fun w : E3 => ∑ k : Lab N,
            (W k * B k) * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))
              * f w)) from
          funext (fun w => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring))]
    rw [MeasureTheory.integral_finsetSum (Finset.univ : Finset (Lab N))
      (fun k _ => ((hfint.mul_bdd (by fun_prop)
        (Filter.Eventually.of_forall (fun w => hE2 k w))).const_mul (W k * B k)).congr
          (Filter.Eventually.of_forall (fun w => by ring)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MeasureTheory.integral_const_mul]
    rfl
  -- assemble the expansion
  have hmain : (∫ w : E3, ∫ y : E3, f w * (∑ k : Lab N, W k *
        Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y)
      = ∑ k : Lab N, (W k * B k) * A k := by
    rw [show (∫ w : E3, ∫ y : E3, f w * (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y - w) : ℂ))) * g y)
        = ∫ w : E3, f w * (∑ k : Lab N,
            (W k * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)))) * B k) from
          integral_congr_ae (Filter.Eventually.of_forall hstep1)]
    exact hstep2
  rw [hmain]
  -- Cauchy–Schwarz over `Lab N`
  have hCS : ∑ k : Lab N, ‖A k‖ * ‖B k‖
      ≤ Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Lab N))
      (fun k => ‖A k‖) (fun k => ‖B k‖)
    rw [← Real.sqrt_sq (Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
    calc Real.sqrt ((∑ k : Lab N, ‖A k‖ * ‖B k‖) ^ 2)
        ≤ Real.sqrt ((∑ k : Lab N, ‖A k‖ ^ 2) * ∑ k : Lab N, ‖B k‖ ^ 2) :=
          Real.sqrt_le_sqrt h
      _ = Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2) :=
          Real.sqrt_mul (Finset.sum_nonneg (fun k _ => sq_nonneg _)) _
  have hAsum : ∑ k : Lab N, ‖A k‖ ^ 2 ≤ ℓ ^ 3 * ∫ x : E3, ‖f x‖ ^ 2 := by
    simp only [hA]
    exact KfrU_aux_sum_kinFT_sq_le hℓ N hf hfs
  have hBsum : ∑ k : Lab N, ‖B k‖ ^ 2 ≤ ℓ ^ 3 * ∫ y : E3, ‖g y‖ ^ 2 := by
    simp only [hB]
    exact KfrU_aux_sum_exp_sq_le hℓ N hg hgs
  -- the chain of inequalities
  have hroot : Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)
      ≤ ℓ ^ 3 * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
    have h1 : Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2)
        ≤ Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
      exact Real.sqrt_le_sqrt hAsum
    have h2 : Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)
        ≤ Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
      exact Real.sqrt_le_sqrt hBsum
    have h3 : Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) = ℓ ^ 3 := by
      rw [← sq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
    have h4 : (0 : ℝ) ≤ Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := Real.sqrt_nonneg _
    calc Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)
        ≤ (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2))
            * (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2)) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
      _ = ℓ ^ 3 * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
          rw [show (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2))
                * (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2))
              = (Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3))
                * (Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2))
              from by ring, h3]
          ring
  calc ‖∑ k : Lab N, (W k * B k) * A k‖
      ≤ ∑ k : Lab N, ‖(W k * B k) * A k‖ := norm_sum_le _ _
    _ ≤ ∑ k : Lab N, C * (‖A k‖ * ‖B k‖) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [norm_mul, norm_mul]
        calc ‖W k‖ * ‖B k‖ * ‖A k‖ ≤ C * ‖B k‖ * ‖A k‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hW k) (norm_nonneg _))
                (norm_nonneg _)
          _ = C * (‖A k‖ * ‖B k‖) := by ring
    _ = C * ∑ k : Lab N, ‖A k‖ * ‖B k‖ := by rw [Finset.mul_sum]
    _ ≤ C * (Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS hC0
    _ ≤ C * (ℓ ^ 3 * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2)) := mul_le_mul_of_nonneg_left hroot hC0
    _ = C * ℓ ^ 3 * Real.sqrt (∫ w : E3, ‖f w‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by ring

/-- The UV cutoff is bounded by `1` in absolute value. -/
lemma KfrU_aux_uvCut_abs_le (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (k : E3) :
    |Work.BoseBoxFock.uvCut fu Λ k| ≤ 1 := by
  rw [Work.BoseBoxFock.uvCut, abs_of_nonneg (Work.BoseBoxFix.LowCut.nonneg fu _)]
  exact Work.BoseBoxFix.LowCut.le_one fu _

/-- The weight `W1h` is dominated by the `L¹` mass of `W1fun`, uniformly in the label, the
lattice size `N` and the cut-off `fu`. -/
lemma KfrU_aux_W1h_abs_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (k : Lab N) :
    |Work.BoseBoxFock.W1h v h μ fu N k|
      ≤ ∫ x : E3,
          |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x| := by
  rw [Work.BoseBoxFock.W1h, abs_mul]
  calc |Work.BoseBoxFock.uvCut fu
          (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) N)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)|
        * |Work.BoseFixR.chat
            (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)|
      ≤ 1 * |Work.BoseFixR.chat
            (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)| :=
        mul_le_mul_of_nonneg_right (KfrU_aux_uvCut_abs_le fu _ _) (abs_nonneg _)
    _ = |Work.BoseFixR.chat
            (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)| := one_mul _
    _ ≤ ∫ x : E3,
          |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x| :=
        Work.BoseB7AK.W1rows.abs_chat_le_integral_abs _

/-- The `χ̂`-weighted weight is dominated by the same constant (`|χ̂| ≤ 1`). -/
lemma KfrU_aux_W1h_hatChih_abs_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (k : Lab N) :
    |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k|
      ≤ ∫ x : E3,
          |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x| := by
  rw [abs_mul, Work.BoseBoxFock.hatChih]
  calc |Work.BoseBoxFock.W1h v h μ fu N k|
        * |Work.BoseK15.corpusBox.hatChi
            (Work.BoseBoxFock.ellH v μ
              • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)|
      ≤ (∫ x : E3,
            |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x|) * 1 :=
        mul_le_mul (KfrU_aux_W1h_abs_le h μ fu N k) (Work.BoseK15.hatChi_le_one.1 _)
          (abs_nonneg _) (MeasureTheory.integral_nonneg (fun x : E3 => abs_nonneg _))
    _ = ∫ x : E3,
          |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x| := mul_one _

theorem KfrU_pairing_uniform {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {μ : ℝ}
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ {fu : Work.BoseBoxFix.LowCut} {N : ℕ}, 1 ≤ N →
        ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℂ},
        MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) →
        MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) →
        tsupport f ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
        ‖∫ w : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
            f w * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w) * g y‖
          ≤ C * (Work.BoseBoxFock.ellH v μ) ^ 3
              * Real.sqrt (∫ w : EuclideanSpace ℝ (Fin 3), ‖f w‖ ^ 2)
              * Real.sqrt (∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ ^ 2)) ∧
      (∀ {fu : Work.BoseBoxFix.LowCut} {N : ℕ}, 1 ≤ N →
        ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℂ},
        MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) →
        MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) →
        tsupport f ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
        ‖∫ w : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
            f w * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (y - w) * g y‖
          ≤ C * (Work.BoseBoxFock.ellH v μ) ^ 3
              * Real.sqrt (∫ w : EuclideanSpace ℝ (Fin 3), ‖f w‖ ^ 2)
              * Real.sqrt (∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ ^ 2)) := by
  have _ := hv
  have _ := hvrad
  have _ := hR
  have _ := hv_supp
  have _ := hRℓ
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  set C₀ : ℝ := ∫ x : E3,
      |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x| with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    exact MeasureTheory.integral_nonneg (fun x : E3 => abs_nonneg _)
  refine ⟨C₀, hC₀0, ?_, ?_⟩
  · intro fu N _hN f g hf hg hfs hgs
    refine KfrU_aux_pairing_sum_le (ℓ := Work.BoseBoxFock.ellH v μ) (N := N)
      (W := fun k => ((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ))
      hℓ (C := C₀) hC₀0 (fun k => ?_) hf hg hfs hgs
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hC₀]
    exact KfrU_aux_W1h_abs_le h μ fu N k
  · intro fu N _hN f g hf hg hfs hgs
    refine KfrU_aux_pairing_sum_le (ℓ := Work.BoseBoxFock.ellH v μ) (N := N)
      (W := fun k => ((Work.BoseBoxFock.W1h v h μ fu N k
        * Work.BoseBoxFock.hatChih v μ N k : ℝ) : ℂ))
      hℓ (C := C₀) hC₀0 (fun k => ?_) hf hg hfs hgs
    rw [Complex.norm_real, Real.norm_eq_abs, hC₀]
    exact KfrU_aux_W1h_hatChih_abs_le h μ fu N k

end Work.BoseBoxFock.PCFU
